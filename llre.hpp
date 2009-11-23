/*
 *
 * LLRE: a toy regexp implementation with LLVM
 *
 */
#ifndef LLRE_HPP
#define LLRE_HPP

#include <string>
#include <exception>
#include <memory>
#include <set>
#include <map>
#include <iostream>
#include <fstream> // for debug
#include <utility>
#include <boost/assert.hpp>
#include <boost/format.hpp>
#include <boost/scoped_ptr.hpp>
#include <boost/utility.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>
#include <llvm/Module.h>
#include <llvm/Function.h>
#include <llvm/Constants.h>
#include <llvm/DerivedTypes.h>
#include <llvm/Instructions.h>
#include <llvm/ModuleProvider.h>
#include <llvm/Analysis/Verifier.h>
#include <llvm/ExecutionEngine/JIT.h>
#include <llvm/Bitcode/ReaderWriter.h>

#define MY_T(str) (str)
//#define LLRE_VERBOSE

namespace llre {

  // stolen from boost/concept_check.hpp
  template <class T> inline void ignore_unused_variable_warning(const T&) { }

  typedef std::string string_t;
  typedef string_t::value_type char_t;

  template<class T>
  inline void insert_all(T& dst, const T& src)
  {
    dst.insert(src.begin(), src.end());
  }

  template<class Iter>
  inline Iter forward(const Iter& iter, size_t d) {
    Iter ret = iter;
    std::advance(ret, d);
    return ret;
  }

  /*
   * regexp AST node type
   */
  enum atom_type_e {
    atom_type_symbol,
    atom_type_group,
    atom_type_star,
    atom_type_choice,
    atom_type_cat,
    atom_type_end,
    atom_type_epsilon,
    atom_types
  };

  inline const char* const to_s(atom_type_e type)
  {
    switch (type) {
    case atom_type_symbol:
      return "symbol";
    case atom_type_group:
      return "group";
    case atom_type_star:
      return "star";
    case atom_type_choice:
      return "choice";
    case atom_type_cat:
      return "cat";
    default:
      BOOST_ASSERT(false);
      return "";
    }
  }

  inline std::ostream& operator<<(std::ostream& out, atom_type_e type)
  {
    return (out << to_s(type));
  }

  class atom_t
  {
  public:
    explicit atom_t(atom_type_e t, char_t v = 0)
      : m_type(t), m_value(v) {}
    typedef char_t value_type;

    atom_type_e type() const { return m_type; }
    value_type value() const {  return m_value; }

    static atom_t end_marker() { return atom_t(atom_type_symbol, 0); }
  private:
    atom_type_e m_type;
    value_type m_value;
  };

  class node_t : boost::noncopyable
  {
  public:
    typedef std::set<node_t*> set_type;

    explicit node_t(const atom_t& a, node_t* l=0, node_t* r=0)
      : m_atom(a), m_left(l), m_right(r) {}

    const atom_t& atom() const { return m_atom; }
    void set_atom(const atom_t& v) { m_atom = v; }

    node_t* left() const { return m_left.get(); }
    void set_left(node_t* n) { BOOST_ASSERT(!m_left.get()); m_left.reset(n); }
    node_t* release_left() { return m_left.release(); }

    node_t* right() const { return m_right.get(); }
    void set_right(node_t* n) { BOOST_ASSERT(!m_right.get()); m_right.reset(n); }
    node_t* release_right() { return m_right.release(); }

    node_t* child() const { BOOST_ASSERT(!m_right.get()); return m_left.get(); }

    bool leaf() const { return !m_left.get() && !m_right.get(); }
    bool filled() const { return m_left.get() && m_right.get(); }
    bool single() const { return m_left.get() && !m_right.get(); }

    /* shorthand */
    atom_t::value_type value() const { return m_atom.value(); }
    atom_type_e type() const { return m_atom.type(); }

  private:
    atom_t m_atom;
    std::auto_ptr<node_t> m_left;
    std::auto_ptr<node_t> m_right;
  };

  class tree_t : boost::noncopyable
  {
  public:
    tree_t() : m_root(make_root()) {}
    node_t* root() const { return m_root.get(); }

  private:
    static node_t* make_root() {
      return new node_t(atom_t(atom_type_cat), 0, new node_t(atom_t::end_marker()));
    }

    boost::scoped_ptr<node_t> m_root;
  };

  class tree_functions_t
  {
  public:
    typedef std::set<node_t*> set_type;
    typedef std::map<const node_t*, set_type> set_map_type;
    typedef std::map<const node_t*, bool> predicate_map_type;

    tree_functions_t(const tree_t& tree) {
      compute(tree.root());
    }

    bool nullable(const node_t* n) const {
      BOOST_ASSERT(m_nullable.end() != m_nullable.find(n));
      return m_nullable.find(n)->second;
    }

    const set_type& firstpos(const node_t* n) const {
      BOOST_ASSERT(m_firstpos.end() != m_firstpos.find(n));
      return m_firstpos.find(n)->second;
    }

    const set_type& lastpos(const node_t* n) const {
      BOOST_ASSERT(m_lastpos.end() != m_lastpos.find(n));
      return m_lastpos.find(n)->second;
    }

    const set_type& followpos(const node_t* n) const {
      if (m_followpos.end() != m_followpos.find(n)) {
        return m_followpos.find(n)->second;
      } else {
        return m_empty_set;
      }
    }

  private:

    void compute(node_t* n) {
      if (n->right()) { compute(n->right()); }
      if (n->left()) { compute(n->left()); }
      compute_node_functions(n);
    }

    void compute_node_functions(node_t* n) {
      m_nullable.insert(std::make_pair(n, compute_nullable(n)));
      m_firstpos.insert(std::make_pair(n, compute_firstpos(n)));
      m_lastpos.insert(std::make_pair(n, compute_lastpos(n)));
      compute_followpos(n);
    }

    bool compute_nullable(node_t* n) {
      switch (n->type()) {
      case atom_type_symbol:
        return false;
      case atom_type_group:
        return m_nullable.find(n->child())->second;
      case atom_type_star:
        return true;
      case atom_type_choice:
        return (m_nullable.find(n->left())->second ||
                m_nullable.find(n->right())->second);
      case atom_type_cat:
        return (m_nullable.find(n->left())->second &&
                m_nullable.find(n->right())->second);
      case atom_type_epsilon:
        return true;
      default:
        BOOST_ASSERT(false);
        return false;
      }
    }

    set_type compute_firstpos(node_t* n) {
      return compute_last_or_first(n, n->single() ? n->child() : 0, n->left(), n->right());
    }

    set_type compute_lastpos(node_t* n) {
      return compute_last_or_first(n, n->single() ? n->child() : 0, n->right(), n->left());
    }

    set_type compute_last_or_first(node_t* n,
                                   node_t* c, node_t* c0, node_t* c1) {
      set_type ret;

      switch (n->type()) {
      case atom_type_symbol:
        ret.insert(n);
        break;
      case atom_type_group:
        BOOST_ASSERT(c);
        insert_all(ret, m_firstpos.find(c)->second);
        break;
      case atom_type_star:
        BOOST_ASSERT(c);
        insert_all(ret, m_firstpos.find(c)->second);
        break;
      case atom_type_choice:
        insert_all(ret, m_firstpos.find(c0)->second);
        insert_all(ret, m_firstpos.find(c1)->second);
        break;
      case atom_type_cat:
        if (nullable(c0)) {
          insert_all(ret, m_firstpos.find(c0)->second);
          insert_all(ret, m_firstpos.find(c1)->second);
        } else {
          insert_all(ret, m_firstpos.find(c0)->second);
        }
        break;
      case atom_type_epsilon:
        break;
      default:
        BOOST_ASSERT(false);
        break;
      }

      return ret;
    }

    void compute_followpos(node_t* n) {
      switch (n->type()) {
      case atom_type_star:
        compute_followpos_star(n);
        break;
      case atom_type_cat:
        compute_followpos_cat(n);
        break;
      default:
        break;
      }
    }

    void compute_followpos_star(node_t* n) {
      const set_type& nfirst = firstpos(n);
      const set_type& nlast  = lastpos(n);
      for (set_type::const_iterator i=nlast.begin(); i!=nlast.end(); ++i) {
        set_type& ifollow = m_followpos[*i];
        for (set_type::const_iterator j=nfirst.begin(); j!=nfirst.end(); ++j) {
          ifollow.insert(*j);
        }
      }
    }

    void compute_followpos_cat(node_t* n) {
      const set_type& llast  = lastpos(n->left());
      const set_type& rfirst = firstpos(n->right());
      for (set_type::const_iterator i=llast.begin(); i!=llast.end(); ++i) {
        set_type& ifollow = m_followpos[*i];
        for (set_type::const_iterator j=rfirst.begin(); j!=rfirst.end(); ++j) {
          ifollow.insert(*j);
        }
      }
    }

  private:
    predicate_map_type m_nullable;
    set_map_type m_firstpos;
    set_map_type m_lastpos;
    set_map_type m_followpos;
  private:
    const set_type m_empty_set; // FIXME: make static
  };

  /*
   * naive dfa
   */

  class dfa_state_t
  {
  public:
    typedef size_t id_type;
    typedef char_t arc_type;
    typedef std::map<arc_type, id_type> transition_map_type;
    typedef transition_map_type::iterator iterator;
    typedef transition_map_type::const_iterator const_iterator;

    dfa_state_t() : m_id(invalid_id()), m_accepting(false) { /* to be default-constructable */ }
    dfa_state_t(id_type id, bool accepting) : m_id(id), m_accepting(accepting) {}

    id_type id() const { return m_id; }
    bool accepting() const { return m_accepting; }

    void insert(arc_type arc, id_type next) {
      m_arcs.insert(std::make_pair(arc, next));
    }

    iterator begin() { return m_arcs.begin(); }
    const_iterator begin() const { return m_arcs.begin(); }
    iterator end() { return m_arcs.end(); }
    const_iterator end() const { return m_arcs.end(); }
    iterator find(arc_type arc) { return m_arcs.find(arc); }
    const_iterator find(arc_type arc) const { return m_arcs.find(arc); }

    size_t arc_size() const { return m_arcs.size(); }
  private:
    static id_type invalid_id() { return std::numeric_limits<id_type>::max(); }
  private:
    id_type m_id;
    bool m_accepting;
    transition_map_type m_arcs;
  };

  class dfa_t
  {
  public:
    typedef dfa_state_t state_type;
    typedef state_type::id_type id_type;
    typedef state_type::arc_type arc_type;
    typedef std::map<id_type, state_type> transition_map_type;
    typedef transition_map_type::iterator iterator;
    typedef transition_map_type::const_iterator const_iterator;

    size_t size() const { return m_states.size(); }
    id_type start() const { return m_start; }
    void set_start(id_type id) { m_start = id; }

    const state_type& state(id_type id) const {
      BOOST_ASSERT(m_states.end() != m_states.find(id));
      return m_states.find(id)->second;
    }

    void insert_state(id_type id, bool accepting) {
      BOOST_ASSERT(m_states.end() == m_states.find(id));
      m_states.insert(std::make_pair(id, state_type(id, accepting)));
    }

    void insert_arc(id_type curr, arc_type arc, id_type next) {
      BOOST_ASSERT(m_states.end() != m_states.find(curr));
      m_states.find(curr)->second.insert(arc, next);
    }

    iterator begin() { return m_states.begin(); }
    iterator end() { return m_states.end(); }
    const_iterator begin() const { return m_states.begin(); }
    const_iterator end() const { return m_states.end(); }

  private:
    id_type m_start;
    transition_map_type m_states;
  };

  class dfa_builder_t
  {
  public:
    typedef tree_functions_t::set_type state_type;
    typedef std::map<state_type, bool> state_map_type;
    typedef std::map< std::pair<state_type, char_t>, state_type > transition_map_type;

    static bool unmarked(const state_map_type::value_type& x) {
      return !(x.second);
    }

    static bool accepting(const state_type::value_type& x) {
      return (x->type() == atom_type_symbol && x->value() == 0);
    }

    dfa_builder_t(const tree_t& tree)
      : m_tree(tree), m_functions(tree) {
      build();
    }

    size_t state_id(const state_type& state) const {
      BOOST_ASSERT(m_dstates.end() != m_dstates.find(state));
      return std::distance(m_dstates.begin(), m_dstates.find(state));
    }

    dfa_t dfa() const {
      dfa_t ret;
      for (state_map_type::const_iterator i=m_dstates.begin(); i!=m_dstates.end(); ++i) {
        ret.insert_state(state_id(i->first),
                         i->first.end() != std::find_if(i->first.begin(), i->first.end(),
                                                        &accepting));
      }

      for (transition_map_type::const_iterator i=m_dtrans.begin(); i!=m_dtrans.end(); ++i) {
        dfa_t::id_type curr_id = state_id(i->first.first);
        dfa_t::id_type next_id = state_id(i->second);
        ret.insert_arc(curr_id, i->first.second, next_id);
      }

      ret.set_start(state_id(m_functions.firstpos(m_tree.root())));

      return ret;
    }

  private:
    void build() {
      // dragonbook fig. 3.62
      m_dstates.insert(std::make_pair(m_functions.firstpos(m_tree.root()), false));
      state_map_type::iterator s;
      while (m_dstates.end()
             != (s = std::find_if(m_dstates.begin(), m_dstates.end(), &unmarked))) {
        s->second = true;
        for (char_t a=0; a<127; ++a) { // assume ascii
          state_type u;

          for (state_type::iterator i=s->first.begin(); i!=s->first.end(); ++i) {
            if ((*i)->value() == a) {
              insert_all(u, m_functions.followpos((*i)));
            }
          }

          if (u.empty()) { continue; }

          if (m_dstates.end() == m_dstates.find(u)) {
            m_dstates.insert(std::make_pair(u, false));
          }

          m_dtrans.insert(std::make_pair(std::make_pair(s->first, a), u));
        }
      }
    }

  private:
    const tree_t& m_tree;
    const tree_functions_t m_functions;
    state_map_type m_dstates;
    transition_map_type m_dtrans;
  };

  /*
   * debug/verification utility
   */
  class position_finder
  {
  public:
    position_finder(const tree_t& tree, const node_t* node) : m_position(0) {
      bool found = find(tree.root(), node);
      BOOST_ASSERT(found);
    }

    size_t position() const { return m_position; }

  private:
    bool find(const node_t* curr, const node_t* node) {

      if (curr->left()) {
        if (find(curr->left(), node)) {
          return true;
        }
      }

      if (curr->right()) {
        if (find(curr->right(), node)) {
          return true;
        }
      }

      if (curr == node) {
        return true;
      }

      m_position++;
      return false;
    }

    size_t m_position;
  };

  inline size_t position(const tree_t& tree, const node_t* node)
  {
    BOOST_ASSERT(node);
    return position_finder(tree, node).position();
  }

  typedef std::set<size_t> position_set_t;

  inline position_set_t
  to_position_set(const tree_t& tree, const tree_functions_t::set_type& nodes)
  {
    typedef tree_functions_t::set_type::const_iterator iter_type;
    position_set_t ret;

    for (iter_type i=nodes.begin(); i!=nodes.end(); ++i) {
      ret.insert(position(tree, *i));
    }

    return ret;
  }

  void dump_node(std::ostream& out, const tree_t& tree, const node_t* node, size_t level)
  {
    for (size_t i=0; i<level; ++i) { out << ' '; }

    out << node->atom().type() << "[" << position(tree, node) << "]";
    if (node->atom().value()) { out << ":" << node->atom().value(); }

    out << std::endl;

    if (node->left()) { dump_node(out, tree, node->left(), level+1); }
    if (node->right()) { dump_node(out, tree, node->right(), level+1); }
  }

  void dump_tree(std::ostream& out, const tree_t& tree)
  {
    dump_node(out, tree, tree.root(), 0);
  }

  void dump_dfa(std::ostream& out, const dfa_t& dfa)
  {
    out << "start:" << dfa.start() << std::endl;
    for (dfa_t::const_iterator i=dfa.begin(); i!=dfa.end(); ++i) {
      out << i->second.id() << "(" << i->second.accepting() << ") ";
      for (dfa_state_t::const_iterator j=i->second.begin(); j!=i->second.end(); ++j) {
        out << j->first << "->" << j->second << ",";
      }
      out << std::endl;
    }
  }

  /*
   * parser
   */
  template<class Iter>
  class basic_range_t
  {
  public:
    typedef Iter iterator;
    typedef char value_type;

    basic_range_t(iterator b, iterator e) : m_begin(b), m_end(e) {}

    iterator begin() const { return m_begin; }
    iterator end() const { return m_end; }
    value_type at(size_t i) const { BOOST_ASSERT(i < size()); return *(m_begin+i); }
    value_type front() const { return at(0); }
    size_t size() const { BOOST_ASSERT(m_begin <= m_end); return std::distance(m_begin, m_end); }
    bool empty() const { return 0 == size(); }

    basic_range_t pop_front() const { BOOST_ASSERT(!empty()); return basic_range_t(m_begin+1, m_end); }
    basic_range_t pop_back() const { BOOST_ASSERT(!empty()); return basic_range_t(m_begin, m_end-1); }

  private:
    iterator m_begin;
    iterator m_end;
  };

  template<class Iter>
  std::ostream& operator<<(std::ostream& out, const llre::basic_range_t<Iter>& r)
  {
    for (typename llre::basic_range_t<Iter>::iterator i=r.begin(); i!=r.end(); ++i) { out << *i; }
    return out;
  }

  class range_t : public basic_range_t<std::string::const_iterator>
  {
  public:
    typedef basic_range_t<std::string::const_iterator> base_type;
    range_t(iterator b, iterator e) : base_type(b, e) {}
    range_t(const string_t& str) : base_type(str.begin(), str.end()) {}
    range_t(const base_type& base) : base_type(base) {}
  };


  class bad_syntax : public std::exception
  {
  public:
    bad_syntax(const std::string& msg="") : m_what(msg) {}
    ~bad_syntax() throw() {}
    const char* what() const throw() { return m_what.c_str(); }
  private:
    std::string m_what;
  };

  class short_of_string : public bad_syntax
  {
  public:
    short_of_string(const std::string& msg="") : bad_syntax(msg) {}
  };

  class wrong_alphabet : public bad_syntax
  {
  public:
    wrong_alphabet(const std::string& msg="") : bad_syntax(msg) {}
  };

  class parser_t
  {
  public:
    typedef range_t::value_type value_type;
    typedef std::auto_ptr<node_t> node_ptr;

    parser_t(const range_t& range, tree_t* tree)
      : m_range(range), m_tree(tree), m_node(0) {}

    void start() {
      exp();
      if (!empty()) { throw bad_syntax(); }
      m_tree->root()->set_left(m_node.release());
      BOOST_ASSERT(m_tree->root()->filled());
    }

    static char_t escaped_symbol(char ch) {
      switch (ch) {
      case 'n': return '\n';
      case 't': return '\t';
      default: return ch;
      }
    }

    static char_t identity_symbol(char ch) {
      return ch;
    }

    /*
     * syntatic elements
     */
    void exp()
    {
      do {
        exp0();
        exp1();
      } while (!m_range.empty());
    }

    void try_exp() {
      try {
        exp();
      } catch(const wrong_alphabet&) {
        /* currently we reject epsilon */
        if (!m_node.get()) { throw; }
      }
    }

    template<class F>
    void symbol(F f)
    {
      if (m_range.empty()) { throw short_of_string(); }
      cat(new node_t(atom_t(atom_type_symbol, f(m_range.front()))));
      m_range = m_range.pop_front();
    }

    void exp0()
    {
      if (m_range.empty()) {
        throw short_of_string();
      } else if (MY_T('(') == m_range.front()) {
        /* store current node to the stack for coming sub-exp() */
        node_ptr left  = node_ptr(m_node.release());

        match(MY_T('('));
        try_exp();
        match(MY_T(')'));

        if (left.get()) {
          m_node.reset(new node_t(atom_t(atom_type_cat),
                                  left.release(),
                                  new node_t(atom_t(atom_type_group),
                                             m_node.release())));
        } else {
          m_node.reset(new node_t(atom_t(atom_type_group), m_node.release()));
        }

      } else if (MY_T('\\' == m_range.front())) {
        match(MY_T('\\'));
        if (!m_range.empty() && m_range.front() == MY_T('e')) {
          // treat epsilon as special escape: its node type is epsilon, not symbol.
          epsilon();
        } else {
          symbol(&parser_t::escaped_symbol);
        }
      } else if (isalnum(m_range.front())) {
        symbol(&parser_t::identity_symbol);
      } else {
        throw wrong_alphabet();
      }
    }

    void exp1()
    {
      if (m_range.empty()) {
        return;
      } else if (m_range.front() == MY_T('|')) {
        /* store current node to the stack for coming sub-exp() */
        node_ptr left  = node_ptr(m_node.release());
        match(MY_T('|'));
        try_exp();
        m_node = node_ptr(new node_t(atom_t(atom_type_choice),
                                     left.release(), m_node.release()));
      } else if (m_range.front() == MY_T('*')) {
        match(MY_T('*'));
        if (m_node->type() == atom_type_cat) {
          m_node->set_right(new node_t(atom_t(atom_type_star),
                                       m_node->release_right()));
        } else {
          m_node.reset(new node_t(atom_t(atom_type_star), m_node.release()));
        }
      }
    }

    void epsilon()
    {
      match(MY_T('e'));
      cat(new node_t(atom_t(atom_type_epsilon)));
    }

    /*
     * parsing utilities
     */
    void match(value_type val)
    {
      if (m_range.empty()) {
        throw short_of_string();
      } else if (m_range.front() != val) {
        throw wrong_alphabet();
      } else {
        m_range = m_range.pop_front();
      }
    }

    bool empty() const { return m_range.empty(); }

    /*
     * tree construction utilities
     */
    void cat(node_t* n)
    {
      if (m_node.get()) {
        BOOST_ASSERT(m_node.get() && n);
        m_node = node_ptr(new node_t(atom_t(atom_type_cat), m_node.release(), n));
      } else {
        m_node = node_ptr(n);
      }
    }

  private:
    range_t m_range;
    tree_t* m_tree;
    node_ptr m_node;
  };

  dfa_t build_dfa(const range_t& range) {
    tree_t tree;
    parser_t(range, &tree).start();
    return dfa_builder_t(tree).dfa();
  }

  /*
   * regexp engine interface
   */
  class matcher_t
  {
  public:
    virtual ~matcher_t() {}
    virtual const char_t* match(const char_t* beg, const char* end) const = 0;
    virtual bool search(const char_t* beg, const char* end, const char_t** mbeg, const char** mend) const = 0;
  };

  /*
   * regexp interpreter
   */
  class interpreter_t : public matcher_t
  {
  public:
    interpreter_t(const string_t& pattern)
      : m_pattern(pattern), m_dfa(build_dfa(pattern)) {}

    const string_t& pattern() const { return m_pattern; }
    const dfa_t& dfa() const { return m_dfa; } // for debug

    bool match(const string_t& str) const {
      const char_t* beg = &str[0];
      const char_t* end = &str[str.size()];
      return end == match(beg, end);
    }

    virtual const char_t* match(const char_t* beg, const char* end) const {
      BOOST_ASSERT(beg <= end);
      const dfa_state_t* s = &(m_dfa.state(m_dfa.start()));
      const char_t* matched = s->accepting() ? beg : 0;

      for (const char_t* i=beg; i!=end; ++i) {
        dfa_state_t::const_iterator j = s->find(*i);
        if (s->end() == j) { break; }
        s = &(m_dfa.state(j->second));
        if (s->accepting()) { matched = i+1; }
      }

      return matched;
    }

    virtual bool search(const char_t* beg, const char* end, const char_t** mbeg, const char** mend) const {
      const char* i = beg;
      while (i < end) {
        const char_t* m = match(i, end);
        if (m) {
          *mbeg = i; *mend = m;
          return true;
        }
        ++i;
      }
      return false;
    }

  private:
    string_t m_pattern;
    dfa_t m_dfa;
  };

  /* debug callback */
  inline void put_char_ptr(int ch)
  {
    std::cout << *(reinterpret_cast<char_t*>(ch)) << std::endl;
  }

  inline void put_char(char_t ch)
  {
    std::cout << (ch) << std::endl;
  }

  inline void put_int(int i)
  {
    std::cout << (i) << std::endl;
  }

  /*
   * regexp compiler with llvm
   */
  struct module_globals_t
  {
    module_globals_t() {
      m_char_ptr_type = llvm::PointerType::get(llvm::Type::Int8Ty);
      m_char_ptr_ptr_type = llvm::PointerType::get(m_char_ptr_type);
      m_sizeof_char = llvm::ConstantInt::get(llvm::Type::Int32Ty, sizeof(char_t));

      std::vector<const llvm::Type*> arg_types_0;
      arg_types_0.push_back(llvm::Type::Int32Ty);
      llvm::FunctionType* ftype0 = llvm::FunctionType::get(llvm::Type::VoidTy, arg_types_0, false);
      m_put_char_ptr
        = llvm::ConstantExpr::getIntToPtr(llvm::ConstantInt::get
                                          (llvm::Type::Int32Ty,
                                           reinterpret_cast<int>(&put_char_ptr)),
                                          llvm::PointerType::get(ftype0));

      std::vector<const llvm::Type*> arg_types_1;
      arg_types_1.push_back(llvm::Type::Int8Ty);
      llvm::FunctionType* ftype1 = llvm::FunctionType::get(llvm::Type::VoidTy, arg_types_1, false);
      m_put_char
        = llvm::ConstantExpr::getIntToPtr(llvm::ConstantInt::get
                                          (llvm::Type::Int32Ty,
                                           reinterpret_cast<int>(&put_char)),
                                          llvm::PointerType::get(ftype1));

      std::vector<const llvm::Type*> arg_types_2;
      arg_types_2.push_back(llvm::Type::Int32Ty);
      llvm::FunctionType* ftype2 = llvm::FunctionType::get(llvm::Type::VoidTy, arg_types_2, false);
      m_put_int
        = llvm::ConstantExpr::getIntToPtr(llvm::ConstantInt::get
                                          (llvm::Type::Int32Ty,
                                           reinterpret_cast<int>(&put_int)),
                                          llvm::PointerType::get(ftype2));
    }

    llvm::Value* m_put_char_ptr;
    llvm::Value* m_put_char;
    llvm::Value* m_put_int;

    llvm::Value* m_sizeof_char;
    const llvm::PointerType* m_char_ptr_type;
    const llvm::PointerType* m_char_ptr_ptr_type;

  };

  class match_compiler_t
  {
  public:
    typedef std::vector<llvm::BasicBlock*> basic_block_list_type;
    typedef std::map<llvm::BasicBlock*, llvm::Value*> basic_block_value_map_type;

    match_compiler_t(const dfa_t& dfa, module_globals_t* globals, bool debug)
      : m_dfa(dfa), m_globals(globals), m_debug(debug) {}

    void build(llvm::Function* f)
    {
      m_head_bb = new llvm::BasicBlock("head", f);
      m_loop_beginning_bb = new llvm::BasicBlock("loop_beginning", f);
      m_state_switch_bb = new llvm::BasicBlock("state_switch", f);
      m_loop_ending_bb = new llvm::BasicBlock("loop_ending", f);
      m_tail_bb = new llvm::BasicBlock("tail", f);
      m_return_rejected_bb = new llvm::BasicBlock("return_rejected", f);
      append_head(m_head_bb, f);
      append_loop_beginning(m_loop_beginning_bb, f);
      append_state_switch(m_state_switch_bb, f);
      append_loop_ending(m_loop_ending_bb, f);
      append_tail(m_tail_bb, f);
      append_return_rejected(m_return_rejected_bb, f);

      connect_graph();
    }

  private:
    // pseudocode:
    //   state = start;
    //   curr = beg;
    void append_head(llvm::BasicBlock* bb, llvm::Function* f) {

      m_beg = llvm::CastInst::createPointerCast(f->arg_begin(), llvm::Type::Int32Ty, "", bb);
      m_end = llvm::CastInst::createPointerCast(boost::next(f->arg_begin()), llvm::Type::Int32Ty, "", bb);
      m_start = llvm::ConstantInt::get(llvm::Type::Int32Ty, m_dfa.start());

    }

    // pseudocode:
    //    default:
    //      return matched;
    void append_return_rejected(llvm::BasicBlock* bb, llvm::Function* f) {
      llvm::PHINode* last = new llvm::PHINode(m_globals->m_char_ptr_type, "matched", bb);
      for (basic_block_value_map_type::iterator i=m_last_matched_map.begin(); i!=m_last_matched_map.end(); ++i) {
        last->addIncoming(i->second, i->first);
      }
      new llvm::ReturnInst(last, bb);
    }

    // pseudocode:
    //   while (curr < end) {
    void append_loop_beginning(llvm::BasicBlock* bb, llvm::Function* f) {
      m_curr_phi = new llvm::PHINode(llvm::Type::Int32Ty, "curr", bb);
      m_curr_phi->addIncoming(m_beg, m_head_bb);
      m_state_phi = new llvm::PHINode(llvm::Type::Int32Ty, "state", bb);
      m_state_phi->addIncoming(m_start, m_head_bb);

      m_matched_phi = new llvm::PHINode(m_globals->m_char_ptr_type, "matched", bb);
      if (m_dfa.state(m_dfa.start()).accepting()) {
        m_matched_phi->addIncoming(f->arg_begin(), m_head_bb);
      } else {
        m_matched_phi->addIncoming(llvm::ConstantPointerNull::get(m_globals->m_char_ptr_type), m_head_bb);
      }

      if (m_debug) {
        new llvm::CallInst(m_globals->m_put_int, m_state_phi, "", bb);
        new llvm::CallInst(m_globals->m_put_char_ptr, m_curr_phi, "", bb);
      }

      m_loop_cond = new llvm::ICmpInst(llvm::ICmpInst::ICMP_NE, m_curr_phi, m_end, "", bb);
    }

    // pseudocode:
    //     int ch = *curr;
    //     switch (state) {
    //     case 0:
    void append_state_switch(llvm::BasicBlock* bb, llvm::Function* f) {

      if (m_debug) {
        new llvm::CallInst(m_globals->m_put_int, m_state_phi, "", bb);
        new llvm::CallInst(m_globals->m_put_char_ptr, m_curr_phi, "", bb);
      }

      llvm::Value* ch = new llvm::LoadInst(new llvm::IntToPtrInst(m_curr_phi, m_globals->m_char_ptr_type, "", bb), "", bb);

      m_last_matched_map.insert(std::make_pair(bb, m_matched_phi));
      llvm::SwitchInst* si = new llvm::SwitchInst(m_state_phi, m_return_rejected_bb, m_dfa.size(), bb);

      for (dfa_t::const_iterator i=m_dfa.begin(); i!=m_dfa.end(); ++i) {
        llvm::BasicBlock* ibb = make_symbol_switch(f, ch, i->second);
        si->addCase(llvm::ConstantInt::get(llvm::Type::Int32Ty, i->first), ibb);
      }

    }

    // pseudocode:
    //       switch(ch) {
    //       case 'a':
    llvm::BasicBlock* make_symbol_switch(llvm::Function* f, llvm::Value* ch, const dfa_state_t& state) {
      std::string bbname = "symbol_switch_" + boost::lexical_cast<std::string>(state.id());
      llvm::BasicBlock* bb = new llvm::BasicBlock(bbname, f);

      if (m_debug) {
        new llvm::CallInst(m_globals->m_put_int, m_state_phi, "", bb);
        new llvm::CallInst(m_globals->m_put_char_ptr, m_curr_phi, "", bb);
      }

      m_last_matched_map.insert(std::make_pair(bb, m_matched_phi));
      llvm::SwitchInst* si = new llvm::SwitchInst(ch, m_return_rejected_bb, state.arc_size(), bb);

      for (dfa_state_t::const_iterator i=state.begin(); i!=state.end(); ++i) {
        llvm::BasicBlock* ibb = make_transit_state(f, state, i->second);
        si->addCase(llvm::ConstantInt::get(llvm::Type::Int8Ty, i->first), ibb);
      }

      return bb;
    }

    // pseudocode:
    //         state = next_state_for_a;
    //         if (state is matched) matched = curr+1
    //         break;
    llvm::BasicBlock* make_transit_state(llvm::Function* f, const dfa_state_t& state, dfa_state_t::id_type next) {
      std::string bbname = ("trainsit_from_" + boost::lexical_cast<std::string>(state.id()) +
                            "_to_" + boost::lexical_cast<std::string>(next));
      llvm::BasicBlock* bb = new llvm::BasicBlock(bbname, f);

      m_next_state_map.insert(std::make_pair(bb, llvm::ConstantInt::get(llvm::Type::Int32Ty, next)));

      if (m_dfa.state(next).accepting()) {
        llvm::Instruction* acc = llvm::BinaryOperator::createAdd(m_curr_phi, m_globals->m_sizeof_char, "", bb);
        m_next_matched_map.insert(std::make_pair(bb, new llvm::IntToPtrInst(acc, m_globals->m_char_ptr_type, "", bb)));
      } else {
        m_next_matched_map.insert(std::make_pair(bb, m_matched_phi));
      }

      m_transit_break_bbs.push_back(bb);

      return bb;
    }

    // pseudocode:
    //     curr++;
    //   }
    void append_loop_ending(llvm::BasicBlock* bb, llvm::Function* f) {

      if (m_debug && 0) {
        new llvm::CallInst(m_globals->m_put_int, m_state_phi, "", bb);
        new llvm::CallInst(m_globals->m_put_char_ptr, m_curr_phi, "", bb);
        new llvm::CallInst(m_globals->m_put_int, llvm::ConstantInt::get(llvm::Type::Int32Ty, 9999999), "", bb);
      }

      llvm::PHINode* next_state = new llvm::PHINode(m_state_phi->getType(), "", bb);
      for (basic_block_value_map_type::iterator i=m_next_state_map.begin(); i!=m_next_state_map.end(); ++i) {
        next_state->addIncoming(i->second, i->first);
      }
      m_state_phi->addIncoming(next_state, bb);

      llvm::PHINode* next_matched = new llvm::PHINode(m_matched_phi->getType(), "", bb);
      for (basic_block_value_map_type::iterator i=m_next_matched_map.begin(); i!=m_next_matched_map.end(); ++i) {
        next_matched->addIncoming(i->second, i->first);
      }
      m_matched_phi->addIncoming(next_matched, bb);

      llvm::Instruction* newcurr
        = llvm::BinaryOperator::createAdd(m_curr_phi, m_globals->m_sizeof_char, "", bb);
      m_curr_phi->addIncoming(newcurr, bb);
    }

    // pseudocode:
    //   return matcheds[state];
    // }
    llvm::BasicBlock* append_tail(llvm::BasicBlock* bb, llvm::Function* f) {
      new llvm::ReturnInst(m_matched_phi, bb);
      return bb;
    }

    void connect_graph()
    {
      new llvm::BranchInst(m_loop_beginning_bb, m_head_bb); // enter loop
      new llvm::BranchInst(m_state_switch_bb, m_tail_bb, m_loop_cond, m_loop_beginning_bb);

      for (basic_block_list_type::const_iterator i=m_transit_break_bbs.begin();
           i!=m_transit_break_bbs.end(); ++i) {
        new llvm::BranchInst(m_loop_ending_bb, *i);
      }

      new llvm::BranchInst(m_loop_beginning_bb, m_loop_ending_bb);
    }

  private:
    const dfa_t& m_dfa;
    module_globals_t* m_globals;
    bool m_debug;

    llvm::BasicBlock* m_head_bb;
    llvm::BasicBlock* m_return_rejected_bb;
    llvm::BasicBlock* m_loop_beginning_bb;
    llvm::BasicBlock* m_loop_ending_bb;
    llvm::BasicBlock* m_state_switch_bb;
    llvm::BasicBlock* m_tail_bb;
    basic_block_list_type m_transit_break_bbs;
    basic_block_value_map_type m_next_state_map;
    basic_block_value_map_type m_next_matched_map;
    basic_block_value_map_type m_last_matched_map;
    llvm::Value* m_beg;
    llvm::Value* m_end;
    llvm::Value* m_start;
    llvm::Value* m_loop_cond;
    llvm::PHINode* m_state_phi;
    llvm::PHINode* m_curr_phi;
    llvm::PHINode* m_matched_phi;
  };

  class search_compiler_t
  {
  public:
    search_compiler_t(const dfa_t& dfa, module_globals_t* globals, llvm::Function* match_fn, bool debug)
      : m_dfa(dfa), m_globals(globals), m_match_fn(match_fn), m_debug(debug) {}

    void append_head(llvm::BasicBlock* bb) {
      llvm::Function* f = bb->getParent();
      m_beg = llvm::CastInst::createPointerCast(f->arg_begin(), llvm::Type::Int32Ty, "", bb);
      m_end = llvm::CastInst::createPointerCast(boost::next(f->arg_begin()), llvm::Type::Int32Ty, "", bb);
    }

    void append_loop_beginning(llvm::BasicBlock* bb) {
      m_curr_phi = new llvm::PHINode(llvm::Type::Int32Ty, "curr", bb);
      m_curr_phi->addIncoming(m_beg, m_head_bb);

      m_loop_cond = new llvm::ICmpInst(llvm::ICmpInst::ICMP_NE, m_curr_phi, m_end, "", bb);
    }

    void append_loop_body(llvm::BasicBlock* bb) {

      if (m_debug) {
        new llvm::CallInst(m_globals->m_put_char_ptr, m_curr_phi, "", bb);
      }

      m_match
        = new llvm::CallInst(m_match_fn,
                             new llvm::IntToPtrInst(m_curr_phi, m_globals->m_char_ptr_type, "", bb),
                             new llvm::IntToPtrInst(m_end, m_globals->m_char_ptr_type, "", bb),
                             "", bb);
      m_found_cond
        = new llvm::ICmpInst(llvm::ICmpInst::ICMP_NE,
                             m_match, llvm::ConstantPointerNull::get(m_globals->m_char_ptr_type), "", bb);
    }

    void append_loop_ending(llvm::BasicBlock* bb) {
      llvm::Instruction* newcurr
        = llvm::BinaryOperator::createAdd(m_curr_phi, m_globals->m_sizeof_char, "", bb);
      m_curr_phi->addIncoming(newcurr, bb);
    }

    void append_tail(llvm::BasicBlock* bb) {
      new llvm::ReturnInst(llvm::ConstantInt::getFalse(), bb);
    }

    void append_return_true(llvm::BasicBlock* bb) {
      new llvm::StoreInst(new llvm::IntToPtrInst(m_curr_phi, m_globals->m_char_ptr_type, "", bb),
                          forward(bb->getParent()->arg_begin(), 2), bb);
      new llvm::StoreInst(m_match,
                          forward(bb->getParent()->arg_begin(), 3), bb);
      new llvm::ReturnInst(llvm::ConstantInt::getTrue(), bb);
    }

    void connect_graph() {
      new llvm::BranchInst(m_loop_beginning_bb, m_head_bb);
      new llvm::BranchInst(m_loop_body_bb, m_tail_bb, m_loop_cond, m_loop_beginning_bb);
      new llvm::BranchInst(m_return_true_bb, m_loop_ending_bb, m_found_cond, m_loop_body_bb);
      new llvm::BranchInst(m_loop_beginning_bb, m_loop_ending_bb);
    }

    void build(llvm::Function* f) {
      m_head_bb = new llvm::BasicBlock("head", f);
      m_loop_beginning_bb = new llvm::BasicBlock("loop_beginning", f);
      m_loop_body_bb = new llvm::BasicBlock("loop_body", f);
      m_loop_ending_bb = new llvm::BasicBlock("loop_ending", f);
      m_return_true_bb = new llvm::BasicBlock("return_true", f);
      m_tail_bb = new llvm::BasicBlock("tail", f);
      append_head(m_tail_bb);
      append_loop_beginning(m_loop_beginning_bb);
      append_loop_body(m_loop_body_bb);
      append_loop_ending(m_loop_ending_bb);
      append_return_true(m_return_true_bb);
      append_tail(m_tail_bb);
      connect_graph();
    }

  private:
    const dfa_t& m_dfa;
    module_globals_t* m_globals;
    llvm::Function* m_match_fn;
    bool m_debug;

    llvm::Value* m_beg;
    llvm::Value* m_end;
    llvm::Value* m_match;
    llvm::Value* m_loop_cond;
    llvm::Value* m_found_cond;
    llvm::PHINode* m_curr_phi;

    llvm::BasicBlock* m_head_bb;
    llvm::BasicBlock* m_loop_beginning_bb;
    llvm::BasicBlock* m_loop_body_bb;
    llvm::BasicBlock* m_return_true_bb;
    llvm::BasicBlock* m_loop_ending_bb;
    llvm::BasicBlock* m_tail_bb;

  };

  class compiler_t : public matcher_t
  {
  public:
    typedef const char_t* (*match_proc_type)(const char_t* beg, const char_t* end);
    typedef const bool (*search_proc_type)(const char_t* beg, const char_t* end, const char_t** beg, const char_t** end);
    typedef std::vector<llvm::BasicBlock*> basic_block_list_type;
    typedef std::map<llvm::BasicBlock*, llvm::Value*> basic_block_value_map_type;

    compiler_t(const string_t& pattern, bool debug=false)
      : m_pattern(pattern), m_dfa(build_dfa(m_pattern)), m_debug(debug),
        m_module(new llvm::Module("test")),
        m_mp(new llvm::ExistingModuleProvider(m_module)),
        m_ee(llvm::ExecutionEngine::create(m_mp, false)),
        m_match_proc(0)
    {
      module_globals_t globals;
      llvm::Function* match_fn = build_match(&globals);
      llvm::Function* search_fn = build_search(&globals, match_fn);
      //std::ofstream hoge("hoge.bc"); llvm::WriteBitcodeToFile(m_module, hoge); hoge.close();
      m_match_proc = reinterpret_cast<match_proc_type>(m_ee->getPointerToFunction(match_fn));
      m_search_proc = reinterpret_cast<search_proc_type>(m_ee->getPointerToFunction(search_fn));
    }

    bool match(const string_t& str) const { // exact match shorthand
      const char_t* end = &(str[0]) + str.size();
      return end == m_match_proc(&(str[0]), end);
    }

    virtual const char_t* match(const char_t* beg, const char_t* end) const {
      return m_match_proc(beg, end);
    }

    virtual bool search(const char_t* beg, const char_t* end, const char_t** mb, const char_t** me) const {
      return m_search_proc(beg, end, mb, me);
    }

    const dfa_t& dfa() const { return m_dfa; }

  private:

    llvm::Function* build_match(module_globals_t* globals)
    {
      const llvm::Type* cp_type = globals->m_char_ptr_type;
      llvm::Function *f
        = llvm::cast<llvm::Function>(m_module->getOrInsertFunction
                                     ("match", cp_type, cp_type, cp_type, (llvm::Type *)0));
      match_compiler_t(m_dfa, globals, m_debug).build(f);
      return f;
    }

    llvm::Function* build_search(module_globals_t* globals, llvm::Function* match_fn)
    {
      const llvm::Type* cp_type = globals->m_char_ptr_type;
      const llvm::Type* cpp_type = globals->m_char_ptr_ptr_type;
      const llvm::Type* bool_type = llvm::PointerType::get(llvm::Type::Int32Ty);

      llvm::Function *f
        = llvm::cast<llvm::Function>(m_module->getOrInsertFunction
                                     ("search", bool_type, cp_type, cp_type, cpp_type, cpp_type,
                                      (llvm::Type *)0));
      search_compiler_t(m_dfa, globals, match_fn, m_debug).build(f);
      return f;
    }

  private:
    string_t m_pattern;
    dfa_t m_dfa;
    bool m_debug;
    llvm::Module* m_module;
    llvm::ExistingModuleProvider* m_mp;
    boost::scoped_ptr<llvm::ExecutionEngine> m_ee;
    match_proc_type m_match_proc;
    search_proc_type m_search_proc;
  };

}//namespace llre

#endif//LLRE_HPP

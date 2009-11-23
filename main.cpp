/*
 *
 */
#include "llre.hpp"

/*
 * test
 */
static bool test_regexp_match(const std::string& pattern)
{
  try {
    llre::tree_t t;
    llre::parser_t p(pattern, &t);
    p.start();
#ifdef LLRE_VERBOSE
    std::cout << "matching: " << pattern << std::endl;
    llre::dump_tree(std::cout, t);
#endif
    return true;
  } catch (const llre::bad_syntax& e) {
    //std::cout << e.what() << std::endl;
    return false;
  }
}

struct tree_tester_t
{
  std::string m_pattern;
  llre::tree_t m_tree;
  llre::parser_t m_parser;
  boost::scoped_ptr<llre::tree_functions_t> m_fn;

  tree_tester_t(const std::string& pattern)
    : m_pattern(pattern), m_tree(), m_parser(m_pattern, &m_tree)
  {
    m_parser.start();
    m_fn.reset(new llre::tree_functions_t(m_tree));
  }

  const llre::node_t* root() const { return m_tree.root(); }

  llre::node_t* choose_child(llre::node_t* n, const std::string::value_type c) const {
    switch (c) {
    case MY_T('l'): return n->left();
    case MY_T('r'): return n->right();
    case MY_T('c'): return n->child();
    default: BOOST_ASSERT(false); return 0;
    }
  }

  llre::node_t* find(const std::string& pat) const {
    llre::node_t* n = m_tree.root();
    for (std::string::const_iterator i=pat.begin(); i!=pat.end(); ++i) {
      BOOST_ASSERT(n);
      n = choose_child(n, *i);
    }
    return n;
  }

  size_t position(const llre::node_t* n) { return llre::position(m_tree, n); }

};

void test_star_tree()
{
  tree_tester_t x("ab*c");
  BOOST_ASSERT(x.find("lll")->value() == MY_T('a'));
  BOOST_ASSERT(x.find("llrc")->value() == MY_T('b'));
  BOOST_ASSERT(x.find("llr")->type() == llre::atom_type_star);
  BOOST_ASSERT(x.find("lr")->value() == MY_T('c'));
}

void test_group_tree()
{
  tree_tester_t x("a(bc)d");
  BOOST_ASSERT(x.find("lll")->value() == MY_T('a'));
  BOOST_ASSERT(x.find("llr")->type() == llre::atom_type_group);
  BOOST_ASSERT(x.find("llrcl")->value() == MY_T('b'));
  BOOST_ASSERT(x.find("llrcr")->value() == MY_T('c'));
  BOOST_ASSERT(x.find("lr")->value() == MY_T('d'));
}

void test_parse_epsilon()
{
  tree_tester_t x("a\\e");
  BOOST_ASSERT(x.find("ll")->value() == MY_T('a'));
  BOOST_ASSERT(x.find("lr")->type() == llre::atom_type_epsilon);
}

void test_group_choice_tree()
{
  tree_tester_t x("(a|b)c");
#ifdef LLRE_VERBOSE
  dump_tree(std::cout, x.m_tree);
#endif
  BOOST_ASSERT(x.find("l")->type() == llre::atom_type_cat);
  BOOST_ASSERT(x.find("ll")->type() == llre::atom_type_group);
  BOOST_ASSERT(x.find("llc")->type() == llre::atom_type_choice);
}

void test_tree_functions()
{
  // see dragonbook example 3.34
  tree_tester_t x("(a|b)*abb");

#ifdef LLRE_VERBOSE
  dump_tree(std::cout, x.m_tree);
#endif

  BOOST_ASSERT(x.find("llllccl")->value() == MY_T('a'));
  BOOST_ASSERT(x.find("llllcc")->type() == llre::atom_type_choice);
  BOOST_ASSERT(x.find("llllc")->type() == llre::atom_type_group);
  BOOST_ASSERT(x.find("llll")->type() == llre::atom_type_star);

  BOOST_ASSERT(12 == x.position(x.root()));
  BOOST_ASSERT(10 == x.position(x.find("l")));
  BOOST_ASSERT( 8 == x.position(x.find("ll")));
  BOOST_ASSERT( 9 == x.position(x.find("lr")));

  llre::node_t* n_for_pos = x.find("lll");
  llre::position_set_t fpos = to_position_set(x.m_tree, x.m_fn->firstpos(n_for_pos));
  BOOST_ASSERT(3 == fpos.size());
  BOOST_ASSERT(fpos.end() != fpos.find(0));
  BOOST_ASSERT(fpos.end() != fpos.find(1));
  BOOST_ASSERT(fpos.end() != fpos.find(5));

  llre::position_set_t lpos = to_position_set(x.m_tree, x.m_fn->lastpos(n_for_pos));
  BOOST_ASSERT(fpos.end() != fpos.find(0));

  llre::node_t* n1 = x.find("llllccl");
  llre::position_set_t fp1 = to_position_set(x.m_tree, x.m_fn->followpos(n1));
  BOOST_ASSERT(fp1.end() != fp1.find(5));
  BOOST_ASSERT(fp1.end() == fp1.find(7));

  llre::node_t* n2 = x.find("llllccr");
  llre::position_set_t fp2 = to_position_set(x.m_tree, x.m_fn->followpos(n2));
  BOOST_ASSERT(fp2.end() != fp2.find(5));
  BOOST_ASSERT(fp2.end() == fp2.find(7));

  llre::node_t* n3 = x.find("lllr");
  llre::position_set_t fp3 = to_position_set(x.m_tree, x.m_fn->followpos(n3));
  BOOST_ASSERT(fp3.end() == fp3.find(5));
  BOOST_ASSERT(fp3.end() != fp3.find(7));

}

void test_comparable()
{
  typedef std::vector<int> int_vector_type;
  int_vector_type a, b;
  bool vec_pred = a < b;
  typedef std::set<int> int_set_type;
  int_set_type c, d;
  bool set_pred = c < d;
  llre::ignore_unused_variable_warning(vec_pred);
  llre::ignore_unused_variable_warning(set_pred);
}

void test_tree_builder()
{
  llre::tree_t tree;
  std::string pattern("(a|b)*abb");
  llre::parser_t(pattern, &tree).start();
  llre::dfa_t dfa = llre::dfa_builder_t(tree).dfa();

#ifdef LLRE_VERBOSE
  dump_dfa(std::cout, dfa);
#endif
  BOOST_ASSERT(dfa.size() == 4);
  const llre::dfa_state_t& start = dfa.state(dfa.start());
  BOOST_ASSERT(2 == start.arc_size());
  BOOST_ASSERT(start.find('a')->second != start.find('b')->second);

  size_t found_accepting = 0;
  for (llre::dfa_t::const_iterator i=dfa.begin(); i != dfa.end(); ++i) {
    if (i->second.accepting()) {
      found_accepting++;
      BOOST_ASSERT(i->second.arc_size() == 2);
      BOOST_ASSERT(i->second.find('a')->second != i->second.find('b')->second);
    }
  }

  BOOST_ASSERT(1 == found_accepting);
}

template<class T>
void test_basic_search(T& target, const std::string& str, bool found,
                       size_t boff=0, size_t eoff=0)
{
  const char* b = &(str[0]);
  const char* e = &(str[str.size()]);
  const char* mb = 0;
  const char* me = 0;
  bool f = target.search(b, e, &mb, &me);
  BOOST_ASSERT(f == found);
  if (!found) { return; }

  BOOST_ASSERT(b + boff == mb);
  BOOST_ASSERT(b + eoff == me);
}

void test_interpreter_search(llre::interpreter_t& interp, const std::string& str, bool found,
                             size_t boff=0, size_t eoff=0)
{
  test_basic_search(interp, str, found, boff, eoff);
}

void test_interpreter_hello()
{
  llre::interpreter_t interp("(a|b)*abb");
  //dump_dfa(std::cout, interp.dfa());
  BOOST_ASSERT( interp.match("abb"));
  BOOST_ASSERT( interp.match("aabb"));
  BOOST_ASSERT( interp.match("ababb"));
  BOOST_ASSERT( interp.match("aaabb"));
  BOOST_ASSERT( interp.match("bbabb"));
  BOOST_ASSERT(!interp.match(""));
  BOOST_ASSERT(!interp.match("a"));
  BOOST_ASSERT(!interp.match("ab"));
  BOOST_ASSERT(!interp.match("bb"));
  BOOST_ASSERT(!interp.match("abbc"));
  BOOST_ASSERT(!interp.match("cabb"));

  test_interpreter_search(interp, "abb", true, 0, 3);
  test_interpreter_search(interp, "aabb", true, 0, 4);
  test_interpreter_search(interp, "abbc", true, 0, 3);
  test_interpreter_search(interp, "cabb", true, 1, 4);
  test_interpreter_search(interp, "cabbc", true, 1, 4);
  test_interpreter_search(interp, "cac", false);
}

bool test_interpreter_match_one(const std::string& pattern, const std::string& str)
{
  llre::interpreter_t interp(pattern);
  return interp.match(str);
}

void test_interpreter_match_misc()
{
  BOOST_ASSERT( test_interpreter_match_one("a\\nb", "a\nb"));
  BOOST_ASSERT(!test_interpreter_match_one("a\\nb", "a\rb"));
  BOOST_ASSERT( test_interpreter_match_one("a\\eb", "ab"));
  BOOST_ASSERT(!test_interpreter_match_one("a\\eb", "aeb"));
}

void test_compiler_match(const llre::compiler_t& compiler, const llre::char_t* str, bool ma, size_t off=0)
{
  const llre::char_t* ret = compiler.match(str, str+strlen(str));
  BOOST_ASSERT((0 != ret) == ma);
  BOOST_ASSERT((!ma) || size_t(ret - str) == off);
}

void test_compiler_search_hello(const llre::compiler_t& compiler)
{
  const llre::char_t* beg = 0;
  const llre::char_t* end = 0;
  std::string str0 = "hello";
  bool found0 = compiler.search(&(str0[0]), &(str0[str0.size()]), &beg, &end);
  BOOST_ASSERT(!found0);
  std::string str1 = "cabbc";
  bool found1 = compiler.search(&(str1[0]), &(str1[str1.size()]), &beg, &end);
  BOOST_ASSERT(found1);
}

void test_compiler_search(llre::compiler_t& compiler, const std::string& str, bool found,
                             size_t boff=0, size_t eoff=0)
{
  test_basic_search(compiler, str, found, boff, eoff);
}

void test_compiler_hello()
{
  // FIXME: unity testcases with interp
  llre::compiler_t compiler("(a|b)*abb");
  //dump_dfa(std::cout, compiler.dfa());
  test_compiler_match(compiler, "babb", true, strlen("babb"));
  test_compiler_match(compiler, "a", false);
  test_compiler_match(compiler, "hoge", false);
  test_compiler_match(compiler, "babbb", true, strlen("babb"));
  test_compiler_match(compiler, "babbc", true, strlen("babb"));
  test_compiler_search_hello(compiler);
  test_compiler_search(compiler, "abb", true, 0, 3);
  test_compiler_search(compiler, "aabb", true, 0, 4);
  test_compiler_search(compiler, "abbc", true, 0, 3);
  test_compiler_search(compiler, "cabb", true, 1, 4);
  test_compiler_search(compiler, "cabbc", true, 1, 4);
  test_compiler_search(compiler, "cac", false);
}

void test_parser()
{
  BOOST_ASSERT( test_regexp_match("a"));
  BOOST_ASSERT( test_regexp_match("ab"));
  BOOST_ASSERT( test_regexp_match("abc"));
  BOOST_ASSERT( test_regexp_match("a*"));
  BOOST_ASSERT( test_regexp_match("a*b"));
  BOOST_ASSERT( test_regexp_match("ab*cd"));
  BOOST_ASSERT( test_regexp_match("a|b"));
  BOOST_ASSERT( test_regexp_match("ab|cd"));
  BOOST_ASSERT( test_regexp_match("ab|cd*"));
  BOOST_ASSERT( test_regexp_match("(a)"));
  BOOST_ASSERT( test_regexp_match("(ab)"));
  BOOST_ASSERT( test_regexp_match("((b))"));
  BOOST_ASSERT( test_regexp_match("a(b)c"));
  BOOST_ASSERT( test_regexp_match("aa(b)cc"));
  BOOST_ASSERT( test_regexp_match("(a(b)c)"));
  BOOST_ASSERT( test_regexp_match("(a(bcd)*e)"));
  BOOST_ASSERT( test_regexp_match("\\("));
  BOOST_ASSERT( test_regexp_match("\\&"));
  BOOST_ASSERT(!test_regexp_match("\\"));
  BOOST_ASSERT(!test_regexp_match(""));
  BOOST_ASSERT(!test_regexp_match("&"));
  BOOST_ASSERT(!test_regexp_match("("));
  BOOST_ASSERT(!test_regexp_match("*"));
  BOOST_ASSERT(!test_regexp_match("()"));
  BOOST_ASSERT(!test_regexp_match("|"));
  BOOST_ASSERT(!test_regexp_match("a|"));
  BOOST_ASSERT(!test_regexp_match("|a"));

}

void run_test()
{
  test_compiler_hello();
  test_interpreter_hello();
  test_interpreter_match_misc();
  test_tree_builder();
  test_tree_functions();
  test_group_choice_tree();
  test_star_tree();
  test_group_tree();
  test_parse_epsilon();
  test_parser();
}

int main(int argc, char* argv[])
{
  llre::ignore_unused_variable_warning(argc);
  llre::ignore_unused_variable_warning(argv);
  run_test();
  return 0;
}

/*
 *
 */
#include "llre.hpp"
#include <boost/scoped_ptr.hpp>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>

class application_error : public std::exception
{
public:
  application_error(const std::string& msg="") : m_what(msg) {}
  ~application_error() throw() {}
  const char* what() const throw() { return m_what.c_str(); }
private:
  std::string m_what;
};

/* scope guard for open()/close() */
class file_t
{
public:
  file_t(const std::string& filename) : m_fd(open(filename.c_str(), O_RDONLY, 644)) {
    if (m_fd <= 0) { throw application_error(std::string("can not open file:") + filename); }
  }

  ~file_t() {
    close(m_fd);
  }

  int fd() const { return m_fd; }

  size_t size() const {
    struct stat s;
    fstat(m_fd, &s);
    return s.st_size;
  }

private:
  int m_fd;
};

/* scope guard for mmap()/munmap() */
class mmap_t
{
public:
  mmap_t(int fd, size_t len) : m_fd(fd), m_len(len), m_addr(mmap(0, m_len, PROT_READ, MAP_FILE, fd, 0)) {
    if (!m_addr) { throw application_error("can not map the file"); }
  }

  ~mmap_t() {
    munmap(m_addr, m_len);
  }

  const void* addr() const { return m_addr; }
  size_t len() const { return m_len; /* XXX: can not handle huge file */ }

private:
  int m_fd;
  size_t m_len;
  void* m_addr;
};

static const char ASCII_LF = 0x0a;
static const char ASCII_CR = 0x0d;

bool is_eol(const char* ptr) {
  return (ptr[0] ==ASCII_LF); // FIXME: handle various EOL types
}

typedef llre::basic_range_t<const char*> array_range_t;

array_range_t find_line_range(const array_range_t& limit, const array_range_t& seed)
{
  if (seed.empty()) { return seed; } // special case.

  const char* head = seed.begin();
  const char* tail = seed.end()-1;

  while ((limit.begin() < head) && !is_eol(head-1)) { --head; }
  while ((tail+1 < limit.end()) && !is_eol(tail+1)) { ++tail; }
  return array_range_t(head, tail+1);
}

class llgrep_t
{
public:

  void search_file(const std::string& filename) {
    file_t file(filename);
    mmap_t map(file.fd(), file.size());

    const char* beg = reinterpret_cast<const char*>(map.addr());
    const char* end = beg + map.len();
    const char* cur = beg;
    while (cur < end) {
      const char* mbeg = 0;
      const char* mend = 0;
      bool found = m_matcher->search(cur, end, &mbeg, &mend);
      if (!found) {
        break;
      }

      m_nfound++;
      array_range_t line = find_line_range(array_range_t(beg, end), array_range_t(mbeg, mend));
      m_out << filename << ":" << line << std::endl;
      BOOST_ASSERT(cur < mend); // should have progress
      cur = mend;
    }
  }

  size_t nfound() const { return m_nfound; }

  llgrep_t(int argc, char* argv[], std::ostream& out)
    : m_out(out), m_nfound(0) {
    if (argc < 3) { throw application_error("short of argument!"); }
    m_pattern = argv[1];
    m_matcher.reset(new llre::compiler_t(m_pattern));
    for (int i=2; i<argc; ++i) {
      search_file(argv[i]);
    }
  }

private:
  std::string m_pattern;
  boost::scoped_ptr<llre::matcher_t> m_matcher;
  std::ostream& m_out;
  size_t m_nfound;
};

int main(int argc, char* argv[])
{
  llgrep_t app(argc, argv, std::cout);
  return (0 < app.nfound()) ? 0 : 1;
}

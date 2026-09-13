// Untrusted encoder. The separate run checker must accept its output.
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
int main(int argc, char** argv) { try {
  if (argc != 5) throw std::runtime_error("usage: pack_runs lengths edges runs offsets");
  std::ifstream ls(argv[1], std::ios::binary), es(argv[2], std::ios::binary);
  std::ofstream rs(argv[3], std::ios::binary), os(argv[4], std::ios::binary);
  if (!ls || !es || !rs || !os) throw std::runtime_error("open failed");
  uint32_t n; uint64_t off = 0, edges = 0, records = 0;
  while (ls.read(reinterpret_cast<char*>(&n), 4)) {
    os.write(reinterpret_cast<char*>(&off), 8);
    std::vector<uint16_t> cols(n);
    es.read(reinterpret_cast<char*>(cols.data()), 2ULL*n);
    if (!es) throw std::runtime_error("short edge stream");
    for (uint32_t i = 0; i < n;) {
      uint32_t j = i + 1;
      while (j < n && cols[j] == cols[i] && j-i < 65535) ++j;
      uint32_t run = ((j-i) << 16) | cols[i];
      rs.write(reinterpret_cast<char*>(&run), 4); ++off; i = j;
    }
    edges += n; ++records;
  }
  if (!ls.eof() || es.peek() != EOF || !rs || !os)
    throw std::runtime_error("bad stream length or output");
  std::cout << "ENCODED " << records << " records, " << edges << " edges, " << off << " runs\n";
  return 0;
} catch (const std::exception& e) { std::cerr << e.what() << '\n'; return 1; } }

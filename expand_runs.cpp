// Untrusted diagnostic decoder, used ONLY for comparison with check_paths.cpp.
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
using I=__int128_t;
#pragma pack(push,1)
struct Node { I v,uend; int64_t cost; uint64_t off; int32_t len,r,row,col,base,kind; };
#pragma pack(pop)
static_assert(sizeof(Node)==72);
void require(bool b){if(!b)throw std::runtime_error("bad run encoding");}
int main(int argc,char**argv){try{
  require(argc==5);
  std::ifstream f(argv[1],std::ios::binary),g(argv[2],std::ios::binary);
  std::ofstream nf(argv[3],std::ios::binary),eg(argv[4],std::ios::binary);
  require(f.good()&&g.good()&&nf.good()&&eg.good());
  Node x;uint64_t runs=0,edges=0;
  while(f.read(reinterpret_cast<char*>(&x),sizeof(x))){
    if(x.kind>=2){
      require(x.off==runs&&x.len>=0);x.off=edges;int left=x.len;
      while(left){
        uint32_t c;require(bool(g.read(reinterpret_cast<char*>(&c),4)));
        uint16_t col=c&65535;int len=c>>16;require(len>0&&len<=left);
        std::vector<uint16_t> v(len,col);
        eg.write(reinterpret_cast<char*>(v.data()),2ULL*len);
        ++runs;edges+=len;left-=len;
      }
    }
    nf.write(reinterpret_cast<char*>(&x),sizeof(x));
  }
  require(f.eof()&&g.peek()==EOF&&nf.good()&&eg.good());
  std::cout<<"EXPANDED "<<runs<<" runs to "<<edges<<" edges\n";return 0;
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}

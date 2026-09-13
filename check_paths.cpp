// Exact accelerator for the path-size part of verify_certificate.py.
// No floating-point arithmetic; every integer operation is overflow checked.
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
#include <limits>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
using I=__int128_t;
#pragma pack(push,1)
struct Node { I v,uend; int64_t cost; uint64_t off; int32_t len,r,row,col,base,kind; };
struct Result { I start,margin; int32_t depth; };
#pragma pack(pop)
static_assert(sizeof(Node)==72);
static_assert(sizeof(Result)==36);
I add(I a,I b){I c;if(__builtin_add_overflow(a,b,&c))throw std::runtime_error("integer addition overflow");return c;}
I mul(I a,I b){I c;if(__builtin_mul_overflow(a,b,&c))throw std::runtime_error("integer multiplication overflow");return c;}
void require(bool b){if(!b)throw std::runtime_error("invalid proof path");}
int main(int argc,char**argv){try{
 if(argc!=5)throw std::runtime_error("usage: check_paths nodes.bin edges.bin result.bin edge_width");
 int ew=std::stoi(argv[4]);require(ew==2||ew==4);
 std::ifstream f(argv[1],std::ios::binary|std::ios::ate),e(argv[2],std::ios::binary|std::ios::ate);
 require(f.good()&&e.good()); auto nb=f.tellg(),eb=e.tellg();require(nb%sizeof(Node)==0&&eb%ew==0);
 size_t n=nb/sizeof(Node),ne=eb/ew;require(n<size_t(std::numeric_limits<int32_t>::max()));std::vector<Node>a(n);std::vector<Result>out(n);std::vector<bool>unc(n,false);
 f.seekg(0);f.read(reinterpret_cast<char*>(a.data()),nb);require(f.good());
 int fd=open(argv[2],O_RDONLY);require(fd>=0);auto ep=mmap(nullptr,size_t(eb),PROT_READ,MAP_PRIVATE,fd,0);require(ep!=MAP_FAILED);madvise(ep,size_t(eb),MADV_SEQUENTIAL);
 auto edges=static_cast<const uint32_t*>(ep);auto cols=static_cast<const uint16_t*>(ep);
 int maxr=0;for(auto &x:a){require(x.r>=0);if(x.r>maxr)maxr=x.r;}
 std::vector<int>mr(maxr+1,0),mc(maxr+1,0);for(auto &x:a){require(x.row>=0&&x.col>=0);if(x.row>mr[x.r])mr[x.r]=x.row;if(x.col>mc[x.r])mc[x.r]=x.col;}
 int current=-1,width=0;std::vector<int32_t>grid;
 uint64_t total=0;const I scale=1000000000000000000LL;
 for(size_t ix=0;ix<n;ix++){
  auto&x=a[ix];
  if(x.r!=current){require(x.r==current+1);current=x.r;width=mc[current]+1;grid.assign(size_t(mr[current]+1)*width,-1);}
  size_t slot=size_t(x.row)*width+x.col;require(slot<grid.size()&&grid[slot]<0);
  require(x.v>0&&x.cost>0&&x.kind>=0&&x.kind<=3&&x.len>=0);int dep=0;I sum=0,req=0;
  if(x.kind>=2){require(x.off<=ne&&uint64_t(x.len)<=ne-x.off&&x.uend>0);for(int k=0;k<x.len;k++){
    uint32_t ci;
    if(ew==4)ci=edges[x.off+k];else{int col=cols[x.off+k];require(x.row-k>=0&&col<width);auto got=grid[size_t(x.row-k)*width+col];require(got>=0);ci=got;}
    require(ci<ix);auto&c=a[ci];require(c.r==x.r&&c.row==x.row-k&&(c.row<x.row||(c.row==x.row&&c.col<x.col)));
    sum=add(sum,mul(c.cost,scale));I need=add(c.v,sum);if(need>req)req=need;if(out[ci].depth+1>dep)dep=out[ci].depth+1;
   }
   require(x.uend>req&&x.uend>sum);total+=x.len;
  }
  I start=x.kind>=2?x.uend-sum:x.v;
  if(x.kind==0)unc[ix]=true;
  else if(x.kind==1||x.kind==3){
   if(x.base>=0){require(size_t(x.base)<ix&&unc[x.base]&&a[x.base].r==x.r);require(a[x.base].row==(x.kind==1?x.row:x.row-x.len));require(start>a[x.base].v);if(out[x.base].depth+1>dep)dep=out[x.base].depth+1;}
   else require(x.base==-1);unc[ix]=true;
  }
  out[ix]={start,x.kind>=2?x.uend-req:I(0),dep};grid[slot]=int32_t(ix);
 }
 require(total==ne);std::ofstream g(argv[3],std::ios::binary);g.write(reinterpret_cast<const char*>(out.data()),n*sizeof(Result));require(g.good());
 std::cout<<"PASS "<<n<<" nodes, "<<total<<" path edges\n";return 0;
}catch(const std::exception&ex){std::cerr<<ex.what()<<"\n";return 1;}}

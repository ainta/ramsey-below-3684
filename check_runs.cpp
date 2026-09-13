// Independent exact checker: dynamic column segment trees, no expanded paths.
// The analytic and graph-semantic obligations are outside this accelerator.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <vector>
using I = __int128_t;
#pragma pack(push,1)
struct Node { I v,uend; int64_t cost; uint64_t off; int32_t len,r,row,col,base,kind; };
struct Result { I start,margin; int32_t depth; };
#pragma pack(pop)
static_assert(sizeof(Node)==72 && sizeof(Result)==36);
void require(bool b) { if (!b) throw std::runtime_error("invalid run certificate"); }
I add(I a, I b) { I c; if (__builtin_add_overflow(a,b,&c)) throw std::runtime_error("addition overflow"); return c; }
I mul(I a, I b) { I c; if (__builtin_mul_overflow(a,b,&c)) throw std::runtime_error("multiplication overflow"); return c; }
struct Summary { I cost=0, need=0; int32_t depth=0, count=0; };
Summary join(Summary a, Summary b) {
  if (!a.count) return b;
  if (!b.count) return a;
  require(a.count <= INT32_MAX-b.count);
  return {add(a.cost,b.cost), std::max(a.need,add(a.cost,b.need)),
          std::max(a.depth,b.depth), a.count+b.count};
}
struct Column {
  int size; std::vector<Summary> tree;
  explicit Column(int s):size(s),tree(2ULL*s) {}
  void put(int row, Summary s) {
    int k=size+row; require(tree[k].count==0); tree[k]=s;
    for (k/=2;k;k/=2) tree[k]=join(tree[2*k+1],tree[2*k]);
  }
  Summary get(int lo, int hi) const {
    Summary low, high;
    for (lo+=size,hi+=size+1;lo<hi;lo/=2,hi/=2) {
      if (lo&1) low=join(tree[lo++],low);
      if (hi&1) high=join(high,tree[--hi]);
    }
    return join(high,low);
  }
};
int main(int argc,char**argv) { try {
  require(argc==5);
  std::ifstream f(argv[1],std::ios::binary|std::ios::ate), e(argv[2],std::ios::binary|std::ios::ate);
  require(f.good()&&e.good()); auto nb=f.tellg(), eb=e.tellg();
  require(nb>=0&&eb>=0&&nb%sizeof(Node)==0&&eb%4==0);
  size_t n=nb/sizeof(Node), nr=eb/4; require(n<size_t(INT32_MAX));
  std::vector<Node> a(n); std::vector<Result> out(n); std::vector<bool> unc(n,false);
  std::vector<uint32_t> runs(nr);
  f.seekg(0);f.read(reinterpret_cast<char*>(a.data()),nb);require(f.good());
  e.seekg(0);e.read(reinterpret_cast<char*>(runs.data()),eb);require(e.good());
  int maxr=0;
  for(auto&x:a){require(x.r>=0&&x.r<10000&&x.row>=0&&x.row<=65535&&x.col>=0&&x.col<=65535);maxr=std::max(maxr,x.r);}
  std::vector<int> mr(maxr+1),mc(maxr+1);
  for(auto&x:a){mr[x.r]=std::max(mr[x.r],x.row);mc[x.r]=std::max(mc[x.r],x.col);}
  int current=-1,size=0; std::vector<Column> columns;
  uint64_t used=0,expanded=0; const I scale=1000000000000000000LL;
  for(size_t ix=0;ix<n;++ix) {
    auto&x=a[ix];
    if(x.r!=current){
      require(x.r==current+1);current=x.r;size=1;while(size<=mr[current])size*=2;
      columns.clear(); columns.reserve(mc[current]+1);
      for(int j=0;j<=mc[current];++j)columns.emplace_back(size);
    }
    require(x.v>0&&x.cost>0&&x.kind>=0&&x.kind<=3&&x.len>=0);
    Summary path; int dep=0;
    if(x.kind>=2){
      require(x.off==used&&x.uend>0&&x.len<=x.row);
      int consumed=0;
      while(consumed<x.len){
        require(used<nr);uint32_t code=runs[used++];int len=code>>16,col=code&65535;
        require(len>0&&len<=x.len-consumed&&col<=mc[current]);
        int hi=x.row-consumed,lo=hi-len+1;
        require(lo>=0&&(hi<x.row||col<x.col));
        Summary part=columns[col].get(lo,hi);
        require(part.count==len); // Every referenced row was checked BEFORE this node.
        path=join(path,part); consumed+=len;
      }
      require(path.count==x.len&&x.uend>path.need&&x.uend>path.cost);
      expanded+=x.len;dep=path.depth;
    }
    I start=x.kind>=2?x.uend-path.cost:x.v;
    if(x.kind==0)unc[ix]=true;
    else if(x.kind==1||x.kind==3){
      if(x.base>=0){
        require(size_t(x.base)<ix&&unc[x.base]&&a[x.base].r==x.r);
        require(a[x.base].row==(x.kind==1?x.row:x.row-x.len));require(start>a[x.base].v);
        require(out[x.base].depth<INT32_MAX);dep=std::max(dep,out[x.base].depth+1);
      } else require(x.base==-1);
      unc[ix]=true;
    }
    out[ix]={start,x.kind>=2?x.uend-path.need:I(0),dep};
    require(dep<INT32_MAX);I cost=mul(x.cost,scale);
    columns[x.col].put(x.row,{cost,add(cost,x.v),dep+1,1});
  }
  require(used==nr&&expanded==std::stoull(argv[4]));
  std::ofstream g(argv[3],std::ios::binary);g.write(reinterpret_cast<const char*>(out.data()),n*sizeof(Result));require(g.good());
  std::cout<<"PASS "<<n<<" nodes, "<<nr<<" runs, "<<expanded<<" implied edges\n";
  return 0;
} catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;} }

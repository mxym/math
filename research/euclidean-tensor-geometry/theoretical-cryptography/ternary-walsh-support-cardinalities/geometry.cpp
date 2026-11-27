#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <vector>
using U=__uint128_t;

template<int D> struct Geometry {
  static constexpr int N=D==4?81:27;
  int digit[N][D]{};
  int midpoint[N][N]{};
  int diff[N][N]{};
  int basis[D+1]{};
  std::vector<int> rest;
  Geometry() {
    for(int x=0;x<N;++x)for(int y=x,i=0;i<D;++i,y/=3)digit[x][i]=y%3;
    for(int i=0,p=1;i<D;++i,p*=3)basis[i+1]=p;
    for(int x=0;x<N;++x){
      bool in=false;for(int y:basis)if(x==y)in=true;if(!in)rest.push_back(x);
      for(int y=0;y<N;++y){
        int f=0,g=0;
        for(int i=0,p=1;i<D;i++,p*=3){
          int a=digit[x][i],b=digit[y][i];
          midpoint[x][y]+=p*((6-a-b)%3);
          f+=p*((3+a-b)%3); g+=p*((3+b-a)%3);
        }
        diff[x][y]=f<g?f:g;
      }
    }
  }
};
struct Counts{uint64_t seen{},diff{},mid{},both{};auto operator<=>(const Counts&)const=default;};
template<int D>struct BitPass{
  Geometry<D> H;
  static constexpr int K=D==4?11:8;
  int pts[K]{};
  std::array<Counts,K+1> out{};
  static void put(U x,U& once,U& many){many|=once&x;once=(once|x)&~many;}
  void scan(int k,int j,U s,U d1,U d2,U m1,U m2){
    if(k>=(D==4?9:6)){
      auto& t=out[k];
      bool d=d1==0,m=(m1&~s)==0;
      t.seen++;t.diff+=d;t.mid+=m;t.both+=d&&m;
    }
    if(k==K)return;
    for(int l=j;l<int(H.rest.size());++l){
      int y=H.rest[l];U a=d1,b=d2,c=m1,d=m2;
      for(int i=0;i<k;++i){
        put(U(1)<<H.diff[pts[i]][y],a,b);put(U(1)<<H.midpoint[pts[i]][y],c,d);
      }
      pts[k]=y;
      scan(k+1,l+1,s|(U(1)<<y),a,b,c,d);
    }
  }
  void run(){
    U s=0,a=0,b=0,c=0,d=0;
    for(int i=0;i<=D;++i){
      int x=pts[i]=H.basis[i];
      s|=U(1)<<x;
      for(int j=0;j<i;++j){
        put(U(1)<<H.diff[x][pts[j]],a,b);put(U(1)<<H.midpoint[x][pts[j]],c,d);
      }
    }
    scan(D+1,0,s,a,b,c,d);
    for(int k=(D==4?9:6);k<=K;++k){
      auto t=out[k];printf("d=%d r=%d total=%llu diff=%llu midpoint=%llu joint=%llu\n",D,k,
        (unsigned long long)t.seen,(unsigned long long)t.diff,(unsigned long long)t.mid,(unsigned long long)t.both);
      assert(t.both==0);
    }
  }
};

int ternary(int a,int b,bool mid){
 int z=0;
 for(int w=1;w<81;w*=3,a/=3,b/=3)z+=w*((6-a%3+(mid?-b%3:b%3))%3);
 return z;
}
int ld(U a){return (uint64_t)a?std::countr_zero((uint64_t)a):64+std::countr_zero((uint64_t)(a>>64));}

// Independent four-dimensional pass. Enumerate combinations by their colexicographic
// masks rather than recursive growing sets. Begin with basis-midpoint certificates;
// then actual integer midpoint multiplicities, then actual difference multiplicities.
void independent4(int k,uint64_t total){
  std::array<int,76> q{};
  const int base[]={0,1,3,9,27};
  bool in[81]{};for(int a:base)in[a]=true;
  for(int a=0,j=0;a<81;++a)if(!in[a])q[j++]=a;
  int vals[81][81]{}, dirs[81][81]{};
  int indexes[81]{};for(int &v:indexes)v=-1;int cnt=0;
  for(int i=0;i<5;++i)for(int j=0;j<i;++j)indexes[ternary(base[i],base[j],true)]=cnt++;
  int with_basis[81]{}, with_extra[81][81]{};
  for(int a=0;a<81;++a){
    if(indexes[a]>=0)with_basis[a]|=1<<indexes[a];
    for(int b:base){
      const int m=ternary(a,b,true);
      if(indexes[m]>=0)with_basis[a]|=1<<indexes[m];
    }
    for(int b=0;b<81;++b){
      vals[a][b]=ternary(a,b,true);
      int d0=ternary(a,b,false),d1=ternary(b,a,false);
      dirs[a][b]=d0<d1?d0:d1;
      with_extra[a][b]=indexes[vals[a][b]]<0?0:1<<indexes[vals[a][b]];
    }
  }
  uint64_t seen=0, covered=0, mid=0, joint=0;
  int extra=k-5,pts[11];for(int j=0;j<5;++j)pts[j]=base[j];
  U first=(U(1)<<extra)-1, limit=U(1)<<76;
  for(U mask=first;mask<limit;){
    int valid=0,xpos=5;
    for(U s=mask;s;s&=s-1){
      const int x=q[ld(s)];
      valid|=with_basis[x];
      for(int j=5;j<xpos;++j)valid|=with_extra[x][pts[j]];
      pts[xpos++]=x;
    }
    ++seen;
    if(valid==1023){
      ++covered;
      bool occupied[81]{};int count[81]{};
      for(int i=0;i<k;++i){occupied[pts[i]]=true;for(int j=0;j<i;++j)count[vals[pts[i]][pts[j]]]++;}
      bool good=true;for(int i=0;i<81;++i)if(count[i]==1&&!occupied[i])good=false;
      if(good){
        ++mid;
        int diffs[81]{};
        for(int i=0;i<k;++i)for(int j=0;j<i;++j)diffs[dirs[pts[i]][pts[j]]]++;
        for(int n:diffs)if(n==1)good=false;
        if(good)++joint;
      }
    }
    const U bit=mask&(-mask), next=mask+bit;
    mask=next|(((next^mask)>>2)>>ld(bit));
  }
  printf("independent d=4 r=%d total=%llu basis-midpoint=%llu midpoint=%llu joint=%llu\n",k,
    (unsigned long long)seen,(unsigned long long)covered,(unsigned long long)mid,(unsigned long long)joint);
  assert(seen==total&&joint==0);
}

int main(){
  BitPass<3> a;a.run();
  BitPass<4> b;b.run();
  assert(b.out[9].seen==1282975&&b.out[10].seen==18474840&&b.out[11].seen==218618940);
  independent4(10,18474840);
  independent4(11,218618940);
  // Negative controls: a genuine 3D support of size 9 must pass both tests;
  // a simplex of four points must fail each test.
  Geometry<3> g;
  auto check=[&](std::vector<int> pts){
    bool occupied[27]{};int m[27]{},d[27]{};
    for(int i=0;i<int(pts.size());++i){
      occupied[pts[i]]=1;
      for(int j=0;j<i;++j){m[g.midpoint[pts[i]][pts[j]]]++;d[g.diff[pts[i]][pts[j]]]++;}
    }
    bool a=true,b=true;
    for(int i=0;i<27;++i){if(d[i]==1)a=false;if(!occupied[i]&&m[i]==1)b=false;}
    return std::array<bool,2>{a,b};
  };
  assert((check({0,1,3,9})==std::array<bool,2>{false,false}));
  assert((check({0,1,3,9,2,4,5,10,11})==std::array<bool,2>{true,true}));
  puts("PASS geometric controls.");
}

#include "plane.hpp"
static bits tr[1024][1024]; // forbidden z for triple (p,r,z), relative to H infinity
bits edge[1024];int S[32];long long nodes,lim;int best;bool hit;
inline bool add(bits&C,int p,int cnt){C.reset(p);C&=edge[p];
 for(int j=0;j<cnt;j++)C&=~tr[p][S[j]];
 for(int j=0;j<cnt;j++)for(int k=0;k<j;k++){int d=p^S[j],e=p^S[k];for(int a=1;a<4;a++)for(int b=1;b<4;b++)C.reset(p^M[a][d]^M[b][e]);}
 for(int k=0;k<num;k++){int b=fval[p][k];int h=--rem[k][b];if(!h)C&=~pencils[k][b];assert(h>=0);}
 S[cnt]=p;return 1;}
void undo(int p){for(int k=0;k<num;k++)++rem[k][fval[p][k]];}
bool rec(bits C,int cnt){best=max(best,cnt);if(cnt==goal){cout<<"FOUND";for(int x:A)cout<<" "<<x;for(int i=0;i<cnt;i++)cout<<" "<<1024+S[i];cout<<endl;return false;}
 assert(nodes<LLONG_MAX);++nodes;if(C.count()<goal-cnt)return false;
 // Greedy coloring of the fixed pair graph (all constraints already forced by C).
 bits U=C;array<int,1024> order,col;int id=0;for(int c=1;U.any();c++){
  bits V=U;while(V.any()){int p=V._Find_first();V&=~edge[p];V.reset(p);U.reset(p);order[id]=p;col[id++]=c;}}
 for(int i=id-1;i>=0;i--){if(col[i]+cnt<goal)return false;int p=order[i];C.reset(p);bits Q=C;add(Q,p,cnt);if(rec(Q,cnt+1))return true;undo(p);}return false;}
int main(int ac,char**av){init();initG();hn=atoi(av[1]);assert(ac==3);int target=atoi(av[2]);int si=0;string l;
 while(getline(cin,l)){++si;istringstream iss(l);A.clear();int z;while(iss>>z)A.push_back(z);goal=target-A.size();setup();
  for(int t=0;t<N;t++)if(allow[t]){bits b;for(int a:A)for(int i=0;i<4;i++)for(int j=0;j<4;j++)b.set(M[i][a]^M[j][t]);for(int p=0;p<N;p++){auto&h=tr[p][t^p];h.reset();for(int j=b._Find_first();j<1024;j=b._Find_next(j))h.set(p^j);}}
  for(int o=0;o<orbs.size();o++){int q=orbs[o][0];bits C;C.set();for(int i=0;i<N;i++){edge[i].reset();for(int j=0;j<N;j++)if(edgeO[i^j]>=o)edge[i].set(j);}
   for(int i=0;i<num;i++)for(int k=0;k<4;k++)rem[i][k]=cap[i];add(C,0,0);add(C,q,1);
   // Every future pair must also avoid a forbidden triple with 0 or the fixed q.
   for(int i=0;i<N;i++)if(C[i])edge[i]&=~(tr[0][i]|tr[q][i]);
   nodes=0;best=2;bool ok=rec(C,2);assert(!ok);cout<<"BRANCH "<<hn<<" "<<target<<" "<<si<<" "<<o<<" "<<orbs.size()<<" "<<nodes<<endl;
  }
 }}

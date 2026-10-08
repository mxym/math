#include <bits/stdc++.h>
using namespace std;
using ll=long long;
struct Edge {int a,b;};
const vector<Edge> F={{-2,-1},{-2,0},{-2,1},{-1,-1},{-1,0},{-1,1},
                      {0,-1},{0,1},{1,-1},{1,0},{1,1},{2,-1},{2,0},{2,1}};
int norm(int a,int b){return a*a+2*b*b;}
int positive_mod(int a,int q){int r=a%q;return r<0?r+q:r;}
struct Cert {int q,sx,sy;vector<int> steps;};
vector<int> path(int z,const vector<int>&parent,const vector<int>&moves){
 vector<int> w;
 while(parent[z]!=-1){w.push_back(moves[z]);z=parent[z];}
 reverse(w.begin(),w.end());return w;
}
Cert produce(int q){
 vector<uint8_t> allowed(q*q,0),visited(q*q,0);
 vector<int> X(q*q),Y(q*q),parent(q*q,-1),moves(q*q,-1);
 vector<int> queue;queue.reserve(q*q);
 int rev[14];for(int i=0;i<14;i++)for(int j=0;j<14;j++)
  if(F[i].a+F[j].a==0 && F[i].b+F[j].b==0)rev[i]=j;
 for(int a=0;a<q;a++)for(int b=0;b<q;b++)
  allowed[a*q+b]=gcd(norm(a,b),q)==1;
 for(int start=0;start<q*q;start++){
  if(!allowed[start]||visited[start])continue;
  queue.clear();queue.push_back(start);visited[start]=1;
  X[start]=start/q;Y[start]=start%q;
  for(size_t i=0;i<queue.size();i++){
   int r=queue[i],a=X[r],b=Y[r];
   for(int j=0;j<14;j++){
    int wx=a+F[j].a, wy=b+F[j].b;
    int s=positive_mod(wx,q)*q+positive_mod(wy,q);
    if(!allowed[s])continue;
    if(visited[s]){
     if(X[s]!=wx||Y[s]!=wy){
      vector<int> u=path(r,parent,moves),v=path(s,parent,moves);
      u.push_back(j);
      for(auto k=v.rbegin();k!=v.rend();k++)u.push_back(rev[*k]);
      int x=start/q,y=start%q;
      for(int k:u){x+=F[k].a;y+=F[k].b;}
      if((x-start/q)%q ||(y-start%q)%q || (x==start/q && y==start%q))
       throw runtime_error("invalid period path");
      return {q,start/q,start%q,u};
     }
    }else{
     visited[s]=1;parent[s]=r;moves[s]=j;
     X[s]=wx;Y[s]=wy;queue.push_back(s);
    }
   }
  }
 }
 throw runtime_error("unexpected finite sieve at q="+to_string(q));
}
int main(){
 int total=0,maxlength=0;
 cout<<"[";
 for(int q=1;q<1122;q++){
  bool squarefree=true;
  for(int p=2;p*p<=q;p++)if(q%(p*p)==0){squarefree=false;break;}
  if(!squarefree)continue;
  auto cert=produce(q);
  if(total)cout<<",";
  cout<<"{\"q\":"<<q<<",\"start\":["<<cert.sx<<","<<cert.sy<<"],\"steps\":[";
  for(size_t j=0;j<cert.steps.size();j++){
   if(j)cout<<",";cout<<cert.steps[j];
  }
  cout<<"]}";
  total++;maxlength=max(maxlength,(int)cert.steps.size());
 }
 cout<<"]\n";
 cerr<<"certificates="<<total<<" max_steps="<<maxlength<<"\n";
}

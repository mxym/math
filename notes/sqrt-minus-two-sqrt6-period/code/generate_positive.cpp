#include <bits/stdc++.h>
using namespace std;
using ll=long long;
const vector<pair<int,int>> F={{-2,-1},{-2,0},{-2,1},{-1,-1},{-1,0},{-1,1},
                                {0,-1},{0,1},{1,-1},{1,0},{1,1},{2,-1},{2,0},{2,1}};
int main(){
 const int q=1122,n=q*q;
 vector<unsigned char> allowed(n),seen(n);
 vector<int> X(n),Y(n);
 vector<int> queue;queue.reserve(n);
 int allowedcount=0,compcount=0,maxsize=0;
 auto mod=[q](int x){int z=x%q;return z<0?z+q:z;};
 for(int a=0;a<q;a++)for(int b=0;b<q;b++){
  int idx=a*q+b;allowed[idx]=gcd(a*a+2*b*b,q)==1;allowedcount+=allowed[idx];
 }
 cout<<"{\"q\":"<<q<<",\"components\":[";
 for(int start=0;start<n;start++){
  if(!allowed[start]||seen[start])continue;
  queue.clear();queue.push_back(start);seen[start]=1;
  X[start]=start/q;Y[start]=start%q;
  for(size_t i=0;i<queue.size();i++){
   int r=queue[i],x=X[r],y=Y[r];
   for(auto [da,db]:F){
    int xx=x+da,yy=y+db;
    int t=mod(xx)*q+mod(yy);
    if(!allowed[t])continue;
    if(seen[t]){
     if(X[t]!=xx||Y[t]!=yy)throw runtime_error("nonzero voltage");
    }else{
     seen[t]=1;X[t]=xx;Y[t]=yy;queue.push_back(t);
    }
   }
  }
  if(compcount)cout<<",";
  cout<<"[";
  for(size_t i=0;i<queue.size();i++){
   if(i)cout<<",";
   int r=queue[i];cout<<"["<<X[r]<<","<<Y[r]<<"]";
  }
  cout<<"]";
  compcount++;maxsize=max(maxsize,(int)queue.size());
 }
 cout<<"]}\n";
 cerr<<"q="<<q<<" allowed="<<allowedcount<<" components="<<compcount<<" max="<<maxsize<<"\n";
}

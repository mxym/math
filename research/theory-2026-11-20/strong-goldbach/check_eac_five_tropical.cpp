// Exact first stage. No input data; output canonical exponent matrices, row-major.
#include <algorithm>
#include <array>
#include <cstdio>
#include <vector>
using Row = std::array<int,5>;
using Mat = std::array<Row,5>;
Mat A;
std::vector<Row> choices[5];
long long raw=0, kept=0;
bool eligible() {
    int heavy=0, masks[10], count=0;
    for (auto row:A) {int total=0;for(int e:row) total+=e; heavy+=(total>=3);}
    if(heavy<2) return false;
    for(int i=0;i<5;i++) for(int j=0;j<i;j++) {
        if(A[i]==A[j]) return false; // different inputs have different complements
        if(A[i][j] && A[j][i]) masks[count++]=(1<<i)|(1<<j);
    }
    bool disjoint=false;
    for(int i=0;i<count;i++) for(int j=0;j<i;j++) if(!(masks[i]&masks[j])) disjoint=true;
    if(!disjoint) return false;
    int reach[5]={};
    for(int i=0;i<5;i++) {reach[i]=1<<i;for(int j=0;j<5;j++) if(A[i][j]) reach[i]|=1<<j;}
    for(int i=0;i<5;i++) for(int j=0;j<5;j++) if((reach[j]>>i)&1) reach[j]|=reach[i];
    for(int m:reach) if(m!=31) return false;
    int detA=0,detB=0;
    Row p={0,1,2,3,4};
    do {
        int sign=1,ap=1,bp=1;
        for(int i=0;i<5;i++) {
            for(int j=0;j<i;j++) if(p[j]>p[i]) sign=-sign;
            ap*=A[i][p[i]];bp*=(p[i]==i)-A[i][p[i]];
        }
        detA+=sign*ap; detB+=sign*bp;
    } while(std::next_permutation(p.begin(),p.end()));
    if(detA || detB) return false;
    do {
        Mat image;
        for(int i=0;i<5;i++) for(int j=0;j<5;j++) image[i][j]=A[p[i]][p[j]];
        if(image<A) return false;
    } while(std::next_permutation(p.begin()+1,p.end()));
    return true;
}
void visit(int i) {
    if(i<5){for(auto r:choices[i]) {A[i]=r; visit(i+1);}return;}
    ++raw;
    if(!eligible()) return;
    ++kept;
    for(auto r:A) for(int e:r) std::printf("%d",e);
    std::puts("");
}
int main() {
    // 0 is the least prime. Other vertices are not presorted.
    for(int i=0;i<5;i++) {
        for(int j=1;j<5;j++) if(j!=i) for(int k=j;k<5;k++) if(k!=i)
        {Row r={};++r[j];++r[k];choices[i].push_back(r);}
        if(i) for(int e=1;e<=5;e++) {
            Row pure={};pure[0]=e;
            if(e>=2) choices[i].push_back(pure);
            if(e<5) for(int j=1;j<5;j++) if(j!=i)
            {auto r=pure;r[j]=1;choices[i].push_back(r);}
        }
        if(choices[i].size()!=(i?22u:10u)) return 1;
    }
    visit(0);std::fprintf(stderr,"raw=%lld canonical=%lld\n",raw,kept);
    return raw==2342560 && kept==45 ? 0:1;
}

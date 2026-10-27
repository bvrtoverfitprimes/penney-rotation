#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using I=long long;
struct Enumerator {
 int k,n,d,h,mode,last_type;
 vector<int> a,b,ia,ib,p;
 vector<unsigned> pred;
 I total=0,accepted=0;
 Enumerator(vector<int> aa,int nn):k(aa.size()),n(nn),a(aa),p(nn),pred(nn){
  b=a;rotate(b.begin(),b.end()-1,b.end());ia.resize(k);ib.resize(k);
  for(int i=0;i<k;i++){ia[a[i]]=i;ib[b[i]]=i;}
 }
 void constrain(int pos,int type){auto &inv=type?ib:ia;for(int j=1;j<k;j++)pred[pos+inv[j]]|=1u<<(pos+inv[j-1]);}
 int hit(int s){
  bool ok=true;for(int j=1;j<k;j++)if(p[s+ia[j-1]]>p[s+ia[j]]){ok=false;break;}if(ok)return 1;
  for(int j=1;j<k;j++)if(p[s+ib[j-1]]>p[s+ib[j]])return 0;return 2;
 }
 void visit(){
  total++;
  if(mode==0){
   int sums[32];sums[0]=-1;int c=0;
   for(int s=1;s<=d;s++){
    sums[s]=sums[s-1];
    if(hit(s)){sums[s]=s>=k?sums[s-k]:0;c=sums[s]-sums[s-1];}else c=0;
   }
   accepted+=(last_type==0?c:-c);
  }else{
   int previous=0;
   for(int s=1;s<=n-k;s++){
    if(s-previous>=k)break;
    if(hit(s)){previous=s;if(s>=h){accepted++;break;}}
   }
  }
 }
 void dfs(unsigned used,int rank){
  if(rank==n){visit();return;}
  unsigned left=((1u<<n)-1)^used;
  while(left){unsigned bit=left&-left;left-=bit;int v=__builtin_ctz(bit);if((pred[v]&used)==pred[v]){p[v]=rank;dfs(used|bit,rank+1);}}
 }
 I run_cluster(int dd,int first,int last){d=dd;mode=0;last_type=last;constrain(0,first);constrain(d,last);dfs(0,0);return accepted;}
 I run_prefix(int hh,int first){h=hh;mode=1;constrain(0,first);dfs(0,0);return accepted;}
};
int main(int argc,char**argv){
 int k=argc>1?atoi(argv[1]):5,h=argc>2?atoi(argv[2]):1;
 int only=argc>3?atoi(argv[3]):-1;
 int D=h+2*k-3,N=k+D,R=h+2*k-2;
 vector<int>a(k);iota(a.begin(),a.end(),0);int id=-1;
 cout<<"{\"k\":"<<k<<",\"h\":"<<h<<",\"max_n\":"<<N<<",\"prefix_n\":"<<R<<",\"cases\":[\n";bool comma=false;
 do{
  id++;auto comp=a;for(int &x:comp)x=k-1-x;
  if(a>comp || (only>=0 && id!=only))continue;
  if(comma)cout<<",\n";comma=true;
  cout<<"{\"id\":"<<id<<",\"a\":[";for(int i=0;i<k;i++)cout<<(i?",":"")<<a[i]+1;cout<<"],\"c\":[";
  for(int d=1;d<=D;d++){
   I v=0;for(int first=0;first<2;first++)for(int last=0;last<2;last++){Enumerator e(a,k+d);v+=e.run_cluster(d,first,last);}
   cout<<(d>1?",":"")<<v;
  }
  I r=0;for(int first=0;first<2;first++){Enumerator e(a,R);r+=e.run_prefix(h,first);}
  cout<<"],\"prefix_count\":"<<r<<"}"<<flush;
 }while(next_permutation(a.begin(),a.end()));
 cout<<"\n]}\n";
}

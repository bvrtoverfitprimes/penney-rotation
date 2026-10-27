#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;
int fact[13];
int code(const int* a,int k){int id=0;for(int i=0;i<k;i++){int s=0;for(int j=i+1;j<k;j++)s+=a[j]<a[i];id+=s*fact[k-i-1];}return id;}
int main(int argc,char**argv){
 int k=argc>1?atoi(argv[1]):5,n=argc>2?atoi(argv[2]):10;
 fact[0]=1;for(int i=1;i<=12;i++)fact[i]=fact[i-1]*i;
 vector<int>p(k),rot(fact[k]),left(fact[k]);for(int i=0;i<k;i++)p[i]=i;
 do{int id=code(p.data(),k);auto q=p;rotate(q.begin(),q.end()-1,q.end());rot[id]=code(q.data(),k);left[rot[id]]=id;}while(next_permutation(p.begin(),p.end()));
 vector<long long>a(fact[k]),b(fact[k]);p.resize(n);for(int i=0;i<n;i++)p[i]=i;
 do{
  int last=code(p.data()+n-k,k);bool unique=true,seenR=false,seenL=false;
  for(int i=0;i<n-k;i++){
   int id=code(p.data()+i,k);
   if(id==last){unique=false;break;}
   seenR|=id==rot[last];seenL|=id==left[last];
  }
  if(unique){if(!seenR)a[last]++;if(!seenL)b[left[last]]++;}
 }while(next_permutation(p.begin(),p.end()));
 long long low=1LL<<60;int idlow=-1,negative=0,zero=0;
 for(int id=0;id<fact[k];id++){long long diff=b[id]-a[id];if(diff<low){low=diff;idlow=id;}negative+=diff<0;zero+=diff==0;}
 cout<<"k="<<k<<" n="<<n<<" min(b-a)="<<low<<" id="<<idlow<<" a="<<a[idlow]<<" b="<<b[idlow]<<" negative="<<negative<<" zero="<<zero<<"\n";
}

// brute-force stability test for a consecutive pattern p on all multisets with total size <= SMAX
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <algorithm>
#include <vector>
#include <map>
using namespace std;
static int L, ordr[16], n, cnt[32], w[64], sz;
static long long hist[16];
static inline int occ_at(int end){ // factor w[end-L+1..end]
    const int *b=w+end-L+1;
    for(int i=0;i+1<L;i++) if(!(b[ordr[i]]<b[ordr[i+1]])) return 0;
    return 1;
}
static void rec(int pos,int s){
    if(pos==sz){ hist[s]++; return; }
    for(int a=0;a<n;a++) if(cnt[a]){
        cnt[a]--; w[pos]=a;
        int add=(pos>=L-1)?occ_at(pos):0;
        rec(pos+1,s+add);
        cnt[a]++;
    }
}
static void parts(int total,int k,int maxp,vector<int>&cur,vector<vector<int> >&out){
    if(k==0){ if(total==0) out.push_back(cur); return; }
    for(int a=min(total,maxp);a>=1;a--){ cur.push_back(a); parts(total-a,k-1,a,cur,out); cur.pop_back(); }
}
int main(int argc,char**argv){
    const char*ps=argv[1]; L=strlen(ps); int smax=atoi(argv[2]); int nmin=argc>3?atoi(argv[3]):L;
    int p[16]; for(int i=0;i<L;i++) p[i]=ps[i]-'0';
    for(int v=1;v<=L;v++) for(int i=0;i<L;i++) if(p[i]==v) ordr[v-1]=i;
    long long words=0; int classes=0;
    for(sz=L;sz<=smax;sz++) for(n=max(L,nmin);n<=sz;n++){
        vector<vector<int> > ps2; vector<int> cur; parts(sz,n,sz,cur,ps2);
        for(size_t t=0;t<ps2.size();t++){
            vector<int> a=ps2[t]; sort(a.begin(),a.end());
            map<vector<long long>,vector<int> > seen;
            do{
                for(int i=0;i<n;i++) cnt[i]=a[i];
                memset(hist,0,sizeof hist); rec(0,0);
                vector<long long> h(hist,hist+16); for(int i=0;i<16;i++) words+=hist[i];
                seen[h]=a;
            }while(next_permutation(a.begin(),a.end()));
            classes++;
            if(seen.size()>1){
                printf("UNSTABLE %s size %d n %d:",ps,sz,n);
                for(map<vector<long long>,vector<int> >::iterator it=seen.begin();it!=seen.end();++it){
                    printf("  M(");for(int i=0;i<n;i++)printf("%d%s",it->second[i],i+1<n?",":"");printf(") hist");
                    for(int i=0;i<5;i++)printf(" %lld",it->first[i]);
                }
                printf("\n"); return 1;
            }
        }
    }
    printf("STABLE so far: %s up to size %d (%d multiset classes, %lld words)\n",ps,smax,classes,words);
    return 0;
}

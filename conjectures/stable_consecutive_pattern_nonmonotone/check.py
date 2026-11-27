import sys, itertools
from functools import lru_cache

def make(p):
    L=len(p)
    order=sorted(range(L), key=lambda i:p[i])  # positions in increasing value
    def is_occ(w):  # w tuple of length L
        for a,b in zip(order, order[1:]):
            if not (w[a] < w[b]): return False
        return True
    def dist(counts):
        n=len(counts)
        @lru_cache(maxsize=None)
        def f(cnt, last):
            if sum(cnt)==0: return ((0,1),)
            res={}
            for a in range(n):
                if cnt[a]==0: continue
                c2=list(cnt); c2[a]-=1
                w=last+(a,)
                add=0
                if len(w)==L and is_occ(w): add=1
                nl=w[-(L-1):] if L>1 else ()
                for s,v in f(tuple(c2), nl):
                    res[s+add]=res.get(s+add,0)+v
            return tuple(sorted(res.items()))
        return f(tuple(counts), ())
    return dist

def partitions(total, parts, maxpart=None):
    if maxpart is None: maxpart=total
    if parts==0:
        if total==0: yield ()
        return
    for a in range(min(total,maxpart), 0, -1):
        for rest in partitions(total-a, parts-1, a):
            yield (a,)+rest

def test(p, nmax, sizemax, verbose=True):
    dist=make(p)
    for n in range(len(p), nmax+1):
        for size in range(n, sizemax+1):
            for part in partitions(size, n):
                seen={}
                for perm in set(itertools.permutations(part)):
                    d=dist(perm)
                    seen.setdefault(d, []).append(perm)
                if len(seen)>1:
                    if verbose:
                        ks=list(seen.items())
                        print('  UNSTABLE', p, 'on', ks[0][1][0], ks[0][0], 'vs', ks[1][1][0], ks[1][0])
                    return False
    return True

if __name__=='__main__':
    for p in [(1,2,3),(1,3,2),(1,3,2,4)]:
        print(p, test(p, 5, 7))

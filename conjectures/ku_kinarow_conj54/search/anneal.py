import random, math, sys
def lines_of(k):
    L=[]
    for c in range(k):
        L.append([(x,c) for x in range(k)])
        L.append([(c,y) for y in range(k)])
        L.append([(x,(x-c)%k) for x in range(k)])
        L.append([(x,(c-x)%k) for x in range(k)])
    return L
def search(k, size, iters=400000, seed=0):
    rnd=random.Random(seed)
    L=lines_of(k)
    inc={}
    for i,l in enumerate(L):
        for p in l: inc.setdefault(p,[]).append(i)
    pts=[(x,y) for x in range(k) for y in range(k)]
    A=set(rnd.sample(pts,size))
    cnt=[0]*len(L)
    for p in A:
        for i in inc[p]: cnt[i]+=1
    def deficit(): return sum(max(0,2-c) for c in cnt)
    cur=deficit(); T=1.0
    for it in range(iters):
        if cur==0: return A
        p=rnd.choice(tuple(A)); q=rnd.choice(pts)
        if q in A: continue
        d=0
        for i in inc[p]:
            if cnt[i]<=2: d+=1
        for i in inc[p]: cnt[i]-=1
        for i in inc[q]:
            if cnt[i]<2: d-=1
        if d<=0 or rnd.random()<math.exp(-d/T):
            for i in inc[q]: cnt[i]+=1
            A.remove(p); A.add(q); cur+=d
        else:
            for i in inc[p]: cnt[i]+=1
        T=max(0.05, T*0.99999)
    return None
for k in [6,9,12,15]:
    found=None
    for seed in range(6):
        found=search(k,2*k+2,seed=seed)
        if found: break
    print('k',k,'size',2*k+2,'found' if found else 'not found')
    if found:
        for y in range(k): print(''.join('#' if (x,y) in found else '.' for x in range(k)))

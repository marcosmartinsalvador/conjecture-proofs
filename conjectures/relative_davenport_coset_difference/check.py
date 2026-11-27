"""Independent check for relative_davenport_coset_difference (no Lean involved).

1. Computes d_S(Z/4) straight from Definition 2.4 of arXiv:2605.17595 by listing every
   multiset of at most 4 elements, and prints the two values used in the counterexample.
2. For a list of small abelian groups, tests the statement of the conjecture for every
   pair of subgroups H1 < H2 and every coset, and reports where it fails. It also tests
   the paper's other conjecture (2.16) on the same groups.
"""
import itertools, collections

def group(orders):
    els = list(itertools.product(*[range(o) for o in orders]))
    idx = {e: i for i, e in enumerate(els)}
    add = [[idx[tuple((a + b) % o for a, b, o in zip(x, y, orders))] for y in els] for x in els]
    return els, add

def d_values(orders):
    """d[t] = largest length of a zero-sum free sequence with sum t (0 if none)."""
    els, add = group(orders)
    n = len(els)
    layer = {(0, 0)}          # (bitmask of nonempty subsequence sums, total)
    d = [0] * n
    k = 0
    while layer:
        nxt = set()
        for mask, tot in layer:
            for x in range(1, n):
                m2 = mask | (1 << x)
                for s in range(n):
                    if mask >> s & 1:
                        m2 |= 1 << add[s][x]
                if m2 & 1:
                    continue      # some nonempty subsequence sums to zero
                nxt.add((m2, add[tot][x]))
        k += 1
        for _, t in nxt:
            d[t] = max(d[t], k)
        layer = nxt
    return els, add, d

def subgroups(els, add):
    n = len(els)
    subs = set()
    def closure(gens):
        S = {0}; todo = [0]
        while todo:
            a = todo.pop()
            for g in gens:
                b = add[a][g]
                if b not in S:
                    S.add(b); todo.append(b)
        return frozenset(S)
    for r in range(0, 5):
        for gens in itertools.combinations(range(n), r):
            subs.add(closure(gens))
    return subs

# 1. Z/4 straight from the definition
def zero_sum_free(T, m):
    return all(sum(U) % m != 0 for r in range(1, len(T) + 1) for U in itertools.combinations(T, r))
def d_direct(S, m=4, maxlen=5):
    best = 0
    for L in range(1, maxlen + 1):
        for T in itertools.combinations_with_replacement(range(m), L):
            if sum(T) % m in S and zero_sum_free(T, m):
                best = max(best, L)
    return best
print("Z/4: d_G =", d_direct({0, 1, 2, 3}), " d_{0,2} =", d_direct({0, 2}), " d_{1,3} =", d_direct({1, 3}))

# 2. where does the statement fail on small groups?
for orders in [(2,), (3,), (4,), (6,), (8,), (9,), (10,), (12,), (2, 2), (2, 4), (3, 3), (2, 2, 2),
               (2, 6), (4, 4), (2, 8), (3, 6), (2, 2, 4), (5, 5), (2, 2, 2, 2)]:
    els, add, d = d_values(orders)
    n = len(els)
    subs = subgroups(els, add)
    dS = lambda S: max(d[x] for x in S)
    fails = collections.Counter()
    for H1 in subs:
        for H2 in subs:
            if H1 < H2:
                seen = set()
                for g in range(n):
                    alpha = frozenset(add[g][h] for h in H1)
                    if alpha in seen:
                        continue
                    seen.add(alpha)
                    beta = frozenset(add[g][h] for h in H2)
                    if dS(beta) != dS(beta - alpha):
                        fails[("index %d" % (len(H2) // len(H1)), "alpha = H1" if 0 in alpha else "alpha != H1")] += 1
    # the paper's other conjecture (2.16): d_alpha >= d_beta when beta is a multiple of
    # alpha in G/H
    bad216 = 0
    for H in subs:
        cos = {g: frozenset(add[g][h] for h in H) for g in range(n)}
        for g in range(n):
            x = 0
            while True:
                x = add[x][g]
                if dS(cos[g]) < dS(cos[x]):
                    bad216 += 1
                if cos[x] == cos[0]:
                    break
    print(orders, "failures:", dict(fails), "| failures of Conjecture 2.16:", bad216)

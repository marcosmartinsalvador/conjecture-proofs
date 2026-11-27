"""Computer checks for PROOF_NOTES.md (delta_primitive_two_primes). No Lean involved.

  python3 check.py          quick checks (about a minute)
  python3 check.py wide     also the wide search over primes below 300 (a few minutes)
"""
import math, sys

def has_delta(n):
    """Delta property straight from the definition (D*_n meets D+_n)."""
    ds = [d for d in range(1, math.isqrt(n) + 1) if n % d == 0]
    D = [n // d - d for d in ds]
    nz = [h for h in D if h != 0]
    S = set(D)
    return any((x + y) in S for x in nz for y in nz)

def factor(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def primes_below(b):
    return [x for x in range(2, b) if all(x % d for d in range(2, math.isqrt(x) + 1))]

# 1. small n with exactly two prime factors
bad = 0; found = []
for n in range(2, 60001):
    if len(factor(n)) == 2:
        hd = has_delta(n)
        pred = any(n % b == 0 and math.isqrt(n // b) ** 2 == n // b for b in (24, 40))
        if hd != pred:
            bad += 1; print("MISMATCH", n)
        if hd:
            found.append(n)
print("n <= 60000 with two prime factors: mismatches with '24 or 40 times a square':", bad)
print("  first members:", found[:10])

# 2. equation (*) of the notes in prime powers
def ispow(m, b):
    if m < b:
        return False
    while m % b == 0:
        m //= b
    return m == 1
LIM = 10 ** 30
sols = []
pr = primes_below(120)
for p in pr:
    for q in pr:
        if p == q:
            continue
        pw = [p ** i for i in range(1, 100) if p ** i < LIM]
        qw = [q ** i for i in range(1, 100) if q ** i < LIM]
        for R1 in pw:
            for S1 in qw:
                if R1 * S1 > LIM:
                    break
                for e in (1, -1):
                    X = R1 * S1 + e * R1 + 1      # = S t
                    Y = R1 * S1 + e * S1 + 1      # = R t
                    g = math.gcd(X, Y)
                    R, S = Y // g, X // g
                    if ispow(R, p) and ispow(S, q):
                        assert R * X == S * Y
                        sols.append((p, q, R, R1, S, S1, e))
print("solutions (p, q, R, R', S, S', eps) of (*):", sols)

# 3. wide search: primes below 300, n <= 10^40
if len(sys.argv) > 1 and sys.argv[1] == "wide":
    def delta_pq(p, a, q, b):
        n = p ** a * q ** b
        small = sorted(d for d in (p ** i * q ** j for i in range(a + 1) for j in range(b + 1)) if d * d < n)
        D = {d: n // d - d for d in small}
        inv = set(D.values())
        return any(D[y] + D[z] in inv for i, y in enumerate(small) for z in small[i:])
    LIM2 = 10 ** 40
    pr = primes_below(300); odd = []; prim = []
    for ip, p in enumerate(pr):
        for q in pr[ip + 1:]:
            memo = {}
            def f(a, b):
                if (a, b) not in memo:
                    memo[(a, b)] = delta_pq(p, a, q, b)
                return memo[(a, b)]
            a = 1
            while p ** a * q <= LIM2:
                b = 1
                while p ** a * q ** b <= LIM2:
                    if f(a, b):
                        if not (p == 2 and q in (3, 5) and a >= 3 and a % 2 == 1 and b % 2 == 1):
                            odd.append((p, a, q, b))
                        if not (a >= 2 and f(a - 2, b)) and not (b >= 2 and f(a, b - 2)):
                            prim.append(p ** a * q ** b)
                    b += 1
                a += 1
    print("wide search: members not of the form 2^odd(>=3) * {3,5}^odd:", odd, " primitive ones:", prim)

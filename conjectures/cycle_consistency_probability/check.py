"""Independent check of q(C_n) for the Horak-Semaev cycle conjecture (arXiv:2603.24890).

A system on the cycle C_n gives each edge i one of the 16 functions F2 x F2 -> F2.
A function is stored as a 4-bit mask: bit 2a+b is set when f(a,b) = 0 (pair allowed).
"""
import itertools
from fractions import Fraction


def brute(n):
    """Number of consistent systems on C_n, by trying every system and every assignment."""
    count = 0
    for fs in itertools.product(range(16), repeat=n):
        if any(all((fs[i] >> (2 * x[i] + x[(i + 1) % n])) & 1 for i in range(n))
               for x in itertools.product(range(2), repeat=n)):
            count += 1
    return count


def mul(A, B):
    """Boolean product of two 2x2 matrices stored as masks."""
    C = 0
    for a in range(2):
        for c in range(2):
            if any((A >> (2 * a + b)) & 1 and (B >> (2 * b + c)) & 1 for b in range(2)):
                C |= 1 << (2 * a + c)
    return C


def by_matrices(nmax):
    """Number of sequences of n matrices whose product has a nonzero diagonal, n = 1..nmax."""
    dist = {0b1001: 1}
    out = {}
    for n in range(1, nmax + 1):
        new = {}
        for A, v in dist.items():
            for B in range(16):
                M = mul(A, B)
                new[M] = new.get(M, 0) + v
        dist = new
        out[n] = sum(v for M, v in dist.items() if (M & 1) or (M >> 3) & 1)
    return out


if __name__ == "__main__":
    # paths, to confirm the reading of the paper: q(P_1) = 15/16, q(P_2) = 207/256
    print("q(P_1) =", Fraction(sum(1 for A in range(16) if A), 16))
    print("q(P_2) =", Fraction(sum(1 for A in range(16) for B in range(16) if mul(A, B)), 256))
    a = [2, 17]  # a_n = (16 s)^n + (16 t)^n = 17 a_{n-1} - 48 a_{n-2}
    counts = by_matrices(15)
    for n in range(3, 16):
        while len(a) <= n:
            a.append(17 * a[-1] - 48 * a[-2])
        corrected = a[n] - 4 ** n - 2 ** (n - 1)      # 16^n (s^n + t^n - 4^-n - 1/(2 8^n))
        printed = a[n] - 4 ** n - 8 * 2 ** n          # 16^n (s^n + t^n - 4^-n - 8^-(n-1))
        direct = brute(n) if n <= 4 else None
        print(n, "count", counts[n], "direct", direct,
              "corrected formula ok:", counts[n] == corrected and (direct in (None, corrected)),
              "printed formula ok:", counts[n] == printed)

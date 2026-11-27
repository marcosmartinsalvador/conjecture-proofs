// Search for A in (Z/kZ)^2 with |A| <= 2k+2 and every row, column, diagonal (x-y=c)
// and anti-diagonal (x+y=c) containing at least 2 points of A.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int k, maxsize;
int col[32], dg[32], ad[32];
int rows[32];           // bitmask chosen per row
long long found = 0, nodes = 0;
int nsub; int subs[1<<16]; int subsz[1<<16];
int firstsol[32]; int havesol = 0;
static void rec(int y, int used) {
    nodes++;
    if (y == k) {
        for (int c = 0; c < k; c++) if (col[c] < 2 || dg[c] < 2 || ad[c] < 2) return;
        found++;
        if (!havesol) { havesol = 1; memcpy(firstsol, rows, sizeof(rows)); }
        return;
    }
    int rem = k - y;              // rows left including this one
    // prune: each remaining row adds at most 1 to each diagonal/antidiagonal/column
    for (int c = 0; c < k; c++) if (col[c] + rem < 2 || dg[c] + rem < 2 || ad[c] + rem < 2) return;
    // total size bound: remaining rows need at least 2 each
    for (int i = 0; i < nsub; i++) {
        int m = subs[i], sz = subsz[i];
        if (used + sz + 2 * (rem - 1) > maxsize) continue;
        rows[y] = m;
        for (int x = 0; x < k; x++) if (m >> x & 1) { col[x]++; dg[((x - y) % k + k) % k]++; ad[(x + y) % k]++; }
        rec(y + 1, used + sz);
        for (int x = 0; x < k; x++) if (m >> x & 1) { col[x]--; dg[((x - y) % k + k) % k]--; ad[(x + y) % k]--; }
        if (havesol && getenv("FIRST")) return;
    }
}
int main(int argc, char **argv) {
    k = atoi(argv[1]); maxsize = atoi(argv[2]);
    nsub = 0;
    for (int m = 0; m < (1 << k); m++) { int s = __builtin_popcount(m); if (s >= 2 && s <= 2 + (maxsize - 2 * k)) { subs[nsub] = m; subsz[nsub] = s; nsub++; } }
    rec(0, 0);
    printf("k=%d maxsize=%d solutions=%lld nodes=%lld\n", k, maxsize, found, nodes);
    if (havesol) { for (int y = 0; y < k; y++) { for (int x = 0; x < k; x++) putchar(firstsol[y] >> x & 1 ? '#' : '.'); putchar('\n'); } }
    return 0;
}

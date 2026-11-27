# Kourovka 20.52: checks, with GAP, of the groups named in source.md.
# Run:  gap -q < check.g        (about two minutes)
# Each line gives j, the order of the group, its class number k, and whether
# |G| - k = 16 * 2^j  (so m = 2^j is attained by a nonabelian group of odd order).
SetPrintFormattingStatus("*stdout*", false);

# Z/n : Z/q as permutations of Z/n: x -> x+1 and x -> u*x.
Frob := function(n, u)
  return Group(PermList(List([0..n-1], x -> ((x+1) mod n)+1)),
               PermList(List([0..n-1], x -> ((u*x) mod n)+1)));
end;

Report := function(j, G, what)
  local k;
  k := NrConjugacyClasses(G);
  Print("j=", j, "  |G|=", Size(G), "  k=", k, "  odd order: ", Size(G) mod 2 = 1, "  nonabelian: ", not IsAbelian(G), "  |G|-k=16*2^j: ", Size(G) - k = 16 * 2^j, "   (", what, ")\n");
end;

# The infinite family (j odd): y = 2^((j-1)/2), n = 12y^2+1, u = 6y^2+3y.
for j in [1,3,5,7,9,11] do
  y := 2^((j-1)/2);  n := 12*y^2+1;  u := 6*y^2+3*y;
  if (u^2+u+1) mod n <> 0 then Print("BAD u for j=", j, "\n"); fi;
  Report(j, Frob(n, u), Concatenation("Z/", String(n), " : Z/3, u=", String(u)));
od;

# Even j, found one at a time.
Report(0, Frob(7, 2), "Z/7 : Z/3");
Report(2, SmallGroup(75, 2), "(Z/5)^2 : Z/3");
Report(4, Frob(97, 35), "Z/97 : Z/3");
Report(6, SmallGroup(1161, 9), "Z/43 : (nonabelian group of order 27)");
# (Z/9 x Z/9 x Z/19) : Z/3 = Z[w]/(beta) : <w>, norm of beta = 1539; w(a,b,c) = (-b, a-b, 7c)
pt := function(a, b, c) return (a mod 9) + 9*(b mod 9) + 81*(c mod 19) + 1; end;
tr := function(f) return PermList(List([0..1538], function(p) local a, b, c; a := p mod 9; b := QuoInt(p, 9) mod 9; c := QuoInt(p, 81); return f(a, b, c); end)); end;
G8 := Group(tr(function(a,b,c) return pt(a+1,b,c); end), tr(function(a,b,c) return pt(a,b+1,c); end),
            tr(function(a,b,c) return pt(a,b,c+1); end), tr(function(a,b,c) return pt(-b,a-b,7*c); end));
Report(8, G8, "(Z/9 x Z/9 x Z/19) : Z/3");
Report(10, DirectProduct(Frob(41, 10), SmallGroup(81, 7)), "(Z/41 : Z/5) x (Z/3 wr Z/3)");
n := 24577;  u := First([1..n], x -> (x^2+x+1) mod n = 0);
Report(12, Frob(n, u), Concatenation("Z/24577 : Z/3, u=", String(u)));

# Exhaustive: which m <= 74 are attained by odd-order groups of order < 2000?
# (|G| - k(G) >= 16|G|/27 for nonabelian G of odd order, so order < 2000 covers m <= 74.)
res := [];
for n in [3,5..1999] do
  for i in [1..NumberSmallGroups(n)] do
    G := SmallGroup(n, i);
    if not IsAbelian(G) then AddSet(res, (n - NrConjugacyClasses(G))/16); fi;
  od;
od;
Print("m <= 74 not attained by a group of order < 2000: ", Filtered([1..74], x -> not x in res), "\n");
QUIT;

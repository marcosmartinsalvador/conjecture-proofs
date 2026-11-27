import conjectures.ku_kinarow_conj54.Statement

/-- A 14-point subset of `(ℤ/6ℤ)^2` meeting every axis-parallel and diagonal line at least
twice. Rows `y = 0, ..., 5` (a `#` is a point, `x` runs left to right):
```
##....
##....
..###.
#....#
.##...
...###
```
-/
theorem cover6 : HasSmallDoubleCover 6 := by
  refine ⟨{(0, 0), (0, 1), (0, 3), (1, 0), (1, 1), (1, 4), (2, 2), (2, 4), (3, 2), (3, 5),
    (4, 2), (4, 5), (5, 3), (5, 5)}, by decide, ?_⟩
  decide +kernel

/-- A 20-point subset of `(ℤ/9ℤ)^2` meeting every axis-parallel and diagonal line at least
twice. -/
theorem cover9 : HasSmallDoubleCover 9 := by
  refine ⟨{(0, 2), (0, 6), (1, 0), (1, 7), (2, 3), (2, 4), (3, 1), (3, 2), (3, 7), (4, 5),
    (4, 7), (5, 4), (5, 8), (6, 1), (6, 2), (6, 6), (7, 3), (7, 5), (8, 0), (8, 8)},
    by decide, ?_⟩
  decide +kernel

theorem result : Claim :=
  ⟨cover6, cover9, fun h => h 6 (by norm_num) (by norm_num) cover6⟩

import conjectures.torus_two_per_line.Statement

open Finset

/-- Membership in a toric line, with the parameter running over `ZMod k`. -/
theorem mem_toricLine (k : ℕ) [NeZero k] (p : ZMod k × ZMod k) (d : ℤ × ℤ)
    (a : ZMod k × ZMod k) :
    a ∈ toricLine k p d ↔
      ∃ t : ZMod k, a = (p.1 + t * (d.1 : ZMod k), p.2 + t * (d.2 : ZMod k)) := by
  unfold toricLine
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, _, rfl⟩
    exact ⟨(t : ZMod k), rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t.val, Finset.mem_range.mpr (ZMod.val_lt t), ?_⟩
    rw [ZMod.natCast_zmod_val]

/-- If every fibre of `φ` on `A` has exactly two points, a sum over `A` of a function
of `φ` is twice the sum over the whole of `ZMod k`. -/
theorem sum_of_fibres (k : ℕ) [NeZero k] (A : Finset (ZMod k × ZMod k))
    (φ : ZMod k × ZMod k → ZMod k)
    (h : ∀ c : ZMod k, (A.filter fun a => φ a = c).card = 2) (g : ZMod k → ZMod k) :
    ∑ a ∈ A, g (φ a) = 2 * ∑ c : ZMod k, g c := by
  rw [← Finset.sum_fiberwise A φ (fun a => g (φ a)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.mp ha).2] :
    ∀ a ∈ A.filter (fun a => φ a = c), g (φ a) = g c)]
  rw [Finset.sum_const, h c]
  simp [two_mul]

/-- Sum of the first squares. -/
theorem six_mul_sum_sq (n : ℕ) : 6 * ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- The sum of all squares in `ZMod k` is the cast of `0² + 1² + ... + (k-1)²`. -/
theorem sum_sq_zmod (k : ℕ) [NeZero k] :
    ∑ c : ZMod k, c ^ 2 = ((∑ i ∈ range k, i ^ 2 : ℕ) : ZMod k) := by
  rw [Nat.cast_sum]
  symm
  refine Finset.sum_bij (fun i _ => (i : ZMod k)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have := congrArg ZMod.val hij
    rwa [ZMod.val_natCast_of_lt hi', ZMod.val_natCast_of_lt hj'] at this
  · intro c _
    exact ⟨c.val, Finset.mem_range.mpr (ZMod.val_lt c), ZMod.natCast_zmod_val c⟩
  · intro i _
    push_cast
    rfl

theorem result : Claim := by
  intro k hk h3 ⟨A, hA⟩
  have : NeZero k := ⟨hk.ne'⟩
  -- the four families of lines are the fibres of four linear maps
  have h1 : ∀ c : ZMod k, (A.filter fun a => a.1 = c).card = 2 := by
    intro c
    have := hA (c, 0) (0, 1) (by unfold IsDirection; simp)
    rw [← this]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_inter, mem_toricLine]
    constructor
    · rintro ⟨ha, rfl⟩
      exact ⟨⟨a.2, by ext <;> simp⟩, ha⟩
    · rintro ⟨⟨t, rfl⟩, ha⟩
      exact ⟨ha, by simp⟩
  have h2 : ∀ c : ZMod k, (A.filter fun a => a.2 = c).card = 2 := by
    intro c
    have := hA (0, c) (1, 0) (by unfold IsDirection; simp)
    rw [← this]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_inter, mem_toricLine]
    constructor
    · rintro ⟨ha, rfl⟩
      exact ⟨⟨a.1, by ext <;> simp⟩, ha⟩
    · rintro ⟨⟨t, rfl⟩, ha⟩
      exact ⟨ha, by simp⟩
  have h3' : ∀ c : ZMod k, (A.filter fun a => a.1 - a.2 = c).card = 2 := by
    intro c
    have := hA (c, 0) (1, 1) (by unfold IsDirection; simp)
    rw [← this]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_inter, mem_toricLine]
    constructor
    · rintro ⟨ha, rfl⟩
      exact ⟨⟨a.2, by ext <;> simp⟩, ha⟩
    · rintro ⟨⟨t, rfl⟩, ha⟩
      exact ⟨ha, by simp⟩
  have h4 : ∀ c : ZMod k, (A.filter fun a => a.1 + a.2 = c).card = 2 := by
    intro c
    have := hA (c, 0) (1, -1) (by unfold IsDirection; simp)
    rw [← this]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_inter, mem_toricLine]
    constructor
    · rintro ⟨ha, rfl⟩
      exact ⟨⟨-a.2, by ext <;> simp⟩, ha⟩
    · rintro ⟨⟨t, rfl⟩, ha⟩
      exact ⟨ha, by simp⟩
  -- Polya's identity (x+y)² + (x-y)² = 2x² + 2y², summed over A
  have key : ∑ a ∈ A, ((a.1 + a.2) ^ 2 + (a.1 - a.2) ^ 2 - 2 * a.1 ^ 2 - 2 * a.2 ^ 2) = 0 :=
    Finset.sum_eq_zero fun a _ => by ring
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum,
    sum_of_fibres k A (fun a => a.1 + a.2) h4 (fun c => c ^ 2),
    sum_of_fibres k A (fun a => a.1 - a.2) h3' (fun c => c ^ 2),
    sum_of_fibres k A (fun a => a.1) h1 (fun c => c ^ 2),
    sum_of_fibres k A (fun a => a.2) h2 (fun c => c ^ 2), sum_sq_zmod] at key
  have key2 : ((4 * ∑ i ∈ range k, i ^ 2 : ℕ) : ZMod k) = 0 := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    linear_combination -key
  rw [ZMod.natCast_eq_zero_iff] at key2
  obtain ⟨j, hj⟩ := key2
  obtain ⟨m, rfl⟩ := h3
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  have hsum := six_mul_sum_sq (3 * q + 2)
  rw [show 3 * q + 2 + 1 = 3 * (q + 1) by ring] at hsum
  -- 24 Σ = 6 k j = 4 n k (2n+1), so 3 j = 2 n (2 n + 1) with n = 3 q + 2
  have e1 : 3 * (q + 1) * (6 * j) = 3 * (q + 1) * (4 * ((3 * q + 2) * (2 * (3 * q + 2) + 1))) := by
    have : 6 * (4 * ∑ i ∈ range (3 * (q + 1)), i ^ 2) = 6 * (3 * (q + 1) * j) := by rw [hj]
    nlinarith [this, hsum]
  have e2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3 * (q + 1)) e1
  have e3 : 3 * j = 3 * (12 * (q * q) + 18 * q + 6) + 2 := by nlinarith [e2]
  omega

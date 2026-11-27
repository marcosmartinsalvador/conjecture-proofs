import Mathlib
import conjectures.stable_consecutive_pattern_nonmonotone.Statement

/-!
# The consecutive pattern 12435 is stable

Plan (details in `source.md`).

* Part 1: value sequences `e : ℕ → ℕ`.  If every position of a set `S` starts an occurrence
  of 12435, then inside a run of overlapping marked occurrences all values are different.
* Part 2: words.  For two neighbouring letters `a`, `a + 1` the map `flp` exchanges them in
  every run that holds exactly one of them.  It is an involution, keeps the marked
  occurrences, and exchanges the two letter counts.
* Part 3: counting.  Inversion over the sets `S` turns "the positions of `S` are occurrences"
  into "exactly `s` occurrences"; neighbouring exchanges generate all rearrangements.
-/

namespace StablePattern

/-! ## Part 1: value sequences -/

/-- An occurrence of 12435 at position `i` of the value sequence `e`. -/
def Pat (e : ℕ → ℕ) (i : ℕ) : Prop :=
  e i < e (i + 1) ∧ e (i + 1) < e (i + 3) ∧ e (i + 3) < e (i + 2) ∧ e (i + 2) < e (i + 4)

instance instDecPat (e : ℕ → ℕ) (i : ℕ) : Decidable (Pat e i) := by
  unfold Pat; infer_instance

/-- The positions `t` and `t + 1` lie in one marked occurrence. -/
def Linked (S : Finset ℕ) (t : ℕ) : Prop := ∃ i ∈ S, i ≤ t ∧ t < i + 4

/-- `x` and `y` lie in the same run of overlapping marked occurrences. -/
def R (S : Finset ℕ) (x y : ℕ) : Prop :=
  (∀ t, x ≤ t → t < y → Linked S t) ∧ (∀ t, y ≤ t → t < x → Linked S t)

theorem R.refl (S : Finset ℕ) (x : ℕ) : R S x x :=
  ⟨fun t h1 h2 => by omega, fun t h1 h2 => by omega⟩

theorem R.symm {S : Finset ℕ} {x y : ℕ} (h : R S x y) : R S y x := ⟨h.2, h.1⟩

theorem R.trans {S : Finset ℕ} {x y z : ℕ} (h1 : R S x y) (h2 : R S y z) : R S x z := by
  constructor
  · intro t ht1 ht2
    by_cases c : t < y
    · exact h1.1 t ht1 c
    · exact h2.1 t (by omega) ht2
  · intro t ht1 ht2
    by_cases c : t < y
    · exact h2.2 t ht1 c
    · exact h1.2 t (by omega) ht2

theorem R_window {S : Finset ℕ} {i : ℕ} (hi : i ∈ S) {x y : ℕ} (hx : i ≤ x) (hx' : x ≤ i + 4)
    (hy : i ≤ y) (hy' : y ≤ i + 4) : R S x y :=
  ⟨fun t h1 h2 => ⟨i, hi, by omega, by omega⟩, fun t h1 h2 => ⟨i, hi, by omega, by omega⟩⟩

/-- Two marked occurrences start at least three positions apart. -/
theorem valid {e : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ i ∈ S, Pat e i) {i j : ℕ}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i < j) : i + 3 ≤ j := by
  by_contra hcon
  have h1 : e i < e (i + 1) ∧ e (i + 1) < e (i + 3) ∧ e (i + 3) < e (i + 2) ∧
      e (i + 2) < e (i + 4) := hS i hi
  have hc : j = i + 1 ∨ j = i + 2 := by omega
  rcases hc with h | h
  · rw [h] at hj
    have h2 : e (i + 1) < e (i + 2) ∧ e (i + 2) < e (i + 4) ∧ e (i + 4) < e (i + 3) ∧
        e (i + 3) < e (i + 5) := hS (i + 1) hj
    omega
  · rw [h] at hj
    have h2 : e (i + 2) < e (i + 3) ∧ e (i + 3) < e (i + 5) ∧ e (i + 5) < e (i + 4) ∧
        e (i + 4) < e (i + 6) := hS (i + 2) hj
    omega

/-- Straightening of positions: the two middle positions of every marked occurrence are
exchanged. -/
def idx (S : Finset ℕ) (t : ℕ) : ℕ :=
  if 2 ≤ t ∧ t - 2 ∈ S then t + 1 else if 3 ≤ t ∧ t - 3 ∈ S then t - 1 else t

theorem idx_cases (S : Finset ℕ) (t : ℕ) :
    (∃ i ∈ S, t = i + 2 ∧ idx S t = i + 3) ∨ (∃ i ∈ S, t = i + 3 ∧ idx S t = i + 2) ∨
      (idx S t = t ∧ ∀ i ∈ S, t ≠ i + 2 ∧ t ≠ i + 3) := by
  unfold idx
  by_cases h1 : 2 ≤ t ∧ t - 2 ∈ S
  · left
    have h1' := h1.1
    exact ⟨t - 2, h1.2, by omega, by rw [ite_eq_left h1]; omega⟩
  · by_cases h2 : 3 ≤ t ∧ t - 3 ∈ S
    · right; left
      have h2' := h2.1
      exact ⟨t - 3, h2.2, by omega, by rw [ite_eq_right h1, ite_eq_left h2]; omega⟩
    · right; right
      refine ⟨by rw [ite_eq_right h1, ite_eq_right h2], fun i hi =>
        ⟨fun h => h1 ⟨by omega, ?_⟩, fun h => h2 ⟨by omega, ?_⟩⟩⟩
      · rw [show t - 2 = i by omega]; exact hi
      · rw [show t - 3 = i by omega]; exact hi

theorem idx_two {e : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ i ∈ S, Pat e i) {i : ℕ} (hi : i ∈ S) :
    idx S (i + 2) = i + 3 := by
  rcases idx_cases S (i + 2) with ⟨j, hj, h1, h2⟩ | ⟨j, hj, h1, h2⟩ | ⟨_, hn⟩
  · have hji : j = i := by omega
    rw [h2, hji]
  · have hji : j < i := by omega
    have := valid hS hj hi hji
    omega
  · exact ((hn i hi).1 rfl).elim

theorem idx_three {e : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ i ∈ S, Pat e i) {i : ℕ} (hi : i ∈ S) :
    idx S (i + 3) = i + 2 := by
  rcases idx_cases S (i + 3) with ⟨j, hj, h1, h2⟩ | ⟨j, hj, h1, h2⟩ | ⟨_, hn⟩
  · have hij : i < j := by omega
    have := valid hS hi hj hij
    omega
  · have hji : j = i := by omega
    rw [h2, hji]
  · exact ((hn i hi).2 rfl).elim

theorem idx_one {e : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ i ∈ S, Pat e i) {i : ℕ} (hi : i ∈ S) :
    idx S (i + 1) = i + 1 := by
  rcases idx_cases S (i + 1) with ⟨j, hj, h1, h2⟩ | ⟨j, hj, h1, h2⟩ | ⟨h, _⟩
  · have hji : j < i := by omega
    have := valid hS hj hi hji
    omega
  · have hji : j < i := by omega
    have := valid hS hj hi hji
    omega
  · exact h

theorem idx_four {e : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ i ∈ S, Pat e i) {i : ℕ} (hi : i ∈ S) :
    idx S (i + 4) = i + 4 := by
  rcases idx_cases S (i + 4) with ⟨j, hj, h1, h2⟩ | ⟨j, hj, h1, h2⟩ | ⟨h, _⟩
  · have hij : i < j := by omega
    have := valid hS hi hj hij
    omega
  · have hij : i < j := by omega
    have := valid hS hi hj hij
    omega
  · exact h

theorem idx_zero {e : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ i ∈ S, Pat e i) {i : ℕ} (hi : i ∈ S) :
    idx S i = i ∨ ∃ j ∈ S, i = j + 3 ∧ idx S i = j + 2 := by
  rcases idx_cases S i with ⟨j, hj, h1, h2⟩ | ⟨j, hj, h1, h2⟩ | ⟨h, _⟩
  · have hji : j < i := by omega
    have := valid hS hj hi hji
    omega
  · right; exact ⟨j, hj, h1, h2⟩
  · left; exact h

/-- Along a linked step the straightened values increase. -/
theorem stepB {e : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ i ∈ S, Pat e i) {t : ℕ} (ht : Linked S t) :
    e (idx S t) < e (idx S (t + 1)) := by
  obtain ⟨i, hi, h1, h2⟩ := ht
  have hP : e i < e (i + 1) ∧ e (i + 1) < e (i + 3) ∧ e (i + 3) < e (i + 2) ∧
      e (i + 2) < e (i + 4) := hS i hi
  have hc : t = i ∨ t = i + 1 ∨ t = i + 2 ∨ t = i + 3 := by omega
  rcases hc with h | h | h | h
  · rw [h, idx_one hS hi]
    rcases idx_zero hS hi with h0 | ⟨j, hj, hj1, hj2⟩
    · rw [h0]; exact hP.1
    · rw [hj2]
      have hQ : e j < e (j + 1) ∧ e (j + 1) < e (j + 3) ∧ e (j + 3) < e (j + 2) ∧
          e (j + 2) < e (j + 4) := hS j hj
      have hij : i + 1 = j + 4 := by omega
      rw [hij]; exact hQ.2.2.2
  · rw [h, idx_one hS hi, show i + 1 + 1 = i + 2 from rfl, idx_two hS hi]; exact hP.2.1
  · rw [h, idx_two hS hi, show i + 2 + 1 = i + 3 from rfl, idx_three hS hi]; exact hP.2.2.1
  · rw [h, idx_three hS hi, show i + 3 + 1 = i + 4 from rfl, idx_four hS hi]; exact hP.2.2.2

theorem mono {e : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ i ∈ S, Pat e i) (x : ℕ) :
    ∀ y, x < y → (∀ t, x ≤ t → t < y → Linked S t) → e (idx S x) < e (idx S y) := by
  intro y
  induction y with
  | zero => intro h; omega
  | succ y ih =>
    intro hxy hl
    rcases Nat.lt_or_ge x y with h | h
    · exact lt_trans (ih h (fun t h1 h2 => hl t h1 (by omega)))
        (stepB hS (hl y (by omega) (by omega)))
    · have hxy' : y = x := by omega
      rw [hxy']
      exact stepB hS (hl x (le_refl x) (by omega))

theorem R_idx (S : Finset ℕ) (x : ℕ) : R S (idx S x) x := by
  rcases idx_cases S x with ⟨i, hi, h1, h2⟩ | ⟨i, hi, h1, h2⟩ | ⟨h2, _⟩
  · rw [h2, h1]
    exact ⟨fun t a b => by omega, fun t a b => ⟨i, hi, by omega, by omega⟩⟩
  · rw [h2, h1]
    exact ⟨fun t a b => ⟨i, hi, by omega, by omega⟩, fun t a b => by omega⟩
  · rw [h2]; exact R.refl S x

theorem idx_idx {e : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ i ∈ S, Pat e i) (x : ℕ) :
    idx S (idx S x) = x := by
  rcases idx_cases S x with ⟨i, hi, h1, h2⟩ | ⟨i, hi, h1, h2⟩ | ⟨h2, _⟩
  · rw [h2, h1]; exact idx_three hS hi
  · rw [h2, h1]; exact idx_two hS hi
  · rw [h2, h2]

/-- Inside a run all values are different. -/
theorem distinct {e : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ i ∈ S, Pat e i) {x y : ℕ}
    (hR : R S x y) (hxy : x ≠ y) : e x ≠ e y := by
  have hR' : R S (idx S x) (idx S y) := (R_idx S x).trans (hR.trans (R_idx S y).symm)
  have hne : idx S x ≠ idx S y := by
    intro h
    have h' := congrArg (idx S) h
    rw [idx_idx hS x, idx_idx hS y] at h'
    exact hxy h'
  have key : e (idx S (idx S x)) ≠ e (idx S (idx S y)) := by
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ne_of_lt (mono hS _ _ h hR'.1)
    · exact (ne_of_lt (mono hS _ _ h hR'.2)).symm
  rwa [idx_idx hS x, idx_idx hS y] at key

/-! ## Part 2: words -/

variable {m n : ℕ}

/-- The letter values of a word, as a function on all of `ℕ`. -/
def ev (w : Fin m → Fin n) (t : ℕ) : ℕ := if h : t < m then (w ⟨t, h⟩ : ℕ) else 0

theorem ev_lt (w : Fin m → Fin n) {t : ℕ} (h : t < m) : ev w t = (w ⟨t, h⟩ : ℕ) := by
  unfold ev; exact dite_eq_left h

theorem ev_fin (w : Fin m → Fin n) (x : Fin m) : ev w x = (w x : ℕ) := ev_lt w x.isLt

theorem ev_lt_of (w : Fin m → Fin n) {s t : ℕ} (hs : s < m) (ht : t < m) :
    w ⟨s, hs⟩ < w ⟨t, ht⟩ ↔ ev w s < ev w t := by
  rw [ev_lt w hs, ev_lt w ht]; exact Iff.rfl

/-- Every position of `S` starts an occurrence of 12435 in `w`. -/
def Marked (S : Finset ℕ) (w : Fin m → Fin n) : Prop := ∀ i ∈ S, i + 5 ≤ m ∧ Pat (ev w) i

/-- The run of `x` holds the letter `c`. -/
def Has (S : Finset ℕ) (w : Fin m → Fin n) (c : Fin n) (x : ℕ) : Prop :=
  ∃ y : Fin m, R S x y ∧ w y = c

/-- The run of `x` holds both letters `a` and `b`. -/
def Both (S : Finset ℕ) (a b : Fin n) (w : Fin m → Fin n) (x : ℕ) : Prop :=
  Has S w a x ∧ Has S w b x

theorem has_congr {S : Finset ℕ} {w : Fin m → Fin n} {c : Fin n} {x x' : ℕ} (h : R S x x') :
    Has S w c x ↔ Has S w c x' :=
  ⟨fun ⟨y, hy, hw⟩ => ⟨y, h.symm.trans hy, hw⟩, fun ⟨y, hy, hw⟩ => ⟨y, h.trans hy, hw⟩⟩

theorem both_congr {S : Finset ℕ} {a b : Fin n} {w : Fin m → Fin n} {x x' : ℕ}
    (h : R S x x') : Both S a b w x ↔ Both S a b w x' :=
  and_congr (has_congr h) (has_congr h)

open Classical in
/-- Exchange the letters `a` and `b` in every run that does not hold both. -/
noncomputable def flp (S : Finset ℕ) (a b : Fin n) (w : Fin m → Fin n) (x : Fin m) : Fin n :=
  if Both S a b w x then w x else Equiv.swap a b (w x)

theorem flp_pos {S : Finset ℕ} {a b : Fin n} {w : Fin m → Fin n} (x : Fin m)
    (h : Both S a b w x) : flp S a b w x = w x := by
  unfold flp; exact ite_eq_left h

theorem flp_neg {S : Finset ℕ} {a b : Fin n} {w : Fin m → Fin n} (x : Fin m)
    (h : ¬ Both S a b w x) : flp S a b w x = Equiv.swap a b (w x) := by
  unfold flp; exact ite_eq_right h

theorem has_flp_pos {S : Finset ℕ} {a b : Fin n} {w : Fin m → Fin n} {x : ℕ}
    (hb : Both S a b w x) (c : Fin n) : Has S (flp S a b w) c x ↔ Has S w c x := by
  constructor
  · rintro ⟨y, hy, hw⟩
    exact ⟨y, hy, (flp_pos y ((both_congr hy).mp hb)).symm.trans hw⟩
  · rintro ⟨y, hy, hw⟩
    exact ⟨y, hy, (flp_pos y ((both_congr hy).mp hb)).trans hw⟩

theorem has_flp_neg {S : Finset ℕ} {a b : Fin n} {w : Fin m → Fin n} {x : ℕ}
    (hb : ¬ Both S a b w x) (c : Fin n) :
    Has S (flp S a b w) c x ↔ Has S w (Equiv.swap a b c) x := by
  have hy' : ∀ y : Fin m, R S x y → flp S a b w y = Equiv.swap a b (w y) :=
    fun y hy => flp_neg y (fun h => hb ((both_congr hy).mpr h))
  constructor
  · rintro ⟨y, hy, hw⟩
    rw [hy' y hy] at hw
    exact ⟨y, hy, Equiv.swap_apply_eq_iff.mp hw⟩
  · rintro ⟨y, hy, hw⟩
    refine ⟨y, hy, ?_⟩
    rw [hy' y hy]
    exact Equiv.swap_apply_eq_iff.mpr hw

theorem both_flp {S : Finset ℕ} {a b : Fin n} {w : Fin m → Fin n} (x : ℕ) :
    Both S a b (flp S a b w) x ↔ Both S a b w x := by
  by_cases hb : Both S a b w x
  · exact and_congr (has_flp_pos hb a) (has_flp_pos hb b)
  · have h1 := has_flp_neg hb a
    have h2 := has_flp_neg hb b
    rw [Equiv.swap_apply_left] at h1
    rw [Equiv.swap_apply_right] at h2
    exact ⟨fun h => ⟨h2.mp h.2, h1.mp h.1⟩, fun h => ⟨h1.mpr h.2, h2.mpr h.1⟩⟩

theorem flp_flp {S : Finset ℕ} {a b : Fin n} (w : Fin m → Fin n) :
    flp S a b (flp S a b w) = w := by
  funext x
  by_cases hb : Both S a b w x
  · rw [flp_pos x ((both_flp (x : ℕ)).mpr hb), flp_pos x hb]
  · rw [flp_neg x (fun h => hb ((both_flp (x : ℕ)).mp h)), flp_neg x hb, Equiv.swap_apply_self]

/-- The exchange of `a` and `a + 1` on natural numbers. -/
def sw (a v : ℕ) : ℕ := if v = a then a + 1 else if v = a + 1 then a else v

theorem sw_lt {a c d : ℕ} (h : c < d) (hnb : ¬ (c = a ∧ d = a + 1)) : sw a c < sw a d := by
  unfold sw
  split_ifs <;> omega

theorem swap_val {a b : Fin n} (hab : (b : ℕ) = a + 1) (c : Fin n) :
    ((Equiv.swap a b c : Fin n) : ℕ) = sw a c := by
  unfold sw
  by_cases h1 : c = a
  · rw [h1, Equiv.swap_apply_left, ite_eq_left rfl]; exact hab
  · by_cases h2 : c = b
    · have h3 : ¬ ((b : ℕ) = a) := by omega
      rw [h2, Equiv.swap_apply_right, ite_eq_right h3, ite_eq_left hab]
    · have h3 : ¬ ((c : ℕ) = a) := fun h => h1 (Fin.ext h)
      have h4 : ¬ ((c : ℕ) = a + 1) := fun h => h2 (Fin.ext (by omega))
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, ite_eq_right h3, ite_eq_right h4]

theorem ev_flp_pos {S : Finset ℕ} {a b : Fin n} {w : Fin m → Fin n} {t : ℕ} (h : t < m)
    (hb : Both S a b w t) : ev (flp S a b w) t = ev w t := by
  rw [ev_lt _ h, ev_lt _ h, flp_pos ⟨t, h⟩ hb]

theorem ev_flp_neg {S : Finset ℕ} {a b : Fin n} (hab : (b : ℕ) = a + 1) {w : Fin m → Fin n}
    {t : ℕ} (h : t < m) (hb : ¬ Both S a b w t) :
    ev (flp S a b w) t = sw a (ev w t) := by
  rw [ev_lt _ h, ev_lt _ h, flp_neg ⟨t, h⟩ hb, swap_val hab]

/-- The exchange keeps the marked occurrences. -/
theorem marked_flp {S : Finset ℕ} {a b : Fin n} (hab : (b : ℕ) = a + 1) {w : Fin m → Fin n}
    (hM : Marked S w) : Marked S (flp S a b w) := by
  intro i hi
  obtain ⟨hm, hP⟩ := hM i hi
  refine ⟨hm, ?_⟩
  unfold Pat at hP ⊢
  by_cases hb : Both S a b w i
  · have key : ∀ t, i ≤ t → t ≤ i + 4 → ev (flp S a b w) t = ev w t := fun t h1 h2 =>
      ev_flp_pos (by omega) ((both_congr (R_window hi (le_refl _) (by omega) h1 h2)).mp hb)
    rw [key i (le_refl _) (by omega), key (i + 1) (by omega) (by omega),
      key (i + 2) (by omega) (by omega), key (i + 3) (by omega) (by omega),
      key (i + 4) (by omega) (by omega)]
    exact hP
  · have key : ∀ t, i ≤ t → t ≤ i + 4 → ev (flp S a b w) t = sw a (ev w t) := fun t h1 h2 =>
      ev_flp_neg hab (by omega)
        (fun h => hb ((both_congr (R_window hi (le_refl _) (by omega) h1 h2)).mpr h))
    have nb : ∀ t t', i ≤ t → t ≤ i + 4 → i ≤ t' → t' ≤ i + 4 →
        ¬ (ev w t = a ∧ ev w t' = a + 1) := by
      intro t t' h1 h2 h3 h4 hh
      obtain ⟨e1, e2⟩ := hh
      have ht : t < m := by omega
      have ht' : t' < m := by omega
      rw [ev_lt w ht] at e1
      rw [ev_lt w ht'] at e2
      exact hb ⟨⟨⟨t, ht⟩, R_window hi (le_refl _) (by omega) h1 h2, Fin.ext e1⟩,
        ⟨⟨t', ht'⟩, R_window hi (le_refl _) (by omega) h3 h4, Fin.ext (by rw [hab]; exact e2)⟩⟩
    rw [key i (le_refl _) (by omega), key (i + 1) (by omega) (by omega),
      key (i + 2) (by omega) (by omega), key (i + 3) (by omega) (by omega),
      key (i + 4) (by omega) (by omega)]
    exact ⟨sw_lt hP.1 (nb i (i + 1) (le_refl _) (by omega) (by omega) (by omega)),
      sw_lt hP.2.1 (nb (i + 1) (i + 3) (by omega) (by omega) (by omega) (by omega)),
      sw_lt hP.2.2.1 (nb (i + 3) (i + 2) (by omega) (by omega) (by omega) (by omega)),
      sw_lt hP.2.2.2 (nb (i + 2) (i + 4) (by omega) (by omega) (by omega) (by omega))⟩

/-- One half of the count: an injection from the positions of `c` in the exchanged word to
the positions of the exchanged letter in the word. -/
theorem mult_flp_le {S : Finset ℕ} {a b : Fin n} {w : Fin m → Fin n} (hM : Marked S w)
    (c : Fin n) : mult (flp S a b w) c ≤ mult w (Equiv.swap a b c) := by
  classical
  unfold mult
  apply Finset.card_le_card_of_forall_subsingleton (fun x y : Fin m => R S x y)
  · intro x hx
    have hx' : flp S a b w x = c := (Finset.mem_filter.mp hx).2
    by_cases hb : Both S a b w x
    · rw [flp_pos x hb] at hx'
      by_cases h1 : c = a
      · obtain ⟨y, hy, hw⟩ := hb.2
        refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hy⟩
        rw [h1, Equiv.swap_apply_left]; exact hw
      · by_cases h2 : c = b
        · obtain ⟨y, hy, hw⟩ := hb.1
          refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hy⟩
          rw [h2, Equiv.swap_apply_right]; exact hw
        · refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, R.refl S x⟩
          rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hx'
    · rw [flp_neg x hb] at hx'
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Equiv.swap_apply_eq_iff.mp hx'⟩,
        R.refl S x⟩
  · intro y _ x hx x' hx'
    obtain ⟨hxs, hxy⟩ := hx
    obtain ⟨hxs', hxy'⟩ := hx'
    have e1 : flp S a b w x = c := (Finset.mem_filter.mp hxs).2
    have e2 : flp S a b w x' = c := (Finset.mem_filter.mp hxs').2
    have hR : R S x x' := hxy.trans hxy'.symm
    have hw : w x = w x' := by
      by_cases hb : Both S a b w x
      · have hb' := (both_congr hR).mp hb
        rw [flp_pos x hb] at e1
        rw [flp_pos x' hb'] at e2
        rw [e1, e2]
      · have hb' : ¬ Both S a b w x' := fun h => hb ((both_congr hR).mpr h)
        rw [flp_neg x hb] at e1
        rw [flp_neg x' hb'] at e2
        exact (Equiv.swap a b).injective (e1.trans e2.symm)
    by_contra hne
    have hne' : (x : ℕ) ≠ x' := fun h => hne (Fin.ext h)
    have hd := distinct (fun i hi => (hM i hi).2) hR hne'
    rw [ev_fin, ev_fin] at hd
    exact hd (congrArg Fin.val hw)

/-- The exchange exchanges the two letter counts. -/
theorem mult_flp {S : Finset ℕ} {a b : Fin n} (hab : (b : ℕ) = a + 1) {w : Fin m → Fin n}
    (hM : Marked S w) (c : Fin n) : mult (flp S a b w) c = mult w (Equiv.swap a b c) := by
  apply le_antisymm (mult_flp_le hM c)
  have h := mult_flp_le (a := a) (b := b) (marked_flp hab hM) (Equiv.swap a b c)
  rwa [flp_flp, Equiv.swap_apply_self] at h

/-! ## Part 3: counting -/

/-- The set of positions where 12435 occurs in `w`. -/
def occSet (w : Fin m → Fin n) : Finset ℕ :=
  (Finset.range m).filter (fun i => i + 5 ≤ m ∧ Pat (ev w) i)

theorem marked_iff (S : Finset ℕ) (w : Fin m → Fin n) : S ⊆ occSet w ↔ Marked S w := by
  constructor
  · intro h i hi
    exact (Finset.mem_filter.mp (h hi)).2
  · intro h i hi
    have h5 := (h i hi).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h i hi⟩

theorem pval : ∀ a : Fin 5, ((p12435 a : Fin 5) : ℕ) =
    if (a : ℕ) = 2 then 3 else if (a : ℕ) = 3 then 2 else (a : ℕ) := by
  decide

theorem occAt_iff (w : Fin m → Fin n) (i : ℕ) :
    OccAt p12435 w i ↔ (i + 5 ≤ m ∧ Pat (ev w) i) := by
  constructor
  · rintro ⟨h, H⟩
    refine ⟨h, ?_⟩
    have h01 := (ev_lt_of w _ _).mp ((H 0 1).mp (by decide))
    have h13 := (ev_lt_of w _ _).mp ((H 1 3).mp (by decide))
    have h32 := (ev_lt_of w _ _).mp ((H 3 2).mp (by decide))
    have h24 := (ev_lt_of w _ _).mp ((H 2 4).mp (by decide))
    exact ⟨h01, h13, h32, h24⟩
  · rintro ⟨h, hP⟩
    refine ⟨h, fun a b => ?_⟩
    have ha := a.isLt
    have hb := b.isLt
    rw [ev_lt_of w (show i + (a : ℕ) < m by omega) (show i + (b : ℕ) < m by omega), Fin.lt_def,
      pval a, pval b]
    have q0 : ev w (i + 0) < ev w (i + 1) := hP.1
    have q1 : ev w (i + 1) < ev w (i + 3) := hP.2.1
    have q2 : ev w (i + 3) < ev w (i + 2) := hP.2.2.1
    have q3 : ev w (i + 2) < ev w (i + 4) := hP.2.2.2
    have ca : (a : ℕ) = 0 ∨ (a : ℕ) = 1 ∨ (a : ℕ) = 2 ∨ (a : ℕ) = 3 ∨ (a : ℕ) = 4 := by omega
    have cb : (b : ℕ) = 0 ∨ (b : ℕ) = 1 ∨ (b : ℕ) = 2 ∨ (b : ℕ) = 3 ∨ (b : ℕ) = 4 := by omega
    rcases ca with h | h | h | h | h <;> rcases cb with h' | h' | h' | h' | h' <;>
      rw [h, h'] <;> split_ifs <;> first | omega | contradiction

theorem occ_eq (w : Fin m → Fin n) : occ p12435 w = (occSet w).card := by
  unfold occ
  have hset : {i : ℕ | OccAt p12435 w i} = ↑(occSet w) := by
    ext i
    rw [Set.mem_ofPred_eq, Finset.mem_coe, occAt_iff]
    unfold occSet
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      have h5 := h.1
      exact ⟨by omega, h⟩
    · intro h
      exact h.2
  rw [hset, Set.ncard_coe_finset]

/-- The words with letter counts `k`. -/
def Wk (m : ℕ) {n : ℕ} (k : Fin n → ℕ) : Finset (Fin m → Fin n) :=
  Finset.univ.filter (fun w => ∀ a, mult w a = k a)

theorem mem_Wk {k : Fin n → ℕ} {w : Fin m → Fin n} : w ∈ Wk m k ↔ ∀ a, mult w a = k a := by
  unfold Wk
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- For neighbouring letters, the number of words with given marked occurrences does not
change when the two letter counts are exchanged. -/
theorem G_eq {a b : Fin n} (hab : (b : ℕ) = a + 1) (k : Fin n → ℕ) (S : Finset ℕ) :
    ((Wk m k).filter (fun w => S ⊆ occSet w)).card =
      ((Wk m (fun c => k (Equiv.swap a b c))).filter (fun w => S ⊆ occSet w)).card := by
  have key : ∀ (k₁ k₂ : Fin n → ℕ), (∀ c, k₂ c = k₁ (Equiv.swap a b c)) →
      ∀ w ∈ (Wk m k₁).filter (fun w => S ⊆ occSet w),
        flp S a b w ∈ (Wk m k₂).filter (fun w => S ⊆ occSet w) := by
    intro k₁ k₂ hk w hw
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hw
    have hM := (marked_iff S w).mp h2
    have hk1 := mem_Wk.mp h1
    refine Finset.mem_filter.mpr
      ⟨mem_Wk.mpr (fun c => ?_), (marked_iff S _).mpr (marked_flp hab hM)⟩
    rw [mult_flp hab hM c, hk1, hk c]
  apply Finset.card_nbij' (flp S a b) (flp S a b)
  · intro w hw
    exact Finset.mem_coe.mpr (key k _ (fun c => rfl) w (Finset.mem_coe.mp hw))
  · intro w hw
    refine Finset.mem_coe.mpr (key _ k (fun c => ?_) w (Finset.mem_coe.mp hw))
    show k c = k (Equiv.swap a b (Equiv.swap a b c))
    rw [Equiv.swap_apply_self]
  · intro w _
    exact flp_flp w
  · intro w _
    exact flp_flp w

/-- Inversion over subsets: equal counts of "contains `S`" give equal counts of "equals `T`". -/
theorem moebius {α : Type*} (W W' : Finset α) (O : α → Finset ℕ) (U : Finset ℕ)
    (hU : ∀ w, O w ⊆ U)
    (hG : ∀ S, S ⊆ U →
      (W.filter (fun w => S ⊆ O w)).card = (W'.filter (fun w => S ⊆ O w)).card) :
    ∀ T, T ⊆ U → (W.filter (fun w => O w = T)).card = (W'.filter (fun w => O w = T)).card := by
  have expand : ∀ (V : Finset α) (T : Finset ℕ), T ⊆ U →
      (V.filter (fun w => T ⊆ O w)).card =
        (V.filter (fun w => O w = T)).card +
          ∑ T' ∈ (U.powerset.filter (fun T' => T ⊆ T')).erase T,
            (V.filter (fun w => O w = T')).card := by
    intro V T hT
    have hmem : T ∈ U.powerset.filter (fun T' => T ⊆ T') :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT, Finset.Subset.refl T⟩
    have h1 : (V.filter (fun w => T ⊆ O w)).card =
        ∑ T' ∈ U.powerset.filter (fun T' => T ⊆ T'),
          ((V.filter (fun w => T ⊆ O w)).filter (fun w => O w = T')).card :=
      Finset.card_eq_sum_card_fiberwise (fun w hw =>
        Finset.mem_coe.mpr (Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (hU w), (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2⟩))
    have h2 : ∀ T' ∈ U.powerset.filter (fun T' => T ⊆ T'),
        ((V.filter (fun w => T ⊆ O w)).filter (fun w => O w = T')).card =
          (V.filter (fun w => O w = T')).card := by
      intro T' hT'
      have hTT' := (Finset.mem_filter.mp hT').2
      congr 1
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hv, _⟩, hc⟩
        exact ⟨hv, hc⟩
      · rintro ⟨hv, hc⟩
        exact ⟨⟨hv, by rw [hc]; exact hTT'⟩, hc⟩
    rw [h1, Finset.sum_congr rfl h2, ← Finset.add_sum_erase _ _ hmem]
  intro T
  induction' hd : U.card - T.card using Nat.strong_induction_on with d ih generalizing T
  intro hT
  have e1 := expand W T hT
  have e2 := expand W' T hT
  have hsum : ∑ T' ∈ (U.powerset.filter (fun T' => T ⊆ T')).erase T,
        (W.filter (fun w => O w = T')).card =
      ∑ T' ∈ (U.powerset.filter (fun T' => T ⊆ T')).erase T,
        (W'.filter (fun w => O w = T')).card := by
    apply Finset.sum_congr rfl
    intro T' hT'
    obtain ⟨hne, hT'2⟩ := Finset.mem_erase.mp hT'
    obtain ⟨hT'U, hTT'⟩ := Finset.mem_filter.mp hT'2
    have hT'U' := Finset.mem_powerset.mp hT'U
    have hlt : T.card < T'.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTT', fun h => hne h.symm⟩)
    have hle : T'.card ≤ U.card := Finset.card_le_card hT'U'
    exact ih (U.card - T'.card) (by omega) T' rfl hT'U'
  have hg := hG T hT
  omega

/-- Equal counts for every exact set give equal counts for every number of occurrences. -/
theorem count_by_card {α : Type*} (W W' : Finset α) (O : α → Finset ℕ) (U : Finset ℕ)
    (hU : ∀ w, O w ⊆ U)
    (hE : ∀ T, T ⊆ U →
      (W.filter (fun w => O w = T)).card = (W'.filter (fun w => O w = T)).card) (s : ℕ) :
    (W.filter (fun w => (O w).card = s)).card = (W'.filter (fun w => (O w).card = s)).card := by
  have expand : ∀ V : Finset α, (V.filter (fun w => (O w).card = s)).card =
      ∑ T ∈ U.powerset, if T.card = s then (V.filter (fun w => O w = T)).card else 0 := by
    intro V
    have h1 : (V.filter (fun w => (O w).card = s)).card =
        ∑ T ∈ U.powerset, ((V.filter (fun w => (O w).card = s)).filter (fun w => O w = T)).card :=
      Finset.card_eq_sum_card_fiberwise (fun w _ =>
        Finset.mem_coe.mpr (Finset.mem_powerset.mpr (hU w)))
    rw [h1]
    apply Finset.sum_congr rfl
    intro T _
    by_cases h : T.card = s
    · rw [ite_eq_left h]
      congr 1
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hv, _⟩, hc⟩
        exact ⟨hv, hc⟩
      · rintro ⟨hv, hc⟩
        exact ⟨⟨hv, by rw [hc]; exact h⟩, hc⟩
    · rw [ite_eq_right h]
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw hc
      exact h (by rw [← hc]; exact (Finset.mem_filter.mp hw).2)
  rw [expand W, expand W']
  apply Finset.sum_congr rfl
  intro T hT
  rw [hE T (Finset.mem_powerset.mp hT)]

/-- Stability under the exchange of two neighbouring letters. -/
theorem adj {a b : Fin n} (hab : (b : ℕ) = a + 1) (k : Fin n → ℕ) (s : ℕ) :
    ((Wk m k).filter (fun w => (occSet w).card = s)).card =
      ((Wk m (fun c => k (Equiv.swap a b c))).filter (fun w => (occSet w).card = s)).card :=
  count_by_card _ _ occSet (Finset.range m) (fun _ => Finset.filter_subset _ _)
    (moebius _ _ occSet (Finset.range m) (fun _ => Finset.filter_subset _ _)
      (fun S _ => G_eq hab k S)) s

/-- Stability under every rearrangement of the letter counts. -/
theorem all_perm : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (k : Fin n → ℕ) (s : ℕ),
    ((Wk m k).filter (fun w => (occSet w).card = s)).card =
      ((Wk m (fun c => k (σ c))).filter (fun w => (occSet w).card = s)).card := by
  intro n
  cases n with
  | zero =>
    intro σ k s
    have hk : (fun c => k (σ c)) = k := funext (fun c => c.elim0)
    rw [hk]
  | succ n =>
    intro σ
    have hσ : σ ∈ Submonoid.closure
        (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ
    induction hσ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro k s
      exact adj (by simp) k s
    | one =>
      intro k s
      rfl
    | mul x y _ _ hx hy =>
      intro k s
      exact (hx k s).trans (hy (fun c => k (x c)) s)

theorem stable : PatternStable p12435 := by
  intro m n k σ s
  have cv : ∀ k' : Fin n → ℕ,
      Set.ncard {w : Fin m → Fin n | (∀ a, mult w a = k' a) ∧ occ p12435 w = s} =
        ((Wk m k').filter (fun w => (occSet w).card = s)).card := by
    intro k'
    have hset : {w : Fin m → Fin n | (∀ a, mult w a = k' a) ∧ occ p12435 w = s} =
        ↑((Wk m k').filter (fun w => (occSet w).card = s)) := by
      ext w
      rw [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, mem_Wk, occ_eq]
    rw [hset, Set.ncard_coe_finset]
  rw [cv k, cv (fun a => k (σ a))]
  exact all_perm n σ k s

end StablePattern

theorem result : Claim := by
  refine ⟨StablePattern.stable, ?_⟩
  rintro (h | h)
  · exact absurd (h (show (2 : Fin 5) < 3 by decide)) (by decide)
  · exact absurd (h (show (0 : Fin 5) < 1 by decide)) (by decide)

module

public import Mathlib

/-!
# Horton's theorem: point sets with no empty convex 7-gon (Erdős Problem 216, `k ≥ 7`)

This is the solution module of the Palomar / Comparator entry: it proves the theorems stated
with `sorry` in `Challenge.lean` (`Horton.horton_euclidean`, `Horton.erdos_216_ge_seven`,
`Horton.cardSet'_eq_empty`, `Horton.erdos_216'`). It does not import `Challenge`; the
definitions used by those statements are repeated here verbatim, as Comparator requires.

Erdős Problem 216 asks for `g(k)`, the least `n` such that every set of `n` points in the
plane in general position contains an *empty convex `k`-gon* (`k` points in convex position
whose convex hull contains no other point of the set). Horton showed that `g(k)` does not
exist for `k ≥ 7`: for every `N` there is a set of `N` points in general position without an
empty convex `7`-gon.

* J. D. Horton, *Sets with no empty convex 7-gons*, Canad. Math. Bull. 26 (1983), 482–484.
* J. Matoušek, *Lectures on Discrete Geometry*, §3.2 (exposition followed here).

## Construction

For `N` points we take `k = N` levels, scale `c = 2^(N+1) + 3`, and the points
`(i, hy c N i)` for `i < N`, where `hy c (k+1) i = (i % 2) * c^(k+1) + hy c k (i / 2)`.
Thus the odd-indexed points are a copy of the level-`k` set lifted by `c^(k+1)` (high above
every line through two even-indexed points) and the even-indexed points a copy that stays
low: this is Horton's recursive construction `H(2m) = H_even ∪ H_odd`, with explicit integer
coordinates. We use a prefix of length `N` of the level-`N` set (prefixes of Horton sets are
Horton sets), so that we get exactly `N` points.

## Proof outline

1. `D_succ_same`: for three indices of equal parity, the orientation at level `k+1` is twice
   the orientation of the halved indices at level `k`.
2. `sorted_mixed`: for `i < j < l` not all of the same parity, the orientation is positive iff
   the middle index `j` is even (low).
3. `gen_pos`: no three Horton points are collinear.
4. `cup_cap` (no open 4-cup/4-cap): if `a < b < e < d` form a cup, some Horton point lies
   strictly above one of the edges `ab`, `be`, `ed` (inside its `x`-range); dually for caps.
5. `good_card`: if no Horton point lies strictly inside a triangle spanned by three other
   points of an index set `T` (which holds for the vertex set of an empty convex polygon),
   then `|T| ≤ 6`. If `T` lies in one parity class, halve and induct. Otherwise the even part
   of `T` is a cup and the odd part a cap (else a vertex lies inside a triangle), and by
   step 4 each has at most `3` points (a fourth would produce a point inside the polygon).
6. Bridge to Mathlib geometry: the open triangle cut out by three strict orientation
   inequalities lies in the interior of the convex hull (`triRegion_subset_interior`), and a
   nonzero determinant rules out collinearity (`not_collinear_of_det2`).

## Main results

* `Horton.horton`: `∀ N, ∃ S : Finset (ℝ × ℝ), S.card = N ∧ InGeneralPosition S ∧
  ∀ k, 7 ≤ k → ¬ HasEmptyConvexKGon k S`.
* `Horton.horton_int`: the same with integer coordinates.
* `Horton.horton_euclidean`: the same in `EuclideanSpace ℝ (Fin 2)`.
* `Horton.erdos_216_ge_seven`: for `k ≥ 7` there is no `n` such that every `n`-point set in
  general position has an empty convex `k`-gon.
* `Horton.cardSet'_eq_empty`, `Horton.erdos_216'`: the statements of Erdős Problem 216 in the
  form used by `google-deepmind/formal-conjectures` (PR #6775), with its definitions copied.

Definitions (`InGeneralPosition`, `ConvexPosition`, `HasEmptyConvexKGon`) are stated with
Mathlib's `Collinear`, `convexHull` and `interior`; they follow `EmptyHexagonLean`
(Subercaseaux–Nawrocki–Gallicchio–Codel–Carneiro–Heule), except that emptiness only forbids
points in the *interior* of the hull, which makes the negative statement stronger (the
closed-hull variant `HasEmptyConvexKGon'` is covered by `not_hasEmptyConvexKGon'`).
-/

@[expose] public section

namespace Horton

/-! ### The Horton set and its orientations -/

/-- Integer orientation determinant. -/
def det (p q r : ℤ × ℤ) : ℤ := (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- `y`-coordinates of the Horton set of size `2^k` with scale `c`: the point with index `i`
has `y`-coordinate `∑_{j<k} bit_j(i) * c^(k-j)`. Odd indices (lowest bit `1`) form a copy of the
level-`k-1` set lifted by `c^k`, even indices a copy that stays low. -/
def hy (c : ℤ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | k + 1, i => ((i % 2 : ℕ) : ℤ) * c ^ (k + 1) + hy c k (i / 2)

/-- The `i`-th point of the level-`k` Horton set with scale `c`. -/
def hpt (c : ℤ) (k i : ℕ) : ℤ × ℤ := ((i : ℤ), hy c k i)

/-- Orientation of the triple of Horton points with indices `i, j, l`. -/
def D (c : ℤ) (k i j l : ℕ) : ℤ := det (hpt c k i) (hpt c k j) (hpt c k l)

lemma D_cyc (c : ℤ) (k i j l : ℕ) : D c k i j l = D c k j l i := by
  simp only [D, det]; ring

lemma D_swap (c : ℤ) (k i j l : ℕ) : D c k i j l = - D c k j i l := by
  simp only [D, det]; ring

lemma D_swap23 (c : ℤ) (k i j l : ℕ) : D c k i j l = - D c k i l j := by
  simp only [D, det]; ring

/-- Three points of the same parity: the level-`k+1` orientation is twice the level-`k`
orientation of the halved indices (the two halves of a Horton set are affine copies of the
smaller Horton set, with the `x`-coordinate doubled). -/
lemma D_succ_same (c : ℤ) (k i j l : ℕ) (hij : i % 2 = j % 2) (hjl : j % 2 = l % 2) :
    D c (k + 1) i j l = 2 * D c k (i / 2) (j / 2) (l / 2) := by
  have hi : (i : ℤ) = 2 * ((i / 2 : ℕ) : ℤ) + ((i % 2 : ℕ) : ℤ) := by omega
  have hj : (j : ℤ) = 2 * ((j / 2 : ℕ) : ℤ) + ((i % 2 : ℕ) : ℤ) := by omega
  have hl : (l : ℤ) = 2 * ((l / 2 : ℕ) : ℤ) + ((i % 2 : ℕ) : ℤ) := by omega
  simp only [D, det, hpt, hy, ← hij, ← hjl]
  rw [hi, hj, hl]; ring

lemma hy_bounds (c : ℤ) (hc : 2 ≤ c) : ∀ k i, 0 ≤ hy c k i ∧ hy c k i ≤ 2 * c ^ k := by
  intro k
  induction k with
  | zero => intro i; simp [hy]
  | succ k ih =>
    intro i
    obtain ⟨h1, h2⟩ := ih (i / 2)
    have hm : ((i % 2 : ℕ) : ℤ) = 0 ∨ ((i % 2 : ℕ) : ℤ) = 1 := by
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]
    have hck : 0 ≤ c ^ k := by positivity
    have : 2 * c ^ k ≤ c ^ (k + 1) := by rw [pow_succ]; nlinarith
    simp only [hy]
    rcases hm with h | h <;> rw [h] <;> constructor <;> nlinarith [pow_pos (by linarith : (0:ℤ) < c) (k+1)]

/-- The elementary estimate behind the sign computations for mixed triples. -/
lemma key_est (c : ℤ) (k : ℕ) (hc : 2 ^ (k + 2) + 2 < c) (A B C E : ℤ)
    (hA : 1 ≤ A) (hB : c ^ (k + 1) - 2 * c ^ k ≤ B) (hC : |C| ≤ 2 * c ^ k)
    (hE : |E| ≤ 2 ^ (k + 1)) : 0 < A * B - C * E := by
  have hc2 : (2:ℤ) ≤ c := by have : (0:ℤ) ≤ 2 ^ (k+2) := by positivity
                             linarith
  have hck : 0 < c ^ k := by positivity
  have hB0 : 0 < c ^ (k + 1) - 2 * c ^ k - 2 * c ^ k * 2 ^ (k + 1) := by
    have : c ^ (k + 1) - 2 * c ^ k - 2 * c ^ k * 2 ^ (k + 1)
        = c ^ k * (c - 2 - 2 ^ (k + 2)) := by ring
    rw [this]; apply mul_pos hck; linarith
  have hBpos : 0 < B := by
    have : 0 ≤ 2 * c ^ k * 2 ^ (k + 1) := by positivity
    linarith
  have h1 : B ≤ A * B := by nlinarith [mul_nonneg (sub_nonneg.2 hA) hBpos.le]
  have h2 : C * E ≤ |C| * |E| := by rw [← abs_mul]; exact le_abs_self _
  have h3 : |C| * |E| ≤ 2 * c ^ k * 2 ^ (k + 1) :=
    mul_le_mul hC hE (abs_nonneg _) (by positivity)
  linarith

/-- Two low (even) points `i < j` and a high (odd) point `l`: `l` lies above the line `ij`. -/
lemma F2 (c : ℤ) (k i j l : ℕ) (hc : 2 ^ (k + 2) + 2 < c) (hij : i < j)
    (hi : i % 2 = 0) (hj : j % 2 = 0) (hl : l % 2 = 1)
    (hi' : i < 2 ^ (k + 1)) (hl' : l < 2 ^ (k + 1)) : 0 < D c (k + 1) i j l := by
  have hc2 : (2:ℤ) ≤ c := by have : (0:ℤ) ≤ 2 ^ (k+2) := by positivity
                             linarith
  obtain ⟨a1, a2⟩ := hy_bounds c hc2 k (i / 2)
  obtain ⟨b1, b2⟩ := hy_bounds c hc2 k (j / 2)
  obtain ⟨d1, d2⟩ := hy_bounds c hc2 k (l / 2)
  simp only [D, det, hpt, hy, hi, hj, hl]
  push_cast
  apply key_est c k hc
  · have : (i:ℤ) < j := by exact_mod_cast hij
    linarith
  · rw [pow_succ]; nlinarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]
    have : (i : ℤ) < 2 ^ (k+1) := by exact_mod_cast hi'
    have : (l : ℤ) < 2 ^ (k+1) := by exact_mod_cast hl'
    constructor <;> linarith

/-- Two high (odd) points `i < j` and a low (even) point `l`: `l` lies below the line `ij`. -/
lemma F3 (c : ℤ) (k i j l : ℕ) (hc : 2 ^ (k + 2) + 2 < c) (hij : i < j)
    (hi : i % 2 = 1) (hj : j % 2 = 1) (hl : l % 2 = 0)
    (hi' : i < 2 ^ (k + 1)) (hl' : l < 2 ^ (k + 1)) : D c (k + 1) i j l < 0 := by
  have hc2 : (2:ℤ) ≤ c := by have : (0:ℤ) ≤ 2 ^ (k+2) := by positivity
                             linarith
  obtain ⟨a1, a2⟩ := hy_bounds c hc2 k (i / 2)
  obtain ⟨b1, b2⟩ := hy_bounds c hc2 k (j / 2)
  obtain ⟨d1, d2⟩ := hy_bounds c hc2 k (l / 2)
  simp only [D, det, hpt, hy, hi, hj, hl]
  push_cast
  have := key_est c k hc ((j:ℤ) - i) (c ^ (k+1) + hy c k (i/2) - hy c k (l/2))
    (hy c k (i/2) - hy c k (j/2)) ((l:ℤ) - i) ?_ ?_ ?_ ?_
  · linarith
  · have : (i:ℤ) < j := by exact_mod_cast hij
    linarith
  · rw [pow_succ]; nlinarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]
    have : (i : ℤ) < 2 ^ (k+1) := by exact_mod_cast hi'
    have : (l : ℤ) < 2 ^ (k+1) := by exact_mod_cast hl'
    constructor <;> linarith

lemma two_pow_succ (k : ℕ) : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring

/-- Orientation of a triple whose minority-parity point is last. -/
lemma mixed_pair (c : ℤ) (k i j l : ℕ) (hc : 2 ^ (k + 2) + 2 < c) (hij : i ≠ j)
    (hp : i % 2 = j % 2) (hl : l % 2 ≠ i % 2)
    (hi : i < 2 ^ (k + 1)) (hj : j < 2 ^ (k + 1)) (hl' : l < 2 ^ (k + 1)) :
    D c (k + 1) i j l ≠ 0 ∧ (0 < D c (k + 1) i j l ↔ (i < j ↔ l % 2 = 1)) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · have := F2 c k i j l hc h h0 (by omega) (by omega) hi hl'
      refine ⟨this.ne', ?_⟩; constructor <;> intro _ <;> [omega; exact this]
    · have := F3 c k i j l hc h h0 (by omega) (by omega) hi hl'
      refine ⟨this.ne, ?_⟩; constructor <;> intro h1
      · exact absurd h1 (not_lt.2 this.le)
      · omega
  · rw [D_swap]
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · have := F2 c k j i l hc h (by omega) h0 (by omega) hj hl'
      refine ⟨by linarith, ?_⟩; constructor <;> intro h1
      · linarith
      · omega
    · have := F3 c k j i l hc h (by omega) h0 (by omega) hj hl'
      refine ⟨by linarith, ?_⟩; constructor <;> intro _
      · omega
      · linarith

/-- Sorted mixed triple: positive orientation iff the middle point is even (low). -/
lemma sorted_mixed (c : ℤ) (k i j l : ℕ) (hc : 2 ^ (k + 2) + 2 < c) (hij : i < j) (hjl : j < l)
    (hl : l < 2 ^ (k + 1)) (hm : ¬ (i % 2 = j % 2 ∧ j % 2 = l % 2)) :
    D c (k + 1) i j l ≠ 0 ∧ (0 < D c (k + 1) i j l ↔ j % 2 = 0) := by
  by_cases h1 : i % 2 = j % 2
  · obtain ⟨h, h'⟩ := mixed_pair c k i j l hc (by omega) h1 (by omega) (by omega) (by omega) hl
    exact ⟨h, by rw [h']; omega⟩
  by_cases h2 : i % 2 = l % 2
  · obtain ⟨h, h'⟩ := mixed_pair c k l i j hc (by omega) h2.symm (by omega) hl (by omega) (by omega)
    rw [D_cyc c (k + 1) l i j] at h h'
    exact ⟨h, by rw [h']; omega⟩
  · obtain ⟨h, h'⟩ := mixed_pair c k j l i hc (by omega) (by omega) (by omega) (by omega) hl
      (by omega)
    rw [← D_cyc c (k + 1) i j l] at h h'
    exact ⟨h, by rw [h']; omega⟩

/-- General position of the Horton set, combinatorial form. -/
lemma gen_pos (c : ℤ) : ∀ k, 2 ^ (k + 1) + 2 < c → ∀ i j l, i < 2 ^ k → j < 2 ^ k → l < 2 ^ k →
    i ≠ j → j ≠ l → i ≠ l → D c k i j l ≠ 0 := by
  intro k
  induction k with
  | zero => intro _ i j l hi hj _ hij; simp at hi hj; omega
  | succ k ih =>
    intro hc i j l hi hj hl hij hjl hil
    have hp := two_pow_succ k
    have hc' : 2 ^ (k + 1) + 2 < c := by
      have : (2:ℤ) ^ (k + 1) ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    by_cases hs : i % 2 = j % 2 ∧ j % 2 = l % 2
    · rw [D_succ_same c k i j l hs.1 hs.2]
      have := ih hc' (i / 2) (j / 2) (l / 2) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      omega
    by_cases h1 : i % 2 = j % 2
    · exact (mixed_pair c k i j l hc hij h1 (by omega) hi hj hl).1
    by_cases h2 : i % 2 = l % 2
    · have := (mixed_pair c k l i j hc (Ne.symm hil) h2.symm (by omega) hl hi hj).1
      rwa [D_cyc c (k + 1) l i j] at this
    · have := (mixed_pair c k j l i hc hjl (by omega) (by omega) hj hl hi).1
      rwa [← D_cyc c (k + 1) i j l] at this

/-- The no-open-4-cup / no-open-4-cap lemma (Horton). -/
lemma cup_cap (c : ℤ) : ∀ k, 2 ^ (k + 1) + 2 < c → ∀ a b e d, a < b → b < e → e < d → d < 2 ^ k →
    (0 < D c k a b e → 0 < D c k b e d → ∃ q, (a < q ∧ q < b ∧ D c k a q b < 0) ∨
      (b < q ∧ q < e ∧ D c k b q e < 0) ∨ (e < q ∧ q < d ∧ D c k e q d < 0)) ∧
    (D c k a b e < 0 → D c k b e d < 0 → ∃ q, (a < q ∧ q < b ∧ 0 < D c k a q b) ∨
      (b < q ∧ q < e ∧ 0 < D c k b q e) ∨ (e < q ∧ q < d ∧ 0 < D c k e q d)) := by
  intro k
  induction k with
  | zero => intro _ a b e d hab hbe hed hd; simp at hd; omega
  | succ k ih =>
    intro hc a b e d hab hbe hed hd
    have hp := two_pow_succ k
    have hc' : 2 ^ (k + 1) + 2 < c := by
      have : (2:ℤ) ^ (k + 1) ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    by_cases hs : a % 2 = b % 2 ∧ b % 2 = e % 2 ∧ e % 2 = d % 2
    · obtain ⟨h1, h2, h3⟩ := hs
      obtain ⟨ihc, iha⟩ := ih hc' (a / 2) (b / 2) (e / 2) (d / 2) (by omega) (by omega) (by omega)
        (by omega)
      rw [D_succ_same c k a b e h1 h2, D_succ_same c k b e d h2 h3]
      -- transfer a witness from level k
      have tr : ∀ x y q', x % 2 = a % 2 → y % 2 = a % 2 →
          (D c (k + 1) x (2 * q' + a % 2) y = 2 * D c k (x / 2) q' (y / 2)) := by
        intro x y q' hx hy
        rw [D_succ_same c k x _ y (by omega) (by omega)]
        congr 2; omega
      constructor
      · intro p1 p2
        obtain ⟨q', hq⟩ := ihc (by linarith) (by linarith)
        refine ⟨2 * q' + a % 2, ?_⟩
        rcases hq with ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩
        · left; refine ⟨by omega, by omega, ?_⟩; rw [tr a b q' rfl (by omega)]; linarith
        · right; left; refine ⟨by omega, by omega, ?_⟩; rw [tr b e q' (by omega) (by omega)]
          linarith
        · right; right; refine ⟨by omega, by omega, ?_⟩; rw [tr e d q' (by omega) (by omega)]
          linarith
      · intro p1 p2
        obtain ⟨q', hq⟩ := iha (by linarith) (by linarith)
        refine ⟨2 * q' + a % 2, ?_⟩
        rcases hq with ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩
        · left; refine ⟨by omega, by omega, ?_⟩; rw [tr a b q' rfl (by omega)]; linarith
        · right; left; refine ⟨by omega, by omega, ?_⟩; rw [tr b e q' (by omega) (by omega)]
          linarith
        · right; right; refine ⟨by omega, by omega, ?_⟩; rw [tr e d q' (by omega) (by omega)]
          linarith
    · -- mixed case: the middle points b, e have equal parity, forced by the signs
      have SM1 := fun hm => sorted_mixed c k a b e hc hab hbe (by omega) hm
      have SM2 := fun hm => sorted_mixed c k b e d hc hbe hed hd hm
      constructor
      · intro p1 p2
        have hb : b % 2 = 0 ∨ (a % 2 = b % 2 ∧ b % 2 = e % 2) := by
          by_cases hm : a % 2 = b % 2 ∧ b % 2 = e % 2
          · exact Or.inr hm
          · exact Or.inl ((SM1 hm).2.1 p1)
        have he : e % 2 = 0 ∨ (b % 2 = e % 2 ∧ e % 2 = d % 2) := by
          by_cases hm : b % 2 = e % 2 ∧ e % 2 = d % 2
          · exact Or.inr hm
          · exact Or.inl ((SM2 hm).2.1 p2)
        have hbe' : b % 2 = 0 ∧ e % 2 = 0 := by omega
        obtain ⟨h1, h2⟩ := sorted_mixed c k b (b + 1) e hc (by omega) (by omega) (by omega)
          (by omega)
        refine ⟨b + 1, Or.inr (Or.inl ⟨by omega, by omega, ?_⟩)⟩
        rcases lt_or_gt_of_ne h1 with h | h
        · exact h
        · exact absurd (h2.1 h) (by omega)
      · intro p1 p2
        have hb : b % 2 = 1 ∨ (a % 2 = b % 2 ∧ b % 2 = e % 2) := by
          by_cases hm : a % 2 = b % 2 ∧ b % 2 = e % 2
          · exact Or.inr hm
          · left; have := (SM1 hm).2
            have : ¬ b % 2 = 0 := fun h => absurd (this.2 h) (not_lt.2 p1.le)
            omega
        have he : e % 2 = 1 ∨ (b % 2 = e % 2 ∧ e % 2 = d % 2) := by
          by_cases hm : b % 2 = e % 2 ∧ e % 2 = d % 2
          · exact Or.inr hm
          · left; have := (SM2 hm).2
            have : ¬ e % 2 = 0 := fun h => absurd (this.2 h) (not_lt.2 p2.le)
            omega
        have hbe' : b % 2 = 1 ∧ e % 2 = 1 := by omega
        obtain ⟨h1, h2⟩ := sorted_mixed c k b (b + 1) e hc (by omega) (by omega) (by omega)
          (by omega)
        exact ⟨b + 1, Or.inr (Or.inl ⟨by omega, by omega, h2.2 (by omega)⟩)⟩


/-- `Inside c k q a b e`: the point with index `q` lies strictly inside the triangle with
vertices of indices `a, b, e` (all three orientations agree). -/
def Inside (c : ℤ) (k q a b e : ℕ) : Prop :=
  (0 < D c k a b q ∧ 0 < D c k b e q ∧ 0 < D c k e a q) ∨
  (D c k a b q < 0 ∧ D c k b e q < 0 ∧ D c k e a q < 0)

/-- `Good c k T`: the index set `T` spans an empty convex polygon in the Horton set of size
`2^k`, in the combinatorial sense: no point of the Horton set lies strictly inside a triangle
spanned by three other points of `T`. -/
def Good (c : ℤ) (k M : ℕ) (T : Finset ℕ) : Prop :=
  (∀ a ∈ T, a < M) ∧ ∀ q, q < M → ∀ a ∈ T, ∀ b ∈ T, ∀ e ∈ T,
    a ≠ b → b ≠ e → a ≠ e → q ≠ a → q ≠ b → q ≠ e → ¬ Inside c k q a b e

lemma L1 (c : ℤ) (k x q y u : ℕ) (hc : 2 ^ (k + 2) + 2 < c) (hxq : x < q) (hqy : q < y)
    (hx : x % 2 = 0) (hq : q % 2 = 0) (hy : y % 2 = 0) (hu : u % 2 = 1)
    (hyb : y < 2 ^ (k + 1)) (hub : u < 2 ^ (k + 1)) (hD : D c (k + 1) x q y < 0) :
    Inside c (k + 1) q x y u := by
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [D_swap23]; linarith
  · rw [← D_cyc c (k + 1) q y u]
    exact (mixed_pair c k q y u hc (by omega) (by omega) (by omega) (by omega) hyb hub).2.2
      (by simp [hqy, hu])
  · rw [D_cyc c (k + 1) u x q]
    exact (mixed_pair c k x q u hc (by omega) (by omega) (by omega) (by omega) (by omega)
      hub).2.2 (by simp [hxq, hu])

lemma L1' (c : ℤ) (k x q y u : ℕ) (hc : 2 ^ (k + 2) + 2 < c) (hxq : x < q) (hqy : q < y)
    (hx : x % 2 = 1) (hq : q % 2 = 1) (hy : y % 2 = 1) (hu : u % 2 = 0)
    (hyb : y < 2 ^ (k + 1)) (hub : u < 2 ^ (k + 1)) (hD : 0 < D c (k + 1) x q y) :
    Inside c (k + 1) q x y u := by
  right
  refine ⟨?_, ?_, ?_⟩
  · rw [D_swap23]; linarith
  · rw [← D_cyc c (k + 1) q y u]
    obtain ⟨h1, h2⟩ :=
      mixed_pair c k q y u hc (by omega) (by omega) (by omega) (by omega) hyb hub
    rcases lt_or_gt_of_ne h1 with h | h
    · exact h
    · exact absurd (h2.1 h) (by simp [hqy, hu])
  · rw [D_cyc c (k + 1) u x q]
    obtain ⟨h1, h2⟩ :=
      mixed_pair c k x q u hc (by omega) (by omega) (by omega) (by omega) (by omega) hub
    rcases lt_or_gt_of_ne h1 with h | h
    · exact h
    · exact absurd (h2.1 h) (by simp [hxq, hu])

lemma inside_succ_same (c : ℤ) (k q a b e r : ℕ) (hq : q % 2 = r) (ha : a % 2 = r)
    (hb : b % 2 = r) (he : e % 2 = r) :
    Inside c (k + 1) q a b e ↔ Inside c k (q / 2) (a / 2) (b / 2) (e / 2) := by
  unfold Inside
  rw [D_succ_same c k a b q (by omega) (by omega), D_succ_same c k b e q (by omega) (by omega),
    D_succ_same c k e a q (by omega) (by omega)]
  omega

lemma good_half (c : ℤ) (k M r : ℕ) (T : Finset ℕ) (hT : Good c (k + 1) M T)
    (hr : ∀ x ∈ T, x % 2 = r) (hr2 : r < 2) :
    Good c k ((M + 1 - r) / 2) (T.image (· / 2)) ∧ (T.image (· / 2)).card = T.card := by
  have hp := two_pow_succ k
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a' ha'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ha'
    have := hT.1 a ha; have := hr a ha; omega
  · intro q' hq' a' ha' b' hb' e' he' hab hbe hae hqa hqb hqe hin
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 he'
    have ra := hr a ha; have rb := hr b hb; have re := hr e he
    have hin' : Inside c (k + 1) (2 * q' + r) a b e := by
      rw [inside_succ_same c k (2 * q' + r) a b e r (by omega) ra rb re]
      have : (2 * q' + r) / 2 = q' := by omega
      rwa [this]
    exact hT.2 (2 * q' + r) (by omega) a ha b hb e he (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hin'
  · apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have := hr x hx; have := hr y hy
    simp only at hxy
    omega

lemma exists_four (s : Finset ℕ) (h : 4 ≤ s.card) :
    ∃ a b e d, a ∈ s ∧ b ∈ s ∧ e ∈ s ∧ d ∈ s ∧ a < b ∧ b < e ∧ e < d := by
  let f := s.orderEmbOfFin rfl
  refine ⟨f ⟨0, by omega⟩, f ⟨1, by omega⟩, f ⟨2, by omega⟩, f ⟨3, by omega⟩,
    s.orderEmbOfFin_mem rfl _, s.orderEmbOfFin_mem rfl _, s.orderEmbOfFin_mem rfl _,
    s.orderEmbOfFin_mem rfl _, ?_, ?_, ?_⟩ <;>
  exact f.lt_iff_lt.2 (by simp [Fin.lt_def])

/-- **Main combinatorial theorem.** A good (empty convex) index set in the Horton set of size
`2^k` has at most `6` points. -/
theorem good_card (c : ℤ) : ∀ k, 2 ^ (k + 1) + 2 < c → ∀ M, M ≤ 2 ^ k → ∀ T : Finset ℕ,
    Good c k M T → T.card ≤ 6 := by
  intro k
  induction k with
  | zero =>
    intro _ M hM T hT
    have : T ⊆ Finset.range 1 := fun a ha => by
      have := hT.1 a ha; simp at hM ⊢; omega
    have := Finset.card_le_card this
    simp at this; omega
  | succ k ih =>
    intro hc M hM T hT
    have hp := two_pow_succ k
    have hc' : 2 ^ (k + 1) + 2 < c := by
      have : (2:ℤ) ^ (k + 1) ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hsplit := Finset.card_filter_add_card_filter_not (s := T) (fun x => x % 2 = 0)
    by_cases h1 : T.filter (fun x => ¬ x % 2 = 0) = ∅
    · have hr : ∀ x ∈ T, x % 2 = 0 := by
        intro x hx
        by_contra hne
        have : x ∈ T.filter (fun x => ¬ x % 2 = 0) := Finset.mem_filter.2 ⟨hx, hne⟩
        rw [h1] at this; simp at this
      obtain ⟨hg, hcard⟩ := good_half c k M 0 T hT hr (by norm_num)
      rw [← hcard]; exact ih hc' _ (by omega) _ hg
    by_cases h0 : T.filter (fun x => x % 2 = 0) = ∅
    · have hr : ∀ x ∈ T, x % 2 = 1 := by
        intro x hx
        by_contra hne
        have : x ∈ T.filter (fun x => x % 2 = 0) := Finset.mem_filter.2 ⟨hx, by omega⟩
        rw [h0] at this; simp at this
      obtain ⟨hg, hcard⟩ := good_half c k M 1 T hT hr (by norm_num)
      rw [← hcard]; exact ih hc' _ (by omega) _ hg
    obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.2 h1
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 h0
    rw [Finset.mem_filter] at hu hv
    have hub : u < 2 ^ (k + 1) := lt_of_lt_of_le (hT.1 u hu.1) hM
    have hvb : v < 2 ^ (k + 1) := lt_of_lt_of_le (hT.1 v hv.1) hM
    have hu2 : u % 2 = 1 := by omega
    -- at most three even points
    have hE : (T.filter (fun x => x % 2 = 0)).card ≤ 3 := by
      by_contra hcon
      obtain ⟨a, b, e, d, ha, hb, he, hd, hab, hbe, hed⟩ :=
        exists_four (T.filter (fun x => x % 2 = 0)) (by omega)
      simp only [Finset.mem_filter] at ha hb he hd
      have hdb : d < 2 ^ (k + 1) := lt_of_lt_of_le (hT.1 d hd.1) hM
      have pos : ∀ x y z, x ∈ T → y ∈ T → z ∈ T → x % 2 = 0 → y % 2 = 0 → z % 2 = 0 →
          x < y → y < z → 0 < D c k (x / 2) (y / 2) (z / 2) := by
        intro x y z hx hy hz px py pz hxy hyz
        have hzM := hT.1 z hz
        have hzb : z < 2 ^ (k + 1) := lt_of_lt_of_le hzM hM
        have ne := gen_pos c (k + 1) hc x y z (by omega) (by omega) hzb (by omega) (by omega)
          (by omega)
        have eq := D_succ_same c k x y z (by omega) (by omega)
        rcases lt_or_gt_of_ne ne with h | h
        · exfalso
          exact hT.2 y (by omega) x hx z hz u hu.1 (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (L1 c k x y z u hc hxy hyz px py pz hu2 hzb hub h)
        · linarith
      have gap : ∀ x y q', x ∈ T → y ∈ T → x % 2 = 0 → y % 2 = 0 → x / 2 < q' → q' < y / 2 →
          D c k (x / 2) q' (y / 2) < 0 → False := by
        intro x y q' hx hy px py h1 h2 h3
        have hyM := hT.1 y hy
        have hyb : y < 2 ^ (k + 1) := lt_of_lt_of_le hyM hM
        have hD : D c (k + 1) x (2 * q') y < 0 := by
          rw [D_succ_same c k x _ y (by omega) (by omega)]
          have : 2 * q' / 2 = q' := by omega
          rw [this]; linarith
        exact hT.2 (2 * q') (by omega) x hx y hy u hu.1 (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
          (L1 c k x (2 * q') y u hc (by omega) (by omega) px (by omega) py hu2 hyb hub hD)
      obtain ⟨q', hq'⟩ := (cup_cap c k hc' (a / 2) (b / 2) (e / 2) (d / 2) (by omega) (by omega)
        (by omega) (by omega)).1 (pos a b e ha.1 hb.1 he.1 ha.2 hb.2 he.2 hab hbe)
        (pos b e d hb.1 he.1 hd.1 hb.2 he.2 hd.2 hbe hed)
      rcases hq' with ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩
      · exact gap a b q' ha.1 hb.1 ha.2 hb.2 x1 x2 x3
      · exact gap b e q' hb.1 he.1 hb.2 he.2 x1 x2 x3
      · exact gap e d q' he.1 hd.1 he.2 hd.2 x1 x2 x3
    -- at most three odd points
    have hO : (T.filter (fun x => ¬ x % 2 = 0)).card ≤ 3 := by
      by_contra hcon
      obtain ⟨a, b, e, d, ha, hb, he, hd, hab, hbe, hed⟩ :=
        exists_four (T.filter (fun x => ¬ x % 2 = 0)) (by omega)
      simp only [Finset.mem_filter] at ha hb he hd
      have hdb : d < 2 ^ (k + 1) := lt_of_lt_of_le (hT.1 d hd.1) hM
      have neg : ∀ x y z, x ∈ T → y ∈ T → z ∈ T → x % 2 = 1 → y % 2 = 1 → z % 2 = 1 →
          x < y → y < z → D c k (x / 2) (y / 2) (z / 2) < 0 := by
        intro x y z hx hy hz px py pz hxy hyz
        have hzM := hT.1 z hz
        have hzb : z < 2 ^ (k + 1) := lt_of_lt_of_le hzM hM
        have ne := gen_pos c (k + 1) hc x y z (by omega) (by omega) hzb (by omega) (by omega)
          (by omega)
        have eq := D_succ_same c k x y z (by omega) (by omega)
        rcases lt_or_gt_of_ne ne with h | h
        · linarith
        · exfalso
          exact hT.2 y (by omega) x hx z hz v hv.1 (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (L1' c k x y z v hc hxy hyz px py pz hv.2 hzb hvb h)
      have gap : ∀ x y q', x ∈ T → y ∈ T → x % 2 = 1 → y % 2 = 1 → x / 2 < q' → q' < y / 2 →
          0 < D c k (x / 2) q' (y / 2) → False := by
        intro x y q' hx hy px py h1 h2 h3
        have hyM := hT.1 y hy
        have hyb : y < 2 ^ (k + 1) := lt_of_lt_of_le hyM hM
        have hD : 0 < D c (k + 1) x (2 * q' + 1) y := by
          rw [D_succ_same c k x _ y (by omega) (by omega)]
          have : (2 * q' + 1) / 2 = q' := by omega
          rw [this]; linarith
        exact hT.2 (2 * q' + 1) (by omega) x hx y hy v hv.1 (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
          (L1' c k x (2 * q' + 1) y v hc (by omega) (by omega) px (by omega) py hv.2 hyb hvb hD)
      obtain ⟨q', hq'⟩ := (cup_cap c k hc' (a / 2) (b / 2) (e / 2) (d / 2) (by omega) (by omega)
        (by omega) (by omega)).2 (neg a b e ha.1 hb.1 he.1 (by omega) (by omega) (by omega) hab hbe)
        (neg b e d hb.1 he.1 hd.1 (by omega) (by omega) (by omega) hbe hed)
      rcases hq' with ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩
      · exact gap a b q' ha.1 hb.1 (by omega) (by omega) x1 x2 x3
      · exact gap b e q' hb.1 he.1 (by omega) (by omega) x1 x2 x3
      · exact gap e d q' he.1 hd.1 (by omega) (by omega) x1 x2 x3
    omega


section Geometry
open Set

/-- Orientation determinant in `ℝ²`. -/
def det2 (p q r : ℝ × ℝ) : ℝ := (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

lemma not_collinear_of_det2 {p q r : ℝ × ℝ} (h : det2 p q r ≠ 0) :
    ¬ Collinear ℝ ({p, q, r} : Set (ℝ × ℝ)) := by
  intro hcol
  rw [collinear_iff_of_mem (p₀ := p) (by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨s, hs⟩ := hv q (by simp)
  obtain ⟨t, ht⟩ := hv r (by simp)
  apply h
  rw [hs, ht]
  simp only [det2, vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- The triangle region cut out by three strict orientation inequalities. -/
def triRegion (a b c : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {m | (0 < det2 a b m ∧ 0 < det2 b c m ∧ 0 < det2 c a m) ∨
    (det2 a b m < 0 ∧ det2 b c m < 0 ∧ det2 c a m < 0)}

lemma triRegion_subset (a b c : ℝ × ℝ) : triRegion a b c ⊆ convexHull ℝ {a, b, c} := by
  intro m hm
  set s := det2 a b c with hs_def
  have hs : s = det2 b c m + det2 c a m + det2 a b m := by simp only [hs_def, det2]; ring
  have hw : 0 < det2 b c m / s ∧ 0 < det2 c a m / s ∧ 0 < det2 a b m / s := by
    rcases hm with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have : 0 < s := by linarith
      exact ⟨div_pos h2 this, div_pos h3 this, div_pos h1 this⟩
    · have : s < 0 := by linarith
      exact ⟨div_pos_of_neg_of_neg h2 this, div_pos_of_neg_of_neg h3 this,
        div_pos_of_neg_of_neg h1 this⟩
  have hs0 : s ≠ 0 := by
    intro h0; have := hw.1; rw [h0, div_zero] at this; exact lt_irrefl _ this
  have hmem := (convex_convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))).sum_mem
    (t := Finset.univ) (w := ![det2 b c m / s, det2 c a m / s, det2 a b m / s])
    (z := ![a, b, c]) (by intro i _; fin_cases i <;> simp [hw.1.le, hw.2.1.le, hw.2.2.le])
    (by simp [Fin.sum_univ_three]; field_simp; linarith)
    (by intro i _; fin_cases i <;> apply subset_convexHull <;> simp)
  convert hmem using 1
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    field_simp
    simp only [hs_def, det2]; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    field_simp
    simp only [hs_def, det2]; ring

lemma triRegion_open (a b c : ℝ × ℝ) : IsOpen (triRegion a b c) := by
  have hc : ∀ p q : ℝ × ℝ, Continuous (fun m => det2 p q m) := by
    intro p q; unfold det2; fun_prop
  unfold triRegion
  apply IsOpen.union
  · exact (isOpen_lt continuous_const (hc a b)).inter
      ((isOpen_lt continuous_const (hc b c)).inter (isOpen_lt continuous_const (hc c a)))
  · exact (isOpen_lt (hc a b) continuous_const).inter
      ((isOpen_lt (hc b c) continuous_const).inter (isOpen_lt (hc c a) continuous_const))

lemma triRegion_subset_interior (a b c : ℝ × ℝ) :
    triRegion a b c ⊆ interior (convexHull ℝ {a, b, c}) :=
  interior_maximal (triRegion_subset a b c) (triRegion_open a b c)


/-- Embedding of integer points into the real plane. -/
def toR (p : ℤ × ℤ) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

lemma toR_injective : Function.Injective toR := by
  intro p q h
  simp only [toR, Prod.mk.injEq, Int.cast_inj] at h
  exact Prod.ext h.1 h.2

/-! ### Faithful geometric definitions -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A finite point set is in *general position* if no three distinct points of it are
collinear (Mathlib's `Collinear`). -/
def InGeneralPosition (S : Finset V) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r → ¬ Collinear ℝ ({p, q, r} : Set V)

/-- A finite point set is in *convex position* (is convex independent): no point lies in the
convex hull of the others. -/
def ConvexPosition [DecidableEq V] (T : Finset V) : Prop :=
  ∀ p ∈ T, p ∉ convexHull ℝ ((T.erase p : Finset V) : Set V)

/-- `S` contains an *empty convex `k`-gon*: `k` points of `S` in convex position such that no
other point of `S` lies in the interior of their convex hull. (Using the interior makes the
emptiness condition as weak as possible, so `¬ HasEmptyConvexKGon` is as strong as possible;
for sets in general position it agrees with "no other point of `S` in the convex hull", the
variant `HasEmptyConvexKGon'` treated in `Solution.lean`.) -/
def HasEmptyConvexKGon [DecidableEq V] [TopologicalSpace V] (k : ℕ) (S : Finset V) : Prop :=
  ∃ T ⊆ S, T.card = k ∧ ConvexPosition T ∧
    ∀ p ∈ S, p ∉ T → p ∉ interior (convexHull ℝ (T : Set V))

/-- Variant of `HasEmptyConvexKGon` where emptiness means that no other point of `S` lies in
the (closed) convex hull, as in `EmptyHexagonLean` (`ConvexIndep` + `EmptyShapeIn`). -/
def HasEmptyConvexKGon' [DecidableEq V] (k : ℕ) (S : Finset V) : Prop :=
  ∃ T ⊆ S, T.card = k ∧ ConvexPosition T ∧ ∀ p ∈ S, p ∉ T → p ∉ convexHull ℝ (T : Set V)

lemma HasEmptyConvexKGon'.toHasEmptyConvexKGon [DecidableEq V] [TopologicalSpace V] {k : ℕ}
    {S : Finset V} (h : HasEmptyConvexKGon' k S) : HasEmptyConvexKGon k S := by
  obtain ⟨T, hTS, hk, hc, he⟩ := h
  exact ⟨T, hTS, hk, hc, fun p hp hpT hin => he p hp hpT (interior_subset hin)⟩

/-! ### The Horton set -/

/-- The scale constant used for the Horton set of `n` points. -/
def scale (n : ℕ) : ℤ := 2 ^ (n + 1) + 3

/-- The Horton set of `n` points, with integer coordinates: the points `(i, hy i)` for
`i < n`, where `hy i = ∑_j bit_j(i) * c^(n-j)` (`c = 2^(n+1)+3`). -/
def hortonSetInt (n : ℕ) : Finset (ℤ × ℤ) := (Finset.range n).image (hpt (scale n) n)

lemma hpt_injective (c : ℤ) (k : ℕ) : Function.Injective (hpt c k) := by
  intro i j h
  simp only [hpt, Prod.mk.injEq, Nat.cast_inj] at h
  exact h.1

lemma card_hortonSetInt (n : ℕ) : (hortonSetInt n).card = n := by
  rw [hortonSetInt, Finset.card_image_of_injective _ (hpt_injective _ _), Finset.card_range]

lemma det2_toR (c : ℤ) (k i j l : ℕ) :
    det2 (toR (hpt c k i)) (toR (hpt c k j)) (toR (hpt c k l)) = (D c k i j l : ℝ) := by
  simp only [det2, toR, hpt, D, det]; push_cast; ring

lemma n_le_two_pow (n : ℕ) : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le

lemma scale_spec (n : ℕ) : 2 ^ (n + 1) + 2 < scale n := by unfold scale; linarith

theorem hortonSet_genPos (n : ℕ) : InGeneralPosition ((hortonSetInt n).image toR) := by
  intro p hp q hq r hr hpq hpr hqr
  simp only [hortonSetInt, Finset.image_image, Finset.mem_image, Finset.mem_range,
    Function.comp] at hp hq hr
  obtain ⟨i, hi, rfl⟩ := hp
  obtain ⟨j, hj, rfl⟩ := hq
  obtain ⟨l, hl, rfl⟩ := hr
  apply not_collinear_of_det2
  rw [det2_toR]
  have h2 := n_le_two_pow n
  have := gen_pos (scale n) n (scale_spec n) i j l (by omega) (by omega) (by omega)
    (fun h => hpq (by rw [h])) (fun h => hqr (by rw [h])) (fun h => hpr (by rw [h]))
  exact_mod_cast this

/-- Core statement: any empty convex polygon in the Horton set has at most `6` vertices. -/
theorem hortonSet_empty_le_six (n : ℕ) (T : Finset (ℝ × ℝ))
    (hTS : T ⊆ (hortonSetInt n).image toR) (hconv : ConvexPosition T)
    (hempty : ∀ p ∈ (hortonSetInt n).image toR, p ∉ T →
      p ∉ interior (convexHull ℝ (T : Set (ℝ × ℝ)))) : T.card ≤ 6 := by
  classical
  set c := scale n
  set P : ℕ → ℝ × ℝ := fun i => toR (hpt c n i) with hP
  have hPinj : Function.Injective P := toR_injective.comp (hpt_injective c n)
  have hS : (hortonSetInt n).image toR = (Finset.range n).image P := by
    simp only [hortonSetInt, Finset.image_image]; rfl
  rw [hS] at hTS hempty
  set I := (Finset.range n).filter (fun i => P i ∈ T) with hI
  have hTI : T = I.image P := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (hTS hp)
      exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hi, hp⟩, rfl⟩
    · intro hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      exact (Finset.mem_filter.1 hi).2
  have hcard : T.card = I.card := by rw [hTI, Finset.card_image_of_injective _ hPinj]
  have hgood : Good c n n I := by
    refine ⟨fun a ha => Finset.mem_range.1 (Finset.mem_filter.1 ha).1, ?_⟩
    intro q hq a ha b hb e he hab hbe hae hqa hqb hqe hin
    have haT := (Finset.mem_filter.1 ha).2
    have hbT := (Finset.mem_filter.1 hb).2
    have heT := (Finset.mem_filter.1 he).2
    have hreg : P q ∈ triRegion (P a) (P b) (P e) := by
      simp only [triRegion, Set.mem_ofPred_eq, hP, det2_toR, Int.cast_pos, Int.cast_lt_zero]
      exact hin
    by_cases hqT : P q ∈ T
    · apply hconv (P q) hqT
      refine convexHull_mono ?_ (triRegion_subset _ _ _ hreg)
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
      rcases hx with rfl | rfl | rfl
      · exact ⟨haT, fun h => hqa (hPinj h).symm⟩
      · exact ⟨hbT, fun h => hqb (hPinj h).symm⟩
      · exact ⟨heT, fun h => hqe (hPinj h).symm⟩
    · apply hempty (P q) (Finset.mem_image.2 ⟨q, Finset.mem_range.2 hq, rfl⟩) hqT
      refine interior_mono (convexHull_mono ?_) (triRegion_subset_interior _ _ _ hreg)
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
  rw [hcard]
  exact good_card c n (scale_spec n) n (n_le_two_pow n) I hgood

/-- **Horton's theorem** (integer-coordinate form). For every `N` there is a set of exactly `N`
points with integer coordinates, in general position, containing no empty convex `k`-gon for
any `k ≥ 7`. -/
theorem horton_int (N : ℕ) : ∃ S : Finset (ℤ × ℤ), S.card = N ∧
    InGeneralPosition (S.image toR) ∧ ∀ k, 7 ≤ k → ¬ HasEmptyConvexKGon k (S.image toR) := by
  refine ⟨hortonSetInt N, card_hortonSetInt N, hortonSet_genPos N, ?_⟩
  rintro k hk ⟨T, hTS, hTk, hconv, hempty⟩
  have := hortonSet_empty_le_six N T hTS hconv hempty
  omega

/-- **Horton's theorem** (1983). For every `N` there is a set of `N` points in the plane in
general position (no three collinear) with no empty convex `k`-gon for any `k ≥ 7`. -/
theorem horton (N : ℕ) : ∃ S : Finset (ℝ × ℝ), S.card = N ∧ InGeneralPosition S ∧
    ∀ k, 7 ≤ k → ¬ HasEmptyConvexKGon k S := by
  obtain ⟨S, hcard, hgp, h⟩ := horton_int N
  exact ⟨S.image toR, by rw [Finset.card_image_of_injective _ toR_injective, hcard], hgp, h⟩

/-- **Erdős Problem 216, the case `k ≥ 7`.** The number `g(k)` does not exist for `k ≥ 7`:
there is no `n` such that every set of `n` points in general position contains an empty convex
`k`-gon. -/
theorem erdos_216_ge_seven (k : ℕ) (hk : 7 ≤ k) :
    ¬ ∃ n : ℕ, ∀ S : Finset (ℝ × ℝ), S.card = n → InGeneralPosition S →
      HasEmptyConvexKGon k S := by
  rintro ⟨n, hn⟩
  obtain ⟨S, hcard, hgp, h⟩ := horton n
  exact h k hk (hn S hcard hgp)

/-- The statement also holds for the closed-hull notion of emptiness. -/
theorem not_hasEmptyConvexKGon' (N : ℕ) : ∃ S : Finset (ℝ × ℝ), S.card = N ∧
    InGeneralPosition S ∧ ∀ k, 7 ≤ k → ¬ HasEmptyConvexKGon' k S := by
  obtain ⟨S, hcard, hgp, h⟩ := horton N
  exact ⟨S, hcard, hgp, fun k hk h' => h k hk h'.toHasEmptyConvexKGon⟩

/-- Variant of `erdos_216_ge_seven` with "at least `n` points". -/
theorem erdos_216_ge_seven' (k : ℕ) (hk : 7 ≤ k) :
    ¬ ∃ n : ℕ, ∀ S : Finset (ℝ × ℝ), n ≤ S.card → InGeneralPosition S →
      HasEmptyConvexKGon k S := by
  rintro ⟨n, hn⟩
  exact erdos_216_ge_seven k hk ⟨n, fun S hS => hn S hS.ge⟩

/-! ### Transport along linear isomorphisms (e.g. to `EuclideanSpace ℝ (Fin 2)`) -/

section Transport

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [TopologicalSpace V]
  [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma InGeneralPosition.map (e : V ≃L[ℝ] W) {S : Finset V} (h : InGeneralPosition S) :
    InGeneralPosition (S.image e) := by
  intro p' hp' q' hq' r' hr' hpq hpr hqr hcol
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hp'
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hq'
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hr'
  apply h p hp q hq r hr (fun h => hpq (by rw [h])) (fun h => hpr (by rw [h]))
    (fun h => hqr (by rw [h]))
  rw [collinear_iff_of_mem (p₀ := e p) (by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  rw [collinear_iff_of_mem (p₀ := p) (by simp)]
  refine ⟨e.symm v, fun x hx => ?_⟩
  have hx' : e x ∈ ({e p, e q, e r} : Set W) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp
  obtain ⟨t, ht⟩ := hv (e x) hx'
  refine ⟨t, ?_⟩
  have := congrArg e.symm ht
  simp only [vadd_eq_add, map_add, map_smul, ContinuousLinearEquiv.symm_apply_apply] at this
  simpa [vadd_eq_add] using this

lemma HasEmptyConvexKGon.of_map (e : V ≃L[ℝ] W) {k : ℕ} {S : Finset V}
    (h : HasEmptyConvexKGon k (S.image e)) : HasEmptyConvexKGon k S := by
  obtain ⟨T', hT'S, hk, hc, he⟩ := h
  have hT' : ∀ x ∈ T', ∃ y ∈ S, e y = x := fun x hx => Finset.mem_image.1 (hT'S hx)
  refine ⟨T'.image e.symm, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨z, hz, rfl⟩ := hT' x hx
    simpa using hz
  · rw [Finset.card_image_of_injective _ e.symm.injective, hk]
  · intro p hp hin
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
    apply hc x hx
    have h1 := Set.mem_image_of_mem e.toLinearEquiv.toLinearMap hin
    rw [LinearMap.image_convexHull] at h1
    simp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.apply_symm_apply] at h1
    convert h1 using 2
    ext z
    simp only [Finset.coe_erase, Finset.coe_image, Set.mem_sdiff, Finset.mem_coe,
      Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro ⟨hz, hzx⟩
      exact ⟨e.symm z, ⟨⟨z, hz, rfl⟩, fun h => hzx (by simpa using congrArg e h)⟩, by simp⟩
    · rintro ⟨y, ⟨⟨w, hw, rfl⟩, hne⟩, rfl⟩
      refine ⟨by simpa using hw, fun h => hne ?_⟩
      have h' : w = x := by simpa using h
      rw [h']
  · intro p hp hpT hin
    apply he (e p) (Finset.mem_image_of_mem _ hp)
    · intro hepT
      exact hpT (Finset.mem_image.2 ⟨e p, hepT, by simp⟩)
    · have h1 := Set.mem_image_of_mem e hin
      have h3 := e.toHomeomorph.image_interior
        (convexHull ℝ ((T'.image e.symm : Finset V) : Set V))
      simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h3
      rw [h3] at h1
      have h2 : (e : V → W) '' convexHull ℝ ((T'.image e.symm : Finset V) : Set V) =
          convexHull ℝ (T' : Set W) := by
        have := LinearMap.image_convexHull e.toLinearEquiv.toLinearMap
          ((T'.image e.symm : Finset V) : Set V)
        simp only [ContinuousLinearEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] at this
        rw [this]
        congr 1
        ext z; simp
      rw [h2] at h1
      exact h1

end Transport

/-- The standard identification of `ℝ × ℝ` with the Euclidean plane. -/
noncomputable def toEuclidean : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm

/-- **Horton's theorem** in the Euclidean plane `EuclideanSpace ℝ (Fin 2)` (the model of `ℝ²`
used by `EmptyHexagonLean` and `formal-conjectures`). -/
theorem horton_euclidean (N : ℕ) : ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = N ∧
    InGeneralPosition S ∧ ∀ k, 7 ≤ k → ¬ HasEmptyConvexKGon k S := by
  classical
  obtain ⟨S, hcard, hgp, h⟩ := horton N
  refine ⟨S.image toEuclidean, ?_, hgp.map toEuclidean, fun k hk hS => h k hk ?_⟩
  · rw [Finset.card_image_of_injective _ toEuclidean.injective, hcard]
  · exact HasEmptyConvexKGon.of_map toEuclidean hS

end Geometry

/-! ### Bridge to the `formal-conjectures` statement of Erdős Problem 216

The definitions below are copied from `google-deepmind/formal-conjectures` pull request
#6775 (`FormalConjectures/ErdosProblems/216.lean`, head commit `44b9bbc3`) and from the file it
uses, `FormalConjecturesForMathlib/Geometry/2d.lean` (`NonTrilinear`, `ConvexIndep`), with
`Set.Triplewise` from `FormalConjecturesForMathlib/Data/Set/Triplewise.lean`. They are primed
here because this repository depends only on Mathlib. The bodies are verbatim. The only
change is that `NonTrilinear` (stated there for an arbitrary Euclidean affine space `P`) is
specialised to `ℝ²`. The theorems `cardSet'_eq_empty` and `erdos_216'` are exactly the
statements `Erdos216.erdos_216.variants.horton` and `Erdos216.erdos_216` of that PR (with
`answer(False)` read as `False`). -/

section FormalConjectures216

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- `Set.Triplewise` from `FormalConjecturesForMathlib/Data/Set/Triplewise.lean`:
the ternary relation `r` holds for all *distinct* `x y z ∈ s`. -/
def SetTriplewise' {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

/-- `EuclideanGeometry.NonTrilinear` from `FormalConjecturesForMathlib/Geometry/2d.lean`:
no three points of `A` lie on the same line. -/
def NonTrilinear' (A : Set ℝ²) : Prop :=
  SetTriplewise' A (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

/-- `ConvexIndep` from `FormalConjecturesForMathlib/Geometry/2d.lean`: the set `S` is convex
independent, i.e. no point of `S` lies in the convex hull of the other points of `S`. -/
def ConvexIndep' (S : Set ℝ²) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

/-- `Erdos216.HasEmptyConvexNGon` from formal-conjectures PR #6775: `P` contains `n` points
`S` in convex position such that no point of `P` lies in the interior of the convex hull of
`S`. -/
def HasEmptyConvexNGon' (n : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep' (S : Set ℝ²) ∧
    ∀ p ∈ P, p ∉ interior (convexHull ℝ (S : Set ℝ²))

/-- `Erdos216.cardSet` from formal-conjectures PR #6775: the set of all `N` such that every
`N`-point set in the plane with no three points collinear contains an empty convex `k`-gon.
Its infimum is `g(k)`. -/
def cardSet' (k : ℕ) := { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear' (pts : Set ℝ²) →
    HasEmptyConvexNGon' k pts }

/-- `Erdos216.g` from formal-conjectures PR #6775. -/
noncomputable def g' (k : ℕ) : ℕ :=
  sInf (cardSet' k)

/-- **Horton's theorem**, formal-conjectures form (`Erdos216.erdos_216.variants.horton` in
PR #6775): for `n ≥ 7` no `N` works, i.e. `g(n)` does not exist. -/
theorem cardSet'_eq_empty : ∀ n ≥ 7, cardSet' n = ∅ := by
  intro n hn
  ext N
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hN
  obtain ⟨S, hcard, hgp, h⟩ := horton_euclidean N
  obtain ⟨T, hTcard, hTS, hT, hempty⟩ := hN S hcard
    (fun x hx y hy z hz hxy hyz hxz => hgp x hx y hy z hz hxy hxz hyz)
  refine h n hn ⟨T, Finset.coe_subset.1 hTS, hTcard, fun p hp => ?_, fun p hp _ => hempty p hp⟩
  rw [Finset.coe_erase]
  exact hT p hp

/-- Erdős Problem 216, formal-conjectures form (`Erdos216.erdos_216` in PR #6775, with
`answer(False)`): it is not the case that `g(k)` exists for every `k ≥ 3`. -/
theorem erdos_216' : (∀ k ≥ 3, (cardSet' k).Nonempty) ↔ False := by
  refine iff_false_intro fun h => ?_
  obtain ⟨N, hN⟩ := h 7 (by norm_num)
  rw [cardSet'_eq_empty 7 le_rfl] at hN
  exact hN

/-- Equivalent negated form of `erdos_216'`. -/
theorem not_forall_cardSet'_nonempty : ¬ ∀ k ≥ 3, (cardSet' k).Nonempty :=
  erdos_216'.1

/-- With the `sInf ∅ = 0` convention of PR #6775, `g' n = 0` for `n ≥ 7`. -/
theorem g'_eq_zero (n : ℕ) (hn : 7 ≤ n) : g' n = 0 := by
  rw [g', cardSet'_eq_empty n hn, Nat.sInf_empty]

end FormalConjectures216

end Horton

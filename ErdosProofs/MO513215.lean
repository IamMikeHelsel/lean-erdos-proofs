module

public import Mathlib

/-!
# MathOverflow 513215: rational reciprocal sums before and after a unit shift

**Question** (MathOverflow 513215, "Can an integer reciprocal series remain rational
after a unit shift in the denominator?", asked by *bihariforces*, July 2026):
Let `(a_n)_{n ≥ 1}` be a sequence of positive integers (repetitions allowed) such that
`∑ 1/a_n` converges, and put `S(k) = ∑_{n ≥ 1} 1/(a_n + k)`. Is there such a sequence with
both `S(0) ∈ ℚ` and `S(1) ∈ ℚ`?

**Answer** (accepted community-wiki answer by *DSM*, credited to a comment of
*Gerry Myerson*): yes. Take `a_n = n (n + 3) / 2`. Then, by telescoping,
* `S(0) = ∑ 2/(n(n+3)) = (2/3)(1 + 1/2 + 1/3) = 11/9`,
* `S(1) = ∑ 2/((n+1)(n+2)) = 1`.

(See also Kovač–Tao, arXiv:2406.17593, for a far-reaching generalisation.)

We formalise this in `ℝ`. Mathlib sequences are indexed from `0`, so the `n`-th term of the
MO sequence (`n ≥ 1`) is `a (n + 1)`. Since all terms are positive, `HasSum` here is the
same as ordinary (absolute) convergence of the series to the stated value.
-/

@[expose] public section

namespace MO513215

open Filter Topology

/-- The sequence `a_n = n (n + 3) / 2` from the accepted answer (used for `n ≥ 1`). -/
def a (n : ℕ) : ℕ := n * (n + 3) / 2

lemma two_mul_a (n : ℕ) : 2 * a n = n * (n + 3) := by
  apply Nat.two_mul_div_two_of_even
  have h : n * (n + 3) = n * (n + 1) + 2 * n := by ring
  rw [h]
  exact (Nat.even_mul_succ_self n).add (even_two_mul n)

lemma a_cast (n : ℕ) : (a n : ℝ) = n * (n + 3) / 2 := by
  have h := congrArg (fun m : ℕ => (m : ℝ)) (two_mul_a n)
  push_cast at h
  linarith

/-- Every term `a_n`, `n ≥ 1`, is a positive integer. -/
lemma a_pos (n : ℕ) : 0 < a (n + 1) := by
  have h := two_mul_a (n + 1)
  rcases Nat.eq_zero_or_pos (a (n + 1)) with h0 | h0
  · rw [h0] at h; simp at h
  · exact h0

lemma term0 (n : ℕ) : 1 / (a (n + 1) : ℝ) = 2 / ((n + 1) * (n + 4)) := by
  rw [a_cast, one_div_div]; push_cast; ring

lemma term1 (n : ℕ) : 1 / ((a (n + 1) : ℝ) + 1) = 2 / ((n + 2) * (n + 3)) := by
  rw [a_cast]; push_cast
  have h : ((n : ℝ) + 1) * ((n : ℝ) + 1 + 3) / 2 + 1 = (n + 2) * (n + 3) / 2 := by ring
  rw [h]; field_simp

/-- Closed form of the partial sums of `S(0)` (telescoping with step 3). -/
lemma partial0 (N : ℕ) :
    ∑ i ∈ Finset.range N, (2 : ℝ) / ((i + 1) * (i + 4)) =
      11 / 9 - 2 / 3 * (1 / (N + 1) + 1 / (N + 2) + 1 / (N + 3)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

/-- Closed form of the partial sums of `S(1)` (telescoping with step 1). -/
lemma partial1 (N : ℕ) :
    ∑ i ∈ Finset.range N, (2 : ℝ) / ((i + 2) * (i + 3)) = 1 - 2 / (N + 2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

/-- `1 / (N + c) → 0` as `N → ∞`, for any real constant `c`. -/
lemma tendsto_inv_add (c : ℝ) :
    Tendsto (fun N : ℕ => 1 / ((N : ℝ) + c)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop)

/-- `S(0) = ∑_{n ≥ 1} 1 / a_n = 11/9`. -/
theorem hasSum_S0 : HasSum (fun n : ℕ => 1 / (a (n + 1) : ℝ)) (11 / 9) := by
  have hnn : ∀ n : ℕ, 0 ≤ 1 / (a (n + 1) : ℝ) := fun n => by positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  simp_rw [term0, partial0]
  have h := ((tendsto_inv_add 1).add (tendsto_inv_add 2)).add (tendsto_inv_add 3)
  have h' := (tendsto_const_nhds (x := (11 / 9 : ℝ))).sub (h.const_mul (2 / 3))
  simpa using h'

/-- `S(1) = ∑_{n ≥ 1} 1 / (a_n + 1) = 1`. -/
theorem hasSum_S1 : HasSum (fun n : ℕ => 1 / ((a (n + 1) : ℝ) + 1)) 1 := by
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((a (n + 1) : ℝ) + 1) := fun n => by positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  simp_rw [term1, partial1]
  have h : Tendsto (fun N : ℕ => 2 / ((N : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

/-- **Answer to MathOverflow 513215.** There is a sequence of positive integers
(`b n = a (n + 1) = (n+1)(n+4)/2`, i.e. `a_n = n(n+3)/2` for `n ≥ 1`) such that
`∑ 1/b_n` converges, and both `S(0) = ∑ 1/b_n` and `S(1) = ∑ 1/(b_n + 1)` converge to
rational numbers, namely `11/9` and `1`. -/
theorem mo513215 :
    ∃ b : ℕ → ℕ, (∀ n, 0 < b n) ∧
      Summable (fun n => 1 / (b n : ℝ)) ∧
      (∃ q : ℚ, HasSum (fun n => 1 / (b n : ℝ)) q) ∧
      (∃ q : ℚ, HasSum (fun n => 1 / ((b n : ℝ) + 1)) q) :=
  ⟨fun n => a (n + 1), a_pos, hasSum_S0.summable,
    ⟨11 / 9, by push_cast; exact hasSum_S0⟩, ⟨1, by push_cast; exact hasSum_S1⟩⟩

/-- The same statement phrased with `S(k) := ∑' n, 1 / (b n + k)`, matching the question. -/
theorem mo513215_tsum :
    ∃ b : ℕ → ℕ, (∀ n, 0 < b n) ∧ Summable (fun n => 1 / (b n : ℝ)) ∧
      (∑' n, 1 / ((b n : ℝ) + 0)) = (11 / 9 : ℚ) ∧
      (∑' n, 1 / ((b n : ℝ) + 1)) = (1 : ℚ) :=
  ⟨fun n => a (n + 1), a_pos, hasSum_S0.summable,
    by push_cast; simpa using hasSum_S0.tsum_eq, by push_cast; exact hasSum_S1.tsum_eq⟩

end MO513215

#print axioms MO513215.mo513215
#print axioms MO513215.mo513215_tsum

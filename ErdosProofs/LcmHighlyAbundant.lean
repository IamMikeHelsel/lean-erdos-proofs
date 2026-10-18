module

public import Mathlib

/-!
# MathOverflow 501066: `lcm(1, …, n)` is not always highly abundant

**Question** (MathOverflow 501066, "Is the least common multiple sequence `lcm(1, 2, …, n)` a
subset of the highly abundant numbers?", October 2025). A positive integer `N` is *highly
abundant* if `σ(N) > σ(m)` for every positive integer `m < N`, where `σ` is the sum of
divisors. Is `L_n = lcm(1, 2, …, n)` highly abundant for every `n`?

**Answer** (Terence Tao's answer to MO 501066): no. Take `n = 200000` and the primes
* `p_1, …, p_25 = 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577,
  587, 593, 599, 601, 607, 613, 617, 619, 631, 641` (just above `√n ≈ 447`),
* `q_1, …, q_13 = 187963, 187973, 187987, 188011, 188017, 188021, 188029, 188299, 199931,
  199933, 199961, 199967, 199999` (just below `n`).

All 38 primes lie in `(√n, n]`, so each divides `L_n` exactly once. The competitor is
`M = L_n · (p_1 ⋯ p_25) / (q_1 ⋯ q_13)`. Then `M < L_n` because `∏ p_j < ∏ q_m`, and
`σ(M) > σ(L_n)` because
`∏ (1 + p_j + p_j²) > ∏ (1 + p_j) · ∏ (1 + q_m)`.

(The MO thread contains much more: the full list of `n` for which `L_n` is highly abundant,
and a proof that `L_n` is not highly abundant for all large `n`. Here we only verify Tao's
explicit counterexample.)

## Proof structure

`L_n` has about 86,000 digits, so nothing about it is computed. The proof is structural.
* `dvd_lcmUpTo`, `not_sq_dvd_lcmUpTo`: a prime `p` with `p ≤ n < p²` divides `L_n` exactly once
  (via `Nat.factorization_lcm`).
* `sigma_mul_prod_pow`: for `B` coprime to distinct primes `p ∈ U`,
  `σ(B · ∏ p^{e p}) = σ(B) · ∏ (1 + p + ⋯ + p^{e p})`.
* `exists_competitor`: a general certificate criterion. Write `L_n = B · ∏_{p ∈ U} p`, with `B`
  coprime to `U`, and put `M = B · ∏_{p ∈ U} p^{e p}`. Two inequalities between explicit
  products over `U` give `M < L_n` and `σ(L_n) < σ(M)`.
* The certificate for Tao's 38 primes (with `e p = 2` on the `p_j` and `e p = 0` on the `q_m`)
  is checked by `decide` on numbers with a few hundred digits.
-/

@[expose] public section

namespace LcmHighlyAbundant

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `N` is *highly abundant* if `σ(m) < σ(N)` for every positive integer `m < N`
(the definition in MO 501066; OEIS A002093). -/
def HighlyAbundant (N : ℕ) : Prop :=
  ∀ m, 0 < m → m < N → σ 1 m < σ 1 N

/-- `L_n = lcm(1, 2, …, n)` (OEIS A003418). -/
def lcmUpTo (n : ℕ) : ℕ := (Icc 1 n).lcm id

example : lcmUpTo 6 = 60 := by decide

lemma lcmUpTo_ne_zero (n : ℕ) : lcmUpTo n ≠ 0 := by
  simp [lcmUpTo, Finset.lcm_eq_zero_iff]

lemma dvd_lcmUpTo {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : k ∣ lcmUpTo n :=
  Finset.dvd_lcm (f := id) (mem_Icc.2 ⟨hk, hkn⟩)

/-- The `p`-adic valuation of an lcm is at most the maximum of the valuations. -/
lemma factorization_lcm_le (p k : ℕ) (s : Finset ℕ) (h0 : ∀ i ∈ s, i ≠ 0)
    (hk : ∀ i ∈ s, i.factorization p ≤ k) : (s.lcm id).factorization p ≤ k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h0s : ∀ i ∈ s, i ≠ 0 := fun i hi => h0 i (mem_insert_of_mem hi)
    have hs : s.lcm id ≠ 0 := by
      rw [Ne, Finset.lcm_eq_zero_iff]
      simpa using fun h => h0s 0 h rfl
    rw [Finset.lcm_insert, id, lcm_eq_nat_lcm,
      Nat.factorization_lcm (h0 a (mem_insert_self a s)) hs, Finsupp.sup_apply]
    exact max_le (hk a (mem_insert_self a s))
      (ih h0s fun i hi => hk i (mem_insert_of_mem hi))

/-- A prime `p` with `n < p²` divides `L_n` at most once. -/
lemma not_sq_dvd_lcmUpTo {n p : ℕ} (hp : p.Prime) (hn : n < p ^ 2) : ¬ p ^ 2 ∣ lcmUpTo n := by
  rw [hp.pow_dvd_iff_le_factorization (lcmUpTo_ne_zero n), not_le, Nat.lt_succ_iff]
  apply factorization_lcm_le
  · intro i hi
    exact (Nat.one_le_iff_ne_zero.1 (mem_Icc.1 hi).1)
  · intro i hi
    obtain ⟨hi1, hin⟩ := mem_Icc.1 hi
    by_contra h
    have hdvd : p ^ 2 ∣ i := (hp.pow_dvd_iff_le_factorization (by omega)).2 (by omega)
    have := Nat.le_of_dvd (by omega) hdvd
    omega

/-- Multiplicativity of `σ` in the form used for the certificate. -/
lemma sigma_mul_prod_pow (B : ℕ) (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime)
    (hB : ∀ p ∈ U, ¬ p ∣ B) (e : ℕ → ℕ) :
    σ 1 (B * ∏ p ∈ U, p ^ e p) = σ 1 B * ∏ p ∈ U, ∑ i ∈ range (e p + 1), p ^ i := by
  rw [isMultiplicative_sigma.map_mul_of_coprime, isMultiplicative_sigma.map_prod]
  · exact congrArg _ (prod_congr rfl fun p hp => sigma_one_apply_prime_pow (hU p hp))
  · intro p hp q hq hpq
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hU p hp) (hU q hq)).2 hpq)
  · exact Nat.Coprime.prod_right fun p hp =>
      Nat.Coprime.pow_right _ ((hU p hp).coprime_iff_not_dvd.2 (hB p hp)).symm

/-- **Certificate criterion.** Let `U` be a set of primes in `(√n, n]` and `e : ℕ → ℕ` new
exponents. If `∏ p^{e p} < ∏ p` and `∏ (p + 1) < ∏ (1 + p + ⋯ + p^{e p})`, then
`M = L_n · ∏ p^{e p} / ∏ p` satisfies `0 < M < L_n` and `σ(L_n) < σ(M)`. -/
theorem exists_competitor (n : ℕ) (U : Finset ℕ) (e : ℕ → ℕ)
    (hU : ∀ p ∈ U, p.Prime ∧ p ≤ n ∧ n < p ^ 2)
    (hlt : ∏ p ∈ U, p ^ e p < ∏ p ∈ U, p)
    (hσ : ∏ p ∈ U, (p + 1) < ∏ p ∈ U, ∑ i ∈ range (e p + 1), p ^ i) :
    ∃ M, M * ∏ p ∈ U, p = lcmUpTo n * ∏ p ∈ U, p ^ e p ∧
      0 < M ∧ M < lcmUpTo n ∧ σ 1 (lcmUpTo n) < σ 1 M := by
  set L := lcmUpTo n with hLdef
  set R := ∏ p ∈ U, p with hRdef
  set X := ∏ p ∈ U, p ^ e p with hXdef
  have hprime : ∀ p ∈ U, p.Prime := fun p hp => (hU p hp).1
  -- `R ∣ L`
  have hRL : R ∣ L := prod_primes_dvd L (fun p hp => (hprime p hp).prime)
    fun p hp => dvd_lcmUpTo (hprime p hp).one_lt.le (hU p hp).2.1
  set B := L / R with hBdef
  have hLBR : L = B * R := (Nat.div_mul_cancel hRL).symm
  have hL0 : L ≠ 0 := lcmUpTo_ne_zero n
  have hB0 : B ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hLBR
    exact hL0 hLBR
  -- `B` is coprime to every `p ∈ U`, since `p² ∤ L`
  have hB : ∀ p ∈ U, ¬ p ∣ B := by
    intro p hp hpB
    apply not_sq_dvd_lcmUpTo (hprime p hp) (hU p hp).2.2
    rw [← hLdef, hLBR, sq]
    exact mul_dvd_mul hpB (dvd_prod_of_mem _ hp)
  have hR1 : R = ∏ p ∈ U, p ^ 1 := by simp [hRdef]
  have hσL : σ 1 L = σ 1 B * ∏ p ∈ U, (p + 1) := by
    rw [hLBR, hR1, sigma_mul_prod_pow B U hprime hB (fun _ => 1)]
    congr 1
    refine prod_congr rfl fun p _ => ?_
    simp [sum_range_succ, add_comm]
  have hσM : σ 1 (B * X) = σ 1 B * ∏ p ∈ U, ∑ i ∈ range (e p + 1), p ^ i :=
    sigma_mul_prod_pow B U hprime hB e
  have hσB : 0 < σ 1 B := sigma_pos 1 B hB0
  have hσ' : σ 1 L < σ 1 (B * X) := by
    rw [hσL, hσM]
    exact Nat.mul_lt_mul_of_pos_left hσ hσB
  refine ⟨B * X, ?_, ?_, ?_, hσ'⟩
  · rw [hLBR]; ring
  · rcases Nat.eq_zero_or_pos (B * X) with h | h
    · rw [h, ArithmeticFunction.map_zero] at hσ'
      exact absurd hσ' (Nat.not_lt_zero _)
    · exact h
  · rw [hLBR]
    exact Nat.mul_lt_mul_of_pos_left hlt (Nat.pos_of_ne_zero hB0)

/-! ## Tao's certificate for `n = 200000` -/

/-- Tao's 25 "medium" primes, just above `√200000 ≈ 447`. -/
def taoP : Finset ℕ :=
  {479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599,
    601, 607, 613, 617, 619, 631, 641}

/-- Tao's 13 "large" primes, just below `200000`. -/
def taoQ : Finset ℕ :=
  {187963, 187973, 187987, 188011, 188017, 188021, 188029, 188299, 199931, 199933, 199961,
    199967, 199999}

/-- All 38 special primes. -/
def taoU : Finset ℕ := taoP ∪ taoQ

/-- New exponents: `2` on the medium primes (which divide `L_n` once), `0` on the large ones. -/
def taoE (p : ℕ) : ℕ := if p < 1000 then 2 else 0

lemma taoU_prime : ∀ p ∈ taoU, p.Prime := by
  simp only [taoU, taoP, taoQ, mem_union, mem_insert, mem_singleton]
  rintro p (h | h) <;>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma taoU_bounds : ∀ p ∈ taoU, p ≤ 200000 ∧ 200000 < p ^ 2 := by decide +kernel

lemma tao_lt : ∏ p ∈ taoU, p ^ taoE p < ∏ p ∈ taoU, p := by decide

lemma tao_sigma : ∏ p ∈ taoU, (p + 1) < ∏ p ∈ taoU, ∑ i ∈ range (taoE p + 1), p ^ i := by
  decide

/-- `∏_{taoU} p^{e p} / ∏_{taoU} p = ∏ p_j / ∏ q_m`. -/
lemma tao_ratio : (∏ p ∈ taoU, p ^ taoE p) * ∏ q ∈ taoQ, q =
    (∏ p ∈ taoU, p) * ∏ p ∈ taoP, p := by
  decide

/-- **Tao's counterexample.** For `L = lcm(1, …, 200000)` there is `M` with
`M · ∏ q_m = L · ∏ p_j` (that is, `M = L · ∏ p_j / ∏ q_m`), `0 < M < L` and `σ(L) < σ(M)`. -/
theorem tao_witness : ∃ M, M * ∏ q ∈ taoQ, q = lcmUpTo 200000 * ∏ p ∈ taoP, p ∧
    0 < M ∧ M < lcmUpTo 200000 ∧ σ 1 (lcmUpTo 200000) < σ 1 M := by
  obtain ⟨M, hM, hpos, hlt, hσ⟩ := exists_competitor 200000 taoU taoE
    (fun p hp => ⟨taoU_prime p hp, taoU_bounds p hp⟩) tao_lt tao_sigma
  refine ⟨M, ?_, hpos, hlt, hσ⟩
  -- abstract the products, so that `ring` does not try to unfold them
  have key : ∀ M L R X Q P : ℕ, 0 < R → M * R = L * X → X * Q = R * P → M * Q = L * P := by
    intro M L R X Q P hR h1 h2
    apply Nat.eq_of_mul_eq_mul_right hR
    calc M * Q * R = (M * R) * Q := by ring
      _ = L * (X * Q) := by rw [h1]; ring
      _ = L * P * R := by rw [h2]; ring
  exact key _ _ _ _ _ _ (prod_pos fun p hp => (taoU_prime p hp).pos) hM tao_ratio

/-- **MO 501066, answered in the negative:** `lcm(1, 2, …, 200000)` is not highly abundant. -/
theorem lcmUpTo_200000_not_highlyAbundant : ¬ HighlyAbundant (lcmUpTo 200000) := by
  obtain ⟨M, -, hpos, hlt, hσ⟩ := tao_witness
  intro h
  exact absurd (h M hpos hlt) (Nat.lt_asymm hσ)

/-- The variant without the positivity condition on `m` also fails. -/
theorem lcmUpTo_200000_not_forall_lt :
    ¬ ∀ m < lcmUpTo 200000, σ 1 m < σ 1 (lcmUpTo 200000) := by
  intro h
  exact lcmUpTo_200000_not_highlyAbundant fun m _ hm => h m hm

/-- The conjecture of MO 501066 is false. -/
theorem not_forall_lcmUpTo_highlyAbundant : ¬ ∀ n, HighlyAbundant (lcmUpTo n) :=
  fun h => lcmUpTo_200000_not_highlyAbundant (h 200000)

end LcmHighlyAbundant

#print axioms LcmHighlyAbundant.lcmUpTo_200000_not_highlyAbundant
#print axioms LcmHighlyAbundant.tao_witness
#print axioms LcmHighlyAbundant.not_forall_lcmUpTo_highlyAbundant

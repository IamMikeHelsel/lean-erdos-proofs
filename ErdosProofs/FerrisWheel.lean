module

public import Mathlib

/-!
# MathOverflow 515611: Ferris wheel numbers exist

**Question** (MathOverflow 515611, "Do Ferris wheel numbers exist?", asked by *Philip Weiss*,
September 2026). Call `n > 1` a *Ferris wheel number* if its positive divisors `d₁, …, d_k`
(`k = d(n)`) can be placed as weights at the `k` equally spaced points of a circle so that the
centre of mass is the centre, i.e. there is a permutation `π` with
`∑_{j=1}^{k} d_{π(j)} ζ^{j-1} = 0`, `ζ = e^{2πi/k}`.

**Answer** (accepted answer by *Vepir*): yes, `n = 907200 = 2⁶·3⁴·5²·7` (210 divisors) is one,
with the explicit arrangement `wheel` below (copied verbatim from the answer).

**Proof.** We do not divide by the cyclotomic polynomial `Φ₂₁₀`. Instead the coefficient
sequence `a_j = wheel[j]` is written (by an exact integer computation, re-checked by `decide`)
as `a_j = g₂(j mod 105) + g₃(j mod 70) + g₅(j mod 42) + g₇(j mod 30)`. A sequence of period
`210/p` contributes a sum of rotated regular `p`-gons, which vanishes since
`1 + ω + ⋯ + ω^{p-1} = 0` for a primitive `p`-th root of unity `ω = ζ^{210/p}`.
(The lists `g₂, …, g₇` were obtained by peeling off, prime by prime, the `p`-gon through each
position with residue `p - 1 mod p`; this is the Rédei–de Bruijn–Schoenberg description of
vanishing sums of 210-th roots of unity.) The bijection with `Nat.divisors 907200` follows from
`wheel.Nodup`, each entry dividing `907200`, and `d(907200) = 7·5·3·2 = 210`.
-/

@[expose] public section

open Complex Finset Real

set_option maxRecDepth 100000

namespace FerrisWheel

/-- A sum over `Fin n` whose coefficients are periodic with period `m`, where `n = p * m`
and `p > 1`, vanishes against powers of a primitive `n`-th root of unity: it is a sum of
rotated regular `p`-gons. -/
lemma sum_periodic_eq_zero {ζ : ℂ} {n p m : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : n = p * m)
    (hp : 1 < p) (hm : 0 < m) (g : ℕ → ℂ) :
    ∑ j : Fin n, g (j % m) * ζ ^ (j : ℕ) = 0 := by
  subst hn
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_eq_zero fun y _ => ?_
  simp only [finProdFinEquiv_apply_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.2,
    pow_add, pow_mul, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i => (ζ ^ m) ^ i) p,
    (hζ.pow (by positivity) (mul_comm p m)).geom_sum_eq_zero hp]
  simp

def wheel : List ℕ :=
  [15, 1344, 3150, 270, 6720, 16, 12960, 64, 105, 8, 200, 1575, 18900, 84,
  6480, 3360, 1512, 25, 432, 7, 28, 324, 448, 27, 11200, 4536, 1680, 9,
  360, 129600, 18, 45, 144, 63, 3024, 525, 405, 350, 135, 43200, 1050, 28350,
  12600, 96, 320, 5670, 7200, 2160, 18144, 5400, 160, 600, 16200, 4032, 20160, 3600,
  81, 900, 40, 113400, 21600, 1, 6048, 288, 15120, 80, 30, 840, 1800, 302400,
  945, 2835, 2400, 378, 45360, 75, 64800, 6, 1008, 864, 36, 420, 4725, 14175,
  100, 2880, 8640, 5184, 70, 100800, 12, 189, 48, 14, 32400, 1080, 2268, 56,
  1134, 8400, 700, 6300, 11340, 1890, 453600, 336, 3240, 280, 504, 800, 2025, 7560,
  560, 108, 30240, 126, 4800, 10800, 75600, 151200, 4, 35, 315, 9450, 37800, 33600,
  150, 2592, 192, 2700, 8100, 60, 225, 168, 2100, 120, 648, 20, 240, 226800,
  1400, 10, 216, 450, 22680, 1440, 1350, 10080, 1728, 90720, 1120, 2, 12096, 1260,
  72, 4320, 1600, 14400, 175, 32, 60480, 675, 224, 252, 630, 25920, 567, 36288,
  300, 672, 162, 3780, 24, 210, 400, 50, 810, 42, 4200, 181440, 576, 3,
  4050, 112, 50400, 5040, 5, 756, 180, 25200, 1296, 9072, 5600, 2240, 1620, 2800,
  960, 1200, 90, 720, 2016, 540, 56700, 21, 2520, 54, 480, 16800, 140, 907200]

def g2 : List ℤ :=
  [336, 1344, 280, 270, 800, 16, 7560, 64, 108, 8, 126, 1575,
  10800, 84, 151200, 3360, 35, 25, 9450, 7, 33600, 324, 2592, 27,
  2700, 4536, 60, 9, 168, 129600, 120, 45, 20, 63, 226800, 525,
  10, 350, 450, 43200, 1440, 28350, 10080, 96, 90720, 5670, 2, 2160,
  1260, 5400, 4320, 600, 14400, 4032, 32, 3600, 675, 900, 252, 113400,
  25920, 1, 36288, 288, 672, 80, 3780, 840, 210, 302400, 50, 2835,
  42, 378, 181440, 75, 3, 6, 112, 864, 5040, 420, 756, 14175,
  25200, 2880, 9072, 5184, 2240, 100800, 2800, 189, 1200, 14, 720, 1080,
  540, 56, 21, 8400, 54, 6300, 16800, 1890, 907200]

def g3 : List ℤ :=
  [875, 0, 2870, 0, -136080, 0, -27000, 0, -3, 0, -5004, 0,
  9936, 0, -144720, 0, -432, 0, -3857, 0, -33572, 0, -1152, 0,
  -112770, 0, 1620, 0, 1113, 0, 82, 0, 124, 0, -453600, 0,
  -2025, 0, -315, 0, 2009, 0, 4044, 0, -90400, 0, 3225, 0,
  -13995, 0, -4160, 0, 290, 0, -99180, 0, -594, 0, 165, 0,
  936, 0, -30240, 0, -127500, 0, -5820, 0, 1590, 0]

def g5 : List ℤ :=
  [119620, 0, 0, 0, 142000, 0, 151600, 0, 0, 0, 144450, 0,
  119308, 0, 0, 0, 139936, 0, 115560, 0, 0, 0, 141948, 0,
  121270, 0, 0, 0, 139392, 0, 120632, 0, 0, 0, 229824, 0,
  121620, 0, 0, 0, 136973, 0]

def g7 : List ℤ :=
  [-120816, 0, 0, 0, 0, 0, -119200, 0, 0, 0, -139372, 0,
  -121144, 0, 0, 0, -138027, 0, -120721, 0, 0, 0, -142940, 0,
  0, 0, 0, 0, -140313, 0]

lemma wheel_length : wheel.length = 210 := rfl

lemma wheel_decomp : ∀ j : Fin 210, (wheel.getD j 0 : ℤ) =
    g2.getD (j % 105) 0 + g3.getD (j % 70) 0 + g5.getD (j % 42) 0 + g7.getD (j % 30) 0 := by
  decide

lemma wheel_nodup : wheel.Nodup := by decide

lemma wheel_dvd : ∀ j : Fin 210, wheel.getD j 0 ∣ 907200 := by decide

lemma card_divisors : (Nat.divisors 907200).card = 210 := by
  rw [show 907200 = 64 * 81 * 25 * 7 by norm_num, Nat.Coprime.card_divisors_mul (by norm_num),
    Nat.Coprime.card_divisors_mul (by norm_num), Nat.Coprime.card_divisors_mul (by norm_num)]
  decide

/-- `n > 1` is a *Ferris wheel number* if its `k = d(n)` positive divisors can be placed
at the `k`-th roots of unity so that the weighted sum is zero (MathOverflow 515611). -/
def IsFerrisWheel (n : ℕ) : Prop :=
  1 < n ∧ ∃ f : Fin n.divisors.card ≃ n.divisors,
    ∑ j, ((f j : ℕ) : ℂ) * exp (2 * π * I * (j : ℕ) / n.divisors.card) = 0

/-- `907200` is a Ferris wheel number, via the arrangement in Vepir's accepted answer. -/
theorem ferrisWheel_907200 : IsFerrisWheel 907200 := by
  refine ⟨by norm_num, ?_⟩
  rw [card_divisors]
  let f : Fin 210 → Nat.divisors 907200 := fun k =>
    ⟨wheel.getD k 0, Nat.mem_divisors.2 ⟨wheel_dvd k, by norm_num⟩⟩
  have hf : Function.Bijective f := by
    refine (Fintype.bijective_iff_injective_and_card f).2
      ⟨fun i j h => ?_, by simp [card_divisors]⟩
    have h' : wheel.getD i 0 = wheel.getD j 0 := congrArg Subtype.val h
    simp only [List.getD_eq_getElem _ _ (by rw [wheel_length]; exact i.2),
      List.getD_eq_getElem _ _ (by rw [wheel_length]; exact j.2)] at h'
    exact Fin.ext ((wheel_nodup.getElem_inj_iff).1 h')
  refine ⟨Equiv.ofBijective f hf, ?_⟩
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℂ, ζ = exp (2 * π * I / 210) := ⟨_, rfl⟩
  have hζ : IsPrimitiveRoot ζ 210 := by
    simpa [hζdef] using isPrimitiveRoot_exp 210 (by norm_num)
  have key : ∀ j : Fin 210, ((Equiv.ofBijective f hf j : ℕ) : ℂ) *
      exp (2 * π * I * (j : ℕ) / (210 : ℕ)) =
      (g2.getD (j % 105) 0 : ℂ) * ζ ^ (j : ℕ) + (g3.getD (j % 70) 0 : ℂ) * ζ ^ (j : ℕ) +
      (g5.getD (j % 42) 0 : ℂ) * ζ ^ (j : ℕ) + (g7.getD (j % 30) 0 : ℂ) * ζ ^ (j : ℕ) := by
    intro j
    have h := congrArg (Int.cast : ℤ → ℂ) (wheel_decomp j)
    push_cast at h
    rw [show exp (2 * π * I * (j : ℕ) / (210 : ℕ)) = ζ ^ (j : ℕ) by
      rw [hζdef, ← Complex.exp_nat_mul]; congr 1; push_cast; ring]
    simp only [Equiv.ofBijective_apply, f, h]
    ring
  have hP (p m : ℕ) (g : List ℤ) (h : 210 = p * m) (hp : 1 < p) (hm : 0 < m) :
      ∑ j : Fin 210, (g.getD (j % m) 0 : ℂ) * ζ ^ (j : ℕ) = 0 :=
    sum_periodic_eq_zero hζ h hp hm fun r => (g.getD r 0 : ℂ)
  simp only [key, sum_add_distrib, hP 2 105 g2 rfl one_lt_two (by norm_num),
    hP 3 70 g3 rfl (by norm_num) (by norm_num), hP 5 42 g5 rfl (by norm_num) (by norm_num),
    hP 7 30 g7 rfl (by norm_num) (by norm_num), add_zero]

/-- Ferris wheel numbers exist (answer to MathOverflow 515611). -/
theorem exists_ferrisWheel : ∃ n, IsFerrisWheel n := ⟨907200, ferrisWheel_907200⟩

end FerrisWheel

#print axioms FerrisWheel.exists_ferrisWheel
#print axioms FerrisWheel.ferrisWheel_907200

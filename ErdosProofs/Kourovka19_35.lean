import Mathlib

/-!
# Kourovka Notebook Problem 19.35 has a negative answer

Kourovka Notebook (Khukhro–Mazurov, eds., arXiv:1401.0300), Problem 19.35 (M. H. Hooshmand):

> Let `G` be a finite group of order `n`. Is it true that for every factorization
> `n = a₁ ⋯ aₖ` there exist subsets `A₁, …, Aₖ` such that `|A₁| = a₁, …, |Aₖ| = aₖ` and
> `G = A₁ ⋯ Aₖ`?

The answer is *no*. G. M. Bergman (letter of 19 December 2019,
https://math.berkeley.edu/~gbergman/papers/gp_factzn.pdf) observed that the alternating group
`A₄` (of order `12 = 2 · 3 · 2`) admits no subsets `A, B, C` with `|A| = 2`, `|B| = 3`,
`|C| = 2` and `A * B * C = A₄`. R. McCulloch, *Some answers regarding factorizations of finite
groups*, arXiv:2607.20569 (2026), writes up Bergman's argument and gives counterexamples for all
`k ≥ 3`; only the `A₄` case is formalized here.

## Proof outline (fully kernel-checked, no `native_decide`)

1. *Normalization.* If `A * B * C = G` and `p ∈ A`, `r ∈ B`, `u ∈ C`, then the translates
   `A' = (p r)⁻¹ A r`, `B' = r⁻¹ B`, `C' = C u⁻¹` again cover `G`, have the same sizes, and each
   contains `1` (`normalize`). So it suffices to rule out `A = {1, a}`, `B = {1, b₁, b₂}`,
   `C = {1, c}`.
2. *A concrete model of `A₄`.* `E : Fin 12 → A₄` lists the twelve even permutations of `Fin 4`,
   each as a product of two transpositions; `mulT` is the multiplication table, packed into a
   single natural number literal. We check by `decide +kernel` that `E` is injective and
   multiplicative; bijectivity follows from `|A₄| = 4!/2 = 12`.
3. *Finite search.* `checkB` verifies (by `decide +kernel`) that for all `a, b₁, b₂, c < 12`
   some element is not among the twelve products `x * y * z` with `x ∈ {1, a}`,
   `y ∈ {1, b₁, b₂}`, `z ∈ {1, c}`.
-/

namespace Kourovka19_35

open Equiv
open scoped Pointwise

/-- The property asked for in Kourovka Notebook Problem 19.35: for every finite group `G` and
every factorization `|G| = a₁ ⋯ aₖ` (given as a list `a = [a₁, …, aₖ]`) there are subsets
`A₁, …, Aₖ` with `|Aᵢ| = aᵢ` and `A₁ * ⋯ * Aₖ = G` (pointwise product of finsets). -/
def Kourovka19_35Statement : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (a : List ℕ),
    a.prod = Fintype.card G →
      ∃ A : List (Finset G), A.map Finset.card = a ∧ A.prod = Finset.univ

/-! ### Step 1: normalization -/

/-- If `A * B * C` covers `G` then so do the translates `(p r)⁻¹ A r`, `r⁻¹ B`, `C u⁻¹`. -/
lemma normalize {G : Type*} [Group G] (A B C : Set G)
    (h : ∀ z, ∃ x ∈ A, ∃ y ∈ B, ∃ w ∈ C, x * y * w = z) (p r u : G) (t : G) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ w ∈ C, t = ((p * r)⁻¹ * x * r) * (r⁻¹ * y) * (w * u⁻¹) := by
  obtain ⟨x, hx, y, hy, w, hw, hxyw⟩ := h (p * r * t * u)
  refine ⟨x, hx, y, hy, w, hw, ?_⟩
  have : t = (p * r)⁻¹ * (x * y * w) * u⁻¹ := by rw [hxyw]; group
  rw [this]; group

/-! ### Step 2: a concrete model of `A₄` -/

/-- Multiplication table of `A₄` on `{0, …, 11}`, packed into one literal (4 bits per entry). -/
def mulN (i j : ℕ) : ℕ :=
  ((154726108906755412667904399632546243950144254042250443404951759298091694343923020738209645234929318317933251037174302361414362188776702137617442012922456545524113962882576912 : ℕ) >>> (4 * (12 * i + j))) % 16 % 12

/-- Multiplication table of `A₄` on `Fin 12`. -/
def mulT (i j : Fin 12) : Fin 12 := ⟨mulN i.val j.val, Nat.mod_lt _ (by decide)⟩

/-- The `i`-th element of `A₄` is `swap (sp i).1 (sp i).2.1 * swap (sp i).2.2.1 (sp i).2.2.2`. -/
def sp : Fin 12 → Fin 4 × Fin 4 × Fin 4 × Fin 4 :=
  ![(0, 1, 0, 1), (0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2), (0, 1, 1, 2), (0, 1, 1, 3),
    (0, 2, 2, 1), (0, 2, 2, 3), (0, 3, 3, 1), (0, 3, 3, 2), (1, 2, 2, 3), (1, 3, 3, 2)]

/-- The twelve even permutations of `Fin 4`. -/
def σ (i : Fin 12) : Perm (Fin 4) :=
  swap (sp i).1 (sp i).2.1 * swap (sp i).2.2.1 (sp i).2.2.2

lemma σ_mem (i : Fin 12) : σ i ∈ alternatingGroup (Fin 4) := by
  have h₁ : ∀ i : Fin 12, (sp i).1 ≠ (sp i).2.1 := by decide
  have h₂ : ∀ i : Fin 12, (sp i).2.2.1 ≠ (sp i).2.2.2 := by decide
  rw [Perm.mem_alternatingGroup, σ, Perm.sign_mul, Perm.sign_swap (h₁ i),
    Perm.sign_swap (h₂ i)]
  decide

/-- The enumeration `Fin 12 → A₄`. -/
def E (i : Fin 12) : alternatingGroup (Fin 4) := ⟨σ i, σ_mem i⟩

lemma σ_mulT : ∀ i j : Fin 12, ∀ x : Fin 4, σ (mulT i j) x = σ i (σ j x) := by
  decide +kernel

lemma σ_inj : ∀ i j : Fin 12, (∀ x : Fin 4, σ i x = σ j x) → i = j := by
  decide +kernel

lemma E_mul (i j : Fin 12) : E (mulT i j) = E i * E j := by
  apply Subtype.ext
  exact Equiv.ext fun x => σ_mulT i j x

lemma E_zero : E 0 = 1 := by
  apply Subtype.ext
  ext x
  revert x
  decide

lemma E_injective : Function.Injective E := fun i j h =>
  σ_inj i j fun x => by
    have := congrArg (fun g : alternatingGroup (Fin 4) => (g : Perm (Fin 4)) x) h
    exact this

lemma card_A4 : Fintype.card (alternatingGroup (Fin 4)) = 12 := by
  rw [card_alternatingGroup]; simp [Nat.factorial]

lemma E_bijective : Function.Bijective E :=
  (Fintype.bijective_iff_injective_and_card E).2 ⟨E_injective, by rw [Fintype.card_fin, card_A4]⟩

/-! ### Step 3: the finite search -/

/-- The twelve products `x * y * z`, `x ∈ {0, a}`, `y ∈ {0, b₁, b₂}`, `z ∈ {0, c}`. -/
def prods (a b₁ b₂ c : ℕ) : List ℕ :=
  [0, a].flatMap fun x => [0, b₁, b₂].flatMap fun y => [0, c].map fun z => mulN (mulN x y) z

/-- For all `a b₁ b₂ c < 12`, some `k < 12` is missed by `prods a b₁ b₂ c`. -/
def checkB : Bool :=
  (List.range 12).all fun a => (List.range 12).all fun b₁ => (List.range 12).all fun b₂ =>
    (List.range 12).all fun c => (List.range 12).any fun k => !((prods a b₁ b₂ c).contains k)

theorem checkB_eq : checkB = true := by decide +kernel

/-- The search, restated over `Fin 12`. -/
lemma no_cover (a b₁ b₂ c : Fin 12) : ∃ k : Fin 12, ∀ x y z : Fin 12,
    (x = 0 ∨ x = a) → (y = 0 ∨ y = b₁ ∨ y = b₂) → (z = 0 ∨ z = c) →
      mulT (mulT x y) z ≠ k := by
  have h := checkB_eq
  simp only [checkB, List.all_eq_true, List.any_eq_true, List.mem_range, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, List.contains_iff_mem] at h
  obtain ⟨k, hk, hnot⟩ := h a.val a.isLt b₁.val b₁.isLt b₂.val b₂.isLt c.val c.isLt
  refine ⟨⟨k, hk⟩, fun x y z hx hy hz heq => ?_⟩
  have heq' : mulN (mulN x.val y.val) z.val = k := congrArg Fin.val heq
  revert hnot
  rw [← heq']
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp [prods]

/-! ### The main theorems -/

/-- **Bergman's counterexample to Kourovka 19.35.** The alternating group `A₄` (order
`12 = 2 · 3 · 2`) has no subsets `A, B, C` with `|A| = 2`, `|B| = 3`, `|C| = 2` and
`A * B * C = A₄`. -/
theorem A4_no_factorization :
    ¬ ∃ A B C : Finset (alternatingGroup (Fin 4)),
      A.card = 2 ∧ B.card = 3 ∧ C.card = 2 ∧ A * B * C = Finset.univ := by
  rintro ⟨A, B, C, hA, hB, hC, hABC⟩
  obtain ⟨p, q, -, rfl⟩ := Finset.card_eq_two.1 hA
  obtain ⟨r, s, t, -, -, -, rfl⟩ := Finset.card_eq_three.1 hB
  obtain ⟨u, v, -, rfl⟩ := Finset.card_eq_two.1 hC
  have hcov : ∀ z, ∃ x ∈ ({p, q} : Set (alternatingGroup (Fin 4))),
      ∃ y ∈ ({r, s, t} : Set (alternatingGroup (Fin 4))),
      ∃ w ∈ ({u, v} : Set (alternatingGroup (Fin 4))), x * y * w = z := by
    intro z
    have hz : z ∈ ({p, q} : Finset _) * {r, s, t} * {u, v} := hABC ▸ Finset.mem_univ z
    obtain ⟨xy, hxy, w, hw, rfl⟩ := Finset.mem_mul.1 hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_mul.1 hxy
    exact ⟨x, by simpa using hx, y, by simpa using hy, w, by simpa using hw, rfl⟩
  set e := Equiv.ofBijective E E_bijective
  obtain ⟨k, hk⟩ := no_cover (e.symm ((p * r)⁻¹ * q * r)) (e.symm (r⁻¹ * s))
    (e.symm (r⁻¹ * t)) (e.symm (v * u⁻¹))
  obtain ⟨x, hx, y, hy, w, hw, h⟩ := normalize _ _ _ hcov p r u (E k)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hw
  have hx' : ∃ x' : Fin 12, (x' = 0 ∨ x' = e.symm ((p * r)⁻¹ * q * r)) ∧
      E x' = (p * r)⁻¹ * x * r := by
    rcases hx with rfl | rfl
    · exact ⟨0, Or.inl rfl, by rw [E_zero]; group⟩
    · exact ⟨_, Or.inr rfl, e.apply_symm_apply _⟩
  have hy' : ∃ y' : Fin 12, (y' = 0 ∨ y' = e.symm (r⁻¹ * s) ∨ y' = e.symm (r⁻¹ * t)) ∧
      E y' = r⁻¹ * y := by
    rcases hy with rfl | rfl | rfl
    · exact ⟨0, Or.inl rfl, by rw [E_zero]; group⟩
    · exact ⟨_, Or.inr (Or.inl rfl), e.apply_symm_apply _⟩
    · exact ⟨_, Or.inr (Or.inr rfl), e.apply_symm_apply _⟩
  have hw' : ∃ w' : Fin 12, (w' = 0 ∨ w' = e.symm (v * u⁻¹)) ∧ E w' = w * u⁻¹ := by
    rcases hw with rfl | rfl
    · exact ⟨0, Or.inl rfl, by rw [E_zero]; group⟩
    · exact ⟨_, Or.inr rfl, e.apply_symm_apply _⟩
  obtain ⟨x', hx'1, hx'2⟩ := hx'
  obtain ⟨y', hy'1, hy'2⟩ := hy'
  obtain ⟨w', hw'1, hw'2⟩ := hw'
  apply hk x' y' w' hx'1 hy'1 hw'1
  apply E_injective
  rw [E_mul, E_mul, hx'2, hy'2, hw'2, ← h]

/-- **Kourovka Notebook Problem 19.35 has a negative answer** (Bergman): the group `A₄` and the
factorization `12 = 2 · 3 · 2` are a counterexample. -/
theorem not_kourovka19_35 : ¬ Kourovka19_35Statement := by
  intro H
  obtain ⟨L, hL, hprod⟩ := H (alternatingGroup (Fin 4)) [2, 3, 2] (by rw [card_A4]; rfl)
  rcases L with _ | ⟨A, _ | ⟨B, _ | ⟨C, _ | ⟨D, L⟩⟩⟩⟩ <;> simp at hL
  obtain ⟨hA, hB, hC⟩ := hL
  exact A4_no_factorization ⟨A, B, C, hA, hB, hC, by simpa [mul_assoc] using hprod⟩

end Kourovka19_35

#print axioms Kourovka19_35.A4_no_factorization
#print axioms Kourovka19_35.not_kourovka19_35

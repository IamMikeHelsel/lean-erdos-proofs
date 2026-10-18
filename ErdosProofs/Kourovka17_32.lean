module

public import Mathlib

/-!
# Kourovka Notebook Problem 17.32 has a negative answer

Kourovka Notebook (Khukhro–Mazurov, eds.), Problem 17.32:
Let `w ∈ Fₙ` and `φ ∈ Aut(Fₙ)`. If `⟨w, φ(w), …, φⁿ(w)⟩ = Fₙ`, must
`⟨w, φ(w), …, φⁿ⁻¹(w)⟩ = Fₙ`?

V. Ionin and A. Semidetnov, *On some more problems from the Kourovka Notebook*,
arXiv:2608.29219 (2026), Question 8.1, answer this in the negative for `n = 2`:
in `F₂ = ⟨x, y⟩` take `w = xy` and `φ(x) = yx`, `φ(y) = x`
(with inverse `φ⁻¹(x) = y`, `φ⁻¹(y) = xy⁻¹`). Then `φ(w) = yx²`, `φ²(w) = w²x`, so
`x = w⁻²φ²(w)` and `y = x⁻¹w`, whence `⟨w, φ(w), φ²(w)⟩ = F₂`; but the epimorphism
`π : F₂ → S₃`, `x ↦ (1 2 3)`, `y ↦ (2 3)` sends both `w` and `φ(w)` to `(1 2)`,
so `⟨w, φ(w)⟩ ≠ F₂`.

This file formalizes that counterexample.
-/

@[expose] public section

namespace Kourovka17_32

open Equiv

/-- The free group of rank 2. -/
abbrev F := FreeGroup (Fin 2)

/-- First free generator. -/
def x : F := FreeGroup.of 0
/-- Second free generator. -/
def y : F := FreeGroup.of 1

/-- The endomorphism `x ↦ yx`, `y ↦ x`. -/
def φHom : F →* F := FreeGroup.lift ![y * x, x]
/-- Its inverse `x ↦ y`, `y ↦ xy⁻¹`. -/
def ψHom : F →* F := FreeGroup.lift ![y, x * y⁻¹]

@[simp] lemma φHom_x : φHom x = y * x := by simp [φHom, x]
@[simp] lemma φHom_y : φHom y = x := by simp [φHom, y]
@[simp] lemma ψHom_x : ψHom x = y := by simp [ψHom, x]
@[simp] lemma ψHom_y : ψHom y = x * y⁻¹ := by simp [ψHom, y]

/-- The automorphism `φ : x ↦ yx, y ↦ x` of `F₂`. -/
def φ : F ≃* F :=
  MonoidHom.toMulEquiv φHom ψHom
    (by
      apply FreeGroup.ext_hom
      intro i
      fin_cases i
      · change ψHom (φHom x) = x; simp
      · change ψHom (φHom y) = y; simp)
    (by
      apply FreeGroup.ext_hom
      intro i
      fin_cases i
      · change φHom (ψHom x) = x; simp
      · change φHom (ψHom y) = y; simp)

@[simp] lemma φ_apply (g : F) : φ g = φHom g := rfl

/-- The element `w = xy`. -/
def w : F := x * y

lemma φ_w : φ w = y * x * x := by simp [w, mul_assoc]

lemma φ_φ_w : φ (φ w) = w * w * x := by simp [w, mul_assoc]

/-- `x = w⁻² φ²(w)`. -/
lemma x_eq : x = (w * w)⁻¹ * φ (φ w) := by rw [φ_φ_w]; group

/-- `y = x⁻¹ w`. -/
lemma y_eq : y = x⁻¹ * w := by simp [w]

/-- The epimorphism `π : F₂ → S₃`, `x ↦ (1 2 3)`, `y ↦ (2 3)` (0-indexed). -/
def π : F →* Perm (Fin 3) := FreeGroup.lift ![finRotate 3, swap 1 2]

@[simp] lemma π_x : π x = finRotate 3 := by simp [π, x]
@[simp] lemma π_y : π y = swap 1 2 := by simp [π, y]

/-- `⟨w, φ(w), φ²(w)⟩ = F₂`. -/
theorem closure_three_eq_top (S : Set F) (h0 : w ∈ S) (h2 : φ (φ w) ∈ S) :
    Subgroup.closure S = ⊤ := by
  have hw : w ∈ Subgroup.closure S := Subgroup.subset_closure h0
  have h2' : φ (φ w) ∈ Subgroup.closure S := Subgroup.subset_closure h2
  have hx : x ∈ Subgroup.closure S := by
    rw [x_eq]; exact mul_mem (inv_mem (mul_mem hw hw)) h2'
  have hy : y ∈ Subgroup.closure S := by
    rw [y_eq]; exact mul_mem (inv_mem hx) hw
  rw [eq_top_iff, ← FreeGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hx
  · exact hy

/-- `⟨w, φ(w)⟩ ≠ F₂`: its image under `π` fixes the point `2`, but `π x` does not. -/
theorem closure_two_ne_top (S : Set F) (hS : S ⊆ {w, φ w}) :
    Subgroup.closure S ≠ ⊤ := by
  intro htop
  have hle : Subgroup.closure S ≤
      (MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3)).comap π := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hS hg with rfl | rfl
    · simp only [SetLike.mem_coe, Subgroup.mem_comap, MulAction.mem_stabilizer_iff,
        Perm.smul_def, w, map_mul, π_x, π_y]
      decide
    · simp only [SetLike.mem_coe, Subgroup.mem_comap, MulAction.mem_stabilizer_iff,
        Perm.smul_def, φ_w, map_mul, π_x, π_y]
      decide
  have hx : x ∈ Subgroup.closure S := htop ▸ Subgroup.mem_top x
  have := hle hx
  simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Perm.smul_def, π_x] at this
  revert this
  decide

/-- Concrete form: there are `φ ∈ Aut(F₂)` and `w ∈ F₂` with `⟨w, φ(w)⟩ ≠ F₂` but
`⟨w, φ(w), φ²(w)⟩ = F₂`. -/
theorem exists_counterexample :
    ∃ (φ : FreeGroup (Fin 2) ≃* FreeGroup (Fin 2)) (w : FreeGroup (Fin 2)),
      Subgroup.closure {w, φ w} ≠ ⊤ ∧ Subgroup.closure {w, φ w, φ (φ w)} = ⊤ :=
  ⟨φ, w, closure_two_ne_top _ le_rfl,
    closure_three_eq_top _ (by simp) (by simp)⟩

/-- **Kourovka Notebook Problem 17.32 has a negative answer** (Ionin–Semidetnov,
arXiv:2608.29219). It is *not* true that for every `n`, every `φ ∈ Aut(Fₙ)` and every
`w ∈ Fₙ`, `⟨w, φ(w), …, φⁿ(w)⟩ = Fₙ` implies `⟨w, φ(w), …, φⁿ⁻¹(w)⟩ = Fₙ`. -/
theorem kourovka_17_32 :
    ¬ ∀ (n : ℕ) (φ : FreeGroup (Fin n) ≃* FreeGroup (Fin n)) (w : FreeGroup (Fin n)),
      Subgroup.closure (Set.range fun i : Fin (n + 1) => (⇑φ)^[i] w) = ⊤ →
      Subgroup.closure (Set.range fun i : Fin n => (⇑φ)^[i] w) = ⊤ := by
  intro h
  refine closure_two_ne_top (Set.range fun i : Fin 2 => (⇑φ)^[i] w) ?_
    (h 2 φ w (closure_three_eq_top _ ⟨0, rfl⟩ ⟨2, rfl⟩))
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

end Kourovka17_32

#print axioms Kourovka17_32.kourovka_17_32
#print axioms Kourovka17_32.exists_counterexample

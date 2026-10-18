module

public import Mathlib

/-!
# Challenge: Horton's theorem (Erdős Problem 216, the case `k ≥ 7`)

This is the statement file of the Palomar / Comparator entry. It imports only Mathlib and
contains the definitions needed to state the results, followed by the compared theorems with
`sorry` proofs. The proofs are in `Solution.lean`, which repeats the definitions below verbatim
(Comparator checks that every constant used by a compared statement is identical in the two
environments).

**Problem.** Erdős Problem 216 (<https://www.erdosproblems.com/216>) asks for `g(k)`, the least
`n` such that every set of `n` points in the plane in general position (no three collinear)
contains an *empty convex `k`-gon*: `k` of the points in convex position whose convex hull
contains no other point of the set. It is known that `g(3) = 3`, `g(4) = 5`, `g(5) = 10`
(Harborth 1978), and that `g(6)` exists (Gerken 2008, Nicolás 2007).

**Result (Horton 1983).** `g(k)` does not exist for `k ≥ 7`: for every `N` there is a set of
`N` points in general position in the plane containing no empty convex `k`-gon for any `k ≥ 7`.
J. D. Horton, *Sets with no empty convex 7-gons*, Canad. Math. Bull. 26 (1983), 482–484.

## Statements

* `Horton.horton_euclidean`: for every `N` there is an `N`-point set in the Euclidean plane
  `EuclideanSpace ℝ (Fin 2)` in general position with no empty convex `k`-gon for any `k ≥ 7`.
* `Horton.erdos_216_ge_seven`: for every `k ≥ 7` there is no `n` such that every `n`-point set in
  general position in `ℝ × ℝ` contains an empty convex `k`-gon (`g(k)` does not exist).
* `Horton.cardSet'_eq_empty`, `Horton.erdos_216'`: the same facts stated with the definitions of
  `google-deepmind/formal-conjectures` pull request #6775 (`FormalConjectures/ErdosProblems/216.lean`),
  copied verbatim (primed, because this project depends only on Mathlib).

## Conventions

* *General position* means that no three distinct points are collinear (Mathlib's `Collinear`).
* *Convex position* means that no point of the set lies in the convex hull of the others.
* *Empty* means that no other point of the ambient set lies in the **interior** of the convex hull
  of the polygon's vertices. This is the weakest emptiness condition (a point on the boundary of
  the hull does not spoil emptiness), so the *absence* of empty convex `k`-gons proved here is the
  strongest form; for sets in general position it is equivalent to the closed-hull version.
-/

@[expose] public section

namespace Horton

section Geometry

open Set

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

/-- **Erdős Problem 216, the case `k ≥ 7`.** The number `g(k)` does not exist for `k ≥ 7`:
there is no `n` such that every set of `n` points in general position contains an empty convex
`k`-gon. -/
theorem erdos_216_ge_seven (k : ℕ) (hk : 7 ≤ k) :
    ¬ ∃ n : ℕ, ∀ S : Finset (ℝ × ℝ), S.card = n → InGeneralPosition S →
      HasEmptyConvexKGon k S := by
  sorry

/-- **Horton's theorem** in the Euclidean plane `EuclideanSpace ℝ (Fin 2)` (the model of `ℝ²`
used by `EmptyHexagonLean` and `formal-conjectures`). -/
theorem horton_euclidean (N : ℕ) : ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = N ∧
    InGeneralPosition S ∧ ∀ k, 7 ≤ k → ¬ HasEmptyConvexKGon k S := by
  sorry

end Geometry

/-! ### The `formal-conjectures` statement of Erdős Problem 216

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

/-- **Horton's theorem**, formal-conjectures form (`Erdos216.erdos_216.variants.horton` in
PR #6775): for `n ≥ 7` no `N` works, i.e. `g(n)` does not exist. -/
theorem cardSet'_eq_empty : ∀ n ≥ 7, cardSet' n = ∅ := by
  sorry

/-- Erdős Problem 216, formal-conjectures form (`Erdos216.erdos_216` in PR #6775, with
`answer(False)`): it is not the case that `g(k)` exists for every `k ≥ 3`. -/
theorem erdos_216' : (∀ k ≥ 3, (cardSet' k).Nonempty) ↔ False := by
  sorry

end FormalConjectures216

end Horton

module

public import Mathlib

/-!
# Erdős Problem 609: `f(3) = 5`

Let `f(n)` be the least `m` such that every `n`-colouring of the edges of `K_{2^n+1}` contains a
monochromatic odd cycle of length at most `m` (Erdős–Graham 1975; Erdős Problem 609,
<https://www.erdosproblems.com/609>).  This file proves the small case `f(3) = 5`:

* (upper bound) every 3-colouring of `E(K_9)` has a monochromatic `C_3` or `C_5`;
* (lower bound) some 3-colouring of `E(K_9)` has no monochromatic `C_3`.

The claim `f(3) = 5` was posted by Jeremy Cai via a "Botnet" agent on 2026-09-25
(write-up: <https://botnet.com/artifacts/32a10c8d-fd77-46db-9059-96f3d71ac10b>; the argument
there was found by the agent grind-09 and cross-checked with a SAT solver).  It settles only
`n = 3` and does not affect the asymptotic question.

## Proof strategy (kernel-checked: no `native_decide`, no `bv_decide`)

1. *Lemma A* (`five`): in a colouring without monochromatic `C_3`, `C_5`, any five vertices
   span an edge of every colour (a `decide` over the `2^10` two-colourings of `K_5`).
2. *Degree lemma* (`noFourStar`): hence no vertex has four neighbours in one colour.
   If `v` had colour-`k` neighbours `a₁, …, a₄`, then by Lemma A every other vertex `x` sends a
   colour-`k` edge to some `aᵢ` and none to `v`; two such vertices cannot be joined in colour
   `k` (that would close a `C_3` or a `C_5` through `v`), so the four remaining vertices
   together with `v` span no colour-`k` edge, contradicting Lemma A.
3. *Symmetry breaking* (`wlog_sorted`): relabel the vertices so that the colours of the edges
   `0x` are sorted for `x = 1, …, 8`, and then the vertices `2, …, 8` are sorted by the pair
   of colours of `0x`, `1x`.
4. *Certificate* (`cert`, `check`, `check_sound`, `cert_ok`): an externally generated
   case-split tree with 46641 branching nodes, checked by the kernel (`decide +kernel`), shows
   that no sorted colouring avoids monochromatic triangles, pentagons and four-stars.  At each
   node all 287 forbidden configurations through the branching edge are tested at once by
   arithmetic on numbers with 287 packed 64-bit slots (`bad`, `bad_sound`).

The lower bound is an explicit colouring (`lowerCol`) checked by `decide`.

## Main results

* `Erdos609F3.mono_tri_or_pent` — the upper bound on `Fin 9`.
* `Erdos609F3.exists_no_monoTri` — the lower bound on `Fin 9`.
* `Erdos609.f_three : Erdos609.f 3 = 5` — with `f` defined as in formal-conjectures
  (`FormalConjectures/ErdosProblems/609.lean`).
-/

@[expose] public section


namespace Erdos609F3

macro "nd" : tactic => `(tactic| (simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]; refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> first | assumption | (apply Ne.symm; assumption)))

/-- An edge colouring of `K_9` with three colours. -/
abbrev Colouring := Sym2 (Fin 9) → Fin 3

/-- A monochromatic triangle. -/
def MonoTri (c : Colouring) : Prop :=
  ∃ a b d : Fin 9, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c s(a, b) = c s(b, d) ∧ c s(b, d) = c s(a, d)

/-- A monochromatic pentagon `a b d e f a`. -/
def MonoPent (c : Colouring) : Prop :=
  ∃ a b d e f : Fin 9, [a, b, d, e, f].Nodup ∧
    c s(a, b) = c s(b, d) ∧ c s(b, d) = c s(d, e) ∧ c s(d, e) = c s(e, f) ∧ c s(e, f) = c s(f, a)

/-- No vertex has four distinct neighbours joined to it in the same colour. -/
def NoFourStar (c : Colouring) : Prop :=
  ∀ v a b d e : Fin 9, [v, a, b, d, e].Nodup →
    ¬ (c s(v, a) = c s(v, b) ∧ c s(v, b) = c s(v, d) ∧ c s(v, d) = c s(v, e))

/-! ### Two-colourings of `K_5` -/

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
/-- Every 2-colouring of `K_5` has a monochromatic triangle or pentagon (finite check). -/
theorem k5_bool : ∀ x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : Bool,
    (x01 = x12 ∧ x12 = x02) ∨ (x01 = x13 ∧ x13 = x03) ∨ (x01 = x14 ∧ x14 = x04) ∨
    (x02 = x23 ∧ x23 = x03) ∨ (x02 = x24 ∧ x24 = x04) ∨ (x03 = x34 ∧ x34 = x04) ∨
    (x12 = x23 ∧ x23 = x13) ∨ (x12 = x24 ∧ x24 = x14) ∨ (x13 = x34 ∧ x34 = x14) ∨
    (x23 = x34 ∧ x34 = x24) ∨
    -- the 12 pentagons on {0,1,2,3,4}, written as 0 a b d e 0
    (x01 = x12 ∧ x12 = x23 ∧ x23 = x34 ∧ x34 = x04) ∨
    (x01 = x12 ∧ x12 = x24 ∧ x24 = x34 ∧ x34 = x03) ∨
    (x01 = x13 ∧ x13 = x23 ∧ x23 = x24 ∧ x24 = x04) ∨
    (x01 = x13 ∧ x13 = x34 ∧ x34 = x24 ∧ x24 = x02) ∨
    (x01 = x14 ∧ x14 = x24 ∧ x24 = x23 ∧ x23 = x03) ∨
    (x01 = x14 ∧ x14 = x34 ∧ x34 = x23 ∧ x23 = x02) ∨
    (x02 = x12 ∧ x12 = x13 ∧ x13 = x34 ∧ x34 = x04) ∨
    (x02 = x12 ∧ x12 = x14 ∧ x14 = x34 ∧ x34 = x03) ∨
    (x02 = x23 ∧ x23 = x13 ∧ x13 = x14 ∧ x14 = x04) ∨
    (x02 = x24 ∧ x24 = x14 ∧ x14 = x13 ∧ x13 = x03) ∨
    (x03 = x13 ∧ x13 = x12 ∧ x12 = x24 ∧ x24 = x04) ∨
    (x03 = x23 ∧ x23 = x12 ∧ x12 = x14 ∧ x14 = x04) := by
  decide

/-- If two colours avoid `k`, then they are equal as soon as they agree on being `k + 1`. -/
theorem fin3_aux : ∀ k u w : Fin 3, u ≠ k → w ≠ k → decide (u = k + 1) = decide (w = k + 1) →
    u = w := by
  decide

/-- **Lemma A.** In a colouring without monochromatic triangles and pentagons, any five
distinct vertices span an edge of every colour. -/
theorem five (c : Colouring) (h3 : ¬ MonoTri c) (h5 : ¬ MonoPent c) (k : Fin 3)
    (p0 p1 p2 p3 p4 : Fin 9) (hnd : [p0, p1, p2, p3, p4].Nodup) :
    c s(p0, p1) = k ∨ c s(p0, p2) = k ∨ c s(p0, p3) = k ∨ c s(p0, p4) = k ∨
    c s(p1, p2) = k ∨ c s(p1, p3) = k ∨ c s(p1, p4) = k ∨ c s(p2, p3) = k ∨
    c s(p2, p4) = k ∨ c s(p3, p4) = k := by
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨n01, n02, n03, n04, n12, n13, n14, n23, n24, n34⟩ := hne
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨d01, d02, d03, d04⟩, ⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hnd
  have E : ∀ {u w : Fin 9} {u' w' : Fin 9}, c s(u, w) ≠ k → c s(u', w') ≠ k →
      decide (c s(u, w) = k + 1) = decide (c s(u', w') = k + 1) → c s(u, w) = c s(u', w') :=
    fun h h' he => fin3_aux k _ _ h h' he
  have tri : ∀ {a b d : Fin 9}, a ≠ b → a ≠ d → b ≠ d → c s(a, b) = c s(b, d) →
      c s(b, d) = c s(a, d) → False := fun h1 h2 h3' e1 e2 => h3 ⟨_, _, _, h1, h2, h3', e1, e2⟩
  have pent : ∀ {a b d e f : Fin 9}, [a, b, d, e, f].Nodup → c s(a, b) = c s(b, d) →
      c s(b, d) = c s(d, e) → c s(d, e) = c s(e, f) → c s(e, f) = c s(f, a) → False :=
    fun hn e1 e2 e3 e4 => h5 ⟨_, _, _, _, _, hn, e1, e2, e3, e4⟩
  have sw : ∀ u w : Fin 9, c s(u, w) = c s(w, u) := fun u w => by rw [Sym2.eq_swap]
  rcases k5_bool (decide (c s(p0, p1) = k + 1)) (decide (c s(p0, p2) = k + 1))
      (decide (c s(p0, p3) = k + 1)) (decide (c s(p0, p4) = k + 1))
      (decide (c s(p1, p2) = k + 1)) (decide (c s(p1, p3) = k + 1))
      (decide (c s(p1, p4) = k + 1)) (decide (c s(p2, p3) = k + 1))
      (decide (c s(p2, p4) = k + 1)) (decide (c s(p3, p4) = k + 1)) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact tri (a := p0) (b := p1) (d := p2) d01 d02 d12 (E n01 n12 h.1) (E n12 n02 h.2)
  · exact tri (a := p0) (b := p1) (d := p3) d01 d03 d13 (E n01 n13 h.1) (E n13 n03 h.2)
  · exact tri (a := p0) (b := p1) (d := p4) d01 d04 d14 (E n01 n14 h.1) (E n14 n04 h.2)
  · exact tri (a := p0) (b := p2) (d := p3) d02 d03 d23 (E n02 n23 h.1) (E n23 n03 h.2)
  · exact tri (a := p0) (b := p2) (d := p4) d02 d04 d24 (E n02 n24 h.1) (E n24 n04 h.2)
  · exact tri (a := p0) (b := p3) (d := p4) d03 d04 d34 (E n03 n34 h.1) (E n34 n04 h.2)
  · exact tri (a := p1) (b := p2) (d := p3) d12 d13 d23 (E n12 n23 h.1) (E n23 n13 h.2)
  · exact tri (a := p1) (b := p2) (d := p4) d12 d14 d24 (E n12 n24 h.1) (E n24 n14 h.2)
  · exact tri (a := p1) (b := p3) (d := p4) d13 d14 d34 (E n13 n34 h.1) (E n34 n14 h.2)
  · exact tri (a := p2) (b := p3) (d := p4) d23 d24 d34 (E n23 n34 h.1) (E n34 n24 h.2)
  · exact pent (a := p0) (b := p1) (d := p2) (e := p3) (f := p4) (by nd) (E n01 n12 h.1) (E n12 n23 h.2.1) (E n23 n34 h.2.2.1) ((E n34 n04 h.2.2.2).trans (sw p0 p4))
  · exact pent (a := p0) (b := p1) (d := p2) (e := p4) (f := p3) (by nd) (E n01 n12 h.1) (E n12 n24 h.2.1) ((E n24 n34 h.2.2.1).trans (sw p3 p4)) ((sw p4 p3).trans ((E n34 n03 h.2.2.2).trans (sw p0 p3)))
  · exact pent (a := p0) (b := p1) (d := p3) (e := p2) (f := p4) (by nd) (E n01 n13 h.1) ((E n13 n23 h.2.1).trans (sw p2 p3)) ((sw p3 p2).trans (E n23 n24 h.2.2.1)) ((E n24 n04 h.2.2.2).trans (sw p0 p4))
  · exact pent (a := p0) (b := p1) (d := p3) (e := p4) (f := p2) (by nd) (E n01 n13 h.1) (E n13 n34 h.2.1) ((E n34 n24 h.2.2.1).trans (sw p2 p4)) ((sw p4 p2).trans ((E n24 n02 h.2.2.2).trans (sw p0 p2)))
  · exact pent (a := p0) (b := p1) (d := p4) (e := p2) (f := p3) (by nd) (E n01 n14 h.1) ((E n14 n24 h.2.1).trans (sw p2 p4)) ((sw p4 p2).trans (E n24 n23 h.2.2.1)) ((E n23 n03 h.2.2.2).trans (sw p0 p3))
  · exact pent (a := p0) (b := p1) (d := p4) (e := p3) (f := p2) (by nd) (E n01 n14 h.1) ((E n14 n34 h.2.1).trans (sw p3 p4)) ((sw p4 p3).trans ((E n34 n23 h.2.2.1).trans (sw p2 p3))) ((sw p3 p2).trans ((E n23 n02 h.2.2.2).trans (sw p0 p2)))
  · exact pent (a := p0) (b := p2) (d := p1) (e := p3) (f := p4) (by nd) ((E n02 n12 h.1).trans (sw p1 p2)) ((sw p2 p1).trans (E n12 n13 h.2.1)) (E n13 n34 h.2.2.1) ((E n34 n04 h.2.2.2).trans (sw p0 p4))
  · exact pent (a := p0) (b := p2) (d := p1) (e := p4) (f := p3) (by nd) ((E n02 n12 h.1).trans (sw p1 p2)) ((sw p2 p1).trans (E n12 n14 h.2.1)) ((E n14 n34 h.2.2.1).trans (sw p3 p4)) ((sw p4 p3).trans ((E n34 n03 h.2.2.2).trans (sw p0 p3)))
  · exact pent (a := p0) (b := p2) (d := p3) (e := p1) (f := p4) (by nd) (E n02 n23 h.1) ((E n23 n13 h.2.1).trans (sw p1 p3)) ((sw p3 p1).trans (E n13 n14 h.2.2.1)) ((E n14 n04 h.2.2.2).trans (sw p0 p4))
  · exact pent (a := p0) (b := p2) (d := p4) (e := p1) (f := p3) (by nd) (E n02 n24 h.1) ((E n24 n14 h.2.1).trans (sw p1 p4)) ((sw p4 p1).trans (E n14 n13 h.2.2.1)) ((E n13 n03 h.2.2.2).trans (sw p0 p3))
  · exact pent (a := p0) (b := p3) (d := p1) (e := p2) (f := p4) (by nd) ((E n03 n13 h.1).trans (sw p1 p3)) ((sw p3 p1).trans (E n13 n12 h.2.1)) (E n12 n24 h.2.2.1) ((E n24 n04 h.2.2.2).trans (sw p0 p4))
  · exact pent (a := p0) (b := p3) (d := p2) (e := p1) (f := p4) (by nd) ((E n03 n23 h.1).trans (sw p2 p3)) ((sw p3 p2).trans ((E n23 n12 h.2.1).trans (sw p1 p2))) ((sw p2 p1).trans (E n12 n14 h.2.2.1)) ((E n14 n04 h.2.2.2).trans (sw p0 p4))


/-! ### Every colour has degree at most three at every vertex -/

theorem tri_of {c : Colouring} (h3 : ¬ MonoTri c) {a b d : Fin 9} (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) (k : Fin 3) (h1 : c s(a, b) = k) (h2 : c s(b, d) = k) (h3' : c s(a, d) = k) :
    False :=
  h3 ⟨a, b, d, hab, had, hbd, h1.trans h2.symm, h2.trans h3'.symm⟩

theorem sym (c : Colouring) (u w : Fin 9) : c s(u, w) = c s(w, u) := by rw [Sym2.eq_swap]

/-- **Degree lemma.** In a colouring of `K_9` without monochromatic triangles and pentagons,
no vertex has four neighbours joined to it in one colour. -/
theorem noFourStar (c : Colouring) (h3 : ¬ MonoTri c) (h5 : ¬ MonoPent c) : NoFourStar c := by
  intro v a1 a2 a3 a4 hnd ⟨e1, e2, e3⟩
  set k := c s(v, a1) with hk
  have k1 : c s(v, a1) = k := rfl
  have k2 : c s(v, a2) = k := e1.symm
  have k3 : c s(v, a3) = k := (e1.trans e2).symm
  have k4 : c s(v, a4) = k := (e1.trans (e2.trans e3)).symm
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd'
  obtain ⟨⟨dv1, dv2, dv3, dv4⟩, ⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hnd'
  -- two colour-`k` neighbours of `v` are not joined in colour `k`
  have nn : ∀ x y : Fin 9, x ≠ y → v ≠ x → v ≠ y → c s(v, x) = k → c s(v, y) = k →
      c s(x, y) ≠ k := fun x y hxy hvx hvy hx hy hxy' => tri_of h3 hvx hvy hxy k hx hxy' hy
  -- the vertices outside `{v, a1, a2, a3, a4}`
  let S : Finset (Fin 9) := Finset.univ \ [v, a1, a2, a3, a4].toFinset
  have hS : ∀ x, x ∈ S ↔ x ≠ v ∧ x ≠ a1 ∧ x ≠ a2 ∧ x ≠ a3 ∧ x ≠ a4 := by
    intro x; simp [S]
  -- (A) no vertex outside is joined to `v` in colour `k`
  have hA : ∀ x ∈ S, c s(v, x) ≠ k := by
    intro x hx hvx
    obtain ⟨xv, x1, x2, x3, x4⟩ := (hS x).1 hx
    rcases five c h3 h5 k a1 a2 a3 a4 x (by nd) with h | h | h | h | h | h | h | h | h | h
    · exact nn _ _ d12 dv1 dv2 k1 k2 h
    · exact nn _ _ d13 dv1 dv3 k1 k3 h
    · exact nn _ _ d14 dv1 dv4 k1 k4 h
    · exact nn _ _ (Ne.symm x1) dv1 (Ne.symm xv) k1 hvx h
    · exact nn _ _ d23 dv2 dv3 k2 k3 h
    · exact nn _ _ d24 dv2 dv4 k2 k4 h
    · exact nn _ _ (Ne.symm x2) dv2 (Ne.symm xv) k2 hvx h
    · exact nn _ _ d34 dv3 dv4 k3 k4 h
    · exact nn _ _ (Ne.symm x3) dv3 (Ne.symm xv) k3 hvx h
    · exact nn _ _ (Ne.symm x4) dv4 (Ne.symm xv) k4 hvx h
  -- (B) every vertex outside is joined to some `ai` in colour `k`
  have hB : ∀ x ∈ S, ∃ a, (a = a1 ∨ a = a2 ∨ a = a3 ∨ a = a4) ∧ c s(a, x) = k := by
    intro x hx
    obtain ⟨xv, x1, x2, x3, x4⟩ := (hS x).1 hx
    rcases five c h3 h5 k a1 a2 a3 a4 x (by nd) with h | h | h | h | h | h | h | h | h | h
    · exact absurd h (nn _ _ d12 dv1 dv2 k1 k2)
    · exact absurd h (nn _ _ d13 dv1 dv3 k1 k3)
    · exact absurd h (nn _ _ d14 dv1 dv4 k1 k4)
    · exact ⟨a1, by simp, h⟩
    · exact absurd h (nn _ _ d23 dv2 dv3 k2 k3)
    · exact absurd h (nn _ _ d24 dv2 dv4 k2 k4)
    · exact ⟨a2, by simp, h⟩
    · exact absurd h (nn _ _ d34 dv3 dv4 k3 k4)
    · exact ⟨a3, by simp, h⟩
    · exact ⟨a4, by simp, h⟩
  -- (C) two vertices outside are not joined in colour `k`
  have hC : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x, y) ≠ k := by
    intro x hx y hy hxy hk'
    obtain ⟨a, ha, hax⟩ := hB x hx
    obtain ⟨b, hb, hby⟩ := hB y hy
    obtain ⟨xv, x1, x2, x3, x4⟩ := (hS x).1 hx
    obtain ⟨yv, y1, y2, y3, y4⟩ := (hS y).1 hy
    have hva : c s(v, a) = k := by rcases ha with rfl | rfl | rfl | rfl <;> assumption
    have hvb : c s(v, b) = k := by rcases hb with rfl | rfl | rfl | rfl <;> assumption
    have hav : a ≠ v := by rcases ha with rfl | rfl | rfl | rfl <;> exact Ne.symm ‹_›
    have hbv : b ≠ v := by rcases hb with rfl | rfl | rfl | rfl <;> exact Ne.symm ‹_›
    have hax' : a ≠ x := by rcases ha with rfl | rfl | rfl | rfl <;> exact Ne.symm ‹_›
    have hay : a ≠ y := by rcases ha with rfl | rfl | rfl | rfl <;> exact Ne.symm ‹_›
    have hbx : b ≠ x := by rcases hb with rfl | rfl | rfl | rfl <;> exact Ne.symm ‹_›
    have hby' : b ≠ y := by rcases hb with rfl | rfl | rfl | rfl <;> exact Ne.symm ‹_›
    by_cases hab : a = b
    · subst hab
      exact tri_of h3 hax' hay hxy k hax hk' hby
    · -- the pentagon `v a x y b`
      refine h5 ⟨v, a, x, y, b, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true, not_false_eq_true]
        exact ⟨⟨Ne.symm hav, Ne.symm xv, Ne.symm yv, Ne.symm hbv⟩, ⟨hax', hay, hab⟩,
          ⟨hxy, Ne.symm hbx⟩, Ne.symm hby'⟩
      · rw [hva, hax]
      · rw [hax, hk']
      · rw [hk', sym c y b, hby]
      · rw [sym c y b, hby, sym c b v, hvb]
  -- `S` has four elements; together with `v` they contradict Lemma A
  have hcard : S.card = 4 := by
    simp only [S, Finset.card_univ_sdiff, Fintype.card_fin, List.toFinset_card_of_nodup hnd,
      List.length_cons, List.length_nil]
  obtain ⟨x1, T, hx1T, hST, hT⟩ := Finset.card_eq_succ.1 hcard
  obtain ⟨x2, x3, x4, h23, h24, h34, rfl⟩ := Finset.card_eq_three.1 hT
  have m1 : x1 ∈ S := by rw [← hST]; simp
  have m2 : x2 ∈ S := by rw [← hST]; simp
  have m3 : x3 ∈ S := by rw [← hST]; simp
  have m4 : x4 ∈ S := by rw [← hST]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx1T
  obtain ⟨h12, h13, h14⟩ := hx1T
  have v1 := ((hS x1).1 m1).1
  have v2 := ((hS x2).1 m2).1
  have v3 := ((hS x3).1 m3).1
  have v4 := ((hS x4).1 m4).1
  rcases five c h3 h5 k v x1 x2 x3 x4 (by nd) with h | h | h | h | h | h | h | h | h | h
  · exact hA x1 m1 h
  · exact hA x2 m2 h
  · exact hA x3 m3 h
  · exact hA x4 m4 h
  · exact hC x1 m1 x2 m2 h12 h
  · exact hC x1 m1 x3 m3 h13 h
  · exact hC x1 m1 x4 m4 h14 h
  · exact hC x2 m2 x3 m3 h23 h
  · exact hC x2 m2 x4 m4 h24 h
  · exact hC x3 m3 x4 m4 h34 h

/-! ### Relabelling vertices -/

/-- Relabel the vertices of a colouring by a permutation. -/
def relabel (σ : Equiv.Perm (Fin 9)) (c : Colouring) : Colouring := fun e => c (Sym2.map σ e)

@[simp] theorem relabel_apply (σ : Equiv.Perm (Fin 9)) (c : Colouring) (a b : Fin 9) :
    relabel σ c s(a, b) = c s(σ a, σ b) := by
  simp [relabel]

theorem relabel_tri {σ : Equiv.Perm (Fin 9)} {c : Colouring} (h : ¬ MonoTri c) :
    ¬ MonoTri (relabel σ c) := by
  rintro ⟨a, b, d, hab, had, hbd, e1, e2⟩
  exact h ⟨σ a, σ b, σ d, σ.injective.ne hab, σ.injective.ne had, σ.injective.ne hbd,
    by simpa using e1, by simpa using e2⟩

theorem relabel_pent {σ : Equiv.Perm (Fin 9)} {c : Colouring} (h : ¬ MonoPent c) :
    ¬ MonoPent (relabel σ c) := by
  rintro ⟨a, b, d, e, f, hnd, e1, e2, e3, e4⟩
  refine h ⟨σ a, σ b, σ d, σ e, σ f, ?_, by simpa using e1, by simpa using e2,
    by simpa using e3, by simpa using e4⟩
  simpa using hnd.map σ.injective

/-! ### Sorting -/

/-- Sort the vertices `1, …, 8` by a key, fixing `0`. -/
theorem sort1 (g : Fin 9 → ℕ) : ∃ σ : Equiv.Perm (Fin 9), σ 0 = 0 ∧
    ∀ x y : Fin 9, x ≠ 0 → x ≤ y → g (σ x) ≤ g (σ y) := by
  let key : Fin 9 → ℕ := fun x => if x = 0 then 0 else g x + 1
  let σ := Tuple.sort key
  have hm : Monotone (key ∘ σ) := Tuple.monotone_sort key
  have h0 : σ 0 = 0 := by
    have h1 : key (σ (σ.symm 0)) = 0 := by simp [key]
    have h2 : key (σ 0) ≤ key (σ (σ.symm 0)) := hm (Fin.zero_le _)
    have h3 : key (σ 0) = 0 := by omega
    by_contra hne
    simp [key, hne] at h3
  refine ⟨σ, h0, fun x y hx hxy => ?_⟩
  have hy : y ≠ 0 := by rintro rfl; exact hx (le_antisymm hxy (Fin.zero_le _))
  have hσx : σ x ≠ 0 := by rw [← h0]; exact σ.injective.ne hx
  have hσy : σ y ≠ 0 := by rw [← h0]; exact σ.injective.ne hy
  have := hm hxy
  simp only [Function.comp, key, hσx, hσy, ↓reduceIte] at this
  omega

/-- Sort the vertices `2, …, 8` by a key, fixing `0` and `1`. -/
theorem sort2 (g : Fin 9 → ℕ) : ∃ σ : Equiv.Perm (Fin 9), σ 0 = 0 ∧ σ 1 = 1 ∧
    ∀ x y : Fin 9, 2 ≤ x → x ≤ y → g (σ x) ≤ g (σ y) := by
  let key : Fin 9 → ℕ := fun x => if x = 0 then 0 else if x = 1 then 1 else g x + 2
  let σ := Tuple.sort key
  have hm : Monotone (key ∘ σ) := Tuple.monotone_sort key
  have h0 : σ 0 = 0 := by
    have h1 : key (σ (σ.symm 0)) = 0 := by simp [key]
    have h2 : key (σ 0) ≤ key (σ (σ.symm 0)) := hm (Fin.zero_le _)
    have h3 : key (σ 0) = 0 := by omega
    by_contra hne
    by_cases h1' : σ 0 = 1 <;> simp [key, hne, h1'] at h3
  have h1 : σ 1 = 1 := by
    have hy : σ.symm 1 ≠ 0 := by
      intro h; have := congrArg σ h; simp [h0] at this
    have hle : (1 : Fin 9) ≤ σ.symm 1 := by
      rcases Fin.eq_zero_or_eq_succ (σ.symm 1) with h | ⟨j, hj⟩
      · exact absurd h hy
      · rw [hj]; exact Fin.succ_pos j
    have h2 : key (σ 1) ≤ key (σ (σ.symm 1)) := hm hle
    have h1' : key (σ (σ.symm 1)) = 1 := by simp [key]
    have hne0 : σ 1 ≠ 0 := by rw [← h0]; exact σ.injective.ne (by decide)
    rw [h1'] at h2
    by_contra hne
    simp only [key, hne0, hne, ↓reduceIte] at h2
    omega
  refine ⟨σ, h0, h1, fun x y hx hxy => ?_⟩
  have hx0 : x ≠ 0 := by rintro rfl; exact absurd hx (by decide)
  have hx1 : x ≠ 1 := by rintro rfl; exact absurd hx (by decide)
  have hy0 : y ≠ 0 := by rintro rfl; exact absurd (le_trans hx hxy) (by decide)
  have hy1 : y ≠ 1 := by rintro rfl; exact absurd (le_trans hx hxy) (by decide)
  have a0 : σ x ≠ 0 := by rw [← h0]; exact σ.injective.ne hx0
  have a1 : σ x ≠ 1 := by rw [← h1]; exact σ.injective.ne hx1
  have b0 : σ y ≠ 0 := by rw [← h0]; exact σ.injective.ne hy0
  have b1 : σ y ≠ 1 := by rw [← h1]; exact σ.injective.ne hy1
  have := hm hxy
  simp only [Function.comp, key, a0, a1, b0, b1, ↓reduceIte] at this
  omega


/-! ### Edge masks and the forbidden configurations -/


/-- Index of the edge `{a, b}` of `K_9` in `0, …, 35` (for `a ≠ b`). -/
def eix (a b : Fin 9) : Nat :=
  if a.val < b.val then b.val * (b.val - 1) / 2 + a.val else a.val * (a.val - 1) / 2 + b.val

/-- The three kinds of forbidden configurations: a triangle `a b c`, a pentagon
`a b c d e`, and a four-star with centre `v` and leaves `a b c d`. -/
inductive Shape where
  | tri (a b c : Fin 9)
  | pent (a b c d e : Fin 9)
  | star (v a b c d : Fin 9)

/-- The edge mask (bit `eix x y` for each edge `xy`) of a configuration. -/
def Shape.mask : Shape → Nat
  | .tri a b c => 2 ^ eix a b ||| 2 ^ eix b c ||| 2 ^ eix a c
  | .pent a b c d e => 2 ^ eix a b ||| 2 ^ eix b c ||| 2 ^ eix c d ||| 2 ^ eix d e ||| 2 ^ eix e a
  | .star v a b c d => 2 ^ eix v a ||| 2 ^ eix v b ||| 2 ^ eix v c ||| 2 ^ eix v d

/-- The vertices of a configuration are distinct. -/
def Shape.valid : Shape → Bool
  | .tri a b c => decide [a, b, c].Nodup
  | .pent a b c d e => decide [a, b, c, d, e].Nodup
  | .star v a b c d => decide [v, a, b, c, d].Nodup

set_option maxRecDepth 100000

/-- For each edge index `e < 36`, the 287 forbidden configurations through `e`
(7 triangles, 210 pentagons, 70 four-stars). -/
def forbS : List (List Shape) := [
  [.tri 0 1 2, .tri 0 1 3, .tri 0 1 4, .tri 0 1 5, .tri 0 1 6, .tri 0 1 7, .tri 0 1 8, .pent 0 1 2
    3 4, .pent 0 1 2 4 3, .pent 0 1 3 2 4, .pent 0 1 3 4 2, .pent 0 1 4 2 3, .pent 0 1 4 3 2,
    .pent 0 1 2 3 5, .pent 0 1 2 5 3, .pent 0 1 3 2 5, .pent 0 1 3 5 2, .pent 0 1 5 2 3, .pent 0 1
    5 3 2, .pent 0 1 2 3 6, .pent 0 1 2 6 3, .pent 0 1 3 2 6, .pent 0 1 3 6 2, .pent 0 1 6 2 3,
    .pent 0 1 6 3 2, .pent 0 1 2 3 7, .pent 0 1 2 7 3, .pent 0 1 3 2 7, .pent 0 1 3 7 2, .pent 0 1
    7 2 3, .pent 0 1 7 3 2, .pent 0 1 2 3 8, .pent 0 1 2 8 3, .pent 0 1 3 2 8, .pent 0 1 3 8 2,
    .pent 0 1 8 2 3, .pent 0 1 8 3 2, .pent 0 1 2 4 5, .pent 0 1 2 5 4, .pent 0 1 4 2 5, .pent 0 1
    4 5 2, .pent 0 1 5 2 4, .pent 0 1 5 4 2, .pent 0 1 2 4 6, .pent 0 1 2 6 4, .pent 0 1 4 2 6,
    .pent 0 1 4 6 2, .pent 0 1 6 2 4, .pent 0 1 6 4 2, .pent 0 1 2 4 7, .pent 0 1 2 7 4, .pent 0 1
    4 2 7, .pent 0 1 4 7 2, .pent 0 1 7 2 4, .pent 0 1 7 4 2, .pent 0 1 2 4 8, .pent 0 1 2 8 4,
    .pent 0 1 4 2 8, .pent 0 1 4 8 2, .pent 0 1 8 2 4, .pent 0 1 8 4 2, .pent 0 1 2 5 6, .pent 0 1
    2 6 5, .pent 0 1 5 2 6, .pent 0 1 5 6 2, .pent 0 1 6 2 5, .pent 0 1 6 5 2, .pent 0 1 2 5 7,
    .pent 0 1 2 7 5, .pent 0 1 5 2 7, .pent 0 1 5 7 2, .pent 0 1 7 2 5, .pent 0 1 7 5 2, .pent 0 1
    2 5 8, .pent 0 1 2 8 5, .pent 0 1 5 2 8, .pent 0 1 5 8 2, .pent 0 1 8 2 5, .pent 0 1 8 5 2,
    .pent 0 1 2 6 7, .pent 0 1 2 7 6, .pent 0 1 6 2 7, .pent 0 1 6 7 2, .pent 0 1 7 2 6, .pent 0 1
    7 6 2, .pent 0 1 2 6 8, .pent 0 1 2 8 6, .pent 0 1 6 2 8, .pent 0 1 6 8 2, .pent 0 1 8 2 6,
    .pent 0 1 8 6 2, .pent 0 1 2 7 8, .pent 0 1 2 8 7, .pent 0 1 7 2 8, .pent 0 1 7 8 2, .pent 0 1
    8 2 7, .pent 0 1 8 7 2, .pent 0 1 3 4 5, .pent 0 1 3 5 4, .pent 0 1 4 3 5, .pent 0 1 4 5 3,
    .pent 0 1 5 3 4, .pent 0 1 5 4 3, .pent 0 1 3 4 6, .pent 0 1 3 6 4, .pent 0 1 4 3 6, .pent 0 1
    4 6 3, .pent 0 1 6 3 4, .pent 0 1 6 4 3, .pent 0 1 3 4 7, .pent 0 1 3 7 4, .pent 0 1 4 3 7,
    .pent 0 1 4 7 3, .pent 0 1 7 3 4, .pent 0 1 7 4 3, .pent 0 1 3 4 8, .pent 0 1 3 8 4, .pent 0 1
    4 3 8, .pent 0 1 4 8 3, .pent 0 1 8 3 4, .pent 0 1 8 4 3, .pent 0 1 3 5 6, .pent 0 1 3 6 5,
    .pent 0 1 5 3 6, .pent 0 1 5 6 3, .pent 0 1 6 3 5, .pent 0 1 6 5 3, .pent 0 1 3 5 7, .pent 0 1
    3 7 5, .pent 0 1 5 3 7, .pent 0 1 5 7 3, .pent 0 1 7 3 5, .pent 0 1 7 5 3, .pent 0 1 3 5 8,
    .pent 0 1 3 8 5, .pent 0 1 5 3 8, .pent 0 1 5 8 3, .pent 0 1 8 3 5, .pent 0 1 8 5 3, .pent 0 1
    3 6 7, .pent 0 1 3 7 6, .pent 0 1 6 3 7, .pent 0 1 6 7 3, .pent 0 1 7 3 6, .pent 0 1 7 6 3,
    .pent 0 1 3 6 8, .pent 0 1 3 8 6, .pent 0 1 6 3 8, .pent 0 1 6 8 3, .pent 0 1 8 3 6, .pent 0 1
    8 6 3, .pent 0 1 3 7 8, .pent 0 1 3 8 7, .pent 0 1 7 3 8, .pent 0 1 7 8 3, .pent 0 1 8 3 7,
    .pent 0 1 8 7 3, .pent 0 1 4 5 6, .pent 0 1 4 6 5, .pent 0 1 5 4 6, .pent 0 1 5 6 4, .pent 0 1
    6 4 5, .pent 0 1 6 5 4, .pent 0 1 4 5 7, .pent 0 1 4 7 5, .pent 0 1 5 4 7, .pent 0 1 5 7 4,
    .pent 0 1 7 4 5, .pent 0 1 7 5 4, .pent 0 1 4 5 8, .pent 0 1 4 8 5, .pent 0 1 5 4 8, .pent 0 1
    5 8 4, .pent 0 1 8 4 5, .pent 0 1 8 5 4, .pent 0 1 4 6 7, .pent 0 1 4 7 6, .pent 0 1 6 4 7,
    .pent 0 1 6 7 4, .pent 0 1 7 4 6, .pent 0 1 7 6 4, .pent 0 1 4 6 8, .pent 0 1 4 8 6, .pent 0 1
    6 4 8, .pent 0 1 6 8 4, .pent 0 1 8 4 6, .pent 0 1 8 6 4, .pent 0 1 4 7 8, .pent 0 1 4 8 7,
    .pent 0 1 7 4 8, .pent 0 1 7 8 4, .pent 0 1 8 4 7, .pent 0 1 8 7 4, .pent 0 1 5 6 7, .pent 0 1
    5 7 6, .pent 0 1 6 5 7, .pent 0 1 6 7 5, .pent 0 1 7 5 6, .pent 0 1 7 6 5, .pent 0 1 5 6 8,
    .pent 0 1 5 8 6, .pent 0 1 6 5 8, .pent 0 1 6 8 5, .pent 0 1 8 5 6, .pent 0 1 8 6 5, .pent 0 1
    5 7 8, .pent 0 1 5 8 7, .pent 0 1 7 5 8, .pent 0 1 7 8 5, .pent 0 1 8 5 7, .pent 0 1 8 7 5,
    .pent 0 1 6 7 8, .pent 0 1 6 8 7, .pent 0 1 7 6 8, .pent 0 1 7 8 6, .pent 0 1 8 6 7, .pent 0 1
    8 7 6, .star 0 1 2 3 4, .star 0 1 2 3 5, .star 0 1 2 3 6, .star 0 1 2 3 7, .star 0 1 2 3 8,
    .star 0 1 2 4 5, .star 0 1 2 4 6, .star 0 1 2 4 7, .star 0 1 2 4 8, .star 0 1 2 5 6, .star 0 1
    2 5 7, .star 0 1 2 5 8, .star 0 1 2 6 7, .star 0 1 2 6 8, .star 0 1 2 7 8, .star 0 1 3 4 5,
    .star 0 1 3 4 6, .star 0 1 3 4 7, .star 0 1 3 4 8, .star 0 1 3 5 6, .star 0 1 3 5 7, .star 0 1
    3 5 8, .star 0 1 3 6 7, .star 0 1 3 6 8, .star 0 1 3 7 8, .star 0 1 4 5 6, .star 0 1 4 5 7,
    .star 0 1 4 5 8, .star 0 1 4 6 7, .star 0 1 4 6 8, .star 0 1 4 7 8, .star 0 1 5 6 7, .star 0 1
    5 6 8, .star 0 1 5 7 8, .star 0 1 6 7 8, .star 1 0 2 3 4, .star 1 0 2 3 5, .star 1 0 2 3 6,
    .star 1 0 2 3 7, .star 1 0 2 3 8, .star 1 0 2 4 5, .star 1 0 2 4 6, .star 1 0 2 4 7, .star 1 0
    2 4 8, .star 1 0 2 5 6, .star 1 0 2 5 7, .star 1 0 2 5 8, .star 1 0 2 6 7, .star 1 0 2 6 8,
    .star 1 0 2 7 8, .star 1 0 3 4 5, .star 1 0 3 4 6, .star 1 0 3 4 7, .star 1 0 3 4 8, .star 1 0
    3 5 6, .star 1 0 3 5 7, .star 1 0 3 5 8, .star 1 0 3 6 7, .star 1 0 3 6 8, .star 1 0 3 7 8,
    .star 1 0 4 5 6, .star 1 0 4 5 7, .star 1 0 4 5 8, .star 1 0 4 6 7, .star 1 0 4 6 8, .star 1 0
    4 7 8, .star 1 0 5 6 7, .star 1 0 5 6 8, .star 1 0 5 7 8, .star 1 0 6 7 8],
  [.tri 0 1 2, .tri 0 2 3, .tri 0 2 4, .tri 0 2 5, .tri 0 2 6, .tri 0 2 7, .tri 0 2 8, .pent 0 1 3
    4 2, .pent 0 1 4 3 2, .pent 0 2 1 3 4, .pent 0 2 1 4 3, .pent 0 2 3 1 4, .pent 0 2 4 1 3,
    .pent 0 1 3 5 2, .pent 0 1 5 3 2, .pent 0 2 1 3 5, .pent 0 2 1 5 3, .pent 0 2 3 1 5, .pent 0 2
    5 1 3, .pent 0 1 3 6 2, .pent 0 1 6 3 2, .pent 0 2 1 3 6, .pent 0 2 1 6 3, .pent 0 2 3 1 6,
    .pent 0 2 6 1 3, .pent 0 1 3 7 2, .pent 0 1 7 3 2, .pent 0 2 1 3 7, .pent 0 2 1 7 3, .pent 0 2
    3 1 7, .pent 0 2 7 1 3, .pent 0 1 3 8 2, .pent 0 1 8 3 2, .pent 0 2 1 3 8, .pent 0 2 1 8 3,
    .pent 0 2 3 1 8, .pent 0 2 8 1 3, .pent 0 1 4 5 2, .pent 0 1 5 4 2, .pent 0 2 1 4 5, .pent 0 2
    1 5 4, .pent 0 2 4 1 5, .pent 0 2 5 1 4, .pent 0 1 4 6 2, .pent 0 1 6 4 2, .pent 0 2 1 4 6,
    .pent 0 2 1 6 4, .pent 0 2 4 1 6, .pent 0 2 6 1 4, .pent 0 1 4 7 2, .pent 0 1 7 4 2, .pent 0 2
    1 4 7, .pent 0 2 1 7 4, .pent 0 2 4 1 7, .pent 0 2 7 1 4, .pent 0 1 4 8 2, .pent 0 1 8 4 2,
    .pent 0 2 1 4 8, .pent 0 2 1 8 4, .pent 0 2 4 1 8, .pent 0 2 8 1 4, .pent 0 1 5 6 2, .pent 0 1
    6 5 2, .pent 0 2 1 5 6, .pent 0 2 1 6 5, .pent 0 2 5 1 6, .pent 0 2 6 1 5, .pent 0 1 5 7 2,
    .pent 0 1 7 5 2, .pent 0 2 1 5 7, .pent 0 2 1 7 5, .pent 0 2 5 1 7, .pent 0 2 7 1 5, .pent 0 1
    5 8 2, .pent 0 1 8 5 2, .pent 0 2 1 5 8, .pent 0 2 1 8 5, .pent 0 2 5 1 8, .pent 0 2 8 1 5,
    .pent 0 1 6 7 2, .pent 0 1 7 6 2, .pent 0 2 1 6 7, .pent 0 2 1 7 6, .pent 0 2 6 1 7, .pent 0 2
    7 1 6, .pent 0 1 6 8 2, .pent 0 1 8 6 2, .pent 0 2 1 6 8, .pent 0 2 1 8 6, .pent 0 2 6 1 8,
    .pent 0 2 8 1 6, .pent 0 1 7 8 2, .pent 0 1 8 7 2, .pent 0 2 1 7 8, .pent 0 2 1 8 7, .pent 0 2
    7 1 8, .pent 0 2 8 1 7, .pent 0 2 3 4 5, .pent 0 2 3 5 4, .pent 0 2 4 3 5, .pent 0 2 4 5 3,
    .pent 0 2 5 3 4, .pent 0 2 5 4 3, .pent 0 2 3 4 6, .pent 0 2 3 6 4, .pent 0 2 4 3 6, .pent 0 2
    4 6 3, .pent 0 2 6 3 4, .pent 0 2 6 4 3, .pent 0 2 3 4 7, .pent 0 2 3 7 4, .pent 0 2 4 3 7,
    .pent 0 2 4 7 3, .pent 0 2 7 3 4, .pent 0 2 7 4 3, .pent 0 2 3 4 8, .pent 0 2 3 8 4, .pent 0 2
    4 3 8, .pent 0 2 4 8 3, .pent 0 2 8 3 4, .pent 0 2 8 4 3, .pent 0 2 3 5 6, .pent 0 2 3 6 5,
    .pent 0 2 5 3 6, .pent 0 2 5 6 3, .pent 0 2 6 3 5, .pent 0 2 6 5 3, .pent 0 2 3 5 7, .pent 0 2
    3 7 5, .pent 0 2 5 3 7, .pent 0 2 5 7 3, .pent 0 2 7 3 5, .pent 0 2 7 5 3, .pent 0 2 3 5 8,
    .pent 0 2 3 8 5, .pent 0 2 5 3 8, .pent 0 2 5 8 3, .pent 0 2 8 3 5, .pent 0 2 8 5 3, .pent 0 2
    3 6 7, .pent 0 2 3 7 6, .pent 0 2 6 3 7, .pent 0 2 6 7 3, .pent 0 2 7 3 6, .pent 0 2 7 6 3,
    .pent 0 2 3 6 8, .pent 0 2 3 8 6, .pent 0 2 6 3 8, .pent 0 2 6 8 3, .pent 0 2 8 3 6, .pent 0 2
    8 6 3, .pent 0 2 3 7 8, .pent 0 2 3 8 7, .pent 0 2 7 3 8, .pent 0 2 7 8 3, .pent 0 2 8 3 7,
    .pent 0 2 8 7 3, .pent 0 2 4 5 6, .pent 0 2 4 6 5, .pent 0 2 5 4 6, .pent 0 2 5 6 4, .pent 0 2
    6 4 5, .pent 0 2 6 5 4, .pent 0 2 4 5 7, .pent 0 2 4 7 5, .pent 0 2 5 4 7, .pent 0 2 5 7 4,
    .pent 0 2 7 4 5, .pent 0 2 7 5 4, .pent 0 2 4 5 8, .pent 0 2 4 8 5, .pent 0 2 5 4 8, .pent 0 2
    5 8 4, .pent 0 2 8 4 5, .pent 0 2 8 5 4, .pent 0 2 4 6 7, .pent 0 2 4 7 6, .pent 0 2 6 4 7,
    .pent 0 2 6 7 4, .pent 0 2 7 4 6, .pent 0 2 7 6 4, .pent 0 2 4 6 8, .pent 0 2 4 8 6, .pent 0 2
    6 4 8, .pent 0 2 6 8 4, .pent 0 2 8 4 6, .pent 0 2 8 6 4, .pent 0 2 4 7 8, .pent 0 2 4 8 7,
    .pent 0 2 7 4 8, .pent 0 2 7 8 4, .pent 0 2 8 4 7, .pent 0 2 8 7 4, .pent 0 2 5 6 7, .pent 0 2
    5 7 6, .pent 0 2 6 5 7, .pent 0 2 6 7 5, .pent 0 2 7 5 6, .pent 0 2 7 6 5, .pent 0 2 5 6 8,
    .pent 0 2 5 8 6, .pent 0 2 6 5 8, .pent 0 2 6 8 5, .pent 0 2 8 5 6, .pent 0 2 8 6 5, .pent 0 2
    5 7 8, .pent 0 2 5 8 7, .pent 0 2 7 5 8, .pent 0 2 7 8 5, .pent 0 2 8 5 7, .pent 0 2 8 7 5,
    .pent 0 2 6 7 8, .pent 0 2 6 8 7, .pent 0 2 7 6 8, .pent 0 2 7 8 6, .pent 0 2 8 6 7, .pent 0 2
    8 7 6, .star 0 1 2 3 4, .star 0 1 2 3 5, .star 0 1 2 3 6, .star 0 1 2 3 7, .star 0 1 2 3 8,
    .star 0 1 2 4 5, .star 0 1 2 4 6, .star 0 1 2 4 7, .star 0 1 2 4 8, .star 0 1 2 5 6, .star 0 1
    2 5 7, .star 0 1 2 5 8, .star 0 1 2 6 7, .star 0 1 2 6 8, .star 0 1 2 7 8, .star 0 2 3 4 5,
    .star 0 2 3 4 6, .star 0 2 3 4 7, .star 0 2 3 4 8, .star 0 2 3 5 6, .star 0 2 3 5 7, .star 0 2
    3 5 8, .star 0 2 3 6 7, .star 0 2 3 6 8, .star 0 2 3 7 8, .star 0 2 4 5 6, .star 0 2 4 5 7,
    .star 0 2 4 5 8, .star 0 2 4 6 7, .star 0 2 4 6 8, .star 0 2 4 7 8, .star 0 2 5 6 7, .star 0 2
    5 6 8, .star 0 2 5 7 8, .star 0 2 6 7 8, .star 2 0 1 3 4, .star 2 0 1 3 5, .star 2 0 1 3 6,
    .star 2 0 1 3 7, .star 2 0 1 3 8, .star 2 0 1 4 5, .star 2 0 1 4 6, .star 2 0 1 4 7, .star 2 0
    1 4 8, .star 2 0 1 5 6, .star 2 0 1 5 7, .star 2 0 1 5 8, .star 2 0 1 6 7, .star 2 0 1 6 8,
    .star 2 0 1 7 8, .star 2 0 3 4 5, .star 2 0 3 4 6, .star 2 0 3 4 7, .star 2 0 3 4 8, .star 2 0
    3 5 6, .star 2 0 3 5 7, .star 2 0 3 5 8, .star 2 0 3 6 7, .star 2 0 3 6 8, .star 2 0 3 7 8,
    .star 2 0 4 5 6, .star 2 0 4 5 7, .star 2 0 4 5 8, .star 2 0 4 6 7, .star 2 0 4 6 8, .star 2 0
    4 7 8, .star 2 0 5 6 7, .star 2 0 5 6 8, .star 2 0 5 7 8, .star 2 0 6 7 8],
  [.tri 0 1 2, .tri 1 2 3, .tri 1 2 4, .tri 1 2 5, .tri 1 2 6, .tri 1 2 7, .tri 1 2 8, .pent 0 1 2
    3 4, .pent 0 1 2 4 3, .pent 0 2 1 3 4, .pent 0 2 1 4 3, .pent 0 3 1 2 4, .pent 0 3 2 1 4,
    .pent 0 1 2 3 5, .pent 0 1 2 5 3, .pent 0 2 1 3 5, .pent 0 2 1 5 3, .pent 0 3 1 2 5, .pent 0 3
    2 1 5, .pent 0 1 2 3 6, .pent 0 1 2 6 3, .pent 0 2 1 3 6, .pent 0 2 1 6 3, .pent 0 3 1 2 6,
    .pent 0 3 2 1 6, .pent 0 1 2 3 7, .pent 0 1 2 7 3, .pent 0 2 1 3 7, .pent 0 2 1 7 3, .pent 0 3
    1 2 7, .pent 0 3 2 1 7, .pent 0 1 2 3 8, .pent 0 1 2 8 3, .pent 0 2 1 3 8, .pent 0 2 1 8 3,
    .pent 0 3 1 2 8, .pent 0 3 2 1 8, .pent 0 1 2 4 5, .pent 0 1 2 5 4, .pent 0 2 1 4 5, .pent 0 2
    1 5 4, .pent 0 4 1 2 5, .pent 0 4 2 1 5, .pent 0 1 2 4 6, .pent 0 1 2 6 4, .pent 0 2 1 4 6,
    .pent 0 2 1 6 4, .pent 0 4 1 2 6, .pent 0 4 2 1 6, .pent 0 1 2 4 7, .pent 0 1 2 7 4, .pent 0 2
    1 4 7, .pent 0 2 1 7 4, .pent 0 4 1 2 7, .pent 0 4 2 1 7, .pent 0 1 2 4 8, .pent 0 1 2 8 4,
    .pent 0 2 1 4 8, .pent 0 2 1 8 4, .pent 0 4 1 2 8, .pent 0 4 2 1 8, .pent 0 1 2 5 6, .pent 0 1
    2 6 5, .pent 0 2 1 5 6, .pent 0 2 1 6 5, .pent 0 5 1 2 6, .pent 0 5 2 1 6, .pent 0 1 2 5 7,
    .pent 0 1 2 7 5, .pent 0 2 1 5 7, .pent 0 2 1 7 5, .pent 0 5 1 2 7, .pent 0 5 2 1 7, .pent 0 1
    2 5 8, .pent 0 1 2 8 5, .pent 0 2 1 5 8, .pent 0 2 1 8 5, .pent 0 5 1 2 8, .pent 0 5 2 1 8,
    .pent 0 1 2 6 7, .pent 0 1 2 7 6, .pent 0 2 1 6 7, .pent 0 2 1 7 6, .pent 0 6 1 2 7, .pent 0 6
    2 1 7, .pent 0 1 2 6 8, .pent 0 1 2 8 6, .pent 0 2 1 6 8, .pent 0 2 1 8 6, .pent 0 6 1 2 8,
    .pent 0 6 2 1 8, .pent 0 1 2 7 8, .pent 0 1 2 8 7, .pent 0 2 1 7 8, .pent 0 2 1 8 7, .pent 0 7
    1 2 8, .pent 0 7 2 1 8, .pent 1 2 3 4 5, .pent 1 2 3 5 4, .pent 1 2 4 3 5, .pent 1 2 4 5 3,
    .pent 1 2 5 3 4, .pent 1 2 5 4 3, .pent 1 2 3 4 6, .pent 1 2 3 6 4, .pent 1 2 4 3 6, .pent 1 2
    4 6 3, .pent 1 2 6 3 4, .pent 1 2 6 4 3, .pent 1 2 3 4 7, .pent 1 2 3 7 4, .pent 1 2 4 3 7,
    .pent 1 2 4 7 3, .pent 1 2 7 3 4, .pent 1 2 7 4 3, .pent 1 2 3 4 8, .pent 1 2 3 8 4, .pent 1 2
    4 3 8, .pent 1 2 4 8 3, .pent 1 2 8 3 4, .pent 1 2 8 4 3, .pent 1 2 3 5 6, .pent 1 2 3 6 5,
    .pent 1 2 5 3 6, .pent 1 2 5 6 3, .pent 1 2 6 3 5, .pent 1 2 6 5 3, .pent 1 2 3 5 7, .pent 1 2
    3 7 5, .pent 1 2 5 3 7, .pent 1 2 5 7 3, .pent 1 2 7 3 5, .pent 1 2 7 5 3, .pent 1 2 3 5 8,
    .pent 1 2 3 8 5, .pent 1 2 5 3 8, .pent 1 2 5 8 3, .pent 1 2 8 3 5, .pent 1 2 8 5 3, .pent 1 2
    3 6 7, .pent 1 2 3 7 6, .pent 1 2 6 3 7, .pent 1 2 6 7 3, .pent 1 2 7 3 6, .pent 1 2 7 6 3,
    .pent 1 2 3 6 8, .pent 1 2 3 8 6, .pent 1 2 6 3 8, .pent 1 2 6 8 3, .pent 1 2 8 3 6, .pent 1 2
    8 6 3, .pent 1 2 3 7 8, .pent 1 2 3 8 7, .pent 1 2 7 3 8, .pent 1 2 7 8 3, .pent 1 2 8 3 7,
    .pent 1 2 8 7 3, .pent 1 2 4 5 6, .pent 1 2 4 6 5, .pent 1 2 5 4 6, .pent 1 2 5 6 4, .pent 1 2
    6 4 5, .pent 1 2 6 5 4, .pent 1 2 4 5 7, .pent 1 2 4 7 5, .pent 1 2 5 4 7, .pent 1 2 5 7 4,
    .pent 1 2 7 4 5, .pent 1 2 7 5 4, .pent 1 2 4 5 8, .pent 1 2 4 8 5, .pent 1 2 5 4 8, .pent 1 2
    5 8 4, .pent 1 2 8 4 5, .pent 1 2 8 5 4, .pent 1 2 4 6 7, .pent 1 2 4 7 6, .pent 1 2 6 4 7,
    .pent 1 2 6 7 4, .pent 1 2 7 4 6, .pent 1 2 7 6 4, .pent 1 2 4 6 8, .pent 1 2 4 8 6, .pent 1 2
    6 4 8, .pent 1 2 6 8 4, .pent 1 2 8 4 6, .pent 1 2 8 6 4, .pent 1 2 4 7 8, .pent 1 2 4 8 7,
    .pent 1 2 7 4 8, .pent 1 2 7 8 4, .pent 1 2 8 4 7, .pent 1 2 8 7 4, .pent 1 2 5 6 7, .pent 1 2
    5 7 6, .pent 1 2 6 5 7, .pent 1 2 6 7 5, .pent 1 2 7 5 6, .pent 1 2 7 6 5, .pent 1 2 5 6 8,
    .pent 1 2 5 8 6, .pent 1 2 6 5 8, .pent 1 2 6 8 5, .pent 1 2 8 5 6, .pent 1 2 8 6 5, .pent 1 2
    5 7 8, .pent 1 2 5 8 7, .pent 1 2 7 5 8, .pent 1 2 7 8 5, .pent 1 2 8 5 7, .pent 1 2 8 7 5,
    .pent 1 2 6 7 8, .pent 1 2 6 8 7, .pent 1 2 7 6 8, .pent 1 2 7 8 6, .pent 1 2 8 6 7, .pent 1 2
    8 7 6, .star 1 0 2 3 4, .star 1 0 2 3 5, .star 1 0 2 3 6, .star 1 0 2 3 7, .star 1 0 2 3 8,
    .star 1 0 2 4 5, .star 1 0 2 4 6, .star 1 0 2 4 7, .star 1 0 2 4 8, .star 1 0 2 5 6, .star 1 0
    2 5 7, .star 1 0 2 5 8, .star 1 0 2 6 7, .star 1 0 2 6 8, .star 1 0 2 7 8, .star 1 2 3 4 5,
    .star 1 2 3 4 6, .star 1 2 3 4 7, .star 1 2 3 4 8, .star 1 2 3 5 6, .star 1 2 3 5 7, .star 1 2
    3 5 8, .star 1 2 3 6 7, .star 1 2 3 6 8, .star 1 2 3 7 8, .star 1 2 4 5 6, .star 1 2 4 5 7,
    .star 1 2 4 5 8, .star 1 2 4 6 7, .star 1 2 4 6 8, .star 1 2 4 7 8, .star 1 2 5 6 7, .star 1 2
    5 6 8, .star 1 2 5 7 8, .star 1 2 6 7 8, .star 2 0 1 3 4, .star 2 0 1 3 5, .star 2 0 1 3 6,
    .star 2 0 1 3 7, .star 2 0 1 3 8, .star 2 0 1 4 5, .star 2 0 1 4 6, .star 2 0 1 4 7, .star 2 0
    1 4 8, .star 2 0 1 5 6, .star 2 0 1 5 7, .star 2 0 1 5 8, .star 2 0 1 6 7, .star 2 0 1 6 8,
    .star 2 0 1 7 8, .star 2 1 3 4 5, .star 2 1 3 4 6, .star 2 1 3 4 7, .star 2 1 3 4 8, .star 2 1
    3 5 6, .star 2 1 3 5 7, .star 2 1 3 5 8, .star 2 1 3 6 7, .star 2 1 3 6 8, .star 2 1 3 7 8,
    .star 2 1 4 5 6, .star 2 1 4 5 7, .star 2 1 4 5 8, .star 2 1 4 6 7, .star 2 1 4 6 8, .star 2 1
    4 7 8, .star 2 1 5 6 7, .star 2 1 5 6 8, .star 2 1 5 7 8, .star 2 1 6 7 8],
  [.tri 0 1 3, .tri 0 2 3, .tri 0 3 4, .tri 0 3 5, .tri 0 3 6, .tri 0 3 7, .tri 0 3 8, .pent 0 1 2
    4 3, .pent 0 1 4 2 3, .pent 0 2 1 4 3, .pent 0 2 4 1 3, .pent 0 3 1 2 4, .pent 0 3 2 1 4,
    .pent 0 1 2 5 3, .pent 0 1 5 2 3, .pent 0 2 1 5 3, .pent 0 2 5 1 3, .pent 0 3 1 2 5, .pent 0 3
    2 1 5, .pent 0 1 2 6 3, .pent 0 1 6 2 3, .pent 0 2 1 6 3, .pent 0 2 6 1 3, .pent 0 3 1 2 6,
    .pent 0 3 2 1 6, .pent 0 1 2 7 3, .pent 0 1 7 2 3, .pent 0 2 1 7 3, .pent 0 2 7 1 3, .pent 0 3
    1 2 7, .pent 0 3 2 1 7, .pent 0 1 2 8 3, .pent 0 1 8 2 3, .pent 0 2 1 8 3, .pent 0 2 8 1 3,
    .pent 0 3 1 2 8, .pent 0 3 2 1 8, .pent 0 1 4 5 3, .pent 0 1 5 4 3, .pent 0 3 1 4 5, .pent 0 3
    1 5 4, .pent 0 3 4 1 5, .pent 0 3 5 1 4, .pent 0 1 4 6 3, .pent 0 1 6 4 3, .pent 0 3 1 4 6,
    .pent 0 3 1 6 4, .pent 0 3 4 1 6, .pent 0 3 6 1 4, .pent 0 1 4 7 3, .pent 0 1 7 4 3, .pent 0 3
    1 4 7, .pent 0 3 1 7 4, .pent 0 3 4 1 7, .pent 0 3 7 1 4, .pent 0 1 4 8 3, .pent 0 1 8 4 3,
    .pent 0 3 1 4 8, .pent 0 3 1 8 4, .pent 0 3 4 1 8, .pent 0 3 8 1 4, .pent 0 1 5 6 3, .pent 0 1
    6 5 3, .pent 0 3 1 5 6, .pent 0 3 1 6 5, .pent 0 3 5 1 6, .pent 0 3 6 1 5, .pent 0 1 5 7 3,
    .pent 0 1 7 5 3, .pent 0 3 1 5 7, .pent 0 3 1 7 5, .pent 0 3 5 1 7, .pent 0 3 7 1 5, .pent 0 1
    5 8 3, .pent 0 1 8 5 3, .pent 0 3 1 5 8, .pent 0 3 1 8 5, .pent 0 3 5 1 8, .pent 0 3 8 1 5,
    .pent 0 1 6 7 3, .pent 0 1 7 6 3, .pent 0 3 1 6 7, .pent 0 3 1 7 6, .pent 0 3 6 1 7, .pent 0 3
    7 1 6, .pent 0 1 6 8 3, .pent 0 1 8 6 3, .pent 0 3 1 6 8, .pent 0 3 1 8 6, .pent 0 3 6 1 8,
    .pent 0 3 8 1 6, .pent 0 1 7 8 3, .pent 0 1 8 7 3, .pent 0 3 1 7 8, .pent 0 3 1 8 7, .pent 0 3
    7 1 8, .pent 0 3 8 1 7, .pent 0 2 4 5 3, .pent 0 2 5 4 3, .pent 0 3 2 4 5, .pent 0 3 2 5 4,
    .pent 0 3 4 2 5, .pent 0 3 5 2 4, .pent 0 2 4 6 3, .pent 0 2 6 4 3, .pent 0 3 2 4 6, .pent 0 3
    2 6 4, .pent 0 3 4 2 6, .pent 0 3 6 2 4, .pent 0 2 4 7 3, .pent 0 2 7 4 3, .pent 0 3 2 4 7,
    .pent 0 3 2 7 4, .pent 0 3 4 2 7, .pent 0 3 7 2 4, .pent 0 2 4 8 3, .pent 0 2 8 4 3, .pent 0 3
    2 4 8, .pent 0 3 2 8 4, .pent 0 3 4 2 8, .pent 0 3 8 2 4, .pent 0 2 5 6 3, .pent 0 2 6 5 3,
    .pent 0 3 2 5 6, .pent 0 3 2 6 5, .pent 0 3 5 2 6, .pent 0 3 6 2 5, .pent 0 2 5 7 3, .pent 0 2
    7 5 3, .pent 0 3 2 5 7, .pent 0 3 2 7 5, .pent 0 3 5 2 7, .pent 0 3 7 2 5, .pent 0 2 5 8 3,
    .pent 0 2 8 5 3, .pent 0 3 2 5 8, .pent 0 3 2 8 5, .pent 0 3 5 2 8, .pent 0 3 8 2 5, .pent 0 2
    6 7 3, .pent 0 2 7 6 3, .pent 0 3 2 6 7, .pent 0 3 2 7 6, .pent 0 3 6 2 7, .pent 0 3 7 2 6,
    .pent 0 2 6 8 3, .pent 0 2 8 6 3, .pent 0 3 2 6 8, .pent 0 3 2 8 6, .pent 0 3 6 2 8, .pent 0 3
    8 2 6, .pent 0 2 7 8 3, .pent 0 2 8 7 3, .pent 0 3 2 7 8, .pent 0 3 2 8 7, .pent 0 3 7 2 8,
    .pent 0 3 8 2 7, .pent 0 3 4 5 6, .pent 0 3 4 6 5, .pent 0 3 5 4 6, .pent 0 3 5 6 4, .pent 0 3
    6 4 5, .pent 0 3 6 5 4, .pent 0 3 4 5 7, .pent 0 3 4 7 5, .pent 0 3 5 4 7, .pent 0 3 5 7 4,
    .pent 0 3 7 4 5, .pent 0 3 7 5 4, .pent 0 3 4 5 8, .pent 0 3 4 8 5, .pent 0 3 5 4 8, .pent 0 3
    5 8 4, .pent 0 3 8 4 5, .pent 0 3 8 5 4, .pent 0 3 4 6 7, .pent 0 3 4 7 6, .pent 0 3 6 4 7,
    .pent 0 3 6 7 4, .pent 0 3 7 4 6, .pent 0 3 7 6 4, .pent 0 3 4 6 8, .pent 0 3 4 8 6, .pent 0 3
    6 4 8, .pent 0 3 6 8 4, .pent 0 3 8 4 6, .pent 0 3 8 6 4, .pent 0 3 4 7 8, .pent 0 3 4 8 7,
    .pent 0 3 7 4 8, .pent 0 3 7 8 4, .pent 0 3 8 4 7, .pent 0 3 8 7 4, .pent 0 3 5 6 7, .pent 0 3
    5 7 6, .pent 0 3 6 5 7, .pent 0 3 6 7 5, .pent 0 3 7 5 6, .pent 0 3 7 6 5, .pent 0 3 5 6 8,
    .pent 0 3 5 8 6, .pent 0 3 6 5 8, .pent 0 3 6 8 5, .pent 0 3 8 5 6, .pent 0 3 8 6 5, .pent 0 3
    5 7 8, .pent 0 3 5 8 7, .pent 0 3 7 5 8, .pent 0 3 7 8 5, .pent 0 3 8 5 7, .pent 0 3 8 7 5,
    .pent 0 3 6 7 8, .pent 0 3 6 8 7, .pent 0 3 7 6 8, .pent 0 3 7 8 6, .pent 0 3 8 6 7, .pent 0 3
    8 7 6, .star 0 1 2 3 4, .star 0 1 2 3 5, .star 0 1 2 3 6, .star 0 1 2 3 7, .star 0 1 2 3 8,
    .star 0 1 3 4 5, .star 0 1 3 4 6, .star 0 1 3 4 7, .star 0 1 3 4 8, .star 0 1 3 5 6, .star 0 1
    3 5 7, .star 0 1 3 5 8, .star 0 1 3 6 7, .star 0 1 3 6 8, .star 0 1 3 7 8, .star 0 2 3 4 5,
    .star 0 2 3 4 6, .star 0 2 3 4 7, .star 0 2 3 4 8, .star 0 2 3 5 6, .star 0 2 3 5 7, .star 0 2
    3 5 8, .star 0 2 3 6 7, .star 0 2 3 6 8, .star 0 2 3 7 8, .star 0 3 4 5 6, .star 0 3 4 5 7,
    .star 0 3 4 5 8, .star 0 3 4 6 7, .star 0 3 4 6 8, .star 0 3 4 7 8, .star 0 3 5 6 7, .star 0 3
    5 6 8, .star 0 3 5 7 8, .star 0 3 6 7 8, .star 3 0 1 2 4, .star 3 0 1 2 5, .star 3 0 1 2 6,
    .star 3 0 1 2 7, .star 3 0 1 2 8, .star 3 0 1 4 5, .star 3 0 1 4 6, .star 3 0 1 4 7, .star 3 0
    1 4 8, .star 3 0 1 5 6, .star 3 0 1 5 7, .star 3 0 1 5 8, .star 3 0 1 6 7, .star 3 0 1 6 8,
    .star 3 0 1 7 8, .star 3 0 2 4 5, .star 3 0 2 4 6, .star 3 0 2 4 7, .star 3 0 2 4 8, .star 3 0
    2 5 6, .star 3 0 2 5 7, .star 3 0 2 5 8, .star 3 0 2 6 7, .star 3 0 2 6 8, .star 3 0 2 7 8,
    .star 3 0 4 5 6, .star 3 0 4 5 7, .star 3 0 4 5 8, .star 3 0 4 6 7, .star 3 0 4 6 8, .star 3 0
    4 7 8, .star 3 0 5 6 7, .star 3 0 5 6 8, .star 3 0 5 7 8, .star 3 0 6 7 8],
  [.tri 0 1 3, .tri 1 2 3, .tri 1 3 4, .tri 1 3 5, .tri 1 3 6, .tri 1 3 7, .tri 1 3 8, .pent 0 1 3
    2 4, .pent 0 1 3 4 2, .pent 0 2 1 3 4, .pent 0 2 3 1 4, .pent 0 2 4 1 3, .pent 0 3 1 2 4,
    .pent 0 1 3 2 5, .pent 0 1 3 5 2, .pent 0 2 1 3 5, .pent 0 2 3 1 5, .pent 0 2 5 1 3, .pent 0 3
    1 2 5, .pent 0 1 3 2 6, .pent 0 1 3 6 2, .pent 0 2 1 3 6, .pent 0 2 3 1 6, .pent 0 2 6 1 3,
    .pent 0 3 1 2 6, .pent 0 1 3 2 7, .pent 0 1 3 7 2, .pent 0 2 1 3 7, .pent 0 2 3 1 7, .pent 0 2
    7 1 3, .pent 0 3 1 2 7, .pent 0 1 3 2 8, .pent 0 1 3 8 2, .pent 0 2 1 3 8, .pent 0 2 3 1 8,
    .pent 0 2 8 1 3, .pent 0 3 1 2 8, .pent 0 1 3 4 5, .pent 0 1 3 5 4, .pent 0 3 1 4 5, .pent 0 3
    1 5 4, .pent 0 4 1 3 5, .pent 0 4 3 1 5, .pent 0 1 3 4 6, .pent 0 1 3 6 4, .pent 0 3 1 4 6,
    .pent 0 3 1 6 4, .pent 0 4 1 3 6, .pent 0 4 3 1 6, .pent 0 1 3 4 7, .pent 0 1 3 7 4, .pent 0 3
    1 4 7, .pent 0 3 1 7 4, .pent 0 4 1 3 7, .pent 0 4 3 1 7, .pent 0 1 3 4 8, .pent 0 1 3 8 4,
    .pent 0 3 1 4 8, .pent 0 3 1 8 4, .pent 0 4 1 3 8, .pent 0 4 3 1 8, .pent 0 1 3 5 6, .pent 0 1
    3 6 5, .pent 0 3 1 5 6, .pent 0 3 1 6 5, .pent 0 5 1 3 6, .pent 0 5 3 1 6, .pent 0 1 3 5 7,
    .pent 0 1 3 7 5, .pent 0 3 1 5 7, .pent 0 3 1 7 5, .pent 0 5 1 3 7, .pent 0 5 3 1 7, .pent 0 1
    3 5 8, .pent 0 1 3 8 5, .pent 0 3 1 5 8, .pent 0 3 1 8 5, .pent 0 5 1 3 8, .pent 0 5 3 1 8,
    .pent 0 1 3 6 7, .pent 0 1 3 7 6, .pent 0 3 1 6 7, .pent 0 3 1 7 6, .pent 0 6 1 3 7, .pent 0 6
    3 1 7, .pent 0 1 3 6 8, .pent 0 1 3 8 6, .pent 0 3 1 6 8, .pent 0 3 1 8 6, .pent 0 6 1 3 8,
    .pent 0 6 3 1 8, .pent 0 1 3 7 8, .pent 0 1 3 8 7, .pent 0 3 1 7 8, .pent 0 3 1 8 7, .pent 0 7
    1 3 8, .pent 0 7 3 1 8, .pent 1 2 4 5 3, .pent 1 2 5 4 3, .pent 1 3 2 4 5, .pent 1 3 2 5 4,
    .pent 1 3 4 2 5, .pent 1 3 5 2 4, .pent 1 2 4 6 3, .pent 1 2 6 4 3, .pent 1 3 2 4 6, .pent 1 3
    2 6 4, .pent 1 3 4 2 6, .pent 1 3 6 2 4, .pent 1 2 4 7 3, .pent 1 2 7 4 3, .pent 1 3 2 4 7,
    .pent 1 3 2 7 4, .pent 1 3 4 2 7, .pent 1 3 7 2 4, .pent 1 2 4 8 3, .pent 1 2 8 4 3, .pent 1 3
    2 4 8, .pent 1 3 2 8 4, .pent 1 3 4 2 8, .pent 1 3 8 2 4, .pent 1 2 5 6 3, .pent 1 2 6 5 3,
    .pent 1 3 2 5 6, .pent 1 3 2 6 5, .pent 1 3 5 2 6, .pent 1 3 6 2 5, .pent 1 2 5 7 3, .pent 1 2
    7 5 3, .pent 1 3 2 5 7, .pent 1 3 2 7 5, .pent 1 3 5 2 7, .pent 1 3 7 2 5, .pent 1 2 5 8 3,
    .pent 1 2 8 5 3, .pent 1 3 2 5 8, .pent 1 3 2 8 5, .pent 1 3 5 2 8, .pent 1 3 8 2 5, .pent 1 2
    6 7 3, .pent 1 2 7 6 3, .pent 1 3 2 6 7, .pent 1 3 2 7 6, .pent 1 3 6 2 7, .pent 1 3 7 2 6,
    .pent 1 2 6 8 3, .pent 1 2 8 6 3, .pent 1 3 2 6 8, .pent 1 3 2 8 6, .pent 1 3 6 2 8, .pent 1 3
    8 2 6, .pent 1 2 7 8 3, .pent 1 2 8 7 3, .pent 1 3 2 7 8, .pent 1 3 2 8 7, .pent 1 3 7 2 8,
    .pent 1 3 8 2 7, .pent 1 3 4 5 6, .pent 1 3 4 6 5, .pent 1 3 5 4 6, .pent 1 3 5 6 4, .pent 1 3
    6 4 5, .pent 1 3 6 5 4, .pent 1 3 4 5 7, .pent 1 3 4 7 5, .pent 1 3 5 4 7, .pent 1 3 5 7 4,
    .pent 1 3 7 4 5, .pent 1 3 7 5 4, .pent 1 3 4 5 8, .pent 1 3 4 8 5, .pent 1 3 5 4 8, .pent 1 3
    5 8 4, .pent 1 3 8 4 5, .pent 1 3 8 5 4, .pent 1 3 4 6 7, .pent 1 3 4 7 6, .pent 1 3 6 4 7,
    .pent 1 3 6 7 4, .pent 1 3 7 4 6, .pent 1 3 7 6 4, .pent 1 3 4 6 8, .pent 1 3 4 8 6, .pent 1 3
    6 4 8, .pent 1 3 6 8 4, .pent 1 3 8 4 6, .pent 1 3 8 6 4, .pent 1 3 4 7 8, .pent 1 3 4 8 7,
    .pent 1 3 7 4 8, .pent 1 3 7 8 4, .pent 1 3 8 4 7, .pent 1 3 8 7 4, .pent 1 3 5 6 7, .pent 1 3
    5 7 6, .pent 1 3 6 5 7, .pent 1 3 6 7 5, .pent 1 3 7 5 6, .pent 1 3 7 6 5, .pent 1 3 5 6 8,
    .pent 1 3 5 8 6, .pent 1 3 6 5 8, .pent 1 3 6 8 5, .pent 1 3 8 5 6, .pent 1 3 8 6 5, .pent 1 3
    5 7 8, .pent 1 3 5 8 7, .pent 1 3 7 5 8, .pent 1 3 7 8 5, .pent 1 3 8 5 7, .pent 1 3 8 7 5,
    .pent 1 3 6 7 8, .pent 1 3 6 8 7, .pent 1 3 7 6 8, .pent 1 3 7 8 6, .pent 1 3 8 6 7, .pent 1 3
    8 7 6, .star 1 0 2 3 4, .star 1 0 2 3 5, .star 1 0 2 3 6, .star 1 0 2 3 7, .star 1 0 2 3 8,
    .star 1 0 3 4 5, .star 1 0 3 4 6, .star 1 0 3 4 7, .star 1 0 3 4 8, .star 1 0 3 5 6, .star 1 0
    3 5 7, .star 1 0 3 5 8, .star 1 0 3 6 7, .star 1 0 3 6 8, .star 1 0 3 7 8, .star 1 2 3 4 5,
    .star 1 2 3 4 6, .star 1 2 3 4 7, .star 1 2 3 4 8, .star 1 2 3 5 6, .star 1 2 3 5 7, .star 1 2
    3 5 8, .star 1 2 3 6 7, .star 1 2 3 6 8, .star 1 2 3 7 8, .star 1 3 4 5 6, .star 1 3 4 5 7,
    .star 1 3 4 5 8, .star 1 3 4 6 7, .star 1 3 4 6 8, .star 1 3 4 7 8, .star 1 3 5 6 7, .star 1 3
    5 6 8, .star 1 3 5 7 8, .star 1 3 6 7 8, .star 3 0 1 2 4, .star 3 0 1 2 5, .star 3 0 1 2 6,
    .star 3 0 1 2 7, .star 3 0 1 2 8, .star 3 0 1 4 5, .star 3 0 1 4 6, .star 3 0 1 4 7, .star 3 0
    1 4 8, .star 3 0 1 5 6, .star 3 0 1 5 7, .star 3 0 1 5 8, .star 3 0 1 6 7, .star 3 0 1 6 8,
    .star 3 0 1 7 8, .star 3 1 2 4 5, .star 3 1 2 4 6, .star 3 1 2 4 7, .star 3 1 2 4 8, .star 3 1
    2 5 6, .star 3 1 2 5 7, .star 3 1 2 5 8, .star 3 1 2 6 7, .star 3 1 2 6 8, .star 3 1 2 7 8,
    .star 3 1 4 5 6, .star 3 1 4 5 7, .star 3 1 4 5 8, .star 3 1 4 6 7, .star 3 1 4 6 8, .star 3 1
    4 7 8, .star 3 1 5 6 7, .star 3 1 5 6 8, .star 3 1 5 7 8, .star 3 1 6 7 8],
  [.tri 0 2 3, .tri 1 2 3, .tri 2 3 4, .tri 2 3 5, .tri 2 3 6, .tri 2 3 7, .tri 2 3 8, .pent 0 1 2
    3 4, .pent 0 1 3 2 4, .pent 0 1 4 2 3, .pent 0 1 4 3 2, .pent 0 2 3 1 4, .pent 0 3 2 1 4,
    .pent 0 1 2 3 5, .pent 0 1 3 2 5, .pent 0 1 5 2 3, .pent 0 1 5 3 2, .pent 0 2 3 1 5, .pent 0 3
    2 1 5, .pent 0 1 2 3 6, .pent 0 1 3 2 6, .pent 0 1 6 2 3, .pent 0 1 6 3 2, .pent 0 2 3 1 6,
    .pent 0 3 2 1 6, .pent 0 1 2 3 7, .pent 0 1 3 2 7, .pent 0 1 7 2 3, .pent 0 1 7 3 2, .pent 0 2
    3 1 7, .pent 0 3 2 1 7, .pent 0 1 2 3 8, .pent 0 1 3 2 8, .pent 0 1 8 2 3, .pent 0 1 8 3 2,
    .pent 0 2 3 1 8, .pent 0 3 2 1 8, .pent 0 2 3 4 5, .pent 0 2 3 5 4, .pent 0 3 2 4 5, .pent 0 3
    2 5 4, .pent 0 4 2 3 5, .pent 0 4 3 2 5, .pent 0 2 3 4 6, .pent 0 2 3 6 4, .pent 0 3 2 4 6,
    .pent 0 3 2 6 4, .pent 0 4 2 3 6, .pent 0 4 3 2 6, .pent 0 2 3 4 7, .pent 0 2 3 7 4, .pent 0 3
    2 4 7, .pent 0 3 2 7 4, .pent 0 4 2 3 7, .pent 0 4 3 2 7, .pent 0 2 3 4 8, .pent 0 2 3 8 4,
    .pent 0 3 2 4 8, .pent 0 3 2 8 4, .pent 0 4 2 3 8, .pent 0 4 3 2 8, .pent 0 2 3 5 6, .pent 0 2
    3 6 5, .pent 0 3 2 5 6, .pent 0 3 2 6 5, .pent 0 5 2 3 6, .pent 0 5 3 2 6, .pent 0 2 3 5 7,
    .pent 0 2 3 7 5, .pent 0 3 2 5 7, .pent 0 3 2 7 5, .pent 0 5 2 3 7, .pent 0 5 3 2 7, .pent 0 2
    3 5 8, .pent 0 2 3 8 5, .pent 0 3 2 5 8, .pent 0 3 2 8 5, .pent 0 5 2 3 8, .pent 0 5 3 2 8,
    .pent 0 2 3 6 7, .pent 0 2 3 7 6, .pent 0 3 2 6 7, .pent 0 3 2 7 6, .pent 0 6 2 3 7, .pent 0 6
    3 2 7, .pent 0 2 3 6 8, .pent 0 2 3 8 6, .pent 0 3 2 6 8, .pent 0 3 2 8 6, .pent 0 6 2 3 8,
    .pent 0 6 3 2 8, .pent 0 2 3 7 8, .pent 0 2 3 8 7, .pent 0 3 2 7 8, .pent 0 3 2 8 7, .pent 0 7
    2 3 8, .pent 0 7 3 2 8, .pent 1 2 3 4 5, .pent 1 2 3 5 4, .pent 1 3 2 4 5, .pent 1 3 2 5 4,
    .pent 1 4 2 3 5, .pent 1 4 3 2 5, .pent 1 2 3 4 6, .pent 1 2 3 6 4, .pent 1 3 2 4 6, .pent 1 3
    2 6 4, .pent 1 4 2 3 6, .pent 1 4 3 2 6, .pent 1 2 3 4 7, .pent 1 2 3 7 4, .pent 1 3 2 4 7,
    .pent 1 3 2 7 4, .pent 1 4 2 3 7, .pent 1 4 3 2 7, .pent 1 2 3 4 8, .pent 1 2 3 8 4, .pent 1 3
    2 4 8, .pent 1 3 2 8 4, .pent 1 4 2 3 8, .pent 1 4 3 2 8, .pent 1 2 3 5 6, .pent 1 2 3 6 5,
    .pent 1 3 2 5 6, .pent 1 3 2 6 5, .pent 1 5 2 3 6, .pent 1 5 3 2 6, .pent 1 2 3 5 7, .pent 1 2
    3 7 5, .pent 1 3 2 5 7, .pent 1 3 2 7 5, .pent 1 5 2 3 7, .pent 1 5 3 2 7, .pent 1 2 3 5 8,
    .pent 1 2 3 8 5, .pent 1 3 2 5 8, .pent 1 3 2 8 5, .pent 1 5 2 3 8, .pent 1 5 3 2 8, .pent 1 2
    3 6 7, .pent 1 2 3 7 6, .pent 1 3 2 6 7, .pent 1 3 2 7 6, .pent 1 6 2 3 7, .pent 1 6 3 2 7,
    .pent 1 2 3 6 8, .pent 1 2 3 8 6, .pent 1 3 2 6 8, .pent 1 3 2 8 6, .pent 1 6 2 3 8, .pent 1 6
    3 2 8, .pent 1 2 3 7 8, .pent 1 2 3 8 7, .pent 1 3 2 7 8, .pent 1 3 2 8 7, .pent 1 7 2 3 8,
    .pent 1 7 3 2 8, .pent 2 3 4 5 6, .pent 2 3 4 6 5, .pent 2 3 5 4 6, .pent 2 3 5 6 4, .pent 2 3
    6 4 5, .pent 2 3 6 5 4, .pent 2 3 4 5 7, .pent 2 3 4 7 5, .pent 2 3 5 4 7, .pent 2 3 5 7 4,
    .pent 2 3 7 4 5, .pent 2 3 7 5 4, .pent 2 3 4 5 8, .pent 2 3 4 8 5, .pent 2 3 5 4 8, .pent 2 3
    5 8 4, .pent 2 3 8 4 5, .pent 2 3 8 5 4, .pent 2 3 4 6 7, .pent 2 3 4 7 6, .pent 2 3 6 4 7,
    .pent 2 3 6 7 4, .pent 2 3 7 4 6, .pent 2 3 7 6 4, .pent 2 3 4 6 8, .pent 2 3 4 8 6, .pent 2 3
    6 4 8, .pent 2 3 6 8 4, .pent 2 3 8 4 6, .pent 2 3 8 6 4, .pent 2 3 4 7 8, .pent 2 3 4 8 7,
    .pent 2 3 7 4 8, .pent 2 3 7 8 4, .pent 2 3 8 4 7, .pent 2 3 8 7 4, .pent 2 3 5 6 7, .pent 2 3
    5 7 6, .pent 2 3 6 5 7, .pent 2 3 6 7 5, .pent 2 3 7 5 6, .pent 2 3 7 6 5, .pent 2 3 5 6 8,
    .pent 2 3 5 8 6, .pent 2 3 6 5 8, .pent 2 3 6 8 5, .pent 2 3 8 5 6, .pent 2 3 8 6 5, .pent 2 3
    5 7 8, .pent 2 3 5 8 7, .pent 2 3 7 5 8, .pent 2 3 7 8 5, .pent 2 3 8 5 7, .pent 2 3 8 7 5,
    .pent 2 3 6 7 8, .pent 2 3 6 8 7, .pent 2 3 7 6 8, .pent 2 3 7 8 6, .pent 2 3 8 6 7, .pent 2 3
    8 7 6, .star 2 0 1 3 4, .star 2 0 1 3 5, .star 2 0 1 3 6, .star 2 0 1 3 7, .star 2 0 1 3 8,
    .star 2 0 3 4 5, .star 2 0 3 4 6, .star 2 0 3 4 7, .star 2 0 3 4 8, .star 2 0 3 5 6, .star 2 0
    3 5 7, .star 2 0 3 5 8, .star 2 0 3 6 7, .star 2 0 3 6 8, .star 2 0 3 7 8, .star 2 1 3 4 5,
    .star 2 1 3 4 6, .star 2 1 3 4 7, .star 2 1 3 4 8, .star 2 1 3 5 6, .star 2 1 3 5 7, .star 2 1
    3 5 8, .star 2 1 3 6 7, .star 2 1 3 6 8, .star 2 1 3 7 8, .star 2 3 4 5 6, .star 2 3 4 5 7,
    .star 2 3 4 5 8, .star 2 3 4 6 7, .star 2 3 4 6 8, .star 2 3 4 7 8, .star 2 3 5 6 7, .star 2 3
    5 6 8, .star 2 3 5 7 8, .star 2 3 6 7 8, .star 3 0 1 2 4, .star 3 0 1 2 5, .star 3 0 1 2 6,
    .star 3 0 1 2 7, .star 3 0 1 2 8, .star 3 0 2 4 5, .star 3 0 2 4 6, .star 3 0 2 4 7, .star 3 0
    2 4 8, .star 3 0 2 5 6, .star 3 0 2 5 7, .star 3 0 2 5 8, .star 3 0 2 6 7, .star 3 0 2 6 8,
    .star 3 0 2 7 8, .star 3 1 2 4 5, .star 3 1 2 4 6, .star 3 1 2 4 7, .star 3 1 2 4 8, .star 3 1
    2 5 6, .star 3 1 2 5 7, .star 3 1 2 5 8, .star 3 1 2 6 7, .star 3 1 2 6 8, .star 3 1 2 7 8,
    .star 3 2 4 5 6, .star 3 2 4 5 7, .star 3 2 4 5 8, .star 3 2 4 6 7, .star 3 2 4 6 8, .star 3 2
    4 7 8, .star 3 2 5 6 7, .star 3 2 5 6 8, .star 3 2 5 7 8, .star 3 2 6 7 8],
  [.tri 0 1 4, .tri 0 2 4, .tri 0 3 4, .tri 0 4 5, .tri 0 4 6, .tri 0 4 7, .tri 0 4 8, .pent 0 1 2
    3 4, .pent 0 1 3 2 4, .pent 0 2 1 3 4, .pent 0 2 3 1 4, .pent 0 3 1 2 4, .pent 0 3 2 1 4,
    .pent 0 1 2 5 4, .pent 0 1 5 2 4, .pent 0 2 1 5 4, .pent 0 2 5 1 4, .pent 0 4 1 2 5, .pent 0 4
    2 1 5, .pent 0 1 2 6 4, .pent 0 1 6 2 4, .pent 0 2 1 6 4, .pent 0 2 6 1 4, .pent 0 4 1 2 6,
    .pent 0 4 2 1 6, .pent 0 1 2 7 4, .pent 0 1 7 2 4, .pent 0 2 1 7 4, .pent 0 2 7 1 4, .pent 0 4
    1 2 7, .pent 0 4 2 1 7, .pent 0 1 2 8 4, .pent 0 1 8 2 4, .pent 0 2 1 8 4, .pent 0 2 8 1 4,
    .pent 0 4 1 2 8, .pent 0 4 2 1 8, .pent 0 1 3 5 4, .pent 0 1 5 3 4, .pent 0 3 1 5 4, .pent 0 3
    5 1 4, .pent 0 4 1 3 5, .pent 0 4 3 1 5, .pent 0 1 3 6 4, .pent 0 1 6 3 4, .pent 0 3 1 6 4,
    .pent 0 3 6 1 4, .pent 0 4 1 3 6, .pent 0 4 3 1 6, .pent 0 1 3 7 4, .pent 0 1 7 3 4, .pent 0 3
    1 7 4, .pent 0 3 7 1 4, .pent 0 4 1 3 7, .pent 0 4 3 1 7, .pent 0 1 3 8 4, .pent 0 1 8 3 4,
    .pent 0 3 1 8 4, .pent 0 3 8 1 4, .pent 0 4 1 3 8, .pent 0 4 3 1 8, .pent 0 1 5 6 4, .pent 0 1
    6 5 4, .pent 0 4 1 5 6, .pent 0 4 1 6 5, .pent 0 4 5 1 6, .pent 0 4 6 1 5, .pent 0 1 5 7 4,
    .pent 0 1 7 5 4, .pent 0 4 1 5 7, .pent 0 4 1 7 5, .pent 0 4 5 1 7, .pent 0 4 7 1 5, .pent 0 1
    5 8 4, .pent 0 1 8 5 4, .pent 0 4 1 5 8, .pent 0 4 1 8 5, .pent 0 4 5 1 8, .pent 0 4 8 1 5,
    .pent 0 1 6 7 4, .pent 0 1 7 6 4, .pent 0 4 1 6 7, .pent 0 4 1 7 6, .pent 0 4 6 1 7, .pent 0 4
    7 1 6, .pent 0 1 6 8 4, .pent 0 1 8 6 4, .pent 0 4 1 6 8, .pent 0 4 1 8 6, .pent 0 4 6 1 8,
    .pent 0 4 8 1 6, .pent 0 1 7 8 4, .pent 0 1 8 7 4, .pent 0 4 1 7 8, .pent 0 4 1 8 7, .pent 0 4
    7 1 8, .pent 0 4 8 1 7, .pent 0 2 3 5 4, .pent 0 2 5 3 4, .pent 0 3 2 5 4, .pent 0 3 5 2 4,
    .pent 0 4 2 3 5, .pent 0 4 3 2 5, .pent 0 2 3 6 4, .pent 0 2 6 3 4, .pent 0 3 2 6 4, .pent 0 3
    6 2 4, .pent 0 4 2 3 6, .pent 0 4 3 2 6, .pent 0 2 3 7 4, .pent 0 2 7 3 4, .pent 0 3 2 7 4,
    .pent 0 3 7 2 4, .pent 0 4 2 3 7, .pent 0 4 3 2 7, .pent 0 2 3 8 4, .pent 0 2 8 3 4, .pent 0 3
    2 8 4, .pent 0 3 8 2 4, .pent 0 4 2 3 8, .pent 0 4 3 2 8, .pent 0 2 5 6 4, .pent 0 2 6 5 4,
    .pent 0 4 2 5 6, .pent 0 4 2 6 5, .pent 0 4 5 2 6, .pent 0 4 6 2 5, .pent 0 2 5 7 4, .pent 0 2
    7 5 4, .pent 0 4 2 5 7, .pent 0 4 2 7 5, .pent 0 4 5 2 7, .pent 0 4 7 2 5, .pent 0 2 5 8 4,
    .pent 0 2 8 5 4, .pent 0 4 2 5 8, .pent 0 4 2 8 5, .pent 0 4 5 2 8, .pent 0 4 8 2 5, .pent 0 2
    6 7 4, .pent 0 2 7 6 4, .pent 0 4 2 6 7, .pent 0 4 2 7 6, .pent 0 4 6 2 7, .pent 0 4 7 2 6,
    .pent 0 2 6 8 4, .pent 0 2 8 6 4, .pent 0 4 2 6 8, .pent 0 4 2 8 6, .pent 0 4 6 2 8, .pent 0 4
    8 2 6, .pent 0 2 7 8 4, .pent 0 2 8 7 4, .pent 0 4 2 7 8, .pent 0 4 2 8 7, .pent 0 4 7 2 8,
    .pent 0 4 8 2 7, .pent 0 3 5 6 4, .pent 0 3 6 5 4, .pent 0 4 3 5 6, .pent 0 4 3 6 5, .pent 0 4
    5 3 6, .pent 0 4 6 3 5, .pent 0 3 5 7 4, .pent 0 3 7 5 4, .pent 0 4 3 5 7, .pent 0 4 3 7 5,
    .pent 0 4 5 3 7, .pent 0 4 7 3 5, .pent 0 3 5 8 4, .pent 0 3 8 5 4, .pent 0 4 3 5 8, .pent 0 4
    3 8 5, .pent 0 4 5 3 8, .pent 0 4 8 3 5, .pent 0 3 6 7 4, .pent 0 3 7 6 4, .pent 0 4 3 6 7,
    .pent 0 4 3 7 6, .pent 0 4 6 3 7, .pent 0 4 7 3 6, .pent 0 3 6 8 4, .pent 0 3 8 6 4, .pent 0 4
    3 6 8, .pent 0 4 3 8 6, .pent 0 4 6 3 8, .pent 0 4 8 3 6, .pent 0 3 7 8 4, .pent 0 3 8 7 4,
    .pent 0 4 3 7 8, .pent 0 4 3 8 7, .pent 0 4 7 3 8, .pent 0 4 8 3 7, .pent 0 4 5 6 7, .pent 0 4
    5 7 6, .pent 0 4 6 5 7, .pent 0 4 6 7 5, .pent 0 4 7 5 6, .pent 0 4 7 6 5, .pent 0 4 5 6 8,
    .pent 0 4 5 8 6, .pent 0 4 6 5 8, .pent 0 4 6 8 5, .pent 0 4 8 5 6, .pent 0 4 8 6 5, .pent 0 4
    5 7 8, .pent 0 4 5 8 7, .pent 0 4 7 5 8, .pent 0 4 7 8 5, .pent 0 4 8 5 7, .pent 0 4 8 7 5,
    .pent 0 4 6 7 8, .pent 0 4 6 8 7, .pent 0 4 7 6 8, .pent 0 4 7 8 6, .pent 0 4 8 6 7, .pent 0 4
    8 7 6, .star 0 1 2 3 4, .star 0 1 2 4 5, .star 0 1 2 4 6, .star 0 1 2 4 7, .star 0 1 2 4 8,
    .star 0 1 3 4 5, .star 0 1 3 4 6, .star 0 1 3 4 7, .star 0 1 3 4 8, .star 0 1 4 5 6, .star 0 1
    4 5 7, .star 0 1 4 5 8, .star 0 1 4 6 7, .star 0 1 4 6 8, .star 0 1 4 7 8, .star 0 2 3 4 5,
    .star 0 2 3 4 6, .star 0 2 3 4 7, .star 0 2 3 4 8, .star 0 2 4 5 6, .star 0 2 4 5 7, .star 0 2
    4 5 8, .star 0 2 4 6 7, .star 0 2 4 6 8, .star 0 2 4 7 8, .star 0 3 4 5 6, .star 0 3 4 5 7,
    .star 0 3 4 5 8, .star 0 3 4 6 7, .star 0 3 4 6 8, .star 0 3 4 7 8, .star 0 4 5 6 7, .star 0 4
    5 6 8, .star 0 4 5 7 8, .star 0 4 6 7 8, .star 4 0 1 2 3, .star 4 0 1 2 5, .star 4 0 1 2 6,
    .star 4 0 1 2 7, .star 4 0 1 2 8, .star 4 0 1 3 5, .star 4 0 1 3 6, .star 4 0 1 3 7, .star 4 0
    1 3 8, .star 4 0 1 5 6, .star 4 0 1 5 7, .star 4 0 1 5 8, .star 4 0 1 6 7, .star 4 0 1 6 8,
    .star 4 0 1 7 8, .star 4 0 2 3 5, .star 4 0 2 3 6, .star 4 0 2 3 7, .star 4 0 2 3 8, .star 4 0
    2 5 6, .star 4 0 2 5 7, .star 4 0 2 5 8, .star 4 0 2 6 7, .star 4 0 2 6 8, .star 4 0 2 7 8,
    .star 4 0 3 5 6, .star 4 0 3 5 7, .star 4 0 3 5 8, .star 4 0 3 6 7, .star 4 0 3 6 8, .star 4 0
    3 7 8, .star 4 0 5 6 7, .star 4 0 5 6 8, .star 4 0 5 7 8, .star 4 0 6 7 8],
  [.tri 0 1 4, .tri 1 2 4, .tri 1 3 4, .tri 1 4 5, .tri 1 4 6, .tri 1 4 7, .tri 1 4 8, .pent 0 1 4
    2 3, .pent 0 1 4 3 2, .pent 0 2 1 4 3, .pent 0 2 3 1 4, .pent 0 2 4 1 3, .pent 0 3 2 1 4,
    .pent 0 1 4 2 5, .pent 0 1 4 5 2, .pent 0 2 1 4 5, .pent 0 2 4 1 5, .pent 0 2 5 1 4, .pent 0 4
    1 2 5, .pent 0 1 4 2 6, .pent 0 1 4 6 2, .pent 0 2 1 4 6, .pent 0 2 4 1 6, .pent 0 2 6 1 4,
    .pent 0 4 1 2 6, .pent 0 1 4 2 7, .pent 0 1 4 7 2, .pent 0 2 1 4 7, .pent 0 2 4 1 7, .pent 0 2
    7 1 4, .pent 0 4 1 2 7, .pent 0 1 4 2 8, .pent 0 1 4 8 2, .pent 0 2 1 4 8, .pent 0 2 4 1 8,
    .pent 0 2 8 1 4, .pent 0 4 1 2 8, .pent 0 1 4 3 5, .pent 0 1 4 5 3, .pent 0 3 1 4 5, .pent 0 3
    4 1 5, .pent 0 3 5 1 4, .pent 0 4 1 3 5, .pent 0 1 4 3 6, .pent 0 1 4 6 3, .pent 0 3 1 4 6,
    .pent 0 3 4 1 6, .pent 0 3 6 1 4, .pent 0 4 1 3 6, .pent 0 1 4 3 7, .pent 0 1 4 7 3, .pent 0 3
    1 4 7, .pent 0 3 4 1 7, .pent 0 3 7 1 4, .pent 0 4 1 3 7, .pent 0 1 4 3 8, .pent 0 1 4 8 3,
    .pent 0 3 1 4 8, .pent 0 3 4 1 8, .pent 0 3 8 1 4, .pent 0 4 1 3 8, .pent 0 1 4 5 6, .pent 0 1
    4 6 5, .pent 0 4 1 5 6, .pent 0 4 1 6 5, .pent 0 5 1 4 6, .pent 0 5 4 1 6, .pent 0 1 4 5 7,
    .pent 0 1 4 7 5, .pent 0 4 1 5 7, .pent 0 4 1 7 5, .pent 0 5 1 4 7, .pent 0 5 4 1 7, .pent 0 1
    4 5 8, .pent 0 1 4 8 5, .pent 0 4 1 5 8, .pent 0 4 1 8 5, .pent 0 5 1 4 8, .pent 0 5 4 1 8,
    .pent 0 1 4 6 7, .pent 0 1 4 7 6, .pent 0 4 1 6 7, .pent 0 4 1 7 6, .pent 0 6 1 4 7, .pent 0 6
    4 1 7, .pent 0 1 4 6 8, .pent 0 1 4 8 6, .pent 0 4 1 6 8, .pent 0 4 1 8 6, .pent 0 6 1 4 8,
    .pent 0 6 4 1 8, .pent 0 1 4 7 8, .pent 0 1 4 8 7, .pent 0 4 1 7 8, .pent 0 4 1 8 7, .pent 0 7
    1 4 8, .pent 0 7 4 1 8, .pent 1 2 3 5 4, .pent 1 2 5 3 4, .pent 1 3 2 5 4, .pent 1 3 5 2 4,
    .pent 1 4 2 3 5, .pent 1 4 3 2 5, .pent 1 2 3 6 4, .pent 1 2 6 3 4, .pent 1 3 2 6 4, .pent 1 3
    6 2 4, .pent 1 4 2 3 6, .pent 1 4 3 2 6, .pent 1 2 3 7 4, .pent 1 2 7 3 4, .pent 1 3 2 7 4,
    .pent 1 3 7 2 4, .pent 1 4 2 3 7, .pent 1 4 3 2 7, .pent 1 2 3 8 4, .pent 1 2 8 3 4, .pent 1 3
    2 8 4, .pent 1 3 8 2 4, .pent 1 4 2 3 8, .pent 1 4 3 2 8, .pent 1 2 5 6 4, .pent 1 2 6 5 4,
    .pent 1 4 2 5 6, .pent 1 4 2 6 5, .pent 1 4 5 2 6, .pent 1 4 6 2 5, .pent 1 2 5 7 4, .pent 1 2
    7 5 4, .pent 1 4 2 5 7, .pent 1 4 2 7 5, .pent 1 4 5 2 7, .pent 1 4 7 2 5, .pent 1 2 5 8 4,
    .pent 1 2 8 5 4, .pent 1 4 2 5 8, .pent 1 4 2 8 5, .pent 1 4 5 2 8, .pent 1 4 8 2 5, .pent 1 2
    6 7 4, .pent 1 2 7 6 4, .pent 1 4 2 6 7, .pent 1 4 2 7 6, .pent 1 4 6 2 7, .pent 1 4 7 2 6,
    .pent 1 2 6 8 4, .pent 1 2 8 6 4, .pent 1 4 2 6 8, .pent 1 4 2 8 6, .pent 1 4 6 2 8, .pent 1 4
    8 2 6, .pent 1 2 7 8 4, .pent 1 2 8 7 4, .pent 1 4 2 7 8, .pent 1 4 2 8 7, .pent 1 4 7 2 8,
    .pent 1 4 8 2 7, .pent 1 3 5 6 4, .pent 1 3 6 5 4, .pent 1 4 3 5 6, .pent 1 4 3 6 5, .pent 1 4
    5 3 6, .pent 1 4 6 3 5, .pent 1 3 5 7 4, .pent 1 3 7 5 4, .pent 1 4 3 5 7, .pent 1 4 3 7 5,
    .pent 1 4 5 3 7, .pent 1 4 7 3 5, .pent 1 3 5 8 4, .pent 1 3 8 5 4, .pent 1 4 3 5 8, .pent 1 4
    3 8 5, .pent 1 4 5 3 8, .pent 1 4 8 3 5, .pent 1 3 6 7 4, .pent 1 3 7 6 4, .pent 1 4 3 6 7,
    .pent 1 4 3 7 6, .pent 1 4 6 3 7, .pent 1 4 7 3 6, .pent 1 3 6 8 4, .pent 1 3 8 6 4, .pent 1 4
    3 6 8, .pent 1 4 3 8 6, .pent 1 4 6 3 8, .pent 1 4 8 3 6, .pent 1 3 7 8 4, .pent 1 3 8 7 4,
    .pent 1 4 3 7 8, .pent 1 4 3 8 7, .pent 1 4 7 3 8, .pent 1 4 8 3 7, .pent 1 4 5 6 7, .pent 1 4
    5 7 6, .pent 1 4 6 5 7, .pent 1 4 6 7 5, .pent 1 4 7 5 6, .pent 1 4 7 6 5, .pent 1 4 5 6 8,
    .pent 1 4 5 8 6, .pent 1 4 6 5 8, .pent 1 4 6 8 5, .pent 1 4 8 5 6, .pent 1 4 8 6 5, .pent 1 4
    5 7 8, .pent 1 4 5 8 7, .pent 1 4 7 5 8, .pent 1 4 7 8 5, .pent 1 4 8 5 7, .pent 1 4 8 7 5,
    .pent 1 4 6 7 8, .pent 1 4 6 8 7, .pent 1 4 7 6 8, .pent 1 4 7 8 6, .pent 1 4 8 6 7, .pent 1 4
    8 7 6, .star 1 0 2 3 4, .star 1 0 2 4 5, .star 1 0 2 4 6, .star 1 0 2 4 7, .star 1 0 2 4 8,
    .star 1 0 3 4 5, .star 1 0 3 4 6, .star 1 0 3 4 7, .star 1 0 3 4 8, .star 1 0 4 5 6, .star 1 0
    4 5 7, .star 1 0 4 5 8, .star 1 0 4 6 7, .star 1 0 4 6 8, .star 1 0 4 7 8, .star 1 2 3 4 5,
    .star 1 2 3 4 6, .star 1 2 3 4 7, .star 1 2 3 4 8, .star 1 2 4 5 6, .star 1 2 4 5 7, .star 1 2
    4 5 8, .star 1 2 4 6 7, .star 1 2 4 6 8, .star 1 2 4 7 8, .star 1 3 4 5 6, .star 1 3 4 5 7,
    .star 1 3 4 5 8, .star 1 3 4 6 7, .star 1 3 4 6 8, .star 1 3 4 7 8, .star 1 4 5 6 7, .star 1 4
    5 6 8, .star 1 4 5 7 8, .star 1 4 6 7 8, .star 4 0 1 2 3, .star 4 0 1 2 5, .star 4 0 1 2 6,
    .star 4 0 1 2 7, .star 4 0 1 2 8, .star 4 0 1 3 5, .star 4 0 1 3 6, .star 4 0 1 3 7, .star 4 0
    1 3 8, .star 4 0 1 5 6, .star 4 0 1 5 7, .star 4 0 1 5 8, .star 4 0 1 6 7, .star 4 0 1 6 8,
    .star 4 0 1 7 8, .star 4 1 2 3 5, .star 4 1 2 3 6, .star 4 1 2 3 7, .star 4 1 2 3 8, .star 4 1
    2 5 6, .star 4 1 2 5 7, .star 4 1 2 5 8, .star 4 1 2 6 7, .star 4 1 2 6 8, .star 4 1 2 7 8,
    .star 4 1 3 5 6, .star 4 1 3 5 7, .star 4 1 3 5 8, .star 4 1 3 6 7, .star 4 1 3 6 8, .star 4 1
    3 7 8, .star 4 1 5 6 7, .star 4 1 5 6 8, .star 4 1 5 7 8, .star 4 1 6 7 8],
  [.tri 0 2 4, .tri 1 2 4, .tri 2 3 4, .tri 2 4 5, .tri 2 4 6, .tri 2 4 7, .tri 2 4 8, .pent 0 1 2
    4 3, .pent 0 1 3 2 4, .pent 0 1 3 4 2, .pent 0 1 4 2 3, .pent 0 2 4 1 3, .pent 0 3 1 2 4,
    .pent 0 1 2 4 5, .pent 0 1 4 2 5, .pent 0 1 5 2 4, .pent 0 1 5 4 2, .pent 0 2 4 1 5, .pent 0 4
    2 1 5, .pent 0 1 2 4 6, .pent 0 1 4 2 6, .pent 0 1 6 2 4, .pent 0 1 6 4 2, .pent 0 2 4 1 6,
    .pent 0 4 2 1 6, .pent 0 1 2 4 7, .pent 0 1 4 2 7, .pent 0 1 7 2 4, .pent 0 1 7 4 2, .pent 0 2
    4 1 7, .pent 0 4 2 1 7, .pent 0 1 2 4 8, .pent 0 1 4 2 8, .pent 0 1 8 2 4, .pent 0 1 8 4 2,
    .pent 0 2 4 1 8, .pent 0 4 2 1 8, .pent 0 2 4 3 5, .pent 0 2 4 5 3, .pent 0 3 2 4 5, .pent 0 3
    4 2 5, .pent 0 3 5 2 4, .pent 0 4 2 3 5, .pent 0 2 4 3 6, .pent 0 2 4 6 3, .pent 0 3 2 4 6,
    .pent 0 3 4 2 6, .pent 0 3 6 2 4, .pent 0 4 2 3 6, .pent 0 2 4 3 7, .pent 0 2 4 7 3, .pent 0 3
    2 4 7, .pent 0 3 4 2 7, .pent 0 3 7 2 4, .pent 0 4 2 3 7, .pent 0 2 4 3 8, .pent 0 2 4 8 3,
    .pent 0 3 2 4 8, .pent 0 3 4 2 8, .pent 0 3 8 2 4, .pent 0 4 2 3 8, .pent 0 2 4 5 6, .pent 0 2
    4 6 5, .pent 0 4 2 5 6, .pent 0 4 2 6 5, .pent 0 5 2 4 6, .pent 0 5 4 2 6, .pent 0 2 4 5 7,
    .pent 0 2 4 7 5, .pent 0 4 2 5 7, .pent 0 4 2 7 5, .pent 0 5 2 4 7, .pent 0 5 4 2 7, .pent 0 2
    4 5 8, .pent 0 2 4 8 5, .pent 0 4 2 5 8, .pent 0 4 2 8 5, .pent 0 5 2 4 8, .pent 0 5 4 2 8,
    .pent 0 2 4 6 7, .pent 0 2 4 7 6, .pent 0 4 2 6 7, .pent 0 4 2 7 6, .pent 0 6 2 4 7, .pent 0 6
    4 2 7, .pent 0 2 4 6 8, .pent 0 2 4 8 6, .pent 0 4 2 6 8, .pent 0 4 2 8 6, .pent 0 6 2 4 8,
    .pent 0 6 4 2 8, .pent 0 2 4 7 8, .pent 0 2 4 8 7, .pent 0 4 2 7 8, .pent 0 4 2 8 7, .pent 0 7
    2 4 8, .pent 0 7 4 2 8, .pent 1 2 4 3 5, .pent 1 2 4 5 3, .pent 1 3 2 4 5, .pent 1 3 4 2 5,
    .pent 1 3 5 2 4, .pent 1 4 2 3 5, .pent 1 2 4 3 6, .pent 1 2 4 6 3, .pent 1 3 2 4 6, .pent 1 3
    4 2 6, .pent 1 3 6 2 4, .pent 1 4 2 3 6, .pent 1 2 4 3 7, .pent 1 2 4 7 3, .pent 1 3 2 4 7,
    .pent 1 3 4 2 7, .pent 1 3 7 2 4, .pent 1 4 2 3 7, .pent 1 2 4 3 8, .pent 1 2 4 8 3, .pent 1 3
    2 4 8, .pent 1 3 4 2 8, .pent 1 3 8 2 4, .pent 1 4 2 3 8, .pent 1 2 4 5 6, .pent 1 2 4 6 5,
    .pent 1 4 2 5 6, .pent 1 4 2 6 5, .pent 1 5 2 4 6, .pent 1 5 4 2 6, .pent 1 2 4 5 7, .pent 1 2
    4 7 5, .pent 1 4 2 5 7, .pent 1 4 2 7 5, .pent 1 5 2 4 7, .pent 1 5 4 2 7, .pent 1 2 4 5 8,
    .pent 1 2 4 8 5, .pent 1 4 2 5 8, .pent 1 4 2 8 5, .pent 1 5 2 4 8, .pent 1 5 4 2 8, .pent 1 2
    4 6 7, .pent 1 2 4 7 6, .pent 1 4 2 6 7, .pent 1 4 2 7 6, .pent 1 6 2 4 7, .pent 1 6 4 2 7,
    .pent 1 2 4 6 8, .pent 1 2 4 8 6, .pent 1 4 2 6 8, .pent 1 4 2 8 6, .pent 1 6 2 4 8, .pent 1 6
    4 2 8, .pent 1 2 4 7 8, .pent 1 2 4 8 7, .pent 1 4 2 7 8, .pent 1 4 2 8 7, .pent 1 7 2 4 8,
    .pent 1 7 4 2 8, .pent 2 3 5 6 4, .pent 2 3 6 5 4, .pent 2 4 3 5 6, .pent 2 4 3 6 5, .pent 2 4
    5 3 6, .pent 2 4 6 3 5, .pent 2 3 5 7 4, .pent 2 3 7 5 4, .pent 2 4 3 5 7, .pent 2 4 3 7 5,
    .pent 2 4 5 3 7, .pent 2 4 7 3 5, .pent 2 3 5 8 4, .pent 2 3 8 5 4, .pent 2 4 3 5 8, .pent 2 4
    3 8 5, .pent 2 4 5 3 8, .pent 2 4 8 3 5, .pent 2 3 6 7 4, .pent 2 3 7 6 4, .pent 2 4 3 6 7,
    .pent 2 4 3 7 6, .pent 2 4 6 3 7, .pent 2 4 7 3 6, .pent 2 3 6 8 4, .pent 2 3 8 6 4, .pent 2 4
    3 6 8, .pent 2 4 3 8 6, .pent 2 4 6 3 8, .pent 2 4 8 3 6, .pent 2 3 7 8 4, .pent 2 3 8 7 4,
    .pent 2 4 3 7 8, .pent 2 4 3 8 7, .pent 2 4 7 3 8, .pent 2 4 8 3 7, .pent 2 4 5 6 7, .pent 2 4
    5 7 6, .pent 2 4 6 5 7, .pent 2 4 6 7 5, .pent 2 4 7 5 6, .pent 2 4 7 6 5, .pent 2 4 5 6 8,
    .pent 2 4 5 8 6, .pent 2 4 6 5 8, .pent 2 4 6 8 5, .pent 2 4 8 5 6, .pent 2 4 8 6 5, .pent 2 4
    5 7 8, .pent 2 4 5 8 7, .pent 2 4 7 5 8, .pent 2 4 7 8 5, .pent 2 4 8 5 7, .pent 2 4 8 7 5,
    .pent 2 4 6 7 8, .pent 2 4 6 8 7, .pent 2 4 7 6 8, .pent 2 4 7 8 6, .pent 2 4 8 6 7, .pent 2 4
    8 7 6, .star 2 0 1 3 4, .star 2 0 1 4 5, .star 2 0 1 4 6, .star 2 0 1 4 7, .star 2 0 1 4 8,
    .star 2 0 3 4 5, .star 2 0 3 4 6, .star 2 0 3 4 7, .star 2 0 3 4 8, .star 2 0 4 5 6, .star 2 0
    4 5 7, .star 2 0 4 5 8, .star 2 0 4 6 7, .star 2 0 4 6 8, .star 2 0 4 7 8, .star 2 1 3 4 5,
    .star 2 1 3 4 6, .star 2 1 3 4 7, .star 2 1 3 4 8, .star 2 1 4 5 6, .star 2 1 4 5 7, .star 2 1
    4 5 8, .star 2 1 4 6 7, .star 2 1 4 6 8, .star 2 1 4 7 8, .star 2 3 4 5 6, .star 2 3 4 5 7,
    .star 2 3 4 5 8, .star 2 3 4 6 7, .star 2 3 4 6 8, .star 2 3 4 7 8, .star 2 4 5 6 7, .star 2 4
    5 6 8, .star 2 4 5 7 8, .star 2 4 6 7 8, .star 4 0 1 2 3, .star 4 0 1 2 5, .star 4 0 1 2 6,
    .star 4 0 1 2 7, .star 4 0 1 2 8, .star 4 0 2 3 5, .star 4 0 2 3 6, .star 4 0 2 3 7, .star 4 0
    2 3 8, .star 4 0 2 5 6, .star 4 0 2 5 7, .star 4 0 2 5 8, .star 4 0 2 6 7, .star 4 0 2 6 8,
    .star 4 0 2 7 8, .star 4 1 2 3 5, .star 4 1 2 3 6, .star 4 1 2 3 7, .star 4 1 2 3 8, .star 4 1
    2 5 6, .star 4 1 2 5 7, .star 4 1 2 5 8, .star 4 1 2 6 7, .star 4 1 2 6 8, .star 4 1 2 7 8,
    .star 4 2 3 5 6, .star 4 2 3 5 7, .star 4 2 3 5 8, .star 4 2 3 6 7, .star 4 2 3 6 8, .star 4 2
    3 7 8, .star 4 2 5 6 7, .star 4 2 5 6 8, .star 4 2 5 7 8, .star 4 2 6 7 8],
  [.tri 0 3 4, .tri 1 3 4, .tri 2 3 4, .tri 3 4 5, .tri 3 4 6, .tri 3 4 7, .tri 3 4 8, .pent 0 1 2
    3 4, .pent 0 1 2 4 3, .pent 0 1 3 4 2, .pent 0 1 4 3 2, .pent 0 2 1 3 4, .pent 0 2 1 4 3,
    .pent 0 1 3 4 5, .pent 0 1 4 3 5, .pent 0 1 5 3 4, .pent 0 1 5 4 3, .pent 0 3 4 1 5, .pent 0 4
    3 1 5, .pent 0 1 3 4 6, .pent 0 1 4 3 6, .pent 0 1 6 3 4, .pent 0 1 6 4 3, .pent 0 3 4 1 6,
    .pent 0 4 3 1 6, .pent 0 1 3 4 7, .pent 0 1 4 3 7, .pent 0 1 7 3 4, .pent 0 1 7 4 3, .pent 0 3
    4 1 7, .pent 0 4 3 1 7, .pent 0 1 3 4 8, .pent 0 1 4 3 8, .pent 0 1 8 3 4, .pent 0 1 8 4 3,
    .pent 0 3 4 1 8, .pent 0 4 3 1 8, .pent 0 2 3 4 5, .pent 0 2 4 3 5, .pent 0 2 5 3 4, .pent 0 2
    5 4 3, .pent 0 3 4 2 5, .pent 0 4 3 2 5, .pent 0 2 3 4 6, .pent 0 2 4 3 6, .pent 0 2 6 3 4,
    .pent 0 2 6 4 3, .pent 0 3 4 2 6, .pent 0 4 3 2 6, .pent 0 2 3 4 7, .pent 0 2 4 3 7, .pent 0 2
    7 3 4, .pent 0 2 7 4 3, .pent 0 3 4 2 7, .pent 0 4 3 2 7, .pent 0 2 3 4 8, .pent 0 2 4 3 8,
    .pent 0 2 8 3 4, .pent 0 2 8 4 3, .pent 0 3 4 2 8, .pent 0 4 3 2 8, .pent 0 3 4 5 6, .pent 0 3
    4 6 5, .pent 0 4 3 5 6, .pent 0 4 3 6 5, .pent 0 5 3 4 6, .pent 0 5 4 3 6, .pent 0 3 4 5 7,
    .pent 0 3 4 7 5, .pent 0 4 3 5 7, .pent 0 4 3 7 5, .pent 0 5 3 4 7, .pent 0 5 4 3 7, .pent 0 3
    4 5 8, .pent 0 3 4 8 5, .pent 0 4 3 5 8, .pent 0 4 3 8 5, .pent 0 5 3 4 8, .pent 0 5 4 3 8,
    .pent 0 3 4 6 7, .pent 0 3 4 7 6, .pent 0 4 3 6 7, .pent 0 4 3 7 6, .pent 0 6 3 4 7, .pent 0 6
    4 3 7, .pent 0 3 4 6 8, .pent 0 3 4 8 6, .pent 0 4 3 6 8, .pent 0 4 3 8 6, .pent 0 6 3 4 8,
    .pent 0 6 4 3 8, .pent 0 3 4 7 8, .pent 0 3 4 8 7, .pent 0 4 3 7 8, .pent 0 4 3 8 7, .pent 0 7
    3 4 8, .pent 0 7 4 3 8, .pent 1 2 3 4 5, .pent 1 2 4 3 5, .pent 1 2 5 3 4, .pent 1 2 5 4 3,
    .pent 1 3 4 2 5, .pent 1 4 3 2 5, .pent 1 2 3 4 6, .pent 1 2 4 3 6, .pent 1 2 6 3 4, .pent 1 2
    6 4 3, .pent 1 3 4 2 6, .pent 1 4 3 2 6, .pent 1 2 3 4 7, .pent 1 2 4 3 7, .pent 1 2 7 3 4,
    .pent 1 2 7 4 3, .pent 1 3 4 2 7, .pent 1 4 3 2 7, .pent 1 2 3 4 8, .pent 1 2 4 3 8, .pent 1 2
    8 3 4, .pent 1 2 8 4 3, .pent 1 3 4 2 8, .pent 1 4 3 2 8, .pent 1 3 4 5 6, .pent 1 3 4 6 5,
    .pent 1 4 3 5 6, .pent 1 4 3 6 5, .pent 1 5 3 4 6, .pent 1 5 4 3 6, .pent 1 3 4 5 7, .pent 1 3
    4 7 5, .pent 1 4 3 5 7, .pent 1 4 3 7 5, .pent 1 5 3 4 7, .pent 1 5 4 3 7, .pent 1 3 4 5 8,
    .pent 1 3 4 8 5, .pent 1 4 3 5 8, .pent 1 4 3 8 5, .pent 1 5 3 4 8, .pent 1 5 4 3 8, .pent 1 3
    4 6 7, .pent 1 3 4 7 6, .pent 1 4 3 6 7, .pent 1 4 3 7 6, .pent 1 6 3 4 7, .pent 1 6 4 3 7,
    .pent 1 3 4 6 8, .pent 1 3 4 8 6, .pent 1 4 3 6 8, .pent 1 4 3 8 6, .pent 1 6 3 4 8, .pent 1 6
    4 3 8, .pent 1 3 4 7 8, .pent 1 3 4 8 7, .pent 1 4 3 7 8, .pent 1 4 3 8 7, .pent 1 7 3 4 8,
    .pent 1 7 4 3 8, .pent 2 3 4 5 6, .pent 2 3 4 6 5, .pent 2 4 3 5 6, .pent 2 4 3 6 5, .pent 2 5
    3 4 6, .pent 2 5 4 3 6, .pent 2 3 4 5 7, .pent 2 3 4 7 5, .pent 2 4 3 5 7, .pent 2 4 3 7 5,
    .pent 2 5 3 4 7, .pent 2 5 4 3 7, .pent 2 3 4 5 8, .pent 2 3 4 8 5, .pent 2 4 3 5 8, .pent 2 4
    3 8 5, .pent 2 5 3 4 8, .pent 2 5 4 3 8, .pent 2 3 4 6 7, .pent 2 3 4 7 6, .pent 2 4 3 6 7,
    .pent 2 4 3 7 6, .pent 2 6 3 4 7, .pent 2 6 4 3 7, .pent 2 3 4 6 8, .pent 2 3 4 8 6, .pent 2 4
    3 6 8, .pent 2 4 3 8 6, .pent 2 6 3 4 8, .pent 2 6 4 3 8, .pent 2 3 4 7 8, .pent 2 3 4 8 7,
    .pent 2 4 3 7 8, .pent 2 4 3 8 7, .pent 2 7 3 4 8, .pent 2 7 4 3 8, .pent 3 4 5 6 7, .pent 3 4
    5 7 6, .pent 3 4 6 5 7, .pent 3 4 6 7 5, .pent 3 4 7 5 6, .pent 3 4 7 6 5, .pent 3 4 5 6 8,
    .pent 3 4 5 8 6, .pent 3 4 6 5 8, .pent 3 4 6 8 5, .pent 3 4 8 5 6, .pent 3 4 8 6 5, .pent 3 4
    5 7 8, .pent 3 4 5 8 7, .pent 3 4 7 5 8, .pent 3 4 7 8 5, .pent 3 4 8 5 7, .pent 3 4 8 7 5,
    .pent 3 4 6 7 8, .pent 3 4 6 8 7, .pent 3 4 7 6 8, .pent 3 4 7 8 6, .pent 3 4 8 6 7, .pent 3 4
    8 7 6, .star 3 0 1 2 4, .star 3 0 1 4 5, .star 3 0 1 4 6, .star 3 0 1 4 7, .star 3 0 1 4 8,
    .star 3 0 2 4 5, .star 3 0 2 4 6, .star 3 0 2 4 7, .star 3 0 2 4 8, .star 3 0 4 5 6, .star 3 0
    4 5 7, .star 3 0 4 5 8, .star 3 0 4 6 7, .star 3 0 4 6 8, .star 3 0 4 7 8, .star 3 1 2 4 5,
    .star 3 1 2 4 6, .star 3 1 2 4 7, .star 3 1 2 4 8, .star 3 1 4 5 6, .star 3 1 4 5 7, .star 3 1
    4 5 8, .star 3 1 4 6 7, .star 3 1 4 6 8, .star 3 1 4 7 8, .star 3 2 4 5 6, .star 3 2 4 5 7,
    .star 3 2 4 5 8, .star 3 2 4 6 7, .star 3 2 4 6 8, .star 3 2 4 7 8, .star 3 4 5 6 7, .star 3 4
    5 6 8, .star 3 4 5 7 8, .star 3 4 6 7 8, .star 4 0 1 2 3, .star 4 0 1 3 5, .star 4 0 1 3 6,
    .star 4 0 1 3 7, .star 4 0 1 3 8, .star 4 0 2 3 5, .star 4 0 2 3 6, .star 4 0 2 3 7, .star 4 0
    2 3 8, .star 4 0 3 5 6, .star 4 0 3 5 7, .star 4 0 3 5 8, .star 4 0 3 6 7, .star 4 0 3 6 8,
    .star 4 0 3 7 8, .star 4 1 2 3 5, .star 4 1 2 3 6, .star 4 1 2 3 7, .star 4 1 2 3 8, .star 4 1
    3 5 6, .star 4 1 3 5 7, .star 4 1 3 5 8, .star 4 1 3 6 7, .star 4 1 3 6 8, .star 4 1 3 7 8,
    .star 4 2 3 5 6, .star 4 2 3 5 7, .star 4 2 3 5 8, .star 4 2 3 6 7, .star 4 2 3 6 8, .star 4 2
    3 7 8, .star 4 3 5 6 7, .star 4 3 5 6 8, .star 4 3 5 7 8, .star 4 3 6 7 8],
  [.tri 0 1 5, .tri 0 2 5, .tri 0 3 5, .tri 0 4 5, .tri 0 5 6, .tri 0 5 7, .tri 0 5 8, .pent 0 1 2
    3 5, .pent 0 1 3 2 5, .pent 0 2 1 3 5, .pent 0 2 3 1 5, .pent 0 3 1 2 5, .pent 0 3 2 1 5,
    .pent 0 1 2 4 5, .pent 0 1 4 2 5, .pent 0 2 1 4 5, .pent 0 2 4 1 5, .pent 0 4 1 2 5, .pent 0 4
    2 1 5, .pent 0 1 2 6 5, .pent 0 1 6 2 5, .pent 0 2 1 6 5, .pent 0 2 6 1 5, .pent 0 5 1 2 6,
    .pent 0 5 2 1 6, .pent 0 1 2 7 5, .pent 0 1 7 2 5, .pent 0 2 1 7 5, .pent 0 2 7 1 5, .pent 0 5
    1 2 7, .pent 0 5 2 1 7, .pent 0 1 2 8 5, .pent 0 1 8 2 5, .pent 0 2 1 8 5, .pent 0 2 8 1 5,
    .pent 0 5 1 2 8, .pent 0 5 2 1 8, .pent 0 1 3 4 5, .pent 0 1 4 3 5, .pent 0 3 1 4 5, .pent 0 3
    4 1 5, .pent 0 4 1 3 5, .pent 0 4 3 1 5, .pent 0 1 3 6 5, .pent 0 1 6 3 5, .pent 0 3 1 6 5,
    .pent 0 3 6 1 5, .pent 0 5 1 3 6, .pent 0 5 3 1 6, .pent 0 1 3 7 5, .pent 0 1 7 3 5, .pent 0 3
    1 7 5, .pent 0 3 7 1 5, .pent 0 5 1 3 7, .pent 0 5 3 1 7, .pent 0 1 3 8 5, .pent 0 1 8 3 5,
    .pent 0 3 1 8 5, .pent 0 3 8 1 5, .pent 0 5 1 3 8, .pent 0 5 3 1 8, .pent 0 1 4 6 5, .pent 0 1
    6 4 5, .pent 0 4 1 6 5, .pent 0 4 6 1 5, .pent 0 5 1 4 6, .pent 0 5 4 1 6, .pent 0 1 4 7 5,
    .pent 0 1 7 4 5, .pent 0 4 1 7 5, .pent 0 4 7 1 5, .pent 0 5 1 4 7, .pent 0 5 4 1 7, .pent 0 1
    4 8 5, .pent 0 1 8 4 5, .pent 0 4 1 8 5, .pent 0 4 8 1 5, .pent 0 5 1 4 8, .pent 0 5 4 1 8,
    .pent 0 1 6 7 5, .pent 0 1 7 6 5, .pent 0 5 1 6 7, .pent 0 5 1 7 6, .pent 0 5 6 1 7, .pent 0 5
    7 1 6, .pent 0 1 6 8 5, .pent 0 1 8 6 5, .pent 0 5 1 6 8, .pent 0 5 1 8 6, .pent 0 5 6 1 8,
    .pent 0 5 8 1 6, .pent 0 1 7 8 5, .pent 0 1 8 7 5, .pent 0 5 1 7 8, .pent 0 5 1 8 7, .pent 0 5
    7 1 8, .pent 0 5 8 1 7, .pent 0 2 3 4 5, .pent 0 2 4 3 5, .pent 0 3 2 4 5, .pent 0 3 4 2 5,
    .pent 0 4 2 3 5, .pent 0 4 3 2 5, .pent 0 2 3 6 5, .pent 0 2 6 3 5, .pent 0 3 2 6 5, .pent 0 3
    6 2 5, .pent 0 5 2 3 6, .pent 0 5 3 2 6, .pent 0 2 3 7 5, .pent 0 2 7 3 5, .pent 0 3 2 7 5,
    .pent 0 3 7 2 5, .pent 0 5 2 3 7, .pent 0 5 3 2 7, .pent 0 2 3 8 5, .pent 0 2 8 3 5, .pent 0 3
    2 8 5, .pent 0 3 8 2 5, .pent 0 5 2 3 8, .pent 0 5 3 2 8, .pent 0 2 4 6 5, .pent 0 2 6 4 5,
    .pent 0 4 2 6 5, .pent 0 4 6 2 5, .pent 0 5 2 4 6, .pent 0 5 4 2 6, .pent 0 2 4 7 5, .pent 0 2
    7 4 5, .pent 0 4 2 7 5, .pent 0 4 7 2 5, .pent 0 5 2 4 7, .pent 0 5 4 2 7, .pent 0 2 4 8 5,
    .pent 0 2 8 4 5, .pent 0 4 2 8 5, .pent 0 4 8 2 5, .pent 0 5 2 4 8, .pent 0 5 4 2 8, .pent 0 2
    6 7 5, .pent 0 2 7 6 5, .pent 0 5 2 6 7, .pent 0 5 2 7 6, .pent 0 5 6 2 7, .pent 0 5 7 2 6,
    .pent 0 2 6 8 5, .pent 0 2 8 6 5, .pent 0 5 2 6 8, .pent 0 5 2 8 6, .pent 0 5 6 2 8, .pent 0 5
    8 2 6, .pent 0 2 7 8 5, .pent 0 2 8 7 5, .pent 0 5 2 7 8, .pent 0 5 2 8 7, .pent 0 5 7 2 8,
    .pent 0 5 8 2 7, .pent 0 3 4 6 5, .pent 0 3 6 4 5, .pent 0 4 3 6 5, .pent 0 4 6 3 5, .pent 0 5
    3 4 6, .pent 0 5 4 3 6, .pent 0 3 4 7 5, .pent 0 3 7 4 5, .pent 0 4 3 7 5, .pent 0 4 7 3 5,
    .pent 0 5 3 4 7, .pent 0 5 4 3 7, .pent 0 3 4 8 5, .pent 0 3 8 4 5, .pent 0 4 3 8 5, .pent 0 4
    8 3 5, .pent 0 5 3 4 8, .pent 0 5 4 3 8, .pent 0 3 6 7 5, .pent 0 3 7 6 5, .pent 0 5 3 6 7,
    .pent 0 5 3 7 6, .pent 0 5 6 3 7, .pent 0 5 7 3 6, .pent 0 3 6 8 5, .pent 0 3 8 6 5, .pent 0 5
    3 6 8, .pent 0 5 3 8 6, .pent 0 5 6 3 8, .pent 0 5 8 3 6, .pent 0 3 7 8 5, .pent 0 3 8 7 5,
    .pent 0 5 3 7 8, .pent 0 5 3 8 7, .pent 0 5 7 3 8, .pent 0 5 8 3 7, .pent 0 4 6 7 5, .pent 0 4
    7 6 5, .pent 0 5 4 6 7, .pent 0 5 4 7 6, .pent 0 5 6 4 7, .pent 0 5 7 4 6, .pent 0 4 6 8 5,
    .pent 0 4 8 6 5, .pent 0 5 4 6 8, .pent 0 5 4 8 6, .pent 0 5 6 4 8, .pent 0 5 8 4 6, .pent 0 4
    7 8 5, .pent 0 4 8 7 5, .pent 0 5 4 7 8, .pent 0 5 4 8 7, .pent 0 5 7 4 8, .pent 0 5 8 4 7,
    .pent 0 5 6 7 8, .pent 0 5 6 8 7, .pent 0 5 7 6 8, .pent 0 5 7 8 6, .pent 0 5 8 6 7, .pent 0 5
    8 7 6, .star 0 1 2 3 5, .star 0 1 2 4 5, .star 0 1 2 5 6, .star 0 1 2 5 7, .star 0 1 2 5 8,
    .star 0 1 3 4 5, .star 0 1 3 5 6, .star 0 1 3 5 7, .star 0 1 3 5 8, .star 0 1 4 5 6, .star 0 1
    4 5 7, .star 0 1 4 5 8, .star 0 1 5 6 7, .star 0 1 5 6 8, .star 0 1 5 7 8, .star 0 2 3 4 5,
    .star 0 2 3 5 6, .star 0 2 3 5 7, .star 0 2 3 5 8, .star 0 2 4 5 6, .star 0 2 4 5 7, .star 0 2
    4 5 8, .star 0 2 5 6 7, .star 0 2 5 6 8, .star 0 2 5 7 8, .star 0 3 4 5 6, .star 0 3 4 5 7,
    .star 0 3 4 5 8, .star 0 3 5 6 7, .star 0 3 5 6 8, .star 0 3 5 7 8, .star 0 4 5 6 7, .star 0 4
    5 6 8, .star 0 4 5 7 8, .star 0 5 6 7 8, .star 5 0 1 2 3, .star 5 0 1 2 4, .star 5 0 1 2 6,
    .star 5 0 1 2 7, .star 5 0 1 2 8, .star 5 0 1 3 4, .star 5 0 1 3 6, .star 5 0 1 3 7, .star 5 0
    1 3 8, .star 5 0 1 4 6, .star 5 0 1 4 7, .star 5 0 1 4 8, .star 5 0 1 6 7, .star 5 0 1 6 8,
    .star 5 0 1 7 8, .star 5 0 2 3 4, .star 5 0 2 3 6, .star 5 0 2 3 7, .star 5 0 2 3 8, .star 5 0
    2 4 6, .star 5 0 2 4 7, .star 5 0 2 4 8, .star 5 0 2 6 7, .star 5 0 2 6 8, .star 5 0 2 7 8,
    .star 5 0 3 4 6, .star 5 0 3 4 7, .star 5 0 3 4 8, .star 5 0 3 6 7, .star 5 0 3 6 8, .star 5 0
    3 7 8, .star 5 0 4 6 7, .star 5 0 4 6 8, .star 5 0 4 7 8, .star 5 0 6 7 8],
  [.tri 0 1 5, .tri 1 2 5, .tri 1 3 5, .tri 1 4 5, .tri 1 5 6, .tri 1 5 7, .tri 1 5 8, .pent 0 1 5
    2 3, .pent 0 1 5 3 2, .pent 0 2 1 5 3, .pent 0 2 3 1 5, .pent 0 2 5 1 3, .pent 0 3 2 1 5,
    .pent 0 1 5 2 4, .pent 0 1 5 4 2, .pent 0 2 1 5 4, .pent 0 2 4 1 5, .pent 0 2 5 1 4, .pent 0 4
    2 1 5, .pent 0 1 5 2 6, .pent 0 1 5 6 2, .pent 0 2 1 5 6, .pent 0 2 5 1 6, .pent 0 2 6 1 5,
    .pent 0 5 1 2 6, .pent 0 1 5 2 7, .pent 0 1 5 7 2, .pent 0 2 1 5 7, .pent 0 2 5 1 7, .pent 0 2
    7 1 5, .pent 0 5 1 2 7, .pent 0 1 5 2 8, .pent 0 1 5 8 2, .pent 0 2 1 5 8, .pent 0 2 5 1 8,
    .pent 0 2 8 1 5, .pent 0 5 1 2 8, .pent 0 1 5 3 4, .pent 0 1 5 4 3, .pent 0 3 1 5 4, .pent 0 3
    4 1 5, .pent 0 3 5 1 4, .pent 0 4 3 1 5, .pent 0 1 5 3 6, .pent 0 1 5 6 3, .pent 0 3 1 5 6,
    .pent 0 3 5 1 6, .pent 0 3 6 1 5, .pent 0 5 1 3 6, .pent 0 1 5 3 7, .pent 0 1 5 7 3, .pent 0 3
    1 5 7, .pent 0 3 5 1 7, .pent 0 3 7 1 5, .pent 0 5 1 3 7, .pent 0 1 5 3 8, .pent 0 1 5 8 3,
    .pent 0 3 1 5 8, .pent 0 3 5 1 8, .pent 0 3 8 1 5, .pent 0 5 1 3 8, .pent 0 1 5 4 6, .pent 0 1
    5 6 4, .pent 0 4 1 5 6, .pent 0 4 5 1 6, .pent 0 4 6 1 5, .pent 0 5 1 4 6, .pent 0 1 5 4 7,
    .pent 0 1 5 7 4, .pent 0 4 1 5 7, .pent 0 4 5 1 7, .pent 0 4 7 1 5, .pent 0 5 1 4 7, .pent 0 1
    5 4 8, .pent 0 1 5 8 4, .pent 0 4 1 5 8, .pent 0 4 5 1 8, .pent 0 4 8 1 5, .pent 0 5 1 4 8,
    .pent 0 1 5 6 7, .pent 0 1 5 7 6, .pent 0 5 1 6 7, .pent 0 5 1 7 6, .pent 0 6 1 5 7, .pent 0 6
    5 1 7, .pent 0 1 5 6 8, .pent 0 1 5 8 6, .pent 0 5 1 6 8, .pent 0 5 1 8 6, .pent 0 6 1 5 8,
    .pent 0 6 5 1 8, .pent 0 1 5 7 8, .pent 0 1 5 8 7, .pent 0 5 1 7 8, .pent 0 5 1 8 7, .pent 0 7
    1 5 8, .pent 0 7 5 1 8, .pent 1 2 3 4 5, .pent 1 2 4 3 5, .pent 1 3 2 4 5, .pent 1 3 4 2 5,
    .pent 1 4 2 3 5, .pent 1 4 3 2 5, .pent 1 2 3 6 5, .pent 1 2 6 3 5, .pent 1 3 2 6 5, .pent 1 3
    6 2 5, .pent 1 5 2 3 6, .pent 1 5 3 2 6, .pent 1 2 3 7 5, .pent 1 2 7 3 5, .pent 1 3 2 7 5,
    .pent 1 3 7 2 5, .pent 1 5 2 3 7, .pent 1 5 3 2 7, .pent 1 2 3 8 5, .pent 1 2 8 3 5, .pent 1 3
    2 8 5, .pent 1 3 8 2 5, .pent 1 5 2 3 8, .pent 1 5 3 2 8, .pent 1 2 4 6 5, .pent 1 2 6 4 5,
    .pent 1 4 2 6 5, .pent 1 4 6 2 5, .pent 1 5 2 4 6, .pent 1 5 4 2 6, .pent 1 2 4 7 5, .pent 1 2
    7 4 5, .pent 1 4 2 7 5, .pent 1 4 7 2 5, .pent 1 5 2 4 7, .pent 1 5 4 2 7, .pent 1 2 4 8 5,
    .pent 1 2 8 4 5, .pent 1 4 2 8 5, .pent 1 4 8 2 5, .pent 1 5 2 4 8, .pent 1 5 4 2 8, .pent 1 2
    6 7 5, .pent 1 2 7 6 5, .pent 1 5 2 6 7, .pent 1 5 2 7 6, .pent 1 5 6 2 7, .pent 1 5 7 2 6,
    .pent 1 2 6 8 5, .pent 1 2 8 6 5, .pent 1 5 2 6 8, .pent 1 5 2 8 6, .pent 1 5 6 2 8, .pent 1 5
    8 2 6, .pent 1 2 7 8 5, .pent 1 2 8 7 5, .pent 1 5 2 7 8, .pent 1 5 2 8 7, .pent 1 5 7 2 8,
    .pent 1 5 8 2 7, .pent 1 3 4 6 5, .pent 1 3 6 4 5, .pent 1 4 3 6 5, .pent 1 4 6 3 5, .pent 1 5
    3 4 6, .pent 1 5 4 3 6, .pent 1 3 4 7 5, .pent 1 3 7 4 5, .pent 1 4 3 7 5, .pent 1 4 7 3 5,
    .pent 1 5 3 4 7, .pent 1 5 4 3 7, .pent 1 3 4 8 5, .pent 1 3 8 4 5, .pent 1 4 3 8 5, .pent 1 4
    8 3 5, .pent 1 5 3 4 8, .pent 1 5 4 3 8, .pent 1 3 6 7 5, .pent 1 3 7 6 5, .pent 1 5 3 6 7,
    .pent 1 5 3 7 6, .pent 1 5 6 3 7, .pent 1 5 7 3 6, .pent 1 3 6 8 5, .pent 1 3 8 6 5, .pent 1 5
    3 6 8, .pent 1 5 3 8 6, .pent 1 5 6 3 8, .pent 1 5 8 3 6, .pent 1 3 7 8 5, .pent 1 3 8 7 5,
    .pent 1 5 3 7 8, .pent 1 5 3 8 7, .pent 1 5 7 3 8, .pent 1 5 8 3 7, .pent 1 4 6 7 5, .pent 1 4
    7 6 5, .pent 1 5 4 6 7, .pent 1 5 4 7 6, .pent 1 5 6 4 7, .pent 1 5 7 4 6, .pent 1 4 6 8 5,
    .pent 1 4 8 6 5, .pent 1 5 4 6 8, .pent 1 5 4 8 6, .pent 1 5 6 4 8, .pent 1 5 8 4 6, .pent 1 4
    7 8 5, .pent 1 4 8 7 5, .pent 1 5 4 7 8, .pent 1 5 4 8 7, .pent 1 5 7 4 8, .pent 1 5 8 4 7,
    .pent 1 5 6 7 8, .pent 1 5 6 8 7, .pent 1 5 7 6 8, .pent 1 5 7 8 6, .pent 1 5 8 6 7, .pent 1 5
    8 7 6, .star 1 0 2 3 5, .star 1 0 2 4 5, .star 1 0 2 5 6, .star 1 0 2 5 7, .star 1 0 2 5 8,
    .star 1 0 3 4 5, .star 1 0 3 5 6, .star 1 0 3 5 7, .star 1 0 3 5 8, .star 1 0 4 5 6, .star 1 0
    4 5 7, .star 1 0 4 5 8, .star 1 0 5 6 7, .star 1 0 5 6 8, .star 1 0 5 7 8, .star 1 2 3 4 5,
    .star 1 2 3 5 6, .star 1 2 3 5 7, .star 1 2 3 5 8, .star 1 2 4 5 6, .star 1 2 4 5 7, .star 1 2
    4 5 8, .star 1 2 5 6 7, .star 1 2 5 6 8, .star 1 2 5 7 8, .star 1 3 4 5 6, .star 1 3 4 5 7,
    .star 1 3 4 5 8, .star 1 3 5 6 7, .star 1 3 5 6 8, .star 1 3 5 7 8, .star 1 4 5 6 7, .star 1 4
    5 6 8, .star 1 4 5 7 8, .star 1 5 6 7 8, .star 5 0 1 2 3, .star 5 0 1 2 4, .star 5 0 1 2 6,
    .star 5 0 1 2 7, .star 5 0 1 2 8, .star 5 0 1 3 4, .star 5 0 1 3 6, .star 5 0 1 3 7, .star 5 0
    1 3 8, .star 5 0 1 4 6, .star 5 0 1 4 7, .star 5 0 1 4 8, .star 5 0 1 6 7, .star 5 0 1 6 8,
    .star 5 0 1 7 8, .star 5 1 2 3 4, .star 5 1 2 3 6, .star 5 1 2 3 7, .star 5 1 2 3 8, .star 5 1
    2 4 6, .star 5 1 2 4 7, .star 5 1 2 4 8, .star 5 1 2 6 7, .star 5 1 2 6 8, .star 5 1 2 7 8,
    .star 5 1 3 4 6, .star 5 1 3 4 7, .star 5 1 3 4 8, .star 5 1 3 6 7, .star 5 1 3 6 8, .star 5 1
    3 7 8, .star 5 1 4 6 7, .star 5 1 4 6 8, .star 5 1 4 7 8, .star 5 1 6 7 8],
  [.tri 0 2 5, .tri 1 2 5, .tri 2 3 5, .tri 2 4 5, .tri 2 5 6, .tri 2 5 7, .tri 2 5 8, .pent 0 1 2
    5 3, .pent 0 1 3 2 5, .pent 0 1 3 5 2, .pent 0 1 5 2 3, .pent 0 2 5 1 3, .pent 0 3 1 2 5,
    .pent 0 1 2 5 4, .pent 0 1 4 2 5, .pent 0 1 4 5 2, .pent 0 1 5 2 4, .pent 0 2 5 1 4, .pent 0 4
    1 2 5, .pent 0 1 2 5 6, .pent 0 1 5 2 6, .pent 0 1 6 2 5, .pent 0 1 6 5 2, .pent 0 2 5 1 6,
    .pent 0 5 2 1 6, .pent 0 1 2 5 7, .pent 0 1 5 2 7, .pent 0 1 7 2 5, .pent 0 1 7 5 2, .pent 0 2
    5 1 7, .pent 0 5 2 1 7, .pent 0 1 2 5 8, .pent 0 1 5 2 8, .pent 0 1 8 2 5, .pent 0 1 8 5 2,
    .pent 0 2 5 1 8, .pent 0 5 2 1 8, .pent 0 2 5 3 4, .pent 0 2 5 4 3, .pent 0 3 2 5 4, .pent 0 3
    4 2 5, .pent 0 3 5 2 4, .pent 0 4 3 2 5, .pent 0 2 5 3 6, .pent 0 2 5 6 3, .pent 0 3 2 5 6,
    .pent 0 3 5 2 6, .pent 0 3 6 2 5, .pent 0 5 2 3 6, .pent 0 2 5 3 7, .pent 0 2 5 7 3, .pent 0 3
    2 5 7, .pent 0 3 5 2 7, .pent 0 3 7 2 5, .pent 0 5 2 3 7, .pent 0 2 5 3 8, .pent 0 2 5 8 3,
    .pent 0 3 2 5 8, .pent 0 3 5 2 8, .pent 0 3 8 2 5, .pent 0 5 2 3 8, .pent 0 2 5 4 6, .pent 0 2
    5 6 4, .pent 0 4 2 5 6, .pent 0 4 5 2 6, .pent 0 4 6 2 5, .pent 0 5 2 4 6, .pent 0 2 5 4 7,
    .pent 0 2 5 7 4, .pent 0 4 2 5 7, .pent 0 4 5 2 7, .pent 0 4 7 2 5, .pent 0 5 2 4 7, .pent 0 2
    5 4 8, .pent 0 2 5 8 4, .pent 0 4 2 5 8, .pent 0 4 5 2 8, .pent 0 4 8 2 5, .pent 0 5 2 4 8,
    .pent 0 2 5 6 7, .pent 0 2 5 7 6, .pent 0 5 2 6 7, .pent 0 5 2 7 6, .pent 0 6 2 5 7, .pent 0 6
    5 2 7, .pent 0 2 5 6 8, .pent 0 2 5 8 6, .pent 0 5 2 6 8, .pent 0 5 2 8 6, .pent 0 6 2 5 8,
    .pent 0 6 5 2 8, .pent 0 2 5 7 8, .pent 0 2 5 8 7, .pent 0 5 2 7 8, .pent 0 5 2 8 7, .pent 0 7
    2 5 8, .pent 0 7 5 2 8, .pent 1 2 5 3 4, .pent 1 2 5 4 3, .pent 1 3 2 5 4, .pent 1 3 4 2 5,
    .pent 1 3 5 2 4, .pent 1 4 3 2 5, .pent 1 2 5 3 6, .pent 1 2 5 6 3, .pent 1 3 2 5 6, .pent 1 3
    5 2 6, .pent 1 3 6 2 5, .pent 1 5 2 3 6, .pent 1 2 5 3 7, .pent 1 2 5 7 3, .pent 1 3 2 5 7,
    .pent 1 3 5 2 7, .pent 1 3 7 2 5, .pent 1 5 2 3 7, .pent 1 2 5 3 8, .pent 1 2 5 8 3, .pent 1 3
    2 5 8, .pent 1 3 5 2 8, .pent 1 3 8 2 5, .pent 1 5 2 3 8, .pent 1 2 5 4 6, .pent 1 2 5 6 4,
    .pent 1 4 2 5 6, .pent 1 4 5 2 6, .pent 1 4 6 2 5, .pent 1 5 2 4 6, .pent 1 2 5 4 7, .pent 1 2
    5 7 4, .pent 1 4 2 5 7, .pent 1 4 5 2 7, .pent 1 4 7 2 5, .pent 1 5 2 4 7, .pent 1 2 5 4 8,
    .pent 1 2 5 8 4, .pent 1 4 2 5 8, .pent 1 4 5 2 8, .pent 1 4 8 2 5, .pent 1 5 2 4 8, .pent 1 2
    5 6 7, .pent 1 2 5 7 6, .pent 1 5 2 6 7, .pent 1 5 2 7 6, .pent 1 6 2 5 7, .pent 1 6 5 2 7,
    .pent 1 2 5 6 8, .pent 1 2 5 8 6, .pent 1 5 2 6 8, .pent 1 5 2 8 6, .pent 1 6 2 5 8, .pent 1 6
    5 2 8, .pent 1 2 5 7 8, .pent 1 2 5 8 7, .pent 1 5 2 7 8, .pent 1 5 2 8 7, .pent 1 7 2 5 8,
    .pent 1 7 5 2 8, .pent 2 3 4 6 5, .pent 2 3 6 4 5, .pent 2 4 3 6 5, .pent 2 4 6 3 5, .pent 2 5
    3 4 6, .pent 2 5 4 3 6, .pent 2 3 4 7 5, .pent 2 3 7 4 5, .pent 2 4 3 7 5, .pent 2 4 7 3 5,
    .pent 2 5 3 4 7, .pent 2 5 4 3 7, .pent 2 3 4 8 5, .pent 2 3 8 4 5, .pent 2 4 3 8 5, .pent 2 4
    8 3 5, .pent 2 5 3 4 8, .pent 2 5 4 3 8, .pent 2 3 6 7 5, .pent 2 3 7 6 5, .pent 2 5 3 6 7,
    .pent 2 5 3 7 6, .pent 2 5 6 3 7, .pent 2 5 7 3 6, .pent 2 3 6 8 5, .pent 2 3 8 6 5, .pent 2 5
    3 6 8, .pent 2 5 3 8 6, .pent 2 5 6 3 8, .pent 2 5 8 3 6, .pent 2 3 7 8 5, .pent 2 3 8 7 5,
    .pent 2 5 3 7 8, .pent 2 5 3 8 7, .pent 2 5 7 3 8, .pent 2 5 8 3 7, .pent 2 4 6 7 5, .pent 2 4
    7 6 5, .pent 2 5 4 6 7, .pent 2 5 4 7 6, .pent 2 5 6 4 7, .pent 2 5 7 4 6, .pent 2 4 6 8 5,
    .pent 2 4 8 6 5, .pent 2 5 4 6 8, .pent 2 5 4 8 6, .pent 2 5 6 4 8, .pent 2 5 8 4 6, .pent 2 4
    7 8 5, .pent 2 4 8 7 5, .pent 2 5 4 7 8, .pent 2 5 4 8 7, .pent 2 5 7 4 8, .pent 2 5 8 4 7,
    .pent 2 5 6 7 8, .pent 2 5 6 8 7, .pent 2 5 7 6 8, .pent 2 5 7 8 6, .pent 2 5 8 6 7, .pent 2 5
    8 7 6, .star 2 0 1 3 5, .star 2 0 1 4 5, .star 2 0 1 5 6, .star 2 0 1 5 7, .star 2 0 1 5 8,
    .star 2 0 3 4 5, .star 2 0 3 5 6, .star 2 0 3 5 7, .star 2 0 3 5 8, .star 2 0 4 5 6, .star 2 0
    4 5 7, .star 2 0 4 5 8, .star 2 0 5 6 7, .star 2 0 5 6 8, .star 2 0 5 7 8, .star 2 1 3 4 5,
    .star 2 1 3 5 6, .star 2 1 3 5 7, .star 2 1 3 5 8, .star 2 1 4 5 6, .star 2 1 4 5 7, .star 2 1
    4 5 8, .star 2 1 5 6 7, .star 2 1 5 6 8, .star 2 1 5 7 8, .star 2 3 4 5 6, .star 2 3 4 5 7,
    .star 2 3 4 5 8, .star 2 3 5 6 7, .star 2 3 5 6 8, .star 2 3 5 7 8, .star 2 4 5 6 7, .star 2 4
    5 6 8, .star 2 4 5 7 8, .star 2 5 6 7 8, .star 5 0 1 2 3, .star 5 0 1 2 4, .star 5 0 1 2 6,
    .star 5 0 1 2 7, .star 5 0 1 2 8, .star 5 0 2 3 4, .star 5 0 2 3 6, .star 5 0 2 3 7, .star 5 0
    2 3 8, .star 5 0 2 4 6, .star 5 0 2 4 7, .star 5 0 2 4 8, .star 5 0 2 6 7, .star 5 0 2 6 8,
    .star 5 0 2 7 8, .star 5 1 2 3 4, .star 5 1 2 3 6, .star 5 1 2 3 7, .star 5 1 2 3 8, .star 5 1
    2 4 6, .star 5 1 2 4 7, .star 5 1 2 4 8, .star 5 1 2 6 7, .star 5 1 2 6 8, .star 5 1 2 7 8,
    .star 5 2 3 4 6, .star 5 2 3 4 7, .star 5 2 3 4 8, .star 5 2 3 6 7, .star 5 2 3 6 8, .star 5 2
    3 7 8, .star 5 2 4 6 7, .star 5 2 4 6 8, .star 5 2 4 7 8, .star 5 2 6 7 8],
  [.tri 0 3 5, .tri 1 3 5, .tri 2 3 5, .tri 3 4 5, .tri 3 5 6, .tri 3 5 7, .tri 3 5 8, .pent 0 1 2
    3 5, .pent 0 1 2 5 3, .pent 0 1 3 5 2, .pent 0 1 5 3 2, .pent 0 2 1 3 5, .pent 0 2 1 5 3,
    .pent 0 1 3 5 4, .pent 0 1 4 3 5, .pent 0 1 4 5 3, .pent 0 1 5 3 4, .pent 0 3 5 1 4, .pent 0 4
    1 3 5, .pent 0 1 3 5 6, .pent 0 1 5 3 6, .pent 0 1 6 3 5, .pent 0 1 6 5 3, .pent 0 3 5 1 6,
    .pent 0 5 3 1 6, .pent 0 1 3 5 7, .pent 0 1 5 3 7, .pent 0 1 7 3 5, .pent 0 1 7 5 3, .pent 0 3
    5 1 7, .pent 0 5 3 1 7, .pent 0 1 3 5 8, .pent 0 1 5 3 8, .pent 0 1 8 3 5, .pent 0 1 8 5 3,
    .pent 0 3 5 1 8, .pent 0 5 3 1 8, .pent 0 2 3 5 4, .pent 0 2 4 3 5, .pent 0 2 4 5 3, .pent 0 2
    5 3 4, .pent 0 3 5 2 4, .pent 0 4 2 3 5, .pent 0 2 3 5 6, .pent 0 2 5 3 6, .pent 0 2 6 3 5,
    .pent 0 2 6 5 3, .pent 0 3 5 2 6, .pent 0 5 3 2 6, .pent 0 2 3 5 7, .pent 0 2 5 3 7, .pent 0 2
    7 3 5, .pent 0 2 7 5 3, .pent 0 3 5 2 7, .pent 0 5 3 2 7, .pent 0 2 3 5 8, .pent 0 2 5 3 8,
    .pent 0 2 8 3 5, .pent 0 2 8 5 3, .pent 0 3 5 2 8, .pent 0 5 3 2 8, .pent 0 3 5 4 6, .pent 0 3
    5 6 4, .pent 0 4 3 5 6, .pent 0 4 5 3 6, .pent 0 4 6 3 5, .pent 0 5 3 4 6, .pent 0 3 5 4 7,
    .pent 0 3 5 7 4, .pent 0 4 3 5 7, .pent 0 4 5 3 7, .pent 0 4 7 3 5, .pent 0 5 3 4 7, .pent 0 3
    5 4 8, .pent 0 3 5 8 4, .pent 0 4 3 5 8, .pent 0 4 5 3 8, .pent 0 4 8 3 5, .pent 0 5 3 4 8,
    .pent 0 3 5 6 7, .pent 0 3 5 7 6, .pent 0 5 3 6 7, .pent 0 5 3 7 6, .pent 0 6 3 5 7, .pent 0 6
    5 3 7, .pent 0 3 5 6 8, .pent 0 3 5 8 6, .pent 0 5 3 6 8, .pent 0 5 3 8 6, .pent 0 6 3 5 8,
    .pent 0 6 5 3 8, .pent 0 3 5 7 8, .pent 0 3 5 8 7, .pent 0 5 3 7 8, .pent 0 5 3 8 7, .pent 0 7
    3 5 8, .pent 0 7 5 3 8, .pent 1 2 3 5 4, .pent 1 2 4 3 5, .pent 1 2 4 5 3, .pent 1 2 5 3 4,
    .pent 1 3 5 2 4, .pent 1 4 2 3 5, .pent 1 2 3 5 6, .pent 1 2 5 3 6, .pent 1 2 6 3 5, .pent 1 2
    6 5 3, .pent 1 3 5 2 6, .pent 1 5 3 2 6, .pent 1 2 3 5 7, .pent 1 2 5 3 7, .pent 1 2 7 3 5,
    .pent 1 2 7 5 3, .pent 1 3 5 2 7, .pent 1 5 3 2 7, .pent 1 2 3 5 8, .pent 1 2 5 3 8, .pent 1 2
    8 3 5, .pent 1 2 8 5 3, .pent 1 3 5 2 8, .pent 1 5 3 2 8, .pent 1 3 5 4 6, .pent 1 3 5 6 4,
    .pent 1 4 3 5 6, .pent 1 4 5 3 6, .pent 1 4 6 3 5, .pent 1 5 3 4 6, .pent 1 3 5 4 7, .pent 1 3
    5 7 4, .pent 1 4 3 5 7, .pent 1 4 5 3 7, .pent 1 4 7 3 5, .pent 1 5 3 4 7, .pent 1 3 5 4 8,
    .pent 1 3 5 8 4, .pent 1 4 3 5 8, .pent 1 4 5 3 8, .pent 1 4 8 3 5, .pent 1 5 3 4 8, .pent 1 3
    5 6 7, .pent 1 3 5 7 6, .pent 1 5 3 6 7, .pent 1 5 3 7 6, .pent 1 6 3 5 7, .pent 1 6 5 3 7,
    .pent 1 3 5 6 8, .pent 1 3 5 8 6, .pent 1 5 3 6 8, .pent 1 5 3 8 6, .pent 1 6 3 5 8, .pent 1 6
    5 3 8, .pent 1 3 5 7 8, .pent 1 3 5 8 7, .pent 1 5 3 7 8, .pent 1 5 3 8 7, .pent 1 7 3 5 8,
    .pent 1 7 5 3 8, .pent 2 3 5 4 6, .pent 2 3 5 6 4, .pent 2 4 3 5 6, .pent 2 4 5 3 6, .pent 2 4
    6 3 5, .pent 2 5 3 4 6, .pent 2 3 5 4 7, .pent 2 3 5 7 4, .pent 2 4 3 5 7, .pent 2 4 5 3 7,
    .pent 2 4 7 3 5, .pent 2 5 3 4 7, .pent 2 3 5 4 8, .pent 2 3 5 8 4, .pent 2 4 3 5 8, .pent 2 4
    5 3 8, .pent 2 4 8 3 5, .pent 2 5 3 4 8, .pent 2 3 5 6 7, .pent 2 3 5 7 6, .pent 2 5 3 6 7,
    .pent 2 5 3 7 6, .pent 2 6 3 5 7, .pent 2 6 5 3 7, .pent 2 3 5 6 8, .pent 2 3 5 8 6, .pent 2 5
    3 6 8, .pent 2 5 3 8 6, .pent 2 6 3 5 8, .pent 2 6 5 3 8, .pent 2 3 5 7 8, .pent 2 3 5 8 7,
    .pent 2 5 3 7 8, .pent 2 5 3 8 7, .pent 2 7 3 5 8, .pent 2 7 5 3 8, .pent 3 4 6 7 5, .pent 3 4
    7 6 5, .pent 3 5 4 6 7, .pent 3 5 4 7 6, .pent 3 5 6 4 7, .pent 3 5 7 4 6, .pent 3 4 6 8 5,
    .pent 3 4 8 6 5, .pent 3 5 4 6 8, .pent 3 5 4 8 6, .pent 3 5 6 4 8, .pent 3 5 8 4 6, .pent 3 4
    7 8 5, .pent 3 4 8 7 5, .pent 3 5 4 7 8, .pent 3 5 4 8 7, .pent 3 5 7 4 8, .pent 3 5 8 4 7,
    .pent 3 5 6 7 8, .pent 3 5 6 8 7, .pent 3 5 7 6 8, .pent 3 5 7 8 6, .pent 3 5 8 6 7, .pent 3 5
    8 7 6, .star 3 0 1 2 5, .star 3 0 1 4 5, .star 3 0 1 5 6, .star 3 0 1 5 7, .star 3 0 1 5 8,
    .star 3 0 2 4 5, .star 3 0 2 5 6, .star 3 0 2 5 7, .star 3 0 2 5 8, .star 3 0 4 5 6, .star 3 0
    4 5 7, .star 3 0 4 5 8, .star 3 0 5 6 7, .star 3 0 5 6 8, .star 3 0 5 7 8, .star 3 1 2 4 5,
    .star 3 1 2 5 6, .star 3 1 2 5 7, .star 3 1 2 5 8, .star 3 1 4 5 6, .star 3 1 4 5 7, .star 3 1
    4 5 8, .star 3 1 5 6 7, .star 3 1 5 6 8, .star 3 1 5 7 8, .star 3 2 4 5 6, .star 3 2 4 5 7,
    .star 3 2 4 5 8, .star 3 2 5 6 7, .star 3 2 5 6 8, .star 3 2 5 7 8, .star 3 4 5 6 7, .star 3 4
    5 6 8, .star 3 4 5 7 8, .star 3 5 6 7 8, .star 5 0 1 2 3, .star 5 0 1 3 4, .star 5 0 1 3 6,
    .star 5 0 1 3 7, .star 5 0 1 3 8, .star 5 0 2 3 4, .star 5 0 2 3 6, .star 5 0 2 3 7, .star 5 0
    2 3 8, .star 5 0 3 4 6, .star 5 0 3 4 7, .star 5 0 3 4 8, .star 5 0 3 6 7, .star 5 0 3 6 8,
    .star 5 0 3 7 8, .star 5 1 2 3 4, .star 5 1 2 3 6, .star 5 1 2 3 7, .star 5 1 2 3 8, .star 5 1
    3 4 6, .star 5 1 3 4 7, .star 5 1 3 4 8, .star 5 1 3 6 7, .star 5 1 3 6 8, .star 5 1 3 7 8,
    .star 5 2 3 4 6, .star 5 2 3 4 7, .star 5 2 3 4 8, .star 5 2 3 6 7, .star 5 2 3 6 8, .star 5 2
    3 7 8, .star 5 3 4 6 7, .star 5 3 4 6 8, .star 5 3 4 7 8, .star 5 3 6 7 8],
  [.tri 0 4 5, .tri 1 4 5, .tri 2 4 5, .tri 3 4 5, .tri 4 5 6, .tri 4 5 7, .tri 4 5 8, .pent 0 1 2
    4 5, .pent 0 1 2 5 4, .pent 0 1 4 5 2, .pent 0 1 5 4 2, .pent 0 2 1 4 5, .pent 0 2 1 5 4,
    .pent 0 1 3 4 5, .pent 0 1 3 5 4, .pent 0 1 4 5 3, .pent 0 1 5 4 3, .pent 0 3 1 4 5, .pent 0 3
    1 5 4, .pent 0 1 4 5 6, .pent 0 1 5 4 6, .pent 0 1 6 4 5, .pent 0 1 6 5 4, .pent 0 4 5 1 6,
    .pent 0 5 4 1 6, .pent 0 1 4 5 7, .pent 0 1 5 4 7, .pent 0 1 7 4 5, .pent 0 1 7 5 4, .pent 0 4
    5 1 7, .pent 0 5 4 1 7, .pent 0 1 4 5 8, .pent 0 1 5 4 8, .pent 0 1 8 4 5, .pent 0 1 8 5 4,
    .pent 0 4 5 1 8, .pent 0 5 4 1 8, .pent 0 2 3 4 5, .pent 0 2 3 5 4, .pent 0 2 4 5 3, .pent 0 2
    5 4 3, .pent 0 3 2 4 5, .pent 0 3 2 5 4, .pent 0 2 4 5 6, .pent 0 2 5 4 6, .pent 0 2 6 4 5,
    .pent 0 2 6 5 4, .pent 0 4 5 2 6, .pent 0 5 4 2 6, .pent 0 2 4 5 7, .pent 0 2 5 4 7, .pent 0 2
    7 4 5, .pent 0 2 7 5 4, .pent 0 4 5 2 7, .pent 0 5 4 2 7, .pent 0 2 4 5 8, .pent 0 2 5 4 8,
    .pent 0 2 8 4 5, .pent 0 2 8 5 4, .pent 0 4 5 2 8, .pent 0 5 4 2 8, .pent 0 3 4 5 6, .pent 0 3
    5 4 6, .pent 0 3 6 4 5, .pent 0 3 6 5 4, .pent 0 4 5 3 6, .pent 0 5 4 3 6, .pent 0 3 4 5 7,
    .pent 0 3 5 4 7, .pent 0 3 7 4 5, .pent 0 3 7 5 4, .pent 0 4 5 3 7, .pent 0 5 4 3 7, .pent 0 3
    4 5 8, .pent 0 3 5 4 8, .pent 0 3 8 4 5, .pent 0 3 8 5 4, .pent 0 4 5 3 8, .pent 0 5 4 3 8,
    .pent 0 4 5 6 7, .pent 0 4 5 7 6, .pent 0 5 4 6 7, .pent 0 5 4 7 6, .pent 0 6 4 5 7, .pent 0 6
    5 4 7, .pent 0 4 5 6 8, .pent 0 4 5 8 6, .pent 0 5 4 6 8, .pent 0 5 4 8 6, .pent 0 6 4 5 8,
    .pent 0 6 5 4 8, .pent 0 4 5 7 8, .pent 0 4 5 8 7, .pent 0 5 4 7 8, .pent 0 5 4 8 7, .pent 0 7
    4 5 8, .pent 0 7 5 4 8, .pent 1 2 3 4 5, .pent 1 2 3 5 4, .pent 1 2 4 5 3, .pent 1 2 5 4 3,
    .pent 1 3 2 4 5, .pent 1 3 2 5 4, .pent 1 2 4 5 6, .pent 1 2 5 4 6, .pent 1 2 6 4 5, .pent 1 2
    6 5 4, .pent 1 4 5 2 6, .pent 1 5 4 2 6, .pent 1 2 4 5 7, .pent 1 2 5 4 7, .pent 1 2 7 4 5,
    .pent 1 2 7 5 4, .pent 1 4 5 2 7, .pent 1 5 4 2 7, .pent 1 2 4 5 8, .pent 1 2 5 4 8, .pent 1 2
    8 4 5, .pent 1 2 8 5 4, .pent 1 4 5 2 8, .pent 1 5 4 2 8, .pent 1 3 4 5 6, .pent 1 3 5 4 6,
    .pent 1 3 6 4 5, .pent 1 3 6 5 4, .pent 1 4 5 3 6, .pent 1 5 4 3 6, .pent 1 3 4 5 7, .pent 1 3
    5 4 7, .pent 1 3 7 4 5, .pent 1 3 7 5 4, .pent 1 4 5 3 7, .pent 1 5 4 3 7, .pent 1 3 4 5 8,
    .pent 1 3 5 4 8, .pent 1 3 8 4 5, .pent 1 3 8 5 4, .pent 1 4 5 3 8, .pent 1 5 4 3 8, .pent 1 4
    5 6 7, .pent 1 4 5 7 6, .pent 1 5 4 6 7, .pent 1 5 4 7 6, .pent 1 6 4 5 7, .pent 1 6 5 4 7,
    .pent 1 4 5 6 8, .pent 1 4 5 8 6, .pent 1 5 4 6 8, .pent 1 5 4 8 6, .pent 1 6 4 5 8, .pent 1 6
    5 4 8, .pent 1 4 5 7 8, .pent 1 4 5 8 7, .pent 1 5 4 7 8, .pent 1 5 4 8 7, .pent 1 7 4 5 8,
    .pent 1 7 5 4 8, .pent 2 3 4 5 6, .pent 2 3 5 4 6, .pent 2 3 6 4 5, .pent 2 3 6 5 4, .pent 2 4
    5 3 6, .pent 2 5 4 3 6, .pent 2 3 4 5 7, .pent 2 3 5 4 7, .pent 2 3 7 4 5, .pent 2 3 7 5 4,
    .pent 2 4 5 3 7, .pent 2 5 4 3 7, .pent 2 3 4 5 8, .pent 2 3 5 4 8, .pent 2 3 8 4 5, .pent 2 3
    8 5 4, .pent 2 4 5 3 8, .pent 2 5 4 3 8, .pent 2 4 5 6 7, .pent 2 4 5 7 6, .pent 2 5 4 6 7,
    .pent 2 5 4 7 6, .pent 2 6 4 5 7, .pent 2 6 5 4 7, .pent 2 4 5 6 8, .pent 2 4 5 8 6, .pent 2 5
    4 6 8, .pent 2 5 4 8 6, .pent 2 6 4 5 8, .pent 2 6 5 4 8, .pent 2 4 5 7 8, .pent 2 4 5 8 7,
    .pent 2 5 4 7 8, .pent 2 5 4 8 7, .pent 2 7 4 5 8, .pent 2 7 5 4 8, .pent 3 4 5 6 7, .pent 3 4
    5 7 6, .pent 3 5 4 6 7, .pent 3 5 4 7 6, .pent 3 6 4 5 7, .pent 3 6 5 4 7, .pent 3 4 5 6 8,
    .pent 3 4 5 8 6, .pent 3 5 4 6 8, .pent 3 5 4 8 6, .pent 3 6 4 5 8, .pent 3 6 5 4 8, .pent 3 4
    5 7 8, .pent 3 4 5 8 7, .pent 3 5 4 7 8, .pent 3 5 4 8 7, .pent 3 7 4 5 8, .pent 3 7 5 4 8,
    .pent 4 5 6 7 8, .pent 4 5 6 8 7, .pent 4 5 7 6 8, .pent 4 5 7 8 6, .pent 4 5 8 6 7, .pent 4 5
    8 7 6, .star 4 0 1 2 5, .star 4 0 1 3 5, .star 4 0 1 5 6, .star 4 0 1 5 7, .star 4 0 1 5 8,
    .star 4 0 2 3 5, .star 4 0 2 5 6, .star 4 0 2 5 7, .star 4 0 2 5 8, .star 4 0 3 5 6, .star 4 0
    3 5 7, .star 4 0 3 5 8, .star 4 0 5 6 7, .star 4 0 5 6 8, .star 4 0 5 7 8, .star 4 1 2 3 5,
    .star 4 1 2 5 6, .star 4 1 2 5 7, .star 4 1 2 5 8, .star 4 1 3 5 6, .star 4 1 3 5 7, .star 4 1
    3 5 8, .star 4 1 5 6 7, .star 4 1 5 6 8, .star 4 1 5 7 8, .star 4 2 3 5 6, .star 4 2 3 5 7,
    .star 4 2 3 5 8, .star 4 2 5 6 7, .star 4 2 5 6 8, .star 4 2 5 7 8, .star 4 3 5 6 7, .star 4 3
    5 6 8, .star 4 3 5 7 8, .star 4 5 6 7 8, .star 5 0 1 2 4, .star 5 0 1 3 4, .star 5 0 1 4 6,
    .star 5 0 1 4 7, .star 5 0 1 4 8, .star 5 0 2 3 4, .star 5 0 2 4 6, .star 5 0 2 4 7, .star 5 0
    2 4 8, .star 5 0 3 4 6, .star 5 0 3 4 7, .star 5 0 3 4 8, .star 5 0 4 6 7, .star 5 0 4 6 8,
    .star 5 0 4 7 8, .star 5 1 2 3 4, .star 5 1 2 4 6, .star 5 1 2 4 7, .star 5 1 2 4 8, .star 5 1
    3 4 6, .star 5 1 3 4 7, .star 5 1 3 4 8, .star 5 1 4 6 7, .star 5 1 4 6 8, .star 5 1 4 7 8,
    .star 5 2 3 4 6, .star 5 2 3 4 7, .star 5 2 3 4 8, .star 5 2 4 6 7, .star 5 2 4 6 8, .star 5 2
    4 7 8, .star 5 3 4 6 7, .star 5 3 4 6 8, .star 5 3 4 7 8, .star 5 4 6 7 8],
  [.tri 0 1 6, .tri 0 2 6, .tri 0 3 6, .tri 0 4 6, .tri 0 5 6, .tri 0 6 7, .tri 0 6 8, .pent 0 1 2
    3 6, .pent 0 1 3 2 6, .pent 0 2 1 3 6, .pent 0 2 3 1 6, .pent 0 3 1 2 6, .pent 0 3 2 1 6,
    .pent 0 1 2 4 6, .pent 0 1 4 2 6, .pent 0 2 1 4 6, .pent 0 2 4 1 6, .pent 0 4 1 2 6, .pent 0 4
    2 1 6, .pent 0 1 2 5 6, .pent 0 1 5 2 6, .pent 0 2 1 5 6, .pent 0 2 5 1 6, .pent 0 5 1 2 6,
    .pent 0 5 2 1 6, .pent 0 1 2 7 6, .pent 0 1 7 2 6, .pent 0 2 1 7 6, .pent 0 2 7 1 6, .pent 0 6
    1 2 7, .pent 0 6 2 1 7, .pent 0 1 2 8 6, .pent 0 1 8 2 6, .pent 0 2 1 8 6, .pent 0 2 8 1 6,
    .pent 0 6 1 2 8, .pent 0 6 2 1 8, .pent 0 1 3 4 6, .pent 0 1 4 3 6, .pent 0 3 1 4 6, .pent 0 3
    4 1 6, .pent 0 4 1 3 6, .pent 0 4 3 1 6, .pent 0 1 3 5 6, .pent 0 1 5 3 6, .pent 0 3 1 5 6,
    .pent 0 3 5 1 6, .pent 0 5 1 3 6, .pent 0 5 3 1 6, .pent 0 1 3 7 6, .pent 0 1 7 3 6, .pent 0 3
    1 7 6, .pent 0 3 7 1 6, .pent 0 6 1 3 7, .pent 0 6 3 1 7, .pent 0 1 3 8 6, .pent 0 1 8 3 6,
    .pent 0 3 1 8 6, .pent 0 3 8 1 6, .pent 0 6 1 3 8, .pent 0 6 3 1 8, .pent 0 1 4 5 6, .pent 0 1
    5 4 6, .pent 0 4 1 5 6, .pent 0 4 5 1 6, .pent 0 5 1 4 6, .pent 0 5 4 1 6, .pent 0 1 4 7 6,
    .pent 0 1 7 4 6, .pent 0 4 1 7 6, .pent 0 4 7 1 6, .pent 0 6 1 4 7, .pent 0 6 4 1 7, .pent 0 1
    4 8 6, .pent 0 1 8 4 6, .pent 0 4 1 8 6, .pent 0 4 8 1 6, .pent 0 6 1 4 8, .pent 0 6 4 1 8,
    .pent 0 1 5 7 6, .pent 0 1 7 5 6, .pent 0 5 1 7 6, .pent 0 5 7 1 6, .pent 0 6 1 5 7, .pent 0 6
    5 1 7, .pent 0 1 5 8 6, .pent 0 1 8 5 6, .pent 0 5 1 8 6, .pent 0 5 8 1 6, .pent 0 6 1 5 8,
    .pent 0 6 5 1 8, .pent 0 1 7 8 6, .pent 0 1 8 7 6, .pent 0 6 1 7 8, .pent 0 6 1 8 7, .pent 0 6
    7 1 8, .pent 0 6 8 1 7, .pent 0 2 3 4 6, .pent 0 2 4 3 6, .pent 0 3 2 4 6, .pent 0 3 4 2 6,
    .pent 0 4 2 3 6, .pent 0 4 3 2 6, .pent 0 2 3 5 6, .pent 0 2 5 3 6, .pent 0 3 2 5 6, .pent 0 3
    5 2 6, .pent 0 5 2 3 6, .pent 0 5 3 2 6, .pent 0 2 3 7 6, .pent 0 2 7 3 6, .pent 0 3 2 7 6,
    .pent 0 3 7 2 6, .pent 0 6 2 3 7, .pent 0 6 3 2 7, .pent 0 2 3 8 6, .pent 0 2 8 3 6, .pent 0 3
    2 8 6, .pent 0 3 8 2 6, .pent 0 6 2 3 8, .pent 0 6 3 2 8, .pent 0 2 4 5 6, .pent 0 2 5 4 6,
    .pent 0 4 2 5 6, .pent 0 4 5 2 6, .pent 0 5 2 4 6, .pent 0 5 4 2 6, .pent 0 2 4 7 6, .pent 0 2
    7 4 6, .pent 0 4 2 7 6, .pent 0 4 7 2 6, .pent 0 6 2 4 7, .pent 0 6 4 2 7, .pent 0 2 4 8 6,
    .pent 0 2 8 4 6, .pent 0 4 2 8 6, .pent 0 4 8 2 6, .pent 0 6 2 4 8, .pent 0 6 4 2 8, .pent 0 2
    5 7 6, .pent 0 2 7 5 6, .pent 0 5 2 7 6, .pent 0 5 7 2 6, .pent 0 6 2 5 7, .pent 0 6 5 2 7,
    .pent 0 2 5 8 6, .pent 0 2 8 5 6, .pent 0 5 2 8 6, .pent 0 5 8 2 6, .pent 0 6 2 5 8, .pent 0 6
    5 2 8, .pent 0 2 7 8 6, .pent 0 2 8 7 6, .pent 0 6 2 7 8, .pent 0 6 2 8 7, .pent 0 6 7 2 8,
    .pent 0 6 8 2 7, .pent 0 3 4 5 6, .pent 0 3 5 4 6, .pent 0 4 3 5 6, .pent 0 4 5 3 6, .pent 0 5
    3 4 6, .pent 0 5 4 3 6, .pent 0 3 4 7 6, .pent 0 3 7 4 6, .pent 0 4 3 7 6, .pent 0 4 7 3 6,
    .pent 0 6 3 4 7, .pent 0 6 4 3 7, .pent 0 3 4 8 6, .pent 0 3 8 4 6, .pent 0 4 3 8 6, .pent 0 4
    8 3 6, .pent 0 6 3 4 8, .pent 0 6 4 3 8, .pent 0 3 5 7 6, .pent 0 3 7 5 6, .pent 0 5 3 7 6,
    .pent 0 5 7 3 6, .pent 0 6 3 5 7, .pent 0 6 5 3 7, .pent 0 3 5 8 6, .pent 0 3 8 5 6, .pent 0 5
    3 8 6, .pent 0 5 8 3 6, .pent 0 6 3 5 8, .pent 0 6 5 3 8, .pent 0 3 7 8 6, .pent 0 3 8 7 6,
    .pent 0 6 3 7 8, .pent 0 6 3 8 7, .pent 0 6 7 3 8, .pent 0 6 8 3 7, .pent 0 4 5 7 6, .pent 0 4
    7 5 6, .pent 0 5 4 7 6, .pent 0 5 7 4 6, .pent 0 6 4 5 7, .pent 0 6 5 4 7, .pent 0 4 5 8 6,
    .pent 0 4 8 5 6, .pent 0 5 4 8 6, .pent 0 5 8 4 6, .pent 0 6 4 5 8, .pent 0 6 5 4 8, .pent 0 4
    7 8 6, .pent 0 4 8 7 6, .pent 0 6 4 7 8, .pent 0 6 4 8 7, .pent 0 6 7 4 8, .pent 0 6 8 4 7,
    .pent 0 5 7 8 6, .pent 0 5 8 7 6, .pent 0 6 5 7 8, .pent 0 6 5 8 7, .pent 0 6 7 5 8, .pent 0 6
    8 5 7, .star 0 1 2 3 6, .star 0 1 2 4 6, .star 0 1 2 5 6, .star 0 1 2 6 7, .star 0 1 2 6 8,
    .star 0 1 3 4 6, .star 0 1 3 5 6, .star 0 1 3 6 7, .star 0 1 3 6 8, .star 0 1 4 5 6, .star 0 1
    4 6 7, .star 0 1 4 6 8, .star 0 1 5 6 7, .star 0 1 5 6 8, .star 0 1 6 7 8, .star 0 2 3 4 6,
    .star 0 2 3 5 6, .star 0 2 3 6 7, .star 0 2 3 6 8, .star 0 2 4 5 6, .star 0 2 4 6 7, .star 0 2
    4 6 8, .star 0 2 5 6 7, .star 0 2 5 6 8, .star 0 2 6 7 8, .star 0 3 4 5 6, .star 0 3 4 6 7,
    .star 0 3 4 6 8, .star 0 3 5 6 7, .star 0 3 5 6 8, .star 0 3 6 7 8, .star 0 4 5 6 7, .star 0 4
    5 6 8, .star 0 4 6 7 8, .star 0 5 6 7 8, .star 6 0 1 2 3, .star 6 0 1 2 4, .star 6 0 1 2 5,
    .star 6 0 1 2 7, .star 6 0 1 2 8, .star 6 0 1 3 4, .star 6 0 1 3 5, .star 6 0 1 3 7, .star 6 0
    1 3 8, .star 6 0 1 4 5, .star 6 0 1 4 7, .star 6 0 1 4 8, .star 6 0 1 5 7, .star 6 0 1 5 8,
    .star 6 0 1 7 8, .star 6 0 2 3 4, .star 6 0 2 3 5, .star 6 0 2 3 7, .star 6 0 2 3 8, .star 6 0
    2 4 5, .star 6 0 2 4 7, .star 6 0 2 4 8, .star 6 0 2 5 7, .star 6 0 2 5 8, .star 6 0 2 7 8,
    .star 6 0 3 4 5, .star 6 0 3 4 7, .star 6 0 3 4 8, .star 6 0 3 5 7, .star 6 0 3 5 8, .star 6 0
    3 7 8, .star 6 0 4 5 7, .star 6 0 4 5 8, .star 6 0 4 7 8, .star 6 0 5 7 8],
  [.tri 0 1 6, .tri 1 2 6, .tri 1 3 6, .tri 1 4 6, .tri 1 5 6, .tri 1 6 7, .tri 1 6 8, .pent 0 1 6
    2 3, .pent 0 1 6 3 2, .pent 0 2 1 6 3, .pent 0 2 3 1 6, .pent 0 2 6 1 3, .pent 0 3 2 1 6,
    .pent 0 1 6 2 4, .pent 0 1 6 4 2, .pent 0 2 1 6 4, .pent 0 2 4 1 6, .pent 0 2 6 1 4, .pent 0 4
    2 1 6, .pent 0 1 6 2 5, .pent 0 1 6 5 2, .pent 0 2 1 6 5, .pent 0 2 5 1 6, .pent 0 2 6 1 5,
    .pent 0 5 2 1 6, .pent 0 1 6 2 7, .pent 0 1 6 7 2, .pent 0 2 1 6 7, .pent 0 2 6 1 7, .pent 0 2
    7 1 6, .pent 0 6 1 2 7, .pent 0 1 6 2 8, .pent 0 1 6 8 2, .pent 0 2 1 6 8, .pent 0 2 6 1 8,
    .pent 0 2 8 1 6, .pent 0 6 1 2 8, .pent 0 1 6 3 4, .pent 0 1 6 4 3, .pent 0 3 1 6 4, .pent 0 3
    4 1 6, .pent 0 3 6 1 4, .pent 0 4 3 1 6, .pent 0 1 6 3 5, .pent 0 1 6 5 3, .pent 0 3 1 6 5,
    .pent 0 3 5 1 6, .pent 0 3 6 1 5, .pent 0 5 3 1 6, .pent 0 1 6 3 7, .pent 0 1 6 7 3, .pent 0 3
    1 6 7, .pent 0 3 6 1 7, .pent 0 3 7 1 6, .pent 0 6 1 3 7, .pent 0 1 6 3 8, .pent 0 1 6 8 3,
    .pent 0 3 1 6 8, .pent 0 3 6 1 8, .pent 0 3 8 1 6, .pent 0 6 1 3 8, .pent 0 1 6 4 5, .pent 0 1
    6 5 4, .pent 0 4 1 6 5, .pent 0 4 5 1 6, .pent 0 4 6 1 5, .pent 0 5 4 1 6, .pent 0 1 6 4 7,
    .pent 0 1 6 7 4, .pent 0 4 1 6 7, .pent 0 4 6 1 7, .pent 0 4 7 1 6, .pent 0 6 1 4 7, .pent 0 1
    6 4 8, .pent 0 1 6 8 4, .pent 0 4 1 6 8, .pent 0 4 6 1 8, .pent 0 4 8 1 6, .pent 0 6 1 4 8,
    .pent 0 1 6 5 7, .pent 0 1 6 7 5, .pent 0 5 1 6 7, .pent 0 5 6 1 7, .pent 0 5 7 1 6, .pent 0 6
    1 5 7, .pent 0 1 6 5 8, .pent 0 1 6 8 5, .pent 0 5 1 6 8, .pent 0 5 6 1 8, .pent 0 5 8 1 6,
    .pent 0 6 1 5 8, .pent 0 1 6 7 8, .pent 0 1 6 8 7, .pent 0 6 1 7 8, .pent 0 6 1 8 7, .pent 0 7
    1 6 8, .pent 0 7 6 1 8, .pent 1 2 3 4 6, .pent 1 2 4 3 6, .pent 1 3 2 4 6, .pent 1 3 4 2 6,
    .pent 1 4 2 3 6, .pent 1 4 3 2 6, .pent 1 2 3 5 6, .pent 1 2 5 3 6, .pent 1 3 2 5 6, .pent 1 3
    5 2 6, .pent 1 5 2 3 6, .pent 1 5 3 2 6, .pent 1 2 3 7 6, .pent 1 2 7 3 6, .pent 1 3 2 7 6,
    .pent 1 3 7 2 6, .pent 1 6 2 3 7, .pent 1 6 3 2 7, .pent 1 2 3 8 6, .pent 1 2 8 3 6, .pent 1 3
    2 8 6, .pent 1 3 8 2 6, .pent 1 6 2 3 8, .pent 1 6 3 2 8, .pent 1 2 4 5 6, .pent 1 2 5 4 6,
    .pent 1 4 2 5 6, .pent 1 4 5 2 6, .pent 1 5 2 4 6, .pent 1 5 4 2 6, .pent 1 2 4 7 6, .pent 1 2
    7 4 6, .pent 1 4 2 7 6, .pent 1 4 7 2 6, .pent 1 6 2 4 7, .pent 1 6 4 2 7, .pent 1 2 4 8 6,
    .pent 1 2 8 4 6, .pent 1 4 2 8 6, .pent 1 4 8 2 6, .pent 1 6 2 4 8, .pent 1 6 4 2 8, .pent 1 2
    5 7 6, .pent 1 2 7 5 6, .pent 1 5 2 7 6, .pent 1 5 7 2 6, .pent 1 6 2 5 7, .pent 1 6 5 2 7,
    .pent 1 2 5 8 6, .pent 1 2 8 5 6, .pent 1 5 2 8 6, .pent 1 5 8 2 6, .pent 1 6 2 5 8, .pent 1 6
    5 2 8, .pent 1 2 7 8 6, .pent 1 2 8 7 6, .pent 1 6 2 7 8, .pent 1 6 2 8 7, .pent 1 6 7 2 8,
    .pent 1 6 8 2 7, .pent 1 3 4 5 6, .pent 1 3 5 4 6, .pent 1 4 3 5 6, .pent 1 4 5 3 6, .pent 1 5
    3 4 6, .pent 1 5 4 3 6, .pent 1 3 4 7 6, .pent 1 3 7 4 6, .pent 1 4 3 7 6, .pent 1 4 7 3 6,
    .pent 1 6 3 4 7, .pent 1 6 4 3 7, .pent 1 3 4 8 6, .pent 1 3 8 4 6, .pent 1 4 3 8 6, .pent 1 4
    8 3 6, .pent 1 6 3 4 8, .pent 1 6 4 3 8, .pent 1 3 5 7 6, .pent 1 3 7 5 6, .pent 1 5 3 7 6,
    .pent 1 5 7 3 6, .pent 1 6 3 5 7, .pent 1 6 5 3 7, .pent 1 3 5 8 6, .pent 1 3 8 5 6, .pent 1 5
    3 8 6, .pent 1 5 8 3 6, .pent 1 6 3 5 8, .pent 1 6 5 3 8, .pent 1 3 7 8 6, .pent 1 3 8 7 6,
    .pent 1 6 3 7 8, .pent 1 6 3 8 7, .pent 1 6 7 3 8, .pent 1 6 8 3 7, .pent 1 4 5 7 6, .pent 1 4
    7 5 6, .pent 1 5 4 7 6, .pent 1 5 7 4 6, .pent 1 6 4 5 7, .pent 1 6 5 4 7, .pent 1 4 5 8 6,
    .pent 1 4 8 5 6, .pent 1 5 4 8 6, .pent 1 5 8 4 6, .pent 1 6 4 5 8, .pent 1 6 5 4 8, .pent 1 4
    7 8 6, .pent 1 4 8 7 6, .pent 1 6 4 7 8, .pent 1 6 4 8 7, .pent 1 6 7 4 8, .pent 1 6 8 4 7,
    .pent 1 5 7 8 6, .pent 1 5 8 7 6, .pent 1 6 5 7 8, .pent 1 6 5 8 7, .pent 1 6 7 5 8, .pent 1 6
    8 5 7, .star 1 0 2 3 6, .star 1 0 2 4 6, .star 1 0 2 5 6, .star 1 0 2 6 7, .star 1 0 2 6 8,
    .star 1 0 3 4 6, .star 1 0 3 5 6, .star 1 0 3 6 7, .star 1 0 3 6 8, .star 1 0 4 5 6, .star 1 0
    4 6 7, .star 1 0 4 6 8, .star 1 0 5 6 7, .star 1 0 5 6 8, .star 1 0 6 7 8, .star 1 2 3 4 6,
    .star 1 2 3 5 6, .star 1 2 3 6 7, .star 1 2 3 6 8, .star 1 2 4 5 6, .star 1 2 4 6 7, .star 1 2
    4 6 8, .star 1 2 5 6 7, .star 1 2 5 6 8, .star 1 2 6 7 8, .star 1 3 4 5 6, .star 1 3 4 6 7,
    .star 1 3 4 6 8, .star 1 3 5 6 7, .star 1 3 5 6 8, .star 1 3 6 7 8, .star 1 4 5 6 7, .star 1 4
    5 6 8, .star 1 4 6 7 8, .star 1 5 6 7 8, .star 6 0 1 2 3, .star 6 0 1 2 4, .star 6 0 1 2 5,
    .star 6 0 1 2 7, .star 6 0 1 2 8, .star 6 0 1 3 4, .star 6 0 1 3 5, .star 6 0 1 3 7, .star 6 0
    1 3 8, .star 6 0 1 4 5, .star 6 0 1 4 7, .star 6 0 1 4 8, .star 6 0 1 5 7, .star 6 0 1 5 8,
    .star 6 0 1 7 8, .star 6 1 2 3 4, .star 6 1 2 3 5, .star 6 1 2 3 7, .star 6 1 2 3 8, .star 6 1
    2 4 5, .star 6 1 2 4 7, .star 6 1 2 4 8, .star 6 1 2 5 7, .star 6 1 2 5 8, .star 6 1 2 7 8,
    .star 6 1 3 4 5, .star 6 1 3 4 7, .star 6 1 3 4 8, .star 6 1 3 5 7, .star 6 1 3 5 8, .star 6 1
    3 7 8, .star 6 1 4 5 7, .star 6 1 4 5 8, .star 6 1 4 7 8, .star 6 1 5 7 8],
  [.tri 0 2 6, .tri 1 2 6, .tri 2 3 6, .tri 2 4 6, .tri 2 5 6, .tri 2 6 7, .tri 2 6 8, .pent 0 1 2
    6 3, .pent 0 1 3 2 6, .pent 0 1 3 6 2, .pent 0 1 6 2 3, .pent 0 2 6 1 3, .pent 0 3 1 2 6,
    .pent 0 1 2 6 4, .pent 0 1 4 2 6, .pent 0 1 4 6 2, .pent 0 1 6 2 4, .pent 0 2 6 1 4, .pent 0 4
    1 2 6, .pent 0 1 2 6 5, .pent 0 1 5 2 6, .pent 0 1 5 6 2, .pent 0 1 6 2 5, .pent 0 2 6 1 5,
    .pent 0 5 1 2 6, .pent 0 1 2 6 7, .pent 0 1 6 2 7, .pent 0 1 7 2 6, .pent 0 1 7 6 2, .pent 0 2
    6 1 7, .pent 0 6 2 1 7, .pent 0 1 2 6 8, .pent 0 1 6 2 8, .pent 0 1 8 2 6, .pent 0 1 8 6 2,
    .pent 0 2 6 1 8, .pent 0 6 2 1 8, .pent 0 2 6 3 4, .pent 0 2 6 4 3, .pent 0 3 2 6 4, .pent 0 3
    4 2 6, .pent 0 3 6 2 4, .pent 0 4 3 2 6, .pent 0 2 6 3 5, .pent 0 2 6 5 3, .pent 0 3 2 6 5,
    .pent 0 3 5 2 6, .pent 0 3 6 2 5, .pent 0 5 3 2 6, .pent 0 2 6 3 7, .pent 0 2 6 7 3, .pent 0 3
    2 6 7, .pent 0 3 6 2 7, .pent 0 3 7 2 6, .pent 0 6 2 3 7, .pent 0 2 6 3 8, .pent 0 2 6 8 3,
    .pent 0 3 2 6 8, .pent 0 3 6 2 8, .pent 0 3 8 2 6, .pent 0 6 2 3 8, .pent 0 2 6 4 5, .pent 0 2
    6 5 4, .pent 0 4 2 6 5, .pent 0 4 5 2 6, .pent 0 4 6 2 5, .pent 0 5 4 2 6, .pent 0 2 6 4 7,
    .pent 0 2 6 7 4, .pent 0 4 2 6 7, .pent 0 4 6 2 7, .pent 0 4 7 2 6, .pent 0 6 2 4 7, .pent 0 2
    6 4 8, .pent 0 2 6 8 4, .pent 0 4 2 6 8, .pent 0 4 6 2 8, .pent 0 4 8 2 6, .pent 0 6 2 4 8,
    .pent 0 2 6 5 7, .pent 0 2 6 7 5, .pent 0 5 2 6 7, .pent 0 5 6 2 7, .pent 0 5 7 2 6, .pent 0 6
    2 5 7, .pent 0 2 6 5 8, .pent 0 2 6 8 5, .pent 0 5 2 6 8, .pent 0 5 6 2 8, .pent 0 5 8 2 6,
    .pent 0 6 2 5 8, .pent 0 2 6 7 8, .pent 0 2 6 8 7, .pent 0 6 2 7 8, .pent 0 6 2 8 7, .pent 0 7
    2 6 8, .pent 0 7 6 2 8, .pent 1 2 6 3 4, .pent 1 2 6 4 3, .pent 1 3 2 6 4, .pent 1 3 4 2 6,
    .pent 1 3 6 2 4, .pent 1 4 3 2 6, .pent 1 2 6 3 5, .pent 1 2 6 5 3, .pent 1 3 2 6 5, .pent 1 3
    5 2 6, .pent 1 3 6 2 5, .pent 1 5 3 2 6, .pent 1 2 6 3 7, .pent 1 2 6 7 3, .pent 1 3 2 6 7,
    .pent 1 3 6 2 7, .pent 1 3 7 2 6, .pent 1 6 2 3 7, .pent 1 2 6 3 8, .pent 1 2 6 8 3, .pent 1 3
    2 6 8, .pent 1 3 6 2 8, .pent 1 3 8 2 6, .pent 1 6 2 3 8, .pent 1 2 6 4 5, .pent 1 2 6 5 4,
    .pent 1 4 2 6 5, .pent 1 4 5 2 6, .pent 1 4 6 2 5, .pent 1 5 4 2 6, .pent 1 2 6 4 7, .pent 1 2
    6 7 4, .pent 1 4 2 6 7, .pent 1 4 6 2 7, .pent 1 4 7 2 6, .pent 1 6 2 4 7, .pent 1 2 6 4 8,
    .pent 1 2 6 8 4, .pent 1 4 2 6 8, .pent 1 4 6 2 8, .pent 1 4 8 2 6, .pent 1 6 2 4 8, .pent 1 2
    6 5 7, .pent 1 2 6 7 5, .pent 1 5 2 6 7, .pent 1 5 6 2 7, .pent 1 5 7 2 6, .pent 1 6 2 5 7,
    .pent 1 2 6 5 8, .pent 1 2 6 8 5, .pent 1 5 2 6 8, .pent 1 5 6 2 8, .pent 1 5 8 2 6, .pent 1 6
    2 5 8, .pent 1 2 6 7 8, .pent 1 2 6 8 7, .pent 1 6 2 7 8, .pent 1 6 2 8 7, .pent 1 7 2 6 8,
    .pent 1 7 6 2 8, .pent 2 3 4 5 6, .pent 2 3 5 4 6, .pent 2 4 3 5 6, .pent 2 4 5 3 6, .pent 2 5
    3 4 6, .pent 2 5 4 3 6, .pent 2 3 4 7 6, .pent 2 3 7 4 6, .pent 2 4 3 7 6, .pent 2 4 7 3 6,
    .pent 2 6 3 4 7, .pent 2 6 4 3 7, .pent 2 3 4 8 6, .pent 2 3 8 4 6, .pent 2 4 3 8 6, .pent 2 4
    8 3 6, .pent 2 6 3 4 8, .pent 2 6 4 3 8, .pent 2 3 5 7 6, .pent 2 3 7 5 6, .pent 2 5 3 7 6,
    .pent 2 5 7 3 6, .pent 2 6 3 5 7, .pent 2 6 5 3 7, .pent 2 3 5 8 6, .pent 2 3 8 5 6, .pent 2 5
    3 8 6, .pent 2 5 8 3 6, .pent 2 6 3 5 8, .pent 2 6 5 3 8, .pent 2 3 7 8 6, .pent 2 3 8 7 6,
    .pent 2 6 3 7 8, .pent 2 6 3 8 7, .pent 2 6 7 3 8, .pent 2 6 8 3 7, .pent 2 4 5 7 6, .pent 2 4
    7 5 6, .pent 2 5 4 7 6, .pent 2 5 7 4 6, .pent 2 6 4 5 7, .pent 2 6 5 4 7, .pent 2 4 5 8 6,
    .pent 2 4 8 5 6, .pent 2 5 4 8 6, .pent 2 5 8 4 6, .pent 2 6 4 5 8, .pent 2 6 5 4 8, .pent 2 4
    7 8 6, .pent 2 4 8 7 6, .pent 2 6 4 7 8, .pent 2 6 4 8 7, .pent 2 6 7 4 8, .pent 2 6 8 4 7,
    .pent 2 5 7 8 6, .pent 2 5 8 7 6, .pent 2 6 5 7 8, .pent 2 6 5 8 7, .pent 2 6 7 5 8, .pent 2 6
    8 5 7, .star 2 0 1 3 6, .star 2 0 1 4 6, .star 2 0 1 5 6, .star 2 0 1 6 7, .star 2 0 1 6 8,
    .star 2 0 3 4 6, .star 2 0 3 5 6, .star 2 0 3 6 7, .star 2 0 3 6 8, .star 2 0 4 5 6, .star 2 0
    4 6 7, .star 2 0 4 6 8, .star 2 0 5 6 7, .star 2 0 5 6 8, .star 2 0 6 7 8, .star 2 1 3 4 6,
    .star 2 1 3 5 6, .star 2 1 3 6 7, .star 2 1 3 6 8, .star 2 1 4 5 6, .star 2 1 4 6 7, .star 2 1
    4 6 8, .star 2 1 5 6 7, .star 2 1 5 6 8, .star 2 1 6 7 8, .star 2 3 4 5 6, .star 2 3 4 6 7,
    .star 2 3 4 6 8, .star 2 3 5 6 7, .star 2 3 5 6 8, .star 2 3 6 7 8, .star 2 4 5 6 7, .star 2 4
    5 6 8, .star 2 4 6 7 8, .star 2 5 6 7 8, .star 6 0 1 2 3, .star 6 0 1 2 4, .star 6 0 1 2 5,
    .star 6 0 1 2 7, .star 6 0 1 2 8, .star 6 0 2 3 4, .star 6 0 2 3 5, .star 6 0 2 3 7, .star 6 0
    2 3 8, .star 6 0 2 4 5, .star 6 0 2 4 7, .star 6 0 2 4 8, .star 6 0 2 5 7, .star 6 0 2 5 8,
    .star 6 0 2 7 8, .star 6 1 2 3 4, .star 6 1 2 3 5, .star 6 1 2 3 7, .star 6 1 2 3 8, .star 6 1
    2 4 5, .star 6 1 2 4 7, .star 6 1 2 4 8, .star 6 1 2 5 7, .star 6 1 2 5 8, .star 6 1 2 7 8,
    .star 6 2 3 4 5, .star 6 2 3 4 7, .star 6 2 3 4 8, .star 6 2 3 5 7, .star 6 2 3 5 8, .star 6 2
    3 7 8, .star 6 2 4 5 7, .star 6 2 4 5 8, .star 6 2 4 7 8, .star 6 2 5 7 8],
  [.tri 0 3 6, .tri 1 3 6, .tri 2 3 6, .tri 3 4 6, .tri 3 5 6, .tri 3 6 7, .tri 3 6 8, .pent 0 1 2
    3 6, .pent 0 1 2 6 3, .pent 0 1 3 6 2, .pent 0 1 6 3 2, .pent 0 2 1 3 6, .pent 0 2 1 6 3,
    .pent 0 1 3 6 4, .pent 0 1 4 3 6, .pent 0 1 4 6 3, .pent 0 1 6 3 4, .pent 0 3 6 1 4, .pent 0 4
    1 3 6, .pent 0 1 3 6 5, .pent 0 1 5 3 6, .pent 0 1 5 6 3, .pent 0 1 6 3 5, .pent 0 3 6 1 5,
    .pent 0 5 1 3 6, .pent 0 1 3 6 7, .pent 0 1 6 3 7, .pent 0 1 7 3 6, .pent 0 1 7 6 3, .pent 0 3
    6 1 7, .pent 0 6 3 1 7, .pent 0 1 3 6 8, .pent 0 1 6 3 8, .pent 0 1 8 3 6, .pent 0 1 8 6 3,
    .pent 0 3 6 1 8, .pent 0 6 3 1 8, .pent 0 2 3 6 4, .pent 0 2 4 3 6, .pent 0 2 4 6 3, .pent 0 2
    6 3 4, .pent 0 3 6 2 4, .pent 0 4 2 3 6, .pent 0 2 3 6 5, .pent 0 2 5 3 6, .pent 0 2 5 6 3,
    .pent 0 2 6 3 5, .pent 0 3 6 2 5, .pent 0 5 2 3 6, .pent 0 2 3 6 7, .pent 0 2 6 3 7, .pent 0 2
    7 3 6, .pent 0 2 7 6 3, .pent 0 3 6 2 7, .pent 0 6 3 2 7, .pent 0 2 3 6 8, .pent 0 2 6 3 8,
    .pent 0 2 8 3 6, .pent 0 2 8 6 3, .pent 0 3 6 2 8, .pent 0 6 3 2 8, .pent 0 3 6 4 5, .pent 0 3
    6 5 4, .pent 0 4 3 6 5, .pent 0 4 5 3 6, .pent 0 4 6 3 5, .pent 0 5 4 3 6, .pent 0 3 6 4 7,
    .pent 0 3 6 7 4, .pent 0 4 3 6 7, .pent 0 4 6 3 7, .pent 0 4 7 3 6, .pent 0 6 3 4 7, .pent 0 3
    6 4 8, .pent 0 3 6 8 4, .pent 0 4 3 6 8, .pent 0 4 6 3 8, .pent 0 4 8 3 6, .pent 0 6 3 4 8,
    .pent 0 3 6 5 7, .pent 0 3 6 7 5, .pent 0 5 3 6 7, .pent 0 5 6 3 7, .pent 0 5 7 3 6, .pent 0 6
    3 5 7, .pent 0 3 6 5 8, .pent 0 3 6 8 5, .pent 0 5 3 6 8, .pent 0 5 6 3 8, .pent 0 5 8 3 6,
    .pent 0 6 3 5 8, .pent 0 3 6 7 8, .pent 0 3 6 8 7, .pent 0 6 3 7 8, .pent 0 6 3 8 7, .pent 0 7
    3 6 8, .pent 0 7 6 3 8, .pent 1 2 3 6 4, .pent 1 2 4 3 6, .pent 1 2 4 6 3, .pent 1 2 6 3 4,
    .pent 1 3 6 2 4, .pent 1 4 2 3 6, .pent 1 2 3 6 5, .pent 1 2 5 3 6, .pent 1 2 5 6 3, .pent 1 2
    6 3 5, .pent 1 3 6 2 5, .pent 1 5 2 3 6, .pent 1 2 3 6 7, .pent 1 2 6 3 7, .pent 1 2 7 3 6,
    .pent 1 2 7 6 3, .pent 1 3 6 2 7, .pent 1 6 3 2 7, .pent 1 2 3 6 8, .pent 1 2 6 3 8, .pent 1 2
    8 3 6, .pent 1 2 8 6 3, .pent 1 3 6 2 8, .pent 1 6 3 2 8, .pent 1 3 6 4 5, .pent 1 3 6 5 4,
    .pent 1 4 3 6 5, .pent 1 4 5 3 6, .pent 1 4 6 3 5, .pent 1 5 4 3 6, .pent 1 3 6 4 7, .pent 1 3
    6 7 4, .pent 1 4 3 6 7, .pent 1 4 6 3 7, .pent 1 4 7 3 6, .pent 1 6 3 4 7, .pent 1 3 6 4 8,
    .pent 1 3 6 8 4, .pent 1 4 3 6 8, .pent 1 4 6 3 8, .pent 1 4 8 3 6, .pent 1 6 3 4 8, .pent 1 3
    6 5 7, .pent 1 3 6 7 5, .pent 1 5 3 6 7, .pent 1 5 6 3 7, .pent 1 5 7 3 6, .pent 1 6 3 5 7,
    .pent 1 3 6 5 8, .pent 1 3 6 8 5, .pent 1 5 3 6 8, .pent 1 5 6 3 8, .pent 1 5 8 3 6, .pent 1 6
    3 5 8, .pent 1 3 6 7 8, .pent 1 3 6 8 7, .pent 1 6 3 7 8, .pent 1 6 3 8 7, .pent 1 7 3 6 8,
    .pent 1 7 6 3 8, .pent 2 3 6 4 5, .pent 2 3 6 5 4, .pent 2 4 3 6 5, .pent 2 4 5 3 6, .pent 2 4
    6 3 5, .pent 2 5 4 3 6, .pent 2 3 6 4 7, .pent 2 3 6 7 4, .pent 2 4 3 6 7, .pent 2 4 6 3 7,
    .pent 2 4 7 3 6, .pent 2 6 3 4 7, .pent 2 3 6 4 8, .pent 2 3 6 8 4, .pent 2 4 3 6 8, .pent 2 4
    6 3 8, .pent 2 4 8 3 6, .pent 2 6 3 4 8, .pent 2 3 6 5 7, .pent 2 3 6 7 5, .pent 2 5 3 6 7,
    .pent 2 5 6 3 7, .pent 2 5 7 3 6, .pent 2 6 3 5 7, .pent 2 3 6 5 8, .pent 2 3 6 8 5, .pent 2 5
    3 6 8, .pent 2 5 6 3 8, .pent 2 5 8 3 6, .pent 2 6 3 5 8, .pent 2 3 6 7 8, .pent 2 3 6 8 7,
    .pent 2 6 3 7 8, .pent 2 6 3 8 7, .pent 2 7 3 6 8, .pent 2 7 6 3 8, .pent 3 4 5 7 6, .pent 3 4
    7 5 6, .pent 3 5 4 7 6, .pent 3 5 7 4 6, .pent 3 6 4 5 7, .pent 3 6 5 4 7, .pent 3 4 5 8 6,
    .pent 3 4 8 5 6, .pent 3 5 4 8 6, .pent 3 5 8 4 6, .pent 3 6 4 5 8, .pent 3 6 5 4 8, .pent 3 4
    7 8 6, .pent 3 4 8 7 6, .pent 3 6 4 7 8, .pent 3 6 4 8 7, .pent 3 6 7 4 8, .pent 3 6 8 4 7,
    .pent 3 5 7 8 6, .pent 3 5 8 7 6, .pent 3 6 5 7 8, .pent 3 6 5 8 7, .pent 3 6 7 5 8, .pent 3 6
    8 5 7, .star 3 0 1 2 6, .star 3 0 1 4 6, .star 3 0 1 5 6, .star 3 0 1 6 7, .star 3 0 1 6 8,
    .star 3 0 2 4 6, .star 3 0 2 5 6, .star 3 0 2 6 7, .star 3 0 2 6 8, .star 3 0 4 5 6, .star 3 0
    4 6 7, .star 3 0 4 6 8, .star 3 0 5 6 7, .star 3 0 5 6 8, .star 3 0 6 7 8, .star 3 1 2 4 6,
    .star 3 1 2 5 6, .star 3 1 2 6 7, .star 3 1 2 6 8, .star 3 1 4 5 6, .star 3 1 4 6 7, .star 3 1
    4 6 8, .star 3 1 5 6 7, .star 3 1 5 6 8, .star 3 1 6 7 8, .star 3 2 4 5 6, .star 3 2 4 6 7,
    .star 3 2 4 6 8, .star 3 2 5 6 7, .star 3 2 5 6 8, .star 3 2 6 7 8, .star 3 4 5 6 7, .star 3 4
    5 6 8, .star 3 4 6 7 8, .star 3 5 6 7 8, .star 6 0 1 2 3, .star 6 0 1 3 4, .star 6 0 1 3 5,
    .star 6 0 1 3 7, .star 6 0 1 3 8, .star 6 0 2 3 4, .star 6 0 2 3 5, .star 6 0 2 3 7, .star 6 0
    2 3 8, .star 6 0 3 4 5, .star 6 0 3 4 7, .star 6 0 3 4 8, .star 6 0 3 5 7, .star 6 0 3 5 8,
    .star 6 0 3 7 8, .star 6 1 2 3 4, .star 6 1 2 3 5, .star 6 1 2 3 7, .star 6 1 2 3 8, .star 6 1
    3 4 5, .star 6 1 3 4 7, .star 6 1 3 4 8, .star 6 1 3 5 7, .star 6 1 3 5 8, .star 6 1 3 7 8,
    .star 6 2 3 4 5, .star 6 2 3 4 7, .star 6 2 3 4 8, .star 6 2 3 5 7, .star 6 2 3 5 8, .star 6 2
    3 7 8, .star 6 3 4 5 7, .star 6 3 4 5 8, .star 6 3 4 7 8, .star 6 3 5 7 8],
  [.tri 0 4 6, .tri 1 4 6, .tri 2 4 6, .tri 3 4 6, .tri 4 5 6, .tri 4 6 7, .tri 4 6 8, .pent 0 1 2
    4 6, .pent 0 1 2 6 4, .pent 0 1 4 6 2, .pent 0 1 6 4 2, .pent 0 2 1 4 6, .pent 0 2 1 6 4,
    .pent 0 1 3 4 6, .pent 0 1 3 6 4, .pent 0 1 4 6 3, .pent 0 1 6 4 3, .pent 0 3 1 4 6, .pent 0 3
    1 6 4, .pent 0 1 4 6 5, .pent 0 1 5 4 6, .pent 0 1 5 6 4, .pent 0 1 6 4 5, .pent 0 4 6 1 5,
    .pent 0 5 1 4 6, .pent 0 1 4 6 7, .pent 0 1 6 4 7, .pent 0 1 7 4 6, .pent 0 1 7 6 4, .pent 0 4
    6 1 7, .pent 0 6 4 1 7, .pent 0 1 4 6 8, .pent 0 1 6 4 8, .pent 0 1 8 4 6, .pent 0 1 8 6 4,
    .pent 0 4 6 1 8, .pent 0 6 4 1 8, .pent 0 2 3 4 6, .pent 0 2 3 6 4, .pent 0 2 4 6 3, .pent 0 2
    6 4 3, .pent 0 3 2 4 6, .pent 0 3 2 6 4, .pent 0 2 4 6 5, .pent 0 2 5 4 6, .pent 0 2 5 6 4,
    .pent 0 2 6 4 5, .pent 0 4 6 2 5, .pent 0 5 2 4 6, .pent 0 2 4 6 7, .pent 0 2 6 4 7, .pent 0 2
    7 4 6, .pent 0 2 7 6 4, .pent 0 4 6 2 7, .pent 0 6 4 2 7, .pent 0 2 4 6 8, .pent 0 2 6 4 8,
    .pent 0 2 8 4 6, .pent 0 2 8 6 4, .pent 0 4 6 2 8, .pent 0 6 4 2 8, .pent 0 3 4 6 5, .pent 0 3
    5 4 6, .pent 0 3 5 6 4, .pent 0 3 6 4 5, .pent 0 4 6 3 5, .pent 0 5 3 4 6, .pent 0 3 4 6 7,
    .pent 0 3 6 4 7, .pent 0 3 7 4 6, .pent 0 3 7 6 4, .pent 0 4 6 3 7, .pent 0 6 4 3 7, .pent 0 3
    4 6 8, .pent 0 3 6 4 8, .pent 0 3 8 4 6, .pent 0 3 8 6 4, .pent 0 4 6 3 8, .pent 0 6 4 3 8,
    .pent 0 4 6 5 7, .pent 0 4 6 7 5, .pent 0 5 4 6 7, .pent 0 5 6 4 7, .pent 0 5 7 4 6, .pent 0 6
    4 5 7, .pent 0 4 6 5 8, .pent 0 4 6 8 5, .pent 0 5 4 6 8, .pent 0 5 6 4 8, .pent 0 5 8 4 6,
    .pent 0 6 4 5 8, .pent 0 4 6 7 8, .pent 0 4 6 8 7, .pent 0 6 4 7 8, .pent 0 6 4 8 7, .pent 0 7
    4 6 8, .pent 0 7 6 4 8, .pent 1 2 3 4 6, .pent 1 2 3 6 4, .pent 1 2 4 6 3, .pent 1 2 6 4 3,
    .pent 1 3 2 4 6, .pent 1 3 2 6 4, .pent 1 2 4 6 5, .pent 1 2 5 4 6, .pent 1 2 5 6 4, .pent 1 2
    6 4 5, .pent 1 4 6 2 5, .pent 1 5 2 4 6, .pent 1 2 4 6 7, .pent 1 2 6 4 7, .pent 1 2 7 4 6,
    .pent 1 2 7 6 4, .pent 1 4 6 2 7, .pent 1 6 4 2 7, .pent 1 2 4 6 8, .pent 1 2 6 4 8, .pent 1 2
    8 4 6, .pent 1 2 8 6 4, .pent 1 4 6 2 8, .pent 1 6 4 2 8, .pent 1 3 4 6 5, .pent 1 3 5 4 6,
    .pent 1 3 5 6 4, .pent 1 3 6 4 5, .pent 1 4 6 3 5, .pent 1 5 3 4 6, .pent 1 3 4 6 7, .pent 1 3
    6 4 7, .pent 1 3 7 4 6, .pent 1 3 7 6 4, .pent 1 4 6 3 7, .pent 1 6 4 3 7, .pent 1 3 4 6 8,
    .pent 1 3 6 4 8, .pent 1 3 8 4 6, .pent 1 3 8 6 4, .pent 1 4 6 3 8, .pent 1 6 4 3 8, .pent 1 4
    6 5 7, .pent 1 4 6 7 5, .pent 1 5 4 6 7, .pent 1 5 6 4 7, .pent 1 5 7 4 6, .pent 1 6 4 5 7,
    .pent 1 4 6 5 8, .pent 1 4 6 8 5, .pent 1 5 4 6 8, .pent 1 5 6 4 8, .pent 1 5 8 4 6, .pent 1 6
    4 5 8, .pent 1 4 6 7 8, .pent 1 4 6 8 7, .pent 1 6 4 7 8, .pent 1 6 4 8 7, .pent 1 7 4 6 8,
    .pent 1 7 6 4 8, .pent 2 3 4 6 5, .pent 2 3 5 4 6, .pent 2 3 5 6 4, .pent 2 3 6 4 5, .pent 2 4
    6 3 5, .pent 2 5 3 4 6, .pent 2 3 4 6 7, .pent 2 3 6 4 7, .pent 2 3 7 4 6, .pent 2 3 7 6 4,
    .pent 2 4 6 3 7, .pent 2 6 4 3 7, .pent 2 3 4 6 8, .pent 2 3 6 4 8, .pent 2 3 8 4 6, .pent 2 3
    8 6 4, .pent 2 4 6 3 8, .pent 2 6 4 3 8, .pent 2 4 6 5 7, .pent 2 4 6 7 5, .pent 2 5 4 6 7,
    .pent 2 5 6 4 7, .pent 2 5 7 4 6, .pent 2 6 4 5 7, .pent 2 4 6 5 8, .pent 2 4 6 8 5, .pent 2 5
    4 6 8, .pent 2 5 6 4 8, .pent 2 5 8 4 6, .pent 2 6 4 5 8, .pent 2 4 6 7 8, .pent 2 4 6 8 7,
    .pent 2 6 4 7 8, .pent 2 6 4 8 7, .pent 2 7 4 6 8, .pent 2 7 6 4 8, .pent 3 4 6 5 7, .pent 3 4
    6 7 5, .pent 3 5 4 6 7, .pent 3 5 6 4 7, .pent 3 5 7 4 6, .pent 3 6 4 5 7, .pent 3 4 6 5 8,
    .pent 3 4 6 8 5, .pent 3 5 4 6 8, .pent 3 5 6 4 8, .pent 3 5 8 4 6, .pent 3 6 4 5 8, .pent 3 4
    6 7 8, .pent 3 4 6 8 7, .pent 3 6 4 7 8, .pent 3 6 4 8 7, .pent 3 7 4 6 8, .pent 3 7 6 4 8,
    .pent 4 5 7 8 6, .pent 4 5 8 7 6, .pent 4 6 5 7 8, .pent 4 6 5 8 7, .pent 4 6 7 5 8, .pent 4 6
    8 5 7, .star 4 0 1 2 6, .star 4 0 1 3 6, .star 4 0 1 5 6, .star 4 0 1 6 7, .star 4 0 1 6 8,
    .star 4 0 2 3 6, .star 4 0 2 5 6, .star 4 0 2 6 7, .star 4 0 2 6 8, .star 4 0 3 5 6, .star 4 0
    3 6 7, .star 4 0 3 6 8, .star 4 0 5 6 7, .star 4 0 5 6 8, .star 4 0 6 7 8, .star 4 1 2 3 6,
    .star 4 1 2 5 6, .star 4 1 2 6 7, .star 4 1 2 6 8, .star 4 1 3 5 6, .star 4 1 3 6 7, .star 4 1
    3 6 8, .star 4 1 5 6 7, .star 4 1 5 6 8, .star 4 1 6 7 8, .star 4 2 3 5 6, .star 4 2 3 6 7,
    .star 4 2 3 6 8, .star 4 2 5 6 7, .star 4 2 5 6 8, .star 4 2 6 7 8, .star 4 3 5 6 7, .star 4 3
    5 6 8, .star 4 3 6 7 8, .star 4 5 6 7 8, .star 6 0 1 2 4, .star 6 0 1 3 4, .star 6 0 1 4 5,
    .star 6 0 1 4 7, .star 6 0 1 4 8, .star 6 0 2 3 4, .star 6 0 2 4 5, .star 6 0 2 4 7, .star 6 0
    2 4 8, .star 6 0 3 4 5, .star 6 0 3 4 7, .star 6 0 3 4 8, .star 6 0 4 5 7, .star 6 0 4 5 8,
    .star 6 0 4 7 8, .star 6 1 2 3 4, .star 6 1 2 4 5, .star 6 1 2 4 7, .star 6 1 2 4 8, .star 6 1
    3 4 5, .star 6 1 3 4 7, .star 6 1 3 4 8, .star 6 1 4 5 7, .star 6 1 4 5 8, .star 6 1 4 7 8,
    .star 6 2 3 4 5, .star 6 2 3 4 7, .star 6 2 3 4 8, .star 6 2 4 5 7, .star 6 2 4 5 8, .star 6 2
    4 7 8, .star 6 3 4 5 7, .star 6 3 4 5 8, .star 6 3 4 7 8, .star 6 4 5 7 8],
  [.tri 0 5 6, .tri 1 5 6, .tri 2 5 6, .tri 3 5 6, .tri 4 5 6, .tri 5 6 7, .tri 5 6 8, .pent 0 1 2
    5 6, .pent 0 1 2 6 5, .pent 0 1 5 6 2, .pent 0 1 6 5 2, .pent 0 2 1 5 6, .pent 0 2 1 6 5,
    .pent 0 1 3 5 6, .pent 0 1 3 6 5, .pent 0 1 5 6 3, .pent 0 1 6 5 3, .pent 0 3 1 5 6, .pent 0 3
    1 6 5, .pent 0 1 4 5 6, .pent 0 1 4 6 5, .pent 0 1 5 6 4, .pent 0 1 6 5 4, .pent 0 4 1 5 6,
    .pent 0 4 1 6 5, .pent 0 1 5 6 7, .pent 0 1 6 5 7, .pent 0 1 7 5 6, .pent 0 1 7 6 5, .pent 0 5
    6 1 7, .pent 0 6 5 1 7, .pent 0 1 5 6 8, .pent 0 1 6 5 8, .pent 0 1 8 5 6, .pent 0 1 8 6 5,
    .pent 0 5 6 1 8, .pent 0 6 5 1 8, .pent 0 2 3 5 6, .pent 0 2 3 6 5, .pent 0 2 5 6 3, .pent 0 2
    6 5 3, .pent 0 3 2 5 6, .pent 0 3 2 6 5, .pent 0 2 4 5 6, .pent 0 2 4 6 5, .pent 0 2 5 6 4,
    .pent 0 2 6 5 4, .pent 0 4 2 5 6, .pent 0 4 2 6 5, .pent 0 2 5 6 7, .pent 0 2 6 5 7, .pent 0 2
    7 5 6, .pent 0 2 7 6 5, .pent 0 5 6 2 7, .pent 0 6 5 2 7, .pent 0 2 5 6 8, .pent 0 2 6 5 8,
    .pent 0 2 8 5 6, .pent 0 2 8 6 5, .pent 0 5 6 2 8, .pent 0 6 5 2 8, .pent 0 3 4 5 6, .pent 0 3
    4 6 5, .pent 0 3 5 6 4, .pent 0 3 6 5 4, .pent 0 4 3 5 6, .pent 0 4 3 6 5, .pent 0 3 5 6 7,
    .pent 0 3 6 5 7, .pent 0 3 7 5 6, .pent 0 3 7 6 5, .pent 0 5 6 3 7, .pent 0 6 5 3 7, .pent 0 3
    5 6 8, .pent 0 3 6 5 8, .pent 0 3 8 5 6, .pent 0 3 8 6 5, .pent 0 5 6 3 8, .pent 0 6 5 3 8,
    .pent 0 4 5 6 7, .pent 0 4 6 5 7, .pent 0 4 7 5 6, .pent 0 4 7 6 5, .pent 0 5 6 4 7, .pent 0 6
    5 4 7, .pent 0 4 5 6 8, .pent 0 4 6 5 8, .pent 0 4 8 5 6, .pent 0 4 8 6 5, .pent 0 5 6 4 8,
    .pent 0 6 5 4 8, .pent 0 5 6 7 8, .pent 0 5 6 8 7, .pent 0 6 5 7 8, .pent 0 6 5 8 7, .pent 0 7
    5 6 8, .pent 0 7 6 5 8, .pent 1 2 3 5 6, .pent 1 2 3 6 5, .pent 1 2 5 6 3, .pent 1 2 6 5 3,
    .pent 1 3 2 5 6, .pent 1 3 2 6 5, .pent 1 2 4 5 6, .pent 1 2 4 6 5, .pent 1 2 5 6 4, .pent 1 2
    6 5 4, .pent 1 4 2 5 6, .pent 1 4 2 6 5, .pent 1 2 5 6 7, .pent 1 2 6 5 7, .pent 1 2 7 5 6,
    .pent 1 2 7 6 5, .pent 1 5 6 2 7, .pent 1 6 5 2 7, .pent 1 2 5 6 8, .pent 1 2 6 5 8, .pent 1 2
    8 5 6, .pent 1 2 8 6 5, .pent 1 5 6 2 8, .pent 1 6 5 2 8, .pent 1 3 4 5 6, .pent 1 3 4 6 5,
    .pent 1 3 5 6 4, .pent 1 3 6 5 4, .pent 1 4 3 5 6, .pent 1 4 3 6 5, .pent 1 3 5 6 7, .pent 1 3
    6 5 7, .pent 1 3 7 5 6, .pent 1 3 7 6 5, .pent 1 5 6 3 7, .pent 1 6 5 3 7, .pent 1 3 5 6 8,
    .pent 1 3 6 5 8, .pent 1 3 8 5 6, .pent 1 3 8 6 5, .pent 1 5 6 3 8, .pent 1 6 5 3 8, .pent 1 4
    5 6 7, .pent 1 4 6 5 7, .pent 1 4 7 5 6, .pent 1 4 7 6 5, .pent 1 5 6 4 7, .pent 1 6 5 4 7,
    .pent 1 4 5 6 8, .pent 1 4 6 5 8, .pent 1 4 8 5 6, .pent 1 4 8 6 5, .pent 1 5 6 4 8, .pent 1 6
    5 4 8, .pent 1 5 6 7 8, .pent 1 5 6 8 7, .pent 1 6 5 7 8, .pent 1 6 5 8 7, .pent 1 7 5 6 8,
    .pent 1 7 6 5 8, .pent 2 3 4 5 6, .pent 2 3 4 6 5, .pent 2 3 5 6 4, .pent 2 3 6 5 4, .pent 2 4
    3 5 6, .pent 2 4 3 6 5, .pent 2 3 5 6 7, .pent 2 3 6 5 7, .pent 2 3 7 5 6, .pent 2 3 7 6 5,
    .pent 2 5 6 3 7, .pent 2 6 5 3 7, .pent 2 3 5 6 8, .pent 2 3 6 5 8, .pent 2 3 8 5 6, .pent 2 3
    8 6 5, .pent 2 5 6 3 8, .pent 2 6 5 3 8, .pent 2 4 5 6 7, .pent 2 4 6 5 7, .pent 2 4 7 5 6,
    .pent 2 4 7 6 5, .pent 2 5 6 4 7, .pent 2 6 5 4 7, .pent 2 4 5 6 8, .pent 2 4 6 5 8, .pent 2 4
    8 5 6, .pent 2 4 8 6 5, .pent 2 5 6 4 8, .pent 2 6 5 4 8, .pent 2 5 6 7 8, .pent 2 5 6 8 7,
    .pent 2 6 5 7 8, .pent 2 6 5 8 7, .pent 2 7 5 6 8, .pent 2 7 6 5 8, .pent 3 4 5 6 7, .pent 3 4
    6 5 7, .pent 3 4 7 5 6, .pent 3 4 7 6 5, .pent 3 5 6 4 7, .pent 3 6 5 4 7, .pent 3 4 5 6 8,
    .pent 3 4 6 5 8, .pent 3 4 8 5 6, .pent 3 4 8 6 5, .pent 3 5 6 4 8, .pent 3 6 5 4 8, .pent 3 5
    6 7 8, .pent 3 5 6 8 7, .pent 3 6 5 7 8, .pent 3 6 5 8 7, .pent 3 7 5 6 8, .pent 3 7 6 5 8,
    .pent 4 5 6 7 8, .pent 4 5 6 8 7, .pent 4 6 5 7 8, .pent 4 6 5 8 7, .pent 4 7 5 6 8, .pent 4 7
    6 5 8, .star 5 0 1 2 6, .star 5 0 1 3 6, .star 5 0 1 4 6, .star 5 0 1 6 7, .star 5 0 1 6 8,
    .star 5 0 2 3 6, .star 5 0 2 4 6, .star 5 0 2 6 7, .star 5 0 2 6 8, .star 5 0 3 4 6, .star 5 0
    3 6 7, .star 5 0 3 6 8, .star 5 0 4 6 7, .star 5 0 4 6 8, .star 5 0 6 7 8, .star 5 1 2 3 6,
    .star 5 1 2 4 6, .star 5 1 2 6 7, .star 5 1 2 6 8, .star 5 1 3 4 6, .star 5 1 3 6 7, .star 5 1
    3 6 8, .star 5 1 4 6 7, .star 5 1 4 6 8, .star 5 1 6 7 8, .star 5 2 3 4 6, .star 5 2 3 6 7,
    .star 5 2 3 6 8, .star 5 2 4 6 7, .star 5 2 4 6 8, .star 5 2 6 7 8, .star 5 3 4 6 7, .star 5 3
    4 6 8, .star 5 3 6 7 8, .star 5 4 6 7 8, .star 6 0 1 2 5, .star 6 0 1 3 5, .star 6 0 1 4 5,
    .star 6 0 1 5 7, .star 6 0 1 5 8, .star 6 0 2 3 5, .star 6 0 2 4 5, .star 6 0 2 5 7, .star 6 0
    2 5 8, .star 6 0 3 4 5, .star 6 0 3 5 7, .star 6 0 3 5 8, .star 6 0 4 5 7, .star 6 0 4 5 8,
    .star 6 0 5 7 8, .star 6 1 2 3 5, .star 6 1 2 4 5, .star 6 1 2 5 7, .star 6 1 2 5 8, .star 6 1
    3 4 5, .star 6 1 3 5 7, .star 6 1 3 5 8, .star 6 1 4 5 7, .star 6 1 4 5 8, .star 6 1 5 7 8,
    .star 6 2 3 4 5, .star 6 2 3 5 7, .star 6 2 3 5 8, .star 6 2 4 5 7, .star 6 2 4 5 8, .star 6 2
    5 7 8, .star 6 3 4 5 7, .star 6 3 4 5 8, .star 6 3 5 7 8, .star 6 4 5 7 8],
  [.tri 0 1 7, .tri 0 2 7, .tri 0 3 7, .tri 0 4 7, .tri 0 5 7, .tri 0 6 7, .tri 0 7 8, .pent 0 1 2
    3 7, .pent 0 1 3 2 7, .pent 0 2 1 3 7, .pent 0 2 3 1 7, .pent 0 3 1 2 7, .pent 0 3 2 1 7,
    .pent 0 1 2 4 7, .pent 0 1 4 2 7, .pent 0 2 1 4 7, .pent 0 2 4 1 7, .pent 0 4 1 2 7, .pent 0 4
    2 1 7, .pent 0 1 2 5 7, .pent 0 1 5 2 7, .pent 0 2 1 5 7, .pent 0 2 5 1 7, .pent 0 5 1 2 7,
    .pent 0 5 2 1 7, .pent 0 1 2 6 7, .pent 0 1 6 2 7, .pent 0 2 1 6 7, .pent 0 2 6 1 7, .pent 0 6
    1 2 7, .pent 0 6 2 1 7, .pent 0 1 2 8 7, .pent 0 1 8 2 7, .pent 0 2 1 8 7, .pent 0 2 8 1 7,
    .pent 0 7 1 2 8, .pent 0 7 2 1 8, .pent 0 1 3 4 7, .pent 0 1 4 3 7, .pent 0 3 1 4 7, .pent 0 3
    4 1 7, .pent 0 4 1 3 7, .pent 0 4 3 1 7, .pent 0 1 3 5 7, .pent 0 1 5 3 7, .pent 0 3 1 5 7,
    .pent 0 3 5 1 7, .pent 0 5 1 3 7, .pent 0 5 3 1 7, .pent 0 1 3 6 7, .pent 0 1 6 3 7, .pent 0 3
    1 6 7, .pent 0 3 6 1 7, .pent 0 6 1 3 7, .pent 0 6 3 1 7, .pent 0 1 3 8 7, .pent 0 1 8 3 7,
    .pent 0 3 1 8 7, .pent 0 3 8 1 7, .pent 0 7 1 3 8, .pent 0 7 3 1 8, .pent 0 1 4 5 7, .pent 0 1
    5 4 7, .pent 0 4 1 5 7, .pent 0 4 5 1 7, .pent 0 5 1 4 7, .pent 0 5 4 1 7, .pent 0 1 4 6 7,
    .pent 0 1 6 4 7, .pent 0 4 1 6 7, .pent 0 4 6 1 7, .pent 0 6 1 4 7, .pent 0 6 4 1 7, .pent 0 1
    4 8 7, .pent 0 1 8 4 7, .pent 0 4 1 8 7, .pent 0 4 8 1 7, .pent 0 7 1 4 8, .pent 0 7 4 1 8,
    .pent 0 1 5 6 7, .pent 0 1 6 5 7, .pent 0 5 1 6 7, .pent 0 5 6 1 7, .pent 0 6 1 5 7, .pent 0 6
    5 1 7, .pent 0 1 5 8 7, .pent 0 1 8 5 7, .pent 0 5 1 8 7, .pent 0 5 8 1 7, .pent 0 7 1 5 8,
    .pent 0 7 5 1 8, .pent 0 1 6 8 7, .pent 0 1 8 6 7, .pent 0 6 1 8 7, .pent 0 6 8 1 7, .pent 0 7
    1 6 8, .pent 0 7 6 1 8, .pent 0 2 3 4 7, .pent 0 2 4 3 7, .pent 0 3 2 4 7, .pent 0 3 4 2 7,
    .pent 0 4 2 3 7, .pent 0 4 3 2 7, .pent 0 2 3 5 7, .pent 0 2 5 3 7, .pent 0 3 2 5 7, .pent 0 3
    5 2 7, .pent 0 5 2 3 7, .pent 0 5 3 2 7, .pent 0 2 3 6 7, .pent 0 2 6 3 7, .pent 0 3 2 6 7,
    .pent 0 3 6 2 7, .pent 0 6 2 3 7, .pent 0 6 3 2 7, .pent 0 2 3 8 7, .pent 0 2 8 3 7, .pent 0 3
    2 8 7, .pent 0 3 8 2 7, .pent 0 7 2 3 8, .pent 0 7 3 2 8, .pent 0 2 4 5 7, .pent 0 2 5 4 7,
    .pent 0 4 2 5 7, .pent 0 4 5 2 7, .pent 0 5 2 4 7, .pent 0 5 4 2 7, .pent 0 2 4 6 7, .pent 0 2
    6 4 7, .pent 0 4 2 6 7, .pent 0 4 6 2 7, .pent 0 6 2 4 7, .pent 0 6 4 2 7, .pent 0 2 4 8 7,
    .pent 0 2 8 4 7, .pent 0 4 2 8 7, .pent 0 4 8 2 7, .pent 0 7 2 4 8, .pent 0 7 4 2 8, .pent 0 2
    5 6 7, .pent 0 2 6 5 7, .pent 0 5 2 6 7, .pent 0 5 6 2 7, .pent 0 6 2 5 7, .pent 0 6 5 2 7,
    .pent 0 2 5 8 7, .pent 0 2 8 5 7, .pent 0 5 2 8 7, .pent 0 5 8 2 7, .pent 0 7 2 5 8, .pent 0 7
    5 2 8, .pent 0 2 6 8 7, .pent 0 2 8 6 7, .pent 0 6 2 8 7, .pent 0 6 8 2 7, .pent 0 7 2 6 8,
    .pent 0 7 6 2 8, .pent 0 3 4 5 7, .pent 0 3 5 4 7, .pent 0 4 3 5 7, .pent 0 4 5 3 7, .pent 0 5
    3 4 7, .pent 0 5 4 3 7, .pent 0 3 4 6 7, .pent 0 3 6 4 7, .pent 0 4 3 6 7, .pent 0 4 6 3 7,
    .pent 0 6 3 4 7, .pent 0 6 4 3 7, .pent 0 3 4 8 7, .pent 0 3 8 4 7, .pent 0 4 3 8 7, .pent 0 4
    8 3 7, .pent 0 7 3 4 8, .pent 0 7 4 3 8, .pent 0 3 5 6 7, .pent 0 3 6 5 7, .pent 0 5 3 6 7,
    .pent 0 5 6 3 7, .pent 0 6 3 5 7, .pent 0 6 5 3 7, .pent 0 3 5 8 7, .pent 0 3 8 5 7, .pent 0 5
    3 8 7, .pent 0 5 8 3 7, .pent 0 7 3 5 8, .pent 0 7 5 3 8, .pent 0 3 6 8 7, .pent 0 3 8 6 7,
    .pent 0 6 3 8 7, .pent 0 6 8 3 7, .pent 0 7 3 6 8, .pent 0 7 6 3 8, .pent 0 4 5 6 7, .pent 0 4
    6 5 7, .pent 0 5 4 6 7, .pent 0 5 6 4 7, .pent 0 6 4 5 7, .pent 0 6 5 4 7, .pent 0 4 5 8 7,
    .pent 0 4 8 5 7, .pent 0 5 4 8 7, .pent 0 5 8 4 7, .pent 0 7 4 5 8, .pent 0 7 5 4 8, .pent 0 4
    6 8 7, .pent 0 4 8 6 7, .pent 0 6 4 8 7, .pent 0 6 8 4 7, .pent 0 7 4 6 8, .pent 0 7 6 4 8,
    .pent 0 5 6 8 7, .pent 0 5 8 6 7, .pent 0 6 5 8 7, .pent 0 6 8 5 7, .pent 0 7 5 6 8, .pent 0 7
    6 5 8, .star 0 1 2 3 7, .star 0 1 2 4 7, .star 0 1 2 5 7, .star 0 1 2 6 7, .star 0 1 2 7 8,
    .star 0 1 3 4 7, .star 0 1 3 5 7, .star 0 1 3 6 7, .star 0 1 3 7 8, .star 0 1 4 5 7, .star 0 1
    4 6 7, .star 0 1 4 7 8, .star 0 1 5 6 7, .star 0 1 5 7 8, .star 0 1 6 7 8, .star 0 2 3 4 7,
    .star 0 2 3 5 7, .star 0 2 3 6 7, .star 0 2 3 7 8, .star 0 2 4 5 7, .star 0 2 4 6 7, .star 0 2
    4 7 8, .star 0 2 5 6 7, .star 0 2 5 7 8, .star 0 2 6 7 8, .star 0 3 4 5 7, .star 0 3 4 6 7,
    .star 0 3 4 7 8, .star 0 3 5 6 7, .star 0 3 5 7 8, .star 0 3 6 7 8, .star 0 4 5 6 7, .star 0 4
    5 7 8, .star 0 4 6 7 8, .star 0 5 6 7 8, .star 7 0 1 2 3, .star 7 0 1 2 4, .star 7 0 1 2 5,
    .star 7 0 1 2 6, .star 7 0 1 2 8, .star 7 0 1 3 4, .star 7 0 1 3 5, .star 7 0 1 3 6, .star 7 0
    1 3 8, .star 7 0 1 4 5, .star 7 0 1 4 6, .star 7 0 1 4 8, .star 7 0 1 5 6, .star 7 0 1 5 8,
    .star 7 0 1 6 8, .star 7 0 2 3 4, .star 7 0 2 3 5, .star 7 0 2 3 6, .star 7 0 2 3 8, .star 7 0
    2 4 5, .star 7 0 2 4 6, .star 7 0 2 4 8, .star 7 0 2 5 6, .star 7 0 2 5 8, .star 7 0 2 6 8,
    .star 7 0 3 4 5, .star 7 0 3 4 6, .star 7 0 3 4 8, .star 7 0 3 5 6, .star 7 0 3 5 8, .star 7 0
    3 6 8, .star 7 0 4 5 6, .star 7 0 4 5 8, .star 7 0 4 6 8, .star 7 0 5 6 8],
  [.tri 0 1 7, .tri 1 2 7, .tri 1 3 7, .tri 1 4 7, .tri 1 5 7, .tri 1 6 7, .tri 1 7 8, .pent 0 1 7
    2 3, .pent 0 1 7 3 2, .pent 0 2 1 7 3, .pent 0 2 3 1 7, .pent 0 2 7 1 3, .pent 0 3 2 1 7,
    .pent 0 1 7 2 4, .pent 0 1 7 4 2, .pent 0 2 1 7 4, .pent 0 2 4 1 7, .pent 0 2 7 1 4, .pent 0 4
    2 1 7, .pent 0 1 7 2 5, .pent 0 1 7 5 2, .pent 0 2 1 7 5, .pent 0 2 5 1 7, .pent 0 2 7 1 5,
    .pent 0 5 2 1 7, .pent 0 1 7 2 6, .pent 0 1 7 6 2, .pent 0 2 1 7 6, .pent 0 2 6 1 7, .pent 0 2
    7 1 6, .pent 0 6 2 1 7, .pent 0 1 7 2 8, .pent 0 1 7 8 2, .pent 0 2 1 7 8, .pent 0 2 7 1 8,
    .pent 0 2 8 1 7, .pent 0 7 1 2 8, .pent 0 1 7 3 4, .pent 0 1 7 4 3, .pent 0 3 1 7 4, .pent 0 3
    4 1 7, .pent 0 3 7 1 4, .pent 0 4 3 1 7, .pent 0 1 7 3 5, .pent 0 1 7 5 3, .pent 0 3 1 7 5,
    .pent 0 3 5 1 7, .pent 0 3 7 1 5, .pent 0 5 3 1 7, .pent 0 1 7 3 6, .pent 0 1 7 6 3, .pent 0 3
    1 7 6, .pent 0 3 6 1 7, .pent 0 3 7 1 6, .pent 0 6 3 1 7, .pent 0 1 7 3 8, .pent 0 1 7 8 3,
    .pent 0 3 1 7 8, .pent 0 3 7 1 8, .pent 0 3 8 1 7, .pent 0 7 1 3 8, .pent 0 1 7 4 5, .pent 0 1
    7 5 4, .pent 0 4 1 7 5, .pent 0 4 5 1 7, .pent 0 4 7 1 5, .pent 0 5 4 1 7, .pent 0 1 7 4 6,
    .pent 0 1 7 6 4, .pent 0 4 1 7 6, .pent 0 4 6 1 7, .pent 0 4 7 1 6, .pent 0 6 4 1 7, .pent 0 1
    7 4 8, .pent 0 1 7 8 4, .pent 0 4 1 7 8, .pent 0 4 7 1 8, .pent 0 4 8 1 7, .pent 0 7 1 4 8,
    .pent 0 1 7 5 6, .pent 0 1 7 6 5, .pent 0 5 1 7 6, .pent 0 5 6 1 7, .pent 0 5 7 1 6, .pent 0 6
    5 1 7, .pent 0 1 7 5 8, .pent 0 1 7 8 5, .pent 0 5 1 7 8, .pent 0 5 7 1 8, .pent 0 5 8 1 7,
    .pent 0 7 1 5 8, .pent 0 1 7 6 8, .pent 0 1 7 8 6, .pent 0 6 1 7 8, .pent 0 6 7 1 8, .pent 0 6
    8 1 7, .pent 0 7 1 6 8, .pent 1 2 3 4 7, .pent 1 2 4 3 7, .pent 1 3 2 4 7, .pent 1 3 4 2 7,
    .pent 1 4 2 3 7, .pent 1 4 3 2 7, .pent 1 2 3 5 7, .pent 1 2 5 3 7, .pent 1 3 2 5 7, .pent 1 3
    5 2 7, .pent 1 5 2 3 7, .pent 1 5 3 2 7, .pent 1 2 3 6 7, .pent 1 2 6 3 7, .pent 1 3 2 6 7,
    .pent 1 3 6 2 7, .pent 1 6 2 3 7, .pent 1 6 3 2 7, .pent 1 2 3 8 7, .pent 1 2 8 3 7, .pent 1 3
    2 8 7, .pent 1 3 8 2 7, .pent 1 7 2 3 8, .pent 1 7 3 2 8, .pent 1 2 4 5 7, .pent 1 2 5 4 7,
    .pent 1 4 2 5 7, .pent 1 4 5 2 7, .pent 1 5 2 4 7, .pent 1 5 4 2 7, .pent 1 2 4 6 7, .pent 1 2
    6 4 7, .pent 1 4 2 6 7, .pent 1 4 6 2 7, .pent 1 6 2 4 7, .pent 1 6 4 2 7, .pent 1 2 4 8 7,
    .pent 1 2 8 4 7, .pent 1 4 2 8 7, .pent 1 4 8 2 7, .pent 1 7 2 4 8, .pent 1 7 4 2 8, .pent 1 2
    5 6 7, .pent 1 2 6 5 7, .pent 1 5 2 6 7, .pent 1 5 6 2 7, .pent 1 6 2 5 7, .pent 1 6 5 2 7,
    .pent 1 2 5 8 7, .pent 1 2 8 5 7, .pent 1 5 2 8 7, .pent 1 5 8 2 7, .pent 1 7 2 5 8, .pent 1 7
    5 2 8, .pent 1 2 6 8 7, .pent 1 2 8 6 7, .pent 1 6 2 8 7, .pent 1 6 8 2 7, .pent 1 7 2 6 8,
    .pent 1 7 6 2 8, .pent 1 3 4 5 7, .pent 1 3 5 4 7, .pent 1 4 3 5 7, .pent 1 4 5 3 7, .pent 1 5
    3 4 7, .pent 1 5 4 3 7, .pent 1 3 4 6 7, .pent 1 3 6 4 7, .pent 1 4 3 6 7, .pent 1 4 6 3 7,
    .pent 1 6 3 4 7, .pent 1 6 4 3 7, .pent 1 3 4 8 7, .pent 1 3 8 4 7, .pent 1 4 3 8 7, .pent 1 4
    8 3 7, .pent 1 7 3 4 8, .pent 1 7 4 3 8, .pent 1 3 5 6 7, .pent 1 3 6 5 7, .pent 1 5 3 6 7,
    .pent 1 5 6 3 7, .pent 1 6 3 5 7, .pent 1 6 5 3 7, .pent 1 3 5 8 7, .pent 1 3 8 5 7, .pent 1 5
    3 8 7, .pent 1 5 8 3 7, .pent 1 7 3 5 8, .pent 1 7 5 3 8, .pent 1 3 6 8 7, .pent 1 3 8 6 7,
    .pent 1 6 3 8 7, .pent 1 6 8 3 7, .pent 1 7 3 6 8, .pent 1 7 6 3 8, .pent 1 4 5 6 7, .pent 1 4
    6 5 7, .pent 1 5 4 6 7, .pent 1 5 6 4 7, .pent 1 6 4 5 7, .pent 1 6 5 4 7, .pent 1 4 5 8 7,
    .pent 1 4 8 5 7, .pent 1 5 4 8 7, .pent 1 5 8 4 7, .pent 1 7 4 5 8, .pent 1 7 5 4 8, .pent 1 4
    6 8 7, .pent 1 4 8 6 7, .pent 1 6 4 8 7, .pent 1 6 8 4 7, .pent 1 7 4 6 8, .pent 1 7 6 4 8,
    .pent 1 5 6 8 7, .pent 1 5 8 6 7, .pent 1 6 5 8 7, .pent 1 6 8 5 7, .pent 1 7 5 6 8, .pent 1 7
    6 5 8, .star 1 0 2 3 7, .star 1 0 2 4 7, .star 1 0 2 5 7, .star 1 0 2 6 7, .star 1 0 2 7 8,
    .star 1 0 3 4 7, .star 1 0 3 5 7, .star 1 0 3 6 7, .star 1 0 3 7 8, .star 1 0 4 5 7, .star 1 0
    4 6 7, .star 1 0 4 7 8, .star 1 0 5 6 7, .star 1 0 5 7 8, .star 1 0 6 7 8, .star 1 2 3 4 7,
    .star 1 2 3 5 7, .star 1 2 3 6 7, .star 1 2 3 7 8, .star 1 2 4 5 7, .star 1 2 4 6 7, .star 1 2
    4 7 8, .star 1 2 5 6 7, .star 1 2 5 7 8, .star 1 2 6 7 8, .star 1 3 4 5 7, .star 1 3 4 6 7,
    .star 1 3 4 7 8, .star 1 3 5 6 7, .star 1 3 5 7 8, .star 1 3 6 7 8, .star 1 4 5 6 7, .star 1 4
    5 7 8, .star 1 4 6 7 8, .star 1 5 6 7 8, .star 7 0 1 2 3, .star 7 0 1 2 4, .star 7 0 1 2 5,
    .star 7 0 1 2 6, .star 7 0 1 2 8, .star 7 0 1 3 4, .star 7 0 1 3 5, .star 7 0 1 3 6, .star 7 0
    1 3 8, .star 7 0 1 4 5, .star 7 0 1 4 6, .star 7 0 1 4 8, .star 7 0 1 5 6, .star 7 0 1 5 8,
    .star 7 0 1 6 8, .star 7 1 2 3 4, .star 7 1 2 3 5, .star 7 1 2 3 6, .star 7 1 2 3 8, .star 7 1
    2 4 5, .star 7 1 2 4 6, .star 7 1 2 4 8, .star 7 1 2 5 6, .star 7 1 2 5 8, .star 7 1 2 6 8,
    .star 7 1 3 4 5, .star 7 1 3 4 6, .star 7 1 3 4 8, .star 7 1 3 5 6, .star 7 1 3 5 8, .star 7 1
    3 6 8, .star 7 1 4 5 6, .star 7 1 4 5 8, .star 7 1 4 6 8, .star 7 1 5 6 8],
  [.tri 0 2 7, .tri 1 2 7, .tri 2 3 7, .tri 2 4 7, .tri 2 5 7, .tri 2 6 7, .tri 2 7 8, .pent 0 1 2
    7 3, .pent 0 1 3 2 7, .pent 0 1 3 7 2, .pent 0 1 7 2 3, .pent 0 2 7 1 3, .pent 0 3 1 2 7,
    .pent 0 1 2 7 4, .pent 0 1 4 2 7, .pent 0 1 4 7 2, .pent 0 1 7 2 4, .pent 0 2 7 1 4, .pent 0 4
    1 2 7, .pent 0 1 2 7 5, .pent 0 1 5 2 7, .pent 0 1 5 7 2, .pent 0 1 7 2 5, .pent 0 2 7 1 5,
    .pent 0 5 1 2 7, .pent 0 1 2 7 6, .pent 0 1 6 2 7, .pent 0 1 6 7 2, .pent 0 1 7 2 6, .pent 0 2
    7 1 6, .pent 0 6 1 2 7, .pent 0 1 2 7 8, .pent 0 1 7 2 8, .pent 0 1 8 2 7, .pent 0 1 8 7 2,
    .pent 0 2 7 1 8, .pent 0 7 2 1 8, .pent 0 2 7 3 4, .pent 0 2 7 4 3, .pent 0 3 2 7 4, .pent 0 3
    4 2 7, .pent 0 3 7 2 4, .pent 0 4 3 2 7, .pent 0 2 7 3 5, .pent 0 2 7 5 3, .pent 0 3 2 7 5,
    .pent 0 3 5 2 7, .pent 0 3 7 2 5, .pent 0 5 3 2 7, .pent 0 2 7 3 6, .pent 0 2 7 6 3, .pent 0 3
    2 7 6, .pent 0 3 6 2 7, .pent 0 3 7 2 6, .pent 0 6 3 2 7, .pent 0 2 7 3 8, .pent 0 2 7 8 3,
    .pent 0 3 2 7 8, .pent 0 3 7 2 8, .pent 0 3 8 2 7, .pent 0 7 2 3 8, .pent 0 2 7 4 5, .pent 0 2
    7 5 4, .pent 0 4 2 7 5, .pent 0 4 5 2 7, .pent 0 4 7 2 5, .pent 0 5 4 2 7, .pent 0 2 7 4 6,
    .pent 0 2 7 6 4, .pent 0 4 2 7 6, .pent 0 4 6 2 7, .pent 0 4 7 2 6, .pent 0 6 4 2 7, .pent 0 2
    7 4 8, .pent 0 2 7 8 4, .pent 0 4 2 7 8, .pent 0 4 7 2 8, .pent 0 4 8 2 7, .pent 0 7 2 4 8,
    .pent 0 2 7 5 6, .pent 0 2 7 6 5, .pent 0 5 2 7 6, .pent 0 5 6 2 7, .pent 0 5 7 2 6, .pent 0 6
    5 2 7, .pent 0 2 7 5 8, .pent 0 2 7 8 5, .pent 0 5 2 7 8, .pent 0 5 7 2 8, .pent 0 5 8 2 7,
    .pent 0 7 2 5 8, .pent 0 2 7 6 8, .pent 0 2 7 8 6, .pent 0 6 2 7 8, .pent 0 6 7 2 8, .pent 0 6
    8 2 7, .pent 0 7 2 6 8, .pent 1 2 7 3 4, .pent 1 2 7 4 3, .pent 1 3 2 7 4, .pent 1 3 4 2 7,
    .pent 1 3 7 2 4, .pent 1 4 3 2 7, .pent 1 2 7 3 5, .pent 1 2 7 5 3, .pent 1 3 2 7 5, .pent 1 3
    5 2 7, .pent 1 3 7 2 5, .pent 1 5 3 2 7, .pent 1 2 7 3 6, .pent 1 2 7 6 3, .pent 1 3 2 7 6,
    .pent 1 3 6 2 7, .pent 1 3 7 2 6, .pent 1 6 3 2 7, .pent 1 2 7 3 8, .pent 1 2 7 8 3, .pent 1 3
    2 7 8, .pent 1 3 7 2 8, .pent 1 3 8 2 7, .pent 1 7 2 3 8, .pent 1 2 7 4 5, .pent 1 2 7 5 4,
    .pent 1 4 2 7 5, .pent 1 4 5 2 7, .pent 1 4 7 2 5, .pent 1 5 4 2 7, .pent 1 2 7 4 6, .pent 1 2
    7 6 4, .pent 1 4 2 7 6, .pent 1 4 6 2 7, .pent 1 4 7 2 6, .pent 1 6 4 2 7, .pent 1 2 7 4 8,
    .pent 1 2 7 8 4, .pent 1 4 2 7 8, .pent 1 4 7 2 8, .pent 1 4 8 2 7, .pent 1 7 2 4 8, .pent 1 2
    7 5 6, .pent 1 2 7 6 5, .pent 1 5 2 7 6, .pent 1 5 6 2 7, .pent 1 5 7 2 6, .pent 1 6 5 2 7,
    .pent 1 2 7 5 8, .pent 1 2 7 8 5, .pent 1 5 2 7 8, .pent 1 5 7 2 8, .pent 1 5 8 2 7, .pent 1 7
    2 5 8, .pent 1 2 7 6 8, .pent 1 2 7 8 6, .pent 1 6 2 7 8, .pent 1 6 7 2 8, .pent 1 6 8 2 7,
    .pent 1 7 2 6 8, .pent 2 3 4 5 7, .pent 2 3 5 4 7, .pent 2 4 3 5 7, .pent 2 4 5 3 7, .pent 2 5
    3 4 7, .pent 2 5 4 3 7, .pent 2 3 4 6 7, .pent 2 3 6 4 7, .pent 2 4 3 6 7, .pent 2 4 6 3 7,
    .pent 2 6 3 4 7, .pent 2 6 4 3 7, .pent 2 3 4 8 7, .pent 2 3 8 4 7, .pent 2 4 3 8 7, .pent 2 4
    8 3 7, .pent 2 7 3 4 8, .pent 2 7 4 3 8, .pent 2 3 5 6 7, .pent 2 3 6 5 7, .pent 2 5 3 6 7,
    .pent 2 5 6 3 7, .pent 2 6 3 5 7, .pent 2 6 5 3 7, .pent 2 3 5 8 7, .pent 2 3 8 5 7, .pent 2 5
    3 8 7, .pent 2 5 8 3 7, .pent 2 7 3 5 8, .pent 2 7 5 3 8, .pent 2 3 6 8 7, .pent 2 3 8 6 7,
    .pent 2 6 3 8 7, .pent 2 6 8 3 7, .pent 2 7 3 6 8, .pent 2 7 6 3 8, .pent 2 4 5 6 7, .pent 2 4
    6 5 7, .pent 2 5 4 6 7, .pent 2 5 6 4 7, .pent 2 6 4 5 7, .pent 2 6 5 4 7, .pent 2 4 5 8 7,
    .pent 2 4 8 5 7, .pent 2 5 4 8 7, .pent 2 5 8 4 7, .pent 2 7 4 5 8, .pent 2 7 5 4 8, .pent 2 4
    6 8 7, .pent 2 4 8 6 7, .pent 2 6 4 8 7, .pent 2 6 8 4 7, .pent 2 7 4 6 8, .pent 2 7 6 4 8,
    .pent 2 5 6 8 7, .pent 2 5 8 6 7, .pent 2 6 5 8 7, .pent 2 6 8 5 7, .pent 2 7 5 6 8, .pent 2 7
    6 5 8, .star 2 0 1 3 7, .star 2 0 1 4 7, .star 2 0 1 5 7, .star 2 0 1 6 7, .star 2 0 1 7 8,
    .star 2 0 3 4 7, .star 2 0 3 5 7, .star 2 0 3 6 7, .star 2 0 3 7 8, .star 2 0 4 5 7, .star 2 0
    4 6 7, .star 2 0 4 7 8, .star 2 0 5 6 7, .star 2 0 5 7 8, .star 2 0 6 7 8, .star 2 1 3 4 7,
    .star 2 1 3 5 7, .star 2 1 3 6 7, .star 2 1 3 7 8, .star 2 1 4 5 7, .star 2 1 4 6 7, .star 2 1
    4 7 8, .star 2 1 5 6 7, .star 2 1 5 7 8, .star 2 1 6 7 8, .star 2 3 4 5 7, .star 2 3 4 6 7,
    .star 2 3 4 7 8, .star 2 3 5 6 7, .star 2 3 5 7 8, .star 2 3 6 7 8, .star 2 4 5 6 7, .star 2 4
    5 7 8, .star 2 4 6 7 8, .star 2 5 6 7 8, .star 7 0 1 2 3, .star 7 0 1 2 4, .star 7 0 1 2 5,
    .star 7 0 1 2 6, .star 7 0 1 2 8, .star 7 0 2 3 4, .star 7 0 2 3 5, .star 7 0 2 3 6, .star 7 0
    2 3 8, .star 7 0 2 4 5, .star 7 0 2 4 6, .star 7 0 2 4 8, .star 7 0 2 5 6, .star 7 0 2 5 8,
    .star 7 0 2 6 8, .star 7 1 2 3 4, .star 7 1 2 3 5, .star 7 1 2 3 6, .star 7 1 2 3 8, .star 7 1
    2 4 5, .star 7 1 2 4 6, .star 7 1 2 4 8, .star 7 1 2 5 6, .star 7 1 2 5 8, .star 7 1 2 6 8,
    .star 7 2 3 4 5, .star 7 2 3 4 6, .star 7 2 3 4 8, .star 7 2 3 5 6, .star 7 2 3 5 8, .star 7 2
    3 6 8, .star 7 2 4 5 6, .star 7 2 4 5 8, .star 7 2 4 6 8, .star 7 2 5 6 8],
  [.tri 0 3 7, .tri 1 3 7, .tri 2 3 7, .tri 3 4 7, .tri 3 5 7, .tri 3 6 7, .tri 3 7 8, .pent 0 1 2
    3 7, .pent 0 1 2 7 3, .pent 0 1 3 7 2, .pent 0 1 7 3 2, .pent 0 2 1 3 7, .pent 0 2 1 7 3,
    .pent 0 1 3 7 4, .pent 0 1 4 3 7, .pent 0 1 4 7 3, .pent 0 1 7 3 4, .pent 0 3 7 1 4, .pent 0 4
    1 3 7, .pent 0 1 3 7 5, .pent 0 1 5 3 7, .pent 0 1 5 7 3, .pent 0 1 7 3 5, .pent 0 3 7 1 5,
    .pent 0 5 1 3 7, .pent 0 1 3 7 6, .pent 0 1 6 3 7, .pent 0 1 6 7 3, .pent 0 1 7 3 6, .pent 0 3
    7 1 6, .pent 0 6 1 3 7, .pent 0 1 3 7 8, .pent 0 1 7 3 8, .pent 0 1 8 3 7, .pent 0 1 8 7 3,
    .pent 0 3 7 1 8, .pent 0 7 3 1 8, .pent 0 2 3 7 4, .pent 0 2 4 3 7, .pent 0 2 4 7 3, .pent 0 2
    7 3 4, .pent 0 3 7 2 4, .pent 0 4 2 3 7, .pent 0 2 3 7 5, .pent 0 2 5 3 7, .pent 0 2 5 7 3,
    .pent 0 2 7 3 5, .pent 0 3 7 2 5, .pent 0 5 2 3 7, .pent 0 2 3 7 6, .pent 0 2 6 3 7, .pent 0 2
    6 7 3, .pent 0 2 7 3 6, .pent 0 3 7 2 6, .pent 0 6 2 3 7, .pent 0 2 3 7 8, .pent 0 2 7 3 8,
    .pent 0 2 8 3 7, .pent 0 2 8 7 3, .pent 0 3 7 2 8, .pent 0 7 3 2 8, .pent 0 3 7 4 5, .pent 0 3
    7 5 4, .pent 0 4 3 7 5, .pent 0 4 5 3 7, .pent 0 4 7 3 5, .pent 0 5 4 3 7, .pent 0 3 7 4 6,
    .pent 0 3 7 6 4, .pent 0 4 3 7 6, .pent 0 4 6 3 7, .pent 0 4 7 3 6, .pent 0 6 4 3 7, .pent 0 3
    7 4 8, .pent 0 3 7 8 4, .pent 0 4 3 7 8, .pent 0 4 7 3 8, .pent 0 4 8 3 7, .pent 0 7 3 4 8,
    .pent 0 3 7 5 6, .pent 0 3 7 6 5, .pent 0 5 3 7 6, .pent 0 5 6 3 7, .pent 0 5 7 3 6, .pent 0 6
    5 3 7, .pent 0 3 7 5 8, .pent 0 3 7 8 5, .pent 0 5 3 7 8, .pent 0 5 7 3 8, .pent 0 5 8 3 7,
    .pent 0 7 3 5 8, .pent 0 3 7 6 8, .pent 0 3 7 8 6, .pent 0 6 3 7 8, .pent 0 6 7 3 8, .pent 0 6
    8 3 7, .pent 0 7 3 6 8, .pent 1 2 3 7 4, .pent 1 2 4 3 7, .pent 1 2 4 7 3, .pent 1 2 7 3 4,
    .pent 1 3 7 2 4, .pent 1 4 2 3 7, .pent 1 2 3 7 5, .pent 1 2 5 3 7, .pent 1 2 5 7 3, .pent 1 2
    7 3 5, .pent 1 3 7 2 5, .pent 1 5 2 3 7, .pent 1 2 3 7 6, .pent 1 2 6 3 7, .pent 1 2 6 7 3,
    .pent 1 2 7 3 6, .pent 1 3 7 2 6, .pent 1 6 2 3 7, .pent 1 2 3 7 8, .pent 1 2 7 3 8, .pent 1 2
    8 3 7, .pent 1 2 8 7 3, .pent 1 3 7 2 8, .pent 1 7 3 2 8, .pent 1 3 7 4 5, .pent 1 3 7 5 4,
    .pent 1 4 3 7 5, .pent 1 4 5 3 7, .pent 1 4 7 3 5, .pent 1 5 4 3 7, .pent 1 3 7 4 6, .pent 1 3
    7 6 4, .pent 1 4 3 7 6, .pent 1 4 6 3 7, .pent 1 4 7 3 6, .pent 1 6 4 3 7, .pent 1 3 7 4 8,
    .pent 1 3 7 8 4, .pent 1 4 3 7 8, .pent 1 4 7 3 8, .pent 1 4 8 3 7, .pent 1 7 3 4 8, .pent 1 3
    7 5 6, .pent 1 3 7 6 5, .pent 1 5 3 7 6, .pent 1 5 6 3 7, .pent 1 5 7 3 6, .pent 1 6 5 3 7,
    .pent 1 3 7 5 8, .pent 1 3 7 8 5, .pent 1 5 3 7 8, .pent 1 5 7 3 8, .pent 1 5 8 3 7, .pent 1 7
    3 5 8, .pent 1 3 7 6 8, .pent 1 3 7 8 6, .pent 1 6 3 7 8, .pent 1 6 7 3 8, .pent 1 6 8 3 7,
    .pent 1 7 3 6 8, .pent 2 3 7 4 5, .pent 2 3 7 5 4, .pent 2 4 3 7 5, .pent 2 4 5 3 7, .pent 2 4
    7 3 5, .pent 2 5 4 3 7, .pent 2 3 7 4 6, .pent 2 3 7 6 4, .pent 2 4 3 7 6, .pent 2 4 6 3 7,
    .pent 2 4 7 3 6, .pent 2 6 4 3 7, .pent 2 3 7 4 8, .pent 2 3 7 8 4, .pent 2 4 3 7 8, .pent 2 4
    7 3 8, .pent 2 4 8 3 7, .pent 2 7 3 4 8, .pent 2 3 7 5 6, .pent 2 3 7 6 5, .pent 2 5 3 7 6,
    .pent 2 5 6 3 7, .pent 2 5 7 3 6, .pent 2 6 5 3 7, .pent 2 3 7 5 8, .pent 2 3 7 8 5, .pent 2 5
    3 7 8, .pent 2 5 7 3 8, .pent 2 5 8 3 7, .pent 2 7 3 5 8, .pent 2 3 7 6 8, .pent 2 3 7 8 6,
    .pent 2 6 3 7 8, .pent 2 6 7 3 8, .pent 2 6 8 3 7, .pent 2 7 3 6 8, .pent 3 4 5 6 7, .pent 3 4
    6 5 7, .pent 3 5 4 6 7, .pent 3 5 6 4 7, .pent 3 6 4 5 7, .pent 3 6 5 4 7, .pent 3 4 5 8 7,
    .pent 3 4 8 5 7, .pent 3 5 4 8 7, .pent 3 5 8 4 7, .pent 3 7 4 5 8, .pent 3 7 5 4 8, .pent 3 4
    6 8 7, .pent 3 4 8 6 7, .pent 3 6 4 8 7, .pent 3 6 8 4 7, .pent 3 7 4 6 8, .pent 3 7 6 4 8,
    .pent 3 5 6 8 7, .pent 3 5 8 6 7, .pent 3 6 5 8 7, .pent 3 6 8 5 7, .pent 3 7 5 6 8, .pent 3 7
    6 5 8, .star 3 0 1 2 7, .star 3 0 1 4 7, .star 3 0 1 5 7, .star 3 0 1 6 7, .star 3 0 1 7 8,
    .star 3 0 2 4 7, .star 3 0 2 5 7, .star 3 0 2 6 7, .star 3 0 2 7 8, .star 3 0 4 5 7, .star 3 0
    4 6 7, .star 3 0 4 7 8, .star 3 0 5 6 7, .star 3 0 5 7 8, .star 3 0 6 7 8, .star 3 1 2 4 7,
    .star 3 1 2 5 7, .star 3 1 2 6 7, .star 3 1 2 7 8, .star 3 1 4 5 7, .star 3 1 4 6 7, .star 3 1
    4 7 8, .star 3 1 5 6 7, .star 3 1 5 7 8, .star 3 1 6 7 8, .star 3 2 4 5 7, .star 3 2 4 6 7,
    .star 3 2 4 7 8, .star 3 2 5 6 7, .star 3 2 5 7 8, .star 3 2 6 7 8, .star 3 4 5 6 7, .star 3 4
    5 7 8, .star 3 4 6 7 8, .star 3 5 6 7 8, .star 7 0 1 2 3, .star 7 0 1 3 4, .star 7 0 1 3 5,
    .star 7 0 1 3 6, .star 7 0 1 3 8, .star 7 0 2 3 4, .star 7 0 2 3 5, .star 7 0 2 3 6, .star 7 0
    2 3 8, .star 7 0 3 4 5, .star 7 0 3 4 6, .star 7 0 3 4 8, .star 7 0 3 5 6, .star 7 0 3 5 8,
    .star 7 0 3 6 8, .star 7 1 2 3 4, .star 7 1 2 3 5, .star 7 1 2 3 6, .star 7 1 2 3 8, .star 7 1
    3 4 5, .star 7 1 3 4 6, .star 7 1 3 4 8, .star 7 1 3 5 6, .star 7 1 3 5 8, .star 7 1 3 6 8,
    .star 7 2 3 4 5, .star 7 2 3 4 6, .star 7 2 3 4 8, .star 7 2 3 5 6, .star 7 2 3 5 8, .star 7 2
    3 6 8, .star 7 3 4 5 6, .star 7 3 4 5 8, .star 7 3 4 6 8, .star 7 3 5 6 8],
  [.tri 0 4 7, .tri 1 4 7, .tri 2 4 7, .tri 3 4 7, .tri 4 5 7, .tri 4 6 7, .tri 4 7 8, .pent 0 1 2
    4 7, .pent 0 1 2 7 4, .pent 0 1 4 7 2, .pent 0 1 7 4 2, .pent 0 2 1 4 7, .pent 0 2 1 7 4,
    .pent 0 1 3 4 7, .pent 0 1 3 7 4, .pent 0 1 4 7 3, .pent 0 1 7 4 3, .pent 0 3 1 4 7, .pent 0 3
    1 7 4, .pent 0 1 4 7 5, .pent 0 1 5 4 7, .pent 0 1 5 7 4, .pent 0 1 7 4 5, .pent 0 4 7 1 5,
    .pent 0 5 1 4 7, .pent 0 1 4 7 6, .pent 0 1 6 4 7, .pent 0 1 6 7 4, .pent 0 1 7 4 6, .pent 0 4
    7 1 6, .pent 0 6 1 4 7, .pent 0 1 4 7 8, .pent 0 1 7 4 8, .pent 0 1 8 4 7, .pent 0 1 8 7 4,
    .pent 0 4 7 1 8, .pent 0 7 4 1 8, .pent 0 2 3 4 7, .pent 0 2 3 7 4, .pent 0 2 4 7 3, .pent 0 2
    7 4 3, .pent 0 3 2 4 7, .pent 0 3 2 7 4, .pent 0 2 4 7 5, .pent 0 2 5 4 7, .pent 0 2 5 7 4,
    .pent 0 2 7 4 5, .pent 0 4 7 2 5, .pent 0 5 2 4 7, .pent 0 2 4 7 6, .pent 0 2 6 4 7, .pent 0 2
    6 7 4, .pent 0 2 7 4 6, .pent 0 4 7 2 6, .pent 0 6 2 4 7, .pent 0 2 4 7 8, .pent 0 2 7 4 8,
    .pent 0 2 8 4 7, .pent 0 2 8 7 4, .pent 0 4 7 2 8, .pent 0 7 4 2 8, .pent 0 3 4 7 5, .pent 0 3
    5 4 7, .pent 0 3 5 7 4, .pent 0 3 7 4 5, .pent 0 4 7 3 5, .pent 0 5 3 4 7, .pent 0 3 4 7 6,
    .pent 0 3 6 4 7, .pent 0 3 6 7 4, .pent 0 3 7 4 6, .pent 0 4 7 3 6, .pent 0 6 3 4 7, .pent 0 3
    4 7 8, .pent 0 3 7 4 8, .pent 0 3 8 4 7, .pent 0 3 8 7 4, .pent 0 4 7 3 8, .pent 0 7 4 3 8,
    .pent 0 4 7 5 6, .pent 0 4 7 6 5, .pent 0 5 4 7 6, .pent 0 5 6 4 7, .pent 0 5 7 4 6, .pent 0 6
    5 4 7, .pent 0 4 7 5 8, .pent 0 4 7 8 5, .pent 0 5 4 7 8, .pent 0 5 7 4 8, .pent 0 5 8 4 7,
    .pent 0 7 4 5 8, .pent 0 4 7 6 8, .pent 0 4 7 8 6, .pent 0 6 4 7 8, .pent 0 6 7 4 8, .pent 0 6
    8 4 7, .pent 0 7 4 6 8, .pent 1 2 3 4 7, .pent 1 2 3 7 4, .pent 1 2 4 7 3, .pent 1 2 7 4 3,
    .pent 1 3 2 4 7, .pent 1 3 2 7 4, .pent 1 2 4 7 5, .pent 1 2 5 4 7, .pent 1 2 5 7 4, .pent 1 2
    7 4 5, .pent 1 4 7 2 5, .pent 1 5 2 4 7, .pent 1 2 4 7 6, .pent 1 2 6 4 7, .pent 1 2 6 7 4,
    .pent 1 2 7 4 6, .pent 1 4 7 2 6, .pent 1 6 2 4 7, .pent 1 2 4 7 8, .pent 1 2 7 4 8, .pent 1 2
    8 4 7, .pent 1 2 8 7 4, .pent 1 4 7 2 8, .pent 1 7 4 2 8, .pent 1 3 4 7 5, .pent 1 3 5 4 7,
    .pent 1 3 5 7 4, .pent 1 3 7 4 5, .pent 1 4 7 3 5, .pent 1 5 3 4 7, .pent 1 3 4 7 6, .pent 1 3
    6 4 7, .pent 1 3 6 7 4, .pent 1 3 7 4 6, .pent 1 4 7 3 6, .pent 1 6 3 4 7, .pent 1 3 4 7 8,
    .pent 1 3 7 4 8, .pent 1 3 8 4 7, .pent 1 3 8 7 4, .pent 1 4 7 3 8, .pent 1 7 4 3 8, .pent 1 4
    7 5 6, .pent 1 4 7 6 5, .pent 1 5 4 7 6, .pent 1 5 6 4 7, .pent 1 5 7 4 6, .pent 1 6 5 4 7,
    .pent 1 4 7 5 8, .pent 1 4 7 8 5, .pent 1 5 4 7 8, .pent 1 5 7 4 8, .pent 1 5 8 4 7, .pent 1 7
    4 5 8, .pent 1 4 7 6 8, .pent 1 4 7 8 6, .pent 1 6 4 7 8, .pent 1 6 7 4 8, .pent 1 6 8 4 7,
    .pent 1 7 4 6 8, .pent 2 3 4 7 5, .pent 2 3 5 4 7, .pent 2 3 5 7 4, .pent 2 3 7 4 5, .pent 2 4
    7 3 5, .pent 2 5 3 4 7, .pent 2 3 4 7 6, .pent 2 3 6 4 7, .pent 2 3 6 7 4, .pent 2 3 7 4 6,
    .pent 2 4 7 3 6, .pent 2 6 3 4 7, .pent 2 3 4 7 8, .pent 2 3 7 4 8, .pent 2 3 8 4 7, .pent 2 3
    8 7 4, .pent 2 4 7 3 8, .pent 2 7 4 3 8, .pent 2 4 7 5 6, .pent 2 4 7 6 5, .pent 2 5 4 7 6,
    .pent 2 5 6 4 7, .pent 2 5 7 4 6, .pent 2 6 5 4 7, .pent 2 4 7 5 8, .pent 2 4 7 8 5, .pent 2 5
    4 7 8, .pent 2 5 7 4 8, .pent 2 5 8 4 7, .pent 2 7 4 5 8, .pent 2 4 7 6 8, .pent 2 4 7 8 6,
    .pent 2 6 4 7 8, .pent 2 6 7 4 8, .pent 2 6 8 4 7, .pent 2 7 4 6 8, .pent 3 4 7 5 6, .pent 3 4
    7 6 5, .pent 3 5 4 7 6, .pent 3 5 6 4 7, .pent 3 5 7 4 6, .pent 3 6 5 4 7, .pent 3 4 7 5 8,
    .pent 3 4 7 8 5, .pent 3 5 4 7 8, .pent 3 5 7 4 8, .pent 3 5 8 4 7, .pent 3 7 4 5 8, .pent 3 4
    7 6 8, .pent 3 4 7 8 6, .pent 3 6 4 7 8, .pent 3 6 7 4 8, .pent 3 6 8 4 7, .pent 3 7 4 6 8,
    .pent 4 5 6 8 7, .pent 4 5 8 6 7, .pent 4 6 5 8 7, .pent 4 6 8 5 7, .pent 4 7 5 6 8, .pent 4 7
    6 5 8, .star 4 0 1 2 7, .star 4 0 1 3 7, .star 4 0 1 5 7, .star 4 0 1 6 7, .star 4 0 1 7 8,
    .star 4 0 2 3 7, .star 4 0 2 5 7, .star 4 0 2 6 7, .star 4 0 2 7 8, .star 4 0 3 5 7, .star 4 0
    3 6 7, .star 4 0 3 7 8, .star 4 0 5 6 7, .star 4 0 5 7 8, .star 4 0 6 7 8, .star 4 1 2 3 7,
    .star 4 1 2 5 7, .star 4 1 2 6 7, .star 4 1 2 7 8, .star 4 1 3 5 7, .star 4 1 3 6 7, .star 4 1
    3 7 8, .star 4 1 5 6 7, .star 4 1 5 7 8, .star 4 1 6 7 8, .star 4 2 3 5 7, .star 4 2 3 6 7,
    .star 4 2 3 7 8, .star 4 2 5 6 7, .star 4 2 5 7 8, .star 4 2 6 7 8, .star 4 3 5 6 7, .star 4 3
    5 7 8, .star 4 3 6 7 8, .star 4 5 6 7 8, .star 7 0 1 2 4, .star 7 0 1 3 4, .star 7 0 1 4 5,
    .star 7 0 1 4 6, .star 7 0 1 4 8, .star 7 0 2 3 4, .star 7 0 2 4 5, .star 7 0 2 4 6, .star 7 0
    2 4 8, .star 7 0 3 4 5, .star 7 0 3 4 6, .star 7 0 3 4 8, .star 7 0 4 5 6, .star 7 0 4 5 8,
    .star 7 0 4 6 8, .star 7 1 2 3 4, .star 7 1 2 4 5, .star 7 1 2 4 6, .star 7 1 2 4 8, .star 7 1
    3 4 5, .star 7 1 3 4 6, .star 7 1 3 4 8, .star 7 1 4 5 6, .star 7 1 4 5 8, .star 7 1 4 6 8,
    .star 7 2 3 4 5, .star 7 2 3 4 6, .star 7 2 3 4 8, .star 7 2 4 5 6, .star 7 2 4 5 8, .star 7 2
    4 6 8, .star 7 3 4 5 6, .star 7 3 4 5 8, .star 7 3 4 6 8, .star 7 4 5 6 8],
  [.tri 0 5 7, .tri 1 5 7, .tri 2 5 7, .tri 3 5 7, .tri 4 5 7, .tri 5 6 7, .tri 5 7 8, .pent 0 1 2
    5 7, .pent 0 1 2 7 5, .pent 0 1 5 7 2, .pent 0 1 7 5 2, .pent 0 2 1 5 7, .pent 0 2 1 7 5,
    .pent 0 1 3 5 7, .pent 0 1 3 7 5, .pent 0 1 5 7 3, .pent 0 1 7 5 3, .pent 0 3 1 5 7, .pent 0 3
    1 7 5, .pent 0 1 4 5 7, .pent 0 1 4 7 5, .pent 0 1 5 7 4, .pent 0 1 7 5 4, .pent 0 4 1 5 7,
    .pent 0 4 1 7 5, .pent 0 1 5 7 6, .pent 0 1 6 5 7, .pent 0 1 6 7 5, .pent 0 1 7 5 6, .pent 0 5
    7 1 6, .pent 0 6 1 5 7, .pent 0 1 5 7 8, .pent 0 1 7 5 8, .pent 0 1 8 5 7, .pent 0 1 8 7 5,
    .pent 0 5 7 1 8, .pent 0 7 5 1 8, .pent 0 2 3 5 7, .pent 0 2 3 7 5, .pent 0 2 5 7 3, .pent 0 2
    7 5 3, .pent 0 3 2 5 7, .pent 0 3 2 7 5, .pent 0 2 4 5 7, .pent 0 2 4 7 5, .pent 0 2 5 7 4,
    .pent 0 2 7 5 4, .pent 0 4 2 5 7, .pent 0 4 2 7 5, .pent 0 2 5 7 6, .pent 0 2 6 5 7, .pent 0 2
    6 7 5, .pent 0 2 7 5 6, .pent 0 5 7 2 6, .pent 0 6 2 5 7, .pent 0 2 5 7 8, .pent 0 2 7 5 8,
    .pent 0 2 8 5 7, .pent 0 2 8 7 5, .pent 0 5 7 2 8, .pent 0 7 5 2 8, .pent 0 3 4 5 7, .pent 0 3
    4 7 5, .pent 0 3 5 7 4, .pent 0 3 7 5 4, .pent 0 4 3 5 7, .pent 0 4 3 7 5, .pent 0 3 5 7 6,
    .pent 0 3 6 5 7, .pent 0 3 6 7 5, .pent 0 3 7 5 6, .pent 0 5 7 3 6, .pent 0 6 3 5 7, .pent 0 3
    5 7 8, .pent 0 3 7 5 8, .pent 0 3 8 5 7, .pent 0 3 8 7 5, .pent 0 5 7 3 8, .pent 0 7 5 3 8,
    .pent 0 4 5 7 6, .pent 0 4 6 5 7, .pent 0 4 6 7 5, .pent 0 4 7 5 6, .pent 0 5 7 4 6, .pent 0 6
    4 5 7, .pent 0 4 5 7 8, .pent 0 4 7 5 8, .pent 0 4 8 5 7, .pent 0 4 8 7 5, .pent 0 5 7 4 8,
    .pent 0 7 5 4 8, .pent 0 5 7 6 8, .pent 0 5 7 8 6, .pent 0 6 5 7 8, .pent 0 6 7 5 8, .pent 0 6
    8 5 7, .pent 0 7 5 6 8, .pent 1 2 3 5 7, .pent 1 2 3 7 5, .pent 1 2 5 7 3, .pent 1 2 7 5 3,
    .pent 1 3 2 5 7, .pent 1 3 2 7 5, .pent 1 2 4 5 7, .pent 1 2 4 7 5, .pent 1 2 5 7 4, .pent 1 2
    7 5 4, .pent 1 4 2 5 7, .pent 1 4 2 7 5, .pent 1 2 5 7 6, .pent 1 2 6 5 7, .pent 1 2 6 7 5,
    .pent 1 2 7 5 6, .pent 1 5 7 2 6, .pent 1 6 2 5 7, .pent 1 2 5 7 8, .pent 1 2 7 5 8, .pent 1 2
    8 5 7, .pent 1 2 8 7 5, .pent 1 5 7 2 8, .pent 1 7 5 2 8, .pent 1 3 4 5 7, .pent 1 3 4 7 5,
    .pent 1 3 5 7 4, .pent 1 3 7 5 4, .pent 1 4 3 5 7, .pent 1 4 3 7 5, .pent 1 3 5 7 6, .pent 1 3
    6 5 7, .pent 1 3 6 7 5, .pent 1 3 7 5 6, .pent 1 5 7 3 6, .pent 1 6 3 5 7, .pent 1 3 5 7 8,
    .pent 1 3 7 5 8, .pent 1 3 8 5 7, .pent 1 3 8 7 5, .pent 1 5 7 3 8, .pent 1 7 5 3 8, .pent 1 4
    5 7 6, .pent 1 4 6 5 7, .pent 1 4 6 7 5, .pent 1 4 7 5 6, .pent 1 5 7 4 6, .pent 1 6 4 5 7,
    .pent 1 4 5 7 8, .pent 1 4 7 5 8, .pent 1 4 8 5 7, .pent 1 4 8 7 5, .pent 1 5 7 4 8, .pent 1 7
    5 4 8, .pent 1 5 7 6 8, .pent 1 5 7 8 6, .pent 1 6 5 7 8, .pent 1 6 7 5 8, .pent 1 6 8 5 7,
    .pent 1 7 5 6 8, .pent 2 3 4 5 7, .pent 2 3 4 7 5, .pent 2 3 5 7 4, .pent 2 3 7 5 4, .pent 2 4
    3 5 7, .pent 2 4 3 7 5, .pent 2 3 5 7 6, .pent 2 3 6 5 7, .pent 2 3 6 7 5, .pent 2 3 7 5 6,
    .pent 2 5 7 3 6, .pent 2 6 3 5 7, .pent 2 3 5 7 8, .pent 2 3 7 5 8, .pent 2 3 8 5 7, .pent 2 3
    8 7 5, .pent 2 5 7 3 8, .pent 2 7 5 3 8, .pent 2 4 5 7 6, .pent 2 4 6 5 7, .pent 2 4 6 7 5,
    .pent 2 4 7 5 6, .pent 2 5 7 4 6, .pent 2 6 4 5 7, .pent 2 4 5 7 8, .pent 2 4 7 5 8, .pent 2 4
    8 5 7, .pent 2 4 8 7 5, .pent 2 5 7 4 8, .pent 2 7 5 4 8, .pent 2 5 7 6 8, .pent 2 5 7 8 6,
    .pent 2 6 5 7 8, .pent 2 6 7 5 8, .pent 2 6 8 5 7, .pent 2 7 5 6 8, .pent 3 4 5 7 6, .pent 3 4
    6 5 7, .pent 3 4 6 7 5, .pent 3 4 7 5 6, .pent 3 5 7 4 6, .pent 3 6 4 5 7, .pent 3 4 5 7 8,
    .pent 3 4 7 5 8, .pent 3 4 8 5 7, .pent 3 4 8 7 5, .pent 3 5 7 4 8, .pent 3 7 5 4 8, .pent 3 5
    7 6 8, .pent 3 5 7 8 6, .pent 3 6 5 7 8, .pent 3 6 7 5 8, .pent 3 6 8 5 7, .pent 3 7 5 6 8,
    .pent 4 5 7 6 8, .pent 4 5 7 8 6, .pent 4 6 5 7 8, .pent 4 6 7 5 8, .pent 4 6 8 5 7, .pent 4 7
    5 6 8, .star 5 0 1 2 7, .star 5 0 1 3 7, .star 5 0 1 4 7, .star 5 0 1 6 7, .star 5 0 1 7 8,
    .star 5 0 2 3 7, .star 5 0 2 4 7, .star 5 0 2 6 7, .star 5 0 2 7 8, .star 5 0 3 4 7, .star 5 0
    3 6 7, .star 5 0 3 7 8, .star 5 0 4 6 7, .star 5 0 4 7 8, .star 5 0 6 7 8, .star 5 1 2 3 7,
    .star 5 1 2 4 7, .star 5 1 2 6 7, .star 5 1 2 7 8, .star 5 1 3 4 7, .star 5 1 3 6 7, .star 5 1
    3 7 8, .star 5 1 4 6 7, .star 5 1 4 7 8, .star 5 1 6 7 8, .star 5 2 3 4 7, .star 5 2 3 6 7,
    .star 5 2 3 7 8, .star 5 2 4 6 7, .star 5 2 4 7 8, .star 5 2 6 7 8, .star 5 3 4 6 7, .star 5 3
    4 7 8, .star 5 3 6 7 8, .star 5 4 6 7 8, .star 7 0 1 2 5, .star 7 0 1 3 5, .star 7 0 1 4 5,
    .star 7 0 1 5 6, .star 7 0 1 5 8, .star 7 0 2 3 5, .star 7 0 2 4 5, .star 7 0 2 5 6, .star 7 0
    2 5 8, .star 7 0 3 4 5, .star 7 0 3 5 6, .star 7 0 3 5 8, .star 7 0 4 5 6, .star 7 0 4 5 8,
    .star 7 0 5 6 8, .star 7 1 2 3 5, .star 7 1 2 4 5, .star 7 1 2 5 6, .star 7 1 2 5 8, .star 7 1
    3 4 5, .star 7 1 3 5 6, .star 7 1 3 5 8, .star 7 1 4 5 6, .star 7 1 4 5 8, .star 7 1 5 6 8,
    .star 7 2 3 4 5, .star 7 2 3 5 6, .star 7 2 3 5 8, .star 7 2 4 5 6, .star 7 2 4 5 8, .star 7 2
    5 6 8, .star 7 3 4 5 6, .star 7 3 4 5 8, .star 7 3 5 6 8, .star 7 4 5 6 8],
  [.tri 0 6 7, .tri 1 6 7, .tri 2 6 7, .tri 3 6 7, .tri 4 6 7, .tri 5 6 7, .tri 6 7 8, .pent 0 1 2
    6 7, .pent 0 1 2 7 6, .pent 0 1 6 7 2, .pent 0 1 7 6 2, .pent 0 2 1 6 7, .pent 0 2 1 7 6,
    .pent 0 1 3 6 7, .pent 0 1 3 7 6, .pent 0 1 6 7 3, .pent 0 1 7 6 3, .pent 0 3 1 6 7, .pent 0 3
    1 7 6, .pent 0 1 4 6 7, .pent 0 1 4 7 6, .pent 0 1 6 7 4, .pent 0 1 7 6 4, .pent 0 4 1 6 7,
    .pent 0 4 1 7 6, .pent 0 1 5 6 7, .pent 0 1 5 7 6, .pent 0 1 6 7 5, .pent 0 1 7 6 5, .pent 0 5
    1 6 7, .pent 0 5 1 7 6, .pent 0 1 6 7 8, .pent 0 1 7 6 8, .pent 0 1 8 6 7, .pent 0 1 8 7 6,
    .pent 0 6 7 1 8, .pent 0 7 6 1 8, .pent 0 2 3 6 7, .pent 0 2 3 7 6, .pent 0 2 6 7 3, .pent 0 2
    7 6 3, .pent 0 3 2 6 7, .pent 0 3 2 7 6, .pent 0 2 4 6 7, .pent 0 2 4 7 6, .pent 0 2 6 7 4,
    .pent 0 2 7 6 4, .pent 0 4 2 6 7, .pent 0 4 2 7 6, .pent 0 2 5 6 7, .pent 0 2 5 7 6, .pent 0 2
    6 7 5, .pent 0 2 7 6 5, .pent 0 5 2 6 7, .pent 0 5 2 7 6, .pent 0 2 6 7 8, .pent 0 2 7 6 8,
    .pent 0 2 8 6 7, .pent 0 2 8 7 6, .pent 0 6 7 2 8, .pent 0 7 6 2 8, .pent 0 3 4 6 7, .pent 0 3
    4 7 6, .pent 0 3 6 7 4, .pent 0 3 7 6 4, .pent 0 4 3 6 7, .pent 0 4 3 7 6, .pent 0 3 5 6 7,
    .pent 0 3 5 7 6, .pent 0 3 6 7 5, .pent 0 3 7 6 5, .pent 0 5 3 6 7, .pent 0 5 3 7 6, .pent 0 3
    6 7 8, .pent 0 3 7 6 8, .pent 0 3 8 6 7, .pent 0 3 8 7 6, .pent 0 6 7 3 8, .pent 0 7 6 3 8,
    .pent 0 4 5 6 7, .pent 0 4 5 7 6, .pent 0 4 6 7 5, .pent 0 4 7 6 5, .pent 0 5 4 6 7, .pent 0 5
    4 7 6, .pent 0 4 6 7 8, .pent 0 4 7 6 8, .pent 0 4 8 6 7, .pent 0 4 8 7 6, .pent 0 6 7 4 8,
    .pent 0 7 6 4 8, .pent 0 5 6 7 8, .pent 0 5 7 6 8, .pent 0 5 8 6 7, .pent 0 5 8 7 6, .pent 0 6
    7 5 8, .pent 0 7 6 5 8, .pent 1 2 3 6 7, .pent 1 2 3 7 6, .pent 1 2 6 7 3, .pent 1 2 7 6 3,
    .pent 1 3 2 6 7, .pent 1 3 2 7 6, .pent 1 2 4 6 7, .pent 1 2 4 7 6, .pent 1 2 6 7 4, .pent 1 2
    7 6 4, .pent 1 4 2 6 7, .pent 1 4 2 7 6, .pent 1 2 5 6 7, .pent 1 2 5 7 6, .pent 1 2 6 7 5,
    .pent 1 2 7 6 5, .pent 1 5 2 6 7, .pent 1 5 2 7 6, .pent 1 2 6 7 8, .pent 1 2 7 6 8, .pent 1 2
    8 6 7, .pent 1 2 8 7 6, .pent 1 6 7 2 8, .pent 1 7 6 2 8, .pent 1 3 4 6 7, .pent 1 3 4 7 6,
    .pent 1 3 6 7 4, .pent 1 3 7 6 4, .pent 1 4 3 6 7, .pent 1 4 3 7 6, .pent 1 3 5 6 7, .pent 1 3
    5 7 6, .pent 1 3 6 7 5, .pent 1 3 7 6 5, .pent 1 5 3 6 7, .pent 1 5 3 7 6, .pent 1 3 6 7 8,
    .pent 1 3 7 6 8, .pent 1 3 8 6 7, .pent 1 3 8 7 6, .pent 1 6 7 3 8, .pent 1 7 6 3 8, .pent 1 4
    5 6 7, .pent 1 4 5 7 6, .pent 1 4 6 7 5, .pent 1 4 7 6 5, .pent 1 5 4 6 7, .pent 1 5 4 7 6,
    .pent 1 4 6 7 8, .pent 1 4 7 6 8, .pent 1 4 8 6 7, .pent 1 4 8 7 6, .pent 1 6 7 4 8, .pent 1 7
    6 4 8, .pent 1 5 6 7 8, .pent 1 5 7 6 8, .pent 1 5 8 6 7, .pent 1 5 8 7 6, .pent 1 6 7 5 8,
    .pent 1 7 6 5 8, .pent 2 3 4 6 7, .pent 2 3 4 7 6, .pent 2 3 6 7 4, .pent 2 3 7 6 4, .pent 2 4
    3 6 7, .pent 2 4 3 7 6, .pent 2 3 5 6 7, .pent 2 3 5 7 6, .pent 2 3 6 7 5, .pent 2 3 7 6 5,
    .pent 2 5 3 6 7, .pent 2 5 3 7 6, .pent 2 3 6 7 8, .pent 2 3 7 6 8, .pent 2 3 8 6 7, .pent 2 3
    8 7 6, .pent 2 6 7 3 8, .pent 2 7 6 3 8, .pent 2 4 5 6 7, .pent 2 4 5 7 6, .pent 2 4 6 7 5,
    .pent 2 4 7 6 5, .pent 2 5 4 6 7, .pent 2 5 4 7 6, .pent 2 4 6 7 8, .pent 2 4 7 6 8, .pent 2 4
    8 6 7, .pent 2 4 8 7 6, .pent 2 6 7 4 8, .pent 2 7 6 4 8, .pent 2 5 6 7 8, .pent 2 5 7 6 8,
    .pent 2 5 8 6 7, .pent 2 5 8 7 6, .pent 2 6 7 5 8, .pent 2 7 6 5 8, .pent 3 4 5 6 7, .pent 3 4
    5 7 6, .pent 3 4 6 7 5, .pent 3 4 7 6 5, .pent 3 5 4 6 7, .pent 3 5 4 7 6, .pent 3 4 6 7 8,
    .pent 3 4 7 6 8, .pent 3 4 8 6 7, .pent 3 4 8 7 6, .pent 3 6 7 4 8, .pent 3 7 6 4 8, .pent 3 5
    6 7 8, .pent 3 5 7 6 8, .pent 3 5 8 6 7, .pent 3 5 8 7 6, .pent 3 6 7 5 8, .pent 3 7 6 5 8,
    .pent 4 5 6 7 8, .pent 4 5 7 6 8, .pent 4 5 8 6 7, .pent 4 5 8 7 6, .pent 4 6 7 5 8, .pent 4 7
    6 5 8, .star 6 0 1 2 7, .star 6 0 1 3 7, .star 6 0 1 4 7, .star 6 0 1 5 7, .star 6 0 1 7 8,
    .star 6 0 2 3 7, .star 6 0 2 4 7, .star 6 0 2 5 7, .star 6 0 2 7 8, .star 6 0 3 4 7, .star 6 0
    3 5 7, .star 6 0 3 7 8, .star 6 0 4 5 7, .star 6 0 4 7 8, .star 6 0 5 7 8, .star 6 1 2 3 7,
    .star 6 1 2 4 7, .star 6 1 2 5 7, .star 6 1 2 7 8, .star 6 1 3 4 7, .star 6 1 3 5 7, .star 6 1
    3 7 8, .star 6 1 4 5 7, .star 6 1 4 7 8, .star 6 1 5 7 8, .star 6 2 3 4 7, .star 6 2 3 5 7,
    .star 6 2 3 7 8, .star 6 2 4 5 7, .star 6 2 4 7 8, .star 6 2 5 7 8, .star 6 3 4 5 7, .star 6 3
    4 7 8, .star 6 3 5 7 8, .star 6 4 5 7 8, .star 7 0 1 2 6, .star 7 0 1 3 6, .star 7 0 1 4 6,
    .star 7 0 1 5 6, .star 7 0 1 6 8, .star 7 0 2 3 6, .star 7 0 2 4 6, .star 7 0 2 5 6, .star 7 0
    2 6 8, .star 7 0 3 4 6, .star 7 0 3 5 6, .star 7 0 3 6 8, .star 7 0 4 5 6, .star 7 0 4 6 8,
    .star 7 0 5 6 8, .star 7 1 2 3 6, .star 7 1 2 4 6, .star 7 1 2 5 6, .star 7 1 2 6 8, .star 7 1
    3 4 6, .star 7 1 3 5 6, .star 7 1 3 6 8, .star 7 1 4 5 6, .star 7 1 4 6 8, .star 7 1 5 6 8,
    .star 7 2 3 4 6, .star 7 2 3 5 6, .star 7 2 3 6 8, .star 7 2 4 5 6, .star 7 2 4 6 8, .star 7 2
    5 6 8, .star 7 3 4 5 6, .star 7 3 4 6 8, .star 7 3 5 6 8, .star 7 4 5 6 8],
  [.tri 0 1 8, .tri 0 2 8, .tri 0 3 8, .tri 0 4 8, .tri 0 5 8, .tri 0 6 8, .tri 0 7 8, .pent 0 1 2
    3 8, .pent 0 1 3 2 8, .pent 0 2 1 3 8, .pent 0 2 3 1 8, .pent 0 3 1 2 8, .pent 0 3 2 1 8,
    .pent 0 1 2 4 8, .pent 0 1 4 2 8, .pent 0 2 1 4 8, .pent 0 2 4 1 8, .pent 0 4 1 2 8, .pent 0 4
    2 1 8, .pent 0 1 2 5 8, .pent 0 1 5 2 8, .pent 0 2 1 5 8, .pent 0 2 5 1 8, .pent 0 5 1 2 8,
    .pent 0 5 2 1 8, .pent 0 1 2 6 8, .pent 0 1 6 2 8, .pent 0 2 1 6 8, .pent 0 2 6 1 8, .pent 0 6
    1 2 8, .pent 0 6 2 1 8, .pent 0 1 2 7 8, .pent 0 1 7 2 8, .pent 0 2 1 7 8, .pent 0 2 7 1 8,
    .pent 0 7 1 2 8, .pent 0 7 2 1 8, .pent 0 1 3 4 8, .pent 0 1 4 3 8, .pent 0 3 1 4 8, .pent 0 3
    4 1 8, .pent 0 4 1 3 8, .pent 0 4 3 1 8, .pent 0 1 3 5 8, .pent 0 1 5 3 8, .pent 0 3 1 5 8,
    .pent 0 3 5 1 8, .pent 0 5 1 3 8, .pent 0 5 3 1 8, .pent 0 1 3 6 8, .pent 0 1 6 3 8, .pent 0 3
    1 6 8, .pent 0 3 6 1 8, .pent 0 6 1 3 8, .pent 0 6 3 1 8, .pent 0 1 3 7 8, .pent 0 1 7 3 8,
    .pent 0 3 1 7 8, .pent 0 3 7 1 8, .pent 0 7 1 3 8, .pent 0 7 3 1 8, .pent 0 1 4 5 8, .pent 0 1
    5 4 8, .pent 0 4 1 5 8, .pent 0 4 5 1 8, .pent 0 5 1 4 8, .pent 0 5 4 1 8, .pent 0 1 4 6 8,
    .pent 0 1 6 4 8, .pent 0 4 1 6 8, .pent 0 4 6 1 8, .pent 0 6 1 4 8, .pent 0 6 4 1 8, .pent 0 1
    4 7 8, .pent 0 1 7 4 8, .pent 0 4 1 7 8, .pent 0 4 7 1 8, .pent 0 7 1 4 8, .pent 0 7 4 1 8,
    .pent 0 1 5 6 8, .pent 0 1 6 5 8, .pent 0 5 1 6 8, .pent 0 5 6 1 8, .pent 0 6 1 5 8, .pent 0 6
    5 1 8, .pent 0 1 5 7 8, .pent 0 1 7 5 8, .pent 0 5 1 7 8, .pent 0 5 7 1 8, .pent 0 7 1 5 8,
    .pent 0 7 5 1 8, .pent 0 1 6 7 8, .pent 0 1 7 6 8, .pent 0 6 1 7 8, .pent 0 6 7 1 8, .pent 0 7
    1 6 8, .pent 0 7 6 1 8, .pent 0 2 3 4 8, .pent 0 2 4 3 8, .pent 0 3 2 4 8, .pent 0 3 4 2 8,
    .pent 0 4 2 3 8, .pent 0 4 3 2 8, .pent 0 2 3 5 8, .pent 0 2 5 3 8, .pent 0 3 2 5 8, .pent 0 3
    5 2 8, .pent 0 5 2 3 8, .pent 0 5 3 2 8, .pent 0 2 3 6 8, .pent 0 2 6 3 8, .pent 0 3 2 6 8,
    .pent 0 3 6 2 8, .pent 0 6 2 3 8, .pent 0 6 3 2 8, .pent 0 2 3 7 8, .pent 0 2 7 3 8, .pent 0 3
    2 7 8, .pent 0 3 7 2 8, .pent 0 7 2 3 8, .pent 0 7 3 2 8, .pent 0 2 4 5 8, .pent 0 2 5 4 8,
    .pent 0 4 2 5 8, .pent 0 4 5 2 8, .pent 0 5 2 4 8, .pent 0 5 4 2 8, .pent 0 2 4 6 8, .pent 0 2
    6 4 8, .pent 0 4 2 6 8, .pent 0 4 6 2 8, .pent 0 6 2 4 8, .pent 0 6 4 2 8, .pent 0 2 4 7 8,
    .pent 0 2 7 4 8, .pent 0 4 2 7 8, .pent 0 4 7 2 8, .pent 0 7 2 4 8, .pent 0 7 4 2 8, .pent 0 2
    5 6 8, .pent 0 2 6 5 8, .pent 0 5 2 6 8, .pent 0 5 6 2 8, .pent 0 6 2 5 8, .pent 0 6 5 2 8,
    .pent 0 2 5 7 8, .pent 0 2 7 5 8, .pent 0 5 2 7 8, .pent 0 5 7 2 8, .pent 0 7 2 5 8, .pent 0 7
    5 2 8, .pent 0 2 6 7 8, .pent 0 2 7 6 8, .pent 0 6 2 7 8, .pent 0 6 7 2 8, .pent 0 7 2 6 8,
    .pent 0 7 6 2 8, .pent 0 3 4 5 8, .pent 0 3 5 4 8, .pent 0 4 3 5 8, .pent 0 4 5 3 8, .pent 0 5
    3 4 8, .pent 0 5 4 3 8, .pent 0 3 4 6 8, .pent 0 3 6 4 8, .pent 0 4 3 6 8, .pent 0 4 6 3 8,
    .pent 0 6 3 4 8, .pent 0 6 4 3 8, .pent 0 3 4 7 8, .pent 0 3 7 4 8, .pent 0 4 3 7 8, .pent 0 4
    7 3 8, .pent 0 7 3 4 8, .pent 0 7 4 3 8, .pent 0 3 5 6 8, .pent 0 3 6 5 8, .pent 0 5 3 6 8,
    .pent 0 5 6 3 8, .pent 0 6 3 5 8, .pent 0 6 5 3 8, .pent 0 3 5 7 8, .pent 0 3 7 5 8, .pent 0 5
    3 7 8, .pent 0 5 7 3 8, .pent 0 7 3 5 8, .pent 0 7 5 3 8, .pent 0 3 6 7 8, .pent 0 3 7 6 8,
    .pent 0 6 3 7 8, .pent 0 6 7 3 8, .pent 0 7 3 6 8, .pent 0 7 6 3 8, .pent 0 4 5 6 8, .pent 0 4
    6 5 8, .pent 0 5 4 6 8, .pent 0 5 6 4 8, .pent 0 6 4 5 8, .pent 0 6 5 4 8, .pent 0 4 5 7 8,
    .pent 0 4 7 5 8, .pent 0 5 4 7 8, .pent 0 5 7 4 8, .pent 0 7 4 5 8, .pent 0 7 5 4 8, .pent 0 4
    6 7 8, .pent 0 4 7 6 8, .pent 0 6 4 7 8, .pent 0 6 7 4 8, .pent 0 7 4 6 8, .pent 0 7 6 4 8,
    .pent 0 5 6 7 8, .pent 0 5 7 6 8, .pent 0 6 5 7 8, .pent 0 6 7 5 8, .pent 0 7 5 6 8, .pent 0 7
    6 5 8, .star 0 1 2 3 8, .star 0 1 2 4 8, .star 0 1 2 5 8, .star 0 1 2 6 8, .star 0 1 2 7 8,
    .star 0 1 3 4 8, .star 0 1 3 5 8, .star 0 1 3 6 8, .star 0 1 3 7 8, .star 0 1 4 5 8, .star 0 1
    4 6 8, .star 0 1 4 7 8, .star 0 1 5 6 8, .star 0 1 5 7 8, .star 0 1 6 7 8, .star 0 2 3 4 8,
    .star 0 2 3 5 8, .star 0 2 3 6 8, .star 0 2 3 7 8, .star 0 2 4 5 8, .star 0 2 4 6 8, .star 0 2
    4 7 8, .star 0 2 5 6 8, .star 0 2 5 7 8, .star 0 2 6 7 8, .star 0 3 4 5 8, .star 0 3 4 6 8,
    .star 0 3 4 7 8, .star 0 3 5 6 8, .star 0 3 5 7 8, .star 0 3 6 7 8, .star 0 4 5 6 8, .star 0 4
    5 7 8, .star 0 4 6 7 8, .star 0 5 6 7 8, .star 8 0 1 2 3, .star 8 0 1 2 4, .star 8 0 1 2 5,
    .star 8 0 1 2 6, .star 8 0 1 2 7, .star 8 0 1 3 4, .star 8 0 1 3 5, .star 8 0 1 3 6, .star 8 0
    1 3 7, .star 8 0 1 4 5, .star 8 0 1 4 6, .star 8 0 1 4 7, .star 8 0 1 5 6, .star 8 0 1 5 7,
    .star 8 0 1 6 7, .star 8 0 2 3 4, .star 8 0 2 3 5, .star 8 0 2 3 6, .star 8 0 2 3 7, .star 8 0
    2 4 5, .star 8 0 2 4 6, .star 8 0 2 4 7, .star 8 0 2 5 6, .star 8 0 2 5 7, .star 8 0 2 6 7,
    .star 8 0 3 4 5, .star 8 0 3 4 6, .star 8 0 3 4 7, .star 8 0 3 5 6, .star 8 0 3 5 7, .star 8 0
    3 6 7, .star 8 0 4 5 6, .star 8 0 4 5 7, .star 8 0 4 6 7, .star 8 0 5 6 7],
  [.tri 0 1 8, .tri 1 2 8, .tri 1 3 8, .tri 1 4 8, .tri 1 5 8, .tri 1 6 8, .tri 1 7 8, .pent 0 1 8
    2 3, .pent 0 1 8 3 2, .pent 0 2 1 8 3, .pent 0 2 3 1 8, .pent 0 2 8 1 3, .pent 0 3 2 1 8,
    .pent 0 1 8 2 4, .pent 0 1 8 4 2, .pent 0 2 1 8 4, .pent 0 2 4 1 8, .pent 0 2 8 1 4, .pent 0 4
    2 1 8, .pent 0 1 8 2 5, .pent 0 1 8 5 2, .pent 0 2 1 8 5, .pent 0 2 5 1 8, .pent 0 2 8 1 5,
    .pent 0 5 2 1 8, .pent 0 1 8 2 6, .pent 0 1 8 6 2, .pent 0 2 1 8 6, .pent 0 2 6 1 8, .pent 0 2
    8 1 6, .pent 0 6 2 1 8, .pent 0 1 8 2 7, .pent 0 1 8 7 2, .pent 0 2 1 8 7, .pent 0 2 7 1 8,
    .pent 0 2 8 1 7, .pent 0 7 2 1 8, .pent 0 1 8 3 4, .pent 0 1 8 4 3, .pent 0 3 1 8 4, .pent 0 3
    4 1 8, .pent 0 3 8 1 4, .pent 0 4 3 1 8, .pent 0 1 8 3 5, .pent 0 1 8 5 3, .pent 0 3 1 8 5,
    .pent 0 3 5 1 8, .pent 0 3 8 1 5, .pent 0 5 3 1 8, .pent 0 1 8 3 6, .pent 0 1 8 6 3, .pent 0 3
    1 8 6, .pent 0 3 6 1 8, .pent 0 3 8 1 6, .pent 0 6 3 1 8, .pent 0 1 8 3 7, .pent 0 1 8 7 3,
    .pent 0 3 1 8 7, .pent 0 3 7 1 8, .pent 0 3 8 1 7, .pent 0 7 3 1 8, .pent 0 1 8 4 5, .pent 0 1
    8 5 4, .pent 0 4 1 8 5, .pent 0 4 5 1 8, .pent 0 4 8 1 5, .pent 0 5 4 1 8, .pent 0 1 8 4 6,
    .pent 0 1 8 6 4, .pent 0 4 1 8 6, .pent 0 4 6 1 8, .pent 0 4 8 1 6, .pent 0 6 4 1 8, .pent 0 1
    8 4 7, .pent 0 1 8 7 4, .pent 0 4 1 8 7, .pent 0 4 7 1 8, .pent 0 4 8 1 7, .pent 0 7 4 1 8,
    .pent 0 1 8 5 6, .pent 0 1 8 6 5, .pent 0 5 1 8 6, .pent 0 5 6 1 8, .pent 0 5 8 1 6, .pent 0 6
    5 1 8, .pent 0 1 8 5 7, .pent 0 1 8 7 5, .pent 0 5 1 8 7, .pent 0 5 7 1 8, .pent 0 5 8 1 7,
    .pent 0 7 5 1 8, .pent 0 1 8 6 7, .pent 0 1 8 7 6, .pent 0 6 1 8 7, .pent 0 6 7 1 8, .pent 0 6
    8 1 7, .pent 0 7 6 1 8, .pent 1 2 3 4 8, .pent 1 2 4 3 8, .pent 1 3 2 4 8, .pent 1 3 4 2 8,
    .pent 1 4 2 3 8, .pent 1 4 3 2 8, .pent 1 2 3 5 8, .pent 1 2 5 3 8, .pent 1 3 2 5 8, .pent 1 3
    5 2 8, .pent 1 5 2 3 8, .pent 1 5 3 2 8, .pent 1 2 3 6 8, .pent 1 2 6 3 8, .pent 1 3 2 6 8,
    .pent 1 3 6 2 8, .pent 1 6 2 3 8, .pent 1 6 3 2 8, .pent 1 2 3 7 8, .pent 1 2 7 3 8, .pent 1 3
    2 7 8, .pent 1 3 7 2 8, .pent 1 7 2 3 8, .pent 1 7 3 2 8, .pent 1 2 4 5 8, .pent 1 2 5 4 8,
    .pent 1 4 2 5 8, .pent 1 4 5 2 8, .pent 1 5 2 4 8, .pent 1 5 4 2 8, .pent 1 2 4 6 8, .pent 1 2
    6 4 8, .pent 1 4 2 6 8, .pent 1 4 6 2 8, .pent 1 6 2 4 8, .pent 1 6 4 2 8, .pent 1 2 4 7 8,
    .pent 1 2 7 4 8, .pent 1 4 2 7 8, .pent 1 4 7 2 8, .pent 1 7 2 4 8, .pent 1 7 4 2 8, .pent 1 2
    5 6 8, .pent 1 2 6 5 8, .pent 1 5 2 6 8, .pent 1 5 6 2 8, .pent 1 6 2 5 8, .pent 1 6 5 2 8,
    .pent 1 2 5 7 8, .pent 1 2 7 5 8, .pent 1 5 2 7 8, .pent 1 5 7 2 8, .pent 1 7 2 5 8, .pent 1 7
    5 2 8, .pent 1 2 6 7 8, .pent 1 2 7 6 8, .pent 1 6 2 7 8, .pent 1 6 7 2 8, .pent 1 7 2 6 8,
    .pent 1 7 6 2 8, .pent 1 3 4 5 8, .pent 1 3 5 4 8, .pent 1 4 3 5 8, .pent 1 4 5 3 8, .pent 1 5
    3 4 8, .pent 1 5 4 3 8, .pent 1 3 4 6 8, .pent 1 3 6 4 8, .pent 1 4 3 6 8, .pent 1 4 6 3 8,
    .pent 1 6 3 4 8, .pent 1 6 4 3 8, .pent 1 3 4 7 8, .pent 1 3 7 4 8, .pent 1 4 3 7 8, .pent 1 4
    7 3 8, .pent 1 7 3 4 8, .pent 1 7 4 3 8, .pent 1 3 5 6 8, .pent 1 3 6 5 8, .pent 1 5 3 6 8,
    .pent 1 5 6 3 8, .pent 1 6 3 5 8, .pent 1 6 5 3 8, .pent 1 3 5 7 8, .pent 1 3 7 5 8, .pent 1 5
    3 7 8, .pent 1 5 7 3 8, .pent 1 7 3 5 8, .pent 1 7 5 3 8, .pent 1 3 6 7 8, .pent 1 3 7 6 8,
    .pent 1 6 3 7 8, .pent 1 6 7 3 8, .pent 1 7 3 6 8, .pent 1 7 6 3 8, .pent 1 4 5 6 8, .pent 1 4
    6 5 8, .pent 1 5 4 6 8, .pent 1 5 6 4 8, .pent 1 6 4 5 8, .pent 1 6 5 4 8, .pent 1 4 5 7 8,
    .pent 1 4 7 5 8, .pent 1 5 4 7 8, .pent 1 5 7 4 8, .pent 1 7 4 5 8, .pent 1 7 5 4 8, .pent 1 4
    6 7 8, .pent 1 4 7 6 8, .pent 1 6 4 7 8, .pent 1 6 7 4 8, .pent 1 7 4 6 8, .pent 1 7 6 4 8,
    .pent 1 5 6 7 8, .pent 1 5 7 6 8, .pent 1 6 5 7 8, .pent 1 6 7 5 8, .pent 1 7 5 6 8, .pent 1 7
    6 5 8, .star 1 0 2 3 8, .star 1 0 2 4 8, .star 1 0 2 5 8, .star 1 0 2 6 8, .star 1 0 2 7 8,
    .star 1 0 3 4 8, .star 1 0 3 5 8, .star 1 0 3 6 8, .star 1 0 3 7 8, .star 1 0 4 5 8, .star 1 0
    4 6 8, .star 1 0 4 7 8, .star 1 0 5 6 8, .star 1 0 5 7 8, .star 1 0 6 7 8, .star 1 2 3 4 8,
    .star 1 2 3 5 8, .star 1 2 3 6 8, .star 1 2 3 7 8, .star 1 2 4 5 8, .star 1 2 4 6 8, .star 1 2
    4 7 8, .star 1 2 5 6 8, .star 1 2 5 7 8, .star 1 2 6 7 8, .star 1 3 4 5 8, .star 1 3 4 6 8,
    .star 1 3 4 7 8, .star 1 3 5 6 8, .star 1 3 5 7 8, .star 1 3 6 7 8, .star 1 4 5 6 8, .star 1 4
    5 7 8, .star 1 4 6 7 8, .star 1 5 6 7 8, .star 8 0 1 2 3, .star 8 0 1 2 4, .star 8 0 1 2 5,
    .star 8 0 1 2 6, .star 8 0 1 2 7, .star 8 0 1 3 4, .star 8 0 1 3 5, .star 8 0 1 3 6, .star 8 0
    1 3 7, .star 8 0 1 4 5, .star 8 0 1 4 6, .star 8 0 1 4 7, .star 8 0 1 5 6, .star 8 0 1 5 7,
    .star 8 0 1 6 7, .star 8 1 2 3 4, .star 8 1 2 3 5, .star 8 1 2 3 6, .star 8 1 2 3 7, .star 8 1
    2 4 5, .star 8 1 2 4 6, .star 8 1 2 4 7, .star 8 1 2 5 6, .star 8 1 2 5 7, .star 8 1 2 6 7,
    .star 8 1 3 4 5, .star 8 1 3 4 6, .star 8 1 3 4 7, .star 8 1 3 5 6, .star 8 1 3 5 7, .star 8 1
    3 6 7, .star 8 1 4 5 6, .star 8 1 4 5 7, .star 8 1 4 6 7, .star 8 1 5 6 7],
  [.tri 0 2 8, .tri 1 2 8, .tri 2 3 8, .tri 2 4 8, .tri 2 5 8, .tri 2 6 8, .tri 2 7 8, .pent 0 1 2
    8 3, .pent 0 1 3 2 8, .pent 0 1 3 8 2, .pent 0 1 8 2 3, .pent 0 2 8 1 3, .pent 0 3 1 2 8,
    .pent 0 1 2 8 4, .pent 0 1 4 2 8, .pent 0 1 4 8 2, .pent 0 1 8 2 4, .pent 0 2 8 1 4, .pent 0 4
    1 2 8, .pent 0 1 2 8 5, .pent 0 1 5 2 8, .pent 0 1 5 8 2, .pent 0 1 8 2 5, .pent 0 2 8 1 5,
    .pent 0 5 1 2 8, .pent 0 1 2 8 6, .pent 0 1 6 2 8, .pent 0 1 6 8 2, .pent 0 1 8 2 6, .pent 0 2
    8 1 6, .pent 0 6 1 2 8, .pent 0 1 2 8 7, .pent 0 1 7 2 8, .pent 0 1 7 8 2, .pent 0 1 8 2 7,
    .pent 0 2 8 1 7, .pent 0 7 1 2 8, .pent 0 2 8 3 4, .pent 0 2 8 4 3, .pent 0 3 2 8 4, .pent 0 3
    4 2 8, .pent 0 3 8 2 4, .pent 0 4 3 2 8, .pent 0 2 8 3 5, .pent 0 2 8 5 3, .pent 0 3 2 8 5,
    .pent 0 3 5 2 8, .pent 0 3 8 2 5, .pent 0 5 3 2 8, .pent 0 2 8 3 6, .pent 0 2 8 6 3, .pent 0 3
    2 8 6, .pent 0 3 6 2 8, .pent 0 3 8 2 6, .pent 0 6 3 2 8, .pent 0 2 8 3 7, .pent 0 2 8 7 3,
    .pent 0 3 2 8 7, .pent 0 3 7 2 8, .pent 0 3 8 2 7, .pent 0 7 3 2 8, .pent 0 2 8 4 5, .pent 0 2
    8 5 4, .pent 0 4 2 8 5, .pent 0 4 5 2 8, .pent 0 4 8 2 5, .pent 0 5 4 2 8, .pent 0 2 8 4 6,
    .pent 0 2 8 6 4, .pent 0 4 2 8 6, .pent 0 4 6 2 8, .pent 0 4 8 2 6, .pent 0 6 4 2 8, .pent 0 2
    8 4 7, .pent 0 2 8 7 4, .pent 0 4 2 8 7, .pent 0 4 7 2 8, .pent 0 4 8 2 7, .pent 0 7 4 2 8,
    .pent 0 2 8 5 6, .pent 0 2 8 6 5, .pent 0 5 2 8 6, .pent 0 5 6 2 8, .pent 0 5 8 2 6, .pent 0 6
    5 2 8, .pent 0 2 8 5 7, .pent 0 2 8 7 5, .pent 0 5 2 8 7, .pent 0 5 7 2 8, .pent 0 5 8 2 7,
    .pent 0 7 5 2 8, .pent 0 2 8 6 7, .pent 0 2 8 7 6, .pent 0 6 2 8 7, .pent 0 6 7 2 8, .pent 0 6
    8 2 7, .pent 0 7 6 2 8, .pent 1 2 8 3 4, .pent 1 2 8 4 3, .pent 1 3 2 8 4, .pent 1 3 4 2 8,
    .pent 1 3 8 2 4, .pent 1 4 3 2 8, .pent 1 2 8 3 5, .pent 1 2 8 5 3, .pent 1 3 2 8 5, .pent 1 3
    5 2 8, .pent 1 3 8 2 5, .pent 1 5 3 2 8, .pent 1 2 8 3 6, .pent 1 2 8 6 3, .pent 1 3 2 8 6,
    .pent 1 3 6 2 8, .pent 1 3 8 2 6, .pent 1 6 3 2 8, .pent 1 2 8 3 7, .pent 1 2 8 7 3, .pent 1 3
    2 8 7, .pent 1 3 7 2 8, .pent 1 3 8 2 7, .pent 1 7 3 2 8, .pent 1 2 8 4 5, .pent 1 2 8 5 4,
    .pent 1 4 2 8 5, .pent 1 4 5 2 8, .pent 1 4 8 2 5, .pent 1 5 4 2 8, .pent 1 2 8 4 6, .pent 1 2
    8 6 4, .pent 1 4 2 8 6, .pent 1 4 6 2 8, .pent 1 4 8 2 6, .pent 1 6 4 2 8, .pent 1 2 8 4 7,
    .pent 1 2 8 7 4, .pent 1 4 2 8 7, .pent 1 4 7 2 8, .pent 1 4 8 2 7, .pent 1 7 4 2 8, .pent 1 2
    8 5 6, .pent 1 2 8 6 5, .pent 1 5 2 8 6, .pent 1 5 6 2 8, .pent 1 5 8 2 6, .pent 1 6 5 2 8,
    .pent 1 2 8 5 7, .pent 1 2 8 7 5, .pent 1 5 2 8 7, .pent 1 5 7 2 8, .pent 1 5 8 2 7, .pent 1 7
    5 2 8, .pent 1 2 8 6 7, .pent 1 2 8 7 6, .pent 1 6 2 8 7, .pent 1 6 7 2 8, .pent 1 6 8 2 7,
    .pent 1 7 6 2 8, .pent 2 3 4 5 8, .pent 2 3 5 4 8, .pent 2 4 3 5 8, .pent 2 4 5 3 8, .pent 2 5
    3 4 8, .pent 2 5 4 3 8, .pent 2 3 4 6 8, .pent 2 3 6 4 8, .pent 2 4 3 6 8, .pent 2 4 6 3 8,
    .pent 2 6 3 4 8, .pent 2 6 4 3 8, .pent 2 3 4 7 8, .pent 2 3 7 4 8, .pent 2 4 3 7 8, .pent 2 4
    7 3 8, .pent 2 7 3 4 8, .pent 2 7 4 3 8, .pent 2 3 5 6 8, .pent 2 3 6 5 8, .pent 2 5 3 6 8,
    .pent 2 5 6 3 8, .pent 2 6 3 5 8, .pent 2 6 5 3 8, .pent 2 3 5 7 8, .pent 2 3 7 5 8, .pent 2 5
    3 7 8, .pent 2 5 7 3 8, .pent 2 7 3 5 8, .pent 2 7 5 3 8, .pent 2 3 6 7 8, .pent 2 3 7 6 8,
    .pent 2 6 3 7 8, .pent 2 6 7 3 8, .pent 2 7 3 6 8, .pent 2 7 6 3 8, .pent 2 4 5 6 8, .pent 2 4
    6 5 8, .pent 2 5 4 6 8, .pent 2 5 6 4 8, .pent 2 6 4 5 8, .pent 2 6 5 4 8, .pent 2 4 5 7 8,
    .pent 2 4 7 5 8, .pent 2 5 4 7 8, .pent 2 5 7 4 8, .pent 2 7 4 5 8, .pent 2 7 5 4 8, .pent 2 4
    6 7 8, .pent 2 4 7 6 8, .pent 2 6 4 7 8, .pent 2 6 7 4 8, .pent 2 7 4 6 8, .pent 2 7 6 4 8,
    .pent 2 5 6 7 8, .pent 2 5 7 6 8, .pent 2 6 5 7 8, .pent 2 6 7 5 8, .pent 2 7 5 6 8, .pent 2 7
    6 5 8, .star 2 0 1 3 8, .star 2 0 1 4 8, .star 2 0 1 5 8, .star 2 0 1 6 8, .star 2 0 1 7 8,
    .star 2 0 3 4 8, .star 2 0 3 5 8, .star 2 0 3 6 8, .star 2 0 3 7 8, .star 2 0 4 5 8, .star 2 0
    4 6 8, .star 2 0 4 7 8, .star 2 0 5 6 8, .star 2 0 5 7 8, .star 2 0 6 7 8, .star 2 1 3 4 8,
    .star 2 1 3 5 8, .star 2 1 3 6 8, .star 2 1 3 7 8, .star 2 1 4 5 8, .star 2 1 4 6 8, .star 2 1
    4 7 8, .star 2 1 5 6 8, .star 2 1 5 7 8, .star 2 1 6 7 8, .star 2 3 4 5 8, .star 2 3 4 6 8,
    .star 2 3 4 7 8, .star 2 3 5 6 8, .star 2 3 5 7 8, .star 2 3 6 7 8, .star 2 4 5 6 8, .star 2 4
    5 7 8, .star 2 4 6 7 8, .star 2 5 6 7 8, .star 8 0 1 2 3, .star 8 0 1 2 4, .star 8 0 1 2 5,
    .star 8 0 1 2 6, .star 8 0 1 2 7, .star 8 0 2 3 4, .star 8 0 2 3 5, .star 8 0 2 3 6, .star 8 0
    2 3 7, .star 8 0 2 4 5, .star 8 0 2 4 6, .star 8 0 2 4 7, .star 8 0 2 5 6, .star 8 0 2 5 7,
    .star 8 0 2 6 7, .star 8 1 2 3 4, .star 8 1 2 3 5, .star 8 1 2 3 6, .star 8 1 2 3 7, .star 8 1
    2 4 5, .star 8 1 2 4 6, .star 8 1 2 4 7, .star 8 1 2 5 6, .star 8 1 2 5 7, .star 8 1 2 6 7,
    .star 8 2 3 4 5, .star 8 2 3 4 6, .star 8 2 3 4 7, .star 8 2 3 5 6, .star 8 2 3 5 7, .star 8 2
    3 6 7, .star 8 2 4 5 6, .star 8 2 4 5 7, .star 8 2 4 6 7, .star 8 2 5 6 7],
  [.tri 0 3 8, .tri 1 3 8, .tri 2 3 8, .tri 3 4 8, .tri 3 5 8, .tri 3 6 8, .tri 3 7 8, .pent 0 1 2
    3 8, .pent 0 1 2 8 3, .pent 0 1 3 8 2, .pent 0 1 8 3 2, .pent 0 2 1 3 8, .pent 0 2 1 8 3,
    .pent 0 1 3 8 4, .pent 0 1 4 3 8, .pent 0 1 4 8 3, .pent 0 1 8 3 4, .pent 0 3 8 1 4, .pent 0 4
    1 3 8, .pent 0 1 3 8 5, .pent 0 1 5 3 8, .pent 0 1 5 8 3, .pent 0 1 8 3 5, .pent 0 3 8 1 5,
    .pent 0 5 1 3 8, .pent 0 1 3 8 6, .pent 0 1 6 3 8, .pent 0 1 6 8 3, .pent 0 1 8 3 6, .pent 0 3
    8 1 6, .pent 0 6 1 3 8, .pent 0 1 3 8 7, .pent 0 1 7 3 8, .pent 0 1 7 8 3, .pent 0 1 8 3 7,
    .pent 0 3 8 1 7, .pent 0 7 1 3 8, .pent 0 2 3 8 4, .pent 0 2 4 3 8, .pent 0 2 4 8 3, .pent 0 2
    8 3 4, .pent 0 3 8 2 4, .pent 0 4 2 3 8, .pent 0 2 3 8 5, .pent 0 2 5 3 8, .pent 0 2 5 8 3,
    .pent 0 2 8 3 5, .pent 0 3 8 2 5, .pent 0 5 2 3 8, .pent 0 2 3 8 6, .pent 0 2 6 3 8, .pent 0 2
    6 8 3, .pent 0 2 8 3 6, .pent 0 3 8 2 6, .pent 0 6 2 3 8, .pent 0 2 3 8 7, .pent 0 2 7 3 8,
    .pent 0 2 7 8 3, .pent 0 2 8 3 7, .pent 0 3 8 2 7, .pent 0 7 2 3 8, .pent 0 3 8 4 5, .pent 0 3
    8 5 4, .pent 0 4 3 8 5, .pent 0 4 5 3 8, .pent 0 4 8 3 5, .pent 0 5 4 3 8, .pent 0 3 8 4 6,
    .pent 0 3 8 6 4, .pent 0 4 3 8 6, .pent 0 4 6 3 8, .pent 0 4 8 3 6, .pent 0 6 4 3 8, .pent 0 3
    8 4 7, .pent 0 3 8 7 4, .pent 0 4 3 8 7, .pent 0 4 7 3 8, .pent 0 4 8 3 7, .pent 0 7 4 3 8,
    .pent 0 3 8 5 6, .pent 0 3 8 6 5, .pent 0 5 3 8 6, .pent 0 5 6 3 8, .pent 0 5 8 3 6, .pent 0 6
    5 3 8, .pent 0 3 8 5 7, .pent 0 3 8 7 5, .pent 0 5 3 8 7, .pent 0 5 7 3 8, .pent 0 5 8 3 7,
    .pent 0 7 5 3 8, .pent 0 3 8 6 7, .pent 0 3 8 7 6, .pent 0 6 3 8 7, .pent 0 6 7 3 8, .pent 0 6
    8 3 7, .pent 0 7 6 3 8, .pent 1 2 3 8 4, .pent 1 2 4 3 8, .pent 1 2 4 8 3, .pent 1 2 8 3 4,
    .pent 1 3 8 2 4, .pent 1 4 2 3 8, .pent 1 2 3 8 5, .pent 1 2 5 3 8, .pent 1 2 5 8 3, .pent 1 2
    8 3 5, .pent 1 3 8 2 5, .pent 1 5 2 3 8, .pent 1 2 3 8 6, .pent 1 2 6 3 8, .pent 1 2 6 8 3,
    .pent 1 2 8 3 6, .pent 1 3 8 2 6, .pent 1 6 2 3 8, .pent 1 2 3 8 7, .pent 1 2 7 3 8, .pent 1 2
    7 8 3, .pent 1 2 8 3 7, .pent 1 3 8 2 7, .pent 1 7 2 3 8, .pent 1 3 8 4 5, .pent 1 3 8 5 4,
    .pent 1 4 3 8 5, .pent 1 4 5 3 8, .pent 1 4 8 3 5, .pent 1 5 4 3 8, .pent 1 3 8 4 6, .pent 1 3
    8 6 4, .pent 1 4 3 8 6, .pent 1 4 6 3 8, .pent 1 4 8 3 6, .pent 1 6 4 3 8, .pent 1 3 8 4 7,
    .pent 1 3 8 7 4, .pent 1 4 3 8 7, .pent 1 4 7 3 8, .pent 1 4 8 3 7, .pent 1 7 4 3 8, .pent 1 3
    8 5 6, .pent 1 3 8 6 5, .pent 1 5 3 8 6, .pent 1 5 6 3 8, .pent 1 5 8 3 6, .pent 1 6 5 3 8,
    .pent 1 3 8 5 7, .pent 1 3 8 7 5, .pent 1 5 3 8 7, .pent 1 5 7 3 8, .pent 1 5 8 3 7, .pent 1 7
    5 3 8, .pent 1 3 8 6 7, .pent 1 3 8 7 6, .pent 1 6 3 8 7, .pent 1 6 7 3 8, .pent 1 6 8 3 7,
    .pent 1 7 6 3 8, .pent 2 3 8 4 5, .pent 2 3 8 5 4, .pent 2 4 3 8 5, .pent 2 4 5 3 8, .pent 2 4
    8 3 5, .pent 2 5 4 3 8, .pent 2 3 8 4 6, .pent 2 3 8 6 4, .pent 2 4 3 8 6, .pent 2 4 6 3 8,
    .pent 2 4 8 3 6, .pent 2 6 4 3 8, .pent 2 3 8 4 7, .pent 2 3 8 7 4, .pent 2 4 3 8 7, .pent 2 4
    7 3 8, .pent 2 4 8 3 7, .pent 2 7 4 3 8, .pent 2 3 8 5 6, .pent 2 3 8 6 5, .pent 2 5 3 8 6,
    .pent 2 5 6 3 8, .pent 2 5 8 3 6, .pent 2 6 5 3 8, .pent 2 3 8 5 7, .pent 2 3 8 7 5, .pent 2 5
    3 8 7, .pent 2 5 7 3 8, .pent 2 5 8 3 7, .pent 2 7 5 3 8, .pent 2 3 8 6 7, .pent 2 3 8 7 6,
    .pent 2 6 3 8 7, .pent 2 6 7 3 8, .pent 2 6 8 3 7, .pent 2 7 6 3 8, .pent 3 4 5 6 8, .pent 3 4
    6 5 8, .pent 3 5 4 6 8, .pent 3 5 6 4 8, .pent 3 6 4 5 8, .pent 3 6 5 4 8, .pent 3 4 5 7 8,
    .pent 3 4 7 5 8, .pent 3 5 4 7 8, .pent 3 5 7 4 8, .pent 3 7 4 5 8, .pent 3 7 5 4 8, .pent 3 4
    6 7 8, .pent 3 4 7 6 8, .pent 3 6 4 7 8, .pent 3 6 7 4 8, .pent 3 7 4 6 8, .pent 3 7 6 4 8,
    .pent 3 5 6 7 8, .pent 3 5 7 6 8, .pent 3 6 5 7 8, .pent 3 6 7 5 8, .pent 3 7 5 6 8, .pent 3 7
    6 5 8, .star 3 0 1 2 8, .star 3 0 1 4 8, .star 3 0 1 5 8, .star 3 0 1 6 8, .star 3 0 1 7 8,
    .star 3 0 2 4 8, .star 3 0 2 5 8, .star 3 0 2 6 8, .star 3 0 2 7 8, .star 3 0 4 5 8, .star 3 0
    4 6 8, .star 3 0 4 7 8, .star 3 0 5 6 8, .star 3 0 5 7 8, .star 3 0 6 7 8, .star 3 1 2 4 8,
    .star 3 1 2 5 8, .star 3 1 2 6 8, .star 3 1 2 7 8, .star 3 1 4 5 8, .star 3 1 4 6 8, .star 3 1
    4 7 8, .star 3 1 5 6 8, .star 3 1 5 7 8, .star 3 1 6 7 8, .star 3 2 4 5 8, .star 3 2 4 6 8,
    .star 3 2 4 7 8, .star 3 2 5 6 8, .star 3 2 5 7 8, .star 3 2 6 7 8, .star 3 4 5 6 8, .star 3 4
    5 7 8, .star 3 4 6 7 8, .star 3 5 6 7 8, .star 8 0 1 2 3, .star 8 0 1 3 4, .star 8 0 1 3 5,
    .star 8 0 1 3 6, .star 8 0 1 3 7, .star 8 0 2 3 4, .star 8 0 2 3 5, .star 8 0 2 3 6, .star 8 0
    2 3 7, .star 8 0 3 4 5, .star 8 0 3 4 6, .star 8 0 3 4 7, .star 8 0 3 5 6, .star 8 0 3 5 7,
    .star 8 0 3 6 7, .star 8 1 2 3 4, .star 8 1 2 3 5, .star 8 1 2 3 6, .star 8 1 2 3 7, .star 8 1
    3 4 5, .star 8 1 3 4 6, .star 8 1 3 4 7, .star 8 1 3 5 6, .star 8 1 3 5 7, .star 8 1 3 6 7,
    .star 8 2 3 4 5, .star 8 2 3 4 6, .star 8 2 3 4 7, .star 8 2 3 5 6, .star 8 2 3 5 7, .star 8 2
    3 6 7, .star 8 3 4 5 6, .star 8 3 4 5 7, .star 8 3 4 6 7, .star 8 3 5 6 7],
  [.tri 0 4 8, .tri 1 4 8, .tri 2 4 8, .tri 3 4 8, .tri 4 5 8, .tri 4 6 8, .tri 4 7 8, .pent 0 1 2
    4 8, .pent 0 1 2 8 4, .pent 0 1 4 8 2, .pent 0 1 8 4 2, .pent 0 2 1 4 8, .pent 0 2 1 8 4,
    .pent 0 1 3 4 8, .pent 0 1 3 8 4, .pent 0 1 4 8 3, .pent 0 1 8 4 3, .pent 0 3 1 4 8, .pent 0 3
    1 8 4, .pent 0 1 4 8 5, .pent 0 1 5 4 8, .pent 0 1 5 8 4, .pent 0 1 8 4 5, .pent 0 4 8 1 5,
    .pent 0 5 1 4 8, .pent 0 1 4 8 6, .pent 0 1 6 4 8, .pent 0 1 6 8 4, .pent 0 1 8 4 6, .pent 0 4
    8 1 6, .pent 0 6 1 4 8, .pent 0 1 4 8 7, .pent 0 1 7 4 8, .pent 0 1 7 8 4, .pent 0 1 8 4 7,
    .pent 0 4 8 1 7, .pent 0 7 1 4 8, .pent 0 2 3 4 8, .pent 0 2 3 8 4, .pent 0 2 4 8 3, .pent 0 2
    8 4 3, .pent 0 3 2 4 8, .pent 0 3 2 8 4, .pent 0 2 4 8 5, .pent 0 2 5 4 8, .pent 0 2 5 8 4,
    .pent 0 2 8 4 5, .pent 0 4 8 2 5, .pent 0 5 2 4 8, .pent 0 2 4 8 6, .pent 0 2 6 4 8, .pent 0 2
    6 8 4, .pent 0 2 8 4 6, .pent 0 4 8 2 6, .pent 0 6 2 4 8, .pent 0 2 4 8 7, .pent 0 2 7 4 8,
    .pent 0 2 7 8 4, .pent 0 2 8 4 7, .pent 0 4 8 2 7, .pent 0 7 2 4 8, .pent 0 3 4 8 5, .pent 0 3
    5 4 8, .pent 0 3 5 8 4, .pent 0 3 8 4 5, .pent 0 4 8 3 5, .pent 0 5 3 4 8, .pent 0 3 4 8 6,
    .pent 0 3 6 4 8, .pent 0 3 6 8 4, .pent 0 3 8 4 6, .pent 0 4 8 3 6, .pent 0 6 3 4 8, .pent 0 3
    4 8 7, .pent 0 3 7 4 8, .pent 0 3 7 8 4, .pent 0 3 8 4 7, .pent 0 4 8 3 7, .pent 0 7 3 4 8,
    .pent 0 4 8 5 6, .pent 0 4 8 6 5, .pent 0 5 4 8 6, .pent 0 5 6 4 8, .pent 0 5 8 4 6, .pent 0 6
    5 4 8, .pent 0 4 8 5 7, .pent 0 4 8 7 5, .pent 0 5 4 8 7, .pent 0 5 7 4 8, .pent 0 5 8 4 7,
    .pent 0 7 5 4 8, .pent 0 4 8 6 7, .pent 0 4 8 7 6, .pent 0 6 4 8 7, .pent 0 6 7 4 8, .pent 0 6
    8 4 7, .pent 0 7 6 4 8, .pent 1 2 3 4 8, .pent 1 2 3 8 4, .pent 1 2 4 8 3, .pent 1 2 8 4 3,
    .pent 1 3 2 4 8, .pent 1 3 2 8 4, .pent 1 2 4 8 5, .pent 1 2 5 4 8, .pent 1 2 5 8 4, .pent 1 2
    8 4 5, .pent 1 4 8 2 5, .pent 1 5 2 4 8, .pent 1 2 4 8 6, .pent 1 2 6 4 8, .pent 1 2 6 8 4,
    .pent 1 2 8 4 6, .pent 1 4 8 2 6, .pent 1 6 2 4 8, .pent 1 2 4 8 7, .pent 1 2 7 4 8, .pent 1 2
    7 8 4, .pent 1 2 8 4 7, .pent 1 4 8 2 7, .pent 1 7 2 4 8, .pent 1 3 4 8 5, .pent 1 3 5 4 8,
    .pent 1 3 5 8 4, .pent 1 3 8 4 5, .pent 1 4 8 3 5, .pent 1 5 3 4 8, .pent 1 3 4 8 6, .pent 1 3
    6 4 8, .pent 1 3 6 8 4, .pent 1 3 8 4 6, .pent 1 4 8 3 6, .pent 1 6 3 4 8, .pent 1 3 4 8 7,
    .pent 1 3 7 4 8, .pent 1 3 7 8 4, .pent 1 3 8 4 7, .pent 1 4 8 3 7, .pent 1 7 3 4 8, .pent 1 4
    8 5 6, .pent 1 4 8 6 5, .pent 1 5 4 8 6, .pent 1 5 6 4 8, .pent 1 5 8 4 6, .pent 1 6 5 4 8,
    .pent 1 4 8 5 7, .pent 1 4 8 7 5, .pent 1 5 4 8 7, .pent 1 5 7 4 8, .pent 1 5 8 4 7, .pent 1 7
    5 4 8, .pent 1 4 8 6 7, .pent 1 4 8 7 6, .pent 1 6 4 8 7, .pent 1 6 7 4 8, .pent 1 6 8 4 7,
    .pent 1 7 6 4 8, .pent 2 3 4 8 5, .pent 2 3 5 4 8, .pent 2 3 5 8 4, .pent 2 3 8 4 5, .pent 2 4
    8 3 5, .pent 2 5 3 4 8, .pent 2 3 4 8 6, .pent 2 3 6 4 8, .pent 2 3 6 8 4, .pent 2 3 8 4 6,
    .pent 2 4 8 3 6, .pent 2 6 3 4 8, .pent 2 3 4 8 7, .pent 2 3 7 4 8, .pent 2 3 7 8 4, .pent 2 3
    8 4 7, .pent 2 4 8 3 7, .pent 2 7 3 4 8, .pent 2 4 8 5 6, .pent 2 4 8 6 5, .pent 2 5 4 8 6,
    .pent 2 5 6 4 8, .pent 2 5 8 4 6, .pent 2 6 5 4 8, .pent 2 4 8 5 7, .pent 2 4 8 7 5, .pent 2 5
    4 8 7, .pent 2 5 7 4 8, .pent 2 5 8 4 7, .pent 2 7 5 4 8, .pent 2 4 8 6 7, .pent 2 4 8 7 6,
    .pent 2 6 4 8 7, .pent 2 6 7 4 8, .pent 2 6 8 4 7, .pent 2 7 6 4 8, .pent 3 4 8 5 6, .pent 3 4
    8 6 5, .pent 3 5 4 8 6, .pent 3 5 6 4 8, .pent 3 5 8 4 6, .pent 3 6 5 4 8, .pent 3 4 8 5 7,
    .pent 3 4 8 7 5, .pent 3 5 4 8 7, .pent 3 5 7 4 8, .pent 3 5 8 4 7, .pent 3 7 5 4 8, .pent 3 4
    8 6 7, .pent 3 4 8 7 6, .pent 3 6 4 8 7, .pent 3 6 7 4 8, .pent 3 6 8 4 7, .pent 3 7 6 4 8,
    .pent 4 5 6 7 8, .pent 4 5 7 6 8, .pent 4 6 5 7 8, .pent 4 6 7 5 8, .pent 4 7 5 6 8, .pent 4 7
    6 5 8, .star 4 0 1 2 8, .star 4 0 1 3 8, .star 4 0 1 5 8, .star 4 0 1 6 8, .star 4 0 1 7 8,
    .star 4 0 2 3 8, .star 4 0 2 5 8, .star 4 0 2 6 8, .star 4 0 2 7 8, .star 4 0 3 5 8, .star 4 0
    3 6 8, .star 4 0 3 7 8, .star 4 0 5 6 8, .star 4 0 5 7 8, .star 4 0 6 7 8, .star 4 1 2 3 8,
    .star 4 1 2 5 8, .star 4 1 2 6 8, .star 4 1 2 7 8, .star 4 1 3 5 8, .star 4 1 3 6 8, .star 4 1
    3 7 8, .star 4 1 5 6 8, .star 4 1 5 7 8, .star 4 1 6 7 8, .star 4 2 3 5 8, .star 4 2 3 6 8,
    .star 4 2 3 7 8, .star 4 2 5 6 8, .star 4 2 5 7 8, .star 4 2 6 7 8, .star 4 3 5 6 8, .star 4 3
    5 7 8, .star 4 3 6 7 8, .star 4 5 6 7 8, .star 8 0 1 2 4, .star 8 0 1 3 4, .star 8 0 1 4 5,
    .star 8 0 1 4 6, .star 8 0 1 4 7, .star 8 0 2 3 4, .star 8 0 2 4 5, .star 8 0 2 4 6, .star 8 0
    2 4 7, .star 8 0 3 4 5, .star 8 0 3 4 6, .star 8 0 3 4 7, .star 8 0 4 5 6, .star 8 0 4 5 7,
    .star 8 0 4 6 7, .star 8 1 2 3 4, .star 8 1 2 4 5, .star 8 1 2 4 6, .star 8 1 2 4 7, .star 8 1
    3 4 5, .star 8 1 3 4 6, .star 8 1 3 4 7, .star 8 1 4 5 6, .star 8 1 4 5 7, .star 8 1 4 6 7,
    .star 8 2 3 4 5, .star 8 2 3 4 6, .star 8 2 3 4 7, .star 8 2 4 5 6, .star 8 2 4 5 7, .star 8 2
    4 6 7, .star 8 3 4 5 6, .star 8 3 4 5 7, .star 8 3 4 6 7, .star 8 4 5 6 7],
  [.tri 0 5 8, .tri 1 5 8, .tri 2 5 8, .tri 3 5 8, .tri 4 5 8, .tri 5 6 8, .tri 5 7 8, .pent 0 1 2
    5 8, .pent 0 1 2 8 5, .pent 0 1 5 8 2, .pent 0 1 8 5 2, .pent 0 2 1 5 8, .pent 0 2 1 8 5,
    .pent 0 1 3 5 8, .pent 0 1 3 8 5, .pent 0 1 5 8 3, .pent 0 1 8 5 3, .pent 0 3 1 5 8, .pent 0 3
    1 8 5, .pent 0 1 4 5 8, .pent 0 1 4 8 5, .pent 0 1 5 8 4, .pent 0 1 8 5 4, .pent 0 4 1 5 8,
    .pent 0 4 1 8 5, .pent 0 1 5 8 6, .pent 0 1 6 5 8, .pent 0 1 6 8 5, .pent 0 1 8 5 6, .pent 0 5
    8 1 6, .pent 0 6 1 5 8, .pent 0 1 5 8 7, .pent 0 1 7 5 8, .pent 0 1 7 8 5, .pent 0 1 8 5 7,
    .pent 0 5 8 1 7, .pent 0 7 1 5 8, .pent 0 2 3 5 8, .pent 0 2 3 8 5, .pent 0 2 5 8 3, .pent 0 2
    8 5 3, .pent 0 3 2 5 8, .pent 0 3 2 8 5, .pent 0 2 4 5 8, .pent 0 2 4 8 5, .pent 0 2 5 8 4,
    .pent 0 2 8 5 4, .pent 0 4 2 5 8, .pent 0 4 2 8 5, .pent 0 2 5 8 6, .pent 0 2 6 5 8, .pent 0 2
    6 8 5, .pent 0 2 8 5 6, .pent 0 5 8 2 6, .pent 0 6 2 5 8, .pent 0 2 5 8 7, .pent 0 2 7 5 8,
    .pent 0 2 7 8 5, .pent 0 2 8 5 7, .pent 0 5 8 2 7, .pent 0 7 2 5 8, .pent 0 3 4 5 8, .pent 0 3
    4 8 5, .pent 0 3 5 8 4, .pent 0 3 8 5 4, .pent 0 4 3 5 8, .pent 0 4 3 8 5, .pent 0 3 5 8 6,
    .pent 0 3 6 5 8, .pent 0 3 6 8 5, .pent 0 3 8 5 6, .pent 0 5 8 3 6, .pent 0 6 3 5 8, .pent 0 3
    5 8 7, .pent 0 3 7 5 8, .pent 0 3 7 8 5, .pent 0 3 8 5 7, .pent 0 5 8 3 7, .pent 0 7 3 5 8,
    .pent 0 4 5 8 6, .pent 0 4 6 5 8, .pent 0 4 6 8 5, .pent 0 4 8 5 6, .pent 0 5 8 4 6, .pent 0 6
    4 5 8, .pent 0 4 5 8 7, .pent 0 4 7 5 8, .pent 0 4 7 8 5, .pent 0 4 8 5 7, .pent 0 5 8 4 7,
    .pent 0 7 4 5 8, .pent 0 5 8 6 7, .pent 0 5 8 7 6, .pent 0 6 5 8 7, .pent 0 6 7 5 8, .pent 0 6
    8 5 7, .pent 0 7 6 5 8, .pent 1 2 3 5 8, .pent 1 2 3 8 5, .pent 1 2 5 8 3, .pent 1 2 8 5 3,
    .pent 1 3 2 5 8, .pent 1 3 2 8 5, .pent 1 2 4 5 8, .pent 1 2 4 8 5, .pent 1 2 5 8 4, .pent 1 2
    8 5 4, .pent 1 4 2 5 8, .pent 1 4 2 8 5, .pent 1 2 5 8 6, .pent 1 2 6 5 8, .pent 1 2 6 8 5,
    .pent 1 2 8 5 6, .pent 1 5 8 2 6, .pent 1 6 2 5 8, .pent 1 2 5 8 7, .pent 1 2 7 5 8, .pent 1 2
    7 8 5, .pent 1 2 8 5 7, .pent 1 5 8 2 7, .pent 1 7 2 5 8, .pent 1 3 4 5 8, .pent 1 3 4 8 5,
    .pent 1 3 5 8 4, .pent 1 3 8 5 4, .pent 1 4 3 5 8, .pent 1 4 3 8 5, .pent 1 3 5 8 6, .pent 1 3
    6 5 8, .pent 1 3 6 8 5, .pent 1 3 8 5 6, .pent 1 5 8 3 6, .pent 1 6 3 5 8, .pent 1 3 5 8 7,
    .pent 1 3 7 5 8, .pent 1 3 7 8 5, .pent 1 3 8 5 7, .pent 1 5 8 3 7, .pent 1 7 3 5 8, .pent 1 4
    5 8 6, .pent 1 4 6 5 8, .pent 1 4 6 8 5, .pent 1 4 8 5 6, .pent 1 5 8 4 6, .pent 1 6 4 5 8,
    .pent 1 4 5 8 7, .pent 1 4 7 5 8, .pent 1 4 7 8 5, .pent 1 4 8 5 7, .pent 1 5 8 4 7, .pent 1 7
    4 5 8, .pent 1 5 8 6 7, .pent 1 5 8 7 6, .pent 1 6 5 8 7, .pent 1 6 7 5 8, .pent 1 6 8 5 7,
    .pent 1 7 6 5 8, .pent 2 3 4 5 8, .pent 2 3 4 8 5, .pent 2 3 5 8 4, .pent 2 3 8 5 4, .pent 2 4
    3 5 8, .pent 2 4 3 8 5, .pent 2 3 5 8 6, .pent 2 3 6 5 8, .pent 2 3 6 8 5, .pent 2 3 8 5 6,
    .pent 2 5 8 3 6, .pent 2 6 3 5 8, .pent 2 3 5 8 7, .pent 2 3 7 5 8, .pent 2 3 7 8 5, .pent 2 3
    8 5 7, .pent 2 5 8 3 7, .pent 2 7 3 5 8, .pent 2 4 5 8 6, .pent 2 4 6 5 8, .pent 2 4 6 8 5,
    .pent 2 4 8 5 6, .pent 2 5 8 4 6, .pent 2 6 4 5 8, .pent 2 4 5 8 7, .pent 2 4 7 5 8, .pent 2 4
    7 8 5, .pent 2 4 8 5 7, .pent 2 5 8 4 7, .pent 2 7 4 5 8, .pent 2 5 8 6 7, .pent 2 5 8 7 6,
    .pent 2 6 5 8 7, .pent 2 6 7 5 8, .pent 2 6 8 5 7, .pent 2 7 6 5 8, .pent 3 4 5 8 6, .pent 3 4
    6 5 8, .pent 3 4 6 8 5, .pent 3 4 8 5 6, .pent 3 5 8 4 6, .pent 3 6 4 5 8, .pent 3 4 5 8 7,
    .pent 3 4 7 5 8, .pent 3 4 7 8 5, .pent 3 4 8 5 7, .pent 3 5 8 4 7, .pent 3 7 4 5 8, .pent 3 5
    8 6 7, .pent 3 5 8 7 6, .pent 3 6 5 8 7, .pent 3 6 7 5 8, .pent 3 6 8 5 7, .pent 3 7 6 5 8,
    .pent 4 5 8 6 7, .pent 4 5 8 7 6, .pent 4 6 5 8 7, .pent 4 6 7 5 8, .pent 4 6 8 5 7, .pent 4 7
    6 5 8, .star 5 0 1 2 8, .star 5 0 1 3 8, .star 5 0 1 4 8, .star 5 0 1 6 8, .star 5 0 1 7 8,
    .star 5 0 2 3 8, .star 5 0 2 4 8, .star 5 0 2 6 8, .star 5 0 2 7 8, .star 5 0 3 4 8, .star 5 0
    3 6 8, .star 5 0 3 7 8, .star 5 0 4 6 8, .star 5 0 4 7 8, .star 5 0 6 7 8, .star 5 1 2 3 8,
    .star 5 1 2 4 8, .star 5 1 2 6 8, .star 5 1 2 7 8, .star 5 1 3 4 8, .star 5 1 3 6 8, .star 5 1
    3 7 8, .star 5 1 4 6 8, .star 5 1 4 7 8, .star 5 1 6 7 8, .star 5 2 3 4 8, .star 5 2 3 6 8,
    .star 5 2 3 7 8, .star 5 2 4 6 8, .star 5 2 4 7 8, .star 5 2 6 7 8, .star 5 3 4 6 8, .star 5 3
    4 7 8, .star 5 3 6 7 8, .star 5 4 6 7 8, .star 8 0 1 2 5, .star 8 0 1 3 5, .star 8 0 1 4 5,
    .star 8 0 1 5 6, .star 8 0 1 5 7, .star 8 0 2 3 5, .star 8 0 2 4 5, .star 8 0 2 5 6, .star 8 0
    2 5 7, .star 8 0 3 4 5, .star 8 0 3 5 6, .star 8 0 3 5 7, .star 8 0 4 5 6, .star 8 0 4 5 7,
    .star 8 0 5 6 7, .star 8 1 2 3 5, .star 8 1 2 4 5, .star 8 1 2 5 6, .star 8 1 2 5 7, .star 8 1
    3 4 5, .star 8 1 3 5 6, .star 8 1 3 5 7, .star 8 1 4 5 6, .star 8 1 4 5 7, .star 8 1 5 6 7,
    .star 8 2 3 4 5, .star 8 2 3 5 6, .star 8 2 3 5 7, .star 8 2 4 5 6, .star 8 2 4 5 7, .star 8 2
    5 6 7, .star 8 3 4 5 6, .star 8 3 4 5 7, .star 8 3 5 6 7, .star 8 4 5 6 7],
  [.tri 0 6 8, .tri 1 6 8, .tri 2 6 8, .tri 3 6 8, .tri 4 6 8, .tri 5 6 8, .tri 6 7 8, .pent 0 1 2
    6 8, .pent 0 1 2 8 6, .pent 0 1 6 8 2, .pent 0 1 8 6 2, .pent 0 2 1 6 8, .pent 0 2 1 8 6,
    .pent 0 1 3 6 8, .pent 0 1 3 8 6, .pent 0 1 6 8 3, .pent 0 1 8 6 3, .pent 0 3 1 6 8, .pent 0 3
    1 8 6, .pent 0 1 4 6 8, .pent 0 1 4 8 6, .pent 0 1 6 8 4, .pent 0 1 8 6 4, .pent 0 4 1 6 8,
    .pent 0 4 1 8 6, .pent 0 1 5 6 8, .pent 0 1 5 8 6, .pent 0 1 6 8 5, .pent 0 1 8 6 5, .pent 0 5
    1 6 8, .pent 0 5 1 8 6, .pent 0 1 6 8 7, .pent 0 1 7 6 8, .pent 0 1 7 8 6, .pent 0 1 8 6 7,
    .pent 0 6 8 1 7, .pent 0 7 1 6 8, .pent 0 2 3 6 8, .pent 0 2 3 8 6, .pent 0 2 6 8 3, .pent 0 2
    8 6 3, .pent 0 3 2 6 8, .pent 0 3 2 8 6, .pent 0 2 4 6 8, .pent 0 2 4 8 6, .pent 0 2 6 8 4,
    .pent 0 2 8 6 4, .pent 0 4 2 6 8, .pent 0 4 2 8 6, .pent 0 2 5 6 8, .pent 0 2 5 8 6, .pent 0 2
    6 8 5, .pent 0 2 8 6 5, .pent 0 5 2 6 8, .pent 0 5 2 8 6, .pent 0 2 6 8 7, .pent 0 2 7 6 8,
    .pent 0 2 7 8 6, .pent 0 2 8 6 7, .pent 0 6 8 2 7, .pent 0 7 2 6 8, .pent 0 3 4 6 8, .pent 0 3
    4 8 6, .pent 0 3 6 8 4, .pent 0 3 8 6 4, .pent 0 4 3 6 8, .pent 0 4 3 8 6, .pent 0 3 5 6 8,
    .pent 0 3 5 8 6, .pent 0 3 6 8 5, .pent 0 3 8 6 5, .pent 0 5 3 6 8, .pent 0 5 3 8 6, .pent 0 3
    6 8 7, .pent 0 3 7 6 8, .pent 0 3 7 8 6, .pent 0 3 8 6 7, .pent 0 6 8 3 7, .pent 0 7 3 6 8,
    .pent 0 4 5 6 8, .pent 0 4 5 8 6, .pent 0 4 6 8 5, .pent 0 4 8 6 5, .pent 0 5 4 6 8, .pent 0 5
    4 8 6, .pent 0 4 6 8 7, .pent 0 4 7 6 8, .pent 0 4 7 8 6, .pent 0 4 8 6 7, .pent 0 6 8 4 7,
    .pent 0 7 4 6 8, .pent 0 5 6 8 7, .pent 0 5 7 6 8, .pent 0 5 7 8 6, .pent 0 5 8 6 7, .pent 0 6
    8 5 7, .pent 0 7 5 6 8, .pent 1 2 3 6 8, .pent 1 2 3 8 6, .pent 1 2 6 8 3, .pent 1 2 8 6 3,
    .pent 1 3 2 6 8, .pent 1 3 2 8 6, .pent 1 2 4 6 8, .pent 1 2 4 8 6, .pent 1 2 6 8 4, .pent 1 2
    8 6 4, .pent 1 4 2 6 8, .pent 1 4 2 8 6, .pent 1 2 5 6 8, .pent 1 2 5 8 6, .pent 1 2 6 8 5,
    .pent 1 2 8 6 5, .pent 1 5 2 6 8, .pent 1 5 2 8 6, .pent 1 2 6 8 7, .pent 1 2 7 6 8, .pent 1 2
    7 8 6, .pent 1 2 8 6 7, .pent 1 6 8 2 7, .pent 1 7 2 6 8, .pent 1 3 4 6 8, .pent 1 3 4 8 6,
    .pent 1 3 6 8 4, .pent 1 3 8 6 4, .pent 1 4 3 6 8, .pent 1 4 3 8 6, .pent 1 3 5 6 8, .pent 1 3
    5 8 6, .pent 1 3 6 8 5, .pent 1 3 8 6 5, .pent 1 5 3 6 8, .pent 1 5 3 8 6, .pent 1 3 6 8 7,
    .pent 1 3 7 6 8, .pent 1 3 7 8 6, .pent 1 3 8 6 7, .pent 1 6 8 3 7, .pent 1 7 3 6 8, .pent 1 4
    5 6 8, .pent 1 4 5 8 6, .pent 1 4 6 8 5, .pent 1 4 8 6 5, .pent 1 5 4 6 8, .pent 1 5 4 8 6,
    .pent 1 4 6 8 7, .pent 1 4 7 6 8, .pent 1 4 7 8 6, .pent 1 4 8 6 7, .pent 1 6 8 4 7, .pent 1 7
    4 6 8, .pent 1 5 6 8 7, .pent 1 5 7 6 8, .pent 1 5 7 8 6, .pent 1 5 8 6 7, .pent 1 6 8 5 7,
    .pent 1 7 5 6 8, .pent 2 3 4 6 8, .pent 2 3 4 8 6, .pent 2 3 6 8 4, .pent 2 3 8 6 4, .pent 2 4
    3 6 8, .pent 2 4 3 8 6, .pent 2 3 5 6 8, .pent 2 3 5 8 6, .pent 2 3 6 8 5, .pent 2 3 8 6 5,
    .pent 2 5 3 6 8, .pent 2 5 3 8 6, .pent 2 3 6 8 7, .pent 2 3 7 6 8, .pent 2 3 7 8 6, .pent 2 3
    8 6 7, .pent 2 6 8 3 7, .pent 2 7 3 6 8, .pent 2 4 5 6 8, .pent 2 4 5 8 6, .pent 2 4 6 8 5,
    .pent 2 4 8 6 5, .pent 2 5 4 6 8, .pent 2 5 4 8 6, .pent 2 4 6 8 7, .pent 2 4 7 6 8, .pent 2 4
    7 8 6, .pent 2 4 8 6 7, .pent 2 6 8 4 7, .pent 2 7 4 6 8, .pent 2 5 6 8 7, .pent 2 5 7 6 8,
    .pent 2 5 7 8 6, .pent 2 5 8 6 7, .pent 2 6 8 5 7, .pent 2 7 5 6 8, .pent 3 4 5 6 8, .pent 3 4
    5 8 6, .pent 3 4 6 8 5, .pent 3 4 8 6 5, .pent 3 5 4 6 8, .pent 3 5 4 8 6, .pent 3 4 6 8 7,
    .pent 3 4 7 6 8, .pent 3 4 7 8 6, .pent 3 4 8 6 7, .pent 3 6 8 4 7, .pent 3 7 4 6 8, .pent 3 5
    6 8 7, .pent 3 5 7 6 8, .pent 3 5 7 8 6, .pent 3 5 8 6 7, .pent 3 6 8 5 7, .pent 3 7 5 6 8,
    .pent 4 5 6 8 7, .pent 4 5 7 6 8, .pent 4 5 7 8 6, .pent 4 5 8 6 7, .pent 4 6 8 5 7, .pent 4 7
    5 6 8, .star 6 0 1 2 8, .star 6 0 1 3 8, .star 6 0 1 4 8, .star 6 0 1 5 8, .star 6 0 1 7 8,
    .star 6 0 2 3 8, .star 6 0 2 4 8, .star 6 0 2 5 8, .star 6 0 2 7 8, .star 6 0 3 4 8, .star 6 0
    3 5 8, .star 6 0 3 7 8, .star 6 0 4 5 8, .star 6 0 4 7 8, .star 6 0 5 7 8, .star 6 1 2 3 8,
    .star 6 1 2 4 8, .star 6 1 2 5 8, .star 6 1 2 7 8, .star 6 1 3 4 8, .star 6 1 3 5 8, .star 6 1
    3 7 8, .star 6 1 4 5 8, .star 6 1 4 7 8, .star 6 1 5 7 8, .star 6 2 3 4 8, .star 6 2 3 5 8,
    .star 6 2 3 7 8, .star 6 2 4 5 8, .star 6 2 4 7 8, .star 6 2 5 7 8, .star 6 3 4 5 8, .star 6 3
    4 7 8, .star 6 3 5 7 8, .star 6 4 5 7 8, .star 8 0 1 2 6, .star 8 0 1 3 6, .star 8 0 1 4 6,
    .star 8 0 1 5 6, .star 8 0 1 6 7, .star 8 0 2 3 6, .star 8 0 2 4 6, .star 8 0 2 5 6, .star 8 0
    2 6 7, .star 8 0 3 4 6, .star 8 0 3 5 6, .star 8 0 3 6 7, .star 8 0 4 5 6, .star 8 0 4 6 7,
    .star 8 0 5 6 7, .star 8 1 2 3 6, .star 8 1 2 4 6, .star 8 1 2 5 6, .star 8 1 2 6 7, .star 8 1
    3 4 6, .star 8 1 3 5 6, .star 8 1 3 6 7, .star 8 1 4 5 6, .star 8 1 4 6 7, .star 8 1 5 6 7,
    .star 8 2 3 4 6, .star 8 2 3 5 6, .star 8 2 3 6 7, .star 8 2 4 5 6, .star 8 2 4 6 7, .star 8 2
    5 6 7, .star 8 3 4 5 6, .star 8 3 4 6 7, .star 8 3 5 6 7, .star 8 4 5 6 7],
  [.tri 0 7 8, .tri 1 7 8, .tri 2 7 8, .tri 3 7 8, .tri 4 7 8, .tri 5 7 8, .tri 6 7 8, .pent 0 1 2
    7 8, .pent 0 1 2 8 7, .pent 0 1 7 8 2, .pent 0 1 8 7 2, .pent 0 2 1 7 8, .pent 0 2 1 8 7,
    .pent 0 1 3 7 8, .pent 0 1 3 8 7, .pent 0 1 7 8 3, .pent 0 1 8 7 3, .pent 0 3 1 7 8, .pent 0 3
    1 8 7, .pent 0 1 4 7 8, .pent 0 1 4 8 7, .pent 0 1 7 8 4, .pent 0 1 8 7 4, .pent 0 4 1 7 8,
    .pent 0 4 1 8 7, .pent 0 1 5 7 8, .pent 0 1 5 8 7, .pent 0 1 7 8 5, .pent 0 1 8 7 5, .pent 0 5
    1 7 8, .pent 0 5 1 8 7, .pent 0 1 6 7 8, .pent 0 1 6 8 7, .pent 0 1 7 8 6, .pent 0 1 8 7 6,
    .pent 0 6 1 7 8, .pent 0 6 1 8 7, .pent 0 2 3 7 8, .pent 0 2 3 8 7, .pent 0 2 7 8 3, .pent 0 2
    8 7 3, .pent 0 3 2 7 8, .pent 0 3 2 8 7, .pent 0 2 4 7 8, .pent 0 2 4 8 7, .pent 0 2 7 8 4,
    .pent 0 2 8 7 4, .pent 0 4 2 7 8, .pent 0 4 2 8 7, .pent 0 2 5 7 8, .pent 0 2 5 8 7, .pent 0 2
    7 8 5, .pent 0 2 8 7 5, .pent 0 5 2 7 8, .pent 0 5 2 8 7, .pent 0 2 6 7 8, .pent 0 2 6 8 7,
    .pent 0 2 7 8 6, .pent 0 2 8 7 6, .pent 0 6 2 7 8, .pent 0 6 2 8 7, .pent 0 3 4 7 8, .pent 0 3
    4 8 7, .pent 0 3 7 8 4, .pent 0 3 8 7 4, .pent 0 4 3 7 8, .pent 0 4 3 8 7, .pent 0 3 5 7 8,
    .pent 0 3 5 8 7, .pent 0 3 7 8 5, .pent 0 3 8 7 5, .pent 0 5 3 7 8, .pent 0 5 3 8 7, .pent 0 3
    6 7 8, .pent 0 3 6 8 7, .pent 0 3 7 8 6, .pent 0 3 8 7 6, .pent 0 6 3 7 8, .pent 0 6 3 8 7,
    .pent 0 4 5 7 8, .pent 0 4 5 8 7, .pent 0 4 7 8 5, .pent 0 4 8 7 5, .pent 0 5 4 7 8, .pent 0 5
    4 8 7, .pent 0 4 6 7 8, .pent 0 4 6 8 7, .pent 0 4 7 8 6, .pent 0 4 8 7 6, .pent 0 6 4 7 8,
    .pent 0 6 4 8 7, .pent 0 5 6 7 8, .pent 0 5 6 8 7, .pent 0 5 7 8 6, .pent 0 5 8 7 6, .pent 0 6
    5 7 8, .pent 0 6 5 8 7, .pent 1 2 3 7 8, .pent 1 2 3 8 7, .pent 1 2 7 8 3, .pent 1 2 8 7 3,
    .pent 1 3 2 7 8, .pent 1 3 2 8 7, .pent 1 2 4 7 8, .pent 1 2 4 8 7, .pent 1 2 7 8 4, .pent 1 2
    8 7 4, .pent 1 4 2 7 8, .pent 1 4 2 8 7, .pent 1 2 5 7 8, .pent 1 2 5 8 7, .pent 1 2 7 8 5,
    .pent 1 2 8 7 5, .pent 1 5 2 7 8, .pent 1 5 2 8 7, .pent 1 2 6 7 8, .pent 1 2 6 8 7, .pent 1 2
    7 8 6, .pent 1 2 8 7 6, .pent 1 6 2 7 8, .pent 1 6 2 8 7, .pent 1 3 4 7 8, .pent 1 3 4 8 7,
    .pent 1 3 7 8 4, .pent 1 3 8 7 4, .pent 1 4 3 7 8, .pent 1 4 3 8 7, .pent 1 3 5 7 8, .pent 1 3
    5 8 7, .pent 1 3 7 8 5, .pent 1 3 8 7 5, .pent 1 5 3 7 8, .pent 1 5 3 8 7, .pent 1 3 6 7 8,
    .pent 1 3 6 8 7, .pent 1 3 7 8 6, .pent 1 3 8 7 6, .pent 1 6 3 7 8, .pent 1 6 3 8 7, .pent 1 4
    5 7 8, .pent 1 4 5 8 7, .pent 1 4 7 8 5, .pent 1 4 8 7 5, .pent 1 5 4 7 8, .pent 1 5 4 8 7,
    .pent 1 4 6 7 8, .pent 1 4 6 8 7, .pent 1 4 7 8 6, .pent 1 4 8 7 6, .pent 1 6 4 7 8, .pent 1 6
    4 8 7, .pent 1 5 6 7 8, .pent 1 5 6 8 7, .pent 1 5 7 8 6, .pent 1 5 8 7 6, .pent 1 6 5 7 8,
    .pent 1 6 5 8 7, .pent 2 3 4 7 8, .pent 2 3 4 8 7, .pent 2 3 7 8 4, .pent 2 3 8 7 4, .pent 2 4
    3 7 8, .pent 2 4 3 8 7, .pent 2 3 5 7 8, .pent 2 3 5 8 7, .pent 2 3 7 8 5, .pent 2 3 8 7 5,
    .pent 2 5 3 7 8, .pent 2 5 3 8 7, .pent 2 3 6 7 8, .pent 2 3 6 8 7, .pent 2 3 7 8 6, .pent 2 3
    8 7 6, .pent 2 6 3 7 8, .pent 2 6 3 8 7, .pent 2 4 5 7 8, .pent 2 4 5 8 7, .pent 2 4 7 8 5,
    .pent 2 4 8 7 5, .pent 2 5 4 7 8, .pent 2 5 4 8 7, .pent 2 4 6 7 8, .pent 2 4 6 8 7, .pent 2 4
    7 8 6, .pent 2 4 8 7 6, .pent 2 6 4 7 8, .pent 2 6 4 8 7, .pent 2 5 6 7 8, .pent 2 5 6 8 7,
    .pent 2 5 7 8 6, .pent 2 5 8 7 6, .pent 2 6 5 7 8, .pent 2 6 5 8 7, .pent 3 4 5 7 8, .pent 3 4
    5 8 7, .pent 3 4 7 8 5, .pent 3 4 8 7 5, .pent 3 5 4 7 8, .pent 3 5 4 8 7, .pent 3 4 6 7 8,
    .pent 3 4 6 8 7, .pent 3 4 7 8 6, .pent 3 4 8 7 6, .pent 3 6 4 7 8, .pent 3 6 4 8 7, .pent 3 5
    6 7 8, .pent 3 5 6 8 7, .pent 3 5 7 8 6, .pent 3 5 8 7 6, .pent 3 6 5 7 8, .pent 3 6 5 8 7,
    .pent 4 5 6 7 8, .pent 4 5 6 8 7, .pent 4 5 7 8 6, .pent 4 5 8 7 6, .pent 4 6 5 7 8, .pent 4 6
    5 8 7, .star 7 0 1 2 8, .star 7 0 1 3 8, .star 7 0 1 4 8, .star 7 0 1 5 8, .star 7 0 1 6 8,
    .star 7 0 2 3 8, .star 7 0 2 4 8, .star 7 0 2 5 8, .star 7 0 2 6 8, .star 7 0 3 4 8, .star 7 0
    3 5 8, .star 7 0 3 6 8, .star 7 0 4 5 8, .star 7 0 4 6 8, .star 7 0 5 6 8, .star 7 1 2 3 8,
    .star 7 1 2 4 8, .star 7 1 2 5 8, .star 7 1 2 6 8, .star 7 1 3 4 8, .star 7 1 3 5 8, .star 7 1
    3 6 8, .star 7 1 4 5 8, .star 7 1 4 6 8, .star 7 1 5 6 8, .star 7 2 3 4 8, .star 7 2 3 5 8,
    .star 7 2 3 6 8, .star 7 2 4 5 8, .star 7 2 4 6 8, .star 7 2 5 6 8, .star 7 3 4 5 8, .star 7 3
    4 6 8, .star 7 3 5 6 8, .star 7 4 5 6 8, .star 8 0 1 2 7, .star 8 0 1 3 7, .star 8 0 1 4 7,
    .star 8 0 1 5 7, .star 8 0 1 6 7, .star 8 0 2 3 7, .star 8 0 2 4 7, .star 8 0 2 5 7, .star 8 0
    2 6 7, .star 8 0 3 4 7, .star 8 0 3 5 7, .star 8 0 3 6 7, .star 8 0 4 5 7, .star 8 0 4 6 7,
    .star 8 0 5 6 7, .star 8 1 2 3 7, .star 8 1 2 4 7, .star 8 1 2 5 7, .star 8 1 2 6 7, .star 8 1
    3 4 7, .star 8 1 3 5 7, .star 8 1 3 6 7, .star 8 1 4 5 7, .star 8 1 4 6 7, .star 8 1 5 6 7,
    .star 8 2 3 4 7, .star 8 2 3 5 7, .star 8 2 3 6 7, .star 8 2 4 5 7, .star 8 2 4 6 7, .star 8 2
    5 6 7, .star 8 3 4 5 7, .star 8 3 4 6 7, .star 8 3 5 6 7, .star 8 4 5 6 7]
]

/-- `bigL[e]` packs the 287 masks of `forbS[e]` into 64-bit slots. -/
def bigL : List Nat := [
  0x204100010000000020400801000000002001080100000000004108010000000020400081000000002001008100000000004100810000000020000881000000000040088100000000000108810000000020400011000000002001001100000000004100110000000020000811000000000040081100000000000108110000000020000091000000000040009100000000000100910000000000000891000000002040000500000000200100050000000000410005000000002000080500000000004008050000000000010805000000002000008500000000004000850000000000010085000000000000088500000000200000150000000000400015000000000001001500000000000008150000000000000095000000001020800100000000102004010000000010008401000000000020840100000000102000410000000010008041000000000020804100000000100004410000000000200441000000000000844100000000102000090000000010008009000000000020800900000000100004090000000000200409000000000000840900000000100000490000000000200049000000000000804900000000000004490000000010200003000000001000800300000000002080030000000010000403000000000020040300000000000084030000000010000043000000000020004300000000000080430000000000000443000000001000000b000000000020000b000000000000800b000000000000040b000000000000004b000000082800800100000004282000010000000c0040800100000004184000010000000c002100010000000818010001000000082400040100000002242000010000000a0040040100000002144000010000000a00200801000000081400080100000004201004010000000220108001000000060001040100000002101100010000000600008801000000041010080100000000085004010000000004508001000000000c0104010000000004310001000000000c008801000000000830080100000008220000410000000122200001000000090040004100000001124000010000000900200081000000081200008100000004200800410000000120088001000000050001004100000001100900010000000500008081000000041008008100000000084800410000000002488001000000000a0100410000000002290001000000000a0080810000000008280081000000022000404100000001200044010000000300000841000000011000480100000003000004810000000210004081000000000440404100000000024044010000000006000841000000000220480100000000060004810000000004204081000000000011404100000000000944010000000000180841000000000008c8010000000000180481000000000010c081000000082100000900000000a12000010000000880400009000000009140000100000008802000110000000811000011000000042004000900000000a00480010000000480010009000000009005000100000004800080110000000410040011000000000844000900000000014480010000000009010009000000000125000100000000090080110000000008240011000000022000200900000000a00024010000000280000809000000009000280100000002800004110000000210002011000000000440200900000000014024010000000005000809000000000120280100000000050004110000000004202011000000000011200900000000000524010000000000140809000000000004a8010000000000140411000000000010a011000000012000020900000000a000024100000001800000890000000090000281000000018000005100000001100002110000000002400209000000000140024100000000030000890000000001200281000000000300005100000000022002110000000000090209000000000005024100000000000c0089000000000004828100000000000c005100000000000882110000000000004a090000000000002a41000000000000608900000000000026810000000000006051000000000000461100000008208000030000000060a0000100000008404000030000000050c000010000000840200005000000081080000500000004200200030000000060028001000000044001000300000000500300010000000440008005000000041002000500000000084200030000000000c2800100000000088100030000000000a300010000000008808005000000000822000500000002200010030000000060001401000000024000080300000000500018010000000240000405000000021000100500000000044010030000000000c0140100000000048008030000000000a018010000000004800405000000000420100500000000001110030000000000031401000000000012080300000000000298010000000000120405000000000010900500000001200001030000000060000141000000014000008300000000500001810000000140000045000000011000010500000000024001030000000000c0014100000000028000830000000000a00181000000000280004500000000022001050000000000090103000000000003014100000000000a0083000000000002818100000000000a0045000000000008810500000000000049030000000000001941000000000000508300000000000015810000000000005045000000000000450500000000a0000023000000006000002900000000c0000013000000005000003100000000c000000d000000009000002500000000014000230000000000c0002900000000018000130000000000a00031000000000180000d00000000012000250000000000050023000000000003002900000000000600130000000000028031000000000006000d00000000000480250000000000002823000000000000182900000000000030130000000000001431000000000000300d000000000000242500000000000002a300000000000001a900000000000003130000000000000171000000000000030d00000000000002650000000030000001000000000060000100000000000180010000000000000c0100000000000000c100000000000000190000000000000007,
  0x4082000200000000408010020000000040021002000000000082100200000000408001020000000040020102000000000082010200000000400011020000000000801102000000000002110200000000408000220000000040020022000000000082002200000000400010220000000000801022000000000002102200000000400001220000000000800122000000000002012200000000000011220000000040800006000000004002000600000000008200060000000040001006000000000080100600000000000210060000000040000106000000000080010600000000000201060000000000001106000000004000002600000000008000260000000000020026000000000000102600000000000001260000000010208002000000001020040200000000100084020000000000208402000000001020004200000000100080420000000000208042000000001000044200000000002004420000000000008442000000001020000a000000001000800a000000000020800a000000001000040a000000000020040a000000000000840a000000001000004a000000000020004a000000000000804a000000000000044a0000000010200003000000001000800300000000002080030000000010000403000000000020040300000000000084030000000010000043000000000020004300000000000080430000000000000443000000001000000b000000000020000b000000000000800b000000000000040b000000000000004b000000084800800200000004482000020000000c0080800200000004188000020000000c002200020000000818020002000000084400040200000002442000020000000a0080040200000002148000020000000a00201002000000081400100200000004401004020000000240108002000000060002040200000002101200020000000600009002000000041010100200000000089004020000000004908002000000000c0204020000000004320002000000000c009002000000000830100200000008420000420000000142200002000000090080004200000001128000020000000900200102000000081200010200000004400800420000000140088002000000050002004200000001100a00020000000500008102000000041008010200000000088800420000000002888002000000000a02004200000000022a0002000000000a0081020000000008280102000000024000404200000001400044020000000300001042000000011000500200000003000005020000000210004102000000000480404200000000028044020000000006001042000000000220500200000000060005020000000004204102000000000012404200000000000a44020000000000181042000000000008d0020000000000180502000000000010c102000000084100000a00000000c1200002000000088080000a000000009180000200000008802000220000000811000022000000044004000a00000000c0048002000000048002000a000000009006000200000004800080220000000410040022000000000884000a0000000001848002000000000902000a000000000126000200000000090080220000000008240022000000024000200a00000000c0002402000000028000100a000000009000300200000002800004220000000210002022000000000480200a0000000001802402000000000500100a000000000120300200000000050004220000000004202022000000000012200a0000000000062402000000000014100a000000000004b0020000000000140422000000000010a022000000014000020a00000000c0000242000000018000010a000000009000030200000001800000620000000110000222000000000280020a0000000001800242000000000300010a00000000012003020000000003000062000000000220022200000000000a020a000000000006024200000000000c010a000000000004830200000000000c00620000000000088222000000000000520a0000000000003242000000000000610a00000000000027020000000000006062000000000000462200000000606000020000000030c0000200000008202000060000000810400006000000082080000300000008404000030000000060018002000000003003000200000004200080060000000410010006000000042002000300000004400100030000000000c18002000000000063000200000000084080060000000008210006000000000842000300000000088100030000000060000c02000000003000180200000002200004060000000210000806000000022000100300000002400008030000000000c00c02000000000060180200000000044004060000000004200806000000000440100300000000048008030000000000030c020000000000019802000000000011040600000000001088060000000000111003000000000012080300000000600000c2000000003000018200000001200000460000000110000086000000012000010300000001400000830000000000c000c20000000000600182000000000240004600000000022000860000000002400103000000000280008300000000000300c2000000000001818200000000000900460000000000088086000000000009010300000000000a008300000000000018c20000000000000d820000000000004846000000000000448600000000000049030000000000005083000000006000001a000000003000003200000000a000000e000000009000001600000000a000002300000000c00000130000000000c0001a0000000000600032000000000140000e000000000120001600000000014000230000000001800013000000000003001a0000000000018032000000000005000e000000000004801600000000000500230000000000060013000000000000181a0000000000000c32000000000000280e000000000000241600000000000028230000000000003013000000000000019a00000000000000f2000000000000028e000000000000025600000000000002a3000000000000031300000000500000020000000000a00002000000000002800200000000000014020000000000000142000000000000002a0000000000000007,
  0x40820004000000004080100400000000400210040000000000821004000000004080010400000000400201040000000000820104000000004000110400000000008011040000000000021104000000004080002400000000400200240000000000820024000000004000102400000000008010240000000000021024000000004000012400000000008001240000000000020124000000000000112400000000408000060000000040020006000000000082000600000000400010060000000000801006000000000002100600000000400001060000000000800106000000000002010600000000000011060000000040000026000000000080002600000000000200260000000000001026000000000000012600000000204100040000000020400804000000002001080400000000004108040000000020400084000000002001008400000000004100840000000020000884000000000040088400000000000108840000000020400014000000002001001400000000004100140000000020000814000000000040081400000000000108140000000020000094000000000040009400000000000100940000000000000894000000002040000500000000200100050000000000410005000000002000080500000000004008050000000000010805000000002000008500000000004000850000000000010085000000000000088500000000200000150000000000400015000000000001001500000000000008150000000000000095000000084801000400000004484000040000000c0081000400000004288000040000000c004200040000000828020004000000084400080400000002444000040000000a0080080400000002248000040000000a00401004000000082400100400000004401008040000000240110004000000060002080400000002201200040000000600011004000000042010100400000000089008040000000004910004000000000c0208040000000004520004000000000c011004000000000850100400000008420000840000000142400004000000090080008400000001228000040000000900400104000000082200010400000004400800840000000140090004000000050002008400000001200a00040000000500010104000000042008010400000000088800840000000002890004000000000a02008400000000024a0004000000000a0101040000000008480104000000024000408400000001400048040000000300001084000000012000500400000003000009040000000220004104000000000480408400000000028048040000000006001084000000000240500400000000060009040000000004404104000000000012408400000000000a48040000000000181084000000000009500400000000001809040000000000114104000000084100001400000000c1400004000000088080001400000000a180000400000008804000240000000821000024000000044004001400000000c0050004000000048002001400000000a006000400000004800100240000000420040024000000000884001400000000018500040000000009020014000000000146000400000000090100240000000008440024000000024000201400000000c0002804000000028000101400000000a000300400000002800008240000000220002024000000000480201400000000018028040000000005001014000000000140300400000000050008240000000004402024000000000012201400000000000628040000000000141014000000000005300400000000001408240000000000112024000000014000021400000000c0000284000000018000011400000000a000030400000001800000a40000000120000224000000000280021400000000018002840000000003000114000000000140030400000000030000a4000000000240022400000000000a0214000000000006028400000000000c0114000000000005030400000000000c00a400000000000902240000000000005214000000000000328400000000000061140000000000002b0400000000000060a40000000000004a240000000030a000040000000050600004000000082020000600000008104000060000000840200005000000081080000500000000300280040000000050018004000000042000800600000004100100060000000440008005000000041002000500000000006280040000000000a18004000000000840800600000000082100060000000008808005000000000822000500000000300014040000000050000c04000000022000040600000002100008060000000240000405000000021000100500000000006014040000000000a00c04000000000440040600000000042008060000000004800405000000000420100500000000000194040000000000028c040000000000110406000000000010880600000000001204050000000000109005000000003000014400000000500000c4000000012000004600000001100000860000000140000045000000011000010500000000006001440000000000a000c40000000002400046000000000220008600000000028000450000000002200105000000000001814400000000000280c40000000000090046000000000008808600000000000a004500000000000881050000000000000d4400000000000014c40000000000004846000000000000448600000000000050450000000000004505000000003000002c000000005000001c00000000a000000e000000009000001600000000c000000d0000000090000025000000000060002c0000000000a0001c000000000140000e0000000001200016000000000180000d0000000001200025000000000001802c000000000002801c000000000005000e0000000000048016000000000006000d00000000000480250000000000000c2c000000000000141c000000000000280e0000000000002416000000000000300d000000000000242500000000000000ec000000000000015c000000000000028e0000000000000256000000000000030d000000000000026500000000600000040000000000c0000400000000000300040000000000001804000000000000018400000000000000340000000000000007,
  0x8104000800000000810020080000000080042008000000000104200800000000810002080000000080040208000000000104020800000000800022080000000001002208000000000004220800000000810000280000000080040028000000000104002800000000800020280000000001002028000000000004202800000000800002280000000001000228000000000004022800000000000022280000000081000018000000008004001800000000010400180000000080002018000000000100201800000000000420180000000080000218000000000100021800000000000402180000000000002218000000008000003800000000010000380000000000040038000000000000203800000000000002380000000010208008000000001020040800000000100084080000000000208408000000001020004800000000100080480000000000208048000000001000044800000000002004480000000000008448000000001020000a000000001000800a000000000020800a000000001000040a000000000020040a000000000000840a000000001000004a000000000020004a000000000000804a000000000000044a0000000010200009000000001000800900000000002080090000000010000409000000000020040900000000000084090000000010000049000000000020004900000000000080490000000000000449000000001000000b000000000020000b000000000000800b000000000000040b000000000000004b000000088800800800000004882000080000000c0100800800000004190000080000000c002400080000000818040008000000088400040800000002842000080000000a0100040800000002150000080000000a0020200800000008140020080000000480100408000000028010800800000006000404080000000210140008000000060000a008000000041010200800000000091004080000000005108008000000000c0404080000000004340008000000000c00a008000000000830200800000008820000480000000182200008000000090100004800000001130000080000000900200208000000081200020800000004800800480000000180088008000000050004004800000001100c00080000000500008208000000041008020800000000090800480000000003088008000000000a04004800000000022c0008000000000a0082080000000008280208000000028000404800000001800044080000000300002048000000011000600800000003000006080000000210004208000000000500404800000000030044080000000006002048000000000220600800000000060006080000000004204208000000000014404800000000000c44080000000000182048000000000008e0080000000000180608000000000010c20800000000c0a00008000000005180000800000008402000280000000810800028000000084100000a000000088080000a00000000c0028008000000005006000800000004400080280000000410020028000000044004000a000000048002000a00000000018280080000000000a6000800000000088080280000000008220028000000000884000a000000000902000a00000000c0001408000000005000300800000002400004280000000210001028000000024000200a000000028000100a00000000018014080000000000a0300800000000048004280000000004201028000000000480200a000000000500100a0000000000061408000000000002b00800000000001204280000000000109028000000000012200a000000000014100a00000000c0000148000000005000030800000001400000680000000110000128000000014000020a000000018000010a00000000018001480000000000a0030800000000028000680000000002200128000000000280020a000000000300010a0000000000060148000000000002830800000000000a0068000000000008812800000000000a020a00000000000c010a0000000000003148000000000000170800000000000050680000000000004528000000000000520a000000000000610a00000000a06000080000000031400008000000082020001800000008104000180000000821000009000000088040000900000000a00180080000000030050008000000042000801800000004100100180000000420040009000000048001000900000000014180080000000000650008000000000840801800000000082100180000000008440009000000000901000900000000a0000c08000000003000280800000002200004180000000210000818000000022000200900000002800008090000000001400c08000000000060280800000000044004180000000004200818000000000440200900000000050008090000000000050c08000000000001a808000000000011041800000000001088180000000000112009000000000014080900000000a00000c80000000030000288000000012000005800000001100000980000000120000209000000018000008900000000014000c80000000000600288000000000240005800000000022000980000000002400209000000000300008900000000000500c8000000000001828800000000000900580000000000088098000000000009020900000000000c008900000000000028c80000000000000e88000000000000485800000000000044980000000000004a090000000000006089000000003000002c000000005000001c000000006000001a00000000a000000e000000006000002900000000c000000d000000000060002c0000000000a0001c0000000000c0001a000000000140000e0000000000c00029000000000180000d000000000001802c000000000002801c000000000003001a000000000005000e0000000000030029000000000006000d0000000000000c2c000000000000141c000000000000181a000000000000280e0000000000001829000000000000300d00000000000000ec000000000000015c000000000000019a000000000000028e00000000000001a9000000000000030d00000000900000080000000001200008000000000004800800000000000024080000000000000248000000000000002a0000000000000019,
  0x81040010000000008100201000000000800420100000000001042010000000008100021000000000800402100000000001040210000000008000221000000000010022100000000000042210000000008100003000000000800400300000000001040030000000008000203000000000010020300000000000042030000000008000023000000000010002300000000000040230000000000000223000000000810000180000000080040018000000000104001800000000800020180000000001002018000000000004201800000000800002180000000001000218000000000004021800000000000022180000000080000038000000000100003800000000000400380000000000002038000000000000023800000000204100100000000020400810000000002001081000000000004108100000000020400090000000002001009000000000004100900000000020000890000000000040089000000000000108900000000020400014000000002001001400000000004100140000000020000814000000000040081400000000000108140000000020000094000000000040009400000000000100940000000000000894000000002040001100000000200100110000000000410011000000002000081100000000004008110000000000010811000000002000009100000000004000910000000000010091000000000000089100000000200000150000000000400015000000000001001500000000000008150000000000000095000000088801001000000004884000100000000c0101001000000004290000100000000c004400100000000828040010000000088400081000000002844000100000000a0100081000000002250000100000000a00402010000000082400201000000004801008100000000280110010000000060004081000000002201400100000000600012010000000042010201000000000091008100000000005110010000000000c0408100000000004540010000000000c012010000000000850201000000008820000900000000182400010000000090100009000000001230000100000000900400210000000082200021000000004800800900000000180090010000000050004009000000001200c00100000000500010210000000042008021000000000090800900000000003090010000000000a04009000000000024c0010000000000a010210000000000848021000000002800040900000000180004810000000030000209000000001200060100000000300000a10000000022000421000000000050040900000000003004810000000000600209000000000024060100000000006000a100000000004404210000000000014409000000000000c4810000000000018209000000000000960100000000000180a10000000000011421000000000c0c000100000000061800010000000084040003000000008208000300000000841000014000000088080001400000000c00300100000000060060010000000044001003000000004200200300000000440040014000000048002001400000000018300100000000000c60010000000000881003000000000084200300000000008840014000000000902001400000000c00018100000000060003010000000024000083000000002200010300000000240002014000000028000101400000000018018100000000000c03010000000000480083000000000044010300000000004802014000000000500101400000000000618100000000000033010000000000012083000000000001110300000000000122014000000000014101400000000c0000190000000006000031000000001400000b000000001200001300000000140000214000000018000011400000000018001900000000000c0031000000000028000b00000000002400130000000000280021400000000030001140000000000060190000000000003031000000000000a00b0000000000009013000000000000a021400000000000c011400000000000031900000000000001b1000000000000050b000000000000049300000000000005214000000000000611400000000312000100000000090600010000000082020001800000008104000180000000880200011000000081100001100000000300480100000000090018010000000042000801800000004100100180000000480008011000000041004001100000000006480100000000001218010000000000840801800000000082100180000000009008011000000000824001100000000300024100000000090000c10000000022000041800000002100008180000000280000411000000021000201100000000006024100000000001200c100000000004400418000000000420081800000000050004110000000004202011000000000001a4100000000000048c10000000000011041800000000001088180000000000140411000000000010a011000000003000025000000000900000d00000000120000058000000011000009800000001800000510000000110000211000000000060025000000000012000d00000000002400058000000000220009800000000030000510000000002200211000000000001825000000000000480d00000000000090058000000000008809800000000000c005100000000000882110000000000000e5000000000000024d00000000000004858000000000000449800000000000060510000000000004611000000005000001c000000006000001a0000000030000032000000009000001600000000c000001300000000500000310000000000a0001c0000000000c0001a0000000000600032000000000120001600000000018000130000000000a00031000000000002801c000000000003001a0000000000018032000000000004801600000000000600130000000000028031000000000000141c000000000000181a0000000000000c32000000000000241600000000000030130000000000001431000000000000015c000000000000019a00000000000000f200000000000002560000000000000313000000000000017100000000a0000010000000000140001000000000000500100000000000002810000000000000029000000000000000340000000000000019,
  0x81040020000000008100202000000000800420200000000001042020000000008100022000000000800402200000000001040220000000008000222000000000010022200000000000042220000000008100003000000000800400300000000001040030000000008000203000000000010020300000000000042030000000008000023000000000010002300000000000040230000000000000223000000000810000280000000080040028000000000104002800000000800020280000000001002028000000000004202800000000800002280000000001000228000000000004022800000000000022280000000080000038000000000100003800000000000400380000000000002038000000000000023800000000408200200000000040801020000000004002102000000000008210200000000040800120000000004002012000000000008201200000000040001120000000000080112000000000000211200000000040800024000000004002002400000000008200240000000040001024000000000080102400000000000210240000000040000124000000000080012400000000000201240000000000001124000000004080002200000000400200220000000000820022000000004000102200000000008010220000000000021022000000004000012200000000008001220000000000020122000000000000112200000000400000260000000000800026000000000002002600000000000010260000000000000126000000088802002000000004888000200000000c0102002000000004490000200000000c008400200000000848040020000000088400102000000002848000200000000a0100102000000002450000200000000a00802020000000084400202000000004801010200000000280120020000000060004102000000002401400200000000600022020000000044010202000000000091010200000000005120020000000000c0410200000000004940020000000000c0220200000000008902020000000088200012000000001828000200000000901000120000000014300002000000009008002200000000842000220000000048008012000000001800a0020000000050004012000000001400c002000000005000202200000000440080220000000000908012000000000030a0020000000000a04012000000000028c0020000000000a0202200000000008880220000000028000412000000001800050200000000300002120000000014000602000000003000012200000000240004220000000000500412000000000030050200000000006002120000000000280602000000000060012200000000004804220000000000014412000000000000c5020000000000018212000000000000a602000000000001812200000000000124220000000006140002000000000a0c000200000000840400030000000082080003000000008804000240000000821000024000000006005002000000000a003002000000004400100300000000420020030000000048001002400000004200400240000000000c5002000000000014300200000000008810030000000000842003000000000090100240000000008440024000000006000282000000000a000182000000002400008300000000220001030000000028000082400000002200020240000000000c028200000000001401820000000000480083000000000044010300000000005000824000000000440202400000000000328200000000000051820000000000012083000000000001110300000000000140824000000000011202400000000600002a000000000a00001a000000001400000b0000000012000013000000001800000a400000001200002240000000000c002a000000000014001a000000000028000b0000000000240013000000000030000a4000000000240022400000000000302a000000000000501a000000000000a00b0000000000009013000000000000c00a400000000000902240000000000001aa000000000000029a000000000000050b0000000000000493000000000000060a40000000000004a2400000000512000200000000090a0002000000008402000280000000810800028000000088020002200000008110000220000000050048020000000009002802000000004400080280000000410020028000000048000802200000004100400220000000000a48020000000000122802000000000088080280000000008220028000000000900802200000000082400220000000050002420000000009000142000000002400004280000000210001028000000028000042200000002100020220000000000a0242000000000012014200000000004800428000000000420102800000000050004220000000004202022000000000002a4200000000000049420000000000012042800000000001090280000000000140422000000000010a0220000000050000260000000009000016000000001400000680000000110000128000000018000006200000001100002220000000000a00260000000000120016000000000028000680000000002200128000000000300006200000000022002220000000000028260000000000004816000000000000a0068000000000008812800000000000c00620000000000088222000000000000166000000000000025600000000000005068000000000000452800000000000060620000000000004622000000003000002c000000003000003200000000a0000023000000006000002900000000500000310000000090000025000000000060002c000000000060003200000000014000230000000000c000290000000000a000310000000001200025000000000001802c000000000001803200000000000500230000000000030029000000000002803100000000000480250000000000000c2c0000000000000c32000000000000282300000000000018290000000000001431000000000000242500000000000000ec00000000000000f200000000000002a300000000000001a90000000000000171000000000000026500000000c000002000000000018000200000000000060020000000000000302000000000000003200000000000000034000000000000002a,
  0x102080040000000010200404000000001000840400000000002084040000000010200024000000001000802400000000002080240000000010000424000000000020042400000000000084240000000010200014000000001000801400000000002080140000000010000414000000000020041400000000000084140000000010000034000000000020003400000000000080340000000000000434000000001020000c000000001000800c000000000020800c000000001000040c000000000020040c000000000000840c000000001000002c000000000020002c000000000000802c000000000000042c000000001000001c000000000020001c000000000000801c000000000000041c000000000000003c00000000010208040000000001020044000000000100084400000000000208440000000001020004800000000100080480000000000208048000000001000044800000000002004480000000000008448000000001020004200000000100080420000000000208042000000001000044200000000002004420000000000008442000000001000004a000000000020004a000000000000804a000000000000044a00000000102000410000000010008041000000000020804100000000100004410000000000200441000000000000844100000000100000490000000000200049000000000000804900000000000004490000000010000043000000000020004300000000000080430000000000000443000000000000004b000000090800804000000005082000400000000c02008040000000041a0000400000000c002800400000000818080040000000090400044000000003042000400000000a0200044000000002160000400000000a0020404000000008140040400000000500100440000000030010804000000006000804400000000210180040000000060000c0400000000410104040000000000a1004400000000006108040000000000c0804400000000004380040000000000c00c0400000000008304040000000018120004000000000930000400000000880200240000000081100024000000008820000480000000901000048000000018004804000000000900c00400000000480008240000000041004024000000004800800480000000500040048000000000304804000000000012c0040000000000900824000000000082402400000000009080048000000000a04004800000001800024400000000090006040000000028000064000000002100022400000000280004048000000030000204800000000030024400000000001206040000000000500064000000000042022400000000005004048000000000600204800000000000c2440000000000004e0400000000000140640000000000010a240000000000014404800000000001820480000000140a0004000000000528000400000000840200140000000081080014000000008420000420000000900800042000000014002804000000000500a0040000000044000814000000004100201400000000440080042000000050002004200000000028280400000000000aa0040000000000880814000000000082201400000000008880042000000000a02004200000001400014400000000050005040000000024000054000000002100011400000000240004042000000030000104200000000028014400000000000a05040000000000480054000000000042011400000000004804042000000000600104200000000000a1440000000000002d04000000000001205400000000000109140000000000012404200000000001810420000000050000260000000009000016000000000c0000148000000014000006800000000c000024200000001800000620000000000a002600000000001200160000000000180014800000000028000680000000001800242000000000300006200000000000282600000000000048160000000000006014800000000000a0068000000000006024200000000000c00620000000000001660000000000000256000000000000031480000000000005068000000000000324200000000000060620000000120600040000000003240004000000008202000c000000008104000c0000000082200004100000009004000410000000120018040000000003009004000000004200080c000000004100100c0000000042008004100000005000100410000000002418040000000000069004000000000084080c000000000082100c00000000008480041000000000a0100410000000120000c40000000003000484000000002200004c000000002100008c0000000022000404100000003000008410000000002400c40000000000060484000000000044004c000000000042008c0000000000440404100000000060008410000000000090c40000000000001c84000000000001104c000000000001088c000000000001140410000000000180841000000003000025000000000900000d000000000a00000c8000000012000005800000000a00002410000000180000051000000000060025000000000012000d000000000014000c8000000000240005800000000014002410000000003000051000000000001825000000000000480d000000000000500c80000000000090058000000000005024100000000000c00510000000000000e5000000000000024d000000000000028c800000000000048580000000000002a410000000000006051000000003000014400000000500000c400000000600000c200000001200000460000000060000141000000014000004500000000006001440000000000a000c40000000000c000c200000000024000460000000000c001410000000002800045000000000001814400000000000280c400000000000300c20000000000090046000000000003014100000000000a00450000000000000d4400000000000014c400000000000018c200000000000048460000000000001941000000000000504500000000000000ec000000000000015c00000000000000f200000000000002560000000000000171000000000000026500000001100000400000000002200040000000000008804000000000000044400000000000000248000000000000014200000000000000c1,
  0x102080080000000010200408000000001000840800000000002084080000000010200028000000001000802800000000002080280000000010000428000000000020042800000000000084280000000010200018000000001000801800000000002080180000000010000418000000000020041800000000000084180000000010000038000000000020003800000000000080380000000000000438000000001020000c000000001000800c000000000020800c000000001000040c000000000020040c000000000000840c000000001000002c000000000020002c000000000000802c000000000000042c000000001000001c000000000020001c000000000000801c000000000000041c000000000000003c000000000204100800000000020400880000000002001088000000000004108800000000020400090000000002001009000000000004100900000000020000890000000000040089000000000000108900000000020400084000000002001008400000000004100840000000020000884000000000040088400000000000108840000000020000094000000000040009400000000000100940000000000000894000000002040008100000000200100810000000000410081000000002000088100000000004008810000000000010881000000002000009100000000004000910000000000010091000000000000089100000000200000850000000000400085000000000001008500000000000008850000000000000095000000090801008000000005084000800000000c02010080000000042a0000800000000c004800800000000828080080000000090400088000000003044000800000000a0200088000000002260000800000000a004040800000000824004080000000050010088000000003001100800000000600080880000000022018008000000006000140800000000420104080000000000a1008800000000006110080000000000c0808800000000004580080000000000c0140800000000008504080000000018140008000000000a30000800000000880400280000000082100028000000008820000900000000901000090000000018005008000000000a00c00800000000480010280000000042004028000000004800800900000000500040090000000000305008000000000014c0080000000000901028000000000084402800000000009080090000000000a040090000000018000288000000000a00060800000000280000a80000000022000228000000002800040900000000300002090000000000300288000000000014060800000000005000a8000000000044022800000000005004090000000000600209000000000000c288000000000000560800000000000140a800000000000112280000000000014409000000000001820900000000140c0008000000000628000800000000840400180000000082080018000000008420000840000000900800084000000014003008000000000600a0080000000044001018000000004200201800000000440080084000000050002008400000000028300800000000000ca0080000000000881018000000000084201800000000008880084000000000a02008400000001400018800000000060005080000000024000098000000002200011800000000240004084000000030000108400000000028018800000000000c05080000000000480098000000000044011800000000004804084000000000600108400000000000a18800000000000035080000000000012098000000000001111800000000000124084000000000018108400000000600002a000000000a00001a000000000c000019000000001400000b000000000c000028400000001800000a40000000000c002a000000000014001a0000000000180019000000000028000b0000000000180028400000000030000a400000000000302a000000000000501a0000000000006019000000000000a00b0000000000006028400000000000c00a40000000000001aa000000000000029a0000000000000319000000000000050b0000000000000328400000000000060a40000000032200080000000011060008000000008202000c000000008104000c0000000090020008100000008120000810000000030088080000000011001808000000004200080c000000004100100c0000000050000808100000004100800810000000000688080000000000221808000000000084080c000000000082100c0000000000a008081000000000828008100000000300044800000000110000c8000000002200004c000000002100008c00000000300000481000000021000408100000000006044800000000002200c8000000000044004c000000000042008c000000000060004810000000004204081000000000001c4800000000000088c8000000000001104c000000000001088c00000000000180481000000000010c08100000000900000d000000000a00000c8000000003000028800000001100000980000000180000089000000009000028100000000012000d000000000014000c8000000000060028800000000022000980000000003000089000000000120028100000000000480d000000000000500c80000000000018288000000000008809800000000000c0089000000000004828100000000000024d000000000000028c80000000000000e8800000000000044980000000000006089000000000000268100000000500000c400000000600000c200000000300001820000000110000086000000014000008300000000500001810000000000a000c40000000000c000c20000000000600182000000000220008600000000028000830000000000a0018100000000000280c400000000000300c20000000000018182000000000008808600000000000a0083000000000002818100000000000014c400000000000018c20000000000000d8200000000000044860000000000005083000000000000158100000000000000ec000000000000019a00000000000000f2000000000000028e00000000000002a300000000000001a900000001200000800000000002400080000000000009008000000000000048800000000000000290000000000000018400000000000000c1,
  0x1020801000000000102004100000000010008410000000000020841000000000102000300000000010008030000000000020803000000000100004300000000000200430000000000000843000000000102000180000000010008018000000000020801800000000100004180000000000200418000000000000841800000000100000380000000000200038000000000000803800000000000004380000000010200014000000001000801400000000002080140000000010000414000000000020041400000000000084140000000010000034000000000020003400000000000080340000000000000434000000001000001c000000000020001c000000000000801c000000000000041c000000000000003c000000000408201000000000040801100000000004002110000000000008211000000000040800120000000004002012000000000008201200000000040001120000000000080112000000000000211200000000040800104000000004002010400000000008201040000000040001104000000000080110400000000000211040000000040000124000000000080012400000000000201240000000000001124000000004080010200000000400201020000000000820102000000004000110200000000008011020000000000021102000000004000012200000000008001220000000000020122000000000000112200000000400001060000000000800106000000000002010600000000000011060000000000000126000000090802010000000005088001000000000c02020100000000044a0001000000000c008801000000000848080100000000090400110000000003048001000000000a0200110000000002460001000000000a008041000000000844004100000000050010110000000003001201000000000600081100000000024018010000000006000241000000000440104100000000000a1011000000000006120100000000000c0811000000000004980100000000000c0241000000000008904100000000018180010000000000c30001000000000880800300000000084100030000000008820001200000000901000120000000018006010000000000c00c01000000000480020300000000044004030000000004800801200000000500040120000000000306010000000000018c0100000000000902030000000000088403000000000009080120000000000a040120000000018000310000000000c0006100000000028000130000000002400023000000000280004120000000030000212000000000030031000000000001806100000000000500130000000000048023000000000005004120000000000600212000000000000c31000000000000066100000000000014130000000000001223000000000000144120000000000018212000000000624001000000000120c0010000000008404001800000000820800180000000090040010400000008220001040000000060090100000000012003010000000004400101800000000420020180000000050001010400000004200801040000000000c90100000000000243010000000000088101800000000008420180000000000a01010400000000084801040000000060004900000000012000190000000002400009800000000220001180000000030000090400000002200041040000000000c049000000000002401900000000000480098000000000044011800000000006000904000000000440410400000000000349000000000000091900000000000012098000000000001111800000000000180904000000000011410400000000a00001a000000000c000019000000000600003100000000120000130000000018000011400000000a000030400000000014001a000000000018001900000000000c0031000000000024001300000000003000114000000000140030400000000000501a000000000000601900000000000030310000000000009013000000000000c0114000000000005030400000000000029a000000000000031900000000000001b10000000000000493000000000000061140000000000002b0400000000522001000000000110a0010000000008402001400000000810800140000000090020010200000008120001020000000050088100000000011002810000000004400081400000000410020140000000050000810200000004100801020000000000a88100000000000222810000000000088081400000000008220140000000000a00810200000000082801020000000050004500000000011000150000000002400005400000000210001140000000030000050200000002100041020000000000a0450000000000022015000000000004800540000000000420114000000000060005020000000004204102000000000002c5000000000000089500000000000012054000000000001091400000000000180502000000000010c102000000009000016000000000c000014800000000500003080000000110000128000000018000010a0000000090000302000000000120016000000000018001480000000000a003080000000002200128000000000300010a0000000001200302000000000004816000000000000601480000000000028308000000000008812800000000000c010a00000000000483020000000000002560000000000000314800000000000017080000000000004528000000000000610a00000000000027020000000030000144000000003000018200000001200001030000000060000141000000005000018100000001100001050000000000600144000000000060018200000000024001030000000000c001410000000000a0018100000000022001050000000000018144000000000001818200000000000901030000000000030141000000000002818100000000000881050000000000000d440000000000000d820000000000004903000000000000194100000000000015810000000000004505000000000000015c000000000000019a00000000000001a900000000000003130000000000000171000000000000030d0000000140000100000000000280010000000000000a01000000000000005100000000000000032000000000000001840000000000000142,
  0x1020802000000000102004200000000010008420000000000020842000000000102000300000000010008030000000000020803000000000100004300000000000200430000000000000843000000000102000280000000010008028000000000020802800000000100004280000000000200428000000000000842800000000100000380000000000200038000000000000803800000000000004380000000010200024000000001000802400000000002080240000000010000424000000000020042400000000000084240000000010000034000000000020003400000000000080340000000000000434000000001000002c000000000020002c000000000000802c000000000000042c000000000000003c000000000810402000000000081002200000000008004220000000000010422000000000081000220000000008004022000000000010402200000000080002220000000000100222000000000000422200000000081000210000000008004021000000000010402100000000080002210000000000100221000000000000422100000000080000230000000000100023000000000000402300000000000002230000000008100020800000000800402080000000001040208000000008000220800000000010022080000000000042208000000008000022800000000010002280000000000040228000000000000222800000000800002180000000001000218000000000004021800000000000022180000000000000238000000090804020000000005090002000000000c02040200000000048a0002000000000c010802000000000888080200000000090400220000000003050002000000000a0200220000000002860002000000000a010042000000000884004200000000050010220000000003001402000000000600082200000000028018020000000006000442000000000480104200000000000a1022000000000006140200000000000c0822000000000005180200000000000c044200000000000910420000000000c28002000000000141800200000000088080030000000008410003000000000900800220000000084200022000000000c00a02000000000140060200000000048002030000000004400403000000000500020220000000044008022000000000018a0200000000000286020000000000090203000000000008840300000000000a020220000000000888022000000000c000520000000001400032000000000280001300000000024000230000000003000012200000000240004220000000000180520000000000028032000000000005001300000000000480230000000000060012200000000004804220000000000006520000000000000a3200000000000014130000000000001223000000000000181220000000000012422000000000a24002000000000121400200000000088040028000000008210002800000000900400210000000082200021000000000a0090200000000012005020000000004800102800000000420040280000000050001021000000004200802100000000001490200000000000245020000000000090102800000000008440280000000000a010210000000000848021000000000a0004a000000000120002a000000000280000a8000000002200022800000000300000a1000000002200042100000000001404a000000000002402a000000000005000a8000000000044022800000000006000a1000000000044042100000000000054a000000000000092a000000000000140a8000000000001122800000000000180a10000000000011421000000000600002a00000000060000310000000014000021400000000c000028400000000a000030400000001200002240000000000c002a00000000000c00310000000000280021400000000018002840000000001400304000000000240022400000000000302a0000000000003031000000000000a02140000000000060284000000000005030400000000000902240000000000001aa00000000000001b10000000000000521400000000000032840000000000002b040000000000004a240000000092200200000000011120020000000008802002400000000811000240000000090020020800000008120002080000000090088200000000011004820000000004800082400000000410040240000000050000820800000004100802080000000001288200000000000224820000000000090082400000000008240240000000000a0082080000000008280208000000009000460000000001100026000000000280000640000000021000224000000003000006080000000210004208000000000120460000000000022026000000000005000640000000000420224000000000060006080000000004204208000000000004c600000000000008a6000000000000140640000000000010a2400000000000180608000000000010c20800000000500002600000000050000308000000014000020a00000000c0000242000000009000030200000001100002220000000000a002600000000000a00308000000000280020a0000000001800242000000000120030200000000022002220000000000028260000000000002830800000000000a020a00000000000602420000000000048302000000000008822200000000000016600000000000001708000000000000520a00000000000032420000000000002702000000000000462200000000300002500000000030000288000000012000020900000000a0000241000000009000028100000001100002110000000000600250000000000060028800000000024002090000000001400241000000000120028100000000022002110000000000018250000000000001828800000000000902090000000000050241000000000004828100000000000882110000000000000e500000000000000e880000000000004a090000000000002a4100000000000026810000000000004611000000000000028e000000000000025600000000000002a30000000000000313000000000000030d00000000000002650000000180000200000000000300020000000000000c02000000000000006200000000000000032000000000000002900000000000000248,
  0x20410040000000002040044000000000200104400000000000410440000000002040024000000000200102400000000000410240000000002000064000000000004006400000000000010640000000002040014000000000200101400000000000410140000000002000054000000000004005400000000000010540000000002000034000000000004003400000000000010340000000000000074000000000204000c000000000200100c000000000004100c000000000200004c000000000004004c000000000000104c000000000200002c000000000004002c000000000000102c000000000000006c000000000200001c000000000004001c000000000000101c000000000000005c000000000000003c000000000010208400000000001020044000000000100084400000000000208440000000001020040800000000100084080000000000208408000000001000044800000000002004480000000000008448000000001020040200000000100084020000000000208402000000001000044200000000002004420000000000008442000000001000040a000000000020040a000000000000840a000000000000044a00000000102004010000000010008401000000000020840100000000100004410000000000200441000000000000844100000000100004090000000000200409000000000000840900000000000004490000000010000403000000000020040300000000000084030000000000000443000000000000040b0000000a0800840000000006082004000000000c04008400000000041c0004000000000c003004000000000818100400000000030220040000000001160004000000000900204400000000081200440000000009040004400000000a0200044000000003000884000000000110180400000000050000c40000000004100844000000000500100440000000060008044000000000060884000000000002380400000000000a00c4000000000008284400000000000a100440000000000c080440000000028120040000000000950004000000000880202400000000081100240000000008840004080000000a0100040800000002800484000000000090140400000000048000a40000000004100424000000000480100408000000060004040800000000050484000000000001340400000000000900a40000000000082424000000000009100408000000000c040408000000009000460000000001100026000000000180002440000000028000064000000001800044080000000300000608000000000120460000000000022026000000000003002440000000000500064000000000030044080000000006000608000000000004c600000000000008a60000000000000c2440000000000014064000000000000c440800000000001806080000000240a0040000000000548004000000000840201400000000081080140000000008440004020000000a0080040200000002400284000000000050120400000000044000940000000004100214000000000440100402000000060002040200000000048284000000000000b20400000000000880940000000000082214000000000008900402000000000c0204020000000050004500000000011000150000000001400014400000000240000540000000014000440200000003000005020000000000a0450000000000022015000000000002801440000000000480054000000000028044020000000006000502000000000002c500000000000008950000000000000a1440000000000012054000000000000a440200000000001805020000000050002420000000009000142000000000c0001408000000024000042800000000c000240200000002800004220000000000a0242000000000012014200000000001801408000000000480042800000000018024020000000005000422000000000002a42000000000000494200000000000061408000000000012042800000000000624020000000000140422000000000000166000000000000025600000000000001708000000000000452800000000000027020000000000004622000000022060040000000000344004000000000820200c000000000810400c0000000008240004010000000a00400401000000022001840000000000301104000000000420008c000000000410010c0000000004201004010000000600010401000000000441840000000000007104000000000008408c000000000008210c000000000008500401000000000c01040100000000300044800000000110000c800000000120000c4000000002200004c00000000120004401000000030000048100000000006044800000000002200c800000000002400c4000000000044004c000000000024044010000000006000481000000000001c4800000000000088c800000000000090c4000000000001104c00000000000094401000000000018048100000000300024100000000090000c1000000000a0000c08000000022000041800000000a0002401000000028000041100000000006024100000000001200c100000000001400c08000000000440041800000000014024010000000005000411000000000001a4100000000000048c100000000000050c080000000000110418000000000005240100000000001404110000000000000e5000000000000024d00000000000000e8800000000000044980000000000002681000000000000461100000000300014040000000050000c040000000060000c0200000002200004060000000060001401000000024000040500000000006014040000000000a00c040000000000c00c0200000000044004060000000000c01401000000000480040500000000000194040000000000028c040000000000030c020000000000110406000000000003140100000000001204050000000000000d4400000000000014c40000000000000d820000000000004486000000000000158100000000000045050000000000000c2c000000000000141c0000000000000c320000000000002416000000000000143100000000000024250000000210000400000000000420040000000000001084000000000000004440000000000000240800000000000014020000000000000c01,
  0x20410080000000002040048000000000200104800000000000410480000000002040028000000000200102800000000000410280000000002000068000000000004006800000000000010680000000002040018000000000200101800000000000410180000000002000058000000000004005800000000000010580000000002000038000000000004003800000000000010380000000000000078000000000204000c000000000200100c000000000004100c000000000200004c000000000004004c000000000000104c000000000200002c000000000004002c000000000000102c000000000000006c000000000200001c000000000004001c000000000000101c000000000000005c000000000000003c00000000002041080000000000204008800000000020010880000000000041088000000000204008100000000020010810000000000041081000000000200008900000000000400890000000000001089000000000204008040000000020010804000000000041080400000000200008840000000000400884000000000001088400000000200008140000000000400814000000000001081400000000000008940000000020400801000000002001080100000000004108010000000020000881000000000040088100000000000108810000000020000811000000000040081100000000000108110000000000000891000000002000080500000000004008050000000000010805000000000000088500000000000008150000000a0801080000000006084008000000000c04010800000000042c0008000000000c005008000000000828100800000000030240080000000001260008000000000900404800000000082200480000000009040008800000000a0200088000000003000908000000000120180800000000050001480000000004200848000000000500100880000000060008088000000000060908000000000002580800000000000a0148000000000008484800000000000a100880000000000c080880000000028140080000000000a50008000000000880402800000000082100280000000008840008100000000a01000810000000028005080000000000a0140800000000048001280000000004200428000000000480100810000000060004081000000000050508000000000001540800000000000901280000000000084428000000000009100810000000000c04081000000000a0004a000000000120002a0000000001800028800000000280000a8000000001800048100000000300000a100000000001404a000000000002402a0000000000030028800000000005000a8000000000030048100000000006000a100000000000054a000000000000092a0000000000000c28800000000000140a8000000000000c48100000000000180a100000000240c0080000000000648008000000000840401800000000082080180000000008440008040000000a0080080400000002400308000000000060120800000000044001180000000004200218000000000440100804000000060002080400000000048308000000000000d20800000000000881180000000000084218000000000008900804000000000c0208040000000060004900000000012000190000000001400018800000000240000980000000014000480400000003000009040000000000c04900000000000240190000000000028018800000000004800980000000000280480400000000060009040000000000034900000000000009190000000000000a1880000000000012098000000000000a48040000000000180904000000006000282000000000a000182000000000c0001810000000024000083000000000c000280400000002800008240000000000c02820000000000140182000000000018018100000000004800830000000000180280400000000050008240000000000032820000000000005182000000000000618100000000000120830000000000006280400000000001408240000000000001aa000000000000029a00000000000001b1000000000000049300000000000002b040000000000004a24000000003420080000000002106008000000000820200c000000000810400c000000000a002008010000000814000801000000003010880000000002100188000000000420008c000000000410010c0000000006000088010000000410100801000000000070880000000000042188000000000008408c000000000008210c00000000000c00880100000000083008010000000110000c800000000120000c40000000003000484000000002100008c0000000030000084100000001100048010000000002200c800000000002400c40000000000060484000000000042008c0000000000600084100000000022048010000000000088c800000000000090c40000000000001c84000000000001088c00000000000180841000000000008c8010000000090000c1000000000a0000c0800000000300028080000000210000818000000028000080900000000900028010000000001200c100000000001400c0800000000006028080000000004200818000000000500080900000000012028010000000000048c100000000000050c08000000000001a80800000000001088180000000000140809000000000004a8010000000000000e5000000000000028c80000000000000e8800000000000048580000000000004a090000000000002a410000000050000c040000000060000c0200000000300018020000000210000806000000024000080300000000500018010000000000a00c040000000000c00c020000000000601802000000000420080600000000048008030000000000a018010000000000028c040000000000030c0200000000000198020000000000108806000000000012080300000000000298010000000000000d4400000000000018c20000000000000d820000000000004846000000000000490300000000000019410000000000000c2c000000000000181a0000000000000c32000000000000280e000000000000282300000000000018290000000220000800000000000440080000000000001108000000000000004880000000000000281000000000000018040000000000000c01,
  0x204101000000000020400500000000002001050000000000004105000000000020400300000000002001030000000000004103000000000020000700000000000040070000000000000107000000000020400180000000002001018000000000004101800000000020000580000000000040058000000000000105800000000020000380000000000040038000000000000103800000000000000780000000002040014000000000200101400000000000410140000000002000054000000000004005400000000000010540000000002000034000000000004003400000000000010340000000000000074000000000200001c000000000004001c000000000000101c000000000000005c000000000000003c00000000004082100000000000408011000000000040021100000000000082110000000000408010200000000040021020000000000082102000000000400011200000000000801120000000000002112000000000408010040000000040021004000000000082100400000000400011040000000000801104000000000002110400000000400010240000000000801024000000000002102400000000000011240000000040801002000000004002100200000000008210020000000040001102000000000080110200000000000211020000000040001022000000000080102200000000000210220000000000001122000000004000100600000000008010060000000000021006000000000000110600000000000010260000000a0802100000000006088010000000000c04021000000000044c0010000000000c009010000000000848101000000000030280100000000001460010000000000900805000000000084200500000000009040011000000000a0200110000000003000a10000000000140181000000000050002500000000004400850000000000500101100000000060008110000000000060a10000000000002981000000000000a0250000000000008885000000000000a101100000000000c081100000000028180100000000000c50010000000000880803000000000084100300000000008840010200000000a01001020000000028006100000000000c0141000000000048002300000000004400430000000000480101020000000060004102000000000050610000000000001941000000000000902300000000000088430000000000009101020000000000c04102000000000c000520000000001400032000000000180003100000000028000130000000001800050200000000300001220000000000180520000000000028032000000000003003100000000000500130000000000030050200000000006001220000000000006520000000000000a320000000000000c3100000000000014130000000000000c5020000000000018122000000000644010000000000220c01000000000084040180000000008208018000000000a0040100400000008240010040000000060111000000000022003100000000004400118000000000420021800000000060001100400000004201010040000000000d11000000000000443100000000000088118000000000008421800000000000c0110040000000008501004000000012000190000000001400018800000000060005080000000022000118000000003000010840000000120005004000000000240190000000000028018800000000000c05080000000000440118000000000060010840000000002405004000000000009190000000000000a1880000000000003508000000000001111800000000000181084000000000009500400000000a000182000000000c000181000000000600030100000000220001030000000028000101400000000a0003004000000000140182000000000018018100000000000c030100000000004401030000000000500101400000000014030040000000000051820000000000006181000000000000330100000000000111030000000000014101400000000000530040000000000001aa000000000000031900000000000001b1000000000000050b00000000000005214000000000000328400000000542010000000000210a01000000000084020140000000008108014000000000a0020100200000008140010020000000050109000000000021002900000000004400094000000000410021400000000060000900200000004101010020000000000b09000000000000422900000000000088094000000000008221400000000000c0090020000000008301002000000011000150000000001400014400000000050005040000000021000114000000003000010420000000110005002000000000220150000000000028014400000000000a05040000000000420114000000000060010420000000002205002000000000008950000000000000a1440000000000002d04000000000001091400000000000181042000000000008d002000000009000142000000000c000140800000000500030080000000210001028000000028000100a0000000090003002000000000120142000000000018014080000000000a030080000000004201028000000000500100a000000000120300200000000000494200000000000061408000000000002b0080000000000109028000000000014100a000000000004b0020000000000001660000000000000314800000000000017080000000000005068000000000000520a00000000000032420000000030001404000000003000180200000002200010030000000060001401000000005000180100000002100010050000000000601404000000000060180200000000044010030000000000c014010000000000a01801000000000420100500000000000194040000000000019802000000000011100300000000000314010000000000029801000000000010900500000000000014c400000000000018c20000000000001941000000000000508300000000000015810000000000005045000000000000141c000000000000181a000000000000182900000000000030130000000000001431000000000000300d0000000240001000000000000480100000000000001210000000000000005100000000000000302000000000000018040000000000001402,
  0x204102000000000020400600000000002001060000000000004106000000000020400300000000002001030000000000004103000000000020000700000000000040070000000000000107000000000020400280000000002001028000000000004102800000000020000680000000000040068000000000000106800000000020000380000000000040038000000000000103800000000000000780000000002040024000000000200102400000000000410240000000002000064000000000004006400000000000010640000000002000034000000000004003400000000000010340000000000000074000000000200002c000000000004002c000000000000102c000000000000006c000000000000003c00000000008104200000000000810022000000000080042200000000000104220000000000810020200000000080042020000000000104202000000000800022200000000001002220000000000004222000000000810020100000000080042010000000000104201000000000800022100000000001002210000000000004221000000000800020300000000001002030000000000004203000000000000022300000000081002008000000008004200800000000010420080000000080002208000000000100220800000000000422080000000080002028000000000100202800000000000420280000000000002228000000008000201800000000010020180000000000042018000000000000221800000000000020380000000a0804200000000006090020000000000c04042000000000048c0020000000000c011020000000000888102000000000030300200000000001860020000000000901006000000000088200600000000009040022000000000a0200220000000003000c20000000000180182000000000050004600000000004800860000000000500102200000000060008220000000000060c20000000000003182000000000000a0460000000000009086000000000000a102200000000000c08220000000000c48020000000000241802000000000088080300000000008410030000000000a00802020000000084400202000000000c0122000000000024006200000000004800230000000000440043000000000060002202000000004401020200000000001922000000000000486200000000000090230000000000008843000000000000c02202000000000089020200000000140003200000000018000310000000000c000610000000002400023000000000300002120000000014000602000000000028032000000000003003100000000000180610000000000048023000000000006002120000000000280602000000000000a320000000000000c310000000000000661000000000000122300000000000018212000000000000a602000000000a44020000000000221402000000000088040280000000008210028000000000a00402010000000082400201000000000a0112000000000022005200000000004800128000000000420042800000000060001201000000004201020100000000001512000000000000445200000000000090128000000000008442800000000000c01201000000000085020100000000120002a00000000018000288000000000a00060800000000220002280000000030000209000000001200060100000000002402a00000000000300288000000000014060800000000004402280000000000600209000000000024060100000000000092a0000000000000c2880000000000005608000000000001122800000000000182090000000000009601000000000600028200000000060003010000000024000201400000000c000280400000000a000300400000002200020240000000000c028200000000000c03010000000000480201400000000018028040000000001403004000000000440202400000000000328200000000000033010000000000012201400000000000628040000000000053004000000000011202400000000000029a00000000000003190000000000000328400000000000061140000000000002b0400000000000060a400000000942020000000000211202000000000088020240000000008110024000000000a002020080000000814002008000000009010a000000000021004a000000000048000a4000000000410042400000000060000a0080000000410102008000000000130a000000000000424a000000000000900a4000000000008242400000000000c00a0080000000008302008000000011000260000000001800024400000000090006040000000021000224000000003000020480000000110006008000000000220260000000000030024400000000001206040000000000420224000000000060020480000000002206008000000000008a60000000000000c2440000000000004e040000000000010a2400000000000182048000000000008e00800000000500024200000000050003008000000024000200a00000000c0002402000000009000300200000002100020220000000000a024200000000000a03008000000000480200a000000000180240200000000012030020000000004202022000000000002a420000000000002b008000000000012200a0000000000062402000000000004b002000000000010a022000000000000256000000000000031480000000000003242000000000000610a0000000000002702000000000000606200000000300024100000000030002808000000022000200900000000a000240100000000900028010000000210002011000000000060241000000000006028080000000004402009000000000140240100000000012028010000000004202011000000000001a410000000000001a80800000000001120090000000000052401000000000004a801000000000010a01100000000000024d000000000000028c80000000000002a41000000000000608900000000000026810000000000006051000000000000280e000000000000241600000000000028230000000000003013000000000000300d00000000000024250000000280002000000000000500200000000000001420000000000000006200000000000000302000000000000028100000000000002408,
  0x204104000000000020400600000000002001060000000000004106000000000020400500000000002001050000000000004105000000000020000700000000000040070000000000000107000000000020400480000000002001048000000000004104800000000020000680000000000040068000000000000106800000000020000580000000000040058000000000000105800000000000000780000000002040044000000000200104400000000000410440000000002000064000000000004006400000000000010640000000002000054000000000004005400000000000010540000000000000074000000000200004c000000000004004c000000000000104c000000000000006c000000000000005c0000000001020840000000000102004200000000010008420000000000020842000000000102004100000000010008410000000000020841000000000100004300000000000200430000000000000843000000000102004080000000010008408000000000020840800000000100004280000000000200428000000000000842800000000100004180000000000200418000000000000841800000000000004380000000010200404000000001000840400000000002084040000000010000424000000000020042400000000000084240000000010000414000000000020041400000000000084140000000000000434000000001000040c000000000020040c000000000000840c000000000000042c000000000000041c00000000a08084000000000060a0040000000000c04084000000000050c0040000000000c02104000000000090810400000000001850040000000000283004000000000090100600000000008820060000000000a010042000000000884004200000000018014400000000002800c40000000000500046000000000048008600000000006000442000000000480104200000000000314400000000000050c4000000000000a0460000000000009086000000000000c044200000000000910420000000001448040000000000242804000000000090080500000000008420050000000000a008041000000000844004100000000014012400000000002400a40000000000500025000000000044008500000000006000241000000000440104100000000000292400000000000048a4000000000000a0250000000000008885000000000000c024100000000000890410000000000c000520000000000c0006100000000028000412000000001800050200000000140006020000000024000422000000000018052000000000001806100000000000500412000000000030050200000000002806020000000000480422000000000000652000000000000066100000000000014412000000000000c502000000000000a6020000000000012422000000001244040000000000222404000000000090040480000000008220048000000000a00404080000000082400408000000001201140000000000220094000000000050001480000000004200848000000000600014080000000042010408000000000025140000000000004494000000000000a0148000000000008484800000000000c014080000000000850408000000000a0004a0000000000a000608000000002800040900000000180004810000000012000601000000002200042100000000001404a00000000000140608000000000050040900000000003004810000000000240601000000000044042100000000000054a000000000000056080000000000014409000000000000c4810000000000009601000000000001142100000000060004900000000006000508000000002400040840000000140004804000000012000500400000002200041040000000000c049000000000000c05080000000000480408400000000028048040000000002405004000000000440410400000000000349000000000000035080000000000012408400000000000a48040000000000095004000000000011410400000000000050b000000000000049300000000000005214000000000000611400000000000060a40000000000004a2400000001142040000000000212204000000000090020440000000008120044000000000a002040400000000814004040000000011010c000000000021008c000000000050000c4000000000410084400000000060000c0400000000410104040000000000230c000000000000428c000000000000a00c4000000000008284400000000000c00c0400000000008304040000000009000460000000000900060400000000280004048000000018000440800000001100060080000000210004208000000000120460000000000012060400000000005004048000000000300440800000000022060080000000004204208000000000004c600000000000004e040000000000014404800000000000c4408000000000008e008000000000010c2080000000050004500000000005000504000000002400040420000000140004402000000011000500200000002100041020000000000a045000000000000a050400000000004804042000000000280440200000000022050020000000004204102000000000002c500000000000002d040000000000012404200000000000a4402000000000008d002000000000010c10200000000000050680000000000004528000000000000520a000000000000610a00000000000060620000000000004622000000003000448000000000300048400000000220004041000000012000440100000001100048010000000210004081000000000060448000000000006048400000000004404041000000000240440100000000022048010000000004204081000000000001c480000000000001c84000000000001140410000000000094401000000000008c801000000000010c081000000000000485800000000000044980000000000004a090000000000006089000000000000605100000000000046110000000000004846000000000000448600000000000049030000000000005083000000000000504500000000000045050000000300004000000000000600400000000000001840000000000000006200000000000000510000000000000048800000000000004440,
  0x40810800000000004080880000000000400188000000000000818800000000004080480000000000400148000000000000814800000000004000c800000000000080c800000000000001c800000000004080280000000000400128000000000000812800000000004000a800000000000080a800000000000001a800000000004000680000000000008068000000000000016800000000000000e800000000004080180000000000400118000000000000811800000000004000980000000000008098000000000000019800000000004000580000000000008058000000000000015800000000000000d800000000004000380000000000008038000000000000013800000000000000b800000000000000780000000000010208400000000001020804000000000100084400000000000208440000000001020800800000000100084080000000000208408000000001000804800000000002080480000000000008448000000001020800200000000100084020000000000208402000000001000804200000000002080420000000000008442000000001000800a000000000020800a000000000000840a000000000000804a00000000102080010000000010008401000000000020840100000000100080410000000000208041000000000000844100000000100080090000000000208009000000000000840900000000000080490000000010008003000000000020800300000000000084030000000000008043000000000000800b0000000604208000000000021c0080000000000a0030800000000008141080000000000a080084000000000c040084000000000502208000000000011a0080000000000900288000000000081208800000000009080080400000000c02008040000000011010c000000000021008c0000000000300088400000000050000c4000000000300108040000000060000c040000000000230c000000000000428c0000000000006088400000000000a00c4000000000006108040000000000c00c040000000048120800000000000990080000000000880248000000000081104800000000008880080080000000c01008008000000009010a000000000021004a0000000000280048400000000048000a4000000000280108008000000060000a008000000000130a000000000000424a0000000000005048400000000000900a4000000000005108008000000000c00a00800000000900882000000000110048200000000018004804000000004800082400000000180088008000000050000820800000000012882000000000002248200000000000304804000000000090082400000000003088008000000000a008208000000000004c600000000000008a600000000000004e040000000000010a240000000000008e008000000000010c2080000000440a0800000000000588080000000000840228000000000081082800000000008480080020000000c008080020000000050109000000000021002900000000002400284000000000440009400000000024010800200000006000090020000000000b090000000000004229000000000000482840000000000088094000000000004908002000000000c0090020000000050088100000000011002810000000001400280400000000440008140000000014008800200000005000081020000000000a881000000000002228100000000000282804000000000088081400000000002888002000000000a008102000000000002c5000000000000089500000000000002d0400000000000109140000000000008d002000000000010c1020000000050048020000000009002802000000000c0028008000000044000802800000000c004800200000004800080220000000000a4802000000000012280200000000001828008000000000880802800000000018480020000000009008022000000000002a4200000000000049420000000000002b0080000000000109028000000000004b002000000000010a022000000000002826000000000000481600000000000028308000000000008812800000000000483020000000000088222000000042060800000000000384080000000000820218000000000081041800000000008280080010000000c004080010000000030108800000000021001880000000002200184000000000420008c00000000022010800100000006000088010000000000708800000000000421880000000000044184000000000008408c000000000004508001000000000c00880100000000300880800000000110018080000000012001804000000004200080c00000000120088001000000050000808100000000006880800000000002218080000000000241804000000000084080c00000000002488001000000000a008081000000000001c4800000000000088c80000000000001c84000000000001088c0000000000008c801000000000010c0810000000030048010000000009001801000000000a0018008000000042000801800000000a00480010000000480008011000000000064801000000000012180100000000001418008000000000840801800000000014480010000000009008011000000000001a4100000000000048c10000000000001a8080000000000108818000000000004a801000000000010a011000000000001825000000000000480d0000000000001828800000000000880980000000000048281000000000008821100000000300280040000000050018004000000006001800200000004200080060000000060028001000000044000800500000000006280040000000000a180040000000000c1800200000000084080060000000000c28001000000000880800500000000000194040000000000028c040000000000019802000000000010880600000000000298010000000000109005000000000001814400000000000280c40000000000018182000000000008808600000000000281810000000000088105000000000001802c000000000002801c00000000000180320000000000048016000000000002803100000000000480250000000410008000000000000820800000000000001084000000000000088040000000000004800800000000000280020000000000018001,
  0x40811000000000004080900000000000400190000000000000819000000000004080500000000000400150000000000000815000000000004000d000000000000080d000000000000001d000000000004080300000000000400130000000000000813000000000004000b000000000000080b000000000000001b000000000004000700000000000008070000000000000017000000000000000f000000000004080180000000000400118000000000000811800000000004000980000000000008098000000000000019800000000004000580000000000008058000000000000015800000000000000d800000000004000380000000000008038000000000000013800000000000000b80000000000000078000000000002041080000000000204100800000000020010880000000000041088000000000204100100000000020010810000000000041081000000000200100900000000000410090000000000001089000000000204100040000000020010804000000000041080400000000200100840000000000410084000000000001088400000000200100140000000000410014000000000001081400000000000100940000000020410001000000002001080100000000004108010000000020010081000000000041008100000000000108810000000020010011000000000041001100000000000108110000000000010091000000002001000500000000004100050000000000010805000000000001008500000000000100150000000604410000000000022c0100000000000a0051000000000008241100000000000a080108000000000c040108000000000502410000000000012a0100000000000900490000000000082209000000000009080100800000000c02010080000000012011400000000002200940000000000300090800000000050001480000000003001100800000000600014080000000000251400000000000044940000000000006090800000000000a0148000000000006110080000000000c014080000000048141000000000000a90100000000000880450000000000082105000000000008880100100000000c0101001000000000a01120000000000220052000000000028005080000000004800128000000000280110010000000060001201000000000015120000000000004452000000000000505080000000000090128000000000005110010000000000c01201000000000a00902000000000120050200000000018005008000000004800102800000000180090010000000050001021000000000014902000000000002450200000000000305008000000000090102800000000003090010000000000a0102100000000000054a000000000000092a0000000000000560800000000000112280000000000009601000000000001142100000000440c1000000000000688100000000000840430000000000082083000000000008480100040000000c008100040000000060111000000000022003100000000002400308000000000440011800000000024011000400000006000110040000000000d110000000000004431000000000000483080000000000088118000000000004910004000000000c0110040000000060090100000000012003010000000001400300800000000440010180000000014009000400000005000101040000000000c901000000000002430100000000000283008000000000088101800000000002890004000000000a010104000000000003490000000000000919000000000000035080000000000011118000000000000950040000000000114104000000006005002000000000a003002000000000c0030010000000044001003000000000c005000400000004800100240000000000c500200000000001430020000000000183001000000000088100300000000001850004000000000901002400000000000328200000000000051820000000000003301000000000001110300000000000053004000000000011202400000000000302a000000000000501a0000000000003031000000000000901300000000000050304000000000009022400000000382100000000000410610000000000082021800000000008104180000000000c0021000100000008180100010000000210018800000000022001840000000000301104000000000410010c00000000060001040100000002101100010000000004218800000000000441840000000000007104000000000008210c00000000000c010401000000000431000100000001100180800000000120018040000000003009004000000004100100c00000000500010041000000011009000100000000022180800000000002418040000000000069004000000000082100c0000000000a0100410000000002290001000000000001c4800000000000090c40000000000001c84000000000001104c000000000001140410000000000094401000000009001801000000000a00180080000000030050008000000041001001800000004800100090000000090050001000000000121801000000000014180080000000000650008000000000821001800000000090100090000000001250001000000000001a4100000000000050c08000000000001a808000000000011041800000000001120090000000000052401000000000001825000000000000500c800000000000182880000000000090058000000000009020900000000000502410000000050018004000000006001800200000000300300020000000410010006000000044001000300000000500300010000000000a180040000000000c180020000000000630002000000000821000600000000088100030000000000a3000100000000000194040000000000030c020000000000019802000000000011040600000000001110030000000000031401000000000001814400000000000300c20000000000018182000000000009004600000000000901030000000000030141000000000001802c000000000003001a0000000000018032000000000005000e000000000005002300000000000300290000000420010000000000000841000000000000001108000000000000090080000000000005001000000000000300040000000000018001,
  0x40812000000000004080a000000000004001a000000000000081a000000000004080600000000000400160000000000000816000000000004000e000000000000080e000000000000001e000000000004080300000000000400130000000000000813000000000004000b000000000000080b000000000000001b000000000004000700000000000008070000000000000017000000000000000f000000000004080280000000000400128000000000000812800000000004000a800000000000080a800000000000001a800000000004000680000000000008068000000000000016800000000000000e800000000004000380000000000008038000000000000013800000000000000b80000000000000078000000000004082100000000000408201000000000040021100000000000082110000000000408200200000000040021020000000000082102000000000400201200000000000820120000000000002112000000000408200040000000040021004000000000082100400000000400201040000000000820104000000000002110400000000400200240000000000820024000000000002102400000000000201240000000040820002000000004002100200000000008210020000000040020102000000000082010200000000000211020000000040020022000000000082002200000000000210220000000000020122000000004002000600000000008200060000000000021006000000000002010600000000000200260000000604820000000000024c0200000000000a0092000000000008441200000000000a080210000000000c040210000000000502820000000000014a02000000000009008a000000000008420a000000000009080201000000000c02020100000000014012400000000002400a400000000003000a1000000000050002500000000003001201000000000600024100000000000292400000000000048a400000000000060a1000000000000a0250000000000006120100000000000c024100000000048182000000000000c90200000000000880860000000000084106000000000008880200200000000c0102002000000000c01220000000000240062000000000028006100000000004800230000000000280120020000000060002202000000000019220000000000004862000000000000506100000000000090230000000000005120020000000000c02202000000000c00a020000000001400602000000000180060100000000048002030000000001800a0020000000050002022000000000018a020000000000028602000000000003060100000000000902030000000000030a0020000000000a020220000000000006520000000000000a32000000000000066100000000000012230000000000000a6020000000000012422000000000684200000000000420c20000000000084043000000000008208300000000000c004200040000000828020004000000022003100000000002400308000000000060120800000000042002180000000006000208040000000220120004000000000443100000000000048308000000000000d208000000000008421800000000000c02080400000000045200040000000120030100000000014003008000000000600a00800000000420020180000000050002008400000001200a0004000000000243010000000000028300800000000000ca00800000000008420180000000000a02008400000000024a0004000000000003490000000000000a188000000000000350800000000000120980000000000012408400000000000a480400000000a003002000000000c003001000000000600600100000000420020030000000048002001400000000a0060004000000000143002000000000018300100000000000c6001000000000084200300000000009020014000000000146000400000000000328200000000000061810000000000003301000000000001208300000000000122014000000000006280400000000000302a00000000000060190000000000003031000000000000a00b000000000000a0214000000000006028400000000582200000000000410a20000000000084022800000000008108280000000000c002200020000000818020002000000021002900000000002400284000000000050120400000000041002140000000006000204020000000210120002000000000422900000000000048284000000000000b204000000000008221400000000000c02040200000000043200020000000110028100000000014002804000000000500a00400000000410020140000000050002004200000001100a0002000000000222810000000000028280400000000000aa00400000000008220140000000000a02004200000000022a0002000000000002c50000000000000a1440000000000002d0400000000000120540000000000012404200000000000a4402000000009002802000000000c002800800000000500600080000000410020028000000048002000a0000000090060002000000000122802000000000018280080000000000a600080000000008220028000000000902000a0000000001260002000000000002a4200000000000061408000000000002b0080000000000120428000000000012200a000000000006240200000000000282600000000000060148000000000002830800000000000a006800000000000a020a00000000000602420000000030028004000000003003000200000004200200030000000060028001000000005003000100000004100200050000000000628004000000000063000200000000084200030000000000c280010000000000a3000100000000082200050000000000028c040000000000030c02000000000003140100000000001208030000000000029801000000000012040500000000000280c400000000000300c2000000000003014100000000000a0083000000000002818100000000000a0045000000000002801c000000000003001a000000000003002900000000000600130000000000028031000000000006000d00000004400200000000000008820000000000000012100000000000000a0100000000000006002000000000000300040000000000028002,
  0x40814000000000004080c000000000004001c000000000000081c000000000004080600000000000400160000000000000816000000000004000e000000000000080e000000000000001e000000000004080500000000000400150000000000000815000000000004000d000000000000080d000000000000001d000000000004000700000000000008070000000000000017000000000000000f000000000004080480000000000400148000000000000814800000000004000c800000000000080c800000000000001c800000000004000680000000000008068000000000000016800000000000000e800000000004000580000000000008058000000000000015800000000000000d80000000000000078000000000008104200000000000810402000000000080042200000000000104220000000000810400200000000080042020000000000104202000000000800402200000000001040220000000000004222000000000810400100000000080042010000000000104201000000000800402100000000001040210000000000004221000000000800400300000000001040030000000000004203000000000000402300000000081040008000000008004200800000000010420080000000080040208000000000104020800000000000422080000000080040028000000000104002800000000000420280000000000040228000000008004001800000000010400180000000000042018000000000004021800000000000400380000000605040000000000028c0400000000000a0114000000000008841400000000000a080420000000000c040420000000000503040000000000018a04000000000009010c000000000008820c000000000009080402000000000c02040200000000018014400000000002800c400000000003000c2000000000050004600000000003001402000000000600044200000000000314400000000000050c400000000000060c2000000000000a0460000000000006140200000000000c04420000000000c88400000000000441840000000000088086000000000008410600000000000c0084002000000008480400200000000240062000000000028006100000000000c01410000000000440043000000000060004102000000002401400200000000004862000000000000506100000000000019410000000000008843000000000000c04102000000000049400200000000140060200000000018006010000000000c00c01000000000440040300000000050004012000000001400c00200000000002860200000000000306010000000000018c01000000000008840300000000000a04012000000000028c0020000000000006520000000000000c310000000000000661000000000000141300000000000014412000000000000c502000000000a84400000000000421440000000000088045000000000008210500000000000c0044001000000008280400100000000220052000000000028005080000000000a01408000000000420042800000000060004081000000002201400100000000004452000000000000505080000000000015408000000000008442800000000000c04081000000000045400100000000120050200000000018005008000000000a00c00800000000420040280000000050004009000000001200c00100000000002450200000000000305008000000000014c00800000000008440280000000000a04009000000000024c00100000000000054a0000000000000c288000000000000560800000000000140a80000000000014409000000000000c481000000000600500200000000060060010000000044004001400000000c005000400000000a006000400000004200400240000000000c500200000000000c60010000000000884001400000000018500040000000001460004000000000844002400000000000518200000000000061810000000000006280400000000001410140000000000053004000000000014082400000000000501a00000000000060190000000000006028400000000000c0114000000000005030400000000000c00a400000000982400000000000411240000000000088024800000000008110480000000000c002400080000000818040008000000021004a00000000002800484000000000090140400000000041004240000000006000404080000000210140008000000000424a000000000000504840000000000013404000000000008242400000000000c04040800000000043400080000000110048200000000018004804000000000900c00400000000410040240000000050004004800000001100c00080000000002248200000000000304804000000000012c00400000000008240240000000000a04004800000000022c0008000000000004c60000000000000c2440000000000004e0400000000000140640000000000014404800000000000c440800000000500480200000000050060008000000044004000a00000000c0048002000000009006000200000004100400220000000000a480200000000000a60008000000000884000a000000000184800200000000012600020000000008240022000000000004942000000000000614080000000000062402000000000014100a000000000004b002000000000014042200000000000481600000000000060148000000000006024200000000000c010a000000000004830200000000000c006200000000300480100000000030050008000000042004000900000000a0048001000000009005000100000004100400110000000000648010000000000065000800000000084400090000000001448001000000000125000100000000082400110000000000048c100000000000050c0800000000000524010000000000140809000000000004a801000000000014041100000000000480d000000000000500c8000000000005024100000000000c0089000000000004828100000000000c0051000000000005000e000000000004801600000000000500230000000000060013000000000006000d000000000004802500000004800400000000000009040000000000000014200000000000000c0200000000000006002000000000000500100000000000048008,
  0x40818000000000004080c000000000004001c000000000000081c000000000004080a000000000004001a000000000000081a000000000004000e000000000000080e000000000000001e000000000004080900000000000400190000000000000819000000000004000d000000000000080d000000000000001d000000000004000b000000000000080b000000000000001b000000000000000f000000000004080880000000000400188000000000000818800000000004000c800000000000080c800000000000001c800000000004000a800000000000080a800000000000001a800000000000000e800000000004000980000000000008098000000000000019800000000000000d800000000000000b800000000001020840000000000102080200000000010008420000000000020842000000000102080100000000010008410000000000020841000000000100080300000000000208030000000000000843000000000102080080000000010008408000000000020840800000000100080280000000000208028000000000000842800000000100080180000000000208018000000000000841800000000000080380000000010208004000000001000840400000000002084040000000010008024000000000020802400000000000084240000000010008014000000000020801400000000000084140000000000008034000000001000800c000000000020800c000000000000840c000000000000802c000000000000801c00000000606080000000000030c0800000000000a0218000000000009041800000000000a080840000000000c040840000000000189080000000000048308000000000009010c000000000008820c00000000000c01080200000000088808020000000002800c400000000003000c2000000000018018200000000004800860000000000600082200000000028018020000000000050c400000000000060c200000000000031820000000000009086000000000000c08220000000000051802000000000148880000000000044288000000000009008a000000000008420a00000000000c00880100000000084808010000000002400a400000000003000a1000000000014018100000000004400850000000000600081100000000024018010000000000048a400000000000060a100000000000029810000000000008885000000000000c081100000000000498010000000000c00a020000000000c00c0100000000048008012000000001800a002000000001400c0020000000044008022000000000018a020000000000018c0100000000000908012000000000030a002000000000028c0020000000000888022000000000000a320000000000000c310000000000000c5020000000000018212000000000000a6020000000000018122000000001284800000000000422480000000000090049000000000008220900000000000c0048008000000008280800800000000220094000000000030009080000000001201808000000000420084800000000060008088000000002201800800000000004494000000000000609080000000000025808000000000008484800000000000c080880000000000458008000000000a009020000000000a00c00800000000480080090000000018009001000000001200c00100000000420080210000000000149020000000000014c00800000000009080090000000000309001000000000024c001000000000084802100000000000092a0000000000000c288000000000000c4810000000000018209000000000000960100000000000180a10000000006009010000000000600a00800000000440080084000000014009000400000001200a000400000004200801040000000000c901000000000000ca00800000000008880084000000000289000400000000024a00040000000008480104000000000009190000000000000a188000000000000a480400000000001810840000000000095004000000000018090400000000000a00b0000000000009013000000000000a021400000000000c011400000000000c00a4000000000009022400000001182800000000000412280000000000090028800000000008120880000000000c002800400000000818080040000000021008c00000000003000884000000000110180400000000041008440000000006000804400000000210180040000000000428c000000000000608840000000000023804000000000008284400000000000c0804400000000004380040000000009008820000000000900c00400000000480080048000000018008800800000001100c00080000000410080208000000000128820000000000012c00400000000009080048000000000308800800000000022c00080000000008280208000000000008a60000000000000c244000000000000c44080000000000182048000000000008e0080000000000180608000000005008810000000000500a00400000000440080042000000014008800200000001100a000200000004100801020000000000a881000000000000aa00400000000008880042000000000288800200000000022a00020000000008280102000000000008950000000000000a144000000000000a44020000000000181042000000000008d002000000000018050200000000000a0068000000000008812800000000000a020a00000000000c010a00000000000c006200000000000882220000000030088080000000003009004000000004200800410000000120088001000000011009000100000004100800810000000000688080000000000069004000000000084800410000000002488001000000000229000100000000082800810000000000088c800000000000090c4000000000000944010000000000180841000000000008c801000000000018048100000000000900580000000000088098000000000009020900000000000c008900000000000c0051000000000008821100000000000900460000000000088086000000000009010300000000000a008300000000000a004500000000000881050000000500080000000000000a080000000000000018400000000000000c020000000000000a010000000000000900800000000000088040,
  0x408180000000000040814000000000004001c000000000000081c0000000000040812000000000004001a000000000000081a00000000000400160000000000000816000000000000001e00000000000408110000000000040019000000000000081900000000000400150000000000000815000000000000001d00000000000400130000000000000813000000000000001b000000000000001700000000000408108000000000040018800000000000081880000000000400148000000000000814800000000000001c80000000000400128000000000000812800000000000001a80000000000000168000000000040011800000000000081180000000000000198000000000000015800000000000001380000000000204104000000000020410200000000002001060000000000004106000000000020410100000000002001050000000000004105000000000020010300000000000041030000000000000107000000000020410080000000002001048000000000004104800000000020010280000000000041028000000000000106800000000020010180000000000041018000000000000105800000000000010380000000002041004000000000200104400000000000410440000000002001024000000000004102400000000000010640000000002001014000000000004101400000000000010540000000000001034000000000200100c000000000004100c000000000000104c000000000000102c000000000000101c00000000030a10000000000005061000000000000a0218000000000009041800000000000c021040000000000908104000000000028910000000000004851000000000000a0114000000000008841400000000000c01102000000000088810200000000001801440000000000180182000000000050010220000000003001402000000000280180200000000048010420000000000031440000000000003182000000000000a102200000000000614020000000000051802000000000009104200000000024890000000000004449000000000000a0092000000000008441200000000000c00901000000000084810100000000001401240000000000140181000000000050010110000000003001201000000000240180100000000044010410000000000029240000000000002981000000000000a10110000000000061201000000000004980100000000000890410000000000c012200000000000c01410000000000480101020000000028012002000000002401400200000000440102020000000000192200000000000019410000000000009101020000000000512002000000000049400200000000008902020000000000014130000000000001223000000000000144120000000000018212000000000001812200000000000124220000000022850000000000004245000000000000a0051000000000008241100000000000c00500800000000082810080000000001201140000000000120180800000000050010088000000003001100800000000220180080000000042010408000000000025140000000000002580800000000000a10088000000000061100800000000004580080000000000850408000000000a011200000000000a014080000000004801008100000000280110010000000022014001000000004201020100000000001512000000000000154080000000000091008100000000005110010000000000454001000000000085020100000000000140a800000000000112280000000000014409000000000001820900000000000180a1000000000001142100000000060111000000000006012080000000004401008040000000240110004000000022012000400000004201010040000000000d110000000000000d208000000000008900804000000000491000400000000045200040000000008501004000000000012098000000000001111800000000000124084000000000018108400000000001809040000000000114104000000000012083000000000001110300000000000122014000000000014101400000000001408240000000000112024000000021830000000000004143000000000000a0030800000000008141080000000000c003004000000000818100400000000011010c00000000001101804000000000500100440000000030010804000000002101800400000000410104040000000000230c0000000000002380400000000000a100440000000000610804000000000043800400000000008304040000000009010a00000000000901404000000000480100408000000028010800800000002101400080000000410102008000000000130a000000000000134040000000000091004080000000005108008000000000434000800000000083020080000000000140640000000000010a240000000000014404800000000001820480000000000180608000000000010c2080000000050109000000000005012040000000004401004020000000240108002000000021012000200000004101010020000000000b090000000000000b20400000000000890040200000000049080020000000004320002000000000830100200000000001205400000000000109140000000000012404200000000001810420000000000180502000000000010c10200000000001204280000000000109028000000000012200a000000000014100a0000000000140422000000000010a02200000000301088000000000030110400000000042010040100000002201080010000000210110001000000041010080100000000007088000000000000710400000000000850040100000000045080010000000004310001000000000830080100000000001104c000000000001088c0000000000011404100000000001808410000000000180481000000000010c08100000000001104180000000000108818000000000011200900000000001408090000000000140411000000000010a0110000000000110406000000000010880600000000001110030000000000120803000000000012040500000000001090050000000600100000000000000c10000000000000001840000000000000142000000000000012100000000000001108000000000000108400,
  0x80c200000000000080a2000000000000806200000000000000e20000000000008092000000000000805200000000000000d2000000000000803200000000000000b20000000000000072000000000000808a000000000000804a00000000000000ca000000000000802a00000000000000aa000000000000006a000000000000801a000000000000009a000000000000005a000000000000003a0000000000008086000000000000804600000000000000c6000000000000802600000000000000a600000000000000660000000000008016000000000000009600000000000000560000000000000036000000000000800e000000000000008e000000000000004e000000000000002e000000000000001e000000000000010208400000000001020804000000000102004400000000000208440000000001020800800000000102004080000000000208408000000001020004800000000002080480000000000200448000000001020800200000000102004020000000000208402000000001020004200000000002080420000000000200442000000001020000a000000000020800a000000000020040a000000000020004a00000000102080010000000010200401000000000020840100000000102000410000000000208041000000000020044100000000102000090000000000208009000000000020040900000000002000490000000010200003000000000020800300000000002004030000000000200043000000000020000b0000000218300000000000041430000000000006042080000000000a0030800000000006082004000000000c00300400000000011828000000000004122800000000000502208000000000090028800000000005082000400000000c00280040000000011420400000000002122040000000000302200400000000090020440000000003042000400000000a00204040000000000230c000000000000428c0000000000002380400000000000828440000000000043800400000000008304040000000009824000000000004112400000000000481208000000000088024800000000004882000080000000c00240008000000009420200000000002112020000000000281200400000000088020240000000002842000080000000a00202008000000000130a000000000000424a00000000000013404000000000008242400000000000434000800000000083020080000000092200200000000011120020000000001812000400000000880200240000000018220000800000009002002080000000001288200000000000224820000000000012c0040000000000824024000000000022c0008000000000828020800000000012046000000000002202600000000000120604000000000042022400000000002206008000000000420420800000000582200000000000410a200000000000440a08000000000084022800000000004482000020000000c0022000200000000542010000000000210a010000000000240a00400000000084020140000000002442000020000000a002010020000000000b0900000000000042290000000000000b2040000000000082214000000000004320002000000000830100200000000522001000000000110a001000000000140a000400000000840200140000000014220000200000009002001020000000000a8810000000000022281000000000000aa0040000000000822014000000000022a000200000000082801020000000000a0450000000000022015000000000000a0504000000000042011400000000002205002000000000420410200000000512000200000000090a0002000000000c0a00008000000084020002800000000c120000200000008802000220000000000a4802000000000012280200000000000a600080000000008220028000000000126000200000000082400220000000000a0242000000000012014200000000000a030080000000004201028000000000120300200000000042020220000000000a0026000000000012001600000000000a00308000000000220012800000000012003020000000002200222000000003821000000000004106100000000000420608000000000082021800000000004282000010000000c002100010000000034200800000000021060080000000002206004000000000820200c0000000002242000010000000a002008010000000000708800000000000421880000000000007104000000000008210c000000000004310001000000000830080100000000322000800000000110600080000000012060004000000008202000c00000000122200001000000090020008100000000006880800000000002218080000000000069004000000000082100c00000000002290001000000000828008100000000006044800000000002200c80000000000060484000000000042008c0000000000220480100000000042040810000000031200010000000009060001000000000a0600008000000082020001800000000a1200001000000088020001100000000006480100000000001218010000000000065000800000000082100180000000001250001000000000824001100000000006024100000000001200c100000000000602808000000000420081800000000012028010000000004202011000000000060025000000000012000d000000000006002880000000002200098000000000120028100000000022002110000000030a000040000000050600004000000006060000200000008202000060000000060a00001000000084020000500000000006280040000000000a18004000000000063000200000000082100060000000000a30001000000000822000500000000006014040000000000a00c04000000000060180200000000042008060000000000a01801000000000420100500000000006001440000000000a000c4000000000060018200000000022000860000000000a001810000000002200105000000000060002c0000000000a0001c000000000060003200000000012000160000000000a000310000000001200025000000081020000000000000082080000000000004200400000000000220004000000000012000080000000000a000020000000000600001,
  0x80c400000000000080a4000000000000806400000000000000e40000000000008094000000000000805400000000000000d4000000000000803400000000000000b40000000000000074000000000000808c000000000000804c00000000000000cc000000000000802c00000000000000ac000000000000006c000000000000801c000000000000009c000000000000005c000000000000003c0000000000008086000000000000804600000000000000c6000000000000802600000000000000a600000000000000660000000000008016000000000000009600000000000000560000000000000036000000000000800e000000000000008e000000000000004e000000000000002e000000000000001e00000000000002041080000000000204100800000000020400880000000000041088000000000204100100000000020400810000000000041081000000000204000900000000000410090000000000040089000000000204100040000000020400804000000000041080400000000204000840000000000410084000000000040088400000000204000140000000000410014000000000040081400000000004000940000000020410001000000002040080100000000004108010000000020400081000000000041008100000000004008810000000020400011000000000041001100000000004008110000000000400091000000002040000500000000004100050000000000400805000000000040008500000000004000150000000228500000000000042450000000000006044100000000000a0051000000000006084008000000000c00500800000000012848000000000004224800000000000502410000000000090049000000000005084000800000000c00480080000000012440400000000002224040000000000302400800000000090040480000000003044000800000000a0040408000000000025140000000000004494000000000000258080000000000084848000000000004580080000000000850408000000000a844000000000004214400000000000481410000000000088045000000000004884000100000000c0044001000000000a440200000000002214020000000000281400800000000088040280000000002844000100000000a0040201000000000015120000000000004452000000000000154080000000000084428000000000004540010000000000850201000000000a2400200000000012140020000000001814000800000000880400280000000018240001000000009004002100000000001490200000000000245020000000000014c0080000000000844028000000000024c001000000000084802100000000001404a000000000002402a00000000000140608000000000044022800000000002406010000000000440421000000000684200000000000420c200000000000440c10000000000084043000000000004484000040000000c0042000400000000644010000000000220c010000000000240c00800000000084040180000000002444000040000000a004010040000000000d1100000000000044310000000000000d2080000000000084218000000000004520004000000000850100400000000624001000000000120c001000000000140c000800000000840400180000000014240000400000009004001040000000000c9010000000000024301000000000000ca0080000000000842018000000000024a000400000000084801040000000000c0490000000000024019000000000000c05080000000000440118000000000024050040000000004404104000000006140002000000000a0c0002000000000c0c00010000000084040003000000000c140000400000008804000240000000000c5002000000000014300200000000000c600100000000008420030000000000146000400000000084400240000000000c0282000000000014018200000000000c030100000000004401030000000000140300400000000044020240000000000c002a000000000014001a00000000000c0031000000000024001300000000001400304000000000240022400000004106100000000000420608000000000003840800000000008104180000000000c0040800100000004184000010000000210600800000000022060040000000000344004000000000810400c000000000a0040040100000002144000010000000000708800000000000441840000000000007104000000000008408c000000000008500401000000000450800100000001106000800000000120600040000000003240004000000008104000c00000000900400041000000011240000100000000006880800000000002418040000000000069004000000000084080c00000000008480041000000000248800100000000006044800000000002400c40000000000060484000000000044004c000000000044040410000000002404401000000009060001000000000a0600008000000003140000800000008104000180000000880400009000000009140000100000000006480100000000001418008000000000065000800000000084080180000000008440009000000000144800100000000006024100000000001400c080000000000602808000000000440041800000000044020090000000001402401000000000060025000000000014000c80000000000600288000000000240005800000000024002090000000001400241000000005060000400000000606000020000000030c00002000000081040000600000008404000030000000050c0000100000000006280040000000000c180020000000000630002000000000840800600000000084200030000000000c2800100000000006014040000000000c00c020000000000601802000000000440040600000000044010030000000000c0140100000000006001440000000000c000c20000000000600182000000000240004600000000024001030000000000c00141000000000060002c0000000000c0001a0000000000600032000000000140000e00000000014000230000000000c00029000000082040000000000000084100000000000004400800000000000240008000000000014000100000000000c000040000000000600001,
  0x80c800000000000080a8000000000000806800000000000000e80000000000008098000000000000805800000000000000d8000000000000803800000000000000b80000000000000078000000000000808c000000000000804c00000000000000cc000000000000802c00000000000000ac000000000000006c000000000000801c000000000000009c000000000000005c000000000000003c000000000000808a000000000000804a00000000000000ca000000000000802a00000000000000aa000000000000006a000000000000801a000000000000009a000000000000005a000000000000003a000000000000800e000000000000008e000000000000004e000000000000002e000000000000001e00000000000004082100000000000408201000000000040801100000000000082110000000000408200200000000040801020000000000082102000000000408001200000000000820120000000000080112000000000408200040000000040801004000000000082100400000000408001040000000000820104000000000080110400000000408000240000000000820024000000000080102400000000008001240000000040820002000000004080100200000000008210020000000040800102000000000082010200000000008011020000000040800022000000000082002200000000008010220000000000800122000000004080000600000000008200060000000000801006000000000080010600000000008000260000000248900000000000044490000000000006048200000000000a0092000000000006088010000000000c0090100000000001488800000000000442880000000000050282000000000009008a000000000005088001000000000c00880100000000014480400000000002428040000000000302801000000000090080500000000003048001000000000a00804100000000000292400000000000048a4000000000000298100000000000088850000000000004980100000000000890410000000000c884000000000004418400000000000481820000000000088086000000000004888000200000000c0084002000000000c480200000000002418020000000000281801000000000088080300000000002848000200000000a0080202000000000019220000000000004862000000000000194100000000000088430000000000004940020000000000890202000000000c28002000000000141800200000000018180010000000008808003000000000182800020000000090080022000000000018a0200000000000286020000000000018c0100000000000884030000000000028c002000000000088802200000000001805200000000000280320000000000018061000000000004802300000000000280602000000000048042200000000420c200000000000440c10000000000006881000000000008208300000000000c0081000400000004288000040000000220c010000000000240c00800000000006480080000000008208018000000000a0080080400000002248000040000000000d1100000000000048308000000000000d208000000000008811800000000000890080400000000049100040000000120c001000000000140c0008000000000628000800000000820800180000000090080008400000001228000040000000000c9010000000000028300800000000000ca00800000000008810180000000000888008400000000028900040000000000c0490000000000028018800000000000c0508000000000048009800000000004804084000000000280480400000000a0c0002000000000c0c0001000000000618000100000000820800030000000088080001400000000a18000040000000000c5002000000000018300100000000000c600100000000008810030000000000884001400000000018500040000000000c0282000000000018018100000000000c030100000000004800830000000000480201400000000018028040000000000c002a000000000018001900000000000c0031000000000028000b0000000000280021400000000018002840000000410a200000000000440a08000000000005880800000000008108280000000000c0080800200000004188000020000000210a010000000000240a00400000000005480040000000008108014000000000a0080040200000002148000020000000000b0900000000000048284000000000000b204000000000008809400000000000890040200000000049080020000000110a001000000000140a0004000000000528000400000000810800140000000090080004200000001128000020000000000a8810000000000028280400000000000aa00400000000008808140000000000888004200000000028880020000000000a0450000000000028014400000000000a050400000000004800540000000000480404200000000028044020000000090a0002000000000c0a0000800000000518000080000000810800028000000088080000a00000000918000020000000000a4802000000000018280080000000000a600080000000008808028000000000884000a00000000018480020000000000a0242000000000018014080000000000a030080000000004800428000000000480200a00000000018024020000000000a0026000000000018001480000000000a003080000000002800068000000000280020a00000000018002420000000030a000040000000030c0000200000008208000030000000060a000010000000050c0000100000008108000050000000000a180040000000000c180020000000000c2800100000000088100030000000000a3000100000000088080050000000000a00c040000000000c00c020000000000c0140100000000048008030000000000a0180100000000048004050000000000a000c40000000000c000c20000000000c0014100000000028000830000000000a0018100000000028000450000000000a0001c0000000000c0001a0000000000c0002900000000018000130000000000a00031000000000180000d000000084080000000000000088200000000000004801000000000000280010000000000018000200000000000c000040000000000a00002,
  0x80d000000000000080b0000000000000807000000000000000f00000000000008098000000000000805800000000000000d8000000000000803800000000000000b800000000000000780000000000008094000000000000805400000000000000d4000000000000803400000000000000b40000000000000074000000000000801c000000000000009c000000000000005c000000000000003c0000000000008092000000000000805200000000000000d2000000000000803200000000000000b20000000000000072000000000000801a000000000000009a000000000000005a000000000000003a0000000000008016000000000000009600000000000000560000000000000036000000000000001e00000000000008104200000000000810402000000000081002200000000000104220000000000810400200000000081002020000000000104202000000000810002200000000001040220000000000100222000000000810400100000000081002010000000000104201000000000810002100000000001040210000000000100221000000000810000300000000001040030000000000100203000000000010002300000000081040008000000008100200800000000010420080000000081000208000000000104020800000000010022080000000081000028000000000104002800000000010020280000000001000228000000008100001800000000010400180000000001002018000000000100021800000000010000380000000289100000000000048510000000000006050400000000000a0114000000000006090020000000000c0110200000000001890800000000000483080000000000050304000000000009010c000000000005090002000000000c01080200000000018500400000000002830040000000000303002000000000090100600000000003050002000000000a01004200000000000314400000000000050c400000000000031820000000000009086000000000000518020000000000091042000000000441840000000000048182000000000000c902000000000008410600000000000c0102002000000004490000200000000241802000000000028180100000000000c500100000000008410030000000000a0100102000000002450000200000000001922000000000000506100000000000019410000000000009023000000000000910102000000000051200200000000141800200000000018180010000000000c300010000000008410003000000000901000120000000014300002000000000018a0200000000000306010000000000018c01000000000009020300000000000908012000000000030a00200000000001805200000000000300310000000000018061000000000005001300000000000500412000000000030050200000000421440000000000048141000000000000a901000000000008210500000000000c0101001000000004290000100000000221402000000000028140080000000000a500080000000008210028000000000a0100081000000002250000100000000001512000000000000505080000000000015408000000000009012800000000000910081000000000051100100000000121400200000000018140008000000000a30000800000000821000280000000090100009000000001230000100000000001490200000000000305008000000000014c00800000000009010280000000000908009000000000030900100000000001404a00000000000300288000000000014060800000000005000a800000000005004090000000000300481000000000614000200000000061800010000000084100001400000000c140000400000000a1800004000000082100002400000000014300200000000001830010000000000185000400000000090200140000000001460004000000000901002400000000014018200000000001801810000000000180280400000000050010140000000001403004000000000500082400000000014001a0000000000180019000000000018002840000000003000114000000000140030400000000030000a400000004112400000000000481208000000000009900800000000008110480000000000c01008008000000041900000800000002112020000000000281200400000000009500040000000008110024000000000a010004080000000215000008000000000130a00000000000050484000000000001340400000000000900a400000000000910040800000000051080080000000111200200000000018120004000000000930000400000000811000240000000090100004800000001130000080000000001288200000000000304804000000000012c004000000000090082400000000009080048000000000308800800000000012046000000000003002440000000000120604000000000050006400000000005004048000000000300440800000000512000200000000051800008000000084100000a00000000c120000200000000918000020000000811000022000000000122802000000000018280080000000001848002000000000902000a00000000012600020000000009008022000000000120142000000000018014080000000001802402000000000500100a00000000012030020000000005000422000000000120016000000000018001480000000001800242000000000300010a0000000001200302000000000300006200000000312000100000000031400008000000082100000900000000a1200001000000009140000100000008110000110000000001218010000000000141800800000000014480010000000009010009000000000125000100000000090080110000000001200c100000000001400c08000000000140240100000000050008090000000001202801000000000500041100000000012000d000000000014000c80000000001400241000000000300008900000000012002810000000003000051000000000140000e000000000120001600000000014000230000000001800013000000000180000d00000000012000250000000881000000000000000904000000000000050020000000000003000200000000000180002000000000014000100000000001200008,
  0x80e000000000000080b0000000000000807000000000000000f000000000000080a8000000000000806800000000000000e8000000000000803800000000000000b8000000000000007800000000000080a4000000000000806400000000000000e4000000000000803400000000000000b40000000000000074000000000000802c00000000000000ac000000000000006c000000000000003c00000000000080a2000000000000806200000000000000e2000000000000803200000000000000b20000000000000072000000000000802a00000000000000aa000000000000006a000000000000003a000000000000802600000000000000a600000000000000660000000000000036000000000000002e0000000000001020840000000000102080200000000010200420000000000020842000000000102080100000000010200410000000000020841000000000102000300000000000208030000000000020043000000000102080080000000010200408000000000020840800000000102000280000000000208028000000000020042800000000102000180000000000208018000000000020041800000000002000380000000010208004000000001020040400000000002084040000000010200024000000000020802400000000002004240000000010200014000000000020801400000000002004140000000000200034000000001020000c000000000020800c000000000020040c000000000020002c000000000020001c0000000030a100000000000050610000000000006060800000000000a02180000000000060a0040000000000c0210400000000004830800000000000503040000000000018a04000000000008820c00000000000c02040200000000048a00020000000002830040000000000303002000000000018600200000000008820060000000000a020022000000000286000200000000000314400000000000060c20000000000003182000000000000a046000000000000a102200000000000614020000000004428800000000000502820000000000014a02000000000008420a00000000000c02020100000000044a00010000000002428040000000000302801000000000014600100000000008420050000000000a020011000000000246000100000000000292400000000000060a10000000000002981000000000000a025000000000000a101100000000000612010000000000c280020000000000c300010000000008820001200000000182800020000000014300002000000008420002200000000002860200000000000306010000000000030a0020000000000a04012000000000028c0020000000000a02022000000000028032000000000003003100000000000300502000000000060021200000000002806020000000000600122000000004224800000000000502410000000000012a01000000000008220900000000000c02010080000000042a00008000000002224040000000000302400800000000012600080000000008220048000000000a020008800000000226000080000000000251400000000000060908000000000002580800000000000a014800000000000a100880000000000611008000000000a240020000000000a30000800000000882000090000000018240001000000001230000100000000822000210000000000245020000000000030500800000000003090010000000000a04009000000000024c0010000000000a0102100000000002402a0000000000030028800000000003004810000000000600209000000000024060100000000006000a10000000006240010000000000628000800000000842000084000000014240000400000001228000040000000822000104000000000243010000000000028300800000000002890004000000000a02008400000000024a0004000000000a01010400000000024019000000000002801880000000000280480400000000060010840000000002405004000000000600090400000000028000b000000000024001300000000002800214000000000300011400000000030000a4000000000240022400000004122800000000000502208000000000011a00800000000008120880000000000c02008040000000041a00004000000002122040000000000302200400000000011600040000000008120044000000000a020004400000000216000040000000000230c00000000000060884000000000002380400000000000a00c400000000000a1004400000000006108040000000009220020000000000930000400000000882000048000000018220000800000001130000080000000812000208000000000224820000000000030480400000000003088008000000000a04004800000000022c0008000000000a008208000000000220260000000000030024400000000003004408000000000600204800000000022060080000000006000608000000005220010000000000528000400000000842000042000000014220000200000001128000020000000812000102000000000222810000000000028280400000000002888002000000000a02004200000000022a0002000000000a00810200000000022015000000000002801440000000000280440200000000060010420000000002205002000000000600050200000000028000680000000002200128000000000280020a000000000300010a00000000030000620000000002200222000000003220008000000000324000400000000822000041000000012220000100000001124000010000000812000081000000000221808000000000024180400000000002488001000000000a0100410000000002290001000000000a0080810000000002200c800000000002400c4000000000024044010000000006000841000000000220480100000000060004810000000002400058000000000220009800000000024002090000000003000089000000000300005100000000022002110000000002400046000000000220008600000000024001030000000002800083000000000280004500000000022001050000000902000000000000000a08000000000000060040000000000003000200000000000280010000000000024000800000000002200040,
  0x80e000000000000080d0000000000000807000000000000000f000000000000080c8000000000000806800000000000000e8000000000000805800000000000000d8000000000000007800000000000080c4000000000000806400000000000000e4000000000000805400000000000000d40000000000000074000000000000804c00000000000000cc000000000000006c000000000000005c00000000000080c2000000000000806200000000000000e2000000000000805200000000000000d20000000000000072000000000000804a00000000000000ca000000000000006a000000000000005a000000000000804600000000000000c600000000000000660000000000000056000000000000004e000000000000204104000000000020410200000000002040060000000000004106000000000020410100000000002040050000000000004105000000000020400300000000000041030000000000004007000000000020410080000000002040048000000000004104800000000020400280000000000041028000000000004006800000000020400180000000000041018000000000004005800000000000400380000000002041004000000000204004400000000000410440000000002040024000000000004102400000000000400640000000002040014000000000004101400000000000400540000000000040034000000000204000c000000000004100c000000000004004c000000000004002c000000000004001c0000000005061000000000000606080000000000030c08000000000009041800000000000c04084000000000050c00400000000004851000000000000605040000000000028c04000000000008841400000000000c04042000000000048c00200000000001850040000000000186002000000000090400220000000003050002000000000286000200000000088400420000000000050c400000000000060c20000000000006140200000000000c0822000000000005180200000000000c04420000000004449000000000000604820000000000024c02000000000008441200000000000c04021000000000044c00100000000001448040000000000146001000000000090400110000000003048001000000000246000100000000084400410000000000048a400000000000060a10000000000006120100000000000c0811000000000004980100000000000c02410000000000c480200000000000c50010000000000884001020000000028480002000000002450000200000000844002020000000000486200000000000050610000000000005120020000000000c0410200000000004940020000000000c02202000000000050013000000000004802300000000000500412000000000060021200000000006001220000000000480422000000004245000000000000604410000000000022c01000000000008241100000000000c04010800000000042c000800000000012440400000000001260008000000000904000880000000030440008000000002260000800000000824004080000000000449400000000000060908000000000006110080000000000c0808800000000004580080000000000c01408000000000a440200000000000a50008000000000884000810000000028440001000000002250000100000000824002010000000000445200000000000050508000000000005110010000000000c0408100000000004540010000000000c0120100000000005000a800000000004402280000000000500409000000000060020900000000006000a100000000004404210000000006440100000000000648008000000000844000804000000024440000400000002248000040000000824001004000000000443100000000000048308000000000004910004000000000c0208040000000004520004000000000c01100400000000048009800000000004401180000000000480408400000000060010840000000006000904000000000440410400000000048008300000000004401030000000000480201400000000050010140000000005000824000000000440202400000004143000000000000604208000000000021c00800000000008141080000000000c04008400000000041c000400000000011420400000000001160004000000000904000440000000030420004000000002160000400000000814004040000000000428c00000000000060884000000000006108040000000000c0804400000000004380040000000000c00c040000000009420200000000000950004000000000884000408000000028420000800000002150000080000000814002008000000000424a00000000000050484000000000005108008000000000c0404080000000004340008000000000c00a008000000000500064000000000042022400000000005004048000000000600204800000000060006080000000004204208000000005420100000000000548004000000000844000402000000024420000200000002148000020000000814001002000000000422900000000000048284000000000004908002000000000c0204020000000004320002000000000c00900200000000048005400000000004201140000000000480404200000000060010420000000006000502000000000420410200000000048004280000000004201028000000000480200a000000000500100a00000000050004220000000004202022000000003420080000000000344004000000000824000401000000022420000100000002144000010000000814000801000000000421880000000000044184000000000004508001000000000c0104010000000004310001000000000c00880100000000044004c000000000042008c000000000044040410000000006000841000000000600048100000000042040810000000004400418000000000420081800000000044020090000000005000809000000000500041100000000042020110000000004400406000000000420080600000000044010030000000004800803000000000480040500000000042010050000000a04000000000000000c10000000000000060040000000000005002000000000000480100000000000044008000000000004200400,
  0x80e000000000000080d000000000000080b000000000000000f000000000000080c800000000000080a800000000000000e8000000000000809800000000000000d800000000000000b800000000000080c400000000000080a400000000000000e4000000000000809400000000000000d400000000000000b4000000000000808c00000000000000cc00000000000000ac000000000000009c00000000000080c200000000000080a200000000000000e2000000000000809200000000000000d200000000000000b2000000000000808a00000000000000ca00000000000000aa000000000000009a000000000000808600000000000000c600000000000000a60000000000000096000000000000008e000000000000408180000000000040814000000000004080c000000000000081c0000000000040812000000000004080a000000000000081a00000000000408060000000000000816000000000000080e00000000000408110000000000040809000000000000081900000000000408050000000000000815000000000000080d00000000000408030000000000000813000000000000080b000000000000080700000000000408108000000000040808800000000000081880000000000408048000000000000814800000000000080c80000000000408028000000000000812800000000000080a8000000000000806800000000004080180000000000008118000000000000809800000000000080580000000000008038000000000030a100000000000030c0800000000000a08084000000000060a004000000000050c00400000000009081040000000000289100000000000028c0400000000000a080420000000000609002000000000048c00200000000008881020000000000189080000000000018a04000000000009080402000000000509000200000000048a0002000000000888080200000000000a0460000000000009086000000000000a102200000000000c082200000000000c04420000000000091042000000000248900000000000024c0200000000000a080210000000000608801000000000044c00100000000008481010000000000148880000000000014a02000000000009080201000000000508800100000000044a0001000000000848080100000000000a0250000000000008885000000000000a101100000000000c081100000000000c024100000000000890410000000000c884000000000000c90200000000000888020020000000048880002000000004490000200000000848040020000000000902300000000000088430000000000009101020000000000c041020000000000c0220200000000008902020000000000902030000000000088403000000000009080120000000000a040120000000000a02022000000000088802200000000228500000000000022c0100000000000a080108000000000608400800000000042c00080000000008281008000000000128480000000000012a01000000000009080100800000000508400080000000042a0000800000000828080080000000000a0148000000000008484800000000000a100880000000000c080880000000000c014080000000000850408000000000a844000000000000a90100000000000888010010000000048840001000000004290000100000000828040010000000000901280000000000084428000000000009100810000000000c040810000000000c0120100000000008502010000000000901028000000000084402800000000009080090000000000a040090000000000a0102100000000008480210000000006842000000000000688100000000000848010004000000044840000400000004288000040000000828020004000000000881180000000000084218000000000008900804000000000c020804000000000c0110040000000008501004000000000881018000000000084201800000000008880084000000000a020084000000000a01010400000000084801040000000008810030000000000842003000000000088400140000000009020014000000000901002400000000084400240000000218300000000000021c0080000000000a080084000000000608200400000000041c00040000000008181004000000000118280000000000011a00800000000009080080400000000508200040000000041a0000400000000818080040000000000a00c4000000000008284400000000000a100440000000000c080440000000000c00c0400000000008304040000000009824000000000000990080000000000888008008000000048820000800000004190000080000000818040008000000000900a40000000000082424000000000009100408000000000c040408000000000c00a0080000000008302008000000000900824000000000082402400000000009080048000000000a040048000000000a0082080000000008280208000000005822000000000000588080000000000848008002000000044820000200000004188000020000000818020002000000000880940000000000082214000000000008900402000000000c020402000000000c0090020000000008301002000000000880814000000000082201400000000008880042000000000a020042000000000a008102000000000828010200000000088080280000000008220028000000000884000a000000000902000a000000000900802200000000082400220000000038210000000000003840800000000008280080010000000428200001000000041840000100000008180100010000000008408c000000000008210c000000000008500401000000000c010401000000000c008801000000000830080100000000084080c000000000082100c00000000008480041000000000a010041000000000a00808100000000082800810000000008408018000000000821001800000000084400090000000009010009000000000900801100000000082400110000000008408006000000000821000600000000084200030000000008810003000000000880800500000000082200050000000c08000000000000000c100000000000000a0800000000000009040000000000000882000000000000084100000000000008208000,
  0xe100000000000000d100000000000000b1000000000000007100000000000000c900000000000000a9000000000000006900000000000000990000000000000059000000000000003900000000000000c500000000000000a50000000000000065000000000000009500000000000000550000000000000035000000000000008d000000000000004d000000000000002d000000000000001d00000000000000c300000000000000a30000000000000063000000000000009300000000000000530000000000000033000000000000008b000000000000004b000000000000002b000000000000001b0000000000000087000000000000004700000000000000270000000000000017000000000000000f00000000000000010208400000000001020804000000000102004400000000010008440000000001020800800000000102004080000000010008408000000001020004800000000100080480000000010000448000000001020800200000000102004020000000010008402000000001020004200000000100080420000000010000442000000001020000a000000001000800a000000001000040a000000001000004a00000000102080010000000010200401000000001000840100000000102000410000000010008041000000001000044100000000102000090000000010008009000000001000040900000000100000490000000010200003000000001000800300000000100004030000000010000043000000001000000b00000002183000000000000414300000000000021c0080000000000814108000000000041c000400000000081810040000000001182800000000000412280000000000011a0080000000000812088000000000041a0000400000000818080040000000011420400000000002122040000000000116000400000000081200440000000002160000400000000814004040000000011010c000000000021008c0000000000110180400000000041008440000000002101800400000000410104040000000009824000000000004112400000000000099008000000000081104800000000004190000080000000818040008000000009420200000000002112020000000000095000400000000081100240000000002150000080000000814002008000000009010a000000000021004a00000000000901404000000000410042400000000021014000800000004101020080000000092200200000000011120020000000000930000400000000811000240000000011300000800000008120002080000000090088200000000011004820000000000900c0040000000041004024000000001100c0008000000041008020800000000900046000000000110002600000000009000604000000002100022400000000110006008000000021000420800000000582200000000000410a20000000000005880800000000008108280000000000418800002000000081802000200000000542010000000000210a01000000000005480040000000008108014000000000214800002000000081400100200000000501090000000000210029000000000005012040000000004100214000000000210120002000000041010100200000000522001000000000110a0010000000000528000400000000810800140000000011280000200000008120001020000000050088100000000011002810000000000500a0040000000041002014000000001100a0002000000041008010200000000500045000000000110001500000000005000504000000002100011400000000110005002000000021000410200000000512000200000000090a0002000000000518000080000000810800028000000009180000200000008110000220000000050048020000000009002802000000000500600080000000410020028000000009006000200000004100400220000000050002420000000009000142000000000500030080000000210001028000000009000300200000002100020220000000050000260000000009000016000000000500003080000000110000128000000009000030200000001100002220000000038210000000000041061000000000000384080000000000810418000000000041840000100000008180100010000000034200800000000021060080000000000344004000000000810400c00000000021440000100000008140008010000000030108800000000021001880000000000301104000000000410010c000000000210110001000000041010080100000000322000800000000110600080000000003240004000000008104000c00000000112400001000000081200008100000000300880800000000110018080000000003009004000000004100100c00000000110090001000000041008008100000000300044800000000110000c80000000003000484000000002100008c00000000110004801000000021000408100000000312000100000000090600010000000003140000800000008104000180000000091400001000000081100001100000000300480100000000090018010000000003005000800000004100100180000000090050001000000041004001100000000300024100000000090000c100000000030002808000000021000081800000000900028010000000210002011000000003000025000000000900000d000000000300002880000000110000098000000009000028100000001100002110000000030a0000400000000506000040000000030c0000200000008104000060000000050c00001000000081080000500000000300280040000000050018004000000003003000200000004100100060000000050030001000000041002000500000000300014040000000050000c040000000030001802000000021000080600000000500018010000000210001005000000003000014400000000500000c40000000030000182000000011000008600000000500001810000000110000105000000003000002c000000005000001c00000000300000320000000090000016000000005000003100000000900000250000000810200000000000041000800000000002100004000000000110000040000000009000000800000000500000020000000030000001,
  0xe200000000000000d200000000000000b2000000000000007200000000000000ca00000000000000aa000000000000006a000000000000009a000000000000005a000000000000003a00000000000000c600000000000000a60000000000000066000000000000009600000000000000560000000000000036000000000000008e000000000000004e000000000000002e000000000000001e00000000000000c300000000000000a30000000000000063000000000000009300000000000000530000000000000033000000000000008b000000000000004b000000000000002b000000000000001b0000000000000087000000000000004700000000000000270000000000000017000000000000000f00000000000000020410800000000002041008000000000204008800000000020010880000000002041001000000000204008100000000020010810000000002040009000000000200100900000000020000890000000002041000400000000204008040000000020010804000000002040008400000000200100840000000020000884000000002040001400000000200100140000000020000814000000002000009400000000204100010000000020400801000000002001080100000000204000810000000020010081000000002000088100000000204000110000000020010011000000002000081100000000200000910000000020400005000000002001000500000000200008050000000020000085000000002000001500000002285000000000000424500000000000022c0100000000000824110000000000042c000800000000082810080000000001284800000000000422480000000000012a0100000000000822090000000000042a000080000000082808008000000001244040000000000222404000000000012600080000000008220048000000000226000080000000082400408000000001201140000000000220094000000000012018080000000004200848000000000220180080000000042010408000000000a8440000000000042144000000000000a901000000000008210500000000000429000010000000082804001000000000a4402000000000022140200000000000a500080000000008210028000000000225000010000000082400201000000000a0112000000000022005200000000000a014080000000004200428000000000220140010000000042010201000000000a2400200000000012140020000000000a300008000000008210002800000000123000010000000082200021000000000a0090200000000012005020000000000a00c0080000000042004028000000001200c0010000000042008021000000000a0004a000000000120002a0000000000a000608000000002200022800000000120006010000000022000421000000000684200000000000420c20000000000006881000000000008208300000000000428800004000000082802000400000000644010000000000220c01000000000006480080000000008208018000000000224800004000000082400100400000000601110000000000220031000000000006012080000000004200218000000000220120004000000042010100400000000624001000000000120c0010000000000628000800000000820800180000000012280000400000008220001040000000060090100000000012003010000000000600a0080000000042002018000000001200a00040000000420080104000000006000490000000001200019000000000060005080000000022000118000000001200050040000000220004104000000006140002000000000a0c000200000000061800010000000082080003000000000a18000040000000821000024000000006005002000000000a00300200000000060060010000000042002003000000000a00600040000000420040024000000006000282000000000a00018200000000060003010000000022000103000000000a0003004000000022000202400000000600002a000000000a00001a00000000060000310000000012000013000000000a000030400000001200002240000000038210000000000042060800000000000384080000000000820218000000000082800800100000004282000010000000034200800000000022060040000000000344004000000000820200c00000000082400040100000002242000010000000030108800000000022001840000000000301104000000000420008c000000000420100401000000022010800100000000322000800000000120600040000000003240004000000008202000c00000000822000041000000012220000100000000300880800000000120018040000000003009004000000004200080c00000000420080041000000012008800100000000300044800000000120000c40000000003000484000000002200004c000000002200040410000000120004401000000003120001000000000a060000800000000314000080000000820200018000000082100000900000000a1200001000000003004801000000000a001800800000000300500080000000420008018000000042004000900000000a0048001000000003000241000000000a0000c0800000000300028080000000220000418000000022000200900000000a0002401000000003000025000000000a00000c800000000300002880000000120000058000000012000020900000000a00002410000000030a0000400000000606000020000000030c00002000000082020000600000008208000030000000060a0000100000000300280040000000060018002000000003003000200000004200080060000000420020003000000006002800100000000300014040000000060000c020000000030001802000000022000040600000002200010030000000060001401000000003000014400000000600000c20000000030000182000000012000004600000001200001030000000060000141000000003000002c000000006000001a000000003000003200000000a000000e00000000a00000230000000060000029000000082040000000000004200100000000000220000800000000012000008000000000a000001000000000600000040000000030000001,
  0xe400000000000000d400000000000000b4000000000000007400000000000000cc00000000000000ac000000000000006c000000000000009c000000000000005c000000000000003c00000000000000c600000000000000a60000000000000066000000000000009600000000000000560000000000000036000000000000008e000000000000004e000000000000002e000000000000001e00000000000000c500000000000000a50000000000000065000000000000009500000000000000550000000000000035000000000000008d000000000000004d000000000000002d000000000000001d0000000000000087000000000000004700000000000000270000000000000017000000000000000f00000000000000040821000000000004082010000000000408011000000000040021100000000004082002000000000408010200000000040021020000000004080012000000000400201200000000040001120000000004082000400000000408010040000000040021004000000004080010400000000400201040000000040001104000000004080002400000000400200240000000040001024000000004000012400000000408200020000000040801002000000004002100200000000408001020000000040020102000000004000110200000000408000220000000040020022000000004000102200000000400001220000000040800006000000004002000600000000400010060000000040000106000000004000002600000002489000000000000444900000000000024c0200000000000844120000000000044c001000000000084810100000000001488800000000000442880000000000014a02000000000008420a0000000000044a0001000000000848080100000000014480400000000002428040000000000146001000000000084200500000000002460001000000000844004100000000014012400000000002400a4000000000014018100000000004400850000000000240180100000000044010410000000000c8840000000000044184000000000000c902000000000008410600000000000449000020000000084804002000000000c4802000000000024180200000000000c500100000000008410030000000000245000020000000084400202000000000c0122000000000024006200000000000c014100000000004400430000000000240140020000000044010202000000000c2800200000000014180020000000000c300010000000008410003000000000143000020000000084200022000000000c00a0200000000014006020000000000c00c0100000000044004030000000001400c0020000000044008022000000000c0005200000000014000320000000000c000610000000002400023000000000140006020000000024000422000000000684200000000000440c10000000000006881000000000008404300000000000848010004000000044840000400000000644010000000000240c00800000000006480080000000008404018000000000844000804000000024440000400000000601110000000000240030800000000006012080000000004400118000000000440100804000000024011000400000000624001000000000140c0008000000000628000800000000840400180000000084200008400000001424000040000000060090100000000014003008000000000600a0080000000044001018000000004400800840000000140090004000000006000490000000001400018800000000060005080000000024000098000000002400040840000000140004804000000006140002000000000c0c0001000000000618000100000000840400030000000084100001400000000c1400004000000006005002000000000c003001000000000600600100000000440010030000000044004001400000000c0050004000000006000282000000000c000181000000000600030100000000240000830000000024000201400000000c000280400000000600002a000000000c0000190000000006000031000000001400000b0000000014000021400000000c000028400000000582200000000000440a08000000000005880800000000008402280000000000848008002000000044820000200000000542010000000000240a00400000000005480040000000008402014000000000844000402000000024420000200000000501090000000000240028400000000005012040000000004400094000000000440100402000000024010800200000000522001000000000140a0004000000000528000400000000840200140000000084200004200000001422000020000000050088100000000014002804000000000500a0040000000044000814000000004400800420000000140088002000000005000450000000001400014400000000050005040000000024000054000000002400040420000000140004402000000005120002000000000c0a0000800000000518000080000000840200028000000084100000a00000000c1200002000000005004802000000000c002800800000000500600080000000440008028000000044004000a00000000c0048002000000005000242000000000c000140800000000500030080000000240000428000000024000200a00000000c0002402000000005000026000000000c000014800000000500003080000000140000068000000014000020a00000000c0000242000000005060000400000000606000020000000060a0000100000008404000030000000050c0000100000008402000050000000050018004000000006001800200000000600280010000000440010003000000005003000100000004400080050000000050000c040000000060000c02000000006000140100000002400008030000000050001801000000024000040500000000500000c400000000600000c20000000060000141000000014000008300000000500001810000000140000045000000005000001c000000006000001a000000006000002900000000c0000013000000005000003100000000c000000d000000084080000000000004400200000000000240001000000000014000010000000000c000002000000000600000040000000050000002,
  0xe800000000000000d800000000000000b8000000000000007800000000000000cc00000000000000ac000000000000006c000000000000009c000000000000005c000000000000003c00000000000000ca00000000000000aa000000000000006a000000000000009a000000000000005a000000000000003a000000000000008e000000000000004e000000000000002e000000000000001e00000000000000c900000000000000a90000000000000069000000000000009900000000000000590000000000000039000000000000008d000000000000004d000000000000002d000000000000001d000000000000008b000000000000004b000000000000002b000000000000001b000000000000000f00000000000000081042000000000008104020000000000810022000000000080042200000000008104002000000000810020200000000080042020000000008100022000000000800402200000000080002220000000008104001000000000810020100000000080042010000000008100021000000000800402100000000080002210000000008100003000000000800400300000000080002030000000008000023000000000810400080000000081002008000000008004200800000000810002080000000080040208000000008000220800000000810000280000000080040028000000008000202800000000800002280000000081000018000000008004001800000000800020180000000080000218000000008000003800000002891000000000000485100000000000028c0400000000000884140000000000048c002000000000088810200000000001890800000000000483080000000000018a04000000000008820c0000000000048a0002000000000888080200000000018500400000000002830040000000000186002000000000088200600000000002860002000000000884004200000000018014400000000002800c4000000000018018200000000004800860000000000280180200000000048010420000000000c8840000000000048182000000000000c902000000000008808600000000000888020020000000048880002000000000c4802000000000028180100000000000c500100000000008808030000000000884001020000000028480002000000000c0122000000000028006100000000000c014100000000004800230000000000480101020000000028012002000000000c2800200000000018180010000000000c300010000000008808003000000000882000120000000018280002000000000c00a0200000000018006010000000000c00c01000000000480020300000000048008012000000001800a002000000000c0005200000000018000310000000000c000610000000002800013000000000280004120000000018000502000000000a8440000000000048141000000000000a901000000000008804500000000000888010010000000048840001000000000a4402000000000028140080000000000a500080000000008804028000000000884000810000000028440001000000000a0112000000000028005080000000000a014080000000004800128000000000480100810000000028011001000000000a2400200000000018140008000000000a300008000000008804002800000000882000090000000018240001000000000a0090200000000018005008000000000a00c008000000004800102800000000480080090000000018009001000000000a0004a00000000018000288000000000a00060800000000280000a800000000280004090000000018000481000000000a0c0002000000000c0c0001000000000c1400004000000088080001400000000a1800004000000088040002400000000a003002000000000c003001000000000c0050004000000048002001400000000a0060004000000048001002400000000a000182000000000c000181000000000c0002804000000028000101400000000a0003004000000028000082400000000a00001a000000000c000019000000000c0000284000000018000011400000000a000030400000001800000a4000000009824000000000004812080000000000099008000000000088024800000000008880080080000000488200008000000009420200000000002812004000000000095000400000000088020240000000008840004080000000284200008000000009010a00000000002800484000000000090140400000000048000a400000000048010040800000002801080080000000092200200000000018120004000000000930000400000000880200240000000088200004800000001822000080000000090088200000000018004804000000000900c00400000000480008240000000048008004800000001800880080000000090004600000000018000244000000000900060400000000280000640000000028000404800000001800044080000000090a0002000000000c0a0000800000000c1200002000000088080000a00000000918000020000000880200022000000009002802000000000c002800800000000c0048002000000048002000a00000000900600020000000480008022000000009000142000000000c000140800000000c0002402000000028000100a00000000900030020000000280000422000000009000016000000000c000014800000000c0000242000000018000010a00000000900003020000000180000062000000009060001000000000a060000800000000a1200001000000088040000900000000914000010000000880200011000000009001801000000000a001800800000000a00480010000000480010009000000009005000100000004800080110000000090000c1000000000a0000c0800000000a000240100000002800008090000000090002801000000028000041100000000900000d000000000a00000c800000000a000024100000001800000890000000090000281000000018000005100000000a000000e000000009000001600000000a000002300000000c000001300000000c000000d0000000090000025000000088100000000000004800400000000000280002000000000018000020000000000c000002000000000a00000100000000090000008,
  0xf000000000000000d800000000000000b8000000000000007800000000000000d400000000000000b40000000000000074000000000000009c000000000000005c000000000000003c00000000000000d200000000000000b20000000000000072000000000000009a000000000000005a000000000000003a000000000000009600000000000000560000000000000036000000000000001e00000000000000d100000000000000b10000000000000071000000000000009900000000000000590000000000000039000000000000009500000000000000550000000000000035000000000000001d000000000000009300000000000000530000000000000033000000000000001b0000000000000017000000000000001020840000000000102080200000000010200420000000001000842000000000102080100000000010200410000000001000841000000000102000300000000010008030000000001000043000000000102080080000000010200408000000001000840800000000102000280000000010008028000000001000042800000000102000180000000010008018000000001000041800000000100000380000000010208004000000001020040400000000100084040000000010200024000000001000802400000000100004240000000010200014000000001000801400000000100004140000000010000034000000001020000c000000001000800c000000001000040c000000001000002c000000001000001c0000000030a1000000000000506100000000000030c0800000000000904180000000000050c004000000000090810400000000001890800000000000503040000000000018a04000000000009010c000000000009080402000000000509000200000000018500400000000003030020000000000186002000000000090100600000000009040022000000000305000200000000018014400000000003000c2000000000018018200000000005000460000000000500102200000000030014020000000001488800000000000502820000000000014a02000000000009008a000000000009080201000000000508800100000000014480400000000003028010000000000146001000000000090080500000000009040011000000000304800100000000014012400000000003000a100000000001401810000000000500025000000000050010110000000003001201000000000141800200000000018180010000000001828000200000000901000120000000014300002000000009008002200000000140060200000000018006010000000001800a0020000000050004012000000001400c0020000000050002022000000001400032000000000180003100000000018000502000000003000021200000000140006020000000030000122000000001284800000000000502410000000000012a010000000000090049000000000009080100800000000508400080000000012440400000000003024008000000000126000800000000090040480000000009040008800000000304400080000000012011400000000003000908000000000120180800000000050001480000000005001008800000000300110080000000012140020000000001814000800000000182400010000000090100009000000001230000100000000900400210000000012005020000000001800500800000000180090010000000050004009000000001200c001000000005000102100000000120002a0000000001800028800000000180004810000000030000209000000001200060100000000300000a100000000120c001000000000140c000800000000142400004000000090080008400000001228000040000000900400104000000012003010000000001400300800000000140090004000000050002008400000001200a0004000000050001010400000001200019000000000140001880000000014000480400000003000010840000000120005004000000030000090400000001400000b000000001200001300000000140000214000000018000011400000001800000a4000000012000022400000001182800000000000502208000000000011a008000000000090028800000000009080080400000000508200040000000011420400000000003022004000000000116000400000000090020440000000009040004400000000304200040000000011010c00000000003000884000000000110180400000000050000c40000000005001004400000000300108040000000011120020000000001812000400000000182200008000000090100004800000001130000080000000900200208000000011004820000000001800480400000000180088008000000050004004800000001100c000800000005000082080000000110002600000000018000244000000001800044080000000300002048000000011000600800000003000006080000000110a001000000000140a000400000000142200002000000090080004200000001128000020000000900200102000000011002810000000001400280400000000140088002000000050002004200000001100a0002000000050000810200000001100015000000000140001440000000014000440200000003000010420000000110005002000000030000050200000001400000680000000110000128000000014000020a000000018000010a000000018000006200000001100002220000000110600080000000012060004000000001222000010000000900400041000000011240000100000009002000810000000110018080000000012001804000000001200880010000000500010041000000011009000100000005000080810000000110000c800000000120000c4000000001200044010000000300000841000000011000480100000003000004810000000120000058000000011000009800000001200002090000000180000089000000018000005100000001100002110000000120000046000000011000008600000001200001030000000140000083000000014000004500000001100001050000000902000000000000050008000000000003000040000000000180000200000000014000010000000001200000800000000110000040,
  0xf000000000000000e800000000000000b8000000000000007800000000000000e400000000000000b4000000000000007400000000000000ac000000000000006c000000000000003c00000000000000e200000000000000b2000000000000007200000000000000aa000000000000006a000000000000003a00000000000000a600000000000000660000000000000036000000000000002e00000000000000e100000000000000b1000000000000007100000000000000a90000000000000069000000000000003900000000000000a500000000000000650000000000000035000000000000002d00000000000000a300000000000000630000000000000033000000000000002b000000000000002700000000000000204104000000000020410200000000002040060000000000200106000000000020410100000000002040050000000000200105000000000020400300000000002001030000000000200007000000000020410080000000002040048000000000200104800000000020400280000000002001028000000000200006800000000020400180000000002001018000000000200005800000000020000380000000002041004000000000204004400000000020010440000000002040024000000000200102400000000020000640000000002040014000000000200101400000000020000540000000002000034000000000204000c000000000200100c000000000200004c000000000200002c000000000200001c00000000030a1000000000000606080000000000030c0800000000000a021800000000000a08084000000000060a00400000000002891000000000000605040000000000028c0400000000000a011400000000000a0804200000000006090020000000000283004000000000030300200000000003050002000000000a0200220000000002860002000000000a0100420000000002800c400000000003000c2000000000030014020000000006000822000000000280180200000000060004420000000002489000000000000604820000000000024c0200000000000a009200000000000a0802100000000006088010000000000242804000000000030280100000000003048001000000000a0200110000000002460001000000000a0080410000000002400a400000000003000a100000000003001201000000000600081100000000024018010000000006000241000000000241802000000000028180100000000002848000200000000a0100102000000002450000200000000a0080202000000002400620000000000280061000000000028012002000000006000410200000000240140020000000060002202000000002800013000000000240002300000000028000412000000003000021200000000300001220000000024000422000000002285000000000000604410000000000022c0100000000000a005100000000000a0801080000000006084008000000000222404000000000030240080000000003044000800000000a0200088000000002260000800000000a004040800000000220094000000000030009080000000003001100800000000600080880000000022018008000000006000140800000000221402000000000028140080000000002844000100000000a0100081000000002250000100000000a004020100000000220052000000000028005080000000002801100100000000600040810000000022014001000000006000120100000000280000a800000000220002280000000028000409000000003000020900000000300000a1000000002200042100000000220c010000000000240c0080000000002444000040000000a0080080400000002248000040000000a0040100400000002200310000000000240030800000000024011000400000006000208040000000220120004000000060001100400000002400009800000000220001180000000024000408400000003000010840000000300000904000000022000410400000002400008300000000220001030000000024000201400000002800010140000000280000824000000022000202400000002183000000000000604208000000000021c0080000000000a003080000000000a0800840000000006082004000000000212204000000000030220040000000003042000400000000a0200044000000002160000400000000a00204040000000021008c0000000000300088400000000030010804000000006000804400000000210180040000000060000c0400000000211202000000000028120040000000002842000080000000a0100040800000002150000080000000a00202008000000021004a0000000000280048400000000028010800800000006000404080000000210140008000000060000a0080000000280000640000000021000224000000002800040480000000300002048000000030000060800000002100042080000000210a010000000000240a0040000000002442000020000000a0080040200000002148000020000000a0020100200000002100290000000000240028400000000024010800200000006000204020000000210120002000000060000900200000002400005400000000210001140000000024000404200000003000010420000000300000502000000021000410200000002400004280000000210001028000000024000200a000000028000100a000000028000042200000002100020220000000210600800000000022060040000000002242000010000000a0040040100000002144000010000000a0020080100000002100188000000000220018400000000022010800100000006000104010000000210110001000000060000880100000002200004c000000002100008c000000002200040410000000300000841000000030000048100000002100040810000000220000418000000021000081800000002200020090000000280000809000000028000041100000002100020110000000220000406000000021000080600000002200010030000000240000803000000024000040500000002100010050000000a04000000000000060010000000000003000040000000000280002000000000024000100000000002200008000000000210000400,
  0xf000000000000000e800000000000000d8000000000000007800000000000000e400000000000000d4000000000000007400000000000000cc000000000000006c000000000000005c00000000000000e200000000000000d2000000000000007200000000000000ca000000000000006a000000000000005a00000000000000c600000000000000660000000000000056000000000000004e00000000000000e100000000000000d1000000000000007100000000000000c90000000000000069000000000000005900000000000000c500000000000000650000000000000055000000000000004d00000000000000c300000000000000630000000000000053000000000000004b000000000000004700000000000000408180000000000040814000000000004080c000000000004001c0000000000040812000000000004080a000000000004001a00000000000408060000000000040016000000000004000e00000000000408110000000000040809000000000004001900000000000408050000000000040015000000000004000d00000000000408030000000000040013000000000004000b000000000004000700000000000408108000000000040808800000000004001880000000000408048000000000040014800000000004000c80000000000408028000000000040012800000000004000a800000000004000680000000000408018000000000040011800000000004000980000000000400058000000000040003800000000005061000000000000606080000000000060a0040000000000c04084000000000050c0040000000000c021040000000000485100000000000060504000000000006090020000000000c04042000000000048c0020000000000c011020000000000483080000000000050304000000000005090002000000000c02040200000000048a0002000000000c010802000000000500046000000000048008600000000005001022000000000600082200000000060004420000000004801042000000000444900000000000060482000000000006088010000000000c04021000000000044c0010000000000c009010000000000442880000000000050282000000000005088001000000000c02020100000000044a0001000000000c008801000000000500025000000000044008500000000005001011000000000600081100000000060002410000000004401041000000000441840000000000048182000000000004888000200000000c0102002000000004490000200000000c008400200000000480023000000000044004300000000004801010200000000600041020000000060002202000000004401020200000000480020300000000044004030000000004800801200000000500040120000000050002022000000004400802200000000424500000000000060441000000000006084008000000000c04010800000000042c0008000000000c005008000000000422480000000000050241000000000005084000800000000c02010080000000042a0000800000000c004800800000000500014800000000042008480000000005001008800000000600080880000000060001408000000004201040800000000421440000000000048141000000000004884000100000000c0101001000000004290000100000000c004400100000000480012800000000042004280000000004801008100000000600040810000000060001201000000004201020100000000480010280000000042004028000000004800800900000000500040090000000050001021000000004200802100000000420c200000000000440c1000000000004484000040000000c0081000400000004288000040000000c004200040000000440011800000000042002180000000004401008040000000600020804000000060001100400000004201010040000000440010180000000042002018000000004400800840000000500020084000000050001010400000004200801040000000440010030000000042002003000000004400400140000000480020014000000048001002400000004200400240000000414300000000000060420800000000006082004000000000c04008400000000041c0004000000000c003004000000000412280000000000050220800000000005082000400000000c02008040000000041a0000400000000c00280040000000050000c400000000041008440000000005001004400000000600080440000000060000c04000000004101040400000000411240000000000048120800000000004882000080000000c0100800800000004190000080000000c00240008000000048000a400000000041004240000000004801004080000000600040408000000060000a00800000004101020080000000480008240000000041004024000000004800800480000000500040048000000050000820800000004100802080000000410a200000000000440a0800000000004482000020000000c0080800200000004188000020000000c0022000200000004400094000000000410021400000000044010040200000006000204020000000600009002000000041010100200000004400081400000000410020140000000044008004200000005000200420000000500008102000000041008010200000004400080280000000410020028000000044004000a000000048002000a000000048000802200000004100400220000000410610000000000042060800000000004282000010000000c0040800100000004184000010000000c002100010000000420008c000000000410010c00000000042010040100000006000104010000000600008801000000041010080100000004200080c000000004100100c000000004200800410000000500010041000000050000808100000004100800810000000420008018000000041001001800000004200400090000000480010009000000048000801100000004100400110000000420008006000000041001000600000004200200030000000440010003000000044000800500000004100200050000000c08000000000000060010000000000005000800000000000480040000000000044002000000000004200100000000000410008000,
  0xf000000000000000e800000000000000d800000000000000b800000000000000e400000000000000d400000000000000b400000000000000cc00000000000000ac000000000000009c00000000000000e200000000000000d200000000000000b200000000000000ca00000000000000aa000000000000009a00000000000000c600000000000000a60000000000000096000000000000008e00000000000000e100000000000000d100000000000000b100000000000000c900000000000000a9000000000000009900000000000000c500000000000000a50000000000000095000000000000008d00000000000000c300000000000000a30000000000000093000000000000008b00000000000000870000000000000080e000000000000080d000000000000080b0000000000000807000000000000080c800000000000080a8000000000000806800000000000080980000000000008058000000000000803800000000000080c400000000000080a40000000000008064000000000000809400000000000080540000000000008034000000000000808c000000000000804c000000000000802c000000000000801c00000000000080c200000000000080a20000000000008062000000000000809200000000000080520000000000008032000000000000808a000000000000804a000000000000802a000000000000801a0000000000008086000000000000804600000000000080260000000000008016000000000000800e000000000000a0218000000000009041800000000000a080840000000000c040840000000000c0210400000000009081040000000000a0114000000000008841400000000000a080420000000000c040420000000000c01102000000000088810200000000009010c000000000008820c000000000009080402000000000c020402000000000c0108020000000008880802000000000901006000000000088200600000000009040022000000000a020022000000000a0100420000000008840042000000000a0092000000000008441200000000000a080210000000000c040210000000000c00901000000000084810100000000009008a000000000008420a000000000009080201000000000c020201000000000c0088010000000008480801000000000900805000000000084200500000000009040011000000000a020011000000000a0080410000000008440041000000000880860000000000084106000000000008880200200000000c010200200000000c0084002000000008480400200000000880803000000000084100300000000008840010200000000a010010200000000a0080202000000008440020200000000880800300000000084100030000000008820001200000000901000120000000090080022000000008420002200000000a0051000000000008241100000000000a080108000000000c040108000000000c0050080000000008281008000000000900490000000000082209000000000009080100800000000c020100800000000c0048008000000008280800800000000900404800000000082200480000000009040008800000000a020008800000000a0040408000000008240040800000000880450000000000082105000000000008880100100000000c010100100000000c0044001000000008280400100000000880402800000000082100280000000008840008100000000a010008100000000a0040201000000008240020100000000880400280000000082100028000000008820000900000000901000090000000090040021000000008220002100000000840430000000000082083000000000008480100040000000c008100040000000c0042000400000008280200040000000840401800000000082080180000000008440008040000000a008008040000000a0040100400000008240010040000000840400180000000082080018000000008420000840000000900800084000000090040010400000008220001040000000840400030000000082080003000000008410000140000000880800014000000088040002400000008210000240000000a0030800000000008141080000000000a080084000000000c040084000000000c0030040000000008181004000000000900288000000000081208800000000009080080400000000c020080400000000c0028004000000008180800400000000900204400000000081200440000000009040004400000000a020004400000000a0020404000000008140040400000000880248000000000081104800000000008880080080000000c010080080000000c0024000800000008180400080000000880202400000000081100240000000008840004080000000a010004080000000a0020200800000008140020080000000880200240000000081100024000000008820000480000000901000048000000090020020800000008120002080000000840228000000000081082800000000008480080020000000c008080020000000c0022000200000008180200020000000840201400000000081080140000000008440004020000000a008004020000000a00201002000000081400100200000008402001400000000810800140000000084200004200000009008000420000000900200102000000081200010200000008402000280000000810800028000000084100000a000000088080000a000000088020002200000008110000220000000820218000000000081041800000000008280080010000000c004080010000000c0021000100000008180100010000000820200c000000000810400c0000000008240004010000000a004004010000000a00200801000000081400080100000008202000c000000008104000c000000008220000410000000900400041000000090020008100000008120000810000000820200018000000081040001800000008210000090000000880400009000000088020001100000008110000110000000820200006000000081040000600000008208000030000000840400003000000084020000500000008108000050000000c080000000000000a0400000000000009020000000000000881000000000000084080000000000008204000000000000810200000
]

/-- `pack (List.replicate 287 1)`. -/
def ONES : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

/-- `pack (List.replicate 287 (2^36 - 1))`. -/
def SM : Nat := 0xfffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff0000000fffffffff

/-- `pack (List.replicate 287 (2^36))`. -/
def GG : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000

/-! ### Packed 64-bit slots -/

/-- Pack a list of numbers into consecutive 64-bit slots (first element lowest). -/
def pack : List Nat → Nat
  | [] => 0
  | x :: xs => 2 ^ 64 * pack xs + x

theorem land_slot {x y a b : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (2 ^ 64 * a + x) &&& (2 ^ 64 * b + y) = 2 ^ 64 * (a &&& b) + (x &&& y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hy,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow _ hy)]
  split_ifs <;> simp

theorem mul_pack_one (c : Nat) :
    ∀ n : Nat, c * pack (List.replicate n 1) = pack (List.replicate n c)
  | 0 => by simp [pack]
  | n + 1 => by
    simp only [List.replicate_succ, pack]
    rw [← mul_pack_one c n]; ring

/-- The value of one slot in the computation of `bad`. -/
def slotF (cm M T K : Nat) : Nat := ((K &&& cm) + M) &&& T

theorem pack_slots (cm M T : Nat) (hc : cm < 2 ^ 64) (hT : T < 2 ^ 64) :
    ∀ xs : List Nat, (∀ x ∈ xs, x < 2 ^ 64 ∧ (x &&& cm) + M < 2 ^ 64) →
      ((pack xs &&& pack (List.replicate xs.length cm)) + pack (List.replicate xs.length M))
        &&& pack (List.replicate xs.length T) = pack (xs.map (slotF cm M T))
  | [], _ => by simp [pack]
  | x :: xs, h => by
    obtain ⟨hx1, hx2⟩ := h x (by simp)
    have ih := pack_slots cm M T hc hT xs (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons, List.replicate_succ, pack, List.map_cons]
    rw [land_slot hx1 hc]
    rw [show 2 ^ 64 * (pack xs &&& pack (List.replicate xs.length cm)) + (x &&& cm) +
        (2 ^ 64 * pack (List.replicate xs.length M) + M) =
        2 ^ 64 * ((pack xs &&& pack (List.replicate xs.length cm)) +
          pack (List.replicate xs.length M)) + ((x &&& cm) + M) by ring]
    rw [land_slot hx2 hT, ih, slotF]

theorem top_bit (k r : Nat) (hr : r < 2 ^ k) : (2 ^ k + r) &&& 2 ^ k = 2 ^ k := by
  have h := Nat.two_pow_add_eq_or_of_lt hr 1
  rw [Nat.mul_one] at h
  rw [h]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hj : k = j
  · subst hj; simp
  · simp [hj]

theorem entry_gen (k K cm i : Nat) (hK : K < 2 ^ k) (hi : K.testBit i = true)
    (hc : cm.testBit i = true) : ((K &&& cm) + (2 ^ k - 1)) &&& 2 ^ k = 2 ^ k := by
  have hz : (K &&& cm) ≠ 0 := by
    intro h
    have := congrArg (fun n => n.testBit i) h
    simp [hi, hc] at this
  have hzk : K &&& cm < 2 ^ k := lt_of_le_of_lt Nat.and_le_left hK
  have hP : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hsum : (K &&& cm) + (2 ^ k - 1) = 2 ^ k + ((K &&& cm) - 1) := by
    generalize 2 ^ k = P at *
    generalize K &&& cm = z at *
    omega
  rw [hsum]
  exact top_bit k _ (by generalize 2 ^ k = P at *; generalize K &&& cm = z at *; omega)

/-- `2 ^ 36 - 1`. -/
def M36 : Nat := 2 ^ 36 - 1
/-- `2 ^ 36`. -/
def T36 : Nat := 2 ^ 36
def cmpl (m : Nat) : Nat := M36 ^^^ (m &&& M36)

theorem cmpl_bit {m i : Nat} (hi : i < 36) (hm : m.testBit i = false) :
    (cmpl m).testBit i = true := by
  rw [cmpl, M36, Nat.testBit_xor, Nat.testBit_land, Nat.testBit_two_pow_sub_one, hm]
  simp [hi]

theorem cmpl_lt (m : Nat) : cmpl m < 2 ^ 64 := by
  have : cmpl m < 2 ^ 36 := by
    rw [cmpl, M36]
    exact Nat.xor_lt_two_pow (by omega) (Nat.and_lt_two_pow _ (by omega))
  omega

theorem slot_bounds (x cm : Nat) (hx : x < 2 ^ 36) : x < 2 ^ 64 ∧ (x &&& cm) + M36 < 2 ^ 64 := by
  have := Nat.and_le_left (n := x) (m := cm)
  rw [M36]
  constructor <;> omega

theorem entry_eq {K m i : Nat} (hK : K < 2 ^ 36) (hi : K.testBit i = true)
    (hm : m.testBit i = false) : slotF (cmpl m) M36 T36 K = T36 := by
  have hi36 : i < 36 := by
    by_contra h
    have : K.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hK (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [this] at hi; exact Bool.false_ne_true hi
  rw [slotF, M36, T36]
  exact entry_gen 36 K (cmpl m) i hK hi (cmpl_bit hi36 hm)


/-- The packed masks through edge `e`. -/
def big (e : Nat) : Nat := bigL.getD e 0

/-- The forbidden masks through edge `e`. -/
def forbM (e : Nat) : List Nat := (forbS.getD e []).map Shape.mask

/-- `bad e m = true` iff some forbidden mask through edge `e < 36` is contained in `m`.
All 287 masks are tested at once using slot arithmetic. -/
def bad (e m : Nat) : Bool :=
  Nat.blt e 36 && !(Nat.beq ((((big e) &&& (cmpl m * ONES)) + SM) &&& GG) GG)

theorem ONES_eq : ONES = pack (List.replicate 287 1) := by decide +kernel
theorem SM_eq : SM = pack (List.replicate 287 M36) := by decide +kernel
theorem GG_eq : GG = pack (List.replicate 287 T36) := by decide +kernel

theorem big_facts_bool : (List.range 36).all (fun e => Nat.beq (big e) (pack (forbM e)) &&
    Nat.beq (forbM e).length 287 && (forbM e).all (fun K => Nat.blt K (2 ^ 36))) = true := by
  decide +kernel

theorem big_facts (e : Nat) (he : e < 36) :
    big e = pack (forbM e) ∧ (forbM e).length = 287 ∧ ∀ K ∈ forbM e, K < 2 ^ 36 := by
  have := List.all_eq_true.1 big_facts_bool e (List.mem_range.2 he)
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem bad_sound {e m : Nat} (h : bad e m = true) :
    ∃ K ∈ forbM e, ∀ i, K.testBit i = true → m.testBit i = true := by
  simp only [bad, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  obtain ⟨he, hne⟩ := h
  by_contra H
  push Not at H
  obtain ⟨hb, hl, hlt⟩ := big_facts e he
  have hT : T36 < 2 ^ 64 := by rw [T36]; norm_num
  have key : ((big e &&& (cmpl m * ONES)) + SM) &&& GG = GG := by
    rw [hb, ONES_eq, mul_pack_one, SM_eq, GG_eq, ← hl,
      pack_slots (cmpl m) M36 T36 (cmpl_lt m) hT (forbM e)
        (fun x hx => slot_bounds x (cmpl m) (hlt x hx))]
    apply congrArg pack
    apply List.eq_replicate_iff.2
    refine ⟨List.length_map _, ?_⟩
    intro x hx
    obtain ⟨K, hK, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, hmi⟩ := H K hK
    exact entry_eq (hlt K hK) hi (by simpa using hmi)
  rw [key, Nat.beq_refl] at hne
  exact Bool.noConfusion hne


/-! ### The certificate checker -/

/-- A case-split certificate: `N e t0 t1 t2` branches on the colour of edge `e`;
`S` additionally tests the symmetry-breaking order conditions; `L` is a closed leaf. -/
inductive Cert where
  | L : Cert
  | N : Nat → Cert → Cert → Cert → Cert
  | S : Nat → Cert → Cert → Cert → Cert

/-- Colour of edge `e` in the partial colouring `(m0, m1, m2)` (`3` = uncoloured). -/
def colOf (m0 m1 m2 e : Nat) : Nat :=
  if m0.testBit e then 0 else if m1.testBit e then 1 else if m2.testBit e then 2 else 3

/-- Pairs `(a, b)`: the colours of `0a` and `0b` must satisfy `c(0a) ≤ c(0b)`. -/
def upairs : List (Fin 9 × Fin 9) := [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8)]

/-- Pairs `(a, b)`: `3 c(0a) + c(1a) ≤ 3 c(0b) + c(1b)`. -/
def quads : List (Fin 9 × Fin 9) := [(2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8)]

/-- Violation of the symmetry-breaking order conditions by a partial colouring. -/
def sortViol (m0 m1 m2 : Nat) : Bool :=
  upairs.any (fun p => Nat.blt (colOf m0 m1 m2 (eix 0 p.2)) (colOf m0 m1 m2 (eix 0 p.1)) &&
      Nat.blt (colOf m0 m1 m2 (eix 0 p.1)) 3) ||
  quads.any (fun p => Nat.blt (colOf m0 m1 m2 (eix 0 p.1)) 3 &&
      Nat.blt (colOf m0 m1 m2 (eix 1 p.1)) 3 && Nat.blt (colOf m0 m1 m2 (eix 0 p.2)) 3 &&
      Nat.blt (colOf m0 m1 m2 (eix 1 p.2)) 3 &&
      Nat.blt (3 * colOf m0 m1 m2 (eix 0 p.2) + colOf m0 m1 m2 (eix 1 p.2))
        (3 * colOf m0 m1 m2 (eix 0 p.1) + colOf m0 m1 m2 (eix 1 p.1)))

/-- The certificate checker. `check t m0 m1 m2 = true` means: every extension of the partial
colouring with colour classes `m0, m1, m2` (bit masks over edge indices) contains a forbidden
configuration or violates the order conditions. -/
noncomputable def check (t : Cert) : Nat → Nat → Nat → Bool :=
  Cert.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ _ _ => false)
    (fun e _ _ _ r0 r1 r2 m0 m1 m2 =>
      (bad e (m0 ||| 2 ^ e) || r0 (m0 ||| 2 ^ e) m1 m2) &&
      (bad e (m1 ||| 2 ^ e) || r1 m0 (m1 ||| 2 ^ e) m2) &&
      (bad e (m2 ||| 2 ^ e) || r2 m0 m1 (m2 ||| 2 ^ e)))
    (fun e _ _ _ r0 r1 r2 m0 m1 m2 =>
      (bad e (m0 ||| 2 ^ e) || sortViol (m0 ||| 2 ^ e) m1 m2 || r0 (m0 ||| 2 ^ e) m1 m2) &&
      (bad e (m1 ||| 2 ^ e) || sortViol m0 (m1 ||| 2 ^ e) m2 || r1 m0 (m1 ||| 2 ^ e) m2) &&
      (bad e (m2 ||| 2 ^ e) || sortViol m0 m1 (m2 ||| 2 ^ e) || r2 m0 m1 (m2 ||| 2 ^ e)))
    t

open Cert in
/-- The certificate (generated by an external search, checked by the kernel). -/
def cert : Cert :=
(S 0 (S 1 (S 3 (S 6 L (S 10 L (S 15 L (S 21 L L (S 28 L L (S 2 L (S 4 L (S 7 (S 11 (S 16 L (S 22 L
  L (S 29 L L (N 5 L L (N 14 L L (N 8 (N 9 (N 19 L L (N 20 (N 17 L L (N 18 L L L)) L L)) L (N 13
  (N 12 (N 17 L L (N 20 L L L)) L (N 17 (N 19 L L (N 20 L L L)) L (N 18 (N 20 L L L) L L))) L L))
  L (N 9 (N 12 (N 13 (N 18 L L (N 20 L L L)) L (N 17 (N 19 L L (N 20 L L L)) L (N 18 (N 19 L L L)
  L L))) L L) L L)))))) (S 22 L (S 29 L L (N 5 L L (N 14 L L (N 19 (N 17 L (N 18 L (N 27 (N 34 (N
  20 L L (N 32 L (N 35 L (N 25 L L (N 26 L L L)) L) L)) L L) L L) (N 20 (N 23 (N 24 (N 25 L (N 26
  L (N 27 (N 35 L L L) L L) (N 27 (N 34 L (N 35 L L L) L) (N 34 (N 32 L (N 30 (N 35 L L L) L L) L)
  L L) L)) (N 26 L (N 27 (N 34 L (N 35 L L L) L) (N 34 (N 33 L (N 30 (N 35 L L L) L L) L) L L) L)
  L)) L (N 9 (N 8 L (N 30 (N 12 L L (N 25 L (N 32 L L (N 26 L (N 35 L L L) L)) L)) L L) (N 26 L (N
  12 (N 13 L (N 30 L (N 32 L L (N 33 L L L)) L) L) (N 13 (N 30 (N 31 L (N 33 L L (N 25 L (N 32 L L
  L) L)) L) L L) L L) L) L)) (N 13 (N 12 L (N 30 (N 8 L L (N 26 L (N 33 L L (N 25 L (N 32 L L L)
  L)) L)) L L) (N 25 L (N 8 (N 30 L (N 32 L L (N 33 L L L)) L) L L) L)) (N 31 (N 35 L (N 32 L L (N
  33 L L L)) L) L L) L) L)) L (N 24 (N 25 L (N 26 L (N 27 (N 34 L (N 30 (N 35 L L L) L L) L) L L)
  (N 9 (N 31 L (N 32 L L L) L) (N 32 (N 8 L L (N 30 L (N 34 L L L) L)) L L) L)) (N 26 L (N 8 (N 9
  L (N 13 (N 31 L (N 33 L L L) L) (N 31 (N 33 L L L) L L) L) (N 32 L (N 30 (N 35 L L L) L L) L))
  (N 30 (N 33 L (N 35 L L L) L) L L) L) L)) L L)) L (N 8 (N 32 L (N 30 (N 23 L L (N 24 (N 26 L (N
  35 L L L) L) L L)) L L) L) (N 30 (N 32 L (N 35 (N 23 L L (N 24 L L L)) L L) L) L L) L))) (N 18 L
  (N 20 (N 23 (N 24 (N 25 L (N 26 L (N 27 (N 35 L L L) L L) (N 27 (N 34 L (N 35 L L L) L) (N 34 (N
  32 L (N 31 (N 35 L L L) L L) L) L L) L)) (N 26 L (N 27 (N 34 L (N 35 L L L) L) (N 34 (N 33 L (N
  31 (N 35 L L L) L L) L) L L) L) L)) L (N 25 L (N 26 L (N 27 (N 34 L (N 30 (N 35 L L L) L L) L) L
  L) (N 8 (N 30 L (N 32 L L L) L) (N 32 (N 9 L L (N 30 L (N 34 L L L) L)) L L) L)) (N 26 L (N 9 (N
  8 L (N 12 (N 30 L (N 33 L L L) L) (N 30 (N 33 L L L) L L) L) (N 32 L (N 31 (N 35 L L L) L L) L))
  (N 31 (N 33 L (N 35 L L L) L) L L) L) L))) L (N 24 (N 8 (N 9 L (N 31 (N 13 L L (N 25 L (N 32 L L
  (N 26 L (N 35 L L L) L)) L)) L L) (N 26 L (N 12 (N 13 L (N 30 L (N 31 (N 33 L L (N 25 L (N 32 L
  L L) L)) L L) L) L) (N 13 (N 31 L (N 32 L L (N 33 L L L)) L) L L) L) L)) (N 12 (N 13 L (N 31 (N
  9 L L (N 26 L (N 33 L L (N 25 L (N 32 L L L) L)) L)) L L) (N 25 L (N 9 (N 31 L (N 32 L L (N 33 L
  L L)) L) L L) L)) (N 30 (N 35 L (N 32 L L (N 33 L L L)) L) L L) L) L) L L)) L (N 9 (N 32 L (N 31
  (N 24 L L (N 23 (N 26 L (N 35 L L L) L) L L)) L L) L) (N 31 (N 32 L (N 35 (N 23 L L (N 24 L L
  L)) L L) L) L L) L)) L)) L (N 20 (N 17 L (N 18 L (N 27 (N 34 (N 33 L (N 35 L (N 25 L L (N 26 L L
  L)) L) L) L L) L L) (N 9 (N 12 (N 33 L (N 30 (N 23 L L (N 24 (N 25 L (N 35 L L L) L) L L)) L L)
  L) (N 30 (N 33 L (N 35 (N 23 L L (N 24 L L L)) L L) L) L L) L) (N 12 (N 33 L (N 30 (N 23 L L (N
  24 (N 25 L (N 35 L L L) L) L L)) L L) L) (N 30 (N 33 L (N 35 (N 23 L L (N 24 L L L)) L L) L) L
  L) L) L)) (N 18 L (N 8 (N 13 (N 33 L (N 31 (N 24 L L (N 23 (N 25 L (N 35 L L L) L) L L)) L L) L)
  (N 31 (N 33 L (N 35 (N 23 L L (N 24 L L L)) L L) L) L L) L) (N 13 (N 33 L (N 31 (N 24 L L (N 23
  (N 25 L (N 35 L L L) L) L L)) L L) L) (N 31 (N 33 L (N 35 (N 23 L L (N 24 L L L)) L L) L) L L)
  L) L) L)) L L))))) (S 29 L L (N 5 L L (N 14 L L (N 19 (N 17 L (N 18 L (N 27 (N 34 (N 20 L L (N
  25 L (N 32 L (N 35 L L L) L) L)) L L) L L) (N 20 (N 23 (N 25 L (N 26 L (N 27 (N 34 L (N 30 (N 35
  L L L) L L) L) (N 34 (N 35 (N 30 L (N 8 L L (N 12 L L L)) L) L L) L L) L) (N 13 (N 12 L (N 30 (N
  8 L L (N 32 L (N 35 L L L) L)) L L) (N 33 L (N 30 (N 35 L L L) L L) L)) (N 24 (N 27 (N 34 L (N
  35 L L L) L) (N 34 (N 32 L (N 30 (N 35 L L L) L L) L) L L) L) L L) L)) (N 26 L (N 9 (N 8 L (N 30
  (N 12 L L (N 33 L (N 35 L L L) L)) L L) (N 32 L (N 30 (N 35 L L L) L L) L)) (N 24 (N 27 (N 34 L
  (N 35 L L L) L) (N 34 (N 33 L (N 30 (N 35 L L L) L L) L) L L) L) L L) L) L)) (N 27 (N 25 L L (N
  26 L L L)) L L) L) L (N 8 (N 25 L (N 23 (N 30 L (N 32 L L L) L) L L) L) (N 23 (N 25 L (N 30 (N
  32 L L L) L L) L) L L) L))) (N 18 L (N 20 (N 24 (N 25 L (N 26 L (N 27 (N 34 L (N 31 (N 35 L L L)
  L L) L) (N 34 (N 35 (N 31 L (N 9 L L (N 13 L L L)) L) L L) L L) L) (N 12 (N 13 L (N 31 (N 9 L L
  (N 32 L (N 35 L L L) L)) L L) (N 33 L (N 31 (N 35 L L L) L L) L)) (N 23 (N 27 (N 34 L (N 35 L L
  L) L) (N 34 (N 32 L (N 31 (N 35 L L L) L L) L) L L) L) L L) L)) (N 26 L (N 8 (N 9 L (N 31 (N 13
  L L (N 33 L (N 35 L L L) L)) L L) (N 32 L (N 31 (N 35 L L L) L L) L)) (N 23 (N 27 (N 34 L (N 35
  L L L) L) (N 34 (N 33 L (N 31 (N 35 L L L) L L) L) L L) L) L L) L) L)) (N 27 (N 25 L L (N 26 L L
  L)) L L) L) L (N 9 (N 25 L (N 24 (N 31 L (N 32 L L L) L) L L) L) (N 24 (N 25 L (N 31 (N 32 L L
  L) L L) L) L L) L)) L)) L (N 20 (N 17 L (N 18 L (N 27 (N 26 L (N 34 (N 33 L (N 35 L L L) L) L L)
  L) L L) (N 9 (N 12 (N 26 L (N 23 (N 30 L (N 33 L L L) L) L L) L) (N 23 (N 26 L (N 30 (N 33 L L
  L) L L) L) L L) L) (N 12 (N 26 L (N 23 (N 30 L (N 33 L L L) L) L L) L) (N 23 (N 26 L (N 30 (N 33
  L L L) L L) L) L L) L) L)) (N 18 L (N 8 (N 13 (N 26 L (N 24 (N 31 L (N 33 L L L) L) L L) L) (N
  24 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L) (N 13 (N 26 L (N 24 (N 31 L (N 33 L L L) L) L L)
  L) (N 24 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L) L) L)) L L))))))) (S 16 L L (S 22 (S 29 L L
  (N 5 L L (N 8 (N 9 (N 14 L L (N 19 L L (N 20 (N 12 (N 17 L L (N 18 L L L)) L (N 13 (N 18 L L L)
  L L)) L L))) L (N 12 (N 14 L L (N 13 (N 17 L L (N 18 (N 20 L L L) L L)) L L)) L (N 13 (N 14 L L
  (N 17 (N 19 L L (N 20 L L L)) L (N 18 (N 20 L L L) L L))) L L))) L (N 9 (N 12 (N 14 L L (N 13 (N
  18 L L (N 17 (N 20 L L L) L L)) L (N 17 (N 19 L L (N 20 L L L)) L (N 18 (N 19 L L L) L L)))) L
  (N 13 (N 14 L L L) L L)) L L)))) L (S 29 L L (N 5 L L (N 8 (N 9 (N 14 L L (N 19 L L (N 20 (N 12
  (N 17 L L (N 18 L L L)) L (N 13 (N 18 L L L) L L)) L L))) L (N 12 (N 14 L L (N 13 (N 17 L L (N
  18 (N 20 L L L) L L)) L L)) L (N 13 (N 14 L L (N 17 (N 19 L L (N 20 L L L)) L (N 18 (N 20 L L L)
  L L))) L L))) L (N 9 (N 12 (N 14 L L (N 13 (N 18 L L (N 17 (N 20 L L L) L L)) L (N 17 (N 19 L L
  (N 20 L L L)) L (N 18 (N 19 L L L) L L)))) L (N 13 (N 14 L L L) L L)) L L)))))) (S 16 L L (S 22
  (S 29 L (N 5 L L (N 20 (N 14 (N 19 L L (N 12 L (N 13 L (N 25 L (N 23 (N 24 (N 26 L L (N 35 L (N
  8 (N 9 L L (N 30 L L (N 31 (N 18 L (N 27 L L (N 32 L L L)) L) L L))) L (N 9 (N 31 L L (N 30 (N
  17 L (N 27 L L (N 32 L L L)) L) L L)) L L)) L)) L (N 30 (N 35 L (N 8 L L (N 9 (N 17 L (N 27 L L
  L) L) L L)) L) L L)) L (N 24 (N 31 (N 35 L (N 9 L L (N 8 (N 18 L (N 27 L L L) L) L L)) L) L L) L
  L)) (N 26 (N 27 L (N 33 L L (N 23 (N 24 L L (N 30 (N 17 L (N 34 L L L) L) L L)) L (N 24 (N 31 (N
  18 L (N 34 L L L) L) L L) L L))) L) L L)) (N 9 (N 8 L (N 17 (N 23 (N 30 L L (N 31 (N 24 L (N 25
  L L (N 26 (N 27 L (N 34 L L L) L) L L)) L) L L)) L (N 31 (N 24 L (N 25 L L (N 18 L (N 27 L L L)
  L)) L) L L)) L L) (N 17 (N 25 L (N 23 (N 30 L L (N 31 (N 24 L (N 32 L L L) L) L L)) L (N 30 (N
  31 (N 24 L (N 32 L L L) L) L L) L L)) (N 27 L (N 23 (N 30 L L L) L L) L)) (N 23 (N 25 L (N 27 L
  (N 35 (N 24 L L (N 30 L L L)) L L) (N 32 L (N 24 (N 35 L L L) L L) L)) (N 27 L (N 30 (N 35 L L
  L) L L) L)) L (N 25 L (N 30 (N 31 (N 24 L (N 32 L L L) L) L L) L L) L)) L)) (N 17 (N 25 L (N 35
  (N 30 L L (N 31 L L L)) L L) (N 27 L (N 23 (N 30 L L (N 8 L (N 24 (N 26 L (N 35 L L L) L) L L)
  L)) L (N 24 (N 31 (N 18 L (N 34 L L L) L) L L) L L)) L)) (N 8 (N 23 (N 30 L L (N 31 (N 35 L (N
  25 L L (N 27 L L L)) L) L L)) L (N 31 (N 35 L (N 25 L L (N 27 L L L)) L) L L)) L (N 23 (N 25 L
  (N 35 (N 24 L L (N 30 L L L)) L L) (N 27 L (N 30 (N 35 L L L) L L) L)) L (N 25 L (N 24 (N 30 (N
  32 L L L) L L) L L) L))) L) L)) (N 13 L (N 8 (N 9 L (N 18 (N 24 (N 31 L L (N 30 (N 23 L (N 25 L
  L (N 26 (N 27 L (N 34 L L L) L) L L)) L) L L)) L (N 30 (N 23 L (N 25 L L (N 17 L (N 27 L L L)
  L)) L) L L)) L L) (N 18 (N 25 L (N 24 (N 31 L L (N 30 (N 23 L (N 32 L L L) L) L L)) L (N 30 (N
  23 L (N 32 L L L) L) L L)) (N 27 L (N 24 (N 31 L L L) L L) L)) (N 24 (N 25 L (N 27 L (N 35 (N 23
  L L (N 30 L L L)) L L) (N 32 L (N 23 (N 35 L L L) L L) L)) (N 27 L (N 31 (N 35 L L L) L L) L)) L
  (N 25 L (N 30 (N 23 L (N 32 L L L) L) L L) L)) L)) (N 18 (N 25 L (N 35 (N 30 L L (N 31 L L L)) L
  L) (N 27 L (N 23 (N 24 (N 26 L (N 35 L L L) L) L (N 30 (N 17 L (N 34 L L L) L) L L)) L (N 24 (N
  31 L L L) L L)) L)) (N 9 (N 24 (N 31 L L (N 30 (N 35 L (N 25 L L (N 27 L L L)) L) L L)) L (N 30
  (N 35 L (N 25 L L (N 27 L L L)) L) L L)) L (N 24 (N 25 L (N 35 (N 23 L L (N 30 L L L)) L L) (N
  27 L (N 31 (N 35 L L L) L L) L)) L (N 25 L (N 23 (N 30 (N 32 L L L) L L) L L) L))) L) L) L))) L
  (N 19 (N 17 L (N 18 L (N 25 L (N 23 (N 24 (N 27 L L (N 35 L (N 8 (N 9 L L (N 30 L L (N 31 (N 13
  L (N 26 L L (N 32 L L L)) L) L L))) L (N 9 (N 31 L L (N 30 (N 12 L (N 26 L L (N 32 L L L)) L) L
  L)) L L)) L)) L (N 30 (N 35 L (N 8 L L (N 9 (N 12 L (N 26 L L L) L) L L)) L) L L)) L (N 24 (N 31
  (N 35 L (N 9 L L (N 8 (N 13 L (N 26 L L L) L) L L)) L) L L) L L)) (N 26 L (N 27 (N 34 L L (N 23
  (N 24 L L (N 30 (N 12 L (N 33 L L L) L) L L)) L (N 24 (N 31 (N 13 L (N 33 L L L) L) L L) L L)))
  L L) L)) (N 9 (N 8 L (N 12 (N 23 (N 30 L L (N 31 (N 24 L (N 25 L L (N 26 L (N 33 L L L) L)) L) L
  L)) L (N 31 (N 24 L (N 25 L L (N 13 L (N 26 L L L) L)) L) L L)) L L) (N 12 (N 25 L (N 23 (N 30 L
  L (N 31 (N 24 L (N 32 L L L) L) L L)) L (N 30 (N 31 (N 24 L (N 32 L L L) L) L L) L L)) (N 26 L
  (N 23 (N 30 L L L) L L) L)) (N 23 (N 25 L (N 26 L (N 35 (N 24 L L (N 30 L L L)) L L) (N 32 L (N
  24 (N 35 L L L) L L) L)) (N 26 L (N 30 (N 35 L L L) L L) L)) L (N 25 L (N 30 (N 31 (N 24 L (N 32
  L L L) L) L L) L L) L)) L)) (N 12 (N 25 L (N 35 (N 30 L L (N 31 L L L)) L L) (N 26 L (N 23 (N 30
  L L (N 8 L (N 24 (N 27 L (N 35 L L L) L) L L) L)) L (N 24 (N 31 (N 13 L (N 33 L L L) L) L L) L
  L)) L)) (N 8 (N 23 (N 30 L L (N 31 (N 35 L (N 25 L L (N 26 L L L)) L) L L)) L (N 31 (N 35 L (N
  25 L L (N 26 L L L)) L) L L)) L (N 23 (N 25 L (N 35 (N 24 L L (N 30 L L L)) L L) (N 26 L (N 30
  (N 35 L L L) L L) L)) L (N 25 L (N 24 (N 30 (N 32 L L L) L L) L L) L))) L) L)) (N 18 L (N 8 (N 9
  L (N 13 (N 24 (N 31 L L (N 30 (N 23 L (N 25 L L (N 26 L (N 33 L L L) L)) L) L L)) L (N 30 (N 23
  L (N 25 L L (N 12 L (N 26 L L L) L)) L) L L)) L L) (N 13 (N 25 L (N 24 (N 31 L L (N 30 (N 23 L
  (N 32 L L L) L) L L)) L (N 30 (N 23 L (N 32 L L L) L) L L)) (N 26 L (N 24 (N 31 L L L) L L) L))
  (N 24 (N 25 L (N 26 L (N 35 (N 23 L L (N 30 L L L)) L L) (N 32 L (N 23 (N 35 L L L) L L) L)) (N
  26 L (N 31 (N 35 L L L) L L) L)) L (N 25 L (N 30 (N 23 L (N 32 L L L) L) L L) L)) L)) (N 13 (N
  25 L (N 35 (N 30 L L (N 31 L L L)) L L) (N 26 L (N 23 (N 24 (N 27 L (N 35 L L L) L) L (N 30 (N
  12 L (N 33 L L L) L) L L)) L (N 24 (N 31 L L L) L L)) L)) (N 9 (N 24 (N 31 L L (N 30 (N 35 L (N
  25 L L (N 26 L L L)) L) L L)) L (N 30 (N 35 L (N 25 L L (N 26 L L L)) L) L L)) L (N 24 (N 25 L
  (N 35 (N 23 L L (N 30 L L L)) L L) (N 26 L (N 31 (N 35 L L L) L L) L)) L (N 25 L (N 23 (N 30 (N
  32 L L L) L L) L L) L))) L) L) L)) L (N 25 L (N 30 (N 35 L (N 32 L L (N 8 (N 9 (N 33 (N 34 L L
  L) L L) L L) L L)) L) L (N 31 (N 35 L (N 32 L L (N 8 (N 9 (N 13 L (N 24 L L L) L) L L) L L)) L)
  L L)) (N 8 (N 9 (N 32 L (N 26 (N 27 L (N 35 (N 30 L L (N 31 L L L)) L L) L) (N 35 (N 30 L L (N
  31 L L L)) L L) L) L) (N 26 (N 27 L (N 12 L (N 13 L (N 33 (N 32 L (N 35 L L L) L) L L) (N 23 (N
  17 L (N 35 L L L) L) L L)) (N 13 L (N 18 (N 24 (N 31 L L (N 23 L (N 30 (N 34 L L L) L L) L)) L
  L) L L) L)) L) (N 24 (N 27 (N 35 L (N 32 (N 34 L L L) L L) L) (N 30 (N 32 L (N 35 L L L) L) L (N
  31 (N 32 L (N 35 L L L) L) L L)) L) L (N 30 (N 12 L (N 23 L L L) L) L L)) L) L) (N 9 (N 26 (N 27
  L (N 12 L (N 13 L (N 33 (N 32 L (N 35 L L L) L) L L) (N 17 (N 23 (N 30 L L (N 24 L (N 31 (N 34 L
  L L) L L) L)) L L) L L)) (N 13 L (N 24 (N 18 L (N 35 L L L) L) L L) L)) L) (N 23 (N 27 (N 35 L
  (N 32 (N 34 L L L) L L) L) (N 30 (N 32 L (N 35 L L L) L) L (N 31 (N 24 L (N 35 L L L) L) L L))
  L) L (N 31 (N 13 L (N 24 L L L) L) L L)) L) (N 32 (N 30 L L (N 31 L L L)) L L) L) L)))) L L)) (N
  5 L L (N 20 (N 14 (N 19 L L (N 27 L (N 12 L (N 13 L (N 26 (N 33 L L L) L L) (N 9 (N 8 L (N 17 (N
  30 (N 23 L L (N 34 L (N 35 L L L) L)) L L) L L) (N 17 (N 23 (N 30 L (N 32 L L (N 25 L (N 33 (N
  34 L L L) L L) L)) L) L (N 25 L (N 32 L (N 30 (N 35 L L L) L L) L) L)) (N 30 (N 34 (N 18 L L (N
  24 (N 31 L (N 33 L L L) L) L L)) L L) L L) L)) (N 17 (N 23 (N 30 L (N 8 L L (N 33 (N 34 L L L) L
  L)) L) L (N 24 (N 25 L (N 8 (N 30 L (N 32 L L (N 33 (N 34 L L L) L L)) L) L (N 32 (N 30 L (N 33
  L L L) L) L L)) (N 8 (N 30 L (N 32 L L (N 33 (N 34 L L L) L L)) L) (N 30 (N 32 L L (N 34 L (N 35
  L L L) L)) L L) L)) L L)) (N 30 (N 34 (N 8 L L (N 18 L L (N 24 (N 33 L (N 35 L L L) L) L L))) L
  L) L L) L) L)) (N 13 L (N 8 (N 9 L (N 18 (N 31 (N 24 L L (N 34 L (N 35 L L L) L)) L L) L L) (N
  18 (N 24 (N 31 L (N 32 L L (N 25 L (N 33 (N 34 L L L) L L) L)) L) L (N 25 L (N 32 L (N 31 (N 35
  L L L) L L) L) L)) (N 31 (N 34 (N 17 L L (N 23 (N 30 L (N 33 L L L) L) L L)) L L) L L) L)) (N 18
  (N 23 (N 24 (N 26 L (N 31 L (N 9 L L (N 33 (N 34 L L L) L L)) L) L) L (N 25 L (N 9 (N 31 L (N 32
  L L (N 33 (N 34 L L L) L L)) L) L (N 32 (N 30 L (N 33 L L L) L) L L)) (N 9 (N 31 L (N 32 L L (N
  33 (N 34 L L L) L L)) L) (N 31 (N 32 L L (N 34 L (N 35 L L L) L)) L L) L))) L (N 24 (N 31 L (N 9
  L L (N 33 (N 34 L L L) L L)) L) L L)) (N 31 (N 34 (N 9 L L (N 17 L L (N 23 (N 33 L (N 35 L L L)
  L) L L))) L L) L L) L) L) L)) L)) L (N 19 (N 26 L (N 17 L (N 18 L (N 27 (N 34 L L L) L L) (N 9
  (N 8 L (N 12 (N 30 (N 23 L L (N 33 L (N 35 L L L) L)) L L) L L) (N 12 (N 23 (N 30 L (N 32 L L (N
  25 L (N 33 (N 34 L L L) L L) L)) L) L (N 25 L (N 32 L (N 30 (N 35 L L L) L L) L) L)) (N 30 (N 33
  (N 13 L L (N 24 (N 31 L (N 34 L L L) L) L L)) L L) L L) L)) (N 12 (N 23 (N 30 L (N 8 L L (N 33
  (N 34 L L L) L L)) L) L (N 24 (N 25 L (N 8 (N 30 L (N 32 L L (N 33 (N 34 L L L) L L)) L) L (N 32
  (N 30 L (N 34 L L L) L) L L)) (N 8 (N 30 L (N 32 L L (N 33 (N 34 L L L) L L)) L) (N 30 (N 32 L L
  (N 33 L (N 35 L L L) L)) L L) L)) L L)) (N 30 (N 33 (N 8 L L (N 13 L L (N 24 (N 34 L (N 35 L L
  L) L) L L))) L L) L L) L) L)) (N 18 L (N 8 (N 9 L (N 13 (N 31 (N 24 L L (N 33 L (N 35 L L L) L))
  L L) L L) (N 13 (N 24 (N 31 L (N 32 L L (N 25 L (N 33 (N 34 L L L) L L) L)) L) L (N 25 L (N 32 L
  (N 31 (N 35 L L L) L L) L) L)) (N 31 (N 33 (N 12 L L (N 23 (N 30 L (N 34 L L L) L) L L)) L L) L
  L) L)) (N 13 (N 23 (N 24 (N 27 L (N 31 L (N 9 L L (N 33 (N 34 L L L) L L)) L) L) L (N 25 L (N 9
  (N 31 L (N 32 L L (N 33 (N 34 L L L) L L)) L) L (N 32 (N 30 L (N 34 L L L) L) L L)) (N 9 (N 31 L
  (N 32 L L (N 33 (N 34 L L L) L L)) L) (N 31 (N 32 L L (N 33 L (N 35 L L L) L)) L L) L))) L (N 24
  (N 31 L (N 9 L L (N 33 (N 34 L L L) L L)) L) L L)) (N 31 (N 33 (N 9 L L (N 12 L L (N 23 (N 34 L
  (N 35 L L L) L) L L))) L L) L L) L) L) L)) L) L (N 25 L (N 26 (N 27 L (N 12 L (N 13 L (N 33 (N
  34 L (N 35 L L L) L) L L) (N 9 (N 17 (N 23 (N 30 L (N 8 L L (N 32 (N 33 L L L) L L)) L) L (N 24
  (N 31 L (N 33 (N 34 L (N 35 L L L) L) L L) L) (N 35 (N 30 L (N 33 L L L) L) L L) L)) (N 30 (N 34
  (N 18 L L (N 23 L L (N 24 (N 31 L (N 33 L L L) L) L L))) L L) L L) L) (N 8 (N 17 (N 23 L L (N 24
  (N 30 L (N 33 (N 34 L L L) L L) L) L L)) (N 30 (N 23 L L (N 24 (N 32 L L (N 34 (N 18 L L (N 31 L
  (N 33 L L L) L)) L L)) L L)) L L) L) L (N 32 (N 30 L (N 33 L L L) L) L L)) L)) (N 13 L (N 8 (N
  18 (N 24 (N 31 L (N 9 L L (N 32 (N 33 L L L) L L)) L) L (N 23 (N 30 L (N 33 (N 34 L (N 35 L L L)
  L) L L) L) (N 35 (N 30 L (N 33 L L L) L) L L) L)) (N 31 (N 34 (N 17 L L (N 23 (N 24 L L (N 30 L
  (N 33 L L L) L)) L L)) L L) L L) L) (N 9 (N 18 (N 24 L L (N 23 (N 31 L (N 33 (N 34 L L L) L L)
  L) L L)) (N 31 (N 24 L L (N 23 (N 32 L L (N 34 (N 17 L L (N 30 L (N 33 L L L) L)) L L)) L L)) L
  L) L) L (N 32 (N 31 L (N 33 L L L) L) L L)) L) L)) L) (N 27 (N 17 L (N 18 L (N 34 (N 33 L (N 35
  L L L) L) L L) (N 9 (N 12 (N 23 (N 30 L (N 8 L L (N 32 (N 34 L L L) L L)) L) L (N 24 (N 31 L (N
  34 (N 33 L (N 35 L L L) L) L L) L) (N 35 (N 30 L (N 34 L L L) L) L L) L)) (N 30 (N 33 (N 13 L L
  (N 23 L L (N 24 (N 31 L (N 34 L L L) L) L L))) L L) L L) L) (N 8 (N 12 (N 23 L L (N 24 (N 30 L
  (N 33 (N 34 L L L) L L) L) L L)) (N 30 (N 23 L L (N 24 (N 32 L L (N 33 (N 13 L L (N 31 L (N 34 L
  L L) L)) L L)) L L)) L L) L) L (N 32 (N 30 L (N 34 L L L) L) L L)) L)) (N 18 L (N 8 (N 13 (N 24
  (N 31 L (N 9 L L (N 32 (N 34 L L L) L L)) L) L (N 23 (N 30 L (N 34 (N 33 L (N 35 L L L) L) L L)
  L) (N 35 (N 30 L (N 34 L L L) L) L L) L)) (N 31 (N 33 (N 12 L L (N 23 (N 24 L L (N 30 L (N 34 L
  L L) L)) L L)) L L) L L) L) (N 9 (N 13 (N 24 L L (N 23 (N 31 L (N 33 (N 34 L L L) L L) L) L L))
  (N 31 (N 24 L L (N 23 (N 32 L L (N 33 (N 12 L L (N 30 L (N 34 L L L) L)) L L)) L L)) L L) L) L
  (N 32 (N 31 L (N 34 L L L) L) L L)) L) L)) (N 35 (N 23 (N 24 L L (N 30 L (N 31 L (N 33 (N 34 L
  (N 17 L L (N 8 (N 12 L L (N 13 (N 18 L L L) L L)) L L)) L) (N 34 (N 12 L L (N 8 (N 13 (N 18 L L
  L) L L) L L)) L L) L) (N 9 (N 12 (N 17 L (N 18 L L L) L) (N 13 (N 17 L L L) L L) L) (N 32 (N 8
  (N 12 L (N 17 L L L) L) L (N 12 (N 17 L (N 18 L L L) L) (N 13 (N 17 L L L) L L) L)) L L) L)) L))
  L (N 24 (N 31 L (N 30 L (N 33 (N 34 L (N 18 L L (N 9 (N 12 (N 17 L L L) L L) L L)) L) (N 34 (N
  13 L L (N 9 (N 12 (N 17 L L L) L L) L L)) L L) L) (N 8 (N 12 (N 17 L (N 18 L L L) L) (N 13 (N 17
  L (N 18 L L L) L) L L) L) (N 32 (N 9 (N 13 L (N 18 L L L) L) L (N 12 (N 17 L (N 18 L L L) L) (N
  13 (N 17 L L L) L L) L)) L L) L)) L) L L)) L L) L) L) (N 8 (N 9 (N 32 L (N 26 (N 27 L (N 35 (N
  33 L (N 12 L (N 13 L L (N 23 L L L)) (N 13 L (N 24 L L L) L)) L) L L) L) (N 35 (N 27 (N 34 L (N
  17 L (N 18 L L (N 23 L L L)) (N 18 L (N 24 L L L) L)) L) (N 30 L (N 12 (N 17 L L (N 18 L (N 31 L
  L L) L)) L (N 31 L (N 13 (N 18 L L L) L L) L)) (N 31 L (N 13 (N 18 L L L) L L) L)) L) L L) L) L)
  (N 26 (N 27 L (N 12 L (N 13 L (N 33 (N 32 L (N 35 L L L) L) L L) (N 23 (N 17 L (N 30 L L L) L) L
  L)) (N 13 L (N 18 (N 24 (N 31 L L L) L L) L L) L)) L) (N 24 (N 27 (N 35 L (N 32 (N 34 L L L) L
  L) L) (N 32 (N 30 L (N 31 L (N 33 (N 34 L L L) L L) (N 12 (N 17 L (N 23 L L L) L) (N 17 (N 23 L
  L L) L L) L)) (N 31 L (N 13 (N 18 L L L) L L) L)) (N 35 (N 30 L L (N 31 L L L)) L L) L) L) L (N
  12 (N 17 L (N 23 L L L) L) (N 23 (N 17 L (N 30 L L L) L) L L) L)) L) L) (N 9 (N 26 (N 27 L (N 12
  L (N 13 L (N 33 (N 32 L (N 35 L L L) L) L L) (N 17 (N 23 (N 30 L L L) L L) L L)) (N 13 L (N 24
  (N 18 L (N 31 L L L) L) L L) L)) L) (N 23 (N 27 (N 35 L (N 32 (N 34 L L L) L L) L) (N 32 (N 30 L
  (N 33 (N 34 L L L) L L) (N 31 L (N 13 (N 18 L (N 24 L L L) L) (N 18 (N 24 L L L) L L) L) L)) (N
  35 (N 30 L L (N 31 L L L)) L L) L) L) L (N 13 (N 18 L (N 24 L L L) L) (N 24 (N 18 L (N 31 L L L)
  L) L L) L)) L) (N 32 (N 26 (N 27 L (N 33 L (N 30 L L (N 31 L L L)) L) L) (N 23 (N 24 (N 27 L (N
  35 L (N 33 (N 34 L L L) L L) L) L) L (N 30 L (N 12 (N 17 L L L) L L) L)) L (N 24 (N 31 L (N 13
  (N 18 L L L) L L) L) L L)) L) L L) L) L)))) L L))) (S 29 L L (N 5 L L (N 20 (N 14 (N 19 L L (N
  12 L (N 13 L (N 26 (N 33 L L L) L L) (N 9 (N 8 L (N 17 (N 30 (N 23 L L (N 24 (N 27 L (N 31 L (N
  34 L L L) L) L) L L)) L L) L L) (N 17 (N 23 (N 27 L (N 30 L (N 32 L L (N 25 L (N 26 (N 33 L L L)
  L L) L)) L) L) L (N 24 (N 25 L (N 27 L (N 26 (N 31 L (N 32 L L L) L) L L) L) L) L L)) (N 30 (N
  23 (N 35 L (N 33 (N 34 L L L) L L) L) L (N 24 (N 25 L (N 27 L (N 35 L L L) L) L) L L)) L L) L))
  (N 17 (N 23 (N 27 L (N 30 L (N 8 L L (N 33 (N 34 L L L) L L)) L) L) L (N 24 (N 27 L (N 25 L (N
  26 (N 33 L (N 30 (N 35 L L L) L L) L) L L) (N 8 (N 30 L (N 32 L L (N 33 (N 34 L L L) L L)) L) (N
  30 (N 32 L L (N 34 L (N 35 L L L) L)) L L) L)) L) L L)) (N 30 (N 8 (N 23 L L (N 24 (N 34 L (N 35
  L L L) L) L L)) L (N 23 (N 35 L (N 32 L L (N 25 L (N 26 (N 27 L L L) L L) L)) L) L (N 24 (N 25 L
  (N 32 L L L) L) L L))) L L) L) L)) (N 13 L (N 8 (N 9 L (N 18 (N 31 (N 24 L L (N 23 (N 27 L (N 30
  L (N 34 L L L) L) L) L L)) L L) L L) (N 18 (N 23 (N 27 L (N 17 L (N 34 (N 31 L (N 33 L L L) L) L
  L) (N 30 L (N 33 (N 34 L L L) L L) L)) L) L (N 24 (N 27 L (N 31 L (N 32 L L (N 25 L (N 26 (N 33
  L L L) L L) L)) L) L) L L)) (N 31 (N 23 (N 27 L (N 17 L L (N 30 L (N 33 (N 34 L L L) L L) L)) L)
  L (N 24 (N 35 L (N 33 (N 34 L L L) L L) L) L L)) L L) L)) (N 18 (N 23 (N 27 L (N 24 (N 31 L (N 9
  L L (N 33 (N 34 L L L) L L)) L) L (N 25 L (N 26 (N 33 L (N 30 (N 35 L L L) L L) L) L L) (N 9 (N
  31 L (N 32 L L (N 33 (N 34 L L L) L L)) L) (N 31 (N 32 L L (N 34 L (N 35 L L L) L)) L L) L))) L)
  L (N 24 (N 27 L (N 31 L (N 9 L L (N 33 (N 34 L L L) L L)) L) L) L L)) (N 31 (N 9 (N 24 L L (N 23
  (N 34 L (N 35 L L L) L) L L)) L (N 23 (N 35 L (N 32 L L (N 24 (N 25 L (N 26 (N 27 L L L) L L) L)
  L L)) L) L (N 24 (N 35 L (N 32 L L (N 25 L (N 26 (N 27 L L L) L L) L)) L) L L))) L L) L) L) L)))
  L (N 19 (N 17 L (N 18 L (N 27 (N 34 L L L) L L) (N 9 (N 8 L (N 12 (N 30 (N 23 L L (N 24 (N 26 L
  (N 31 L (N 33 L L L) L) L) L L)) L L) L L) (N 12 (N 23 (N 26 L (N 30 L (N 32 L L (N 25 L (N 27
  (N 34 L L L) L L) L)) L) L) L (N 24 (N 25 L (N 26 L (N 27 (N 31 L (N 32 L L L) L) L L) L) L) L
  L)) (N 30 (N 23 (N 35 L (N 33 (N 34 L L L) L L) L) L (N 24 (N 25 L (N 26 L (N 35 L L L) L) L) L
  L)) L L) L)) (N 12 (N 23 (N 26 L (N 30 L (N 8 L L (N 33 (N 34 L L L) L L)) L) L) L (N 24 (N 26 L
  (N 25 L (N 27 (N 34 L (N 30 (N 35 L L L) L L) L) L L) (N 8 (N 30 L (N 32 L L (N 33 (N 34 L L L)
  L L)) L) (N 30 (N 32 L L (N 33 L (N 35 L L L) L)) L L) L)) L) L L)) (N 30 (N 8 (N 23 L L (N 24
  (N 33 L (N 35 L L L) L) L L)) L (N 23 (N 35 L (N 32 L L (N 25 L (N 26 (N 27 L L L) L L) L)) L) L
  (N 24 (N 25 L (N 32 L L L) L) L L))) L L) L) L)) (N 18 L (N 8 (N 9 L (N 13 (N 31 (N 24 L L (N 23
  (N 26 L (N 30 L (N 33 L L L) L) L) L L)) L L) L L) (N 13 (N 23 (N 26 L (N 12 L (N 33 (N 31 L (N
  34 L L L) L) L L) (N 30 L (N 33 (N 34 L L L) L L) L)) L) L (N 24 (N 26 L (N 31 L (N 32 L L (N 25
  L (N 27 (N 34 L L L) L L) L)) L) L) L L)) (N 31 (N 23 (N 26 L (N 12 L L (N 30 L (N 33 (N 34 L L
  L) L L) L)) L) L (N 24 (N 35 L (N 33 (N 34 L L L) L L) L) L L)) L L) L)) (N 13 (N 23 (N 26 L (N
  24 (N 31 L (N 9 L L (N 33 (N 34 L L L) L L)) L) L (N 25 L (N 27 (N 34 L (N 30 (N 35 L L L) L L)
  L) L L) (N 9 (N 31 L (N 32 L L (N 33 (N 34 L L L) L L)) L) (N 31 (N 32 L L (N 33 L (N 35 L L L)
  L)) L L) L))) L) L (N 24 (N 26 L (N 31 L (N 9 L L (N 33 (N 34 L L L) L L)) L) L) L L)) (N 31 (N
  9 (N 24 L L (N 23 (N 33 L (N 35 L L L) L) L L)) L (N 23 (N 35 L (N 32 L L (N 24 (N 25 L (N 26 (N
  27 L L L) L L) L) L L)) L) L (N 24 (N 35 L (N 32 L L (N 25 L (N 26 (N 27 L L L) L L) L)) L) L
  L))) L L) L) L) L)) L (N 23 (N 24 (N 25 L (N 26 (N 27 L (N 35 L L L) L) (N 27 (N 35 L L L) L L)
  L) (N 8 (N 9 (N 32 L (N 12 L (N 30 L L (N 13 L (N 31 L L L) L)) (N 13 L (N 31 L L L) L)) L) (N
  12 L (N 17 L (N 30 L L (N 13 (N 18 L (N 31 L L L) L) (N 18 (N 31 L L L) L L) L)) (N 13 (N 18 L
  (N 31 L L L) L) (N 18 (N 31 L L L) L L) L)) (N 13 (N 18 L (N 31 L L L) L) (N 18 (N 31 L L L) L
  L) L)) L) (N 9 (N 13 L (N 18 L (N 31 L L (N 12 (N 17 L (N 30 L L L) L) (N 17 (N 30 L L L) L L)
  L)) (N 12 (N 17 L (N 30 L L L) L) (N 17 (N 30 L L L) L L) L)) (N 12 (N 17 L (N 30 L L L) L) (N
  17 (N 30 L L L) L L) L)) (N 32 (N 26 (N 27 L (N 35 L (N 33 (N 34 L L L) L L) L) L) (N 27 (N 35 L
  (N 33 (N 34 L L L) L L) L) (N 35 (N 30 L (N 33 (N 34 L L L) L L) (N 31 L (N 13 (N 18 L L L) L L)
  L)) L L) L) L) L L) L) L)) L (N 25 L (N 26 (N 27 L (N 35 (N 30 L (N 33 L (N 12 L L (N 13 L L L))
  L) L) L L) L) (N 27 (N 35 (N 30 L (N 33 (N 34 L (N 17 L L (N 18 L L L)) L) L L) L) L L) L L) L)
  (N 8 (N 12 L (N 17 L (N 30 L L L) L) L) (N 9 (N 12 (N 17 L (N 30 L L L) L) (N 17 (N 30 L L L) L
  L) L) (N 32 (N 30 L (N 12 (N 17 L L L) L L) L) L L) L) L))) L (N 24 (N 25 L (N 26 (N 27 L (N 35
  (N 31 L (N 33 L (N 12 L L (N 13 L L L)) L) L) L L) L) (N 27 (N 35 (N 31 L (N 33 (N 34 L (N 17 L
  L (N 18 L L L)) L) L L) L) L L) L L) L) (N 8 (N 9 (N 13 L (N 18 L (N 31 L L L) L) L) (N 13 (N 18
  L (N 31 L L L) L) (N 18 (N 31 L L L) L L) L) L) (N 9 (N 13 L (N 18 L (N 31 L L L) L) L) (N 32 (N
  31 L (N 13 (N 18 L L L) L L) L) L L) L) L)) L L)))) L L))) (S 29 L L L)))) (S 11 L L (S 16 L L
  (S 22 (S 29 (N 5 L L (N 20 (N 35 L (N 8 (N 9 (N 12 (N 14 L L (N 17 L L (N 18 L L L))) L (N 13 (N
  18 L L L) L L)) L (N 12 (N 14 L L (N 18 L L L)) L (N 13 (N 18 L L L) L L))) L (N 9 (N 12 (N 14 L
  L (N 17 L L L)) L (N 13 (N 14 L L L) L L)) L L)) L) L L)) L (N 5 L L (N 20 (N 8 (N 9 (N 12 (N 14
  L L (N 17 L L (N 18 L L L))) L (N 13 (N 18 L L L) L L)) L (N 12 (N 14 L L (N 18 L L L)) L (N 13
  (N 18 L L L) L L))) L (N 9 (N 12 (N 14 L L (N 17 L L L)) L (N 13 (N 14 L L L) L L)) L L)) L L)))
  L (S 29 L L L)))) (S 11 L L (S 16 L L (S 22 (S 29 (N 5 L L (N 14 (N 19 (N 20 L L L) L L) L L))
  (N 5 L L (N 14 (N 19 (N 20 L L L) L L) L L)) L) (S 29 L L L) L)))) (S 7 (S 11 (S 16 L (S 22 L (S
  29 L L (N 14 L L (N 5 L (N 8 (N 12 (N 17 L L (N 23 L L (N 27 (N 19 (N 25 L L (N 26 L L L)) L (N
  20 (N 26 L L L) L L)) L L))) L (N 17 (N 19 L L (N 20 L L L)) L (N 20 (N 18 L (N 19 (N 25 L L (N
  26 (N 27 L L L) L L)) L (N 23 (N 25 L L (N 26 L L L)) L (N 26 (N 27 L L L) L L))) (N 9 (N 19 L L
  (N 25 L L (N 26 (N 27 L L L) L L))) (N 19 (N 25 L L (N 26 (N 27 L L L) L L)) L (N 27 (N 25 L L
  (N 26 L L L)) L L)) L)) L L))) L (N 12 (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 18 L (N 20 (N 26
  L L (N 25 (N 27 L L L) L L)) L (N 23 (N 25 L L (N 26 L L L)) L (N 25 (N 27 L L L) L L))) (N 13
  (N 20 L L (N 26 L L (N 25 (N 27 L L L) L L))) (N 20 (N 26 L L (N 25 (N 27 L L L) L L)) L (N 27
  (N 25 L L (N 26 L L L)) L L)) L)) L L)) L L)) (N 8 (N 12 (N 17 L L (N 23 L L (N 27 (N 30 L (N 18
  (N 19 L L (N 20 L L L)) (N 31 (N 34 (N 35 L (N 19 (N 20 L L (N 25 L L L)) L (N 20 (N 26 L L L) L
  L)) L) L L) L L) L) L) L L))) L (N 13 (N 17 (N 19 L L (N 20 L L L)) L (N 20 (N 18 L (N 23 (N 25
  L L (N 26 L L L)) L L) L) L L)) (N 17 (N 19 L L (N 20 L L L)) L (N 20 (N 18 L (N 23 (N 25 L L (N
  26 L L L)) L L) L) L L)) L)) L (N 12 (N 9 (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 18 L (N 23 (N
  25 L L (N 26 L L L)) L L) L) L L)) (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 18 L (N 23 (N 25 L L
  (N 26 L L L)) L L) L) L L)) L) L L))))) (S 29 L L (N 14 L L (N 5 L (N 8 (N 12 (N 17 L L (N 19 (N
  9 L (N 18 L (N 24 (N 31 (N 13 L L (N 25 L (N 32 L L L) L)) L L) L L) (N 23 L (N 30 L L L) L)) (N
  13 (N 20 L L (N 26 L (N 33 L (N 35 (N 18 L (N 24 (N 31 L L L) L L) (N 23 L (N 30 L L L) L)) L L)
  L) L)) (N 18 L (N 24 (N 26 L (N 31 (N 33 L L L) L L) L) L L) (N 23 L (N 30 L L L) L)) L)) L (N
  20 (N 13 L (N 18 L (N 24 (N 31 (N 9 L L (N 25 L (N 26 L (N 33 L L L) L) L)) L L) L L) (N 23 L (N
  30 L L L) L)) (N 9 (N 25 L (N 32 L (N 35 (N 18 L (N 24 (N 31 L L L) L L) (N 23 L (N 30 L L L)
  L)) L L) L) L) (N 18 L (N 24 (N 25 L (N 31 (N 32 L L L) L L) L) L L) (N 23 L (N 30 L L L) L))
  L)) L L))) L (N 17 (N 19 L L (N 20 L L L)) L (N 20 (N 18 L (N 19 (N 9 L (N 24 (N 31 (N 13 L L (N
  25 L (N 32 L L L) L)) L L) L L) (N 13 (N 26 L (N 24 (N 31 L (N 33 L L L) L) L L) L) (N 24 (N 26
  L (N 31 (N 33 L L L) L L) L) L L) L)) L (N 24 (N 25 L (N 26 L (N 27 (N 31 (N 35 L (N 32 L L (N
  33 L L L)) L) (N 9 (N 13 L L (N 32 L L L)) L (N 13 (N 33 L L L) L L)) L) L (N 34 (N 32 L (N 9 (N
  31 L L L) L L) L) L L)) (N 27 (N 9 (N 13 L (N 31 L L L) L) (N 13 (N 31 L L L) L L) L) L L)) (N
  26 L (N 27 (N 34 (N 32 L (N 35 L L L) L) L L) L L) L)) (N 31 (N 9 (N 13 L L (N 25 L L L)) L (N
  13 (N 26 L L L) L L)) L L) L)) (N 9 (N 19 L L (N 25 L (N 32 L (N 35 (N 23 (N 30 L (N 31 L L L)
  L) (N 24 (N 30 L L L) L L) L) L L) L) L)) (N 19 (N 23 (N 30 L (N 31 (N 35 L (N 25 L L (N 26 L (N
  33 L L L) L)) L) L L) L) (N 24 (N 30 (N 35 L (N 32 L L (N 26 L (N 33 L L L) L)) L) L L) L L) L)
  L (N 23 (N 25 L (N 24 (N 30 L (N 31 (N 32 L L L) L L) L) L L) L) (N 24 (N 25 L (N 30 (N 32 L L
  L) L L) L) L L) L)) L)) L L))) L (N 12 (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 18 L (N 20 (N 13
  L (N 24 (N 31 (N 9 L L (N 25 L (N 26 L (N 33 L L L) L) L)) L L) L L) (N 9 (N 25 L (N 24 (N 31 L
  (N 32 L L L) L) L L) L) (N 24 (N 25 L (N 31 (N 32 L L L) L L) L) L L) L)) L (N 24 (N 25 L (N 26
  L (N 27 (N 31 (N 35 L (N 32 L L (N 33 L L L)) L) (N 9 (N 13 L L (N 32 L L L)) L (N 13 (N 33 L L
  L) L L)) L) L (N 34 (N 33 L (N 13 (N 31 L L L) L L) L) L L)) (N 27 (N 34 (N 32 L (N 35 L L L) L)
  L L) L L)) (N 26 L (N 27 (N 9 (N 13 L (N 31 L L L) L) (N 13 (N 31 L L L) L L) L) L L) L)) (N 31
  (N 9 (N 13 L L (N 25 L L L)) L (N 13 (N 26 L L L) L L)) L L) L)) (N 13 (N 20 L L (N 26 L (N 33 L
  (N 35 (N 23 (N 30 L (N 31 L L L) L) (N 24 (N 30 L L L) L L) L) L L) L) L)) (N 20 (N 23 (N 30 L
  (N 31 (N 35 L (N 26 L L (N 25 L (N 32 L L L) L)) L) L L) L) (N 24 (N 30 (N 35 L (N 33 L L (N 25
  L (N 32 L L L) L)) L) L L) L L) L) L (N 23 (N 26 L (N 24 (N 30 L (N 31 (N 33 L L L) L L) L) L L)
  L) (N 24 (N 26 L (N 30 (N 33 L L L) L L) L) L L) L)) L)) L L)) L L)) (N 8 (N 12 (N 17 L L (N 18
  (N 19 L L (N 20 L L L)) (N 27 (N 34 (N 35 L (N 19 (N 20 L L (N 9 L (N 23 L (N 24 (N 30 L L (N 32
  L (N 25 L L (N 26 L L L)) L)) L L) (N 25 L (N 24 (N 26 L (N 30 L (N 31 (N 32 L L (N 33 L L L)) L
  L) L) L) L L) L)) L)) L (N 20 (N 13 L (N 23 L (N 24 (N 30 L L (N 32 L (N 25 L L (N 26 L L L))
  L)) L L) (N 25 L (N 24 (N 26 L (N 30 L (N 31 (N 32 L L (N 33 L L L)) L L) L) L) L L) L)) L) L
  L)) L) L L) L L) L)) L (N 13 (N 17 (N 19 L L (N 20 L L L)) L (N 20 (N 18 L (N 26 L (N 24 (N 27
  (N 31 L (N 33 L L L) L) L L) L L) L) L) L L)) (N 17 (N 19 L L (N 20 L L L)) L (N 20 (N 18 L (N
  27 (N 26 L (N 24 (N 33 (N 34 L L L) L L) L L) L) L L) L) L L)) L)) L (N 12 (N 9 (N 17 (N 19 L L
  (N 20 L L L)) L (N 19 (N 18 L (N 25 L (N 24 (N 27 (N 31 L (N 32 L L L) L) L L) L L) L) L) L L))
  (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 18 L (N 27 (N 25 L (N 24 (N 32 (N 34 L L L) L L) L L)
  L) L L) L) L L)) L) L L)))))) (S 22 L (S 29 L (N 14 L L (N 35 (N 5 L (N 18 (N 19 L L (N 20 L L
  L)) (N 8 (N 12 (N 17 L L (N 23 L L (N 27 (N 34 L L L) L L))) L (N 17 (N 19 L L (N 20 L L L)) L
  (N 20 (N 13 (N 19 (N 9 L (N 25 L L (N 26 L (N 27 (N 30 L L (N 31 L L L)) L L) L)) (N 23 (N 30 L
  L (N 34 L L L)) L (N 26 L (N 24 (N 30 L L L) L L) L))) L (N 27 (N 34 L L L) L L)) (N 9 (N 19 L L
  (N 27 (N 34 L L L) L L)) L (N 19 (N 23 (N 26 L L (N 30 L L L)) L (N 24 (N 26 L L L) L L)) L (N
  27 (N 34 L L L) L L))) L) L L))) L (N 12 (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 9 (N 20 (N 13
  L (N 26 L L (N 25 L (N 27 (N 30 L L (N 31 L L L)) L L) L)) (N 23 (N 30 L L (N 34 L L L)) L (N 25
  L (N 24 (N 30 L L L) L L) L))) L (N 27 (N 34 L L L) L L)) (N 13 (N 20 L L (N 27 (N 34 L L L) L
  L)) L (N 20 (N 23 (N 25 L L (N 30 L L L)) L (N 24 (N 25 L L L) L L)) L (N 27 (N 34 L L L) L L)))
  L) L L)) L L)) L) (N 18 (N 19 L L (N 20 L L L)) (N 19 (N 17 L (N 20 (N 23 (N 30 L L (N 31 L L
  L)) L (N 24 (N 31 L L L) L L)) L (N 9 (N 8 L (N 12 (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L
  L L) L L)) L L) (N 12 (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 30 L L L) L L)) (N 23 (N 30 L L
  (N 31 L L L)) L (N 24 (N 30 L L L) L L)) L)) (N 12 (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L
  L L) L L)) (N 8 (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) L (N 23 (N 30 L L (N 31
  L L L)) L (N 24 (N 30 L L L) L L))) L) L)) (N 20 (N 23 (N 30 L L (N 31 L (N 27 (N 34 L L L) L L)
  L)) L (N 30 (N 24 L (N 27 (N 34 L L L) L L) L) L L)) L (N 9 (N 8 L (N 12 (N 23 (N 30 L L (N 31 L
  (N 32 L L L) L)) L (N 25 L (N 24 (N 30 L L L) L L) L)) (N 23 (N 30 L L (N 31 L (N 32 L L L) L))
  L (N 25 L (N 24 (N 30 L L L) L L) L)) L) (N 23 (N 30 L L L) L L)) (N 12 (N 23 (N 30 L L (N 8 L
  (N 31 L L L) L)) L (N 30 (N 8 L (N 24 L L L) L) L L)) (N 23 (N 30 L L (N 31 L (N 8 (N 32 L L L)
  L L) L)) L (N 30 (N 24 L (N 8 (N 25 L L L) L L) L) L L)) L) L))) L (N 20 (N 8 (N 13 (N 12 L (N
  17 L (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) (N 23 (N 30 L L (N 31 L (N 33 L L
  L) L)) L (N 26 L (N 24 (N 30 L L L) L L) L))) (N 17 L (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N
  30 L L L) L L)) (N 23 (N 30 L L L) L L))) (N 17 L (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L
  L L) L L)) (N 23 (N 30 L L (N 12 L (N 31 L L L) L)) L (N 30 (N 12 L (N 24 L L L) L) L L))) L) (N
  13 (N 12 L (N 17 L L (N 23 (N 30 L L (N 31 L (N 33 L L L) L)) L (N 26 L (N 24 (N 30 L L L) L L)
  L))) (N 17 L (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 30 L L L) L L)) (N 23 (N 30 L L L) L L)))
  (N 17 L (N 12 (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) L (N 23 (N 30 L L (N 31 L
  L L)) L (N 24 (N 30 L L L) L L))) (N 23 (N 30 L L (N 31 L (N 12 (N 33 L L L) L L) L)) L (N 30 (N
  24 L (N 12 (N 26 L L L) L L) L) L L))) L) L) L L)) L)) L L)) (N 14 L L (N 5 L (N 18 (N 19 L L (N
  20 L L L)) (N 27 (N 8 (N 12 (N 17 L L (N 23 L L (N 19 (N 9 L (N 24 (N 25 L L (N 20 (N 13 L L (N
  26 L (N 31 (N 32 L (N 35 L L L) L) L L) L)) L L)) L L) (N 20 (N 13 L (N 24 (N 26 L L (N 25 L (N
  31 (N 32 L (N 35 L L L) L) L L) L)) L L) L) L L)) L (N 20 (N 13 L (N 26 L L L) L) L L)))) L (N
  17 (N 19 L L (N 20 L L L)) L (N 20 (N 13 (N 33 L (N 31 (N 24 L (N 9 L L (N 25 L L (N 26 L L L)))
  L) L L) L) (N 24 (N 26 L L (N 23 (N 25 L (N 30 L (N 31 (N 32 L L L) L L) L) L) L L)) L L) L) L
  L))) L (N 12 (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 9 (N 32 L (N 31 (N 24 L (N 13 L L (N 25 L
  L (N 26 L L L))) L) L L) L) (N 24 (N 25 L L (N 23 (N 26 L (N 30 L (N 31 (N 33 L L L) L L) L) L)
  L L)) L L) L) L L)) L L)) L L) L) (N 18 (N 19 L L (N 20 L L L)) (N 19 (N 17 L (N 24 (N 27 (N 34
  (N 20 L L (N 32 L (N 31 (N 9 L (N 25 L L (N 26 L (N 35 L L L) L)) L) L L) L)) L L) L L) L L) (N
  20 (N 23 (N 24 (N 25 L (N 26 L (N 27 (N 35 L L L) L L) (N 27 (N 34 L (N 35 L L L) L) (N 34 (N 32
  L (N 31 (N 35 L L L) L L) L) L L) L)) (N 26 L (N 27 (N 34 L (N 35 L L L) L) (N 34 (N 33 L (N 31
  (N 35 L L L) L L) L) L L) L) L)) (N 25 L L (N 26 L L L)) L) L (N 8 (N 9 L (N 12 (N 30 L (N 13 L
  (N 24 (N 31 (N 35 L (N 25 L (N 26 L L (N 32 L L L)) (N 26 L (N 33 L L L) L)) L) L L) L L) (N 25
  L (N 32 L L L) L)) L) (N 24 (N 25 L (N 32 L L (N 26 L (N 13 (N 33 L L L) L L) L)) (N 26 L (N 13
  (N 33 L L L) L L) L)) (N 25 L L (N 13 (N 26 L L L) L L)) L) L) (N 12 (N 13 L (N 26 L (N 33 L L
  L) L) L) (N 13 (N 26 L (N 33 L L L) L) (N 24 (N 26 L L L) L L) L) L)) (N 12 (N 13 L (N 24 (N 25
  L (N 9 (N 31 L (N 32 L L (N 33 L L L)) L) L (N 26 L (N 33 L L L) L)) (N 26 L (N 33 L L L) L)) (N
  26 L L (N 9 (N 25 L L L) L L)) L) (N 9 (N 25 L (N 32 L L L) L) (N 24 (N 25 L L L) L L) L)) (N 30
  (N 24 (N 35 L (N 32 L L (N 33 L L L)) L) (N 27 (N 25 L L (N 26 L L L)) L L) L) L L) L) L)) L (N
  9 (N 32 L (N 31 (N 24 L (N 25 L L (N 23 (N 26 L L L) L L)) L) L L) L) (N 12 (N 23 (N 8 L (N 24
  (N 25 L L (N 26 L (N 32 (N 31 L (N 34 L L L) L) L L) L)) L L) (N 30 L (N 24 (N 25 L (N 32 (N 31
  L (N 34 L L L) L) L L) (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L) L)) (N 25 L L (N 26 L L L)) L)
  L)) L (N 8 (N 25 L (N 32 L L L) L) (N 24 (N 25 L L L) L L) L)) (N 23 (N 24 (N 25 L (N 32 (N 8 L
  L (N 30 L (N 34 L L L) L)) L L) (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L) L)) (N 25 L L (N 26 L
  L L)) L) L (N 8 (N 25 L (N 32 L L L) L) (N 24 (N 25 L L L) L L) L)) L) L))) L (N 20 (N 8 (N 13
  (N 33 L (N 31 (N 24 L (N 17 L L (N 26 L L (N 23 (N 25 L L L) L L))) L) L L) L) (N 17 L (N 24 (N
  27 (N 34 (N 33 L (N 26 L L (N 25 L (N 35 L L L) L)) L) L L) L L) L L) (N 23 (N 12 L (N 24 (N 26
  L L (N 25 L (N 33 (N 31 L (N 34 L L L) L) L L) L)) L L) (N 30 L (N 24 (N 25 L (N 26 L (N 27 (N
  35 L L L) L L) (N 32 (N 31 L (N 34 L L L) L) L L)) (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L)
  L)) (N 25 L L (N 26 L L L)) L) L)) L (N 12 (N 26 L (N 33 L L L) L) (N 24 (N 26 L L L) L L) L)))
  L) (N 13 (N 33 L (N 31 (N 24 L (N 9 L L (N 17 L L (N 25 (N 27 L L L) L L))) L) L L) L) (N 17 L
  (N 24 (N 27 (N 34 (N 33 L (N 26 L L (N 25 L (N 32 L L L) L)) L) L L) L L) L L) (N 23 (N 24 (N 25
  L (N 9 (N 31 L (N 33 (N 34 L L L) L L) L) L (N 32 (N 31 L (N 34 L L L) L) L L)) (N 26 L (N 33 (N
  12 L L (N 30 L (N 34 L L L) L)) L L) L)) (N 25 L L (N 26 L L L)) L) L (N 12 (N 26 L (N 33 L L L)
  L) (N 24 (N 26 L L L) L L) L))) L) L) L L)) L)))) (S 29 L L L))) (S 16 L (S 22 (S 29 L L (N 5 L
  (N 8 (N 12 (N 14 L L (N 17 L L (N 19 (N 9 L (N 18 L (N 24 (N 31 (N 13 L L (N 32 L (N 25 L L (N
  26 L (N 33 L L L) L)) L)) L L) L L) (N 30 L (N 23 L L (N 31 (N 35 L (N 25 L L (N 26 L L L)) L) L
  L)) L)) (N 13 (N 18 L (N 20 (N 33 L (N 26 L L (N 25 L (N 24 (N 31 L L L) L L) L)) L) L (N 23 L
  (N 24 (N 30 L L (N 27 (N 31 L (N 32 L L L) L) L L)) L L) (N 25 L (N 24 (N 27 (N 31 L (N 30 L L
  (N 32 L L L)) L) L L) L L) L))) (N 30 L (N 23 L L (N 25 L (N 31 (N 24 L (N 26 L L (N 32 L L L))
  L) L L) L)) L)) (N 26 L L (N 25 L (N 24 (N 32 L (N 31 (N 33 L L L) L L) L) L L) L)) L)) L (N 20
  (N 18 L (N 23 L (N 24 (N 30 L L (N 27 (N 34 (N 32 L (N 31 (N 33 L (N 35 L L L) L) L L) L) L L) L
  L)) L L) (N 26 L (N 24 (N 27 (N 34 (N 33 L L (N 25 L (N 30 L (N 35 L L L) L) L)) L L) L L) L L)
  L)) (N 30 L (N 23 L L (N 26 L (N 24 (N 31 (N 35 L L L) L L) L L) L)) L)) L L)))) L (N 14 (N 19 L
  L (N 9 L (N 13 L (N 24 (N 31 (N 18 L L (N 32 L (N 25 L L (N 35 L (N 27 (N 17 L L (N 20 L L L)) L
  L) L)) L)) L L) L L) (N 17 (N 30 L (N 23 L L (N 31 (N 35 L (N 25 L L (N 27 L L L)) L) L L)) L) L
  (N 20 (N 24 (N 25 L (N 32 L L (N 27 L (N 18 (N 31 L (N 30 (N 34 L L L) L L) L) L L) L)) (N 27 L
  (N 34 (N 30 L (N 31 (N 35 L L L) L L) L) L L) L)) (N 25 L L (N 27 L L L)) L) L L))) (N 13 L (N
  17 (N 18 (N 20 (N 34 L (N 27 L L (N 25 L (N 24 (N 31 L L L) L L) L)) L) L (N 23 L (N 24 (N 30 L
  L (N 26 (N 31 L (N 32 L L L) L) L L)) L L) (N 25 L (N 24 (N 26 (N 31 L (N 30 L L (N 32 L L L))
  L) L L) L L) L))) (N 24 (N 27 L L (N 25 L (N 31 (N 34 L L L) L L) L)) L L) L) L (N 20 (N 18 (N
  24 (N 31 L (N 32 L L (N 25 L (N 27 L (N 30 (N 34 L L L) L L) L) L)) L) (N 25 L L (N 27 L L L))
  L) (N 24 (N 27 L L (N 25 L (N 31 (N 32 L (N 35 L L L) L) L L) L)) L L) L) L L)) (N 17 (N 30 L (N
  23 L L (N 25 L (N 31 (N 34 L (N 35 L L L) L) L L) L)) L) L L)))) L (N 17 (N 19 L L (N 20 (N 13 L
  (N 23 L (N 24 (N 30 L L (N 26 (N 33 (N 32 L (N 31 (N 34 L (N 35 L L L) L) L L) L) L L) L L)) L
  L) (N 26 (N 27 L (N 24 (N 33 (N 34 L L (N 25 L (N 30 L (N 35 L L L) L) L)) L L) L L) L) L L)) (N
  30 L (N 23 L L (N 27 L (N 24 (N 31 (N 35 L L L) L L) L L) L)) L)) L L)) L (N 20 (N 19 (N 9 L (N
  18 L (N 24 (N 31 (N 13 L L (N 26 L (N 32 L (N 35 L L L) L) L)) L L) L L) (N 24 (N 25 L (N 32 L L
  (N 26 L (N 13 (N 31 L (N 30 (N 33 L L L) L L) L) L L) L)) (N 26 L (N 33 (N 30 L (N 31 (N 35 L L
  L) L L) L) L L) L)) (N 25 L L (N 26 L L L)) L)) (N 18 L (N 13 (N 24 (N 31 L (N 32 L L (N 25 L (N
  26 L (N 30 (N 33 L L L) L L) L) L)) L) (N 25 L L (N 26 L L L)) L) (N 24 (N 26 L L (N 25 L (N 31
  (N 32 L (N 35 L L L) L) L L) L)) L L) L) L)) L (N 24 (N 25 L (N 31 (N 35 L (N 32 L L (N 9 L (N
  13 L (N 18 L L L) L) L)) L) (N 30 (N 35 L (N 32 L L (N 33 (N 34 L L L) L L)) L) L (N 33 (N 34 L
  L L) L L)) L) (N 9 (N 31 L (N 32 L (N 13 L L (N 18 L L (N 30 (N 33 (N 34 L L L) L L) L L))) L)
  L) (N 26 (N 27 L (N 34 (N 31 L (N 33 L L L) L) L L) L) (N 33 (N 34 L (N 27 (N 31 L L L) L L) L)
  L L) L) L)) (N 23 (N 25 L (N 9 (N 13 (N 18 L L (N 26 L L (N 27 (N 30 L (N 31 L L L) L) L L))) L
  (N 26 (N 27 L L (N 18 (N 30 L (N 31 L L L) L) L L)) L L)) L (N 13 (N 18 L L L) L L)) (N 26 (N 27
  L L L) L L)) L (N 26 (N 27 L L L) L L)) L)) L L)))) L (N 12 (N 14 L L (N 17 (N 19 L L (N 20 L L
  L)) L (N 19 (N 18 L (N 20 (N 24 (N 25 L (N 26 L (N 13 (N 31 L (N 9 L L (N 33 L L L)) L) L (N 9
  (N 31 L (N 32 L L L) L) (N 31 (N 32 L L L) L L) L)) (N 27 (N 34 L L (N 23 L (N 30 (N 32 L (N 35
  L L L) L) L L) L)) L L)) (N 26 L (N 33 (N 13 L L (N 30 L (N 31 L L L) L)) L L) L)) (N 25 L L (N
  26 L L L)) L) L (N 24 (N 25 L (N 26 L (N 13 (N 31 L (N 9 L L (N 30 (N 32 L L L) L L)) L) L (N 33
  (N 31 L (N 9 (N 32 L L L) L L) L) L L)) (N 27 (N 34 (N 32 L (N 35 L L L) L) L L) L L)) (N 26 L
  (N 33 (N 30 L (N 31 L L L) L) L L) L)) (N 25 L L (N 26 L L L)) L)) (N 13 (N 20 (N 24 (N 31 L (N
  30 (N 33 L L (N 9 L (N 32 L L L) L)) L L) L) (N 26 L L (N 25 L (N 27 (N 9 (N 31 L (N 30 (N 35 L
  L L) L L) L) L (N 33 L (N 31 (N 35 L L L) L L) L)) L L) L)) L) L (N 24 (N 31 L (N 30 (N 33 L L
  L) L L) L) (N 26 L L (N 25 L (N 27 (N 9 (N 31 L (N 30 (N 33 L L L) L L) L) L (N 23 (N 30 L (N 31
  (N 32 L L L) L L) L) L (N 30 (N 32 L (N 35 L L L) L) (N 31 (N 32 L L L) L L) L))) L L) L)) L))
  (N 26 L L (N 25 L (N 24 (N 20 (N 27 (N 35 L (N 32 (N 30 L (N 31 L L L) L) L L) L) (N 30 (N 32 L
  (N 35 L L L) L) (N 31 (N 35 L L L) L L) L) L) L (N 33 (N 30 L (N 31 L L L) L) L L)) L L) L)) L))
  L L))) L (N 14 (N 13 L (N 17 (N 19 L L (N 20 (N 24 (N 25 L (N 26 (N 33 L L (N 23 L (N 30 (N 32 L
  (N 35 L L L) L) L L) L)) L (N 27 L (N 18 (N 31 L (N 9 L L (N 34 L L L)) L) L (N 9 (N 31 L (N 32
  L L L) L) (N 31 (N 32 L L L) L L) L)) L)) (N 27 L (N 34 (N 18 L L (N 30 L (N 31 L L L) L)) L L)
  L)) (N 25 L L (N 27 L L L)) L) L (N 24 (N 25 L (N 26 (N 35 L (N 23 L (N 27 L L (N 32 (N 33 L L
  L) L L)) (N 32 (N 33 L L L) L L)) L) L (N 27 L (N 33 (N 34 (N 30 L (N 31 L L L) L) L L) L L) L))
  (N 27 L (N 34 (N 30 L (N 31 L L L) L) L L) L)) (N 25 L L (N 27 L L L)) L))) L (N 19 (N 20 L L L)
  L L)) (N 17 (N 19 L L (N 18 (N 20 (N 24 (N 31 L (N 30 (N 34 L L (N 9 L (N 32 L L L) L)) L L) L)
  (N 27 L L (N 25 L (N 26 (N 9 (N 31 L (N 30 (N 35 L L L) L L) L) L (N 34 L (N 31 (N 35 L L L) L
  L) L)) L L) L)) L) L (N 24 (N 31 L (N 30 (N 34 L L L) L L) L) (N 26 (N 27 L L (N 25 L (N 9 (N 31
  L (N 30 (N 34 L L L) L L) L) L (N 23 (N 30 L (N 31 (N 32 L L L) L L) L) L (N 30 (N 32 L (N 35 L
  L L) L) (N 31 (N 32 L L L) L L) L))) L)) L L) L)) (N 27 L L (N 25 L (N 24 (N 20 (N 26 (N 35 L (N
  32 (N 30 L (N 31 L L L) L) L L) L) (N 30 (N 32 L (N 35 L L L) L) (N 31 (N 35 L L L) L L) L) L) L
  (N 34 (N 30 L (N 31 L L L) L) L L)) L L) L)) L)) L (N 19 (N 20 L L L) L L))) L L))) (N 8 (N 12
  (N 14 L L (N 17 L L (N 18 (N 19 L L (N 20 L L L)) (N 34 (N 19 (N 35 L (N 9 L (N 20 (N 27 L L (N
  23 L (N 30 L L L) L)) L (N 23 L (N 24 (N 30 L L (N 33 L L L)) L L) (N 25 L (N 24 (N 27 (N 30 L
  (N 26 L L (N 32 L L L)) L) L L) L L) L))) (N 20 (N 27 L L (N 23 L (N 30 L L L) L)) L L)) L) L (N
  20 (N 13 (N 23 L (N 24 (N 31 L (N 30 L L (N 32 L L L)) L) L L) (N 26 L (N 24 (N 27 (N 30 L (N 31
  L L L) L) L L) L L) L)) (N 26 L L (N 23 L (N 24 (N 25 L (N 32 L (N 31 (N 35 L L L) L L) L) L) L
  L) L)) L) L L)) L L) L))) L (N 13 (N 14 L L (N 17 (N 19 L L (N 20 L L L)) L (N 20 (N 18 L (N 34
  (N 33 L (N 26 L L (N 25 L (N 24 (N 31 L L L) L L) L)) L) L L) L) L L))) (N 33 (N 14 (N 19 L L (N
  35 L (N 9 L (N 17 (N 20 (N 26 L L (N 23 L (N 30 L L L) L)) L (N 23 L (N 24 (N 30 L L (N 34 L L
  L)) L L) (N 25 L (N 24 (N 26 (N 30 L (N 27 L L (N 32 L L L)) L) L L) L L) L))) L (N 20 (N 26 L L
  (N 25 L (N 34 L L L) L)) L L)) (N 20 (N 26 L L (N 25 L (N 34 L L L) L)) L L)) L)) L (N 17 (N 19
  L L (N 20 (N 18 (N 23 L (N 24 (N 31 L (N 30 L L (N 32 L L L)) L) L L) (N 26 (N 27 L (N 24 (N 30
  L (N 31 L L L) L) L L) L) L L)) (N 27 L L (N 23 L (N 24 (N 25 L (N 32 L (N 31 (N 35 L L L) L L)
  L) L) L L) L)) L) L L)) L (N 20 (N 34 L (N 18 (N 19 L L (N 27 L L (N 25 L (N 24 (N 31 L L L) L
  L) L))) L L) L) L L))) L L) L)) L (N 9 (N 12 (N 14 L L (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N
  18 L (N 32 L (N 31 (N 24 L (N 23 (N 25 L L (N 26 L L L)) L L) L) L L) L) L) L L))) L (N 14 (N 13
  L (N 17 (N 19 L L (N 32 L (N 31 (N 24 L (N 23 (N 25 L L (N 27 L L L)) L L) L) L L) L)) L L) L) L
  L)) (N 12 (N 14 L L (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 18 L (N 34 (N 32 L (N 25 L L (N 26
  L (N 35 L L L) L)) L) L L) L) L L))) L (N 14 (N 13 L (N 17 (N 19 L L (N 33 (N 32 L (N 25 L L (N
  27 L (N 35 L L L) L)) L) L L)) L L) L) L L)) L)))) L (S 29 L L (N 5 L (N 8 (N 12 (N 14 L L (N 17
  L L (N 19 (N 9 L (N 18 L (N 24 (N 31 (N 13 L L (N 25 L (N 32 L L L) L)) L L) L L) (N 23 L (N 30
  L L L) L)) (N 13 (N 18 L (N 20 (N 26 L (N 33 L L L) L) L (N 23 L (N 24 (N 26 L (N 30 L L (N 27
  (N 31 L (N 32 L L L) L) L L)) L) L L) (N 25 L (N 24 (N 26 L (N 27 (N 31 L (N 30 L L (N 32 L L
  L)) L) L L) L) L L) L))) (N 23 L (N 30 L L L) L)) (N 26 (N 24 L (N 18 L L (N 23 L L L)) L) L L)
  L)) L (N 20 (N 18 L (N 23 L (N 24 (N 30 L L (N 27 (N 34 (N 32 L (N 31 (N 33 L (N 35 L L L) L) L
  L) L) L L) L L)) L L) (N 27 (N 25 L (N 24 (N 26 L (N 34 (N 33 L L (N 30 L (N 35 L L L) L)) L L)
  L) L L) L) L L)) (N 23 L (N 30 L L L) L)) L L)))) L (N 14 (N 19 L L (N 9 L (N 13 L (N 24 (N 31
  (N 18 L L (N 25 L (N 32 L L L) L)) L L) L L) (N 17 (N 23 L (N 30 L L L) L) L (N 20 (N 23 (N 30 L
  (N 31 (N 35 L (N 25 L L (N 27 L L L)) L) L L) L) (N 24 (N 30 (N 35 L (N 32 L L (N 34 L L L)) L)
  L L) L L) L) L L))) (N 13 L (N 17 (N 18 (N 20 (N 27 L (N 34 L L L) L) L (N 23 L (N 24 (N 27 L (N
  30 L L (N 26 (N 31 L (N 32 L L L) L) L L)) L) L L) (N 25 L (N 24 (N 26 (N 27 L (N 31 L (N 30 L L
  (N 32 L L L)) L) L) L L) L L) L))) (N 24 (N 27 L L L) L L) L) L (N 20 (N 18 (N 24 (N 27 L (N 31
  L (N 32 L L (N 25 L (N 30 (N 34 L L L) L L) L)) L) L) (N 25 L L (N 23 (N 27 L L L) L L)) L) (N
  24 (N 27 (N 26 L L (N 23 L (N 25 L (N 30 (N 34 L L L) L L) L) L)) L L) L L) L) L L)) (N 17 (N 23
  L (N 30 L L L) L) L L)))) L (N 17 (N 19 L L (N 20 (N 13 L (N 23 L (N 24 (N 30 L L (N 26 (N 33 (N
  32 L (N 31 (N 34 L (N 35 L L L) L) L L) L) L L) L L)) L L) (N 26 (N 25 L (N 24 (N 27 L (N 33 (N
  34 L L (N 30 L (N 35 L L L) L)) L L) L) L L) L) L L)) (N 23 L (N 30 L L L) L)) L L)) L (N 20 (N
  19 (N 9 L (N 18 L (N 24 (N 31 (N 13 L L (N 25 L (N 32 L L L) L)) L L) L L) (N 23 (N 30 L (N 31
  (N 35 L (N 25 L L (N 26 L L L)) L) L L) L) (N 24 (N 30 (N 35 L (N 32 L L (N 33 L L L)) L) L L) L
  L) L)) (N 18 L (N 13 (N 24 (N 26 L (N 31 L (N 32 L L (N 25 L (N 30 (N 33 L L L) L L) L)) L) L)
  (N 25 L L (N 23 (N 26 L L L) L L)) L) (N 24 (N 26 (N 27 L L (N 23 L (N 25 L (N 30 (N 33 L L L) L
  L) L) L)) L L) L L) L) L)) L (N 24 (N 25 L (N 31 (N 35 L (N 32 L L (N 9 L (N 13 L (N 18 L L L)
  L) L)) L) (N 30 (N 35 L (N 32 L L (N 33 (N 34 L L L) L L)) L) L (N 33 (N 34 L L L) L L)) L) (N 9
  (N 13 L (N 18 L (N 31 L L L) L) L) (N 13 (N 18 L (N 31 L L L) L) (N 18 (N 31 L L L) L L) L) L))
  (N 23 (N 25 L (N 9 (N 13 (N 18 L L (N 26 L L (N 27 (N 30 L (N 31 L L L) L) L L))) L (N 26 (N 27
  L L (N 18 (N 30 L (N 31 L L L) L) L L)) L L)) L (N 13 (N 18 L L L) L L)) (N 26 (N 27 L L L) L
  L)) L (N 26 (N 27 L L L) L L)) L)) L L)))) L (N 12 (N 14 L L (N 17 (N 19 L L (N 20 L L L)) L (N
  19 (N 18 L (N 20 (N 24 (N 25 L (N 26 L (N 13 (N 31 L (N 9 L L (N 33 L L L)) L) L (N 9 (N 31 L (N
  32 L L L) L) (N 31 (N 32 L L L) L L) L)) (N 27 (N 34 L L (N 9 (N 31 L (N 32 L L L) L) (N 31 (N
  32 L L L) L L) L)) L L)) (N 26 L (N 13 (N 33 L L L) L L) L)) (N 31 (N 9 (N 13 L L (N 25 L L L))
  L (N 13 (N 26 L L L) L L)) L L) L) L (N 24 (N 25 L (N 26 L (N 13 (N 31 L (N 9 L L (N 30 (N 32 L
  L L) L L)) L) L (N 27 (N 33 (N 31 L (N 9 (N 32 L L L) L L) L) L L) L L)) (N 27 (N 34 (N 32 L (N
  35 L L L) L) L L) L L)) (N 26 L (N 13 (N 9 L (N 31 L L L) L) L L) L)) (N 31 (N 9 (N 13 L L (N 25
  L L L)) L (N 13 (N 23 (N 25 L L L) L L) L L)) L L) L)) (N 13 (N 20 (N 23 (N 30 L (N 31 (N 24 L
  (N 26 L L (N 9 L (N 25 L L L) L)) L) L L) L) (N 24 (N 30 (N 31 L (N 33 L L (N 9 L (N 32 L L L)
  L)) L) L L) L L) L) L (N 23 (N 26 L (N 24 (N 30 L (N 31 L L L) L) L L) L) (N 24 (N 26 L (N 30 (N
  33 L L L) L L) L) L L) L)) (N 20 (N 23 (N 26 L L (N 25 L (N 24 (N 30 L (N 31 (N 9 L (N 32 L L L)
  L) L L) L) L L) L)) (N 24 (N 26 L L (N 25 L (N 30 (N 32 L (N 35 L L L) L) L L) L)) L L) L) L (N
  26 (N 23 L (N 24 L L L) L) L L)) L)) L L))) L (N 14 (N 13 L (N 17 (N 19 L L (N 20 (N 24 (N 25 L
  (N 26 (N 33 L L (N 23 (N 30 L (N 31 (N 32 L (N 35 L L L) L) L L) L) (N 30 (N 32 L (N 35 L L L)
  L) L L) L)) L (N 27 L (N 18 (N 31 L (N 9 L L (N 34 L L L)) L) L (N 9 (N 31 L (N 32 L L L) L) (N
  31 (N 32 L L L) L L) L)) L)) (N 26 (N 27 L (N 18 (N 34 L L L) L L) L) L L)) (N 31 (N 9 (N 18 L L
  (N 25 L L L)) L (N 18 (N 27 L L L) L L)) L L) L) L (N 24 (N 25 L (N 26 (N 27 L (N 18 (N 31 L (N
  9 L L (N 30 (N 32 L L L) L L)) L) L (N 33 (N 32 L (N 35 L L L) L) L L)) (N 33 (N 32 L (N 35 L L
  L) L) L L)) L (N 27 L (N 18 (N 31 L (N 9 L L (N 30 (N 32 L L L) L L)) L) L L) L)) (N 26 (N 27 L
  (N 18 (N 9 L (N 31 L L L) L) L L) L) L L)) (N 31 (N 9 (N 18 L L (N 25 L L L)) L (N 18 (N 23 (N
  25 L L L) L L) L L)) L L) L))) L (N 19 (N 20 L L L) L L)) (N 17 (N 19 L L (N 18 (N 20 (N 23 (N
  30 L (N 31 (N 24 L (N 27 L L (N 9 L (N 25 L L L) L)) L) L L) L) (N 24 (N 30 (N 31 L (N 34 L L (N
  9 L (N 32 L L L) L)) L) L L) L L) L) L (N 23 (N 27 L (N 24 (N 30 L (N 31 L L L) L) L L) L) (N 24
  (N 27 L (N 30 (N 34 L L L) L L) L) L L) L)) (N 20 (N 23 (N 27 L L (N 25 L (N 24 (N 30 L (N 31 (N
  9 L (N 32 L L L) L) L L) L) L L) L)) (N 24 (N 27 L L (N 25 L (N 30 (N 32 L (N 35 L L L) L) L L)
  L)) L L) L) L (N 27 (N 23 L (N 24 L L L) L) L L)) L)) L (N 19 (N 20 L L L) L L))) L L))) (N 8 (N
  12 (N 14 L L (N 17 L L (N 18 (N 19 L L (N 20 L L L)) (N 27 (N 34 (N 35 L (N 19 (N 20 L L (N 9 L
  (N 23 L (N 24 (N 30 L L (N 33 L L L)) L L) (N 25 L (N 24 (N 26 L (N 30 L L L) L) L L) L)) L)) L
  (N 20 (N 13 (N 23 L (N 24 (N 30 L L (N 33 L L L)) L L) (N 25 L (N 24 (N 26 L (N 30 L L L) L) L
  L) L)) (N 26 L L (N 23 L (N 24 (N 25 L (N 32 L L L) L) L L) L)) L) L L)) L) L L) L L) L))) L (N
  13 (N 14 L L (N 17 (N 19 L L (N 20 L L L)) L (N 20 (N 18 L (N 27 (N 26 L (N 24 (N 31 L (N 30 (N
  33 L L L) L L) L) L L) L) L L) L) L L))) (N 26 (N 33 (N 35 L (N 14 (N 19 L L (N 20 L L (N 9 L (N
  17 (N 23 L (N 24 (N 30 L L (N 34 L L L)) L L) (N 25 L (N 24 (N 27 L (N 30 L L L) L) L L) L)) L
  L) L))) L (N 17 (N 19 L L (N 20 (N 18 (N 23 L (N 24 (N 30 L L (N 34 L L L)) L L) (N 25 L (N 24
  (N 27 L (N 30 L L L) L) L L) L)) (N 27 L L (N 23 L (N 24 (N 25 L (N 32 L L L) L) L L) L)) L) L
  L)) L (N 20 (N 27 L (N 34 L L L) L) L L))) L) L L) L L) L)) L (N 9 (N 12 (N 14 L L (N 17 (N 19 L
  L (N 20 L L L)) L (N 19 (N 18 L (N 25 L (N 24 (N 27 (N 31 L (N 32 L L L) L) L L) L L) L) L) L
  L))) L (N 14 (N 13 L (N 17 (N 19 L L (N 25 L (N 24 (N 26 (N 31 L (N 32 L L L) L) L L) L L) L)) L
  L) L) L L)) (N 12 (N 14 L L (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 18 L (N 27 (N 25 L (N 24 (N
  32 (N 34 L L L) L L) L L) L) L L) L) L L))) L (N 14 (N 13 L (N 17 (N 19 L L (N 26 (N 25 L (N 24
  (N 32 (N 33 L L L) L L) L L) L) L L)) L L) L) L L)) L))))) (S 22 (S 29 L (N 5 L (N 8 (N 12 (N 14
  L L (N 17 L L (N 30 L L (N 34 (N 18 (N 19 L L (N 20 L L L)) (N 19 (N 32 L L (N 33 L L L)) L (N
  20 (N 33 L L L) L L)) L) L L)))) L (N 14 (N 19 L L (N 32 L L (N 34 (N 9 L (N 13 L (N 18 (N 31 L
  L L) L L) (N 17 (N 27 L (N 30 L L (N 33 L L L)) L) L L)) (N 25 L (N 13 L (N 24 (N 17 (N 27 L (N
  30 L L (N 33 L L L)) L) L (N 20 (N 33 L L L) L L)) L L) (N 17 (N 30 L L L) L L)) L)) L L))) L (N
  17 (N 19 L L (N 20 (N 13 L (N 30 L L (N 26 (N 33 (N 34 L L L) L L) L L)) L) L L)) L (N 20 (N 13
  (N 18 L (N 19 (N 32 L L (N 26 L (N 33 (N 34 L L L) L L) L)) L (N 34 (N 33 L L (N 25 L (N 26 L (N
  30 (N 32 L L L) L L) L) L)) L L)) L) (N 18 (N 19 L L (N 27 L (N 34 (N 30 L L (N 33 L L L)) L L)
  L)) (N 9 (N 19 L L (N 32 L L (N 25 L (N 26 (N 27 L (N 31 (N 24 L L (N 33 (N 34 L L L) L L)) L L)
  L) L L) L))) L (N 19 (N 26 L L (N 32 L L L)) L (N 25 L (N 32 (N 30 L L (N 31 L L L)) L L) L)))
  L) L) L L)))) L (N 12 (N 14 L L (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 18 L (N 9 (N 32 L L (N
  25 L (N 26 L (N 30 (N 33 L L L) L L) L) L)) (N 13 (N 20 (N 33 L L (N 25 L (N 32 (N 34 L L L) L
  L) L)) L (N 34 (N 32 L L (N 25 L (N 26 L (N 30 (N 33 L L L) L L) L) L)) L L)) L (N 20 (N 24 (N
  25 L (N 26 L (N 30 (N 32 L L (N 33 L L L)) L (N 31 (N 32 L L L) L L)) (N 31 (N 32 L L L) L L))
  (N 26 L (N 30 (N 32 L L L) L L) L)) L (N 26 L (N 31 (N 33 L L L) L L) L)) L (N 26 L (N 33 (N 30
  L L (N 31 L L L)) L L) L))) L) L) L L))) L (N 14 (N 13 L (N 17 (N 19 L L (N 18 (N 20 (N 34 L L
  (N 25 L (N 27 L (N 32 (N 33 L L L) L L) L) L)) L (N 27 L (N 34 (N 30 L L (N 25 L (N 26 (N 32 (N
  33 L L L) L L) L L) L)) L L) L)) (N 9 (N 32 L L (N 25 L (N 27 L (N 30 (N 34 L L L) L L) L) L)) L
  (N 25 L (N 32 (N 30 L L (N 33 L L L)) L L) L)) L)) L (N 19 (N 20 L L L) L L)) (N 17 (N 19 L L (N
  18 (N 20 (N 34 L L (N 25 L (N 27 L (N 32 (N 33 L L L) L L) L) L)) L (N 27 L (N 33 (N 32 L L (N
  25 L (N 30 (N 34 L L L) L L) L)) L L) L)) (N 20 (N 25 L (N 24 (N 27 L (N 30 (N 32 L L (N 34 L L
  L)) L (N 32 (N 33 L L L) L L)) (N 32 (N 30 L L (N 33 L L L)) L L)) L (N 33 (N 26 L (N 32 L L (N
  34 L L L)) L) L L)) (N 27 L (N 24 (N 30 (N 32 L L L) L L) L L) L)) L (N 27 L (N 33 (N 32 L L (N
  25 L (N 30 (N 34 L L L) L L) L)) L L) L)) L)) L L)) L L))) (N 8 (N 12 (N 14 L L (N 17 L L (N 30
  L L (N 23 L (N 34 (N 18 (N 19 L L (N 20 L L L)) (N 19 (N 32 L L (N 33 L L L)) L (N 20 (N 33 L L
  L) L L)) L) L L) L)))) L (N 20 (N 13 (N 14 L L (N 17 L L (N 18 L (N 30 (N 23 L (N 32 L L (N 33 L
  L L)) L) L L) L))) (N 14 (N 19 L L (N 32 L L (N 27 L (N 34 (N 30 L L (N 33 L L L)) L L) L))) L
  (N 17 (N 19 L L (N 30 L L (N 23 L (N 24 (N 26 (N 33 (N 34 L L L) L L) L L) L L) L))) L (N 30 (N
  23 L (N 32 L L (N 26 (N 19 L L (N 25 L (N 27 L (N 35 L L L) L) L)) L L)) L) L L))) L) L L)) L (N
  19 (N 17 L L (N 12 (N 14 L L (N 18 L (N 30 (N 23 L (N 32 L L (N 33 L L L)) L) L L) L)) L L)) L
  L))) (N 5 L (N 8 (N 12 (N 14 L L (N 17 L L (N 18 (N 19 L L (N 20 L L L)) (N 19 (N 9 L (N 24 (N
  31 (N 13 L L (N 32 L (N 25 L L (N 26 L (N 33 L L L) L)) L)) L L) L L) (N 20 (N 13 (N 33 L (N 26
  L L (N 25 L (N 24 (N 31 L L L) L L) L)) L) (N 24 (N 26 L L (N 25 L (N 31 (N 33 L L L) L L) L)) L
  L) L) L L)) L (N 20 (N 13 (N 33 L (N 26 L L (N 23 L (N 24 (N 31 L L L) L L) L)) L) (N 24 (N 26 L
  L (N 23 L (N 25 L (N 30 L L (N 31 (N 33 L L L) L L)) L) L)) L L) L) L L)) L))) L (N 14 (N 19 L L
  (N 9 L (N 13 L (N 18 (N 24 (N 31 L L L) L L) L L) (N 17 (N 27 L (N 24 (N 30 L (N 23 L L (N 31 (N
  18 L (N 34 L L L) L) L L)) L) L L) L) L L)) (N 13 L (N 17 (N 27 L (N 24 (N 18 (N 31 L (N 30 L L
  (N 32 L L L)) L) (N 31 (N 34 L L L) L L) L) L L) L) L (N 20 (N 27 L (N 24 (N 33 (N 26 L L (N 25
  L (N 34 L (N 35 L L L) L) L)) L L) L L) L) L L)) (N 17 (N 27 L (N 30 L (N 23 L L (N 25 L (N 31
  (N 34 L (N 35 L L L) L) L L) L)) L) L) L L)))) L (N 17 (N 19 L L (N 20 (N 13 L (N 27 L (N 24 (N
  33 (N 34 L (N 18 (N 31 L L L) L L) L) L L) L L) L) L) L L)) L (N 20 (N 13 (N 18 L (N 19 (N 9 L
  (N 24 (N 31 L L L) L L) (N 24 (N 31 L (N 32 L L (N 25 L (N 26 L (N 30 (N 33 L L L) L L) L) L))
  L) (N 25 L L (N 26 L L L)) L)) L (N 24 (N 31 L (N 9 L L (N 25 L (N 32 (N 30 L L (N 26 L (N 33 (N
  34 L L L) L L) L)) L L) L)) L) (N 25 L L (N 26 L L L)) L)) L) (N 33 (N 34 L (N 31 (N 35 L (N 25
  L L (N 26 (N 27 L L L) L L)) L) L L) L) L L) L) L L)))) L (N 12 (N 14 L L (N 17 (N 19 L L (N 20
  L L L)) L (N 19 (N 18 L (N 9 (N 32 L (N 31 (N 24 L (N 13 L L (N 25 L L (N 26 L L L))) L) L L) L)
  (N 24 (N 31 (N 13 L L (N 32 L (N 25 L L (N 26 L (N 33 L L L) L)) L)) L L) L L) L) L) L L))) L (N
  14 (N 13 L (N 17 (N 19 L L (N 27 L (N 24 (N 18 (N 31 L (N 9 L L (N 25 L (N 30 (N 32 L L L) L L)
  L)) L) (N 31 (N 34 L L L) L L) L) L L) L)) L (N 19 (N 20 L L L) L L)) (N 17 (N 19 L L (N 27 L (N
  18 (N 20 (N 34 L (N 35 (N 30 L (N 31 L L L) L) L L) L) L (N 24 (N 31 L (N 30 (N 33 (N 34 L (N 35
  L L L) L) L L) L L) L) (N 26 (N 9 (N 31 L (N 30 (N 35 L L L) L L) L) L (N 25 L (N 35 (N 23 L L
  (N 30 L (N 31 L L L) L)) L L) L)) L L) L)) (N 24 (N 34 (N 30 L (N 31 L L L) L) L L) L L) L) L))
  L L)) L L))) (N 8 (N 12 (N 14 L L (N 17 L L (N 18 (N 19 L L (N 20 L L L)) (N 19 (N 9 L (N 20 (N
  23 L (N 24 (N 25 L (N 32 L L (N 26 L (N 13 (N 33 L L L) L L) L)) (N 26 L (N 33 (N 13 L L (N 31 L
  (N 32 L L L) L)) L L) L)) (N 25 L L (N 26 L L L)) L) (N 30 L (N 24 (N 25 L (N 32 L L (N 26 L (N
  13 (N 33 L L L) L L) L)) (N 26 L (N 13 (N 33 L L L) L L) L)) (N 25 L L (N 26 L L L)) L) L)) L (N
  32 L (N 25 L L (N 23 L (N 26 L (N 24 (N 31 (N 33 L L L) L L) L L) L) L)) L)) (N 20 (N 13 (N 33 L
  (N 26 L L (N 23 L (N 25 L (N 24 (N 31 L L L) L L) L) L)) L) (N 26 L L (N 23 L (N 24 (N 25 L (N
  32 L (N 31 (N 33 L L L) L L) L) L) L L) L)) L) L L)) L (N 20 (N 13 (N 33 L (N 26 L L (N 23 L (N
  25 L (N 24 (N 31 L L L) L L) L) L)) L) (N 26 L L (N 23 L (N 24 (N 25 L (N 33 (N 31 L (N 34 L L
  L) L) L L) L) L L) L)) L) L L)) L))) L (N 20 (N 13 (N 14 L L (N 17 L L (N 18 L (N 19 (N 9 L (N
  23 (N 30 L (N 24 (N 27 L (N 31 L (N 32 L L (N 26 L (N 35 L L L) L)) L) L) (N 25 L L (N 26 L L
  L)) L) L) (N 24 (N 31 L (N 32 L L (N 26 L (N 33 (N 34 L L L) L L) L)) L) (N 25 L L (N 26 L L L))
  L) L) (N 23 (N 30 L (N 24 (N 27 L (N 31 L (N 32 L L (N 25 L (N 26 L (N 35 L L L) L) L)) L) L) (N
  25 L L (N 26 L L L)) L) L) (N 24 (N 31 L (N 32 L L (N 25 L (N 26 L (N 27 (N 34 L L L) L L) L)
  L)) L) (N 25 L L (N 26 L L L)) L) L)) L (N 23 (N 30 L (N 24 (N 27 L (N 31 L (N 33 (N 34 L L L) L
  L) L) L) (N 25 L L (N 26 L L L)) L) L) (N 24 (N 31 L (N 33 (N 34 L L L) L L) L) (N 25 L L (N 26
  L L L)) L) L)) L))) (N 33 (N 34 L (N 31 (N 35 L (N 25 L L (N 27 (N 14 L L (N 26 L L L)) L L)) L)
  L L) L) L L) L) L L)) L (N 19 (N 17 L L (N 12 (N 14 L L (N 18 L (N 9 (N 32 L (N 31 (N 24 L (N 25
  L L (N 26 L L L)) L) L L) L) (N 20 (N 23 (N 30 L (N 24 (N 27 L (N 34 (N 32 L (N 35 L L L) L) L
  L) L) (N 25 L L (N 26 L L L)) L) L) (N 24 (N 25 L (N 32 (N 30 L (N 31 L L L) L) L L) (N 26 L (N
  33 (N 13 L L (N 30 L (N 31 L (N 34 L L L) L) L)) L L) L)) (N 25 L L (N 26 L L L)) L) L) L (N 23
  (N 30 L (N 24 (N 27 L (N 34 (N 32 L (N 35 L L L) L) L L) L) (N 25 L L (N 26 L L L)) L) L) (N 24
  (N 25 L (N 32 (N 30 L (N 31 L L L) L) L L) (N 26 L (N 33 (N 30 L (N 31 L (N 27 (N 35 L L L) L L)
  L) L) L L) L)) (N 25 L L (N 26 L L L)) L) L)) L) L)) L L)) L L)))) (S 29 L L (N 27 (N 5 L (N 8
  (N 12 (N 14 L L (N 17 L L (N 23 L L (N 18 (N 19 L L (N 20 L L L)) (N 19 (N 25 L L (N 26 L L L))
  L (N 20 (N 26 L L L) L L)) L)))) L (N 14 (N 19 L L (N 25 L L (N 9 L (N 13 L (N 18 (N 24 L L L) L
  L) (N 17 (N 23 L L (N 26 L L L)) L L)) (N 32 L (N 13 L (N 31 (N 17 (N 23 L L (N 26 L L L)) L (N
  20 (N 26 L L L) L L)) L L) (N 17 (N 23 L L L) L L)) L)))) L (N 17 (N 19 L L (N 20 (N 13 L (N 18
  L (N 24 L L L) L) L) L L)) L (N 20 (N 26 L L (N 23 (N 25 L L L) L L)) L L)))) L (N 12 (N 14 L L
  (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 18 L (N 25 L L (N 23 (N 26 L L L) L L)) L) L L))) L (N
  14 (N 13 L (N 17 (N 19 L L (N 23 L L (N 24 L (N 18 (N 20 L L (N 25 (N 26 L L L) L L)) L L) L)))
  L (N 19 (N 20 L L L) L L)) (N 17 (N 19 L L (N 23 L L (N 24 L (N 25 (N 26 L L L) L L) L))) L L))
  L L))) (N 8 (N 12 (N 14 L L (N 17 L L (N 23 L L (N 30 L (N 18 (N 19 L L (N 20 L L L)) (N 19 (N
  25 L L (N 26 L L L)) L (N 20 (N 26 L L L) L L)) L) L)))) L (N 20 (N 26 L L (N 23 (N 14 L L (N 25
  L L L)) L L)) L L)) L (N 19 (N 17 L L (N 12 (N 14 L L (N 18 L (N 23 (N 25 L L (N 26 L L L)) L L)
  L)) L L)) L L))) L L)) (S 29 L L L))) (S 16 L L (S 22 (S 29 L (N 20 (N 5 L (N 13 (N 14 L L (N 18
  L (N 17 L L (N 8 (N 12 (N 30 L L (N 33 L (N 31 (N 34 (N 35 L (N 24 L L (N 25 L L L)) L) L L) L
  L) L)) L (N 26 L (N 19 (N 9 L (N 32 L L (N 31 (N 24 L L (N 25 L (N 33 L (N 35 L L L) L) L)) L
  L)) (N 24 (N 25 L (N 30 (N 33 L (N 35 L L L) L) L (N 31 L (N 32 L L (N 33 (N 34 L L L) L L)) L))
  (N 31 L (N 32 L L L) L)) L (N 25 L (N 32 L (N 23 (N 30 L L (N 31 (N 35 L L L) L L)) L L) L) L)))
  L (N 34 (N 33 L (N 35 (N 24 L L (N 23 (N 25 L (N 27 L (N 30 L L (N 31 L L L)) L) L) L L)) L L)
  L) L L)) L)) L L)) L)) (N 8 (N 12 (N 14 L L (N 17 L L (N 18 L (N 30 L L (N 31 (N 33 L L L) L L))
  L))) L (N 14 (N 19 L L (N 9 L (N 18 (N 32 L L (N 27 L (N 31 (N 24 L L (N 25 L (N 33 (N 34 L (N
  35 L L L) L) L L) L)) L L) L)) L L) (N 17 (N 30 L L (N 33 (N 26 L (N 34 L (N 35 L L L) L) L) L
  L)) L (N 27 L (N 18 (N 24 (N 25 L (N 30 (N 34 L (N 35 L L L) L) L (N 31 L (N 32 L L (N 33 (N 34
  L L L) L L)) L)) (N 31 L (N 32 L L L) L)) L (N 25 L (N 32 L (N 23 (N 30 L L (N 31 (N 35 L L L) L
  L)) L L) L) L)) (N 34 (N 30 L L (N 33 L L L)) L L) L) L)))) L (N 33 (N 17 (N 19 L L (N 30 L L (N
  34 L (N 18 (N 31 (N 35 L (N 24 L L (N 25 L L L)) L) L L) L L) L))) L (N 18 (N 19 L L (N 27 L (N
  34 L (N 35 (N 24 L L (N 23 (N 25 L (N 26 L (N 30 L L (N 31 L L L)) L) L) L L)) L L) L) L)) (N 34
  L L (N 19 (N 30 L L L) L L)) L)) L L))) L (N 12 (N 14 L L (N 17 L L L)) L (N 14 (N 19 L L L) L
  L))) L) (N 13 (N 14 L L (N 18 L (N 8 (N 17 L (N 19 (N 9 L (N 25 L (N 32 L L (N 26 L (N 31 (N 24
  L L (N 23 (N 30 L L L) L L)) L L) L)) (N 26 L (N 24 (N 27 (N 23 L L (N 31 L L L)) L L) L L) L))
  (N 31 (N 24 L (N 25 L L (N 26 L L L)) L) L L)) L (N 25 L (N 23 (N 30 L L (N 24 (N 31 L L L) L
  L)) L (N 24 (N 31 L L L) L L)) (N 26 L (N 24 (N 9 L (N 27 (N 23 L L (N 31 L L L)) L L) L) L L)
  L))) (N 19 (N 9 L (N 25 L (N 32 L L (N 26 L (N 24 (N 31 L (N 33 (N 34 L L L) L L) L) L (N 30 (N
  23 L (N 33 L L L) L) L L)) L)) (N 26 L (N 24 (N 27 (N 35 L (N 32 L L (N 34 L L L)) L) (N 30 (N
  33 L (N 35 L L L) L) L (N 31 L (N 32 L L (N 33 (N 34 L L L) L L)) L)) L) L L) L)) (N 24 (N 31 L
  (N 32 L L (N 25 L (N 26 L (N 33 (N 34 L L L) L L) L) L)) L) (N 25 L L (N 26 L L L)) L)) L (N 25
  L (N 24 (N 9 L (N 26 L (N 27 (N 35 L (N 23 L L (N 12 (N 30 L L L) L L)) L) (N 34 (N 35 L L L) L
  L) L) (N 32 (N 30 L L (N 31 L (N 33 (N 34 L L L) L L) L)) L L)) (N 31 L (N 32 (N 30 L L (N 33 (N
  34 L L L) L L)) L L) L)) L (N 30 (N 23 L (N 12 L L (N 26 L (N 33 L L L) L)) L) L L)) (N 26 L (N
  24 (N 9 L (N 27 (N 35 L (N 32 (N 34 L L L) L L) L) (N 34 (N 33 L (N 35 L L L) L) L L) L) L) L L)
  L)))) (N 17 L (N 12 (N 19 (N 23 (N 30 L L (N 31 (N 24 L (N 25 L L (N 26 L L L)) L) L L)) L (N 26
  L (N 24 (N 31 L L L) L L) L)) L (N 23 (N 30 L L (N 31 (N 24 L (N 25 L L (N 26 L L L)) L) L L)) L
  (N 26 L (N 24 (N 31 L L L) L L) L))) L (N 26 L (N 19 (N 23 (N 24 (N 27 L L (N 25 L (N 35 L L L)
  L)) L (N 25 L (N 9 (N 31 L L L) L L) L)) L (N 24 (N 31 L L L) L L)) L (N 23 (N 24 (N 27 L L (N
  25 L (N 35 L L L) L)) L (N 25 L (N 9 (N 31 L L L) L L) L)) L (N 24 (N 31 L L L) L L))) L)) (N 19
  (N 25 L (N 35 (N 30 L L (N 23 (N 24 L L L) L L)) L L) (N 26 L (N 24 (N 9 L (N 31 L L (N 23 (N 27
  L (N 30 (N 32 L L L) L L) L) L L)) (N 31 L (N 32 (N 30 L L (N 34 L L L)) L L) L)) L L) L)) L (N
  25 L (N 35 (N 30 L L (N 23 (N 24 L L L) L L)) L L) (N 26 L (N 24 (N 9 L (N 31 L L (N 23 (N 27 L
  (N 30 (N 32 L L L) L L) L) L L)) L) L L) L)))) L) L)) (N 14 (N 19 L L (N 8 (N 9 L (N 12 L (N 18
  (N 25 L (N 32 L L (N 27 L (N 31 (N 24 L L (N 23 (N 30 L L L) L L)) L L) L)) (N 26 (N 27 L (N 24
  (N 23 L L (N 31 L L L)) L L) L) L L)) (N 24 (N 25 L (N 32 L L (N 27 L (N 31 (N 33 (N 34 L L L) L
  L) L L) L)) (N 26 (N 27 L (N 23 L L (N 31 (N 34 L L L) L L)) L) L L)) L (N 25 L (N 23 (N 30 L L
  L) L L) L)) L) (N 18 (N 25 L (N 32 L L (N 27 L (N 24 (N 31 L (N 33 (N 34 L L L) L L) L) L (N 30
  (N 23 L (N 34 L L L) L) L L)) L)) (N 27 L (N 24 (N 26 (N 35 L (N 32 L L (N 33 L L L)) L) (N 30
  (N 34 L (N 35 L L L) L) L (N 31 L (N 32 L L (N 33 (N 34 L L L) L L)) L)) L) L L) L)) (N 24 (N 25
  L (N 32 L L (N 27 L (N 31 (N 34 (N 17 L L (N 30 L L L)) L L) L L) L)) (N 27 L (N 34 (N 30 L L (N
  17 (N 31 L L L) L L)) L L) L)) L (N 25 L (N 30 (N 23 L (N 17 L L (N 27 L (N 34 L L L) L)) L) L
  L) L)) L)) (N 12 L (N 31 (N 35 L (N 18 (N 24 L (N 25 L L (N 27 L L L)) L) (N 24 (N 25 L (N 32 L
  L (N 27 L (N 33 (N 34 L L L) L L) L)) (N 26 (N 27 L (N 32 L L L) L) L L)) (N 25 L L (N 27 L L
  L)) L) L) L) L L) (N 18 (N 24 (N 31 L (N 32 L L (N 25 L (N 27 L (N 33 (N 34 L L L) L L) L) L))
  L) (N 25 L L (N 27 L L L)) L) (N 24 (N 25 L (N 27 L (N 17 (N 30 L L (N 23 L (N 26 (N 35 L L L) L
  L) L)) L (N 30 (N 34 L L L) L L)) (N 32 L (N 23 (N 35 L L L) L L) L)) (N 27 L (N 32 L (N 31 (N
  35 L L L) L L) L) L)) (N 25 L L (N 27 L L L)) L) L))) (N 12 L (N 17 (N 18 (N 23 (N 30 L L (N 31
  (N 24 L (N 25 L L (N 27 L L L)) L) L L)) L (N 26 (N 27 L (N 24 (N 31 L L L) L L) L) L L)) (N 23
  (N 30 L L (N 31 (N 33 (N 26 L L (N 25 L (N 35 L L L) L)) L L) L L)) L (N 26 (N 27 L (N 24 (N 31
  (N 33 L L (N 30 (N 32 L (N 35 L L L) L) L L)) L L) L L) L) L L)) L) L (N 27 L (N 18 (N 23 (N 24
  (N 26 L L (N 25 L (N 35 L L L) L)) L (N 25 L (N 9 (N 31 L L L) L L) L)) L (N 24 (N 31 L L L) L
  L)) (N 34 (N 33 L L (N 30 (N 32 L (N 35 L L L) L) L L)) L L) L) L)) (N 18 (N 25 L (N 35 (N 30 L
  L (N 23 (N 24 L L L) L L)) L L) (N 27 L (N 24 (N 9 L (N 31 L L (N 23 (N 26 L (N 30 (N 32 L L L)
  L L) L) L L)) (N 31 L (N 32 (N 30 L L (N 33 L L L)) L L) L)) L L) L)) (N 25 L (N 35 (N 30 L L (N
  23 (N 24 L L L) L L)) L L) (N 27 L (N 24 (N 34 (N 17 (N 30 L L (N 23 (N 26 L (N 33 L L L) L) L
  L)) L (N 23 (N 26 L (N 30 (N 33 L L (N 32 L (N 35 L L L) L)) L L) L) L L)) L L) L L) L)) L)) L))
  L (N 8 (N 18 (N 19 L L (N 12 L (N 25 L (N 23 (N 30 L L (N 24 (N 31 L L L) L L)) L (N 24 (N 31 L
  L L) L L)) (N 26 (N 27 L (N 24 (N 9 L (N 23 L L (N 31 L L L)) L) L L) L) L L)) (N 25 L (N 24 (N
  9 L (N 26 (N 35 L (N 33 (N 32 L L (N 34 L L L)) L L) L) (N 33 (N 35 L (N 27 L L (N 34 L L L)) L)
  L L) L) (N 31 L (N 32 (N 30 L L (N 33 (N 34 L L L) L L)) L L) L)) L (N 30 (N 23 L (N 17 L L (N
  27 L (N 34 L L L) L)) L) L L)) (N 27 L (N 24 (N 9 L (N 26 (N 35 L (N 32 (N 33 L L L) L L) L) (N
  33 (N 34 L (N 35 L L L) L) L L) L) L) L L) L)))) (N 19 (N 9 L (N 17 L (N 24 (N 25 L (N 32 L L (N
  26 L (N 31 (N 33 (N 34 L L L) L L) L L) L)) (N 26 L (N 27 (N 23 L L (N 31 (N 33 L L L) L L)) L
  L) L)) L (N 25 L (N 23 (N 30 L L L) L L) L)) (N 24 (N 25 L (N 32 L L (N 26 L (N 31 (N 33 (N 12 L
  L (N 30 L L L)) L L) L L) L)) (N 26 L (N 33 (N 30 L L (N 12 (N 31 L L L) L L)) L L) L)) L (N 25
  L (N 30 (N 23 L (N 12 L L (N 26 L (N 33 L L L) L)) L) L L) L))) (N 17 L (N 31 (N 35 L (N 24 (N
  25 L (N 32 L L (N 26 L (N 33 (N 34 L L L) L L) L)) (N 26 L (N 32 L L L) L)) (N 25 L L (N 26 L L
  L)) L) L) L L) (N 24 (N 25 L (N 26 L (N 12 (N 30 L L (N 23 L (N 27 (N 35 L L L) L L) L)) L (N 30
  (N 33 L L L) L L)) (N 32 L (N 23 (N 35 L L L) L L) L)) (N 26 L (N 32 L (N 31 (N 35 L L L) L L)
  L) L)) (N 25 L L (N 26 L L L)) L))) L (N 25 L (N 24 (N 30 (N 35 L (N 32 L L (N 33 (N 34 L L L) L
  L)) L) L (N 31 (N 35 L (N 32 L L (N 9 L (N 33 (N 34 L L L) L L) L)) L) (N 33 (N 34 L L L) L L)
  L)) L (N 30 (N 23 L (N 12 L L (N 17 L L (N 32 L L (N 35 L (N 26 (N 27 L L L) L L) L)))) L) L L))
  (N 9 (N 32 L (N 24 (N 31 L L (N 30 (N 23 L (N 35 L (N 26 (N 27 L L L) L L) L) L) L L)) (N 26 (N
  27 L L L) L L) L) L) (N 24 (N 26 (N 27 L (N 34 (N 31 L L (N 23 L (N 12 L L (N 30 (N 17 L L (N 32
  L (N 35 L L L) L)) L L)) L)) L L) L) (N 33 (N 34 L (N 27 (N 35 L L L) L L) L) L L) L) L L) L)))
  L) (N 18 (N 19 L L (N 12 L (N 17 (N 23 (N 30 L L (N 31 (N 24 L (N 25 L L (N 27 L L L)) L) L L))
  L (N 26 (N 27 L (N 24 (N 31 L L L) L L) L) L L)) L (N 27 L (N 23 (N 24 (N 26 L L (N 25 L (N 35 L
  L L) L)) L (N 25 L (N 9 (N 31 L L L) L L) L)) L (N 24 (N 31 L L L) L L)) L)) (N 25 L (N 35 (N 30
  L L (N 23 (N 24 L L L) L L)) L L) (N 27 L (N 24 (N 9 L (N 31 L L (N 23 (N 26 L (N 30 (N 32 L L
  L) L L) L) L L)) L) L L) L)))) (N 19 (N 17 L (N 12 (N 23 (N 30 L L (N 31 (N 33 L (N 26 L L (N 25
  L (N 32 L L L) L)) L) L L)) L (N 26 L (N 24 (N 27 (N 31 (N 33 L L (N 25 L (N 32 L L L) L)) L L)
  L L) L L) L)) L (N 26 L (N 33 (N 34 L L (N 30 (N 32 L (N 35 L L L) L) L L)) L L) L)) (N 25 L (N
  35 (N 30 L L (N 23 (N 24 L L L) L L)) L L) (N 26 L (N 24 (N 33 (N 12 (N 30 L L (N 23 (N 27 L (N
  34 L L L) L) L L)) L (N 23 (N 27 L (N 30 (N 34 L L (N 32 L (N 35 L L L) L)) L L) L) L L)) L L) L
  L) L))) L (N 25 L (N 35 (N 30 L L (N 24 (N 23 L L (N 26 L (N 12 (N 17 L (N 27 L L L) L) L L) L))
  L L)) L L) (N 9 (N 24 (N 26 (N 27 L (N 23 L L (N 31 L (N 12 L L (N 17 (N 30 (N 32 L L L) L L) L
  L)) L)) L) (N 33 (N 34 L (N 27 (N 35 L L L) L L) L) L L) L) (N 26 (N 27 L L L) L L) L) (N 24 (N
  32 (N 30 L L (N 31 L L L)) L L) L L) L))) L) L)) L)) L L) L) (S 29 L (N 20 (N 35 (N 5 L (N 13 (N
  14 L L (N 18 L (N 17 L L (N 8 (N 12 (N 23 L L (N 26 L (N 24 (N 34 L L L) L L) L)) L (N 19 (N 9 L
  (N 25 L L (N 24 (N 26 L (N 27 (N 23 L L (N 30 L L L)) L L) L) L L)) (N 23 (N 26 L (N 30 L L (N
  34 L L L)) L) L (N 27 (N 30 L L L) L L))) L (N 27 (N 34 L L L) L L))) L L)) L)) (N 8 (N 12 (N 14
  L L (N 17 L L (N 18 L (N 23 L L (N 24 (N 26 L L L) L L)) L))) L (N 14 (N 19 L L (N 9 L (N 18 (N
  25 L L (N 24 (N 26 (N 23 L L (N 33 L L L)) L L) L L)) L L) (N 17 (N 23 L L (N 26 (N 33 L L L) L
  L)) L (N 18 (N 23 (N 27 L (N 30 L L (N 33 L L L)) L) L (N 26 (N 30 L L L) L L)) (N 27 (N 34 L L
  L) L L) L)))) L (N 26 (N 33 L L L) L L))) L (N 12 (N 14 L L (N 17 L L L)) L (N 14 (N 19 L L L) L
  L))) L) (N 13 (N 14 L L (N 18 L (N 8 (N 17 L (N 19 (N 9 L (N 23 (N 30 L L (N 31 L L L)) L (N 24
  (N 31 L L L) L L)) (N 24 (N 31 L L L) L L)) L (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L L L)
  L L))) (N 19 (N 9 L (N 23 (N 30 L L (N 12 L (N 31 L (N 34 L L L) L) L)) L (N 30 (N 12 L (N 24 L
  (N 27 L L L) L) L) L L)) (N 23 (N 30 L L (N 12 L (N 31 L (N 34 L L L) L) L)) L (N 30 (N 12 L (N
  24 L (N 27 L L L) L) L) L L))) L (N 23 (N 30 L L (N 12 L (N 31 L (N 27 (N 34 L L L) L L) L) L))
  L (N 30 (N 12 L (N 24 L (N 26 (N 27 L L L) L L) L) L) L L)))) (N 17 L (N 12 (N 19 (N 23 (N 30 L
  L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) L (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L L L)
  L L))) L (N 19 (N 23 (N 26 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 30 L L L) L L)) L (N 23 (N 26
  L (N 30 L L (N 31 L L L)) L) L (N 24 (N 30 L L L) L L)))) (N 19 (N 23 (N 30 L L (N 31 L (N 27 (N
  34 L L L) L L) L)) L (N 30 (N 24 L (N 26 (N 27 L L L) L L) L) L L)) L (N 23 (N 30 L L (N 31 L (N
  27 (N 34 L L L) L L) L)) L (N 30 (N 24 L (N 26 (N 27 L L L) L L) L) L L)))) L) L)) (N 14 (N 19 L
  L (N 8 (N 9 L (N 12 L (N 18 (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) (N 23 (N 30
  L L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) L) (N 18 (N 23 (N 30 L L (N 17 L (N 31 L (N 33 L L
  L) L) L)) L (N 30 (N 17 L (N 24 L (N 26 L L L) L) L) L L)) (N 23 (N 30 L L (N 31 L L L)) L (N 24
  (N 30 L L L) L L)) L)) (N 12 L (N 24 (N 31 L L L) L L) (N 18 (N 23 (N 30 L L (N 17 L (N 31 L (N
  33 L L L) L) L)) L (N 30 (N 17 L (N 24 L (N 26 L L L) L) L) L L)) (N 23 (N 30 L L (N 17 L (N 31
  L L L) L)) L (N 30 (N 17 L (N 24 L L L) L) L L)) L))) (N 12 L (N 17 (N 18 (N 23 (N 30 L L (N 31
  L L L)) L (N 24 (N 31 L L L) L L)) (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) L) L
  (N 18 (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 30 L L L) L L)) (N 23 (N 30 L L (N 31
  L L L)) L (N 24 (N 30 L L L) L L)) L)) (N 18 (N 23 (N 30 L L (N 31 L (N 26 (N 33 L L L) L L) L))
  L (N 30 (N 24 L (N 26 (N 27 L L L) L L) L) L L)) (N 23 (N 30 L L (N 31 L (N 17 (N 33 L L L) L L)
  L)) L (N 30 (N 24 L (N 17 (N 26 L L L) L L) L) L L)) L)) L)) L (N 8 (N 18 (N 19 L L (N 12 L (N
  23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) (N 23 (N 30 L L (N 17 L (N 31 L (N 26 (N
  33 L L L) L L) L) L)) L (N 30 (N 17 L (N 24 L (N 26 (N 27 L L L) L L) L) L) L L)))) (N 19 (N 9 L
  (N 17 L (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) (N 23 (N 30 L L (N 31 L L L)) L
  (N 24 (N 30 L L L) L L))) (N 17 L (N 24 (N 31 L L L) L L) (N 23 (N 30 L L (N 12 L (N 31 L L L)
  L)) L (N 30 (N 12 L (N 24 L L L) L) L L)))) L (N 23 (N 30 L L (N 31 L (N 12 L L (N 17 L L L))
  L)) L (N 24 (N 30 L L (N 31 L (N 12 (N 17 L L L) L L) L)) (N 26 (N 27 L L L) L L) L))) L) (N 18
  (N 19 L L (N 12 L (N 17 (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) L (N 23 (N 27 L
  (N 30 L L (N 31 L L L)) L) L (N 24 (N 30 L L L) L L))) (N 23 (N 30 L L (N 31 L (N 26 (N 33 L L
  L) L L) L)) L (N 30 (N 24 L (N 26 (N 27 L L L) L L) L) L L)))) (N 19 (N 17 L (N 12 (N 23 (N 30 L
  L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) L (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 30 L L L)
  L L))) (N 23 (N 30 L L (N 31 L (N 12 (N 34 L L L) L L) L)) L (N 30 (N 24 L (N 12 (N 27 L L L) L
  L) L) L L))) L (N 23 (N 30 L L (N 31 L (N 24 (N 26 L L (N 12 (N 34 L L L) L L)) L L) L)) L (N 24
  (N 30 L L (N 31 L (N 12 (N 17 L L L) L L) L)) (N 26 (N 27 L L L) L L) L))) L) L)) L)) L L) L L)
  L) L))) (S 11 L (S 16 L L (S 22 (S 29 (N 35 L (N 5 L (N 8 (N 12 (N 14 L L (N 17 L L (N 18 (N 19
  L L (N 20 L L L)) (N 19 (N 20 (N 23 L (N 30 L L (N 32 L L (N 33 L L L))) (N 24 (N 25 L (N 30 L L
  (N 32 L L (N 33 L L L))) (N 26 L (N 33 L L L) L)) (N 25 L L (N 26 L L L)) L)) L (N 9 (N 23 L (N
  30 L L (N 32 L L L)) (N 25 L (N 24 (N 30 L L (N 32 L L L)) L L) L)) (N 25 L L (N 23 L (N 33 L L
  L) L)) L)) L (N 20 (N 13 (N 23 L (N 30 L L (N 33 L L L)) (N 26 L (N 24 (N 30 L L (N 33 L L L)) L
  L) L)) (N 26 L L (N 23 L (N 32 L L L) L)) L) L L)) L))) L (N 14 (N 13 L (N 17 (N 19 L L (N 18 (N
  20 (N 23 L (N 30 L L (N 26 (N 33 L L L) L L)) (N 26 (N 33 L L L) L L)) L (N 27 L (N 34 L L L)
  L)) (N 9 (N 20 (N 23 L (N 30 L L (N 26 (N 33 L L L) L L)) (N 26 (N 33 L L L) L L)) L (N 27 L (N
  34 L L L) L)) L (N 20 (N 23 L (N 30 L L (N 26 (N 33 L L L) L L)) (N 26 (N 33 L L L) L L)) L (N
  27 L (N 34 L L L) L))) L)) L (N 20 (N 19 L L (N 18 (N 27 L (N 34 L L L) L) (N 9 (N 24 (N 27 L (N
  31 L L (N 32 L L L)) L) L (N 25 L (N 32 L L (N 31 (N 34 L L L) L L)) L)) L (N 24 (N 25 L (N 32 L
  L (N 31 (N 33 (N 34 L L L) L L) L L)) (N 26 (N 27 L (N 32 L L L) L) L L)) L (N 25 L (N 32 L L L)
  L))) L)) L L)) (N 17 (N 19 L L (N 18 (N 20 (N 23 L (N 30 L L (N 32 L L (N 27 L (N 34 L L L) L)))
  (N 25 L (N 30 L L (N 32 L L (N 34 L L L))) (N 27 L (N 34 L L L) L))) L (N 27 L (N 34 L L L) L))
  (N 20 (N 23 L (N 30 L L (N 32 L L (N 34 L L L))) (N 25 L (N 30 L L (N 32 L L (N 34 L L L))) (N
  27 L (N 34 L L L) L))) L (N 27 L (N 34 L L L) L)) L)) L L)) L (N 17 (N 19 L L (N 20 (N 13 L (N
  18 (N 23 L (N 30 L L (N 26 (N 32 L L (N 25 L (N 27 L L L) L)) L L)) (N 26 (N 27 L (N 32 L L (N
  34 L L L)) L) L L)) (N 9 (N 23 L (N 30 L L (N 34 L L L)) (N 26 (N 27 L (N 30 L L (N 34 L L L))
  L) L L)) L (N 25 L (N 32 L L L) L)) L) L) L L)) L (N 20 (N 13 (N 18 L (N 19 (N 25 L (N 32 L L (N
  33 L L L)) (N 26 L (N 33 L L L) L)) L (N 25 L (N 32 L L (N 33 L L L)) (N 26 L (N 32 L L L) L)))
  L) (N 18 (N 19 L L (N 27 L (N 34 L L L) L)) (N 9 (N 19 (N 24 (N 26 L L (N 25 L (N 32 L L L) L))
  L (N 23 (N 26 L L (N 25 L (N 30 L L L) L)) (N 32 L L (N 26 (N 34 L L L) L L)) L)) L (N 24 (N 31
  L L (N 32 L (N 25 L L (N 26 (N 27 L L L) L L)) L)) L (N 25 L (N 32 L L (N 26 (N 34 L L L) L L))
  L))) L (N 19 (N 24 (N 25 L (N 32 L L (N 26 (N 34 L L L) L L)) (N 26 (N 27 L (N 32 L L L) L) L
  L)) L (N 25 L (N 32 L L L) L)) L (N 25 L (N 32 L L L) L))) L) L) L L)))) L (N 12 (N 14 (N 9 L (N
  17 (N 20 L L (N 18 (N 19 (N 23 L (N 30 L L (N 25 (N 32 L L L) L L)) (N 25 (N 32 L L L) L L)) L
  (N 27 L (N 34 L L L) L)) (N 13 (N 19 (N 23 L (N 30 L L (N 25 (N 32 L L L) L L)) (N 25 (N 32 L L
  L) L L)) L (N 27 L (N 34 L L L) L)) L (N 19 (N 23 L (N 30 L L (N 25 (N 32 L L L) L L)) (N 25 (N
  32 L L L) L L)) L (N 27 L (N 34 L L L) L))) L)) L (N 19 (N 20 L L (N 18 (N 27 L (N 34 L L L) L)
  (N 13 (N 24 (N 27 L (N 31 L L (N 33 L L L)) L) L (N 26 L (N 33 L L (N 31 (N 34 L L L) L L)) L))
  L (N 24 (N 25 (N 27 L (N 34 L L L) L) L (N 26 L (N 30 (N 34 L L L) L L) L)) L (N 26 L (N 33 L L
  L) L))) L)) L L)) (N 17 (N 20 L L (N 18 (N 19 (N 23 L (N 30 L L (N 32 (N 25 L (N 26 L L (N 27 L
  L L)) L) L L)) (N 25 (N 32 L (N 26 L L (N 27 L L L)) L) (N 30 L L (N 32 (N 33 L L (N 34 L L L))
  L L)) L)) L (N 27 L (N 34 L L L) L)) (N 19 (N 23 L (N 30 L L (N 32 (N 25 L (N 26 L L (N 27 L L
  L)) L) L L)) (N 25 (N 32 L (N 26 L L (N 27 L L L)) L) (N 30 L L (N 32 (N 33 L L (N 34 L L L)) L
  L)) L)) L (N 27 L (N 34 L L L) L)) L)) L L)) L (N 17 (N 20 L L (N 19 (N 9 L (N 18 (N 23 L (N 30
  L L (N 25 (N 32 (N 33 L L (N 26 L (N 27 L L L) L)) L L) L L)) (N 25 (N 27 L (N 32 (N 33 L L (N
  34 L L L)) L L) L) L L)) (N 13 (N 23 L (N 30 L L (N 34 L L L)) (N 25 (N 27 L (N 30 L L (N 34 L L
  L)) L) L L)) L (N 26 L (N 33 L L L) L)) L) L) L L)) L (N 19 (N 9 (N 18 L (N 20 (N 25 L (N 32 L L
  (N 33 L L L)) (N 26 L (N 32 L L L) L)) L (N 25 L (N 32 L L (N 33 L L L)) (N 26 L (N 32 L L L)
  L))) L) (N 18 (N 20 L L (N 27 L (N 34 L L L) L)) (N 13 (N 20 (N 24 (N 25 L L (N 26 L (N 33 L L
  L) L)) L (N 23 (N 25 L L (N 26 L (N 30 L L L) L)) (N 33 L L (N 25 (N 34 L L L) L L)) L)) L (N 24
  (N 31 L L (N 33 L (N 26 L L (N 25 (N 27 L L L) L L)) L)) L (N 26 L (N 33 L L (N 25 (N 34 L L L)
  L L)) L))) L (N 20 (N 24 (N 25 (N 23 L (N 33 L L (N 34 L L L)) (N 27 L (N 34 L L L) L)) L (N 26
  L (N 33 L L L) L)) L (N 26 L (N 33 L L L) L)) L (N 26 L (N 33 L L L) L))) L) L) L L))) L (N 14
  (N 17 (N 18 (N 19 (N 20 L L (N 9 L (N 25 (N 32 L L (N 34 L (N 26 L L (N 27 L L L)) L)) L (N 27 L
  (N 34 L L (N 32 (N 33 L L L) L L)) L)) (N 27 L (N 34 L L (N 32 (N 33 L L L) L L)) (N 34 L (N 25
  (N 26 L L L) L L) L)))) L (N 20 (N 13 L (N 26 (N 33 L L (N 34 L (N 25 L L (N 27 L L L)) L)) L (N
  27 L (N 34 L L (N 32 (N 33 L L L) L L)) L)) (N 27 L (N 34 L L (N 32 (N 33 L L L) L L)) (N 34 L
  (N 25 (N 26 L L L) L L) L))) L (N 27 L (N 34 L L L) L))) (N 19 (N 20 L L (N 9 L (N 13 (N 24 (N
  31 L L (N 33 L (N 26 L L (N 27 L L L)) L)) L (N 26 L (N 33 L L (N 34 L L L)) L)) L (N 24 (N 25
  (N 26 L (N 33 L L L) L) L (N 27 L (N 30 (N 33 L L L) L L) L)) L (N 25 (N 26 L (N 33 L L L) L) L
  L))) (N 27 L (N 34 L L (N 32 (N 33 L L L) L L)) (N 34 L (N 25 (N 26 L L L) L L) L)))) L (N 20 (N
  13 L (N 9 (N 24 (N 31 L L (N 32 L (N 25 L L (N 27 L L L)) L)) L (N 25 L (N 32 L L (N 34 L L L))
  L)) L (N 24 (N 25 (N 26 L L (N 23 L (N 27 L (N 30 (N 32 L L L) L L) L) L)) (N 32 (N 26 L L (N 30
  L L L)) L L) L) L (N 26 (N 25 L (N 32 L L L) L) L L))) (N 27 L (N 34 L L (N 32 (N 33 L L L) L
  L)) (N 34 L (N 25 (N 26 L L L) L L) L))) L (N 27 L (N 34 L L L) L))) L) L (N 19 (N 20 L L L) L
  L)) L L))) (N 8 (N 12 (N 14 L L (N 17 L L (N 18 (N 19 L L (N 20 L L L)) (N 19 (N 20 (N 23 L (N
  30 L L (N 32 L L (N 33 L L L))) (N 30 L (N 25 L L (N 26 L L L)) L)) L (N 9 (N 23 L (N 30 L L (N
  32 L L L)) (N 25 L (N 30 L L L) L)) (N 25 L L (N 23 L (N 33 L L L) L)) L)) L (N 20 (N 13 (N 23 L
  (N 30 L L (N 33 L L L)) (N 26 L (N 30 L L L) L)) (N 26 L L (N 23 L (N 32 L L L) L)) L) L L))
  L))) L (N 20 (N 13 (N 14 L L (N 17 L L (N 18 L (N 19 (N 23 (N 30 L (N 25 L L (N 26 L L L)) L) (N
  30 (N 32 L L (N 33 L L L)) L L) L) L (N 23 (N 30 L (N 25 L L (N 26 L L L)) L) (N 30 (N 32 L L (N
  33 L L L)) L L) L)) L))) (N 14 (N 19 L L (N 17 (N 18 (N 23 L (N 30 L L (N 24 (N 26 (N 33 L L L)
  L L) L L)) (N 26 (N 33 L L L) L L)) (N 23 L (N 30 L L (N 24 (N 26 (N 33 L L L) L L) L L)) (N 26
  (N 33 L L L) L L)) L) L (N 18 (N 27 L (N 34 L L L) L) (N 23 (N 27 L (N 30 L (N 25 L L (N 24 (N
  26 L L L) L L)) L) L) (N 30 (N 32 L L (N 33 (N 26 L L (N 25 L (N 27 L L L) L)) L L)) L L) L)
  L))) L (N 17 (N 19 L L (N 18 (N 23 L (N 30 L L (N 24 (N 26 (N 31 L (N 34 L L L) L) L L) L L)) (N
  26 (N 27 L (N 24 (N 30 L (N 31 L L L) L) L L) L) L L)) (N 23 L (N 30 L L (N 24 (N 26 (N 32 L L
  (N 25 L (N 27 L L L) L)) L L) L L)) (N 26 (N 27 L (N 24 (N 30 L (N 25 L L (N 32 L L L)) L) L L)
  L) L L)) L)) L (N 18 (N 19 L L (N 27 L (N 34 L L L) L)) (N 19 (N 23 (N 26 L L (N 25 L (N 30 L L
  L) L)) (N 30 (N 32 L L (N 33 L L L)) L L) L) L (N 23 (N 30 L (N 25 L L (N 26 (N 24 L (N 27 L L
  L) L) L L)) L) (N 30 (N 32 L L (N 25 L (N 9 (N 26 (N 27 L L L) L L) L L) L)) L L) L)) L))) L) L
  L)) L (N 19 (N 9 (N 17 L L (N 12 (N 14 L L (N 18 L (N 20 (N 23 (N 30 L (N 25 L L (N 26 L L L))
  L) (N 30 (N 32 L L (N 33 L L L)) L L) L) L (N 23 (N 30 L (N 25 L L (N 26 L L L)) L) (N 30 (N 32
  L L (N 33 L L L)) L L) L)) L)) L L)) (N 12 (N 14 (N 20 L L (N 17 (N 18 (N 23 L (N 30 L L (N 24
  (N 25 (N 32 L L L) L L) L L)) (N 25 (N 32 L L L) L L)) (N 23 L (N 30 L L (N 24 (N 25 (N 32 L L
  L) L L) L L)) (N 25 (N 32 L L L) L L)) L) L (N 18 (N 27 L (N 34 L L L) L) (N 23 (N 27 L (N 30 L
  (N 26 L L (N 24 (N 25 L L L) L L)) L) L) (N 30 (N 33 L L (N 32 (N 25 L L (N 26 L (N 27 L L L)
  L)) L L)) L L) L) L))) L (N 17 (N 20 L L (N 18 (N 23 L (N 30 L L (N 24 (N 25 (N 31 L (N 34 L L
  L) L) L L) L L)) (N 25 (N 27 L (N 24 (N 30 L (N 31 L L L) L) L L) L) L L)) (N 23 L (N 30 L L (N
  24 (N 25 (N 32 (N 33 L L (N 26 L (N 27 L L L) L)) L L) L L) L L)) (N 25 (N 27 L (N 24 (N 30 L (N
  26 L L (N 33 L L L)) L) L L) L) L L)) L)) L (N 18 (N 20 L L (N 27 L (N 34 L L L) L)) (N 20 (N 23
  (N 25 L L (N 26 L (N 30 L L L) L)) (N 30 (N 32 L L (N 33 L L L)) L L) L) L (N 23 (N 30 L (N 26 L
  L (N 25 (N 24 L (N 27 L L L) L) L L)) L) (N 30 (N 33 L L (N 25 (N 26 L (N 27 L L L) L) L L)) L
  L) L)) L))) L (N 14 (N 20 L L L) L L)) L) L L))) L) L (N 5 L (N 8 (N 12 (N 14 L L (N 17 L L (N
  18 (N 19 L L (N 20 L L L)) (N 19 (N 20 (N 23 L (N 24 (N 30 L L (N 25 L (N 32 (N 9 L L (N 31 L (N
  34 L L L) L)) L L) (N 26 L (N 33 (N 13 L L (N 31 L (N 34 L L L) L)) L L) L))) L L) (N 24 (N 25 L
  (N 9 (N 31 L (N 13 L L (N 32 L L L)) L) L (N 13 (N 31 L (N 33 L L L) L) (N 26 L L (N 31 (N 32 L
  L L) L L)) L)) (N 26 L (N 33 (N 13 L L (N 31 L (N 34 L L L) L)) L L) L)) (N 25 L L (N 26 L L L))
  L)) L (N 9 (N 32 L (N 25 L L (N 23 L (N 24 (N 31 L L L) L L) L)) L) (N 24 (N 25 L L (N 23 L (N
  26 L (N 30 L L (N 31 (N 32 L L L) L L)) L) L)) L L) L)) L (N 20 (N 13 (N 33 L (N 26 L L (N 23 L
  (N 24 (N 31 L L L) L L) L)) L) (N 24 (N 26 L L (N 23 L (N 25 L (N 30 L L (N 31 (N 32 L L L) L
  L)) L) L)) L L) L) L L)) L))) L (N 14 (N 13 L (N 17 (N 19 L L (N 27 L (N 24 (N 18 (N 31 L (N 9 L
  L (N 30 L L (N 20 (N 34 L L L) L L))) L) (N 31 (N 34 L L L) L L) L) L L) L)) L (N 20 (N 19 L L
  (N 33 (N 26 L L (N 25 L (N 24 (N 32 L L (N 34 L (N 31 (N 35 L L L) L L) L)) L L) L)) L L)) L L))
  (N 17 (N 19 L L (N 27 L (N 30 L (N 23 L L (N 31 (N 34 L (N 35 L L L) L) L L)) L) L)) L L)) L (N
  17 (N 19 L L (N 20 (N 13 L (N 27 L (N 24 (N 33 (N 34 L (N 18 (N 31 L L L) L L) L) L L) L L) L)
  L) L L)) L (N 20 (N 13 (N 18 L (N 19 (N 24 (N 31 L (N 9 L L (N 33 (N 34 L L L) L L)) L) (N 25 L
  L (N 26 L L L)) L) L (N 24 (N 31 L (N 9 L L (N 25 L (N 32 (N 30 L L (N 26 L (N 33 (N 34 L L L) L
  L) L)) L L) L)) L) (N 25 L L (N 26 L L L)) L)) L) (N 33 (N 34 L (N 31 (N 35 L (N 25 L L (N 26 (N
  27 L L L) L L)) L) L L) L) L L) L) L L)))) L (N 12 (N 14 (N 9 L (N 17 (N 20 L L (N 27 L (N 24 (N
  18 (N 31 L (N 13 L L (N 30 L L (N 19 (N 34 L L L) L L))) L) (N 31 (N 34 L L L) L L) L) L L) L))
  L (N 19 (N 20 L L (N 32 (N 25 L L (N 26 L (N 24 (N 33 L L (N 34 L (N 31 (N 35 L L L) L L) L)) L
  L) L)) L L)) L L)) (N 17 (N 20 L L (N 27 L (N 30 L (N 23 L L (N 31 (N 34 L (N 35 L L L) L) L L))
  L) L)) L L)) L (N 17 (N 20 L L (N 19 (N 9 L (N 27 L (N 24 (N 32 (N 34 L (N 18 (N 31 L L L) L L)
  L) L L) L L) L) L) L L)) L (N 19 (N 9 (N 18 L (N 20 (N 24 (N 31 L (N 13 L L (N 32 (N 34 L L L) L
  L)) L) (N 25 L L (N 26 L L L)) L) L (N 24 (N 31 L (N 13 L L (N 26 L (N 32 (N 34 L L L) L L) L))
  L) (N 25 L L (N 26 L L L)) L)) L) (N 32 (N 34 L (N 31 (N 35 L (N 26 L L (N 25 (N 27 L L L) L L))
  L) L L) L) L L) L) L L))) L (N 14 (N 17 (N 27 L (N 18 (N 19 (N 20 L L (N 34 L (N 35 (N 30 L (N
  31 L L L) L) L L) L)) L (N 20 (N 34 L (N 35 (N 30 L (N 31 L L L) L) L L) L) L (N 24 (N 31 L (N
  30 (N 34 L (N 35 L L L) L) L L) L) (N 9 (N 13 L L (N 25 L L (N 23 (N 26 (N 30 L (N 31 L L L) L)
  L L) L L))) L (N 25 (N 26 L L (N 13 (N 23 (N 30 L (N 31 L L L) L) L L) L L)) L L)) L))) (N 24 (N
  34 (N 31 L (N 30 L L (N 9 (N 13 L L L) L L)) L) L L) L L) L) L) L (N 19 (N 20 L L L) L L)) L
  L))) (N 8 (N 12 (N 14 L L (N 17 L L (N 18 (N 19 L L (N 20 L L L)) (N 19 (N 20 (N 23 L (N 24 (N
  25 L (N 9 (N 31 L (N 32 L L (N 13 L (N 26 L L L) L)) L) L (N 13 (N 31 L (N 33 L L L) L) (N 26 L
  L (N 32 (N 31 L (N 34 L L L) L) L L)) L)) (N 26 L (N 33 (N 13 L L (N 31 L (N 34 L L L) L)) L L)
  L)) (N 25 L L (N 26 L L L)) L) (N 30 L (N 24 (N 25 L (N 35 (N 27 L (N 31 L (N 34 (N 9 L L (N 13
  L L L)) L L) L) L) L L) (N 26 L (N 13 (N 33 L L L) L L) L)) (N 25 L L (N 26 L L L)) L) L)) L (N
  9 (N 32 L (N 25 L L (N 23 L (N 26 L (N 24 (N 31 L L L) L L) L) L)) L) (N 25 L L (N 23 L (N 24 (N
  26 L (N 32 (N 31 L (N 34 L L L) L) L L) L) L L) L)) L)) L (N 20 (N 13 (N 33 L (N 26 L L (N 23 L
  (N 25 L (N 24 (N 31 L L L) L L) L) L)) L) (N 26 L L (N 23 L (N 24 (N 25 L (N 32 (N 31 L (N 34 L
  L L) L) L L) L) L L) L)) L) L L)) L))) L (N 20 (N 13 (N 14 L L (N 17 L L (N 18 L (N 19 (N 23 (N
  30 L (N 24 (N 27 L (N 31 L (N 9 L L (N 33 (N 34 L L L) L L)) L) L) (N 25 L L (N 26 L L L)) L) L)
  (N 24 (N 31 L (N 33 (N 34 L L L) L L) L) (N 25 L L (N 26 L L L)) L) L) L (N 23 (N 30 L (N 24 (N
  27 L (N 31 L (N 9 L L (N 25 L (N 35 L L L) L)) L) L) (N 25 L L (N 26 L L L)) L) L) (N 24 (N 31 L
  (N 33 (N 34 L L L) L L) L) (N 25 L L (N 26 L L L)) L) L)) L))) (N 33 (N 34 L (N 31 (N 35 L (N 25
  L L (N 27 (N 17 L L (N 18 L (N 24 L (N 23 (N 14 L L (N 26 L L L)) L L) L) L)) L L)) L) L L) L) L
  L) L) L L)) L (N 19 (N 9 (N 17 L L (N 12 (N 14 L L (N 18 L (N 20 (N 23 (N 30 L (N 24 (N 27 L (N
  31 L (N 13 L L (N 32 (N 34 L L L) L L)) L) L) (N 25 L L (N 26 L L L)) L) L) (N 24 (N 31 L (N 32
  (N 34 L L L) L L) L) (N 25 L L (N 26 L L L)) L) L) L (N 23 (N 30 L (N 24 (N 27 L (N 31 L (N 13 L
  L (N 26 L (N 35 L L L) L)) L) L) (N 25 L L (N 26 L L L)) L) L) (N 24 (N 31 L (N 32 (N 34 L L L)
  L L) L) (N 25 L L (N 26 L L L)) L) L)) L)) L L)) (N 32 (N 34 L (N 31 (N 35 L (N 27 (N 17 L L (N
  12 (N 18 L (N 24 L (N 23 (N 14 L L (N 25 L L (N 26 L L L))) L L) L) L) L L)) L L) L) L L) L) L
  L) L) L L)))) L (S 29 L L L))) (S 16 L L (S 22 (S 29 (N 20 (N 35 L (N 5 L (N 8 (N 12 (N 14 L L
  (N 17 L L (N 18 L (N 13 (N 19 (N 23 L (N 30 L L (N 32 L L (N 26 L (N 33 L L L) L))) (N 26 L (N
  24 (N 32 L L (N 33 L L L)) L L) L)) L (N 23 L (N 30 L L (N 32 L L (N 25 L (N 26 L L L) L))) (N
  26 L (N 24 (N 32 L L (N 33 L L L)) L L) L))) (N 9 (N 19 (N 23 L (N 30 L L (N 33 L L L)) (N 24 (N
  26 L (N 30 L L (N 31 L L L)) L) L L)) L (N 23 L (N 30 L L (N 33 L L L)) (N 24 (N 26 L (N 30 L L
  (N 31 L L L)) L) L L))) L (N 19 (N 23 L (N 30 L L (N 33 L L L)) (N 24 (N 26 L (N 30 L L (N 33 L
  L L)) L) L L)) L (N 25 L (N 32 L L L) L))) L) L))) L (N 13 (N 14 L L (N 17 L L (N 18 L (N 26 L
  (N 33 L L L) L) L))) (N 14 (N 19 L L (N 17 (N 18 (N 23 L (N 30 L L (N 32 L L (N 27 L (N 34 L L
  L) L))) (N 27 L (N 24 (N 32 L L (N 34 L L L)) L L) L)) (N 9 (N 23 L (N 30 L L (N 34 L L L)) (N
  24 (N 27 L (N 30 L L (N 31 L L L)) L) L L)) L (N 23 L (N 30 L L (N 34 L L L)) (N 24 (N 27 L (N
  30 L L (N 34 L L L)) L) L L))) L) L (N 18 (N 27 L (N 34 L L L) L) (N 9 (N 24 (N 27 L (N 31 L L
  (N 32 L L L)) L) L (N 25 L (N 32 L L (N 31 (N 34 L L L) L L)) L)) L (N 24 (N 25 L (N 32 L L (N
  31 (N 33 (N 34 L L L) L L) L L)) (N 31 (N 32 L (N 26 (N 27 L L L) L L) L) L L)) L (N 25 L (N 32
  L L L) L))) L))) L (N 17 (N 19 L L (N 18 (N 23 L (N 30 L L (N 32 L L (N 25 L (N 27 L L L) L)))
  (N 27 L (N 24 (N 32 L L (N 34 L L L)) L L) L)) (N 9 (N 23 L (N 30 L L (N 34 L L L)) (N 24 (N 27
  L (N 30 L L (N 31 L L L)) L) L L)) L (N 25 L (N 32 L L L) L)) L)) L (N 18 (N 19 L L (N 27 L (N
  34 L L L) L)) (N 9 (N 19 (N 24 (N 26 L (N 31 L L (N 32 L L L)) L) L (N 25 L (N 32 L L (N 31 (N
  33 L L L) L L)) L)) L (N 24 (N 31 L L (N 32 L (N 25 L L (N 26 (N 27 L L L) L L)) L)) L (N 25 L
  (N 32 L L (N 31 (N 33 (N 34 L L L) L L) L L)) L))) L (N 19 (N 24 (N 25 L (N 32 L L (N 31 (N 33
  (N 34 L L L) L L) L L)) (N 31 (N 32 L (N 26 (N 27 L L L) L L) L) L L)) L (N 25 L (N 32 L L L)
  L)) L (N 25 L (N 32 L L L) L))) L))) L)) L (N 12 (N 17 L L (N 14 (N 19 L L L) L L)) L (N 14 (N
  19 L L L) L L))) (N 8 (N 12 (N 14 L L (N 17 L L (N 18 L (N 13 (N 19 (N 23 L (N 30 L L (N 32 L L
  (N 26 L (N 33 L L L) L))) (N 26 L (N 24 (N 30 L (N 25 L L (N 33 L L L)) L) L L) L)) L (N 23 L (N
  30 L L (N 32 L L (N 25 L (N 26 L L L) L))) (N 26 L (N 24 (N 30 L (N 25 L L (N 32 L L L)) L) L L)
  L))) (N 19 (N 23 L (N 30 L L (N 32 L L (N 26 L (N 33 L L L) L))) (N 26 L (N 24 (N 30 L (N 25 L L
  (N 33 L L L)) L) L L) L)) L (N 23 L (N 30 L L (N 32 L L (N 25 L (N 26 L L L) L))) (N 26 L (N 24
  (N 30 L (N 25 L L (N 32 L L L)) L) L L) L))) L) L))) L (N 13 (N 14 L L (N 17 L L (N 18 L (N 26 L
  (N 33 L L L) L) L))) (N 14 (N 19 L L (N 17 (N 18 (N 23 L (N 30 L L (N 32 L L (N 27 L (N 34 L L
  L) L))) (N 27 L (N 24 (N 30 L (N 25 L L (N 34 L L L)) L) L L) L)) (N 23 L (N 30 L L (N 32 L L (N
  27 L (N 34 L L L) L))) (N 27 L (N 24 (N 30 L (N 25 L L (N 34 L L L)) L) L L) L)) L) L (N 18 (N
  27 L (N 34 L L L) L) (N 23 (N 27 L (N 30 L (N 25 L L (N 24 (N 26 L (N 32 L L (N 33 (N 34 L L L)
  L L)) L) L L)) L) L) (N 30 (N 32 L L (N 34 L (N 25 L L (N 26 (N 27 L L L) L L)) L)) L L) L) L)))
  L (N 17 (N 19 L L (N 18 (N 23 L (N 30 L L (N 32 L L (N 25 L (N 27 L L L) L))) (N 27 L (N 24 (N
  30 L (N 25 L L (N 32 L L L)) L) L L) L)) (N 23 L (N 30 L L (N 32 L L (N 25 L (N 27 L L L) L)))
  (N 27 L (N 24 (N 30 L (N 25 L L (N 32 L L L)) L) L L) L)) L)) L (N 18 (N 19 L L (N 27 L (N 34 L
  L L) L)) (N 19 (N 23 (N 26 L (N 30 L (N 25 L L (N 24 (N 27 L (N 32 L L (N 33 (N 34 L L L) L L))
  L) L L)) L) L) (N 30 (N 32 L L (N 33 L (N 25 L L (N 26 (N 27 L L L) L L)) L)) L L) L) L (N 23 (N
  30 L (N 25 L L (N 32 L (N 9 (N 26 (N 27 L L L) L L) L L) L)) L) (N 30 (N 32 L L (N 25 L (N 9 (N
  26 (N 27 L L L) L L) L L) L)) L L) L)) L))) L)) L (N 14 (N 19 L L L) L L))) L) L L) (N 20 (N 5 L
  (N 8 (N 12 (N 14 L L (N 17 L L (N 18 L (N 30 L L (N 33 (N 34 L L L) L L)) L))) L (N 13 (N 14 L L
  (N 17 L L (N 18 L (N 26 L (N 33 (N 30 L L (N 34 L L L)) L L) L) L))) (N 14 (N 19 L L (N 17 (N 30
  L L (N 33 (N 34 L L L) L L)) L (N 34 (N 30 L L (N 33 L L L)) L L))) L (N 33 (N 34 L L (N 30 (N
  32 L L L) L L)) L L)) L)) L (N 12 (N 17 L L (N 14 (N 19 L L L) L L)) L (N 14 (N 19 L L L) L L)))
  (N 8 (N 12 (N 14 L L (N 17 L L (N 18 L (N 30 L L (N 23 L (N 33 (N 34 L L L) L L) L)) L))) L (N
  13 (N 14 L L (N 17 L L (N 18 L (N 26 L (N 30 (N 33 L L L) L L) L) L))) (N 14 (N 19 L L (N 17 (N
  30 L L (N 23 L (N 33 (N 34 L L L) L L) L)) L (N 30 (N 34 L L L) L L))) L (N 33 (N 34 L L (N 30
  (N 32 L L L) L L)) L L)) L)) L (N 14 (N 19 L L L) L L))) L L) L) (S 29 L L L) L))) (S 11 L L (S
  16 L L L)))) (S 4 L L (S 7 (S 11 (S 16 L (S 22 L (S 29 L (N 5 L (N 14 L L (N 35 (N 19 (N 17 L (N
  18 L L (N 9 (N 25 L L (N 26 (N 33 L L L) L L)) L (N 13 (N 24 (N 31 L L L) L L) L L))) (N 18 L (N
  8 (N 25 L L (N 26 (N 33 L L L) L L)) L (N 12 (N 23 (N 30 L L L) L L) L L)) (N 20 (N 25 (N 27 L L
  (N 23 L (N 24 L L L) L)) L (N 26 (N 33 L L L) L L)) L (N 27 (N 34 L L L) L L)))) L (N 20 (N 17 L
  (N 18 L L (N 9 (N 8 (N 25 L L (N 32 L L L)) (N 12 (N 13 L L (N 24 (N 31 L L L) L L)) L (N 13 (N
  24 L L (N 26 L L L)) L (N 24 (N 26 L L L) L L))) L) L L)) (N 8 (N 9 (N 25 L L (N 32 L L L)) (N
  12 (N 26 L L (N 23 L (N 18 L L (N 24 (N 25 L L L) L L)) L)) L (N 18 L (N 23 (N 30 L L L) L L) (N
  27 (N 34 L L L) L L))) L) (N 9 (N 18 L L (N 27 (N 34 L L L) L L)) L L) L)) L L)) L L)) L) (N 5 L
  (N 14 L L (N 19 (N 17 L (N 18 L L (N 24 (N 25 L L (N 26 L L L)) L L)) (N 18 L (N 23 (N 25 L L (N
  26 L L L)) L L) (N 20 (N 23 (N 25 L L (N 26 L L L)) (N 24 (N 25 L L (N 26 L L L)) L L) L) L (N
  27 (N 25 L L (N 26 L L L)) L L)))) L (N 20 (N 17 L (N 18 L L (N 9 (N 24 (N 13 L L (N 25 L L (N
  26 L L L))) L L) L L)) (N 8 (N 9 (N 25 L L (N 26 (N 27 L L L) L L)) (N 12 (N 23 L (N 18 L L (N
  24 (N 25 L L (N 26 L L L)) L L)) L) L (N 18 L (N 23 (N 24 (N 25 L L (N 26 L L L)) L L) L L) (N
  27 (N 25 L L (N 26 L L L)) L L))) L) (N 9 (N 18 L L (N 27 (N 25 L L (N 26 L L L)) L L)) L L) L))
  L L))) L)) (S 29 L L L)) (S 22 L (S 29 L (N 5 L (N 14 L L (N 35 (N 17 (N 19 L L (N 20 L L L)) (N
  18 (N 19 L L (N 20 L L L)) L L) L) L L)) L) L) L)) (S 16 L (S 22 (S 29 L (N 5 L (N 14 (N 12 L (N
  13 L L (N 9 (N 19 L L (N 32 L L (N 34 (N 8 L (N 17 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 20 (N
  27 L (N 31 L L (N 33 L L L)) L) L L)) (N 18 (N 31 L L L) L L)) L L))) L (N 18 (N 19 L L (N 31 (N
  24 L (N 32 L L (N 34 L L L)) L) L L)) L L))) (N 13 L (N 8 (N 19 L L (N 32 L L (N 34 (N 9 L (N 17
  (N 27 L (N 30 L L (N 31 L L L)) L) L (N 20 (N 30 L L L) L L)) (N 17 (N 30 L L L) L L)) L L))) L
  (N 17 (N 19 L L (N 30 (N 23 L (N 32 L L (N 34 L L L)) L) L L)) L L)) (N 19 (N 20 L L (N 17 L (N
  18 L L L) L)) L (N 20 (N 25 L (N 27 L (N 17 (N 18 (N 34 L L (N 32 (N 33 L L (N 8 L (N 9 L L L)
  L)) L L)) L (N 8 (N 9 L (N 24 (N 32 L L (N 33 (N 34 L L L) L L)) L L) L) (N 9 (N 32 L L (N 33 (N
  34 L L L) L L)) L L) L)) L (N 8 (N 9 L (N 32 L L (N 33 (N 34 L L L) L L)) L) (N 9 (N 23 (N 32 L
  L (N 33 (N 34 L L L) L L)) L L) L L) L)) (N 32 (N 33 L L (N 30 L (N 31 L L L) L)) L L)) (N 27 L
  (N 34 (N 33 L L (N 17 (N 18 L L (N 30 L (N 31 L L L) L)) L (N 32 (N 8 L (N 9 L L L) L) L L))) L
  L) L)) L (N 33 (N 32 L L (N 34 (N 35 L (N 17 (N 27 L (N 18 (N 30 L (N 31 L L L) L) L L) L) (N 18
  (N 27 L L L) L L) L) L) L L)) L L))))) L (N 19 (N 17 L (N 18 L L (N 9 (N 32 L L (N 33 (N 8 L (N
  12 (N 26 L (N 30 L L (N 31 L L L)) L) L (N 20 (N 26 L (N 31 L L (N 34 L L L)) L) L L)) (N 13 (N
  31 L L L) L L)) L L)) L (N 13 (N 31 (N 24 L (N 32 L L (N 33 L L L)) L) L L) L L))) (N 18 L (N 8
  (N 32 L L (N 33 (N 9 L (N 12 (N 26 L (N 30 L L (N 31 L L L)) L) L (N 20 (N 30 L L L) L L)) (N 12
  (N 30 L L L) L L)) L L)) L (N 12 (N 30 (N 23 L (N 32 L L (N 33 L L L)) L) L L) L L)) (N 20 (N 25
  L (N 26 L (N 12 (N 13 (N 33 L L (N 32 (N 34 L L (N 8 L (N 9 L L L) L)) L L)) L (N 8 (N 9 L (N 24
  (N 32 L L (N 33 (N 34 L L L) L L)) L L) L) (N 9 (N 32 L L (N 33 (N 34 L L L) L L)) L L) L)) L (N
  8 (N 9 L (N 32 L L (N 33 (N 34 L L L) L L)) L) (N 9 (N 23 (N 32 L L (N 33 (N 34 L L L) L L)) L
  L) L L) L)) (N 32 (N 34 L L (N 30 L (N 31 L L L) L)) L L)) (N 26 L (N 33 (N 34 L L (N 12 (N 13 L
  L (N 30 L (N 31 L L L) L)) L (N 32 (N 8 L (N 9 L L L) L) L L))) L L) L)) L (N 34 (N 32 L L (N 33
  (N 35 L (N 12 (N 26 L (N 13 (N 30 L (N 31 L L L) L) L L) L) (N 13 (N 26 L L L) L L) L) L) L L))
  L L)))) L (N 20 (N 25 L (N 32 (N 30 L (N 31 L L (N 13 (N 18 L L (N 33 (N 34 L L L) L L)) L (N 18
  (N 33 (N 34 L L L) L L) L L))) (N 31 L (N 12 (N 17 L L (N 33 (N 34 L L L) L L)) L (N 17 (N 33 (N
  34 L L L) L L) L L)) (N 33 (N 34 L L L) L L))) L (N 33 (N 34 L L L) L L)) (N 32 (N 33 (N 34 L L
  L) L L) L L)) L L))) L) (N 5 L (N 14 (N 12 L (N 13 L L (N 9 (N 19 L L (N 8 L (N 23 (N 30 (N 17 L
  L (N 20 (N 32 L (N 25 L L (N 27 L (N 35 L L L) L)) L) L L)) L L) L L) (N 18 (N 24 L (N 23 (N 31
  L (N 30 (N 35 L L L) L L) L) L L) L) L L))) L (N 18 (N 19 L L (N 17 (N 20 (N 34 L (N 27 L L (N
  25 L (N 23 (N 30 L L L) L L) L)) L) L (N 23 (N 30 L (N 8 L L (N 25 L (N 31 (N 32 L L L) L L) L))
  L) (N 24 (N 25 L L (N 27 L L L)) L L) L)) (N 23 (N 27 L L (N 25 L (N 26 (N 24 L (N 30 (N 34 L L
  L) L L) L) L L) L)) L L) L)) L L))) (N 13 L (N 8 (N 19 L L (N 9 L (N 24 (N 31 (N 18 L L (N 20 (N
  32 L (N 25 L L (N 27 L (N 35 L L L) L)) L) L L)) L L) L L) (N 17 (N 23 L (N 24 (N 30 L (N 31 (N
  35 L L L) L L) L) L L) L) L L))) L (N 17 (N 19 L L (N 18 (N 20 (N 34 L (N 27 L L (N 25 L (N 24
  (N 31 L L L) L L) L)) L) L (N 23 (N 30 L (N 31 (N 24 L (N 9 L L (N 25 L L L)) L) L L) L) (N 24
  (N 31 L (N 9 L L (N 25 L (N 30 (N 32 L L L) L L) L)) L) L L) L)) (N 24 (N 27 L L (N 25 L (N 26
  (N 23 L (N 31 (N 34 L L L) L L) L) L L) L)) L L) L)) L L)) (N 19 (N 20 L L (N 17 L (N 18 L L L)
  L)) L (N 20 (N 23 (N 24 (N 35 L (N 25 L (N 26 L (N 27 L L (N 32 (N 30 L (N 31 L L L) L) L L)) (N
  33 (N 32 L L (N 34 L L L)) L L)) (N 27 L (N 34 (N 33 L L (N 26 L (N 32 (N 30 L (N 31 L L L) L) L
  L) L)) L L) L)) L) (N 25 L (N 9 (N 8 L (N 32 L L (N 18 (N 27 L (N 17 (N 34 L L L) L L) L) L L))
  (N 18 (N 31 L (N 30 (N 35 L L L) L L) L) L L)) L (N 18 (N 17 (N 30 L (N 31 (N 32 L L (N 8 L (N
  34 L L L) L)) L L) L) (N 27 L L (N 34 (N 30 L (N 31 L L L) L) L L)) L) L L)) (N 27 L (N 34 (N 9
  (N 31 L (N 30 (N 35 L L L) L L) L) L (N 17 (N 18 L L L) L L)) L L) L)) L) (N 24 (N 25 L (N 8 (N
  9 L (N 32 L L (N 17 (N 27 L (N 18 (N 34 L L L) L L) L) L L)) (N 17 (N 30 L (N 31 (N 35 L L L) L
  L) L) L L)) L (N 17 (N 18 (N 31 L (N 30 (N 32 L L (N 9 L (N 34 L L L) L)) L L) L) (N 27 L L (N
  34 (N 30 L (N 31 L L L) L) L L)) L) L L)) (N 27 L (N 34 (N 8 (N 30 L (N 31 (N 35 L L L) L L) L)
  L (N 17 (N 18 L L L) L L)) L L) L)) L L) L) L (N 17 (N 18 (N 23 (N 30 L (N 31 (N 24 L (N 34 L (N
  8 L L (N 27 L L (N 25 L (N 32 L L L) L))) L) L) L L) L) (N 24 (N 31 L (N 30 (N 34 L (N 9 L L (N
  27 L L (N 25 L (N 32 L L L) L))) L) L L) L) L L) L) (N 27 L L (N 25 L (N 24 (N 34 (N 30 L (N 31
  L L L) L) L L) L L) L)) L) (N 18 (N 27 L L (N 25 L (N 23 (N 34 (N 30 L (N 31 L L L) L) L L) L L)
  L)) L L) L))))) L (N 19 (N 17 L (N 18 L L (N 9 (N 8 L (N 23 (N 30 (N 12 L L (N 20 (N 32 L (N 25
  L L (N 26 L (N 35 L L L) L)) L) L L)) L L) L L) (N 13 (N 24 L (N 23 (N 31 L (N 30 (N 35 L L L) L
  L) L) L L) L) L L)) L (N 13 (N 12 (N 20 (N 33 L (N 26 L L (N 25 L (N 23 (N 30 L L L) L L) L)) L)
  L (N 23 (N 30 L (N 8 L L (N 25 L (N 31 (N 32 L L L) L L) L)) L) (N 24 (N 25 L L (N 26 L L L)) L
  L) L)) (N 23 (N 26 L L (N 25 L (N 27 (N 24 L (N 30 (N 33 L L L) L L) L) L L) L)) L L) L) L L)))
  (N 18 L (N 8 (N 9 L (N 24 (N 31 (N 13 L L (N 20 (N 32 L (N 25 L L (N 26 L (N 35 L L L) L)) L) L
  L)) L L) L L) (N 12 (N 23 L (N 24 (N 30 L (N 31 (N 35 L L L) L L) L) L L) L) L L)) L (N 12 (N 13
  (N 20 (N 33 L (N 26 L L (N 25 L (N 24 (N 31 L L L) L L) L)) L) L (N 23 (N 30 L (N 31 (N 24 L (N
  9 L L (N 25 L L L)) L) L L) L) (N 24 (N 31 L (N 9 L L (N 25 L (N 30 (N 32 L L L) L L) L)) L) L
  L) L)) (N 24 (N 26 L L (N 25 L (N 27 (N 23 L (N 31 (N 33 L L L) L L) L) L L) L)) L L) L) L L))
  (N 20 (N 23 (N 24 (N 35 L (N 25 L (N 26 L (N 27 L L (N 34 (N 32 L L (N 33 L L L)) L L)) (N 32 (N
  30 L (N 31 L L L) L) L L)) (N 26 L (N 33 (N 34 L L (N 27 L (N 32 (N 30 L (N 31 L L L) L) L L)
  L)) L L) L)) L) (N 25 L (N 9 (N 8 L (N 32 L L (N 13 (N 26 L (N 12 (N 33 L L L) L L) L) L L)) (N
  13 (N 31 L (N 30 (N 35 L L L) L L) L) L L)) L (N 13 (N 12 (N 30 L (N 31 (N 32 L L (N 8 L (N 33 L
  L L) L)) L L) L) (N 26 L L (N 33 (N 30 L (N 31 L L L) L) L L)) L) L L)) (N 26 L (N 33 (N 9 (N 31
  L (N 30 (N 35 L L L) L L) L) L (N 12 (N 13 L L L) L L)) L L) L)) L) (N 24 (N 25 L (N 8 (N 9 L (N
  32 L L (N 12 (N 26 L (N 13 (N 33 L L L) L L) L) L L)) (N 12 (N 30 L (N 31 (N 35 L L L) L L) L) L
  L)) L (N 12 (N 13 (N 31 L (N 30 (N 32 L L (N 9 L (N 33 L L L) L)) L L) L) (N 26 L L (N 33 (N 30
  L (N 31 L L L) L) L L)) L) L L)) (N 26 L (N 33 (N 8 (N 30 L (N 31 (N 35 L L L) L L) L) L (N 12
  (N 13 L L L) L L)) L L) L)) L L) L) L (N 12 (N 13 (N 23 (N 30 L (N 31 (N 24 L (N 33 L (N 8 L L
  (N 26 L L (N 25 L (N 32 L L L) L))) L) L) L L) L) (N 24 (N 31 L (N 30 (N 33 L (N 9 L L (N 26 L L
  (N 25 L (N 32 L L L) L))) L) L L) L) L L) L) (N 26 L L (N 25 L (N 24 (N 33 (N 30 L (N 31 L L L)
  L) L L) L L) L)) L) (N 13 (N 26 L L (N 25 L (N 23 (N 33 (N 30 L (N 31 L L L) L) L L) L L) L)) L
  L) L)))) L (N 20 (N 23 (N 24 (N 35 L (N 25 L (N 26 L (N 27 L L (N 32 (N 30 L (N 31 L L L) L) L
  L)) (N 32 (N 30 L (N 31 L L L) L) L L)) (N 26 L (N 27 L (N 32 (N 30 L (N 31 L L L) L) L L) L)
  L)) L) (N 25 L (N 9 (N 13 (N 18 L L (N 31 L (N 30 (N 35 L L L) L L) L)) L (N 8 (N 30 L (N 32 L L
  L) L) (N 32 (N 30 L (N 31 L L L) L) L L) L)) L (N 13 (N 18 L L L) L L)) (N 8 (N 30 L (N 31 (N 32
  L (N 12 L L (N 17 L L (N 35 L (N 26 (N 27 L L L) L L) L))) L) L L) L) (N 9 (N 13 (N 18 L L (N 26
  L (N 31 L (N 30 (N 33 L L L) L L) L) L)) L (N 18 (N 27 L (N 31 L (N 30 (N 34 L L L) L L) L) L) L
  (N 26 (N 27 L (N 34 (N 30 L (N 33 L L L) L) L L) L) (N 33 (N 34 L (N 27 (N 30 L L L) L L) L) L
  L) L))) L L) L)) L) (N 24 (N 25 L (N 8 (N 12 (N 17 L L (N 30 L (N 31 (N 35 L L L) L L) L)) L (N
  9 (N 31 L (N 32 L L L) L) (N 32 (N 30 L (N 31 L L L) L) L L) L)) L (N 12 (N 17 L L L) L L)) (N 8
  (N 9 (N 31 L (N 30 (N 32 L (N 13 L L (N 18 L L (N 35 L (N 26 (N 27 L L L) L L) L))) L) L L) L)
  (N 12 (N 17 L L (N 26 L (N 30 L (N 31 (N 33 L L L) L L) L) L)) L (N 17 (N 27 L (N 30 L (N 31 (N
  34 L L L) L L) L) L) L (N 26 (N 27 L (N 34 (N 31 L (N 33 L L L) L) L L) L) (N 33 (N 34 L (N 27
  (N 31 L L L) L L) L) L L) L))) L) (N 9 (N 13 L L (N 18 L L (N 26 (N 27 L L L) L L))) L L) L)) L
  L) L) L L))) L)) (S 29 L L (N 5 L (N 14 (N 12 L (N 13 L L (N 24 (N 25 L L (N 9 (N 18 L L (N 19 L
  L (N 8 L (N 20 (N 27 L L L) L L) L))) L (N 18 (N 19 L L (N 27 L L L)) L L))) L L)) (N 13 L (N 23
  (N 25 L L (N 8 (N 17 L L (N 19 L L (N 9 L (N 20 (N 27 L L L) L L) L))) L (N 17 (N 19 L L (N 27 L
  L L)) L L))) L L) (N 19 (N 20 L L (N 17 L (N 18 L L L) L)) L (N 20 (N 23 (N 25 L L (N 27 (N 26 L
  L (N 17 L (N 18 L L L) L)) L L)) (N 24 (N 25 L L (N 27 (N 18 L L (N 26 L L L)) L L)) L L) L) L
  (N 26 (N 25 L L (N 27 (N 17 (N 23 L (N 24 L L L) L) (N 18 (N 24 L L L) L L) L) L L)) L L))))) L
  (N 19 (N 17 L (N 18 L L (N 24 (N 25 L L (N 26 (N 13 L L (N 9 (N 20 L L L) L L)) L L)) L L)) (N
  18 L (N 23 (N 25 L L (N 26 (N 12 L L (N 8 (N 20 L L L) L L)) L L)) L L) (N 20 (N 23 (N 25 L L (N
  26 (N 27 L L (N 12 L (N 13 L L L) L)) L L)) (N 24 (N 25 L L (N 26 (N 13 L L (N 27 L L L)) L L))
  L L) L) L (N 27 (N 25 L L (N 26 (N 12 (N 23 L (N 24 L L L) L) (N 13 (N 24 L L L) L L) L) L L)) L
  L)))) L (N 20 (N 23 (N 25 L L (N 26 (N 27 L L L) L L)) (N 24 (N 25 L L (N 26 (N 27 L L L) L L))
  L L) L) L L))) L)) (S 29 L L L)) (S 22 (S 29 L (N 5 L (N 14 (N 12 L (N 13 L L (N 18 (N 19 L L (N
  9 (N 31 L L (N 32 L L L)) L (N 31 (N 24 L (N 32 L L (N 34 L L L)) L) L L))) L L)) (N 13 L (N 17
  (N 19 L L (N 8 (N 30 L L (N 32 L L L)) L (N 30 (N 23 L (N 32 L L (N 34 L L L)) L) L L))) L L) (N
  17 (N 19 L L (N 18 (N 20 (N 34 L L (N 25 L (N 27 L (N 32 (N 33 L L L) L L) L) L)) L (N 27 L (N
  33 (N 32 L L (N 34 (N 30 L (N 31 L L L) L) L L)) L L) L)) (N 8 (N 32 L L (N 27 L (N 30 L (N 31
  (N 34 L L L) L L) L) L)) L (N 20 (N 23 (N 30 L (N 25 L (N 24 (N 35 L (N 27 L L (N 26 L (N 32 (N
  9 L L (N 31 L L L)) L L) L)) L) L (N 31 (N 32 L L (N 34 L L L)) L L)) (N 27 L (N 24 (N 35 L L L)
  L L) L)) L) (N 24 (N 25 L (N 27 L (N 35 (N 26 L L (N 33 L L L)) L L) (N 32 (N 30 L (N 26 (N 35 L
  L L) L L) L) L L)) (N 27 L (N 32 (N 9 L (N 30 L (N 31 L L (N 33 L L L)) L) L) L L) L)) L (N 25 L
  (N 33 (N 26 L (N 35 L L L) L) L L) L)) L) L (N 27 L (N 33 (N 32 L L (N 25 L (N 34 (N 30 L (N 31
  L L L) L) L L) L)) L L) L))) L)) (N 18 (N 19 L L (N 9 (N 32 L L (N 27 L (N 31 L (N 30 (N 34 L L
  L) L L) L) L)) L (N 20 (N 24 (N 31 L (N 25 L (N 23 (N 35 L (N 27 L L (N 26 L (N 32 (N 8 L L (N
  30 L L L)) L L) L)) L) L (N 30 (N 32 L L (N 34 L L L)) L L)) (N 27 L (N 23 (N 35 L L L) L L) L))
  L) (N 23 (N 25 L (N 27 L (N 35 (N 26 L L (N 33 L L L)) L L) (N 32 (N 31 L (N 26 (N 35 L L L) L
  L) L) L L)) (N 27 L (N 32 (N 8 L (N 30 L L (N 33 L L L)) L) L L) L)) L (N 25 L (N 33 (N 26 L (N
  35 L L L) L) L L) L)) L) L (N 27 L (N 33 (N 32 L L (N 25 L (N 34 (N 30 L (N 31 L L L) L) L L)
  L)) L L) L)))) L L) L))) L (N 17 (N 19 L L (N 20 (N 12 L (N 13 L L L) L) L L)) (N 18 (N 19 L L
  (N 13 (N 20 L L L) L L)) L L) L)) L) L) (S 29 L (N 5 L (N 35 (N 14 (N 12 L (N 13 L L (N 18 (N 19
  L L (N 9 (N 24 L L (N 25 L L L)) L (N 24 (N 31 L L L) L L))) L L)) (N 13 L (N 17 (N 19 L L (N 8
  (N 23 L L (N 25 L L L)) L (N 23 (N 30 L L L) L L))) L L) (N 17 (N 19 L L (N 18 (N 20 (N 27 L L
  (N 34 L L L)) L (N 26 (N 33 L L L) L L)) (N 8 (N 25 L L (N 23 L (N 24 (N 27 L L L) L L) L)) L (N
  20 (N 23 (N 25 L L (N 27 L L L)) (N 24 (N 25 L L (N 27 L L L)) L (N 25 (N 26 L L L) L L)) L) L
  (N 26 (N 33 L L L) L L))) L)) (N 18 (N 19 L L (N 9 (N 25 L L (N 24 L (N 23 (N 27 L L L) L L) L))
  L (N 20 (N 24 (N 25 L L (N 27 L L L)) (N 23 (N 25 L L (N 27 L L L)) L (N 25 (N 26 L L L) L L))
  L) L (N 26 (N 33 L L L) L L)))) L L) L))) L (N 17 (N 19 L L (N 20 (N 12 L (N 13 L L L) L) L L))
  (N 18 (N 19 L L (N 13 (N 20 L L L) L L)) L L) L)) L L) L) L) L)) (S 16 L L L)) (S 11 L (S 16 L
  (S 22 (S 29 (N 5 L (N 35 L (N 14 (N 19 (N 20 L L (N 8 (N 9 L (N 12 L L (N 17 L L L)) (N 12 L (N
  13 L L (N 18 L L L)) (N 17 L (N 18 L L L) L))) (N 9 (N 13 L L (N 18 L L L)) L (N 13 (N 18 (N 24
  L (N 31 L L (N 25 (N 32 L L L) L L)) (N 25 (N 32 L L L) L L)) L (N 12 (N 24 (N 31 L (N 25 (N 32
  L L (N 30 (N 33 L (N 26 L L (N 27 L L L)) L) L L)) L (N 26 L (N 23 (N 30 L L (N 32 (N 34 L L L)
  L L)) L L) L)) L) (N 31 (N 23 (N 17 L (N 27 L L (N 34 L L L)) (N 27 L (N 34 L L L) L)) L (N 25
  (N 27 L (N 26 L L (N 34 L L L)) L) L L)) L L) L) (N 26 L L (N 25 (N 27 L (N 34 L L L) L) L L))
  L)) L (N 18 (N 17 (N 24 (N 31 L (N 25 (N 32 L L (N 30 (N 34 L (N 26 L L (N 27 L L L)) L) L L)) L
  (N 27 L (N 23 (N 30 L L (N 32 (N 33 L L L) L L)) L L) L)) L) (N 31 (N 23 (N 12 L (N 26 L L (N 33
  L L L)) (N 26 L (N 33 L L L) L)) L (N 25 (N 26 L (N 27 L L (N 33 L L L)) L) L L)) L L) L) (N 27
  L L (N 25 (N 26 L (N 33 L L L) L) L L)) L) L L))) (N 9 (N 12 L (N 13 L L (N 18 L L L)) (N 17 L
  (N 18 L L L) L)) (N 12 (N 17 (N 23 L (N 30 L L (N 25 (N 32 L L L) L L)) (N 25 (N 32 L L L) L L))
  L (N 13 (N 23 (N 30 L (N 25 (N 32 L L (N 31 (N 33 L (N 26 L L (N 27 L L L)) L) L L)) L (N 26 L
  (N 24 (N 31 L L (N 32 (N 34 L L L) L L)) L L) L)) L) (N 30 (N 24 (N 18 L (N 27 L L (N 34 L L L))
  (N 27 L (N 34 L L L) L)) L (N 25 (N 27 L (N 26 L L (N 34 L L L)) L) L L)) L L) L) (N 26 L L (N
  25 (N 27 L (N 34 L L L) L) L L)) L)) L (N 17 (N 18 (N 23 (N 30 L (N 25 (N 32 L L (N 31 (N 34 L
  (N 26 L L (N 27 L L L)) L) L L)) L (N 27 L (N 24 (N 31 L L (N 32 (N 33 L L L) L L)) L L) L)) L)
  (N 30 (N 24 (N 13 L (N 26 L L (N 33 L L L)) (N 26 L (N 33 L L L) L)) L (N 25 (N 26 L (N 27 L L
  (N 33 L L L)) L) L L)) L L) L) (N 27 L L (N 25 (N 26 L (N 33 L L L) L) L L)) L) L L)) (N 12 (N
  26 L (N 33 L L (N 34 (N 32 L L (N 17 L (N 18 L L L) L)) L L)) (N 27 (N 17 L (N 18 L L (N 13 (N
  24 L (N 23 L L (N 25 L (N 32 L L L) L)) L) L L)) (N 23 L (N 25 L (N 30 (N 34 L L L) L L) L) L))
  (N 33 L L (N 34 (N 17 L L (N 32 L L L)) L L)) L)) (N 13 (N 26 L L (N 33 L L (N 18 (N 27 L (N 34
  L L L) L) L (N 24 (N 27 L (N 31 L (N 32 (N 34 L L L) L L) L) L) (N 31 (N 34 L (N 25 (N 27 L L L)
  L L) L) L L) L)))) L (N 18 (N 17 (N 24 (N 26 L L (N 27 L (N 34 L L L) L)) (N 31 (N 33 L L (N 26
  (N 23 L L (N 25 L (N 27 L L L) L)) L L)) L L) L) (N 27 L L (N 26 (N 24 L (N 25 L (N 31 (N 33 L L
  L) L L) L) L) L L)) L) L L)) (N 17 (N 18 (N 23 (N 30 L (N 26 L (N 34 L L (N 32 (N 33 L L L) L
  L)) (N 27 L (N 34 L L L) L)) L) (N 30 (N 24 (N 13 L (N 26 L L (N 33 L L L)) (N 26 L (N 33 L L L)
  L)) L (N 13 (N 26 L (N 25 (N 32 L L L) L L) L) (N 26 (N 25 L (N 32 L L L) L) L L) L)) L L) L) (N
  27 L L (N 34 L L (N 23 (N 26 L (N 30 L (N 32 (N 33 L L L) L L) L) L) (N 30 (N 33 L (N 25 (N 26 L
  L L) L L) L) L L) L))) L) (N 18 (N 27 L L (N 34 L L (N 13 (N 26 L (N 33 L L L) L) L (N 23 (N 24
  (N 25 L (N 26 L (N 31 L (N 30 (N 32 (N 33 L L L) L L) L L) L) L) L) (N 31 (N 33 L (N 25 (N 26 L
  L L) L L) L) L L) L) (N 24 (N 26 L L L) L L) L)))) L L) L))))) L (N 20 (N 8 (N 12 L (N 13 L L (N
  9 (N 18 (N 24 L (N 31 L L (N 26 (N 33 L L L) L L)) (N 26 (N 33 L L L) L L)) L (N 24 (N 31 L (N
  25 L (N 32 L L (N 27 L (N 33 (N 34 L L L) L L) L)) (N 26 (N 27 L (N 34 L L L) L) L L)) L) (N 31
  (N 23 (N 17 L (N 27 L L (N 34 L L L)) (N 27 L (N 34 L L L) L)) L (N 26 (N 27 L (N 25 L L (N 34 L
  L L)) L) L L)) L L) L)) L (N 18 (N 17 (N 23 L (N 24 (N 25 L L (N 27 L L L)) L L) (N 25 L (N 26
  (N 32 L L (N 34 L L L)) L L) L)) (N 27 L L (N 25 L (N 32 L L L) L)) L) L L))) (N 13 L (N 17 (N
  23 L (N 30 L L (N 26 (N 33 L L L) L L)) (N 26 (N 33 L L L) L L)) L (N 9 (N 23 (N 30 L (N 25 L (N
  32 L L (N 27 L (N 33 (N 34 L L L) L L) L)) (N 26 (N 27 L (N 34 L L L) L) L L)) L) (N 30 (N 24 (N
  18 L (N 27 L L (N 34 L L L)) (N 27 L (N 34 L L L) L)) L (N 26 (N 27 L (N 25 L L (N 34 L L L)) L)
  L L)) L L) L) (N 25 L L (N 26 (N 27 L (N 34 L L L) L) L L)) L)) (N 25 L (N 32 L L (N 34 (N 33 L
  L (N 17 L (N 18 L L L) L)) L L)) (N 27 (N 17 L (N 18 L L (N 9 (N 24 L (N 23 L L (N 26 L (N 33 L
  L L) L)) L) L L)) (N 23 L (N 26 L (N 30 (N 34 L L L) L L) L) L)) (N 32 L L (N 34 (N 17 L L (N 33
  L L L)) L L)) L)))) (N 9 (N 13 L L (N 25 L L (N 32 L L (N 12 L (N 17 (N 27 L (N 34 L L L) L) L
  (N 18 (N 27 L (N 34 L L L) L) L (N 26 (N 33 L L L) L L))) (N 18 (N 27 L (N 34 L L L) L) L (N 24
  (N 27 L (N 31 L (N 33 (N 34 L L L) L L) L) L) (N 31 (N 34 L (N 26 (N 27 L L L) L L) L) L L)
  L)))))) L (N 18 (N 13 L L (N 12 L (N 17 (N 23 (N 25 L L (N 27 L (N 34 L L L) L)) L (N 25 (N 26 L
  L L) L L)) L L) (N 17 (N 24 (N 25 L L (N 27 L (N 34 L L L) L)) (N 31 (N 32 L L (N 25 (N 23 L L
  (N 26 L (N 27 L L L) L)) L L)) L L) L) (N 27 L L (N 25 (N 24 L (N 26 L (N 31 (N 32 L L L) L L)
  L) L) L L)) L))) L L)) (N 17 (N 12 L (N 13 L L (N 18 (N 9 (N 24 L (N 31 L L (N 26 (N 33 L L L) L
  L)) (N 25 L (N 26 (N 33 L L L) L L) L)) L (N 24 (N 25 L (N 31 L (N 32 (N 26 L L (N 23 (N 27 L (N
  30 L L (N 33 L L L)) L) L L)) L L) L) L) (N 31 (N 32 L (N 25 (N 23 L L (N 26 L L L)) L L) L) L
  L) L)) L L)) (N 13 L (N 18 (N 23 (N 30 L (N 25 L (N 34 L L (N 32 (N 33 L L L) L L)) (N 27 L (N
  34 L L L) L)) L) (N 30 (N 24 (N 9 L (N 25 L L (N 32 L L L)) (N 25 L (N 32 L L L) L)) L (N 26 (N
  25 L (N 27 L L (N 32 L L L)) L) L L)) L L) L) (N 27 L L (N 26 (N 25 L (N 32 L L L) L) L L)) L)
  (N 18 (N 23 (N 30 L (N 25 L (N 34 L L (N 32 (N 33 L L L) L L)) (N 27 L (N 34 L L L) L)) L) (N 30
  (N 24 (N 9 L (N 25 L L (N 32 L L L)) (N 25 L (N 32 L L L) L)) L (N 9 (N 25 L (N 26 (N 33 L L L)
  L L) L) (N 25 (N 26 L (N 33 L L L) L) L L) L)) L L) L) (N 27 L L (N 34 L L (N 23 (N 25 L (N 30 L
  (N 32 (N 33 L L L) L L) L) L) (N 30 (N 32 L (N 25 (N 26 L L L) L L) L) L L) L))) L))) (N 18 (N
  13 L L (N 27 L L (N 34 L L (N 9 (N 25 L (N 32 L L L) L) L (N 12 L (N 26 (N 33 L L L) L L) (N 23
  (N 24 (N 25 L (N 26 L (N 31 L (N 30 (N 32 (N 33 L L L) L L) L L) L) L) L) (N 31 (N 32 L (N 25 (N
  26 L L L) L L) L) L L) L) (N 24 (N 25 L L L) L L) L)))))) L L) L)) L (N 8 (N 12 L (N 13 L L (N
  18 (N 9 (N 17 (N 23 L (N 24 L L (N 25 L L L)) (N 26 (N 24 L (N 31 L L (N 32 L (N 25 L L (N 27 L
  L L)) L)) (N 25 L (N 27 L (N 31 L (N 30 L L (N 32 L L (N 34 L L L))) L) L) L)) L L)) (N 27 L L
  (N 34 L L L)) L) L (N 17 (N 23 L (N 24 (N 25 L L (N 27 L L L)) L L) (N 25 L (N 26 (N 32 L L (N
  34 L L L)) L L) L)) (N 27 L L (N 34 L L L)) L)) L L)) (N 13 L (N 17 (N 18 (N 23 L (N 30 L L (N
  26 (N 32 L (N 25 L L (N 27 L L L)) L) L L)) (N 25 L (N 26 (N 30 L (N 32 L L (N 34 L L L)) L) L
  L) L)) (N 27 L L (N 34 L L L)) L) L L) (N 17 (N 18 (N 23 L (N 30 L L (N 32 L (N 25 L L (N 27 L L
  L)) L)) (N 25 L (N 30 L (N 32 L L (N 34 L L L)) L) L)) (N 27 L L (N 34 L L L)) L) (N 18 (N 27 L
  L (N 34 L L L)) L L) L))) (N 9 (N 13 L L (N 18 (N 25 L L (N 24 L (N 27 L (N 34 L L L) L) L)) L
  L)) L (N 18 (N 13 (N 17 (N 24 L (N 31 L L (N 25 (N 32 (N 33 L (N 26 L L (N 27 L L L)) L) L L) L
  L)) (N 25 (N 26 L (N 31 L (N 32 (N 33 L L (N 34 L L L)) L L) L) L) L L)) (N 27 L L (N 34 L L L))
  L) L (N 17 (N 24 (N 31 L (N 25 (N 23 L (N 26 L L (N 27 L L L)) (N 26 L (N 33 L L (N 34 L L L))
  L)) L (N 27 L (N 34 L L L) L)) L) (N 31 (N 23 (N 12 L (N 30 L L (N 32 (N 33 L L L) L L)) (N 25
  (N 26 L (N 33 L L L) L) L (N 27 L (N 34 L L L) L))) L (N 25 (N 26 L (N 27 L L (N 33 L L L)) L) L
  L)) L L) L) (N 27 L L (N 34 L L L)) L)) L L)) (N 17 (N 18 (N 27 L (N 34 L L (N 32 (N 33 L L L) L
  L)) (N 34 L (N 25 (N 26 L L L) L L) L)) (N 27 L L (N 34 L L L)) L) (N 18 (N 27 L L (N 34 L L L))
  L L) L)))) L (N 19 (N 20 (N 8 (N 17 L (N 18 L L (N 9 (N 13 (N 24 L (N 31 L L (N 27 (N 34 L L L)
  L L)) (N 27 (N 34 L L L) L L)) L (N 24 (N 31 L (N 25 L (N 32 L L (N 26 L (N 33 (N 34 L L L) L L)
  L)) (N 26 L (N 27 (N 33 L L L) L L) L)) L) (N 31 (N 23 (N 12 L (N 26 L L (N 33 L L L)) (N 26 L
  (N 33 L L L) L)) L (N 27 (N 26 L (N 25 L L (N 33 L L L)) L) L L)) L L) L)) L (N 13 (N 12 (N 23 L
  (N 24 (N 25 L L (N 26 L L L)) L L) (N 25 L (N 27 (N 32 L L (N 33 L L L)) L L) L)) (N 26 L L (N
  25 L (N 32 L L L) L)) L) L L))) (N 18 L (N 12 (N 23 L (N 30 L L (N 27 (N 34 L L L) L L)) (N 27
  (N 34 L L L) L L)) L (N 9 (N 23 (N 30 L (N 25 L (N 32 L L (N 26 L (N 33 (N 34 L L L) L L) L)) (N
  26 L (N 27 (N 33 L L L) L L) L)) L) (N 30 (N 24 (N 13 L (N 26 L L (N 33 L L L)) (N 26 L (N 33 L
  L L) L)) L (N 27 (N 26 L (N 25 L L (N 33 L L L)) L) L L)) L L) L) (N 25 L L (N 27 (N 26 L (N 33
  L L L) L) L L)) L)) (N 25 L (N 32 L L (N 33 (N 34 L L (N 12 L (N 13 L L L) L)) L L)) (N 26 (N 12
  L (N 13 L L (N 9 (N 24 L (N 23 L L (N 27 L (N 34 L L L) L)) L) L L)) (N 23 L (N 27 L (N 30 (N 33
  L L L) L L) L) L)) (N 32 L L (N 33 (N 12 L L (N 34 L L L)) L L)) L)))) (N 9 (N 18 L L (N 25 L L
  (N 32 L L (N 13 (N 26 L (N 33 L L L) L) L (N 17 L (N 27 (N 34 L L L) L L) (N 24 (N 26 L (N 31 L
  (N 33 (N 34 L L L) L L) L) L) (N 31 (N 33 L (N 26 (N 27 L L L) L L) L) L L) L)))))) L (N 13 (N
  18 L L (N 12 (N 17 L (N 23 (N 25 L L (N 26 L (N 33 L L L) L)) L (N 25 (N 27 L L L) L L)) (N 24
  (N 25 L L (N 26 L (N 33 L L L) L)) (N 31 (N 32 L L (N 25 (N 23 L L (N 26 L (N 27 L L L) L)) L
  L)) L L) L)) (N 17 L L (N 26 L L (N 25 (N 24 L (N 27 L (N 31 (N 32 L L L) L L) L) L) L L))) L))
  L L)) (N 12 (N 13 (N 17 L (N 18 L L (N 9 (N 24 L (N 31 L L (N 27 (N 34 L L L) L L)) (N 25 L (N
  27 (N 34 L L L) L L) L)) L (N 24 (N 25 L (N 31 L (N 32 (N 27 L L (N 23 (N 26 L (N 30 L L (N 34 L
  L L)) L) L L)) L L) L) L) (N 31 (N 32 L (N 25 (N 23 L L (N 27 L L L)) L L) L) L L) L))) (N 18 L
  (N 23 (N 30 L (N 25 L (N 33 L L (N 32 (N 34 L L L) L L)) (N 26 L (N 33 L L L) L)) L) (N 30 (N 24
  (N 9 L (N 25 L L (N 32 L L L)) (N 25 L (N 32 L L L) L)) L (N 27 (N 25 L (N 26 L L (N 32 L L L))
  L) L L)) L L) L) (N 23 (N 30 L (N 25 L (N 33 L L (N 32 (N 34 L L L) L L)) (N 26 L (N 33 L L L)
  L)) L) (N 30 (N 24 (N 9 L (N 25 L L (N 32 L L L)) (N 25 L (N 32 L L L) L)) L (N 9 (N 25 L (N 26
  L L (N 32 L L L)) L) (N 25 (N 27 L (N 34 L L L) L) L L) L)) L L) L))) (N 17 L L (N 26 L L (N 33
  L L (N 18 L (N 27 (N 34 L L L) L L) (N 23 (N 25 L (N 30 L (N 32 (N 34 L L L) L L) L) L) (N 30 (N
  32 L (N 25 (N 27 L L L) L L) L) L L) L))))) L) (N 13 (N 18 L L (N 26 L L (N 33 L L (N 9 (N 25 L
  (N 32 L L L) L) L (N 17 L (N 27 (N 34 L L L) L L) (N 23 (N 24 (N 25 L (N 27 L (N 31 L (N 30 (N
  32 (N 34 L L L) L L) L L) L) L) L) (N 31 (N 32 L (N 25 (N 27 L L L) L L) L) L L) L) (N 24 (N 25
  L L L) L L) L)))))) L L) L)) L (N 8 (N 17 L (N 18 L L (N 13 (N 9 (N 12 (N 23 L (N 24 L L (N 25 L
  L L)) (N 27 (N 24 L (N 31 L L (N 32 L (N 25 L L (N 26 L L L)) L)) (N 25 L (N 26 L (N 31 L (N 30
  L L (N 32 L L (N 33 L L L))) L) L) L)) L L)) (N 26 L L (N 33 L L L)) L) L (N 12 (N 23 L (N 24 (N
  25 L L (N 26 L L L)) L L) (N 25 L (N 27 (N 32 L L (N 33 L L L)) L L) L)) (N 26 L L (N 33 L L L))
  L)) L L)) (N 12 (N 13 (N 18 L (N 23 L (N 30 L L (N 27 (N 32 L (N 25 L L (N 26 L L L)) L) L L))
  (N 25 L (N 27 (N 30 L (N 32 L L (N 33 L L L)) L) L L) L)) (N 23 L (N 30 L L (N 32 L (N 25 L L (N
  26 L L L)) L)) (N 25 L (N 30 L (N 32 L L (N 33 L L L)) L) L))) (N 26 L L (N 33 L L L)) L) (N 13
  (N 18 L L (N 26 L L (N 33 L L L))) L L) L)) (N 9 (N 18 L L (N 13 (N 25 L L (N 24 L (N 26 L (N 33
  L L L) L) L)) L L)) L (N 13 (N 12 (N 18 (N 24 L (N 31 L L (N 25 (N 32 (N 34 L (N 26 L L (N 27 L
  L L)) L) L L) L L)) (N 25 (N 27 L (N 31 L (N 32 (N 33 L L (N 34 L L L)) L L) L) L) L L)) L (N 24
  (N 31 L (N 25 (N 23 L (N 26 L L (N 27 L L L)) (N 27 L (N 33 L L (N 34 L L L)) L)) L (N 26 L (N
  33 L L L) L)) L) (N 31 (N 23 (N 17 L (N 30 L L (N 32 (N 34 L L L) L L)) (N 25 (N 27 L (N 34 L L
  L) L) L (N 26 L (N 33 L L L) L))) L (N 25 (N 27 L (N 26 L L (N 33 L L L)) L) L L)) L L) L)) (N
  26 L L (N 33 L L L)) L) L L)) (N 12 (N 13 (N 26 L (N 33 L L (N 32 (N 34 L L L) L L)) (N 33 L (N
  25 (N 27 L L L) L L) L)) (N 26 L L (N 33 L L L)) L) (N 13 (N 26 L L (N 33 L L L)) L L) L))) L (N
  20 (N 8 (N 25 L (N 32 L L (N 9 (N 33 (N 34 L L L) L L) L L)) (N 32 L (N 9 (N 26 (N 27 L L L) L
  L) L L) L)) (N 9 (N 25 L L (N 32 L L L)) L (N 13 (N 18 L L L) L L)) (N 9 (N 25 L (N 32 L L L) L)
  (N 12 (N 17 L L L) L L) L)) L L))) L) L) L (N 5 L (N 14 (N 19 (N 20 L L (N 23 (N 24 (N 35 L (N
  25 L (N 8 (N 9 L L (N 30 L (N 31 (N 32 L L (N 33 (N 34 (N 12 L (N 13 L L (N 17 L L L)) (N 17 L
  (N 18 L L L) L)) L L) L L)) L L) L)) L (N 9 (N 31 L (N 30 (N 32 L L (N 33 (N 34 (N 12 L (N 13 L
  L (N 18 L L L)) (N 17 L (N 18 L L L) L)) L L) L L)) L L) L) L (N 26 L (N 27 L L (N 33 (N 32 L L
  (N 34 (N 12 (N 13 L L (N 17 L (N 18 (N 30 L (N 31 L L L) L) L L) L)) L (N 13 (N 18 L (N 17 (N 30
  L (N 31 L L L) L) L L) L) L (N 17 (N 18 L (N 30 L (N 31 L L L) L) L) (N 18 (N 30 L (N 31 L L L)
  L) L L) L))) L L)) L L)) (N 27 L (N 34 (N 32 L L (N 33 (N 17 (N 18 L L (N 12 L (N 13 (N 30 L (N
  31 L L L) L) L L) L)) L (N 12 (N 13 L (N 30 L (N 31 L L L) L) L) (N 13 (N 18 L L (N 30 L (N 31 L
  L L) L)) L L) L)) L L)) L L) L)))) (N 26 L (N 12 (N 30 L (N 31 (N 13 L L (N 17 L (N 18 L L L)
  L)) L L) L) L (N 34 (N 32 L L (N 33 (N 13 (N 18 L (N 8 L L (N 27 L L L)) L) L (N 17 (N 18 L (N 8
  L L (N 27 L L L)) L) (N 18 (N 9 L L (N 27 L L L)) L L) L)) L L)) L L)) (N 27 L (N 34 (N 32 L L
  (N 33 (N 17 (N 18 L L (N 9 L (N 12 L L L) L)) L (N 8 (N 12 L (N 13 L L L) L) (N 13 (N 9 L L (N
  18 L L L)) L L) L)) L L)) L L) L))) L) (N 30 (N 35 L (N 31 (N 8 L (N 9 (N 13 L L (N 18 L L L)) L
  (N 12 L (N 17 L L (N 13 (N 33 L L L) L L)) (N 17 L (N 18 (N 34 L L L) L L) L))) (N 12 L (N 9 (N
  13 L L (N 18 L L L)) L (N 13 (N 18 L L (N 33 L L L)) L (N 17 L (N 18 (N 34 L L L) L L) L))) (N
  17 L (N 18 (N 34 L L L) L L) L))) L L) L) (N 31 (N 35 L (N 8 (N 9 L (N 12 L L (N 17 L L L)) (N
  12 L (N 13 L L (N 17 L L L)) (N 17 L (N 18 L L L) L))) (N 9 (N 12 L L (N 17 L L L)) L (N 12 (N
  17 L L (N 33 L L L)) L (N 17 (N 34 L L L) L L))) (N 9 (N 12 L (N 13 L L (N 17 L L L)) (N 17 L (N
  18 L L L) L)) (N 12 (N 17 L L (N 13 (N 18 L L (N 27 L L L)) L L)) L (N 17 (N 18 (N 13 L L (N 26
  L L L)) L L) L L)) (N 12 (N 17 L (N 27 L L (N 33 L L L)) (N 33 L (N 13 (N 26 L L (N 27 L L L)) L
  L) L)) (N 13 (N 18 L L (N 33 L L L)) L (N 17 (N 34 L L L) L L)) (N 17 (N 34 L (N 18 (N 26 L L (N
  27 L L L)) L L) L) (N 18 (N 34 L L L) L L) L)))) L) L L) L) L) (N 24 (N 30 (N 35 L (N 31 (N 9 L
  (N 8 (N 12 L L (N 17 L L L)) L (N 12 (N 17 L L (N 13 L (N 33 L L L) L)) L (N 17 (N 18 L (N 34 L
  L L) L) L L))) (N 13 L (N 8 (N 12 L L (N 17 L L L)) L (N 12 (N 17 L L (N 33 L L L)) L (N 17 (N
  18 L (N 34 L L L) L) L L))) (N 18 L (N 17 (N 34 L L L) L L) L))) (N 8 (N 9 L (N 12 L L (N 17 L L
  L)) (N 12 L (N 13 L L (N 17 L L L)) (N 17 L (N 18 L L L) L))) (N 9 (N 12 L L (N 17 L L L)) L (N
  12 (N 17 L L (N 13 (N 18 L L (N 27 L L L)) L L)) L (N 17 (N 18 (N 13 L L (N 26 L L L)) L L) L
  L))) (N 9 (N 12 L (N 13 L L (N 17 L L L)) (N 17 L (N 18 L L L) L)) (N 12 (N 17 L L (N 33 L L L))
  L (N 17 (N 34 L L L) L L)) (N 12 (N 17 L (N 26 L L (N 34 L L L)) (N 33 L (N 13 (N 18 L L (N 27 L
  L L)) L L) L)) (N 13 (N 18 L L (N 33 L L L)) L (N 17 (N 18 (N 26 L L (N 27 L L L)) L L) L L)) (N
  17 (N 34 L (N 18 (N 13 L L (N 26 L L L)) L L) L) (N 18 (N 34 L L L) L L) L)))) L) L) (N 31 (N 35
  L L L) L L) L) L L) L)) L (N 20 (N 23 (N 24 (N 35 L (N 25 L (N 8 (N 30 L (N 31 (N 9 L L (N 17 L
  (N 18 L L L) L)) L L) L) L (N 34 (N 33 L L (N 32 (N 9 (N 18 L (N 12 L L (N 17 (N 27 L L (N 26 L
  (N 13 L L (N 30 L (N 31 L L L) L)) L)) L L)) L) L (N 17 (N 18 L (N 12 L L (N 27 L L (N 26 L (N
  13 L L (N 30 L (N 31 L L L) L)) L))) L) (N 18 (N 13 L L (N 27 L L (N 26 L (N 12 L L (N 30 L (N
  31 L L L) L)) L))) L L) L)) L L)) L L)) (N 27 L (N 34 (N 33 L L (N 32 (N 17 (N 18 L L (N 8 L (N
  9 (N 13 L L (N 26 L (N 12 L L (N 30 L (N 31 L L L) L)) L)) L L) L)) L (N 8 (N 9 L (N 12 L L (N
  26 L (N 13 L L (N 30 L (N 31 L L L) L)) L)) L) (N 9 (N 13 L L (N 18 L L (N 26 L (N 12 L L (N 30
  L (N 31 L L L) L)) L))) L L) L)) L L)) L L) L)) L) (N 30 (N 35 L (N 31 (N 8 L (N 9 (N 13 L L (N
  18 L L (N 32 L L L))) L (N 17 L (N 12 L L (N 18 (N 34 L L L) L L)) L)) (N 17 L (N 18 (N 34 L L
  L) L L) L)) L L) L) (N 31 (N 35 L (N 8 (N 12 L (N 13 L L (N 17 L L (N 32 L L L))) (N 13 L (N 17
  L L (N 9 (N 18 L L (N 27 L L L)) L L)) (N 17 L (N 27 L L (N 32 L L L)) (N 32 L (N 9 (N 25 L L (N
  27 L L L)) L L) L)))) (N 9 (N 12 L L (N 13 L L (N 18 L L (N 32 L L L)))) L (N 17 (N 34 L L L) L
  L)) (N 17 (N 34 L (N 12 L L (N 18 (N 25 L L (N 27 L L L)) L L)) L) (N 18 (N 34 L L L) L L) L))
  L) L L) L) L) (N 24 (N 30 (N 35 L (N 31 (N 9 L (N 8 (N 12 L L (N 17 L L (N 32 L L L))) L (N 17
  (N 12 L L (N 18 L (N 34 L L L) L)) L L)) (N 18 L (N 17 (N 34 L L L) L L) L)) (N 8 (N 12 L (N 13
  L L (N 17 L L (N 9 (N 18 L L (N 27 L L L)) L L))) (N 13 L (N 17 L L (N 32 L L L)) (N 17 L (N 25
  L L (N 34 L L L)) (N 32 L (N 9 (N 18 L L (N 27 L L L)) L L) L)))) (N 9 (N 12 L L (N 13 L L (N 18
  L L (N 32 L L L)))) L (N 17 (N 12 L L (N 13 L L (N 18 (N 25 L L (N 27 L L L)) L L))) L L)) (N 17
  (N 34 L (N 13 L L (N 18 (N 9 L L (N 25 L L L)) L L)) L) (N 18 (N 34 L L L) L L) L)) L) L) (N 31
  (N 35 L L L) L L) L) L L) L) L (N 23 (N 24 (N 35 L (N 25 L (N 8 (N 30 L (N 31 (N 9 L L (N 17 L
  (N 18 L L L) L)) L L) L) L (N 34 (N 9 (N 18 L (N 12 L L (N 17 (N 27 L L (N 26 L (N 13 L L (N 30
  L (N 31 L L L) L)) L)) L L)) L) L (N 32 (N 33 L L (N 27 L (N 17 (N 18 (N 26 L L (N 12 L (N 13 L
  L L) L)) L L) L L) L)) L L)) L L)) (N 27 L (N 34 (N 17 (N 30 L (N 31 L L L) L) L (N 18 (N 9 L (N
  8 (N 12 L L L) L L) L) L L)) L L) L)) L) (N 30 (N 35 L (N 31 (N 8 L (N 9 (N 13 L L (N 18 L L L))
  L (N 17 L (N 12 L L (N 18 (N 34 L L L) L L)) L)) (N 17 L (N 18 (N 34 L L L) L L) L)) L L) L) (N
  31 (N 35 L (N 8 (N 12 L (N 13 L L (N 17 L L L)) (N 17 L (N 13 L L (N 18 (N 34 L L L) L L)) L))
  (N 9 (N 12 L L (N 18 L L L)) L (N 17 (N 34 L L L) L L)) (N 17 (N 34 L (N 12 L L (N 18 (N 27 L L
  (N 25 (N 26 L L L) L L)) L L)) L) (N 18 (N 34 L L L) L L) L)) L) L L) L) L) (N 24 (N 30 (N 35 L
  (N 31 (N 9 L (N 8 (N 12 L L (N 17 L L L)) L (N 17 (N 12 L L (N 18 L (N 34 L L L) L)) L L)) (N 18
  L (N 17 (N 34 L L L) L L) L)) (N 8 (N 12 L (N 13 L L (N 17 L L L)) (N 17 L (N 13 L L (N 18 (N 34
  L L L) L L)) L)) (N 9 (N 12 L L (N 18 L L L)) L (N 17 (N 12 L L (N 18 (N 13 L L (N 26 (N 25 L L
  (N 27 L L L)) L L)) L L)) L L)) (N 17 (N 34 L (N 18 (N 9 L L (N 13 L L (N 25 (N 26 L L (N 27 L L
  L)) L L))) L L) L) (N 18 (N 34 L L L) L L) L)) L) L) (N 31 (N 35 L L L) L L) L) L L) L))) L (N
  19 (N 20 (N 23 (N 24 (N 35 L (N 25 L (N 8 (N 30 L (N 31 (N 9 L L (N 12 L (N 13 L L L) L)) L L)
  L) L (N 33 (N 34 L L (N 32 (N 9 (N 13 L (N 12 (N 17 L L (N 26 L L (N 27 L (N 18 L L (N 30 L (N
  31 L L L) L)) L))) L L) L) L (N 12 (N 13 L (N 17 L L (N 26 L L (N 27 L (N 18 L L (N 30 L (N 31 L
  L L) L)) L))) L) (N 13 (N 18 L L (N 26 L L (N 27 L (N 17 L L (N 30 L (N 31 L L L) L)) L))) L L)
  L)) L L)) L L)) (N 26 L (N 33 (N 34 L L (N 32 (N 12 (N 13 L L (N 8 L (N 9 (N 18 L L (N 27 L (N
  17 L L (N 30 L (N 31 L L L) L)) L)) L L) L)) L (N 8 (N 9 L (N 17 L L (N 27 L (N 18 L L (N 30 L
  (N 31 L L L) L)) L)) L) (N 9 (N 13 L L (N 18 L L (N 27 L (N 17 L L (N 30 L (N 31 L L L) L)) L)))
  L L) L)) L L)) L L) L)) L) (N 30 (N 35 L (N 31 (N 8 L (N 9 (N 13 L L (N 32 L L L)) L (N 12 L (N
  13 (N 33 L L L) L L) L)) (N 12 L (N 13 (N 33 L L L) L L) L)) L L) L) (N 31 (N 35 L (N 8 (N 12 L
  (N 17 L L (N 18 L L (N 26 L L (N 32 L L L)))) (N 32 L (N 9 (N 17 L L (N 25 L L (N 26 L L L))) L
  L) L)) (N 9 (N 13 L L (N 32 L L L)) L (N 12 (N 33 L L L) L L)) (N 12 (N 33 L (N 13 (N 17 L L (N
  25 L L (N 26 L L L))) L L) L) (N 13 (N 33 L L L) L L) L)) L) L L) L) L) (N 24 (N 30 (N 35 L (N
  31 (N 9 L (N 8 (N 12 L L (N 32 L L L)) L (N 12 (N 13 L (N 33 L L L) L) L L)) (N 13 L (N 12 (N 33
  L L L) L L) L)) (N 8 (N 12 L (N 17 L L (N 18 L L (N 25 L L (N 33 L L L)))) (N 32 L (N 9 (N 13 L
  L (N 26 L L L)) L L) L)) (N 9 (N 13 L L (N 32 L L L)) L (N 12 (N 13 (N 17 L L (N 18 L L (N 25 L
  L (N 26 L L L)))) L L) L L)) (N 12 (N 33 L (N 13 (N 9 L L (N 25 L L L)) L L) L) (N 13 (N 33 L L
  L) L L) L)) L) L) (N 31 (N 35 L L L) L L) L) L L) L) L (N 23 (N 24 (N 35 L (N 25 L (N 8 (N 30 L
  (N 31 (N 9 L L (N 12 L (N 13 L L L) L)) L L) L) L (N 33 (N 9 (N 13 L (N 12 (N 17 L L (N 26 L L
  (N 27 L (N 18 L L (N 30 L (N 31 L L L) L)) L))) L L) L) L (N 32 (N 34 L L (N 26 L (N 12 (N 13 (N
  27 L L (N 17 L (N 18 L L L) L)) L L) L L) L)) L L)) L L)) (N 26 L (N 33 (N 12 (N 30 L (N 31 L L
  L) L) L (N 13 (N 9 L (N 8 (N 17 L L L) L L) L) L L)) L L) L)) L) (N 30 (N 35 L (N 31 (N 8 L (N 9
  (N 13 L L (N 18 L L L)) L (N 12 L (N 13 (N 33 L L L) L L) L)) (N 12 L (N 13 (N 33 L L L) L L)
  L)) L L) L) (N 31 (N 35 L (N 8 (N 12 L (N 17 L L (N 13 (N 33 L L L) L L)) (N 17 L (N 18 L L L)
  L)) (N 9 (N 13 L L (N 17 L L L)) L (N 12 (N 33 L L L) L L)) (N 12 (N 33 L (N 13 (N 17 L L (N 26
  L L (N 25 (N 27 L L L) L L))) L L) L) (N 13 (N 33 L L L) L L) L)) L) L L) L) L) (N 24 (N 30 (N
  35 L (N 31 (N 9 L (N 8 (N 12 L L (N 17 L L L)) L (N 12 (N 13 L (N 33 L L L) L) L L)) (N 13 L (N
  12 (N 33 L L L) L L) L)) (N 8 (N 12 L (N 17 L L (N 13 (N 33 L L L) L L)) (N 17 L (N 18 L L L)
  L)) (N 9 (N 13 L L (N 17 L L L)) L (N 12 (N 13 (N 17 L L (N 18 L L (N 26 L L (N 25 (N 27 L L L)
  L L)))) L L) L L)) (N 12 (N 33 L (N 13 (N 9 L L (N 18 L L (N 25 (N 26 L L (N 27 L L L)) L L))) L
  L) L) (N 13 (N 33 L L L) L L) L)) L) L) (N 31 (N 35 L L L) L L) L) L L) L)) L (N 20 (N 23 (N 24
  (N 35 L (N 25 L (N 8 (N 30 L (N 31 (N 9 L L (N 32 L L L)) L L) L) L (N 9 (N 13 L (N 12 (N 17 L L
  L) L L) L) L L)) (N 26 L (N 27 L (N 32 (N 33 (N 34 L L L) L L) L L) L) L)) L) (N 30 (N 35 L (N
  31 (N 8 L (N 9 (N 13 L L (N 32 L L L)) L (N 12 L (N 17 L L L) L)) (N 12 L (N 9 (N 13 L L L) L L)
  L)) L L) L) (N 31 (N 35 L (N 8 (N 12 L (N 17 L L (N 32 L L L)) (N 32 L (N 9 (N 17 L L (N 25 L L
  (N 26 (N 27 L L L) L L))) L L) L)) (N 9 (N 13 L L (N 32 L L L)) L (N 12 (N 17 L L L) L L)) (N 9
  (N 13 L (N 18 L L L) L) (N 12 (N 17 L L L) L L) L)) L) L L) L) L) (N 24 (N 30 (N 35 L (N 31 (N 9
  L (N 8 (N 12 L L (N 32 L L L)) L (N 12 (N 17 L L L) L L)) (N 13 L (N 8 (N 12 L L L) L L) L)) (N
  8 (N 12 L (N 17 L L (N 9 (N 13 L L (N 18 L L (N 25 L L (N 26 (N 27 L L L) L L)))) L L)) (N 32 L
  (N 9 (N 13 L L (N 18 L L (N 25 L L (N 26 (N 27 L L L) L L)))) L L) L)) (N 9 (N 13 L L (N 32 L L
  L)) L (N 12 (N 17 L L L) L L)) (N 9 (N 13 L (N 18 L L L) L) (N 12 (N 17 L L L) L L) L)) L) L) (N
  31 (N 35 L L L) L L) L) L L) L) L L))) L)) L (S 29 L L L)) (S 22 (S 29 (N 5 L (N 35 L (N 14 (N
  17 (N 18 (N 19 (N 20 L L (N 8 L (N 9 L L (N 13 (N 24 L (N 31 L L (N 25 (N 32 L L L) L L)) (N 25
  (N 32 L L L) L L)) L (N 24 (N 31 L (N 25 (N 32 L L (N 30 (N 34 L (N 26 L L (N 27 L L L)) L) L
  L)) L (N 27 L (N 23 (N 30 L L (N 32 (N 33 L L L) L L)) L L) L)) L) (N 31 (N 23 (N 12 L (N 26 L L
  (N 33 L L L)) (N 26 L (N 33 L L L) L)) L (N 25 (N 26 L (N 27 L L (N 33 L L L)) L) L L)) L L)
  L))) (N 9 L (N 12 (N 23 L (N 30 L L (N 25 (N 32 L L L) L L)) (N 25 (N 32 L L L) L L)) L (N 23 (N
  30 L (N 25 (N 32 L L (N 31 (N 34 L (N 26 L L (N 27 L L L)) L) L L)) L (N 27 L (N 24 (N 31 L L (N
  32 (N 33 L L L) L L)) L L) L)) L) (N 30 (N 24 (N 13 L (N 26 L L (N 33 L L L)) (N 26 L (N 33 L L
  L) L)) L (N 25 (N 26 L (N 27 L L (N 33 L L L)) L) L L)) L L) L)) (N 27 L (N 34 L L (N 32 (N 33 L
  L L) L L)) (N 34 L (N 25 (N 26 L L L) L L) L))))) L (N 20 (N 12 L (N 13 L L (N 9 (N 24 L (N 31 L
  L (N 26 (N 33 L L L) L L)) (N 25 L (N 26 (N 33 L L L) L L) L)) L (N 24 (N 31 L (N 25 L (N 34 L L
  (N 27 L (N 32 (N 33 L L L) L L) L)) (N 27 L (N 34 L L L) L)) L) (N 31 (N 23 (N 8 L (N 25 L L (N
  32 L L L)) (N 25 L (N 32 L L L) L)) L (N 26 (N 25 L (N 27 L L (N 32 L L L)) L) L L)) L L) L)))
  (N 13 L (N 8 (N 23 L (N 30 L L (N 26 (N 33 L L L) L L)) (N 25 L (N 26 (N 33 L L L) L L) L)) L (N
  23 (N 30 L (N 25 L (N 34 L L (N 27 L (N 32 (N 33 L L L) L L) L)) (N 27 L (N 34 L L L) L)) L) (N
  30 (N 24 (N 9 L (N 25 L L (N 32 L L L)) (N 25 L (N 32 L L L) L)) L (N 26 (N 25 L (N 27 L L (N 32
  L L L)) L) L L)) L L) L)) (N 27 L (N 34 L L (N 32 (N 33 L L L) L L)) (N 34 L (N 25 (N 26 L L L)
  L L) L)))) L (N 27 L (N 34 L L L) L))) (N 8 (N 12 L L (N 19 L L (N 13 L (N 9 (N 20 (N 23 L (N 30
  L L (N 26 (N 33 L L L) L L)) (N 25 L (N 26 (N 33 L L L) L L) L)) L (N 27 L (N 34 L L L) L)) L (N
  20 (N 23 L (N 30 L L (N 26 (N 33 L L L) L L)) (N 25 L (N 26 (N 33 L L L) L L) L)) L (N 27 L (N
  34 L L L) L))) (N 20 (N 23 L (N 30 L L (N 32 L (N 25 L L (N 27 L L L)) L)) (N 25 L (N 30 L (N 27
  L L (N 32 L L L)) L) L)) L (N 27 L (N 34 L L L) L))))) L (N 12 (N 20 L L (N 9 L (N 13 (N 19 (N
  23 L (N 30 L L (N 25 (N 32 L L L) L L)) (N 25 (N 32 L L L) L L)) L (N 27 L (N 34 L L L) L)) L (N
  19 (N 23 L (N 30 L L (N 25 (N 32 L L L) L L)) (N 25 (N 32 L L L) L L)) L (N 27 L (N 34 L L L)
  L))) (N 19 (N 23 L (N 30 L L (N 33 L (N 25 (N 26 L L (N 27 L L L)) L L) L)) (N 26 L (N 30 L (N
  27 L L (N 33 L L L)) L) L)) L (N 27 L (N 34 L L L) L)))) L (N 19 (N 20 L L (N 9 L (N 13 (N 23 (N
  30 L (N 27 L L (N 25 (N 24 L L (N 26 L (N 33 L L L) L)) L L)) L) (N 30 (N 34 L L (N 26 L (N 27 L
  L L) L)) L L) L) L (N 23 (N 26 L (N 30 L (N 27 L L (N 34 L L L)) L) L) (N 30 (N 33 L (N 26 (N 25
  L L (N 27 L L L)) L L) L) L L) L)) (N 23 (N 30 L (N 27 L L (N 26 L (N 34 L L L) L)) L) (N 30 (N
  34 L L (N 27 L (N 33 L L L) L)) L L) L))) L (N 20 (N 13 L (N 9 (N 23 (N 30 L (N 27 L L (N 25 L
  (N 32 L L L) L)) L) (N 30 (N 34 L L (N 25 L (N 27 L L L) L)) L L) L) L (N 23 (N 25 L (N 30 L (N
  27 L L (N 34 L L L)) L) L) (N 30 (N 32 L (N 25 (N 26 L L (N 27 L L L)) L L) L) L L) L)) (N 23 (N
  30 L (N 27 L L (N 25 L (N 34 L L L) L)) L) (N 30 (N 34 L L (N 27 L (N 32 L L L) L)) L L) L)) L
  (N 27 L (N 34 L L L) L))))) L) (N 18 (N 9 (N 13 L L (N 19 L L (N 12 L (N 8 (N 20 (N 23 (N 30 L L
  (N 32 L (N 25 L L (N 27 L L L)) L)) L (N 25 L (N 26 (N 32 L L (N 34 L L L)) L L) L)) L (N 27 L
  (N 34 L L L) L)) L (N 20 (N 23 (N 24 L (N 31 L L (N 26 (N 33 L L L) L L)) (N 25 L (N 26 (N 33 L
  L L) L L) L)) L (N 25 L (N 32 L L L) L)) L (N 27 L (N 34 L L L) L))) (N 20 (N 24 L (N 31 L L (N
  32 L (N 25 L L (N 27 L L L)) L)) (N 25 L (N 31 L (N 27 L L (N 32 L L L)) L) L)) L (N 27 L (N 34
  L L L) L))))) L (N 13 (N 20 L L (N 8 L (N 12 (N 19 (N 23 (N 30 L L (N 32 (N 25 L L (N 24 L (N 31
  L L L) L)) L L)) L (N 25 (N 26 L (N 32 L L (N 34 L L L)) L) L L)) L (N 27 L (N 34 L L L) L)) L
  (N 19 (N 23 (N 24 L (N 31 L L (N 25 (N 32 L L L) L L)) (N 25 (N 32 L L L) L L)) L (N 25 (N 26 L
  (N 33 L L L) L) L L)) L (N 27 L (N 34 L L L) L))) (N 19 (N 24 L (N 31 L L (N 33 L (N 25 (N 26 L
  L (N 27 L L L)) L L) L)) (N 26 L (N 31 L (N 27 L L (N 33 L L L)) L) L)) L (N 27 L (N 34 L L L)
  L)))) L (N 19 (N 20 L L (N 8 L (N 12 (N 23 (N 30 L L (N 32 (N 25 L L (N 27 L (N 33 L L L) L)) L
  L)) L (N 25 (N 26 L (N 32 L L (N 34 L L L)) L) L L)) L (N 23 (N 24 (N 25 L L (N 26 L (N 27 L (N
  31 L L L) L) L)) (N 31 (N 33 L (N 26 (N 25 L L (N 27 L L L)) L L) L) L L) L) L (N 25 (N 26 L (N
  33 L L L) L) L L))) (N 24 (N 31 L (N 27 L L (N 26 L (N 34 L L L) L)) L) (N 31 (N 34 L L (N 27 L
  (N 33 L L L) L)) L L) L))) L (N 20 (N 12 L (N 8 (N 23 (N 30 L L (N 32 L (N 25 L L (N 27 L L L))
  L)) L (N 25 L (N 26 (N 32 L L (N 34 L L L)) L L) L)) L (N 23 (N 24 (N 25 L (N 26 L L (N 27 L (N
  31 L L L) L)) L) (N 31 (N 32 L (N 25 (N 26 L L (N 27 L L L)) L L) L) L L) L) L (N 26 (N 25 L (N
  32 L L L) L) L L))) (N 24 (N 31 L (N 27 L L (N 25 L (N 34 L L L) L)) L) (N 31 (N 34 L L (N 27 L
  (N 32 L L L) L)) L L) L)) L (N 27 L (N 34 L L L) L))))) L L) L) L (N 17 (N 18 (N 19 (N 20 L L (N
  8 L (N 9 L L L) L)) L (N 20 (N 12 L (N 13 L L L) L) L L)) (N 8 (N 12 L L (N 19 L L L)) L (N 12
  (N 20 L L L) L L)) L) (N 18 (N 9 (N 13 L L (N 19 L L L)) L (N 13 (N 20 L L L) L L)) L L) L)) L)
  L) (N 5 L (N 14 (N 17 (N 18 (N 19 (N 20 L L (N 34 L L (N 27 L (N 33 (N 32 L L (N 8 L (N 9 L L L)
  L)) L L) L))) L (N 20 (N 34 L L (N 27 L (N 32 (N 33 L L (N 12 L (N 13 L L L) L)) L L) L)) L (N
  27 L (N 34 (N 30 L (N 31 L L (N 32 (N 33 L L L) L L)) (N 32 (N 33 L L L) L L)) L L) L))) (N 8 (N
  12 L L (N 19 L L (N 13 L (N 30 L L (N 23 L (N 26 (N 32 (N 33 L L L) L L) L L) L)) (N 20 (N 23 L
  (N 24 (N 25 L (N 30 L L (N 32 (N 33 L L L) L L)) (N 27 L (N 34 (N 33 L L (N 30 L (N 31 L L L)
  L)) L L) L)) L (N 25 L (N 9 (N 30 L L (N 32 L L L)) L L) L)) (N 25 L (N 30 L (N 33 (N 26 L (N 32
  L L (N 34 L L L)) L) L L) L) L)) L (N 27 L (N 33 (N 34 L L L) L L) L))))) L (N 12 (N 20 L L (N 9
  L (N 30 L L (N 23 L (N 25 (N 32 (N 33 L L L) L L) L L) L)) (N 19 (N 23 L (N 24 (N 26 L (N 30 L L
  (N 32 (N 33 L L L) L L)) (N 27 L (N 34 (N 32 L L (N 30 L (N 31 L L L) L)) L L) L)) L (N 26 L (N
  13 (N 30 L L (N 33 L L L)) L L) L)) (N 26 L (N 30 L (N 32 (N 25 L (N 33 L L (N 34 L L L)) L) L
  L) L) L)) L (N 27 L (N 32 (N 34 L L L) L L) L)))) L (N 19 (N 20 L L (N 9 L (N 30 (N 23 L (N 33 L
  L (N 34 L L L)) L) L L) (N 23 (N 30 L (N 13 (N 26 L (N 24 (N 31 L L (N 25 L (N 32 (N 33 L L L) L
  L) L)) L (N 31 (N 32 (N 25 L (N 33 L L (N 34 L L L)) L) L L) L L)) (N 27 L (N 24 (N 35 L L L) L
  L) L)) L (N 26 L (N 24 (N 31 (N 33 (N 32 L L (N 34 L L L)) L L) L L) L L) L)) L) (N 24 (N 27 L
  (N 30 (N 33 L L (N 34 L L L)) (N 35 (N 25 L L (N 31 L L L)) L L) L) (N 33 (N 30 L (N 25 (N 26 L
  L L) L L) L) L L)) L (N 32 (N 25 L (N 30 (N 33 L L (N 34 L L L)) L L) L) L L)) L))) L (N 20 (N
  13 L (N 30 (N 23 L (N 32 L L (N 34 L L L)) L) L L) (N 23 (N 30 L (N 9 (N 25 L (N 24 (N 31 L L (N
  26 L (N 32 (N 33 L L L) L L) L)) L (N 31 (N 32 L L (N 34 L L L)) L L)) (N 27 L (N 24 (N 35 L L
  L) L L) L)) L (N 25 L (N 24 (N 31 (N 32 (N 33 L L (N 34 L L L)) L L) L L) L L) L)) L) (N 24 (N
  27 L (N 30 (N 32 L L (N 34 L L L)) (N 35 (N 25 L L (N 9 (N 26 L L (N 31 L L L)) L L)) L L) L) (N
  32 (N 30 L (N 25 (N 26 L L L) L L) L) L L)) L (N 33 (N 26 L (N 30 (N 32 L L (N 34 L L L)) L L)
  L) L L)) L)) L (N 27 L (N 34 (N 30 L (N 31 L L (N 32 (N 33 L L L) L L)) L) L L) L))))) L) (N 18
  (N 9 (N 13 L L (N 19 L L (N 12 L (N 31 L L (N 24 L (N 26 (N 32 (N 33 L L L) L L) L L) L)) (N 20
  (N 24 L (N 23 (N 25 L (N 31 L L (N 32 (N 33 L L L) L L)) (N 27 L (N 34 (N 33 L L (N 30 L (N 31 L
  L L) L)) L L) L)) L (N 25 L (N 8 (N 31 L L (N 32 L L L)) L L) L)) (N 25 L (N 31 L (N 33 (N 26 L
  (N 32 L L (N 34 L L L)) L) L L) L) L)) L (N 27 L (N 33 (N 34 L L L) L L) L))))) L (N 13 (N 20 L
  L (N 8 L (N 31 L L (N 24 L (N 25 (N 32 (N 33 L L L) L L) L L) L)) (N 19 (N 24 L (N 23 (N 26 L (N
  31 L L (N 32 (N 33 L L L) L L)) (N 27 L (N 34 (N 32 L L (N 30 L (N 31 L L L) L)) L L) L)) L (N
  26 L (N 12 (N 31 L L (N 33 L L L)) L L) L)) (N 26 L (N 31 L (N 32 (N 25 L (N 33 L L (N 34 L L
  L)) L) L L) L) L)) L (N 27 L (N 32 (N 34 L L L) L L) L)))) L (N 19 (N 20 L L (N 8 L (N 31 (N 24
  L (N 33 L L (N 34 L L L)) L) L L) (N 24 (N 31 L (N 12 (N 26 L (N 23 (N 30 L L (N 25 L (N 32 (N
  33 L L L) L L) L)) L (N 30 (N 32 (N 25 L (N 33 L L (N 34 L L L)) L) L L) L L)) (N 27 L (N 23 (N
  35 L L L) L L) L)) L (N 26 L (N 23 (N 30 (N 33 (N 32 L L (N 34 L L L)) L L) L L) L L) L)) L) (N
  23 (N 27 L (N 31 (N 33 L L (N 34 L L L)) (N 35 (N 25 L L (N 30 L L L)) L L) L) (N 33 (N 31 L (N
  25 (N 26 L L L) L L) L) L L)) L (N 32 (N 25 L (N 31 (N 33 L L (N 34 L L L)) L L) L) L L)) L))) L
  (N 20 (N 12 L (N 31 (N 24 L (N 32 L L (N 34 L L L)) L) L L) (N 24 (N 31 L (N 8 (N 25 L (N 23 (N
  30 L L (N 26 L (N 32 (N 33 L L L) L L) L)) L (N 30 (N 32 L L (N 34 L L L)) L L)) (N 27 L (N 23
  (N 35 L L L) L L) L)) L (N 25 L (N 23 (N 30 (N 32 (N 33 L L (N 34 L L L)) L L) L L) L L) L)) L)
  (N 23 (N 27 L (N 31 (N 32 L L (N 34 L L L)) (N 35 (N 25 L L (N 8 (N 26 L L (N 30 L L L)) L L)) L
  L) L) (N 32 (N 31 L (N 25 (N 26 L L L) L L) L) L L)) L (N 33 (N 26 L (N 31 (N 32 L L (N 34 L L
  L)) L L) L) L L)) L)) L (N 27 L (N 34 (N 31 L (N 30 L L (N 32 (N 33 L L L) L L)) L) L L) L)))))
  L L) L) L (N 17 (N 18 (N 19 (N 20 L L (N 8 L (N 9 L L L) L)) L (N 20 (N 12 L (N 13 L L L) L) L
  L)) (N 8 (N 12 L L (N 19 L L L)) L (N 12 (N 20 L L L) L L)) L) (N 18 (N 9 (N 13 L L (N 19 L L
  L)) L (N 13 (N 20 L L L) L L)) L L) L)) L) L) (S 29 L L L) L)) (S 16 L L L)) (S 11 L L L))))))
  (S 21 L L (S 28 L L (S 2 L (S 4 L (S 7 (S 11 (S 16 L (S 22 L L (S 29 L L (N 5 L L (N 14 L L (N
  17 (N 18 (N 19 L (N 20 L (N 27 (N 34 L L L) L L) (N 25 (N 23 L (N 24 L (N 27 (N 34 L (N 32 (N 35
  L L L) L L) L) (N 34 (N 35 (N 32 L (N 8 L L (N 9 L L L)) L) L L) L L) L) (N 13 (N 9 L (N 32 (N 8
  L L (N 30 L (N 35 L L L) L)) L L) (N 31 L (N 32 (N 35 L L L) L L) L)) (N 26 (N 27 (N 34 L (N 35
  L L L) L) (N 34 (N 30 L (N 32 (N 35 L L L) L L) L) L L) L) L L) L)) (N 24 L (N 12 (N 8 L (N 32
  (N 9 L L (N 31 L (N 35 L L L) L)) L L) (N 30 L (N 32 (N 35 L L L) L L) L)) (N 26 (N 27 (N 34 L
  (N 35 L L L) L) (N 34 (N 31 L (N 32 (N 35 L L L) L L) L) L L) L) L L) L) L)) (N 27 (N 23 L L (N
  24 L L L)) L L) L)) (N 20 L (N 26 (N 23 L (N 24 L (N 27 (N 34 L (N 33 (N 35 L L L) L L) L) (N 34
  (N 35 (N 33 L (N 12 L L (N 13 L L L)) L) L L) L L) L) (N 9 (N 13 L (N 33 (N 12 L L (N 30 L (N 35
  L L L) L)) L L) (N 31 L (N 33 (N 35 L L L) L L) L)) (N 25 (N 27 (N 34 L (N 35 L L L) L) (N 34 (N
  30 L (N 33 (N 35 L L L) L L) L) L L) L) L L) L)) (N 24 L (N 8 (N 12 L (N 33 (N 13 L L (N 31 L (N
  35 L L L) L)) L L) (N 30 L (N 33 (N 35 L L L) L L) L)) (N 25 (N 27 (N 34 L (N 35 L L L) L) (N 34
  (N 31 L (N 33 (N 35 L L L) L L) L) L L) L) L L) L) L)) (N 27 (N 23 L L (N 24 L L L)) L L) L) L))
  L (N 19 L (N 20 L (N 27 (N 23 L (N 34 (N 30 L (N 35 L L L) L) L L) L) L L) (N 8 (N 23 L (N 25 (N
  30 L (N 32 L L L) L) L L) L) (N 25 (N 23 L (N 30 (N 32 L L L) L L) L) L L) L)) (N 20 L (N 9 (N
  12 (N 23 L (N 26 (N 30 L (N 33 L L L) L) L L) L) (N 26 (N 23 L (N 30 (N 33 L L L) L L) L) L L)
  L) (N 12 (N 23 L (N 26 (N 30 L (N 33 L L L) L) L L) L) (N 26 (N 23 L (N 30 (N 33 L L L) L L) L)
  L L) L) L) L))) L (N 18 (N 19 L (N 20 L (N 27 (N 24 L (N 34 (N 31 L (N 35 L L L) L) L L) L) L L)
  (N 9 (N 24 L (N 25 (N 31 L (N 32 L L L) L) L L) L) (N 25 (N 24 L (N 31 (N 32 L L L) L L) L) L L)
  L)) (N 20 L (N 8 (N 13 (N 24 L (N 26 (N 31 L (N 33 L L L) L) L L) L) (N 26 (N 24 L (N 31 (N 33 L
  L L) L L) L) L L) L) (N 13 (N 24 L (N 26 (N 31 L (N 33 L L L) L) L L) L) (N 26 (N 24 L (N 31 (N
  33 L L L) L L) L) L L) L) L) L)) L L)))))) (S 22 L L (S 29 L L (N 5 L L (N 14 L L (N 27 (N 34 (N
  35 L (N 8 (N 9 (N 19 L (N 25 L (N 32 L L (N 33 (N 20 L (N 30 L (N 31 L (N 17 (N 18 L L (N 23 L L
  L)) L (N 18 (N 24 L L L) L L)) L) L) L) L L)) (N 20 (N 26 L (N 33 L L L) L) (N 23 (N 26 L (N 12
  L L (N 13 (N 24 L (N 30 L L (N 31 L L L)) L) L L)) L) (N 24 (N 26 L (N 13 L L (N 12 (N 30 L L (N
  31 L L L)) L L)) L) (N 26 (N 30 (N 33 L (N 12 L L (N 13 (N 17 L L (N 18 L L L)) L L)) L) L (N 31
  (N 18 L (N 32 L L L) L) L L)) L L) L) L) L)) (N 17 (N 18 L (N 20 L (N 12 L L (N 13 (N 23 L (N 30
  L L (N 31 L L L)) (N 24 L (N 30 L L L) L)) L L)) L) L) (N 18 (N 20 L (N 13 L L (N 12 (N 23 L (N
  30 L L (N 31 L L L)) (N 24 L (N 31 L L L) L)) L L)) L) (N 20 (N 26 L (N 33 L L L) L) (N 12 (N 13
  (N 26 L (N 33 L L L) L) L (N 23 L (N 30 L L (N 31 (N 33 L L L) L L)) (N 25 L (N 32 L L (N 30 L
  (N 24 (N 26 L L L) L L) L)) L))) L (N 13 (N 24 L (N 31 L L (N 30 (N 33 L L L) L L)) (N 25 L (N
  32 L L (N 31 L (N 23 (N 26 L L L) L L) L)) L)) L L)) L) L) L)) (N 12 (N 17 L (N 19 (N 18 L (N 20
  L L (N 25 L (N 32 L L L) L)) (N 20 L (N 23 L (N 30 L L L) L) L)) L (N 18 (N 20 L (N 13 (N 26 L
  (N 33 L L L) L) L (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 31 L L L) L))) L) (N 20 (N 13 L L
  (N 26 L (N 33 L L L) L)) L L) L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L) (N 19 (N
  20 L L L) L L) L)) (N 13 (N 17 (N 18 L (N 19 L L (N 20 L L L)) (N 19 L (N 20 L (N 23 L (N 30 L L
  L) L) L) L)) (N 19 (N 20 L L (N 18 L (N 25 L (N 32 L L L) L) L)) L (N 20 (N 18 L (N 26 L (N 33 L
  L L) L) L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L) (N 19 (N 20 L L L) L L) L))
  (N 18 (N 20 L L (N 17 L (N 19 L L L) L)) L (N 20 (N 17 L (N 19 L L L) L) L L)) (N 17 (N 18 L (N
  19 L L (N 20 L L L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 19 (N 20 L L (N 18 L (N
  24 (N 25 L (N 32 L L L) L) L L) L)) L (N 20 (N 18 L (N 26 L (N 33 L L L) L) L) L L)) (N 18 (N 19
  L (N 20 L (N 24 L (N 31 L L L) L) L) L) (N 19 (N 20 L L L) L L) L))) (N 13 (N 17 (N 18 L (N 19 L
  L (N 20 L L L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 19 (N 18 L (N 20 L L (N 25 L
  (N 32 L L L) L)) (N 20 L (N 23 (N 30 L (N 26 L L (N 32 L L L)) L) (N 25 L L (N 33 L L L)) L) L))
  L (N 18 (N 20 L (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 30 L L L) L)) L) (N 20 (N 26 L (N 33
  L L L) L) L L) L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N 20 L L L) L L)
  L)) (N 18 (N 24 L L (N 17 L (N 19 L L (N 20 L L L)) L)) L (N 17 (N 19 L (N 20 L (N 23 L (N 30 L
  L L) L) L) L) (N 19 (N 20 L L L) L L) L)) L)) (N 13 (N 12 (N 17 L (N 20 L (N 23 L (N 30 L L (N
  33 L L L)) (N 26 L (N 30 L L (N 33 L L L)) L)) (N 18 (N 19 L (N 23 L (N 30 L L (N 31 L L L)) (N
  24 L (N 31 L L L) L)) L) (N 19 (N 25 L (N 32 L L L) L) (N 23 L (N 30 L L (N 31 (N 32 L L L) L
  L)) (N 26 L (N 32 (N 25 L (N 31 L L L) L) L L) L)) L) L)) (N 20 L (N 18 (N 19 L (N 24 L (N 31 L
  L L) L) L) (N 19 (N 23 L (N 30 L L (N 31 (N 24 L (N 33 L L L) L) L L)) (N 25 L (N 26 L (N 24 (N
  31 L L L) L L) L) L)) (N 23 L (N 30 L L (N 31 (N 24 L (N 32 L L L) L) L L)) (N 26 L (N 30 L (N
  24 (N 31 L L L) L L) L) L)) L) L) L)) (N 17 (N 18 L (N 20 L L (N 19 L (N 23 L (N 25 (N 30 L L (N
  31 L L L)) L L) (N 24 L (N 31 L L L) L)) L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N
  19 (N 20 L L (N 18 L (N 25 L (N 32 L L L) L) L)) L (N 20 (N 18 L (N 25 L (N 32 L L L) L) L) L
  L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L) (N 20 (N 19 L (N 24 (N 31 L (N 25 L L (N
  33 L L L)) L) (N 26 L L (N 32 L L L)) L) L) L L) L)) (N 17 (N 18 L (N 19 L (N 20 L (N 23 L (N 30
  L L (N 31 L L L)) (N 24 L (N 30 L L L) L)) (N 23 L (N 30 L L L) L)) (N 20 L (N 24 L (N 31 L L L)
  L) L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L (N
  31 L L L)) (N 24 L (N 30 L L L) L)) (N 23 L (N 30 L L L) L)) (N 20 L (N 24 L (N 31 L L L) L) L))
  (N 19 (N 20 L (N 25 L (N 32 L L (N 33 L L L)) (N 26 L (N 32 L L L) L)) (N 25 L (N 32 L L L) L))
  (N 20 (N 25 L (N 32 L L (N 33 L L L)) (N 26 L (N 32 L L L) L)) L (N 23 (N 25 L (N 30 L L L) L)
  (N 30 (N 32 L L L) L L) L)) (N 20 (N 25 L (N 32 L L L) L) (N 24 (N 25 L (N 33 L L L) L) (N 31 (N
  33 L L L) L L) L) L)) (N 19 (N 20 L (N 25 L (N 32 L L L) L) L) (N 20 (N 25 L (N 32 L L L) L) (N
  23 (N 25 L (N 30 L L L) L) (N 30 (N 32 L L L) L L) L) L) L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30
  L L L) L) L) L) (N 19 (N 20 L (N 26 L (N 33 L L L) L) L) (N 20 (N 26 L (N 33 L L L) L) (N 23 (N
  26 L (N 30 L (N 24 (N 31 L L L) L L) L) L) (N 30 (N 31 (N 24 L (N 26 L L L) L) L L) L L) L) L)
  L) L))) (N 12 (N 17 L (N 20 (N 18 L (N 19 L L (N 24 (N 25 L (N 32 L L L) L) L L)) (N 19 L (N 23
  L (N 30 L L L) L) L)) L (N 18 (N 19 L (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 31 L L L) L))
  L) (N 19 (N 25 L (N 32 L L L) L) L L) L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L) (N
  19 (N 20 L L L) L L) L)) (N 20 (N 26 L L (N 19 L (N 17 L L (N 18 L L L)) L)) L (N 17 (N 18 L (N
  19 L L L) L) (N 19 (N 18 L (N 25 L (N 32 L L L) L) L) L L) L)) (N 17 (N 18 L (N 19 L L (N 20 L L
  L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 20 (N 18 L (N 19 L L (N 24 (N 25 L (N 32 L
  L L) L) L L)) (N 19 L (N 25 L (N 32 L L L) L) L)) L (N 18 (N 19 L (N 23 L (N 30 L L L) L) L) (N
  19 (N 25 L (N 32 L L L) L) L L) L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N
  20 L L L) L L) L))) L)) (N 9 (N 12 (N 13 (N 18 L (N 19 (N 17 L (N 20 L L (N 25 L (N 32 L L L)
  L)) (N 20 L (N 24 L (N 31 L L L) L) L)) L (N 20 L (N 17 (N 26 L (N 33 L L L) L) L L) L)) (N 20 L
  (N 17 (N 19 L (N 23 L (N 30 L L L) L) L) L L) L)) (N 17 (N 18 L (N 19 L L (N 20 L L L)) (N 19 L
  (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 19 (N 20 L L (N 18 L (N 25 L (N 32 L L L) L) L)) L (N
  20 (N 18 L (N 26 L (N 33 L L L) L) L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L)
  (N 19 (N 20 L L L) L L) L)) (N 17 (N 18 L (N 19 L L (N 20 L (N 23 L (N 26 (N 30 L L (N 31 L L
  L)) L L) (N 24 L (N 31 L L L) L)) L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 19 (N 20
  L L (N 18 L (N 25 L (N 32 L L L) L) L)) L (N 20 (N 18 L (N 26 L (N 33 L L L) L) L) L L)) (N 18
  (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L) (N 19 (N 20 L (N 24 (N 31 L (N 26 L L (N 32 L L
  L)) L) (N 25 L L (N 33 L L L)) L) L) L L) L))) (N 17 (N 23 L L (N 18 L (N 19 L L (N 20 L L L))
  L)) L (N 18 (N 19 L (N 20 L (N 13 L L (N 23 L L (N 30 L L L))) L) L) (N 19 (N 20 L L L) L L) L))
  (N 13 (N 18 L (N 19 (N 17 L (N 20 L L (N 23 (N 25 L (N 32 L L L) L) L L)) (N 20 L (N 24 L (N 31
  L L L) L) L)) L (N 17 (N 20 L (N 23 L (N 26 (N 30 L L (N 31 L L L)) L L) (N 24 L (N 30 L L L)
  L)) L) (N 20 (N 26 L (N 33 L L L) L) L L) L)) (N 17 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L)
  L) (N 19 (N 20 L L L) L L) L)) (N 17 (N 18 L (N 19 L L (N 20 L L L)) (N 19 L (N 20 L (N 23 L (N
  30 L L L) L) L) L)) (N 19 (N 20 L L (N 18 L (N 23 (N 25 L (N 32 L L L) L) L L) L)) L (N 20 (N 18
  L (N 26 L (N 33 L L L) L) L) L L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N
  20 L L L) L L) L)) L)) (N 19 (N 25 L L (N 20 L (N 17 L L (N 18 L L L)) L)) L (N 17 (N 18 L (N 20
  L L L) L) (N 20 (N 18 L (N 25 L L (N 32 L L L)) L) L L) L)) (N 13 (N 12 (N 20 L (N 17 (N 18 L (N
  19 L L (N 24 L (N 31 L L L) L)) (N 19 L (N 23 L (N 30 L L L) L) L)) L (N 18 (N 19 L (N 24 L (N
  31 L L L) L) L) (N 19 (N 24 (N 31 L (N 26 L L (N 32 L L L)) L) (N 25 L L (N 33 L L L)) L) L L)
  L)) (N 17 (N 18 L (N 19 L L L) L) (N 19 (N 18 L (N 25 L (N 32 L L L) L) L) L L) L)) (N 17 (N 23
  L L (N 18 L (N 19 L L (N 20 L L L)) L)) L (N 18 (N 19 L (N 20 L (N 23 L L (N 30 L L L)) L) L) (N
  19 (N 20 L L L) L L) L)) (N 17 (N 18 L (N 19 L L (N 20 L (N 24 L (N 31 L L L) L) L)) (N 19 L (N
  20 L (N 23 L (N 30 L L L) L) L) L)) (N 19 (N 20 L L (N 18 L (N 23 (N 25 L (N 32 L L L) L) L L)
  L)) L (N 20 (N 18 L (N 25 L (N 32 L L L) L) L) L L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L L)
  L) L) L) (N 19 (N 20 L (N 26 L (N 33 L L L) L) L) L L) L))) (N 12 (N 17 (N 18 L (N 19 L L (N 20
  L L L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 19 (N 20 L L (N 18 L (N 25 L (N 32 L L
  L) L) L)) L (N 20 (N 18 L (N 24 (N 25 L (N 32 L L L) L) L L) L) L L)) (N 18 (N 19 L (N 20 L (N
  24 L (N 31 L L L) L) L) L) (N 19 (N 20 L L L) L L) L)) (N 17 (N 20 L L (N 18 L (N 19 L L L) L))
  L (N 20 (N 18 L (N 19 L L L) L) L L)) (N 17 (N 18 L (N 19 L L (N 20 L L L)) (N 19 L (N 20 L (N
  23 L (N 30 L L L) L) L) L)) (N 19 (N 20 L L (N 18 L (N 23 (N 25 L (N 32 L L L) L) L L) L)) L (N
  20 (N 18 L (N 24 (N 25 L (N 32 L L L) L) L L) L) L L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L
  L) L) L) L) (N 19 (N 20 L L L) L L) L))) L)) (N 9 (N 12 (N 13 (N 18 L (N 20 L (N 24 L (N 31 L L
  (N 33 L L L)) (N 26 L (N 31 L L (N 33 L L L)) L)) (N 17 (N 19 L (N 23 L (N 30 L L (N 31 L L L))
  (N 24 L (N 30 L L L) L)) L) (N 19 (N 25 L (N 32 L L L) L) (N 24 L (N 31 L L (N 30 (N 32 L L L) L
  L)) (N 26 L (N 32 (N 25 L (N 30 L L L) L) L L) L)) L) L)) (N 20 L (N 17 (N 19 L (N 23 L (N 30 L
  L L) L) L) (N 19 (N 23 (N 30 L (N 24 L L (N 26 L L L)) L) (N 30 (N 31 L L (N 33 L L L)) L L) L)
  (N 23 (N 30 L (N 24 L L (N 25 L L L)) L) (N 30 (N 31 L L (N 32 L L L)) L L) L) L) L) L)) (N 17
  (N 18 L (N 19 L L (N 20 L L L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 20 (N 18 L (N
  19 L L (N 25 L (N 32 L L L) L)) (N 19 L (N 23 (N 30 L (N 25 L L (N 33 L L L)) L) (N 26 L L (N 32
  L L L)) L) L)) L (N 18 (N 19 L (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 30 L L L) L)) L) (N 19
  (N 25 L (N 32 L L L) L) L L) L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N 20
  L L L) L L) L)) (N 17 (N 18 L (N 19 L (N 20 L (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 30 L L
  L) L)) (N 24 L (N 31 L L L) L)) (N 20 L (N 23 L (N 30 L L L) L) L)) (N 19 L (N 20 L (N 23 L (N
  30 L L L) L) L) L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 30 L L L)
  L)) (N 24 L (N 31 L L L) L)) (N 20 L (N 23 L (N 30 L L L) L) L)) (N 19 (N 20 L (N 25 L (N 32 L L
  (N 33 L L L)) (N 26 L (N 32 L L L) L)) (N 25 L (N 32 L L L) L)) (N 20 (N 25 L (N 32 L L (N 33 L
  L L)) (N 26 L (N 32 L L L) L)) L (N 24 (N 25 L (N 31 L L L) L) (N 31 (N 32 L L L) L L) L)) (N 20
  (N 25 L (N 32 L L L) L) (N 23 (N 25 L (N 33 L L L) L) (N 30 (N 33 L L L) L L) L) L)) (N 19 (N 20
  L (N 26 L (N 33 L L L) L) L) (N 20 (N 26 L (N 33 L L L) L) (N 23 (N 26 L (N 30 L L L) L) (N 30
  (N 33 L L L) L L) L) L) L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N 20 L (N
  25 L (N 32 L L L) L) L) (N 20 (N 25 L (N 32 L L L) L) (N 23 (N 25 L (N 30 L (N 24 (N 31 L L L) L
  L) L) L) (N 30 (N 31 (N 24 L (N 25 L L L) L) L L) L L) L) L) L) L))) (N 13 (N 18 L (N 20 (N 17 L
  (N 19 L L (N 23 (N 25 L (N 32 L L L) L) L L)) (N 19 L (N 24 L (N 31 L L L) L) L)) L (N 17 (N 19
  L (N 23 L (N 25 (N 30 L L (N 31 L L L)) L L) (N 24 L (N 30 L L L) L)) L) (N 19 (N 25 L (N 32 L L
  L) L) L L) L)) (N 17 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N 20 L L L) L L) L))
  (N 20 (N 26 L L (N 19 L (N 17 L L (N 18 L L L)) L)) L (N 17 (N 18 L (N 19 L L L) L) (N 19 (N 18
  L (N 25 L (N 32 L L L) L) L) L L) L)) (N 17 (N 18 L (N 20 L L (N 19 L (N 24 L (N 31 L L L) L)
  L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 19 (N 20 L L (N 18 L (N 25 L (N 32 L L L)
  L) L)) L (N 20 (N 18 L (N 23 (N 25 L (N 32 L L L) L) L L) L) L L)) (N 18 (N 19 L (N 20 L (N 23 L
  (N 30 L L L) L) L) L) (N 20 (N 19 L (N 25 L (N 32 L L L) L) L) L L) L))) L) (N 12 (N 13 (N 20 L
  (N 18 (N 17 L (N 19 L L (N 23 L (N 30 L L L) L)) (N 19 L (N 23 L (N 30 L L L) L) L)) L (N 17 (N
  19 L (N 23 L (N 30 L L L) L) L) (N 19 (N 23 (N 30 L (N 26 L L (N 32 L L L)) L) (N 25 L L (N 33 L
  L L)) L) L L) L)) (N 17 (N 18 L (N 19 L L L) L) (N 19 (N 18 L (N 25 L (N 32 L L L) L) L) L L)
  L)) (N 18 (N 24 L L (N 17 L (N 19 L L (N 20 L L L)) L)) L (N 17 (N 19 L (N 20 L (N 23 L (N 30 L
  L L) L) L) L) (N 19 (N 20 L L L) L L) L)) (N 17 (N 18 L (N 19 L L (N 20 L L L)) (N 19 L (N 20 L
  (N 23 L (N 30 L L L) L) L) L)) (N 19 (N 18 L (N 20 L L (N 24 (N 25 L (N 32 L L L) L) L L)) (N 20
  L (N 26 L (N 33 L L L) L) L)) L (N 18 (N 20 L (N 23 L (N 30 L L L) L) L) (N 20 (N 25 L (N 32 L L
  L) L) L L) L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N 20 L L L) L L) L)))
  (N 13 (N 17 (N 18 L (N 19 L L (N 20 L L L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 19
  (N 20 L L (N 18 L (N 25 L (N 32 L L L) L) L)) L (N 20 (N 18 L (N 23 (N 25 L (N 32 L L L) L) L L)
  L) L L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N 20 L L L) L L) L)) (N 18
  (N 20 L L (N 17 L (N 19 L L L) L)) L (N 20 (N 17 L (N 19 L L L) L) L L)) (N 17 (N 18 L (N 19 L L
  (N 20 L L L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 19 (N 20 L L (N 18 L (N 24 (N 25
  L (N 32 L L L) L) L L) L)) L (N 20 (N 18 L (N 23 (N 25 L (N 32 L L L) L) L L) L) L L)) (N 18 (N
  19 L (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N 20 L L L) L L) L))) L) L)) L) (N 35 (N 8 (N
  9 (N 19 L (N 32 L L (N 33 (N 26 L (N 30 L (N 31 L (N 17 (N 20 L (N 12 L L (N 13 (N 18 L L (N 23
  L L L)) L L)) L) L (N 18 (N 20 L (N 24 L L L) L) L L)) L) L) L) L L)) (N 17 (N 20 L (N 32 L L (N
  25 L (N 30 L (N 18 (N 31 L (N 33 (N 26 L (N 12 L L (N 13 L L L)) L) L L) L) L L) L) L)) L) (N 18
  (N 20 L (N 13 L L (N 12 (N 30 L L (N 31 L L L)) L L)) L) (N 20 (N 26 L (N 25 L (N 30 (N 33 L (N
  12 L L (N 13 (N 23 L L (N 24 L L L)) L L)) L) L (N 31 (N 24 L (N 32 L L L) L) L L)) (N 32 L (N
  23 (N 24 L (N 12 L L (N 13 (N 33 L L L) L L)) L) (N 33 (N 12 L L (N 13 L L L)) L L) L) L)) L) L
  L) L) L)) (N 12 (N 17 L (N 30 L L (N 31 (N 24 L (N 18 (N 13 L L (N 19 L L (N 20 L (N 32 L L L)
  L))) L L) L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 (N 13 L L (N 32 L L (N 33 L L L))) L L)
  L) L) L) (N 19 (N 20 (N 13 L L (N 24 (N 31 L L L) L L)) L L) L L) L)) (N 13 (N 17 (N 19 L (N 32
  L L (N 20 L (N 26 (N 33 L L L) L L) L)) (N 20 L (N 18 (N 33 L L L) L L) L)) (N 19 (N 30 L L (N
  18 L (N 24 (N 31 L L L) L L) L)) L (N 20 (N 18 L (N 26 L (N 33 L L L) L) L) L L)) (N 18 (N 19 L
  (N 20 L (N 24 L (N 31 L L L) L) L) L) (N 19 (N 20 (N 31 L L L) L L) L L) L)) (N 18 (N 20 L L (N
  19 L (N 17 (N 32 L L L) L L) L)) L (N 20 (N 17 L (N 19 (N 30 L L L) L L) L) L L)) (N 17 (N 19 L
  (N 32 L L (N 20 L (N 26 (N 33 L L L) L L) L)) (N 20 L (N 18 (N 26 (N 33 L L L) L L) L L) L)) (N
  19 (N 30 L L (N 18 L (N 24 (N 31 L L L) L L) L)) L (N 20 (N 18 L (N 26 L (N 33 (N 30 L L (N 31 L
  L L)) L L) L) L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 (N 32 L L (N 33 L L L)) L L) L) L) L)
  (N 19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L))) (N 13 (N 17 (N 19 L (N 32 L L (N 20 L (N 30 L
  (N 33 (N 18 L L (N 23 L (N 26 L L L) L)) L L) L) L)) (N 20 L (N 18 (N 33 L L L) L L) L)) (N 19
  (N 30 L L (N 18 L (N 20 (N 31 L L L) L L) L)) L (N 18 (N 20 L (N 33 L L L) L) (N 20 (N 26 L (N
  31 L L (N 30 (N 23 L (N 33 L L L) L) L L)) L) L L) L)) (N 18 (N 19 L (N 33 L L L) L) (N 19 (N 30
  L L L) L L) L)) (N 18 (N 24 L L (N 23 L (N 25 (N 26 L L L) L L) L)) L (N 17 (N 19 L (N 20 L (N
  23 L (N 24 L L (N 25 (N 26 L L L) L L)) L) L) L) (N 19 (N 30 L L L) L L) L)) L)) (N 13 (N 12 (N
  17 L (N 30 L L (N 31 (N 18 L (N 20 L L (N 19 (N 24 L (N 25 L (N 32 L L L) L) L) L L)) L) L L))
  (N 20 L (N 33 L L (N 30 L (N 18 (N 19 L (N 24 L (N 31 L (N 25 (N 32 L L L) L L) L) L) L) L L)
  L)) L)) (N 17 (N 19 L (N 32 L L (N 20 L (N 18 (N 33 L L L) L L) L)) (N 20 L (N 32 L L L) L)) (N
  19 (N 30 L L (N 18 L (N 31 (N 20 L L (N 23 L L (N 24 L (N 26 L L L) L))) L L) L)) L (N 20 (N 31
  L L L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L (N 33 L L (N 25 (N 32 L L L) L L)) L) L) L)
  L) (N 20 (N 31 L L L) L L) L)) (N 17 (N 19 L (N 32 L L (N 20 L (N 18 (N 33 L L L) L L) L)) (N 20
  L (N 32 L L L) L)) (N 30 (N 19 L (N 32 L L (N 33 L L L)) (N 24 L (N 31 (N 18 L (N 20 L L L) L) L
  L) L)) L (N 31 (N 18 L (N 20 L L L) L) L L)) (N 18 (N 19 L (N 33 L L L) L) (N 30 (N 19 L (N 33 L
  L L) L) L L) L))) (N 12 (N 17 L (N 30 L L (N 31 (N 24 L (N 18 (N 20 L L (N 19 L (N 32 L L L) L))
  L L) L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 (N 32 L L (N 33 L L L)) L L) L) L) L) (N 19 (N
  20 (N 24 (N 31 L L L) L L) L L) L L) L)) (N 20 (N 26 L L (N 25 L (N 23 (N 24 L L L) L L) L)) L
  (N 17 (N 19 L (N 32 L L L) L) (N 19 (N 18 L (N 25 L (N 26 L L (N 23 (N 24 L L L) L L)) L) L) L
  L) L)) (N 17 (N 19 L (N 32 L L (N 18 (N 20 L (N 24 L (N 25 (N 26 L L L) L L) L) L) L L)) (N 20 L
  (N 32 L L L) L)) (N 20 (N 18 L (N 19 (N 30 L L (N 24 (N 31 L L L) L L)) L (N 24 (N 31 L L L) L
  L)) (N 25 L (N 24 (N 30 L L L) L L) L)) L (N 30 (N 19 L (N 32 L L L) L) L L)) (N 18 (N 19 L (N
  20 L (N 23 L (N 24 L (N 26 (N 33 L L L) L L) L) L) L) L) (N 19 (N 30 L L L) L L) L))) L)) (N 9
  (N 12 (N 13 (N 18 L (N 31 L L (N 30 (N 17 L (N 23 L L L) L) L L)) (N 20 L (N 17 (N 19 L (N 23 L
  (N 30 L L L) L) L) L L) L)) (N 17 (N 19 L (N 33 L L (N 25 (N 32 L L L) L L)) (N 20 L (N 33 L L
  L) L)) (N 19 (N 31 L L (N 23 (N 30 L L L) L L)) L (N 20 (N 18 L (N 26 L (N 33 L L L) L) L) L L))
  (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L) (N 19 (N 31 L L L) L L) L)) (N 17 (N 19 L (N
  33 L L (N 18 (N 32 L L L) L L)) (N 20 L (N 33 L L L) L)) (N 19 (N 31 L L (N 18 L (N 20 (N 30 L L
  L) L L) L)) L (N 20 (N 18 L (N 26 L (N 30 L L (N 31 (N 23 L L (N 24 L (N 25 L L L) L)) L L)) L)
  L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L (N 32 L L (N 26 (N 33 L L L) L L)) L) L) L) L) (N
  19 (N 31 L L L) L L) L))) (N 17 (N 23 L L (N 24 L (N 25 (N 26 L L L) L L) L)) L (N 18 (N 19 L (N
  20 L (N 13 L L (N 23 L L (N 24 L (N 25 (N 26 L L L) L L) L))) L) L) (N 19 (N 31 L L L) L L) L))
  (N 13 (N 18 L (N 31 L L (N 30 (N 23 L (N 17 (N 19 L L (N 20 L (N 32 L L L) L)) L L) L) L L)) (N
  17 (N 19 L (N 20 L (N 23 L (N 30 (N 32 L L (N 33 L L L)) L L) L) L) L) (N 19 (N 20 (N 23 (N 30 L
  L L) L L) L L) L L) L)) (N 17 (N 19 L (N 18 (N 32 L L (N 20 L (N 26 (N 33 L L L) L L) L)) L (N
  20 L (N 23 L (N 30 (N 32 L L (N 33 L L L)) L L) L) L)) (N 20 L (N 18 (N 26 (N 33 L L L) L L) L
  L) L)) (N 19 (N 31 L L (N 23 (N 30 L L L) L L)) L (N 20 (N 18 L (N 26 L (N 33 (N 30 L L (N 31 L
  L L)) L L) L) L) L L)) (N 18 (N 19 L (N 20 L (N 23 L (N 24 L (N 31 L L L) L) L) L) L) (N 19 (N
  31 L L L) L L) L)) L)) (N 19 (N 25 L L (N 26 L (N 23 (N 24 L L L) L L) L)) L (N 17 (N 20 L (N 18
  (N 33 (N 25 L L (N 23 L (N 26 L L L) L)) L L) L L) L) (N 20 (N 18 L (N 25 L L (N 23 (N 24 L L L)
  L L)) L) L L) L)) (N 13 (N 12 (N 20 L (N 33 L L (N 32 (N 25 L (N 19 (N 17 L L (N 18 L (N 30 L L
  L) L)) L L) L) L L)) (N 17 (N 19 L (N 18 (N 25 (N 32 L L L) L L) L L) L) (N 19 (N 18 L (N 25 L
  (N 32 (N 30 L L (N 31 L L L)) L L) L) L) L L) L)) (N 17 (N 23 L L (N 24 L (N 25 (N 26 L L L) L
  L) L)) L (N 18 (N 19 L (N 20 L (N 23 L L (N 24 L (N 25 (N 26 L L L) L L) L)) L) L) (N 19 (N 20
  (N 31 L L L) L L) L L) L)) (N 17 (N 19 L (N 18 (N 33 L L (N 20 L (N 23 L (N 25 (N 26 L L L) L L)
  L) L)) L (N 20 L (N 23 L (N 24 L (N 25 (N 32 L L L) L L) L) L) L)) (N 20 L (N 24 L (N 25 (N 32 L
  L L) L L) L) L)) (N 19 (N 18 L (N 20 (N 31 L L (N 23 (N 30 L L L) L L)) L (N 23 (N 30 L L L) L
  L)) (N 20 (N 31 L L L) L L)) L (N 20 (N 31 L L L) L L)) (N 18 (N 19 L (N 33 L L L) L) (N 19 (N
  26 L (N 23 (N 30 L L L) L L) L) L L) L))) (N 12 (N 17 (N 19 L (N 33 L L (N 25 (N 32 L L L) L L))
  (N 20 L (N 33 L L L) L)) (N 19 (N 18 L (N 20 (N 30 L L (N 24 (N 31 L L L) L L)) L (N 25 L (N 32
  (N 30 L L (N 31 L L L)) L L) L)) (N 20 (N 30 L L L) L L)) L (N 20 (N 18 L (N 24 (N 31 L L L) L
  L) L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 (N 32 L L (N 33 L L L)) L L) L) L) L) (N 19 (N
  20 (N 24 (N 31 L L L) L L) L L) L L) L)) (N 17 (N 20 L L (N 19 L (N 18 (N 23 L L (N 24 L (N 25
  (N 26 L L L) L L) L)) L L) L)) L (N 20 (N 18 L (N 19 (N 24 (N 31 L L L) L L) L L) L) L L)) (N 17
  (N 19 L (N 18 (N 20 L (N 23 L (N 24 L (N 25 (N 26 L L (N 32 L L L)) L (N 26 (N 32 L L L) L L))
  (N 25 (N 26 L L L) L L)) (N 24 L (N 25 (N 26 L L L) L L) L)) (N 23 L (N 25 (N 26 L L L) L L) L))
  L (N 20 L (N 23 L (N 24 L (N 25 (N 32 L L L) L L) L) L) L)) (N 20 L (N 18 (N 24 L (N 25 (N 26 L
  L L) L L) L) L L) L)) (N 19 (N 18 L (N 20 (N 23 (N 24 L L (N 30 L L L)) L (N 24 (N 30 L L L) L
  L)) L (N 23 (N 30 L L L) L L)) (N 20 (N 23 (N 30 L L L) L L) L L)) L (N 20 (N 18 L (N 24 (N 31 L
  L L) L L) L) L L)) (N 18 (N 19 L (N 20 L (N 23 L (N 24 L (N 26 (N 33 L L L) L L) L) L) L) L) (N
  19 (N 20 (N 24 (N 30 L L L) L L) L L) L L) L))) L)) (N 9 (N 12 (N 13 (N 18 L (N 31 L L (N 30 (N
  17 L (N 20 L L (N 19 (N 23 L (N 25 L (N 32 L L L) L) L) L L)) L) L L)) (N 20 L (N 33 L L (N 31 L
  (N 17 (N 19 L (N 23 L (N 30 L (N 25 (N 32 L L L) L L) L) L) L) L L) L)) L)) (N 17 (N 19 L (N 33
  L L (N 30 L (N 32 (N 18 L L (N 20 L (N 23 L (N 25 L L L) L) L)) L L) L)) (N 20 L (N 33 L L L)
  L)) (N 20 (N 30 L L (N 18 L (N 19 (N 31 L L L) L L) L)) L (N 18 (N 19 L (N 32 L L L) L) (N 19 (N
  25 L (N 31 L L (N 30 (N 23 L (N 32 L L L) L) L L)) L) L L) L)) (N 18 (N 19 L (N 32 L L L) L) (N
  19 (N 31 L L L) L L) L)) (N 17 (N 19 L (N 33 L L (N 20 L (N 18 (N 32 L L L) L L) L)) (N 20 L (N
  33 L L L) L)) (N 30 (N 20 L (N 32 L L (N 33 L L L)) (N 24 L (N 31 (N 18 L (N 19 L L L) L) L L)
  L)) L (N 31 (N 18 L (N 19 L L L) L) L L)) (N 18 (N 19 L (N 32 L L L) L) (N 30 (N 20 L (N 32 L L
  L) L) L L) L))) (N 13 (N 18 L (N 31 L L (N 30 (N 23 L (N 17 (N 20 L L (N 19 L (N 32 L L L) L)) L
  L) L) L L)) (N 17 (N 19 L (N 20 L (N 23 L (N 30 (N 32 L L (N 33 L L L)) L L) L) L) L) (N 19 (N
  20 (N 23 (N 30 L L L) L L) L L) L L) L)) (N 20 (N 26 L L (N 25 L (N 23 (N 24 L L L) L L) L)) L
  (N 17 (N 19 L (N 18 (N 32 L L L) L L) L) (N 19 (N 18 L (N 25 L (N 26 L L (N 23 (N 24 L L L) L
  L)) L) L) L L) L)) (N 17 (N 19 L (N 20 L (N 18 (N 32 L L (N 23 L (N 25 (N 26 L L L) L L) L)) L
  (N 23 L (N 24 L (N 26 (N 33 L L L) L L) L) L)) (N 24 L (N 26 (N 32 L L L) L L) L)) (N 20 L (N 18
  (N 32 L L L) L L) L)) (N 19 (N 31 L L (N 18 L (N 20 (N 23 (N 30 L L L) L L) L L) L)) L (N 20 (N
  18 L (N 23 (N 30 L L L) L L) L) L L)) (N 18 (N 19 L (N 32 L L L) L) (N 20 (N 25 L (N 23 (N 30 L
  L L) L L) L) L L) L))) L) (N 12 (N 13 (N 20 L (N 33 L L (N 32 (N 25 L (N 19 (N 18 L L (N 17 L (N
  30 L L L) L)) L L) L) L L)) (N 17 (N 19 L (N 18 (N 25 (N 32 L L L) L L) L L) L) (N 19 (N 18 L (N
  25 L (N 32 (N 30 L L (N 31 L L L)) L L) L) L) L L) L)) (N 18 (N 24 L L (N 23 L (N 25 (N 26 L L
  L) L L) L)) L (N 17 (N 19 L (N 20 L (N 23 L (N 24 L L (N 25 (N 26 L L L) L L)) L) L) L) (N 19 (N
  20 (N 30 L L L) L L) L L) L)) (N 17 (N 19 L (N 33 L L (N 18 (N 20 L (N 24 L (N 25 (N 26 L L L) L
  L) L) L) L L)) (N 20 L (N 33 L L L) L)) (N 19 (N 18 L (N 20 (N 30 L L (N 24 (N 31 L L L) L L)) L
  (N 24 (N 31 L L L) L L)) (N 26 L (N 24 (N 30 L L L) L L) L)) L (N 30 (N 20 L (N 32 L L L) L) L
  L)) (N 18 (N 19 L (N 20 L (N 23 L (N 24 L (N 25 (N 32 L L L) L L) L) L) L) L) (N 19 (N 20 (N 30
  L L L) L L) L L) L))) (N 13 (N 17 (N 19 L (N 18 (N 33 L L (N 25 (N 32 L L L) L L)) L (N 20 L (N
  23 L (N 30 (N 32 L L (N 33 L L L)) L L) L) L)) (N 20 L (N 18 (N 33 L L L) L L) L)) (N 19 (N 18 L
  (N 20 (N 31 L L (N 23 (N 30 L L L) L L)) L (N 25 L (N 32 (N 30 L L (N 31 L L L)) L L) L)) (N 20
  (N 23 (N 30 L L L) L L) L L)) L (N 20 (N 18 L (N 23 (N 30 L L L) L L) L) L L)) (N 18 (N 19 L (N
  20 L (N 23 L (N 24 L (N 31 L L L) L) L) L) L) (N 19 (N 20 (N 31 L L L) L L) L L) L)) (N 18 (N 20
  L L (N 19 L (N 17 (N 24 L L (N 23 L (N 25 (N 26 L L L) L L) L)) L L) L)) L (N 20 (N 17 L (N 19
  (N 23 (N 30 L L L) L L) L L) L) L L)) (N 17 (N 19 L (N 18 (N 20 L (N 23 L (N 24 L (N 25 (N 26 L
  L (N 32 L L L)) L (N 26 (N 32 L L L) L L)) (N 25 (N 26 L L L) L L)) (N 24 L (N 25 (N 26 L L L) L
  L) L)) (N 24 L (N 25 (N 26 L L L) L L) L)) L (N 20 L (N 23 L (N 24 L (N 26 (N 33 L L L) L L) L)
  L) L)) (N 20 L (N 18 (N 23 L (N 25 (N 26 L L L) L L) L) L L) L)) (N 19 (N 18 L (N 20 (N 23 (N 24
  L L (N 30 L L L)) L (N 24 (N 30 L L L) L L)) L (N 24 (N 31 L L L) L L)) (N 20 (N 23 (N 30 L L L)
  L L) L L)) L (N 20 (N 18 L (N 23 (N 30 L L L) L L) L) L L)) (N 18 (N 19 L (N 20 L (N 23 L (N 24
  L (N 25 (N 32 L L L) L L) L) L) L) L) (N 19 (N 20 (N 24 (N 30 L L L) L L) L L) L L) L))) L) L))
  (N 8 (N 9 (N 19 L (N 32 L L (N 33 (N 30 L (N 31 L L L) L) L L)) (N 17 (N 20 L (N 32 L L (N 25 L
  (N 30 L (N 18 (N 31 L L L) L L) L) L)) L) (N 18 (N 20 L (N 13 L L (N 12 (N 30 L L (N 31 L L L))
  L L)) L) (N 20 (N 26 L (N 32 L L (N 25 L (N 30 (N 33 L L L) L L) L)) L) L L) L) L)) (N 12 (N 17
  L (N 30 L L (N 31 (N 32 L (N 33 L L L) L) L L)) (N 18 (N 19 L (N 24 L L L) L) (N 19 (N 20 (N 13
  L L (N 24 (N 25 L L (N 23 L (N 26 L (N 33 L L L) L) L)) L L)) L L) L L) L)) (N 13 (N 17 (N 19 L
  (N 24 L L (N 23 L (N 30 L L L) L)) (N 20 L (N 18 (N 23 L L (N 24 L (N 31 L L L) L)) L L) L)) (N
  19 (N 26 L L (N 23 (N 25 L (N 32 L L L) L) L L)) L (N 20 (N 26 L L L) L L)) (N 18 (N 19 L (N 24
  L L L) L) (N 19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L)) (N 18 (N 20 L L (N 19 L (N 17 (N 24
  L L (N 23 L (N 30 L L L) L)) L L) L)) L (N 20 (N 17 L (N 19 (N 23 (N 30 L L L) L L) L L) L) L
  L)) (N 17 (N 19 L (N 24 L L (N 18 (N 20 L (N 23 L L L) L) L L)) (N 20 L (N 18 (N 23 L L (N 24 L
  (N 25 (N 26 (N 30 L L (N 32 L L L)) L L) L L) L)) L L) L)) (N 19 (N 26 L L (N 18 L (N 25 L L L)
  L)) L (N 20 (N 26 L L L) L L)) (N 18 (N 19 L (N 24 L L L) L) (N 19 (N 20 (N 24 (N 25 L L (N 26 L
  (N 23 (N 30 L L (N 32 L L L)) L L) L)) L L) L L) L L) L))) (N 13 (N 17 (N 19 L (N 24 L L (N 23 L
  (N 30 L L L) L)) (N 20 L (N 18 (N 33 (N 26 L (N 24 L L (N 23 L (N 30 L L L) L)) L) L L) L L) L))
  (N 19 (N 18 L (N 25 L L (N 20 (N 24 (N 26 L (N 33 L L L) L) L L) L L)) (N 30 (N 23 L (N 25 L L
  (N 26 L (N 33 L L L) L)) L) L L)) L (N 18 (N 20 L (N 31 L L (N 23 L (N 30 (N 32 L L L) L L) L))
  L) (N 20 (N 25 L L (N 24 (N 26 L (N 33 L L L) L) L L)) L L) L)) (N 18 (N 19 L (N 24 L L L) L) (N
  19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L)) (N 18 (N 24 L L (N 23 L (N 25 (N 26 (N 30 (N 17 L
  (N 19 L L (N 20 L L L)) L) L L) L L) L L) L)) L (N 17 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L)
  L) (N 19 (N 20 (N 30 (N 23 L (N 25 L L (N 26 L L L)) L) L L) L L) L L) L)) L)) (N 13 (N 12 (N 17
  L (N 30 L L (N 31 (N 18 L (N 20 L L (N 19 (N 24 L (N 25 L (N 32 L L L) L) L) L L)) L) L L)) (N
  20 L (N 33 L L (N 30 L (N 18 (N 24 L L L) L L) L)) L)) (N 17 (N 19 L (N 20 L (N 23 L L (N 18 (N
  24 L (N 31 L L L) L) L L)) (N 32 (N 25 L (N 23 L L (N 24 L (N 31 L L L) L)) L) L L)) (N 20 L (N
  18 (N 23 L L (N 24 L (N 31 L L L) L)) L L) L)) (N 19 (N 26 L L (N 23 (N 25 L (N 32 L L L) L) L
  L)) L (N 20 (N 26 L L L) L L)) (N 18 (N 19 L (N 20 L (N 23 L L (N 24 L (N 31 L L L) L)) L) L) (N
  20 (N 31 (N 24 L (N 26 L L (N 25 L (N 32 L L L) L)) L) L L) L L) L)) (N 17 (N 19 L (N 20 L (N 18
  (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 30 L L L) L)) L (N 23 L (N 30 L L L) L)) (N 23 L (N
  30 L L L) L)) (N 20 L (N 24 L (N 30 L L (N 23 L (N 25 (N 32 L L L) L L) L)) L) L)) (N 30 (N 23 L
  (N 31 (N 18 L (N 19 (N 20 (N 24 L (N 25 L L (N 26 L L L)) (N 25 L (N 26 L L L) L)) L (N 25 L (N
  26 L L L) L)) L (N 20 (N 24 L (N 25 L L L) L) L L)) (N 24 L (N 25 (N 19 L (N 20 L L L) L) L L)
  L)) L (N 32 L (N 33 L L L) L)) (N 31 (N 18 L (N 20 (N 24 L (N 25 L (N 26 L L L) L) L) L L) L) L
  L)) L (N 31 (N 18 L (N 20 (N 24 L (N 26 L (N 32 L L L) L) L) L L) L) L L)) (N 18 (N 19 L (N 20 L
  (N 23 L (N 31 L L L) L) L) L) (N 30 (N 23 L (N 31 (N 24 L (N 26 (N 19 L (N 20 L L L) L) L L) L)
  L L) L) L L) L))) (N 12 (N 17 L (N 30 L L (N 31 (N 32 L (N 33 L L L) L) L L)) (N 18 (N 19 L (N
  20 L (N 24 L L L) L) L) (N 19 (N 20 (N 24 (N 26 L L (N 23 L (N 25 L (N 32 L L L) L) L)) L L) L
  L) L L) L)) (N 20 (N 26 L L (N 25 L (N 23 (N 24 (N 32 (N 19 L (N 17 L L (N 18 L L L)) L) L L) L
  L) L L) L)) L (N 17 (N 19 L (N 18 (N 32 (N 25 L (N 23 L L (N 24 L L L)) L) L L) L L) L) (N 19 (N
  18 L (N 25 L (N 32 L L L) L) L) L L) L)) (N 17 (N 19 L (N 18 (N 20 L (N 24 L L (N 23 L (N 30 L L
  L) L)) (N 23 L (N 30 L L L) L)) L (N 20 L (N 24 L L L) L)) (N 20 L (N 24 L L L) L)) (N 20 (N 18
  L (N 26 L L (N 19 (N 24 (N 25 L (N 32 L L L) L) L L) L L)) (N 25 L (N 24 (N 30 (N 32 L L L) L L)
  L L) L)) L (N 30 (N 23 L (N 26 (N 19 L (N 32 L L L) L) L L) L) L L)) (N 18 (N 19 L (N 20 L (N 24
  L L L) L) L) (N 19 (N 26 L L L) L L) L))) L)) (N 9 (N 12 (N 13 (N 18 L (N 31 L L (N 30 (N 17 L
  (N 23 L L L) L) L L)) (N 20 L (N 17 (N 19 L (N 23 L L L) L) L L) L)) (N 17 (N 19 L (N 23 L L (N
  18 (N 24 L (N 31 L L L) L) L L)) (N 20 L (N 18 (N 24 L L (N 23 L (N 30 L L L) L)) L L) L)) (N 19
  (N 25 L L (N 20 (N 23 (N 26 L (N 33 L L L) L) L L) L L)) L (N 20 (N 18 L (N 26 L L L) L) L L))
  (N 18 (N 19 L (N 20 L (N 24 L L L) L) L) (N 19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L)) (N 17
  (N 19 L (N 23 L L (N 18 (N 24 L (N 31 L L L) L) L L)) (N 20 L (N 33 (N 26 L (N 23 L L (N 24 L (N
  31 L L L) L)) L) L L) L)) (N 19 (N 25 L L (N 20 (N 23 (N 26 L (N 33 L L L) L) L L) L L)) L (N 20
  (N 18 L (N 25 L L (N 23 (N 26 L (N 33 L L L) L) L L)) L) L L)) (N 18 (N 19 L (N 20 L (N 23 L L
  (N 24 L (N 31 L L L) L)) L) L) (N 19 (N 31 (N 24 L (N 25 L L (N 26 L (N 33 L L L) L)) L) L L) L
  L) L))) (N 17 (N 23 L L (N 24 L (N 25 (N 26 (N 31 (N 18 L (N 13 L L (N 19 L L (N 20 L L L))) L)
  L L) L L) L L) L)) L (N 18 (N 19 L (N 20 L (N 13 L L (N 23 L L (N 24 L (N 31 L L L) L))) L) L)
  (N 19 (N 20 (N 31 (N 24 L (N 13 L L (N 25 L L (N 26 L L L))) L) L L) L L) L L) L)) (N 13 (N 18 L
  (N 31 L L (N 30 (N 32 L (N 33 L L L) L) L L)) (N 17 (N 19 L (N 23 L L L) L) (N 19 (N 20 (N 23 (N
  25 L L (N 24 L (N 26 L (N 33 L L L) L) L)) L L) L L) L L) L)) (N 17 (N 19 L (N 23 L L (N 18 (N
  20 L (N 24 L L L) L) L L)) (N 20 L (N 18 (N 24 L L (N 23 L (N 25 (N 26 (N 30 (N 33 L L L) L L) L
  L) L L) L)) L L) L)) (N 19 (N 25 L L (N 20 (N 23 (N 26 L (N 18 L L (N 24 (N 30 (N 33 L L L) L L)
  L L)) L) L L) L L)) L (N 20 (N 18 L (N 26 L L L) L) L L)) (N 18 (N 19 L (N 23 L L L) L) (N 19 (N
  26 L L L) L L) L)) L)) (N 19 (N 25 L L (N 26 L (N 23 (N 24 (N 33 (N 17 L (N 20 (N 12 L L (N 13 L
  (N 18 L L (N 30 L L L)) L)) L L) (N 18 L (N 31 L L L) L)) L L) L L) L L) L)) L (N 17 (N 20 L (N
  18 (N 33 (N 23 L (N 26 (N 12 L L (N 13 L (N 24 L L (N 30 L L L)) L)) L L) (N 24 L (N 31 L L L)
  L)) L L) L L) L) (N 20 (N 18 L (N 25 L L (N 23 (N 24 (N 26 L (N 32 (N 30 L L (N 31 L L L)) L L)
  L) L L) L L)) L) L L) L)) (N 13 (N 12 (N 20 L (N 33 L L (N 32 (N 30 L (N 31 L L L) L) L L)) (N
  17 (N 19 L (N 18 (N 23 L L (N 24 L (N 31 L L L) L)) L L) L) (N 19 (N 25 L L L) L L) L)) (N 17 (N
  23 L L (N 24 L (N 25 (N 26 (N 31 (N 18 L (N 19 L L (N 20 L L L)) L) L L) L L) L L) L)) L (N 18
  (N 19 L (N 20 L (N 23 L L (N 24 L (N 31 L L L) L)) L) L) (N 19 (N 20 (N 31 (N 24 L (N 25 L L (N
  26 L L L)) L) L L) L L) L L) L)) (N 17 (N 19 L (N 23 L L (N 18 (N 20 L (N 24 L (N 31 L L L) L)
  L) L L)) (N 20 L (N 24 L (N 25 (N 31 (N 32 L L L) L L) L L) L) L)) (N 19 (N 25 L L (N 18 L (N 20
  (N 23 (N 26 L (N 33 L L L) L) L L) L L) L)) L (N 20 (N 25 L L L) L L)) (N 18 (N 19 L (N 23 L L
  L) L) (N 19 (N 26 L (N 23 (N 30 (N 33 L L L) L L) L L) L) L L) L))) (N 12 (N 17 (N 19 L (N 23 L
  L (N 18 (N 24 L (N 20 L L (N 25 (N 26 (N 30 L L (N 33 L L L)) L L) L L)) L) L L)) (N 20 L (N 24
  L L L) L)) (N 19 (N 25 L L (N 18 L (N 26 L L L) L)) L (N 20 (N 25 L L L) L L)) (N 18 (N 19 L (N
  20 L (N 24 L L L) L) L) (N 19 (N 20 (N 24 (N 26 L L (N 25 L (N 23 (N 30 L L (N 33 L L L)) L L)
  L)) L L) L L) L L) L)) (N 17 (N 20 L L (N 19 L (N 18 (N 23 L L (N 24 L (N 25 (N 26 (N 31 (N 32 L
  L L) L L) L L) L L) L)) L L) L)) L (N 20 (N 18 L (N 19 (N 24 (N 26 L L (N 23 (N 25 L (N 31 (N 32
  L L L) L L) L) L L)) L L) L L) L) L L)) (N 17 (N 19 L (N 23 L L (N 18 (N 20 L (N 24 L L L) L) L
  L)) (N 20 L (N 24 L L L) L)) (N 19 (N 25 L L (N 18 L (N 26 L L L) L)) L (N 20 (N 25 L L L) L L))
  (N 18 (N 19 L (N 23 L L L) L) (N 19 (N 26 L L L) L L) L))) L)) (N 9 (N 12 (N 13 (N 18 L (N 31 L
  L (N 30 (N 17 L (N 20 L L (N 19 (N 23 L (N 25 L (N 32 L L L) L) L) L L)) L) L L)) (N 20 L (N 33
  L L (N 31 L (N 17 (N 23 L L L) L L) L)) L)) (N 17 (N 19 L (N 18 (N 20 L (N 24 L L (N 23 L (N 30
  L L L) L)) (N 32 (N 25 L (N 24 L L (N 23 L (N 30 L L L) L)) L) L L)) L (N 20 L (N 23 L (N 30 L L
  L) L) L)) (N 20 L (N 18 (N 23 L (N 30 L L L) L) L L) L)) (N 20 (N 18 L (N 26 L L (N 19 (N 24 (N
  25 L (N 32 L L L) L) L L) L L)) (N 30 (N 23 L (N 26 L L (N 25 L (N 32 L L L) L)) L) L L)) L (N
  18 (N 19 L (N 31 L L (N 23 L (N 30 (N 32 L L L) L L) L)) L) (N 19 (N 25 L (N 32 L L L) L) L L)
  L)) (N 18 (N 19 L (N 20 L (N 24 L L L) L) L) (N 19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L))
  (N 17 (N 19 L (N 20 L (N 18 (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 30 L L L) L)) L (N 23 L
  (N 30 L L L) L)) (N 24 L (N 30 L L (N 23 L (N 25 (N 32 L L L) L L) L)) L)) (N 20 L (N 23 L (N 30
  L L L) L) L)) (N 30 (N 23 L (N 31 (N 18 L (N 19 (N 20 (N 24 L (N 25 L L (N 26 L L L)) (N 25 L (N
  26 L L L) L)) L (N 24 L (N 25 L L L) L)) L (N 20 (N 25 L (N 26 L L L) L) L L)) (N 24 L (N 26 (N
  19 L (N 20 L L L) L) L L) L)) L (N 32 L (N 33 L L L) L)) (N 31 (N 18 L (N 19 (N 24 L (N 25 L (N
  26 L L L) L) L) L L) L) L L)) L (N 31 (N 18 L (N 19 (N 24 L (N 25 L (N 32 L L L) L) L) L L) L) L
  L)) (N 18 (N 19 L (N 20 L (N 23 L (N 31 L L L) L) L) L) (N 30 (N 23 L (N 31 (N 24 L (N 25 (N 19
  L (N 20 L L L) L) L L) L) L L) L) L L) L))) (N 13 (N 18 L (N 31 L L (N 30 (N 32 L (N 33 L L L)
  L) L L)) (N 17 (N 19 L (N 20 L (N 23 L L L) L) L) (N 19 (N 20 (N 23 (N 26 L L (N 24 L (N 25 L (N
  32 L L L) L) L)) L L) L L) L L) L)) (N 20 (N 26 L L (N 25 L (N 23 (N 24 (N 32 (N 19 L (N 17 L L
  (N 18 L L L)) L) L L) L L) L L) L)) L (N 17 (N 19 L (N 18 (N 32 (N 25 L (N 23 L L (N 24 L L L))
  L) L L) L L) L) (N 19 (N 18 L (N 25 L (N 32 L L L) L) L) L L) L)) (N 17 (N 19 L (N 20 L (N 23 L
  L (N 18 (N 24 L (N 31 L L L) L) L L)) (N 24 L (N 26 (N 31 (N 32 L L L) L L) L L) L)) (N 20 L (N
  23 L L L) L)) (N 19 (N 26 L L (N 18 L (N 20 (N 23 (N 25 L (N 32 L L L) L) L L) L L) L)) L (N 20
  (N 26 L L L) L L)) (N 18 (N 19 L (N 20 L (N 23 L L L) L) L) (N 20 (N 25 L (N 23 (N 30 (N 32 L L
  L) L L) L L) L) L L) L))) L) (N 12 (N 13 (N 20 L (N 33 L L (N 32 (N 30 L (N 31 L L L) L) L L))
  (N 17 (N 19 L (N 18 (N 24 L L (N 23 L (N 30 L L L) L)) L L) L) (N 19 (N 18 L (N 25 L L L) L) L
  L) L)) (N 18 (N 24 L L (N 23 L (N 25 (N 26 (N 30 (N 17 L (N 19 L L (N 20 L L L)) L) L L) L L) L
  L) L)) L (N 17 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N 20 (N 30 (N 23 L (N 25 L L
  (N 26 L L L)) L) L L) L L) L L) L)) (N 17 (N 19 L (N 24 L L (N 18 (N 20 L (N 23 L (N 30 L L L)
  L) L) L L)) (N 20 L (N 18 (N 23 L (N 30 L L L) L) L L) L)) (N 19 (N 18 L (N 25 L L (N 20 (N 24
  (N 26 L (N 33 L L L) L) L L) L L)) (N 26 L (N 24 (N 30 (N 33 L L L) L L) L L) L)) L (N 30 (N 23
  L (N 25 (N 20 L (N 32 L L L) L) L L) L) L L)) (N 18 (N 19 L (N 24 L L L) L) (N 19 (N 25 L L L) L
  L) L))) (N 13 (N 17 (N 19 L (N 24 L L (N 23 L (N 20 L L (N 18 (N 25 (N 26 (N 30 (N 32 L L L) L
  L) L L) L L) L L)) L)) (N 20 L (N 23 L L L) L)) (N 19 (N 26 L L (N 23 (N 25 L (N 18 L L (N 20 (N
  24 (N 30 (N 32 L L L) L L) L L) L L)) L) L L)) L (N 20 (N 26 L L L) L L)) (N 18 (N 19 L (N 24 L
  L L) L) (N 19 (N 25 L L L) L L) L)) (N 18 (N 20 L L (N 19 L (N 17 (N 24 L L (N 23 L (N 25 (N 26
  (N 30 (N 32 L L L) L L) L L) L L) L)) L L) L)) L (N 20 (N 17 L (N 19 (N 23 (N 26 L L (N 24 (N 25
  L (N 30 (N 32 L L L) L L) L) L L)) L L) L L) L) L L)) (N 17 (N 19 L (N 24 L L (N 18 (N 20 L (N
  23 L L L) L) L L)) (N 20 L (N 23 L L L) L)) (N 19 (N 26 L L (N 18 L (N 25 L L L) L)) L (N 20 (N
  26 L L L) L L)) (N 18 (N 19 L (N 24 L L L) L) (N 19 (N 25 L L L) L L) L))) L) L)) L) L) (N 34 (N
  35 (N 8 (N 9 (N 19 L (N 25 L L (N 26 (N 23 L (N 24 L (N 33 L (N 17 (N 20 L (N 12 L L (N 13 (N 18
  L L (N 30 L L L)) L L)) L) L (N 18 (N 20 L (N 31 L L L) L) L L)) L) L) L) L L)) (N 17 (N 20 L (N
  25 L L (N 23 L (N 18 (N 24 L (N 26 (N 32 L (N 33 L (N 12 L L (N 13 L L L)) L) L) L L) L) L L)
  L)) L) (N 18 (N 20 L (N 13 L L (N 12 (N 23 L L (N 24 L L L)) L L)) L) (N 20 (N 33 L (N 23 (N 26
  L (N 12 L L (N 13 (N 24 L L (N 30 L L L)) L L)) L) L (N 24 (N 25 L (N 26 L (N 31 L L L) L) L) L
  L)) L) L L) L) L)) (N 12 (N 17 L (N 23 L L (N 24 (N 25 L (N 26 L (N 31 L (N 18 (N 13 L L (N 19 L
  L (N 20 L L L))) L L) L) L) L) L L)) (N 18 (N 19 L (N 20 L (N 31 L (N 24 (N 13 L L (N 25 L L (N
  26 L L L))) L L) L) L) L) (N 19 (N 20 (N 13 L L (N 23 L L (N 24 (N 31 L L L) L L))) L L) L L)
  L)) (N 13 (N 17 (N 19 L (N 25 L L (N 20 L (N 23 L (N 26 (N 33 L L L) L L) L) L)) (N 20 L (N 18
  (N 26 L L L) L L) L)) (N 19 (N 23 L L (N 18 L (N 24 (N 31 L L L) L L) L)) L (N 20 (N 18 L (N 24
  L L (N 23 (N 30 L L L) L L)) L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L) (N 19
  (N 20 (N 24 L L L) L L) L L) L)) (N 18 (N 20 L L (N 19 L (N 17 (N 25 L L L) L L) L)) L (N 20 (N
  17 L (N 19 (N 23 L L L) L L) L) L L)) (N 17 (N 19 L (N 25 L L (N 20 L (N 23 L (N 26 (N 33 L L L)
  L L) L) L)) (N 20 L (N 18 (N 25 L L (N 23 L (N 26 (N 33 L L L) L L) L)) L L) L)) (N 19 (N 23 L L
  (N 18 L (N 24 (N 31 L L L) L L) L)) L (N 20 (N 18 L (N 33 L (N 26 (N 23 L L (N 24 L L L)) L L)
  L) L) L L)) (N 18 (N 19 L (N 20 L (N 31 L (N 24 (N 25 L L (N 26 L L L)) L L) L) L) L) (N 19 (N
  20 (N 23 L L (N 24 (N 31 L L L) L L)) L L) L L) L))) (N 13 (N 17 (N 19 L (N 25 L L (N 20 L (N 23
  L (N 26 (N 18 L L (N 24 L (N 30 L (N 33 L L L) L) L)) L L) L) L)) (N 20 L (N 18 (N 26 L L L) L
  L) L)) (N 19 (N 23 L L (N 18 L (N 20 (N 24 L L L) L L) L)) L (N 18 (N 20 L (N 26 L L L) L) (N 20
  (N 24 L L (N 23 (N 25 L (N 26 L (N 30 L (N 33 L L L) L) L) L) L L)) L L) L)) (N 18 (N 19 L (N 26
  L L L) L) (N 19 (N 23 L L L) L L) L)) (N 18 (N 31 L L (N 30 L (N 32 (N 33 L L L) L L) L)) L (N
  17 (N 19 L (N 20 L (N 23 L (N 25 L L (N 24 (N 26 L L L) L L)) L) L) L) (N 19 (N 23 L L L) L L)
  L)) L)) (N 13 (N 12 (N 17 L (N 23 L L (N 24 (N 18 L (N 20 L L (N 19 (N 25 L (N 26 L (N 31 L (N
  32 L L L) L) L) L) L L)) L) L L)) (N 20 L (N 26 L L (N 23 L (N 18 (N 19 L (N 24 L (N 25 (N 31 L
  (N 32 L L L) L) L L) L) L) L L) L)) L)) (N 17 (N 19 L (N 25 L L (N 20 L (N 18 (N 26 L L L) L L)
  L)) (N 20 L (N 25 L L L) L)) (N 19 (N 23 L L (N 18 L (N 24 (N 20 L L (N 25 L (N 26 L (N 30 L L
  (N 33 L L L)) L) L)) L L) L)) L (N 20 (N 24 L L L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 26 L L
  (N 25 (N 23 L (N 30 L L (N 33 L L L)) L) L L)) L) L) L) (N 20 (N 24 L L L) L L) L)) (N 17 (N 19
  L (N 25 L L (N 20 L (N 18 (N 26 L L L) L L) L)) (N 20 L (N 25 L L L) L)) (N 23 (N 19 L (N 25 L L
  (N 26 L L L)) (N 24 (N 18 L (N 20 L L L) L) L L)) L (N 24 (N 18 L (N 20 L L L) L) L L)) (N 18 (N
  19 L (N 26 L L L) L) (N 23 (N 19 L (N 26 L L L) L) L L) L))) (N 12 (N 17 L (N 23 L L (N 24 (N 25
  L (N 26 L (N 31 L (N 18 (N 19 L L (N 20 L L L)) L L) L) L) L) L L)) (N 18 (N 19 L (N 20 L (N 31
  L (N 24 (N 25 L L (N 26 L L L)) L L) L) L) L) (N 19 (N 20 (N 23 L L (N 24 (N 31 L L L) L L)) L
  L) L L) L)) (N 20 (N 33 L L (N 32 L (N 30 (N 31 L L L) L L) L)) L (N 17 (N 19 L (N 25 L L L) L)
  (N 19 (N 18 L (N 23 L L (N 24 (N 26 L L L) L L)) L) L L) L)) (N 17 (N 19 L (N 25 L L (N 18 (N 20
  L (N 23 L (N 26 (N 33 L L L) L L) L) L) L L)) (N 20 L (N 25 L L L) L)) (N 20 (N 18 L (N 19 (N 23
  L L (N 24 (N 31 L L L) L L)) L (N 24 (N 31 L L L) L L)) (N 23 (N 19 L (N 25 L L L) L) L L)) L (N
  23 (N 19 L (N 25 L L L) L) L L)) (N 18 (N 19 L (N 20 L (N 26 (N 33 L L L) L L) L) L) (N 19 (N 23
  L L L) L L) L))) L)) (N 9 (N 12 (N 13 (N 18 L (N 24 L L (N 23 (N 17 L (N 30 L L L) L) L L)) (N
  20 L (N 17 (N 19 L (N 23 L (N 30 L L L) L) L) L L) L)) (N 17 (N 19 L (N 26 L L (N 23 L (N 25 (N
  32 L L L) L L) L)) (N 20 L (N 26 L L L) L)) (N 19 (N 24 L L (N 23 (N 30 L L L) L L)) L (N 20 (N
  18 L (N 23 L L (N 24 (N 31 L L L) L L)) L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L) L)
  L) L) (N 19 (N 24 L L L) L L) L)) (N 17 (N 19 L (N 26 L L (N 18 (N 25 L L L) L L)) (N 20 L (N 26
  L L L) L)) (N 19 (N 24 L L (N 18 L (N 20 (N 23 L L L) L L) L)) L (N 20 (N 18 L (N 23 L L (N 24
  (N 25 L (N 26 L (N 30 L L (N 32 L L L)) L) L) L L)) L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 25
  L L (N 26 (N 23 L (N 30 L L (N 32 L L L)) L) L L)) L) L) L) (N 19 (N 24 L L L) L L) L))) (N 17
  (N 30 L L (N 31 L (N 32 (N 33 L L L) L L) L)) L (N 18 (N 19 L (N 20 L (N 13 L L (N 24 L (N 25 L
  L (N 23 (N 26 L L L) L L)) L)) L) L) (N 19 (N 24 L L L) L L) L)) (N 13 (N 18 L (N 24 L L (N 23
  (N 25 L (N 26 L (N 30 L (N 17 (N 19 L L (N 20 L L L)) L L) L) L) L) L L)) (N 17 (N 19 L (N 20 L
  (N 30 L (N 23 (N 25 L L (N 26 L L L)) L L) L) L) L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L
  L) L)) (N 17 (N 19 L (N 18 (N 25 L L (N 20 L (N 24 L (N 26 (N 33 L L L) L L) L) L)) L (N 20 L (N
  30 L (N 23 (N 25 L L (N 26 L L L)) L L) L) L)) (N 20 L (N 18 (N 25 L L (N 24 L (N 26 (N 33 L L
  L) L L) L)) L L) L)) (N 19 (N 24 L L (N 23 (N 30 L L L) L L)) L (N 20 (N 18 L (N 33 L (N 26 (N
  23 L L (N 24 L L L)) L L) L) L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L) (N 19
  (N 24 L L L) L L) L)) L)) (N 19 (N 32 L L (N 33 L (N 30 (N 31 L L L) L L) L)) L (N 17 (N 20 L (N
  18 (N 26 (N 32 L L (N 25 (N 30 L (N 33 L L L) L) L L)) L L) L L) L) (N 20 (N 18 L (N 32 L L (N
  25 (N 23 L L (N 24 L L L)) L L)) L) L L) L)) (N 13 (N 12 (N 20 L (N 26 L L (N 25 (N 23 L (N 24 L
  (N 32 L (N 19 (N 17 L L (N 18 L L L)) L L) L) L) L) L L)) (N 17 (N 19 L (N 18 (N 25 (N 32 L L L)
  L L) L L) L) (N 19 (N 18 L (N 32 L (N 25 (N 23 L L (N 24 L L L)) L L) L) L) L L) L)) (N 17 (N 30
  L L (N 31 L (N 32 (N 33 L L L) L L) L)) L (N 18 (N 19 L (N 20 L (N 24 L (N 26 L L (N 23 (N 25 L
  L L) L L)) L) L) L) (N 19 (N 20 (N 24 L L L) L L) L L) L)) (N 17 (N 19 L (N 18 (N 26 L L (N 20 L
  (N 24 L (N 25 (N 32 L L L) L L) L) L)) L (N 20 L (N 25 (N 32 L L L) L L) L)) (N 20 L (N 25 (N 24
  L (N 18 (N 26 L L L) L L) L) L L) L)) (N 19 (N 18 L (N 20 (N 24 L L (N 23 (N 30 L L L) L L)) L
  (N 23 (N 30 L L L) L L)) (N 20 (N 24 L L L) L L)) L (N 20 (N 24 L L L) L L)) (N 18 (N 19 L (N 26
  L L L) L) (N 19 (N 23 (N 24 (N 20 L (N 26 L L L) L) L L) L L) L L) L))) (N 12 (N 17 (N 19 L (N
  26 L L (N 23 L (N 25 (N 32 L L L) L L) L)) (N 20 L (N 26 L L L) L)) (N 19 (N 18 L (N 20 (N 23 L
  L (N 24 (N 31 L L L) L L)) L (N 32 L (N 25 (N 23 L L (N 24 L L L)) L L) L)) (N 20 (N 23 L L L) L
  L)) L (N 20 (N 18 L (N 23 L L (N 24 (N 31 L L L) L L)) L) L L)) (N 18 (N 19 L (N 20 L (N 31 L (N
  24 (N 25 L L (N 26 L L L)) L L) L) L) L) (N 19 (N 20 (N 23 L L (N 24 (N 31 L L L) L L)) L L) L
  L) L)) (N 17 (N 20 L L (N 19 L (N 18 (N 25 (N 32 L L L) L L) L L) L)) L (N 20 (N 18 L (N 19 (N
  24 (N 31 L L L) L L) L L) L) L L)) (N 17 (N 19 L (N 18 (N 20 L (N 25 (N 32 L L (N 33 L L L)) L
  (N 26 (N 32 L L L) L L)) (N 25 (N 32 L L L) L L)) L (N 20 L (N 25 (N 32 L L L) L L) L)) (N 20 L
  (N 18 (N 25 (N 33 L L L) L L) L L) L)) (N 19 (N 18 L (N 20 (N 23 (N 30 L L (N 31 L L L)) L (N 24
  (N 30 L L L) L L)) L (N 23 (N 30 L L L) L L)) (N 20 (N 23 (N 30 L L L) L L) L L)) L (N 20 (N 18
  L (N 24 (N 31 L L L) L L) L) L L)) (N 18 (N 19 L (N 20 L (N 26 (N 33 L L L) L L) L) L) (N 19 (N
  20 (N 23 (N 31 L L L) L L) L L) L L) L))) L)) (N 9 (N 12 (N 13 (N 18 L (N 24 L L (N 23 (N 17 L
  (N 20 L L (N 19 (N 25 L (N 26 L (N 30 L (N 32 L L L) L) L) L) L L)) L) L L)) (N 20 L (N 26 L L
  (N 24 L (N 17 (N 19 L (N 23 L (N 25 (N 30 L (N 32 L L L) L) L L) L) L) L L) L)) L)) (N 17 (N 19
  L (N 26 L L (N 23 L (N 25 (N 18 L L (N 20 L (N 24 L (N 30 L (N 32 L L L) L) L) L)) L L) L)) (N
  20 L (N 26 L L L) L)) (N 20 (N 23 L L (N 18 L (N 19 (N 24 L L L) L L) L)) L (N 18 (N 19 L (N 25
  L L L) L) (N 19 (N 24 L L (N 23 (N 25 L (N 26 L (N 30 L (N 32 L L L) L) L) L) L L)) L L) L)) (N
  18 (N 19 L (N 25 L L L) L) (N 19 (N 24 L L L) L L) L)) (N 17 (N 19 L (N 26 L L (N 20 L (N 18 (N
  25 L L L) L L) L)) (N 20 L (N 26 L L L) L)) (N 23 (N 20 L (N 25 L L (N 26 L L L)) (N 24 (N 18 L
  (N 19 L L L) L) L L)) L (N 24 (N 18 L (N 19 L L L) L) L L)) (N 18 (N 19 L (N 25 L L L) L) (N 23
  (N 20 L (N 25 L L L) L) L L) L))) (N 13 (N 18 L (N 24 L L (N 23 (N 25 L (N 26 L (N 30 L (N 17 (N
  19 L L (N 20 L L L)) L L) L) L) L) L L)) (N 17 (N 19 L (N 20 L (N 30 L (N 23 (N 25 L L (N 26 L L
  L)) L L) L) L) L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L) L)) (N 20 (N 33 L L (N 32 L (N
  30 (N 31 L L L) L L) L)) L (N 17 (N 19 L (N 18 (N 25 L L L) L L) L) (N 19 (N 18 L (N 24 L L (N
  23 (N 26 L L L) L L)) L) L L) L)) (N 17 (N 19 L (N 20 L (N 18 (N 25 L L (N 24 L (N 26 (N 33 L L
  L) L L) L)) L (N 26 (N 33 L L L) L L)) (N 25 (N 18 L (N 24 L L L) L) L L)) (N 20 L (N 18 (N 25 L
  L L) L L) L)) (N 19 (N 24 L L (N 18 L (N 20 (N 23 (N 30 L L L) L L) L L) L)) L (N 20 (N 18 L (N
  23 (N 30 L L L) L L) L) L L)) (N 18 (N 19 L (N 25 L L L) L) (N 20 (N 23 (N 24 (N 19 L (N 25 L L
  L) L) L L) L L) L L) L))) L) (N 12 (N 13 (N 20 L (N 26 L L (N 25 (N 23 L (N 24 L (N 32 L (N 19
  (N 17 L L (N 18 L L L)) L L) L) L) L) L L)) (N 17 (N 19 L (N 18 (N 25 (N 32 L L L) L L) L L) L)
  (N 19 (N 18 L (N 32 L (N 25 (N 23 L L (N 24 L L L)) L L) L) L) L L) L)) (N 18 (N 31 L L (N 30 L
  (N 32 (N 33 L L L) L L) L)) L (N 17 (N 19 L (N 20 L (N 23 L (N 26 L L (N 24 (N 25 L L L) L L))
  L) L) L) (N 19 (N 20 (N 23 L L L) L L) L L) L)) (N 17 (N 19 L (N 26 L L (N 18 (N 20 L (N 23 L (N
  25 (N 32 L L L) L L) L) L) L L)) (N 20 L (N 26 L L L) L)) (N 19 (N 18 L (N 20 (N 23 L L (N 24 (N
  31 L L L) L L)) L (N 24 (N 31 L L L) L L)) (N 23 (N 20 L (N 26 L L L) L) L L)) L (N 23 (N 20 L
  (N 25 L L L) L) L L)) (N 18 (N 19 L (N 20 L (N 25 (N 32 L L L) L L) L) L) (N 19 (N 20 (N 23 L L
  L) L L) L L) L))) (N 13 (N 17 (N 19 L (N 18 (N 26 L L (N 24 L (N 25 (N 32 L L L) L L) L)) L (N
  20 L (N 30 L (N 23 (N 25 L L (N 26 L L L)) L L) L) L)) (N 20 L (N 18 (N 26 L L L) L L) L)) (N 19
  (N 18 L (N 20 (N 24 L L (N 23 (N 30 L L L) L L)) L (N 32 L (N 25 (N 23 L L (N 24 L L L)) L L)
  L)) (N 20 (N 23 (N 30 L L L) L L) L L)) L (N 20 (N 18 L (N 23 (N 30 L L L) L L) L) L L)) (N 18
  (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L) (N 19 (N 20 (N 24 L L L) L L) L L) L)) (N 18 (N 20
  L L (N 19 L (N 17 (N 25 (N 32 L L L) L L) L L) L)) L (N 20 (N 17 L (N 19 (N 23 (N 30 L L L) L L)
  L L) L) L L)) (N 17 (N 19 L (N 18 (N 20 L (N 25 (N 32 L L (N 33 L L L)) L (N 26 (N 32 L L L) L
  L)) (N 25 (N 32 L L L) L L)) L (N 20 L (N 26 (N 33 L L L) L L) L)) (N 20 L (N 18 (N 25 (N 33 L L
  L) L L) L L) L)) (N 19 (N 18 L (N 20 (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 30 L L L) L L)) L
  (N 24 (N 31 L L L) L L)) (N 20 (N 23 (N 30 L L L) L L) L L)) L (N 20 (N 18 L (N 23 (N 30 L L L)
  L L) L) L L)) (N 18 (N 19 L (N 20 L (N 25 (N 32 L L L) L L) L) L) (N 19 (N 20 (N 23 (N 31 L L L)
  L L) L L) L L) L))) L) L)) (N 8 (N 9 (N 19 L (N 25 L L (N 26 (N 23 L (N 24 L L L) L) L L)) (N 17
  (N 20 L (N 25 L L (N 23 L (N 18 (N 24 L L L) L L) L)) L) (N 18 (N 20 L (N 13 L L (N 12 (N 23 L L
  (N 24 L L L)) L L)) L) (N 20 (N 33 L (N 25 L L (N 23 (N 26 L L L) L L)) L) L L) L) L)) (N 12 (N
  17 L (N 23 L L (N 24 (N 25 L (N 26 L L L) L) L L)) (N 18 (N 19 L (N 31 L L L) L) (N 19 (N 20 (N
  13 L L (N 23 L L (N 24 (N 25 L (N 26 L L L) L) L L))) L L) L L) L)) (N 13 (N 17 (N 19 L (N 31 L
  L (N 23 L (N 30 L L L) L)) (N 20 L (N 18 (N 26 (N 33 L L L) L L) L L) L)) (N 19 (N 33 L L (N 25
  L (N 32 L L L) L)) L (N 20 (N 33 L L L) L L)) (N 18 (N 19 L (N 31 L L L) L) (N 19 (N 20 (N 24 (N
  31 L L L) L L) L L) L L) L)) (N 18 (N 20 L L (N 19 L (N 17 (N 25 (N 32 L L L) L L) L L) L)) L (N
  20 (N 17 L (N 19 (N 23 (N 30 L L L) L L) L L) L) L L)) (N 17 (N 19 L (N 31 L L (N 18 (N 20 L (N
  30 L L L) L) L L)) (N 20 L (N 18 (N 26 (N 30 L L (N 24 L (N 31 L L L) L)) L L) L L) L)) (N 19 (N
  33 L L (N 18 L (N 32 L L L) L)) L (N 20 (N 33 L L L) L L)) (N 18 (N 19 L (N 31 L L L) L) (N 19
  (N 20 (N 24 (N 31 (N 32 L L (N 26 L (N 33 L L L) L)) L L) L L) L L) L L) L))) (N 13 (N 17 (N 19
  L (N 31 L L (N 23 L (N 30 L L L) L)) (N 20 L (N 18 (N 26 (N 33 L (N 31 L L (N 23 L (N 30 L L L)
  L)) L) L L) L L) L)) (N 19 (N 18 L (N 32 L L (N 20 (N 26 L (N 33 L L L) L) L L)) (N 23 (N 30 L
  (N 32 L L (N 26 L (N 33 L L L) L)) L) L L)) L (N 18 (N 20 L (N 24 L L (N 23 (N 25 L L L) L L))
  L) (N 20 (N 26 L (N 33 L L L) L) L L) L)) (N 18 (N 19 L (N 31 L L L) L) (N 19 (N 20 (N 23 (N 24
  (N 31 L L L) L L) L L) L L) L L) L)) (N 18 (N 31 L L (N 30 L (N 23 (N 17 L (N 19 L L (N 20 L L
  L)) L) L L) L)) L (N 17 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N 20 (N 23 (N 30 L
  (N 32 L L (N 33 L L L)) L) L L) L L) L L) L)) L)) (N 13 (N 12 (N 17 L (N 23 L L (N 24 (N 18 L (N
  20 L L (N 19 (N 25 L (N 26 L L L) L) L L)) L) L L)) (N 20 L (N 26 L L (N 23 L (N 18 (N 24 L L L)
  L L) L)) L)) (N 17 (N 19 L (N 20 L (N 30 L L (N 18 (N 24 L (N 31 L L L) L) L L)) (N 25 (N 32 L
  (N 30 L L (N 24 L (N 31 L L L) L)) L) L L)) (N 20 L (N 18 (N 24 L (N 31 L L L) L) L L) L)) (N 19
  (N 33 L L (N 25 L (N 32 L L L) L)) L (N 20 (N 33 L L L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N
  31 L L L) L) L) L) (N 20 (N 24 (N 31 L (N 33 L L (N 25 L (N 32 L L L) L)) L) L L) L L) L)) (N 17
  (N 19 L (N 20 L (N 18 (N 23 L (N 24 L L (N 30 L L L)) (N 24 L (N 30 L L L) L)) L (N 23 L (N 30 L
  L L) L)) (N 23 L (N 30 L L L) L)) (N 20 L (N 25 (N 24 L (N 31 L L L) L) L L) L)) (N 23 (N 24 (N
  18 L (N 19 (N 20 (N 25 L (N 26 L L (N 32 L L L)) (N 26 L (N 32 L L L) L)) L (N 25 L (N 26 L L L)
  L)) L (N 20 (N 25 L (N 26 L L L) L) L L)) (N 25 L (N 19 (N 32 L L L) L L) L)) L (N 25 L (N 26 L
  L L) L)) L (N 24 (N 18 L (N 20 (N 25 L (N 26 L L L) L) L L) L) L L)) (N 18 (N 19 L (N 20 L (N 24
  L (N 30 L L L) L) L) L) (N 23 (N 24 (N 26 L (N 19 (N 33 L L L) L L) L) L L) L L) L))) (N 12 (N
  17 L (N 23 L L (N 24 (N 25 L (N 26 L L L) L) L L)) (N 18 (N 19 L (N 20 L (N 31 L L L) L) L) (N
  19 (N 20 (N 23 L L (N 24 (N 25 L (N 26 L L L) L) L L)) L L) L L) L)) (N 20 (N 33 L L (N 32 L (N
  25 (N 19 L (N 17 L L (N 18 L L L)) L) L L) L)) L (N 17 (N 19 L (N 18 (N 25 (N 32 L (N 30 L L (N
  31 L L L)) L) L L) L L) L) (N 19 (N 18 L (N 25 L (N 32 L L L) L) L) L L) L)) (N 17 (N 19 L (N 18
  (N 20 L (N 31 L L (N 23 L (N 30 L L L) L)) (N 23 L (N 30 L L L) L)) L (N 20 L (N 31 L L L) L))
  (N 20 L (N 31 L L L) L)) (N 20 (N 18 L (N 33 L L (N 19 (N 23 (N 25 L (N 26 L L L) L) L L) L L))
  (N 23 (N 24 (N 25 L (N 32 L L L) L) L L) L L)) L (N 23 (N 25 L (N 26 L L L) L) L L)) (N 18 (N 19
  L (N 20 L (N 31 L L L) L) L) (N 19 (N 33 L L L) L L) L))) L)) (N 9 (N 12 (N 13 (N 18 L (N 24 L L
  (N 23 (N 17 L (N 30 L L L) L) L L)) (N 20 L (N 17 (N 19 L (N 30 L L L) L) L L) L)) (N 17 (N 19 L
  (N 30 L L (N 18 (N 24 L (N 31 L L L) L) L L)) (N 20 L (N 18 (N 26 (N 33 L L L) L L) L L) L)) (N
  19 (N 32 L L (N 20 (N 26 L (N 33 L L L) L) L L)) L (N 20 (N 18 L (N 33 L L L) L) L L)) (N 18 (N
  19 L (N 20 L (N 31 L L L) L) L) (N 19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L)) (N 17 (N 19 L
  (N 30 L L (N 18 (N 24 L (N 31 L L L) L) L L)) (N 20 L (N 26 (N 33 L (N 30 L L (N 24 L (N 31 L L
  L) L)) L) L L) L)) (N 19 (N 32 L L (N 20 (N 26 L (N 33 L L L) L) L L)) L (N 20 (N 18 L (N 26 L
  (N 33 L L L) L) L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L) (N 19 (N 24 (N 31 L
  (N 32 L L (N 26 L (N 33 L L L) L)) L) L L) L L) L))) (N 17 (N 30 L L (N 31 L (N 24 (N 18 L (N 13
  L L (N 19 L L (N 20 L L L))) L) L L) L)) L (N 18 (N 19 L (N 20 L (N 13 L L (N 24 L (N 31 L L L)
  L)) L) L) (N 19 (N 20 (N 24 (N 31 L (N 13 L L (N 32 L L (N 33 L L L))) L) L L) L L) L L) L)) (N
  13 (N 18 L (N 24 L L (N 23 (N 25 L (N 26 L L L) L) L L)) (N 17 (N 19 L (N 30 L L L) L) (N 19 (N
  20 (N 23 (N 24 L L (N 25 L (N 26 L L L) L)) L L) L L) L L) L)) (N 17 (N 19 L (N 30 L L (N 18 (N
  20 L (N 31 L L L) L) L L)) (N 20 L (N 18 (N 26 (N 31 L L (N 23 L (N 30 L L L) L)) L L) L L) L))
  (N 19 (N 32 L L (N 20 (N 30 (N 33 L (N 18 L L (N 23 (N 26 L L L) L L)) L) L L) L L)) L (N 20 (N
  18 L (N 33 L L L) L) L L)) (N 18 (N 19 L (N 30 L L L) L) (N 19 (N 33 L L L) L L) L)) L)) (N 19
  (N 32 L L (N 33 L (N 26 (N 30 (N 31 (N 17 L (N 20 (N 12 L L (N 13 L (N 18 L L (N 23 L L L)) L))
  L L) (N 18 L (N 24 L L L) L)) L L) L L) L L) L)) L (N 17 (N 20 L (N 18 (N 26 (N 23 L (N 24 L L
  (N 30 L L L)) (N 24 L (N 31 L L L) L)) L L) L L) L) (N 20 (N 18 L (N 32 L L (N 25 (N 23 L L (N
  24 L L L)) L L)) L) L L) L)) (N 13 (N 12 (N 20 L (N 26 L L (N 25 (N 23 L (N 24 L L L) L) L L))
  (N 17 (N 19 L (N 18 (N 25 (N 26 L L (N 23 L (N 24 L L L) L)) L L) L L) L) (N 19 (N 32 L L L) L
  L) L)) (N 17 (N 30 L L (N 31 L (N 24 (N 18 L (N 19 L L (N 20 L L L)) L) L L) L)) L (N 18 (N 19 L
  (N 20 L (N 24 L (N 31 L L L) L) L) L) (N 19 (N 20 (N 24 (N 31 L (N 32 L L (N 33 L L L)) L) L L)
  L L) L L) L)) (N 17 (N 19 L (N 30 L L (N 18 (N 20 L (N 24 L (N 31 L L L) L) L) L L)) (N 20 L (N
  25 (N 24 L (N 31 L L L) L) L L) L)) (N 19 (N 32 L L (N 18 L (N 20 (N 24 (N 25 L (N 26 L L L) L)
  L L) L L) L)) L (N 20 (N 32 L L L) L L)) (N 18 (N 19 L (N 30 L L L) L) (N 19 (N 23 (N 24 (N 26 L
  (N 33 L L L) L) L L) L L) L L) L))) (N 12 (N 17 (N 19 L (N 30 L L (N 18 (N 31 L (N 20 L L (N 23
  L L (N 24 (N 25 L L L) L L))) L) L L)) (N 20 L (N 31 L L L) L)) (N 19 (N 32 L L (N 18 L (N 33 L
  L L) L)) L (N 20 (N 32 L L L) L L)) (N 18 (N 19 L (N 20 L (N 31 L L L) L) L) (N 19 (N 20 (N 24
  (N 31 (N 33 L L (N 25 L (N 32 L L L) L)) L L) L L) L L) L L) L)) (N 17 (N 20 L L (N 19 L (N 18
  (N 25 (N 23 L L (N 24 L (N 31 L L L) L)) L L) L L) L)) L (N 20 (N 18 L (N 19 (N 24 (N 26 L L (N
  23 (N 25 L (N 32 L L L) L) L L)) L L) L L) L) L L)) (N 17 (N 19 L (N 30 L L (N 18 (N 20 L (N 31
  L L L) L) L L)) (N 20 L (N 31 L L L) L)) (N 19 (N 32 L L (N 18 L (N 33 L L L) L)) L (N 20 (N 32
  L L L) L L)) (N 18 (N 19 L (N 30 L L L) L) (N 19 (N 33 L L L) L L) L))) L)) (N 9 (N 12 (N 13 (N
  18 L (N 24 L L (N 23 (N 17 L (N 20 L L (N 19 (N 25 L (N 26 L L L) L) L L)) L) L L)) (N 20 L (N
  26 L L (N 24 L (N 17 (N 23 L L L) L L) L)) L)) (N 17 (N 19 L (N 18 (N 20 L (N 31 L L (N 23 L (N
  30 L L L) L)) (N 25 (N 32 L (N 31 L L (N 23 L (N 30 L L L) L)) L) L L)) L (N 20 L (N 23 L (N 30
  L L L) L) L)) (N 20 L (N 18 (N 23 L (N 30 L L L) L) L L) L)) (N 20 (N 18 L (N 33 L L (N 19 (N 25
  L (N 32 L L L) L) L L)) (N 23 (N 30 L (N 33 L L (N 25 L (N 32 L L L) L)) L) L L)) L (N 18 (N 19
  L (N 24 L L (N 23 (N 25 L L L) L L)) L) (N 19 (N 25 L (N 32 L L L) L) L L) L)) (N 18 (N 19 L (N
  20 L (N 31 L L L) L) L) (N 19 (N 20 (N 23 (N 24 (N 31 L L L) L L) L L) L L) L L) L)) (N 17 (N 19
  L (N 20 L (N 18 (N 23 L (N 24 L L (N 30 L L L)) (N 24 L (N 30 L L L) L)) L (N 23 L (N 30 L L L)
  L)) (N 25 (N 24 L (N 31 L L L) L) L L)) (N 20 L (N 23 L (N 30 L L L) L) L)) (N 23 (N 24 (N 18 L
  (N 19 (N 20 (N 25 L (N 26 L L (N 32 L L L)) (N 26 L (N 32 L L L) L)) L (N 25 L (N 26 L L L) L))
  L (N 20 (N 25 L (N 26 L L L) L) L L)) (N 26 L (N 19 (N 33 L L L) L L) L)) L (N 25 L (N 26 L L L)
  L)) L (N 24 (N 18 L (N 19 (N 25 L (N 26 L L L) L) L L) L) L L)) (N 18 (N 19 L (N 20 L (N 24 L (N
  30 L L L) L) L) L) (N 23 (N 24 (N 25 L (N 19 (N 32 L L L) L L) L) L L) L L) L))) (N 13 (N 18 L
  (N 24 L L (N 23 (N 25 L (N 26 L L L) L) L L)) (N 17 (N 19 L (N 20 L (N 30 L L L) L) L) (N 19 (N
  20 (N 23 (N 24 L L (N 25 L (N 26 L L L) L)) L L) L L) L L) L)) (N 20 (N 33 L L (N 32 L (N 25 (N
  19 L (N 17 L L (N 18 L L L)) L) L L) L)) L (N 17 (N 19 L (N 18 (N 25 (N 32 L (N 30 L L (N 31 L L
  L)) L) L L) L L) L) (N 19 (N 18 L (N 25 L (N 32 L L L) L) L) L L) L)) (N 17 (N 19 L (N 20 L (N
  30 L L (N 18 (N 24 L (N 31 L L L) L) L L)) (N 25 (N 24 L (N 31 L L L) L) L L)) (N 20 L (N 30 L L
  L) L)) (N 19 (N 33 L L (N 18 L (N 20 (N 24 (N 25 L (N 26 L L L) L) L L) L L) L)) L (N 20 (N 33 L
  L L) L L)) (N 18 (N 19 L (N 20 L (N 30 L L L) L) L) (N 20 (N 23 (N 24 (N 25 L (N 32 L L L) L) L
  L) L L) L L) L))) L) (N 12 (N 13 (N 20 L (N 26 L L (N 25 (N 23 L (N 24 L L L) L) L L)) (N 17 (N
  19 L (N 18 (N 25 (N 26 L L (N 23 L (N 24 L L L) L)) L L) L L) L) (N 19 (N 18 L (N 32 L L L) L) L
  L) L)) (N 18 (N 31 L L (N 30 L (N 23 (N 17 L (N 19 L L (N 20 L L L)) L) L L) L)) L (N 17 (N 19 L
  (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N 20 (N 23 (N 30 L (N 32 L L (N 33 L L L)) L) L L)
  L L) L L) L)) (N 17 (N 19 L (N 31 L L (N 18 (N 20 L (N 23 L (N 30 L L L) L) L) L L)) (N 20 L (N
  18 (N 23 L (N 30 L L L) L) L L) L)) (N 19 (N 18 L (N 32 L L (N 20 (N 23 (N 25 L (N 26 L L L) L)
  L L) L L)) (N 23 (N 24 (N 26 L (N 33 L L L) L) L L) L L)) L (N 23 (N 25 L (N 26 L L L) L) L L))
  (N 18 (N 19 L (N 31 L L L) L) (N 19 (N 32 L L L) L L) L))) (N 13 (N 17 (N 19 L (N 31 L L (N 30 L
  (N 20 L L (N 18 (N 23 (N 25 L L L) L L) L L)) L)) (N 20 L (N 30 L L L) L)) (N 19 (N 33 L L (N 30
  (N 32 L (N 18 L L (N 20 (N 23 (N 25 L L L) L L) L L)) L) L L)) L (N 20 (N 33 L L L) L L)) (N 18
  (N 19 L (N 31 L L L) L) (N 19 (N 32 L L L) L L) L)) (N 18 (N 20 L L (N 19 L (N 17 (N 25 (N 24 L
  L (N 23 L (N 30 L L L) L)) L L) L L) L)) L (N 20 (N 17 L (N 19 (N 23 (N 26 L L (N 24 (N 25 L (N
  32 L L L) L) L L)) L L) L L) L) L L)) (N 17 (N 19 L (N 31 L L (N 18 (N 20 L (N 30 L L L) L) L
  L)) (N 20 L (N 30 L L L) L)) (N 19 (N 33 L L (N 18 L (N 32 L L L) L)) L (N 20 (N 33 L L L) L L))
  (N 18 (N 19 L (N 31 L L L) L) (N 19 (N 32 L L L) L L) L))) L) L)) L) (N 35 (N 8 (N 9 (N 19 L (N
  25 L L (N 20 (N 17 L L (N 18 L L L)) L L)) (N 17 (N 20 L (N 18 (N 25 L L (N 32 L L L)) L L) L)
  (N 18 (N 20 L L L) L L) L)) (N 12 (N 17 L (N 23 L L (N 18 (N 19 L L (N 20 L L L)) L L)) (N 18 (N
  19 L (N 20 L L L) L) (N 19 (N 20 (N 13 L L (N 23 L L (N 30 L L L))) L L) L L) L)) (N 13 (N 17 (N
  19 L (N 20 L L (N 18 (N 25 (N 32 L L L) L L) L L)) (N 20 L (N 18 (N 26 (N 33 L L L) L L) L L)
  L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N 19 L
  (N 20 L L L) L) (N 19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L)) (N 18 (N 20 L L (N 19 L (N 17
  (N 25 (N 32 L L L) L L) L L) L)) L (N 20 (N 17 L (N 19 (N 23 (N 30 L L L) L L) L L) L) L L)) (N
  17 (N 19 L (N 20 L L (N 18 (N 25 (N 32 L L L) L L) L L)) (N 20 L (N 18 (N 26 (N 33 L L L) L L) L
  L) L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N
  19 L (N 20 L L L) L) (N 19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L))) (N 13 (N 17 (N 19 L (N
  20 L L (N 18 (N 23 L (N 25 (N 32 L L L) L L) L) L L)) (N 20 L (N 18 (N 26 (N 33 L L L) L L) L L)
  L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N 19 L
  (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L) L)) (N 18 (N 19 L (N 20 L L (N 17
  (N 23 L (N 25 (N 32 L L L) L L) L) L L)) (N 20 L (N 17 (N 26 (N 33 L L L) L L) L L) L)) L (N 17
  (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L) L)) L)) (N 13 (N 12 (N 17
  L (N 20 L L (N 18 (N 19 L L L) L L)) (N 20 L (N 18 (N 19 L L L) L L) L)) (N 17 (N 19 L (N 20 L L
  (N 18 (N 25 (N 32 L L L) L L) L L)) (N 20 L (N 18 (N 24 L (N 25 (N 32 L L L) L L) L) L L) L)) (N
  18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N 19 L (N 20
  L L L) L) (N 19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L)) (N 17 (N 19 L (N 20 L L (N 18 (N 23
  L (N 25 (N 32 L L L) L L) L) L L)) (N 20 L (N 18 (N 24 L (N 25 (N 32 L L L) L L) L) L L) L)) (N
  18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N 19 L (N 20
  L L L) L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L) L))) (N 12 (N 17 L (N 23 L L (N 18 (N 19
  L L (N 20 L L L)) L L)) (N 18 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 L L (N 30 L L L)) L L) L
  L) L)) (N 20 (N 17 L (N 18 L L (N 19 (N 23 (N 30 L L L) L L) L L)) (N 18 L (N 19 (N 24 (N 31 L L
  L) L L) L L) L)) L (N 17 (N 19 L (N 18 (N 25 (N 32 L L L) L L) L L) L) (N 18 (N 19 L L L) L L)
  L)) (N 17 (N 19 L (N 20 L L (N 18 (N 23 L (N 25 (N 32 L L L) L L) L) L L)) (N 20 L (N 18 (N 25
  (N 32 L L L) L L) L L) L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L
  L) L L)) (N 18 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L) L))) L)) (N
  9 (N 12 (N 13 (N 18 L (N 20 L L (N 17 (N 19 L L L) L L)) (N 20 L (N 17 (N 19 L L L) L L) L)) (N
  17 (N 19 L (N 20 L L (N 18 (N 25 (N 32 L L L) L L) L L)) (N 20 L (N 18 (N 26 (N 33 L L L) L L) L
  L) L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N
  19 L (N 20 L L L) L) (N 19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L)) (N 17 (N 19 L (N 20 L L
  (N 18 (N 24 L (N 25 (N 32 L L L) L L) L) L L)) (N 20 L (N 18 (N 26 (N 33 L L L) L L) L L) L)) (N
  18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N 19 L (N 20
  L L L) L) (N 19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L))) (N 17 (N 19 L (N 20 L L (N 18 (N 25
  (N 32 L L L) L L) L L)) (N 20 L (N 18 (N 13 L L (N 26 (N 33 L L L) L L)) L L) L)) L (N 18 (N 19
  L (N 20 L L L) L) (N 19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L)) (N 13 (N 18 L (N 24 L L (N
  17 (N 19 L L (N 20 L L L)) L L)) (N 17 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L L L) L
  L) L L) L L) L)) (N 17 (N 19 L (N 20 L L (N 18 (N 25 (N 32 L L L) L L) L L)) (N 20 L (N 18 (N 26
  (N 33 L L L) L L) L L) L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L
  L) L L)) (N 18 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L) L)) L)) (N
  19 (N 17 L (N 18 L L (N 20 (N 23 (N 30 L L L) L L) L L)) (N 18 L (N 20 (N 24 (N 31 L L L) L L) L
  L) L)) L (N 17 (N 20 L (N 18 (N 26 (N 33 L L L) L L) L L) L) (N 18 (N 20 L L L) L L) L)) (N 13
  (N 12 (N 20 L (N 26 L L (N 19 (N 17 L L (N 18 L L L)) L L)) (N 17 (N 19 L (N 18 (N 25 (N 32 L L
  L) L L) L L) L) (N 18 (N 19 L L L) L L) L)) (N 17 (N 19 L (N 20 L L (N 18 (N 25 (N 32 L L L) L
  L) L L)) (N 20 L (N 18 (N 24 L (N 25 (N 32 L L L) L L) L) L L) L)) L (N 18 (N 19 L (N 20 L L L)
  L) (N 19 (N 20 (N 24 (N 31 L L L) L L) L L) L L) L)) (N 17 (N 19 L (N 20 L L (N 18 (N 25 (N 32 L
  L L) L L) L L)) (N 20 L (N 18 (N 24 L (N 25 (N 32 L L L) L L) L) L L) L)) (N 18 (N 19 L L (N 20
  L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N 19 L (N 20 L L L) L) (N 19 (N
  20 (N 23 (N 30 L L L) L L) L L) L L) L))) (N 12 (N 17 (N 19 L (N 20 L L (N 18 (N 25 (N 32 L L L)
  L L) L L)) (N 20 L (N 18 (N 25 (N 32 L L L) L L) L L) L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19
  (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 24 (N 31 L
  L L) L L) L L) L L) L)) (N 17 (N 20 L L (N 19 L (N 18 (N 25 (N 32 L L L) L L) L L) L)) L (N 20
  (N 18 L (N 19 (N 24 (N 31 L L L) L L) L L) L) L L)) (N 17 (N 19 L (N 20 L L (N 18 (N 25 (N 32 L
  L L) L L) L L)) (N 20 L (N 18 (N 25 (N 32 L L L) L L) L L) L)) (N 18 (N 19 L L (N 20 L L L)) L
  (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23
  (N 30 L L L) L L) L L) L L) L))) L)) (N 9 (N 12 (N 13 (N 18 L (N 20 L L (N 17 (N 19 L L L) L L))
  (N 20 L (N 17 (N 19 L L L) L L) L)) (N 17 (N 19 L (N 20 L L (N 18 (N 25 (N 32 L L L) L L) L L))
  (N 20 L (N 18 (N 23 L (N 25 (N 32 L L L) L L) L) L L) L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19
  (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L
  L L) L L) L L) L L) L)) (N 17 (N 19 L (N 20 L L (N 18 (N 24 L (N 25 (N 32 L L L) L L) L) L L))
  (N 20 L (N 18 (N 23 L (N 25 (N 32 L L L) L L) L) L L) L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19
  (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L
  L L) L L) L L) L L) L))) (N 13 (N 18 L (N 24 L L (N 17 (N 19 L L (N 20 L L L)) L L)) (N 17 (N 19
  L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L) L)) (N 20 (N 17 L (N 18 L L (N
  19 (N 23 (N 30 L L L) L L) L L)) (N 18 L (N 19 (N 23 (N 30 L L L) L L) L L) L)) L (N 17 (N 19 L
  (N 18 (N 25 (N 32 L L L) L L) L L) L) (N 18 (N 19 L L L) L L) L)) (N 17 (N 19 L (N 20 L L (N 18
  (N 24 L (N 25 (N 32 L L L) L L) L) L L)) (N 20 L (N 18 (N 25 (N 32 L L L) L L) L L) L)) (N 18 (N
  19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N 18 (N 19 L (N 20 L L L)
  L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L) L))) L) (N 12 (N 13 (N 20 L (N 26 L L (N 19 (N
  17 L L (N 18 L L L)) L L)) (N 17 (N 19 L (N 18 (N 25 (N 32 L L L) L L) L L) L) (N 18 (N 19 L L
  L) L L) L)) (N 18 (N 19 L (N 20 L L (N 17 (N 25 (N 32 L L L) L L) L L)) (N 20 L (N 17 (N 23 L (N
  25 (N 32 L L L) L L) L) L L) L)) L (N 17 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L L L)
  L L) L L) L L) L)) (N 17 (N 19 L (N 20 L L (N 18 (N 25 (N 32 L L L) L L) L L)) (N 20 L (N 18 (N
  23 L (N 25 (N 32 L L L) L L) L) L L) L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30
  L L L) L L) L L) L L)) (N 18 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L
  L) L))) (N 13 (N 17 (N 19 L (N 20 L L (N 18 (N 25 (N 32 L L L) L L) L L)) (N 20 L (N 18 (N 25 (N
  32 L L L) L L) L L) L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L L)
  L L)) (N 18 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L) L)) (N 18 (N
  20 L L (N 19 L (N 17 (N 25 (N 32 L L L) L L) L L) L)) L (N 20 (N 17 L (N 19 (N 23 (N 30 L L L) L
  L) L L) L) L L)) (N 17 (N 19 L (N 20 L L (N 18 (N 25 (N 32 L L L) L L) L L)) (N 20 L (N 18 (N 25
  (N 32 L L L) L L) L L) L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L
  L) L L)) (N 18 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L) L))) L) L))
  L L) L) L)))))) (S 16 (S 22 L L (S 29 L L (N 5 L L (N 8 (N 9 (N 14 L L (N 12 (N 13 (N 17 L (N 18
  L (N 19 L (N 20 L L (N 25 L (N 32 L L L) L)) (N 20 L (N 26 (N 33 L L L) L L) L)) (N 23 L (N 30 L
  L L) L)) (N 18 L (N 24 L (N 31 L L L) L) L)) L (N 17 L (N 19 L (N 20 L (N 27 (N 34 (N 18 L L (N
  23 L (N 30 L L L) L)) L L) L L) (N 25 L (N 32 L L L) L)) (N 20 L (N 26 (N 33 (N 35 L (N 23 L (N
  27 (N 30 L L (N 31 L L L)) L L) (N 24 L (N 31 L L L) L)) L) L L) L L) L)) (N 19 L (N 18 (N 24 L
  (N 31 L (N 35 (N 20 L (N 27 (N 34 L L L) L L) (N 25 L (N 32 L L L) L)) L L) L) L) (N 20 L (N 27
  (N 24 L (N 31 (N 34 L L L) L L) L) L L) (N 25 L (N 32 L L L) L)) L) L))) L (N 13 (N 18 L (N 19 L
  (N 20 L (N 27 (N 34 (N 17 L L (N 23 L (N 24 L (N 31 L L L) L) L)) L L) L L) (N 25 L (N 32 L L L)
  L)) (N 20 L (N 26 (N 33 (N 35 L (N 23 L (N 27 (N 30 L L (N 31 L L L)) L L) (N 24 L (N 30 L L L)
  L)) L) L L) L L) L)) (N 19 L (N 17 (N 23 L (N 30 L (N 35 (N 20 L (N 27 (N 34 L L L) L L) (N 25 L
  (N 32 L L L) L)) L L) L) L) (N 20 L (N 27 (N 23 L (N 30 (N 34 L L L) L L) L) L L) (N 25 L (N 32
  L L L) L)) L) L)) L L))) L (N 12 (N 14 L L (N 13 (N 17 L (N 19 L (N 20 L (N 27 (N 34 (N 18 L L
  (N 23 L (N 30 L L L) L)) L L) L L) (N 23 L (N 27 (N 30 L L (N 24 L (N 18 (N 31 L (N 34 L L L) L)
  (N 31 (N 34 L L L) L L) L) L)) L L) (N 18 (N 24 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N
  24 L (N 31 (N 34 L L L) L L) L) L L) L))) (N 20 L (N 26 (N 33 L L L) L L) L)) (N 20 L (N 18 (N
  24 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 19 L (N 27 (N 24 L (N 31 (N 34 L L L) L L) L) L L)
  (N 26 (N 33 L L L) L L)) L) L)) L L)) L (N 13 (N 14 L L (N 19 L (N 20 L (N 26 (N 23 L (N 27 (N
  24 L (N 33 (N 35 L (N 30 L L (N 31 L L L)) L) L (N 17 (N 30 L (N 34 L L L) L) (N 30 (N 34 L L L)
  L L) L)) (N 17 (N 18 L (N 34 L L L) L) (N 18 (N 34 L L L) L L) L)) L L) (N 24 L (N 27 (N 33 (N
  30 L (N 35 L L L) L) L L) L L) L)) L (N 33 (N 30 L (N 34 (N 17 (N 23 L (N 27 L L L) L) (N 23 (N
  27 L L L) L L) L) L L) L) L L)) (N 17 (N 23 L (N 30 L (N 35 (N 25 (N 32 L (N 34 L L L) L) (N 27
  (N 32 L L L) L L) L) L L) L) L) (N 23 (N 25 L (N 27 L L L) L) (N 27 (N 30 (N 32 L (N 34 L L L)
  L) L L) L L) L) L)) (N 20 L (N 26 (N 24 L (N 27 (N 33 (N 31 L (N 35 L L L) L) L L) L L) L) L L)
  L))) L L))) L (N 9 (N 12 (N 14 L L (N 13 (N 18 L (N 19 L (N 20 L (N 27 (N 34 (N 17 L L (N 23 L
  (N 24 L (N 31 L L L) L) L)) L L) L L) (N 24 L (N 27 (N 31 L L (N 23 L (N 17 (N 30 L (N 34 L L L)
  L) (N 30 (N 34 L L L) L L) L) L)) L L) (N 17 (N 23 L (N 27 (N 30 L (N 34 L L L) L) L L) L) (N 27
  (N 23 L (N 30 (N 34 L L L) L L) L) L L) L))) (N 20 L (N 26 (N 33 L L L) L L) L)) (N 20 L (N 17
  (N 23 L (N 27 (N 30 L (N 34 L L L) L) L L) L) (N 19 L (N 27 (N 23 L (N 30 (N 34 L L L) L L) L) L
  L) (N 26 (N 33 L L L) L L)) L) L)) L (N 19 L (N 20 L (N 26 (N 23 L (N 27 (N 24 L (N 33 (N 35 L
  (N 30 L L (N 31 L L L)) L) L (N 18 (N 31 L (N 34 L L L) L) (N 31 (N 34 L L L) L L) L)) (N 33 (N
  30 L (N 35 L L L) L) L L)) L L) (N 24 L (N 27 (N 17 (N 18 L (N 34 L L L) L) (N 18 (N 34 L L L) L
  L) L) L L) L)) L (N 33 (N 31 L (N 34 (N 18 (N 24 L (N 27 L L L) L) (N 24 (N 27 L L L) L L) L) L
  L) L) L L)) (N 18 (N 24 L (N 31 L (N 35 (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L)
  L L) L) L) (N 24 (N 25 L (N 27 L L L) L) (N 27 (N 31 (N 32 L (N 34 L L L) L) L L) L L) L) L)) (N
  20 L (N 26 (N 23 L (N 27 (N 33 (N 30 L (N 35 L L L) L) L L) L L) L) L L) L)))) L (N 13 (N 14 L L
  L) L L)) L L))))) L (S 22 L L (S 29 L L (N 5 L L (N 8 (N 9 (N 14 L L (N 12 (N 13 (N 17 L (N 18 L
  (N 19 L (N 27 (N 34 (N 35 L (N 20 (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 31 L L L) L)) L (N
  25 L (N 32 L L L) L)) L) L L) L L) (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L) L)) (N
  19 L (N 23 L (N 30 L L L) L) L)) (N 18 L (N 19 L (N 24 L (N 31 L L L) L) L) L)) L (N 17 L (N 19
  L (N 23 L (N 27 (N 30 L L (N 32 L (N 25 L L (N 34 (N 35 L L L) L L)) L)) L L) (N 25 L (N 27 (N
  32 L L (N 30 L (N 34 (N 35 L L L) L L) L)) L L) L)) (N 18 (N 20 L (N 26 (N 33 (N 35 L (N 23 L (N
  27 (N 30 L L (N 31 L L L)) L L) (N 24 L (N 31 L L L) L)) L) L L) L L) L) (N 20 (N 23 L (N 27 (N
  26 L (N 30 L L (N 32 L (N 33 (N 31 L (N 34 L L L) L) L L) L)) L) L L) (N 25 L (N 24 (N 26 L (N
  27 (N 31 L (N 33 (N 34 L L L) L L) L) L L) L) (N 27 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L)
  L)) (N 26 (N 27 (N 33 (N 34 (N 35 L (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 31 L L L) L)) L)
  L L) L L) L L) L L) L) L)) (N 19 L (N 18 (N 20 L (N 24 L (N 27 (N 31 L (N 34 (N 35 L L L) L L)
  L) L L) L) L) (N 20 (N 23 L (N 27 (N 24 (N 31 L (N 34 (N 35 L L L) L L) L) (N 31 (N 25 L (N 26 L
  L (N 32 L L L)) (N 26 L (N 33 L L L) L)) L L) L) L L) (N 25 L (N 27 (N 26 L (N 30 L (N 32 L L (N
  33 (N 34 L L L) L L)) L) L) L L) L)) (N 27 (N 34 (N 35 L (N 23 L (N 30 L L (N 31 (N 33 L L L) L
  L)) (N 25 L (N 26 (N 24 L (N 30 L L L) L) L L) L)) L) L L) L L) L) L) L))) L (N 13 (N 18 L (N 19
  L (N 24 L (N 27 (N 31 L L (N 32 L (N 25 L L (N 34 (N 35 L L L) L L)) L)) L L) (N 25 L (N 27 (N
  32 L L (N 31 L (N 34 (N 35 L L L) L L) L)) L L) L)) (N 17 (N 20 L (N 26 (N 33 (N 35 L (N 23 L (N
  27 (N 30 L L (N 31 L L L)) L L) (N 24 L (N 30 L L L) L)) L) L L) L L) L) (N 20 (N 24 L (N 27 (N
  26 L (N 31 L L (N 32 L (N 33 (N 30 L (N 34 L L L) L) L L) L)) L) L L) (N 25 L (N 23 (N 26 L (N
  27 (N 30 L (N 33 (N 34 L L L) L L) L) L L) L) (N 27 (N 26 L (N 30 (N 33 L L L) L L) L) L L) L)
  L)) (N 26 (N 27 (N 33 (N 34 (N 35 L (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 30 L L L) L)) L)
  L L) L L) L L) L L) L) L)) (N 19 L (N 17 (N 20 L (N 23 L (N 27 (N 30 L (N 34 (N 35 L L L) L L)
  L) L L) L) L) (N 20 (N 23 (N 30 L (N 34 (N 24 L (N 27 (N 35 L L L) L L) (N 25 L (N 26 L (N 27 (N
  35 L L L) L L) L) L)) L L) L) (N 27 (N 30 (N 24 L (N 25 L (N 26 L L (N 32 L L L)) (N 26 L (N 33
  L L L) L)) (N 25 L (N 26 L (N 31 L (N 32 L L (N 33 L L L)) L) L) L)) L L) L L) L) (N 27 (N 34 (N
  35 L (N 23 (N 26 L L (N 24 L (N 30 L L L) L)) (N 30 (N 31 L L (N 32 L L L)) L L) L) L) L L) L L)
  L) L) L)) L L))) L (N 12 (N 14 L L (N 13 (N 17 L (N 23 L (N 27 (N 30 L L (N 18 (N 24 L (N 31 L
  (N 34 (N 35 L L L) L L) L) L) (N 24 (N 31 L (N 34 (N 35 L L L) L L) L) (N 31 (N 32 L (N 33 L (N
  34 (N 35 L L L) L L) L) L) L L) L) L)) L L) (N 18 (N 24 L (N 27 (N 31 L (N 34 (N 35 L L L) L L)
  L) L L) L) (N 24 (N 25 L (N 26 L (N 27 (N 31 L (N 34 (N 35 L L L) L L) L) L L) L) L) (N 27 (N 31
  (N 25 (N 19 L (N 20 L L (N 32 L (N 34 (N 35 L L L) L L) L)) (N 20 L (N 33 L L L) L)) (N 26 (N 34
  L (N 19 L L (N 20 L L L)) L) (N 33 L L (N 30 L (N 32 L (N 19 (N 34 (N 35 L L L) L L) L L) L) L))
  L) L) L L) L L) L) L)) (N 18 (N 19 L (N 20 L (N 24 L (N 27 (N 31 L (N 34 (N 35 L L L) L L) L) L
  L) L) L) L) (N 19 (N 20 (N 23 L (N 27 (N 34 L (N 30 L L (N 33 L L L)) L) L L) (N 25 L (N 26 L (N
  27 (N 30 L (N 34 L L L) L) L L) L) L)) (N 23 L (N 27 (N 26 L L (N 25 L (N 32 L (N 34 (N 35 L L
  L) L L) L) L)) L L) (N 25 L (N 26 (N 27 L L L) L L) L)) L) (N 20 (N 23 L (N 27 (N 24 (N 31 L (N
  34 (N 35 L L L) L L) L) (N 31 (N 35 L (N 25 L L (N 26 L L L)) L) L L) L) L L) (N 26 L (N 27 (N
  25 L (N 30 L (N 33 L L (N 32 (N 34 L L L) L L)) L) L) L L) L)) (N 27 (N 34 (N 35 L (N 23 L (N 30
  L L (N 31 (N 33 L L L) L L)) (N 26 (N 24 L (N 30 L L L) L) L L)) L) L L) L L) L) L) L)) L L)) L
  (N 13 (N 14 L L (N 27 (N 34 (N 35 L (N 17 (N 18 L (N 19 L (N 20 L (N 23 L (N 30 L L (N 31 L L
  L)) (N 24 L (N 30 L L L) L)) (N 23 L (N 30 L L L) L)) (N 20 L (N 24 L (N 31 L L L) L) L)) (N 19
  L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L (N 31 L L L))
  (N 24 L (N 30 L L L) L)) (N 23 L (N 30 L L L) L)) (N 20 L (N 24 L (N 31 L L L) L) L)) (N 19 (N
  20 L (N 25 L (N 32 L L (N 26 (N 24 L (N 31 L L L) L) L L)) (N 26 (N 23 L (N 31 L L L) L) L L))
  (N 25 L (N 32 L L L) L)) (N 20 (N 26 L (N 33 L L (N 30 (N 32 L L L) L L)) (N 33 L (N 23 (N 25 L
  L L) L L) L)) L (N 23 (N 25 L (N 30 L L L) L) (N 30 (N 32 L L L) L L) L)) (N 20 (N 26 L (N 33 L
  L L) L) (N 26 (N 24 L (N 31 L L L) L) L L) L)) (N 19 (N 20 L (N 25 L (N 32 L L L) L) L) (N 20 (N
  23 (N 25 L (N 30 L L L) L) (N 30 (N 32 L L L) L L) L) (N 23 (N 25 L (N 30 L L L) L) (N 30 (N 32
  L L L) L L) L) L) L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N 20 L (N 26 (N
  23 L (N 31 L L L) L) L L) L) (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 23 L (N 31 L L L) L) L L) L)
  L) L)) L) (N 35 (N 17 (N 19 L (N 32 L L (N 20 L (N 30 L L L) L)) (N 20 L (N 32 L L L) L)) (N 30
  (N 33 L L (N 19 L (N 32 L L L) L)) L (N 31 (N 33 L L L) L L)) (N 18 (N 19 L (N 33 L L L) L) (N
  30 (N 33 L L L) L L) L)) (N 17 (N 19 L (N 20 L (N 30 L L (N 18 (N 31 L L L) L L)) (N 23 L (N 30
  L L L) L)) (N 20 L (N 24 L (N 26 (N 30 L L (N 23 L (N 25 (N 32 L L L) L L) L)) L L) L) L)) (N 30
  (N 33 L L (N 23 L (N 31 (N 32 L (N 19 (N 25 L L L) L L) L) L L) L)) L (N 31 (N 33 L L L) L L))
  (N 18 (N 19 L (N 20 L (N 31 L L L) L) L) (N 30 (N 33 L L L) L L) L)) L) L) (N 34 (N 35 (N 17 (N
  19 L (N 25 L L (N 20 L (N 23 L L L) L)) (N 20 L (N 25 L L L) L)) (N 23 (N 26 L L (N 19 L (N 25 L
  L L) L)) L (N 24 (N 26 L L L) L L)) (N 18 (N 19 L (N 26 L L L) L) (N 23 (N 26 L L L) L L) L)) (N
  17 (N 19 L (N 20 L (N 23 L L (N 18 (N 24 L L L) L L)) (N 23 L (N 30 L L L) L)) (N 20 L (N 23 L L
  (N 24 (N 25 L L L) L L)) L)) (N 23 (N 26 L L (N 24 (N 25 L (N 19 (N 32 L L L) L L) L) L L)) L (N
  24 (N 26 L L L) L L)) (N 18 (N 19 L (N 20 L (N 24 L L L) L) L) (N 23 (N 26 L L L) L L) L)) L) (N
  35 (N 17 (N 19 L (N 20 L L (N 18 (N 23 L (N 25 (N 32 L L L) L L) L) L L)) (N 20 L (N 18 (N 24 L
  L L) L L) L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L)) (N
  18 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 26 L L L) L L) L L) L L) L)) L L) L) L)) L L)))
  L (N 9 (N 12 (N 14 L L (N 13 (N 18 L (N 24 L (N 27 (N 31 L L (N 17 (N 23 L (N 30 L (N 34 (N 35 L
  L L) L L) L) L) (N 23 (N 30 L (N 34 (N 35 L L L) L L) L) (N 30 (N 32 L (N 33 L (N 34 (N 35 L L
  L) L L) L) L) L L) L) L)) L L) (N 17 (N 23 L (N 27 (N 30 L (N 34 (N 35 L L L) L L) L) L L) L) (N
  23 (N 25 L (N 26 L (N 27 (N 30 L (N 34 (N 35 L L L) L L) L) L L) L) L) (N 27 (N 30 (N 25 (N 19 L
  (N 20 L L (N 32 L (N 34 (N 35 L L L) L L) L)) (N 20 L (N 33 L L L) L)) (N 26 (N 34 L (N 19 L L
  (N 20 L L L)) L) (N 33 L L (N 31 L (N 32 L (N 19 (N 34 (N 35 L L L) L L) L L) L) L)) L) L) L L)
  L L) L) L)) (N 17 (N 19 L (N 20 L (N 23 L (N 27 (N 30 L (N 34 (N 35 L L L) L L) L) L L) L) L) L)
  (N 19 (N 20 (N 23 (N 30 L (N 34 (N 27 L (N 24 L L (N 26 L L L)) L) L L) L) (N 27 (N 30 (N 34 L
  (N 31 L L (N 33 L L L)) L) L L) L L) L) (N 23 (N 26 L L (N 24 L (N 25 L (N 27 (N 30 L (N 32 L (N
  34 (N 35 L L L) L L) L) L) L L) L) L)) (N 27 (N 26 L L (N 24 L (N 25 L (N 30 (N 32 L (N 33 L L
  (N 31 L (N 34 (N 35 L L L) L L) L)) L) L L) L) L)) L L) L) L) (N 20 (N 23 (N 30 L (N 34 (N 35 L
  (N 24 L L (N 25 L L L)) L) L L) L) (N 27 (N 30 (N 35 L (N 31 L L (N 32 L L L)) L) L L) L L) L)
  (N 27 (N 34 (N 35 L (N 23 (N 26 L L (N 24 L (N 30 L L L) L)) (N 30 (N 26 L L (N 32 L L L)) L L)
  L) L) L L) L L) L) L) L)) L (N 27 (N 34 (N 35 L (N 17 (N 18 L (N 19 L (N 20 L (N 23 L (N 30 L L
  (N 31 L L L)) (N 24 L (N 30 L L L) L)) (N 24 L (N 31 L L L) L)) (N 20 L (N 23 L (N 30 L L L) L)
  L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 18 (N 19 L (N 20 L (N 23 L (N 30 L L (N 31
  L L L)) (N 24 L (N 30 L L L) L)) (N 24 L (N 31 L L L) L)) (N 20 L (N 23 L (N 30 L L L) L) L)) (N
  19 (N 20 L (N 25 L (N 32 L L (N 26 (N 23 L (N 30 L L L) L) L L)) (N 26 (N 23 L (N 30 L L L) L) L
  L)) (N 25 L (N 32 L L L) L)) (N 20 (N 26 L (N 33 L L (N 30 (N 32 L L L) L L)) (N 33 L (N 23 (N
  25 L L L) L L) L)) L (N 24 (N 25 L (N 31 L L L) L) (N 31 (N 32 L L L) L L) L)) (N 20 (N 26 L (N
  33 L L L) L) (N 26 (N 23 L (N 30 L L L) L) L L) L)) (N 19 (N 20 L (N 26 (N 23 L (N 30 L L L) L)
  L L) L) (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 23 L (N 30 L L L) L) L L) L) L)) (N 18 (N 19 L (N
  20 L (N 23 L (N 30 L L L) L) L) L) (N 19 (N 20 L (N 25 L (N 32 L L L) L) L) (N 20 (N 23 (N 25 L
  (N 30 L (N 24 (N 31 L L L) L L) L) L) (N 30 (N 31 (N 24 L (N 25 L L L) L) L L) L L) L) (N 23 (N
  25 L (N 26 L L (N 33 L L L)) L) (N 30 (N 26 L L (N 33 L L L)) L L) L) L) L) L)) L) (N 35 (N 17
  (N 19 L (N 33 L L (N 20 L (N 30 L L L) L)) (N 20 L (N 30 L L L) L)) (N 30 (N 33 L L (N 20 L (N
  32 L L L) L)) L (N 31 (N 33 L L L) L L)) (N 18 (N 19 L (N 32 L L L) L) (N 30 (N 20 L (N 32 L L
  L) L) L L) L)) (N 17 (N 19 L (N 20 L (N 30 L L (N 18 (N 31 L L L) L L)) (N 24 L (N 30 L L (N 23
  L (N 25 (N 32 L L L) L L) L)) L)) (N 20 L (N 30 L L L) L)) (N 30 (N 33 L L (N 31 (N 18 L (N 19
  (N 20 (N 24 L (N 25 L (N 26 L L L) L) L) L L) L L) L) L L)) L (N 31 (N 33 L L L) L L)) (N 18 (N
  19 L (N 20 L (N 31 L L L) L) L) (N 30 (N 23 L (N 31 (N 24 L (N 25 (N 19 L (N 32 L L L) L) L L)
  L) L L) L) L L) L)) L) L) (N 34 (N 35 (N 17 (N 19 L (N 26 L L (N 20 L (N 23 L L L) L)) (N 20 L
  (N 23 L L L) L)) (N 23 (N 26 L L (N 20 L (N 25 L L L) L)) L (N 24 (N 26 L L L) L L)) (N 18 (N 19
  L (N 25 L L L) L) (N 23 (N 20 L (N 25 L L L) L) L L) L)) (N 17 (N 19 L (N 20 L (N 23 L L (N 18
  (N 24 L L L) L L)) (N 25 (N 24 L (N 31 L L L) L) L L)) (N 20 L (N 23 L L L) L)) (N 23 (N 26 L L
  (N 24 (N 18 L (N 19 (N 20 (N 25 L (N 32 L L L) L) L L) L L) L) L L)) L (N 24 (N 26 L L L) L L))
  (N 18 (N 19 L (N 20 L (N 24 L L L) L) L) (N 23 (N 24 (N 25 L (N 19 (N 32 L L L) L L) L) L L) L
  L) L)) L) (N 35 (N 17 (N 19 L (N 20 L L (N 18 (N 24 L (N 25 (N 32 L L L) L L) L) L L)) (N 20 L
  (N 23 L L L) L)) (N 18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 (N 23 (N 26 L L L) L L) L L) L L))
  (N 18 (N 19 L (N 20 L L L) L) (N 19 (N 20 (N 23 (N 30 L L L) L L) L L) L L) L)) L L) L) L))) L
  (N 13 (N 14 L L L) L L)) L L)))))) (S 16 (S 22 L (S 29 L L (N 5 L L (N 14 (N 12 L (N 13 L (N 20
  (N 26 (N 33 L L L) L L) L L) (N 19 L (N 17 (N 20 (N 27 L (N 26 (N 25 L L (N 33 L (N 34 L L L)
  L)) L L) L) (N 26 (N 27 L L L) L L) L) L (N 24 (N 27 L (N 20 (N 25 L L (N 8 (N 9 L L (N 26 (N 32
  L (N 30 (N 34 L L L) L L) L) L L)) L L)) L L) L) L L)) (N 20 (N 23 (N 27 L (N 24 (N 25 L (N 26
  (N 35 L L L) L L) (N 26 (N 33 L (N 35 L L L) L) (N 33 (N 34 L (N 30 (N 35 L L L) L L) L) L L)
  L)) L (N 9 (N 8 L (N 17 (N 30 L L L) L L) (N 17 (N 18 L (N 30 L (N 34 L L L) L) L) (N 30 (N 34 L
  (N 35 L L L) L) L L) L)) (N 17 (N 18 L (N 30 L (N 34 L L L) L) L) (N 30 (N 8 L L (N 34 L (N 35 L
  L L) L)) L L) L) L)) L) L (N 24 (N 27 L (N 8 (N 9 L (N 18 (N 31 L (N 34 L L L) L) (N 31 (N 34 L
  (N 35 L L L) L) L L) L) (N 32 L (N 30 (N 34 L (N 35 L L L) L) L L) L)) (N 30 (N 34 L (N 35 L L
  L) L) L L) L) L) L L)) (N 26 (N 27 L L L) L L) L))) (N 13 L (N 19 L (N 18 (N 20 (N 27 L (N 26 (N
  25 L L (N 33 L (N 34 L L L) L)) L L) L) (N 26 (N 27 L L L) L L) L) L (N 23 (N 27 L (N 20 (N 25 L
  L (N 9 (N 8 L L (N 26 (N 32 L (N 31 (N 34 L L L) L L) L) L L)) L L)) L L) L) L L)) (N 20 (N 23
  (N 27 L (N 24 (N 25 L (N 26 (N 35 L L L) L L) (N 26 (N 33 L (N 35 L L L) L) (N 33 (N 34 L (N 31
  (N 35 L L L) L L) L) L L) L)) L (N 9 (N 8 L (N 17 (N 30 L (N 34 L L L) L) (N 30 (N 34 L (N 35 L
  L L) L) L L) L) (N 32 L (N 31 (N 34 L (N 35 L L L) L) L L) L)) (N 31 (N 34 L (N 35 L L L) L) L
  L) L)) L) L (N 24 (N 27 L (N 8 (N 9 L (N 18 (N 31 L L L) L L) (N 17 (N 18 L (N 30 L (N 34 L L L)
  L) L) (N 18 (N 31 L (N 34 L L L) L) (N 31 (N 34 L L L) L L) L) L)) (N 17 (N 18 L (N 31 (N 9 L L
  (N 34 L (N 35 L L L) L)) L L) L) (N 30 (N 34 L (N 35 L L L) L) L L) L) L) L) L L)) (N 26 (N 27 L
  L L) L L) L)) L)) L (N 19 L (N 20 (N 12 L (N 13 L (N 26 (N 27 L (N 25 L L (N 33 (N 34 L (N 35 L
  L L) L) L L)) L) L L) (N 9 (N 17 (N 27 L (N 26 (N 25 L L (N 23 (N 8 L L (N 30 L (N 34 L L L) L))
  L L)) L L) L) L (N 24 (N 18 L (N 25 L L (N 8 (N 23 (N 27 L (N 26 (N 30 L (N 31 L (N 32 L L (N 33
  (N 34 L L L) L L)) L) L) L L) L) L L) L L)) L) L L)) (N 27 (N 17 L L (N 18 L L L)) L L) L)) (N
  13 L (N 8 (N 18 (N 27 L (N 26 (N 25 L L (N 24 (N 9 L L (N 31 L (N 34 L L L) L)) L L)) L L) L) L
  (N 23 (N 17 L (N 25 L L (N 9 (N 24 (N 27 L (N 26 (N 30 L (N 31 L (N 32 L L (N 33 (N 34 L L L) L
  L)) L) L) L L) L) L L) L L)) L) L L)) (N 27 (N 17 L L (N 18 L L L)) L L) L) L)) (N 23 (N 27 L (N
  25 L L (N 26 (N 12 L L (N 13 L L L)) L L)) L) L (N 24 (N 27 L (N 18 (N 9 L L (N 13 L L L)) L L)
  L) L L)) L) (N 20 (N 12 L (N 13 L (N 26 (N 27 L (N 33 (N 34 L (N 35 L L L) L) L L) L) L L) (N 9
  (N 17 (N 27 L (N 34 L (N 30 (N 23 L L (N 8 L (N 18 L (N 24 (N 31 L L L) L L) L) L)) L L) L) L)
  (N 30 (N 34 L (N 35 (N 23 L L (N 24 L L L)) L L) L) L L) L) (N 17 (N 27 L (N 34 L (N 30 (N 23 L
  L (N 8 L (N 18 L (N 24 (N 25 L L L) L L) L) L)) L L) L) L) (N 30 (N 34 L (N 35 (N 23 L L (N 24 L
  L L)) L L) L) L L) L) L)) (N 13 L (N 8 (N 18 (N 27 L (N 34 L (N 31 (N 24 L L (N 9 L (N 17 L (N
  23 (N 30 L L L) L L) L) L)) L L) L) L) (N 31 (N 34 L (N 35 (N 23 L L (N 24 L L L)) L L) L) L L)
  L) (N 18 (N 27 L (N 34 L (N 31 (N 24 L L (N 9 L (N 17 L (N 23 (N 25 L L L) L L) L) L)) L L) L)
  L) (N 31 (N 34 L (N 35 (N 23 L L (N 24 L L L)) L L) L) L L) L) L) L)) (N 23 (N 27 L (N 25 L L (N
  26 (N 12 L L (N 13 L L L)) L L)) L) L (N 24 (N 27 L (N 25 L L (N 13 (N 26 L L L) L L)) L) L L))
  L))))) (S 29 L L (N 5 L L (N 14 (N 12 L (N 13 L (N 20 (N 26 (N 33 L L L) L L) L L) (N 19 L (N 17
  (N 20 (N 27 L (N 26 (N 25 L L (N 33 L (N 34 L L L) L)) L L) L) (N 26 (N 27 L (N 25 L L (N 33 (N
  34 L L L) L L)) L) L L) L) L (N 18 (N 20 (N 27 L (N 26 (N 25 L L (N 33 L (N 34 L L L) L)) L L)
  L) (N 26 (N 27 L (N 25 L L (N 33 (N 34 L L L) L L)) L) L L) L) (N 20 (N 8 (N 9 L L (N 25 L (N 32
  L L L) L)) L (N 9 (N 25 L (N 32 L L L) L) L L)) L L) L)) (N 20 (N 23 (N 27 L (N 25 L (N 26 (N 33
  L (N 30 (N 35 L L L) L L) L) (N 33 (N 34 L (N 30 (N 35 L L L) L L) L) L L) L) (N 9 (N 8 L (N 30
  (N 17 L L (N 34 L (N 35 L L L) L)) L L) (N 32 L (N 30 (N 17 L (N 24 (N 34 L (N 35 L L L) L) L L)
  L) L L) L)) (N 24 (N 26 (N 33 L (N 30 (N 34 L (N 35 L L L) L) L L) L) (N 33 (N 34 L (N 30 (N 35
  L L L) L L) L) L L) L) (N 26 (N 33 L (N 30 (N 17 L L (N 8 L (N 18 (N 31 (N 32 L L (N 34 L (N 35
  L L L) L)) L L) L L) L)) L L) L) L L) L) L)) L) (N 26 (N 25 L L (N 27 L (N 30 (N 33 L (N 34 L L
  L) L) L L) L)) L L) L) (N 26 (N 27 L (N 25 L L (N 33 (N 34 L (N 35 L L L) L) L L)) L) L L) L)))
  (N 13 L (N 19 L (N 18 (N 20 (N 27 L (N 26 (N 25 L L (N 33 L (N 34 L L L) L)) L L) L) (N 26 (N 27
  L (N 25 L L (N 33 (N 34 L L L) L L)) L) L L) L) L (N 17 (N 20 (N 27 L (N 26 (N 25 L L (N 33 L (N
  34 L L L) L)) L L) L) (N 26 (N 27 L (N 25 L L (N 33 (N 34 L L L) L L)) L) L L) L) (N 20 (N 8 (N
  9 L L (N 25 L (N 32 L L L) L)) L (N 9 (N 25 L (N 32 L L L) L) L L)) L L) L)) (N 20 (N 24 (N 27 L
  (N 25 L (N 26 (N 33 L (N 31 (N 35 L L L) L L) L) (N 33 (N 34 L (N 31 (N 35 L L L) L L) L) L L)
  L) (N 8 (N 9 L (N 31 (N 18 L L (N 34 L (N 35 L L L) L)) L L) (N 32 L (N 31 (N 18 L (N 23 (N 34 L
  (N 35 L L L) L) L L) L) L L) L)) (N 23 (N 26 (N 33 L (N 31 (N 34 L (N 35 L L L) L) L L) L) (N 33
  (N 34 L (N 31 (N 35 L L L) L L) L) L L) L) (N 26 (N 33 L (N 31 (N 18 L L (N 9 L (N 17 (N 30 (N
  32 L L (N 34 L (N 35 L L L) L)) L L) L L) L)) L L) L) L L) L) L)) L) (N 26 (N 25 L L (N 27 L (N
  31 (N 33 L (N 34 L L L) L) L L) L)) L L) L) (N 26 (N 27 L (N 25 L L (N 33 (N 34 L (N 35 L L L)
  L) L L)) L) L L) L)) L)) L (N 19 L (N 20 (N 12 L (N 13 L (N 26 (N 27 L (N 25 L L (N 33 (N 34 L
  (N 35 L L L) L) L L)) L) L L) (N 9 (N 17 (N 27 L (N 26 (N 25 L L (N 34 L (N 18 L L (N 33 (N 35 L
  L L) L L)) L)) L L) L) L (N 18 (N 24 L (N 26 (N 27 L (N 25 L L (N 31 L (N 33 (N 35 L L L) L L)
  L)) L) L L) L) (N 8 (N 23 (N 27 L (N 24 (N 25 L L (N 26 (N 30 L (N 31 L (N 32 L L (N 33 (N 34 L
  L L) L L)) L) L) L L)) L L) L) (N 25 L L (N 26 (N 27 L L L) L L)) L) L (N 23 (N 25 L (N 27 L L
  L) L) (N 25 (N 26 L L L) L L) L)) L)) (N 8 (N 17 (N 18 L L (N 23 L (N 30 L L L) L)) L (N 18 (N
  27 L (N 26 (N 25 L L (N 34 L (N 33 (N 35 L L L) L L) L)) L L) L) L L)) L (N 17 (N 18 L L (N 27 L
  (N 26 (N 25 L L (N 32 (N 30 L (N 33 L L L) L) L L)) L L) L)) L (N 18 (N 25 (N 23 L (N 26 L L L)
  L) L L) L L))) L)) (N 13 L (N 8 (N 18 (N 27 L (N 26 (N 25 L L (N 34 L (N 17 L L (N 33 (N 35 L L
  L) L L)) L)) L L) L) L (N 17 (N 23 L (N 26 (N 27 L (N 25 L L (N 30 L (N 33 (N 35 L L L) L L) L))
  L) L L) L) (N 9 (N 23 (N 27 L (N 24 (N 25 L L (N 26 (N 30 L (N 31 L (N 32 L L (N 33 (N 34 L L L)
  L L)) L) L) L L)) L L) L) (N 26 (N 27 L L L) L L) L) L (N 23 (N 25 L (N 27 L L L) L) (N 26 (N 27
  L L L) L L) L)) L)) (N 9 (N 17 (N 18 L L (N 27 L (N 26 (N 25 L L (N 34 L (N 33 (N 35 L L L) L L)
  L)) L L) L)) L (N 18 (N 24 L (N 31 L L L) L) L L)) L (N 17 (N 18 L L (N 25 (N 23 L (N 26 L L L)
  L) L L)) L (N 18 (N 27 L (N 26 (N 25 L L (N 32 (N 30 L (N 33 L L L) L) L L)) L L) L) L L))) L)
  L)) (N 26 (N 27 (N 23 L (N 24 L (N 33 (N 35 L (N 25 (N 30 (N 34 L (N 8 L L (N 12 L L L)) L) L (N
  31 (N 13 L (N 18 L L L) L) L L)) L (N 30 (N 34 L (N 12 L L (N 13 L L L)) L) L (N 31 (N 13 L (N
  18 L L L) L) L L))) L) (N 34 (N 35 L (N 17 L L (N 18 L L L)) L) L L) L) (N 9 (N 12 (N 17 (N 30 L
  (N 8 L L (N 34 L (N 18 L L (N 25 (N 35 L L L) L L)) L)) L) (N 30 (N 34 L L L) L L) L) (N 17 (N
  18 L L (N 13 (N 25 (N 8 L L (N 30 (N 33 L L L) L L)) L L) L L)) L L) L) (N 17 (N 18 L L (N 25 (N
  34 L (N 33 (N 30 L (N 35 L L L) L) L L) L) L L)) L L) L)) (N 24 L (N 8 (N 13 (N 18 (N 31 L (N 9
  L L (N 34 L (N 17 L L (N 25 (N 35 L L L) L L)) L)) L) (N 31 (N 34 L L L) L L) L) (N 18 (N 17 L L
  (N 12 (N 25 (N 9 L L (N 30 L (N 35 L L L) L)) L L) L L)) L L) L) (N 18 (N 17 L L (N 25 (N 34 L
  (N 33 (N 31 L (N 35 L L L) L) L L) L) L L)) L L) L) L)) (N 34 (N 17 (N 18 L L (N 30 L (N 23 (N
  25 L L (N 33 L (N 8 L L (N 12 L L L)) L)) (N 33 (N 35 L L L) L L) L) L)) L (N 18 (N 31 L (N 24
  (N 25 L L (N 33 L (N 9 L L (N 13 L L L)) L)) (N 33 (N 35 L L L) L L) L) L) L L)) L L) L) (N 27
  (N 33 (N 12 (N 13 (N 23 L (N 8 (N 17 L (N 30 L L (N 18 (N 34 L L L) L L)) (N 24 L (N 31 L (N 18
  (N 34 L L L) L L) L) L)) L (N 30 L (N 34 (N 35 L L L) L L) L)) (N 24 L (N 31 L (N 18 (N 34 L L
  L) L L) L) L)) L (N 23 L (N 30 L (N 34 (N 35 L L L) L L) L) L)) L (N 13 (N 24 L (N 31 L (N 34 (N
  35 L L L) L L) L) L) L L)) L L) L L) L) L) (N 20 (N 12 L (N 13 L (N 26 (N 27 L (N 33 (N 34 L (N
  35 L L L) L) L L) L) L L) (N 9 (N 17 (N 27 L (N 34 L (N 35 (N 18 L (N 23 (N 30 L L L) L L) (N 23
  (N 30 L (N 33 L L L) L) (N 26 (N 30 L L L) L L) L)) L L) L) L) (N 23 (N 27 L (N 30 (N 8 L L (N
  25 L (N 32 L (N 35 L L L) L) L)) L L) L) L L) L) (N 17 (N 27 L (N 34 L (N 35 (N 18 L (N 23 (N 30
  L L L) L L) (N 23 (N 30 L (N 33 L L L) L) (N 26 (N 30 L L L) L L) L)) L L) L) L) (N 23 (N 27 L
  (N 30 (N 8 L L (N 25 L (N 32 L L L) L)) L L) L) L L) L) L)) (N 13 L (N 8 (N 18 (N 27 L (N 34 L
  (N 35 (N 17 L (N 24 (N 31 L L L) L L) (N 23 (N 30 L (N 31 L (N 24 (N 26 L L L) L L) L) L) (N 26
  (N 31 L (N 33 L L L) L) L L) L)) L L) L) L) (N 24 (N 27 L (N 31 (N 9 L L (N 25 L (N 32 L (N 35 L
  L L) L) L)) L L) L) L L) L) (N 18 (N 27 L (N 34 L (N 35 (N 17 L (N 24 (N 31 L L L) L L) (N 23 (N
  30 L (N 25 L L (N 31 L (N 9 (N 24 L L L) L L) L)) L) (N 26 (N 25 L L (N 30 (N 32 L L L) L L)) L
  L) L)) L L) L) L) (N 24 (N 27 L (N 31 (N 9 L L (N 25 L (N 32 L L L) L)) L L) L) L L) L) L) L))
  (N 26 (N 27 (N 23 L (N 24 L (N 33 (N 35 L (N 25 (N 30 (N 34 L (N 12 L L (N 13 L L L)) L) L (N 31
  (N 13 L (N 18 L L L) L) L L)) L (N 8 (N 9 (N 32 L (N 34 (N 30 L L (N 31 L L L)) L L) L) (N 13 (N
  30 L L (N 31 L L L)) L (N 30 (N 12 L (N 17 L L L) L) L L)) L) (N 9 (N 12 (N 30 L L (N 31 L L L))
  L (N 31 (N 13 L (N 18 L L L) L) L L)) (N 32 (N 30 L L (N 31 L L L)) L L) L) L)) L) (N 34 (N 35 L
  (N 17 L L (N 18 L L L)) L) L L) L) (N 9 (N 12 (N 17 (N 30 L (N 8 L L (N 34 L (N 18 L L (N 32 (N
  35 L L L) L L)) L)) L) (N 30 (N 8 L L (N 32 L (N 34 L L L) L)) L L) L) (N 17 (N 18 L L (N 13 (N
  25 (N 8 L L (N 30 (N 33 L L L) L L)) L L) L L)) L L) L) (N 25 (N 35 L (N 30 (N 34 L (N 12 (N 33
  L L L) L L) L) L L) L) L L) L)) (N 24 L (N 8 (N 13 (N 18 (N 31 L (N 9 L L (N 34 L (N 17 L L (N
  32 (N 35 L L L) L L)) L)) L) (N 31 (N 9 L L (N 32 L (N 34 L L L) L)) L L) L) (N 18 (N 17 L L (N
  12 (N 25 (N 9 L L (N 30 L (N 35 L L L) L)) L L) L L)) L L) L) (N 25 (N 35 L (N 31 (N 34 L (N 13
  (N 33 L L L) L L) L) L L) L) L L) L) L)) (N 25 (N 23 L (N 17 (N 18 (N 34 L (N 33 (N 35 L L L) L
  L) L) L (N 9 (N 8 L (N 12 (N 30 L L L) L L) (N 32 L (N 34 (N 30 L (N 35 L L L) L) L L) L)) (N 12
  (N 30 L (N 8 L L (N 32 (N 35 L L L) L L)) L) (N 30 (N 8 L L (N 32 L (N 34 L L L) L)) L L) L) L))
  L (N 18 (N 24 L (N 35 (N 33 L (N 34 L L L) L) L L) L) L L)) (N 24 L (N 18 (N 8 (N 9 L (N 13 (N
  31 L L L) L L) (N 32 L (N 34 (N 17 L L (N 30 L (N 35 L L L) L)) L L) L)) (N 13 (N 31 L (N 9 L L
  (N 32 (N 35 L L L) L L)) L) (N 31 (N 9 L L (N 32 L (N 34 L L L) L)) L L) L) L) L L) L)) L (N 8
  (N 9 (N 32 L (N 34 (N 23 (N 12 L (N 13 L L (N 17 L L L)) (N 13 L (N 31 L L L) L)) (N 17 (N 18 L
  L (N 12 L (N 30 L L L) L)) L (N 18 (N 13 L (N 31 L L L) L) L L)) L) L L) L) (N 18 (N 23 (N 12 L
  (N 13 L L (N 17 L L L)) (N 13 L (N 17 L L (N 24 (N 31 L L L) L L)) L)) (N 17 (N 34 L (N 32 (N 33
  (N 35 L L L) L L) L L) L) L (N 13 (N 24 L (N 31 L L L) L) (N 24 (N 31 L L L) L L) L)) L) L (N 12
  (N 17 L (N 23 L L L) L) (N 17 (N 23 L (N 30 L L L) L) L L) L)) L) (N 9 (N 17 (N 23 (N 12 L (N 13
  L L (N 30 L L L)) (N 13 L (N 18 (N 24 L (N 31 L L L) L) L L) L)) (N 12 (N 24 L (N 30 L L (N 18
  (N 13 L (N 31 L L L) L) L L)) L) L (N 18 (N 13 L (N 24 L (N 31 L L L) L) L) L L)) L) L (N 13 (N
  18 L (N 23 L L L) L) (N 18 (N 24 L (N 31 L L L) L) L L) L)) (N 32 (N 17 (N 18 (N 34 L (N 33 (N
  35 L L L) L L) L) L (N 30 L (N 12 (N 23 L L L) L L) L)) L (N 18 (N 31 L (N 13 (N 24 L L L) L L)
  L) L L)) L L) L) L)) L) (N 27 (N 33 (N 12 (N 13 (N 23 L (N 8 (N 17 L (N 30 L L (N 24 L (N 31 L
  (N 18 (N 34 L L L) L L) L) L)) (N 24 L (N 31 L (N 18 (N 34 L L L) L L) L) L)) L (N 30 L (N 17 (N
  34 L L L) L L) L)) (N 24 L (N 31 L (N 18 (N 34 L L L) L L) L) L)) L (N 23 L (N 30 L (N 17 (N 34
  L L L) L L) L) L)) L (N 13 (N 24 L (N 31 L (N 18 (N 34 L L L) L L) L) L) L L)) L L) L L) L)
  L)))))) (S 22 L L (S 29 L L (N 5 L L (N 14 (N 12 L (N 13 L (N 20 (N 26 (N 33 L L L) L L) L L) (N
  17 (N 18 (N 19 L (N 20 (N 27 L (N 34 L L L) L) (N 26 (N 27 (N 34 L L L) L L) L L) L) (N 20 (N 27
  L (N 26 (N 33 L (N 34 L L L) L) L L) L) (N 26 (N 33 (N 35 L (N 23 (N 27 L (N 30 L L L) L) (N 25
  L L (N 30 (N 34 L L L) L L)) L) L) L L) L L) L)) L (N 9 (N 8 L (N 23 (N 30 L L L) L L) (N 19 L
  (N 20 (N 23 (N 27 L (N 25 L L (N 26 (N 30 L (N 33 L L L) L) L L)) L) (N 25 L L (N 26 (N 27 L (N
  30 (N 34 L L L) L L) L) L L)) L) (N 26 (N 27 (N 23 L (N 24 L (N 25 L L (N 30 (N 33 L L L) L L))
  L) L) L L) L L) L) (N 20 (N 23 (N 27 L (N 26 (N 30 L (N 33 L L L) L) L L) L) (N 25 L L (N 26 (N
  27 L (N 30 (N 32 L (N 33 L (N 34 L L L) L) L) L L) L) L L)) L) (N 26 (N 33 (N 35 L (N 23 (N 27 L
  (N 30 L L L) L) (N 25 L L (N 30 (N 34 L L L) L L)) L) L) L L) L L) L))) (N 19 L (N 8 (N 23 L (N
  30 L L L) L) L (N 20 (N 23 (N 25 L L (N 27 L (N 26 (N 30 L (N 33 L L L) L) L L) L)) (N 26 (N 25
  L L (N 27 L (N 30 (N 34 L L L) L L) L)) L L) L) (N 26 (N 25 L L (N 27 (N 23 L (N 24 L (N 30 (N
  33 L L L) L L) L) L) L L)) L L) L)) (N 20 (N 23 (N 27 L (N 25 L L (N 26 (N 30 L (N 33 L L L) L)
  L L)) L) (N 26 (N 25 L L (N 27 L (N 30 (N 8 L L (N 32 L (N 34 L L L) L)) L L) L)) L L) L) (N 26
  (N 33 (N 35 L (N 23 (N 27 L (N 30 L L L) L) (N 25 L L (N 30 (N 34 L L L) L L)) L) L) L L) L L)
  L)) L)) L (N 18 (N 19 L (N 20 (N 23 (N 27 L (N 25 L L (N 26 (N 33 L (N 30 (N 34 L L L) L L) L) L
  L)) L) (N 26 (N 25 L L (N 8 (N 9 L (N 27 L (N 30 (N 34 L L L) L L) L) L) L L)) L L) L) (N 26 (N
  27 (N 23 L (N 24 L (N 25 L L (N 8 (N 9 L (N 30 (N 34 L L L) L L) L) L L)) L) L) L L) L L) L) (N
  8 (N 9 L (N 20 (N 23 (N 27 L (N 25 L L (N 26 (N 30 L (N 33 L L L) L) L L)) L) (N 25 L L (N 26 (N
  27 L (N 30 (N 33 L (N 34 L L L) L) L L) L) L L)) L) (N 26 (N 33 (N 35 L (N 23 (N 27 L (N 30 L L
  L) L) (N 25 L L (N 30 (N 34 L L L) L L)) L) L) L L) L L) L) (N 25 L (N 23 (N 27 L (N 20 (N 26 (N
  30 L (N 32 L L L) L) L L) L L) L) L L) L)) (N 23 (N 27 L (N 25 L L (N 26 (N 30 (N 34 L (N 35 L L
  L) L) L L) L L)) L) L L) L)) L L))) (N 13 L (N 17 (N 18 (N 19 L (N 20 (N 27 L (N 34 L L L) L) (N
  26 (N 27 (N 34 L L L) L L) L L) L) (N 20 (N 27 L (N 26 (N 33 L (N 34 L L L) L) L L) L) (N 26 (N
  33 (N 35 L (N 24 (N 27 L (N 31 L L L) L) (N 25 L L (N 31 (N 34 L L L) L L)) L) L) L L) L L) L))
  L (N 19 L (N 20 (N 23 (N 27 L (N 25 L L (N 8 L (N 9 (N 26 (N 30 L (N 33 L L L) L) L L) L L) L))
  L) (N 26 (N 25 L L (N 27 L (N 33 L (N 30 (N 34 L L L) L L) L) L)) L L) L) (N 26 (N 27 (N 23 L (N
  24 L (N 25 L L (N 8 L (N 9 (N 30 (N 33 L L L) L L) L L) L)) L) L) L L) L L) L) (N 9 (N 8 L (N 20
  (N 23 (N 27 L (N 25 L L (N 26 (N 30 L (N 33 L L L) L) L L)) L) (N 25 L L (N 26 (N 27 L (N 30 (N
  33 L (N 34 L L L) L) L L) L) L L)) L) (N 26 (N 33 (N 35 L (N 23 (N 27 L (N 30 L L L) L) (N 25 L
  L (N 30 (N 34 L L L) L L)) L) L) L L) L L) L) (N 25 L (N 24 (N 27 L (N 20 (N 26 (N 31 L (N 32 L
  L L) L) L L) L L) L) L L) L)) (N 24 (N 27 L (N 25 L L (N 26 (N 31 (N 34 L (N 35 L L L) L) L L) L
  L)) L) L L) L))) L (N 18 (N 8 (N 9 L (N 24 (N 31 L L L) L L) (N 19 L (N 20 (N 23 (N 27 L (N 25 L
  L (N 26 (N 30 L (N 33 L L L) L) L L)) L) (N 25 L L (N 26 (N 27 L (N 33 L (N 30 (N 34 L L L) L L)
  L) L) L L)) L) (N 26 (N 27 (N 23 L (N 24 L (N 25 L L (N 31 (N 33 L L L) L L)) L) L) L L) L L) L)
  (N 20 (N 23 (N 27 L (N 26 (N 30 L (N 33 L L L) L) L L) L) (N 26 (N 27 L (N 33 L (N 30 (N 34 L L
  L) L L) L) L) L L) L) (N 26 (N 33 (N 35 L (N 23 (N 27 L (N 30 L L L) L) (N 30 (N 34 L L L) L L)
  L) L) L L) L L) L))) (N 19 L (N 9 (N 24 L (N 31 L L L) L) L (N 20 (N 23 (N 25 L L (N 27 L (N 26
  (N 33 L (N 30 (N 34 L L L) L L) L) L L) L)) (N 26 (N 25 L L (N 27 L (N 30 (N 34 L L L) L L) L))
  L L) L) (N 26 (N 25 L L (N 27 (N 23 L (N 24 L (N 30 (N 34 L L L) L L) L) L) L L)) L L) L)) (N 20
  (N 23 (N 27 L (N 25 L L (N 26 (N 33 L (N 30 (N 34 L L L) L L) L) L L)) L) (N 26 (N 25 L L (N 27
  L (N 30 (N 33 L (N 34 L L L) L) L L) L)) L L) L) (N 26 (N 33 (N 35 L (N 23 (N 27 L (N 25 L L (N
  30 (N 34 L L L) L L)) L) (N 25 L L (N 30 (N 34 L L L) L L)) L) L) L L) L L) L)) L) L L)) L)) L
  (N 17 (N 18 (N 19 L (N 20 (N 27 L (N 34 L L L) L) (N 27 (N 34 L L L) L L) L) (N 20 (N 27 L (N 34
  L (N 35 (N 12 L (N 26 (N 33 L L L) L L) (N 13 L (N 26 (N 33 L L L) L L) L)) L L) L) L) (N 26 (N
  27 (N 34 L (N 33 (N 35 L (N 23 L L (N 24 L L L)) L) L L) L) (N 34 (N 25 (N 23 L (N 24 L (N 35 (N
  33 L (N 12 L L (N 13 L L L)) L) L L) (N 30 L (N 12 (N 35 L L L) L L) L)) (N 24 L (N 31 L (N 13
  (N 35 L L L) L L) L) L)) L (N 8 (N 23 L (N 9 (N 24 L (N 32 L (N 35 (N 33 L (N 12 L L (N 13 L L
  L)) L) L L) L) L) (N 12 L (N 30 L L (N 13 (N 24 L (N 31 L L L) L) L L)) (N 31 L (N 13 (N 24 L L
  L) L L) L)) L) L) (N 9 (N 24 L (N 13 L (N 31 L L (N 12 (N 23 L (N 30 L L L) L) L L)) (N 30 L (N
  12 (N 23 L L L) L L) L)) L) (N 32 (N 23 (N 33 L (N 12 L L (N 13 L L L)) L) (N 30 L L (N 31 L (N
  13 (N 24 L L L) L L) L)) L) L L) L) L)) L L) L) (N 27 (N 23 L L (N 24 L L L)) L L) L) L)) L (N
  19 L (N 20 (N 12 L (N 13 L (N 26 (N 27 L (N 33 (N 34 L L L) L L) L) L L) (N 9 (N 23 (N 27 L (N
  25 L L (N 26 (N 30 L (N 8 L L (N 32 (N 31 L (N 33 (N 34 L L L) L L) L) L L)) L) L L)) L) (N 26
  (N 27 L (N 30 (N 34 L L L) L L) L) L L) L) (N 8 (N 23 L (N 30 L L L) L) L (N 23 (N 25 L L (N 27
  L (N 26 (N 30 L (N 32 (N 31 L (N 24 (N 35 L L L) L L) L) L L) L) L L) L)) (N 26 (N 27 L (N 30 (N
  34 L L L) L L) L) L L) L)) L)) (N 13 L (N 8 (N 23 L (N 26 (N 25 L L (N 27 L (N 30 L (N 33 (N 34
  L L L) L L) L) L)) L L) L) (N 9 (N 23 (N 25 L L (N 27 L (N 26 (N 30 L (N 33 (N 34 L L L) L L) L)
  L L) L)) (N 26 (N 27 L (N 30 (N 34 L L L) L L) L) L L) L) L (N 25 (N 23 L (N 24 L (N 26 (N 27 L
  (N 30 (N 32 L L L) L L) L) L L) L) L) L L)) L) L)) (N 27 (N 23 L (N 26 (N 34 (N 30 L (N 35 L L
  L) L) L L) L L) L) L L) L) (N 9 (N 12 (N 20 L (N 23 L (N 26 (N 30 L (N 8 L L (N 33 (N 35 L L L)
  L L)) L) L L) L) L) (N 20 (N 13 L (N 26 (N 27 L (N 33 (N 34 L (N 35 L L L) L) L L) L) L L) (N 23
  (N 27 L (N 26 (N 30 L (N 8 L L (N 25 L (N 32 (N 31 L (N 33 (N 35 L L L) L L) L) L L) L)) L) L L)
  L) (N 26 (N 27 L (N 30 (N 8 L L (N 25 (N 24 L (N 35 L L L) L) L L)) L L) L) L L) L)) (N 26 (N 33
  (N 35 L (N 13 (N 23 L (N 30 L L L) L) L (N 23 (N 27 L (N 30 L L L) L) (N 30 (N 34 L L L) L L)
  L)) L) L L) L L) L) L) (N 12 (N 20 L (N 23 L (N 26 (N 30 L (N 8 L L (N 25 (N 32 (N 35 L L L) L
  L) L L)) L) L L) L) L) (N 20 (N 13 L (N 26 (N 27 L (N 33 (N 34 L (N 35 L L L) L) L L) L) L L) (N
  23 (N 27 L (N 25 L L (N 8 L (N 30 L L L) L)) L) (N 26 (N 27 L (N 30 (N 8 L L (N 25 (N 24 L (N 35
  L L L) L) L L)) L L) L) L L) L)) (N 26 (N 33 (N 35 L (N 13 (N 23 L (N 30 L L L) L) L (N 23 (N 27
  L (N 30 L L L) L) (N 30 (N 34 L L L) L L) L)) L) L L) L L) L) L) L))) L (N 18 (N 19 L (N 20 (N
  12 L (N 13 L (N 26 (N 27 L (N 33 (N 34 L L L) L L) L) L L) (N 9 (N 24 L (N 26 (N 25 L L (N 27 L
  (N 31 L (N 33 (N 34 L L L) L L) L) L)) L L) L) (N 8 (N 23 (N 25 L L (N 27 L (N 26 (N 30 L (N 33
  (N 34 L L L) L L) L) L L) L)) (N 26 (N 27 L (N 30 (N 34 L L L) L L) L) L L) L) L (N 25 (N 23 L
  (N 24 L (N 26 (N 27 L (N 30 (N 32 L L L) L L) L) L L) L) L) L L)) L)) (N 13 L (N 8 (N 23 (N 27 L
  (N 25 L L (N 26 (N 30 L (N 33 (N 34 L L L) L L) L) L L)) L) (N 26 (N 27 L (N 34 (N 30 L (N 33 L
  L L) L) L L) L) L L) L) (N 9 (N 24 L (N 31 L L L) L) L (N 23 (N 25 L L (N 27 L (N 26 (N 32 (N 30
  L (N 31 L (N 24 (N 35 L L L) L L) L) L) L L) L L) L)) (N 26 (N 27 L (N 30 (N 34 L L L) L L) L) L
  L) L)) L) L)) (N 27 (N 24 L (N 26 (N 34 (N 31 L (N 35 L L L) L) L L) L L) L) L L) L) (N 8 (N 13
  (N 20 L (N 24 L (N 26 (N 31 L (N 9 L L (N 33 (N 35 L L L) L L)) L) L L) L) L) (N 20 (N 12 L (N
  26 (N 27 L (N 33 (N 34 L (N 35 L L L) L) L L) L) L L) (N 23 (N 27 L (N 26 (N 30 L (N 33 (N 35 L
  L L) L L) L) L L) L) (N 26 (N 27 L (N 24 (N 31 L (N 9 L L (N 25 L (N 32 (N 30 L (N 33 (N 35 L L
  L) L L) L) L L) L)) L) (N 31 (N 35 L L L) L L) L) L) L L) L)) (N 26 (N 33 (N 35 L (N 12 (N 24 L
  (N 31 L L L) L) L (N 23 (N 27 L (N 30 L L L) L) (N 30 (N 34 L L L) L L) L)) L) L L) L L) L) L)
  (N 13 (N 20 L (N 24 L (N 26 (N 31 L (N 9 L L (N 25 (N 32 (N 35 L L L) L L) L L)) L) L L) L) L)
  (N 20 (N 12 L (N 26 (N 27 L (N 33 (N 34 L (N 35 L L L) L) L L) L) L L) (N 23 (N 27 L (N 25 L L
  (N 26 (N 9 (N 24 L (N 31 L L L) L) (N 24 (N 31 L L L) L L) L) L L)) L) (N 26 (N 27 L (N 30 (N 34
  L (N 32 L L (N 25 (N 9 L (N 24 L L L) L) L L)) L) L L) L) L L) L)) (N 26 (N 33 (N 35 L (N 12 (N
  24 L (N 31 L L L) L) L (N 23 (N 27 L (N 25 L L (N 30 (N 34 L L L) L L)) L) (N 30 (N 34 L L L) L
  L) L)) L) L L) L L) L) L) L)) L L)))))) (S 22 L L (S 29 L L L)))) (S 11 L L (S 16 (S 22 (S 29 L
  L (N 5 L L (N 27 L (N 8 (N 9 (N 12 (N 14 L L (N 20 L (N 26 L L L) L)) L (N 13 (N 14 L L (N 20 L
  (N 26 L L L) L)) L L)) L (N 12 (N 14 L L (N 13 (N 20 L (N 26 L L L) L) L L)) L (N 13 (N 14 L L
  (N 20 L (N 26 L L L) L)) L L))) L (N 9 (N 12 (N 14 L L (N 20 L (N 26 L L L) L)) L (N 13 (N 14 L
  L L) L L)) L L)) L))) L (S 29 L L (N 5 L L (N 8 (N 9 (N 12 (N 14 L L (N 20 L (N 13 (N 17 L (N 18
  L (N 19 L L (N 27 (N 34 (N 35 L (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 31 L L L) L)) L) L L)
  L L)) (N 23 L (N 30 L L L) L)) (N 18 L (N 24 L (N 31 L L L) L) L)) L (N 23 L (N 30 L (N 17 L L
  (N 19 L (N 27 (N 24 L (N 34 (N 35 L L L) L L) L) L L) L)) L) L)) L)) L (N 13 (N 14 L L (N 20 L
  (N 24 L (N 31 L (N 18 L L (N 19 L (N 27 (N 23 L (N 34 (N 35 L L L) L L) L) L L) L)) L) L) L)) L
  L)) L (N 12 (N 14 L L (N 13 (N 20 L (N 17 L (N 19 L (N 27 (N 24 L (N 34 (N 18 L L (N 23 L (N 30
  L L L) L)) L L) L) L L) (N 18 (N 24 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N 24 L (N 31
  (N 34 L L L) L L) L) L L) L)) (N 18 (N 24 L (N 31 L (N 35 (N 19 L (N 27 (N 34 L L L) L L) (N 23
  L (N 25 (N 32 L (N 33 L (N 26 (N 27 L L L) L L) L) L) (N 26 (N 32 L L L) L L) L) (N 30 L (N 25
  (N 32 L (N 33 L L L) L) (N 27 (N 32 (N 26 L (N 33 L L L) L) L L) L L) L) L))) L L) L) L) (N 19 L
  (N 27 (N 24 L (N 31 (N 34 L L L) L L) L) L L) (N 23 L (N 27 (N 24 L (N 31 (N 32 L (N 34 L L L)
  L) L L) L) L L) (N 30 L (N 34 (N 31 L (N 24 (N 25 L (N 27 L L L) L) L L) L) L L) L))) L)) L) L
  L)) L (N 13 (N 14 L L (N 20 L (N 19 L (N 24 (N 25 L L (N 18 L (N 27 L L L) L)) (N 27 (N 23 L (N
  25 (N 26 (N 35 L (N 31 (N 32 L L (N 18 L (N 33 L L L) L)) L L) L) (N 33 (N 31 L (N 34 (N 35 L L
  L) L L) L) L L) L) L (N 32 (N 31 L (N 18 (N 34 L L L) L L) L) L L)) (N 25 (N 17 (N 18 L (N 34 L
  L L) L) (N 18 (N 34 L L L) L L) L) L L)) L L) L) (N 18 (N 24 L (N 31 L (N 35 (N 25 (N 32 L (N 34
  (N 26 L (N 27 L L L) L) L L) L) (N 27 (N 32 (N 33 L (N 34 L L L) L) L L) L L) L) L L) L) L) (N
  24 (N 25 L (N 27 L L L) L) (N 27 (N 31 (N 32 L (N 34 L L L) L) L L) L L) L) L)) L)) L L))) L (N
  9 (N 12 (N 14 L L (N 20 L (N 13 (N 18 L (N 19 L (N 27 (N 23 L (N 34 (N 17 L L (N 24 L (N 31 L L
  L) L)) L L) L) L L) (N 17 (N 23 L (N 27 (N 30 L (N 34 L L L) L) L L) L) (N 27 (N 23 L (N 30 (N
  34 L L L) L L) L) L L) L)) (N 17 (N 23 L (N 30 L (N 35 (N 19 L (N 27 (N 34 L L L) L L) (N 24 L
  (N 25 (N 32 L (N 33 L (N 26 (N 27 L L L) L L) L) L) (N 26 (N 32 L L L) L L) L) (N 31 L (N 25 (N
  32 L (N 33 L L L) L) (N 27 (N 32 (N 26 L (N 33 L L L) L) L L) L L) L) L))) L L) L) L) (N 19 L (N
  27 (N 23 L (N 30 (N 34 L L L) L L) L) L L) (N 23 (N 25 L (N 27 L L L) L) (N 27 (N 30 (N 32 L (N
  34 L L L) L) L L) L L) L)) L)) L (N 19 L (N 23 (N 25 L L (N 17 L (N 27 L L L) L)) (N 27 (N 24 L
  (N 25 (N 26 (N 35 L (N 30 (N 32 L L (N 17 L (N 33 L L L) L)) L L) L) (N 33 (N 30 L (N 34 (N 35 L
  L L) L L) L) L L) L) L (N 32 (N 30 L (N 17 (N 34 L L L) L L) L) L L)) (N 25 (N 17 (N 18 L (N 34
  L L L) L) (N 18 (N 34 L L L) L L) L) L L)) L L) L) (N 17 (N 23 L (N 30 L (N 35 (N 25 (N 32 L (N
  34 (N 26 L (N 27 L L L) L) L L) L) (N 27 (N 32 (N 33 L (N 34 L L L) L) L L) L L) L) L L) L) L)
  (N 23 (N 25 L (N 27 L L L) L) (N 27 (N 30 (N 32 L (N 34 L L L) L) L L) L L) L) L))) L)) L (N 13
  (N 14 L L L) L L)) L L))))) L (S 22 L L (S 29 L L L)))) (S 11 L L (S 16 (S 22 (S 29 L (N 5 L L
  (N 14 (N 27 L (N 30 (N 34 L (N 35 L L L) L) L (N 31 (N 34 L (N 35 L L L) L) L L)) L) L L)) (N 5
  L L (N 14 (N 27 L (N 19 (N 20 L (N 26 L L L) L) (N 25 (N 26 L L L) L L) L) L) L L))) (S 29 L L
  (N 5 L L (N 14 (N 19 (N 20 L (N 8 L (N 9 L (N 25 (N 32 L L L) L L) (N 12 (N 17 (N 23 L L (N 18 L
  (N 24 (N 26 L L L) L L) L)) L (N 24 (N 26 L (N 27 L L L) L) L L)) (N 26 (N 25 L (N 27 (N 17 L L
  (N 18 L L L)) L L) L) L L) L)) (N 9 L (N 13 (N 18 (N 24 L L (N 17 L (N 23 (N 26 L L L) L L) L))
  L (N 23 (N 26 L (N 27 L L L) L) L L)) (N 26 (N 25 L (N 27 (N 17 L L (N 18 L L L)) L L) L) L L)
  L) L)) L) (N 20 (N 12 L (N 13 L (N 26 (N 33 L L L) L L) (N 8 (N 17 (N 23 L L (N 18 L (N 24 (N 25
  L L L) L L) L)) L (N 24 (N 25 L (N 27 L L L) L) L L)) (N 25 (N 26 L (N 27 (N 17 L L (N 18 L L
  L)) L L) L) L L) L)) (N 13 L (N 9 (N 18 (N 24 L L (N 17 L (N 23 (N 25 L L L) L L) L)) L (N 23 (N
  25 L (N 27 L L L) L) L L)) (N 25 (N 26 L (N 27 (N 17 L L (N 18 L L L)) L L) L) L L) L) L)) (N 23
  (N 27 L (N 25 (N 26 L L L) L L) L) L (N 24 (N 27 L (N 18 (N 9 L L (N 8 (N 12 L L L) L L)) L L)
  L) L L)) L) L) L L))) (S 29 L L L)) (S 22 L L (S 29 L L L)) (S 22 L L L)))) (S 7 (S 11 (S 16 L
  (S 22 L (S 29 L L (N 14 L L (N 27 (N 5 L (N 17 (N 23 L L (N 24 L (N 18 (N 34 L (N 31 (N 9 L (N
  13 L L (N 19 L L (N 8 (N 12 L L (N 20 L (N 32 L L L) L)) L L))) (N 13 L (N 20 L L (N 12 (N 8 L L
  (N 19 L (N 32 L L L) L)) L L)) L)) L L) L) (N 31 (N 34 L (N 19 L L (N 20 L L L)) L) L L) L) L))
  L (N 18 (N 23 L L (N 24 L (N 19 L (N 9 (N 31 L (N 13 L L (N 34 (N 35 L L L) L L)) L) L (N 13 (N
  31 L (N 34 (N 35 L L L) L L) L) (N 20 L L (N 12 (N 25 (N 31 (N 32 L (N 34 L L L) L) L L) L L) L
  L)) L)) (N 20 L (N 8 (N 13 (N 31 L (N 9 L L (N 34 (N 35 L L L) L L)) L) L (N 9 (N 31 L (N 32 L
  (N 34 (N 35 L L L) L L) L) L) (N 26 (N 31 (N 32 L (N 34 L L L) L) L L) L L) L)) (N 9 (N 13 L L
  (N 31 L (N 34 (N 35 L L L) L L) L)) L (N 13 (N 31 L (N 34 (N 35 L L L) L L) L) L L)) L) L)) L))
  (N 23 (N 24 (N 35 L (N 31 (N 9 L (N 13 L L (N 25 L L (N 8 (N 12 L L (N 20 (N 26 L (N 32 L L L)
  L) L L)) L L))) (N 13 L (N 26 L L (N 12 (N 8 L L (N 19 (N 25 L (N 32 L L L) L) L L)) L L)) L)) L
  L) L) (N 31 (N 35 L (N 25 L L (N 26 L L L)) L) L L) L) L (N 24 (N 25 L (N 9 (N 31 L (N 13 L L (N
  34 (N 35 L L L) L L)) L) L (N 13 (N 31 L (N 34 (N 35 L L L) L L) L) (N 26 L L (N 12 (N 19 (N 31
  (N 32 L (N 35 L L L) L) L L) L L) L L)) L)) (N 26 L (N 8 (N 13 (N 31 L (N 9 L L (N 34 (N 35 L L
  L) L L)) L) L (N 9 (N 31 L (N 32 L (N 34 (N 35 L L L) L L) L) L) (N 20 (N 31 (N 32 L (N 35 L L
  L) L) L L) L L) L)) (N 9 (N 13 L L (N 31 L (N 34 (N 35 L L L) L L) L)) L (N 13 (N 31 L (N 34 (N
  35 L L L) L L) L) L L)) L) L)) (N 31 (N 9 (N 13 L L (N 32 L (N 33 L (N 34 (N 35 L (N 25 L L (N 8
  (N 19 L L (N 20 (N 26 L L L) L L)) L L)) L) (N 35 (N 19 L L (N 8 (N 20 (N 26 L L L) L L) L L)) L
  L) L) (N 12 (N 19 (N 25 L (N 26 L L L) L) (N 20 (N 25 L L L) L L) L) (N 30 (N 8 (N 19 L (N 25 L
  L L) L) L (N 19 (N 25 L (N 26 L L L) L) (N 20 (N 25 L L L) L L) L)) L L) L)) L)) L (N 13 (N 33 L
  (N 32 L (N 34 (N 35 L (N 26 L L (N 12 (N 19 (N 25 L L L) L L) L L)) L) (N 35 (N 20 L L (N 12 (N
  19 (N 25 L L L) L L) L L)) L L) L) (N 8 (N 19 (N 25 L (N 26 L L L) L) (N 20 (N 25 L (N 26 L L L)
  L) L L) L) (N 30 (N 12 (N 20 L (N 26 L L L) L) L (N 19 (N 25 L (N 26 L L L) L) (N 20 (N 25 L L
  L) L L) L)) L L) L)) L) L L)) L L) L)) L)) (N 17 (N 23 L L (N 24 L (N 18 (N 34 L (N 31 (N 9 L (N
  19 L L (N 8 (N 20 L (N 33 L L L) L) L L)) (N 13 L (N 20 L L (N 12 (N 8 L (N 32 L L L) L) L L))
  L)) L L) L) (N 19 L (N 20 L L (N 34 (N 31 L (N 35 L L L) L) L L)) (N 20 L (N 34 (N 31 L (N 35 L
  L L) L) L L) L)) L) L)) L (N 18 (N 23 L L (N 24 L (N 8 (N 12 (N 30 L (N 31 (N 34 L (N 9 L (N 19
  L L (N 13 L (N 20 L L L) L)) (N 13 L (N 20 L L L) L)) L) L L) L) (N 13 (N 31 L (N 30 (N 34 L L
  L) L L) L) L (N 19 L (N 9 (N 25 L (N 32 L L L) L) L L) L)) L) (N 9 (N 31 L (N 30 (N 34 L L L) L
  L) L) L (N 20 L (N 13 (N 31 L (N 30 (N 34 L L L) L L) L) L L) L)) L) L)) (N 23 (N 24 (N 35 L (N
  31 (N 9 L (N 25 L L (N 8 (N 20 (N 26 L (N 33 L L L) L) L L) L L)) (N 13 L (N 20 (N 26 L L (N 12
  (N 8 L (N 32 L L L) L) L L)) L L) L)) L L) L) (N 25 L (N 26 L L (N 35 (N 31 L (N 34 L L L) L) L
  L)) (N 26 L (N 35 (N 31 L (N 34 L L L) L) L L) L)) L) L (N 8 (N 12 (N 30 L (N 31 (N 24 (N 35 L
  (N 9 L (N 25 L L (N 13 L (N 26 L L L) L)) (N 13 L (N 26 L L L) L)) L) (N 32 L (N 19 (N 25 L L (N
  26 L (N 33 L L L) L)) L (N 33 L (N 20 (N 26 L L L) L L) L)) (N 33 L (N 20 (N 26 L L L) L L) L))
  L) L L) L) (N 13 (N 24 (N 31 L (N 30 (N 35 L L L) L L) L) (N 30 (N 31 (N 9 L (N 19 (N 25 L L (N
  26 L L L)) L (N 20 (N 26 L L L) L L)) (N 33 L (N 20 (N 26 L L L) L L) L)) (N 34 (N 35 L L L) L
  L) L) (N 31 (N 32 L L (N 33 L L L)) L L) L) L) L (N 9 (N 19 L (N 25 L (N 32 L L L) L) L) (N 19
  (N 25 L L L) L L) L)) L) (N 9 (N 12 (N 24 (N 31 L (N 30 (N 35 L L L) L L) L) (N 30 (N 31 (N 13 L
  (N 19 (N 25 L L (N 26 L L L)) L (N 20 (N 26 L L L) L L)) (N 32 L (N 19 (N 25 L L L) L L) L)) (N
  34 (N 35 L L L) L L) L) (N 31 (N 32 L L (N 33 L L L)) L L) L) L) (N 30 (N 13 (N 24 L (N 31 L (N
  34 (N 35 L L L) L L) L) L) L (N 32 L (N 19 (N 25 L L L) L L) L)) L L) L) L (N 12 (N 13 (N 20 L
  (N 26 L (N 33 L L L) L) L) (N 20 (N 26 L L L) L L) L) (N 13 (N 30 (N 33 L (N 20 (N 26 L L L) L
  L) L) L L) L L) L)) L)) L))) L L))) (S 29 L L (N 14 L L (N 5 L (N 17 (N 18 (N 19 L (N 9 (N 24 L
  (N 27 (N 23 L L (N 31 L (N 34 L L L) L)) L L) L) L (N 13 (N 24 L (N 27 (N 23 L L (N 31 L (N 34 L
  L L) L)) L L) L) (N 20 L L (N 8 (N 12 L L (N 23 L (N 30 L L L) L)) L (N 12 (N 23 L (N 30 L L L)
  L) L L))) L)) (N 20 L (N 13 (N 24 L (N 27 (N 23 L L (N 31 L (N 34 L L L) L)) L L) L) L (N 9 (N
  24 L (N 27 (N 23 L L (N 31 L (N 34 L L L) L)) L L) L) (N 8 (N 12 L L (N 23 L (N 30 L L L) L)) L
  (N 12 (N 23 L (N 30 L L L) L) L L)) L)) L)) (N 19 L (N 20 L L (N 27 (N 24 L (N 23 L L (N 31 (N
  34 L L L) L L)) L) L L)) (N 20 L (N 27 (N 24 L (N 23 L L (N 31 (N 34 L L L) L L)) L) L L) L)) L)
  L (N 18 (N 19 L (N 9 (N 24 L (N 27 (N 23 L L (N 31 L (N 13 L L (N 34 (N 35 L L L) L L)) L)) L L)
  L) L (N 13 (N 24 L (N 27 (N 23 L L (N 31 L (N 34 (N 35 L L L) L L) L)) L L) L) (N 20 L L (N 12
  (N 8 (N 23 L (N 24 (N 25 L L L) L L) (N 24 (N 25 L (N 27 L L L) L) (N 25 (N 26 (N 27 (N 31 (N 32
  L (N 34 L L L) L) L L) L L) L L) L L) L)) L (N 23 (N 25 L (N 27 L L L) L) (N 24 (N 25 L L L) L
  L) L)) L L)) L)) (N 20 L (N 8 (N 13 (N 24 L (N 27 (N 23 L L (N 31 L (N 9 L L (N 34 (N 35 L L L)
  L L)) L)) L L) L) L (N 9 (N 24 L (N 25 L (N 27 (N 23 L L (N 31 L (N 32 L (N 34 (N 35 L L L) L L)
  L) L)) L L) L) L) (N 12 (N 23 L (N 24 (N 26 L L L) L L) (N 24 (N 25 L (N 27 L L L) L) (N 25 (N
  26 (N 27 (N 31 (N 32 L (N 34 L L L) L) L L) L L) L L) L L) L)) L (N 23 (N 25 L (N 27 L L L) L)
  (N 24 (N 26 L L L) L L) L)) L)) (N 9 (N 13 L L (N 24 L (N 27 (N 23 L L (N 12 (N 31 L (N 34 (N 35
  L L L) L L) L) L L)) L L) L)) L (N 13 (N 24 L (N 27 (N 23 L L (N 31 L (N 34 (N 35 L L L) L L)
  L)) L L) L) L L)) L) L)) (N 24 (N 25 L (N 26 L (N 27 (N 31 (N 35 L (N 32 L L (N 33 L L L)) L) (N
  34 (N 35 L (N 8 (N 9 (N 13 L L (N 32 L L L)) L (N 13 (N 33 L L L) L L)) L (N 12 (N 19 (N 32 L L
  L) L L) L L)) L) L L) L) (N 34 (N 35 (N 31 L (N 30 L L (N 32 (N 33 L L L) L L)) L) L L) L L) L)
  (N 9 (N 31 L (N 13 L L (N 34 (N 12 (N 19 (N 32 L (N 35 L L L) L) (N 20 (N 32 L L L) L L) L) (N
  23 (N 8 (N 19 L (N 32 L L L) L) L (N 19 (N 32 L (N 35 L L L) L) (N 20 (N 32 L L L) L L) L)) L L)
  L) L L)) L) (N 12 (N 19 (N 31 (N 32 L L L) L L) L L) L L) L)) (N 26 L (N 8 (N 13 (N 31 L (N 9 L
  L (N 34 (N 19 (N 32 L (N 33 L (N 20 (N 27 L L L) L L) L) L) (N 20 (N 27 (N 32 L (N 35 L L L) L)
  L L) L L) L) L L)) L) (N 20 (N 31 (N 33 L L L) L L) L L) L) (N 13 (N 9 L L (N 23 (N 31 L (N 34
  (N 12 (N 20 L (N 33 L L L) L) L (N 19 (N 32 L (N 33 L (N 20 (N 27 L L L) L L) L) L) (N 20 (N 32
  L L L) L L) L)) L L) L) L L)) L L) L) L)) (N 27 (N 31 (N 9 (N 13 L L (N 32 L (N 23 (N 25 L (N 35
  L L L) L) L (N 12 (N 25 (N 34 L (N 8 L L (N 19 L L L)) L) (N 34 (N 35 L L L) L L) L) (N 8 (N 25
  L (N 19 L L (N 33 L (N 20 (N 26 L L L) L L) L)) L) L (N 30 (N 19 (N 25 L (N 35 L L L) L) (N 25
  (N 34 L L L) L L) L) L L)) L)) L)) L (N 13 (N 33 L (N 23 (N 26 L (N 35 L L L) L) L (N 8 (N 25 (N
  19 L (N 20 L L (N 32 L (N 34 (N 35 L L L) L L) L)) (N 20 L (N 26 (N 34 L L L) L L) L)) (N 35 (N
  34 L (N 20 L L (N 32 L L L)) L) L L) L) (N 12 (N 26 L (N 20 L L (N 32 L (N 19 (N 25 L L L) L L)
  L)) L) L (N 30 (N 20 (N 25 L (N 35 L L L) L) (N 26 (N 34 L L L) L L) L) L L)) L)) L) L L)) L L)
  L L) L) L)) (N 17 (N 18 (N 19 L (N 20 L (N 27 (N 34 L L L) L L) (N 24 (N 25 L (N 27 L L L) L) (N
  25 (N 23 L (N 27 (N 34 L (N 32 (N 35 L L L) L L) L) (N 34 (N 31 L (N 32 (N 35 L L L) L L) L) L
  L) L) (N 12 (N 8 L (N 32 (N 9 L L (N 31 L (N 35 L L L) L)) L L) (N 30 L (N 32 (N 9 L (N 26 (N 31
  L (N 35 L L L) L) L L) L) L L) L)) (N 26 (N 27 (N 34 L (N 32 (N 31 L (N 35 L L L) L) L L) L) (N
  34 (N 31 L (N 32 (N 35 L L L) L L) L) L L) L) (N 27 (N 34 L (N 32 (N 9 L L (N 8 L (N 13 (N 30 L
  L (N 31 L (N 35 L L L) L)) L L) L)) L L) L) L L) L) L)) (N 27 (N 23 L L (N 32 (N 31 L (N 34 L L
  L) L) L L)) L L) L) L)) (N 20 L (N 24 (N 26 L (N 27 L L L) L) (N 26 (N 23 L (N 27 (N 34 L (N 33
  (N 35 L L L) L L) L) (N 34 (N 31 L (N 33 (N 35 L L L) L L) L) L L) L) (N 8 (N 12 L (N 33 (N 13 L
  L (N 31 L (N 35 L L L) L)) L L) (N 30 L (N 33 (N 13 L (N 25 (N 31 L (N 35 L L L) L) L L) L) L L)
  L)) (N 25 (N 27 (N 34 L (N 33 (N 31 L (N 35 L L L) L) L L) L) (N 34 (N 31 L (N 33 (N 35 L L L) L
  L) L) L L) L) (N 27 (N 34 L (N 33 (N 13 L L (N 9 (N 12 L (N 30 L L (N 31 L (N 35 L L L) L)) L) L
  L)) L L) L) L L) L) L)) (N 27 (N 23 L L (N 33 (N 31 L (N 34 L L L) L) L L)) L L) L) L) L)) (N 19
  L (N 20 L L (N 27 (N 24 L (N 23 L L (N 34 (N 31 L (N 35 L L L) L) L L)) L) L L)) (N 20 L (N 27
  (N 24 L (N 23 L L (N 34 (N 31 L (N 35 L L L) L) L L)) L) L L) L)) L) L (N 18 (N 19 L (N 20 L (N
  27 (N 24 L (N 34 (N 31 L (N 35 L L L) L) L L) L) L L) (N 9 (N 24 L (N 31 L (N 35 (N 12 (N 13 L
  (N 25 (N 32 L L L) L L) (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L)) (N 13 L (N 25
  (N 32 L L L) L L) (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L)) L) L L) L) L) (N 25
  (N 24 L (N 32 (N 8 L L (N 23 L (N 30 L (N 35 L L L) L) L)) L L) L) L L) L)) (N 20 L (N 8 (N 13
  (N 24 L (N 31 L (N 35 (N 9 L (N 26 (N 33 L L L) L L) (N 25 (N 32 L (N 33 L (N 26 (N 27 L L L) L
  L) L) L) (N 27 (N 33 L (N 34 L L L) L) L L) L)) L L) L) L) (N 26 (N 24 L (N 33 (N 12 L L (N 23 L
  (N 30 L (N 35 L L L) L) L)) L L) L) L L) L) (N 13 (N 24 L (N 31 L (N 35 (N 9 L (N 26 (N 33 L L
  L) L L) (N 25 (N 32 L (N 23 L L (N 30 (N 34 L L L) L L)) L) (N 27 (N 23 L L (N 30 (N 32 L L L) L
  L)) L L) L)) L L) L) L) (N 26 (N 24 L (N 33 (N 12 L L (N 23 L (N 30 L L L) L)) L L) L) L L) L)
  L) L)) (N 24 (N 25 L (N 26 L (N 27 (N 31 (N 35 L (N 32 L L (N 33 L L L)) L) (N 34 (N 35 L (N 19
  (N 20 L L (N 32 L L L)) L (N 20 (N 33 L L L) L L)) L) L L) L) (N 34 (N 35 (N 31 L (N 30 L L (N 8
  (N 12 (N 23 L L L) L L) L L)) L) L L) L L) L) (N 9 (N 31 L (N 34 (N 12 (N 13 L (N 19 (N 32 L L
  L) L L) (N 19 (N 32 L (N 35 L L L) L) (N 20 (N 32 L L L) L L) L)) (N 13 L L (N 23 (N 19 (N 32 L
  (N 35 L L L) L) (N 20 (N 32 L L L) L L) L) L L)) L) L L) L) (N 19 (N 32 (N 8 L L (N 30 L (N 31 L
  L L) L)) L L) L L) L)) (N 26 L (N 8 (N 13 (N 31 L (N 34 (N 9 L (N 20 (N 33 L L L) L L) (N 19 (N
  32 L (N 33 L (N 20 (N 27 L L L) L L) L) L) (N 20 (N 27 (N 32 L (N 35 L L L) L) L L) L L) L)) L
  L) L) (N 20 (N 33 (N 12 L L (N 30 L (N 31 L L L) L)) L L) L L) L) (N 23 (N 9 (N 13 L (N 20 (N 31
  L (N 33 (N 34 L L L) L L) L) L L) L) L (N 13 (N 31 L (N 34 (N 19 (N 32 L (N 33 L (N 20 (N 27 L L
  L) L L) L) L) (N 20 (N 32 L L L) L L) L) L L) L) (N 19 (N 20 (N 33 (N 12 L L (N 30 L (N 31 L L
  L) L)) L L) L L) L L) L)) L L) L) L)) (N 27 (N 23 (N 25 L (N 9 (N 13 (N 31 L (N 34 (N 35 L L L)
  L L) L) L (N 12 (N 8 L (N 19 (N 32 L L L) L L) (N 30 L (N 31 (N 32 L (N 35 L L L) L) L L) L)) (N
  19 (N 32 L (N 8 L L (N 30 (N 35 L L L) L L)) L) (N 32 (N 8 L L (N 30 L (N 31 L L L) L)) L L) L)
  L)) L (N 13 (N 26 L (N 35 (N 31 L (N 34 L L L) L) L L) L) L L)) (N 26 L (N 13 (N 8 (N 9 (N 31 L
  (N 30 L L (N 12 L (N 20 (N 33 L L L) L L) L)) L) L (N 12 L (N 20 (N 33 L L L) L L) (N 30 L (N 31
  (N 32 L (N 35 L L L) L) L L) L))) (N 9 (N 31 L (N 34 (N 35 L L L) L L) L) L (N 19 (N 20 (N 33 L
  (N 34 L L L) L) (N 33 (N 34 L L L) L L) L) (N 20 (N 32 (N 34 L L L) L L) L L) L)) L) L L) L)) L
  (N 8 (N 12 (N 30 L (N 31 (N 25 (N 9 L (N 19 L L (N 20 L L L)) (N 20 L (N 33 L L L) L)) (N 9 (N
  13 L L (N 19 L (N 32 L L L) L)) L (N 13 (N 20 L (N 33 L L L) L) L L)) L) L L) L) (N 13 (N 25 (N
  9 L (N 19 L L (N 20 L L L)) (N 20 L (N 19 L L (N 26 (N 33 L L L) L L)) L)) (N 9 (N 31 L (N 30 (N
  34 (N 35 L L L) L L) L L) L) L (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L) L)) L) L (N
  9 (N 19 L (N 25 L (N 32 L L L) L) L) (N 19 (N 25 L L L) L L) L)) L) (N 9 (N 12 (N 25 (N 19 L (N
  20 L L (N 32 L L L)) (N 20 L (N 13 (N 26 L (N 33 L L L) L) L L) L)) (N 13 (N 26 L (N 31 L (N 30
  (N 32 L L (N 20 L (N 33 L L L) L)) L L) L) L) L (N 19 (N 32 L L L) L L)) L) (N 30 (N 13 (N 31 L
  (N 34 (N 35 L L L) L L) L) L (N 32 L (N 19 (N 25 L L L) L L) L)) L L) L) L (N 12 (N 13 (N 20 L
  (N 26 L (N 33 L L L) L) L) (N 20 (N 25 L L L) L L) L) (N 13 (N 30 (N 33 L (N 20 (N 26 L L L) L
  L) L) L L) L L) L)) L)) L L) L) L)))))) (S 22 L L (S 29 L L L))) (S 16 (S 22 L (S 29 L L (N 5 L
  (N 8 (N 12 (N 14 L L (N 23 L L (N 17 L (N 18 (N 30 L L (N 19 L (N 20 L (N 27 (N 34 L L L) L L)
  (N 25 (N 24 L (N 32 L (N 9 L L (N 31 (N 34 L L L) L L)) L) L) L L)) (N 20 L (N 26 (N 24 L (N 33
  (N 13 L L (N 31 L (N 35 L L L) L)) L L) L) L L) L))) L L) (N 18 (N 19 L (N 20 L (N 13 (N 24 L (N
  31 L (N 9 L L (N 30 L L (N 33 (N 26 L L (N 25 (N 35 L L L) L L)) L L))) L) L) L (N 9 (N 24 L (N
  25 L L (N 26 (N 31 L (N 30 L L (N 32 L (N 27 (N 34 L L L) L L) L)) L) L L)) L) (N 32 (N 25 L L
  (N 26 (N 24 L (N 31 L L L) L) L L)) L L) L)) (N 25 (N 24 L (N 32 L (N 9 L L (N 34 (N 27 L (N 31
  L L L) L) L L)) L) L) L L)) (N 20 L (N 26 (N 24 L (N 33 (N 13 L L (N 31 L (N 35 L L L) L)) L L)
  L) L L) L)) (N 20 L L (N 19 L (N 25 (N 9 L L (N 13 (N 24 L (N 27 (N 31 (N 32 L (N 34 L L L) L) L
  L) L L) L) L L)) L L) L)) L)))) L (N 14 (N 25 L L (N 9 L (N 13 L (N 18 (N 24 (N 31 L L L) L L) L
  L) (N 18 (N 19 L (N 32 L L (N 23 (N 27 L (N 30 L (N 17 L L (N 26 (N 31 (N 34 L L L) L L) L L))
  L) L) L (N 26 (N 27 L (N 20 (N 33 L (N 34 L L L) L) (N 33 (N 34 L L L) L L) L) L) L L))) (N 23
  (N 27 L (N 30 L (N 17 L L (N 26 (N 31 (N 34 L L L) L L) L L)) L) L) L (N 26 (N 27 L (N 20 (N 33
  L (N 34 L L L) L) (N 33 (N 34 L (N 35 L L L) L) L L) L) L) L L))) (N 19 L L (N 24 (N 27 L L L) L
  L)) L)) (N 13 L (N 18 (N 19 L (N 20 (N 27 L (N 34 L (N 17 L L (N 26 (N 33 L L L) L L)) L) L) L
  (N 23 (N 17 L (N 30 L L L) L) L L)) (N 32 L (N 31 (N 24 L (N 34 L (N 20 (N 27 L (N 35 (N 23 L L
  (N 26 L L L)) L L) L) L (N 23 (N 17 L (N 30 L L L) L) L L)) L) L) L L) L)) (N 19 L L (N 24 (N 27
  L L L) L L)) L) (N 23 (N 27 L (N 18 (N 30 L (N 17 L L (N 19 L (N 26 (N 31 (N 34 L L L) L L) L L)
  L)) L) L L) L) L L)))) L (N 18 (N 19 L (N 23 (N 25 L L (N 26 (N 27 L (N 13 L (N 20 (N 33 (N 34 L
  (N 35 L L L) L) L L) L L) (N 30 L (N 17 L L (N 31 (N 34 L L L) L L)) L)) L) L L)) L (N 26 (N 20
  (N 25 L L (N 27 L (N 34 L (N 17 L L (N 30 (N 32 L L (N 13 L (N 33 (N 35 L L L) L L) L)) L L)) L)
  L)) (N 33 (N 35 L (N 31 (N 34 L L L) L L) L) L L) L) L L)) (N 26 (N 20 (N 25 L L (N 27 L (N 34 L
  (N 33 (N 35 L L L) L L) L) L)) (N 33 (N 35 L (N 31 (N 34 L L L) L L) L) L L) L) L L)) (N 27 (N
  23 L L (N 20 (N 26 L L L) L L)) L L) L))) L (N 12 (N 14 L L (N 18 (N 19 L (N 20 L (N 13 (N 24 L
  (N 31 L (N 9 L L (N 25 (N 23 L L (N 30 (N 33 L L L) L L)) L L)) L) L) L (N 9 (N 24 L (N 31 L (N
  35 (N 23 (N 25 L L (N 26 L L L)) L (N 25 (N 32 L (N 34 L L L) L) L L)) L L) L) L) (N 32 (N 31 L
  (N 24 (N 25 L L (N 26 L L L)) L L) L) L L) L)) (N 25 (N 23 L L (N 24 L (N 26 (N 27 (N 34 L (N 32
  (N 31 L (N 35 L L L) L) L L) L) (N 35 (N 32 L (N 34 L L L) L) L L) L) L (N 13 (N 31 L (N 9 L L
  (N 30 (N 33 L L L) L L)) L) (N 31 (N 33 L L L) L L) L)) L)) L L)) (N 20 L (N 23 (N 25 L L L) L
  L) L)) (N 20 L L (N 19 L (N 25 (N 23 L L (N 24 L (N 27 (N 31 (N 32 L (N 34 L L L) L) L L) L L)
  L)) L L) L)) L)) L (N 14 (N 13 L (N 18 (N 19 L (N 20 (N 27 L (N 34 L (N 17 L L (N 23 (N 25 L L
  L) L L)) L) L) L (N 23 (N 25 L L (N 27 L (N 17 (N 30 L (N 34 L L L) L) (N 30 (N 34 L L L) L L)
  L) L)) L L)) (N 23 (N 25 L L (N 27 L (N 9 (N 24 L (N 31 L L L) L) (N 24 (N 31 L L L) L L) L) L))
  L L)) (N 19 L L (N 17 (N 23 (N 27 L L L) L L) L L)) L) (N 18 (N 19 L (N 23 (N 25 L L (N 27 L (N
  17 (N 30 L (N 34 L L L) L) (N 30 (N 34 L L L) L L) L) L)) L (N 25 (N 26 L L L) L L)) (N 23 (N 25
  L L (N 27 L (N 9 (N 24 L (N 31 L (N 30 (N 35 L L L) L L) L) L) (N 17 (N 30 L (N 34 L L L) L) (N
  30 (N 32 L (N 34 L L L) L) L L) L) L) L)) L L)) (N 27 (N 23 L L (N 26 L L L)) L L) L)) L L))) (N
  8 (N 12 (N 14 L L (N 23 L L (N 17 L (N 18 (N 19 L (N 20 L (N 27 (N 34 L L L) L L) (N 25 (N 24 L
  (N 32 L (N 9 L L (N 26 (N 34 (N 27 L (N 31 L L L) L) L L) L L)) L) L) L L)) (N 20 L (N 26 (N 24
  L (N 33 (N 13 L L (N 25 (N 9 L (N 31 L (N 32 L L L) L) L) L L)) L L) L) L L) L)) (N 24 (N 25 L L
  (N 26 L L L)) L L) L) (N 30 L (N 18 (N 19 L (N 20 L (N 34 (N 27 L (N 31 L (N 24 (N 13 L L (N 25
  L L L)) L L) L) L) L L) (N 25 (N 9 L (N 32 L L L) L) L L)) (N 20 L (N 13 (N 24 L (N 31 L L L) L)
  L L) L)) (N 19 L (N 9 (N 25 L L (N 13 (N 20 L (N 24 L L L) L) L L)) L (N 13 (N 20 L (N 24 (N 26
  L L L) L L) L) L L)) (N 20 L (N 13 (N 24 (N 26 L L L) L L) L L) L)) L) L)))) L (N 13 (N 14 L L
  (N 18 (N 24 L (N 31 L (N 33 (N 30 L L (N 20 L (N 23 (N 26 L L L) L L) L)) L L) L) L) (N 19 L (N
  9 (N 24 L (N 20 L L (N 25 L L L)) L) L (N 20 L (N 24 (N 27 L L L) L L) (N 23 (N 25 L L L) L L)))
  (N 20 L (N 24 (N 26 L L L) L L) L)) L)) (N 33 (N 14 (N 25 L L (N 34 L (N 9 L (N 18 (N 19 L (N 32
  L L (N 20 (N 26 L L (N 17 L (N 27 L L L) L)) L (N 23 (N 17 L (N 27 L L L) L) L L))) (N 20 (N 26
  L L (N 17 L (N 23 (N 30 L L L) L L) L)) L (N 23 (N 17 L (N 30 L L L) L) L L))) (N 19 L L (N 24
  (N 27 L L L) L L)) L) (N 26 (N 20 L L (N 19 L (N 18 (N 23 (N 17 L (N 27 L L L) L) L L) L L) L))
  L L)) L)) L (N 18 (N 19 L (N 20 (N 27 L (N 34 L (N 17 L L (N 23 (N 30 L L L) L L)) L) L) L (N 23
  (N 25 L L L) L L)) (N 20 (N 26 (N 25 L L (N 27 L (N 32 L (N 31 (N 9 L (N 24 L (N 34 L L L) L) L)
  L L) L) L)) L L) L L)) (N 19 L L (N 20 (N 26 (N 27 L L L) L L) L L)) L)) L L) L)) L (N 9 (N 12
  (N 14 L L (N 18 (N 24 L (N 31 L (N 35 (N 13 L (N 20 L L (N 19 L (N 25 (N 32 L L L) L L) L)) (N
  19 L (N 20 L (N 23 (N 25 L L (N 26 L L L)) L (N 25 (N 30 (N 17 L (N 34 L L L) L) L L) L L)) (N
  25 (N 23 L L (N 26 (N 33 L L L) L L)) L L)) (N 20 L (N 23 (N 25 L L L) L L) L))) L L) L) L) (N
  19 L (N 13 (N 24 L (N 20 L L (N 25 (N 23 L L (N 17 (N 27 (N 30 L (N 31 L L L) L) L L) L L)) L
  L)) L) L (N 20 L (N 24 (N 27 L L L) L L) (N 25 (N 23 L L (N 24 L (N 17 (N 26 (N 27 (N 30 L (N 31
  (N 32 L (N 34 L L L) L) L L) L) L L) L L) L L) L)) L L))) (N 20 L (N 23 (N 25 L L L) L L) L))
  L)) L (N 14 (N 13 L (N 23 (N 25 L L (N 27 L (N 18 (N 24 L (N 31 L (N 32 L L L) L) L) L L) L)) L
  L) L) L L)) (N 12 (N 14 L L (N 18 (N 19 L (N 32 (N 31 L (N 20 L (N 13 (N 24 L (N 30 L L (N 23 (N
  25 L L L) L L)) L) L (N 23 (N 25 L L (N 26 L L L)) L (N 25 (N 24 L (N 30 L L L) L) L L))) (N 25
  (N 23 L L (N 24 L (N 30 L L L) L)) L L)) L) L L) (N 20 L (N 23 (N 25 L L L) L L) L)) (N 19 L L
  (N 20 L L L)) L)) L (N 14 (N 13 L (N 23 (N 25 L L (N 27 L (N 18 (N 33 (N 32 L (N 19 L L (N 31 (N
  24 L (N 34 L L L) L) L L)) L) L L) L L) L)) L L) L) L L)) L)))) (S 29 L L (N 5 L (N 8 (N 12 (N
  14 L L (N 17 L (N 18 (N 23 L L (N 30 L L (N 19 L (N 20 L (N 26 (N 24 L (N 25 (N 27 (N 34 L L L)
  L L) L L) L) L L) (N 24 (N 25 L (N 27 L L L) L) (N 25 (N 26 (N 32 L (N 9 L L (N 31 (N 34 L L L)
  L L)) L) L L) L L) L)) (N 20 L (N 26 (N 24 L (N 33 (N 13 L L (N 31 L (N 35 L L L) L)) L L) L) L
  L) L)))) L L) (N 18 (N 19 L (N 20 L (N 13 (N 24 L (N 23 L L (N 26 (N 31 L (N 9 L L (N 33 L L L))
  L) L L)) L) L (N 9 (N 24 L (N 23 L L (N 25 L (N 32 L L L) L)) L) (N 25 (N 32 L L L) L L) L)) (N
  23 L (N 24 (N 25 L (N 27 L L L) L) L L) (N 24 (N 25 L (N 27 L L L) L) (N 26 (N 25 (N 32 L (N 9 L
  L (N 34 (N 27 L (N 31 L L L) L) L L)) L) (N 27 (N 32 (N 9 L L (N 13 (N 31 L (N 33 L L L) L) L
  L)) L L) L L) L) L L) L))) (N 20 L (N 26 (N 24 L (N 23 L L (N 33 (N 13 L L (N 31 L (N 35 L L L)
  L)) L L)) L) L L) L)) (N 20 L L (N 19 L (N 9 (N 25 L (N 32 L L L) L) L (N 13 (N 23 L (N 24 (N 25
  L L L) L L) (N 24 (N 25 L (N 27 L L L) L) (N 26 (N 27 (N 31 (N 32 L (N 34 L L L) L) L L) L L) L
  L) L)) L L)) L)) L))) L (N 14 (N 9 L (N 13 L (N 18 (N 24 (N 31 L L L) L L) L L) (N 18 (N 19 L (N
  25 L L (N 32 L L (N 23 (N 27 L (N 26 (N 30 L (N 17 L L (N 31 (N 34 L L L) L L)) L) L L) L) (N 24
  (N 27 L L L) L L) L))) (N 23 (N 27 L (N 30 L (N 17 L L (N 31 (N 24 L (N 34 L L L) L) L L)) L) L)
  (N 24 (N 27 L (N 30 (N 17 L L (N 20 (N 31 L (N 34 L L L) L) L L)) L L) L) L L) L)) (N 19 L L (N
  24 (N 27 L (N 31 (N 34 L (N 35 L L L) L) L L) L) L L)) L)) (N 13 L (N 18 (N 19 L (N 20 (N 27 L
  (N 25 L L (N 26 (N 33 L L (N 17 L (N 34 L L L) L)) L L)) L) L (N 17 (N 23 L (N 30 L L L) L) (N
  23 (N 30 L L L) L L) L)) (N 20 (N 27 L (N 34 L (N 35 (N 17 L (N 23 (N 30 L L (N 33 L L L)) L (N
  25 L (N 24 (N 33 L L L) L L) L)) (N 26 (N 33 L L L) L L)) L L) L) L) L (N 17 (N 23 L (N 30 L L
  L) L) (N 23 (N 30 L L L) L L) L))) (N 19 L L (N 24 (N 27 L (N 31 (N 34 L (N 35 L L L) L) L L) L)
  L L)) L) (N 18 (N 19 L (N 23 (N 27 L (N 25 L L (N 26 (N 30 L (N 17 L L (N 31 (N 24 L (N 34 L L
  L) L) L L)) L) L L)) L) (N 24 (N 27 L (N 25 L L (N 26 (N 30 (N 17 L L (N 20 (N 31 L (N 33 L L L)
  L) L L)) L L) L L)) L) L L) L) (N 17 (N 23 L (N 30 L L L) L) (N 23 (N 30 L L L) L L) L)) (N 17
  (N 23 L (N 30 L L L) L) L (N 19 L (N 20 (N 23 (N 27 L (N 24 (N 25 L L (N 26 (N 30 L (N 35 L L L)
  L) L L)) L L) L) (N 24 (N 25 L L (N 27 L (N 26 (N 30 (N 34 L L L) L L) L L) L)) L L) L) L L) L))
  L))) L (N 18 (N 19 L (N 24 (N 27 L (N 25 L L (N 13 L (N 20 (N 26 (N 31 L (N 9 L L (N 32 (N 33 L
  L L) L L)) L) L L) L L) L)) L) (N 23 (N 27 L (N 25 L L (N 26 (N 13 L (N 20 (N 31 (N 9 L L (N 32
  L (N 34 L L L) L)) L L) L L) L) L L)) L) L (N 26 (N 13 (N 20 L (N 31 L (N 9 L L (N 33 (N 35 L L
  L) L L)) L) L) (N 20 (N 25 L L L) L L) L) L L)) L) (N 20 (N 27 L (N 34 L (N 35 (N 13 L (N 26 (N
  33 L L L) L L) (N 9 (N 24 L (N 23 (N 30 L L L) L L) L) (N 17 L (N 23 (N 25 L L L) L L) (N 23 (N
  25 L (N 31 L L L) L) (N 24 (N 30 L L L) L L) L)) L)) L L) L) L) (N 26 (N 33 (N 35 L (N 13 (N 24
  L (N 31 L L L) L) L (N 9 (N 24 L (N 31 L L L) L) (N 23 (N 25 L (N 27 L L L) L) (N 24 (N 27 L L
  L) L L) L) L)) L) L L) L L) L)) (N 17 (N 19 L (N 9 (N 13 (N 20 L L (N 23 L (N 24 L L L) L)) L (N
  20 (N 23 L (N 25 L L L) L) L L)) L (N 13 (N 20 L L (N 23 L (N 30 L L L) L)) L L)) (N 20 (N 27 L
  (N 24 (N 34 L (N 31 (N 35 L L L) L L) L) L L) L) L L)) L (N 20 (N 13 L (N 19 L L (N 24 (N 26 (N
  27 L (N 31 (N 9 L L (N 25 L (N 32 L (N 35 L L L) L) L)) L L) L) L L) L L)) (N 9 (N 25 L (N 32 L
  (N 19 L L (N 35 (N 23 (N 27 L (N 31 L L L) L) (N 24 (N 30 L L L) L L) L) L L)) L) L) (N 19 L L
  (N 24 (N 25 L (N 27 L (N 31 (N 32 L L L) L L) L) L) L L)) L)) L L)) L))) L (N 12 (N 14 L L (N 18
  (N 19 L (N 20 L (N 13 (N 24 L (N 31 L (N 9 L L (N 23 (N 26 L L L) L L)) L) L) L (N 9 (N 24 L (N
  31 L (N 35 (N 23 (N 25 L (N 27 L L L) L) L (N 26 (N 33 L L (N 30 (N 32 L (N 34 L L L) L) L L)) L
  L)) L L) L) L) (N 25 (N 24 L (N 23 L L (N 26 (N 31 (N 32 L L L) L L) L L)) L) L L) L)) (N 24 (N
  25 L (N 27 L L L) L) (N 23 (N 25 L (N 27 L L L) L) L (N 26 (N 9 (N 31 L (N 13 L L (N 33 (N 35 L
  L L) L L)) L) (N 25 (N 31 (N 32 L L L) L L) L L) L) L L)) L)) (N 20 L (N 26 (N 23 L (N 24 L L L)
  L) L L) L)) (N 20 L L (N 19 L (N 9 (N 13 (N 24 L (N 31 L L L) L) L (N 17 (N 23 L (N 24 (N 25 L L
  L) L L) (N 24 (N 25 L (N 27 L L L) L) (N 26 (N 27 (N 31 (N 32 L (N 34 L L L) L) L L) L L) L L)
  L)) L (N 24 (N 25 L (N 27 L L L) L) (N 26 (N 23 L L (N 27 (N 31 (N 32 L (N 34 L L L) L) L L) L
  L)) L L) L))) L (N 13 (N 17 (N 23 L (N 30 L L L) L) L (N 23 (N 25 L (N 27 L L L) L) (N 24 (N 25
  L L L) L L) L)) L L)) L)) L)) L (N 14 (N 13 L (N 18 (N 19 L (N 20 (N 27 L (N 34 L (N 17 L L (N
  25 (N 26 L L L) L L)) L) L) L (N 17 (N 27 L (N 34 L (N 35 (N 23 (N 25 L L (N 26 (N 24 L (N 30 L
  L L) L) L L)) (N 24 (N 30 L L L) L L) L) L L) L) L) (N 23 (N 27 L (N 25 L L (N 26 (N 30 (N 34 L
  L L) L L) L L)) L) L L) L)) (N 17 (N 20 L L (N 27 L (N 34 L (N 35 (N 23 (N 30 L (N 31 L L L) L)
  (N 24 (N 30 L L L) L L) L) L L) L) L)) (N 23 (N 27 L (N 30 (N 34 L (N 35 L L L) L) L L) L) L L)
  L)) (N 19 L L (N 17 (N 24 (N 27 L (N 31 (N 9 L L (N 25 L (N 32 L (N 35 L L L) L) L)) L L) L) L
  L) L L)) L) (N 18 (N 19 L (N 23 (N 27 L (N 25 L L (N 26 (N 17 (N 30 L (N 31 (N 24 L (N 34 L L L)
  L) L L) L) (N 30 (N 34 L L L) L L) L) L L)) L) (N 24 (N 27 L (N 9 L L (N 25 L L (N 17 (N 20 L L
  (N 26 (N 30 (N 31 L (N 34 L L L) L) L L) L L)) L L))) L) L L) L) (N 17 (N 27 L (N 34 L (N 35 (N
  20 L (N 23 (N 30 L L L) L L) (N 23 (N 30 L (N 31 L L L) L) (N 24 (N 30 L L L) L L) L)) L L) L)
  L) (N 23 (N 27 L (N 30 (N 34 L (N 35 L L L) L) L L) L) L L) L)) (N 17 (N 19 L (N 9 (N 20 (N 27 L
  (N 34 L L L) L) L (N 23 (N 27 L (N 24 (N 25 L L (N 26 (N 30 L (N 31 L L L) L) L L)) L L) L) (N
  24 (N 25 L L (N 27 L (N 26 (N 30 (N 34 L L L) L L) L L) L)) L L) L)) L (N 20 (N 27 L (N 34 L L
  L) L) L (N 23 (N 27 L (N 24 (N 25 L L (N 26 (N 30 L (N 35 L L L) L) L L)) L L) L) (N 24 (N 25 L
  L (N 27 L (N 26 (N 30 (N 34 L L L) L L) L L) L)) L L) L))) (N 20 (N 27 L (N 24 (N 34 L (N 31 (N
  35 L L L) L L) L) L L) L) L (N 23 (N 27 L (N 24 (N 30 L (N 31 (N 35 L L L) L L) L) L L) L) (N 24
  (N 27 L (N 30 (N 34 L (N 35 L L L) L) L L) L) L L) L))) L (N 19 L (N 20 (N 9 (N 25 L (N 32 L L
  L) L) L (N 23 (N 25 L (N 27 L L L) L) (N 24 (N 25 L L L) L L) L)) L L) L)) L)) L L))) (N 8 (N 12
  (N 14 L L (N 17 L (N 18 (N 19 L (N 20 L (N 27 (N 34 L L L) L L) (N 23 L (N 27 (N 24 L (N 30 L L
  (N 34 L (N 31 (N 32 L L L) L L) L)) L) L L) (N 24 (N 25 L (N 27 L L L) L) (N 25 (N 32 L (N 9 L L
  (N 34 (N 27 L (N 31 L L L) L) L L)) L) (N 27 (N 32 (N 9 L L (N 13 (N 31 L (N 34 L L L) L) L L))
  L L) L L) L) L))) (N 20 L (N 26 (N 24 L (N 33 (N 13 L L (N 31 L (N 35 L L L) L)) L L) L) L L)
  L)) (N 13 (N 19 L (N 20 L L (N 27 (N 24 L (N 34 (N 31 L (N 35 L L L) L) L L) L) L L)) (N 20 L (N
  26 (N 33 L L L) L L) L)) L (N 9 (N 25 L (N 32 L (N 19 L L (N 20 L (N 26 (N 24 L (N 27 (N 33 (N
  35 L L L) L L) L L) L) L L) L)) L) L) (N 19 L L (N 20 L L L)) L)) L) (N 18 (N 19 L (N 20 L (N 13
  (N 24 L (N 31 L (N 35 (N 9 L (N 23 L (N 27 (N 32 L L (N 33 L L L)) L L) (N 25 (N 26 (N 27 L (N
  34 L L L) L) L L) L L)) (N 26 (N 33 L L L) L L)) L L) L) L) L (N 9 (N 24 L (N 25 L (N 32 L L L)
  L) L) (N 25 (N 32 L L L) L L) L)) (N 9 (N 24 L (N 25 L (N 32 L L L) L) L) (N 25 (N 32 L L L) L
  L) L)) (N 20 L (N 13 (N 24 L (N 26 (N 33 L L L) L L) L) L L) L)) (N 19 L (N 9 (N 13 (N 24 L (N
  27 (N 31 L (N 34 (N 35 L L L) L L) L) L L) L) L (N 25 L (N 32 L L L) L)) L (N 13 (N 20 L (N 26
  (N 33 L L L) L L) L) L L)) (N 20 L (N 13 (N 26 (N 33 L L L) L L) L L) L)) L))) L (N 13 (N 14 L L
  (N 18 (N 24 L (N 31 L (N 35 (N 9 L (N 26 (N 33 L L L) L L) (N 19 L (N 20 L (N 26 (N 33 L L L) L
  L) (N 17 (N 23 L (N 27 L (N 25 (N 32 L L L) L L) L) L) (N 23 (N 25 L (N 27 L L L) L) (N 27 (N 34
  L L L) L L) L) L)) (N 20 L (N 26 (N 33 L L L) L L) L))) L L) L) L) (N 19 L (N 9 (N 24 L (N 27 (N
  31 L (N 34 (N 35 L L L) L L) L) L L) L) L (N 20 L (N 26 (N 24 L (N 27 (N 33 (N 31 L (N 35 L L L)
  L) L L) L L) L) L L) (N 17 (N 23 L (N 30 L (N 35 (N 24 (N 25 L (N 27 L L L) L) (N 27 (N 34 L L
  L) L L) L) L L) L) L) (N 27 (N 23 L (N 24 L (N 30 (N 34 L L L) L L) L) L) L L) L))) (N 20 L (N
  26 (N 24 L (N 27 (N 33 (N 31 L (N 35 L L L) L) L L) L L) L) L L) L)) L)) (N 26 (N 33 (N 35 L (N
  14 (N 20 L L (N 27 L (N 34 L L L) L)) L (N 18 (N 19 L (N 20 (N 27 L (N 34 L L L) L) L (N 17 (N
  23 L (N 30 L L L) L) (N 23 (N 25 L (N 27 L L L) L) (N 24 (N 27 L L L) L L) L) L)) (N 20 (N 27 L
  (N 34 L L L) L) L L)) (N 19 L L (N 20 (N 27 L (N 34 L L L) L) L L)) L)) L) L L) L L) L)) L (N 9
  (N 12 (N 14 L L (N 18 (N 24 L (N 31 L (N 35 (N 13 L (N 20 L L (N 19 L (N 25 (N 32 L L L) L L)
  L)) (N 19 L (N 20 L (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L) (N 25 (N 32 L (N 34
  L L L) L) (N 27 (N 32 L L L) L L) L)) (N 20 L (N 26 (N 33 L L L) L L) L))) L L) L) L) (N 19 L (N
  13 (N 24 L (N 27 (N 31 L (N 34 (N 35 L L L) L L) L) L L) L) L (N 20 L (N 27 (N 24 L (N 34 (N 17
  L L (N 23 L (N 30 L (N 35 L L L) L) L)) L L) L) L L) (N 24 (N 25 L (N 27 L L L) L) (N 27 (N 23 L
  (N 25 (N 32 L (N 34 (N 35 L L L) L L) L) (N 26 (N 32 (N 35 L L L) L L) L L) L) (N 17 (N 30 L (N
  34 L (N 31 (N 32 L L L) L L) L) L) (N 34 (N 30 L (N 35 L L L) L) L L) L)) L L) L))) (N 20 L (N
  26 (N 23 L (N 24 L (N 27 (N 33 (N 13 L L (N 30 L (N 35 L L L) L)) L L) L L) L) L) L L) L)) L)) L
  (N 14 (N 13 L (N 25 L (N 24 (N 18 L (N 17 (N 19 L L (N 26 (N 27 L (N 31 L (N 32 L L L) L) L) L
  L)) L L) L) L L) L) L) L L)) (N 12 (N 14 L L (N 18 (N 19 L (N 25 (N 24 L (N 32 (N 31 L (N 35 L L
  L) L) L L) L) L L) (N 20 L (N 26 (N 23 L (N 24 L (N 25 (N 27 (N 17 L (N 30 (N 33 L L L) L L) L)
  L L) L L) L) L) L L) L)) (N 19 L L (N 20 L L L)) L)) L (N 14 (N 13 L (N 26 (N 25 L (N 19 L L (N
  24 (N 27 L (N 32 (N 33 L L L) L L) L) L L)) L) L L) L) L L)) L))))) (S 22 L L (S 29 L L (N 5 L
  (N 8 (N 12 (N 14 L L (N 17 L L (N 18 (N 19 L L (N 20 L L L)) (N 19 (N 9 L (N 24 (N 31 (N 13 L L
  (N 25 L (N 32 L L L) L)) L L) L L) (N 13 (N 20 (N 26 L (N 33 L L L) L) L (N 25 L (N 32 L (N 35
  (N 23 L (N 24 (N 31 L L L) L L) (N 24 (N 26 L (N 31 L (N 27 (N 34 L L L) L L) L) L) (N 26 (N 27
  L L L) L L) L)) L L) L) L)) (N 24 (N 26 L L L) L L) L)) L (N 20 (N 23 L (N 24 (N 26 L (N 30 L L
  (N 33 (N 13 L L (N 25 L (N 27 (N 31 L (N 34 L L L) L) L L) L)) L L)) L) L L) (N 24 (N 25 L (N 26
  L (N 33 (N 13 L L (N 31 L (N 34 L L L) L)) L L) L) L) (N 26 (N 27 L L L) L L) L)) L L)) L))) L
  (N 14 (N 19 L L (N 9 L (N 13 L (N 18 (N 24 (N 31 L L L) L L) L L) (N 17 (N 23 L (N 30 L L L) L)
  L (N 20 (N 18 (N 23 (N 27 L (N 24 (N 30 L (N 31 L L L) L) L L) L) (N 24 (N 27 L (N 30 (N 31 L (N
  34 L L L) L) L L) L) L L) L) (N 24 (N 31 (N 35 L (N 23 (N 27 L (N 30 L L L) L) (N 30 (N 34 L L
  L) L L) L) L) L L) L L) L) L L))) (N 13 L (N 17 (N 18 (N 20 (N 27 L (N 24 (N 31 L (N 34 L L L)
  L) L L) L) L (N 23 L (N 30 L L L) L)) (N 24 (N 27 L (N 31 (N 34 L L L) L L) L) L L) L) L (N 20
  (N 26 (N 33 L L L) L L) L L)) (N 17 (N 23 L (N 30 L L L) L) L L)))) L (N 17 (N 19 L L (N 20 (N
  13 L (N 26 (N 27 L (N 24 (N 33 (N 34 L (N 35 L L L) L) L L) L L) L) L L) (N 23 L (N 30 L L L)
  L)) L L)) L (N 20 (N 18 (N 19 L L (N 13 L (N 26 (N 27 L (N 24 (N 31 L (N 9 L L (N 25 L (N 32 (N
  30 L L (N 33 (N 34 L L L) L L)) L L) L)) L) L L) L) L L) (N 9 (N 24 L (N 23 (N 27 L L L) L L) L)
  (N 23 (N 25 L (N 24 (N 27 L (N 30 L (N 31 L L L) L) L) L L) L) (N 24 (N 25 L (N 27 L (N 26 (N 30
  (N 32 L L L) L L) L L) L) L) L L) L) L))) (N 19 (N 9 L (N 24 (N 31 (N 13 L L (N 25 L (N 32 L L
  L) L)) L L) L L) (N 13 (N 24 (N 26 L (N 31 L (N 33 (N 34 L L L) L L) L) L) (N 26 (N 27 L L L) L
  L) L) (N 24 (N 26 (N 27 L (N 31 (N 34 L L L) L L) L) L L) L L) L)) L (N 24 (N 25 L (N 26 (N 27 L
  (N 34 (N 31 L (N 33 L L L) L) L L) L) (N 33 (N 34 L (N 27 (N 31 L L L) L L) L) L L) L) (N 9 (N
  13 L (N 31 L L L) L) (N 13 (N 31 L L L) L L) L)) (N 26 (N 27 L L L) L L) L)) L) L L)))) L (N 12
  (N 14 L L (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 18 L (N 20 (N 24 (N 25 L (N 26 L (N 13 (N 31
  L (N 9 L L (N 33 L L L)) L) L (N 9 (N 31 L (N 32 L (N 27 (N 34 L L L) L L) L) L) (N 31 (N 32 L L
  L) L L) L)) (N 9 (N 31 L (N 13 L L (N 32 L (N 23 (N 27 (N 34 L L L) L L) L L) L)) L) (N 31 (N 32
  L L L) L L) L)) L) (N 27 (N 25 L (N 26 L L (N 9 (N 23 (N 31 (N 13 L L (N 32 L (N 34 L L L) L)) L
  L) L L) L L)) L) L L) L) L (N 24 (N 25 L (N 26 L (N 13 (N 31 L (N 9 L L (N 30 (N 33 L L L) L L))
  L) L (N 33 (N 31 L (N 9 (N 30 L L (N 32 L (N 23 (N 27 (N 34 L L L) L L) L L) L)) L L) L) L L))
  (N 9 (N 13 L (N 31 L L L) L) (N 13 (N 31 L L L) L L) L)) L) (N 27 (N 25 L (N 31 (N 32 L (N 34 (N
  35 L L L) L L) L) L L) L) L L) L)) L) L L))) L (N 14 (N 13 L (N 17 (N 19 L L (N 18 (N 20 (N 27 L
  (N 24 (N 31 L (N 34 L L L) L) L L) L) L (N 23 (N 27 L (N 24 (N 30 L (N 31 L L L) L) L L) L) (N
  24 (N 27 L (N 30 (N 31 L (N 34 L L L) L) L L) L) L L) L)) (N 24 (N 27 L (N 31 (N 34 L L L) L L)
  L) L L) L)) L (N 19 (N 20 L L L) L L)) (N 17 (N 19 L L (N 18 (N 20 (N 27 L (N 24 (N 31 L (N 34 L
  L L) L) L L) L) L (N 23 (N 27 L (N 24 (N 30 L (N 31 L L L) L) L L) L) (N 24 (N 27 L (N 30 (N 31
  L (N 34 L L L) L) L L) L) L L) L)) (N 20 (N 23 (N 27 L (N 24 (N 30 L (N 31 (N 34 L L L) L L) L)
  L L) L) (N 24 (N 27 L (N 30 (N 34 L L L) L L) L) L L) L) L (N 23 (N 27 L (N 24 (N 30 L (N 31 (N
  34 L L L) L L) L) L L) L) (N 24 (N 27 L (N 30 (N 34 L L L) L L) L) L L) L)) L)) L (N 19 (N 20 L
  L L) L L))) L L))) (N 8 (N 12 (N 14 L L (N 17 L L (N 18 (N 19 L L (N 20 L L L)) (N 19 (N 9 L (N
  20 (N 23 L (N 24 (N 25 L (N 32 L L (N 26 L (N 13 (N 33 L L L) L L) L)) (N 26 L (N 13 (N 33 L L
  L) L L) L)) L L) (N 25 L (N 24 (N 26 L (N 30 L (N 31 (N 35 L L L) L L) L) L) L L) L)) L (N 25 L
  (N 32 L L L) L)) (N 20 (N 13 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L) L) L L)) L (N 20 (N
  13 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L) L) L L)) L))) L (N 13 (N 14 L L (N 17 (N 19 L
  L (N 20 L L L)) L (N 20 (N 18 L (N 19 (N 9 L (N 23 (N 26 L (N 24 (N 30 L (N 31 L L L) L) L L) L)
  (N 24 (N 26 L (N 31 L (N 30 (N 33 L L L) L L) L) L) L L) L) (N 23 (N 26 L (N 24 (N 30 L (N 31 L
  L L) L) L L) L) (N 24 (N 26 L (N 31 L (N 30 (N 33 L L L) L L) L) L) L L) L)) L (N 23 (N 26 L (N
  24 (N 30 L (N 31 L L L) L) L L) L) (N 24 (N 26 L (N 31 L (N 30 (N 33 L L L) L L) L) L) L L) L))
  L) L L))) (N 26 (N 33 (N 35 L (N 14 (N 19 L L (N 20 L L (N 9 L (N 17 (N 23 L (N 30 L L L) L) L
  L) L))) L (N 17 (N 19 L L (N 20 (N 27 L (N 34 L L L) L) L L)) L (N 20 (N 27 L (N 34 L L L) L) L
  L))) L) L L) L L) L)) L (N 9 (N 12 (N 14 L L (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 18 L (N 25
  L (N 32 L (N 35 (N 20 (N 23 (N 30 L (N 31 L L L) L) (N 24 (N 30 L (N 31 L L L) L) L L) L) L (N
  23 (N 30 L (N 31 L L L) L) (N 24 (N 30 L (N 31 L L L) L) L L) L)) L L) L) L) L) L L))) L (N 14
  (N 13 L (N 17 (N 19 L L (N 25 L (N 24 (N 18 L (N 26 (N 27 L (N 31 L (N 32 L L L) L) L) L L) L) L
  L) L)) L L) L) L L)) (N 12 (N 14 L L (N 17 (N 19 L L (N 20 L L L)) L (N 19 (N 18 L (N 20 (N 23
  (N 25 L (N 24 (N 30 L (N 31 (N 32 L L L) L L) L) L L) L) (N 24 (N 25 L (N 32 (N 30 L (N 31 L L
  L) L) L L) L) L L) L) L (N 23 (N 25 L (N 24 (N 30 L (N 31 (N 32 L L L) L L) L) L L) L) (N 24 (N
  25 L (N 32 (N 30 L (N 31 L L L) L) L L) L) L L) L)) L) L L))) L (N 14 (N 13 L (N 17 (N 19 L L (N
  26 (N 25 L (N 24 (N 27 L (N 32 (N 33 L L L) L L) L) L L) L) L L)) L L) L) L L)) L))))) (S 22 L L
  (S 29 L L L))) (S 16 (S 22 L (S 29 L (N 35 (N 5 L (N 13 (N 14 L L (N 19 L (N 20 L (N 23 (N 27 L
  (N 25 L L (N 26 L L L)) L) L (N 27 (N 34 L (N 32 L L (N 8 (N 26 (N 33 L L L) L L) L L)) L) (N 34
  (N 25 L L (N 8 (N 26 (N 33 L L L) L L) L L)) L L) L)) (N 12 (N 23 (N 25 L (N 27 L L L) L) L (N
  25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L)) (N 8 (N 9 (N 25 L (N 32 L L L) L) L (N 17
  (N 23 L L (N 30 L L (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L))) L (N 18 (N 23 (N
  25 L (N 27 L L L) L) L (N 24 L (N 25 (N 32 L (N 34 L L L) L) (N 26 (N 34 L L L) L L) L) (N 31 L
  (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L) L))) (N 27 (N 34 L L L) L L) L))) L (N
  9 (N 17 (N 18 L (N 27 (N 34 L L L) L L) (N 23 (N 25 L (N 27 L L L) L) L (N 24 L (N 25 (N 32 L (N
  34 L L L) L) (N 26 (N 32 L L L) L L) L) (N 31 L (N 25 (N 32 L (N 33 L L L) L) (N 27 (N 32 L L L)
  L L) L) L)))) L (N 18 L (N 27 (N 34 L L L) L L) L)) L (N 17 (N 23 (N 25 L (N 27 L L L) L) L (N
  25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L)) L (N 18 (N 23 (N 25 L (N 27 L L L) L) L
  (N 30 (N 32 L (N 34 L L L) L) L L)) (N 27 (N 34 L L L) L L) L)))) L)) (N 20 L (N 18 (N 9 L (N 8
  (N 12 (N 23 L L (N 30 L L (N 17 L (N 26 (N 33 L L L) L L) (N 24 L (N 26 (N 31 L L (N 32 L L L))
  L L) (N 25 (N 32 L L (N 31 L (N 33 L L L) L)) L L))))) L (N 23 (N 25 L L (N 24 L (N 26 L L L)
  L)) L (N 24 L (N 26 (N 31 L L (N 30 (N 32 L L L) L L)) L L) L))) L (N 12 (N 23 (N 25 L L L) L L)
  L L)) (N 24 L (N 31 L (N 8 (N 23 (N 25 L (N 26 L L L) L) L (N 25 (N 32 L (N 34 L L L) L) (N 26
  (N 27 (N 32 L (N 33 L L L) L) L L) L L) L)) (N 12 (N 17 (N 23 L L (N 27 L (N 25 (N 26 (N 33 L L
  L) L L) L L) L)) L (N 23 (N 25 L (N 26 L L L) L) L (N 25 (N 32 L (N 34 L L L) L) (N 26 (N 27 (N
  32 L L L) L L) L L) L))) L (N 17 (N 27 L (N 25 (N 23 L L (N 26 (N 33 L L L) L L)) L L) L) L (N
  23 (N 25 L (N 26 L L L) L) L (N 30 (N 32 L (N 33 L L L) L) L L)))) L) L) L)) (N 27 (N 34 L L L)
  L L) L) L))) (N 8 (N 12 (N 14 L L (N 23 L L (N 30 L L (N 17 L (N 18 (N 19 L (N 20 L (N 27 (N 34
  L L L) L L) (N 25 (N 32 L L L) L L)) (N 20 L (N 26 (N 33 L L L) L L) L)) L (N 19 L (N 20 L (N 27
  (N 34 L L L) L L) (N 25 (N 32 L L L) L L)) L)) (N 19 L (N 18 (N 20 L (N 26 (N 33 L L (N 32 L (N
  25 (N 27 L L L) L L) L)) L (N 33 (N 25 L (N 24 (N 27 L L L) L L) L) L L)) (N 26 (N 33 L L L) L
  L)) L (N 20 L (N 26 (N 33 L L (N 32 L (N 25 (N 27 L L L) L L) L)) L (N 33 (N 25 L (N 24 (N 27 L
  L L) L L) L) L L)) L)) (N 20 L (N 18 (N 26 (N 33 L L L) L L) L L) L)))))) L (N 14 (N 9 L (N 25 L
  L (N 32 L L (N 18 (N 19 L (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 26 (N 33 L L L) L
  L) L L)) (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 26 (N 33 L L L) L L) L L))) L (N 17
  (N 23 L L (N 24 (N 26 (N 33 L L L) L L) L L)) (N 19 L (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L
  (N 24 (N 26 (N 33 L L L) L L) L L)) (N 20 (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 26
  (N 33 L L L) L L) L L)) (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 26 (N 33 L L L) L L)
  L L)) L)) L)))) (N 19 L (N 18 (N 23 (N 27 L (N 25 L L (N 26 (N 24 L (N 31 L L L) L) L L)) L) L
  (N 26 (N 33 L L L) L L)) L (N 25 L (N 32 L L L) L)) (N 18 (N 20 (N 27 L (N 34 L (N 17 L (N 23 (N
  30 L L (N 33 L L L)) L (N 26 (N 33 L L L) L L)) (N 26 (N 33 L L L) L L)) L) L) (N 23 (N 27 L (N
  25 L L (N 26 (N 24 L (N 31 L L L) L) L L)) L) L (N 26 (N 33 L L L) L L)) L) (N 20 (N 24 (N 27 L
  L L) L L) L L) L))) L (N 26 (N 33 L L L) L L))) L (N 12 (N 14 L L (N 19 L (N 18 (N 20 L (N 23 (N
  26 L L (N 25 L (N 27 L L L) L)) L (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L)) (N
  26 (N 33 L L L) L L)) L (N 20 L (N 23 (N 26 L L (N 25 L (N 27 L L L) L)) L (N 25 (N 32 L (N 34 L
  L L) L) (N 27 (N 32 L L L) L L) L)) (N 26 (N 33 L L L) L L))) (N 20 L (N 18 (N 23 (N 26 L L L) L
  L) L L) L))) L (N 14 (N 9 (N 19 L (N 18 (N 23 (N 27 L (N 25 L L (N 30 L L L)) L) L (N 24 L (N 25
  L L L) L)) L (N 17 (N 23 (N 27 L (N 25 L L (N 30 L L L)) L) L (N 25 L (N 32 L L L) L)) (N 25 L L
  (N 23 (N 30 L L L) L L)) L)) (N 23 (N 30 L L L) L L)) (N 18 (N 19 L (N 23 (N 25 L L (N 30 L L
  L)) L (N 24 (N 25 L L L) L L)) (N 23 (N 30 L L L) L L)) L (N 17 (N 19 L (N 23 (N 25 L L (N 30 L
  L L)) L (N 24 (N 25 L L L) L L)) (N 23 (N 30 L L L) L L)) (N 19 L (N 23 (N 25 L L (N 30 L L L))
  L (N 24 (N 25 L L L) L L)) (N 23 (N 30 L L L) L L)) L)) L) L L))) L) (N 13 (N 14 L L (N 8 (N 19
  L (N 20 L (N 23 (N 27 L (N 12 L L (N 26 L L L)) L) L (N 18 (N 24 L (N 31 L (N 9 L (N 26 (N 33 L
  L (N 25 (N 32 L L L) L L)) L L) (N 26 (N 34 L (N 27 (N 17 L L (N 12 (N 30 L L L) L L)) L L) L)
  (N 27 (N 34 L L L) L L) L)) L) L) (N 27 (N 34 L L L) L L) L)) (N 12 (N 17 L (N 23 L L (N 25 (N
  32 L L L) L L)) L) (N 17 (N 23 L L (N 30 L L (N 18 (N 24 L (N 27 L (N 25 (N 32 L L L) L L) L) L)
  (N 9 (N 24 L (N 25 L (N 32 L L L) L) L) L (N 24 (N 25 L (N 27 L L L) L) (N 27 (N 34 L L L) L L)
  L)) L))) L L) L)) (N 20 L (N 18 (N 9 L (N 23 (N 26 L (N 27 L L L) L) L (N 24 L (N 26 (N 31 L (N
  33 L L L) L) L L) L)) (N 24 L (N 31 L (N 23 (N 25 L (N 26 L L L) L) L (N 25 (N 32 L (N 34 L L L)
  L) (N 26 (N 27 (N 32 L (N 33 L L L) L) L L) L L) L)) L) L)) (N 9 (N 23 (N 26 L (N 27 L L L) L) L
  (N 24 L (N 27 (N 34 L L L) L L) L)) L (N 23 (N 25 L (N 27 L L L) L) L (N 24 (N 25 L (N 27 L L L)
  L) (N 27 (N 34 L L L) L L) L))) L) L)) (N 19 L (N 27 (N 34 L L L) L L) (N 20 L (N 17 (N 18 (N 27
  L (N 26 (N 33 L L L) L L) L) (N 9 (N 23 (N 26 L (N 27 L L L) L) L (N 24 L (N 27 (N 34 L L L) L
  L) L)) L (N 23 (N 25 L (N 27 L L L) L) L (N 24 (N 25 L (N 27 L L L) L) (N 27 (N 34 L L L) L L)
  L))) L) L (N 18 (N 24 L (N 9 L L (N 31 L (N 23 (N 25 L (N 26 L L L) L) L (N 30 (N 32 L (N 33 L L
  L) L) L L)) L)) L) (N 9 (N 24 L (N 27 (N 34 L L L) L L) L) L (N 23 (N 25 L (N 27 L L L) L) L (N
  30 (N 24 L (N 34 L L L) L) L L))) L)) L)) L)) (N 14 (N 12 L (N 19 L (N 17 (N 18 (N 20 L L (N 27
  L (N 34 L (N 8 (N 23 L L (N 24 (N 31 L L L) L L)) L (N 9 (N 24 L L (N 31 L L L)) (N 23 (N 25 L L
  (N 30 L L L)) L (N 24 (N 25 L L L) L L)) L)) L) L)) L (N 23 (N 30 L L L) L L)) L (N 18 (N 20 (N
  24 (N 31 L L L) L L) L L) L L)) (N 20 (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 31 L L
  L) L L)) L (N 9 (N 8 L (N 17 (N 18 (N 24 L L (N 31 L L L)) (N 23 (N 27 L (N 30 L L (N 31 L L L))
  L) L (N 24 (N 31 L L L) L L)) L) L L) (N 23 (N 30 L L L) L L)) (N 17 (N 18 (N 27 L (N 34 L (N 23
  (N 30 L L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) L) L) (N 23 (N 27 L (N 30 L L (N 31 L L L))
  L) L (N 24 (N 31 L L L) L L)) L) (N 8 (N 18 (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N
  31 L L L) L L)) (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 31 L L L) L L)) L) L (N 23
  (N 30 L L L) L L)) L) L))) (N 19 L (N 18 (N 23 (N 27 L (N 25 L L (N 30 L L (N 8 (N 17 L (N 20 (N
  34 L L L) L L) L) L L))) L) L (N 30 (N 24 L (N 26 (N 33 L L L) L L) L) L L)) L (N 23 (N 30 L L
  L) L L)) (N 23 (N 27 L (N 30 L L (N 31 L (N 18 (N 26 (N 33 L L L) L L) L L) L)) L) L (N 30 (N 24
  L (N 26 (N 33 L L L) L L) L) L L)))) L (N 8 (N 19 L (N 18 (N 23 (N 27 L (N 25 L L (N 26 (N 24 L
  (N 33 L L L) L) L L)) L) L (N 24 (N 27 L (N 25 L L (N 26 (N 30 L L (N 12 L (N 31 L L L) L)) L
  L)) L) (N 26 (N 33 L L (N 12 (N 30 L L L) L L)) L L) L)) L (N 23 (N 30 L L L) L L)) (N 18 (N 20
  (N 27 L (N 34 L (N 12 L (N 26 (N 33 L L L) L L) (N 17 L (N 23 (N 30 L L (N 31 L (N 26 (N 33 L L
  L) L L) L)) L (N 30 (N 24 L (N 26 (N 33 L L L) L L) L) L L)) (N 23 (N 30 L L L) L L))) L) L) (N
  26 (N 33 L L L) L L) L) (N 20 (N 12 L (N 26 (N 33 L L L) L L) (N 23 (N 27 L (N 30 L L (N 31 L L
  L)) L) L (N 30 (N 17 L (N 24 L L L) L) L L))) L L) L)) (N 19 L (N 27 (N 34 L L L) L L) (N 18 (N
  20 (N 27 L (N 34 L (N 12 L (N 17 L L (N 24 (N 31 L L L) L L)) (N 17 L (N 23 (N 30 L L (N 31 L (N
  26 (N 33 L L L) L L) L)) L (N 30 (N 24 L (N 26 (N 33 L L L) L L) L) L L)) (N 23 (N 30 L L L) L
  L))) L) L) (N 26 (N 33 L L L) L L) L) (N 20 (N 12 L (N 26 (N 33 L L L) L L) (N 23 (N 27 L (N 30
  L L (N 31 L L L)) L) L (N 30 (N 24 L (N 34 L L L) L) L L))) L L) L)) L)) L)) L L) (N 5 L (N 13
  (N 14 L L (N 20 L (N 18 (N 24 L (N 31 L (N 9 L L (N 35 (N 19 L (N 23 (N 26 L (N 27 L L L) L) L
  (N 26 (N 33 L (N 34 L L L) L) (N 27 (N 33 L L L) L L) L)) (N 8 (N 23 (N 25 L (N 26 L L L) L) L
  (N 25 (N 32 L (N 34 L L L) L) (N 26 (N 27 (N 32 L (N 34 L L L) L) L L) L L) L)) (N 12 (N 17 (N
  23 L L (N 27 L (N 25 (N 26 (N 33 L L L) L L) L L) L)) L (N 23 (N 25 L (N 26 L L L) L) L (N 25 (N
  32 L (N 34 L L L) L) (N 26 (N 27 (N 32 L L L) L L) L L) L))) L (N 17 (N 27 L (N 25 (N 23 L L (N
  26 (N 33 L L L) L L)) L L) L) L (N 23 (N 25 L (N 26 L L L) L) L (N 30 (N 32 L (N 34 L L L) L) L
  L)))) L)) L L)) L) L) (N 27 (N 23 L L (N 24 L (N 31 (N 9 L L (N 33 L (N 34 L L L) L)) L L) L)) L
  L) L) L)) (N 26 (N 8 (N 12 (N 14 L L (N 20 L (N 18 (N 23 L L (N 24 L (N 31 (N 33 L L L) L L) L))
  L L) L)) L (N 14 (N 27 L (N 18 (N 9 L (N 24 (N 31 L L L) L L) (N 19 L (N 25 L L (N 20 (N 33 L (N
  34 L L L) L) (N 33 (N 34 L L L) L L) L)) (N 20 (N 33 L (N 31 (N 24 L (N 34 L L L) L) L L) L) (N
  25 L L (N 32 L (N 31 (N 34 L L L) L L) L)) L))) L L) L) L (N 18 (N 19 L (N 20 (N 27 L (N 25 L L
  (N 34 L (N 17 L L (N 33 (N 35 L L L) L L)) L)) L) (N 33 (N 35 L (N 31 (N 24 L (N 27 L L L) L) L
  L) L) L L) L) (N 20 (N 27 L (N 34 L (N 35 (N 31 L (N 33 L L L) L) L L) L) L) (N 33 (N 35 L (N 31
  (N 24 L (N 27 L L L) L) L L) L) L L) L)) (N 19 L L (N 20 (N 27 L L L) L L)) L))) L (N 12 (N 14 L
  L (N 20 L (N 18 (N 23 L L (N 19 L (N 24 L (N 25 (N 31 (N 33 L L L) L L) L L) L) L)) L L) L)) L
  (N 14 (N 27 L (N 18 (N 9 (N 24 L (N 31 L L L) L) (N 24 (N 31 L L L) L L) L) L L) L) L L))) L L)
  L) (N 13 (N 14 L L (N 20 L (N 8 (N 18 (N 24 L (N 31 L (N 35 (N 9 L (N 26 (N 33 L L L) L L) (N 19
  L (N 23 (N 26 L (N 27 L L L) L) L (N 26 (N 33 L (N 34 L L L) L) (N 27 (N 33 L L L) L L) L)) (N
  23 (N 25 L (N 26 L L L) L) L (N 25 (N 32 L (N 34 L L L) L) (N 26 (N 27 (N 32 L (N 34 L L L) L) L
  L) L L) L)))) L L) L) L) (N 9 (N 24 L (N 27 (N 23 L L (N 31 L (N 34 (N 35 L L L) L L) L)) L L)
  L) L (N 19 L (N 27 (N 23 L L (N 24 L (N 34 (N 17 L L (N 30 L (N 31 L L L) L)) L L) L)) L L) (N
  23 (N 25 L (N 27 L L L) L) L (N 24 (N 25 L (N 27 L L L) L) (N 27 (N 17 (N 34 L (N 31 (N 32 L L
  L) L L) L) L (N 12 (N 30 L (N 31 (N 32 L (N 34 L L L) L) L L) L) (N 26 (N 33 (N 30 L (N 31 L L
  L) L) L L) L L) L)) L L) L)))) L) (N 17 (N 18 (N 24 L (N 9 L L (N 27 L (N 19 L L (N 25 (N 23 L L
  (N 26 (N 31 L (N 33 (N 35 L L L) L L) L) L L)) L L)) L)) L) (N 9 (N 24 L (N 27 (N 23 L L (N 31 L
  (N 34 L L L) L)) L L) L) L (N 19 L (N 27 (N 34 L L L) L L) (N 23 (N 25 L (N 27 L L L) L) L (N 24
  (N 25 L (N 27 L L L) L) (N 27 (N 34 L (N 31 (N 32 L L L) L L) L) L L) L)))) L) L (N 18 (N 24 L
  (N 9 L L (N 31 L (N 35 (N 19 L (N 27 (N 23 L L (N 30 (N 32 L L (N 25 (N 26 L (N 33 L L L) L) L
  L)) L L)) L L) (N 23 (N 25 L (N 26 L L L) L) L (N 30 (N 32 L (N 34 L L L) L) L L))) L L) L)) L)
  (N 9 (N 24 L (N 27 (N 23 L L (N 31 L (N 30 (N 34 L L L) L L) L)) L L) L) L (N 19 L (N 27 (N 23 L
  L (N 24 L (N 34 (N 30 L (N 31 L L L) L) L L) L)) L L) (N 23 (N 25 L (N 27 L L L) L) L (N 12 (N
  24 (N 25 L (N 27 L L L) L) (N 27 (N 25 (N 26 (N 33 L (N 35 L L L) L) (N 33 (N 30 L (N 31 L L L)
  L) L L) L) (N 26 (N 32 (N 35 L L L) L L) L L) L) L L) L) (N 26 (N 24 L (N 27 (N 30 (N 33 L L L)
  L L) L L) L) L L) L)))) L)) L) L)) (N 14 (N 12 L (N 20 (N 24 (N 26 (N 33 L L L) L L) L L) L L)
  (N 18 (N 19 L (N 20 (N 27 L (N 26 (N 25 L L (N 33 L (N 34 L L L) L)) L L) L) (N 26 (N 27 L (N 25
  L L (N 33 (N 34 L L L) L L)) L) L L) L) (N 20 (N 27 L (N 34 L (N 35 (N 17 L (N 23 (N 30 L L (N
  31 L (N 26 (N 33 L L L) L L) L)) L (N 30 (N 24 L (N 26 (N 33 L L L) L L) L) L L)) (N 23 (N 30 L
  L L) L L)) L L) L) L) (N 26 (N 27 L (N 25 L L (N 33 (N 34 L (N 35 L L L) L) L L)) L) L L) L)) (N
  19 L L (N 20 (N 23 (N 27 L (N 24 (N 25 L (N 26 (N 35 L L L) L L) (N 26 (N 33 L (N 35 L L L) L)
  (N 33 (N 34 L (N 31 (N 35 L L L) L L) L) L L) L)) L L) L) L (N 8 (N 9 L (N 24 (N 27 L (N 31 (N
  34 L (N 35 L L L) L) L L) L) L L) (N 17 (N 27 L (N 24 (N 30 L (N 34 L L L) L) L L) L) (N 24 (N
  27 L (N 34 (N 30 L (N 33 L L L) L) L L) L) L L) L)) (N 17 (N 27 L (N 24 (N 34 L (N 30 (N 35 L L
  L) L L) L) L L) L) (N 24 (N 27 L (N 30 (N 34 L L L) L L) L) L L) L) L)) L L)) L)) L (N 8 (N 18
  (N 19 L (N 20 (N 27 L (N 26 (N 25 L L (N 34 L (N 17 L L (N 33 (N 35 L L L) L L)) L)) L L) L) (N
  26 (N 33 (N 35 L (N 12 (N 23 L L (N 24 L (N 31 L L L) L)) L (N 23 (N 27 L (N 17 L L (N 24 (N 31
  L L L) L L)) L) L (N 17 (N 27 L (N 34 L L L) L) (N 27 (N 34 L L L) L L) L))) L) L L) L L) L) (N
  20 (N 27 L (N 34 L (N 35 (N 12 L (N 24 (N 33 L L L) L L) (N 17 L (N 23 (N 30 L L (N 31 L (N 26
  (N 33 L L L) L L) L)) L (N 30 (N 24 L (N 26 (N 33 L L L) L L) L) L L)) (N 23 (N 30 L L L) L L)))
  L L) L) L) (N 26 (N 33 (N 35 L (N 12 (N 23 L L (N 24 L (N 31 L L L) L)) L (N 23 (N 27 L (N 24 (N
  31 L L L) L L) L) L (N 17 (N 27 L (N 34 L L L) L) (N 34 (N 24 L (N 27 L L L) L) L L) L))) L) L
  L) L L) L)) (N 19 L L (N 20 (N 12 L (N 24 (N 26 (N 27 L (N 33 (N 34 L (N 35 L L L) L) L L) L) L
  L) L L) (N 23 (N 27 L (N 24 (N 17 L (N 34 (N 31 L (N 33 L L L) L) L L) (N 30 L (N 34 (N 31 L (N
  33 L L L) L) L L) L)) L L) L) L (N 17 (N 27 L (N 24 (N 30 L (N 34 L L L) L) L L) L) (N 24 (N 27
  L (N 34 (N 30 L (N 33 L L L) L) L L) L) L L) L))) L L)) L) (N 18 (N 19 L (N 27 (N 17 L L (N 20 L
  (N 23 L L (N 12 (N 24 L (N 26 (N 33 (N 30 L (N 31 L L L) L) L L) L L) L) L L)) L)) L L) (N 20 (N
  27 L (N 34 L (N 35 (N 12 L (N 17 L L (N 24 (N 33 L L L) L L)) (N 17 L (N 23 (N 30 L L (N 31 L (N
  26 (N 33 L L L) L L) L)) L (N 30 (N 24 L (N 26 (N 33 L L L) L L) L) L L)) (N 23 (N 30 L L L) L
  L))) L L) L) L) (N 26 (N 33 (N 35 L (N 12 (N 23 L L (N 24 L (N 31 L L L) L)) L (N 17 (N 27 L (N
  34 L L L) L) L (N 23 (N 27 L (N 24 (N 31 L L L) L L) L) L L))) L) L L) L L) L)) (N 19 L L (N 20
  (N 12 L (N 24 (N 26 (N 27 L (N 33 (N 34 L (N 35 L L L) L) L L) L) L L) L L) (N 23 (N 27 L (N 24
  (N 25 L (N 26 (N 35 L L L) L L) (N 9 (N 31 L (N 32 (N 33 L L L) L L) L) (N 31 (N 32 L L L) L L)
  L)) L L) L) L (N 17 (N 27 L (N 24 (N 34 L (N 30 (N 35 L L L) L L) L) L L) L) (N 24 (N 27 L (N 30
  (N 34 L L L) L L) L) L L) L))) L L)) L) L)) L))) (S 29 L L L)) (S 22 L (S 29 L L (N 27 (N 5 L (N
  13 (N 14 L L (N 17 (N 20 L (N 23 L L (N 24 L (N 18 (N 31 L (N 34 L L L) L) (N 19 L L (N 31 (N 34
  L L L) L L)) L) L)) L) L (N 18 (N 20 L (N 23 L L (N 24 L (N 31 L (N 9 L L (N 34 (N 35 L L L) L
  L)) L) L)) L) (N 20 (N 26 L (N 23 (N 24 (N 31 L (N 35 L L L) L) (N 25 L L (N 31 (N 35 L L L) L
  L)) L) L (N 24 (N 31 L (N 9 L L (N 34 (N 35 L L L) L L)) L) (N 31 (N 35 L L L) L L) L)) L) (N 34
  (N 35 L (N 31 (N 33 L L L) L L) L) L L) L) L))) (N 20 (N 26 L L L) L L) L) (N 13 (N 14 L L (N 8
  (N 17 (N 20 L (N 23 L L (N 24 L (N 12 L (N 26 (N 33 (N 31 L (N 35 L L L) L) L L) L L) (N 30 L (N
  31 (N 33 L L L) L L) L)) L)) L) L (N 18 (N 20 L (N 23 L L (N 24 L (N 31 L (N 30 (N 34 L L L) L
  L) L) L)) L) (N 20 (N 26 L (N 23 (N 12 L (N 33 (N 31 L (N 34 L L L) L) L L) (N 30 L (N 31 (N 33
  L L L) L L) L)) L (N 12 (N 30 L (N 33 L L L) L) (N 33 (N 30 L (N 31 L L L) L) L L) L)) L) (N 34
  (N 35 L (N 31 (N 33 L L L) L L) L) L L) L) L)) (N 17 (N 20 L (N 23 L L (N 24 L (N 9 (N 18 L (N
  19 L L (N 31 L (N 34 (N 35 L L L) L L) L)) L) L (N 18 (N 31 L (N 34 L L L) L) (N 19 L L (N 34 (N
  31 L (N 35 L L L) L) L L)) L)) L)) L) L (N 18 (N 20 L (N 23 L L (N 24 L (N 9 L L (N 31 L (N 30
  (N 34 L L L) L L) L)) L)) L) (N 9 (N 24 L (N 31 L (N 34 (N 35 L L L) L L) L) L) L (N 20 (N 26 L
  (N 23 (N 24 (N 31 L (N 35 L L L) L) (N 25 L L (N 35 (N 31 L (N 34 L L L) L) L L)) L) L (N 12 (N
  33 L (N 30 (N 35 L L L) L L) L) (N 30 (N 33 L L L) L L) L)) L) (N 34 (N 35 L (N 31 (N 33 L L L)
  L L) L) L L) L)) L)) L)) (N 14 (N 12 L (N 18 (N 24 L L L) L L) (N 17 (N 23 L L (N 24 L (N 20 (N
  26 L L L) L L) L)) L (N 23 (N 18 L (N 20 (N 26 L L L) L L) L) L L))) L (N 8 (N 17 (N 23 L L (N
  24 L (N 12 L L (N 20 (N 26 L L L) L L)) L)) L (N 18 (N 23 L L (N 24 L (N 12 (N 20 L L L) L L)
  L)) (N 20 (N 26 L L L) L L) L)) (N 17 (N 23 L L (N 24 L (N 20 (N 26 L L L) L L) L)) L (N 18 (N
  23 L L (N 24 L (N 12 (N 20 L L L) L L) L)) (N 20 (N 26 L L L) L L) L)) L)) L)) L L)) (S 29 L L
  L)) (S 22 L L L))) (S 11 L (S 16 (S 22 (S 29 L L (N 27 L (N 5 L (N 8 (N 12 (N 14 L L (N 17 L (N
  18 (N 23 L L (N 25 L L (N 26 L L L))) L L) (N 18 (N 19 L (N 23 L L (N 25 L L (N 26 L L L))) (N
  20 L (N 26 L L L) L)) (N 19 L L (N 20 L L L)) L))) L (N 14 (N 13 L (N 18 (N 19 L (N 25 L L (N 9
  (N 24 L (N 31 L L L) L) L (N 20 (N 34 L (N 17 L L (N 26 (N 33 L L L) L L)) L) L (N 23 (N 17 L (N
  30 L L L) L) L L)))) (N 20 (N 34 L (N 35 (N 31 L (N 24 (N 9 L L (N 23 L L (N 26 L L L))) L L) L)
  L L) L) L (N 17 (N 23 L (N 30 L L L) L) (N 23 (N 30 L L L) L L) L))) (N 19 L L (N 24 (N 31 (N 9
  L L (N 34 L (N 35 L L L) L)) L L) L L)) L) (N 18 (N 19 L (N 25 L L (N 9 (N 24 L (N 31 L (N 30 (N
  35 L L L) L L) L) L) L (N 23 (N 30 L (N 17 L L (N 26 (N 24 L (N 31 (N 34 L L L) L L) L) L L)) L)
  L L))) (N 24 (N 31 L (N 30 (N 32 L L (N 33 (N 34 L (N 35 L L L) L) L L)) L L) L) (N 25 L L (N 23
  (N 30 L (N 17 L L (N 26 (N 31 (N 34 L L L) L L) L L)) L) L (N 26 (N 9 (N 31 L (N 30 (N 35 L L L)
  L L) L) (N 31 (N 32 L L (N 34 L (N 35 L L L) L)) L L) L) L L))) L)) (N 19 L L (N 24 (N 17 (N 30
  L (N 23 L L (N 20 (N 31 (N 35 L L L) L L) L L)) L) L (N 20 (N 9 (N 31 L (N 30 (N 34 L L L) L L)
  L) (N 25 L L (N 31 (N 32 L L (N 34 L (N 35 L L L) L)) L L)) L) L L)) L L)) L)) L (N 18 (N 19 L
  (N 25 L L (N 26 (N 9 (N 24 L (N 31 L (N 13 L L (N 30 (N 32 L L L) L L)) L) L) L (N 13 L (N 20 (N
  32 (N 31 L (N 24 (N 23 L L (N 30 L L (N 17 L (N 34 L L L) L))) L L) L) L L) L L) L)) L L)) (N 20
  (N 34 L (N 35 (N 31 L (N 33 L L L) L) L L) L) (N 25 L L (N 26 (N 13 L L (N 33 (N 34 L (N 35 L L
  L) L) L L)) L L)) L)) (N 19 L L (N 20 (N 24 (N 13 L (N 26 (N 31 (N 9 L L (N 25 L (N 32 L L L)
  L)) L L) L L) (N 9 (N 31 L (N 30 (N 32 L L L) L L) L) (N 25 L L (N 31 (N 32 L L L) L L)) L)) L
  L) L L)) L))) L (N 12 (N 14 (N 9 L (N 18 (N 19 (N 34 L (N 35 (N 31 L (N 24 (N 13 L L (N 23 L L
  (N 25 L L L))) L L) L) L L) L) L (N 17 (N 23 L (N 30 L L L) L) (N 23 (N 30 L L L) L L) L)) (N 20
  L L (N 24 (N 31 (N 13 L L (N 34 L (N 35 L L L) L)) L L) L L)) L) (N 18 (N 20 L (N 26 L L (N 13
  (N 24 L (N 31 L (N 30 (N 35 L L L) L L) L) L) L (N 23 (N 30 L (N 17 L L (N 25 (N 24 L (N 31 (N
  34 L L L) L L) L) L L)) L) L L))) (N 24 (N 31 L (N 30 (N 33 L L (N 32 (N 34 L (N 35 L L L) L) L
  L)) L L) L) (N 26 L L (N 23 (N 30 L (N 17 L L (N 25 (N 31 (N 34 L L L) L L) L L)) L) L (N 25 (N
  13 (N 31 L (N 30 (N 35 L L L) L L) L) (N 31 (N 33 L L (N 34 L (N 35 L L L) L)) L L) L) L L)))
  L)) (N 20 L L (N 24 (N 17 (N 30 L (N 23 L L (N 19 (N 31 (N 35 L L L) L L) L L)) L) L (N 19 (N 13
  (N 31 L (N 30 (N 34 L L L) L L) L) (N 26 L L (N 31 (N 33 L L (N 34 L (N 35 L L L) L)) L L)) L) L
  L)) L L)) L)) L (N 18 (N 20 L (N 26 L L (N 25 (N 9 L (N 19 (N 32 (N 34 L (N 35 L L L) L) L L) L
  L) (N 13 (N 24 L (N 31 L (N 30 (N 33 L L L) L L) L) L) L L)) L L)) (N 19 (N 34 L (N 35 (N 31 L
  (N 32 L L L) L) L L) L) (N 25 (N 9 L L (N 26 L L (N 32 (N 34 L (N 35 L L L) L) L L))) L L) L))
  (N 20 L L (N 19 (N 24 (N 9 L (N 25 (N 31 (N 13 L L (N 26 L (N 33 L L L) L)) L L) L L) (N 13 (N
  31 L (N 30 (N 33 L L L) L L) L) (N 26 L L (N 31 (N 33 L L L) L L)) L)) L L) L L)) L)) L (N 14 (N
  18 (N 24 (N 31 L (N 9 L (N 13 L L (N 30 (N 34 L (N 35 L L L) L) L L)) (N 30 (N 34 L (N 35 L L L)
  L) L L)) L) (N 23 (N 25 (N 26 L L (N 35 L (N 31 (N 34 L L L) L L) L)) L (N 17 (N 30 L (N 34 L L
  L) L) (N 30 (N 34 L (N 35 L L L) L) L L) L)) L (N 25 (N 26 L L L) L L)) L) (N 24 (N 17 (N 19 (N
  20 L L (N 34 L (N 31 (N 35 L L L) L L) L)) L (N 20 (N 34 L (N 31 (N 35 L L L) L L) L) L (N 23 (N
  30 L (N 35 L L L) L) (N 30 (N 34 L (N 35 L L L) L) L L) L))) L (N 19 (N 20 L L L) L L)) L L) L)
  L L))) (N 8 (N 12 (N 14 L L (N 17 L (N 23 L L (N 25 L L (N 26 L L L))) (N 18 (N 19 L (N 23 L L
  (N 25 L L (N 26 L L L))) (N 20 L (N 26 L L L) L)) (N 24 (N 19 L (N 20 L L (N 25 L L L)) (N 20 L
  (N 26 L L L) L)) L L) L))) L (N 13 (N 14 L L (N 18 (N 24 L (N 31 L (N 35 (N 9 L (N 19 L L (N 26
  L L L)) (N 19 L (N 25 L L (N 26 L L L)) (N 20 L (N 25 L L L) L))) L L) L) L) (N 24 (N 31 L (N 34
  (N 9 L (N 19 L L (N 20 L L L)) (N 19 L (N 20 L L (N 25 L L L)) (N 20 L (N 25 L L L) L))) L L) L)
  L L) L)) (N 33 (N 14 (N 18 (N 19 L (N 25 L L (N 32 L L (N 9 (N 24 L (N 31 L (N 30 (N 35 L L L) L
  L) L) L) L (N 26 (N 20 L L (N 23 (N 17 L (N 34 L L L) L) L L)) L L)))) (N 20 (N 26 L L (N 17 L
  (N 23 (N 25 L L (N 30 L (N 34 L L L) L)) L L) L)) L (N 9 (N 24 L (N 23 (N 17 L (N 25 L L (N 30 L
  (N 31 L L L) L)) L) L L) L) (N 25 L L (N 32 L L (N 17 (N 23 L (N 24 (N 30 L (N 31 L L L) L) L L)
  L) (N 23 (N 30 L (N 31 (N 34 L L L) L L) L) L L) L))) L))) (N 19 L L (N 24 (N 17 (N 34 L (N 31
  (N 35 L L L) L L) L) L (N 20 (N 26 L L L) L L)) L L)) L) L (N 18 (N 19 L (N 25 L L (N 20 (N 26
  (N 34 L (N 35 L L L) L) L L) L L)) (N 20 (N 26 (N 34 L (N 35 L L L) L) L L) L L)) (N 19 L L (N
  20 (N 24 (N 26 (N 34 L (N 35 L L L) L) L L) L L) L L)) L)) L L) L)) L (N 9 (N 12 (N 14 L L (N 18
  (N 24 L (N 31 L (N 35 (N 13 L (N 20 L L (N 25 L L L)) (N 19 L (N 25 L L (N 26 L L L)) (N 20 L (N
  25 L L L) L))) L L) L) L) (N 24 (N 31 L (N 34 (N 13 L (N 19 L L (N 20 L L L)) (N 19 L (N 20 L L
  (N 25 L L L)) (N 20 L (N 25 L L L) L))) L L) L) L L) L)) L (N 14 (N 13 L (N 33 (N 32 L (N 19 L L
  (N 25 L L (N 31 (N 18 L (N 24 L L L) L) L L))) L) L L) L) L L)) (N 32 (N 12 (N 14 (N 18 (N 19 (N
  25 L L (N 17 L (N 23 (N 26 L L (N 30 L (N 34 L L L) L)) L L) L)) L (N 17 (N 23 L (N 20 L L (N 24
  (N 13 L (N 26 L L (N 30 L (N 31 L L L) L)) L) L L)) L) (N 23 (N 26 L L (N 30 L (N 31 (N 34 L L
  L) L L) L)) L L) L)) (N 20 L L (N 24 (N 17 (N 34 L (N 31 (N 35 L L L) L L) L) L (N 19 (N 25 L L
  L) L L)) L L)) L) L (N 18 (N 19 (N 34 L (N 35 L L L) L) L (N 20 L (N 26 L L L) L)) (N 20 L L (N
  19 (N 24 (N 25 (N 34 L (N 35 L L L) L) L L) L L) L L)) L)) L (N 14 (N 33 L (N 13 (N 20 L L (N 26
  L L (N 31 (N 18 L (N 24 L L L) L) L L))) L L) L) L L)) L L) L))) L)) L (S 29 L L (N 5 L (N 8 (N
  12 (N 14 L L (N 17 L (N 18 (N 23 L L (N 30 L L (N 19 L (N 25 (N 24 L (N 26 (N 32 (N 9 L L (N 31
  L (N 35 L L L) L)) L L) L L) L) L L) (N 20 L (N 26 (N 24 L (N 25 (N 33 (N 13 L L (N 31 L (N 35 L
  L L) L)) L L) L L) L) L L) L)))) L L) (N 18 (N 19 L (N 9 (N 24 L (N 23 L L (N 25 (N 26 (N 31 L
  (N 13 L L (N 32 L L L)) L) L L) L L)) L) L (N 13 (N 24 L (N 23 L L (N 25 (N 26 (N 31 L (N 33 L L
  L) L) L L) L L)) L) (N 20 L L (N 25 (N 24 L (N 23 L L (N 26 (N 31 (N 32 L L L) L L) L L)) L) L
  L)) L)) (N 20 L (N 26 (N 24 L (N 23 L L (N 25 (N 33 (N 13 L L (N 31 L (N 35 L L L) L)) L L) L
  L)) L) L L) L)) (N 19 L L (N 20 L L L)) L))) L (N 14 (N 13 L (N 18 (N 19 L (N 9 (N 24 L (N 31 L
  L L) L) L (N 20 (N 27 L (N 34 L (N 17 L L (N 26 (N 33 L L L) L L)) L) L) L (N 17 (N 23 L (N 27 L
  L L) L) (N 23 (N 30 L L L) L L) L))) (N 20 (N 27 L (N 34 L (N 35 (N 17 L (N 23 (N 25 L L (N 26
  (N 24 L (N 31 L L L) L) L L)) L (N 25 (N 26 L L L) L L)) (N 26 (N 33 L L L) L L)) L L) L) L) L
  (N 17 (N 23 L (N 30 L L L) L) (N 23 (N 30 L L L) L L) L))) (N 19 L L (N 24 (N 27 L (N 31 (N 9 L
  L (N 34 L (N 35 L L L) L)) L L) L) L L)) L) (N 18 (N 19 L (N 9 (N 24 L (N 23 (N 25 L L (N 26 (N
  27 L (N 30 L (N 31 L L L) L) L) L L)) L L) L) L (N 23 (N 25 L L (N 27 L (N 26 (N 30 L (N 17 L L
  (N 31 (N 34 L L L) L L)) L) L L) L)) (N 24 (N 27 L L L) L L) L)) (N 23 (N 27 L (N 30 L (N 17 L L
  (N 31 (N 9 L (N 24 L (N 34 L L L) L) L) L L)) L) L) (N 24 (N 27 L (N 30 (N 17 L L (N 9 L (N 20
  (N 25 L L (N 31 L (N 34 L L L) L)) L L) L)) L L) L) L L) L)) (N 19 L L (N 17 (N 23 L (N 30 L L
  L) L) L (N 20 (N 9 (N 23 (N 27 L (N 24 (N 30 L (N 31 L L L) L) L L) L) (N 24 (N 27 L (N 30 (N 31
  L (N 34 L L L) L) L L) L) L L) L) (N 24 (N 25 L L (N 27 L (N 31 (N 32 L L (N 34 L (N 35 L L L)
  L)) L L) L)) L L) L) L L))) L)) L (N 18 (N 19 L (N 9 (N 24 L (N 31 L (N 13 L L (N 23 (N 25 L L
  L) L L)) L) L) L (N 13 (N 24 L (N 26 (N 23 L L (N 20 L (N 25 (N 31 L (N 33 (N 35 L L L) L L) L)
  L L) L)) L L) L) (N 26 (N 33 (N 35 L (N 20 (N 27 L (N 34 L L L) L) L (N 25 (N 23 L (N 24 L L L)
  L) L L)) L) L L) L L) L)) (N 20 (N 27 L (N 34 L (N 35 (N 13 L (N 26 (N 33 L L L) L L) (N 9 (N 24
  L (N 23 (N 25 L L L) L L) L) (N 25 (N 32 L L L) L L) L)) L L) L) L) (N 26 (N 33 (N 35 L (N 13 (N
  24 L (N 31 L L L) L) L (N 9 (N 24 L (N 31 L L L) L) (N 25 (N 23 L (N 24 L L L) L) L L) L)) L) L
  L) L L) L)) (N 19 L L (N 20 (N 13 L (N 24 (N 26 (N 27 L (N 31 (N 9 L L (N 25 L (N 32 L L L) L))
  L L) L) L L) L L) (N 9 (N 17 (N 23 L (N 30 L L L) L) L (N 23 (N 25 L (N 24 (N 27 L (N 30 L (N 31
  L L L) L) L) L L) L) (N 24 (N 25 L (N 27 L (N 26 (N 30 (N 32 L L L) L L) L L) L) L) L L) L)) (N
  24 (N 25 L L L) L L) L)) L L)) L))) L (N 12 (N 14 (N 9 L (N 18 (N 19 (N 27 L (N 34 L (N 35 (N 17
  L (N 20 L L (N 23 (N 26 L L (N 25 (N 24 L (N 31 L L L) L) L L)) L (N 25 (N 26 L L L) L L))) (N
  25 (N 32 L L L) L L)) L L) L) L) L (N 17 (N 23 L (N 30 L L L) L) (N 23 (N 30 L L L) L L) L)) (N
  20 L L (N 24 (N 27 L (N 31 (N 13 L L (N 34 L (N 35 L L L) L)) L L) L) L L)) L) (N 18 (N 20 L (N
  13 (N 24 L (N 23 (N 26 L L (N 25 (N 27 L (N 30 L (N 31 L L L) L) L) L L)) L L) L) L (N 23 (N 26
  L L (N 27 L (N 25 (N 30 L (N 17 L L (N 31 (N 34 L L L) L L)) L) L L) L)) (N 24 (N 27 L L L) L L)
  L)) (N 23 (N 27 L (N 30 L (N 17 L L (N 31 (N 13 L (N 24 L (N 34 L L L) L) L) L L)) L) L) (N 24
  (N 27 L (N 30 (N 17 L L (N 13 L (N 19 (N 26 L L (N 31 L (N 34 L L L) L)) L L) L)) L L) L) L L)
  L)) (N 20 L L (N 17 (N 23 L (N 30 L L L) L) L (N 19 (N 13 (N 23 (N 27 L (N 24 (N 30 L (N 31 L L
  L) L) L L) L) (N 24 (N 27 L (N 30 (N 31 L (N 34 L L L) L) L L) L) L L) L) (N 24 (N 26 L L (N 27
  L (N 31 (N 33 L L (N 34 L (N 35 L L L) L)) L L) L)) L L) L) L L))) L)) L (N 18 (N 20 L (N 13 (N
  24 L (N 31 L (N 9 L L (N 23 (N 26 L L L) L L)) L) L) L (N 9 (N 24 L (N 25 (N 23 L L (N 19 L (N
  26 (N 31 L (N 32 (N 35 L L L) L L) L) L L) L)) L L) L) (N 25 (N 32 (N 35 L (N 19 (N 27 L (N 34 L
  L L) L) L (N 26 (N 23 L (N 24 L L L) L) L L)) L) L L) L L) L)) (N 19 (N 27 L (N 34 L (N 35 (N 9
  L (N 25 (N 32 L L L) L L) (N 13 (N 24 L (N 23 (N 26 L L L) L L) L) (N 26 (N 33 L L L) L L) L)) L
  L) L) L) (N 25 (N 32 (N 35 L (N 9 (N 24 L (N 31 L L L) L) L (N 13 (N 24 L (N 31 L L L) L) (N 26
  (N 23 L (N 24 L L L) L) L L) L)) L) L L) L L) L)) (N 20 L L (N 19 (N 9 L (N 24 (N 25 (N 27 L (N
  31 (N 13 L L (N 26 L (N 33 L L L) L)) L L) L) L L) L L) (N 13 (N 17 (N 23 L (N 30 L L L) L) L (N
  23 (N 26 L (N 24 (N 27 L (N 30 L (N 31 L L L) L) L) L L) L) (N 24 (N 26 L (N 27 L (N 25 (N 30 (N
  33 L L L) L L) L L) L) L) L L) L)) (N 24 (N 26 L L L) L L) L)) L L)) L)) L (N 14 (N 18 (N 24 (N
  27 L (N 31 L (N 9 L (N 13 L L (N 30 (N 34 L (N 35 L L L) L) L L)) (N 30 (N 34 L (N 35 L L L) L)
  L L)) L) L) (N 23 (N 27 L (N 25 (N 26 L L (N 9 L (N 31 (N 13 L L (N 34 L (N 35 L L L) L)) L L)
  (N 17 (N 30 L (N 34 L L L) L) (N 30 (N 34 L (N 35 L L L) L) L L) L))) L (N 26 (N 13 L (N 31 (N 9
  L L (N 34 L (N 35 L L L) L)) L L) (N 17 (N 30 L (N 34 L L L) L) (N 30 (N 34 L (N 35 L L L) L) L
  L) L)) L L)) L) L (N 25 (N 26 L L L) L L)) L) (N 17 (N 19 (N 20 L L (N 27 L (N 24 (N 34 L (N 31
  (N 35 L L L) L L) L) L L) L)) L (N 20 (N 27 L (N 24 (N 34 L (N 31 (N 35 L L L) L L) L) L L) L) L
  (N 23 (N 27 L (N 24 (N 30 L (N 31 (N 35 L L L) L L) L) L L) L) (N 24 (N 27 L (N 30 (N 34 L (N 35
  L L L) L) L L) L) L L) L))) L (N 19 (N 20 L L L) L L)) L) L L))) (N 8 (N 12 (N 14 L L (N 17 L (N
  18 (N 19 L (N 9 (N 24 L (N 31 L (N 35 (N 13 L (N 20 L L (N 23 L L (N 25 (N 32 L L L) L L))) (N
  25 (N 32 L L L) L L)) L L) L) L) L (N 13 (N 24 L (N 31 L (N 35 (N 20 L (N 26 (N 33 L L L) L L)
  (N 25 (N 32 L L L) L L)) L L) L) L) (N 20 L L (N 25 (N 24 L (N 23 L L (N 26 (N 32 (N 31 L (N 35
  L L L) L) L L) L L)) L) L L)) L)) (N 20 L (N 26 (N 24 L (N 33 (N 13 L L (N 31 L (N 35 L L L) L))
  L L) L) L L) L)) (N 9 (N 13 (N 24 L (N 27 (N 31 L (N 34 (N 35 L L L) L L) L) L L) L) L (N 19 L
  (N 20 L L (N 25 (N 32 L L L) L L)) (N 20 L (N 26 (N 24 L (N 27 (N 33 (N 31 L (N 35 L L L) L) L
  L) L L) L) L L) L))) L (N 13 (N 19 L (N 20 L L (N 25 (N 24 L (N 27 (N 32 (N 31 L (N 35 L L L) L)
  L L) L L) L) L L)) (N 20 L (N 26 (N 33 L L L) L L) L)) L L)) L) (N 18 (N 19 L (N 9 (N 24 L (N 31
  L (N 35 (N 13 L (N 20 L L (N 23 L L (N 30 L L L))) (N 25 (N 32 L L L) L L)) L L) L) L) L (N 20 L
  (N 13 (N 24 L (N 26 (N 33 L L L) L L) L) L L) L)) (N 20 L (N 13 (N 24 L (N 26 (N 33 L L L) L L)
  L) L L) L)) (N 19 L (N 9 (N 13 (N 24 L (N 27 (N 31 L (N 34 (N 35 L L L) L L) L) L L) L) L (N 25
  (N 32 L L L) L L)) L (N 13 (N 20 L (N 26 (N 33 L L L) L L) L) L L)) (N 20 L (N 13 (N 26 (N 33 L
  L L) L L) L L) L)) L))) L (N 13 (N 14 L L (N 18 (N 24 L (N 31 L (N 35 (N 9 L (N 19 L L (N 20 L
  (N 26 (N 33 L L L) L L) L)) (N 19 L (N 20 L (N 26 (N 33 L L L) L L) (N 25 (N 32 L L L) L L)) (N
  20 L (N 26 (N 33 L L L) L L) L))) L L) L) L) (N 19 L (N 9 (N 24 L (N 27 (N 31 L (N 34 (N 35 L L
  L) L L) L) L L) L) L (N 20 L (N 26 (N 24 L (N 27 (N 33 (N 31 L (N 35 L L L) L) L L) L L) L) L L)
  (N 25 (N 23 L (N 24 L (N 27 (N 32 (N 30 L (N 35 L L L) L) L L) L L) L) L) L L))) (N 20 L (N 26
  (N 24 L (N 27 (N 33 (N 31 L (N 35 L L L) L) L L) L L) L) L L) L)) L)) (N 26 (N 33 (N 35 L (N 14
  (N 20 L L (N 17 (N 23 L (N 30 L L L) L) (N 18 (N 19 L (N 25 L L (N 32 L L (N 9 (N 24 L (N 31 L L
  L) L) L (N 23 (N 27 L (N 30 L (N 31 (N 34 L L L) L L) L) L) (N 24 (N 27 L L L) L L) L)))) (N 9
  (N 24 L (N 31 L L L) L) (N 25 L L (N 32 L L (N 23 (N 27 L (N 30 L (N 31 (N 34 L L L) L L) L) L)
  (N 24 (N 27 L L L) L L) L))) L)) L L) L)) L (N 18 (N 19 L (N 9 (N 24 L (N 31 L L L) L) L (N 20
  (N 27 L (N 34 L L L) L) L (N 25 (N 23 L (N 24 L L L) L) L L))) (N 20 (N 27 L (N 34 L L L) L) L
  L)) (N 19 L L (N 20 (N 27 L (N 34 L L L) L) L L)) L)) L) L L) L L) L)) L (N 9 (N 12 (N 14 L L (N
  18 (N 24 L (N 31 L (N 35 (N 13 L (N 20 L L (N 19 L (N 25 (N 32 L L L) L L) L)) (N 19 L (N 25 (N
  32 L L L) L L) (N 20 L (N 26 (N 33 L L L) L L) L))) L L) L) L) (N 19 L (N 25 (N 24 L (N 27 (N 32
  (N 31 L (N 35 L L L) L) L L) L L) L) L L) (N 20 L (N 26 (N 23 L (N 24 L (N 27 (N 33 (N 13 L L (N
  30 L (N 35 L L L) L)) L L) L L) L) L) L L) L)) L)) L (N 14 (N 13 L (N 26 (N 25 L (N 19 L L (N 24
  (N 18 L (N 17 (N 27 L (N 31 L (N 30 (N 32 L L L) L L) L) L) L L) L) L L)) L) L L) L) L L)) (N 25
  (N 32 (N 35 L (N 12 (N 14 (N 19 L L (N 17 (N 23 L (N 30 L L L) L) (N 18 (N 20 L (N 26 L L (N 33
  L L (N 13 (N 24 L (N 31 L L L) L) L (N 23 (N 27 L (N 30 L (N 31 (N 34 L L L) L L) L) L) (N 24 (N
  27 L L L) L L) L)))) (N 13 (N 24 L (N 31 L L L) L) (N 26 L L (N 33 L L (N 23 (N 27 L (N 30 L (N
  31 (N 34 L L L) L L) L) L) (N 24 (N 27 L L L) L L) L))) L)) L L) L)) L (N 18 (N 19 (N 27 L (N 34
  L L L) L) L (N 20 L (N 26 (N 23 L (N 24 L L L) L) L L) L)) (N 20 L L (N 19 (N 27 L (N 34 L L L)
  L) L L)) L)) L (N 14 (N 19 L L (N 26 L (N 33 L L L) L)) L L)) L) L L) L L) L))))) L (S 22 L L (S
  29 L L L))) (S 16 (S 22 (S 29 L (N 27 L (N 5 L (N 8 (N 12 (N 14 L L (N 30 L L (N 13 (N 17 L (N
  23 L L (N 25 L L (N 20 L (N 26 L L L) L))) (N 19 L (N 23 L L (N 25 L L (N 26 L L L))) (N 20 L (N
  26 L L L) L))) (N 17 L (N 23 L L (N 25 L L (N 26 L L L))) (N 19 L (N 23 L L (N 25 L L (N 26 L L
  L))) (N 20 L (N 26 L L L) L))) L))) L (N 13 (N 14 L L (N 20 L (N 26 L L L) L)) (N 14 (N 19 L (N
  25 L L (N 35 (N 30 L L (N 26 (N 33 L L L) L L)) L L)) (N 25 L (N 34 (N 30 L L (N 20 (N 33 L L L)
  L L)) L L) (N 30 (N 32 L L (N 34 L (N 35 L L L) L)) L (N 33 (N 32 L L (N 9 (N 20 (N 26 L (N 34 L
  (N 35 L L L) L) L) (N 26 (N 34 L (N 35 L L L) L) L L) L) (N 31 (N 34 L (N 35 L L L) L) L L) L))
  L L)))) L (N 33 (N 19 L (N 25 L L (N 26 (N 35 L L L) L L)) (N 18 (N 20 (N 34 L (N 35 L L L) L)
  (N 25 L L (N 26 (N 32 (N 23 L L (N 30 L L (N 31 L (N 35 L L L) L))) L L) L L)) L) (N 20 (N 34 L
  L L) L L) L)) L L)) L)) L (N 12 (N 13 (N 14 (N 33 L L (N 9 L (N 19 (N 20 L (N 26 L L (N 18 (N 34
  L (N 17 L L (N 25 (N 32 L L L) L L)) L) L (N 25 (N 32 L L (N 30 (N 17 L (N 23 L L L) L) L L)) L
  (N 30 (N 17 L (N 23 L L L) L) L L)))) (N 26 L (N 24 (N 18 L (N 31 L L (N 30 (N 34 L L L) L L))
  (N 17 (N 30 L L (N 25 (N 32 L L L) L L)) (N 35 (N 23 L L (N 25 L L L)) L L) L)) L (N 25 (N 32 L
  L (N 30 (N 17 L (N 23 L L L) L) L L)) L (N 30 (N 17 L (N 23 L L L) L) L L))) L)) L (N 30 (N 17 L
  (N 23 L L L) L) L L)) (N 32 (N 20 L (N 26 L L (N 25 (N 34 L (N 35 L L L) L) L L)) (N 26 L (N 19
  (N 34 L (N 35 L L L) L) L L) L)) L L))) L (N 20 L (N 26 L L (N 25 (N 32 (N 33 (N 30 L L (N 34 L
  (N 35 L L L) L)) L L) L L) L L)) (N 26 L (N 19 (N 32 (N 33 (N 30 L L (N 34 L (N 35 L L L) L)) L
  L) L L) L L) L))) (N 14 (N 9 L (N 18 (N 19 (N 34 L (N 35 (N 30 L L (N 32 L L L)) L L) L) L (N 30
  (N 17 L (N 23 L L L) L) L L)) L (N 19 (N 20 L (N 26 L L (N 23 (N 30 L L (N 25 (N 32 L L L) L L))
  L (N 24 (N 25 (N 32 L L L) L L) L L))) (N 17 (N 30 L L (N 25 (N 32 L L L) L L)) (N 26 L L (N 33
  (N 30 L L (N 32 L L L)) L L)) L)) L (N 20 L (N 23 (N 30 L L L) L L) L))) (N 20 L (N 26 L L (N 25
  (N 18 (N 23 (N 30 L L (N 32 (N 19 L (N 34 L L L) L) L L)) L (N 32 (N 19 L (N 34 L L L) L) L L))
  L (N 32 (N 19 L (N 34 L L L) L) L L)) L L)) (N 19 (N 26 L (N 17 (N 30 L L (N 32 (N 25 L (N 34 L
  L L) L) L L)) L (N 32 (N 25 L (N 34 L L L) L) L L)) (N 33 (N 30 L L (N 32 L L L)) L L)) (N 26 L
  L (N 25 (N 33 (N 30 L L (N 32 L L L)) L L) L L)) L))) L (N 20 L (N 26 L L (N 25 (N 32 (N 33 (N
  23 L L (N 30 L L (N 34 L (N 35 L L L) L))) L L) L L) L L)) (N 26 L (N 19 (N 32 (N 33 (N 17 L L
  (N 30 L L (N 34 L (N 35 L L L) L))) L L) L L) L L) L))) L) L (N 14 (N 9 (N 13 L (N 19 L (N 25 L
  L (N 23 (N 30 (N 35 L L L) L L) L L)) (N 30 (N 32 L L (N 25 L (N 34 L L L) L)) L L)) L) (N 13 (N
  19 (N 20 L (N 26 L L (N 30 (N 33 L L L) L L)) (N 26 L (N 30 (N 33 L L L) L L) L)) L (N 30 (N 33
  L L (N 20 L (N 26 L L L) L)) L L)) (N 18 (N 19 (N 34 L (N 35 (N 30 L L (N 31 L L L)) L L) L) L
  (N 30 (N 34 L (N 35 L L L) L) L L)) L (N 17 (N 19 (N 34 L (N 35 (N 30 L L (N 31 L L L)) L L) L)
  L (N 30 (N 23 L (N 34 L L L) L) L L)) (N 35 (N 30 L L (N 31 L L L)) L L) L)) L) L) L L))) (N 8
  (N 12 (N 14 L L (N 30 L L (N 33 (N 31 L (N 13 (N 17 L (N 18 (N 23 L L (N 24 L (N 25 L L (N 20 L
  (N 26 L L L) L)) L)) L L) (N 20 L (N 23 L (N 19 L L (N 26 L L L)) L) L)) (N 17 L (N 18 (N 23 L L
  (N 25 L L (N 20 L (N 26 L L L) L))) L L) (N 20 L (N 18 (N 23 L (N 19 L L (N 26 L L L)) L) L L)
  L)) L) L) L L))) L (N 13 (N 14 L L (N 20 L (N 26 L L L) L)) (N 14 (N 19 L (N 25 L L (N 35 (N 30
  L L (N 18 (N 23 (N 26 L L L) L L) L L)) L L)) (N 25 L (N 34 (N 30 L L (N 17 (N 20 L L L) L L)) L
  L) (N 30 (N 32 L L (N 34 L (N 35 L L L) L)) L (N 33 (N 32 L L (N 9 (N 17 (N 23 L (N 34 L L L) L)
  (N 23 (N 35 L L L) L L) L) (N 17 (N 23 L (N 34 L L L) L) (N 18 (N 23 (N 35 L L L) L L) L L) L)
  L)) L L)))) L (N 33 (N 19 L (N 25 L L (N 26 (N 35 L L L) L L)) (N 18 (N 20 (N 34 L (N 35 L L L)
  L) (N 25 L L (N 26 (N 32 (N 30 L L (N 23 L (N 34 L L L) L)) L L) L L)) L) (N 20 (N 34 L (N 35 L
  L L) L) L L) L)) L L)) L)) L (N 14 (N 9 (N 12 L L (N 13 L (N 30 (N 32 L L (N 34 L (N 35 L L L)
  L)) L L) L)) (N 12 (N 13 (N 33 L L (N 30 (N 34 L (N 35 L L L) L) L L)) (N 19 (N 20 L (N 26 L L
  (N 18 (N 34 L (N 17 L L (N 23 (N 30 L L L) L L)) L) L (N 30 (N 17 L (N 23 L L L) L) L L))) (N 17
  (N 30 L L (N 18 L (N 34 L L L) L)) (N 35 (N 30 L L (N 32 L L L)) L L) L)) L (N 30 (N 17 L (N 23
  L L L) L) L L)) L) L (N 30 (N 34 L (N 35 L L L) L) L L)) L) L L))) L) (N 27 L (N 5 L (N 8 (N 12
  (N 14 L L (N 20 L (N 26 L L L) L)) L (N 13 (N 14 L L (N 20 L (N 26 L L L) L)) (N 14 (N 18 (N 19
  L (N 25 L L (N 26 (N 9 (N 24 L (N 31 L L L) L) L (N 20 (N 33 L (N 34 L L L) L) (N 33 (N 34 L L
  L) L L) L)) L L)) (N 20 (N 34 L (N 35 (N 31 L (N 33 L L L) L) L L) L) (N 25 L L (N 26 (N 33 (N
  34 L (N 35 L L L) L) L L) L L)) L)) (N 19 L L (N 20 (N 24 (N 31 (N 9 L L (N 34 L (N 35 L L L)
  L)) L L) L L) L L)) L) L (N 18 (N 19 L (N 25 L L (N 26 (N 9 (N 24 L (N 31 L L L) L) L (N 32 (N
  31 L (N 24 (N 23 L L (N 30 L L (N 33 (N 34 L (N 35 L L L) L) L L))) L L) L) L L)) L L)) (N 20 (N
  34 L (N 35 (N 31 L (N 33 L L L) L) L L) L) (N 25 L L (N 26 (N 33 (N 34 L (N 35 L L L) L) L L) L
  L)) L)) (N 19 L L (N 20 (N 24 (N 31 (N 9 L L (N 25 L (N 32 L L L) L)) L L) L L) L L)) L)) L)) L
  (N 12 (N 20 L (N 26 L L L) L) L (N 14 (N 9 (N 13 L (N 18 (N 24 L (N 31 L L L) L) (N 19 L L (N 17
  (N 20 (N 24 (N 31 L L L) L L) L L) L L)) L) L) (N 32 (N 33 L (N 31 (N 34 L (N 35 L L L) L) L L)
  L) L L) L) L L))) (N 8 (N 12 (N 14 L L (N 20 L (N 26 L L L) L)) L (N 13 (N 14 L L (N 20 L (N 26
  L L L) L)) (N 14 (N 18 (N 19 L (N 25 L L (N 26 (N 9 (N 24 L (N 31 L (N 32 L L (N 33 (N 35 L L L)
  L L)) L) L) L (N 20 (N 33 L (N 34 L L L) L) (N 33 (N 34 L L L) L L) L)) L L)) (N 20 (N 34 L (N
  35 (N 31 L (N 33 L L L) L) L L) L) (N 25 L L (N 26 (N 33 (N 34 L (N 35 L L L) L) L L) L L)) L))
  (N 19 L L (N 20 (N 24 (N 25 L (N 9 (N 31 L (N 32 L L (N 33 (N 34 L L L) L L)) L) L (N 17 (N 34 L
  (N 31 (N 35 L L L) L L) L) L (N 23 (N 26 L (N 35 L L L) L) (N 26 (N 35 L L L) L L) L))) (N 26 (N
  33 L (N 35 L L L) L) (N 33 (N 34 L (N 35 L L L) L) L L) L)) L L) L L)) L) L (N 18 (N 19 L (N 25
  L L (N 26 (N 9 (N 24 L (N 31 L (N 33 (N 35 L L L) L L) L) L) L (N 32 (N 31 L (N 33 (N 23 L L (N
  30 L (N 34 L L L) L)) L L) L) L L)) L L)) (N 20 (N 34 L (N 35 (N 31 L (N 33 L L L) L) L L) L) (N
  25 L L (N 26 (N 33 (N 34 L (N 35 L L L) L) L L) L L)) L)) (N 19 L L (N 20 (N 24 (N 25 L (N 9 (N
  31 L (N 33 (N 34 L L L) L L) L) L (N 32 (N 31 L (N 33 (N 34 L L L) L L) L) L L)) (N 9 (N 31 L (N
  32 (N 33 (N 34 L L L) L L) L L) L) (N 31 (N 32 L L L) L L) L)) L L) L L)) L)) L)) L (N 14 (N 9
  (N 12 L L (N 13 L (N 17 (N 18 (N 20 L (N 24 L (N 25 L L (N 26 (N 31 L (N 32 (N 33 L L L) L L) L)
  L L)) L) L) (N 19 L L (N 20 (N 24 (N 31 L (N 34 L L L) L) L L) L L)) L) (N 23 (N 25 L L (N 18 (N
  24 L (N 26 (N 31 L (N 35 L L L) L) L L) L) (N 19 L L (N 20 (N 24 (N 26 L (N 31 L (N 32 (N 33 L L
  L) L L) L) L) L L) L L)) L)) L L) L) L)) (N 32 (N 33 L (N 31 (N 34 L (N 35 L L L) L) L L) L) L
  L) L) L L))) L)) (S 29 L L (N 26 (N 5 L (N 8 (N 12 (N 14 L L (N 20 L (N 23 L L (N 24 L (N 13 (N
  33 L (N 34 (N 31 L (N 17 L L (N 18 (N 27 L L L) L L)) L) L L) L) (N 18 (N 31 (N 33 L L L) L L) L
  L) L) L)) L)) L (N 13 (N 14 L L (N 20 L (N 23 L L (N 24 L (N 18 (N 31 L (N 9 L L (N 35 (N 33 L
  (N 34 L L L) L) L L)) L) (N 19 L L (N 27 (N 31 (N 9 L L (N 25 (N 32 L (N 34 L L L) L) L L)) L L)
  L L)) L) L)) L)) (N 14 (N 25 L L (N 18 (N 19 L (N 9 (N 24 L (N 31 L L L) L) L (N 20 (N 27 L (N
  33 L (N 34 L L L) L) L) (N 33 (N 32 L L (N 35 L (N 31 (N 34 L L L) L L) L)) L L) L)) (N 20 (N 27
  L (N 33 L (N 31 (N 24 L (N 34 L L L) L) L L) L) L) (N 33 (N 35 L (N 31 (N 24 L (N 27 L L L) L) L
  L) L) L L) L)) (N 19 L L (N 20 (N 27 L L L) L L)) L)) L (N 18 (N 19 L (N 9 (N 24 L (N 31 L L L)
  L) L (N 20 (N 27 L (N 34 L (N 17 L L (N 33 (N 35 L L L) L L)) L) L) (N 33 (N 35 L (N 31 (N 34 L
  L L) L L) L) L L) L)) (N 20 (N 27 L (N 34 L (N 35 (N 31 L (N 33 L L L) L) L L) L) L) (N 33 (N 35
  L (N 31 (N 24 L (N 27 L L L) L) L L) L) L L) L)) (N 19 L L (N 20 (N 27 L L L) L L)) L)) L)) L (N
  12 (N 20 L (N 23 L L (N 24 L (N 25 (N 14 L L (N 13 (N 33 L (N 34 (N 30 L (N 31 L L L) L) L L) L)
  (N 18 (N 31 (N 33 L L L) L L) L L) L)) L L) L)) L) L (N 14 (N 25 L L (N 23 (N 13 L (N 27 L (N 18
  (N 9 (N 24 L (N 31 L L L) L) (N 24 (N 31 L L L) L L) L) L L) L) L) L L)) L L))) (N 8 (N 12 (N 14
  L L (N 20 L (N 23 L L (N 24 L (N 13 (N 33 L (N 34 (N 31 L (N 27 (N 35 L L L) L L) L) L L) L) (N
  18 (N 33 (N 31 L (N 35 L L L) L) L L) L L) L) L)) L)) L (N 13 (N 14 L L (N 20 L (N 23 L L (N 24
  L (N 17 (N 30 L (N 31 (N 18 L (N 9 L L (N 19 L L (N 25 (N 27 (N 32 L (N 34 L L L) L) L L) L L)))
  L) L L) L) (N 18 (N 31 L (N 30 (N 32 L L (N 33 L (N 34 L L L) L)) L L) L) L L) L) L)) L)) (N 14
  (N 25 L L (N 18 (N 19 L (N 9 (N 24 L (N 27 L (N 31 L (N 32 L L (N 30 (N 35 L L L) L L)) L) L) L)
  L (N 20 (N 27 L (N 33 L (N 34 L L L) L) L) (N 33 (N 32 L L (N 35 L (N 34 (N 24 L (N 27 L L L) L)
  L L) L)) L L) L)) (N 20 (N 27 L (N 33 L (N 31 (N 24 L (N 34 L L L) L) L L) L) L) (N 33 (N 35 L
  (N 23 (N 27 L (N 24 (N 31 L L L) L L) L) L (N 17 (N 27 L (N 34 L L L) L) (N 34 (N 24 L (N 27 L L
  L) L) L L) L)) L) L L) L)) (N 19 L L (N 20 (N 27 L (N 24 (N 33 L (N 31 (N 35 L L L) L L) L) L L)
  L) L L)) L)) L (N 18 (N 19 L (N 9 (N 24 L (N 31 L (N 33 (N 35 L L L) L L) L) L) L (N 20 (N 27 L
  (N 34 L (N 17 L L (N 23 (N 30 L L L) L L)) L) L) (N 33 (N 35 L (N 34 (N 24 L (N 27 L L L) L) L
  L) L) L L) L)) (N 20 (N 27 L (N 34 L (N 35 (N 31 L (N 33 L L L) L) L L) L) L) (N 33 (N 35 L (N
  23 (N 25 L L (N 27 L (N 24 (N 31 L L L) L L) L)) L (N 17 (N 27 L (N 34 L L L) L) (N 34 (N 24 L
  (N 27 L L L) L) L L) L)) L) L L) L)) (N 19 L L (N 20 (N 27 L (N 24 (N 25 L L (N 9 (N 31 L (N 32
  (N 33 L L L) L L) L) L L)) L L) L) L L)) L)) L)) L (N 14 (N 25 L L (N 23 (N 12 L L (N 13 L (N 27
  L (N 9 (N 17 (N 30 L (N 34 (N 18 L (N 20 L L L) L) L L) L) (N 18 (N 24 L (N 31 L (N 30 (N 32 L L
  L) L L) L) L) (N 19 L L (N 20 (N 24 (N 31 L (N 33 L L L) L) L L) L L)) L) L) (N 18 (N 32 (N 30 L
  (N 31 (N 34 L L L) L L) L) L L) L L) L) L) L)) L L)) L L))) L L)) (S 29 L L L)) (S 22 L L (S 29
  L L L)) (S 22 L L L))) (S 11 L L (S 16 (S 22 (S 29 L (N 14 (N 27 L (N 5 L (N 9 (N 13 L (N 12 L L
  (N 8 (N 19 L (N 25 L L (N 18 (N 23 (N 30 L L (N 26 (N 31 L (N 32 L L L) L) L L)) (N 24 L L (N 26
  (N 34 (N 17 L L (N 20 L L L)) L L) L L)) L) L (N 17 (N 23 L (N 30 L L (N 20 (N 34 L L L) L L))
  L) (N 23 (N 30 L L (N 32 L L L)) L L) L))) (N 17 (N 30 L L (N 32 L (N 31 (N 33 (N 34 L (N 35 L L
  L) L) L L) L L) L)) (N 35 (N 30 L L (N 26 (N 33 L L L) L L)) L L) L)) L (N 19 L (N 25 L L (N 30
  (N 32 L (N 34 L L L) L) L L)) (N 25 L (N 30 (N 32 L (N 35 L L L) L) L L) L)))) L) (N 8 (N 12 L L
  (N 13 L (N 18 (N 19 L (N 25 L L (N 23 (N 30 L L (N 26 (N 24 L L (N 31 (N 32 L L L) L L)) L L)) L
  L)) (N 17 (N 30 L L (N 20 L (N 23 L L (N 25 L L L)) L)) (N 25 L L (N 23 (N 30 L L (N 26 (N 35 L
  L L) L L)) L L)) L)) L (N 17 (N 30 L L (N 31 (N 32 L L L) L L)) (N 25 L L (N 23 (N 30 L L (N 26
  (N 35 L L L) L L)) L L)) L)) L)) L (N 12 (N 13 (N 20 L (N 26 L L (N 18 (N 23 (N 30 L L (N 25 (N
  31 L (N 33 L L L) L) L L)) (N 24 L L (N 25 (N 34 (N 17 L L (N 19 L L L)) L L) L L)) L) L (N 17
  (N 23 L (N 30 L L (N 19 (N 34 L L L) L L)) L) (N 23 (N 30 L L (N 33 L L L)) L L) L))) (N 17 (N
  30 L L (N 32 (N 33 L (N 31 (N 34 L (N 35 L L L) L) L L) L) L L)) (N 35 (N 30 L L (N 25 (N 32 L L
  L) L L)) L L) L)) (N 18 (N 20 L (N 26 L L (N 23 (N 30 L L (N 25 (N 24 L L (N 31 (N 33 L L L) L
  L)) L L)) L L)) (N 17 (N 30 L L (N 19 L (N 23 L L (N 26 L L L)) L)) (N 26 L L (N 23 (N 30 L L (N
  25 (N 35 L L L) L L)) L L)) L)) L (N 17 (N 30 L L (N 31 (N 33 L L L) L L)) (N 26 L L (N 23 (N 30
  L L (N 25 (N 35 L L L) L L)) L L)) L)) L) L (N 13 (N 20 L (N 26 L L (N 30 (N 33 L (N 34 L L L)
  L) L L)) (N 26 L (N 30 (N 33 L (N 35 L L L) L) L L) L)) (N 18 (N 24 (N 31 L L (N 30 (N 34 L (N
  35 L L L) L) L L)) L (N 23 (N 30 (N 34 L (N 35 L L L) L) L (N 31 (N 32 (N 33 L L L) L L) L L))
  (N 34 (N 17 L L (N 19 L L L)) L L) L)) L (N 17 (N 24 (N 30 (N 34 L (N 35 L L L) L) L (N 31 (N 32
  (N 33 L L L) L L) L L)) L (N 31 (N 34 L (N 35 L L L) L) L L)) (N 35 (N 30 L L (N 31 L L L)) L L)
  L)) L))) L) (N 9 (N 13 L (N 12 L (N 19 L (N 25 L L (N 17 (N 18 (N 20 L L (N 31 L L (N 24 L (N 30
  (N 23 L (N 34 L L L) L) L L) L))) L (N 30 (N 23 L (N 34 L L L) L) L L)) L (N 18 (N 31 L L L) L
  L))) (N 17 (N 20 (N 34 L (N 35 (N 30 L L (N 31 L L L)) L L) L) L (N 18 (N 31 L L (N 24 L (N 25 L
  L (N 30 (N 8 L (N 23 L L L) L) L L)) L)) (N 23 (N 30 L L (N 8 L (N 24 (N 31 L L L) L L) L)) L (N
  24 (N 31 L L L) L L)) L)) (N 35 (N 30 L L (N 31 L L L)) L L) L)) (N 19 L (N 25 L L (N 18 (N 23
  (N 24 L (N 26 (N 35 L (N 31 L L (N 17 (N 30 L L L) L L)) L) L (N 30 (N 17 L (N 34 L L L) L) L
  L)) (N 26 (N 30 (N 17 L (N 34 L L L) L) L L) L L)) (N 34 (N 17 L L (N 30 L L L)) L L) L) L (N 30
  (N 34 L (N 35 L L L) L) L L))) (N 17 (N 25 L (N 20 (N 34 L (N 35 (N 30 L L (N 18 L (N 31 L L L)
  L)) L L) L) L (N 30 (N 23 L (N 34 L L L) L) L L)) (N 8 (N 23 L (N 30 L L (N 32 L (N 31 (N 34 L L
  L) L L) L)) L) (N 23 (N 30 L L (N 18 (N 20 L (N 24 L (N 26 (N 31 L (N 35 L L L) L) L L) L) L) (N
  20 (N 24 (N 26 L (N 31 L (N 34 L L L) L) L) L L) L L) L)) (N 34 (N 30 L L (N 18 L (N 20 L L L)
  L)) L L) L) L)) (N 35 (N 30 L L (N 23 (N 24 L (N 26 L L L) L) L L)) L L) L))) L) (N 13 (N 8 L (N
  19 (N 20 L (N 26 L L (N 17 (N 18 L L (N 30 (N 23 L (N 34 L L L) L) L L)) L (N 18 (N 31 L L L) L
  L))) (N 17 (N 34 L (N 35 (N 30 L L (N 31 L L L)) L L) L) (N 35 (N 30 L L (N 31 L L L)) L L) L))
  L (N 17 (N 20 L (N 26 L L (N 18 (N 31 L L (N 24 L (N 30 (N 23 L (N 34 L L L) L) L L) L)) L (N 30
  (N 23 L (N 34 L L L) L) L L))) (N 18 (N 31 L L (N 24 L (N 26 L L (N 30 (N 12 L (N 23 L L L) L) L
  L)) L)) (N 23 (N 30 L L (N 12 L (N 24 (N 31 L L L) L L) L)) L (N 24 (N 31 L L L) L L)) L)) (N 20
  L L (N 35 (N 30 L L (N 31 L L L)) L L)) L)) (N 20 L (N 26 L L (N 18 (N 23 (N 24 L (N 25 (N 35 L
  (N 31 L L (N 17 (N 30 L L L) L L)) L) L (N 30 (N 17 L (N 34 L L L) L) L L)) (N 25 (N 30 (N 17 L
  (N 34 L L L) L) L L) L L)) (N 34 (N 17 L L (N 30 L L L)) L L) L) L (N 30 (N 34 L (N 35 L L L) L)
  L L))) (N 17 (N 26 L (N 19 (N 34 L (N 35 (N 30 L L (N 18 L (N 31 L L L) L)) L L) L) L (N 30 (N
  23 L (N 34 L L L) L) L L)) (N 12 (N 23 L (N 30 L L (N 33 L (N 31 (N 34 L L L) L L) L)) L) (N 23
  (N 30 L L (N 18 (N 19 L (N 24 L (N 25 (N 31 L (N 35 L L L) L) L L) L) L) (N 19 (N 24 (N 25 L (N
  31 L (N 34 L L L) L) L) L L) L L) L)) (N 34 (N 30 L L (N 18 L (N 19 L L L) L)) L L) L) L)) (N 35
  (N 30 L L (N 23 (N 24 L (N 25 L L L) L) L L)) L L) L))) (N 30 (N 34 L (N 35 L L L) L) L (N 18 (N
  24 (N 31 L (N 32 (N 33 L L L) L L) L) (N 31 (N 34 L (N 35 L L L) L) L L) L) (N 24 (N 31 (N 34 L
  (N 35 L L L) L) L L) L L) L)) L) L)) L) L L) L) (S 29 L (N 14 (N 35 (N 5 L (N 9 (N 13 L (N 12 L
  L (N 8 (N 19 L (N 18 (N 23 (N 27 L (N 25 L L (N 30 L L (N 32 L L L))) L) L (N 24 L (N 25 L L L)
  L)) L (N 17 (N 23 L L (N 25 L (N 24 (N 27 L L L) L L) L)) (N 25 L L (N 23 (N 27 L (N 30 L L (N
  32 L L L)) L) L L)) L)) (N 17 (N 23 L L (N 25 L (N 24 (N 33 L L L) L L) L)) (N 18 (N 23 (N 27 L
  (N 30 L L (N 33 L L L)) L) L (N 24 L (N 25 L L L) L)) L (N 20 (N 23 (N 27 L (N 30 L L (N 33 L L
  L)) L) L (N 25 L (N 24 (N 33 L L L) L L) L)) (N 23 (N 27 L (N 25 L L (N 30 L L (N 33 L L L))) L)
  L (N 25 L (N 24 (N 27 L L L) L L) L)) L)) L)) L (N 19 L (N 18 (N 23 (N 27 L (N 25 L L (N 30 L L
  L)) L) L (N 24 L (N 25 (N 26 L L L) L L) L)) L (N 17 (N 23 (N 27 L (N 25 L L (N 30 L L L)) L) L
  (N 26 (N 33 L L L) L L)) (N 23 (N 25 L L (N 30 L L L)) L (N 25 (N 26 L L L) L L)) L)) (N 23 (N
  30 L L L) L L)))) L) (N 8 (N 12 L L (N 13 L (N 18 (N 19 L (N 23 (N 25 L L (N 27 L (N 30 L L (N
  31 L L L)) L)) L (N 24 (N 25 L L L) L L)) (N 17 (N 23 L L (N 20 L (N 24 (N 25 L L L) L L) L)) (N
  23 (N 25 L L (N 27 L (N 30 L L (N 31 L L L)) L)) L (N 24 (N 25 L L L) L L)) L)) L (N 17 (N 23 L
  L (N 24 (N 25 L L L) L L)) (N 19 L (N 23 (N 25 L L (N 27 L (N 30 L L (N 31 L L L)) L)) L (N 24
  (N 25 L L L) L L)) (N 20 (N 23 (N 25 L L (N 27 L (N 30 L L (N 31 L L L)) L)) L (N 24 (N 25 L L
  L) L L)) (N 23 (N 25 L L (N 27 L (N 30 L L (N 31 L L L)) L)) L (N 24 (N 25 L L L) L L)) L)) L))
  L)) L (N 12 (N 13 (N 20 L (N 18 (N 23 (N 27 L (N 26 L L (N 30 L L (N 32 L L L))) L) L (N 24 L (N
  26 L L L) L)) L (N 17 (N 23 L L (N 25 (N 32 L L L) L L)) (N 26 L L (N 23 (N 27 L (N 30 L L (N 32
  L L L)) L) L L)) L)) (N 17 (N 23 L L (N 25 (N 32 L L L) L L)) (N 18 (N 23 (N 27 L (N 30 L L (N
  32 L L L)) L) L (N 24 L (N 26 L L L) L)) L (N 19 (N 23 (N 27 L (N 30 L L (N 32 L L L)) L) L (N
  25 (N 32 L L L) L L)) (N 23 (N 27 L (N 26 L L (N 30 L L (N 32 L L L))) L) L (N 25 (N 32 L L L) L
  L)) L)) L)) (N 18 (N 20 L (N 23 (N 26 L L (N 27 L (N 30 L L (N 31 L L L)) L)) L (N 24 (N 26 L L
  L) L L)) (N 17 (N 23 L L (N 19 L (N 24 (N 26 L L L) L L) L)) (N 23 (N 26 L L (N 27 L (N 30 L L
  (N 31 L L L)) L)) L (N 24 (N 26 L L L) L L)) L)) L (N 17 (N 23 L L (N 24 (N 26 L L L) L L)) (N
  20 L (N 23 (N 26 L L (N 27 L (N 30 L L (N 31 L L L)) L)) L (N 24 (N 26 L L L) L L)) (N 19 (N 23
  (N 26 L L (N 27 L (N 30 L L (N 31 L L L)) L)) L (N 24 (N 26 L L L) L L)) (N 23 (N 26 L L (N 27 L
  (N 30 L L (N 31 L L L)) L)) L (N 24 (N 26 L L L) L L)) L)) L)) L) L (N 13 (N 20 L (N 18 (N 23 (N
  27 L (N 26 L L (N 30 L L L)) L) L (N 24 L (N 25 (N 26 L L L) L L) L)) L (N 17 (N 23 (N 27 L (N
  26 L L (N 30 L L L)) L) L (N 25 (N 32 L L L) L L)) (N 23 (N 26 L L (N 30 L L L)) L (N 25 (N 26 L
  L L) L L)) L)) (N 23 (N 30 L L L) L L)) (N 18 (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24
  (N 30 L L L) L L)) L (N 17 (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 30 L L L) L L))
  (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 30 L L L) L L)) L)) L))) L) (N 9 (N 13 L (N
  12 L (N 19 L (N 17 (N 18 (N 20 L L (N 24 L L (N 31 L L L))) L (N 23 (N 30 L L L) L L)) L (N 18
  (N 24 L L L) L L)) (N 17 (N 20 (N 27 L (N 34 L (N 18 L (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N
  31 L L L) L L)) (N 23 (N 30 L L L) L L)) L) L) L (N 18 (N 24 L L (N 31 L L L)) (N 23 (N 27 L (N
  30 L L (N 31 L L L)) L) L (N 24 (N 31 L L L) L L)) L)) (N 8 (N 20 (N 23 (N 27 L (N 30 L L (N 31
  L L L)) L) L (N 24 (N 31 L L L) L L)) L (N 18 (N 24 L L (N 31 L L L)) (N 23 (N 27 L (N 30 L L (N
  31 L L L)) L) L (N 24 (N 31 L L L) L L)) L)) L (N 23 (N 30 L L L) L L)) L)) (N 19 L (N 18 (N 23
  (N 27 L (N 25 L L (N 30 L L (N 8 (N 32 L L L) L L))) L) L (N 24 L (N 25 (N 26 L L L) L L) L)) L
  (N 23 (N 30 L L L) L L)) (N 17 (N 23 (N 27 L (N 30 L L (N 8 L (N 31 L (N 18 (N 20 L (N 24 L (N
  25 L L (N 26 (N 33 L L L) L L)) L) L) L L) L) L)) L) L (N 30 (N 8 L (N 24 L (N 25 (N 26 L L L) L
  L) L) L) L L)) (N 23 (N 27 L (N 30 L L (N 31 L (N 18 (N 24 L (N 25 L L (N 26 (N 33 L L L) L L))
  L) L L) L)) L) L (N 30 (N 24 L (N 18 (N 25 (N 26 L L L) L L) L L) L) L L)) L))) L) (N 13 (N 8 L
  (N 19 (N 20 L (N 17 (N 18 L L (N 23 (N 30 L L L) L L)) L (N 18 (N 24 L L L) L L)) (N 17 (N 27 L
  (N 34 L (N 18 L (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 31 L L L) L L)) (N 23 (N 30 L L L) L
  L)) L) L) (N 12 (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 31 L L L) L L)) L (N 23 (N
  30 L L L) L L)) L)) L (N 17 (N 20 L (N 18 (N 24 L L (N 31 L L L)) L (N 23 (N 30 L L L) L L)) (N
  18 (N 24 L L (N 31 L L L)) (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 31 L L L) L L))
  L)) (N 20 L L (N 12 (N 18 (N 24 L L (N 31 L L L)) (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N
  24 (N 31 L L L) L L)) L) L (N 23 (N 30 L L L) L L))) L)) (N 20 L (N 18 (N 23 (N 27 L (N 26 L L
  (N 30 L L (N 12 (N 33 L L L) L L))) L) L (N 24 L (N 25 (N 26 L L L) L L) L)) L (N 23 (N 30 L L
  L) L L)) (N 17 (N 23 (N 27 L (N 30 L L (N 12 L (N 31 L (N 18 (N 19 L (N 24 L (N 25 (N 32 L L L)
  L L) L) L) L L) L) L)) L) L (N 30 (N 12 L (N 24 L (N 25 (N 26 L L L) L L) L) L) L L)) (N 23 (N
  27 L (N 30 L L (N 31 L (N 18 (N 24 L (N 25 (N 32 L L L) L L) L) L L) L)) L) L (N 30 (N 24 L (N
  18 (N 25 (N 26 L L L) L L) L L) L) L L)) L))) (N 23 (N 27 L (N 30 L L (N 31 L (N 18 (N 24 (N 25
  L L (N 8 (N 33 L L L) L L)) L L) L L) L)) L) L (N 18 (N 24 (N 27 L (N 30 L L (N 31 L (N 8 (N 12
  L L L) L L) L)) L) (N 25 (N 26 L L L) L L) L) (N 24 (N 31 L L L) L L) L)) L) L)) L L) L L) L) L)
  (S 22 L (S 29 L L L) L) L)))) (S 4 L L (S 7 (S 11 (S 16 L (S 22 L (S 29 L (N 5 L (N 14 L L (N 27
  (N 34 (N 35 L L L) L L) L L)) L) (N 5 L (N 14 L L (N 27 (N 17 (N 23 L (N 24 L L L) L) (N 18 (N
  24 L L L) L L) L) L L)) L)) (S 29 L L L)) (S 22 L L L)) (S 16 (S 22 L (S 29 L (N 5 L (N 35 (N 14
  (N 12 L (N 13 L L (N 9 (N 25 L L (N 32 L L (N 8 L (N 17 (N 19 L (N 20 (N 27 L (N 34 L (N 18 L L
  (N 24 (N 31 L L L) L L)) L) L) L (N 24 (N 31 L L L) L L)) (N 20 (N 27 L (N 34 L (N 18 L (N 23 (N
  30 L L (N 31 L L L)) L (N 24 (N 26 (N 30 L L (N 31 L L L)) L L) L L)) (N 24 (N 31 L L L) L L))
  L) L) L (N 24 (N 31 L L L) L L))) L (N 20 (N 19 L (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N
  24 (N 30 L L L) L L)) (N 18 (N 24 L L (N 31 L L L)) (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L
  (N 24 (N 30 L L L) L L)) L)) L L)) (N 19 L (N 17 (N 24 (N 31 L L L) L L) L L) L)))) L (N 24 (N
  31 L L L) L L))) (N 13 L (N 8 (N 25 L L (N 32 L L (N 9 L (N 18 (N 19 L (N 20 (N 27 L (N 34 L (N
  17 L L (N 23 (N 30 L L L) L L)) L) L) L (N 23 (N 30 L L L) L L)) (N 20 (N 27 L (N 34 L (N 17 L
  (N 23 (N 30 L L (N 31 L L L)) L (N 24 (N 30 L L L) L L)) (N 23 (N 30 L L L) L L)) L) L) L (N 23
  (N 30 L L L) L L))) L (N 20 (N 19 L (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 30 L L
  L) L L)) (N 17 (N 23 L L (N 30 L L L)) (N 23 (N 27 L (N 30 L L (N 31 L L L)) L) L (N 24 (N 30 L
  L L) L L)) L)) L L)) (N 19 L (N 18 (N 23 (N 30 L L L) L L) L L) L)))) L (N 23 (N 30 L L L) L L))
  (N 19 L (N 25 (N 26 L L (N 23 L (N 24 L L L) L)) L (N 26 (N 27 L (N 33 L L (N 17 (N 18 (N 20 L
  (N 34 L L L) L) (N 20 (N 34 L L L) L L) L) (N 18 (N 20 (N 34 L L L) L L) L L) L)) L) L (N 33 (N
  32 L L (N 34 L (N 17 (N 18 (N 20 L (N 27 L L L) L) (N 20 (N 27 L L L) L L) L) (N 18 (N 20 (N 27
  L L L) L L) L L) L) L)) L L))) (N 25 (N 26 L L (N 23 L (N 24 L L L) L)) L (N 26 (N 27 L (N 33 L
  L (N 17 (N 18 (N 20 L (N 34 L (N 23 (N 24 L (N 30 L L L) L) (N 24 (N 31 L L L) L L) L) L) L) (N
  24 (N 31 L L L) L L) L) (N 18 (N 23 (N 30 L L L) L L) L L) L)) L) L (N 33 (N 32 L L (N 34 L (N 8
  (N 9 L (N 23 L (N 17 (N 24 (N 31 L L L) L L) L L) L) L) (N 9 (N 24 L (N 18 (N 23 (N 30 L L L) L
  L) L L) L) L L) L) L)) L L)))))) L (N 19 L (N 25 (N 32 L L (N 26 (N 33 L L L) L L)) L (N 26 (N
  33 L L L) L L)) (N 26 (N 33 L L L) L L))) L L) L) (N 5 L (N 14 (N 12 L (N 13 L L (N 24 (N 25 L L
  (N 27 L (N 17 (N 9 (N 18 L (N 31 L (N 30 (N 34 L L L) L L) L) L) L (N 18 (N 20 L L (N 31 L (N 30
  (N 23 L (N 34 L L L) L) L L) L)) (N 19 L (N 34 (N 20 L L (N 30 L (N 31 L L L) L)) L L) (N 8 (N
  23 L (N 30 L L L) L) (N 23 (N 30 L L L) L L) L)) L)) L L) L)) L L)) (N 13 L (N 23 (N 25 L L (N
  27 L (N 18 (N 8 (N 17 L (N 30 L (N 31 (N 34 L L L) L L) L) L) L (N 17 (N 20 L L (N 30 L (N 31 (N
  24 L (N 34 L L L) L) L L) L)) (N 19 L (N 34 (N 20 L L (N 30 L (N 31 L L L) L)) L L) (N 9 (N 24 L
  (N 31 L L L) L) (N 24 (N 31 L L L) L L) L)) L)) L L) L)) L L) (N 17 (N 18 (N 27 L (N 34 L (N 35
  (N 19 L (N 20 L L (N 26 (N 33 L L L) L L)) (N 20 L (N 23 (N 25 L L (N 30 L (N 31 L L L) L)) (N
  24 (N 31 L L L) L L) L) (N 26 (N 33 L L L) L L))) L L) L) L) (N 19 L (N 9 (N 25 L L (N 8 L (N 32
  L L (N 23 (N 27 L (N 24 (N 30 L (N 31 L L L) L) L L) L) (N 24 (N 27 L (N 30 (N 34 L L L) L L) L)
  L L) L)) (N 23 (N 27 L (N 24 (N 30 L (N 31 L L L) L) L L) L) (N 24 (N 27 L (N 31 L (N 30 (N 34 L
  L L) L L) L) L) L L) L))) L (N 23 (N 25 L L (N 27 L (N 24 (N 30 L (N 31 (N 34 L L L) L L) L) L
  L) L)) (N 24 (N 25 L L (N 27 L (N 34 (N 20 L L (N 26 (N 30 L (N 31 L L L) L) L L)) L L) L)) L L)
  L)) (N 23 (N 25 L L (N 27 L (N 24 (N 30 L (N 31 (N 35 L L L) L L) L) L L) L)) (N 24 (N 25 L L (N
  27 L (N 35 (N 30 L (N 31 L L L) L) L L) L)) L L) L)) L) (N 18 (N 19 L (N 8 (N 25 L L (N 9 L (N
  32 L L (N 23 (N 27 L (N 30 L (N 31 (N 34 L L L) L L) L) L) (N 24 (N 27 L L L) L L) L)) (N 23 (N
  27 L (N 30 L (N 31 (N 34 L L L) L L) L) L) (N 24 (N 27 L L L) L L) L))) L (N 23 (N 25 L L (N 27
  L (N 34 (N 20 L L (N 26 (N 30 L (N 31 L L L) L) L L)) L L) L)) (N 24 (N 27 L L L) L L) L)) (N 23
  (N 25 L L (N 27 L (N 24 (N 31 L (N 30 (N 35 L L L) L L) L) (N 35 (N 30 L (N 31 L L L) L) L L) L)
  L)) (N 24 (N 27 L L L) L L) L)) L L) L))) L (N 17 (N 18 (N 27 L (N 34 L (N 35 (N 19 L (N 20 L L
  (N 25 (N 32 L L L) L L)) (N 20 L (N 26 (N 33 L L L) L L) L)) L L) L) L) (N 19 L (N 9 (N 13 (N 24
  L (N 31 L L L) L) L (N 8 (N 23 L (N 24 (N 25 L L (N 26 (N 27 L (N 20 (N 34 L L L) L L) L) L L))
  L L) L) (N 32 (N 25 L L (N 26 (N 30 L (N 31 L L L) L) L L)) L L) L)) L (N 13 (N 12 (N 23 L (N 24
  (N 25 L L (N 26 L L L)) L L) L) (N 20 L L (N 24 (N 25 L L L) L L)) L) L L)) (N 26 (N 20 (N 25 L
  L (N 27 L (N 13 L L (N 24 (N 34 L (N 31 (N 35 L L L) L L) L) L L)) L)) (N 24 (N 12 L L (N 9 (N
  13 L L (N 25 L L (N 27 L (N 31 L (N 30 (N 34 L L L) L L) L) L))) L L)) L L) L) L L)) L) (N 18 (N
  19 L (N 8 (N 12 (N 23 L (N 30 L L L) L) L (N 9 (N 24 L (N 23 (N 25 L L (N 26 (N 27 L (N 20 (N 34
  L L L) L L) L) L L)) L L) L) (N 32 (N 25 L L (N 26 (N 30 L (N 31 L L L) L) L L)) L L) L)) L (N
  12 (N 13 (N 24 L (N 23 (N 25 L L (N 26 L L L)) L L) L) (N 20 L L (N 23 (N 25 L L L) L L)) L) L
  L)) (N 26 (N 20 (N 25 L L (N 27 L (N 12 L L (N 23 (N 34 L (N 30 (N 35 L L L) L L) L) L L)) L))
  (N 23 (N 12 L L (N 8 (N 13 L L (N 25 L L (N 27 L (N 30 L (N 31 (N 34 L L L) L L) L) L))) L L)) L
  L) L) L L)) L L) L)) L)) (S 29 L L L)) (S 22 L (S 29 L L (N 5 L (N 27 (N 14 (N 12 L (N 13 L L (N
  18 (N 24 L L L) L L)) (N 13 L (N 17 (N 23 L L L) L L) (N 17 (N 19 L L (N 23 L (N 24 L L L) L))
  (N 18 (N 24 L L L) L L) L))) L (N 17 (N 19 L L (N 20 (N 26 L L L) L L)) (N 18 (N 24 L L L) L L)
  L)) L L) L)) (S 29 L L L)) (S 22 L L L)) (S 16 (S 22 L (S 29 L (N 5 L (N 35 (N 12 (N 14 L L (N
  13 (N 19 L (N 20 L (N 27 (N 34 L (N 32 L L (N 26 (N 33 L L L) L L)) L) (N 34 (N 25 L L (N 26 (N
  33 L L L) L L)) L L) L) (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L)) (N 20 L (N 17
  (N 8 L (N 9 (N 18 L (N 23 L (N 24 L L (N 25 (N 26 (N 27 L (N 33 L L L) L) L L) L L)) (N 24 L (N
  27 (N 34 L L L) L L) (N 25 (N 33 L (N 34 L L L) L) (N 27 (N 30 L L (N 32 L L L)) L L) L))) L) L
  (N 18 (N 24 L (N 23 L L (N 27 L (N 25 (N 26 (N 33 L L L) L L) L L) L)) L) (N 23 L (N 24 (N 25 L
  L L) L L) (N 24 (N 25 L (N 27 L L L) L) (N 27 (N 34 L L L) L L) L)) L)) (N 23 L (N 30 L (N 9 (N
  18 L (N 24 L L (N 26 (N 33 L L L) L L)) L) (N 18 (N 24 L L (N 27 L (N 25 (N 26 (N 33 L L L) L L)
  L L) L)) L L) L) L) L)) (N 18 (N 8 (N 9 L (N 23 L (N 24 L L (N 27 (N 34 L L L) L L)) (N 24 L (N
  25 (N 26 (N 27 L (N 33 L L L) L) L L) L L) (N 25 (N 33 L (N 34 L L L) L) (N 27 (N 31 L L (N 32 L
  L L)) L L) L))) (N 24 L (N 23 L L (N 26 (N 30 L L (N 31 L (N 33 L L L) L)) L L)) L)) L (N 9 L (N
  23 (N 25 L (N 27 L L L) L) (N 24 L L (N 27 (N 34 L L L) L L)) L) L)) L L) L) L)) (N 8 (N 17 L (N
  18 (N 19 L (N 20 L (N 27 (N 34 L L L) L L) (N 23 L (N 27 (N 34 L L L) L L) (N 25 (N 32 L (N 34 L
  L L) L) (N 27 (N 32 L L L) L L) L))) (N 20 L (N 26 (N 33 L L L) L L) L)) L (N 19 L (N 20 L (N 27
  (N 34 L L L) L L) (N 23 L (N 27 (N 34 L L L) L L) (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L
  L) L L) L))) L)) (N 19 L (N 18 (N 20 L (N 23 L (N 27 (N 24 L L (N 34 L (N 25 (N 26 L L (N 32 L L
  L)) L L) L)) L L) (N 30 L (N 34 (N 25 L (N 27 L L L) L) L L) L)) (N 23 L (N 24 (N 25 L (N 26 L L
  L) L) L (N 25 (N 32 L (N 34 L L L) L) (N 26 (N 32 L L L) L L) L)) (N 30 L (N 24 (N 25 L (N 27 L
  L L) L) L (N 25 (N 32 L (N 33 L L L) L) (N 27 (N 32 L L L) L L) L)) L))) L (N 20 L (N 23 L (N 27
  (N 24 L L (N 31 (N 33 L L (N 26 (N 25 L (N 32 L L L) L) L L)) L L)) L L) (N 30 L (N 34 (N 25 L
  (N 27 L L L) L) L L) L)) L)) L)) L (N 19 L (N 18 (N 20 L (N 26 (N 33 L L (N 23 L (N 24 L L (N 27
  (N 25 L (N 32 L L L) L) L L)) (N 17 (N 27 L (N 34 L L L) L) (N 27 (N 34 L L L) L L) L))) L (N 33
  (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L) L L)) (N 25 (N 32 L (N 34 L L L) L) (N
  27 (N 32 L L L) L L) L)) L (N 20 L (N 26 (N 33 L L (N 23 L (N 24 L L (N 27 (N 25 L (N 32 L L L)
  L) L L)) (N 17 (N 30 L (N 34 L L L) L) (N 27 (N 34 L L L) L L) L))) L (N 33 (N 25 (N 32 L (N 34
  L L L) L) (N 27 (N 32 L L L) L L) L) L L)) (N 17 (N 23 L (N 24 (N 25 L (N 26 L L L) L) L (N 31
  (N 32 L (N 34 L L L) L) L L)) (N 30 L (N 24 (N 25 L (N 27 L L L) L) L (N 31 (N 32 L (N 33 L L L)
  L) L L)) L)) (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L) L))) (N 20 L (N 18 (N 26
  (N 33 L L L) L L) L L) L))) L)) (N 13 (N 14 L L (N 9 (N 18 L (N 17 (N 19 L (N 20 L (N 27 (N 34 L
  L L) L L) (N 24 L (N 27 (N 34 L L L) L L) (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L)
  L))) (N 20 L (N 26 (N 33 L L L) L L) L)) L (N 19 L (N 20 L (N 27 (N 34 L L L) L L) (N 24 L (N 27
  (N 34 L L L) L L) (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L))) L)) (N 19 L (N 17
  (N 20 L (N 24 L (N 27 (N 23 L L (N 34 L (N 25 (N 26 L L (N 32 L L L)) L L) L)) L L) (N 31 L (N
  34 (N 25 L (N 27 L L L) L) L L) L)) (N 24 L (N 23 (N 25 L (N 26 L L L) L) L (N 25 (N 32 L (N 34
  L L L) L) (N 26 (N 32 L L L) L L) L)) (N 31 L (N 23 (N 25 L (N 27 L L L) L) L (N 25 (N 32 L (N
  33 L L L) L) (N 27 (N 32 L L L) L L) L)) L))) L (N 20 L (N 24 L (N 27 (N 23 L L (N 30 (N 33 L L
  (N 26 (N 25 L (N 32 L L L) L) L L)) L L)) L L) (N 31 L (N 34 (N 25 L (N 27 L L L) L) L L) L))
  L)) L)) L (N 19 L (N 17 (N 20 L (N 26 (N 33 L L (N 23 L (N 24 L L (N 25 (N 27 L (N 32 L L L) L)
  L L)) (N 24 L (N 27 (N 25 L (N 32 L L L) L) L L) (N 18 (N 27 L (N 34 L L L) L) (N 27 (N 34 L L
  L) L L) L)))) L (N 33 (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L) L L)) (N 25 (N 32
  L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L)) L (N 20 L (N 26 (N 33 L L (N 23 L (N 24 L L (N 25
  (N 27 L (N 32 L L L) L) L L)) (N 8 (N 24 L (N 27 (N 25 L (N 32 L L L) L) L L) (N 18 (N 31 L (N
  34 L L L) L) (N 27 (N 34 L L L) L L) L)) (N 25 (N 32 L L L) L L) L))) L (N 33 (N 25 (N 32 L (N
  34 L L L) L) (N 27 (N 32 L L L) L L) L) L L)) (N 18 (N 24 L (N 23 (N 25 L (N 26 L L L) L) L (N
  30 (N 32 L (N 34 L L L) L) L L)) (N 31 L (N 23 (N 25 L (N 27 L L L) L) L (N 30 (N 32 L (N 33 L L
  L) L) L L)) L)) (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L) L))) (N 20 L (N 17 (N
  26 (N 33 L L L) L L) L L) L)))) L L) L) L L) L) L) L) (S 22 L (S 29 L (N 5 L (N 27 (N 34 (N 35 L
  L L) L L) L L) L) L) L) L)) (S 11 L (S 16 (S 22 (S 29 L (N 5 L (N 27 L (N 14 (N 32 (N 33 L L (N
  34 (N 19 L (N 25 L L (N 35 (N 8 (N 9 L L (N 31 L (N 12 L L (N 30 L L L)) L)) L (N 30 L (N 17 (N
  31 L L (N 9 (N 13 L L L) L L)) L L) L)) L L)) (N 25 L (N 8 (N 9 L L (N 31 L (N 12 L L (N 30 L L
  L)) L)) L (N 30 L (N 23 (N 31 L L (N 9 (N 13 L L L) L L)) L L) L)) (N 30 L (N 31 L L (N 9 (N 13
  L L L) L L)) (N 31 L (N 8 (N 12 L L L) L L) L)))) (N 35 (N 25 L L (N 19 L (N 8 (N 9 L L (N 18 (N
  31 L (N 12 L L (N 30 L L L)) L) L L)) L (N 17 (N 30 L (N 24 (N 13 L L (N 31 L L L)) L L) L) L
  L)) (N 26 (N 12 L (N 13 L L (N 31 L L L)) (N 23 L (N 31 L L L) L)) L (N 23 (N 24 L (N 30 L L (N
  12 L (N 31 L L L) L)) L) (N 24 (N 31 L L (N 13 L (N 30 L L L) L)) L L) L)))) L L) L)) L (N 33 (N
  34 (N 20 L (N 26 L L (N 35 (N 12 (N 13 L L (N 31 L (N 8 L L (N 30 L L L)) L)) L (N 30 L (N 17 (N
  31 L L (N 8 L (N 9 (N 13 L L L) L L) L)) L L) L)) L L)) (N 26 L (N 12 (N 13 L L (N 31 L (N 8 L L
  (N 30 L L L)) L)) L (N 30 L (N 23 (N 31 L L (N 9 (N 13 L L L) L L)) L L) L)) (N 30 L (N 31 L L
  (N 9 (N 13 L L L) L L)) (N 31 L (N 8 (N 12 L L L) L L) L)))) (N 35 (N 26 L L (N 20 L (N 12 (N 13
  L L (N 18 (N 31 L (N 8 L L (N 30 L L L)) L) L L)) L (N 17 (N 30 L (N 24 (N 9 L L (N 31 L L L)) L
  L) L) L L)) (N 25 (N 8 L (N 9 L L (N 31 L L L)) (N 23 L (N 31 L L L) L)) L (N 23 (N 24 L (N 30 L
  L (N 8 L (N 31 L L L) L)) L) (N 24 (N 31 L L (N 9 L (N 30 L L L) L)) L L) L)))) L L) L) L (N 30
  (N 34 L (N 35 L L L) L) (N 31 (N 34 L (N 35 L L L) L) L L) L))) L (N 32 (N 33 (N 34 (N 35 L (N
  19 L L (N 20 L L L)) L) (N 35 (N 25 L L (N 26 L L L)) L L) L) L (N 19 (N 34 L (N 35 L L L) L) (N
  25 (N 35 L L L) L L) L)) L (N 33 (N 20 (N 34 L (N 35 L L L) L) (N 26 (N 35 L L L) L L) L) L L)))
  L) L) (N 5 L (N 27 L (N 14 (N 17 (N 18 (N 34 L (N 35 (N 30 L (N 31 L L L) L) L L) L) (N 24 (N 23
  (N 30 L (N 35 L L L) L) (N 30 (N 34 L (N 35 L L L) L) (N 31 (N 35 L L L) L L) L) L) L L) L) (N
  18 (N 23 (N 24 (N 31 L (N 35 L L L) L) (N 30 (N 34 L (N 35 L L L) L) (N 31 (N 34 L L L) L L) L)
  L) L L) L L) L) L (N 17 (N 18 (N 34 L (N 35 (N 30 L (N 31 L L L) L) L L) L) (N 24 (N 23 (N 30 L
  (N 35 L L L) L) (N 30 (N 34 L (N 35 L L L) L) (N 31 (N 35 L L L) L L) L) L) L L) L) (N 18 (N 23
  (N 24 (N 31 L (N 35 L L L) L) (N 30 (N 34 L (N 35 L L L) L) (N 31 (N 34 L L L) L L) L) L) L L) L
  L) L)) L) L)) (S 29 L L (N 5 L (N 14 (N 17 (N 18 (N 27 L (N 34 L (N 35 (N 19 L (N 20 L L (N 8 (N
  23 L (N 13 L L (N 24 (N 31 L L L) L L)) L) L (N 9 (N 24 L (N 12 L L (N 23 (N 30 L L L) L L)) L)
  L (N 23 (N 30 L (N 31 L L L) L) (N 24 (N 31 L L L) L L) L)))) (N 20 L (N 12 (N 23 L (N 9 L L (N
  24 (N 31 L L L) L L)) L) L (N 13 (N 24 L (N 8 L L (N 23 (N 30 L L L) L L)) L) L (N 23 (N 30 L (N
  31 L L L) L) (N 24 (N 31 L L L) L L) L))) (N 23 (N 30 L (N 31 L L L) L) (N 24 (N 31 L L L) L L)
  L))) L L) L) L) (N 23 (N 27 L (N 24 (N 30 L (N 31 (N 35 L L L) L L) L) L L) L) (N 24 (N 27 L (N
  35 (N 30 L (N 31 L L L) L) L L) L) L L) L) L) (N 18 (N 23 (N 27 L (N 8 (N 12 L L (N 25 L L (N 30
  L (N 31 (N 34 L L L) L L) L))) L (N 12 (N 26 L L (N 30 L (N 31 (N 34 L L L) L L) L)) L (N 24 (N
  31 L (N 30 (N 35 L L L) L L) L) (N 35 (N 30 L (N 31 L L L) L) L L) L))) L) (N 24 (N 27 L L L) L
  L) L) L L) L) L (N 17 (N 18 (N 27 L (N 34 L (N 35 (N 19 L (N 20 L L (N 25 (N 32 L L L) L L)) (N
  20 L (N 26 (N 33 L L L) L L) L)) L L) L) L) (N 23 (N 27 L (N 24 (N 30 L (N 31 (N 35 L L L) L L)
  L) L L) L) (N 24 (N 27 L (N 35 (N 30 L (N 31 L L L) L) L L) L) L L) L) L) (N 18 (N 23 (N 27 L (N
  8 (N 12 L L (N 25 L L (N 26 (N 30 L (N 31 (N 34 L L L) L L) L) L L))) L (N 12 (N 26 L L (N 25 (N
  30 L (N 31 (N 34 L L L) L L) L) L L)) L L)) L) (N 24 (N 27 L L L) L L) L) L L) L)) L)) (S 29 L L
  L)) (S 22 L L (S 29 L L L)) (S 22 L L L)) (S 16 (S 22 (S 29 L (N 5 L (N 27 L (N 12 (N 13 (N 14
  (N 33 L L (N 8 L (N 9 L L (N 32 (N 19 (N 25 L L (N 26 L (N 20 L L (N 23 (N 31 (N 18 L (N 24 L L
  L) L) L L) L L)) L)) L (N 20 L (N 17 (N 26 L L (N 25 (N 31 (N 18 L (N 24 L L L) L) L L) L L)) L
  L) L)) L L)) (N 32 (N 9 L (N 19 (N 25 L L (N 26 L (N 20 L L (N 24 (N 30 (N 17 L (N 23 L L L) L)
  L L) L L)) L)) L (N 20 L (N 18 (N 26 L L (N 25 (N 30 (N 17 L (N 23 L L L) L) L L) L L)) L L) L))
  (N 20 L (N 26 L L (N 25 (N 34 L (N 35 L L L) L) L L)) (N 26 L (N 19 (N 34 L (N 35 L L L) L) L L)
  L))) L L))) L (N 20 L (N 26 L L (N 25 (N 32 (N 33 (N 34 L (N 35 L L L) L) L L) L L) L L)) (N 26
  L (N 19 (N 32 (N 33 (N 34 L (N 35 L L L) L) L L) L L) L L) L))) (N 8 (N 14 L L (N 17 L (N 23 L L
  (N 25 L (N 19 L L (N 20 L L L)) L)) (N 19 L (N 25 L L (N 26 L L L)) L))) L (N 14 (N 9 L (N 18 (N
  19 (N 34 L (N 35 (N 30 L L (N 32 L L L)) L L) L) L (N 20 L (N 23 (N 30 L L L) L L) L)) L (N 19
  (N 20 L (N 26 L L (N 25 (N 32 L L (N 23 (N 30 L L L) L L)) L L)) (N 17 (N 30 L L (N 23 L (N 25
  (N 32 L L L) L L) L)) (N 26 L L (N 25 (N 32 L L (N 23 (N 30 L L L) L L)) L L)) L)) L L)) (N 20 L
  (N 26 L L (N 25 (N 18 (N 23 (N 35 L (N 34 (N 19 L L (N 31 L L L)) L L) L) L (N 32 (N 19 L (N 34
  L L L) L) L L)) L (N 32 (N 19 L (N 34 L L L) L) L L)) L L)) (N 19 (N 26 L (N 17 (N 34 L (N 35 (N
  31 L L (N 32 L L L)) L L) L) L (N 32 (N 25 L (N 34 L L L) L) L L)) (N 33 (N 32 L L (N 30 L (N 31
  L L L) L)) L L)) (N 26 L L (N 25 (N 33 (N 32 L L (N 18 (N 30 L (N 31 L L L) L) L L)) L L) L L))
  L))) L (N 20 L (N 26 L L (N 25 (N 32 (N 33 (N 23 L L (N 30 L (N 34 L L L) L)) L L) L L) L L)) (N
  26 L (N 19 (N 32 (N 33 (N 17 L L (N 30 L (N 35 L L L) L)) L L) L L) L L) L)))) L) (N 13 (N 9 (N
  14 L L (N 18 L (N 24 L L (N 25 L (N 19 L L (N 20 L L L)) L)) (N 19 L (N 25 L L (N 26 L L L))
  L))) L (N 14 (N 8 L (N 17 (N 19 (N 34 L (N 35 (N 30 L L (N 32 L L L)) L L) L) L (N 20 L (N 24 (N
  31 L L L) L L) L)) L (N 19 (N 20 L (N 26 L L (N 25 (N 32 L L (N 24 (N 31 L L L) L L)) L L)) (N
  18 (N 31 L L (N 24 L (N 25 (N 32 L L L) L L) L)) (N 26 L L (N 25 (N 32 L L (N 24 (N 31 L L L) L
  L)) L L)) L)) L L)) (N 20 L (N 26 L L (N 25 (N 17 (N 24 (N 35 L (N 34 (N 19 L L (N 30 L L L)) L
  L) L) L (N 32 (N 19 L (N 34 L L L) L) L L)) L (N 32 (N 19 L (N 34 L L L) L) L L)) L L)) (N 19 (N
  26 L (N 18 (N 34 L (N 35 (N 30 L L (N 32 L L L)) L L) L) L (N 32 (N 25 L (N 34 L L L) L) L L))
  (N 33 (N 32 L L (N 30 L (N 31 L L L) L)) L L)) (N 26 L L (N 25 (N 33 (N 32 L L (N 17 (N 30 L (N
  31 L L L) L) L L)) L L) L L)) L))) L (N 20 L (N 26 L L (N 25 (N 32 (N 33 (N 24 L L (N 31 L (N 34
  L L L) L)) L L) L L) L L)) (N 26 L (N 19 (N 32 (N 33 (N 18 L L (N 31 L (N 35 L L L) L)) L L) L
  L) L L) L)))) L L) L) L) L) L) (S 29 L (N 5 L (N 35 (N 12 (N 13 (N 14 (N 26 L L (N 33 L L (N 20
  L (N 8 L (N 9 L L (N 25 (N 32 L L L) L L)) (N 25 (N 32 L L L) L L)) L))) L (N 20 L (N 25 (N 32 L
  L (N 26 (N 33 L L L) L L)) L (N 26 (N 33 L L L) L L)) (N 25 (N 32 L L L) L L))) (N 8 (N 14 L L
  (N 17 L (N 18 (N 19 L (N 23 L L (N 25 (N 30 L L (N 32 L L L)) L L)) (N 20 L (N 26 (N 33 L L L) L
  L) L)) L (N 19 L (N 23 L L (N 25 (N 30 L L (N 32 L L L)) L L)) L)) (N 19 L (N 9 (N 18 (N 20 L (N
  23 L (N 24 L L (N 25 (N 27 (N 26 L L (N 32 L L L)) L L) L L)) (N 25 (N 30 L (N 34 L L L) L) L
  L)) (N 25 (N 32 L L L) L L)) L (N 20 L (N 23 L (N 27 (N 24 L L (N 25 (N 26 L L (N 32 L L L)) L
  L)) L L) (N 25 (N 30 L (N 24 L L (N 26 (N 27 L (N 31 (N 34 L L L) L L) L) L L)) L) L L)) L)) L
  (N 18 (N 20 L (N 23 L (N 27 (N 24 L L (N 25 (N 32 L L L) L L)) L L) (N 25 (N 30 L (N 24 L L (N
  32 L L L)) L) L L)) (N 25 (N 32 L L L) L L)) L (N 20 L (N 25 (N 32 L L L) L L) L))) L))) L (N 14
  (N 9 L (N 18 (N 19 (N 27 L (N 34 L (N 17 L (N 20 L L (N 23 (N 26 L L (N 25 (N 24 L L (N 30 L L
  (N 32 L L L))) L L)) L (N 25 (N 30 L L L) L L))) (N 23 (N 30 L L L) L L)) L) L) L (N 20 L (N 23
  (N 30 L L L) L L) L)) L (N 19 (N 20 L (N 23 (N 26 L L (N 25 (N 24 L L (N 31 L L L)) L L)) L (N
  25 (N 30 L L L) L L)) (N 17 (N 23 L L (N 30 L L L)) (N 23 (N 26 L L (N 25 (N 24 L L (N 31 L L
  L)) L L)) L (N 25 (N 30 L L L) L L)) L)) L L)) (N 20 L (N 18 (N 25 (N 26 L L (N 32 L L (N 30 L
  (N 24 (N 31 L L L) L L) L))) L (N 26 (N 23 L (N 24 L L L) L) L L)) L (N 25 (N 32 L L L) L L)) (N
  19 (N 25 (N 26 L L (N 27 L (N 32 L L (N 30 L (N 17 (N 18 L (N 23 L (N 24 (N 31 L L L) L L) L) L)
  L L) L)) L)) L (N 26 (N 23 L (N 24 L L L) L) L L)) (N 18 (N 25 (N 26 L L (N 32 L L (N 30 L (N 17
  (N 23 L (N 24 (N 31 L L L) L L) L) L L) L))) L (N 26 (N 23 L (N 24 L L L) L) L L)) L (N 25 (N 32
  L L L) L L)) L))) L (N 20 L (N 18 (N 25 (N 32 L L (N 26 (N 33 L L L) L L)) L (N 26 (N 33 L L L)
  L L)) L (N 19 (N 9 L (N 23 (N 26 L L (N 25 (N 32 L L L) L L)) L (N 25 (N 32 L L L) L L)) (N 25
  (N 32 L L L) L L)) (N 9 (N 25 (N 32 L L (N 23 L (N 17 (N 24 L L (N 26 (N 27 L L L) L L)) L L)
  L)) L (N 26 (N 33 L L L) L L)) L (N 25 (N 32 L L L) L L)) L)) (N 25 (N 32 L L L) L L)))) L) (N
  13 (N 9 (N 14 L L (N 18 L (N 17 (N 19 L (N 24 L L (N 25 (N 31 L L (N 32 L L L)) L L)) (N 20 L (N
  26 (N 33 L L L) L L) L)) L (N 19 L (N 24 L L (N 25 (N 31 L L (N 32 L L L)) L L)) L)) (N 19 L (N
  8 (N 17 (N 20 L (N 23 L (N 24 L L (N 31 L L L)) (N 25 (N 32 L L (N 33 L L L)) L L)) (N 25 (N 32
  L L L) L L)) L (N 20 L (N 24 L (N 27 (N 23 L L (N 25 (N 26 L L (N 32 L L L)) L L)) L L) (N 25 (N
  31 L (N 23 L L (N 26 (N 27 L (N 30 (N 34 L L L) L L) L) L L)) L) L L)) L)) L (N 17 (N 20 L (N 24
  L (N 27 (N 23 L L (N 25 (N 32 L L L) L L)) L L) (N 25 (N 31 L (N 23 L L (N 32 L L L)) L) L L))
  (N 25 (N 32 L L L) L L)) L (N 20 L (N 25 (N 32 L L L) L L) L))) L))) L (N 14 (N 8 L (N 17 (N 19
  (N 27 L (N 34 L (N 18 L (N 20 L L (N 23 (N 26 L L (N 25 (N 24 L L (N 31 L L L)) L L)) L (N 25 (N
  26 L L (N 24 (N 30 L L (N 32 L L L)) L L)) L L))) (N 24 (N 31 L L L) L L)) L) L) L (N 20 L (N 24
  (N 31 L L L) L L) L)) L (N 19 (N 20 L (N 23 (N 26 L L (N 25 (N 24 L L (N 31 L L L)) L L)) L (N
  25 (N 26 L L (N 24 (N 30 L L L) L L)) L L)) (N 18 (N 24 L L (N 31 L L L)) (N 23 (N 26 L L (N 25
  (N 24 L L (N 31 L L L)) L L)) L (N 25 (N 26 L L (N 24 (N 30 L L L) L L)) L L)) L)) L L)) (N 20 L
  (N 17 (N 25 (N 26 L L (N 32 L L (N 31 L (N 23 (N 30 L L L) L L) L))) L (N 26 (N 23 L (N 24 L L
  L) L) L L)) L (N 25 (N 32 L L L) L L)) (N 19 (N 25 (N 26 L L (N 27 L (N 32 L L (N 31 L (N 18 (N
  17 L (N 23 (N 30 L L L) L L) L) L L) L)) L)) L (N 26 (N 23 L (N 24 L L L) L) L L)) (N 17 (N 25
  (N 26 L L (N 32 L L (N 31 L (N 18 (N 23 (N 30 L L L) L L) L L) L))) L (N 26 (N 23 L (N 24 L L L)
  L) L L)) L (N 25 (N 32 L L L) L L)) L))) L (N 20 L (N 17 (N 25 (N 32 L L (N 26 (N 33 L L L) L
  L)) L (N 26 (N 33 L L L) L L)) L (N 19 (N 8 L (N 23 (N 26 L L (N 25 (N 32 L L L) L L)) L (N 25
  (N 27 L (N 30 (N 24 L L (N 32 L L L)) L L) L) L L)) (N 25 (N 32 L L L) L L)) (N 8 (N 25 (N 32 L
  L (N 24 L (N 18 (N 23 L L (N 26 (N 27 L L L) L L)) L L) L)) L (N 26 (N 33 L L L) L L)) L (N 25
  (N 32 L L L) L L)) L)) (N 25 (N 32 L L L) L L)))) L L) L) L L) L) L) L) (S 22 L (S 29 L L L) L)
  L)) (S 11 L L L))))))) (S 15 L L (S 21 L L (S 28 L L L)))) (S 10 L L (S 15 L L (S 21 L L L))))
  (S 6 L (S 10 L (S 15 L L (S 21 L L (S 28 L L (S 2 L (S 4 (S 7 (S 11 L (S 16 L (S 22 L L (S 29 L
  L (N 9 L L (N 5 (N 8 (N 12 L L (N 17 L L (N 20 (N 13 (N 18 L L (N 19 L L L)) L (N 14 (N 19 L L
  L) L L)) L L))) L (N 12 (N 13 L L (N 14 L L L)) L (N 14 (N 13 (N 18 L L (N 19 (N 20 L L L) L L))
  L (N 17 (N 18 L L (N 19 L L L)) L (N 19 (N 20 L L L) L L))) L L))) L (N 8 (N 12 (N 13 L L (N 14
  L L L)) L (N 13 (N 14 (N 19 L L (N 18 (N 20 L L L) L L)) L (N 17 (N 18 L L (N 19 L L L)) L (N 18
  (N 20 L L L) L L))) L L)) L L))))) (S 22 L L (S 29 L L (N 9 L L (N 5 (N 8 (N 12 L L (N 13 (N 14
  (N 17 L (N 18 L (N 19 L (N 27 (N 34 (N 35 L (N 20 (N 23 L (N 30 L L (N 31 L L L)) (N 24 L (N 33
  L L L) L)) L (N 23 L (N 30 L L L) L)) L) L L) L L) (N 24 L (N 31 L L L) L)) (N 19 L (N 25 L (N
  32 L L L) L) L)) (N 18 L (N 19 L (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L) L) L) L))
  L (N 17 L (N 18 L (N 23 L (N 27 (N 30 L L (N 31 L (N 24 L L (N 34 (N 35 L L L) L L)) L)) L L) (N
  24 L (N 27 (N 31 L L (N 30 L (N 34 (N 35 L L L) L L) L)) L L) L)) (N 19 (N 20 L (N 25 L (N 27 (N
  32 L (N 34 (N 35 L L L) L L) L) L L) L) L) (N 20 (N 23 L (N 27 (N 30 L L (N 26 L (N 31 L (N 33
  (N 34 L L L) L L) L) L)) L L) (N 24 L (N 27 (N 26 L (N 33 (N 32 L (N 34 L L L) L) L L) L) L L)
  L)) (N 27 (N 34 (N 35 L (N 23 L (N 30 L L (N 26 (N 25 L (N 31 L L L) L) L L)) (N 24 L (N 26 (N
  25 L (N 30 L L (N 31 L L L)) L) L L) L)) L) L L) L L) L) L)) (N 18 L (N 19 (N 20 L (N 26 (N 33
  (N 35 L (N 23 L (N 27 (N 30 L L (N 31 L (N 24 L L (N 25 L L L)) L)) L L) (N 24 L (N 25 L (N 27
  (N 30 L (N 31 L L (N 32 L L L)) L) L L) L) L)) L) L L) L L) L) (N 20 (N 23 L (N 24 L (N 27 (N 26
  L (N 31 L L (N 25 (N 30 L (N 32 L (N 33 (N 34 L L L) L L) L) L) L L)) L) L L) (N 25 (N 26 L (N
  27 (N 32 L (N 33 (N 34 L L L) L L) L) L L) L) (N 27 (N 26 L (N 32 (N 33 L L L) L L) L) L L) L))
  (N 24 L (N 27 (N 26 L (N 30 L (N 31 L L (N 33 (N 32 L (N 34 L L L) L) L L)) L) L) L L) L)) (N 26
  (N 27 (N 33 (N 34 (N 35 L (N 23 L (N 30 L L (N 31 L (N 24 L L (N 25 L L L)) L)) (N 24 L (N 25 L
  (N 30 L (N 31 L L (N 32 L L L)) L) L) L)) L) L L) L L) L L) L L) L) L) L))) L (N 14 (N 17 L (N
  19 L (N 23 L (N 27 (N 30 L L (N 32 L (N 25 L L (N 34 (N 35 L L L) L L)) L)) L L) (N 25 L (N 27
  (N 32 L L (N 30 L (N 34 (N 35 L L L) L L) L)) L L) L)) (N 18 (N 20 L (N 24 L (N 27 (N 31 L (N 34
  (N 35 L L L) L L) L) L L) L) L) (N 20 (N 23 L (N 27 (N 30 L L (N 26 L (N 32 L (N 33 (N 34 L L L)
  L L) L) L)) L L) (N 25 L (N 27 (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L) L) L L) L)) (N 27 (N
  34 (N 35 L (N 23 L (N 30 L L (N 26 (N 24 L (N 32 L L L) L) L L)) (N 25 L (N 26 (N 24 L (N 30 L L
  (N 32 L L L)) L) L L) L)) L) L L) L L) L) L)) (N 19 L (N 18 (N 20 L (N 26 (N 33 (N 35 L (N 23 L
  (N 27 (N 30 L L (N 31 L (N 24 L L (N 25 L L L)) L)) L L) (N 24 L (N 25 L (N 27 (N 30 L (N 31 L L
  (N 32 L L L)) L) L L) L) L)) L) L L) L L) L) (N 20 (N 23 L (N 25 L (N 27 (N 26 L (N 32 L L (N 24
  (N 30 L (N 31 L (N 33 (N 34 L L L) L L) L) L) L L)) L) L L) (N 24 (N 26 L (N 27 (N 31 L (N 33 (N
  34 L L L) L L) L) L L) L) (N 27 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L)) (N 25 L (N 27 (N 26
  L (N 30 L (N 32 L L (N 33 (N 31 L (N 34 L L L) L) L L)) L) L) L L) L)) (N 26 (N 27 (N 33 (N 34
  (N 35 L (N 23 L (N 30 L L (N 31 L (N 24 L L (N 25 L L L)) L)) (N 24 L (N 25 L (N 30 L (N 31 L L
  (N 32 L L L)) L) L) L)) L) L L) L L) L L) L L) L) L) L)) L L))) L (N 12 (N 13 L L (N 14 L L L))
  L (N 14 (N 13 (N 18 L (N 24 L (N 27 (N 31 L L (N 19 (N 25 L (N 32 L (N 34 (N 35 L L L) L L) L)
  L) (N 25 (N 32 L (N 34 (N 35 L L L) L L) L) (N 32 (N 30 L (N 33 L (N 34 (N 35 L L L) L L) L) L)
  L L) L) L)) L L) (N 19 (N 25 L (N 27 (N 32 L (N 34 (N 35 L L L) L L) L) L L) L) (N 23 (N 25 L (N
  27 (N 32 (N 17 L (N 20 L L (N 30 L (N 34 (N 35 L L L) L L) L)) (N 20 L (N 33 L L L) L)) L L) L
  L) L) (N 25 (N 26 L (N 27 (N 32 L (N 34 (N 35 L L L) L L) L) L L) L) (N 27 (N 32 (N 26 (N 34 L
  (N 17 L L (N 20 L L L)) L) (N 33 L L (N 30 L (N 17 (N 31 L (N 34 (N 35 L L L) L L) L) L L) L))
  L) L L) L L) L) L) L)) (N 17 (N 19 L (N 20 (N 23 L (N 24 L (N 27 (N 34 L (N 31 L L (N 33 L L L))
  L) L L) (N 26 L (N 27 (N 31 L (N 34 L L L) L) L L) L)) (N 24 L (N 26 L (N 33 L L L) L) L)) (N 23
  L (N 27 (N 26 L L (N 24 L (N 30 L (N 34 (N 35 L L L) L L) L) L)) L L) (N 24 L (N 26 (N 27 L L L)
  L L) L)) L) L) (N 19 (N 20 L (N 25 L (N 27 (N 32 L (N 34 (N 35 L L L) L L) L) L L) L) L) (N 20
  (N 24 L (N 27 (N 23 L (N 25 (N 32 L (N 34 (N 35 L L L) L L) L) (N 26 L L (N 30 (N 32 L L L) L
  L)) L) (N 26 L (N 33 L L L) L)) L L) (N 26 L (N 27 (N 23 L (N 31 L (N 33 L L (N 30 (N 34 L L L)
  L L)) L) L) L L) L)) (N 27 (N 34 (N 35 L (N 24 L (N 31 L L (N 32 (N 33 L L L) L L)) (N 26 (N 25
  L (N 31 L L L) L) L L)) L) L L) L L) L) L) L)) L (N 27 (N 34 (N 35 L (N 17 (N 18 L (N 19 L (N 20
  L (N 23 L (N 30 L L (N 26 (N 25 L (N 32 L L L) L) L L)) (N 26 (N 24 L (N 32 L L L) L) L L)) (N
  23 L (N 30 L L L) L)) (N 20 L (N 23 L (N 30 L L L) L) L)) (N 19 L (N 20 L (N 26 (N 24 L (N 32 L
  L L) L) L L) L) L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L (N 32 L L L)) (N 25 L (N 31 L L L)
  L)) (N 24 L (N 31 L L L) L)) (N 20 L (N 24 L (N 31 L L L) L) L)) (N 19 (N 20 L (N 24 L (N 31 L L
  (N 32 L L L)) (N 25 L (N 31 L L L) L)) (N 24 L (N 31 L L L) L)) (N 20 (N 26 L (N 33 L L (N 30 (N
  31 L L L) L L)) (N 33 L (N 23 (N 24 L L L) L L) L)) L (N 23 (N 24 L (N 30 L L L) L) (N 30 (N 31
  L L L) L L) L)) (N 20 (N 23 (N 24 L (N 30 L L L) L) (N 30 (N 31 L L L) L L) L) (N 23 (N 24 L (N
  30 L L L) L) (N 30 (N 31 L L L) L L) L) L)) (N 19 (N 20 L (N 24 L (N 31 L L L) L) L) (N 20 (N 26
  L (N 33 L L L) L) (N 26 (N 24 L (N 32 L L L) L) L L) L) L)) (N 18 (N 19 L (N 20 L (N 25 L (N 32
  L L L) L) L) L) (N 19 (N 20 L (N 25 L (N 32 L L L) L) L) (N 20 (N 26 L (N 33 L L L) L) (N 26 (N
  25 L (N 32 L L L) L) L L) L) L) L)) L) (N 35 (N 17 (N 18 L (N 31 L L (N 19 L (N 20 (N 32 L L L)
  L L) L)) (N 19 L (N 31 L L L) L)) (N 30 (N 18 L (N 31 L L (N 32 L L L)) (N 31 L (N 19 (N 20 L L
  L) L L) L)) L (N 33 (N 19 L (N 31 L L L) L) L L)) (N 18 (N 20 L (N 30 L L L) L) (N 32 (N 33 L L
  L) L L) L)) (N 17 (N 18 L (N 19 L (N 20 (N 23 L (N 30 L L (N 26 L (N 25 (N 32 L L L) L L) L)) (N
  26 L (N 30 L L L) L)) L (N 23 L (N 30 L L L) L)) (N 23 L (N 30 L L L) L)) (N 19 L (N 31 (N 33 L
  L L) L L) L)) (N 30 (N 23 L (N 31 L (N 32 L L (N 18 (N 24 L L L) L L)) (N 32 L (N 18 (N 20 L L
  L) L L) L)) (N 32 L (N 19 (N 20 L L L) L L) L)) L (N 33 (N 31 L (N 32 L L L) L) L L)) (N 18 (N
  20 L (N 25 L (N 26 (N 30 (N 32 L L L) L L) L L) L) L) (N 32 (N 33 L L L) L L) L)) L) L) (N 34 (N
  35 (N 17 (N 18 L (N 24 L L (N 19 L (N 20 (N 25 L L L) L L) L)) (N 19 L (N 24 L L L) L)) (N 23 (N
  18 L (N 24 L L (N 25 L L L)) (N 24 L (N 19 (N 20 L L L) L L) L)) L (N 26 (N 19 L (N 24 L L L) L)
  L L)) (N 18 (N 20 L (N 23 L L L) L) (N 25 (N 26 L L L) L L) L)) (N 17 (N 18 L (N 19 L (N 20 (N
  23 L (N 30 L L (N 33 L L L)) (N 24 (N 26 L L L) L L)) L (N 23 L (N 30 L L L) L)) (N 23 L (N 30 L
  L L) L)) (N 19 L (N 24 (N 26 L L L) L L) L)) (N 23 (N 24 L (N 25 L L (N 18 (N 31 L L L) L L)) (N
  25 L (N 18 (N 20 L L L) L L) L)) L (N 26 (N 24 L (N 25 L L L) L) L L)) (N 18 (N 20 L (N 23 (N 25
  L L L) L L) L) (N 25 (N 26 L L L) L L) L)) L) (N 35 (N 17 (N 18 L (N 19 L L (N 20 (N 23 L (N 24
  (N 31 L L L) L L) L) L L)) (N 19 L (N 20 (N 24 (N 26 L L L) L L) L L) L)) (N 18 (N 20 L L (N 19
  (N 23 (N 30 L L L) L L) L L)) L (N 19 (N 20 L L L) L L)) (N 18 (N 20 L (N 19 (N 25 L L L) L L)
  L) (N 19 (N 20 L L L) L L) L)) L L) L) L)) L L))) L (N 8 (N 12 (N 13 L L (N 14 L L L)) L (N 13
  (N 14 (N 19 L (N 25 L (N 27 (N 32 L L (N 18 (N 24 L (N 31 L (N 34 (N 35 L L L) L L) L) L) (N 24
  (N 31 L (N 34 (N 35 L L L) L L) L) (N 31 (N 30 L (N 33 L (N 34 (N 35 L L L) L L) L) L) L L) L)
  L)) L L) (N 18 (N 24 L (N 27 (N 31 L (N 34 (N 35 L L L) L L) L) L L) L) (N 23 (N 24 L (N 27 (N
  31 (N 17 L (N 20 L L (N 30 L (N 34 (N 35 L L L) L L) L)) (N 20 L (N 33 L L L) L)) L L) L L) L)
  (N 24 (N 26 L (N 27 (N 31 L (N 34 (N 35 L L L) L L) L) L L) L) (N 27 (N 31 (N 26 (N 34 L (N 17 L
  L (N 20 L L L)) L) (N 33 L L (N 30 L (N 17 (N 32 L (N 34 (N 35 L L L) L L) L) L L) L)) L) L L) L
  L) L) L) L)) (N 17 (N 18 L (N 20 (N 23 L (N 24 (N 31 L (N 34 (N 27 L (N 25 L L (N 26 L L L)) L)
  L L) L) (N 27 (N 31 (N 34 L (N 30 L L (N 32 L L L)) L) L L) L L) L) (N 25 L (N 26 L (N 33 L L L)
  L) L)) (N 23 L (N 27 (N 26 L L (N 25 L (N 30 L (N 34 (N 35 L L L) L L) L) L)) L L) (N 25 L (N 26
  (N 27 L L L) L L) L)) L) L) (N 18 (N 20 L (N 24 L (N 27 (N 31 L (N 34 (N 35 L L L) L L) L) L L)
  L) L) (N 20 (N 24 (N 31 L (N 34 (N 35 L (N 23 L L (N 25 L L L)) L) L L) L) (N 27 (N 31 (N 35 L
  (N 30 L L (N 32 L L L)) L) L L) L L) L) (N 27 (N 34 (N 35 L (N 24 (N 26 L L (N 23 L (N 31 L L L)
  L)) (N 31 (N 26 L L (N 30 L L L)) L L) L) L) L L) L L) L) L) L)) L (N 27 (N 34 (N 35 L (N 17 (N
  18 L (N 19 L (N 20 L (N 23 L (N 30 L L (N 26 (N 24 L (N 31 L L L) L) L L)) (N 26 (N 24 L (N 31 L
  L L) L) L L)) (N 23 L (N 30 L L L) L)) (N 20 L (N 26 (N 24 L (N 31 L L L) L) L L) L)) (N 19 L (N
  20 L (N 23 L (N 30 L L L) L) L) L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L (N 32 L L L)) (N 25
  L (N 31 L L L) L)) (N 25 L (N 32 L L L) L)) (N 20 L (N 24 L (N 31 L L L) L) L)) (N 19 (N 20 L (N
  24 L (N 31 L L (N 32 L L L)) (N 25 L (N 31 L L L) L)) (N 25 L (N 32 L L L) L)) (N 20 (N 26 L (N
  33 L L (N 30 (N 31 L L L) L L)) (N 33 L (N 23 (N 24 L L L) L L) L)) L (N 23 (N 25 L (N 30 L L L)
  L) (N 30 (N 32 L L L) L L) L)) (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 24 L (N 31 L L L) L) L L)
  L)) (N 19 (N 20 L (N 24 L (N 31 L L L) L) L) (N 20 (N 23 (N 24 L (N 32 L L L) L) (N 30 (N 32 L L
  L) L L) L) (N 23 (N 24 L (N 32 L L L) L) (N 30 (N 32 L L L) L L) L) L) L)) (N 18 (N 19 L (N 20 L
  (N 24 L (N 31 L L L) L) L) L) (N 19 (N 20 L (N 24 L (N 31 L L L) L) L) (N 20 (N 26 L (N 33 L L
  L) L) (N 26 (N 24 L (N 31 L L L) L) L L) L) L) L)) L) (N 35 (N 17 (N 18 L (N 32 L L (N 19 L (N
  20 (N 31 L L L) L L) L)) (N 19 L (N 32 L L L) L)) (N 30 (N 19 L (N 31 L L (N 32 L L L)) (N 31 L
  (N 18 (N 20 L L L) L L) L)) L (N 33 (N 18 L (N 31 L L L) L) L L)) (N 18 (N 20 L (N 31 L L L) L)
  (N 31 (N 33 L L L) L L) L)) (N 17 (N 18 L (N 19 L (N 20 (N 23 L (N 30 L L (N 26 L (N 24 (N 31 L
  L L) L L) L)) (N 26 L (N 30 L L L) L)) L (N 23 L (N 30 L L L) L)) (N 31 (N 33 L L L) L L)) (N 19
  L (N 23 L (N 30 L L L) L) L)) (N 30 (N 23 L (N 31 L (N 32 L L (N 18 (N 20 L L L) L L)) (N 32 L
  (N 18 (N 24 L L L) L L) L)) (N 31 L (N 18 (N 20 L L L) L L) L)) L (N 33 (N 31 L (N 32 L L L) L)
  L L)) (N 18 (N 20 L (N 31 L L L) L) (N 31 (N 33 L L L) L L) L)) L) L) (N 34 (N 35 (N 17 (N 18 L
  (N 25 L L (N 19 L (N 20 (N 24 L L L) L L) L)) (N 19 L (N 25 L L L) L)) (N 23 (N 19 L (N 24 L L
  (N 25 L L L)) (N 24 L (N 18 (N 20 L L L) L L) L)) L (N 26 (N 18 L (N 24 L L L) L) L L)) (N 18 (N
  20 L (N 24 L L L) L) (N 24 (N 26 L L L) L L) L)) (N 17 (N 18 L (N 19 L (N 20 (N 23 L (N 30 L L
  (N 33 L L L)) (N 24 (N 26 L L L) L L)) L (N 23 L (N 30 L L L) L)) (N 24 (N 26 L L L) L L)) (N 19
  L (N 23 L (N 30 L L L) L) L)) (N 23 (N 24 L (N 25 L L (N 18 (N 20 L L L) L L)) (N 25 L (N 18 (N
  31 L L L) L L) L)) L (N 26 (N 24 L (N 25 L L L) L) L L)) (N 18 (N 20 L (N 24 L L L) L) (N 24 (N
  26 L L L) L L) L)) L) (N 35 (N 17 (N 18 L (N 19 L L (N 20 (N 24 (N 26 L L L) L L) L L)) (N 19 L
  (N 20 (N 23 L (N 24 (N 31 L L L) L L) L) L L) L)) (N 18 (N 20 L L (N 19 (N 23 (N 30 L L L) L L)
  L L)) L (N 19 (N 20 L L L) L L)) (N 18 (N 20 L (N 24 L L L) L) (N 19 (N 20 L L L) L L) L)) L L)
  L) L)) L L)) L L)))))) (S 16 L (S 22 L (S 29 L L (N 9 L L (N 27 (N 13 (N 12 L (N 14 (N 17 (N 23
  L L (N 18 L (N 19 L (N 20 (N 34 L L L) L L) (N 8 (N 26 L (N 20 (N 33 L L L) L L) L) (N 5 (N 24 L
  (N 31 L L L) L) L (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L) L)) L)) (N 19 L (N 5 (N
  26 L (N 20 (N 33 L L L) L L) L) (N 8 (N 25 L (N 32 L L L) L) L (N 20 (N 26 L (N 33 L L L) L) (N
  26 (N 33 L L L) L L) L)) L) L))) L (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L) L)) L
  (N 17 (N 23 L L (N 18 L (N 19 L (N 20 (N 34 L L L) L L) (N 8 (N 5 L (N 24 (N 31 L L L) L L) (N
  20 (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L) L) (N 26 (N 24 L (N 25 L (N 31 (N 33 L L L) L L)
  L) L) L L) L)) (N 5 (N 24 L (N 31 L L L) L) L (N 20 (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L)
  L) (N 26 (N 24 L (N 25 L (N 31 (N 33 L L L) L L) L) L) L L) L)) L)) (N 19 L (N 5 (N 26 L (N 20
  (N 31 L (N 34 L L L) L) L L) L) (N 8 (N 30 L L (N 20 (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L)
  L) (N 26 (N 25 L (N 32 (N 33 L L L) L L) L) L L) L)) L (N 30 (N 31 L (N 34 L L L) L) L L)) L)
  L))) L (N 20 (N 26 L (N 33 (N 31 L (N 34 L (N 18 L L (N 19 L L L)) L) L) L L) L) (N 26 (N 33 (N
  31 L (N 34 (N 35 L (N 24 L L (N 25 L L L)) L) L L) L) L L) L L) L))) (N 14 (N 17 (N 23 L L (N 18
  L (N 19 L (N 20 (N 34 L L L) L L) (N 8 (N 26 L (N 5 L (N 24 (N 31 L L L) L L) (N 30 L (N 31 (N
  33 L L L) L L) L)) L) (N 20 (N 26 L (N 33 L (N 34 L L L) L) L) (N 34 (N 35 L (N 31 (N 33 L L L)
  L L) L) L L) L) L)) (N 19 L (N 5 (N 26 L (N 8 L (N 25 (N 32 L L L) L L) (N 30 L (N 32 (N 33 L L
  L) L L) L)) L) (N 20 (N 26 L (N 33 L (N 34 L L L) L) L) (N 34 (N 35 L (N 32 (N 33 L L L) L L) L)
  L L) L) L) L))) L (N 20 (N 26 L (N 33 L (N 34 (N 35 L L L) L L) L) L) (N 23 (N 24 L (N 25 L (N
  26 (N 35 L L L) L L) (N 8 (N 5 L (N 18 (N 31 L L L) L L) (N 30 L (N 31 (N 33 L L L) L L) L)) (N
  18 (N 31 L (N 5 L L (N 30 (N 35 L L L) L L)) L) (N 31 (N 5 L L (N 30 L (N 33 L L L) L)) L L) L)
  L)) (N 25 L (N 5 (N 8 L (N 19 (N 32 L L L) L L) (N 30 L (N 32 (N 33 L L L) L L) L)) (N 19 (N 32
  L (N 8 L L (N 30 (N 35 L L L) L L)) L) (N 32 (N 8 L L (N 30 L (N 33 L L L) L)) L L) L) L) L)) L
  (N 5 (N 8 (N 30 L (N 33 (N 26 L (N 18 L (N 19 L L (N 31 L L L)) (N 19 L (N 32 L L L) L)) L) L L)
  L) (N 18 L (N 34 (N 35 L (N 31 L L (N 19 (N 32 L L L) L L)) L) L L) (N 19 (N 25 L (N 32 L L L)
  L) (N 25 (N 32 L L L) L L) L)) L) (N 8 (N 19 L (N 34 (N 35 L (N 32 L L (N 18 (N 31 L L L) L L))
  L) L L) (N 18 (N 24 L (N 31 L L L) L) (N 24 (N 31 L L L) L L) L)) (N 30 (N 26 (N 33 L (N 34 (N
  35 L L L) L L) L) (N 33 (N 31 L (N 34 (N 35 L L L) L L) (N 32 L (N 19 (N 25 L L L) L L) L)) L L)
  L) L L) L) L)) L)) L (N 8 (N 17 (N 23 L L (N 5 L (N 18 L (N 24 (N 31 L L L) L L) (N 19 L (N 20
  (N 26 L (N 34 L (N 31 (N 33 L L L) L L) L) L) (N 34 (N 35 L (N 31 (N 33 L L L) L L) L) L L) L)
  L)) (N 18 L (N 30 L (N 31 (N 24 L (N 33 L (N 20 (N 26 L L L) L L) L) L) L L) L) L))) L (N 18 (N
  20 L (N 31 L (N 34 (N 35 L (N 5 L L (N 24 L L L)) L) L L) L) L) (N 20 (N 26 L (N 19 L (N 34 (N
  33 L (N 35 L L L) L) L L) (N 23 (N 24 L (N 25 L L L) L) L (N 5 (N 24 L (N 31 L L L) L) (N 24 (N
  31 L L L) L L) L))) L) (N 34 (N 35 L (N 31 (N 33 L L L) L L) L) L L) L) L)) (N 17 (N 23 L L (N
  18 L (N 19 L (N 20 (N 34 L L L) L L) (N 20 (N 26 L (N 34 L (N 31 (N 33 L L L) L L) L) L) (N 34
  (N 35 L (N 31 (N 33 L L L) L L) L) L L) L)) (N 19 L (N 25 (N 26 L (N 32 (N 33 L (N 35 L L L) L)
  L L) L) L L) L))) L (N 18 (N 20 L (N 31 L (N 34 (N 35 L (N 5 L L (N 24 L L L)) L) L L) L) L) (N
  20 (N 26 L (N 19 L (N 34 (N 33 L (N 35 L L L) L) L L) (N 23 (N 24 L (N 25 L L L) L) L (N 5 (N 24
  L (N 31 L L L) L) (N 24 (N 31 L L L) L L) L))) L) (N 34 (N 35 L (N 31 (N 33 L L L) L L) L) L L)
  L) L)) L))) L (N 14 (N 12 L (N 17 (N 23 L L (N 18 L (N 19 L (N 20 (N 34 L L L) L L) (N 8 (N 26 L
  (N 20 (N 32 L (N 34 L L L) L) L L) L) (N 5 (N 30 L L (N 20 (N 26 L (N 33 (N 31 L (N 34 L L L) L)
  L L) L) (N 26 (N 24 L (N 31 (N 33 L L L) L L) L) L L) L)) L (N 30 (N 31 L (N 34 L L L) L) L L))
  L)) (N 19 L (N 5 (N 8 L (N 25 (N 32 L L L) L L) (N 20 (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L)
  L) (N 26 (N 24 L (N 25 L (N 32 (N 33 L L L) L L) L) L) L L) L)) (N 8 (N 25 L (N 32 L L L) L) L
  (N 20 (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L) L) (N 26 (N 24 L (N 25 L (N 31 (N 33 L L L) L
  L) L) L) L L) L)) L) L))) L (N 20 (N 26 L (N 33 (N 32 L (N 34 L (N 18 L L (N 19 L L L)) L) L) L
  L) L) (N 26 (N 33 (N 32 L (N 34 (N 35 L (N 24 L L (N 25 L L L)) L) L L) L) L L) L L) L)) (N 5 (N
  17 (N 23 L L (N 8 L (N 18 L (N 19 L (N 20 (N 34 L L L) L L) (N 20 (N 26 L (N 34 L (N 31 (N 33 L
  L L) L L) L) L) (N 34 (N 35 L (N 31 (N 33 L L L) L L) L) L L) L)) (N 19 L (N 25 (N 32 L L L) L
  L) L)) (N 19 L (N 30 L (N 32 (N 25 L (N 33 L (N 20 (N 26 L L L) L L) L) L) L L) L) L))) L (N 19
  (N 20 L (N 32 L (N 34 (N 35 L (N 8 L L (N 25 L L L)) L) L L) L) L) (N 20 (N 26 L (N 18 L (N 34
  (N 33 L (N 35 L L L) L) L L) (N 23 (N 24 L (N 25 L L L) L) L (N 8 (N 25 L (N 32 L L L) L) (N 25
  (N 32 L L L) L L) L))) L) (N 34 (N 35 L (N 32 (N 33 L L L) L L) L) L L) L) L)) (N 17 (N 23 L L
  (N 18 L (N 19 L (N 20 (N 34 L L L) L L) (N 24 (N 26 L (N 31 (N 33 L (N 35 L L L) L) L L) L) L
  L)) (N 19 L (N 20 (N 26 L (N 34 L (N 31 (N 33 L L L) L L) L) L) (N 34 (N 35 L (N 31 (N 33 L L L)
  L L) L) L L) L) L))) L (N 19 (N 20 L (N 32 L (N 34 (N 35 L (N 8 L L (N 25 L L L)) L) L L) L) L)
  (N 20 (N 26 L (N 18 L (N 34 (N 33 L (N 35 L L L) L) L L) (N 23 (N 24 L (N 25 L L L) L) L (N 8 (N
  25 L (N 32 L L L) L) (N 25 (N 32 L L L) L L) L))) L) (N 34 (N 35 L (N 32 (N 33 L L L) L L) L) L
  L) L) L)) L)) L L)) L L))) (S 29 L L (N 9 L L (N 13 (N 12 L (N 14 (N 17 (N 18 L (N 19 L (N 20 (N
  26 L (N 33 L L L) L) L L) (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L) L)) (N 19 L (N
  20 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L) L) L)) L (N 20 (N 26 L (N 33 L L L) L) (N 26
  (N 33 L L L) L L) L)) L (N 17 (N 18 L (N 19 L (N 20 (N 27 (N 34 L L L) L L) L L) (N 8 (N 5 L (N
  23 L L (N 24 (N 31 L L L) L L)) (N 20 (N 23 L (N 24 (N 26 L L L) L L) (N 24 (N 26 L (N 27 (N 31
  L (N 34 L L L) L) L L) L) (N 27 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L)) (N 26 (N 24 L (N 23
  L L (N 25 L (N 27 (N 31 (N 33 L L L) L L) L L) L)) L) L L) L)) (N 5 (N 23 L L (N 24 L (N 31 L L
  L) L)) L (N 20 (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N 26 L (N 27 (N 31 L (N 34 L L L) L) L L)
  L) (N 27 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L)) (N 26 (N 24 L (N 25 L (N 27 (N 23 L L (N 31
  (N 33 L L L) L L)) L L) L) L) L L) L)) L)) (N 19 L (N 20 (N 24 (N 26 L (N 23 L L (N 5 L (N 8 (N
  27 (N 30 L L (N 31 L (N 34 L L L) L)) L L) L L) L)) L) (N 27 (N 23 L L (N 26 L (N 33 (N 31 L (N
  34 L L L) L) L L) L)) L L) L) (N 26 (N 24 L (N 25 L (N 27 (N 23 L L (N 5 L (N 8 (N 30 L L (N 31
  (N 33 L L L) L L)) L L) L)) L L) L) L) L L) L) L)) L (N 20 (N 18 L (N 19 L (N 27 (N 26 L (N 33
  (N 34 L L L) L L) L) L L) (N 8 (N 24 (N 26 L (N 23 L L (N 27 (N 31 L (N 5 L L (N 30 (N 32 L (N
  33 (N 34 L L L) L L) L) L L)) L) L L)) L) (N 27 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L) (N 5
  (N 24 L (N 31 L L L) L) L (N 23 (N 24 L (N 25 L (N 27 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L)
  L) L (N 30 (N 31 L (N 24 (N 26 L (N 27 (N 32 L (N 25 (N 35 L L L) L L) L) L L) L) L L) L) L L)))
  L)) (N 19 L (N 5 (N 24 L (N 27 (N 23 L L (N 26 L (N 31 L (N 33 (N 34 L L L) L L) L) L)) L L) L)
  (N 8 (N 23 (N 24 L (N 25 L (N 27 (N 26 L (N 30 L L (N 31 (N 33 L L L) L L)) L) L L) L) L) L (N
  24 (N 26 L (N 27 (N 31 L (N 33 (N 34 L L L) L L) L) L L) L) (N 27 (N 26 L (N 31 (N 33 L L L) L
  L) L) L L) L)) L (N 23 (N 24 L (N 25 L (N 27 (N 26 L (N 30 (N 31 L L L) L L) L) L L) L) L) L L))
  L) L)) (N 26 (N 24 L (N 27 (N 33 (N 31 L (N 35 L L L) L) L L) L L) L) L L) L))) (N 14 (N 17 (N
  18 L (N 19 L (N 20 (N 26 L (N 27 (N 34 L L L) L L) L) L L) (N 20 (N 26 L (N 27 (N 33 L (N 34 L L
  L) L) L L) L) (N 27 (N 34 (N 35 L (N 23 L (N 24 (N 26 L L L) L L) (N 8 (N 25 L (N 33 L L L) L)
  (N 24 (N 26 L (N 31 L L L) L) (N 31 (N 33 L L L) L L) L) L)) L) L L) L L) L)) (N 19 L (N 20 (N
  26 L (N 27 (N 33 L (N 34 L L L) L) L L) L) (N 27 (N 34 (N 35 L (N 23 L (N 25 (N 26 L L L) L L)
  (N 5 (N 24 L (N 33 L L L) L) (N 24 (N 26 L (N 33 L L L) L) (N 32 (N 33 L L L) L L) L) L)) L) L
  L) L L) L) L)) L (N 20 (N 26 L (N 33 L (N 35 (N 18 L (N 27 (N 34 L L L) L L) (N 19 L (N 27 (N 34
  L L L) L L) L)) L L) L) L) (N 26 (N 33 L (N 34 (N 24 L (N 27 (N 35 L L L) L L) (N 25 L (N 27 (N
  35 L L L) L L) L)) L L) L) (N 27 (N 33 (N 23 (N 24 L (N 25 L (N 35 (N 34 L (N 18 L L (N 19 L L
  L)) L) L L) (N 31 L (N 18 (N 35 L L L) L L) L)) (N 25 L (N 32 L (N 19 (N 35 L L L) L L) L) L)) L
  (N 5 (N 24 L (N 8 (N 25 L (N 30 L (N 35 (N 34 L (N 18 L L (N 19 L L L)) L) L L) L) L) (N 18 L (N
  31 L L (N 19 (N 25 L (N 32 L L L) L) L L)) (N 32 L (N 19 (N 25 L L L) L L) L)) L) L) (N 8 (N 25
  L (N 19 L (N 32 L L (N 18 (N 24 L (N 31 L L L) L) L L)) (N 31 L (N 18 (N 24 L L L) L L) L)) L)
  (N 30 (N 24 (N 34 L (N 18 L L (N 19 L L L)) L) (N 31 L L (N 32 L (N 19 (N 25 L L L) L L) L)) L)
  L L) L) L)) L L) L L) L) L)) L (N 8 (N 17 (N 5 L (N 18 L (N 24 (N 31 L L L) L L) (N 19 L (N 20
  (N 23 L (N 24 (N 26 L L L) L L) (N 24 (N 26 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N 26
  L (N 31 (N 33 L (N 34 L L L) L) L L) L) L L) L)) (N 27 (N 34 (N 35 L (N 23 L (N 24 (N 26 L L L)
  L L) (N 24 (N 26 L (N 31 L L L) L) (N 31 (N 33 L L L) L L) L)) L) L L) L L) L) L)) (N 18 L (N 19
  L (N 20 (N 27 (N 34 L L L) L L) L L) (N 20 (N 23 L (N 24 (N 26 L (N 27 (N 31 L (N 34 L L L) L) L
  L) L) L L) (N 30 L (N 31 (N 24 L (N 27 (N 26 L (N 33 L (N 34 L L L) L) L) L L) L) L L) L)) (N 27
  (N 34 (N 35 L (N 23 L (N 24 (N 26 L L L) L L) (N 30 L (N 31 (N 33 L L L) L L) L)) L) L L) L L)
  L)) (N 19 L (N 23 L (N 25 (N 26 L (N 20 (N 27 (N 30 L (N 32 L L L) L) L L) L L) L) L L) L) L)))
  L (N 18 (N 20 L (N 24 L (N 27 (N 31 L (N 5 L L (N 34 (N 35 L L L) L L)) L) L L) L) L) (N 20 (N
  19 L (N 27 (N 26 L (N 34 (N 33 L (N 35 L L L) L) L L) L) L L) (N 24 (N 26 L (N 27 (N 31 L (N 5 L
  L (N 23 L (N 30 (N 32 L (N 34 (N 35 L L L) L L) L) L L) L)) L) L L) L) (N 27 (N 26 L (N 31 (N 5
  L L (N 23 (N 25 L (N 35 L L L) L) L L)) L L) L) L L) L)) (N 27 (N 34 (N 35 L (N 19 (N 24 L (N 31
  L L L) L) L (N 24 (N 26 L (N 31 L L L) L) (N 31 (N 33 L L L) L L) L)) L) L L) L L) L) L)) (N 17
  (N 18 L (N 19 L (N 20 (N 27 (N 34 L L L) L L) L L) (N 20 (N 24 (N 26 L (N 23 L L (N 27 (N 31 L
  (N 34 L L L) L) L L)) L) (N 27 (N 23 L L (N 26 L (N 31 (N 5 L L (N 30 L (N 33 L L L) L)) L L)
  L)) L L) L) (N 27 (N 34 (N 35 L (N 23 L (N 24 (N 26 L L L) L L) (N 24 (N 26 L (N 31 L L L) L) (N
  31 (N 33 L L L) L L) L)) L) L L) L L) L)) (N 19 L (N 25 (N 26 L (N 23 L L (N 27 (N 32 (N 33 L (N
  35 L L L) L) L L) L L)) L) L L) L)) L (N 18 (N 20 L (N 24 L (N 27 (N 31 L (N 5 L L (N 23 (N 30
  (N 35 L L L) L L) L L)) L) L L) L) L) (N 20 (N 19 L (N 27 (N 26 L (N 34 (N 33 L (N 35 L L L) L)
  L L) L) L L) (N 24 (N 26 L (N 23 L L (N 5 L (N 31 L L L) L)) L) (N 27 (N 26 L (N 31 (N 5 L L (N
  23 (N 25 L (N 35 L L L) L) L L)) L L) L) L L) L)) (N 27 (N 34 (N 35 L (N 19 (N 24 L (N 31 L L L)
  L) L (N 24 (N 26 L (N 31 L L L) L) (N 31 (N 33 L L L) L L) L)) L) L L) L L) L) L)) L))) L (N 14
  (N 12 L (N 17 (N 18 L (N 19 L (N 20 (N 27 (N 34 L L L) L L) L L) (N 20 (N 24 (N 26 L (N 23 L L
  (N 27 (N 33 (N 31 L (N 34 L L L) L) L L) L L)) L) (N 27 (N 23 L L (N 5 (N 8 L (N 26 L (N 30 L L
  (N 31 (N 33 L L L) L L)) L) L) L L)) L L) L) (N 26 (N 24 L (N 25 L (N 27 (N 23 L L (N 5 (N 8 L
  (N 30 L L (N 31 (N 33 L L L) L L)) L) L L)) L L) L) L) L L) L)) (N 19 L (N 5 (N 8 L (N 23 L L (N
  25 (N 32 L L L) L L)) (N 20 (N 23 L (N 24 (N 26 L L L) L L) (N 24 (N 26 L (N 27 (N 31 L (N 34 L
  L L) L) L L) L) (N 27 (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L) L) L L) L)) (N 26 (N 24 L (N 23
  L L (N 25 L (N 27 (N 32 (N 33 L L L) L L) L L) L)) L) L L) L)) (N 8 (N 23 L L (N 25 L (N 32 L L
  L) L)) L (N 20 (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N 26 L (N 27 (N 33 (N 31 L (N 34 L L L) L)
  L L) L L) L) (N 27 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L)) (N 26 (N 24 L (N 25 L (N 27 (N 23
  L L (N 31 (N 33 L L L) L L)) L L) L) L) L L) L)) L) L)) L (N 20 (N 18 L (N 19 L (N 27 (N 26 L (N
  33 (N 34 L L L) L L) L) L L) (N 8 (N 25 L (N 27 (N 23 L L (N 26 L (N 32 L (N 33 (N 34 L L L) L
  L) L) L)) L L) L) (N 5 (N 23 (N 24 L (N 25 L (N 27 (N 26 L (N 30 L L (N 31 (N 33 L L L) L L)) L)
  L L) L) L) L (N 24 (N 26 L (N 27 (N 31 L (N 33 (N 34 L L L) L L) L) L L) L) (N 27 (N 26 L (N 31
  (N 33 L L L) L L) L) L L) L)) L (N 23 (N 24 L (N 25 L (N 27 (N 26 L (N 30 (N 31 L L L) L L) L) L
  L) L) L) L L)) L)) (N 19 L (N 5 (N 24 (N 26 L (N 23 L L (N 27 (N 31 L (N 33 (N 34 L L L) L L) L)
  L L)) L) (N 27 (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L) L) L L) L) (N 8 (N 25 L (N 32 L L L)
  L) L (N 23 (N 24 L (N 25 L (N 27 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L) L) L (N 30 (N 31 L
  (N 24 (N 26 L (N 27 (N 32 L (N 25 (N 35 L L L) L L) L) L L) L) L L) L) L L))) L) L)) (N 26 (N 25
  L (N 27 (N 33 (N 32 L (N 35 L L L) L) L L) L L) L) L L) L)) (N 5 (N 17 (N 8 L (N 18 L (N 19 L (N
  20 (N 25 (N 32 L L L) L L) L L) (N 20 (N 23 L (N 24 (N 26 L L L) L L) (N 24 (N 26 L (N 27 (N 31
  L (N 34 L L L) L) L L) L) (N 27 (N 26 L (N 31 (N 33 L (N 34 L L L) L) L L) L) L L) L)) (N 27 (N
  34 (N 35 L (N 23 L (N 24 (N 26 L L L) L L) (N 24 (N 26 L (N 31 L L L) L) (N 31 (N 33 L L L) L L)
  L)) L) L L) L L) L)) (N 19 L (N 25 (N 32 L L L) L L) L)) (N 18 L (N 19 L (N 20 (N 27 (N 34 L L
  L) L L) L L) (N 23 L (N 24 (N 26 L (N 20 (N 27 (N 30 L (N 31 L L L) L) L L) L L) L) L L) L)) (N
  19 L (N 20 (N 23 L (N 25 (N 26 L (N 27 (N 32 L (N 34 L L L) L) L L) L) L L) (N 30 L (N 32 (N 25
  L (N 27 (N 26 L (N 33 L (N 34 L L L) L) L) L L) L) L L) L)) (N 27 (N 34 (N 35 L (N 23 L (N 25 (N
  26 L L L) L L) (N 30 L (N 32 (N 33 L L L) L L) L)) L) L L) L L) L) L))) L (N 19 (N 20 L (N 25 L
  (N 27 (N 32 L (N 8 L L (N 34 (N 35 L L L) L L)) L) L L) L) L) (N 20 (N 18 L (N 27 (N 26 L (N 34
  (N 33 L (N 35 L L L) L) L L) L) L L) (N 24 (N 26 L (N 27 (N 31 L (N 34 (N 35 L L L) L L) L) L L)
  L) (N 27 (N 26 L (N 25 (N 32 L (N 8 L L (N 23 L (N 30 (N 31 L (N 34 (N 35 L L L) L L) L) L L)
  L)) L) (N 32 (N 35 L L L) L L) L) L) L L) L)) (N 27 (N 34 (N 35 L (N 18 (N 25 L (N 32 L L L) L)
  L (N 24 (N 26 L (N 31 L L L) L) (N 31 (N 33 L L L) L L) L)) L) L L) L L) L) L)) (N 17 (N 18 L (N
  19 L (N 20 (N 27 (N 34 L L L) L L) L L) (N 24 (N 26 L (N 23 L L (N 27 (N 31 (N 33 L (N 35 L L L)
  L) L L) L L)) L) L L)) (N 19 L (N 20 (N 24 (N 26 L (N 23 L L (N 27 (N 34 L (N 31 (N 33 L L L) L
  L) L) L L)) L) (N 27 (N 23 L L (N 26 L (N 31 (N 33 L (N 34 L L L) L) L L) L)) L L) L) (N 27 (N
  34 (N 35 L (N 23 L (N 24 (N 26 L L L) L L) (N 24 (N 26 L (N 31 (N 33 L L L) L L) L) (N 31 (N 33
  L L L) L L) L)) L) L L) L L) L) L)) L (N 19 (N 20 L (N 25 L (N 27 (N 32 L (N 8 L L (N 23 (N 30
  (N 35 L L L) L L) L L)) L) L L) L) L) (N 20 (N 18 L (N 27 (N 26 L (N 34 (N 33 L (N 35 L L L) L)
  L L) L) L L) (N 24 (N 26 L (N 23 L L (N 27 (N 8 (N 25 L (N 32 L L L) L) (N 25 (N 32 L L L) L L)
  L) L L)) L) (N 27 (N 26 L (N 31 (N 33 L (N 30 L L (N 23 (N 8 L (N 25 L L L) L) L L)) L) L L) L)
  L L) L)) (N 27 (N 34 (N 35 L (N 18 (N 25 L (N 32 L L L) L) L (N 24 (N 26 L (N 23 L L (N 31 (N 33
  L L L) L L)) L) (N 31 (N 33 L L L) L L) L)) L) L L) L L) L) L)) L)) L L))))) (S 22 L L (S 29 L L
  L)))) (S 11 L (S 16 (S 22 L L (S 29 L L (N 5 (N 8 (N 9 L L (N 12 L L (N 13 (N 14 (N 17 L (N 18 L
  (N 19 L (N 27 (N 34 (N 20 L L (N 23 L (N 30 L L L) L)) L L) L L) (N 24 L (N 31 L L L) L)) (N 19
  L (N 25 (N 32 L L L) L L) L)) (N 18 L (N 19 L (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 27 L L L) L
  L) L) (N 24 L (N 31 L L L) L)) (N 19 L (N 25 (N 32 L L L) L L) L))) L (N 17 L (N 18 L (N 19 L (N
  27 (N 34 (N 20 L L (N 23 L (N 30 L L L) L)) L L) L L) (N 24 L (N 31 L L L) L)) (N 19 L (N 25 (N
  32 (N 35 L (N 23 L (N 27 (N 30 L L (N 33 L L L)) L L) (N 24 L (N 33 L L L) L)) L) L L) L L) L))
  (N 18 L (N 19 L (N 20 (N 23 L (N 27 (N 26 L (N 33 (N 32 L L (N 24 L (N 31 L L L) L)) L L) L) L
  L) (N 24 L (N 25 (N 26 L (N 27 (N 30 L (N 34 L L L) L) L L) L) L L) L)) (N 26 (N 27 L L L) L L)
  L) (N 24 L (N 31 L L L) L)) L))) L (N 14 (N 17 L (N 18 L (N 19 L (N 27 (N 34 (N 20 L L (N 23 L
  (N 30 L L L) L)) L L) L L) (N 23 L (N 27 (N 30 L L (N 20 (N 26 L (N 33 (N 31 L (N 34 L L L) L) L
  L) L) (N 26 (N 24 L (N 31 (N 33 L L L) L L) L) L L) L)) L L) (N 20 (N 24 (N 26 L (N 27 (N 31 L
  (N 34 L L L) L) L L) L) (N 27 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L) (N 26 (N 24 L (N 25 L
  (N 27 (N 31 (N 33 L L L) L L) L L) L) L) L L) L))) (N 19 L (N 25 (N 32 L L L) L L) L)) (N 19 L
  (N 18 L (N 20 (N 23 L (N 27 (N 26 L (N 33 (N 32 L L (N 30 L (N 34 L L L) L)) L L) L) L L) (N 25
  (N 26 L (N 27 (N 30 L (N 34 L L L) L) L L) L) L L)) (N 26 (N 25 L L (N 23 L (N 24 L (N 27 (N 31
  (N 33 L L L) L L) L L) L) L)) L L) L) (N 25 (N 32 L L L) L L)) L)) L L)))) L (N 9 (N 13 L L (N
  12 (N 14 (N 17 L (N 18 L (N 20 L (N 27 (N 34 (N 19 L L (N 23 L (N 30 L L L) L)) L L) L L) (N 24
  L (N 31 L L L) L)) (N 20 L (N 26 (N 33 L L L) L L) L)) (N 18 L (N 19 (N 25 L (N 32 L L L) L) (N
  25 (N 32 L L L) L L) L) (N 20 L (N 26 (N 33 L L L) L L) L))) L (N 17 L (N 18 L (N 20 L (N 27 (N
  34 (N 19 L L (N 23 L (N 30 L L L) L)) L L) L L) (N 24 L (N 31 L L L) L)) (N 20 L (N 26 (N 33 (N
  35 L (N 23 L (N 27 (N 30 L L (N 32 L L L)) L L) (N 24 L (N 32 L L L) L)) L) L L) L L) L)) (N 18
  L (N 19 (N 20 L (N 23 L (N 27 (N 25 L (N 32 (N 33 L L (N 24 L (N 31 L L L) L)) L L) L) L L) (N
  24 L (N 26 (N 25 L (N 27 (N 30 L (N 34 L L L) L) L L) L) L L) L)) (N 24 L (N 31 L L L) L)) (N 25
  (N 27 L (N 20 L L (N 24 L L L)) L) L L) L) L))) L (N 14 (N 18 L (N 20 L (N 24 L (N 27 (N 31 L L
  (N 26 (N 33 (N 30 L (N 32 L (N 35 L L L) L) L) L L) L L)) L L) (N 26 (N 23 L (N 25 L (N 27 (N 33
  (N 32 L L (N 30 L (N 35 L L L) L)) L L) L L) L) L) L L)) (N 24 L (N 31 L L L) L)) (N 20 L (N 26
  (N 33 (N 35 L (N 19 (N 23 L (N 27 (N 30 L L (N 32 L L L)) L L) (N 24 L (N 32 L L L) L)) (N 25 L
  L (N 23 L (N 30 L L L) L)) L) L) L L) L L) L)) L L))) L (N 12 (N 13 L L (N 14 (N 17 L (N 18 L (N
  20 L (N 27 (N 34 (N 19 L L (N 23 L (N 30 L L L) L)) L L) L L) (N 23 L (N 27 (N 30 L L (N 19 (N
  25 L (N 32 (N 31 L (N 34 L L L) L) L L) L) (N 25 (N 24 L (N 31 (N 32 L L L) L L) L) L L) L)) L
  L) (N 19 (N 24 (N 25 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N 25 L (N 31 (N 32 L L L) L
  L) L) L L) L) (N 25 (N 24 L (N 26 L (N 27 (N 31 (N 32 L L L) L L) L L) L) L) L L) L))) (N 20 L
  (N 26 (N 33 L L L) L L) L)) (N 20 L (N 18 L (N 19 (N 23 L (N 27 (N 25 L (N 32 (N 33 L L (N 30 L
  (N 34 L L L) L)) L L) L) L L) (N 26 (N 25 L (N 27 (N 30 L (N 34 L L L) L) L L) L) L L)) (N 25 (N
  26 L L (N 23 L (N 24 L (N 27 (N 31 (N 32 L L L) L L) L L) L) L)) L L) L) (N 26 (N 33 L L L) L
  L)) L)) L L)) L (N 14 (N 13 (N 18 L (N 19 L (N 24 L (N 27 (N 31 L L (N 25 (N 32 (N 30 L (N 33 L
  (N 35 L L L) L) L) L L) L L)) L L) (N 25 (N 23 L (N 26 L (N 27 (N 32 (N 33 L L (N 30 L (N 35 L L
  L) L)) L L) L L) L) L) L L)) (N 24 L (N 31 L L L) L)) (N 19 L (N 25 (N 32 (N 35 L (N 20 (N 23 L
  (N 27 (N 30 L L (N 33 L L L)) L L) (N 24 L (N 33 L L L) L)) (N 26 L L (N 23 L (N 30 L L L) L))
  L) L) L L) L L) L)) L (N 18 L (N 27 (N 23 L (N 34 (N 35 L (N 30 L L (N 17 L (N 19 L (N 20 L L L)
  L) L)) L) (N 31 (N 35 L (N 30 L L (N 32 (N 33 L L L) L L)) L) L (N 32 (N 33 L L L) L L)) L) (N
  17 (N 19 L (N 20 L (N 34 L L L) L) L) (N 19 (N 20 L (N 34 L L L) L) (N 20 (N 34 L L L) L L) L)
  L)) (N 24 (N 23 L (N 17 (N 19 (N 20 L L (N 25 L L (N 26 (N 30 L (N 31 L L L) L) L L))) L (N 25
  (N 26 L L (N 20 (N 30 L (N 31 L L L) L) L L)) L L)) L (N 19 (N 20 L L L) L L)) (N 25 (N 26 L L
  L) L L)) L (N 25 (N 26 L L L) L L)) L) (N 19 (N 20 L (N 26 (N 25 L (N 27 (N 32 (N 33 L L L) L L)
  L L) L) L L) L) (N 25 (N 26 L (N 20 (N 27 (N 32 (N 33 L L L) L L) L L) L L) L) L L) L))) L L))))
  L (N 8 (N 9 L L (N 12 (N 13 L L (N 14 L L L)) L (N 13 (N 14 (N 18 L (N 19 L (N 25 (N 32 L L (N
  23 L (N 27 (N 24 (N 31 L (N 34 (N 30 L (N 35 L L L) L) L L) L) (N 31 (N 30 L (N 35 L L L) L) L
  L) L) L L) (N 26 L (N 20 (N 33 L L L) L L) L))) L (N 23 (N 24 L (N 27 L L L) L) (N 27 (N 26 L (N
  20 (N 33 L L (N 17 L (N 34 L L L) L)) L (N 17 (N 30 L (N 34 L L L) L) (N 30 (N 34 L L L) L L)
  L)) L) L L) L)) (N 20 (N 24 (N 31 L (N 34 (N 27 L (N 26 L L (N 17 L (N 23 L L L) L)) L) L L) L)
  (N 27 (N 31 (N 34 L (N 33 L L (N 17 L (N 30 L L L) L)) L) L L) L L) L) (N 24 (N 26 L L (N 23 L
  (N 27 (N 31 L (N 34 (N 17 L (N 30 L L L) L) L L) L) L L) L)) (N 27 (N 26 L L (N 23 L (N 31 (N 30
  L (N 35 L L L) L) L L) L)) L L) L) L)) (N 19 L (N 25 (N 32 L L L) L L) L)) L (N 18 L (N 19 L (N
  25 (N 23 L (N 27 (N 26 L (N 20 (N 34 L (N 17 L L (N 30 (N 31 L L L) L L)) L) L (N 32 (N 30 L (N
  35 L L L) L) L L)) (N 32 (N 30 L (N 35 L L L) L) L L)) L L) (N 17 (N 30 L (N 34 (N 20 L (N 27 L
  L L) L) L L) L) (N 20 (N 27 (N 34 L L L) L L) L L) L)) L (N 32 (N 20 (N 23 (N 24 L (N 27 L L L)
  L) (N 27 (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L) L) L L) L) (N 26 (N 27 L L L) L L) L) L L))
  (N 20 (N 24 (N 26 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N 26 L (N 31 (N 33 L L L) L L)
  L) L L) L) (N 26 (N 24 L (N 27 L L L) L) L L) L)) (N 19 L (N 25 (N 23 L (N 27 (N 32 (N 30 L (N
  35 L L L) L) L L) L L) L) L L) L))) L L))) L (N 9 (N 12 (N 13 L L (N 14 (N 18 L (N 20 L (N 26 (N
  33 L L (N 23 L (N 27 (N 24 (N 31 L (N 34 (N 30 L (N 35 L L L) L) L L) L) (N 31 (N 30 L (N 35 L L
  L) L) L L) L) L L) (N 25 L (N 19 (N 32 L L L) L L) L))) L (N 23 (N 24 L (N 27 L L L) L) (N 27 (N
  25 L (N 19 (N 32 L L (N 17 L (N 34 L L L) L)) L (N 17 (N 30 L (N 34 L L L) L) (N 30 (N 34 L L L)
  L L) L)) L) L L) L)) (N 19 (N 24 (N 31 L (N 34 (N 27 L (N 25 L L (N 17 L (N 23 L L L) L)) L) L
  L) L) (N 27 (N 31 (N 34 L (N 32 L L (N 17 L (N 30 L L L) L)) L) L L) L L) L) (N 24 (N 25 L L (N
  23 L (N 27 (N 31 L (N 34 (N 17 L (N 30 L L L) L) L L) L) L L) L)) (N 27 (N 25 L L (N 23 L (N 31
  (N 30 L (N 35 L L L) L) L L) L)) L L) L) L)) (N 20 L (N 26 (N 33 L L L) L L) L)) L (N 18 L (N 20
  L (N 26 (N 23 L (N 27 (N 25 L (N 19 (N 34 L (N 17 L L (N 30 (N 31 L L L) L L)) L) L (N 32 (N 33
  (N 30 L (N 34 L L L) L) L L) L L)) (N 33 (N 30 L (N 35 L L L) L) L L)) L L) (N 17 (N 30 L (N 34
  (N 19 L (N 27 L L L) L) L L) L) (N 19 (N 27 (N 34 L L L) L L) L L) L)) L (N 33 (N 19 (N 23 (N 24
  L (N 27 L L L) L) (N 27 (N 25 L (N 32 (N 31 L (N 34 L L L) L) L L) L) L L) L) (N 25 (N 27 L L L)
  L L) L) L L)) (N 19 (N 24 (N 25 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N 25 L (N 31 (N
  32 L L L) L L) L) L L) L) (N 25 (N 24 L (N 27 L L L) L) L L) L)) (N 20 L (N 26 (N 23 L (N 27 (N
  33 (N 30 L (N 35 L L L) L) L L) L L) L) L L) L)))) L (N 13 (N 14 L L L) L L)) L L))))) L (S 22 L
  L (S 29 L L (N 5 (N 8 (N 9 L L (N 12 L L (N 13 (N 14 (N 17 L (N 18 L (N 23 L (N 27 (N 30 L L (N
  31 L (N 24 L L (N 34 (N 35 L L L) L L)) L)) L L) (N 24 L (N 27 (N 31 L L (N 30 L (N 34 (N 35 L L
  L) L L) L)) L L) L)) (N 19 (N 20 L (N 25 L (N 32 L L L) L) L) (N 25 (N 32 L L L) L L) L)) (N 18
  L (N 19 (N 20 L (N 26 (N 33 L L L) L L) L) (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L)
  L) L) L)) L (N 17 L (N 18 L (N 23 L (N 27 (N 30 L L (N 31 L (N 24 L L (N 34 (N 35 L L L) L L))
  L)) L L) (N 24 L (N 27 (N 31 L L (N 30 L (N 34 (N 35 L L L) L L) L)) L L) L)) (N 19 (N 20 L (N
  23 L (N 27 (N 25 L (N 30 L L (N 26 (N 31 L (N 32 (N 33 L L L) L L) L) L L)) L) L L) (N 24 L (N
  26 (N 25 L (N 27 (N 32 (N 33 L L L) L L) L L) L) L L) L)) L) (N 25 (N 32 (N 35 L (N 20 (N 23 L
  (N 27 (N 30 L L (N 33 L L L)) L L) (N 24 L (N 33 L L L) L)) (N 26 L L (N 33 L L L)) L) L) L L) L
  L) L)) (N 18 L (N 19 (N 20 L (N 26 (N 33 (N 35 L (N 23 L (N 27 (N 30 L L (N 32 L L L)) L L) (N
  24 L (N 25 L (N 30 L L L) L) L)) L) L L) L L) L) (N 20 (N 23 L (N 27 (N 26 L (N 33 (N 32 L L (N
  24 L (N 31 L L L) L)) L L) L) L L) (N 24 L (N 25 (N 26 L (N 27 (N 30 L (N 31 L L (N 32 (N 33 L L
  L) L L)) L) L L) L) L L) L)) (N 26 (N 25 L L (N 23 L (N 24 L (N 31 L L L) L) L)) L L) L) L) L)))
  L (N 14 (N 17 L (N 23 L (N 27 (N 30 L L (N 20 (N 26 L (N 33 (N 31 L (N 32 L (N 34 L L L) L) L) L
  L) L) (N 26 (N 33 (N 31 L (N 32 L (N 35 L L L) L) L) L L) L L) L)) L L) (N 20 (N 18 L (N 19 L (N
  25 (N 26 L (N 27 (N 32 L L (N 30 L (N 33 (N 34 L L L) L L) L)) L L) L) L L) (N 24 (N 26 L (N 27
  (N 31 L (N 33 (N 34 L L L) L L) L) L L) L) (N 27 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L)) (N
  19 L (N 25 (N 32 L L L) L L) L)) (N 26 (N 24 L (N 25 L (N 27 (N 33 (N 32 L L (N 30 L (N 35 L L
  L) L)) L L) L L) L) L) L L) L)) (N 18 (N 20 L (N 26 (N 33 (N 35 L (N 19 (N 23 L (N 27 (N 30 L L
  (N 32 L L L)) L L) (N 24 L (N 25 L (N 30 L L L) L) L)) (N 25 L L (N 23 L (N 24 L (N 31 L L L) L)
  L)) L) L) L L) L L) L) (N 19 (N 20 L (N 26 (N 33 (N 35 L (N 23 L (N 27 (N 30 L L (N 32 L L L)) L
  L) (N 24 L (N 25 L (N 30 L L L) L) L)) L) L L) L L) L) (N 20 (N 23 L (N 27 (N 26 L (N 33 (N 32 L
  L (N 30 L (N 34 L L L) L)) L L) L) L L) (N 25 (N 26 L (N 27 (N 30 L (N 32 L L (N 33 (N 34 L L L)
  L L)) L) L L) L) L L)) (N 26 (N 25 L L (N 23 L (N 24 L (N 27 (N 31 (N 33 L L L) L L) L L) L) L))
  L L) L) L) L)) L L)))) L (N 9 (N 13 L L (N 12 (N 14 (N 17 L (N 18 L (N 23 L (N 27 (N 30 L L (N
  31 L (N 24 L L (N 34 (N 35 L L L) L L)) L)) L L) (N 24 L (N 27 (N 31 L L (N 30 L (N 34 (N 35 L L
  L) L L) L)) L L) L)) (N 19 (N 20 L (N 26 (N 33 L L L) L L) L) (N 20 (N 26 L (N 33 L L L) L) (N
  26 (N 33 L L L) L L) L) L)) (N 18 L (N 19 (N 20 L (N 25 L (N 32 L L L) L) L) (N 25 (N 32 L L L)
  L L) L) L)) L (N 17 L (N 18 L (N 23 L (N 27 (N 30 L L (N 31 L (N 24 L L (N 34 (N 35 L L L) L L))
  L)) L L) (N 24 L (N 27 (N 31 L L (N 30 L (N 34 (N 35 L L L) L L) L)) L L) L)) (N 19 (N 20 L (N
  26 (N 33 (N 35 L (N 23 L (N 27 (N 30 L L (N 32 L L L)) L L) (N 24 L (N 32 L L L) L)) L) L L) L
  L) L) (N 20 (N 23 L (N 27 (N 26 L (N 30 L L (N 25 (N 31 L (N 32 (N 33 L L L) L L) L) L L)) L) L
  L) (N 24 L (N 25 (N 26 L (N 27 (N 32 (N 33 L L L) L L) L L) L) L L) L)) (N 26 (N 25 L L (N 23 L
  (N 30 L L L) L)) L L) L) L)) (N 18 L (N 19 (N 20 L (N 23 L (N 27 (N 25 L (N 32 (N 33 L L (N 24 L
  (N 31 L L L) L)) L L) L) L L) (N 24 L (N 26 (N 25 L (N 27 (N 30 L (N 31 L L (N 32 (N 33 L L L) L
  L)) L) L L) L) L L) L)) L) (N 25 (N 32 (N 35 L (N 20 (N 23 L (N 27 (N 30 L L (N 33 L L L)) L L)
  (N 24 L (N 26 L (N 30 L L L) L) L)) (N 26 L L (N 33 L L L)) L) L) L L) L L) L) L))) L (N 14 (N
  18 L (N 24 L (N 27 (N 31 L L (N 20 (N 26 L (N 33 (N 30 L (N 32 L (N 34 L L L) L) L) L L) L) (N
  26 (N 33 (N 30 L (N 32 L (N 35 L L L) L) L) L L) L L) L)) L L) (N 20 (N 17 L (N 19 L (N 25 (N 26
  L (N 27 (N 32 L L (N 31 L (N 33 (N 34 L L L) L L) L)) L L) L) L L) (N 23 (N 26 L (N 27 (N 30 L
  (N 33 (N 34 L L L) L L) L) L L) L) (N 27 (N 26 L (N 30 (N 33 L L L) L L) L) L L) L)) (N 19 L (N
  25 (N 32 L L L) L L) L)) (N 26 (N 23 L (N 25 L (N 27 (N 33 (N 32 L L (N 30 L (N 35 L L L) L)) L
  L) L L) L) L) L L) L)) (N 17 (N 20 L (N 26 (N 33 (N 35 L (N 19 (N 23 L (N 27 (N 30 L L (N 32 L L
  L)) L L) (N 24 L (N 32 L L L) L)) (N 25 L L (N 23 L (N 30 L L L) L)) L) L) L L) L L) L) (N 19 (N
  20 L (N 26 (N 33 (N 35 L (N 23 L (N 27 (N 30 L L (N 32 L L L)) L L) (N 24 L (N 32 L L L) L)) L)
  L L) L L) L) (N 20 (N 24 L (N 27 (N 26 L (N 33 (N 32 L L (N 30 L (N 34 L L L) L)) L L) L) L L)
  (N 25 (N 26 L (N 27 (N 31 L (N 32 L L (N 33 (N 34 L L L) L L)) L) L L) L) L L)) (N 26 (N 25 L L
  (N 23 L (N 24 L (N 27 (N 30 (N 33 L L L) L L) L L) L) L)) L L) L) L) L)) L L))) L (N 12 (N 13 L
  L (N 14 (N 17 L (N 23 L (N 27 (N 30 L L (N 19 (N 25 L (N 32 (N 31 L (N 33 L (N 34 L L L) L) L) L
  L) L) (N 25 (N 32 (N 31 L (N 33 L (N 35 L L L) L) L) L L) L L) L)) L L) (N 19 (N 18 L (N 20 L (N
  26 (N 25 L (N 27 (N 32 (N 34 L L L) L L) L L) L) L L) (N 24 (N 25 L (N 27 (N 31 L (N 32 (N 34 L
  L L) L L) L) L L) L) (N 27 (N 25 L (N 31 (N 32 L L L) L L) L) L L) L)) (N 20 L (N 26 (N 33 L L
  L) L L) L)) (N 25 (N 24 L (N 26 L (N 27 (N 32 (N 33 L L (N 30 L (N 35 L L L) L)) L L) L L) L) L)
  L L) L)) (N 18 (N 19 L (N 25 (N 32 (N 35 L (N 20 (N 23 L (N 27 (N 30 L L (N 33 L L L)) L L) (N
  24 L (N 26 L (N 30 L L L) L) L)) (N 26 L L (N 23 L (N 24 L (N 31 L L L) L) L)) L) L) L L) L L)
  L) (N 19 (N 20 L (N 23 L (N 27 (N 25 L (N 32 (N 33 L L (N 30 L (N 34 L L L) L)) L L) L) L L) (N
  26 (N 25 L (N 27 (N 30 L (N 32 (N 34 L L L) L L) L) L L) L) L L)) L) (N 25 (N 32 (N 35 L (N 20
  (N 23 L (N 27 (N 30 L L (N 33 L L L)) L L) (N 24 L (N 26 L (N 30 L L L) L) L)) (N 26 L L (N 23 L
  (N 24 L (N 31 L L L) L) L)) L) L) L L) L L) L) L)) L L)) L (N 14 (N 13 (N 18 L (N 24 L (N 27 (N
  31 L L (N 19 (N 25 L (N 32 (N 30 L (N 33 L (N 34 L L L) L) L) L L) L) (N 25 (N 32 (N 30 L (N 33
  L (N 35 L L L) L) L) L L) L L) L)) L L) (N 19 (N 17 L (N 20 L (N 26 (N 25 L (N 27 (N 32 (N 34 L
  L L) L L) L L) L) L L) (N 23 (N 25 L (N 27 (N 30 L (N 32 (N 34 L L L) L L) L) L L) L) (N 27 (N
  25 L (N 30 (N 32 L L L) L L) L) L L) L)) (N 20 L (N 26 (N 33 L L L) L L) L)) (N 25 (N 23 L (N 26
  L (N 27 (N 32 (N 33 L L (N 30 L (N 35 L L L) L)) L L) L L) L) L) L L) L)) (N 17 (N 19 L (N 25 (N
  32 (N 35 L (N 20 (N 23 L (N 27 (N 30 L L (N 33 L L L)) L L) (N 24 L (N 33 L L L) L)) (N 26 L L
  (N 23 L (N 30 L L L) L)) L) L) L L) L L) L) (N 19 (N 20 L (N 24 L (N 27 (N 25 L (N 32 (N 33 L L
  (N 30 L (N 34 L L L) L)) L L) L) L L) (N 26 (N 25 L (N 27 (N 31 L (N 32 (N 34 L L L) L L) L) L
  L) L) L L)) L) (N 25 (N 32 (N 35 L (N 20 (N 23 L (N 27 (N 30 L L (N 33 L L L)) L L) (N 24 L (N
  33 L L L) L)) (N 26 L L (N 23 L (N 30 L L L) L)) L) L) L L) L L) L) L)) L (N 27 (N 34 (N 35 L (N
  17 (N 18 L (N 19 L (N 20 L (N 23 L (N 30 L L (N 25 (N 26 L L L) L L)) (N 25 (N 26 L L L) L L))
  (N 23 L (N 30 L L L) L)) (N 20 L (N 23 L (N 30 L L L) L) L)) (N 19 L (N 20 L (N 25 (N 26 L L L)
  L L) L) L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L (N 25 (N 26 L L L) L L)) (N 25 (N 26 L L L)
  L L)) (N 24 L (N 31 L L L) L)) (N 20 L (N 24 L (N 31 L L L) L) L)) (N 19 (N 20 L (N 25 L (N 32 L
  L (N 30 (N 31 L L L) L L)) (N 26 (N 32 L (N 23 (N 24 L L L) L L) L) L L)) (N 23 (N 24 L (N 30 L
  L L) L) (N 30 (N 31 L L L) L L) L)) (N 20 (N 25 (N 26 L (N 33 L L (N 30 (N 31 L L L) L L)) (N 33
  L (N 23 (N 24 L L L) L L) L)) L (N 26 L (N 30 (N 31 L L L) L L) L)) L (N 23 (N 24 L (N 30 L L L)
  L) (N 30 (N 31 L L L) L L) L)) (N 20 (N 23 (N 24 L (N 30 L L L) L) (N 30 (N 31 L L L) L L) L) (N
  23 (N 24 L (N 30 L L L) L) (N 30 (N 31 L L L) L L) L) L)) (N 19 (N 20 L (N 25 L (N 32 L L L) L)
  L) (N 25 (N 26 L (N 33 L L L) L) L L) L)) (N 18 (N 19 L (N 20 L (N 25 (N 26 L L L) L L) L) L) (N
  19 (N 20 L (N 25 L (N 32 L L L) L) L) (N 25 (N 26 L (N 33 L L L) L) L L) L) L)) L) (N 35 (N 17
  (N 18 L (N 31 L L (N 30 L (N 19 (N 20 L L L) L L) L)) (N 31 L (N 19 (N 20 L L L) L L) L)) (N 30
  (N 18 L (N 31 L L (N 19 (N 20 L L L) L L)) (N 31 L (N 19 (N 20 L L L) L L) L)) L (N 32 (N 33 L L
  L) L L)) (N 18 (N 30 L (N 19 (N 20 L L L) L L) L) (N 32 (N 33 L L L) L L) L)) (N 17 (N 18 L (N
  23 L (N 30 L L (N 31 (N 32 (N 33 L L L) L L) L L)) (N 30 L (N 19 (N 20 L L L) L L) L)) (N 19 (N
  20 L (N 25 L (N 26 (N 30 L L (N 23 L (N 24 (N 31 L L L) L L) L)) L L) L) L) (N 25 (N 26 L (N 20
  (N 30 L L (N 23 L (N 24 (N 31 L L L) L L) L)) L L) L) L L) L)) (N 30 (N 23 L (N 31 L (N 18 (N 24
  L L (N 19 (N 20 L L L) L L)) L (N 19 (N 20 L L L) L L)) (N 32 (N 33 L L L) L L)) (N 32 (N 33 L L
  L) L L)) L (N 32 (N 33 L L L) L L)) (N 18 (N 19 (N 20 L (N 25 L (N 26 (N 30 (N 32 L L L) L L) L
  L) L) L) (N 25 (N 26 L (N 20 (N 30 (N 33 L L L) L L) L L) L) L L) L) (N 32 (N 33 L L L) L L) L))
  L) L) (N 34 (N 35 (N 17 (N 18 L (N 24 L L (N 23 L (N 19 (N 20 L L L) L L) L)) (N 24 L (N 19 (N
  20 L L L) L L) L)) (N 23 (N 18 L (N 24 L L (N 19 (N 20 L L L) L L)) (N 24 L (N 19 (N 20 L L L) L
  L) L)) L (N 25 (N 26 L L L) L L)) (N 18 (N 23 L (N 19 (N 20 L L L) L L) L) (N 25 (N 26 L L L) L
  L) L)) (N 17 (N 18 L (N 23 L (N 30 L L (N 19 (N 20 L L L) L L)) (N 24 (N 25 (N 26 L L L) L L) L
  L)) (N 19 (N 20 L (N 23 L L (N 24 (N 25 L L L) L L)) L) (N 23 L L (N 24 (N 25 (N 26 L L L) L L)
  L L)) L)) (N 23 (N 24 L (N 18 (N 31 L L (N 19 (N 20 L L L) L L)) L (N 19 (N 20 L L L) L L)) (N
  25 (N 26 L L L) L L)) L (N 25 (N 26 L L L) L L)) (N 18 (N 19 (N 20 L (N 23 (N 25 L L L) L L) L)
  (N 23 (N 24 L L (N 25 (N 26 L L L) L L)) L L) L) (N 25 (N 26 L L L) L L) L)) L) (N 35 (N 17 (N
  18 L (N 19 (N 20 L L (N 23 L (N 24 (N 31 L L L) L L) L)) L (N 20 (N 23 L (N 24 (N 31 L L L) L L)
  L) L L)) (N 19 (N 20 L (N 23 L L (N 30 L L L)) L) (N 20 (N 23 L L (N 30 L L L)) L L) L)) (N 18
  (N 19 (N 20 L L (N 23 (N 30 L L L) L L)) L (N 20 (N 23 (N 30 L L L) L L) L L)) L (N 19 (N 20 L L
  L) L L)) (N 18 (N 19 (N 20 L (N 23 (N 25 L L L) L L) L) (N 20 (N 23 (N 26 L L L) L L) L L) L) (N
  19 (N 20 L L L) L L) L)) L L) L) L)) L L)))) L (N 8 (N 9 L L (N 12 (N 13 L L (N 14 L L L)) L (N
  13 (N 14 (N 27 (N 34 (N 35 L (N 17 (N 18 L (N 19 L (N 20 L (N 26 L L (N 23 L (N 30 L L L) L)) (N
  23 L (N 30 L L L) L)) (N 20 L (N 26 L L (N 23 L (N 30 L L L) L)) L)) (N 19 L (N 20 L (N 23 L (N
  30 L L L) L) L) L)) (N 18 (N 19 L (N 25 L L (N 24 L (N 31 L L L) L)) (N 20 L (N 24 L (N 31 L L
  L) L) L)) (N 19 (N 20 L (N 24 L (N 31 L L (N 32 L L L)) (N 25 L (N 31 L L L) L)) (N 23 (N 30 L
  (N 24 L L (N 25 L L L)) L) (N 30 (N 31 L L (N 32 L L L)) L L) L)) (N 20 (N 23 L (N 30 L L (N 33
  L L L)) (N 25 (N 26 L (N 30 L L L) L) L L)) L (N 23 (N 25 L L (N 24 L (N 30 L L L) L)) (N 30 (N
  25 L L (N 31 L L L)) L L) L)) (N 20 (N 23 L (N 30 L L (N 33 L L L)) (N 26 L (N 30 L L L) L)) (N
  24 (N 26 L L (N 23 L (N 31 L L L) L)) (N 31 (N 26 L L (N 30 L L L)) L L) L) L)) (N 19 (N 20 L (N
  24 L (N 31 L L L) L) L) (N 25 (N 32 L L L) L L) L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L)
  L) L) L) (N 19 (N 20 L (N 24 L (N 31 L L L) L) L) (N 20 (N 23 L (N 30 L L L) L) (N 26 (N 33 L L
  L) L L) L) L) L)) L) (N 35 (N 17 (N 18 L (N 32 L L (N 30 L (N 19 L L (N 20 (N 31 L L L) L L))
  L)) (N 19 L (N 30 L L L) L)) (N 30 (N 32 L L (N 31 L (N 18 (N 33 L L L) L L) L)) L (N 32 (N 33 L
  L L) L L)) (N 18 (N 20 L (N 31 L L L) L) (N 31 (N 33 L L L) L L) L)) (N 17 (N 18 L (N 19 L (N 30
  L L (N 20 (N 33 L L L) L L)) (N 31 (N 24 L (N 33 L L (N 23 L (N 30 L L L) L)) L) L L)) (N 19 L
  (N 30 L L L) L)) (N 30 (N 32 L L (N 31 L (N 18 (N 24 L L L) L L) L)) L (N 32 (N 33 L L L) L L))
  (N 18 (N 20 L (N 31 L L L) L) (N 31 (N 33 L L L) L L) L)) L) L) (N 34 (N 35 (N 17 (N 18 L (N 25
  L L (N 23 L (N 19 L L (N 20 (N 24 L L L) L L)) L)) (N 19 L (N 23 L L L) L)) (N 23 (N 25 L L (N
  24 L (N 18 (N 26 L L L) L L) L)) L (N 25 (N 26 L L L) L L)) (N 18 (N 20 L (N 24 L L L) L) (N 24
  (N 26 L L L) L L) L)) (N 17 (N 18 L (N 19 L (N 23 L L (N 20 (N 26 L L L) L L)) (N 24 (N 26 L L
  (N 23 L (N 30 L L L) L)) L L)) (N 19 L (N 23 L L L) L)) (N 23 (N 25 L L (N 24 L (N 18 (N 31 L L
  L) L L) L)) L (N 25 (N 26 L L L) L L)) (N 18 (N 20 L (N 24 L L L) L) (N 24 (N 26 L L L) L L) L))
  L) (N 35 (N 17 (N 18 L (N 19 L L (N 20 (N 24 (N 31 L L L) L L) L L)) (N 19 L (N 23 L L L) L)) (N
  18 (N 20 L L (N 19 (N 23 (N 30 L L L) L L) L L)) L (N 19 (N 20 L L L) L L)) (N 18 (N 20 L (N 24
  L L L) L) (N 19 (N 20 L L L) L L) L)) L L) L) L) L (N 27 (N 34 (N 35 L (N 17 (N 18 L (N 19 L (N
  20 L (N 23 L (N 30 L L (N 26 (N 24 L (N 31 L L L) L) L L)) (N 25 (N 26 (N 24 L (N 31 L L L) L) L
  L) L L)) (N 23 L (N 30 L L L) L)) (N 20 L (N 26 (N 24 L (N 31 L L L) L) L L) L)) (N 19 L (N 20 L
  (N 23 L (N 30 L L L) L) L) L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L (N 25 (N 23 L (N 30 L L
  L) L) L L)) (N 25 (N 23 L (N 30 L L L) L) L L)) (N 25 (N 23 L (N 30 L L L) L) L L)) (N 20 L (N
  24 L (N 31 L L L) L) L)) (N 19 (N 20 L (N 25 L (N 32 L L (N 26 (N 31 L L L) L L)) (N 26 (N 24 L
  (N 31 L L L) L) L L)) (N 25 L (N 32 L L L) L)) (N 20 (N 25 (N 23 L (N 30 L L (N 33 L L L)) (N 26
  L (N 30 L L L) L)) L (N 26 L (N 33 L L L) L)) L (N 25 (N 23 L (N 30 L L L) L) L L)) (N 20 (N 26
  L (N 33 L L L) L) (N 26 (N 24 L (N 31 L L L) L) L L) L)) (N 19 (N 20 L (N 25 L (N 32 L L L) L)
  L) (N 25 (N 23 L (N 30 L L L) L) L L) L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L) (N
  19 (N 20 L (N 26 (N 24 L (N 31 L L L) L) L L) L) (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 24 L (N
  31 L L L) L) L L) L) L) L)) L) (N 35 (N 17 (N 18 L (N 32 L L (N 19 L (N 30 L L L) L)) (N 19 L (N
  30 L L L) L)) (N 30 (N 32 L L (N 19 L (N 31 L L L) L)) L (N 32 (N 33 (N 18 L (N 31 L L L) L) L
  L) L L)) (N 18 (N 20 L (N 31 L L L) L) (N 31 (N 33 L L L) L L) L)) (N 17 (N 18 L (N 19 L (N 30 L
  L (N 20 (N 23 L (N 26 L (N 24 (N 31 L L L) L L) L) L) L L)) (N 31 (N 33 L L L) L L)) (N 19 L (N
  30 L L L) L)) (N 30 (N 32 L L (N 31 L (N 18 (N 20 L L L) L L) L)) L (N 32 (N 33 (N 31 L (N 18 (N
  20 L L L) L L) L) L L) L L)) (N 18 (N 20 L (N 31 L L L) L) (N 31 (N 33 L L L) L L) L)) L) L) (N
  34 (N 35 (N 17 (N 18 L (N 25 L L (N 19 L (N 23 L L L) L)) (N 19 L (N 23 L L L) L)) (N 23 (N 25 L
  L (N 19 L (N 24 L L L) L)) L (N 25 (N 26 (N 18 L (N 24 L L L) L) L L) L L)) (N 18 (N 20 L (N 24
  L L L) L) (N 24 (N 26 L L L) L L) L)) (N 17 (N 18 L (N 19 L (N 23 L L (N 20 (N 24 (N 26 L L L) L
  L) L L)) (N 24 (N 26 L L L) L L)) (N 19 L (N 23 L L L) L)) (N 23 (N 25 L L (N 24 L (N 18 (N 20 L
  L L) L L) L)) L (N 25 (N 26 (N 24 L (N 18 (N 20 L L L) L L) L) L L) L L)) (N 18 (N 20 L (N 24 L
  L L) L) (N 24 (N 26 L L L) L L) L)) L) (N 35 (N 17 (N 18 L (N 19 L L (N 20 (N 24 (N 26 L L L) L
  L) L L)) (N 19 L (N 23 L L L) L)) (N 18 (N 20 L L (N 19 (N 23 (N 25 L L L) L L) L L)) L (N 19 (N
  20 (N 23 (N 25 L L L) L L) L L) L L)) (N 18 (N 20 L (N 24 L L L) L) (N 19 (N 20 (N 24 (N 26 L L
  L) L L) L L) L L) L)) L L) L) L)) L L))) L (N 9 (N 12 (N 13 L L (N 14 (N 27 (N 34 (N 35 L (N 17
  (N 18 L (N 19 L (N 25 L L (N 23 L (N 30 L L L) L)) (N 20 L (N 23 L (N 30 L L L) L) L)) (N 19 L
  (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 18 (N 19 L (N 20 L (N 26 L L (N 24 L (N 31 L L L) L))
  (N 24 L (N 31 L L L) L)) (N 20 L (N 26 L L (N 24 L (N 31 L L L) L)) L)) (N 19 (N 20 L (N 23 L (N
  30 L L (N 32 L L L)) (N 25 L (N 30 L L L) L)) (N 23 L (N 30 L L (N 32 L L L)) (N 25 L (N 30 L L
  L) L))) (N 20 (N 24 L (N 31 L L (N 33 L L L)) (N 25 (N 26 L (N 31 L L L) L) L L)) L (N 24 (N 25
  L L (N 23 L (N 31 L L L) L)) (N 31 (N 25 L L (N 30 L L L)) L L) L)) (N 20 (N 23 (N 30 L (N 24 L
  L (N 26 L L L)) L) (N 30 (N 31 L L (N 33 L L L)) L L) L) (N 23 (N 26 L L (N 24 L (N 30 L L L)
  L)) (N 30 (N 26 L L (N 31 L L L)) L L) L) L)) (N 19 (N 20 L (N 23 L (N 30 L L L) L) L) (N 20 (N
  24 L (N 31 L L L) L) (N 26 (N 33 L L L) L L) L) L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L)
  L) L) L) (N 19 (N 20 L (N 23 L (N 30 L L L) L) L) (N 25 (N 32 L L L) L L) L) L)) L) (N 35 (N 17
  (N 18 L (N 33 L L (N 30 L (N 20 L L (N 19 (N 31 L L L) L L)) L)) (N 20 L (N 30 L L L) L)) (N 30
  (N 33 L L (N 31 L (N 18 (N 32 L L L) L L) L)) L (N 32 (N 33 L L L) L L)) (N 18 (N 19 L (N 31 L L
  L) L) (N 31 (N 32 L L L) L L) L)) (N 17 (N 18 L (N 20 L (N 30 L L (N 19 (N 32 L L L) L L)) (N 31
  (N 24 L (N 32 L L (N 23 L (N 30 L L L) L)) L) L L)) (N 20 L (N 30 L L L) L)) (N 30 (N 33 L L (N
  31 L (N 18 (N 24 L L L) L L) L)) L (N 32 (N 33 L L L) L L)) (N 18 (N 19 L (N 31 L L L) L) (N 31
  (N 32 L L L) L L) L)) L) L) (N 34 (N 35 (N 17 (N 18 L (N 26 L L (N 23 L (N 20 L L (N 19 (N 24 L
  L L) L L)) L)) (N 20 L (N 23 L L L) L)) (N 23 (N 26 L L (N 24 L (N 18 (N 25 L L L) L L) L)) L (N
  25 (N 26 L L L) L L)) (N 18 (N 19 L (N 24 L L L) L) (N 24 (N 25 L L L) L L) L)) (N 17 (N 18 L (N
  20 L (N 23 L L (N 19 (N 25 L L L) L L)) (N 24 (N 25 L L (N 23 L (N 30 L L L) L)) L L)) (N 20 L
  (N 23 L L L) L)) (N 23 (N 26 L L (N 24 L (N 18 (N 31 L L L) L L) L)) L (N 25 (N 26 L L L) L L))
  (N 18 (N 19 L (N 24 L L L) L) (N 24 (N 25 L L L) L L) L)) L) (N 35 (N 17 (N 18 L (N 20 L L (N 19
  (N 24 (N 31 L L L) L L) L L)) (N 20 L (N 23 L L L) L)) (N 18 (N 19 L L (N 20 (N 23 (N 30 L L L)
  L L) L L)) L (N 19 (N 20 L L L) L L)) (N 18 (N 19 L (N 24 L L L) L) (N 19 (N 20 L L L) L L) L))
  L L) L) L) L (N 27 (N 34 (N 35 L (N 17 (N 18 L (N 19 L (N 20 L (N 23 L (N 30 L L (N 25 (N 24 L
  (N 31 L L L) L) L L)) (N 25 (N 24 L (N 31 L L L) L) L L)) (N 25 (N 24 L (N 31 L L L) L) L L)) (N
  20 L (N 23 L (N 30 L L L) L) L)) (N 19 L (N 20 L (N 23 L (N 30 L L L) L) L) L)) (N 18 (N 19 L (N
  20 L (N 24 L (N 31 L L (N 26 (N 23 L (N 30 L L L) L) L L)) (N 25 (N 26 (N 23 L (N 30 L L L) L) L
  L) L L)) (N 24 L (N 31 L L L) L)) (N 20 L (N 26 (N 23 L (N 30 L L L) L) L L) L)) (N 19 (N 20 L
  (N 25 L (N 32 L L (N 26 (N 30 L L L) L L)) (N 26 (N 23 L (N 30 L L L) L) L L)) (N 25 L (N 32 L L
  L) L)) (N 20 (N 25 (N 24 L (N 31 L L (N 33 L L L)) (N 26 L (N 31 L L L) L)) L (N 26 L (N 33 L L
  L) L)) L (N 25 (N 24 L (N 31 L L L) L) L L)) (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 23 L (N 30 L
  L L) L) L L) L)) (N 19 (N 20 L (N 26 (N 23 L (N 30 L L L) L) L L) L) (N 20 (N 26 L (N 33 L L L)
  L) (N 26 (N 23 L (N 30 L L L) L) L L) L) L)) (N 18 (N 19 L (N 20 L (N 24 L (N 31 L L L) L) L) L)
  (N 19 (N 20 L (N 25 L (N 32 L L L) L) L) (N 25 (N 24 L (N 31 L L L) L) L L) L) L)) L) (N 35 (N
  17 (N 18 L (N 33 L L (N 20 L (N 30 L L L) L)) (N 20 L (N 30 L L L) L)) (N 30 (N 33 L L (N 20 L
  (N 31 L L L) L)) L (N 32 (N 18 L (N 31 L L L) L) L L)) (N 18 (N 19 L (N 31 L L L) L) (N 31 (N 32
  L L L) L L) L)) (N 17 (N 18 L (N 20 L (N 30 L L (N 19 (N 23 L (N 25 L (N 24 (N 31 L L L) L L) L)
  L) L L)) (N 31 (N 32 L L L) L L)) (N 20 L (N 30 L L L) L)) (N 30 (N 33 L L (N 31 L (N 18 (N 19 L
  L L) L L) L)) L (N 32 (N 31 L (N 18 (N 19 L L L) L L) L) L L)) (N 18 (N 19 L (N 31 L L L) L) (N
  31 (N 32 L L L) L L) L)) L) L) (N 34 (N 35 (N 17 (N 18 L (N 26 L L (N 20 L (N 23 L L L) L)) (N
  20 L (N 23 L L L) L)) (N 23 (N 26 L L (N 20 L (N 24 L L L) L)) L (N 25 (N 18 L (N 24 L L L) L) L
  L)) (N 18 (N 19 L (N 24 L L L) L) (N 24 (N 25 L L L) L L) L)) (N 17 (N 18 L (N 20 L (N 23 L L (N
  19 (N 24 (N 25 L L L) L L) L L)) (N 24 (N 25 L L L) L L)) (N 20 L (N 23 L L L) L)) (N 23 (N 26 L
  L (N 24 L (N 18 (N 19 L L L) L L) L)) L (N 25 (N 24 L (N 18 (N 19 L L L) L L) L) L L)) (N 18 (N
  19 L (N 24 L L L) L) (N 24 (N 25 L L L) L L) L)) L) (N 35 (N 17 (N 18 L (N 20 L L (N 19 (N 24 (N
  25 L L L) L L) L L)) (N 20 L (N 23 L L L) L)) (N 18 (N 19 L L (N 20 (N 23 (N 26 L L L) L L) L
  L)) L (N 19 (N 20 (N 23 (N 26 L L L) L L) L L) L L)) (N 18 (N 19 L (N 24 L L L) L) (N 19 (N 20
  (N 24 (N 25 L L L) L L) L L) L L) L)) L L) L) L))) L (N 13 (N 14 L L L) L L)) L L)))))) (S 16 (S
  22 L (S 29 L L (N 26 (N 5 (N 8 (N 9 L L (N 12 L L (N 23 L L (N 13 (N 24 L L (N 25 L L L)) L (N
  14 (N 25 L L L) L L))))) L (N 9 (N 13 L L (N 24 L L (N 12 (N 20 L (N 23 L L (N 25 L L L)) L) L
  (N 14 (N 25 L L L) L L)))) L (N 12 (N 13 L L (N 14 (N 20 L (N 23 L L (N 25 L L L)) L) L L)) L (N
  14 (N 25 L L (N 18 L (N 23 (N 24 L L L) L L) L)) L L)))) L (N 8 (N 9 L L (N 12 (N 13 L L (N 14 L
  L L)) L (N 13 (N 24 L L (N 18 L (N 19 L (N 23 (N 25 L L L) L L) L) L)) L L))) L (N 9 (N 12 (N 13
  L L (N 20 L (N 23 L L (N 18 L (N 24 (N 25 L L L) L L) L)) L)) L (N 13 (N 14 L L L) L L)) L L)))
  L L)) (S 29 L L (N 5 (N 8 (N 9 L L (N 12 L L (N 13 (N 14 (N 17 L (N 18 L (N 19 L (N 20 (N 26 L
  (N 27 (N 34 L L L) L L) L) L L) (N 24 L (N 31 L L L) L)) (N 19 L (N 25 (N 32 L L L) L L) L)) (N
  18 L (N 19 L (N 20 (N 26 L (N 27 (N 33 L (N 34 L L L) L) L L) L) (N 27 (N 26 L (N 33 (N 34 L L
  L) L L) L) L L) L) (N 24 L (N 31 L L L) L)) (N 19 L (N 25 (N 32 L L L) L L) L))) L (N 24 L (N 31
  L (N 18 L L (N 17 L (N 19 L (N 25 (N 26 L (N 27 (N 32 (N 35 L L L) L L) L L) L) L L) L) L)) L)
  L)) L (N 14 (N 17 L (N 18 L (N 19 L (N 20 (N 25 (N 32 L L L) L L) L L) (N 20 (N 23 L (N 27 (N 26
  L (N 30 L L (N 34 L (N 31 (N 33 L L L) L L) L)) L) L L) (N 24 (N 26 L (N 27 (N 31 L (N 34 L L L)
  L) L L) L) (N 27 (N 26 L (N 31 (N 33 L (N 34 L L L) L) L L) L) L L) L)) (N 27 (N 34 (N 35 L (N
  23 L (N 30 L L (N 31 (N 33 L L L) L L)) (N 24 (N 26 L (N 31 L L L) L) (N 30 L L (N 31 (N 33 L L
  L) L L)) L)) L) L L) L L) L)) (N 19 L (N 25 (N 32 L L L) L L) L)) (N 19 L (N 25 (N 32 L L L) L
  L) L)) L L)))) L (N 9 (N 13 L L (N 12 (N 20 L (N 14 (N 17 L (N 18 L (N 27 (N 34 (N 19 L L (N 23
  L (N 30 L L L) L)) L L) L L) (N 23 L (N 27 (N 30 L L (N 25 L (N 19 (N 32 L L L) L L) L)) L L) (N
  24 L (N 27 (N 25 L (N 19 (N 32 L L L) L L) L) L L) L))) (N 18 L (N 19 (N 25 L (N 32 L L L) L) (N
  25 (N 27 L L L) L L) L) (N 19 (N 25 L (N 32 L L L) L) (N 25 (N 32 L L L) L L) L))) L (N 23 L (N
  30 L (N 17 L L (N 18 L (N 35 (N 19 (N 24 L (N 27 (N 34 L L L) L L) (N 25 (N 26 L (N 27 L L L) L)
  (N 27 (N 32 (N 33 L (N 34 L L L) L) L L) L L) L)) (N 25 (N 27 L L L) L L) L) L L) L)) L) L)) L)
  L (N 14 (N 20 L (N 18 L (N 24 L (N 27 (N 25 L (N 31 L L (N 32 (N 19 L L (N 23 L (N 26 (N 33 L (N
  34 L L L) L) L L) L)) L L)) L) L L) (N 23 (N 26 L (N 27 L L L) L) (N 25 (N 26 L (N 27 L L L) L)
  (N 27 (N 32 (N 19 L L (N 33 L (N 34 L L L) L)) L L) L L) L) L)) (N 19 (N 25 L (N 32 L L L) L) (N
  25 (N 32 L L L) L L) L)) L) L L))) L (N 12 (N 13 L L (N 14 (N 20 L (N 17 L (N 18 L (N 27 (N 34
  (N 19 L L (N 23 L (N 30 L L L) L)) L L) L L) (N 19 (N 23 L (N 27 (N 25 L (N 30 L L (N 32 (N 31 L
  (N 34 L L L) L) L L)) L) L L) (N 24 (N 25 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N 25 L
  (N 32 (N 31 L (N 34 L L L) L) L L) L) L L) L)) (N 25 (N 24 L (N 26 L (N 27 (N 32 (N 33 L L L) L
  L) L L) L) L) L L) L)) (N 18 L (N 19 (N 23 L (N 25 (N 26 L (N 27 L L L) L) (N 27 (N 32 (N 33 L
  (N 34 L L L) L) L L) L L) L) (N 30 L (N 24 (N 25 L (N 27 (N 32 (N 33 L (N 34 L L L) L) L L) L L)
  L) (N 27 (N 25 L (N 32 (N 31 L L (N 33 L (N 34 L L L) L)) L L) L) L L) L) L)) (N 25 (N 26 L (N
  27 (N 32 (N 33 L L L) L L) L L) L) L L) L) (N 19 (N 23 L (N 24 (N 25 L (N 27 (N 31 L (N 34 L L
  L) L) L L) L) (N 27 (N 25 L (N 26 (N 32 (N 31 L (N 34 L L L) L) L L) L L) L) L L) L) (N 30 L (N
  24 (N 25 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N 25 L (N 32 (N 31 L (N 34 L L L) L) L
  L) L) L L) L) L)) (N 25 (N 24 L (N 26 L (N 27 (N 32 (N 33 L L L) L L) L L) L) L) L L) L))) L) L
  L)) L (N 14 (N 13 (N 18 L (N 19 L (N 25 (N 26 L (N 27 (N 32 (N 33 L (N 35 L L L) L) L L) L L) L)
  L L) (N 24 L (N 31 L L L) L)) (N 19 L (N 25 (N 26 L (N 27 (N 32 (N 33 L (N 35 L L L) L) L L) L
  L) L) L L) L)) L (N 18 L (N 20 (N 19 L (N 25 (N 26 L (N 27 (N 32 (N 33 L (N 34 L L L) L) L L) L
  L) L) L L) (N 17 (N 23 L (N 27 L (N 24 (N 26 L L L) L L) L) L) (N 23 (N 24 L (N 27 L L L) L) (N
  27 (N 26 L (N 30 (N 31 L (N 34 L L L) L) L L) L) L L) L) L)) (N 25 (N 26 L (N 27 (N 33 (N 32 L
  (N 34 L L L) L) L L) L L) L) (N 27 (N 32 (N 33 L (N 26 (N 34 L L L) L L) L) L L) L L) L) L) (N
  19 (N 20 L (N 24 (N 25 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N 25 L (N 32 (N 31 L (N 34
  L L L) L) L L) L) L L) L) L) (N 25 (N 26 L (N 27 (N 32 (N 33 L (N 35 L L L) L) L L) L L) L) L L)
  L))) L L)))) L (N 8 (N 9 L L (N 12 (N 13 L L (N 14 L L L)) L (N 13 (N 14 (N 18 L (N 19 L (N 20
  (N 26 L (N 27 (N 33 L (N 34 L L L) L) L L) L) (N 27 (N 26 L (N 33 (N 34 L L L) L L) L) L L) L)
  (N 20 (N 26 L (N 27 (N 33 L (N 34 L L L) L) L L) L) (N 24 (N 26 L (N 27 (N 31 L (N 33 (N 34 L L
  L) L L) L) L L) L) (N 27 (N 26 L (N 31 (N 33 L L L) L L) L) L L) L) L)) (N 19 L (N 25 (N 32 L L
  L) L L) L)) L (N 18 L (N 19 L (N 20 (N 24 (N 26 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N
  26 L (N 31 (N 33 L (N 34 L L L) L) L L) L) L L) L) (N 27 (N 26 L (N 33 (N 34 L L L) L L) L) L L)
  L) (N 20 (N 24 (N 26 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N 26 L (N 31 (N 33 L (N 34 L
  L L) L) L L) L) L L) L) (N 24 (N 26 L (N 27 (N 31 L (N 33 (N 34 L L L) L L) L) L L) L) (N 27 (N
  26 L (N 31 (N 33 L L L) L L) L) L L) L) L)) (N 19 L (N 25 (N 23 L (N 27 (N 26 L (N 32 (N 30 L (N
  35 L L L) L) L L) L) L L) L) L L) L))) L L))) L (N 9 (N 12 (N 13 L L (N 20 L (N 14 (N 18 L (N 23
  (N 26 L (N 27 L L L) L) (N 26 (N 33 L (N 34 (N 30 L (N 27 (N 35 L L L) L L) L) L L) L) (N 27 (N
  33 (N 30 L (N 34 (N 35 L L L) L L) L) L L) L L) L) L) (N 17 (N 23 L (N 30 L (N 35 (N 24 (N 31 L
  (N 34 L L L) L) (N 27 (N 31 L (N 34 L L L) L) L L) L) L L) L) L) (N 23 (N 24 L (N 27 L L L) L)
  (N 27 (N 30 (N 31 L (N 34 L L L) L) L L) L L) L) L)) L (N 18 L (N 23 (N 26 L (N 27 L L L) L) (N
  26 (N 27 (N 25 L (N 19 (N 34 L (N 17 L L (N 31 (N 32 L L L) L L)) L) L (N 32 (N 34 L (N 17 (N 30
  L (N 31 L L (N 24 (N 33 L L L) L L)) L) L L) L) L L)) (N 17 (N 19 L (N 34 L L L) L) (N 19 (N 34
  L L L) L L) L)) (N 34 (N 30 L (N 33 (N 35 L L L) L L) L) L L) L) (N 27 (N 33 (N 30 L (N 34 (N 35
  L L L) L L) L) L L) L L) L) L) (N 17 (N 23 L (N 30 L (N 35 (N 24 (N 31 L (N 34 L L L) L) (N 27
  (N 31 L (N 34 L L L) L) L L) L) L L) L) L) (N 23 (N 24 L (N 27 L L L) L) (N 27 (N 30 (N 31 L (N
  34 L L L) L) L L) L L) L) L))) L)) L (N 13 (N 14 L L L) L L)) L L))))) (S 22 L L (S 29 L L (N 20
  (N 5 (N 8 (N 9 L L (N 12 L L (N 17 L L (N 13 (N 18 L L (N 19 L L L)) L (N 14 (N 19 L L L) L
  L))))) L (N 9 (N 13 L L (N 18 L L (N 12 (N 17 L L (N 19 L L L)) L (N 14 (N 19 L L L) L L)))) L
  (N 12 (N 13 L L (N 14 (N 17 L L (N 19 L L L)) L L)) L (N 14 (N 19 L L (N 17 (N 18 L L L) L L)) L
  L)))) L (N 8 (N 9 L L (N 12 (N 13 L L (N 14 L L L)) L (N 13 (N 18 L L (N 17 (N 19 L L L) L L)) L
  L))) L (N 9 (N 12 (N 13 L L (N 17 L L (N 18 (N 19 L L L) L L))) L (N 13 (N 14 L L L) L L)) L
  L))) L L))) (S 22 L L (S 29 L L L)))) (S 11 L L (S 16 (S 22 L (S 29 L (N 14 (N 35 (N 9 (N 13 L L
  (N 8 L (N 18 L (N 17 (N 20 L (N 23 (N 27 L (N 5 L L (N 12 L L L)) L) L (N 27 (N 34 L (N 19 L L
  (N 31 L L (N 5 (N 12 L L (N 24 L L (N 25 L (N 26 (N 33 L L L) L L) L))) L L))) L) (N 34 (N 19 L
  L (N 24 L L (N 5 (N 12 L L (N 25 (N 26 L L L) L L)) L L))) L L) L)) (N 12 (N 23 L L (N 30 L L (N
  5 L (N 24 (N 31 L L L) L L) (N 24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L) L)))) (N 5 (N
  23 L L (N 24 L (N 31 L L L) L)) L (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N 31 L (N 34 L L L) L)
  (N 27 (N 31 L L L) L L) L))) L)) L (N 20 L (N 23 (N 27 L (N 24 L L (N 5 (N 26 L L L) L L)) L) L
  (N 27 (N 34 L (N 31 L L (N 5 (N 24 L L (N 25 L (N 26 (N 33 L L L) L L) L)) L L)) L) (N 34 (N 24
  L L (N 5 (N 25 (N 26 L L L) L L) L L)) L L) L)) (N 12 (N 19 (N 23 (N 24 L (N 27 L L L) L) L (N
  24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L) L)) (N 27 (N 34 L L L) L L) L) (N 5 (N 24 L
  (N 31 L L L) L) L (N 19 (N 23 (N 24 L (N 27 L L L) L) L (N 30 (N 31 L (N 34 L L L) L) L L)) (N
  27 (N 34 L L L) L L) L)) L))) (N 20 L (N 17 (N 19 (N 27 L (N 25 L L (N 24 (N 33 L L L) L L)) L)
  (N 27 (N 34 L L L) L L) L) L (N 5 (N 19 (N 23 (N 26 L (N 27 L L L) L) L (N 24 L (N 27 (N 33 L (N
  34 L L L) L) L L) (N 25 L (N 27 (N 31 L (N 34 L L L) L) L L) L))) (N 27 (N 34 L L L) L L) L) (N
  12 (N 19 (N 23 (N 26 L (N 27 L L L) L) L (N 25 L (N 27 (N 32 L L (N 31 L (N 34 L L L) L)) L L)
  (N 24 (N 33 L (N 34 L L L) L) (N 27 (N 31 L L (N 32 L (N 34 L L L) L)) L L) L))) (N 27 (N 34 L L
  L) L L) L) L (N 19 (N 23 (N 27 L (N 24 L L (N 25 L L L)) L) L (N 25 L (N 27 (N 30 (N 32 L L (N
  31 L (N 34 L L L) L)) L L) L L) L)) (N 27 (N 34 L L L) L L) L)) L)) L)) (N 5 (N 18 L (N 20 L (N
  23 (N 27 L (N 12 L L (N 26 L L L)) L) L (N 19 (N 25 L (N 27 (N 32 L (N 34 L L L) L) L L) L) (N
  27 (N 34 L L L) L L) L)) (N 24 L (N 31 L L L) L)) (N 20 L (N 19 (N 23 (N 26 L (N 27 L L L) L) L
  (N 25 L (N 27 (N 32 L (N 34 L L L) L) L L) L)) (N 23 (N 26 L (N 27 L L L) L) L (N 24 L (N 27 (N
  25 L (N 34 L L L) L) L L) (N 31 L (N 34 (N 27 L (N 32 L L L) L) L L) L))) L) L)) (N 18 L (N 27
  (N 34 L L L) L L) (N 20 L (N 17 (N 19 (N 27 L (N 25 L L (N 23 (N 24 L L L) L L)) L) (N 23 (N 27
  L (N 12 L L (N 24 L L (N 25 (N 26 L L L) L L))) L) L (N 25 (N 26 L (N 27 L L L) L) (N 27 (N 34 L
  L L) L L) L)) L) L (N 19 (N 25 L (N 27 (N 23 L L (N 30 (N 32 L (N 34 L L L) L) L L)) L L) L) (N
  23 (N 27 L (N 24 L L (N 25 (N 26 L L L) L L)) L) L (N 30 (N 34 L (N 12 (N 25 L L L) L L) L) L
  L)) L)) L)) L))) L (N 13 (N 12 L (N 18 L (N 17 (N 19 L (N 23 (N 27 L (N 5 L L (N 8 L L L)) L) L
  (N 27 (N 34 L (N 20 L L (N 31 L L (N 5 (N 8 L L (N 24 L L (N 25 (N 32 L L L) L L))) L L))) L) (N
  34 (N 20 L L (N 24 L L (N 5 (N 8 L L (N 25 (N 26 L L L) L L)) L L))) L L) L)) (N 8 (N 23 L L (N
  30 L L (N 5 L (N 24 (N 31 L L L) L L) (N 24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L)
  L)))) (N 5 (N 23 L L (N 24 L (N 31 L L L) L)) L (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N 31 L (N
  34 L L L) L) (N 27 (N 31 L L L) L L) L))) L)) L (N 19 L (N 23 (N 27 L (N 24 L L (N 5 (N 25 L L
  L) L L)) L) L (N 27 (N 34 L (N 31 L L (N 5 (N 24 L L (N 25 (N 32 L L L) L L)) L L)) L) (N 34 (N
  24 L L (N 5 (N 25 (N 26 L L L) L L) L L)) L L) L)) (N 8 (N 20 (N 23 (N 24 L (N 27 L L L) L) L (N
  24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L) L)) (N 27 (N 34 L L L) L L) L) (N 5 (N 24 L
  (N 31 L L L) L) L (N 20 (N 23 (N 24 L (N 27 L L L) L) L (N 30 (N 31 L (N 34 L L L) L) L L)) (N
  27 (N 34 L L L) L L) L)) L))) (N 19 L (N 17 (N 20 (N 27 L (N 25 (N 32 L L L) L L) L) (N 27 (N 34
  L L L) L L) L) L (N 5 (N 20 (N 23 (N 25 L (N 27 L L L) L) L (N 24 L (N 27 (N 32 L (N 34 L L L)
  L) L L) (N 26 L (N 27 (N 31 L (N 34 L L L) L) L L) L))) (N 27 (N 34 L L L) L L) L) (N 8 (N 20 (N
  23 (N 25 L (N 27 L L L) L) L (N 25 (N 32 L (N 34 L L L) L) (N 27 (N 32 L L L) L L) L)) (N 27 (N
  34 L L L) L L) L) L (N 20 (N 23 (N 27 L (N 24 L L (N 26 L L L)) L) L (N 26 L (N 27 (N 30 (N 32 L
  (N 34 L L L) L) L L) L L) L)) (N 27 (N 34 L L L) L L) L)) L)) L)) (N 5 (N 18 L (N 19 L (N 23 (N
  27 L (N 8 L L (N 25 L L L)) L) L (N 20 (N 26 L (N 27 (N 33 L (N 34 L L L) L) L L) L) (N 27 (N 34
  L L L) L L) L)) (N 24 L (N 31 L L L) L)) (N 19 L (N 20 (N 23 (N 25 L (N 27 L L L) L) L (N 26 L
  (N 27 (N 32 L (N 34 L L L) L) L L) L)) (N 23 (N 25 L (N 27 L L L) L) L (N 24 L (N 27 (N 26 L (N
  34 L L L) L) L L) (N 31 L (N 34 (N 27 L (N 33 L L L) L) L L) L))) L) L)) (N 18 L (N 27 (N 34 L L
  L) L L) (N 19 L (N 17 (N 20 (N 27 L (N 25 (N 32 L L L) L L) L) (N 23 (N 27 L (N 8 L L (N 24 L L
  (N 25 (N 26 L L L) L L))) L) L (N 25 (N 26 L (N 27 (N 34 L L L) L L) L) (N 27 (N 34 L L L) L L)
  L)) L) L (N 20 (N 26 L (N 27 (N 23 L L (N 30 (N 32 L (N 34 L L L) L) L L)) L L) L) (N 23 (N 27 L
  (N 24 L L (N 25 (N 26 L L L) L L)) L) L (N 30 (N 34 L (N 8 (N 26 L L L) L L) L) L L)) L)) L))
  L)) L (N 18 L (N 23 (N 27 L (N 24 L L (N 5 (N 25 (N 26 L L L) L L) L L)) L) L (N 27 (N 34 L (N
  31 L L (N 5 (N 24 (N 25 L (N 19 (N 33 L L L) L L) L) L L) L L)) L) (N 5 (N 24 (N 31 L L (N 25 (N
  26 L L L) L L)) L (N 25 (N 26 L L L) L L)) L (N 24 (N 31 L L L) L L)) L)) (N 5 (N 19 (N 20 L (N
  8 L (N 17 (N 23 L L (N 27 L (N 12 L L (N 24 (N 25 L L L) L L)) L)) L (N 23 (N 24 L (N 27 L L L)
  L) L (N 24 (N 25 L (N 27 (N 26 L (N 33 L L L) L) L L) L) (N 27 (N 25 L (N 26 (N 31 L (N 34 L L
  L) L) L L) L) L L) L))) (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N 25 L (N 27 (N 26 L (N 33 L L L)
  L) L L) L) (N 27 (N 25 L (N 26 (N 31 L (N 34 L L L) L) L L) L) L L) L))) L) (N 20 (N 12 L (N 17
  (N 23 L L (N 27 L (N 8 L L (N 24 (N 26 L L L) L L)) L)) L (N 23 (N 24 L (N 27 L L L) L) L (N 24
  (N 26 L (N 27 (N 25 L (N 32 L L L) L) L L) L) (N 27 (N 26 L (N 25 (N 31 L (N 34 L L L) L) L L)
  L) L L) L))) (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N 26 L (N 27 (N 25 L (N 32 L L L) L) L L) L)
  (N 27 (N 26 L (N 25 (N 31 L (N 34 L L L) L) L L) L) L L) L))) (N 23 (N 24 L (N 27 L L L) L) L (N
  24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L (N 34 L L L) L) L L) L)) L) L) (N 19 (N 20 L (N 8 L (N
  12 (N 17 (N 23 L L (N 27 L (N 24 (N 25 L L L) L L) L)) L (N 23 (N 24 L (N 27 L L L) L) L (N 24
  (N 25 L (N 27 (N 26 L (N 33 L L L) L) L L) L) (N 27 (N 31 L L L) L L) L))) L (N 17 (N 27 L (N 24
  (N 25 L L L) L L) L) L (N 23 (N 24 L (N 27 L L L) L) L (N 30 (N 31 L (N 34 L L L) L) L L)))) (N
  17 (N 27 L (N 24 (N 25 L L L) L L) L) L (N 23 (N 24 L (N 27 L L L) L) L (N 30 (N 31 L (N 34 L L
  L) L) L L)))) L) (N 17 (N 20 (N 27 L (N 24 (N 26 L L L) L L) L) (N 23 (N 24 L (N 27 L L L) L) L
  (N 24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L) L)) L) L (N 20 (N 12 L (N 8 (N 23 (N 24 L
  (N 27 L L L) L) L (N 24 (N 26 L (N 27 (N 25 L (N 32 L L L) L) L L) L) (N 27 (N 31 L L L) L L)
  L)) L (N 23 (N 24 L (N 27 L L L) L) L (N 30 (N 31 L (N 34 L L L) L) L L))) (N 23 (N 24 L (N 27 L
  L L) L) L (N 30 (N 31 L (N 34 L L L) L) L L))) (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N 31 L (N
  34 L L L) L) (N 27 (N 31 L L L) L L) L)) L)) L) L)))) L L) L L) (N 14 (N 9 (N 13 L L (N 20 L (N
  8 L (N 17 (N 18 L (N 19 (N 25 L (N 27 L L L) L) (N 25 (N 27 L L L) L L) L) (N 19 (N 25 L (N 27 L
  L L) L) (N 25 (N 27 L L L) L L) L)) L (N 18 L (N 19 (N 25 L (N 32 L L L) L) (N 25 (N 27 L L L) L
  L) L) (N 5 (N 19 (N 25 L (N 32 L L L) L) (N 25 (N 27 L L L) L L) L) (N 12 (N 19 (N 25 L (N 32 L
  L L) L) (N 25 (N 27 L L L) L L) L) L (N 19 (N 25 L (N 32 L L L) L) (N 25 (N 27 L L L) L L) L))
  L))) (N 5 (N 18 L (N 19 (N 25 L (N 27 (N 23 L L (N 32 L (N 34 L L L) L)) L L) L) (N 27 (N 23 L L
  (N 25 L (N 32 (N 34 L L L) L L) L)) L L) L) (N 19 (N 25 L (N 27 (N 23 L L (N 32 L (N 34 L L L)
  L)) L L) L) (N 23 (N 26 L (N 27 L L L) L) L (N 24 L (N 27 (N 25 L (N 26 (N 32 (N 33 L (N 34 L L
  L) L) L L) L L) L) L L) (N 31 L (N 34 (N 32 L (N 25 (N 26 L (N 27 L L L) L) L L) L) L L) L)))
  L)) (N 17 (N 18 L (N 27 (N 19 L (N 34 L L L) L) L L) (N 19 (N 25 L (N 27 L L L) L) (N 23 (N 27 L
  (N 12 L L (N 24 L L (N 25 (N 26 L L L) L L))) L) L (N 25 (N 26 L (N 27 L L L) L) (N 27 (N 32 (N
  33 L (N 34 L L L) L) L L) L L) L)) L)) L (N 18 L (N 27 (N 23 L L (N 25 L (N 12 (N 19 (N 32 L (N
  34 L L L) L) (N 32 (N 34 L L L) L L) L) (N 26 (N 30 (N 31 L L (N 33 (N 32 L (N 34 L L L) L) L
  L)) L L) L L) L) L)) L L) (N 19 (N 25 L (N 27 (N 23 L L (N 32 L (N 34 L L L) L)) L L) L) (N 23
  (N 27 L (N 24 L L (N 25 (N 26 L L L) L L)) L) L (N 12 (N 25 (N 26 L (N 27 L L L) L) (N 27 (N 32
  (N 33 L (N 34 L L L) L) L L) L L) L) (N 26 (N 25 L (N 27 (N 30 (N 32 (N 33 L L L) L L) L L) L L)
  L) L L) L)) L))) L)) L)) L (N 13 (N 19 L (N 12 L (N 17 (N 18 L (N 20 (N 26 L (N 27 L L L) L) (N
  26 (N 27 L L L) L L) L) (N 20 (N 26 L (N 27 L L L) L) (N 26 (N 27 L L L) L L) L)) L (N 18 L (N
  20 (N 26 L (N 33 L L L) L) (N 26 (N 27 L L L) L L) L) (N 5 (N 20 (N 26 L (N 33 L L L) L) (N 26
  (N 27 L L L) L L) L) (N 8 (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 27 L L L) L L) L) L (N 20 (N 26
  L (N 33 L L L) L) (N 26 (N 27 L L L) L L) L)) L))) (N 5 (N 18 L (N 20 (N 26 L (N 27 (N 23 L L (N
  33 L (N 34 L L L) L)) L L) L) (N 27 (N 23 L L (N 26 L (N 33 (N 34 L L L) L L) L)) L L) L) (N 20
  (N 26 L (N 27 (N 23 L L (N 33 L (N 34 L L L) L)) L L) L) (N 23 (N 25 L (N 27 L L L) L) L (N 24 L
  (N 27 (N 26 L (N 25 (N 33 (N 32 L (N 34 L L L) L) L L) L L) L) L L) (N 31 L (N 34 (N 33 L (N 26
  (N 25 L (N 27 L L L) L) L L) L) L L) L))) L)) (N 17 (N 18 L (N 27 (N 20 L (N 34 L L L) L) L L)
  (N 20 (N 26 L (N 27 L L L) L) (N 23 (N 27 L (N 8 L L (N 24 L L (N 25 (N 26 L L L) L L))) L) L (N
  25 (N 26 L (N 27 (N 33 (N 32 L (N 34 L L L) L) L L) L L) L) (N 27 (N 26 L (N 32 (N 33 L L L) L
  L) L) L L) L)) L)) L (N 18 L (N 27 (N 23 L L (N 26 L (N 8 (N 20 (N 33 L (N 34 L L L) L) (N 33 (N
  34 L L L) L L) L) (N 25 (N 30 (N 31 L L (N 32 (N 33 L (N 34 L L L) L) L L)) L L) L L) L) L)) L
  L) (N 20 (N 26 L (N 27 (N 23 L L (N 33 L (N 34 L L L) L)) L L) L) (N 23 (N 27 L (N 24 L L (N 25
  (N 26 L L L) L L)) L) L (N 8 (N 25 (N 26 L (N 27 (N 32 L (N 30 (N 34 L L L) L L) L) L L) L) (N
  27 (N 26 L (N 32 (N 33 L L L) L L) L) L L) L) (N 25 (N 26 L (N 27 (N 30 (N 32 (N 33 L L L) L L)
  L L) L L) L) L L) L)) L))) L)) L) L (N 18 L (N 19 (N 20 L (N 8 L (N 17 (N 27 L (N 34 L L L) L) L
  (N 23 (N 27 L (N 24 L L (N 5 (N 12 L L (N 25 (N 26 L L L) L L)) L L)) L) L (N 25 (N 26 L (N 27 L
  L L) L) (N 27 (N 32 (N 33 L (N 34 L L L) L) L L) L L) L))) (N 5 (N 23 (N 27 L (N 12 L L (N 17 L
  L (N 24 L L (N 25 (N 26 L L L) L L)))) L) L (N 25 (N 26 L (N 27 L L L) L) (N 27 (N 34 L (N 17 L
  L (N 32 (N 33 L L L) L L)) L) L L) L)) (N 27 (N 17 L L (N 23 L L (N 25 L (N 34 L (N 32 (N 33 L L
  L) L L) L) L))) L L) L)) L) (N 20 (N 12 L (N 17 (N 27 L (N 34 L L L) L) L (N 23 (N 27 L (N 24 L
  L (N 5 (N 8 L L (N 25 (N 26 L L L) L L)) L L)) L) L (N 25 (N 26 L (N 27 (N 33 (N 32 L (N 34 L L
  L) L) L L) L L) L) (N 27 (N 26 L (N 32 (N 33 L L L) L L) L) L L) L))) (N 5 (N 23 (N 27 L (N 8 L
  L (N 17 L L (N 24 L L (N 25 (N 26 L L L) L L)))) L) L (N 25 (N 26 L (N 27 (N 34 L (N 17 L L (N
  32 (N 33 L L L) L L)) L) L L) L) (N 27 (N 17 L L (N 8 (N 26 L (N 30 L (N 32 (N 33 L L L) L L) L)
  L) L L)) L L) L)) (N 27 (N 17 L L (N 23 L L (N 26 L (N 34 L (N 32 (N 33 L L L) L L) L) L))) L L)
  L)) (N 27 (N 23 L L (N 34 (N 17 L L (N 35 L (N 25 (N 26 L (N 33 L L L) L) (N 26 (N 32 L L L) L
  L) L) L)) L L)) L L) L) L) (N 5 (N 19 (N 20 L (N 8 L (N 17 (N 23 L L (N 27 L (N 12 L L (N 24 (N
  25 L L L) L L)) L)) L (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N 25 L (N 27 (N 31 L (N 34 L L L)
  L) L L) L) (N 27 (N 25 L (N 26 (N 32 (N 31 L (N 34 L L L) L) L L) L L) L) L L) L))) (N 23 (N 24
  L (N 27 L L L) L) L (N 24 (N 25 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N 25 L (N 26 (N
  34 L (N 31 (N 32 L L L) L L) L) L L) L) L L) L))) L) (N 20 (N 12 L (N 17 (N 23 L L (N 27 L (N 8
  L L (N 24 (N 26 L L L) L L)) L)) L (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N 26 L (N 27 (N 31 L
  (N 34 L L L) L) L L) L) (N 27 (N 26 L (N 25 (N 33 (N 31 L (N 34 L L L) L) L L) L L) L) L L) L)))
  (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N 26 L (N 27 (N 31 L (N 34 L L L) L) L L) L) (N 27 (N 26
  L (N 25 (N 34 L (N 31 (N 33 L L L) L L) L) L L) L) L L) L))) (N 23 (N 24 L (N 27 L L L) L) L (N
  24 (N 31 L (N 34 (N 35 L (N 25 (N 26 L L L) L L) L) L L) L) (N 27 (N 25 (N 26 L (N 33 (N 32 L (N
  34 L L L) L) L L) L) (N 26 (N 32 (N 33 L (N 34 L L L) L) L L) L L) L) L L) L)) L) L) (N 19 (N 20
  L (N 8 L (N 12 (N 17 (N 23 L L (N 27 L (N 24 (N 25 L L L) L L) L)) L (N 23 (N 24 L (N 27 L L L)
  L) L (N 24 (N 25 L (N 27 (N 32 (N 31 L (N 34 L L L) L) L L) L L) L) (N 27 (N 25 L (N 26 (N 31 (N
  32 L L L) L L) L L) L) L L) L))) L (N 17 (N 27 L (N 24 (N 25 L L L) L L) L) L (N 23 (N 24 L (N
  27 L L L) L) L (N 30 (N 31 L (N 34 L L L) L) L L)))) (N 17 (N 27 L (N 24 (N 25 L L L) L L) L) L
  (N 23 (N 24 L (N 27 L L L) L) L (N 12 (N 24 (N 25 L (N 27 (N 34 L (N 31 (N 32 L L L) L L) L) L
  L) L) (N 27 (N 25 L (N 26 (N 31 (N 35 L L L) L L) L L) L) L L) L) (N 26 (N 25 L (N 27 (N 30 (N
  31 L (N 34 L L L) L) L L) L L) L) L L) L)))) L) (N 17 (N 20 (N 27 L (N 24 (N 26 L L L) L L) L)
  (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N 25 (N 26 L (N 27 (N 12 L L (N 33 (N 31 L (N 34 L L L)
  L) L L)) L L) L) (N 27 (N 32 (N 33 L (N 34 L L L) L) L L) L L) L) (N 27 (N 31 (N 34 L (N 32 (N
  33 L L L) L L) L) L L) L L) L)) L) L (N 20 (N 12 L (N 8 (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N
  26 L (N 27 (N 33 (N 31 L (N 34 L L L) L) L L) L L) L) (N 27 (N 26 L (N 25 (N 31 (N 33 L L L) L
  L) L L) L) L L) L)) L (N 23 (N 24 L (N 27 L L L) L) L (N 30 (N 31 L (N 34 L L L) L) L L))) (N 23
  (N 24 L (N 27 L L L) L) L (N 8 (N 24 (N 26 L (N 27 (N 34 L (N 31 (N 33 L L L) L L) L) L L) L) (N
  27 (N 26 L (N 25 (N 31 (N 35 L L L) L L) L L) L) L L) L) (N 25 (N 26 L (N 27 (N 30 (N 31 L (N 34
  L L L) L) L L) L L) L) L L) L))) (N 23 (N 24 L (N 27 L L L) L) L (N 24 (N 25 (N 26 L (N 27 (N 33
  (N 31 L (N 34 L L L) L) L L) L L) L) (N 27 (N 32 (N 33 L (N 26 (N 34 L L L) L L) L) L L) L L) L)
  (N 27 (N 31 (N 35 L (N 25 (N 26 L L L) L L) L) L L) L L) L)) L)) L) L)))) L L)) (S 29 L L L)) (S
  22 L (S 29 L L (N 14 (N 27 (N 9 (N 13 L L (N 8 L (N 17 (N 23 L L (N 18 L (N 19 (N 20 L (N 34 L L
  L) L) (N 20 (N 34 L L L) L L) L) (N 5 (N 20 L (N 25 L (N 19 (N 32 L L L) L L) L) L) (N 12 (N 20
  L (N 25 L (N 19 (N 32 L L L) L L) L) L) L (N 19 (N 20 L (N 25 L (N 32 L L L) L) L) (N 25 (N 32 L
  L L) L L) L)) L))) L (N 19 (N 20 L (N 25 L (N 32 L L L) L) L) (N 25 (N 32 L L L) L L) L)) (N 5
  (N 17 (N 20 L (N 23 L L (N 25 L (N 12 L (N 26 (N 33 (N 32 L (N 35 L L L) L) L L) L L) (N 30 L (N
  32 (N 33 L L L) L L) L)) L)) L) L (N 18 L (N 19 (N 20 L (N 23 L L (N 25 L (N 32 L (N 30 (N 34 L
  L L) L L) L) L)) L) (N 20 (N 26 L (N 34 (N 33 L (N 35 L L L) L) L L) L) L L) L) (N 19 (N 20 L (N
  23 L L (N 25 L (N 32 L (N 30 (N 34 L L L) L L) L) L)) L) (N 20 (N 26 L (N 23 (N 12 L (N 33 (N 32
  L (N 34 L L L) L) L L) (N 30 L (N 32 (N 33 L L L) L L) L)) L (N 12 (N 30 L (N 33 L L L) L) (N 33
  (N 30 L (N 32 L L L) L) L L) L)) L) (N 34 (N 35 L (N 32 (N 33 L L L) L L) L) L L) L) L))) (N 17
  (N 23 L L (N 18 L (N 19 (N 20 L (N 34 L L L) L) (N 20 (N 34 L L L) L L) L) (N 19 (N 20 L (N 25 L
  (N 32 L (N 34 L L L) L) L) L) (N 20 (N 26 L (N 34 L (N 32 (N 33 L L L) L L) L) L) (N 34 (N 35 L
  (N 32 (N 33 L L L) L L) L) L L) L) L))) L (N 19 (N 20 L (N 25 L (N 32 L (N 34 (N 35 L L L) L L)
  L) L) L) (N 20 (N 26 L (N 23 (N 24 L (N 25 (N 35 L L L) L L) (N 25 (N 32 L (N 35 L L L) L) (N 32
  (N 35 L L L) L L) L)) L (N 12 (N 33 L (N 30 (N 35 L L L) L L) L) (N 30 (N 33 (N 32 L (N 34 L L
  L) L) L L) L L) L)) L) (N 34 (N 35 L (N 32 (N 33 L L L) L L) L) L L) L) L)) L))) L (N 13 (N 12 L
  (N 17 (N 23 L L (N 18 L (N 19 (N 20 L (N 34 L L L) L) (N 20 (N 34 L L L) L L) L) (N 5 (N 19 L (N
  26 L (N 20 (N 33 L L L) L L) L) L) (N 8 (N 19 L (N 26 L (N 20 (N 33 L L L) L L) L) L) L (N 19 (N
  20 L (N 25 L (N 26 (N 33 L L L) L L) L) L) (N 20 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L)
  L) L)) L))) L (N 19 (N 20 L (N 25 L (N 26 (N 33 L L L) L L) L) L) (N 20 (N 26 L (N 33 L L L) L)
  (N 26 (N 33 L L L) L L) L) L)) (N 5 (N 17 (N 19 L (N 23 L L (N 26 L (N 8 L (N 25 (N 32 (N 33 L
  (N 35 L L L) L) L L) L L) (N 30 L (N 32 (N 33 L L L) L L) L)) L)) L) L (N 18 L (N 19 (N 20 L (N
  25 L (N 34 (N 32 L (N 35 L L L) L) L L) L) L) (N 20 (N 23 L L (N 26 L (N 33 L (N 30 (N 34 L L L)
  L L) L) L)) L L) L) (N 19 (N 20 L (N 25 L (N 23 (N 8 L (N 32 (N 33 L (N 34 L L L) L) L L) (N 30
  L (N 32 (N 33 L L L) L L) L)) L (N 8 (N 30 L (N 32 L L L) L) (N 32 (N 30 L (N 33 L L L) L) L L)
  L)) L) L) (N 20 (N 23 L L (N 26 L (N 33 L (N 30 (N 34 L L L) L L) L) L)) (N 34 (N 35 L (N 32 (N
  33 L L L) L L) L) L L) L) L))) (N 17 (N 23 L L (N 18 L (N 19 (N 20 L (N 34 L L L) L) (N 20 (N 34
  L L L) L L) L) (N 19 (N 20 L (N 25 L (N 34 L (N 32 (N 33 L L L) L L) L) L) L) (N 20 (N 26 L (N
  33 L (N 34 L L L) L) L) (N 34 (N 35 L (N 32 (N 33 L L L) L L) L) L L) L) L))) L (N 19 (N 20 L (N
  25 L (N 23 (N 24 L (N 26 (N 35 L L L) L L) (N 26 (N 33 L (N 35 L L L) L) (N 33 (N 35 L L L) L L)
  L)) L (N 8 (N 32 L (N 30 (N 35 L L L) L L) L) (N 30 (N 32 (N 33 L (N 34 L L L) L) L L) L L) L))
  L) L) (N 20 (N 26 L (N 33 L (N 34 (N 35 L L L) L L) L) L) (N 34 (N 35 L (N 32 (N 33 L L L) L L)
  L) L L) L) L)) L)) L (N 17 (N 23 L L (N 18 L (N 19 (N 20 L (N 34 L L L) L) (N 20 (N 34 L L L) L
  L) L) (N 5 (N 8 L (N 12 L (N 30 L L (N 19 (N 20 L (N 25 L (N 26 (N 32 (N 33 L L L) L L) L L) L)
  L) (N 25 (N 26 L (N 20 (N 32 (N 33 L L L) L L) L L) L) L L) L)) (N 19 (N 20 L (N 25 L (N 32 (N
  31 L (N 34 L L L) L) L L) L) L) (N 25 (N 26 L (N 32 (N 33 L (N 35 L L L) L) L L) L) L L) L)) (N
  12 L (N 19 (N 20 L (N 25 L (N 26 (N 33 (N 32 L (N 34 L L L) L) L L) L L) L) L) (N 20 (N 26 L (N
  33 (N 31 L (N 34 L L L) L) L L) L) (N 26 (N 25 L (N 32 (N 33 L L L) L L) L) L L) L) L) (N 30 L
  (N 19 (N 20 L (N 25 L (N 32 (N 33 L L L) L L) L) L) (N 32 (N 33 L (N 20 (N 26 L L L) L L) L) L
  L) L) L))) (N 19 (N 20 L (N 25 L (N 34 L (N 31 (N 32 (N 33 L L L) L L) L L) L) L) L) (N 20 (N 26
  L (N 34 L (N 31 (N 32 (N 33 L L L) L L) L L) L) L) (N 34 (N 35 L (N 31 (N 32 (N 33 L L L) L L) L
  L) L) L L) L) L) L))) L (N 19 (N 20 L (N 25 L (N 23 (N 12 L (N 26 (N 33 (N 32 L (N 35 L L L) L)
  L L) L L) (N 5 (N 8 L (N 32 (N 33 L (N 34 L L L) L) L L) (N 30 L (N 32 (N 33 L L L) L L) L)) (N
  24 L (N 26 (N 35 L L L) L L) (N 18 (N 34 L (N 31 (N 33 L L L) L L) L) (N 31 (N 34 (N 32 L (N 35
  L L L) L) L L) L L) L)) L)) L (N 26 (N 32 (N 33 L (N 34 L L L) L) (N 34 (N 35 L L L) L L) L) (N
  33 (N 35 L L L) L L) L)) L) L) (N 20 (N 26 L (N 23 (N 8 L (N 25 (N 32 (N 33 L (N 35 L L L) L) L
  L) L L) (N 5 (N 12 L (N 33 (N 32 L (N 34 L L L) L) L L) (N 30 L (N 32 (N 33 L L L) L L) L)) (N
  24 L (N 25 (N 35 L L L) L L) (N 18 (N 34 L (N 31 (N 32 L L L) L L) L) (N 31 (N 34 (N 33 L (N 35
  L L L) L) L L) L L) L)) L)) L (N 25 (N 32 (N 33 L (N 35 L L L) L) (N 34 (N 35 L L L) L L) L) (N
  32 (N 35 L L L) L L) L)) L) (N 34 (N 35 L (N 32 (N 33 L L L) L L) L) L L) L) L)))) L L) L L)) (S
  29 L L L)) (S 22 L L L)))) (S 7 L (S 11 L L (S 16 (S 22 (S 29 L L (N 27 L (N 5 (N 8 (N 9 L L (N
  12 L L (N 13 (N 14 (N 17 L (N 23 L L (N 24 L L (N 25 L L L))) (N 18 L (N 23 L L (N 24 L L (N 25
  L L L))) (N 19 L (N 25 L L L) L))) L (N 17 L (N 23 L L (N 24 L L L)) (N 18 L (N 23 L L (N 24 L L
  L)) L))) L (N 14 (N 17 L (N 23 L L (N 25 L L L)) (N 19 L (N 23 L L (N 25 L L L)) L)) L L)))) L
  (N 9 (N 12 (N 13 L L (N 20 L (N 26 L L L) L)) L (N 14 (N 13 L L (N 18 L (N 24 L L (N 25 (N 26 L
  L L) L L)) (N 19 (N 20 L (N 26 L L L) L) (N 24 L L (N 25 (N 26 L L L) L L)) L))) L L)) L (N 12
  (N 13 L L (N 14 (N 20 L (N 26 L L L) L) L L)) L (N 14 (N 13 (N 18 L (N 24 L L (N 25 (N 26 L L L)
  L L)) (N 19 (N 20 L (N 26 L L L) L) (N 24 L L (N 25 (N 26 L L L) L L)) L)) L (N 18 L (N 24 L L
  (N 25 (N 26 L L L) L L)) (N 24 L (N 19 (N 20 L L L) L L) L))) L L)))) L (N 8 (N 9 (N 12 (N 14 L
  L (N 20 L (N 26 L L L) L)) L (N 13 (N 14 L L (N 19 L (N 25 L L (N 24 (N 26 L L L) L L)) (N 18 (N
  20 L (N 26 L L L) L) (N 25 L L (N 24 (N 26 L L L) L L)) L))) L L)) L (N 12 (N 14 L L (N 13 (N 20
  L (N 26 L L L) L) L L)) L (N 13 (N 14 (N 19 L (N 25 L L (N 24 (N 26 L L L) L L)) (N 18 (N 20 L
  (N 26 L L L) L) (N 24 (N 26 L L L) L L) L)) L (N 19 L (N 25 L L (N 24 (N 26 L L L) L L)) (N 25 L
  (N 18 (N 20 L L L) L L) L))) L L))) L (N 9 (N 12 (N 20 L (N 26 L L L) L) L (N 13 (N 14 L L L) L
  L)) L L))) L)) L (S 29 L L (N 5 (N 8 (N 9 L L (N 12 L L (N 13 (N 14 (N 17 L (N 18 L (N 19 L (N
  20 (N 26 L (N 27 (N 34 L L L) L L) L) L L) (N 24 (N 31 L L L) L L)) (N 19 L (N 25 (N 32 L L L) L
  L) L)) (N 18 L (N 19 L (N 20 (N 26 L (N 27 (N 33 L (N 34 L L L) L) L L) L) (N 27 (N 34 (N 35 L
  (N 23 L (N 30 L L (N 31 (N 24 L L (N 25 (N 32 L L L) L L)) L L)) (N 24 (N 25 (N 26 L (N 33 L L
  L) L) L L) L L)) L) L L) L L) L) (N 24 (N 31 L L L) L L)) (N 19 L (N 25 (N 32 L L L) L L) L))) L
  (N 17 L (N 18 L (N 24 (N 31 L L L) L L) (N 19 L (N 25 (N 26 L (N 27 (N 32 (N 33 L (N 35 L L L)
  L) L L) L L) L) L L) L)) (N 18 L (N 24 (N 31 L L L) L L) L))) L (N 14 (N 17 L (N 18 L (N 19 L (N
  20 (N 25 (N 32 L L L) L L) L L) (N 24 (N 26 L (N 27 (N 31 (N 33 L (N 35 L L L) L) L L) L L) L) L
  L)) (N 19 L (N 25 (N 32 L L L) L L) L)) (N 19 L (N 25 (N 32 L L L) L L) L)) L L)))) L (N 9 (N 12
  (N 13 L L (N 20 L (N 14 (N 17 L (N 18 L (N 27 (N 34 (N 19 L L (N 23 L (N 30 L L L) L)) L L) L L)
  (N 23 L (N 27 (N 30 L L (N 19 (N 25 L (N 32 L L L) L) (N 25 (N 32 L L L) L L) L)) L L) (N 19 (N
  25 L (N 32 L L L) L) (N 25 (N 32 L L L) L L) L))) (N 18 L (N 19 (N 25 L (N 32 L L L) L) (N 25 (N
  32 L L L) L L) L) (N 19 (N 25 L (N 32 L L L) L) (N 25 (N 32 L L L) L L) L))) L (N 23 L (N 30 L
  (N 17 L L (N 18 L (N 27 (N 34 (N 35 L L L) L L) L L) L)) L) L)) L)) L (N 14 (N 13 L L (N 18 L (N
  20 (N 17 L (N 19 L (N 25 (N 32 L L L) L L) (N 23 (N 24 L L (N 26 L (N 27 L L L) L)) (N 27 (N 24
  L L (N 26 L (N 30 (N 31 L L (N 33 L (N 34 L L L) L)) L L) L)) L L) L)) (N 19 L (N 25 (N 32 L L
  L) L L) L)) (N 24 (N 25 L (N 27 (N 31 L L (N 32 (N 19 L L (N 23 L (N 33 L (N 34 L L L) L) L)) L
  L)) L L) L) L (N 23 (N 26 L (N 27 L L L) L) (N 27 (N 25 (N 26 L (N 32 L (N 19 L L (N 17 L (N 30
  (N 33 L L L) L L) L)) L) L) (N 32 (N 19 L L (N 31 L L (N 33 L (N 26 (N 34 L L L) L L) L))) L L)
  L) L L) L)) L) (N 19 (N 20 L (N 25 L (N 32 L L L) L) L) (N 25 (N 32 L L L) L L) L))) L L)) L (N
  12 (N 13 L L (N 14 (N 20 L (N 17 L (N 18 L (N 27 (N 34 (N 19 L L (N 23 L (N 30 L L L) L)) L L) L
  L) (N 19 (N 23 L (N 27 (N 25 L (N 30 L L (N 32 (N 31 L (N 34 L L L) L) L L)) L) L L) (N 24 (N 25
  L (N 27 (N 32 (N 31 L (N 34 L L L) L) L L) L L) L) (N 27 (N 25 L (N 31 (N 32 L L L) L L) L) L L)
  L)) (N 25 (N 24 L (N 26 L (N 27 (N 31 (N 32 L L L) L L) L L) L) L) L L) L)) (N 18 L (N 19 (N 23
  L (N 27 (N 25 L (N 32 (N 31 L L (N 24 (N 30 L (N 34 L L L) L) L L)) L L) L) L L) (N 24 (N 25 L
  (N 27 (N 30 L (N 34 L L L) L) L L) L) L L)) (N 25 (N 24 L L (N 23 L (N 26 L (N 27 (N 31 (N 32 L
  L L) L L) L L) L) L)) L L) L) (N 19 (N 23 L (N 24 (N 25 L (N 27 (N 32 (N 31 L (N 34 L L L) L) L
  L) L L) L) (N 27 (N 25 L (N 26 (N 31 (N 32 L L L) L L) L L) L) L L) L) (N 30 L (N 24 (N 25 L (N
  27 (N 32 (N 31 L (N 34 L L L) L) L L) L L) L) (N 27 (N 25 L (N 31 (N 32 L L L) L L) L) L L) L)
  L)) (N 25 (N 24 L (N 26 L (N 27 (N 31 (N 32 L L L) L L) L L) L) L) L L) L))) L) L L)) L (N 14 (N
  13 (N 18 L (N 20 (N 26 L (N 27 (N 33 L (N 34 L L L) L) L L) L) (N 24 (N 26 L (N 27 (N 31 L L (N
  19 L (N 25 (N 32 (N 33 L L L) L L) L L) L)) L L) L) L (N 19 (N 17 L (N 27 (N 34 L L L) L L) (N
  23 (N 25 L (N 27 L L L) L) (N 27 (N 25 L (N 32 (N 30 L (N 34 L L L) L) L L) L) L L) L)) (N 25 (N
  23 L (N 26 L (N 27 (N 32 (N 33 L L L) L L) L L) L) L) L L) L)) L) (N 19 (N 20 L (N 17 L (N 25 (N
  26 L (N 27 L L L) L) (N 27 (N 32 (N 33 L (N 34 L L L) L) L L) L L) L) (N 23 (N 25 L (N 27 L L L)
  L) (N 25 (N 26 L (N 27 L L L) L) (N 27 (N 32 (N 30 L (N 33 L (N 34 L L L) L) L) L L) L L) L) L))
  L) (N 25 (N 26 L (N 27 (N 32 (N 33 L (N 35 L L L) L) L L) L L) L) L L) L)) L (N 18 L (N 20 (N 19
  L (N 25 (N 26 L (N 27 (N 32 (N 33 L (N 34 L L L) L) L L) L L) L) L L) (N 24 (N 23 L (N 27 (N 17
  L (N 26 L (N 30 (N 31 L L L) L L) L) L) L L) L) L L)) (N 24 (N 23 L (N 27 (N 25 (N 26 L (N 33 (N
  31 L L (N 19 L (N 32 L L L) L)) L L) L) (N 32 (N 33 L (N 26 (N 34 L L L) L L) L) L L) L) L L) (N
  17 (N 30 L (N 34 (N 19 L (N 27 L L L) L) L L) L) (N 19 (N 27 (N 34 L L L) L L) L L) L)) L (N 31
  (N 19 (N 23 (N 27 L (N 17 L L (N 25 (N 26 L L L) L L)) L) (N 27 (N 25 L (N 32 (N 33 L (N 34 L L
  L) L) L L) L) L L) L) (N 25 (N 26 L (N 27 (N 23 L (N 32 (N 33 L L L) L L) L) L L) L) L L) L) L
  L)) L) (N 19 (N 20 L (N 24 (N 23 L (N 25 (N 26 L (N 27 L L L) L) (N 27 (N 32 (N 31 L (N 34 L L
  L) L) L L) L L) L) (N 17 (N 25 L (N 27 L L L) L) (N 25 (N 26 L (N 27 L L L) L) (N 27 (N 32 (N 31
  L (N 34 L L L) L) L L) L L) L) L)) (N 27 (N 25 L (N 31 (N 32 (N 33 L (N 34 L L L) L) L L) L L)
  L) L L) L) L) (N 25 (N 26 L (N 27 (N 32 (N 33 L (N 35 L L L) L) L L) L L) L) L L) L))) L L)))) L
  (N 8 (N 9 (N 12 (N 14 L L (N 20 L (N 13 (N 17 L (N 19 L (N 27 (N 34 (N 18 L L (N 23 L (N 30 L L
  L) L)) L L) L L) (N 23 L (N 27 (N 30 L L (N 18 (N 24 L (N 31 L L L) L) (N 24 (N 31 L L L) L L)
  L)) L L) (N 18 (N 24 L (N 31 L L L) L) (N 24 (N 31 L L L) L L) L))) (N 18 (N 24 L (N 31 L L L)
  L) (N 24 (N 31 L L L) L L) L)) L (N 23 L (N 30 L (N 17 L L (N 19 L (N 27 (N 34 (N 35 L L L) L L)
  L L) L)) L) L)) L)) L (N 13 (N 14 L L (N 19 L (N 20 (N 17 L (N 18 L (N 24 (N 31 L L L) L L) (N
  23 (N 25 L L (N 26 L (N 27 L L L) L)) (N 27 (N 25 L L (N 26 L (N 30 (N 32 L L (N 33 L (N 34 L L
  L) L)) L L) L)) L L) L)) (N 18 L (N 24 (N 31 L L L) L L) L)) (N 24 (N 25 L L (N 26 L (N 27 (N 23
  L (N 31 L (N 18 L L (N 17 L (N 30 (N 33 L L L) L L) L)) L) L) L L) L)) (N 27 (N 31 (N 18 L L (N
  23 L (N 32 L L (N 33 L (N 26 (N 34 L L L) L L) L)) L)) L L) L L) L) L) (N 18 (N 20 L (N 24 L (N
  31 L L L) L) L) (N 24 (N 31 L L L) L L) L))) L L)) L (N 12 (N 14 L L (N 13 (N 20 L (N 17 L (N 19
  L (N 27 (N 34 (N 18 L L (N 23 L (N 30 L L L) L)) L L) L L) (N 18 (N 23 L (N 27 (N 24 L (N 30 L L
  (N 31 (N 32 L (N 34 L L L) L) L L)) L) L L) (N 24 (N 25 L (N 27 L L L) L) (N 27 (N 31 (N 32 L (N
  34 L L L) L) L L) L L) L)) (N 24 (N 25 L (N 26 L (N 27 (N 31 (N 32 L L L) L L) L L) L) L) L L)
  L)) (N 18 (N 19 L (N 23 L (N 27 (N 24 L (N 31 (N 32 L L (N 25 (N 30 L (N 34 L L L) L) L L)) L L)
  L) L L) (N 25 (N 24 L (N 27 (N 30 L (N 34 L L L) L) L L) L) L L)) (N 23 L (N 24 (N 25 L (N 27 L
  L L) L) (N 27 (N 31 (N 32 L (N 34 L L L) L) L L) L L) L) (N 30 L (N 24 (N 25 L (N 27 L L L) L)
  (N 27 (N 31 (N 32 L (N 34 L L L) L) L L) L L) L) L))) (N 24 (N 26 L (N 27 (N 31 (N 33 L L L) L
  L) L L) L) L L) L)) L) L L)) L (N 13 (N 14 (N 19 L (N 20 (N 26 L (N 27 (N 33 L (N 34 L L L) L) L
  L) L) (N 24 (N 26 L (N 27 (N 33 (N 31 L (N 34 L L L) L) L L) L L) L) (N 27 (N 31 (N 33 L (N 26
  (N 34 L L L) L L) L) L L) L L) L) L) (N 18 (N 20 L (N 17 L (N 24 (N 26 L (N 27 L L L) L) (N 27
  (N 31 (N 33 L (N 34 L L L) L) L L) L L) L) (N 23 (N 24 L (N 27 L L L) L) (N 24 (N 26 L (N 27 L L
  L) L) (N 27 (N 31 (N 30 L (N 33 L (N 34 L L L) L) L) L L) L L) L) L)) L) (N 24 (N 26 L (N 27 (N
  31 (N 33 L (N 35 L L L) L) L L) L L) L) L L) L)) L (N 19 L (N 20 (N 18 L (N 24 (N 26 L (N 27 (N
  31 (N 33 L (N 34 L L L) L) L L) L L) L) L L) (N 25 (N 23 L (N 27 (N 17 L (N 26 L (N 30 (N 32 L L
  L) L L) L) L) L L) L) L L)) (N 24 (N 26 L (N 27 (N 33 (N 31 L (N 34 L L L) L) L L) L L) L) (N 27
  (N 31 (N 33 L (N 26 (N 34 L L L) L L) L) L L) L L) L) L) (N 18 (N 20 L (N 24 (N 26 L (N 27 L L
  L) L) (N 27 (N 31 (N 33 L (N 34 L L L) L) L L) L L) L) L) (N 24 (N 26 L (N 27 (N 31 (N 33 L (N
  35 L L L) L) L L) L L) L) L L) L))) L L))) L (N 9 (N 12 (N 20 L (N 13 (N 14 L L (N 23 (N 26 L (N
  27 L L L) L) (N 26 (N 33 L (N 34 (N 30 L (N 27 (N 35 L L L) L L) L) L L) L) (N 27 (N 33 (N 30 L
  (N 34 (N 35 L L L) L L) L) L L) L L) L) L)) L (N 14 (N 23 (N 26 L (N 27 L L L) L) (N 26 (N 33 L
  (N 34 (N 30 L (N 27 (N 35 L L L) L L) L) L L) L) (N 27 (N 33 (N 30 L (N 34 (N 35 L L L) L L) L)
  L L) L L) L) L) L (N 23 (N 26 L (N 27 L L L) L) (N 26 (N 27 (N 30 (N 33 L (N 34 L L L) L) (N 35
  (N 33 L (N 34 L L L) L) L L) L) (N 17 (N 30 L (N 33 (N 35 L L L) L L) L) L (N 18 (N 19 L L L) L
  L)) L) (N 27 (N 33 (N 30 L (N 34 (N 35 L L L) L L) L) L L) L L) L) L))) L) L (N 13 (N 14 L L L)
  L L)) L L))))) L (S 22 L L (S 29 L L L)))) (S 11 L L (S 16 (S 22 (S 29 L (N 14 (N 27 L (N 5 (N 8
  (N 9 L L (N 12 L L (N 30 L L (N 32 (N 33 L L L) L L)))) L (N 9 (N 13 L L (N 12 (N 30 L L (N 32
  (N 33 L L L) L L)) L (N 33 (N 30 L L (N 32 L L L)) L L))) L (N 32 (N 33 L L (N 30 (N 31 L L L) L
  L)) L L))) L (N 8 (N 12 L L (N 9 (N 13 L L L) L L)) L (N 9 (N 13 L L L) L L))) L) L L) (N 14 (N
  27 L (N 5 (N 8 (N 9 L L (N 12 L L (N 19 L (N 25 L L L) L))) L (N 9 (N 13 L L (N 12 (N 20 L (N 26
  L L L) L) L (N 18 L (N 24 L L (N 25 (N 26 L L L) L L)) (N 19 (N 20 L (N 25 L L L) L) (N 24 L L
  (N 25 (N 26 L L L) L L)) L)))) L (N 12 (N 13 L L (N 20 L (N 26 L L L) L)) L (N 13 (N 18 L (N 24
  L L (N 25 (N 26 L L L) L L)) (N 19 (N 20 L (N 26 L L L) L) (N 24 L L (N 25 (N 26 L L L) L L))
  L)) L (N 18 L (N 24 L L (N 25 (N 26 L L L) L L)) (N 24 L (N 19 (N 20 L L L) L L) L)))))) L (N 8
  (N 12 L L (N 9 (N 13 L L L) L L)) L (N 9 (N 13 L L L) L L))) L) L L)) (S 29 L L (N 14 (N 25 (N
  26 L L L) L L) L L)) (S 29 L L L)) (S 22 L L (S 29 L L L)) (S 22 L L L)))) (S 7 L L (S 11 L L (S
  16 (S 22 (S 29 L (N 9 (N 13 (N 14 L L L) L L) L L) L) (S 29 L (N 9 (N 13 (N 14 L L L) L L) L L)
  L) L) (S 22 L (S 29 L L L) L) L)))) (S 4 (S 7 (S 11 L (S 16 L (S 22 L (S 29 L L (N 9 L L (N 27
  (N 13 (N 12 L (N 14 (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L (N 24 L L (N 25 L L L))) L (N
  19 (N 25 L L L) L L)) L) L (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L (N 25 L L L)) L (N 19
  (N 25 L L L) L L)) L)) (N 14 (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L (N 24 L L (N 25 L L
  L))) L (N 19 (N 25 L L L) L L)) L) L (N 8 (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L (N 25 L
  L L)) L (N 19 (N 25 L L L) L L)) L) (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L (N 25 L L L))
  L (N 19 (N 25 L L L) L L)) L) L))) L (N 14 (N 12 L (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L
  (N 24 L L L)) L (N 19 (N 20 L L L) L L)) L) (N 5 (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L
  (N 24 L L L)) L (N 19 (N 20 L L L) L L)) L) (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L (N 24
  L L L)) L (N 19 (N 20 L L L) L L)) L) L)) L L)) L L))) (S 29 L L (N 9 L L (N 13 (N 12 L (N 14 (N
  17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L (N 5 L (N 23 (N 30 (N 8 L L (N 24 L (N 31 L L L) L))
  L L) L L) (N 8 (N 19 L L (N 24 L (N 23 (N 25 L (N 30 L (N 31 L L L) L) L) L L) L)) (N 23 (N 25 L
  (N 30 (N 32 L L L) L L) L) L L) L))) L (N 19 (N 20 L L (N 25 L (N 23 (N 32 L (N 8 L L (N 24 L (N
  30 (N 35 L L L) L L) L)) L) L L) L)) L L)) L) L (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L (N
  19 (N 5 L (N 23 (N 25 L (N 30 (N 8 L L (N 24 L (N 31 L L L) L)) L L) L) L L) (N 8 (N 25 L (N 23
  (N 30 L (N 32 L L L) L) L L) L) (N 23 (N 25 L (N 30 (N 32 L L L) L L) L) L L) L)) L L)) L (N 19
  (N 20 L L (N 23 (N 25 L (N 24 L (N 26 (N 27 (N 35 L (N 32 (N 30 L (N 34 L L L) L) L L) L) (N 34
  (N 32 L (N 30 (N 35 L L L) L L) L) L L) L) L (N 33 (N 32 L (N 8 (N 30 L L L) L L) L) L L)) (N 26
  (N 5 (N 8 L (N 30 L L L) L) (N 8 (N 30 L L L) L L) L) L L)) L) (N 25 (N 27 L L L) L L) L)) L L))
  L)) (N 14 (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L (N 5 L (N 19 (N 8 L (N 23 (N 30 (N 35 L
  (N 24 L (N 31 L L (N 32 L L L)) (N 25 L (N 32 L L L) L)) L) L L) L L) (N 24 L (N 31 L L L) L)) L
  (N 24 L (N 31 L L L) L)) (N 19 (N 8 L (N 25 L (N 32 L L L) L) L) L L))) L (N 19 (N 20 L L (N 8 L
  (N 25 L (N 32 L L L) L) L)) L L)) L) L (N 8 (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L (N 19
  (N 25 L (N 32 L (N 35 (N 5 L (N 23 (N 30 L L L) L L) (N 23 (N 30 L (N 34 L L L) L) (N 26 (N 34 L
  L L) L L) L)) L L) L) L) L L)) L (N 19 (N 20 L L (N 25 L (N 32 L (N 35 (N 23 (N 30 L (N 34 L L
  L) L) (N 26 (N 27 (N 34 L L L) L L) L L) L) L L) L) L)) L L)) L) (N 17 (N 18 L L (N 19 L L L))
  (N 18 (N 20 L L (N 19 (N 5 L (N 23 (N 25 L (N 30 (N 32 L L L) L L) L) L L) (N 23 (N 25 L (N 32
  (N 30 L (N 33 L L L) L) L L) L) (N 24 L L (N 25 (N 26 L L L) L L)) L)) L L)) L (N 19 (N 20 L L
  (N 23 (N 25 L (N 32 (N 30 L (N 33 L L L) L) L L) L) (N 25 (N 26 L L L) L L) L)) L L)) L) L))) L
  (N 14 (N 12 L (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L L (N 19 (N 8 L (N 23 (N 24 L (N 30 (N
  5 L L (N 25 L (N 32 L L L) L)) L L) L) L L) (N 5 (N 24 L (N 23 (N 30 L (N 31 L L L) L) L L) L)
  (N 23 (N 24 L (N 30 (N 31 L L L) L L) L) L L) L)) L (N 23 (N 24 L (N 25 L (N 26 (N 27 (N 35 L (N
  31 (N 30 L (N 34 L L L) L) L L) L) (N 34 (N 31 L (N 30 (N 35 L L L) L L) L) L L) L) L (N 33 (N
  31 L (N 5 (N 30 L L L) L L) L) L L)) (N 26 (N 5 (N 8 L (N 30 L L L) L) (N 8 (N 30 L L L) L L) L)
  L L)) L) (N 24 (N 27 L L L) L L) L))) L (N 19 (N 20 L L L) L L)) L) (N 5 (N 17 (N 18 L L (N 19 L
  L L)) (N 18 (N 20 L L (N 24 L (N 31 L (N 35 (N 19 (N 8 L (N 23 (N 30 L L L) L L) (N 23 (N 30 L
  (N 34 L L L) L) (N 26 (N 34 L L L) L L) L)) L (N 23 (N 30 L (N 34 L L L) L) (N 26 (N 27 (N 34 L
  L L) L L) L L) L)) L L) L) L)) L (N 19 (N 20 L L L) L L)) L) (N 17 (N 18 L L (N 19 L L L)) (N 18
  (N 20 L L (N 19 (N 8 L (N 23 (N 24 L (N 30 (N 31 L L L) L L) L) L L) (N 23 (N 24 L (N 31 (N 30 L
  (N 33 L L L) L) L L) L) (N 24 (N 26 L L L) L L) L)) L (N 23 (N 24 L (N 31 (N 30 L (N 33 L L L)
  L) L L) L) (N 24 (N 26 L L L) L L) L))) L (N 19 (N 20 L L L) L L)) L) L)) L L))))) (S 22 L L (S
  29 L L L))) (S 16 L (S 22 L (S 29 L (N 9 L L (N 27 (N 34 (N 35 L L L) L L) L L)) (N 9 L L (N 27
  (N 12 (N 13 L L (N 14 L L L)) (N 13 (N 14 (N 17 (N 23 L (N 20 (N 26 L L L) L L) L) (N 20 (N 26 L
  L L) L L) L) L (N 5 (N 31 L (N 30 (N 17 L (N 18 L L (N 19 (N 20 L L L) L L)) L) L L) L) (N 17 (N
  23 L (N 18 L L (N 19 L (N 20 (N 26 L L L) L L) L)) L) (N 20 (N 26 L L L) L L) L) L)) L (N 14 (N
  8 (N 32 L (N 30 (N 17 L (N 19 L L (N 18 (N 20 L L L) L L)) L) L L) L) (N 17 (N 23 L (N 19 L L (N
  18 L (N 20 (N 26 L L L) L L) L)) L) (N 20 (N 26 L L L) L L) L) L) L L)) L) L L))) (S 29 L L L))
  (S 22 L L L))) (S 11 L (S 16 (S 22 L (S 29 L L (N 9 (N 8 L (N 13 (N 14 L L (N 24 L L (N 5 L (N
  12 L (N 17 (N 23 (N 30 L L L) L L) L L) (N 32 (N 34 L (N 17 (N 18 L (N 31 L L (N 33 (N 19 (N 25
  L L (N 20 L (N 27 L L L) L)) L (N 26 (N 20 L (N 27 L L L) L) L L)) L L)) (N 19 (N 25 L L (N 20 L
  (N 26 (N 35 L L L) L L) L)) L (N 26 (N 27 L (N 35 L L L) L) L L))) (N 18 L L (N 23 (N 27 L L L)
  L L)) L) L) L L)) (N 12 L (N 17 (N 18 L (N 19 (N 20 L L (N 25 (N 32 L L L) L L)) L (N 20 (N 26
  (N 33 L L L) L L) L L)) (N 31 L (N 30 (N 23 L (N 34 L (N 19 (N 20 L L (N 25 (N 32 L L L) L L)) L
  (N 20 (N 26 (N 33 L L L) L L) L L)) L) L) L L) L)) (N 18 L L (N 23 (N 27 L L L) L L)) L) (N 25
  (N 27 L (N 17 (N 32 (N 19 L L (N 18 L (N 26 (N 34 L (N 35 L L L) L) L L) L)) L L) L L) L) L
  L))))) L (N 14 (N 17 (N 18 L (N 19 (N 25 L L (N 27 L (N 32 L L (N 34 L (N 20 L L (N 24 (N 31 L L
  L) L L)) L)) L)) L (N 20 L (N 12 (N 23 L (N 30 L (N 5 L L (N 33 (N 26 L L (N 24 (N 31 L L L) L
  L)) L L)) L) L) L (N 5 (N 23 L (N 24 L L (N 26 (N 25 L L (N 30 L (N 31 L L L) L)) L L)) L) (N 31
  (N 24 L L (N 26 (N 25 L L (N 30 L (N 35 L L L) L)) L L)) L L) L)) (N 24 (N 23 L (N 25 L L (N 31
  L (N 5 L L (N 30 (N 34 L L L) L L)) L)) L) L L))) (N 20 L (N 26 (N 25 L L (N 33 (N 12 L L (N 32
  L L (N 35 L (N 30 (N 34 L L L) L L) L))) L L)) L L) L)) (N 18 L L (N 20 L L L)) L) L (N 17 (N 18
  L (N 19 (N 27 L (N 34 L (N 20 L L (N 24 (N 25 L L L) L L)) L) L) L (N 26 (N 20 (N 24 L L (N 27 L
  (N 34 L (N 33 (N 35 L L L) L L) L) L)) (N 33 (N 35 L (N 30 (N 34 L L L) L L) L) L L) L) L L)) (N
  26 (N 19 (N 20 L (N 27 L (N 33 (N 34 L (N 35 L L L) L) L L) L) L) L (N 20 (N 24 L L (N 27 L (N
  34 L (N 33 (N 35 L L L) L L) L) L)) (N 33 (N 35 L (N 30 (N 34 L L L) L L) L) L L) L)) L L)) (N
  18 L L (N 20 (N 26 (N 27 L L L) L L) L L)) L))) (N 13 (N 14 L L (N 12 L (N 24 L L (N 33 (N 34 L
  (N 5 L (N 17 (N 18 L (N 31 L L (N 32 (N 20 (N 26 L L (N 19 L (N 27 L L L) L)) L (N 25 (N 19 L (N
  27 L L L) L) L L)) L L)) (N 20 (N 26 L L (N 19 L (N 25 (N 35 L L L) L L) L)) L (N 25 (N 27 L (N
  35 L L L) L) L L))) (N 18 L L (N 23 (N 27 L L L) L L)) L) (N 26 (N 20 L L (N 18 L (N 17 (N 25 (N
  27 L (N 35 L L L) L) L L) L L) L)) L L)) L) L L)) L)) L (N 14 (N 17 (N 18 L (N 20 L (N 12 (N 23
  L (N 30 L (N 35 (N 5 L (N 24 (N 25 L L (N 31 L L (N 33 L L L))) L (N 26 (N 33 L L L) L L)) (N 33
  (N 24 L L (N 26 L L L)) L L)) L L) L) L) L (N 5 (N 23 L (N 24 L L (N 25 (N 26 L L L) L L)) L) (N
  31 (N 24 L L (N 25 (N 26 L L L) L L)) L L) L)) (N 24 (N 23 L (N 25 L L (N 31 L (N 5 L L (N 26 (N
  34 (N 19 L (N 27 L (N 30 L L L) L) L) L L) L L)) L)) L) L L)) (N 20 L (N 26 (N 25 L L (N 33 (N
  12 L L (N 24 (N 5 L (N 23 L (N 31 L (N 30 (N 34 L L L) L L) L) L) L) L L)) L L)) L L) L)) (N 18
  L (N 5 (N 24 L L (N 20 L (N 23 (N 26 L L L) L L) L)) L (N 12 (N 20 L (N 23 (N 27 L L L) L L) (N
  24 (N 23 L (N 19 (N 25 L L (N 26 (N 27 (N 31 L (N 34 L L L) L) L L) L L)) L L) L) L L)) L L)) (N
  20 L (N 23 (N 24 L L (N 5 (N 26 L L L) L L)) L L) L)) L) L (N 12 (N 17 (N 23 L (N 30 L (N 33 (N
  35 (N 26 L L (N 18 L (N 20 L (N 24 (N 25 L L L) L L) L) L)) L L) L L) L) L) (N 18 L (N 5 (N 23 L
  (N 20 L L (N 24 L L L)) L) L (N 20 L (N 23 (N 27 L L L) L L) (N 24 (N 25 L L L) L L))) (N 20 L
  (N 23 (N 26 L L L) L L) L)) L) (N 33 (N 17 (N 18 L (N 20 (N 27 L (N 34 L (N 19 L L (N 25 (N 24 L
  L (N 26 (N 35 L L L) L L)) L L)) L) L) L (N 24 (N 25 L L L) L L)) (N 20 (N 26 (N 24 L L (N 27 L
  (N 31 L (N 30 (N 5 L (N 23 L (N 34 L L L) L) L) L L) L) L)) L L) L L)) (N 18 L L (N 20 (N 26 (N
  27 L L L) L L) L L)) L) L L) L)))) L (N 13 (N 12 L (N 14 (N 17 (N 18 L (N 19 L (N 8 (N 23 L (N
  30 L (N 5 L L (N 32 (N 25 L L (N 24 (N 31 L L L) L L)) L L)) L) L) L (N 5 (N 23 L (N 24 L L (N
  25 (N 26 L L (N 30 L (N 31 L L L) L)) L L)) L) (N 31 (N 24 L L (N 25 (N 26 L L (N 30 L (N 35 L L
  L) L)) L L)) L L) L)) (N 24 (N 23 L (N 26 L L (N 31 L (N 5 L L (N 30 (N 34 L L L) L L)) L)) L) L
  L)) (N 19 L (N 25 (N 26 L L (N 32 (N 8 L L (N 33 L L (N 35 L (N 30 (N 34 L L L) L L) L))) L L))
  L L) L)) (N 18 L L (N 19 L L L)) L) L (N 17 (N 18 L (N 20 (N 27 L (N 34 L (N 19 L L (N 24 (N 26
  L L L) L L)) L) L) L (N 25 (N 19 (N 24 L L (N 27 L (N 34 L (N 32 (N 35 L L L) L L) L) L)) (N 32
  (N 35 L (N 30 (N 34 L L L) L L) L) L L) L) L L)) (N 25 (N 19 (N 20 L L (N 24 L L (N 27 L (N 34 L
  (N 32 (N 35 L L L) L L) L) L))) (N 32 (N 35 L (N 30 (N 34 L L L) L L) L) L L) L) L L)) (N 18 L L
  (N 19 (N 25 (N 27 L L L) L L) L L)) L)) (N 14 (N 17 (N 18 L (N 19 L (N 8 (N 23 L (N 30 L (N 35
  (N 5 L (N 24 (N 26 L L (N 31 L L (N 32 L L L))) L (N 25 (N 32 L L L) L L)) (N 32 (N 24 L L (N 25
  L L L)) L L)) L L) L) L) L (N 5 (N 23 L (N 24 L L (N 25 (N 26 L L L) L L)) L) (N 31 (N 24 L L (N
  25 (N 26 L L L) L L)) L L) L)) (N 24 (N 23 L (N 26 L L (N 31 L (N 5 L L (N 25 (N 34 (N 20 L (N
  27 L (N 30 L L L) L) L) L L) L L)) L)) L) L L)) (N 19 L (N 25 (N 26 L L (N 32 (N 8 L L (N 24 (N
  5 L (N 23 L (N 31 L (N 30 (N 34 L L L) L L) L) L) L) L L)) L L)) L L) L)) (N 18 L (N 5 (N 24 L L
  (N 19 L (N 23 (N 25 L L L) L L) L)) L (N 8 (N 19 L (N 23 (N 27 L L L) L L) (N 24 (N 23 L (N 20
  (N 26 L L (N 25 (N 27 (N 31 L (N 34 L L L) L) L L) L L)) L L) L) L L)) L L)) (N 19 L (N 23 (N 24
  L L (N 5 (N 25 L L L) L L)) L L) L)) L) L (N 8 (N 17 (N 23 L (N 30 L (N 32 (N 35 (N 25 L L (N 18
  L (N 19 L (N 24 (N 26 L L L) L L) L) L)) L L) L L) L) L) (N 18 L (N 5 (N 23 L (N 19 L L (N 24 L
  L L)) L) L (N 19 L (N 23 (N 27 L L L) L L) (N 24 (N 26 L L L) L L))) (N 19 L (N 23 (N 25 L L L)
  L L) L)) L) (N 32 (N 17 (N 18 L (N 19 (N 27 L (N 34 L (N 20 L L (N 25 (N 35 L L L) L L)) L) L) L
  (N 24 (N 26 L L L) L L)) (N 19 (N 25 (N 24 L L (N 27 L (N 31 L (N 30 (N 5 L (N 23 L (N 34 L L L)
  L) L) L L) L) L)) L L) L L)) (N 18 L L (N 19 (N 25 (N 27 L L L) L L) L L)) L) L L) L))) L (N 14
  (N 17 (N 18 L (N 23 (N 24 L L (N 5 L (N 25 (N 26 L L L) L L) L)) (N 24 (N 25 (N 26 L L (N 19 L
  (N 8 (N 30 L (N 32 L L (N 5 L (N 12 L L (N 31 (N 33 L L L) L L)) L)) L) L (N 5 (N 30 L (N 31 L
  (N 12 L L (N 27 (N 34 L L L) L L)) L) L) (N 31 (N 30 L (N 35 L L L) L) L L) L)) (N 27 (N 34 L (N
  31 (N 30 L (N 35 L L L) L) L L) L) (N 35 (N 31 L (N 34 L L L) L) L L) L))) L (N 26 (N 20 L (N 12
  (N 30 L (N 33 L L (N 5 L (N 8 L L (N 31 (N 32 L L L) L L)) L)) L) L (N 5 (N 30 L (N 31 L (N 8 L
  L (N 27 (N 34 L L L) L L)) L) L) (N 31 (N 30 L (N 35 L L L) L) L L) L)) (N 27 (N 34 L (N 31 (N
  30 L (N 35 L L L) L) L L) L) (N 35 (N 31 L (N 34 L L L) L) L L) L)) L (N 27 (N 34 L (N 31 (N 30
  L (N 35 L L L) L) L L) L) (N 35 (N 31 L (N 34 L L L) L) L L) L))) L (N 25 (N 26 L L L) L L)) L)
  (N 24 (N 23 L (N 25 (N 26 L L L) L L) L) L L)) (N 18 L (N 5 (N 8 (N 12 L L (N 23 L (N 19 L L (N
  24 (N 26 L L (N 20 (N 27 (N 30 L (N 34 L L L) L) L L) L L)) L L)) L)) L (N 12 (N 23 L (N 20 L L
  (N 24 (N 25 L L (N 19 (N 27 (N 30 L (N 34 L L L) L) L L) L L)) L L)) L) L (N 23 (N 24 L L (N 25
  (N 26 L L L) L L)) (N 27 (N 19 (N 20 L L (N 24 (N 25 L L (N 26 (N 31 L (N 34 L L L) L) L L)) L
  L)) L (N 24 (N 25 (N 26 L L (N 20 (N 31 L (N 34 L L L) L) L L)) L L) L L)) L L) L))) L (N 8 (N
  12 L L L) L L)) (N 24 (N 23 L (N 19 (N 20 L L L) L L) L) L L)) L) L L)))) (S 29 L L (N 9 (N 8 L
  (N 13 (N 14 L L (N 5 L (N 12 L (N 17 (N 23 (N 30 L L L) L L) L L) (N 25 (N 27 L (N 32 (N 19 L L
  (N 34 L (N 35 L L L) L)) L L) L) L L)) (N 12 L (N 17 (N 18 L (N 19 (N 20 L L (N 25 (N 32 L L L)
  L L)) L (N 20 (N 26 (N 33 L L L) L L) L L)) (N 19 (N 20 L L (N 25 (N 32 L L L) L L)) L (N 20 (N
  26 (N 33 L L L) L L) L L))) (N 18 L L (N 23 (N 27 L (N 30 (N 34 L (N 35 L L L) L) L L) L) L L))
  L) (N 25 (N 27 L (N 32 (N 19 L L (N 18 L (N 17 (N 24 L L (N 26 (N 34 L (N 35 L L L) L) L L)) L
  L) L)) L L) L) L L)))) L (N 14 (N 17 (N 18 L (N 19 (N 25 L L (N 27 L (N 24 (N 23 L (N 26 (N 32 L
  L (N 31 L (N 34 L L L) L)) L L) L) L L) L)) L (N 20 L (N 12 (N 23 L (N 30 L (N 5 L L (N 26 (N 33
  L L L) L L)) L) L) L (N 5 (N 23 L (N 24 L L L) L) (N 24 (N 31 L L L) L L) L)) (N 23 (N 24 L (N
  27 L L L) L) (N 24 (N 25 L L (N 26 (N 31 L (N 5 L L (N 30 (N 34 L L L) L L)) L) L L)) L L) L)))
  (N 20 L (N 26 (N 25 L L (N 33 (N 12 L L (N 32 L L (N 35 L (N 5 (N 23 L (N 24 L L L) L) (N 19 (N
  23 L (N 30 L L L) L) L (N 23 (N 24 L (N 27 L L L) L) (N 24 (N 30 (N 27 L (N 34 L L L) L) L L) L
  L) L)) L) L))) L L)) L L) L)) (N 18 L L (N 20 L L L)) L) L (N 17 (N 18 L (N 19 (N 27 L (N 34 L
  (N 20 L L (N 24 (N 25 L L L) L L)) L) L) L (N 20 (N 27 L (N 26 (N 24 L L (N 12 L (N 25 (N 33 (N
  34 L (N 35 L L L) L) L L) L L) L)) L L) L) (N 26 (N 33 (N 35 L (N 12 (N 23 L (N 30 L L L) L) L
  (N 25 (N 24 L (N 27 L L L) L) L L)) L) L L) L L) L)) (N 19 (N 20 L (N 26 (N 27 L (N 33 (N 34 L
  (N 35 L L L) L) L L) L) L L) L) L (N 20 (N 27 L (N 34 L (N 35 (N 12 L (N 26 (N 33 L L L) L L) (N
  25 (N 32 L L L) L L)) L L) L) L) (N 26 (N 33 (N 35 L (N 12 (N 23 L (N 30 L L L) L) L (N 25 (N 24
  L (N 27 L L L) L) L L)) L) L L) L L) L))) (N 18 L L (N 20 (N 12 L (N 23 (N 26 (N 27 L (N 30 (N 5
  L L (N 24 L (N 31 L (N 35 L L L) L) L)) L L) L) L L) L L) (N 25 (N 24 L (N 23 (N 27 L (N 32 (N
  19 L L (N 31 L (N 35 L L L) L)) L L) L) L L) L) L L)) L L)) L))) (N 13 (N 14 L L (N 12 L (N 26
  (N 27 L (N 33 (N 20 L L (N 34 L (N 35 L L L) L)) L L) L) L L) L)) L (N 14 (N 17 (N 18 L (N 20 L
  (N 12 (N 23 L (N 30 L (N 35 (N 5 L (N 24 (N 25 L L (N 26 (N 27 L (N 34 L L L) L) L L)) L (N 25
  (N 26 L L L) L L)) (N 26 (N 33 L L L) L L)) L L) L) L) L (N 5 (N 23 L (N 24 L (N 31 L L L) L) L)
  (N 24 (N 31 L L L) L L) L)) (N 23 (N 24 L (N 27 L L L) L) (N 24 (N 31 L (N 5 L L (N 34 (N 19 L
  (N 25 L L (N 27 L (N 30 L L L) L)) L) L L)) L) (N 27 (N 31 (N 5 L L (N 12 (N 19 L (N 25 L L (N
  30 L (N 34 L L L) L)) L) L L)) L L) L L) L) L)) (N 20 L (N 26 (N 33 (N 12 L L (N 35 L (N 5 (N 23
  L (N 30 L L L) L) (N 19 (N 23 L (N 30 L L L) L) (N 25 L L (N 32 L L (N 23 (N 24 L (N 27 L L L)
  L) (N 24 (N 30 (N 27 L (N 34 L L L) L) L L) L L) L))) L) L) L)) L L) L L) L)) (N 18 L (N 5 (N 12
  (N 23 L (N 27 (N 30 L (N 34 (N 35 L L L) L L) L) L L) L) L (N 24 L (N 31 L L L) L)) L (N 12 (N
  20 L (N 26 (N 33 L L L) L L) (N 19 (N 23 (N 24 L (N 27 L L L) L) (N 27 (N 34 L (N 30 (N 31 L L
  L) L L) L) L L) L) (N 27 (N 23 L (N 25 L L (N 34 (N 30 L (N 35 L L L) L) L L)) L) L L) L)) L L))
  (N 20 L (N 26 (N 33 (N 12 L L (N 5 (N 23 L (N 24 L (N 27 (N 30 L (N 35 L L L) L) L L) L) L) L
  L)) L L) L L) L)) L) L (N 12 (N 17 (N 23 L (N 30 L (N 35 (N 5 L (N 26 (N 33 L L L) L L) (N 18 L
  (N 20 L (N 26 (N 33 L L L) L L) (N 19 (N 27 L (N 24 (N 25 L L L) L L) L) (N 25 (N 32 L L L) L L)
  L)) (N 20 L (N 26 (N 33 L L L) L L) L))) L L) L) L) (N 18 L (N 5 (N 23 L (N 27 (N 30 L (N 34 (N
  35 L L L) L L) L) L L) L) L (N 20 L (N 26 (N 23 L (N 27 (N 33 (N 30 L (N 35 L L L) L) L L) L L)
  L) L L) (N 19 (N 23 (N 24 L (N 27 L L L) L) (N 27 (N 25 L (N 32 (N 31 L (N 34 L L L) L) L L) L)
  L L) L) (N 25 (N 27 L L L) L L) L))) (N 20 L (N 26 (N 23 L (N 27 (N 33 (N 30 L (N 35 L L L) L) L
  L) L L) L) L L) L)) L) (N 26 (N 33 (N 35 L (N 17 (N 18 L (N 20 (N 27 L (N 34 L L L) L) L (N 19
  (N 27 L (N 34 L L L) L) (N 25 (N 24 L (N 27 L L L) L) L L) L)) (N 20 (N 27 L (N 34 L L L) L) L
  L)) (N 18 L L (N 20 (N 27 L (N 34 L L L) L) L L)) L) L) L L) L L) L)))) L (N 13 (N 12 L (N 14 (N
  17 (N 18 L (N 19 L (N 8 (N 23 L (N 30 L (N 5 L L (N 25 (N 32 L L L) L L)) L) L) L (N 5 (N 23 L
  (N 24 L L L) L) (N 24 (N 31 L L L) L L) L)) (N 20 (N 26 L L (N 27 L (N 24 (N 23 L (N 25 (N 31 L
  (N 34 L L L) L) L L) L) L L) L)) L (N 23 (N 24 L (N 27 L L L) L) (N 24 (N 26 L L (N 25 (N 31 L
  (N 5 L L (N 30 (N 34 L L L) L L)) L) L L)) L L) L))) (N 19 L (N 25 (N 26 L L (N 32 (N 8 L L (N
  33 L L (N 35 L (N 5 (N 23 L (N 24 L L L) L) (N 20 (N 23 L (N 30 L L L) L) L (N 23 (N 24 L (N 27
  L L L) L) (N 24 (N 30 (N 27 L (N 34 L L L) L) L L) L L) L)) L) L))) L L)) L L) L)) (N 18 L L (N
  19 L L L)) L) L (N 17 (N 18 L (N 20 (N 27 L (N 34 L (N 19 L L (N 24 (N 26 L L L) L L)) L) L) L
  (N 19 (N 27 L (N 25 (N 24 L L (N 8 L (N 26 (N 32 (N 34 L (N 35 L L L) L) L L) L L) L)) L L) L)
  (N 25 (N 32 (N 35 L (N 8 (N 23 L (N 30 L L L) L) L (N 26 (N 24 L (N 27 L L L) L) L L)) L) L L) L
  L) L)) (N 19 (N 20 L L (N 27 L (N 34 L (N 35 (N 8 L (N 25 (N 32 L L L) L L) (N 26 (N 33 L L L) L
  L)) L L) L) L)) (N 25 (N 32 (N 35 L (N 8 (N 23 L (N 30 L L L) L) L (N 26 (N 24 L (N 27 L L L) L)
  L L)) L) L L) L L) L)) (N 18 L L (N 19 (N 8 L (N 23 (N 25 (N 27 L (N 30 (N 5 L L (N 24 L (N 31 L
  (N 35 L L L) L) L)) L L) L) L L) L L) (N 26 (N 24 L (N 23 (N 27 L (N 33 (N 20 L L (N 31 L (N 35
  L L L) L)) L L) L) L L) L) L L)) L L)) L)) (N 14 (N 17 (N 18 L (N 19 L (N 8 (N 23 L (N 30 L (N
  35 (N 5 L (N 24 (N 26 L L (N 25 (N 27 L (N 34 L L L) L) L L)) L (N 25 (N 26 L L L) L L)) (N 25
  (N 32 L L L) L L)) L L) L) L) L (N 5 (N 23 L (N 24 L (N 31 L L L) L) L) (N 24 (N 31 L L L) L L)
  L)) (N 23 (N 24 L (N 27 L L L) L) (N 24 (N 31 L (N 5 L L (N 34 (N 20 L (N 26 L L (N 27 L (N 30 L
  L L) L)) L) L L)) L) (N 27 (N 31 (N 5 L L (N 8 (N 20 L (N 26 L L (N 30 L (N 34 L L L) L)) L) L
  L)) L L) L L) L) L)) (N 19 L (N 25 (N 32 (N 8 L L (N 35 L (N 5 (N 23 L (N 30 L L L) L) (N 20 (N
  23 L (N 30 L L L) L) (N 26 L L (N 33 L L (N 23 (N 24 L (N 27 L L L) L) (N 24 (N 30 (N 27 L (N 34
  L L L) L) L L) L L) L))) L) L) L)) L L) L L) L)) (N 18 L (N 5 (N 8 (N 23 L (N 27 (N 30 L (N 34
  (N 35 L L L) L L) L) L L) L) L (N 24 L (N 31 L L L) L)) L (N 8 (N 19 L (N 25 (N 32 L L L) L L)
  (N 20 (N 23 (N 24 L (N 27 L L L) L) (N 27 (N 34 L (N 30 (N 31 L L L) L L) L) L L) L) (N 27 (N 23
  L (N 26 L L (N 34 (N 30 L (N 35 L L L) L) L L)) L) L L) L)) L L)) (N 19 L (N 25 (N 32 (N 8 L L
  (N 5 (N 23 L (N 24 L (N 27 (N 30 L (N 35 L L L) L) L L) L) L) L L)) L L) L L) L)) L) L (N 8 (N
  17 (N 23 L (N 30 L (N 35 (N 5 L (N 25 (N 32 L L L) L L) (N 18 L (N 19 L (N 25 (N 32 L L L) L L)
  (N 20 (N 27 L (N 24 (N 26 L L L) L L) L) (N 26 (N 33 L L L) L L) L)) (N 19 L (N 25 (N 32 L L L)
  L L) L))) L L) L) L) (N 18 L (N 5 (N 23 L (N 27 (N 30 L (N 34 (N 35 L L L) L L) L) L L) L) L (N
  19 L (N 25 (N 23 L (N 27 (N 32 (N 30 L (N 35 L L L) L) L L) L L) L) L L) (N 20 (N 23 (N 24 L (N
  27 L L L) L) (N 27 (N 26 L (N 33 (N 31 L (N 34 L L L) L) L L) L) L L) L) (N 26 (N 27 L L L) L L)
  L))) (N 19 L (N 25 (N 23 L (N 27 (N 32 (N 30 L (N 35 L L L) L) L L) L L) L) L L) L)) L) (N 25 (N
  32 (N 35 L (N 17 (N 18 L (N 19 (N 27 L (N 34 L L L) L) L (N 20 (N 27 L (N 34 L L L) L) (N 26 (N
  24 L (N 27 L L L) L) L L) L)) (N 19 (N 27 L (N 34 L L L) L) L L)) (N 18 L L (N 19 (N 27 L (N 34
  L L L) L) L L)) L) L) L L) L L) L))) L (N 14 (N 17 (N 18 L (N 23 (N 27 L (N 24 L L (N 5 L (N 8 L
  (N 12 L (N 30 L L L) L) L) L)) L) (N 27 (N 34 L (N 19 L (N 20 L L (N 31 (N 30 L (N 35 L L L) L)
  L L)) (N 31 (N 30 L (N 35 L L L) L) L L)) L) (N 24 (N 25 (N 26 L L (N 5 (N 30 L (N 31 L L L) L)
  (N 31 (N 30 L (N 35 L L L) L) L L) L)) L (N 26 (N 5 (N 30 L (N 31 L L L) L) (N 31 (N 30 L (N 35
  L L L) L) L L) L) L L)) L (N 25 (N 26 L L L) L L)) L) L) (N 5 (N 23 L (N 30 L (N 35 (N 8 L (N 12
  L L (N 19 (N 20 L (N 24 (N 25 L L L) L L) L) L L)) (N 12 L (N 20 (N 19 L (N 24 (N 26 L L L) L L)
  L) L L) (N 19 (N 20 L (N 26 (N 33 L L L) L L) L) (N 25 (N 32 L L L) L L) L))) L L) L) L) (N 19
  (N 20 L (N 26 (N 23 L (N 25 L L L) L) L L) L) (N 25 (N 26 L (N 20 (N 23 L L L) L L) L) L L) L)
  L)) (N 18 L (N 5 (N 8 (N 12 L L (N 23 L (N 27 (N 30 L (N 34 (N 35 L L L) L L) L) L L) L)) L (N
  12 (N 23 L (N 27 (N 30 L (N 34 (N 35 L L L) L L) L) L L) L) L (N 23 (N 24 L (N 27 L L L) L) (N
  27 (N 24 (N 31 L (N 34 (N 35 L L L) L L) L) (N 31 (N 30 L (N 35 L L L) L) L L) L) L L) L))) L (N
  8 (N 12 L L L) L L)) (N 5 (N 19 (N 20 L (N 8 L L (N 26 (N 25 L (N 27 (N 23 L (N 32 (N 33 L L L)
  L L) L) L L) L) L L)) L) (N 25 (N 26 L (N 20 (N 12 L L (N 27 (N 23 L (N 32 (N 33 L L L) L L) L)
  L L)) L L) L) L L) L) (N 19 (N 20 L L L) L L) L)) L) L L))))) (S 22 L L (S 29 L L (N 9 (N 8 L (N
  13 (N 14 L L (N 18 L L (N 5 L (N 12 L (N 17 (N 23 (N 30 L L L) L L) L L) (N 25 (N 32 (N 19 L L
  (N 20 (N 27 L (N 23 (N 34 L (N 35 L L L) L) L L) L) L L)) L L) L L)) (N 12 L (N 17 (N 19 (N 20
  (N 27 L (N 23 (N 30 L (N 34 L L L) L) L L) L) L (N 25 (N 32 L L L) L L)) L (N 20 (N 26 (N 33 L L
  L) L L) L L)) (N 23 (N 30 (N 35 L (N 19 (N 20 (N 24 L (N 31 L L (N 32 (N 25 L L (N 26 (N 33 L L
  L) L L)) L L)) (N 25 (N 26 (N 27 L (N 34 L L L) L) L L) L L)) L (N 25 (N 32 L L L) L L)) L (N 20
  (N 26 (N 33 L L L) L L) L L)) L) L L) L L) L) (N 19 (N 25 (N 32 L L L) L L) L L))))) L (N 14 (N
  17 (N 18 L L (N 20 (N 19 L L (N 5 L (N 12 L (N 23 (N 30 L L L) L L) (N 23 (N 24 L (N 25 L L (N
  27 L (N 30 L (N 31 (N 34 L L L) L L) L) L)) L) (N 24 (N 27 L L L) L L) L)) (N 12 L (N 26 (N 33 L
  L L) L L) L))) L L)) (N 18 (N 19 L L (N 5 L (N 23 (N 30 (N 12 L L (N 24 L (N 31 L L L) L)) L L)
  L L) (N 12 (N 20 (N 26 L (N 33 L L L) L) L (N 24 L (N 23 (N 26 L (N 30 L (N 31 L L L) L) L) L L)
  L)) (N 23 (N 26 (N 25 L L (N 24 L (N 27 L (N 30 (N 32 L L (N 31 L (N 35 L L L) L)) L L) L) L)) L
  L) L L) L))) L (N 20 (N 19 L L (N 23 (N 24 L (N 25 (N 26 L (N 32 L L (N 33 (N 12 L L (N 30 L (N
  34 L L L) L)) L L)) L) L (N 26 (N 27 L (N 33 L (N 12 L L (N 5 L (N 30 (N 31 L L L) L L) L)) L)
  L) (N 33 (N 12 L L (N 32 L L (N 34 L (N 27 (N 30 L L L) L L) L))) L L) L)) (N 25 (N 26 L (N 12
  (N 33 L L L) L L) L) L L)) (N 26 (N 27 L L L) L L) L)) L L)) L) L (N 17 (N 18 L L (N 20 (N 12 L
  (N 26 (N 27 L (N 23 (N 30 L (N 5 L L (N 24 L (N 31 (N 32 L L (N 33 (N 34 L L L) L L)) L L) L))
  L) L L) L) L L) (N 25 (N 24 L (N 23 (N 5 L (N 27 L (N 30 L (N 31 (N 32 L L L) L L) L) L) L) L L)
  L) L L)) L L)) (N 18 (N 19 L L (N 20 (N 5 L (N 23 (N 30 (N 12 L L (N 24 L (N 31 L L L) L)) L L)
  L L) (N 12 (N 23 (N 26 L (N 30 L (N 31 L L (N 24 L (N 32 (N 33 L L L) L L) L)) L) L) (N 24 L L
  (N 25 (N 26 L L L) L L)) L) (N 23 (N 26 (N 25 L L (N 24 L (N 27 L (N 30 (N 34 L L L) L L) L) L))
  L L) L L) L)) L L)) L (N 20 (N 19 (N 23 (N 24 L (N 25 (N 27 L (N 32 L L (N 12 L (N 26 (N 30 (N
  34 L L L) L L) L L) L)) L) L (N 12 (N 26 L (N 30 L (N 5 L L (N 31 (N 33 L L L) L L)) L) L) (N 26
  (N 27 L (N 30 (N 34 L L L) L L) L) L L) L)) (N 25 (N 12 L (N 5 (N 30 L L L) L L) L) L L)) (N 26
  (N 27 L L L) L L) L) L (N 23 (N 24 L (N 25 (N 26 (N 27 L (N 34 (N 30 L (N 33 L L L) L) L L) L)
  (N 33 (N 34 L (N 27 (N 30 L L L) L L) L) L L) L) L (N 32 (N 12 (N 26 L (N 30 L (N 5 L L (N 31 L
  L L)) L) L) (N 26 (N 27 L (N 30 (N 34 L L L) L L) L) L L) L) L L)) (N 25 (N 5 (N 12 L (N 30 L L
  L) L) (N 12 (N 30 L L L) L L) L) L L)) (N 26 (N 27 L L L) L L) L)) L L)) L))) (N 13 (N 14 L L (N
  12 L (N 18 L L (N 26 (N 33 (N 20 L L (N 5 L (N 19 (N 27 L (N 23 (N 34 L (N 35 L L L) L) L L) L)
  L L) L)) L L) L L)) L)) L (N 14 (N 17 (N 18 L L (N 20 (N 19 L L (N 12 L (N 26 (N 33 L L L) L L)
  L)) L L)) (N 18 (N 19 L L (N 5 L (N 20 (N 23 (N 24 L (N 31 L L (N 12 (N 26 L (N 33 L L L) L) (N
  26 (N 33 L L L) L L) L)) (N 12 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L) L)) (N 24 L L (N
  12 (N 26 L L L) L L)) L) L (N 24 L (N 31 L L L) L)) (N 20 (N 12 (N 26 L (N 33 L L L) L) (N 26 (N
  33 L L L) L L) L) L L))) L (N 20 (N 19 L L (N 12 (N 26 L (N 33 L L L) L) (N 26 (N 33 L L L) L L)
  L)) L L)) L) L (N 12 (N 17 (N 18 L L (N 20 L L L)) (N 18 (N 19 L L (N 20 (N 5 L (N 23 (N 26 L (N
  30 L (N 31 L L (N 32 (N 33 L L L) L L)) L) L) (N 24 L L (N 25 (N 26 L L L) L L)) L) (N 23 (N 26
  L (N 30 L (N 32 (N 33 L L L) L L) L) L) (N 25 (N 26 L L L) L L) L)) L L)) L (N 20 (N 19 (N 5 L
  (N 23 (N 26 L (N 30 L (N 33 (N 34 L L L) L L) L) L) (N 26 (N 27 L L L) L L) L) (N 23 (N 24 L (N
  26 L (N 30 L (N 33 (N 34 L L L) L L) L) L) L) (N 26 (N 27 L L L) L L) L)) L (N 23 (N 26 L (N 30
  L (N 32 (N 33 (N 34 L L L) L L) L L) L) L) (N 25 (N 26 (N 27 L L L) L L) L L) L)) L L)) L) (N 26
  (N 33 (N 35 L (N 17 (N 18 L L (N 20 (N 27 L (N 34 L L L) L) L L)) (N 18 (N 19 L L (N 20 (N 25 L
  (N 32 L L L) L) L L)) L (N 20 (N 27 L (N 34 L L L) L) L L)) L) L) L L) L L) L)))) L (N 13 (N 12
  L (N 14 (N 17 (N 18 L L (N 19 (N 20 L L (N 5 L (N 8 L (N 23 (N 30 L L L) L L) (N 23 (N 24 L (N
  26 L L (N 27 L (N 30 L (N 31 (N 34 L L L) L L) L) L)) L) (N 24 (N 27 L L L) L L) L)) (N 8 L (N
  25 (N 32 L L L) L L) L))) L L)) (N 18 (N 20 L L (N 5 L (N 23 (N 30 (N 8 L L (N 24 L (N 31 L L L)
  L)) L L) L L) (N 8 (N 19 (N 25 L (N 32 L L L) L) L (N 24 L (N 23 (N 25 L (N 30 L (N 31 L L L) L)
  L) L L) L)) (N 23 (N 25 (N 26 L L (N 24 L (N 27 L (N 30 (N 32 (N 34 L L L) L L) L L) L) L)) L L)
  L L) L))) L (N 19 (N 20 L L (N 23 (N 24 L (N 25 (N 26 L L (N 27 L (N 32 L (N 8 L L (N 5 L (N 30
  (N 31 L L L) L L) L)) L) L)) (N 32 (N 8 L L (N 33 L L (N 34 L (N 27 (N 30 L L L) L L) L))) L L)
  L) (N 26 (N 25 L (N 8 (N 32 L L L) L L) L) L L)) (N 25 (N 27 L L L) L L) L)) L L)) L) L (N 17 (N
  18 L L (N 19 (N 8 L (N 25 (N 27 L (N 23 (N 30 L (N 5 L L (N 24 L (N 31 (N 32 (N 34 L L L) L L) L
  L) L)) L) L L) L) L L) (N 26 (N 24 L (N 23 (N 5 L (N 27 L (N 30 L (N 31 (N 33 L L L) L L) L) L)
  L) L L) L) L L)) L L)) (N 18 (N 20 L L (N 19 (N 5 L (N 23 (N 30 (N 8 L L (N 24 L (N 31 L L L)
  L)) L L) L L) (N 8 (N 23 (N 25 L (N 30 L (N 31 L L (N 24 L (N 32 (N 33 L L L) L L) L)) L) L) (N
  24 L L (N 25 (N 26 L L L) L L)) L) (N 23 (N 25 (N 26 L L (N 24 L (N 27 L (N 30 (N 34 L L L) L L)
  L) L)) L L) L L) L)) L L)) L (N 19 (N 20 (N 23 (N 24 L (N 25 (N 27 L (N 34 (N 30 L (N 32 L L L)
  L) L L) L) (N 32 (N 34 L (N 27 (N 30 L L L) L L) L) L L) L) (N 26 (N 8 L (N 5 (N 30 L L L) L L)
  L) L L)) (N 25 (N 27 L L L) L L) L) L (N 23 (N 24 L (N 25 (N 27 L (N 34 (N 30 L (N 32 L L L) L)
  L L) L) (N 32 (N 34 L (N 27 (N 30 L L L) L L) L) L L) L) (N 26 (N 5 (N 8 L (N 30 L L L) L) (N 8
  (N 30 L L L) L L) L) L L)) (N 25 (N 27 L L L) L L) L)) L L)) L)) (N 14 (N 17 (N 18 L L (N 19 (N
  20 L L (N 8 L (N 25 (N 32 L L L) L L) L)) L L)) (N 18 (N 20 L L (N 5 L (N 19 (N 23 (N 24 L (N 31
  L L (N 8 (N 25 L (N 32 L L L) L) (N 25 (N 32 L L L) L L) L)) (N 8 (N 25 L (N 32 L L L) L) (N 25
  (N 32 L L L) L L) L)) (N 24 L L (N 8 (N 25 L L L) L L)) L) L (N 24 L (N 31 L L L) L)) (N 19 (N 8
  (N 25 L (N 32 L L L) L) (N 25 (N 32 L L L) L L) L) L L))) L (N 19 (N 20 L L (N 8 (N 25 L (N 32 L
  L L) L) (N 25 (N 32 L L L) L L) L)) L L)) L) L (N 8 (N 17 (N 18 L L (N 19 L L L)) (N 18 (N 20 L
  L (N 19 (N 5 L (N 23 (N 25 L (N 30 L (N 31 L L (N 32 (N 33 L L L) L L)) L) L) (N 24 L L (N 25 (N
  26 L L L) L L)) L) (N 23 (N 25 L (N 30 L (N 32 (N 33 L L L) L L) L) L) (N 25 (N 26 L L L) L L)
  L)) L L)) L (N 19 (N 20 (N 5 L (N 23 (N 25 L (N 30 L (N 32 (N 34 L L L) L L) L) L) (N 25 (N 27 L
  L L) L L) L) (N 23 (N 24 L (N 25 L (N 30 L (N 32 (N 34 L L L) L L) L) L) L) (N 25 (N 27 L L L) L
  L) L)) L (N 23 (N 25 L (N 30 L (N 32 (N 34 L L L) L L) L) L) (N 25 (N 27 L L L) L L) L)) L L))
  L) (N 25 (N 32 (N 35 L (N 17 (N 18 L L (N 19 (N 27 L (N 34 L L L) L) L L)) (N 18 (N 20 L L (N 19
  (N 26 L (N 33 L L L) L) L L)) L (N 19 (N 27 L (N 34 L L L) L) L L)) L) L) L L) L L) L))) L (N 14
  (N 17 (N 18 L L (N 19 (N 20 L L L) L L)) (N 18 (N 19 (N 20 L L (N 23 (N 24 L (N 27 (N 34 L (N 30
  (N 31 L (N 35 L L L) L) L L) L) (N 34 (N 31 L (N 30 (N 35 L L L) L L) L) L L) L) L) (N 27 (N 24
  L (N 25 L L (N 5 (N 12 L L (N 26 (N 31 L (N 34 L L L) L) L L)) L L)) L) L L) L)) L (N 20 (N 23
  (N 24 L (N 27 (N 34 L (N 30 (N 31 L (N 35 L L L) L) L L) L) (N 34 (N 31 L (N 30 (N 35 L L L) L
  L) L) L L) L) L) (N 27 (N 24 L (N 26 L L (N 5 (N 8 L L (N 25 (N 31 L (N 34 L L L) L) L L)) L L))
  L) L L) L) L (N 23 (N 24 L (N 27 (N 30 (N 31 L (N 35 L L L) L) (N 34 (N 31 L (N 35 L L L) L) L
  L) L) (N 34 (N 31 L (N 30 (N 35 L L L) L L) L) L L) L) L) (N 27 (N 24 L (N 5 (N 31 L (N 34 (N 35
  L L L) L L) L) L (N 8 (N 12 L L L) L L)) L) L L) L))) L (N 19 (N 20 L L L) L L)) L) L L))))) (S
  22 L L (S 29 L L L))) (S 16 (S 22 L (S 29 L (N 35 (N 9 (N 8 L (N 12 (N 13 L L (N 14 (N 18 L (N
  17 (N 5 L (N 19 (N 25 L L (N 27 L (N 32 L L (N 34 L (N 20 L L (N 24 (N 31 L L L) L L)) L)) L)) L
  (N 20 L (N 23 L (N 30 L L (N 31 (N 24 L L (N 26 L L L)) L L)) (N 24 (N 25 L L (N 26 (N 27 L (N
  34 L L L) L) L L)) L L)) (N 24 (N 31 L L L) L L))) (N 19 (N 25 L L (N 27 L (N 32 L L (N 34 L (N
  20 L L (N 24 (N 31 L L L) L L)) L)) L)) L (N 20 L (N 23 L (N 24 (N 25 L L (N 31 L L (N 33 L L
  L))) L (N 26 (N 31 L L L) L L)) (N 24 (N 31 L L L) L L)) (N 24 (N 31 L L L) L L)))) L (N 19 (N
  25 L L (N 32 L L (N 20 L (N 24 (N 31 L L (N 33 L L L)) L (N 26 (N 33 L L L) L L)) (N 24 (N 31 L
  L L) L L)))) L (N 20 L (N 24 (N 25 L L (N 31 L L (N 33 L L L))) L (N 26 (N 33 L L L) L L)) L)))
  (N 20 L (N 17 (N 26 (N 33 L L L) L L) L L) L)) L (N 20 L (N 26 (N 33 L L L) L L) L))) (N 13 (N
  14 L L (N 24 L L (N 31 L L (N 5 L (N 17 (N 18 L (N 19 (N 27 L (N 34 L (N 20 L L (N 25 (N 32 L L
  L) L L)) L) L) L (N 26 (N 33 L L L) L L)) (N 19 (N 27 L (N 34 L (N 20 L (N 23 (N 30 L L (N 32 L
  L L)) L (N 25 (N 26 (N 30 L L (N 32 L L L)) L L) L L)) (N 25 (N 32 L L L) L L)) L) L) L (N 26 (N
  33 L L L) L L))) L (N 19 (N 18 L (N 23 (N 27 L (N 30 L L (N 32 (N 25 L L (N 26 L L L)) L L)) L)
  L (N 25 (N 26 (N 27 L (N 30 (N 32 L L (N 33 L L L)) L L) L) L L) L L)) (N 20 (N 27 L (N 34 L (N
  23 (N 30 L L (N 32 (N 25 L L (N 26 L L L)) L L)) L (N 25 (N 26 (N 30 (N 32 L L (N 33 L L L)) L
  L) L L) L L)) L) L) (N 23 (N 27 L (N 30 L L (N 32 (N 25 L L (N 26 L L L)) L L)) L) L (N 25 (N 26
  (N 27 L (N 30 (N 32 L L (N 33 L L L)) L L) L) L L) L L)) L)) L L)) (N 18 L (N 17 (N 26 (N 33 L L
  L) L L) L L) L))))) L (N 14 (N 18 L (N 17 (N 19 (N 25 L L (N 27 L (N 32 L L (N 34 L (N 20 L L (N
  24 (N 31 L L L) L L)) L)) L)) L (N 20 L (N 24 (N 25 L L (N 31 L L (N 33 L L L))) L (N 26 (N 33 L
  L L) L L)) (N 24 (N 31 L L L) L L))) L (N 19 (N 25 L L (N 32 L L (N 20 L (N 24 (N 31 L L (N 33 L
  L L)) L (N 26 (N 33 L L L) L L)) (N 24 (N 31 L L L) L L)))) L (N 20 L (N 24 (N 25 L L (N 31 L L
  (N 33 L L L))) L (N 26 (N 33 L L L) L L)) L))) (N 20 L (N 17 (N 26 (N 33 L L L) L L) L L) L)) L
  (N 26 (N 33 L L L) L L))) L) (N 12 (N 13 L L (N 14 (N 18 L (N 20 L (N 24 (N 25 L L (N 23 L (N 26
  (N 27 L (N 34 L L L) L) L L) L)) L (N 26 (N 33 L L L) L L)) (N 24 (N 31 L L L) L L)) (N 20 L (N
  26 (N 33 L L L) L L) L)) L (N 20 L (N 26 (N 33 L L L) L L) L))) (N 13 (N 14 L L (N 24 L L (N 31
  L L (N 5 L (N 18 L (N 17 (N 25 (N 27 L (N 32 L L (N 33 L L L)) L) L (N 26 (N 32 L L L) L L)) L
  (N 25 (N 32 L L L) L L)) (N 25 (N 27 L (N 32 L L (N 33 L L L)) L) L (N 26 (N 32 L L L) L L))) (N
  18 L (N 17 (N 26 (N 33 L L L) L L) L L) L))))) L (N 14 (N 18 L (N 17 (N 20 L (N 24 (N 25 L L (N
  23 L (N 26 (N 27 L (N 34 L L L) L) L L) L)) L (N 26 (N 33 L L L) L L)) (N 24 (N 31 L L L) L L))
  L (N 25 (N 32 L L L) L L)) (N 20 L (N 17 (N 26 (N 33 L L L) L L) L L) L)) L (N 26 (N 33 L L L) L
  L))) L)) L (N 12 (N 13 L L (N 14 (N 8 L (N 18 L (N 17 (N 5 L (N 19 (N 27 L (N 34 L (N 20 L L (N
  24 (N 31 L L L) L L)) L) L) L (N 24 (N 31 L L L) L L)) (N 24 (N 31 L L L) L L)) L (N 19 (N 20 L
  (N 24 (N 25 L L (N 31 L L L)) L (N 25 (N 26 L L L) L L)) (N 24 (N 31 L L L) L L)) L (N 20 L (N
  24 (N 31 L L L) L L) L))) (N 19 (N 20 L (N 17 (N 5 L (N 24 (N 25 L L L) L L) L) L L) L) L L)) L)
  L L)) (N 13 (N 14 (N 18 L (N 17 (N 19 L (N 8 (N 5 L (N 23 L (N 30 L L (N 24 (N 26 L L (N 31 L L
  (N 32 L L L))) L (N 25 (N 32 L L L) L L))) (N 24 (N 26 L L (N 25 (N 27 L (N 34 L L L) L) L L)) L
  (N 25 (N 26 L L L) L L))) (N 23 L (N 24 (N 26 L L (N 31 L L (N 32 L L L))) L (N 25 (N 26 L L L)
  L L)) (N 24 (N 31 L L L) L L))) L (N 5 (N 24 L L (N 25 (N 32 L L L) L L)) (N 24 (N 26 L L (N 25
  (N 27 L (N 34 L L L) L) L L)) L (N 25 (N 32 L L L) L L)) L)) (N 24 (N 31 L L L) L L)) L (N 19 L
  (N 8 (N 24 (N 26 L L (N 31 L L (N 32 L L L))) L (N 25 (N 32 L L L) L L)) L (N 25 (N 32 L L L) L
  L)) (N 24 (N 31 L L L) L L))) (N 19 L (N 25 (N 32 L L L) L L) L)) L (N 5 (N 24 L L (N 25 (N 32 L
  L L) L L)) (N 18 L (N 17 (N 24 (N 26 L L (N 25 (N 32 L L L) L L)) L (N 25 (N 32 L L L) L L)) L
  (N 19 (N 8 L (N 23 (N 24 L L (N 25 (N 32 L L L) L L)) L (N 25 (N 24 L L (N 32 L L L)) L L)) (N
  25 (N 32 L L L) L L)) (N 8 (N 24 (N 26 L L (N 25 (N 32 L L L) L L)) L (N 25 (N 32 L L L) L L)) L
  (N 25 (N 32 L L L) L L)) L)) (N 25 (N 32 L L L) L L)) L)) L (N 14 (N 8 (N 18 L (N 17 (N 5 L (N
  19 L (N 23 L (N 30 L L (N 31 (N 24 L L (N 25 (N 26 L L L) L L)) L L)) (N 24 (N 31 L L (N 25 (N
  26 L L L) L L)) L L)) (N 24 (N 31 L L L) L L)) (N 24 (N 31 L L L) L L)) L (N 19 L (N 24 (N 31 L
  L (N 25 (N 26 L L L) L L)) L (N 25 (N 26 L L L) L L)) (N 24 (N 31 L L L) L L))) (N 19 L (N 17 (N
  5 L (N 24 (N 31 L L L) L L) L) L L) L)) (N 18 L (N 17 (N 19 (N 27 L (N 34 L (N 20 L L (N 24 (N
  31 L L L) L L)) L) L) L (N 24 (N 31 L L L) L L)) L (N 19 (N 20 L (N 24 (N 25 L L (N 31 L L L)) L
  (N 25 (N 26 L L L) L L)) (N 24 (N 31 L L L) L L)) L (N 24 (N 31 L L L) L L))) (N 19 (N 20 L (N
  17 (N 24 (N 25 L L L) L L) L L) L) L L)) L) L L)) L)) L L) (N 26 (N 9 (N 8 L (N 12 (N 13 L L (N
  20 L (N 17 (N 23 L (N 30 L (N 5 L L (N 33 (N 35 L L L) L L)) L) L) L L) L)) (N 13 (N 14 L L (N
  24 L L (N 27 L (N 17 (N 5 L (N 23 (N 30 L L L) L L) (N 18 L (N 19 (N 20 L (N 34 L L L) L) L (N
  20 (N 33 L (N 34 L L L) L) (N 33 (N 34 L L L) L L) L)) (N 31 L (N 30 (N 23 L (N 34 L (N 20 (N 33
  L L L) L L) L) L) L L) L))) L L) L))) L (N 14 (N 20 L (N 17 (N 25 L L (N 33 (N 32 L L (N 35 L (N
  30 (N 19 L L (N 23 L (N 27 L L L) L)) L L) L)) L L)) L L) L) L (N 17 (N 18 L (N 19 (N 20 L (N 27
  L (N 34 L L L) L) L) L (N 20 (N 24 L L (N 27 L (N 34 L (N 33 (N 35 L L L) L L) L) L)) (N 33 (N
  35 L (N 30 (N 23 L (N 27 L L L) L) L L) L) L L) L)) (N 19 (N 20 L (N 27 L (N 33 (N 34 L (N 35 L
  L L) L) L L) L) L) L (N 20 (N 24 L L (N 27 L (N 34 L (N 35 (N 30 L (N 33 L L L) L) L L) L) L))
  (N 33 (N 35 L (N 30 (N 23 L (N 27 L L L) L) L L) L) L L) L))) (N 18 L L (N 20 (N 27 L L L) L L))
  L))) L) (N 12 (N 13 L L (N 20 L (N 23 L (N 14 (N 25 L L (N 33 L (N 34 (N 30 L (N 27 (N 35 L L L)
  L L) L) L L) L)) L (N 17 (N 30 L (N 35 (N 33 L (N 34 L L L) L) L L) L) (N 27 (N 25 L L (N 19 (N
  34 L (N 18 L L (N 30 (N 33 L L L) L L)) L) L L)) L L) L)) L) L)) (N 13 (N 14 L L (N 24 L L (N 27
  L (N 5 L (N 17 (N 18 L (N 31 L L (N 20 (N 33 L (N 34 L L L) L) (N 33 (N 34 L L L) L L) L)) (N 20
  (N 33 L (N 30 (N 23 L (N 34 L L L) L) L L) L) (N 33 (N 34 L (N 35 L L L) L) L L) L)) (N 18 L L
  (N 20 (N 23 (N 30 (N 33 L (N 35 L L L) L) L L) L L) L L)) L) (N 17 (N 18 L (N 20 (N 33 L (N 34 L
  L L) L) (N 33 (N 34 L L L) L L) L) (N 31 L (N 30 (N 23 L (N 34 L (N 20 (N 33 L L L) L L) L) L) L
  L) L)) (N 18 L L (N 20 (N 23 (N 31 L (N 30 (N 33 L (N 35 L L L) L) L L) L) L L) L L)) L)) L))) L
  (N 14 (N 20 L (N 17 (N 25 L L (N 33 (N 35 L (N 18 L (N 23 (N 24 L L (N 27 L (N 30 L L L) L)) (N
  27 (N 30 L L L) L L) L) (N 23 (N 24 L L (N 5 L (N 27 L (N 30 L L L) L) L)) (N 27 (N 30 L L L) L
  L) L)) L) L L)) L L) L) L (N 17 (N 18 L (N 20 (N 24 L L (N 27 L (N 34 L (N 19 L L (N 25 (N 32 (N
  35 L L L) L L) L L)) L) L)) (N 33 (N 35 L (N 23 (N 24 L L (N 27 L (N 30 L L L) L)) (N 27 (N 30 L
  L L) L L) L) L) L L) L) (N 20 (N 24 L L (N 27 L (N 34 L (N 35 (N 30 L (N 33 L L L) L) L L) L)
  L)) (N 33 (N 35 L (N 23 (N 24 L L (N 5 L (N 27 L (N 30 L L L) L) L)) (N 27 (N 30 L L L) L L) L)
  L) L L) L)) (N 18 L L (N 20 (N 24 L L (N 27 L (N 23 (N 5 (N 30 L (N 31 L L L) L) (N 30 (N 31 L
  (N 35 L L L) L) L L) L) L L) L)) L L)) L))) L)) L (N 12 (N 13 L L (N 14 (N 8 L (N 20 L (N 17 (N
  23 L (N 25 L L (N 18 L (N 24 (N 30 L (N 33 L L L) L) L L) L)) L) L L) L) L) L L)) (N 13 (N 24 L
  L (N 25 (N 14 L L (N 27 L (N 5 (N 31 L (N 30 (N 17 L (N 23 L L L) L) L L) L) (N 17 (N 18 L (N 31
  (N 30 L (N 32 L L L) L) L L) (N 19 (N 20 L (N 33 (N 31 L (N 34 L L L) L) L L) L) (N 32 (N 31 L
  (N 30 (N 34 L L L) L L) L) L L) L)) (N 18 L L (N 19 (N 8 L L (N 20 (N 23 (N 30 (N 31 L (N 35 L L
  L) L) L L) L L) L L)) L L)) L) L) L)) L L)) L (N 14 (N 25 L L (N 18 L (N 17 (N 24 (N 20 L (N 23
  L (N 33 (N 32 L (N 8 (N 30 L L L) L L) L) L L) L) L) L L) L L) L)) L L)) L)) L L)) (S 29 L L L))
  (S 22 L (S 29 L L (N 20 (N 26 (N 27 L L L) L L) L L)) (S 29 L L L)) (S 22 L L L))) (S 11 L L (S
  16 (S 22 L (S 29 L (N 14 (N 35 (N 8 (N 9 L L (N 12 L (N 13 (N 18 L (N 17 (N 5 L (N 19 L (N 23 L
  (N 30 L L (N 31 (N 24 L L (N 25 L L L)) L L)) (N 24 (N 31 L L (N 30 L (N 32 L L L) L)) L L)) (N
  24 (N 31 L L L) L L)) (N 19 L (N 23 L (N 24 (N 26 L L (N 34 L (N 27 (N 20 L L (N 25 L L (N 31 L
  L L))) L L) L)) L (N 25 (N 26 L L L) L L)) (N 30 L (N 31 (N 24 L (N 27 L L L) L) L L) L)) (N 23
  L (N 24 (N 25 (N 26 L L (N 27 L (N 31 L L L) L)) L L) L L) (N 30 L (N 31 (N 24 L (N 27 L L L) L)
  L L) L)))) L (N 19 L (N 27 (N 34 L (N 31 L L (N 25 (N 32 L L L) L L)) L) (N 34 (N 24 L L (N 25
  (N 26 L L L) L L)) L L) L) (N 20 (N 24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L) L) (N 24
  (N 26 L L (N 31 L (N 34 L L L) L)) (N 27 (N 31 L L L) L L) L) L))) (N 19 L (N 17 (N 5 L (N 20 (N
  27 L (N 25 (N 32 L L L) L L) L) (N 23 L (N 25 (N 26 L L (N 24 (N 27 L (N 32 L L L) L) L L)) L L)
  (N 24 (N 26 L L (N 32 L (N 34 L L L) L)) (N 27 (N 26 L L (N 30 L L (N 31 L L L))) L L) L)) L) (N
  23 L (N 24 (N 25 (N 26 L L (N 27 L (N 32 L L L) L)) L L) L L) L)) L L) L)) L (N 18 L (N 17 (N 5
  L (N 19 L (N 23 L (N 30 L L (N 31 (N 24 L L (N 25 (N 26 L L L) L L)) L L)) (N 24 (N 31 L L (N 30
  L (N 26 (N 33 L L L) L L) L)) L L)) (N 24 (N 31 L L L) L L)) (N 19 L (N 23 L (N 24 (N 31 L (N 34
  L L L) L) L L) (N 30 L (N 31 (N 24 L (N 27 L L L) L) L L) L)) (N 23 L (N 24 (N 25 (N 26 L L (N
  27 L (N 31 L L L) L)) L L) L L) (N 30 L (N 31 (N 24 L (N 27 L L L) L) L L) L)))) L (N 19 L (N 27
  (N 34 L (N 31 L L (N 20 (N 32 L L L) L L)) L) (N 34 (N 24 L L (N 20 (N 25 L L L) L L)) L L) L)
  (N 20 (N 24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L) L) (N 24 (N 31 L (N 34 L L L) L) (N
  27 (N 31 L L L) L L) L) L))) (N 19 L (N 17 (N 5 L (N 20 (N 27 L (N 24 (N 26 L L L) L L) L) (N 26
  (N 33 L L L) L L) L) L) L L) L))) L)) (N 9 (N 13 L L (N 12 (N 18 L (N 17 (N 5 L (N 20 L (N 23 L
  (N 30 L L (N 31 (N 24 L L (N 26 L L L)) L L)) (N 24 (N 31 L L (N 30 L (N 33 L L L) L)) L L)) (N
  24 (N 31 L L L) L L)) (N 20 L (N 23 L (N 24 (N 25 L L (N 34 L (N 27 (N 19 L L (N 26 L L (N 31 L
  L L))) L L) L)) L (N 25 (N 26 L L L) L L)) (N 30 L (N 31 (N 24 L (N 27 L L L) L) L L) L)) (N 23
  L (N 24 (N 25 L L (N 26 (N 27 L (N 31 L L L) L) L L)) L L) (N 30 L (N 31 (N 24 L (N 27 L L L) L)
  L L) L)))) L (N 20 L (N 27 (N 34 L (N 31 L L (N 26 (N 33 L L L) L L)) L) (N 34 (N 24 L L (N 25
  (N 26 L L L) L L)) L L) L) (N 19 (N 24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L) L) (N 24
  (N 25 L L (N 31 L (N 34 L L L) L)) (N 27 (N 31 L L L) L L) L) L))) (N 20 L (N 17 (N 5 L (N 19 (N
  27 L (N 25 L L (N 24 (N 33 L L L) L L)) L) (N 23 L (N 26 (N 25 L L (N 24 (N 27 L (N 33 L L L) L)
  L L)) L L) (N 24 (N 25 L L (N 33 L (N 34 L L L) L)) (N 27 (N 25 L L (N 30 L L (N 31 L L L))) L
  L) L)) L) (N 23 L (N 24 (N 25 L L (N 26 (N 27 L (N 33 L L L) L) L L)) L L) L)) L L) L)) (N 18 L
  (N 17 (N 20 L (N 26 (N 33 L L (N 31 L (N 24 (N 27 L L L) L L) L)) L (N 33 (N 24 L (N 27 (N 31 L
  L L) L L) L) L L)) (N 24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L) L)) L (N 20 L (N 26 (N
  33 L L (N 31 L (N 24 (N 27 L L L) L L) L)) L (N 33 (N 24 L (N 27 (N 31 L L L) L L) L) L L)) (N
  19 (N 24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L) L) (N 24 (N 25 L L (N 31 L (N 34 L L L)
  L)) (N 27 (N 31 L L L) L L) L) L))) (N 20 L (N 17 (N 26 (N 33 L L L) L L) L L) L)) L)) L (N 12
  (N 13 L L (N 18 L (N 17 (N 5 L (N 20 L (N 23 L (N 30 L L (N 31 (N 24 L L (N 25 (N 26 L L L) L
  L)) L L)) (N 24 (N 31 L L (N 30 L (N 25 (N 32 L L L) L L) L)) L L)) (N 24 (N 31 L L L) L L)) (N
  20 L (N 23 L (N 24 (N 31 L (N 34 L L L) L) L L) (N 30 L (N 31 (N 24 L (N 27 L L L) L) L L) L))
  (N 23 L (N 24 (N 26 (N 25 L L (N 27 L (N 31 L L L) L)) L L) L L) (N 30 L (N 31 (N 24 L (N 27 L L
  L) L) L L) L)))) L (N 20 L (N 27 (N 34 L (N 31 L L (N 19 (N 33 L L L) L L)) L) (N 34 (N 24 L L
  (N 19 (N 26 L L L) L L)) L L) L) (N 19 (N 24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L) L)
  (N 24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L) L) L))) (N 20 L (N 17 (N 5 L (N 19 (N 27 L
  (N 24 (N 25 L L L) L L) L) (N 25 (N 32 L L L) L L) L) L) L L) L))) (N 13 (N 18 L (N 17 (N 19 L
  (N 25 (N 32 L L (N 31 L (N 24 (N 27 L L L) L L) L)) L (N 32 (N 24 L (N 27 (N 31 L L L) L L) L) L
  L)) (N 24 (N 31 L (N 34 L L L) L) (N 27 (N 31 L L L) L L) L)) L (N 19 L (N 25 (N 32 L L (N 31 L
  (N 24 (N 27 L L L) L L) L)) L (N 32 (N 24 L (N 27 (N 31 L L L) L L) L) L L)) (N 20 (N 24 (N 31 L
  (N 34 L L L) L) (N 27 (N 31 L L L) L L) L) (N 24 (N 26 L L (N 31 L (N 34 L L L) L)) (N 27 (N 31
  L L L) L L) L) L))) (N 19 L (N 17 (N 25 (N 32 L L L) L L) L L) L)) L (N 18 L (N 17 (N 27 (N 34 L
  (N 31 L L (N 19 L (N 20 L L L) L)) L) (N 24 (N 31 L L (N 25 (N 26 L L L) L L)) L (N 25 (N 26 L L
  L) L L)) L) L (N 27 (N 34 L (N 31 L L (N 24 (N 25 L (N 19 (N 33 L L L) L L) L) L L)) L) (N 24 (N
  31 L L (N 25 (N 26 L L L) L L)) L (N 25 (N 26 L L L) L L)) L)) (N 5 (N 17 (N 19 (N 20 L (N 26 (N
  33 L L L) L L) L) (N 25 (N 32 L L L) L L) L) (N 19 (N 20 L L L) L L) L) (N 17 (N 19 (N 20 L (N
  26 (N 33 L L L) L L) L) (N 25 (N 32 L L L) L L) L) L L) L))) L)) L) L L) L L) L) L) (S 22 L (S
  29 L (N 14 (N 27 (N 34 (N 35 L L L) L L) L L) L L) L) L) L))) (S 7 L (S 11 L (S 16 (S 22 (S 29 L
  L (N 27 L (N 9 (N 13 (N 14 L L (N 17 (N 23 (N 30 L (N 5 L (N 8 L (N 12 L L (N 32 (N 31 L L (N 33
  (N 18 (N 19 L L (N 20 L (N 26 L L L) L)) L (N 19 (N 24 L L (N 25 L L (N 20 L (N 26 (N 34 L (N 35
  L L L) L) L L) L))) L (N 20 (N 24 L L (N 26 L (N 34 L (N 35 L L L) L) L)) (N 26 (N 24 L L (N 25
  L L (N 34 L (N 35 L L L) L))) L L) L))) L L)) L L)) (N 12 L (N 33 (N 31 L L (N 32 (N 18 (N 20 L
  L (N 19 L (N 25 L L L) L)) L (N 20 (N 24 L L (N 26 L L (N 19 L (N 25 (N 34 L (N 35 L L L) L) L
  L) L))) L (N 19 (N 24 L L (N 25 L (N 34 L (N 35 L L L) L) L)) (N 25 (N 24 L L (N 26 L L (N 34 L
  (N 35 L L L) L))) L L) L))) L L)) L L) L)) (N 8 L (N 12 L (N 19 (N 20 L L (N 25 (N 32 L L L) L
  L)) L (N 20 (N 26 (N 33 L L L) L L) L L)) (N 32 (N 31 L L (N 33 (N 19 (N 25 L L (N 20 L (N 24 L
  L L) L)) L (N 18 (N 20 L (N 26 L L L) L) (N 26 (N 20 L (N 34 L L L) L) L L) L)) L L)) L L)) (N
  12 L (N 33 (N 31 L L (N 32 (N 20 (N 26 L L (N 19 L (N 24 L L L) L)) L (N 18 (N 19 L (N 25 L L L)
  L) (N 25 (N 19 L (N 34 L L L) L) L L) L)) L L)) L L) L))) L) (N 30 (N 34 L (N 35 L L L) L) (N 35
  (N 34 (N 18 L (N 5 (N 24 L L (N 31 L L (N 32 L (N 8 L L (N 12 L L L)) L))) L (N 19 L (N 20 L L
  (N 25 (N 32 L L L) L L)) (N 20 L (N 26 (N 33 L L L) L L) L))) (N 19 L (N 8 (N 25 L L (N 20 L (N
  12 L L (N 26 (N 32 L L L) L L)) L)) L (N 12 (N 26 L L (N 25 (N 32 L L L) L L)) (N 20 L L (N 5 (N
  32 L L L) L L)) L)) (N 20 L (N 26 (N 33 L L L) L L) L))) (N 5 (N 8 L (N 12 L L (N 24 L L (N 31 L
  L (N 32 (N 19 L L (N 26 L L L)) L L)))) (N 12 L (N 24 L L (N 31 L L (N 32 (N 25 L L (N 26 L L
  L)) L L))) L)) (N 8 (N 12 L L (N 25 L L (N 20 L (N 19 L L (N 26 (N 32 L L L) L L)) L))) L (N 12
  (N 26 L L (N 19 L (N 20 L L (N 25 (N 32 L L L) L L)) L)) L L)) (N 8 (N 12 L (N 20 L L (N 25 L L
  L)) (N 19 L (N 20 L L (N 25 L L L)) (N 20 L (N 18 (N 26 L L L) L L) L))) (N 12 (N 19 L L (N 26 L
  L L)) L (N 32 (N 19 L L (N 26 L L L)) L L)) (N 12 (N 19 L (N 20 L L (N 18 (N 25 L L L) L L)) (N
  20 L (N 26 L L L) L)) (N 33 (N 20 L L (N 25 L L L)) L L) L))) L) L L) L) L) (N 23 (N 30 (N 34 L
  (N 35 L L L) L) (N 34 (N 35 (N 24 L (N 5 (N 18 L L (N 31 L L (N 32 L (N 8 L L (N 12 L L L)) L)))
  L (N 18 (N 19 L L (N 20 L L L)) L (N 19 (N 20 L L (N 8 L (N 25 L L L) L)) L (N 20 (N 12 L (N 26
  L L L) L) L L)))) (N 25 L (N 8 (N 19 L L (N 20 (N 18 L L (N 26 L (N 33 L L L) L)) L L)) L (N 12
  (N 20 L L (N 19 (N 32 L L L) L L)) (N 26 L L (N 5 (N 32 L L L) L L)) L)) (N 26 L (N 20 (N 33 L L
  L) L L) L))) (N 5 (N 8 L (N 12 L L (N 18 L L (N 31 L L (N 32 (N 19 L L (N 20 L L L)) L L)))) (N
  12 L (N 18 L L (N 31 L L (N 32 (N 19 L L (N 20 L L L)) L L))) L)) (N 8 (N 12 L L (N 19 L L (N 20
  (N 32 L L L) L L))) L (N 12 (N 20 L L (N 19 (N 32 L L L) L L)) L L)) (N 8 (N 12 L (N 19 L L (N
  26 L L L)) (N 19 L (N 25 L L (N 26 L L L)) (N 26 L (N 18 (N 20 L L L) L L) L))) (N 12 (N 20 L L
  (N 25 L L L)) L (N 32 (N 19 L L (N 20 L L L)) L L)) (N 12 (N 20 L (N 25 L L (N 26 L L L)) (N 25
  L (N 18 (N 19 L L L) L L) L)) (N 33 (N 19 L L (N 20 L L L)) L L) L))) L) L L) L) L L) L)) L (N
  14 (N 17 (N 23 (N 30 L (N 5 L (N 8 L (N 12 L L (N 31 (N 32 L L (N 33 (N 18 (N 19 L L (N 24 L L
  (N 20 L (N 25 L L (N 26 (N 34 L (N 35 L L L) L) L L)) L))) L (N 19 (N 20 L (N 26 L L L) L) L (N
  20 (N 25 L L (N 26 L (N 34 L (N 35 L L L) L) L)) (N 26 (N 24 L L (N 25 L L (N 34 L (N 35 L L L)
  L))) L L) L))) L L)) L L)) (N 12 L (N 18 (N 20 L L (N 24 (N 31 L L L) L L)) L (N 20 (N 26 (N 33
  L L L) L L) L L)) (N 31 (N 32 L L (N 33 (N 18 (N 24 L L (N 20 L (N 25 L L L) L)) L (N 19 (N 20 L
  (N 26 L L L) L) (N 26 (N 20 L (N 34 L L L) L) L L) L)) L L)) L L))) (N 12 L (N 33 (N 32 L L (N
  31 (N 8 L (N 19 (N 20 L L (N 18 L (N 24 L L L) L)) L (N 20 (N 25 L L (N 26 L L (N 18 L (N 24 (N
  34 L (N 35 L L L) L) L L) L))) L (N 18 (N 24 L (N 25 L L (N 34 L (N 35 L L L) L)) L) (N 24 (N 25
  L L (N 26 L L (N 34 L (N 35 L L L) L))) L L) L))) (N 20 (N 26 L L (N 18 L (N 25 L L L) L)) L (N
  18 (N 19 L (N 24 L L L) L) (N 24 (N 19 L (N 34 L L L) L) L L) L))) L L)) L L) L)) L) (N 30 (N 34
  L (N 35 L L L) L) (N 35 (N 34 (N 18 L (N 5 (N 24 L L (N 20 L (N 12 L L (N 19 L L (N 26 (N 31 L L
  L) L L))) L)) L (N 12 (N 26 L L (N 24 (N 31 L L L) L L)) (N 20 L L (N 24 (N 31 L L L) L L)) L))
  (N 20 L (N 26 (N 33 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 24 L L (N 20 L (N 18 L L (N 26 (N
  31 L L L) L L)) L))) (N 12 L (N 20 L L (N 24 L L L)) (N 18 L (N 20 L L (N 24 L L L)) (N 20 L (N
  19 (N 26 L L L) L L) L)))) (N 8 (N 12 L L (N 25 L L (N 31 (N 18 L L (N 26 L L L)) L L))) L (N 12
  (N 18 L L (N 26 L L L)) L (N 31 (N 18 L L (N 26 L L L)) L L))) (N 12 (N 8 L (N 26 L L (N 18 L (N
  20 L L (N 24 (N 31 L L L) L L)) L)) (N 18 L (N 20 L L (N 19 (N 24 L L L) L L)) (N 20 L (N 26 L L
  L) L))) (N 33 (N 20 L L (N 24 L L L)) L L) L)) L) L L) L) L) (N 23 (N 30 (N 34 L (N 35 L L L) L)
  (N 34 (N 35 (N 24 L (N 5 (N 18 L L (N 20 (N 19 L L (N 26 L (N 33 L L L) L)) L L)) L (N 12 (N 20
  L L (N 18 (N 31 L L L) L L)) (N 26 L L (N 18 (N 31 L L L) L L)) L)) (N 26 L (N 20 (N 33 L L L) L
  L) L)) (N 5 (N 8 L (N 12 L L (N 18 L L (N 20 (N 31 L L L) L L))) (N 12 L (N 18 L L (N 26 L L L))
  (N 18 L (N 24 L L (N 26 L L L)) (N 26 L (N 19 (N 20 L L L) L L) L)))) (N 8 (N 12 L L (N 19 L L
  (N 31 (N 18 L L (N 20 L L L)) L L))) L (N 12 (N 20 L L (N 24 L L L)) L (N 31 (N 18 L L (N 20 L L
  L)) L L))) (N 12 (N 8 L (N 20 L L (N 18 (N 31 L L L) L L)) (N 20 L (N 24 L L (N 26 L L L)) (N 24
  L (N 18 (N 19 L L L) L L) L))) (N 33 (N 18 L L (N 20 L L L)) L L) L)) L) L L) L) L L) L) L (N 17
  (N 23 (N 30 L (N 5 L (N 8 L (N 12 L L (N 31 (N 32 L L L) L L)) (N 12 L (N 33 (N 18 (N 20 L L (N
  19 L (N 25 L L L) L)) L (N 20 (N 26 (N 24 L L (N 31 (N 32 L L (N 19 L (N 25 L L L) L)) L L)) L
  L) L L)) L L) L)) (N 12 L (N 33 (N 8 L (N 19 (N 20 L L (N 18 L (N 24 L L L) L)) L (N 20 (N 26 (N
  25 L L (N 32 (N 31 L L (N 18 L (N 24 L L L) L)) L L)) L L) L L)) (N 20 (N 34 L (N 35 L L L) L) L
  (N 26 (N 24 L (N 18 (N 19 L L L) L L) L) L L))) L L) L)) L) (N 30 (N 34 L (N 35 L L L) L) (N 35
  (N 34 (N 18 L (N 5 (N 24 L L (N 20 L (N 12 L L (N 8 L (N 32 L L L) L)) L)) L (N 12 (N 26 L L (N
  19 L (N 20 L L L) L)) (N 20 L L (N 19 L (N 24 (N 25 L L L) L L) L)) L)) (N 20 L (N 26 (N 33 L L
  L) L L) L)) (N 5 (N 8 L (N 12 L L (N 24 L L (N 26 (N 33 L L L) L L))) (N 12 L (N 24 L L (N 20 (N
  33 L L L) L L)) L)) (N 8 (N 12 L L (N 25 L L (N 26 (N 33 L L L) L L))) L (N 12 (N 26 L L (N 18
  (N 25 L L L) L L)) L L)) (N 12 (N 8 L (N 26 L L (N 19 (N 24 L L L) L L)) (N 20 L (N 26 L L (N 18
  (N 19 L L L) L L)) (N 26 L (N 18 (N 19 L L L) L L) L))) (N 33 (N 20 L L (N 26 L L L)) L L) L))
  L) L L) L) L) (N 23 (N 30 (N 34 L (N 35 L L L) L) (N 34 (N 35 (N 24 L (N 5 (N 18 L L (N 20 (N 19
  L L (N 26 L (N 33 L L L) L)) L L)) L (N 12 (N 20 L L (N 18 (N 19 L L L) L L)) (N 26 L L (N 18 (N
  19 L L L) L L)) L)) (N 26 L (N 20 (N 33 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 18 L L (N 20 (N
  33 L L L) L L))) (N 12 L (N 18 L L (N 20 (N 33 L L L) L L)) L)) (N 8 (N 12 L L (N 19 L L (N 20
  (N 33 L L L) L L))) L (N 12 (N 20 L L (N 18 (N 19 L L L) L L)) L L)) (N 12 (N 8 L (N 20 L L (N
  18 (N 19 L L L) L L)) (N 20 L (N 26 L L (N 18 (N 19 L L L) L L)) (N 26 L (N 18 (N 19 L L L) L L)
  L))) (N 33 (N 20 L L (N 26 L L L)) L L) L)) L) L L) L) L L) L))) L (N 13 (N 14 (N 17 (N 23 (N 30
  L (N 5 L (N 8 L (N 12 L L (N 18 (N 19 L L (N 24 (N 31 L L L) L L)) L (N 19 (N 25 (N 32 L L L) L
  L) L L))) (N 31 (N 33 L L (N 32 (N 12 L (N 18 (N 20 L L (N 24 L L (N 19 L (N 25 (N 26 L L (N 34
  L (N 35 L L L) L)) L L) L))) L (N 19 (N 20 L L (N 25 L (N 26 L L (N 34 L (N 35 L L L) L)) L)) (N
  25 (N 20 L L (N 24 L L (N 26 L L (N 34 L (N 35 L L L) L)))) L L) L)) (N 18 (N 24 L L (N 19 L (N
  26 L L L) L)) L (N 19 (N 20 L (N 25 L L L) L) (N 25 (N 20 L (N 34 L L L) L) L L) L))) L L)) L
  L)) (N 8 L (N 32 (N 33 L L (N 31 (N 12 L (N 19 (N 20 L L (N 25 L L (N 18 L (N 24 (N 26 L L (N 34
  L (N 35 L L L) L)) L L) L))) L (N 18 (N 20 L L (N 24 L (N 26 L L (N 34 L (N 35 L L L) L)) L)) (N
  24 (N 20 L L (N 25 L L (N 26 L L (N 34 L (N 35 L L L) L)))) L L) L)) (N 19 (N 25 L L (N 18 L (N
  26 L L L) L)) L (N 18 (N 20 L (N 24 L L L) L) (N 24 (N 20 L (N 34 L L L) L) L L) L))) L L)) L L)
  L)) L) (N 30 (N 34 L (N 35 L L L) L) (N 35 (N 34 (N 18 L (N 5 (N 24 L L (N 19 L (N 8 L L (N 20 L
  L (N 25 (N 31 L L L) L L))) L)) L (N 8 (N 25 L L (N 24 (N 31 L L L) L L)) (N 19 L L (N 24 (N 31
  L L L) L L)) L)) (N 19 L (N 25 (N 32 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 19 L L (N 24 L L
  L))) (N 12 L (N 24 L L (N 19 L (N 18 L L (N 25 (N 31 L L L) L L)) L)) (N 18 L (N 19 L L (N 24 L
  L L)) (N 19 L (N 20 (N 25 L L L) L L) L)))) (N 8 (N 12 L L (N 18 L L (N 25 L L L))) L (N 31 (N
  18 L L (N 25 L L L)) L L)) (N 8 (N 12 L (N 25 L L (N 18 L (N 19 L L (N 24 (N 31 L L L) L L)) L))
  (N 18 L (N 19 L L (N 20 (N 24 L L L) L L)) (N 19 L (N 25 L L L) L))) (N 32 (N 19 L L (N 24 L L
  L)) L L) L)) L) L L) L) L) (N 23 (N 30 (N 34 L (N 35 L L L) L) (N 34 (N 35 (N 24 L (N 5 (N 18 L
  L (N 19 (N 20 L L (N 25 L (N 32 L L L) L)) L L)) L (N 8 (N 19 L L (N 18 (N 31 L L L) L L)) (N 25
  L L (N 18 (N 31 L L L) L L)) L)) (N 25 L (N 19 (N 32 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 18
  L L (N 25 L L L))) (N 12 L (N 18 L L (N 19 (N 31 L L L) L L)) (N 18 L (N 24 L L (N 25 L L L)) (N
  25 L (N 19 (N 20 L L L) L L) L)))) (N 8 (N 12 L L (N 19 L L (N 24 L L L))) L (N 31 (N 18 L L (N
  19 L L L)) L L)) (N 8 (N 12 L (N 19 L L (N 18 (N 31 L L L) L L)) (N 19 L (N 24 L L (N 25 L L L))
  (N 24 L (N 18 (N 20 L L L) L L) L))) (N 32 (N 18 L L (N 19 L L L)) L L) L)) L) L L) L) L L) L) L
  (N 17 (N 23 (N 30 L (N 5 L (N 8 L (N 12 L L (N 32 (N 18 (N 19 L L (N 20 L (N 26 L L L) L)) L (N
  19 (N 25 (N 24 L L (N 31 (N 33 L L (N 20 L (N 26 L L L) L)) L L)) L L) L L)) L L)) (N 12 L (N 31
  (N 33 L L L) L L) L)) (N 8 L (N 32 (N 12 L (N 19 (N 20 L L (N 25 (N 26 L L (N 33 (N 31 L L (N 18
  L (N 24 L L L) L)) L L)) L L)) L (N 20 (N 18 L (N 24 L L L) L) L L)) (N 19 (N 34 L (N 35 L L L)
  L) L (N 25 (N 24 L (N 18 (N 20 L L L) L L) L) L L))) L L) L)) L) (N 30 (N 34 L (N 35 L L L) L)
  (N 35 (N 34 (N 18 L (N 5 (N 24 L L (N 19 L (N 8 L L (N 12 L (N 33 L L L) L)) L)) L (N 8 (N 25 L
  L (N 19 L (N 20 L L L) L)) (N 19 L L (N 20 L (N 24 (N 25 L L L) L L) L)) L)) (N 19 L (N 25 (N 32
  L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 24 L L (N 19 (N 32 L L L) L L))) (N 12 L (N 24 L L (N
  25 (N 32 L L L) L L)) L)) (N 8 (N 12 L L (N 25 L L (N 18 (N 26 L L L) L L))) L (N 12 (N 25 (N 32
  L L L) L L) L L)) (N 8 (N 12 L (N 25 L L (N 19 L (N 18 (N 20 L L L) L L) L)) (N 19 L (N 25 L L
  (N 18 (N 20 L L L) L L)) (N 25 L (N 18 (N 20 L L L) L L) L))) (N 32 (N 19 L L (N 25 L L L)) L L)
  L)) L) L L) L) L) (N 23 (N 30 (N 34 L (N 35 L L L) L) (N 34 (N 35 (N 24 L (N 5 (N 18 L L (N 19
  (N 20 L L (N 25 L (N 32 L L L) L)) L L)) L (N 8 (N 19 L L (N 18 (N 20 L L L) L L)) (N 25 L L (N
  18 (N 19 L L L) L L)) L)) (N 25 L (N 19 (N 32 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 18 L L (N
  19 (N 32 L L L) L L))) (N 12 L (N 18 L L (N 19 (N 32 L L L) L L)) L)) (N 8 (N 12 L L (N 19 L L
  (N 18 (N 20 L L L) L L))) L (N 12 (N 19 (N 32 L L L) L L) L L)) (N 8 (N 12 L (N 19 L L (N 18 (N
  20 L L L) L L)) (N 19 L (N 25 L L (N 18 (N 20 L L L) L L)) (N 25 L (N 18 (N 20 L L L) L L) L)))
  (N 32 (N 19 L L (N 25 L L L)) L L) L)) L) L L) L) L L) L)) L (N 14 (N 17 (N 23 (N 30 L (N 5 L (N
  8 L (N 12 L L (N 31 (N 18 (N 19 L L (N 24 (N 25 L L (N 32 (N 33 L L (N 20 L (N 26 L L L) L)) L
  L)) L L)) L (N 19 (N 20 L (N 26 L L L) L) L L)) L L)) (N 31 (N 12 L (N 18 (N 20 L L (N 24 (N 26
  L L (N 33 (N 32 L L (N 19 L (N 25 L L L) L)) L L)) L L)) L (N 20 (N 19 L (N 25 L L L) L) L L))
  (N 18 (N 34 L (N 35 L L L) L) L (N 24 (N 25 L (N 19 (N 20 L L L) L L) L) L L))) L L)) (N 8 L (N
  12 L (N 31 (N 32 (N 33 L L L) L L) L L) L) L)) L) (N 30 (N 34 L (N 35 L L L) L) (N 35 (N 34 (N
  18 L (N 5 (N 24 L L (N 19 L (N 20 L L L) L)) L (N 24 (N 31 L L L) L L)) (N 19 L (N 20 L (N 24 (N
  25 L L L) L L) L) L)) (N 5 (N 8 L (N 12 L L (N 24 L L (N 18 L (N 19 (N 20 L L L) L L) L))) (N 12
  L (N 24 L L (N 18 L (N 19 (N 20 L L L) L L) L)) (N 18 L (N 24 L L (N 19 (N 20 L L L) L L)) (N 24
  L (N 19 (N 20 L L L) L L) L)))) (N 8 (N 12 L L (N 25 L L (N 18 (N 31 L L L) L L))) L (N 31 (N 18
  L L (N 24 L L L)) L L)) (N 8 (N 12 L (N 24 (N 31 L L L) L L) L) (N 12 (N 24 (N 31 L L L) L L) L
  L) L)) L) L L) L) L) (N 23 (N 30 (N 34 L (N 35 L L L) L) (N 34 (N 35 (N 24 L (N 5 (N 18 L L (N
  19 (N 20 L L L) L L)) L (N 18 (N 31 L L L) L L)) (N 25 L (N 18 (N 19 L L L) L L) L)) (N 5 (N 8 L
  (N 12 L L (N 18 L L (N 19 (N 20 L L L) L L))) (N 12 L (N 18 L L (N 19 (N 20 L L L) L L)) (N 18 L
  (N 24 L L (N 19 (N 20 L L L) L L)) (N 24 L (N 19 (N 20 L L L) L L) L)))) (N 8 (N 12 L L (N 19 L
  L (N 18 (N 31 L L L) L L))) L (N 31 (N 18 L L (N 24 L L L)) L L)) (N 8 (N 12 L (N 18 (N 31 L L
  L) L L) L) (N 12 (N 18 (N 31 L L L) L L) L L) L)) L) L L) L) L L) L) L L))) L)) L (S 29 L L (N 9
  (N 13 (N 14 L L (N 17 (N 23 (N 27 L (N 30 L (N 5 L (N 8 L (N 12 L L (N 25 (N 18 L L (N 24 L L (N
  32 (N 19 L L (N 31 L L (N 33 (N 34 L (N 35 L L L) L) L L))) L L))) L L)) (N 12 L (N 26 (N 18 L L
  (N 24 L L (N 33 (N 20 L L (N 31 L L (N 32 (N 34 L (N 35 L L L) L) L L))) L L))) L L) L)) (N 8 L
  (N 12 L (N 19 (N 20 L L (N 25 (N 32 L L L) L L)) L (N 20 (N 26 (N 33 L L L) L L) L L)) (N 25 (N
  32 (N 19 L L (N 18 L (N 24 L L (N 26 (N 31 L L (N 33 (N 20 L (N 34 L L L) L) L L)) L L)) L)) L
  L) L L)) (N 12 L (N 26 (N 33 (N 20 L L (N 18 L (N 24 L L (N 25 (N 31 L L (N 32 (N 19 L (N 34 L L
  L) L) L L)) L L)) L)) L L) L L) L))) L) L) (N 27 (N 34 L (N 18 L (N 5 (N 24 L L (N 25 L (N 8 L L
  (N 12 L L L)) L)) L (N 19 L (N 20 L L (N 25 (N 24 L L (N 32 (N 8 L L (N 30 L (N 35 L L L) L)) L
  L)) L L)) (N 20 L (N 26 (N 24 L L (N 33 (N 12 L L (N 30 L (N 35 L L L) L)) L L)) L L) L))) (N 19
  L (N 8 (N 30 L (N 35 (N 32 L L (N 12 L (N 20 L L L) L)) L L) L) L (N 33 (N 31 L L (N 32 (N 12 (N
  26 L (N 5 L L (N 20 L L L)) L) (N 20 L L (N 25 (N 5 L (N 30 L L L) L) L L)) L) L L)) L L)) (N 20
  L (N 26 (N 33 (N 12 L L (N 5 L (N 24 L L (N 25 (N 30 L (N 35 L L L) L) L L)) L)) L L) L L) L)))
  L) (N 30 (N 34 L (N 35 (N 5 L (N 8 L (N 12 L L (N 25 (N 32 L L L) L L)) (N 12 L (N 26 (N 33 L L
  L) L L) L)) (N 8 L (N 12 L (N 19 (N 20 L L (N 25 L L L)) L (N 20 (N 26 L L L) L L)) (N 25 (N 32
  L L L) L L)) (N 12 L (N 26 (N 33 L L L) L L) L))) L L) L) (N 35 (N 34 (N 18 L (N 5 (N 24 L L (N
  25 (N 26 (N 31 L L (N 32 L (N 8 L L (N 12 L L L)) L)) L L) L L)) L (N 19 L (N 20 L L (N 25 (N 32
  L L L) L L)) (N 20 L (N 26 (N 33 L L L) L L) L))) (N 19 L (N 8 (N 25 L L (N 12 L (N 20 L L L)
  L)) L (N 26 (N 12 L (N 33 L L L) L) L L)) (N 20 L (N 26 (N 33 L L L) L L) L))) (N 5 (N 8 L (N 12
  L L (N 24 L L (N 25 (N 32 L L L) L L))) (N 12 L (N 24 L L (N 25 (N 33 L L L) L L)) L)) (N 8 (N
  12 L L (N 25 (N 32 L L L) L L)) L (N 12 (N 26 (N 33 L L L) L L) L L)) (N 8 (N 12 L (N 20 L L (N
  19 L (N 25 (N 32 L L L) L L) L)) (N 19 L (N 20 L L (N 25 (N 32 L L L) L L)) (N 20 L (N 18 (N 24
  L L (N 25 (N 32 L L L) L L)) L L) L))) (N 12 (N 19 L L (N 20 L (N 26 (N 33 L L L) L L) L)) L (N
  25 (N 32 L L L) L L)) (N 12 (N 19 L (N 20 L L (N 18 (N 24 L L (N 25 (N 32 L L L) L L)) L L)) (N
  20 L (N 25 (N 32 L L L) L L) L)) (N 26 (N 33 L L L) L L) L))) L) L L) L) L) L) (N 23 (N 27 L (N
  30 (N 34 L (N 35 L L L) L) (N 34 (N 35 (N 5 (N 8 L (N 12 L L (N 32 L L L)) (N 12 L (N 33 L L L)
  L)) (N 8 (N 12 L L (N 19 L L (N 20 (N 32 L L L) L L))) L (N 12 (N 20 L L (N 19 (N 32 L L L) L
  L)) L L)) (N 8 (N 12 L (N 19 L L (N 26 L L L)) (N 25 L (N 19 L L (N 18 (N 20 L L L) L L)) L)) (N
  12 (N 20 L L (N 25 L L L)) L (N 25 (N 32 L L L) L L)) (N 12 (N 26 L (N 20 L L (N 18 (N 19 L L L)
  L L)) L) (N 26 (N 33 L L L) L L) L))) (N 5 (N 8 L (N 12 L L (N 18 L L (N 25 (N 31 L L (N 32 (N
  19 L L (N 20 L L L)) L L)) L L))) (N 12 L (N 18 L L (N 26 (N 31 L L (N 32 (N 19 L L (N 20 L L
  L)) L L)) L L)) L)) (N 8 (N 12 L L (N 19 L L (N 20 (N 32 L L L) L L))) L (N 12 (N 20 L L (N 19
  (N 32 L L L) L L)) L L)) (N 8 (N 12 L (N 19 L L (N 26 L L L)) (N 25 L (N 19 L L (N 26 L L L))
  L)) (N 12 (N 20 L L (N 25 L L L)) L (N 25 (N 32 (N 19 L L (N 20 L L L)) L L) L L)) (N 12 (N 26 L
  (N 20 L L (N 25 L L L)) L) (N 26 (N 33 (N 19 L L (N 20 L L L)) L L) L L) L))) L) L L) L) L) (N
  27 (N 30 (N 34 L (N 35 (N 5 (N 8 L (N 12 L L (N 25 L L L)) (N 12 L (N 26 L L L) L)) (N 8 (N 12 L
  L (N 19 L L (N 20 (N 25 L L L) L L))) L (N 12 (N 20 L L (N 19 (N 25 L L L) L L)) L L)) (N 8 (N
  12 L (N 19 L L (N 33 L L L)) (N 32 L (N 19 L L (N 18 (N 20 L L L) L L)) L)) (N 12 (N 20 L L (N
  32 L L L)) L (N 25 (N 32 L L L) L L)) (N 12 (N 33 L (N 20 L L (N 18 (N 19 L L L) L L)) L) (N 26
  (N 33 L L L) L L) L))) (N 5 (N 8 L (N 12 L L (N 18 L L (N 24 L L (N 25 (N 19 L L (N 20 L L L)) L
  L)))) (N 12 L (N 18 L L (N 24 L L (N 25 (N 19 L L (N 20 L L L)) L L))) L)) (N 8 (N 12 L L (N 19
  L L (N 20 (N 25 L L L) L L))) L (N 12 (N 20 L L (N 19 (N 25 L L L) L L)) L L)) (N 8 (N 12 L (N
  19 L L (N 33 L L L)) (N 32 L (N 19 L L (N 33 L L L)) L)) (N 12 (N 20 L L (N 32 L L L)) L (N 25
  (N 19 L L (N 20 L L L)) L L)) (N 12 (N 33 L (N 20 L L (N 32 L L L)) L) (N 26 (N 19 L L (N 20 L L
  L)) L L) L))) L) L) (N 34 (N 35 L L L) L L) L) L L) L) L)) L (N 14 (N 17 (N 23 (N 27 L (N 30 L
  (N 5 L (N 8 L (N 12 L L (N 24 (N 19 L L (N 25 L L (N 31 (N 18 L L (N 32 L L (N 33 (N 34 L (N 35
  L L L) L) L L))) L L))) L L)) (N 12 L (N 18 (N 20 L L (N 24 (N 31 L L L) L L)) L (N 20 (N 26 (N
  33 L L L) L L) L L)) (N 24 (N 31 (N 18 L L (N 19 L (N 25 L L (N 26 (N 32 L L (N 33 (N 20 L (N 34
  L L L) L) L L)) L L)) L)) L L) L L))) (N 12 L (N 26 (N 33 (N 20 L L (N 31 (N 32 L L (N 34 L (N
  35 L L L) L)) L L)) L L) L L) L)) L) L) (N 27 (N 34 L (N 18 L (N 5 (N 30 L (N 35 (N 31 L L (N 12
  L (N 20 L L L) L)) L L) L) L (N 33 (N 32 L L (N 31 (N 12 (N 26 L (N 8 L L (N 20 L L (N 19 L (N
  24 (N 25 L L (N 30 L (N 35 L L L) L)) L L) L))) L) (N 20 L L (N 24 (N 25 L L (N 26 (N 30 L (N 35
  L L L) L) L L)) L L)) L) L L)) L L)) (N 20 L (N 26 (N 33 (N 12 L L (N 30 L (N 35 L L L) L)) L L)
  L L) L)) L) (N 30 (N 34 L (N 35 (N 5 L (N 8 L (N 12 L L (N 24 (N 31 L L L) L L)) (N 12 L (N 18
  (N 20 L L (N 24 L L L)) L (N 20 (N 26 L L L) L L)) (N 24 (N 31 L L L) L L))) (N 12 L (N 26 (N 33
  L L L) L L) L)) L L) L) (N 35 (N 34 (N 18 L (N 5 (N 24 L L (N 12 L (N 20 L L L) L)) L (N 26 (N
  12 L (N 33 L L L) L) L L)) (N 20 L (N 26 (N 33 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 24 (N 31
  L L L) L L)) (N 12 L (N 20 L L (N 18 L (N 24 (N 31 L L L) L L) L)) (N 18 L (N 20 L L (N 24 (N 31
  L L L) L L)) (N 20 L (N 19 (N 24 (N 31 L L L) L L) L L) L)))) (N 8 (N 12 L L (N 24 (N 31 L L L)
  L L)) L (N 12 (N 18 L L (N 20 L (N 26 (N 33 L L L) L L) L)) L (N 24 (N 31 L L L) L L))) (N 12 (N
  8 L (N 26 (N 33 L L L) L L) (N 18 L (N 20 L L (N 19 (N 24 (N 31 L L L) L L) L L)) (N 20 L (N 24
  (N 31 L L L) L L) L))) (N 26 (N 33 L L L) L L) L)) L) L L) L) L) L) (N 23 (N 27 L (N 30 (N 34 L
  (N 35 L L L) L) (N 34 (N 35 (N 5 (N 8 L (N 12 L L (N 18 L L (N 20 (N 31 L L L) L L))) (N 12 L (N
  18 L L (N 26 L L L)) (N 24 L (N 18 L L (N 19 (N 20 L L L) L L)) L))) (N 8 (N 12 L L (N 31 L L
  L)) L (N 12 (N 20 L L (N 24 L L L)) L (N 24 (N 31 L L L) L L))) (N 12 (N 26 L (N 20 L L (N 18 (N
  33 L L L) L L)) L) (N 26 (N 33 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 18 L L (N 20 (N 31 L L
  L) L L))) (N 12 L (N 18 L L (N 26 L L L)) (N 24 L (N 18 L L (N 26 L L L)) L))) (N 8 (N 12 L L (N
  19 L L (N 24 (N 31 (N 18 L L (N 20 L L L)) L L) L L))) L (N 12 (N 20 L L (N 24 L L L)) L (N 24
  (N 31 (N 18 L L (N 20 L L L)) L L) L L))) (N 12 (N 26 L (N 20 L L (N 24 L L L)) L) (N 26 (N 33
  (N 18 L L (N 20 L L L)) L L) L L) L)) L) L L) L) L) (N 27 (N 30 (N 34 L (N 35 (N 5 (N 8 L (N 12
  L L (N 18 L L (N 20 (N 24 L L L) L L))) (N 12 L (N 18 L L (N 33 L L L)) (N 31 L (N 18 L L (N 19
  (N 20 L L L) L L)) L))) (N 8 (N 12 L L (N 24 L L L)) L (N 12 (N 20 L L (N 31 L L L)) L (N 24 (N
  31 L L L) L L))) (N 12 (N 33 L (N 20 L L (N 18 (N 26 L L L) L L)) L) (N 26 (N 33 L L L) L L) L))
  (N 5 (N 8 L (N 12 L L (N 18 L L (N 20 (N 24 L L L) L L))) (N 12 L (N 18 L L (N 33 L L L)) (N 31
  L (N 18 L L (N 33 L L L)) L))) (N 8 (N 12 L L (N 19 L L (N 24 (N 18 L L (N 20 L L L)) L L))) L
  (N 12 (N 20 L L (N 31 L L L)) L (N 24 (N 18 L L (N 20 L L L)) L L))) (N 12 (N 33 L (N 20 L L (N
  31 L L L)) L) (N 26 (N 18 L L (N 20 L L L)) L L) L)) L) L) (N 34 (N 35 L L L) L L) L) L L) L) L)
  L (N 17 (N 23 (N 27 L (N 30 L (N 5 L (N 8 L (N 12 L L (N 24 (N 25 L L L) L L)) (N 12 L (N 26 (N
  33 (N 34 L (N 35 L L L) L) L L) L L) L)) (N 12 L (N 26 (N 33 (N 34 L (N 35 L L L) L) L L) L L)
  L)) L) L) (N 27 (N 34 L (N 18 L (N 5 (N 30 L (N 35 (N 31 L L (N 12 L (N 20 L L L) L)) L L) L) L
  (N 33 (N 12 (N 30 L (N 35 L L L) L) (N 20 L L (N 19 L (N 24 (N 25 L L L) L L) L)) L) L L)) (N 20
  L (N 26 (N 33 (N 30 L (N 35 L L L) L) L L) L L) L)) L) (N 30 (N 34 L (N 35 (N 5 L (N 8 L (N 12 L
  L (N 24 (N 25 L L L) L L)) (N 12 L (N 26 (N 33 L L L) L L) L)) (N 12 L (N 26 (N 33 L L L) L L)
  L)) L L) L) (N 35 (N 34 (N 18 L (N 5 (N 24 L L (N 12 L (N 20 L L L) L)) L (N 26 (N 12 L (N 33 L
  L L) L) L L)) (N 20 L (N 26 (N 33 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 24 (N 25 L L L) L L))
  (N 12 L (N 26 (N 33 L L L) L L) L)) (N 8 (N 12 L L (N 24 (N 25 L L L) L L)) L (N 12 (N 26 (N 33
  L L L) L L) L L)) (N 12 (N 8 L (N 26 (N 33 L L L) L L) (N 20 L (N 26 (N 33 L L L) L L) (N 18 (N
  19 L (N 24 (N 25 L L L) L L) L) (N 19 (N 24 (N 25 L L L) L L) L L) L))) (N 26 (N 33 L L L) L L)
  L)) L) L L) L) L) L) (N 23 (N 27 L (N 30 (N 34 L (N 35 L L L) L) (N 34 (N 35 (N 5 (N 8 L (N 12 L
  L (N 32 L L L)) (N 12 L (N 18 L L (N 20 (N 33 L L L) L L)) L)) (N 8 (N 12 L L (N 31 L L L)) L (N
  12 (N 20 L L (N 18 (N 19 L L L) L L)) L L)) (N 12 (N 26 L (N 20 L L (N 18 (N 19 L L L) L L)) L)
  (N 26 (N 33 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 18 L L (N 20 (N 33 L L L) L L))) (N 12 L (N
  18 L L (N 20 (N 33 L L L) L L)) L)) (N 8 (N 12 L L (N 19 L L (N 20 (N 33 L L L) L L))) L (N 12
  (N 20 L L (N 18 (N 19 L L L) L L)) L L)) (N 12 (N 26 L (N 20 L L (N 18 (N 19 L L L) L L)) L) (N
  26 (N 33 (N 20 L L (N 18 (N 19 L L L) L L)) L L) L L) L)) L) L L) L) L) (N 27 (N 30 (N 34 L (N
  35 (N 5 (N 8 L (N 12 L L (N 25 L L L)) (N 12 L (N 18 L L (N 20 (N 26 L L L) L L)) L)) (N 8 (N 12
  L L (N 24 L L L)) L (N 12 (N 20 L L (N 18 (N 19 L L L) L L)) L L)) (N 12 (N 33 L (N 20 L L (N 18
  (N 19 L L L) L L)) L) (N 26 (N 33 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 18 L L (N 20 (N 26 L
  L L) L L))) (N 12 L (N 18 L L (N 20 (N 26 L L L) L L)) L)) (N 8 (N 12 L L (N 19 L L (N 20 (N 26
  L L L) L L))) L (N 12 (N 20 L L (N 18 (N 19 L L L) L L)) L L)) (N 12 (N 33 L (N 20 L L (N 18 (N
  19 L L L) L L)) L) (N 26 (N 20 L L (N 18 (N 19 L L L) L L)) L L) L)) L) L) (N 34 (N 35 L L L) L
  L) L) L L) L) L))) L (N 13 (N 14 (N 17 (N 23 (N 27 L (N 30 L (N 5 L (N 8 L (N 12 L L (N 18 (N 19
  L L (N 24 (N 31 L L L) L L)) L (N 19 (N 25 (N 32 L L L) L L) L L))) (N 24 (N 31 (N 18 L L (N 32
  (N 33 L L (N 34 L (N 35 L L L) L)) L L)) L L) L L)) (N 8 L (N 25 (N 32 (N 19 L L (N 31 (N 33 L L
  (N 34 L (N 35 L L L) L)) L L)) L L) L L) L)) L) L) (N 27 (N 34 L (N 18 L (N 5 (N 30 L (N 35 (N
  31 L L (N 8 L (N 19 L L L) L)) L L) L) L (N 32 (N 33 L L (N 31 (N 8 (N 25 L (N 12 L L (N 19 L L
  (N 20 L (N 24 (N 26 L L (N 30 L (N 35 L L L) L)) L L) L))) L) (N 19 L L (N 24 (N 25 (N 26 L L (N
  30 L (N 35 L L L) L)) L L) L L)) L) L L)) L L)) (N 19 L (N 25 (N 32 (N 8 L L (N 30 L (N 35 L L
  L) L)) L L) L L) L)) L) (N 30 (N 34 L (N 35 (N 5 L (N 8 L (N 12 L L (N 18 (N 19 L L (N 24 L L
  L)) L (N 19 (N 25 L L L) L L))) (N 24 (N 31 L L L) L L)) (N 8 L (N 25 (N 32 L L L) L L) L)) L L)
  L) (N 35 (N 34 (N 18 L (N 5 (N 24 L L (N 8 L (N 19 L L L) L)) L (N 25 (N 8 L (N 32 L L L) L) L
  L)) (N 19 L (N 25 (N 32 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 19 L L (N 18 L (N 24 (N 31 L L
  L) L L) L))) (N 12 L (N 24 (N 31 L L L) L L) (N 18 L (N 19 L L (N 24 (N 31 L L L) L L)) (N 19 L
  (N 20 (N 24 (N 31 L L L) L L) L L) L)))) (N 8 (N 12 L L (N 18 L L (N 19 L (N 25 (N 32 L L L) L
  L) L))) L (N 24 (N 31 L L L) L L)) (N 8 (N 12 L (N 25 (N 32 L L L) L L) (N 18 L (N 19 L L (N 20
  (N 24 (N 31 L L L) L L) L L)) (N 19 L (N 24 (N 31 L L L) L L) L))) (N 25 (N 32 L L L) L L) L))
  L) L L) L) L) L) (N 23 (N 27 L (N 30 (N 34 L (N 35 L L L) L) (N 34 (N 35 (N 5 (N 8 L (N 12 L L
  (N 18 L L (N 25 L L L))) (N 24 L (N 18 L L (N 19 (N 31 L L L) L L)) L)) (N 8 (N 12 L L (N 19 L L
  (N 24 L L L))) L (N 24 (N 31 L L L) L L)) (N 8 (N 25 L (N 19 L L (N 18 (N 32 L L L) L L)) L) (N
  25 (N 32 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 18 L L (N 25 L L L))) (N 24 L (N 18 L L (N 25
  L L L)) L)) (N 8 (N 12 L L (N 19 L L (N 24 L L L))) L (N 24 (N 31 (N 18 L L (N 19 L L L)) L L) L
  L)) (N 8 (N 25 L (N 19 L L (N 24 L L L)) L) (N 25 (N 32 (N 18 L L (N 19 L L L)) L L) L L) L)) L)
  L L) L) L) (N 27 (N 30 (N 34 L (N 35 (N 5 (N 8 L (N 12 L L (N 18 L L (N 32 L L L))) (N 31 L (N
  18 L L (N 19 (N 24 L L L) L L)) L)) (N 8 (N 12 L L (N 19 L L (N 31 L L L))) L (N 24 (N 31 L L L)
  L L)) (N 8 (N 32 L (N 19 L L (N 18 (N 25 L L L) L L)) L) (N 25 (N 32 L L L) L L) L)) (N 5 (N 8 L
  (N 12 L L (N 18 L L (N 32 L L L))) (N 31 L (N 18 L L (N 32 L L L)) L)) (N 8 (N 12 L L (N 19 L L
  (N 31 L L L))) L (N 24 (N 18 L L (N 19 L L L)) L L)) (N 8 (N 32 L (N 19 L L (N 31 L L L)) L) (N
  25 (N 18 L L (N 19 L L L)) L L) L)) L) L) (N 34 (N 35 L L L) L L) L) L L) L) L) L (N 17 (N 23 (N
  27 L (N 30 L (N 5 L (N 8 L (N 12 L L (N 25 (N 32 (N 34 L (N 35 L L L) L) L L) L L)) (N 12 L (N
  24 (N 26 L L L) L L) L)) (N 8 L (N 25 (N 32 (N 34 L (N 35 L L L) L) L L) L L) L)) L) L) (N 27 (N
  34 L (N 18 L (N 5 (N 30 L (N 35 (N 31 L L (N 8 L (N 19 L L L) L)) L L) L) L (N 32 (N 8 (N 30 L
  (N 35 L L L) L) (N 19 L L (N 20 L (N 24 (N 26 L L L) L L) L)) L) L L)) (N 19 L (N 25 (N 32 (N 30
  L (N 35 L L L) L) L L) L L) L)) L) (N 30 (N 34 L (N 35 (N 5 L (N 8 L (N 12 L L (N 25 (N 32 L L
  L) L L)) (N 12 L (N 24 (N 26 L L L) L L) L)) (N 8 L (N 25 (N 32 L L L) L L) L)) L L) L) (N 35 (N
  34 (N 18 L (N 5 (N 24 L L (N 8 L (N 19 L L L) L)) L (N 25 (N 8 L (N 32 L L L) L) L L)) (N 19 L
  (N 25 (N 32 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 25 (N 32 L L L) L L)) (N 12 L (N 24 (N 26 L
  L L) L L) L)) (N 8 (N 12 L L (N 25 (N 32 L L L) L L)) L (N 12 (N 24 (N 26 L L L) L L) L L)) (N 8
  (N 12 L (N 25 (N 32 L L L) L L) (N 19 L (N 25 (N 32 L L L) L L) (N 18 (N 20 L (N 24 (N 25 L L L)
  L L) L) (N 20 (N 24 (N 26 L L L) L L) L L) L))) (N 25 (N 32 L L L) L L) L)) L) L L) L) L) L) (N
  23 (N 27 L (N 30 (N 34 L (N 35 L L L) L) (N 34 (N 35 (N 5 (N 8 L (N 12 L L (N 18 L L (N 19 (N 32
  L L L) L L))) (N 12 L (N 33 L L L) L)) (N 8 (N 12 L L (N 19 L L (N 18 (N 20 L L L) L L))) L (N
  12 (N 31 L L L) L L)) (N 8 (N 25 L (N 19 L L (N 18 (N 20 L L L) L L)) L) (N 25 (N 32 L L L) L L)
  L)) (N 5 (N 8 L (N 12 L L (N 18 L L (N 19 (N 32 L L L) L L))) (N 12 L (N 18 L L (N 19 (N 32 L L
  L) L L)) L)) (N 8 (N 12 L L (N 19 L L (N 18 (N 20 L L L) L L))) L (N 12 (N 19 (N 32 L L L) L L)
  L L)) (N 8 (N 25 L (N 19 L L (N 18 (N 20 L L L) L L)) L) (N 25 (N 32 (N 19 L L (N 18 (N 20 L L
  L) L L)) L L) L L) L)) L) L L) L) L) (N 27 (N 30 (N 34 L (N 35 (N 5 (N 8 L (N 12 L L (N 18 L L
  (N 19 (N 25 L L L) L L))) (N 12 L (N 26 L L L) L)) (N 8 (N 12 L L (N 19 L L (N 18 (N 20 L L L) L
  L))) L (N 12 (N 24 L L L) L L)) (N 8 (N 32 L (N 19 L L (N 18 (N 20 L L L) L L)) L) (N 25 (N 32 L
  L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 18 L L (N 19 (N 25 L L L) L L))) (N 12 L (N 18 L L (N 19
  (N 25 L L L) L L)) L)) (N 8 (N 12 L L (N 19 L L (N 18 (N 20 L L L) L L))) L (N 12 (N 19 (N 25 L
  L L) L L) L L)) (N 8 (N 32 L (N 19 L L (N 18 (N 20 L L L) L L)) L) (N 25 (N 19 L L (N 18 (N 20 L
  L L) L L)) L L) L)) L) L) (N 34 (N 35 L L L) L L) L) L L) L) L)) L (N 14 (N 17 (N 23 (N 27 L (N
  30 L (N 5 L (N 8 L (N 12 L L (N 24 (N 31 (N 34 L (N 35 L L L) L) L L) L L)) (N 24 (N 31 (N 34 L
  (N 35 L L L) L) L L) L L)) (N 8 L (N 12 L (N 25 (N 26 L L L) L L) L) L)) L) L) (N 27 (N 34 L (N
  18 L (N 5 (N 30 L (N 35 (N 31 L L (N 8 L (N 12 L L L) L)) L L) L) L (N 24 (N 31 (N 30 L (N 35 L
  L L) L) L L) L L)) (N 19 L (N 20 L (N 25 (N 26 L L L) L L) L) L)) L) (N 30 (N 34 L (N 35 (N 5 L
  (N 8 L (N 12 L L (N 24 (N 31 L L L) L L)) (N 24 (N 31 L L L) L L)) (N 8 L (N 12 L (N 24 (N 18 L
  (N 31 L L L) L) L L) L) L)) L L) L) (N 35 (N 34 (N 18 L (N 5 (N 24 L L (N 8 L (N 12 L L L) L)) L
  (N 24 (N 31 L L L) L L)) (N 19 L (N 20 L (N 24 (N 5 L (N 31 L L L) L) L L) L) L)) (N 5 (N 8 L (N
  12 L L (N 24 (N 31 L L L) L L)) (N 12 L (N 24 (N 31 L L L) L L) (N 18 L (N 24 (N 31 L L L) L L)
  (N 19 (N 20 L (N 24 (N 25 L L L) L L) L) (N 20 (N 24 (N 26 L L L) L L) L L) L)))) (N 8 (N 12 L L
  (N 24 (N 31 L L L) L L)) L (N 24 (N 31 L L L) L L)) (N 8 (N 12 L (N 24 (N 31 L L L) L L) L) (N
  12 (N 24 (N 31 L L L) L L) L L) L)) L) L L) L) L) L) (N 23 (N 27 L (N 30 (N 34 L (N 35 L L L) L)
  (N 34 (N 35 (N 5 (N 8 L (N 12 L L (N 18 L L (N 19 (N 20 L L L) L L))) (N 24 L (N 18 L L (N 19 (N
  20 L L L) L L)) L)) (N 8 (N 12 L L (N 19 L L (N 18 (N 31 L L L) L L))) L (N 24 (N 31 L L L) L
  L)) (N 8 (N 12 L (N 33 L L L) L) (N 12 (N 32 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 18 L L (N
  19 (N 20 L L L) L L))) (N 24 L (N 18 L L (N 19 (N 20 L L L) L L)) L)) (N 8 (N 12 L L (N 19 L L
  (N 18 (N 31 L L L) L L))) L (N 24 (N 31 (N 18 L L (N 19 (N 20 L L L) L L)) L L) L L)) (N 8 (N 12
  L (N 18 (N 31 L L L) L L) L) (N 12 (N 18 (N 31 L L L) L L) L L) L)) L) L L) L) L) (N 27 (N 30 (N
  34 L (N 35 (N 5 (N 8 L (N 12 L L (N 18 L L (N 19 (N 20 L L L) L L))) (N 31 L (N 18 L L (N 19 (N
  20 L L L) L L)) L)) (N 8 (N 12 L L (N 19 L L (N 18 (N 24 L L L) L L))) L (N 24 (N 31 L L L) L
  L)) (N 8 (N 12 L (N 26 L L L) L) (N 12 (N 25 L L L) L L) L)) (N 5 (N 8 L (N 12 L L (N 18 L L (N
  19 (N 20 L L L) L L))) (N 31 L (N 18 L L (N 19 (N 20 L L L) L L)) L)) (N 8 (N 12 L L (N 19 L L
  (N 18 (N 24 L L L) L L))) L (N 24 (N 18 L L (N 19 (N 20 L L L) L L)) L L)) (N 8 (N 12 L (N 18 (N
  24 L L L) L L) L) (N 12 (N 18 (N 24 L L L) L L) L L) L)) L) L) (N 34 (N 35 L L L) L L) L) L L)
  L) L) L L))))) L (S 22 L L (S 29 L L L))) (S 16 (S 22 (S 29 L (N 27 L (N 9 (N 12 (N 13 (N 14 L L
  (N 5 L (N 18 (N 24 L L (N 31 L L (N 19 L (N 25 L L (N 26 L L L)) (N 20 L (N 26 L L L) L)))) L (N
  20 L (N 26 L L (N 25 (N 24 L L (N 23 L (N 32 (N 35 L L L) L L) L)) L L)) (N 26 L (N 19 (N 17 L
  (N 24 L L (N 32 (N 34 L L L) L L)) L) L L) L))) (N 20 L (N 26 L L (N 24 (N 25 L L L) L L)) (N 26
  L (N 18 (N 19 L L L) L L) L)))) L (N 14 (N 8 L (N 19 (N 25 L L (N 32 L L (N 18 L (N 24 L L (N 26
  L L L)) (N 20 L (N 26 L L L) L)))) L (N 20 L (N 26 L L (N 24 (N 25 L L (N 23 L (N 31 (N 35 L L
  L) L L) L)) L L)) (N 26 L (N 18 (N 17 L (N 25 L L (N 31 (N 34 L L L) L L)) L) L L) L))) (N 20 L
  (N 26 L L (N 24 (N 25 L L L) L L)) (N 26 L (N 18 (N 19 L L L) L L) L))) L (N 20 L (N 26 L L L)
  L))) (N 13 (N 14 L L (N 31 (N 32 L L (N 33 L L L)) L (N 32 (N 33 (N 34 (N 35 L (N 19 L L (N 20 L
  (N 26 L L L) L)) L) (N 35 (N 25 L L (N 20 L (N 26 L L L) L)) L L) L) L (N 5 (N 8 L (N 19 (N 25 L
  L L) L L) (N 18 L (N 24 L L (N 25 (N 35 L L L) L L)) (N 19 (N 25 L (N 34 L L L) L) (N 24 L L (N
  25 (N 35 L L L) L L)) L))) (N 18 (N 19 L (N 25 L L L) L) L (N 19 (N 24 L L (N 25 L (N 34 L L L)
  L)) (N 25 (N 35 L L L) L L) L)) L)) L (N 33 (N 20 (N 26 L (N 18 L L (N 34 L (N 35 L L L) L)) L)
  (N 26 (N 24 L L (N 34 L (N 35 L L L) L)) L L) L) L L)))) L (N 14 (N 31 (N 32 L L (N 33 (N 34 (N
  35 L (N 18 L L (N 20 L (N 26 L L L) L)) L) (N 35 (N 24 L L (N 20 L (N 26 L L L) L)) L L) L) L (N
  8 (N 5 L (N 18 (N 24 L L L) L L) (N 18 (N 24 L (N 34 L L L) L) (N 24 (N 35 L L L) L L) L)) (N 18
  (N 19 L L (N 24 L (N 34 L L L) L)) (N 24 (N 35 L L L) L L) L) L))) L (N 33 (N 32 L L (N 20 (N 26
  L (N 19 L L (N 34 L (N 35 L L L) L)) L) (N 26 (N 25 L L (N 34 L (N 35 L L L) L)) L L) L)) L L))
  L (N 33 (N 20 (N 34 L (N 35 L L L) L) (N 26 (N 34 L (N 35 L L L) L) L L) L) L L))) L) L (N 12 (N
  13 (N 5 L (N 14 (N 33 L L (N 8 L (N 18 (N 19 (N 34 L (N 17 L L (N 35 (N 31 L L (N 32 L L L)) L
  L)) L) L (N 24 (N 31 L L L) L L)) L (N 19 (N 25 (N 32 L L L) L L) L L)) (N 32 (N 18 (N 34 L (N
  35 (N 24 L L (N 25 L L L)) L L) L) L (N 19 (N 25 L (N 34 L L L) L) (N 25 (N 35 L L L) L L) L)) L
  L))) L (N 18 (N 20 L (N 26 L L (N 25 (N 32 (N 33 (N 19 L (N 34 L L L) L) L L) L L) L L)) (N 26 L
  (N 19 (N 32 (N 33 L L L) L L) L L) L)) L (N 32 (N 19 (N 34 L (N 35 L L L) L) (N 25 (N 35 L L L)
  L L) L) L L))) (N 14 (N 8 L (N 33 L L (N 31 (N 19 (N 34 L (N 35 (N 24 L L (N 25 L L L)) L L) L)
  L (N 18 (N 24 L (N 34 L L L) L) (N 24 (N 35 L L L) L L) L)) L L)) L) L L)) L (N 14 (N 8 L (N 19
  (N 20 L (N 26 L L (N 24 (N 31 (N 33 (N 18 L (N 34 L L L) L) L L) L L) L L)) (N 26 L (N 18 (N 31
  (N 33 L L L) L L) L L) L)) L (N 31 (N 18 (N 34 L (N 35 L L L) L) (N 24 (N 35 L L L) L L) L) L
  L)) L) L L)) (N 13 (N 14 (N 31 (N 33 L L (N 32 (N 34 (N 35 L (N 18 L L (N 19 L L L)) L) (N 35 (N
  24 L L (N 25 L L L)) L L) L) L (N 8 (N 30 L (N 18 (N 24 L (N 34 L L L) L) (N 24 (N 35 L L L) L
  L) L) L) (N 18 (N 24 L (N 34 L L L) L) (N 24 (N 35 L L L) L L) L) L))) L (N 32 (N 33 L L (N 5 (N
  30 L (N 18 L (N 24 L L (N 25 (N 35 L L L) L L)) (N 24 L (N 19 (N 34 L L L) L L) L)) L) (N 18 (N
  34 L (N 25 (N 35 L L L) L L) L) L (N 24 (N 35 L (N 19 (N 34 L L L) L L) L) L L)) L)) L L)) L (N
  5 (N 18 L (N 24 L L (N 25 (N 32 (N 35 L L L) L L) L L)) (N 32 (N 19 (N 34 L (N 35 L L L) L) (N
  24 L L (N 25 (N 35 L L L) L L)) L) L L)) (N 18 (N 20 L (N 26 L L (N 25 (N 32 (N 33 (N 19 L (N 34
  L L L) L) L L) L L) L L)) (N 26 L (N 19 (N 32 (N 33 L L L) L L) L L) L)) L (N 32 (N 19 (N 34 L
  (N 35 L L L) L) (N 25 (N 35 L L L) L L) L) L L)) L)) L (N 14 (N 8 (N 19 L (N 25 L L (N 24 (N 31
  (N 35 L L L) L L) L L)) (N 31 (N 18 (N 34 L (N 35 L L L) L) (N 24 (N 35 L L L) L L) L) L L)) (N
  19 (N 20 L (N 26 L L (N 24 (N 31 (N 33 (N 18 L (N 34 L L L) L) L L) L L) L L)) (N 26 L (N 18 (N
  31 (N 33 L L L) L L) L L) L)) L (N 31 (N 18 (N 34 L (N 35 L L L) L) (N 24 (N 35 L L L) L L) L) L
  L)) L) L L)) L)) L) (N 27 L (N 9 (N 12 (N 20 L (N 26 L L L) L) (N 13 (N 14 L L (N 17 (N 20 (N 34
  L (N 35 (N 30 L (N 33 L L L) L) L L) L) (N 26 (N 24 L L (N 33 (N 34 L (N 35 L L L) L) L L)) L L)
  L) (N 20 (N 18 L L (N 23 (N 19 (N 34 L (N 30 (N 35 L L L) L L) L) L (N 24 L (N 5 (N 30 L (N 8 L
  L (N 31 L L (N 32 (N 34 L L L) L L))) L) L (N 26 (N 33 L (N 35 L L L) L) (N 33 (N 35 L L L) L L)
  L)) (N 26 (N 33 L (N 35 L L L) L) (N 33 (N 34 L (N 35 L L L) L) L L) L))) L L)) L L) L)) L (N 14
  (N 17 (N 20 (N 34 L (N 35 (N 30 L (N 33 L L L) L) L L) L) (N 26 (N 25 L L (N 33 (N 34 L (N 35 L
  L L) L) L L)) L L) L) (N 20 (N 19 L L (N 23 (N 18 (N 34 L (N 30 (N 35 L L L) L L) L) L (N 25 L
  (N 8 (N 30 L (N 5 L L (N 31 (N 34 L L L) L L)) L) L (N 26 (N 33 L (N 35 L L L) L) (N 33 (N 35 L
  L L) L L) L)) (N 26 (N 33 L (N 35 L L L) L) (N 33 (N 34 L (N 35 L L L) L) L L) L))) L L)) L L)
  L) L (N 17 (N 20 (N 34 L (N 35 (N 30 L (N 33 L L L) L) L L) L) (N 26 (N 33 (N 34 L (N 35 L L L)
  L) L L) L L) L) (N 20 (N 23 (N 18 (N 19 L L (N 34 L (N 30 (N 35 L L L) L L) L)) L (N 19 (N 34 L
  (N 30 (N 35 L L L) L L) L) L (N 26 (N 35 L (N 33 (N 34 L L L) L L) L) (N 33 (N 34 L (N 35 L L L)
  L) L L) L))) L L) L L) L))) L) L (N 12 (N 20 L (N 26 L L L) L) (N 13 (N 14 (N 17 (N 20 (N 26 L
  (N 33 L L L) L) (N 26 (N 33 L L L) L L) L) (N 20 (N 18 L L (N 19 L L L)) L L) L) L (N 5 (N 17 (N
  23 L (N 24 L L (N 25 (N 26 (N 30 L (N 35 L L L) L) L L) L L)) L) (N 18 L L (N 19 (N 20 (N 23 (N
  30 L (N 34 L L L) L) L L) L L) L L)) L) (N 31 (N 33 L (N 20 (N 18 L L (N 24 L L (N 26 (N 30 (N
  17 L (N 23 L L L) L) L L) L L))) L L) L) L L) L)) L (N 14 (N 8 (N 17 (N 23 L (N 25 L L (N 24 (N
  26 (N 30 L (N 35 L L L) L) L L) L L)) L) (N 19 L L (N 18 (N 20 (N 23 (N 30 L (N 34 L L L) L) L
  L) L L) L L)) L) (N 32 (N 33 L (N 20 (N 19 L L (N 25 L L (N 26 (N 30 (N 17 L (N 23 L L L) L) L
  L) L L))) L L) L) L L) L) L L)) L)) L)) (S 29 L L (N 26 (N 9 (N 12 (N 20 L (N 23 L (N 13 (N 14 L
  L (N 24 L L (N 33 L (N 34 (N 30 L (N 5 L L (N 27 (N 35 L L L) L L)) L) L L) L))) L (N 14 (N 25 L
  L (N 33 L (N 34 (N 30 L (N 8 L L (N 27 (N 35 L L L) L L)) L) L L) L)) L (N 17 (N 30 L (N 35 (N
  33 L (N 34 L L L) L) L L) L) (N 27 (N 5 (N 8 L L (N 18 L L (N 25 L L (N 19 (N 30 L (N 34 L L L)
  L) L L)))) L (N 8 (N 19 L L (N 24 L L (N 18 (N 30 L (N 34 L L L) L) L L))) L (N 18 (N 19 L L (N
  24 L L (N 25 (N 34 L (N 30 (N 32 L L L) L L) L) L L))) L (N 24 (N 25 L L (N 19 (N 34 L (N 30 (N
  31 L L L) L L) L) L L)) L L)))) L L) L))) L) L) (N 13 (N 14 L L (N 24 L L (N 17 (N 20 (N 27 L (N
  33 L (N 30 (N 23 L (N 34 L L L) L) L L) L) L) (N 33 (N 35 L (N 23 (N 27 L (N 30 L L L) L) (N 27
  (N 30 L L L) L L) L) L) L L) L) (N 20 (N 18 L L (N 27 L (N 23 (N 8 L L (N 33 L (N 30 (N 35 L L
  L) L L) L)) L L) L)) L L) L))) L (N 14 (N 25 L L (N 17 (N 20 (N 27 L (N 33 L (N 30 (N 23 L (N 34
  L L L) L) L L) L) L) (N 33 (N 35 L (N 23 (N 27 L (N 30 L L L) L) (N 27 (N 30 L L L) L L) L) L) L
  L) L) (N 20 (N 19 L L (N 27 L (N 23 (N 5 L L (N 33 L (N 30 (N 35 L L L) L L) L)) L L) L)) L L)
  L)) L (N 17 (N 20 (N 27 L (N 34 L (N 35 (N 30 L (N 33 L L L) L) L L) L) L) (N 33 (N 35 L (N 23
  (N 27 L (N 30 L L L) L) (N 27 (N 30 L L L) L L) L) L) L L) L) (N 20 (N 27 L (N 23 (N 5 (N 8 L L
  (N 18 L L (N 24 L L (N 30 L (N 31 (N 33 L L L) L L) L)))) L (N 8 (N 19 L L (N 25 L L (N 30 L (N
  32 (N 33 L L L) L L) L))) L (N 18 (N 19 L L (N 25 L L L)) L (N 24 (N 19 L L (N 25 L L L)) L
  L)))) L L) L) L L) L))) L) L (N 12 (N 20 L (N 23 L (N 13 (N 14 L L (N 5 L (N 17 (N 24 L L (N 25
  (N 19 L (N 8 L L (N 30 L (N 33 L L L) L)) L) L L)) L L) L)) L (N 14 (N 8 L (N 17 (N 25 L L (N 24
  (N 18 L (N 5 L L (N 30 L (N 33 L L L) L)) L) L L)) L L) L) L L)) L) L) (N 13 (N 24 L L (N 25 (N
  14 L L (N 5 (N 8 L (N 19 (N 27 L (N 17 (N 20 L (N 23 L (N 30 L L L) L) L) L L) L) L L) (N 17 (N
  23 L (N 27 L (N 30 L (N 31 (N 32 L L L) L L) L) L) L) (N 18 L L (N 19 (N 20 (N 27 L (N 23 (N 30
  L (N 33 L L L) L) L L) L) L L) L L)) L)) (N 31 (N 32 L (N 19 (N 8 L L (N 18 L L (N 27 L (N 17 (N
  34 L L L) L L) L))) L L) L) L L) L)) L L)) L (N 14 (N 25 L L (N 24 (N 8 (N 5 L (N 18 (N 27 L (N
  17 (N 20 L (N 23 L (N 30 L L L) L) L) L L) L) L L) (N 17 (N 23 L (N 27 L (N 30 L (N 31 (N 32 L L
  L) L L) L) L) L) (N 18 (N 19 L L (N 20 (N 27 L (N 23 (N 30 L (N 33 L L L) L) L L) L) L L)) L L)
  L)) (N 32 (N 31 L (N 18 (N 5 L L (N 19 L L (N 27 L (N 17 (N 34 L L L) L L) L))) L L) L) L L) L)
  L L)) L L)) L)) L L)) (S 29 L L L)) (S 22 L L (S 29 L L L)) (S 22 L L L))) (S 11 L L (S 16 (S 22
  (S 29 L (N 14 (N 27 L (N 8 (N 12 L (N 9 (N 13 L L (N 32 L L (N 31 (N 5 L (N 18 (N 24 L L (N 25 L
  (N 19 L L (N 20 (N 23 (N 33 (N 26 L (N 35 L L L) L) L L) L L) L L)) L)) L (N 19 L (N 17 (N 25 L
  L (N 24 (N 26 (N 33 (N 20 L (N 34 L L L) L) L L) L L) L L)) L L) L)) (N 19 L (N 25 L L (N 24 (N
  34 L (N 35 L L L) L) L L)) (N 25 L (N 18 (N 34 L (N 35 L L L) L) L L) L))) L L))) L (N 13 (N 19
  L (N 25 L L (N 24 (N 26 L L (N 23 L (N 31 (N 18 L (N 34 L L L) L) L L) L)) L L)) (N 25 L (N 18
  (N 20 L L (N 17 L (N 31 (N 24 L (N 34 L L L) L) L L) L)) L L) L)) L (N 19 L (N 25 L L (N 24 (N
  31 (N 32 (N 26 L L (N 33 L L L)) L L) L L) L L)) (N 25 L (N 18 (N 31 (N 32 (N 20 L L (N 33 L L
  L)) L L) L L) L L) L)))) L) (N 9 (N 13 L L (N 12 (N 20 L (N 26 L L (N 24 (N 25 L L (N 23 L (N 31
  (N 18 L (N 34 L L L) L) L L) L)) L L)) (N 26 L (N 18 (N 19 L L (N 17 L (N 31 (N 24 L (N 34 L L
  L) L) L L) L)) L L) L)) (N 31 (N 32 L L (N 33 (N 34 (N 35 L (N 18 L L (N 20 L (N 26 L L L) L))
  L) (N 35 (N 24 L L (N 20 L (N 26 L L L) L)) L L) L) L (N 18 (N 24 L (N 34 L L L) L) (N 24 (N 35
  L L L) L L) L))) L (N 32 (N 33 L L L) L L)) L)) L (N 12 (N 13 (N 33 L L (N 31 (N 5 L (N 18 (N 24
  L L (N 26 L (N 19 (N 20 L L (N 23 (N 32 (N 25 L (N 35 L L L) L) L L) L L)) L L) L)) L (N 20 L (N
  17 (N 25 (N 26 L L (N 24 (N 32 (N 19 L (N 34 L L L) L) L L) L L)) L L) L L) L)) (N 20 L (N 26 L
  L (N 24 (N 34 L (N 35 L L L) L) L L)) (N 26 L (N 18 (N 34 L (N 35 L L L) L) L L) L))) L L)) L (N
  20 L (N 26 L L (N 24 (N 31 (N 33 (N 25 L L (N 32 L L L)) L L) L L) L L)) (N 26 L (N 18 (N 31 (N
  33 (N 19 L L (N 32 L L L)) L L) L L) L L) L))) (N 13 (N 31 (N 33 L L (N 32 (N 34 (N 35 L (N 18 L
  L (N 19 L (N 25 L L L) L)) L) (N 35 (N 24 L L (N 19 L (N 25 L L L) L)) L L) L) L (N 18 (N 24 L
  (N 34 L L L) L) (N 24 (N 35 L L L) L L) L))) L (N 32 (N 33 L L L) L L)) L (N 31 (N 32 (N 33 L L
  (N 18 (N 20 L (N 24 (N 26 L L L) L L) L) (N 24 (N 26 L L L) L L) L)) L (N 18 (N 34 L (N 35 L L
  L) L) (N 24 (N 35 L L L) L L) L)) L (N 32 (N 33 L L L) L L))) L)) L) L) L L) L) (S 29 L (N 14 (N
  35 (N 8 (N 12 L (N 9 (N 13 L L (N 25 L L (N 24 (N 31 L L (N 32 L L L)) L L))) L (N 13 (N 19 L (N
  17 (N 5 L (N 18 L L (N 25 (N 32 L L L) L L)) (N 18 L (N 23 L (N 24 (N 26 L L (N 31 L L (N 32 L L
  L))) L (N 25 (N 26 L L L) L L)) (N 24 (N 31 L L L) L L)) (N 23 L (N 24 (N 31 L L L) L L) L))) L
  (N 18 (N 5 L (N 20 L (N 24 (N 26 L L (N 27 L (N 31 L L (N 32 L L L)) L)) L (N 25 (N 26 L L L) L
  L)) (N 24 (N 26 L L (N 27 L (N 31 L L (N 32 L L L)) L)) L (N 25 (N 26 L L L) L L))) (N 24 (N 31
  L L L) L L)) (N 5 (N 23 L (N 24 (N 26 L L (N 31 L L (N 32 L L L))) L (N 25 (N 26 L L L) L L)) (N
  24 (N 26 L L (N 25 (N 27 L (N 30 L (N 31 L L (N 32 L L L)) L) L) L L)) L L)) L (N 24 (N 31 L L
  L) L L)) L)) (N 24 (N 31 L L L) L L)) L (N 19 L (N 17 (N 5 L (N 18 (N 27 L (N 34 L (N 20 L L (N
  24 (N 31 L L L) L L)) L) L) L (N 24 (N 31 L L L) L L)) (N 24 (N 31 L L L) L L)) L (N 18 (N 5 L
  (N 24 (N 27 L (N 31 L L (N 25 (N 26 L L L) L L)) L) L (N 25 (N 26 L L L) L L)) (N 24 (N 31 L L
  L) L L)) (N 5 (N 23 L (N 24 (N 26 L L (N 31 L L L)) L (N 25 (N 26 L L L) L L)) (N 24 (N 26 L L
  (N 31 L L L)) L L)) L (N 24 (N 31 L L L) L L)) L)) (N 24 (N 31 L L L) L L)))) L) (N 9 (N 13 L L
  (N 12 (N 20 L (N 17 (N 5 L (N 18 L L (N 26 (N 33 L L L) L L)) (N 18 L (N 23 L (N 24 (N 25 L L (N
  31 L L (N 33 L L L))) L (N 25 (N 26 L L L) L L)) (N 24 (N 31 L L L) L L)) (N 23 L (N 24 (N 31 L
  L L) L L) L))) L (N 18 (N 5 L (N 19 L (N 24 (N 25 L L (N 27 L (N 31 L L (N 33 L L L)) L)) L (N
  25 (N 26 L L L) L L)) (N 24 (N 25 L L (N 27 L (N 31 L L (N 33 L L L)) L)) L (N 25 (N 26 L L L) L
  L))) (N 24 (N 31 L L L) L L)) (N 5 (N 23 L (N 24 (N 25 L L (N 31 L L (N 33 L L L))) L (N 25 (N
  26 L L L) L L)) (N 24 (N 25 L L (N 26 (N 27 L (N 30 L (N 31 L L (N 33 L L L)) L) L) L L)) L L))
  L (N 24 (N 31 L L L) L L)) L)) (N 24 (N 31 L L L) L L)) (N 24 (N 25 L L (N 31 L L (N 33 L L L)))
  L (N 25 (N 26 L L L) L L)) L)) L (N 12 (N 13 (N 26 L L (N 24 (N 31 L L (N 32 L L L)) L L)) L (N
  20 L (N 17 (N 5 L (N 18 (N 27 L (N 34 L (N 19 L L (N 24 (N 31 L L L) L L)) L) L) L (N 24 (N 31 L
  L L) L L)) (N 24 (N 31 L L L) L L)) L (N 18 (N 5 L (N 24 (N 27 L (N 31 L L (N 25 (N 26 L L L) L
  L)) L) L (N 25 (N 26 L L L) L L)) (N 24 (N 31 L L L) L L)) (N 5 (N 23 L (N 24 (N 25 L L (N 31 L
  L L)) L (N 25 (N 26 L L L) L L)) (N 24 (N 25 L L (N 31 L L L)) L L)) L (N 24 (N 31 L L L) L L))
  L)) (N 24 (N 31 L L L) L L))) (N 13 (N 24 (N 26 L L (N 31 L L (N 32 L L L))) L (N 25 (N 26 L L
  L) L L)) L (N 24 (N 31 L L (N 25 (N 26 L L L) L L)) L (N 25 (N 26 L L L) L L))) L)) L) L L) L L)
  L) L) (S 22 L (S 29 L L L) L) L))) (S 7 L L (S 11 L L L))))))) (S 15 L L (S 21 L L (S 28 L L
  L)))) (S 10 L L (S 15 L L (S 21 L L L)))) (S 6 L L (S 10 L L (S 15 L L L)))) (S 3 L (S 6 L (S 10
  L L (S 15 L L (S 21 L L (S 28 L L L)))) (S 10 L L (S 15 L L (S 21 L L L)))) (S 6 L L (S 10 L L
  (S 15 L L L)))) (S 3 L L (S 6 L L (S 10 L L L)))) (S 1 L (S 3 L (S 6 L L (S 10 L L (S 15 L L (S
  21 L L L)))) (S 6 L L (S 10 L L (S 15 L L L)))) (S 3 L L (S 6 L L (S 10 L L L)))) (S 1 L L (S 3
  L L (S 6 L L L))))

theorem cert_ok : check cert 0 0 0 = true := by decide +kernel

/-! ### Soundness of the checker -/

/-- The partial colouring `(m0, m1, m2)` is consistent with the edge colouring `col`. -/
def Cons (col : Nat → Fin 3) (m0 m1 m2 : Nat) : Prop :=
  (∀ i, m0.testBit i = true → col i = 0) ∧ (∀ i, m1.testBit i = true → col i = 1) ∧
    (∀ i, m2.testBit i = true → col i = 2)

/-- `col` violates one of the order conditions. -/
def SortBad (col : Nat → Fin 3) : Prop :=
  (∃ p ∈ upairs, (col (eix 0 p.2)).val < (col (eix 0 p.1)).val) ∨
  (∃ p ∈ quads, 3 * (col (eix 0 p.2)).val + (col (eix 1 p.2)).val <
    3 * (col (eix 0 p.1)).val + (col (eix 1 p.1)).val)

/-- `col` contains a monochromatic forbidden configuration or violates the order conditions. -/
def Bad (col : Nat → Fin 3) : Prop :=
  (∃ e, ∃ K ∈ forbM e, ∃ k : Fin 3, ∀ i, K.testBit i = true → col i = k) ∨ SortBad col

theorem colOf_eq {col : Nat → Fin 3} {m0 m1 m2 e : Nat} (h : Cons col m0 m1 m2)
    (hl : colOf m0 m1 m2 e < 3) : colOf m0 m1 m2 e = (col e).val := by
  obtain ⟨h0, h1, h2⟩ := h
  unfold colOf at *
  by_cases b0 : m0.testBit e = true
  · simp [b0, h0 e b0]
  · by_cases b1 : m1.testBit e = true
    · simp [b0, b1, h1 e b1]
    · by_cases b2 : m2.testBit e = true
      · simp [b0, b1, b2, h2 e b2]
      · simp [b0, b1, b2] at hl

theorem sortViol_sound {col : Nat → Fin 3} {m0 m1 m2 : Nat} (h : Cons col m0 m1 m2)
    (hs : sortViol m0 m1 m2 = true) : SortBad col := by
  unfold sortViol at hs
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, Nat.blt_eq] at hs
  rcases hs with ⟨p, hp, h1, h2⟩ | ⟨p, hp, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩
  · left
    refine ⟨p, hp, ?_⟩
    rw [colOf_eq h (lt_trans h1 h2), colOf_eq h h2] at h1
    exact h1
  · right
    refine ⟨p, hp, ?_⟩
    rw [colOf_eq h h1, colOf_eq h h2, colOf_eq h h3, colOf_eq h h4] at h5
    exact h5

theorem or_bit {col : Nat → Fin 3} {m e : Nat} {k : Fin 3}
    (hm : ∀ i, m.testBit i = true → col i = k) (he : col e = k) :
    ∀ i, (m ||| 2 ^ e).testBit i = true → col i = k := by
  intro i hi
  rw [Nat.testBit_or, Nat.testBit_two_pow] at hi
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hi
  rcases hi with hi | rfl
  · exact hm i hi
  · exact he

theorem bad_Bad {col : Nat → Fin 3} {e m : Nat} {k : Fin 3} (hb : bad e m = true)
    (hm : ∀ i, m.testBit i = true → col i = k) : Bad col := by
  obtain ⟨K, hK, hKm⟩ := bad_sound hb
  exact Or.inl ⟨e, K, hK, k, fun i hi => hm i (hKm i hi)⟩

theorem fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> simp

/-- **Soundness of the certificate checker.** -/
theorem check_sound (col : Nat → Fin 3) :
    ∀ (t : Cert) (m0 m1 m2 : Nat), check t m0 m1 m2 = true → Cons col m0 m1 m2 → Bad col := by
  intro t
  induction t with
  | L => intro m0 m1 m2 h; exact absurd h (by simp [check])
  | N e t0 t1 t2 ih0 ih1 ih2 =>
    intro m0 m1 m2 h hc
    change ((bad e (m0 ||| 2 ^ e) || check t0 (m0 ||| 2 ^ e) m1 m2) &&
      (bad e (m1 ||| 2 ^ e) || check t1 m0 (m1 ||| 2 ^ e) m2) &&
      (bad e (m2 ||| 2 ^ e) || check t2 m0 m1 (m2 ||| 2 ^ e))) = true at h
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨h0, h1⟩, h2⟩ := h
    obtain ⟨c0, c1, c2⟩ := hc
    rcases fin3_cases (col e) with he | he | he
    · rcases h0 with hb | hk
      · exact bad_Bad hb (or_bit c0 he)
      · exact ih0 _ _ _ hk ⟨or_bit c0 he, c1, c2⟩
    · rcases h1 with hb | hk
      · exact bad_Bad hb (or_bit c1 he)
      · exact ih1 _ _ _ hk ⟨c0, or_bit c1 he, c2⟩
    · rcases h2 with hb | hk
      · exact bad_Bad hb (or_bit c2 he)
      · exact ih2 _ _ _ hk ⟨c0, c1, or_bit c2 he⟩
  | S e t0 t1 t2 ih0 ih1 ih2 =>
    intro m0 m1 m2 h hc
    change ((bad e (m0 ||| 2 ^ e) || sortViol (m0 ||| 2 ^ e) m1 m2 ||
        check t0 (m0 ||| 2 ^ e) m1 m2) &&
      (bad e (m1 ||| 2 ^ e) || sortViol m0 (m1 ||| 2 ^ e) m2 || check t1 m0 (m1 ||| 2 ^ e) m2) &&
      (bad e (m2 ||| 2 ^ e) || sortViol m0 m1 (m2 ||| 2 ^ e) ||
        check t2 m0 m1 (m2 ||| 2 ^ e))) = true at h
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨h0, h1⟩, h2⟩ := h
    obtain ⟨c0, c1, c2⟩ := hc
    rcases fin3_cases (col e) with he | he | he
    · rcases h0 with (hb | hs) | hk
      · exact bad_Bad hb (or_bit c0 he)
      · exact Or.inr (sortViol_sound ⟨or_bit c0 he, c1, c2⟩ hs)
      · exact ih0 _ _ _ hk ⟨or_bit c0 he, c1, c2⟩
    · rcases h1 with (hb | hs) | hk
      · exact bad_Bad hb (or_bit c1 he)
      · exact Or.inr (sortViol_sound ⟨c0, or_bit c1 he, c2⟩ hs)
      · exact ih1 _ _ _ hk ⟨c0, or_bit c1 he, c2⟩
    · rcases h2 with (hb | hs) | hk
      · exact bad_Bad hb (or_bit c2 he)
      · exact Or.inr (sortViol_sound ⟨c0, c1, or_bit c2 he⟩ hs)
      · exact ih2 _ _ _ hk ⟨c0, c1, or_bit c2 he⟩

/-! ### From masks back to the colouring -/

/-- The edges of `K_9` in index order (`eix`). -/
def edgeList : List (Sym2 (Fin 9)) :=
  [s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(1, 3), s(2, 3), s(0, 4), s(1, 4), s(2, 4), s(3, 4), s(0, 5), s(1, 5), s(2, 5), s(3, 5), s(4, 5), s(0, 6), s(1, 6), s(2, 6), s(3, 6), s(4, 6), s(5, 6), s(0, 7), s(1, 7), s(2, 7), s(3, 7), s(4, 7), s(5, 7), s(6, 7), s(0, 8), s(1, 8), s(2, 8), s(3, 8), s(4, 8), s(5, 8), s(6, 8), s(7, 8)]

/-- The edge with index `n`. -/
def edgeOf (n : Nat) : Sym2 (Fin 9) := edgeList.getD n s(0, 0)

theorem edgeOf_eix : ∀ a b : Fin 9, a ≠ b → edgeOf (eix a b) = s(a, b) := by decide

theorem shapes_ok_bool : forbS.all (fun l => l.all Shape.valid) = true := by
  decide +kernel

theorem shapes_ok {e : Nat} {p : Shape} (hp : p ∈ forbS.getD e []) : p.valid = true := by
  rw [List.getD_eq_getElem?_getD] at hp
  cases h : forbS[e]? with
  | none => rw [h] at hp; simp at hp
  | some l =>
    rw [h] at hp
    have hl : l ∈ forbS := List.mem_of_getElem? h
    exact List.all_eq_true.1 (List.all_eq_true.1 shapes_ok_bool l hl) p hp

/-- The order conditions produced by the symmetry breaking. -/
def Sorted (c : Colouring) : Prop :=
  (c s(0, 1)).val ≤ (c s(0, 2)).val ∧
    ∀ p ∈ quads, 3 * (c s(0, p.1)).val + (c s(1, p.1)).val ≤
      3 * (c s(0, p.2)).val + (c s(1, p.2)).val

theorem quads_facts : ∀ p ∈ quads, (2 : Fin 9) ≤ p.1 ∧ p.1 ≤ p.2 ∧ (0 : Fin 9) ≠ p.1 ∧
    (0 : Fin 9) ≠ p.2 ∧ (1 : Fin 9) ≠ p.1 ∧ (1 : Fin 9) ≠ p.2 := by decide

theorem upairs_facts : ∀ p ∈ upairs, p = (1, 2) ∨ p ∈ quads := by decide

/-- A sorted colouring without monochromatic triangles, pentagons and four-stars
does not exist: this is the kernel-checked case analysis. -/
theorem no_sorted (c : Colouring) (h3 : ¬ MonoTri c) (h5 : ¬ MonoPent c) (h4 : NoFourStar c)
    (hS : Sorted c) : False := by
  have hcol : ∀ a b : Fin 9, a ≠ b → c (edgeOf (eix a b)) = c s(a, b) :=
    fun a b h => by rw [edgeOf_eix a b h]
  rcases check_sound (fun i => c (edgeOf i)) cert 0 0 0 cert_ok
      ⟨by simp, by simp, by simp⟩ with ⟨e, K, hK, k, hk⟩ | hsb
  · obtain ⟨s, hp, rfl⟩ := List.mem_map.1 hK
    have hv := shapes_ok hp
    simp only at hk
    cases s with
    | tri a b d =>
      simp only [Shape.valid, decide_eq_true_eq, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
        not_false_eq_true] at hv
      obtain ⟨⟨hab, had⟩, hbd⟩ := hv
      have t1 := hk (eix a b) (by simp [Shape.mask, Nat.testBit_or, Nat.testBit_two_pow_self])
      have t2 := hk (eix b d) (by simp [Shape.mask, Nat.testBit_or, Nat.testBit_two_pow_self])
      have t3 := hk (eix a d) (by simp [Shape.mask, Nat.testBit_or, Nat.testBit_two_pow_self])
      rw [hcol a b hab] at t1; rw [hcol b d hbd] at t2; rw [hcol a d had] at t3
      exact tri_of h3 hab had hbd k t1 t2 t3
    | pent a b d e f =>
      have hnd : [a, b, d, e, f].Nodup := by simpa [Shape.valid] using hv
      have hv' := hnd
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true] at hv'
      obtain ⟨⟨hab, had, hae, haf⟩, ⟨hbd, hbe, hbf⟩, ⟨hde, hdf⟩, hef⟩ := hv'
      have t1 := hk (eix a b) (by simp [Shape.mask, Nat.testBit_or, Nat.testBit_two_pow_self])
      have t2 := hk (eix b d) (by simp [Shape.mask, Nat.testBit_or, Nat.testBit_two_pow_self])
      have t3 := hk (eix d e) (by simp [Shape.mask, Nat.testBit_or, Nat.testBit_two_pow_self])
      have t4 := hk (eix e f) (by simp [Shape.mask, Nat.testBit_or, Nat.testBit_two_pow_self])
      have t5 := hk (eix f a) (by simp [Shape.mask, Nat.testBit_or, Nat.testBit_two_pow_self])
      rw [hcol a b hab] at t1; rw [hcol b d hbd] at t2; rw [hcol d e hde] at t3
      rw [hcol e f hef] at t4; rw [hcol f a (Ne.symm haf)] at t5
      exact h5 ⟨a, b, d, e, f, hnd, t1.trans t2.symm, t2.trans t3.symm, t3.trans t4.symm,
        t4.trans t5.symm⟩
    | star v a b d e =>
      have hnd : [v, a, b, d, e].Nodup := by simpa [Shape.valid] using hv
      have hv' := hnd
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true] at hv'
      obtain ⟨⟨hva, hvb, hvd, hve⟩, -, -, -⟩ := hv'
      have t1 := hk (eix v a) (by simp [Shape.mask, Nat.testBit_or, Nat.testBit_two_pow_self])
      have t2 := hk (eix v b) (by simp [Shape.mask, Nat.testBit_or, Nat.testBit_two_pow_self])
      have t3 := hk (eix v d) (by simp [Shape.mask, Nat.testBit_or, Nat.testBit_two_pow_self])
      have t4 := hk (eix v e) (by simp [Shape.mask, Nat.testBit_or, Nat.testBit_two_pow_self])
      rw [hcol v a hva] at t1; rw [hcol v b hvb] at t2; rw [hcol v d hvd] at t3
      rw [hcol v e hve] at t4
      exact h4 v a b d e hnd ⟨t1.trans t2.symm, t2.trans t3.symm, t3.trans t4.symm⟩
  · have b1 := fun x : Fin 3 => x.isLt
    rcases hsb with ⟨p, hp, hlt⟩ | ⟨p, hp, hlt⟩
    · simp only at hlt
      rcases upairs_facts p hp with rfl | hq
      · rw [hcol 0 2 (by decide), hcol 0 1 (by decide)] at hlt
        have := hS.1
        omega
      · obtain ⟨-, -, n1, n2, -, -⟩ := quads_facts p hq
        rw [hcol 0 p.2 n2, hcol 0 p.1 n1] at hlt
        have := hS.2 p hq
        have := b1 (c s(1, p.1)); have := b1 (c s(1, p.2))
        omega
    · simp only at hlt
      obtain ⟨-, -, n1, n2, n3, n4⟩ := quads_facts p hp
      rw [hcol 0 p.2 n2, hcol 0 p.1 n1, hcol 1 p.2 n4, hcol 1 p.1 n3] at hlt
      have := hS.2 p hp
      omega

/-- Symmetry breaking: every colouring without monochromatic triangles and pentagons can be
relabelled into a sorted one. -/
theorem wlog_sorted (c : Colouring) (h3 : ¬ MonoTri c) (h5 : ¬ MonoPent c) :
    ∃ c' : Colouring, ¬ MonoTri c' ∧ ¬ MonoPent c' ∧ Sorted c' := by
  obtain ⟨σ1, h10, hm1⟩ := sort1 (fun x => (c s(0, x)).val)
  have hc1 : ∀ x y : Fin 9, x ≠ 0 → x ≤ y →
      (relabel σ1 c s(0, x)).val ≤ (relabel σ1 c s(0, y)).val := by
    intro x y hx hxy
    simp only [relabel_apply, h10]
    exact hm1 x y hx hxy
  obtain ⟨σ2, h20, h21, hm2⟩ :=
    sort2 (fun x => 3 * (relabel σ1 c s(0, x)).val + (relabel σ1 c s(1, x)).val)
  refine ⟨relabel σ2 (relabel σ1 c), relabel_tri (relabel_tri h3),
    relabel_pent (relabel_pent h5), ?_, ?_⟩
  · have e1 : (relabel σ2 (relabel σ1 c)) s(0, 1) = relabel σ1 c s(0, 1) := by
      rw [relabel_apply, h20, h21]
    have e2 : (relabel σ2 (relabel σ1 c)) s(0, 2) = relabel σ1 c s(0, σ2 2) := by
      rw [relabel_apply, h20]
    rw [e1, e2]
    apply hc1 1 (σ2 2) (by decide)
    have hne : σ2 2 ≠ 0 := by rw [← h20]; exact σ2.injective.ne (by decide)
    rcases Fin.eq_zero_or_eq_succ (σ2 2) with h | ⟨j, hj⟩
    · exact absurd h hne
    · rw [hj]; exact Fin.succ_pos j
  · intro p hp
    obtain ⟨q1, q2, -⟩ := quads_facts p hp
    have := hm2 p.1 p.2 q1 q2
    simp only [relabel_apply, h20, h21] at this ⊢
    exact this

/-- **Upper bound for `f(3)`.** Every 3-colouring of the edges of `K_9` contains a
monochromatic triangle or a monochromatic pentagon. -/
theorem mono_tri_or_pent (c : Colouring) : MonoTri c ∨ MonoPent c := by
  by_contra h
  rw [not_or] at h
  obtain ⟨c', h3, h5, hS⟩ := wlog_sorted c h.1 h.2
  exact no_sorted c' h3 h5 (noFourStar c' h3 h5) hS

/-- The adjacency table of a 3-colouring of `K_9` without monochromatic triangles
(the diagonal is irrelevant). -/
def lowerM : Fin 9 → Fin 9 → Fin 3 :=
  ![![0, 0, 0, 0, 0, 1, 1, 2, 2],
    ![0, 0, 1, 1, 2, 0, 0, 0, 0],
    ![0, 1, 0, 2, 1, 0, 0, 0, 0],
    ![0, 1, 2, 0, 1, 0, 0, 0, 0],
    ![0, 2, 1, 1, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 2, 1, 2],
    ![1, 0, 0, 0, 0, 2, 0, 2, 1],
    ![2, 0, 0, 0, 0, 1, 2, 0, 1],
    ![2, 0, 0, 0, 0, 2, 1, 1, 0]]

theorem lowerM_symm : ∀ a b, lowerM a b = lowerM b a := by decide

/-- A 3-colouring of `E(K_9)` without monochromatic triangles. -/
def lowerCol : Sym2 (Fin 9) → Fin 3 := Sym2.lift ⟨lowerM, lowerM_symm⟩

theorem lowerM_triangle_free : ∀ a b d : Fin 9, a ≠ b → b ≠ d → d ≠ a →
    ¬ (lowerM a b = lowerM b d ∧ lowerM b d = lowerM d a) := by decide

/-- **Lower bound for `f(3)`.** Some 3-colouring of the edges of `K_9` has no monochromatic
triangle. -/
theorem exists_no_monoTri : ∃ c : Colouring, ¬ MonoTri c := by
  refine ⟨lowerCol, ?_⟩
  rintro ⟨a, b, d, hab, had, hbd, e1, e2⟩
  simp only [lowerCol, Sym2.lift_mk] at e1 e2
  exact lowerM_triangle_free a b d hab hbd (Ne.symm had) ⟨e1, e2.trans (lowerM_symm a d)⟩

/-- **Erdős Problem 609, `n = 3`, on `Fin 9`.** Every 3-colouring of `E(K_9)` has a
monochromatic `C_3` or `C_5`, and some 3-colouring has no monochromatic `C_3`. -/
theorem f_three_fin9 :
    (∀ c : Colouring, MonoTri c ∨ MonoPent c) ∧ ∃ c : Colouring, ¬ MonoTri c :=
  ⟨mono_tri_or_pent, exists_no_monoTri⟩

end Erdos609F3

/-! ### Definitions copied verbatim from formal-conjectures

`SimpleGraph.cycleLengths` and `SimpleGraph.oddCycleLengths` are from
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean`. -/

namespace SimpleGraph

/-- `G.cycleLengths` is the set of lengths of the cycles in `G`. -/
def cycleLengths {α : Type*} (G : SimpleGraph α) : Set ℕ :=
  {m | ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ w.length = m}

/-- `G.oddCycleLengths` is the set of lengths of odd cycles in `G`. -/
def oddCycleLengths {α : Type*} (G : SimpleGraph α) : Set ℕ :=
  {m ∈ G.cycleLengths | Odd m}

end SimpleGraph

namespace Erdos609

/-! The next three definitions are copied verbatim from
`FormalConjectures/ErdosProblems/609.lean` in formal-conjectures. -/

/--
The monochromatic subgraph of color `i` under edge coloring `c : Sym2 V → Fin n`.
-/
def monochromaticGraph {V : Type*} {n : ℕ} (c : Sym2 V → Fin n) (i : Fin n) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v ↦ c s(u, v) = i)

/--
A coloring `c` has a monochromatic odd cycle of length at most `m`.
-/
def MonochromaticHasOddCycleLe (n : ℕ) (m : ℕ) (c : Sym2 (Fin (2 ^ n + 1)) → Fin n) : Prop :=
  ∃ (i : Fin n) (l : ℕ), l ∈ (monochromaticGraph c i).oddCycleLengths ∧ l ≤ m

/--
$f(n)$ is the minimal $m$ such that if the edges of $K_{2^n+1}$ are coloured with $n$ colours
then there must be a monochromatic odd cycle of length at most $m$.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (c : Sym2 (Fin (2 ^ n + 1)) → Fin n), MonochromaticHasOddCycleLe n m c}

/-! ### Bridge to the formal-conjectures statement -/

open SimpleGraph

/-- An edge of colour `i` is an edge of the colour-`i` graph. -/
theorem mono_adj {V : Type*} {n : ℕ} {c : Sym2 V → Fin n} {i : Fin n} {u v : V} (huv : u ≠ v)
    (h : c s(u, v) = i) : (monochromaticGraph c i).Adj u v := by
  rw [monochromaticGraph, fromRel_adj]
  exact ⟨huv, Or.inl h⟩

/-- Adjacency in the colour-`i` graph. -/
theorem mono_adj_iff {V : Type*} {n : ℕ} {c : Sym2 V → Fin n} {i : Fin n} {u v : V} :
    (monochromaticGraph c i).Adj u v ↔ u ≠ v ∧ c s(u, v) = i := by
  rw [monochromaticGraph, fromRel_adj, Sym2.eq_swap (a := v)]
  simp

/-- A triangle gives an odd cycle of length `3`. -/
theorem three_mem {V : Type*} {G : SimpleGraph V} {a b d : V} (h1 : G.Adj a b) (h2 : G.Adj b d)
    (h3 : G.Adj d a) (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) : 3 ∈ G.oddCycleLengths := by
  refine ⟨⟨a, Walk.cons h1 (Walk.cons h2 (Walk.cons h3 Walk.nil)), ?_, rfl⟩, by decide⟩
  rw [Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · simp [Walk.cons_isPath_iff, hbd, Ne.symm had, Ne.symm hab]
  · simp [Walk.edges, hab, hbd, had]

/-- A pentagon gives an odd cycle of length `5`. -/
theorem five_mem {V : Type*} {G : SimpleGraph V} {a b d e f : V} (h1 : G.Adj a b)
    (h2 : G.Adj b d) (h3 : G.Adj d e) (h4 : G.Adj e f) (h5 : G.Adj f a)
    (hnd : [a, b, d, e, f].Nodup) : 5 ∈ G.oddCycleLengths := by
  refine ⟨⟨a, Walk.cons h1 (Walk.cons h2 (Walk.cons h3 (Walk.cons h4 (Walk.cons h5 Walk.nil)))),
    ?_, rfl⟩, by decide⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨hab, had, hae, haf⟩, ⟨hbd, hbe, hbf⟩, ⟨hde, hdf⟩, hef⟩ := hnd
  rw [Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · simp [Walk.cons_isPath_iff, hbd, hbe, hbf, hde, hdf, hef, Ne.symm hab, Ne.symm had,
      Ne.symm hae, Ne.symm haf]
  · simp [Walk.edges, hab, hbd, had, hae, haf, hbe, hbf]

/-- A closed walk of length `3` is a triangle. -/
theorem len3 {V : Type*} {G : SimpleGraph V} {a : V} (w : G.Walk a a) (hw : w.length = 3) :
    ∃ b d, G.Adj a b ∧ G.Adj b d ∧ G.Adj d a := by
  cases w with
  | nil => simp at hw
  | cons h1 w1 =>
    cases w1 with
    | nil => simp at hw
    | cons h2 w2 =>
      cases w2 with
      | nil => simp at hw
      | cons h3 w3 =>
        cases w3 with
        | nil => exact ⟨_, _, h1, h2, h3⟩
        | cons _ _ => simp at hw

/-- `5` belongs to the set whose infimum is `f 3`. -/
theorem five_mem_set :
    5 ∈ {m : ℕ | ∀ (c : Sym2 (Fin (2 ^ 3 + 1)) → Fin 3), MonochromaticHasOddCycleLe 3 m c} := by
  intro c
  rcases Erdos609F3.mono_tri_or_pent c with ⟨a, b, d, hab, had, hbd, e1, e2⟩ |
    ⟨a, b, d, e, f, hnd, e1, e2, e3, e4⟩
  · refine ⟨c s(a, b), 3, three_mem (mono_adj hab rfl) (mono_adj hbd e1.symm)
      (mono_adj (Ne.symm had) ?_) hab hbd had, le_of_lt (by norm_num)⟩
    rw [Sym2.eq_swap]; exact (e1.trans e2).symm
  · have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true] at hnd'
    obtain ⟨⟨hab, had, hae, haf⟩, ⟨hbd, hbe, hbf⟩, ⟨hde, hdf⟩, hef⟩ := hnd'
    exact ⟨c s(a, b), 5, five_mem (mono_adj hab rfl) (mono_adj hbd e1.symm)
      (mono_adj hde (e1.trans e2).symm) (mono_adj hef (e1.trans (e2.trans e3)).symm)
      (mono_adj (Ne.symm haf) (e1.trans (e2.trans (e3.trans e4))).symm) hnd, le_rfl⟩

/-- No `m < 5` belongs to the set whose infimum is `f 3`. -/
theorem not_mem_set_of_lt {m : ℕ} (hm : m < 5) :
    m ∉ {m : ℕ | ∀ (c : Sym2 (Fin (2 ^ 3 + 1)) → Fin 3), MonochromaticHasOddCycleLe 3 m c} := by
  intro hmem
  obtain ⟨i, l, ⟨⟨a, w, hw, rfl⟩, hodd⟩, hle⟩ := hmem Erdos609F3.lowerCol
  have h3 : 3 ≤ w.length := hw.three_le_length
  have hl3 : w.length = 3 := by obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨b, d, h1, h2, h3'⟩ := len3 w hl3
  rw [mono_adj_iff] at h1 h2 h3'
  refine Erdos609F3.lowerM_triangle_free a b d h1.1 h2.1 h3'.1 ⟨?_, ?_⟩
  · have := h1.2.trans h2.2.symm; simpa [Erdos609F3.lowerCol] using this
  · have := h2.2.trans h3'.2.symm; simpa [Erdos609F3.lowerCol] using this

/-- **Erdős Problem 609, the case `n = 3`:** `f(3) = 5`, with `f` as in formal-conjectures. -/
theorem f_three : f 3 = 5 := by
  apply le_antisymm (Nat.sInf_le five_mem_set)
  apply le_csInf ⟨5, five_mem_set⟩
  intro m hm
  by_contra hlt
  exact not_mem_set_of_lt (not_le.1 hlt) hm

end Erdos609

#print axioms Erdos609F3.mono_tri_or_pent
#print axioms Erdos609F3.exists_no_monoTri
#print axioms Erdos609F3.f_three_fin9
#print axioms Erdos609.f_three

end

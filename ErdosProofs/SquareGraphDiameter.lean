module

public import Mathlib

/-!
# The "`uv + 1` is a square" graph has diameter 3

Let `G` be the simple graph on the positive integers in which `u ~ v` iff `u ≠ v` and
`u * v + 1` is a perfect square.  Konrad Burnik asked for the diameter of `G`
(MathOverflow question 509929, "Diameter of the diophantine graph on positive integers:
`u ∼ v ⟺ uv + 1` is a perfect square", April 2026), conjecturing `diam G ≤ 6`.

The answer by Jack Edward Tisdell (paraphrasing and checking a solution found by ChatGPT)
shows that the diameter is exactly `3`:

* If `u * v` is not a square, take a nontrivial Pell solution `p² - u v q² = 1` with `q > 0`
  and put `w = (u + v) q² + 2 p q`.  Then `u w + 1 = (u q + p)²` and `v w + 1 = (v q + p)²`,
  so `w` is a common neighbour and `d(u, v) ≤ 2`.
* If `u * v` is a square, then `(u + 2) * v` is not a square, and `u ~ u + 2` because
  `u (u + 2) + 1 = (u + 1)²`; hence `d(u, v) ≤ 3`.
* `d(1, 4) = 3`: `1 * 4 + 1 = 5` is not a square, and a common neighbour `w` would give
  `w + 1 = a²`, `4 w + 1 = b²`, so `(2a)² - b² = 3`, forcing `a = 1`, `w = 0`.

For the second bullet we use a slightly different argument than the MO answer: if both
`u v` and `(u + 2) v` were squares then so would be `u (u + 2) v²`, hence `u (u + 2)`,
but `u² < u (u + 2) < (u + 1)²`.

## Main results

* `SqGraph.connected : SqGraph.Connected`
* `SqGraph.dist_le_three : SqGraph.dist u v ≤ 3`
* `SqGraph.dist_one_four : SqGraph.dist 1 4 = 3`
* `SqGraph.ediam_eq : SqGraph.ediam = 3`
* `SqGraph.diam_eq : SqGraph.diam = 3`
-/

@[expose] public section

namespace SquareGraphDiameter

open SimpleGraph

/-- The graph on positive integers with `u ~ v ↔ u ≠ v ∧ u * v + 1` is a perfect square. -/
def SqGraph : SimpleGraph ℕ+ where
  Adj u v := u ≠ v ∧ IsSquare ((u : ℕ) * v + 1)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Nat.mul_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma sqGraph_adj {u v : ℕ+} : SqGraph.Adj u v ↔ u ≠ v ∧ IsSquare ((u : ℕ) * v + 1) :=
  Iff.rfl

/-! ### Arithmetic lemmas -/

/-- If `a * b²` is a square and `b > 0`, then `a` is a square. -/
lemma isSquare_of_isSquare_mul_sq {a b : ℕ} (hb : 0 < b) (h : IsSquare (a * b ^ 2)) :
    IsSquare a := by
  obtain ⟨c, hc⟩ := h
  have hdvd : b ^ 2 ∣ c ^ 2 := ⟨a, by rw [sq c, ← hc]; ring⟩
  obtain ⟨k, rfl⟩ := (Nat.pow_dvd_pow_iff two_ne_zero).mp hdvd
  refine ⟨k, ?_⟩
  have hb2 : 0 < b ^ 2 := by positivity
  have : a * b ^ 2 = (k * k) * b ^ 2 := by rw [hc]; ring
  exact Nat.eq_of_mul_eq_mul_right hb2 this

/-- `u (u + 2)` is never a square for `u > 0`: it lies strictly between `u²` and `(u+1)²`. -/
lemma not_isSquare_mul_add_two {u : ℕ} (hu : 0 < u) : ¬ IsSquare (u * (u + 2)) := by
  rintro ⟨k, hk⟩
  rcases le_or_gt k u with h | h
  · have : k * k ≤ u * u := Nat.mul_le_mul h h
    nlinarith
  · have : (u + 1) * (u + 1) ≤ k * k := Nat.mul_le_mul h h
    nlinarith

/-- If `u v` is a square then `(u + 2) v` is not (for `u, v > 0`). -/
lemma not_isSquare_add_two_mul {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (h : IsSquare (u * v)) :
    ¬ IsSquare ((u + 2) * v) := by
  intro h'
  apply not_isSquare_mul_add_two hu
  apply isSquare_of_isSquare_mul_sq hv
  have : u * (u + 2) * v ^ 2 = (u * v) * ((u + 2) * v) := by ring
  rw [this]
  exact h.mul h'

/-! ### Adjacency facts -/

/-- `u ~ u + 2`, since `u (u + 2) + 1 = (u + 1)²`. -/
lemma adj_add_two (u : ℕ+) : SqGraph.Adj u (u + 2) := by
  refine ⟨fun h => ?_, ⟨(u : ℕ) + 1, ?_⟩⟩
  · have := congrArg (fun x : ℕ+ => (x : ℕ)) h
    simp at this
  · push_cast; ring

/-- If `u v` is not a square, then `u` and `v` have a common neighbour (Pell construction). -/
lemma exists_common_neighbor {u v : ℕ+} (h : ¬ IsSquare ((u : ℕ) * v)) :
    ∃ w : ℕ+, SqGraph.Adj u w ∧ SqGraph.Adj w v := by
  have hd0 : (0 : ℤ) < (u : ℕ) * (v : ℕ) := by positivity
  have hd : ¬ IsSquare (((u : ℕ) : ℤ) * ((v : ℕ) : ℤ)) := by
    rw [← Nat.cast_mul, Int.isSquare_natCast_iff]; exact h
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare hd0 hd
  set p := x.natAbs
  set q := y.natAbs
  have hq : 0 < q := Int.natAbs_pos.mpr hy
  have hpell : p ^ 2 = (u : ℕ) * v * q ^ 2 + 1 := by
    have h1 : ((p : ℕ) : ℤ) ^ 2 = x ^ 2 := by simp [p]
    have h2 : ((q : ℕ) : ℤ) ^ 2 = y ^ 2 := by simp [q]
    have : ((p ^ 2 : ℕ) : ℤ) = (((u : ℕ) * v * q ^ 2 + 1 : ℕ) : ℤ) := by
      push_cast; rw [h1, h2]; linarith
    exact_mod_cast this
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · rw [h0] at hpell; simp at hpell
    · exact h0
  set w : ℕ := ((u : ℕ) + v) * q ^ 2 + 2 * p * q with hw
  have hwpos : 0 < w := by positivity
  have hu_lt : (u : ℕ) < w := by
    have : (u : ℕ) ≤ ((u : ℕ) + v) * q ^ 2 := by
      calc (u : ℕ) ≤ (u : ℕ) + v := Nat.le_add_right _ _
        _ = ((u : ℕ) + v) * 1 := (mul_one _).symm
        _ ≤ ((u : ℕ) + v) * q ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hq)
    have : 0 < 2 * p * q := by positivity
    omega
  have hv_lt : (v : ℕ) < w := by
    have : (v : ℕ) ≤ ((u : ℕ) + v) * q ^ 2 := by
      calc (v : ℕ) ≤ (u : ℕ) + v := Nat.le_add_left _ _
        _ = ((u : ℕ) + v) * 1 := (mul_one _).symm
        _ ≤ ((u : ℕ) + v) * q ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hq)
    have : 0 < 2 * p * q := by positivity
    omega
  refine ⟨⟨w, hwpos⟩, ⟨?_, ⟨(u : ℕ) * q + p, ?_⟩⟩, ⟨?_, ⟨(v : ℕ) * q + p, ?_⟩⟩⟩
  · intro he; rw [he] at hu_lt; exact lt_irrefl _ hu_lt
  · simp only [PNat.mk_coe, hw]
    have : (p : ℕ) * p = (u : ℕ) * v * q ^ 2 + 1 := by rw [← sq]; exact hpell
    nlinarith [this]
  · intro he; rw [← he] at hv_lt; exact lt_irrefl _ hv_lt
  · simp only [PNat.mk_coe, hw]
    have : (p : ℕ) * p = (u : ℕ) * v * q ^ 2 + 1 := by rw [← sq]; exact hpell
    nlinarith [this]

/-! ### Upper bound: every pair is joined by a walk of length at most 3 -/

lemma exists_walk_length_le_three (u v : ℕ+) : ∃ p : SqGraph.Walk u v, p.length ≤ 3 := by
  by_cases h : IsSquare ((u : ℕ) * v)
  · -- go `u → u + 2` first; then `(u + 2) v` is not a square
    have h' : ¬ IsSquare (((u + 2 : ℕ+) : ℕ) * v) := by
      rw [PNat.add_coe]
      exact not_isSquare_add_two_mul u.pos v.pos h
    obtain ⟨w, h1, h2⟩ := exists_common_neighbor h'
    exact ⟨.cons (adj_add_two u) (.cons h1 (.cons h2 .nil)), by simp⟩
  · obtain ⟨w, h1, h2⟩ := exists_common_neighbor h
    exact ⟨.cons h1 (.cons h2 .nil), by simp⟩

theorem connected : SqGraph.Connected := by
  rw [connected_iff_exists_forall_reachable]
  exact ⟨1, fun v => (exists_walk_length_le_three 1 v).elim fun p _ => p.reachable⟩

theorem dist_le_three (u v : ℕ+) : SqGraph.dist u v ≤ 3 := by
  obtain ⟨p, hp⟩ := exists_walk_length_le_three u v
  exact (dist_le p).trans hp

theorem edist_le_three (u v : ℕ+) : SqGraph.edist u v ≤ 3 := by
  obtain ⟨p, hp⟩ := exists_walk_length_le_three u v
  exact (edist_le p).trans (by exact_mod_cast hp)

/-! ### Lower bound: `d(1, 4) = 3` -/

lemma not_adj_one_four : ¬ SqGraph.Adj 1 4 := by
  rintro ⟨-, k, hk⟩
  have hk' : k * k = 5 := by simpa using hk.symm
  have : k ≤ 2 := by nlinarith
  interval_cases k <;> omega

lemma no_common_neighbor_one_four (w : ℕ+) : ¬ (SqGraph.Adj 1 w ∧ SqGraph.Adj w 4) := by
  rintro ⟨⟨-, a, ha⟩, ⟨-, b, hb⟩⟩
  have hw := w.pos
  simp only [one_mul, PNat.val_ofNat] at ha hb
  -- `(2a)² = b² + 3`, so `b < 2a`, hence `b + 1 ≤ 2a`, forcing `a ≤ 1` and `w = 0`.
  have key : (2 * a) * (2 * a) = b * b + 3 := by nlinarith
  have hb2a : b < 2 * a := by nlinarith
  have : (b + 1) * (b + 1) ≤ (2 * a) * (2 * a) := Nat.mul_le_mul hb2a hb2a
  have ha1 : a ≤ 1 := by nlinarith
  interval_cases a <;> omega

theorem two_lt_edist_one_four : 2 < SqGraph.edist 1 4 := by
  rw [two_lt_edist_iff]
  refine ⟨by decide, not_adj_one_four, ?_⟩
  ext w
  simp only [mem_commonNeighbors, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h4⟩
  exact no_common_neighbor_one_four w ⟨h1, h4.symm⟩

theorem edist_one_four : SqGraph.edist 1 4 = 3 :=
  le_antisymm (edist_le_three 1 4) (Order.add_one_le_of_lt two_lt_edist_one_four)

theorem dist_one_four : SqGraph.dist 1 4 = 3 := by
  have h := (connected.preconnected 1 4).coe_dist_eq_edist
  rw [edist_one_four] at h
  exact_mod_cast h

/-! ### The diameter -/

theorem ediam_eq : SqGraph.ediam = 3 :=
  le_antisymm (ediam_le_of_edist_le edist_le_three) (edist_one_four ▸ edist_le_ediam)

theorem diam_eq : SqGraph.diam = 3 := by
  rw [diam, ediam_eq]; rfl

end SquareGraphDiameter

#print axioms SquareGraphDiameter.connected
#print axioms SquareGraphDiameter.dist_le_three
#print axioms SquareGraphDiameter.dist_one_four
#print axioms SquareGraphDiameter.ediam_eq
#print axioms SquareGraphDiameter.diam_eq

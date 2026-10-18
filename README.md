# Lean formalizations of recently settled problems

Kernel-checked Lean 4 proofs (Lean v4.35.0, Mathlib v4.35.0) of recently answered questions from
MathOverflow, the Kourovka Notebook and the Erdős problem list. Every theorem is
`sorry`-free and depends only on `propext`, `Classical.choice`, `Quot.sound`
(no `native_decide`). Each file's docstring cites the original question and the
authors of the informal solution being formalized. All `.lean` files use the Lean module system.

Proofs were produced with AI assistance (Claude Code) and checked by the Lean kernel.

| File | Source | Result |
|---|---|---|
| `ErdosProofs/MO513215.lean` | MathOverflow 513215 | a_n = n(n+3)/2 has S(0)=11/9, S(1)=1 |
| `ErdosProofs/Kourovka17_32.lean` | Kourovka 17.32 (Ionin–Semidetnov 2026) | Cayley–Hamilton analogue for F_n fails (n=2 witness) |
| `ErdosProofs/SquareGraphDiameter.lean` | MathOverflow 509929 | graph u~v iff uv+1 square has diameter 3 |
| `ErdosProofs/FerrisWheel.lean` | MathOverflow 515611 | 907200 is a Ferris wheel number (210 divisors at 210th roots of unity sum to 0) |
| `ErdosProofs/LcmHighlyAbundant.lean` | MathOverflow 501066 (Tao) | lcm(1..200000) is not highly abundant |
| `ErdosProofs/Kourovka19_35.lean` | Kourovka 19.35 (Bergman / McCulloch 2026) | A4 has no subset factorization of sizes 2,3,2 |
| [`Challenge.lean`](Challenge.lean) / [`Solution.lean`](Solution.lean) | Erdős Problem 216, k ≥ 7 (Horton 1983) | for every N a set of N points in general position with no empty convex k-gon, k ≥ 7 |
| `ErdosProofs/Erdos609.lean` | Erdős Problem 609, small case (Cai 2026) | f(3) = 5: every 3-colouring of K_9 has a monochromatic C_3 or C_5, and some has no monochromatic C_3 |

Build: `lake exe cache get && lake build`.

## Horton's theorem (Palomar entry)

The Horton development is laid out as a [Palomar](https://palomar-registry.org) /
Comparator Challenge–Solution pair:

* [`Challenge.lean`](Challenge.lean) imports only Mathlib and states, with `sorry`, the compared
  theorems together with every definition they use (`InGeneralPosition`, `ConvexPosition`,
  `HasEmptyConvexKGon`, and the formal-conjectures PR #6775 copies `SetTriplewise'`,
  `NonTrilinear'`, `ConvexIndep'`, `HasEmptyConvexNGon'`, `cardSet'`).
* [`Solution.lean`](Solution.lean) repeats those definitions verbatim and contains the full proof
  (Horton's construction, the no-open-4-cup/4-cap lemma and the transfer to Mathlib geometry).
  `ErdosProofs/Horton.lean` re-exports it, so `import ErdosProofs` still provides the whole
  `Horton` namespace.
* [`comparator.json`](comparator.json) compares
  `Horton.horton_euclidean` ([Solution.lean#L872](Solution.lean#L872)),
  `Horton.erdos_216_ge_seven` ([Solution.lean#L767](Solution.lean#L767)),
  `Horton.cardSet'_eq_empty` ([Solution.lean#L932](Solution.lean#L932)) and
  `Horton.erdos_216'` ([Solution.lean#L946](Solution.lean#L946)), permitting only
  `propext`, `Quot.sound`, `Classical.choice`.
* [`formalization.yaml`](formalization.yaml) holds the metadata (sources, automation, review,
  fidelity notes); the repository is licensed under [Apache-2.0](LICENSE).

Check locally (Lean ≥ 4.35, needs `bwrap`):

```sh
lake exe cache get
lake comparator --config comparator.json            # Lean kernel
lake comparator --config comparator.json --paranoid # also lean4lean, nanoda, con-leche, con-ron
```

`lake build Challenge` reports the four intentional `sorry`s of the statement file; the default
`lake build` (library + Solution) is warning-free. The Palomar mechanical preflight runs on every
push to `main` via [`.github/workflows/palomar-preflight.yml`](.github/workflows/palomar-preflight.yml).

Note: the Horton code previously lived in `ErdosProofs/Horton.lean` (e.g. `cardSet'_eq_empty` at
`#L918`, `erdos_216'` at `#L932` of commit `76d38ca`); links to those anchors should now point to
`Solution.lean` at the lines above.

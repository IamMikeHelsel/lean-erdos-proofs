# Lean formalizations of recently settled problems

Kernel-checked Lean 4 proofs (Mathlib v4.33.1) of recently answered questions from
MathOverflow, the Kourovka Notebook and the Erdős problem list. Every theorem is
`sorry`-free and depends only on `propext`, `Classical.choice`, `Quot.sound`
(no `native_decide`). Each file's docstring cites the original question and the
authors of the informal solution being formalized.

Proofs were produced with AI assistance (Claude Code) and checked by the Lean kernel.

| File | Source | Result |
|---|---|---|
| `ErdosProofs/MO513215.lean` | MathOverflow 513215 | a_n = n(n+3)/2 has S(0)=11/9, S(1)=1 |
| `ErdosProofs/Kourovka17_32.lean` | Kourovka 17.32 (Ionin–Semidetnov 2026) | Cayley–Hamilton analogue for F_n fails (n=2 witness) |
| `ErdosProofs/SquareGraphDiameter.lean` | MathOverflow 509929 | graph u~v iff uv+1 square has diameter 3 |
| `ErdosProofs/FerrisWheel.lean` | MathOverflow 515611 | 907200 is a Ferris wheel number (210 divisors at 210th roots of unity sum to 0) |
| `ErdosProofs/LcmHighlyAbundant.lean` | MathOverflow 501066 (Tao) | lcm(1..200000) is not highly abundant |

Build: `lake exe cache get && lake build`.

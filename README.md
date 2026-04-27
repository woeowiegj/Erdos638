# Erdős Problem 638 — Lean formalisation

Companion Lean 4 / Mathlib formalisation for the note
*A counterexample to a hereditary triangle Ramsey compactness problem*
(B. Saturnino).

## Status

- **Verified in Lean:** the compactness / diagonal reduction —
  minimal-core existence, the de Bruijn–Erdős step, the
  age ⊆ S ⇒ finite-colour obstruction argument, and the assembly into
  the ordinary and induced hereditary counterexamples.
- **Assumed (`sorry`):** the finite avoidance principle
  (`avoidance_principle`) and the recursive block-sequence construction
  (`exists_block_sequence`). These are proved in the written note from
  the Nešetřil–Rödl sparse triangle-copy Ramsey theorem, Berge-cycle
  theory, and the resulting recursive construction; they are not
  formalised here.

Thus this project mechanically certifies the reduction from those two
inputs to the hereditary counterexamples. It is not a complete formalisation
of the written proof.

## Files

- `RequestProject/Defs.lean` — definitions
- `RequestProject/Construction.lean` — construction and main theorem
- `RequestProject/Main.lean` — top-level imports

## Acknowledgement

Initial Lean draft produced with [Aristotle](https://aristotle.harmonic.fun)
(Harmonic). Remaining `sorry`s and the framing above are my responsibility.

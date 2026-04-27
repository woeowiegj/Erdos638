import RequestProject.Defs
import RequestProject.Construction

/-!
# A counterexample to a hereditary triangle Ramsey compactness problem

This project formalizes the main theorem from:

> B. Saturnino, "A counterexample to a hereditary triangle Ramsey
> compactness problem"

## Main result

There exist hereditary classes of finite graphs (under both ordinary and induced
subgraphs) that contain finite n-colour triangle-Ramsey graphs for every positive
integer n, but for which no graph G with age contained in the class satisfies
G → (K₃)²_κ for any infinite cardinal κ.

## Files

- `Defs.lean`: Core definitions (triangles, Ramsey arrow, bundled finite graphs,
  subgraph relations, ages, hereditary classes, minimal 2-Ramsey cores).

- `Construction.lean`: The block sequence construction, definition of the classes
  S_ord and S_ind, and proofs of the main theorem.

## Sorry'd inputs

The only external input used is the Nešetřil–Rödl sparse triangle-copy Ramsey
theorem, which is encoded via two sorry'd lemmas:

1. `avoidance_principle`: the finite avoidance principle (Proposition 8 of the paper),
   which combines the Nešetřil–Rödl theorem with Berge cycle theory.

2. `exists_block_sequence`: existence of the block sequence with the required
   Ramsey and core-uniqueness properties (constructed using the avoidance principle).

All other lemmas and theorems are fully proved.
-/

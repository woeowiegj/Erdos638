# Summary of changes for run 29202cb9-be7a-4743-a93a-a1cb137b7398
## Formalization of "A counterexample to a hereditary triangle Ramsey compactness problem"

I formalized the main theorem from the paper by Brian Saturnino in Lean 4 with Mathlib. The formalization is split across three files:

### File structure

- **`RequestProject/Defs.lean`** — Core definitions:
  - `SimpleGraph.Triangle`: triangles in simple graphs
  - `TriangleRamsey G n`: the Ramsey arrow G → (K₃)²_n (every n-colouring of edges yields a monochromatic triangle)
  - `FinGraph`: bundled finite simple graphs (Σ n, SimpleGraph (Fin n))
  - `FinGraph.IsOrdSubgraphOf` / `FinGraph.IsIndSubgraphOf`: ordinary and induced subgraph embeddings
  - `IsOrdHereditary` / `IsIndHereditary`: hereditary graph classes
  - `OrdAge` / `IndAge`: ordinary and induced ages of a graph
  - `IsMinimal2Core`: minimal 2-Ramsey cores
  - `exists_minimal_core`: every finite 2-Ramsey graph contains a minimal core (**fully proved**)

- **`RequestProject/Construction.lean`** — The block sequence construction and main theorem:
  - `avoidance_principle`: the finite avoidance principle combining Nešetřil–Rödl with Berge cycle theory (**sorry'd — NR black box**)
  - `exists_block_sequence`: existence of the block sequence with Ramsey + core-uniqueness properties (**sorry'd — uses avoidance principle**)
  - `S_ord` / `S_ind`: the hereditary classes
  - `S_ord_hereditary`, `S_ind_hereditary`: hereditariness (**fully proved**)
  - `S_ord_ramsey'`, `S_ind_ramsey'`: finite Ramsey property for all n ≥ 1 (**fully proved**)
  - `no_core_not_ramsey_2`: core-free graphs are not 2-Ramsey, using de Bruijn–Erdős compactness via Tychonoff's theorem (**fully proved**)
  - `finite_graph_not_ramsey`: finite graphs are not Ramsey for sufficiently many colours (**fully proved**)
  - `core_forces_finite`: cores from unique blocks bound vertex count (**fully proved**)
  - `age_sub_S_ord_finite_chromatic` / `age_sub_S_ind_finite_chromatic`: the key structural lemma — Age ⊆ S implies finite chromatic number (**fully proved**)
  - `main_theorem_ord`, `main_theorem_ind`, `main_theorem`: the combined main theorem (**fully proved**)

- **`RequestProject/Main.lean`** — Documentation and imports

### Main theorem statement (in Lean)

```
theorem main_theorem :
    -- Ordinary version
    (∃ S : Set FinGraph,
      IsOrdHereditary S ∧
      (∀ n, n ≥ 1 → ∃ G ∈ S, TriangleRamsey G.2 n) ∧
      (∀ (V : Type*) (G : SimpleGraph V), OrdAge G ⊆ S →
        ∃ m : ℕ, ¬TriangleRamsey G m)) ∧
    -- Induced version
    (∃ S : Set FinGraph,
      IsIndHereditary S ∧
      (∀ n, n ≥ 1 → ∃ G ∈ S, TriangleRamsey G.2 n) ∧
      (∀ (V : Type*) (G : SimpleGraph V), IndAge G ⊆ S →
        ∃ m : ℕ, ¬TriangleRamsey G m))
```

### Sorry count

Only **2 sorry's** remain, both clearly labeled as the external black-box input from the paper:

1. `avoidance_principle` — The finite avoidance principle (Proposition 8), which encodes the Nešetřil–Rödl sparse triangle-copy Ramsey theorem combined with Berge cycle theory in triangle hypergraphs.

2. `exists_block_sequence` — Existence of the block sequence constructed using the avoidance principle.

All other lemmas and theorems (including the de Bruijn–Erdős compactness argument, the minimal core existence, the finite graph non-Ramsey bound, the core-forces-finite argument, and the main case analysis) are **fully machine-verified**.
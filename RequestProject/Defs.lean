import Mathlib

/-!
# Definitions for the hereditary triangle Ramsey counterexample

This file contains the core definitions used in the formalization of the main theorem:
the Ramsey arrow for triangles, bundled finite graphs, subgraph relations, ages,
hereditary classes, and minimal 2-Ramsey cores.
-/

noncomputable section
open scoped Classical

/-! ## Triangles and the Ramsey arrow -/

/-- A triangle in a simple graph: three mutually adjacent vertices. -/
structure SimpleGraph.Triangle {V : Type*} (G : SimpleGraph V) where
  (a b c : V)
  adj_ab : G.Adj a b
  adj_bc : G.Adj b c
  adj_ac : G.Adj a c

/-- `TriangleRamsey G n` is the Ramsey arrow `G → (K₃)²_n`:
every `n`-colouring of pairs of vertices contains a monochromatic triangle.
For `n = 0` this is vacuously true when `V` is nonempty (no `Fin 0`-valued
function exists on a nonempty domain). -/
def TriangleRamsey {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ c : Sym2 V → Fin n,
    ∃ t : G.Triangle,
      c s(t.a, t.b) = c s(t.b, t.c) ∧ c s(t.b, t.c) = c s(t.a, t.c)

/-! ## Bundled finite graphs -/

/-- A bundled finite simple graph: a natural number `n` together with a
`SimpleGraph (Fin n)`. -/
def FinGraph := Σ (n : ℕ), SimpleGraph (Fin n)

instance : Nonempty FinGraph := ⟨⟨0, ⊥⟩⟩

/-- `H` embeds as an ordinary (non-induced) subgraph of `G`:
there exists an injective map preserving adjacency. -/
def FinGraph.IsOrdSubgraphOf (H G : FinGraph) : Prop :=
  ∃ f : Fin H.1 → Fin G.1, Function.Injective f ∧
    ∀ u v, H.2.Adj u v → G.2.Adj (f u) (f v)

/-- `H` embeds as an induced subgraph of `G`:
there exists an injective map preserving and reflecting adjacency. -/
def FinGraph.IsIndSubgraphOf (H G : FinGraph) : Prop :=
  ∃ f : Fin H.1 → Fin G.1, Function.Injective f ∧
    ∀ u v, H.2.Adj u v ↔ G.2.Adj (f u) (f v)

/-- Reflexivity of ordinary subgraph relation. -/
lemma FinGraph.IsOrdSubgraphOf.refl (G : FinGraph) : G.IsOrdSubgraphOf G :=
  ⟨id, Function.injective_id, fun _ _ h => h⟩

/-- Transitivity of ordinary subgraph relation. -/
lemma FinGraph.IsOrdSubgraphOf.trans {A B C : FinGraph}
    (h1 : A.IsOrdSubgraphOf B) (h2 : B.IsOrdSubgraphOf C) :
    A.IsOrdSubgraphOf C := by
  obtain ⟨f, hf_inj, hf_adj⟩ := h1
  obtain ⟨g, hg_inj, hg_adj⟩ := h2
  exact ⟨g ∘ f, hg_inj.comp hf_inj, fun u v h => hg_adj _ _ (hf_adj u v h)⟩

/-- Transitivity of induced subgraph relation. -/
lemma FinGraph.IsIndSubgraphOf.trans {A B C : FinGraph}
    (h1 : A.IsIndSubgraphOf B) (h2 : B.IsIndSubgraphOf C) :
    A.IsIndSubgraphOf C := by
  obtain ⟨f, hf_inj, hf_adj⟩ := h1
  obtain ⟨g, hg_inj, hg_adj⟩ := h2
  exact ⟨g ∘ f, hg_inj.comp hf_inj, fun u v => (hf_adj u v).trans (hg_adj _ _)⟩

/-- An induced subgraph is in particular an ordinary subgraph. -/
lemma FinGraph.IsIndSubgraphOf.toOrd {H G : FinGraph}
    (h : H.IsIndSubgraphOf G) : H.IsOrdSubgraphOf G := by
  obtain ⟨f, hf_inj, hf_adj⟩ := h
  exact ⟨f, hf_inj, fun u v h' => (hf_adj u v).mp h'⟩

/-! ## Hereditary classes and ages -/

/-- A graph class is hereditary under ordinary subgraphs. -/
def IsOrdHereditary (S : Set FinGraph) : Prop :=
  ∀ G ∈ S, ∀ H : FinGraph, H.IsOrdSubgraphOf G → H ∈ S

/-- A graph class is hereditary under induced subgraphs. -/
def IsIndHereditary (S : Set FinGraph) : Prop :=
  ∀ G ∈ S, ∀ H : FinGraph, H.IsIndSubgraphOf G → H ∈ S

/-- The ordinary age of a graph `G`: the set of all bundled finite graphs
that embed as ordinary subgraphs of `G`. -/
def OrdAge {V : Type*} (G : SimpleGraph V) : Set FinGraph :=
  { H | ∃ f : Fin H.1 → V, Function.Injective f ∧
    ∀ u v, H.2.Adj u v → G.Adj (f u) (f v) }

/-- The induced age of a graph `G`. -/
def IndAge {V : Type*} (G : SimpleGraph V) : Set FinGraph :=
  { H | ∃ f : Fin H.1 → V, Function.Injective f ∧
    ∀ u v, H.2.Adj u v ↔ G.Adj (f u) (f v) }

/-! ## Minimal 2-Ramsey cores -/

/-- `M` is a minimal 2-Ramsey core: `M → (K₃)²_2` and every subgraph of `M`
that also satisfies this Ramsey property must embed `M` back
(i.e., no strictly smaller subgraph is Ramsey). -/
def IsMinimal2Core (M : FinGraph) : Prop :=
  TriangleRamsey M.2 2 ∧
  ∀ H : FinGraph, H.IsOrdSubgraphOf M → TriangleRamsey H.2 2 →
    M.IsOrdSubgraphOf H

/-
Every finite graph that is 2-Ramsey for triangles contains a minimal
2-Ramsey core as an ordinary subgraph. This follows from finiteness:
take a minimal element in the finite poset of subgraphs.
-/
lemma exists_minimal_core {G : FinGraph} (hG : TriangleRamsey G.2 2) :
    ∃ M : FinGraph, IsMinimal2Core M ∧ M.IsOrdSubgraphOf G := by
  set S := {H : FinGraph | H.IsOrdSubgraphOf G ∧ TriangleRamsey H.snd 2} with hS_def;
  have hS_finite : S.Finite := by
    have : ∀ H ∈ S, H.1 ≤ G.1 := by
      rintro H ⟨ ⟨ f, hf₁, hf₂ ⟩, hH ⟩;
      simpa using Fintype.card_le_of_injective f hf₁
    -- Since $H.1 \leq G.1$ for all $H \in S$, the set $S$ is finite because there are only finitely many possible values for $H.1$.
    have h_finite_H1 : Set.Finite {n : ℕ | ∃ H ∈ S, H.1 = n} := by
      exact Set.finite_iff_bddAbove.mpr ⟨ G.fst, by rintro n ⟨ H, hH, rfl ⟩ ; exact this H hH ⟩;
    have h_finite_H2 : ∀ n ∈ {n : ℕ | ∃ H ∈ S, H.1 = n}, Set.Finite {H : FinGraph | H.1 = n ∧ H ∈ S} := by
      intros n hn
      have h_finite_H2 : Set.Finite {H : SimpleGraph (Fin n) | TriangleRamsey H 2} := by
        exact Set.toFinite _;
      exact Set.Finite.subset ( h_finite_H2.image fun H => ⟨ n, H ⟩ ) fun x hx => by aesop;
    exact Set.Finite.subset ( Set.Finite.biUnion h_finite_H1 fun n hn => h_finite_H2 n hn ) fun x hx => by aesop;
  -- By the well-ordering principle, there exists a minimal element $M$ in $S$.
  obtain ⟨M, hM⟩ : ∃ M ∈ S, ∀ H ∈ S, ¬(H.1 < M.1 ∨ (H.1 = M.1 ∧ H.2.edgeFinset.card < M.2.edgeFinset.card)) := by
    have h_well_ordering : ∀ (T : Finset (FinGraph)), T.Nonempty → ∃ M ∈ T, ∀ H ∈ T, ¬(H.1 < M.1 ∨ (H.1 = M.1 ∧ H.2.edgeFinset.card < M.2.edgeFinset.card)) := by
      intros T hT_nonempty;
      induction' hT_nonempty using Finset.Nonempty.cons_induction with x hx ih;
      · aesop;
      · simp_all +decide [ Finset.cons_eq_insert ];
        grind;
    specialize h_well_ordering hS_finite.toFinset ⟨ G, hS_finite.mem_toFinset.mpr ⟨ FinGraph.IsOrdSubgraphOf.refl G, hG ⟩ ⟩ ; aesop;
  refine' ⟨ M, ⟨ hM.1.2, fun H hH hH' => _ ⟩, hM.1.1 ⟩;
  have hH_in_S : H ∈ S := by
    exact ⟨ hH.trans hM.1.1, hH' ⟩;
  have hH_eq_M : H.1 = M.1 := by
    have hH_le_M : H.1 ≤ M.1 := by
      obtain ⟨ f, hf₁, hf₂ ⟩ := hH;
      simpa using Fintype.card_le_of_injective f hf₁;
    exact le_antisymm hH_le_M ( not_lt.mp fun contra => hM.2 H hH_in_S <| Or.inl contra );
  have hH_eq_M_edges : H.2.edgeFinset.card = M.2.edgeFinset.card := by
    have hH_eq_M_edges : H.2.edgeFinset.card ≤ M.2.edgeFinset.card := by
      obtain ⟨ f, hf₁, hf₂ ⟩ := hH;
      have hH_eq_M_edges : H.2.edgeFinset.card ≤ Finset.card (Finset.image (fun e => Sym2.map f e) H.2.edgeFinset) := by
        rw [ Finset.card_image_of_injective ];
        exact?;
      refine le_trans hH_eq_M_edges <| Finset.card_le_card ?_;
      simp_all +decide [ Finset.subset_iff ];
      rintro ⟨ u, v ⟩ huv; specialize hf₂ u v; aesop;
    exact le_antisymm hH_eq_M_edges ( not_lt.mp fun contra => hM.2 H hH_in_S <| Or.inr ⟨ hH_eq_M, contra ⟩ );
  obtain ⟨ f, hf₁, hf₂ ⟩ := hH;
  have hH_eq_M_edges : ∀ u v, M.snd.Adj (f u) (f v) → H.snd.Adj u v := by
    have hH_eq_M_edges : Finset.image (fun e => Sym2.map f e) H.snd.edgeFinset = M.snd.edgeFinset := by
      refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr _ ) _;
      · rintro ⟨ u, v ⟩ huv; specialize hf₂ u v; aesop;
      · rw [ Finset.card_image_of_injective ];
        · linarith;
        · intro e₁ e₂ h; induction e₁ using Sym2.inductionOn ; induction e₂ using Sym2.inductionOn ; aesop;
    intro u v huv; replace hH_eq_M_edges := Finset.ext_iff.mp hH_eq_M_edges ( Sym2.mk ( f u, f v ) ) ; simp_all +decide [ Sym2.eq_swap ] ;
    obtain ⟨ a, ha₁, ha₂ ⟩ := hH_eq_M_edges; rcases a with ⟨ u', v' ⟩ ; simp_all +decide [ Sym2.eq_swap ] ;
    cases ha₂ <;> simp_all +decide [ hf₁.eq_iff ];
    exact ha₁.symm;
  have hH_eq_M_edges : Function.Bijective f := by
    have := Fintype.bijective_iff_injective_and_card f; aesop;
  use fun u => Classical.choose ( hH_eq_M_edges.2 u );
  have hH_eq_M_edges : ∀ u, f (Classical.choose (hH_eq_M_edges.2 u)) = u := by
    exact fun u => Classical.choose_spec ( hH_eq_M_edges.2 u );
  exact ⟨ fun u v huv => by have := hH_eq_M_edges u; have := hH_eq_M_edges v; aesop, fun u v huv => by have := hH_eq_M_edges u; have := hH_eq_M_edges v; aesop ⟩

end
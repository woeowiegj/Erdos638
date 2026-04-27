import RequestProject.Defs

/-!
# The block sequence construction and main theorem

We construct the block sequence `W₂, W₃, W₄, ...` and define the hereditary
classes `S_ord` and `S_ind`. The main theorem is proved from key lemmas about
the construction.

## Key inputs (sorry'd)

1. **Finite avoidance principle** (Proposition 8 of the paper):
   combines the Nešetřil–Rödl sparse triangle-copy Ramsey theorem with
   the theory of Berge cycles in triangle hypergraphs to produce Ramsey
   graphs avoiding specified minimal cores.

2. **De Bruijn–Erdős compactness**: if every finite subhypergraph of the
   triangle hypergraph is 2-colourable, then the whole hypergraph is
   2-colourable.

3. **Core-based finiteness**: if a graph contains a core from a unique
   block of the sequence, then any graph whose age is contained in S
   has bounded size.
-/

noncomputable section
open scoped Classical

/-! ## The avoidance principle (sorry'd black box) -/

/-- **Finite avoidance principle** (Proposition 8).
Given a finite family `F` of minimal 2-Ramsey cores and `n ≥ 2`, there exists
a finite simple graph `W` such that `W → (K₃)²_n` and no member of `F` occurs
as an ordinary subgraph of `W`.

The proof uses the Nešetřil–Rödl sparse triangle-copy Ramsey theorem
(Theorem 3 of the paper) together with the theory of Berge cycles in
triangle hypergraphs (Lemmas 6–7). -/
lemma avoidance_principle (F : Finset FinGraph)
    (hF : ∀ M ∈ F, IsMinimal2Core M) (n : ℕ) (hn : n ≥ 2) :
    ∃ W : FinGraph, TriangleRamsey W.2 n ∧
      ∀ M ∈ F, ¬M.IsOrdSubgraphOf W := by
  sorry

/-! ## The block sequence -/

/-- Existence of the block sequence with the two key properties:
1. Each `W n` is Ramsey for `n` colours (for `n ≥ 2`).
2. Each minimal 2-Ramsey core appears as an ordinary subgraph of at most
   one block.

The sequence is constructed by recursion: at stage `n`, we apply the avoidance
principle with `F` equal to the set of all minimal cores appearing in earlier
blocks. -/
lemma exists_block_sequence :
    ∃ W : ℕ → FinGraph,
      (∀ n, n ≥ 2 → TriangleRamsey (W n).2 n) ∧
      (∀ (M : FinGraph), IsMinimal2Core M →
        ∀ i j, i ≠ j →
          M.IsOrdSubgraphOf (W i) → ¬M.IsOrdSubgraphOf (W j)) := by
  sorry

/-! ## The class S_ord -/

/-- The set of all ordinary subgraphs of a given finite graph. -/
def OrdSub (G : FinGraph) : Set FinGraph :=
  { H | H.IsOrdSubgraphOf G }

/-- The set of all induced subgraphs of a given finite graph. -/
def IndSub (G : FinGraph) : Set FinGraph :=
  { H | H.IsIndSubgraphOf G }

/-- Fix a block sequence with the required properties. -/
private def blockSeq : ℕ → FinGraph := (exists_block_sequence.choose)

private lemma blockSeq_ramsey : ∀ n, n ≥ 2 → TriangleRamsey (blockSeq n).2 n :=
  exists_block_sequence.choose_spec.1

private lemma blockSeq_core_unique :
    ∀ (M : FinGraph), IsMinimal2Core M →
      ∀ i j, i ≠ j →
        M.IsOrdSubgraphOf (blockSeq i) → ¬M.IsOrdSubgraphOf (blockSeq j) :=
  exists_block_sequence.choose_spec.2

/-- `S_ord`: the hereditary class under ordinary subgraphs.
Defined as the union of ordinary-subgraph closures of all blocks. -/
def S_ord : Set FinGraph := ⋃ n, OrdSub (blockSeq n)

/-- `S_ind`: the hereditary class under induced subgraphs.
Defined as the union of induced-subgraph closures of all blocks. -/
def S_ind : Set FinGraph := ⋃ n, IndSub (blockSeq n)

/-! ## Properties of S_ord -/

/-- S_ord is hereditary under ordinary subgraphs (Lemma 10). -/
theorem S_ord_hereditary : IsOrdHereditary S_ord := by
  intro G hG H hHG
  rw [S_ord, Set.mem_iUnion] at hG ⊢
  obtain ⟨n, hn⟩ := hG
  exact ⟨n, hHG.trans hn⟩

/-- For every `n ≥ 2`, some graph in `S_ord` is Ramsey for `n` colours (Lemma 11). -/
theorem S_ord_ramsey (n : ℕ) (hn : n ≥ 2) :
    ∃ G ∈ S_ord, TriangleRamsey G.2 n := by
  refine ⟨blockSeq n, ?_, blockSeq_ramsey n hn⟩
  rw [S_ord, Set.mem_iUnion]
  exact ⟨n, FinGraph.IsOrdSubgraphOf.refl _⟩

/-- For every `n ≥ 1`, some graph in `S_ord` is Ramsey for `n` colours (Lemma 11). -/
theorem S_ord_ramsey' (n : ℕ) (hn : n ≥ 1) :
    ∃ G ∈ S_ord, TriangleRamsey G.2 n := by
  rcases (show n = 1 ∨ n ≥ 2 by omega) with rfl | hn2
  · -- n = 1: W_2 works (Ramsey for 2 colours implies Ramsey for 1 colour)
    obtain ⟨G, hG, hR⟩ := S_ord_ramsey 2 (by omega)
    refine ⟨G, hG, ?_⟩
    intro c
    -- With only 1 colour, use the 2-colour Ramsey property
    have hR' := hR (fun x => (0 : Fin 2))
    obtain ⟨t, ht1, ht2⟩ := hR'
    exact ⟨t, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · exact S_ord_ramsey n (by omega)

/-! ## The key structural lemma: Age ⊆ S_ord → finite chromatic number -/

set_option maxHeartbeats 1600000 in
/-- If `G` contains no minimal 2-Ramsey core, then `G` is not 2-Ramsey.
This uses de Bruijn–Erdős compactness: every finite subhypergraph of the
triangle hypergraph `T(G)` is 2-colourable (since otherwise a finite subgraph
would be 2-Ramsey and hence contain a core), so `T(G)` itself is 2-colourable. -/
lemma no_core_not_ramsey_2 {V : Type*} (G : SimpleGraph V)
    (hnocore : ∀ M : FinGraph, IsMinimal2Core M →
      ¬∃ f : Fin M.1 → V, Function.Injective f ∧
        ∀ u v, M.2.Adj u v → G.Adj (f u) (f v)) :
    ¬TriangleRamsey G 2 := by
  intro h;
  -- Let $G_F$ be the subgraph of $G$ induced by the endpoints of the edges in $F$.
  obtain ⟨F, hF⟩ : ∃ F : Finset (Sym2 V), ∀ c : Sym2 V → Fin 2, ∃ t : G.Triangle, c s(t.a, t.b) = c s(t.b, t.c) ∧ c s(t.b, t.c) = c s(t.a, t.c) ∧ s(t.a, t.b) ∈ F ∧ s(t.b, t.c) ∈ F ∧ s(t.a, t.c) ∈ F := by
    have h_compact : IsCompact (Set.univ : Set (Sym2 V → Fin 2)) := by
      exact isCompact_univ;
    have h_finite_subcover : ∀ c : Sym2 V → Fin 2, ∃ t : G.Triangle, c s(t.a, t.b) = c s(t.b, t.c) ∧ c s(t.b, t.c) = c s(t.a, t.c) := by
      exact h;
    choose f hf using h_finite_subcover;
    have h_finite_subcover : ∀ c : Sym2 V → Fin 2, ∃ U : Finset (Sym2 V), c ∈ {d : Sym2 V → Fin 2 | ∀ e ∈ U, d e = c e} ∧ ∀ d ∈ {d : Sym2 V → Fin 2 | ∀ e ∈ U, d e = c e}, d s((f c).a, (f c).b) = d s((f c).b, (f c).c) ∧ d s((f c).b, (f c).c) = d s((f c).a, (f c).c) := by
      intro c
      use {s((f c).a, (f c).b), s((f c).b, (f c).c), s((f c).a, (f c).c)};
      grind;
    choose U hU₁ hU₂ using h_finite_subcover;
    have := h_compact.elim_nhds_subcover ( fun c => { d | ∀ e ∈ U c, d e = c e } );
    simp +zetaDelta at *;
    obtain ⟨ t, ht ⟩ := this ( fun c => by
      rw [ nhds_pi ];
      simp +decide [ Filter.mem_pi ];
      exact ⟨ U c, Finset.finite_toSet _, fun e => { c e }, fun e => by simp +decide, fun d hd e he => hd e he ⟩ );
    use Finset.biUnion t (fun c => U c ∪ {s((f c).a, (f c).b), s((f c).b, (f c).c), s((f c).a, (f c).c)});
    intro c;
    obtain ⟨ x, hx ⟩ := Set.mem_iUnion₂.mp ( ht.symm ▸ Set.mem_univ c );
    exact ⟨ f x, hU₂ x c hx.2 |>.1, hU₂ x c hx.2 |>.2, Finset.mem_biUnion.mpr ⟨ x, hx.1, Finset.mem_union_right _ ( Finset.mem_insert_self _ _ ) ⟩, Finset.mem_biUnion.mpr ⟨ x, hx.1, Finset.mem_union_right _ ( Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ) ⟩, Finset.mem_biUnion.mpr ⟨ x, hx.1, Finset.mem_union_right _ ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ) ⟩ ⟩;
  -- Let $G_F$ be the subgraph of $G$ induced by the endpoints of the edges in $F$. Then $G_F$ is 2-Ramsey.
  obtain ⟨G_F, hG_F⟩ : ∃ G_F : FinGraph, TriangleRamsey G_F.2 2 ∧ ∃ f : Fin G_F.1 → V, Function.Injective f ∧ ∀ u v, G_F.2.Adj u v → G.Adj (f u) (f v) := by
    obtain ⟨S, hS⟩ : ∃ S : Finset V, ∀ t : G.Triangle, s(t.a, t.b) ∈ F ∧ s(t.b, t.c) ∈ F ∧ s(t.a, t.c) ∈ F → t.a ∈ S ∧ t.b ∈ S ∧ t.c ∈ S := by
      have hG_F : Set.Finite {v : V | ∃ e ∈ F, v ∈ e} := by
        have h_finite : ∀ e ∈ F, Set.Finite {v : V | v ∈ e} := by
          intro e he; exact (by
          rcases e with ⟨ u, v ⟩ ; exact Set.toFinite { u, v } |> Set.Finite.subset <| by aesop_cat;);
        exact Set.Finite.subset ( Set.Finite.biUnion ( Finset.finite_toSet F ) h_finite ) fun x hx => by aesop;
      exact ⟨ hG_F.toFinset, fun t ht => ⟨ hG_F.mem_toFinset.mpr ⟨ _, ht.1, by simp +decide ⟩, hG_F.mem_toFinset.mpr ⟨ _, ht.2.1, by simp +decide ⟩, hG_F.mem_toFinset.mpr ⟨ _, ht.2.2, by simp +decide ⟩ ⟩ ⟩;
    obtain ⟨f, hf⟩ : ∃ f : Fin (Finset.card S) → V, Function.Injective f ∧ ∀ i, f i ∈ S := by
      have h_finite : Nonempty (Fin (Finset.card S) ≃ S) := by
        exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
      exact ⟨ _, Subtype.val_injective.comp h_finite.some.injective, fun i => h_finite.some i |>.2 ⟩;
    refine' ⟨ ⟨ S.card, SimpleGraph.fromRel fun u v => G.Adj ( f u ) ( f v ) ⟩, _, f, hf.1, _ ⟩ <;> simp +decide [ SimpleGraph.fromRel ];
    · intro c;
      obtain ⟨ t, ht ⟩ := hF ( fun x => if hx : ∃ i j, x = s(f i, f j) then c ( s(hx.choose, hx.choose_spec.choose) ) else 0 );
      -- Since $t.a$, $t.b$, and $t.c$ are in $S$, there exist indices $i$, $j$, and $k$ such that $f i = t.a$, $f j = t.b$, and $f k = t.c$.
      obtain ⟨i, hi⟩ : ∃ i : Fin S.card, f i = t.a := by
        have h_image : Finset.image f Finset.univ = S := by
          exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => hf.2 i ) ( by rw [ Finset.card_image_of_injective _ hf.1, Finset.card_fin ] );
        exact Finset.mem_image.mp ( h_image.symm ▸ hS t ht.2.2 |>.1 ) |> Exists.imp fun i => And.right
      obtain ⟨j, hj⟩ : ∃ j : Fin S.card, f j = t.b := by
        have := Finset.eq_of_subset_of_card_le ( show Finset.image f Finset.univ ⊆ S from Finset.image_subset_iff.mpr fun i _ => hf.2 i ) ; simp_all +decide [ Finset.card_image_of_injective _ hf.1 ] ;
        exact Finset.mem_image.mp ( this.symm ▸ hS t ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2 |>.2.1 ) |> Exists.imp fun x hx => hx.2
      obtain ⟨k, hk⟩ : ∃ k : Fin S.card, f k = t.c := by
        have := Finset.eq_of_subset_of_card_le ( show Finset.image f Finset.univ ⊆ S from Finset.image_subset_iff.mpr fun i _ => hf.2 i ) ; simp_all +decide [ Finset.card_image_of_injective _ hf.1 ] ;
        exact Finset.mem_image.mp ( this.symm ▸ hS t ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2 |>.2.2 ) |> Exists.imp fun x hx => hx.2;
      use ⟨ i, j, k, by
        exact ⟨ by rintro rfl; exact t.adj_ab.ne ( by aesop ), Or.inl ( by simpa [ hi, hj ] using t.adj_ab ) ⟩, by
        have := t.adj_bc; simp_all +decide [ SimpleGraph.adj_comm ] ;
        rintro rfl; simp_all +decide [ SimpleGraph.adj_comm ] ;, by
        exact ⟨ by rintro rfl; exact t.adj_ac.ne ( by aesop ), Or.inl ( by simpa [ hi, hk ] using t.adj_ac ) ⟩ ⟩;
      convert ht.1 using 1;
      split_ifs <;> simp +decide [ ← hi, ← hj, ← hk ] at *;
      · simp +decide [ hf.1.eq_iff ] at *;
        split_ifs at ht <;> simp +decide [ ‹f i = t.a›, ‹f j = t.b›, ‹f k = t.c› ] at ht ⊢;
        grind +suggestions;
        grind;
        grind +suggestions;
        · grind +suggestions;
        · lia;
        · lia;
        · grind +extAll;
        · grind +suggestions;
      · grind;
      · exact False.elim ( ‹∀ x x_1 : Fin S.card, ( f i = f x → ¬f j = f x_1 ) ∧ ( f i = f x_1 → ¬f j = f x ) › i j |>.1 rfl rfl );
      · grind;
    · exact fun u v huv h => h.elim ( fun h => h ) fun h => h.symm;
  obtain ⟨ M, hM₁, hM₂ ⟩ := exists_minimal_core hG_F.1;
  exact hnocore M hM₁ ( by rcases hM₂ with ⟨ f, hf₁, hf₂ ⟩ ; rcases hG_F.2 with ⟨ g, hg₁, hg₂ ⟩ ; exact ⟨ g ∘ f, hg₁.comp hf₁, fun u v huv => hg₂ _ _ ( hf₂ _ _ huv ) ⟩ )

/-
A finite graph is not Ramsey for sufficiently many colours.
Specifically, if `G` has `N` vertices, then `G` is not `(N.choose 2 + 1)`-Ramsey:
we can colour each edge with a distinct colour, preventing monochromatic triangles.
-/
lemma finite_graph_not_ramsey (G : FinGraph) :
    ∃ m : ℕ, ¬TriangleRamsey G.2 m := by
  by_contra! h;
  -- By assumption, $G$ is Ramsey for all $m$, so in particular for $m = (Finset.univ : Finset (Sym2 (Fin G.1))).card + 1$.
  obtain ⟨c, hc⟩ : ∃ c : Sym2 (Fin G.1) → Fin ((Finset.univ : Finset (Sym2 (Fin G.1))).card + 1), Function.Injective c := by
    exact ⟨ fun x => ⟨ Fintype.equivFin _ x |> Fin.val, Nat.lt_succ_of_lt ( Fin.is_lt _ ) ⟩, fun x y hxy => by simpa [ Fin.ext_iff ] using Fintype.equivFin _ |>.injective ( Fin.ext <| by simpa using hxy ) ⟩;
  obtain ⟨ t, ht ⟩ := h _ c;
  simp_all +decide [ hc.eq_iff ];
  cases ht.1 <;> have := t.adj_ab <;> have := t.adj_bc <;> have := t.adj_ac <;> aesop

/-
**Key structural lemma** (Lemma 13):
If `G` is a graph with `OrdAge G ⊆ S_ord`, then there exists a finite `m`
such that `G` is not `m`-Ramsey for triangles.

**Proof sketch.** There are two cases.

*Case 1:* `G` contains no minimal 2-Ramsey core. Then by `no_core_not_ramsey_2`,
`G` is not 2-Ramsey, so `m = 2` works.

*Case 2:* `G` contains a minimal core `M`. Since `OrdAge G ⊆ S_ord`, the core
`M ∈ S_ord`, so `M ∈ OrdSub (blockSeq j)` for some `j`. By `blockSeq_core_unique`,
`j` is the unique block containing `M`. Every finite subgraph of `G` containing `M`
must also lie in `OrdSub (blockSeq j)` (since it contains `M` and `M` only appears
in block `j`). This bounds the number of vertices of `G` by `(blockSeq j).1`,
forcing `G` to be finite. A finite graph is not Ramsey for sufficiently many colours.

If `G` contains a core `M` that embeds into a unique block `blockSeq j`,
and `OrdAge G ⊆ S_ord`, then any finite subset of `V` containing the
image of the core has at most `(blockSeq j).1` elements.
This forces `G` to have at most `(blockSeq j).1` vertices.
-/
lemma core_forces_finite {V : Type*} (G : SimpleGraph V)
    (hAge : OrdAge G ⊆ S_ord)
    (M : FinGraph) (hM : IsMinimal2Core M)
    (g : Fin M.1 → V) (hg_inj : Function.Injective g)
    (hg_adj : ∀ u v, M.2.Adj u v → G.Adj (g u) (g v))
    (j : ℕ) (hj : M.IsOrdSubgraphOf (blockSeq j)) :
    ∀ (S : Finset V), (∀ i : Fin M.1, g i ∈ S) → S.card ≤ (blockSeq j).1 := by
  intro S hS;
  -- Let $G_S$ be the induced subgraph of $G$ on $S$.
  obtain ⟨GS, hGS⟩ : ∃ GS : Fin S.card → V, Function.Injective GS ∧ ∀ i, GS i ∈ S ∧ ∀ u v, GS u ∈ S ∧ GS v ∈ S → G.Adj (GS u) (GS v) → G.Adj (GS u) (GS v) := by
    have hGS : Nonempty (Fin S.card ≃ S) := by
      exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
    exact ⟨ _, Subtype.val_injective.comp hGS.some.injective, fun i => ⟨ hGS.some i |>.2, fun u v _ _ => by assumption ⟩ ⟩;
  -- Since $M$ is a minimal 2-Ramsey core and $S$ contains all vertices of $M$, the induced subgraph $G[S]$ must also contain $M$ as a subgraph.
  have hGS_subgraph : M.IsOrdSubgraphOf (⟨S.card, SimpleGraph.fromRel (fun u v => G.Adj (GS u) (GS v))⟩) := by
    have hGS_subgraph : ∀ i : Fin M.fst, ∃ j : Fin S.card, GS j = g i := by
      have hGS_subgraph : Finset.image GS Finset.univ = S := by
        exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => hGS.2 i |>.1 ) ( by rw [ Finset.card_image_of_injective _ hGS.1, Finset.card_fin ] );
      exact fun i => Finset.mem_image.mp ( hGS_subgraph.symm ▸ hS i ) |> Exists.imp fun j hj => hj.2;
    choose f hf using hGS_subgraph;
    use f;
    simp_all +decide [ SimpleGraph.fromRel, Function.Injective.eq_iff hg_inj ];
    exact ⟨ fun u v huv => hg_inj <| by have := hf u; have := hf v; aesop, fun u v huv => fun h => by have := hf u; have := hf v; have := hg_adj u v huv; aesop ⟩;
  -- Since $G[S]$ is a subgraph of $G$, it must be in $S_ord$.
  have hGS_in_S_ord : ⟨S.card, SimpleGraph.fromRel (fun u v => G.Adj (GS u) (GS v))⟩ ∈ S_ord := by
    refine' hAge _;
    use GS;
    simp_all +decide [ SimpleGraph.fromRel ];
    exact fun u v huv h => h.elim ( fun h => h ) fun h => h.symm;
  obtain ⟨ k, hk ⟩ := Set.mem_iUnion.mp hGS_in_S_ord;
  have := blockSeq_core_unique M hM k j;
  by_cases hkj : k = j <;> simp_all +decide;
  · obtain ⟨ f, hf_inj, hf_adj ⟩ := hk;
    exact?;
  · exact False.elim ( this ( hGS_subgraph.trans hk ) )

theorem age_sub_S_ord_finite_chromatic {V : Type*} (G : SimpleGraph V)
    (hAge : OrdAge G ⊆ S_ord) :
    ∃ m : ℕ, ¬TriangleRamsey G m := by
  -- Case split: does G contain a minimal 2-Ramsey core?
  by_cases h : ∃ M : FinGraph, IsMinimal2Core M ∧
    ∃ f : Fin M.1 → V, Function.Injective f ∧ ∀ u v, M.2.Adj u v → G.Adj (f u) (f v)
  · -- Case 2: G contains a minimal core M
    obtain ⟨M, hM_core, g, hg_inj, hg_adj⟩ := h
    -- M ∈ OrdAge G, so M ∈ S_ord
    have hM_in_age : M ∈ OrdAge G := ⟨g, hg_inj, hg_adj⟩
    have hM_in_S : M ∈ S_ord := hAge hM_in_age
    -- M ∈ OrdSub (blockSeq j) for some j
    rw [S_ord, Set.mem_iUnion] at hM_in_S
    obtain ⟨j, hj⟩ := hM_in_S
    -- By core_forces_finite, every finite superset of the core image has
    -- at most (blockSeq j).1 vertices. Hence V has at most (blockSeq j).1 elements.
    have hbound := core_forces_finite G hAge M hM_core g hg_inj hg_adj j hj
    -- G has at most (blockSeq j).1 vertices, so it's a finite graph
    -- and hence not Ramsey for sufficiently many colours.
    -- For any finite set S ⊇ range g with |S| ≤ (blockSeq j).1,
    -- all vertices must be in S. So V is finite.
    -- Since V is finite, we can use the fact that any finite graph is not Ramsey for sufficiently many colors.
    have h_finite : Finite V := by
      contrapose! hbound;
      have := Set.Infinite.exists_subset_card_eq ( Set.infinite_univ.diff ( Set.toFinite ( Set.range g ) ) ) ( ( blockSeq j ).fst + 1 );
      obtain ⟨ t, ht₁, ht₂ ⟩ := this; use Finset.image g Finset.univ ∪ t; simp_all +decide [ Finset.card_image_of_injective _ hg_inj ] ;
      exact lt_of_lt_of_le ( by simp +decide [ ht₂ ] ) ( Finset.card_mono ( Finset.subset_union_right ) );
    refine' ⟨ Fintype.card ( Sym2 V ), _ ⟩;
    intro h;
    obtain ⟨ c, hc ⟩ := h ( fun e => Fintype.equivFin ( Sym2 V ) e );
    have := c.adj_ab.ne; have := c.adj_bc.ne; have := c.adj_ac.ne; simp_all +decide [ Sym2.eq_swap ] ;
  · -- Case 1: G contains no minimal core
    have hnocore : ∀ M : FinGraph, IsMinimal2Core M →
        ¬∃ f : Fin M.1 → V, Function.Injective f ∧
          ∀ u v, M.2.Adj u v → G.Adj (f u) (f v) := by
      intro M hM ⟨f, hf_inj, hf_adj⟩
      exact h ⟨M, hM, f, hf_inj, hf_adj⟩
    exact ⟨2, no_core_not_ramsey_2 G hnocore⟩

/-! ## Main Theorem (ordinary subgraph version) -/

/-- **Main Theorem (ordinary subgraph version)** (Proposition 14).
There exists a hereditary class `S` of finite graphs (under ordinary subgraphs)
such that:
1. For every `n ≥ 1`, some `G ∈ S` satisfies `G → (K₃)²_n`.
2. For every graph `G` with `OrdAge G ⊆ S`, there exists a finite `m` such
   that `G` is not `m`-Ramsey. In particular, `G` does not satisfy
   `G → (K₃)²_κ` for any infinite cardinal `κ`. -/
theorem main_theorem_ord :
    ∃ S : Set FinGraph,
      IsOrdHereditary S ∧
      (∀ n, n ≥ 1 → ∃ G ∈ S, TriangleRamsey G.2 n) ∧
      (∀ (V : Type*) (G : SimpleGraph V), OrdAge G ⊆ S →
        ∃ m : ℕ, ¬TriangleRamsey G m) := by
  exact ⟨S_ord, S_ord_hereditary, S_ord_ramsey', fun V G h => age_sub_S_ord_finite_chromatic G h⟩

/-! ## Properties of S_ind -/

/-- S_ind is hereditary under induced subgraphs (Lemma 15). -/
theorem S_ind_hereditary : IsIndHereditary S_ind := by
  intro G hG H hHG
  rw [S_ind, Set.mem_iUnion] at hG ⊢
  obtain ⟨n, hn⟩ := hG
  exact ⟨n, hHG.trans hn⟩

/-- For every `n ≥ 1`, some graph in `S_ind` is Ramsey for `n` colours (Lemma 16). -/
theorem S_ind_ramsey' (n : ℕ) (hn : n ≥ 1) :
    ∃ G ∈ S_ind, TriangleRamsey G.2 n := by
  rcases (show n = 1 ∨ n ≥ 2 by omega) with rfl | hn2
  · -- n = 1: blockSeq 2 works; Ramsey for 2 implies Ramsey for 1
    refine ⟨blockSeq 2, ?_, ?_⟩
    · rw [S_ind, Set.mem_iUnion]
      exact ⟨2, ⟨id, Function.injective_id, fun _ _ => Iff.rfl⟩⟩
    · intro c
      obtain ⟨t, _, _⟩ := blockSeq_ramsey 2 (by omega) (fun _ => (0 : Fin 2))
      exact ⟨t, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · refine ⟨blockSeq n, ?_, blockSeq_ramsey n hn2⟩
    rw [S_ind, Set.mem_iUnion]
    exact ⟨n, ⟨id, Function.injective_id, fun _ _ => Iff.rfl⟩⟩

/-
**Key structural lemma** (Lemma 17, induced version):
If `G` is a graph with `IndAge G ⊆ S_ind`, then there exists a finite `m`
such that `G` is not `m`-Ramsey for triangles. The argument is analogous to
the ordinary case.
-/
set_option maxHeartbeats 3200000 in
theorem age_sub_S_ind_finite_chromatic {V : Type*} (G : SimpleGraph V)
    (hAge : IndAge G ⊆ S_ind) :
    ∃ m : ℕ, ¬TriangleRamsey G m := by
  by_cases h : ∀ M : FinGraph, IsMinimal2Core M → ¬∃ f : Fin M.1 → V, Function.Injective f ∧ ∀ u v, M.2.Adj u v → G.Adj ( f u ) ( f v );
  · exact ⟨ 2, no_core_not_ramsey_2 G h ⟩;
  · obtain ⟨M, hM⟩ : ∃ M : FinGraph, IsMinimal2Core M ∧ ∃ f : Fin M.1 → V, Function.Injective f ∧ ∀ u v, M.2.Adj u v → G.Adj (f u) (f v) := by
      grind;
    obtain ⟨g, hg_inj, hg_adj⟩ := hM.right
    obtain ⟨j, hj⟩ : ∃ j, M.IsOrdSubgraphOf (blockSeq j) := by
      have hM_in_S_ind : ∃ H ∈ S_ind, M.IsOrdSubgraphOf H := by
        refine' ⟨ ⟨ M.1, SimpleGraph.fromRel fun u v => G.Adj ( g u ) ( g v ) ⟩, hAge _, _ ⟩;
        · use g;
          simp +decide [ hg_inj.eq_iff, SimpleGraph.adj_comm ];
          exact ⟨ hg_inj, fun u v huv => by rintro rfl; exact huv.ne rfl ⟩;
        · use fun u => u;
          exact ⟨ Function.injective_id, fun u v huv => ⟨ huv.ne, Or.inl ( hg_adj u v huv ) ⟩ ⟩;
      obtain ⟨ H, hH₁, hH₂ ⟩ := hM_in_S_ind;
      obtain ⟨ j, hj ⟩ := Set.mem_iUnion.mp hH₁;
      exact ⟨ j, hH₂.trans ( hj.toOrd ) ⟩;
    have h_finite : ∀ (S : Finset V), (∀ i : Fin M.1, g i ∈ S) → S.card ≤ (blockSeq j).1 := by
      intro S hS
      have h_ind_subgraph : ∃ f : Fin S.card → V, Function.Injective f ∧ ∀ i, f i ∈ S ∧ ∀ u v, (SimpleGraph.fromRel (fun u v => G.Adj (f u) (f v))).Adj u v ↔ G.Adj (f u) (f v) := by
        have h_ind_subgraph : ∃ f : Fin S.card → V, Function.Injective f ∧ ∀ i, f i ∈ S := by
          have h_ind_subgraph : Nonempty (Fin S.card ≃ S) := by
            exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
          exact ⟨ _, Subtype.val_injective.comp h_ind_subgraph.some.injective, fun i => h_ind_subgraph.some i |>.2 ⟩;
        obtain ⟨ f, hf_inj, hf_mem ⟩ := h_ind_subgraph; use f; simp_all +decide [ SimpleGraph.adj_comm ] ;
        exact fun i u v huv => by rintro rfl; exact huv.ne rfl;
      obtain ⟨f, hf_inj, hf_adj⟩ := h_ind_subgraph
      have h_ind_subgraph_in_S_ind : (⟨S.card, SimpleGraph.fromRel (fun u v => G.Adj (f u) (f v))⟩ : FinGraph) ∈ S_ind := by
        apply hAge;
        use f;
        exact ⟨ hf_inj, fun u v => by simpa using hf_adj u |>.2 u v ⟩;
      obtain ⟨k, hk⟩ : ∃ k, (⟨S.card, SimpleGraph.fromRel (fun u v => G.Adj (f u) (f v))⟩ : FinGraph) ∈ IndSub (blockSeq k) := by
        exact Set.mem_iUnion.mp h_ind_subgraph_in_S_ind;
      have h_core_in_block : M.IsOrdSubgraphOf (blockSeq k) := by
        have h_core_in_block : M.IsOrdSubgraphOf (⟨S.card, SimpleGraph.fromRel (fun u v => G.Adj (f u) (f v))⟩ : FinGraph) := by
          have h_core_in_block : ∀ i : Fin M.1, ∃ j : Fin S.card, f j = g i := by
            have h_core_in_block : Finset.image f Finset.univ = S := by
              exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => hf_adj i |>.1 ) ( by rw [ Finset.card_image_of_injective _ hf_inj, Finset.card_fin ] );
            exact fun i => Finset.mem_image.mp ( h_core_in_block.symm ▸ hS i ) |> Exists.imp fun x hx => hx.2;
          choose h hh using h_core_in_block;
          use h;
          simp_all +decide [ Function.Injective, SimpleGraph.fromRel ];
          exact ⟨ fun i j hij => hg_inj <| by have := hh i; have := hh j; aesop, fun u v huv => fun h => by have := hh u; have := hh v; have := hg_adj u v huv; aesop ⟩;
        exact FinGraph.IsOrdSubgraphOf.trans h_core_in_block ( FinGraph.IsIndSubgraphOf.toOrd hk );
      have h_core_in_block : k = j := by
        exact Classical.not_not.1 fun h => blockSeq_core_unique M hM.1 k j h h_core_in_block hj;
      obtain ⟨ f', hf'_inj, hf'_adj ⟩ := hk;
      have := Fintype.card_le_of_injective f' hf'_inj; aesop;
    have h_finite : Finite V := by
      contrapose! h_finite;
      have := h_finite.natEmbedding;
      use Finset.image (fun i : ℕ => this i) (Finset.range ((blockSeq j).fst + 1)) ∪ Finset.image g Finset.univ;
      exact ⟨ fun i => Finset.mem_union_right _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ), lt_of_lt_of_le ( by simp +decide [ Finset.card_image_of_injective _ this.injective ] ) ( Finset.card_mono <| Finset.subset_union_left ) ⟩;
    have := Finite.exists_equiv_fin V;
    obtain ⟨ n, ⟨ e ⟩ ⟩ := this;
    have := finite_graph_not_ramsey ⟨ n, G.map e ⟩;
    obtain ⟨ m, hm ⟩ := this;
    use m;
    contrapose! hm;
    intro c;
    obtain ⟨ t, ht ⟩ := hm ( fun x => c ( Sym2.map e x ) );
    use ⟨ e t.a, e t.b, e t.c, by
      exact ⟨ t.a, t.b, t.adj_ab, rfl, rfl ⟩, by
      exact ⟨ t.b, t.c, t.adj_bc, rfl, rfl ⟩, by
      exact ⟨ t.a, t.c, t.adj_ac, rfl, rfl ⟩ ⟩;
    exact ht

/-! ## Main Theorem (induced subgraph version) -/

/-- **Main Theorem (induced subgraph version)** (Proposition 18).
There exists a hereditary class `S` of finite graphs (under induced subgraphs)
such that:
1. For every `n ≥ 1`, some `G ∈ S` satisfies `G → (K₃)²_n`.
2. For every graph `G` with `IndAge G ⊆ S`, there exists a finite `m` such
   that `G` is not `m`-Ramsey. -/
theorem main_theorem_ind :
    ∃ S : Set FinGraph,
      IsIndHereditary S ∧
      (∀ n, n ≥ 1 → ∃ G ∈ S, TriangleRamsey G.2 n) ∧
      (∀ (V : Type*) (G : SimpleGraph V), IndAge G ⊆ S →
        ∃ m : ℕ, ¬TriangleRamsey G m) := by
  exact ⟨S_ind, S_ind_hereditary, S_ind_ramsey', fun V G h => age_sub_S_ind_finite_chromatic G h⟩

/-- **The Main Theorem** (combined statement).
Both the ordinary-subgraph and induced-subgraph hereditary versions of the
triangle Ramsey compactness problem have negative answers. -/
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
        ∃ m : ℕ, ¬TriangleRamsey G m)) :=
  ⟨main_theorem_ord, main_theorem_ind⟩

end
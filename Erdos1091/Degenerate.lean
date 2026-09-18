/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Erdos1091.Construction
import Erdos1091.DegenerateCore
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# Proposition 4.6: every proper subgraph of `Gₘ` is 2-degenerate, hence 3-colorable

The paper's argument is six lines, and rests on exactly two facts about the construction:
`G'ₘ = Gₘ \ {v}` is connected, and every vertex other than `v` has degree exactly 3.

Let `H ⊊ Gₘ` be a non-empty proper subgraph.

* If `V(H) = V(Gₘ)`, some edge `e ∈ E(Gₘ) \ E(H)` is missing. That edge is incident to a
  vertex `≠ v`, and that vertex has `H`-degree at most 2.
* If `V(H) ⊊ V(Gₘ)` and `V(H) ⊄ {v}`, connectivity of `G'ₘ` supplies a `u ∈ V(H) \ {v}` with a
  `Gₘ`-neighbour outside `V(H)`; again `u` has `H`-degree at most 2.

Since this applies to every subgraph of `H` as well, `H` is 2-degenerate, and a 2-degenerate
graph is 3-colorable (`Erdos1091.colorable_three_of_isTwoDegenerate`, proved in
`Erdos1091.DegenerateCore` — Mathlib has no degeneracy or greedy-colouring API).

## Implementation notes

The quantifier in `Erdos1091.IsTwoDegenerate` ranges over `H.coe.Subgraph`, which makes the
hereditary step awkward. Two devices keep the proof short:

* `Erdos1091.isTwoDegenerate_of_forall_set` replaces that quantifier by one over plain *sets*
  of ambient vertices. This is the converse of `Erdos1091.exists_mem_encard_le_two`, and it is
  what lets the whole argument be run once, in `Erdos1091.master`, on subsets of `Vtx m`
  rather than on subgraphs of a subgraph.
* `Erdos1091.encard_le_two_of_excluded` isolates the counting common to *all four* branches:
  a vertex `p ≠ v` has `Gₘ`-degree exactly 3, so as soon as one of its three `Gₘ`-neighbours
  fails to be an `H`-neighbour inside `S`, at most two remain. Phrasing the hypothesis as a
  negated conjunction lets the "missing edge" branch (`w ∈ S`, but `¬ H.Adj p w`) and the
  "boundary" branch (`w ∉ S`) share one proof.

## References

* [APSSV26b] arXiv:2604.06609, Proposition 4.6.
-/

namespace Erdos1091

open SimpleGraph

variable {m : ℕ}

/-- Every edge of `Gₘ` has at least one endpoint different from `v`. -/
theorem exists_ne_v_of_adj {u w : Vtx m} (h : (G m).Adj u w) :
    u ≠ Vtx.v m ∨ w ≠ Vtx.v m := by
  by_contra hcon
  push Not at hcon
  exact h.ne (hcon.1.trans hcon.2.symm)

/-- The `Set`-indexed criterion for 2-degeneracy: it is enough to find, in every non-empty set
of vertices, one vertex with at most two neighbours *inside that set*.

This is the converse of `Erdos1091.exists_mem_encard_le_two`. -/
theorem isTwoDegenerate_of_forall_set {V : Type*} {H : SimpleGraph V}
    (h : ∀ s : Set V, s.Nonempty → ∃ u ∈ s, {z | z ∈ s ∧ H.Adj u z}.encard ≤ 2) :
    IsTwoDegenerate H := by
  intro K hK
  obtain ⟨u, hu, hcard⟩ := h K.verts hK
  refine ⟨⟨u, hu⟩, ?_⟩
  have himg : Subtype.val '' (K.coe.neighborSet ⟨u, hu⟩ : Set K.verts) ⊆
      {z | z ∈ K.verts ∧ H.Adj u z} := by
    rintro z ⟨⟨y, hy⟩, hadj, rfl⟩
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.Subgraph.coe_adj] at hadj
    exact ⟨hy, K.adj_sub hadj⟩
  calc (K.coe.neighborSet ⟨u, hu⟩ : Set K.verts).encard
      = (Subtype.val '' (K.coe.neighborSet ⟨u, hu⟩ : Set K.verts)).encard :=
        (Subtype.val_injective.encard_image _).symm
    _ ≤ ({z | z ∈ K.verts ∧ H.Adj u z} : Set V).encard := Set.encard_le_encard himg
    _ ≤ 2 := hcard

/-! ### The counting step -/

/-- `Erdos1091.degree_eq_three` in `Set.encard` form. -/
theorem neighborSet_encard_eq_three (m : ℕ) (hm : 1 ≤ m) (u : Vtx m) (hu : u ≠ Vtx.v m) :
    ((G m).neighborSet u : Set (Vtx m)).encard = 3 := by
  have h := degree_eq_three m hm u hu
  rw [← SimpleGraph.coe_neighborFinset, Set.encard_coe_eq_coe_finsetCard]
  rw [SimpleGraph.degree] at h
  rw [h]
  rfl

/-- **The counting core.** If `p ≠ v`, `w` is a `Gₘ`-neighbour of `p`, and every element of `T`
is a `Gₘ`-neighbour of `p` other than `w`, then `T` has at most two elements: `p` has exactly
three neighbours and `w` is not among those counted. -/
theorem encard_le_two_of_subset_neighborSet_diff (m : ℕ) (hm : 1 ≤ m) {p w : Vtx m}
    (hp : p ≠ Vtx.v m) (hw : (G m).Adj p w) {T : Set (Vtx m)}
    (hT : T ⊆ ((G m).neighborSet p : Set (Vtx m)) \ {w}) : T.encard ≤ 2 := by
  have hmem : w ∈ ((G m).neighborSet p : Set (Vtx m)) := hw
  have h3 := neighborSet_encard_eq_three m hm p hp
  calc T.encard ≤ (((G m).neighborSet p : Set (Vtx m)) \ {w}).encard := Set.encard_le_encard hT
    _ = ((G m).neighborSet p : Set (Vtx m)).encard - 1 := Set.encard_sdiff_singleton_of_mem hmem
    _ = 2 := by rw [h3]; rfl

/-- The uniform bound used in every branch of `Erdos1091.master`: if `p ≠ v` has a
`Gₘ`-neighbour `w` which fails to be an `H`-neighbour of `p` inside `S`, then `p` has at most
two `H`-neighbours inside `S`. -/
theorem encard_le_two_of_excluded (m : ℕ) (hm : 1 ≤ m) (H : (G m).Subgraph)
    (S : Set (Vtx m)) {p w : Vtx m} (hp : p ≠ Vtx.v m) (hpw : (G m).Adj p w)
    (hexcl : ¬ (w ∈ S ∧ H.Adj p w)) :
    {z | z ∈ S ∧ H.Adj p z}.encard ≤ 2 := by
  refine encard_le_two_of_subset_neighborSet_diff m hm hp hpw ?_
  rintro z ⟨hzS, hadj⟩
  refine ⟨H.adj_sub hadj, ?_⟩
  rintro rfl
  exact hexcl ⟨hzS, hadj⟩

/-- A proper subgraph carrying *all* the vertices must be missing an edge. -/
theorem exists_missing_edge (m : ℕ) (H : (G m).Subgraph) (hne : H ≠ ⊤)
    (hverts : H.verts = Set.univ) : ∃ a b : Vtx m, (G m).Adj a b ∧ ¬ H.Adj a b := by
  by_contra hcon
  push Not at hcon
  refine hne ?_
  refine SimpleGraph.Subgraph.ext ?_ ?_
  · simp [hverts]
  · funext a b
    simp only [SimpleGraph.Subgraph.top_adj, eq_iff_iff]
    exact ⟨fun h => H.adj_sub h, fun h => hcon a b h⟩

/-- The `a`-slot of the `b`-leaf hanging off the spine block `S₀`. It is a `Gₘ`-neighbour of the
special vertex `v`, and it exists for every `m` because the `b`-leaf is unconditionally valid.

It is used as a concrete witness in the one branch of `Erdos1091.master` where `S = {v}ᶜ`: there
the only vertex missing from `S` is `v` itself, so we must point at a vertex that `v` actually
sees. -/
def probeVtx (m : ℕ) : Vtx m := Vtx.mk ⟨Block.leaf 0 Slot.b, rfl⟩ Slot.a

theorem probeVtx_ne_v (m : ℕ) : probeVtx m ≠ Vtx.v m := by
  simp [probeVtx, Vtx.mk, Vtx.v]

theorem probeVtx_adj_v (m : ℕ) : (G m).Adj (probeVtx m) (Vtx.v m) := by
  rw [G_adj]
  refine ⟨probeVtx_ne_v m, Or.inr ?_⟩
  simp [rawAdjVB, specialAdjVB, probeVtx, Vtx.mk, Vtx.v]

/-- **Master lemma.** For a proper subgraph `H` of `Gₘ` and any non-empty set `S` of vertices of
`H`, some `p ∈ S` has at most two `H`-neighbours inside `S`.

The case split is on "does `S` contain a vertex other than `v`", then "is there a vertex other
than `v` *outside* `S`" — which makes `S = Set.univ` fall out as a sub-branch rather than
needing to be decided up front. -/
theorem master (m : ℕ) (hm : 1 ≤ m) (H : (G m).Subgraph) (hne : H ≠ ⊤)
    (S : Set (Vtx m)) (hS : S.Nonempty) (hSH : S ⊆ H.verts) :
    ∃ p ∈ S, {z | z ∈ S ∧ H.Adj p z}.encard ≤ 2 := by
  by_cases hex : ∃ p₀ ∈ S, p₀ ≠ Vtx.v m
  case neg =>
    -- `S ⊆ {v}`, hence `S = {v}`, and `v` has no `H`-neighbour at all.
    push Not at hex
    obtain ⟨x, hx⟩ := hS
    obtain rfl : x = Vtx.v m := hex x hx
    refine ⟨Vtx.v m, hx, ?_⟩
    have : {z | z ∈ S ∧ H.Adj (Vtx.v m) z} = (∅ : Set (Vtx m)) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hzS, hadj⟩
      obtain rfl : z = Vtx.v m := hex z hzS
      exact (G m).irrefl (H.adj_sub hadj)
    rw [this]
    simp
  case pos =>
  obtain ⟨p₀, hp₀S, hp₀v⟩ := hex
  by_cases hout : ∃ z, z ∉ S ∧ z ≠ Vtx.v m
  case pos =>
    -- A `G'ₘ`-walk from `p₀ ∈ S` to `z ∉ S` must cross the boundary of `S`.
    obtain ⟨z, hzS, hzv⟩ := hout
    obtain ⟨W⟩ := G'_reachable m hm p₀ z hp₀v hzv
    obtain ⟨d, -, hd1, hd2⟩ := W.exists_boundary_dart S hp₀S hzS
    have hdv : d.fst ≠ Vtx.v m := by
      rintro hfst
      exact G'_not_adj_v d.snd (hfst ▸ d.adj)
    refine ⟨d.fst, hd1, ?_⟩
    exact encard_le_two_of_excluded m hm H S hdv (G'_le_G d.adj) (fun h => hd2 h.1)
  case neg =>
    push Not at hout
    by_cases hv : Vtx.v m ∈ S
    case pos =>
      -- `S = Set.univ`, so `H.verts = Set.univ` and `H` must be missing an edge.
      have hSuniv : S = Set.univ := by
        ext z
        simp only [Set.mem_univ, iff_true]
        by_contra hzS
        exact hzS (hout z hzS ▸ hv)
      have hverts : H.verts = Set.univ := Set.eq_univ_of_univ_subset (hSuniv ▸ hSH)
      obtain ⟨a, b, hab, hnab⟩ := exists_missing_edge m H hne hverts
      rcases exists_ne_v_of_adj hab with ha | hb
      · exact ⟨a, hSuniv ▸ Set.mem_univ a,
          encard_le_two_of_excluded m hm H S ha hab (fun h => hnab h.2)⟩
      · refine ⟨b, hSuniv ▸ Set.mem_univ b,
          encard_le_two_of_excluded m hm H S hb hab.symm (fun h => hnab ?_)⟩
        exact (H.adj_comm b a).mp h.2
    case neg =>
      -- `S = {v}ᶜ`: the probe vertex lies in `S` and is adjacent to `v ∉ S`.
      have hpS : probeVtx m ∈ S := by
        by_contra hcon
        exact probeVtx_ne_v m (hout _ hcon)
      exact ⟨probeVtx m, hpS, encard_le_two_of_excluded m hm H S (probeVtx_ne_v m)
        (probeVtx_adj_v m) (fun h => hv h.1)⟩

/-! ### Assembly -/

/-- **Proposition 4.6**, degeneracy half: every proper subgraph of `Gₘ` is 2-degenerate. -/
theorem proper_subgraph_isTwoDegenerate (m : ℕ) (hm : 1 ≤ m) (H : (G m).Subgraph) (hne : H ≠ ⊤) :
    IsTwoDegenerate H.coe := by
  refine isTwoDegenerate_of_forall_set ?_
  intro s hs
  obtain ⟨x, hx⟩ := hs
  obtain ⟨p, hpS, hpcard⟩ := master m hm H hne (Subtype.val '' s) ⟨x.1, x, hx, rfl⟩
    (by rintro _ ⟨y, -, rfl⟩; exact y.2)
  obtain ⟨u, hus, rfl⟩ := hpS
  refine ⟨u, hus, ?_⟩
  have hsub : Subtype.val '' {z | z ∈ s ∧ H.coe.Adj u z} ⊆
      {z | z ∈ Subtype.val '' s ∧ H.Adj u.1 z} := by
    rintro _ ⟨z, ⟨hzs, hadj⟩, rfl⟩
    exact ⟨⟨z, hzs, rfl⟩, hadj⟩
  calc ({z | z ∈ s ∧ H.coe.Adj u z}).encard
      = (Subtype.val '' {z | z ∈ s ∧ H.coe.Adj u z}).encard :=
        (Subtype.val_injective.encard_image _).symm
    _ ≤ _ := Set.encard_le_encard hsub
    _ ≤ 2 := hpcard

/-- Any non-empty proper subgraph of `Gₘ` has a vertex of degree at most 2. This is the
statement as the paper phrases it ("minimum degree at most 2"); the hereditary version above is
what the greedy colouring actually consumes. -/
theorem exists_degree_le_two (m : ℕ) (hm : 1 ≤ m) (H : (G m).Subgraph) (hne : H ≠ ⊤)
    (hverts : H.verts.Nonempty) :
    ∃ u : H.verts, (H.coe.neighborSet u : Set H.verts).encard ≤ 2 := by
  obtain ⟨x, hx⟩ := hverts
  obtain ⟨u, -, hu⟩ := exists_mem_encard_le_two
    (proper_subgraph_isTwoDegenerate m hm H hne) Set.univ ⟨⟨x, hx⟩, trivial⟩
  refine ⟨u, ?_⟩
  have : {z | z ∈ (Set.univ : Set H.verts) ∧ H.coe.Adj u z}
      = (H.coe.neighborSet u : Set H.verts) := by
    ext z; simp [SimpleGraph.mem_neighborSet]
  rwa [this] at hu

/-- **Proposition 4.6.** Every proper subgraph of `Gₘ` has chromatic number at most 3. -/
theorem proper_subgraph_chromaticNumber_le_three (m : ℕ) (hm : 1 ≤ m)
    (H : (G m).Subgraph) (hne : H ≠ ⊤) :
    H.coe.chromaticNumber ≤ 3 := by
  classical
  have : Fintype ↥H.verts := (Set.toFinite H.verts).fintype
  exact (colorable_three_of_isTwoDegenerate
    (proper_subgraph_isTwoDegenerate m hm H hne)).chromaticNumber_le

end Erdos1091

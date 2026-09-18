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

import Erdos1091.CliqueFree
import Erdos1091.Chords
import Erdos1091.Coloring
import Erdos1091.Degenerate

/-!
# Theorem 4.1 and the Erdos 1091 counterexample

All of the mathematics is carried out on the structured vertex type `Vtx m`, where the block
decomposition is visible. The target statement (from formal-conjectures PR #5870) asks for a
graph on `Fin n`, so we transport exactly once, at the very end, along an equivalence
`Vtx m ~ Fin (20 * m + 31)` obtained from the cardinality computation `card_vtx`.

## The transport lemmas

Mathlib has the `CliqueFree` and `chromaticNumber` halves already
(`SimpleGraph.cliqueFree_map_iff`, `SimpleGraph.chromaticNumber_congr`); the subgraph condition
and the chord bound are **not** in Mathlib and are proved here. Both are stated for a general
graph isomorphism `H ~g H'`, which is the reusable form, and then specialised to
`H.map e.toEmbedding` because that is the shape the assembly consumes:

* `subgraph_chromaticNumber_congr` pulls a subgraph `K` of `H'` back to `K.comap` along the
  isomorphism. Note that Mathlib's `Subgraph.comap` carries an extra `H.Adj` conjunct in its
  adjacency, which is what supplies the first component of the `map_rel_iff'` field below.
* `cycle_chords_congr` pushes a cycle of `H'` back along the inverse isomorphism and shows the
  image of its chord set lands inside the chord set of the pulled-back cycle. Only the "into"
  direction is needed for an upper bound.

These two are general-purpose statements about arbitrary graphs, new in this development; they
are candidates for upstreaming independently of Erdos 1091.

## The constant `C`

`C = 51` works: `20m + 31 <= 51m` exactly when `m >= 1`, which is the hypothesis we are given,
and `m <= 20m + 31` holds always. Any `C >= 51` would do; `51` is the smallest that `omega`
discharges directly from `1 <= m`.

## Credit

The mathematics of Section 4 -- the construction of `G_m` and all of the proofs -- is due to
Alexeev, Putterman, Sawhney, Sellke and Valiant [APSSV26b]; **prover credit is theirs**. What is
claimed here is **formalizer credit** for the Lean development.

## References

* [APSSV26b] arXiv:2604.06609, Theorem 4.1.
-/

namespace Erdos1091

open SimpleGraph

variable {m : ℕ}

/-! ### General-purpose transport lemmas -/

/-- Transport of `CliqueFree` along an equivalence. This one is already in Mathlib as
`cliqueFree_map_iff`; it is restated here so that the four transport steps of the assembly read
uniformly. -/
theorem cliqueFree_map_equiv {V W : Type*} [Nonempty V] (e : V ≃ W) {H : SimpleGraph V} {k : ℕ}
    (h : H.CliqueFree k) : (H.map e.toEmbedding).CliqueFree k :=
  cliqueFree_map_iff.mpr h

/-- Transport of the chromatic number along an equivalence. -/
theorem chromaticNumber_map_equiv {V W : Type*} (e : V ≃ W) (H : SimpleGraph V) :
    (H.map e.toEmbedding).chromaticNumber = H.chromaticNumber :=
  (chromaticNumber_congr (Iso.map e H)).symm

theorem subgraph_chromaticNumber_congr {V W : Type*} {H : SimpleGraph V} {H' : SimpleGraph W}
    (φ : H ≃g H') (n : ℕ)
    (h : ∀ K : H.Subgraph, K ≠ ⊤ → K.coe.chromaticNumber ≤ n) :
    ∀ K : H'.Subgraph, K ≠ ⊤ → K.coe.chromaticNumber ≤ n := by
  intro K hK
  have hne : (K.comap φ.toHom) ≠ ⊤ := by
    intro htop
    apply hK
    have hv : ∀ u : V, φ u ∈ K.verts := by
      intro u
      have hu : u ∈ (K.comap φ.toHom).verts := by rw [htop]; trivial
      exact hu
    have ha : ∀ u v : V, H.Adj u v → K.Adj (φ u) (φ v) := by
      intro u v huv
      have hu : (K.comap φ.toHom).Adj u v := by rw [htop]; exact huv
      exact hu.2
    ext x y
    · simp only [Subgraph.verts_top, Set.mem_univ, iff_true]
      have hx := hv (φ.symm x)
      simpa using hx
    · simp only [Subgraph.top_adj]
      constructor
      · exact fun hxy => K.adj_sub hxy
      · intro hxy
        have hsym : H.Adj (φ.symm x) (φ.symm y) := by
          have : H'.Adj (φ (φ.symm x)) (φ (φ.symm y)) := by simpa using hxy
          exact (φ.map_rel_iff).1 this
        have := ha _ _ hsym
        simpa using this
  have hiso : (K.comap φ.toHom).coe ≃g K.coe := by
    refine ⟨⟨fun u => ⟨φ u.1, u.2⟩, fun w => ⟨φ.symm w.1, ?_⟩, ?_, ?_⟩, ?_⟩
    · show φ (φ.symm w.1) ∈ K.verts
      simp
    · rintro ⟨u, hu⟩
      apply Subtype.ext
      simp
    · rintro ⟨w, hw⟩
      apply Subtype.ext
      simp
    · rintro ⟨u, hu⟩ ⟨v, hv⟩
      show K.Adj (φ u) (φ v) ↔ (H.Adj u v ∧ K.Adj (φ u) (φ v))
      constructor
      · intro hadj
        exact ⟨(φ.map_rel_iff).1 (K.adj_sub hadj), hadj⟩
      · exact fun hadj => hadj.2
  rw [← SimpleGraph.chromaticNumber_congr hiso]
  exact h _ hne

/-- Transport of the "every proper subgraph is 3-colorable" condition along an equivalence. -/
theorem subgraph_chromaticNumber_map_equiv {V W : Type*} (e : V ≃ W) (H : SimpleGraph V) {n : ℕ}
    (h : ∀ K : H.Subgraph, K ≠ ⊤ → K.coe.chromaticNumber ≤ n) :
    ∀ K : (H.map e.toEmbedding).Subgraph, K ≠ ⊤ → K.coe.chromaticNumber ≤ n :=
  subgraph_chromaticNumber_congr (Iso.map e H) n h

theorem cycle_chords_congr {V W : Type*} {H : SimpleGraph V} {H' : SimpleGraph W}
    (φ : H ≃g H') {k : ℕ}
    (h : ∀ c : Cycle H, c.chords.encard ≤ k) :
    ∀ c : Cycle H', c.chords.encard ≤ k := by
  intro c
  -- the inverse isomorphism, as a plain injective function
  have hinj : Function.Injective (φ.symm : W → V) := φ.symm.toEquiv.injective
  have hinj2 : Function.Injective (Sym2.map (φ.symm : W → V)) := Sym2.map.injective hinj
  -- pull back the cycle along `φ.symm`
  have hcyc : (c.walk.map φ.symm.toHom).IsCycle :=
    (SimpleGraph.Walk.isCycle_map_iff_of_injective hinj).mpr c.isCycle
  let c' : Cycle H := ⟨φ.symm c.base, c.walk.map φ.symm.toHom, hcyc⟩
  -- the image of the chords of `c` under `Sym2.map φ.symm` lies inside the chords of `c'`
  have hsub : Sym2.map (φ.symm : W → V) '' c.chords ⊆ c'.chords := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨hedge, hsupp, hnot⟩ := he
    refine ⟨?_, ?_, ?_⟩
    · exact (SimpleGraph.Iso.map_mem_edgeSet_iff φ.symm).mpr hedge
    · intro v hv
      rw [Sym2.mem_map] at hv
      obtain ⟨a, ha, rfl⟩ := hv
      have : a ∈ c.walk.support := hsupp a ha
      show φ.symm a ∈ (c.walk.map φ.symm.toHom).support
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map_of_mem this
    · intro hmem
      have hmem' : Sym2.map (φ.symm : W → V) e ∈
          c.walk.edges.map (Sym2.map (φ.symm : W → V)) := by
        have : Sym2.map (φ.symm : W → V) e ∈ (c.walk.map φ.symm.toHom).edges := hmem
        rwa [SimpleGraph.Walk.edges_map] at this
      obtain ⟨e0, he0, heq⟩ := List.mem_map.mp hmem'
      exact hnot (hinj2 heq ▸ he0)
  have hcard : (Sym2.map (φ.symm : W → V) '' c.chords).encard = c.chords.encard :=
    Set.InjOn.encard_image (hinj2.injOn)
  calc c.chords.encard = (Sym2.map (φ.symm : W → V) '' c.chords).encard := hcard.symm
    _ ≤ c'.chords.encard := Set.encard_le_encard hsub
    _ ≤ k := h c'

/-- Transport of the chord bound along an equivalence: an equivalence carries cycles to cycles
and chords to chords, so the bound is preserved. -/
theorem cycle_chords_map_equiv {V W : Type*} (e : V ≃ W) (H : SimpleGraph V) {k : ℕ}
    (h : ∀ c : Cycle H, c.chords.encard ≤ k) :
    ∀ c : Cycle (H.map e.toEmbedding), c.chords.encard ≤ k :=
  cycle_chords_congr (Iso.map e H) h

/-! ### The graph on `Fin (20m + 31)` -/

/-- The vertex type of `G_m` is equivalent to `Fin (20m + 31)`, by `card_vtx`. -/
noncomputable def vtxEquiv (m : ℕ) (hm : 1 ≤ m) : Vtx m ≃ Fin (20 * m + 31) :=
  Fintype.equivFinOfCardEq (card_vtx m hm)

/-- `G_m` transported onto `Fin (20m + 31)`; this is the graph the target statement asks for. -/
noncomputable def Gfin (m : ℕ) (hm : 1 ≤ m) : SimpleGraph (Fin (20 * m + 31)) :=
  (G m).map (vtxEquiv m hm).toEmbedding

/-! ### Theorem 4.1 -/

/-- The size bounds `m <= 20m + 31 <= 51m` for `m >= 1`, giving the constant `C = 51`. -/
theorem size_bounds (m : ℕ) (hm : 1 ≤ m) : m ≤ 20 * m + 31 ∧ 20 * m + 31 ≤ 51 * m := by
  omega

/-- **Theorem 4.1.** For every `m >= 1` the graph `G_m` on `20m + 31` vertices is `K4`-free, has
chromatic number 4, has all proper subgraphs 3-colorable, and every cycle has at most 10
chords.

Each of the four conjuncts is one of the Section 4 results transported along `vtxEquiv`:
Lemma 4.2, Proposition 4.5, Proposition 4.6 and Proposition 4.10 respectively. -/
theorem theorem_4_1 (m : ℕ) (hm : 1 ≤ m) :
    (Gfin m hm).CliqueFree 4 ∧
    (Gfin m hm).chromaticNumber = 4 ∧
    (∀ H : (Gfin m hm).Subgraph, H ≠ ⊤ → H.coe.chromaticNumber ≤ 3) ∧
    (∀ c : Cycle (Gfin m hm), c.chords.encard ≤ 10) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cliqueFree_map_equiv (vtxEquiv m hm) (G_cliqueFree_four m)
  · exact (chromaticNumber_map_equiv (vtxEquiv m hm) (G m)).trans (G_chromaticNumber m hm)
  · exact subgraph_chromaticNumber_map_equiv (vtxEquiv m hm) (G m)
      (proper_subgraph_chromaticNumber_le_three m hm)
  · exact cycle_chords_map_equiv (vtxEquiv m hm) (G m) (cycle_chords_le_ten m hm)

/-- **The target statement**, verbatim from formal-conjectures PR #5870
(`FormalConjectures/ErdosProblems/1091.lean`).

An internal OpenAI model (see [APSSV26b]) gave a negative answer to Erdos' question: for every
`m >= 1` there is a `K4`-free graph on about `m` vertices with chromatic number 4, every proper
subgraph 3-colorable, and every cycle carrying at most 10 chords. -/
theorem erdos_1091.variants.counterexample :
    ∃ C : ℕ, ∀ m : ℕ, 1 ≤ m →
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        m ≤ n ∧ n ≤ C * m ∧ G.CliqueFree 4 ∧ G.chromaticNumber = 4 ∧
          (∀ H : G.Subgraph, H ≠ ⊤ → H.coe.chromaticNumber ≤ 3) ∧
          (∀ c : G.Cycle, c.chords.encard ≤ 10) := by
  refine ⟨51, fun m hm => ⟨20 * m + 31, Gfin m hm, (size_bounds m hm).1, (size_bounds m hm).2, ?_⟩⟩
  obtain ⟨h1, h2, h3, h4⟩ := theorem_4_1 m hm
  exact ⟨h1, h2, h3, h4⟩

end Erdos1091

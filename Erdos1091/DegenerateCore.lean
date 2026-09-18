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

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card

/-!
# 2-degenerate graphs are 3-colorable

This is a **general-purpose graph-theory lemma built specifically for this formalization**; it is
*not* available in Mathlib.  At the time of writing Mathlib contains no notion of graph degeneracy
and no greedy-colouring theorem (`Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex` only relates
`Colorable` to cliques, homomorphisms and the chromatic number), so everything below is proved from
scratch.

## Main definitions

* `Erdos1091.IsTwoDegenerate`: every non-empty subgraph has a vertex of degree at most `2`.

## Main results

* `Erdos1091.colorable_three_of_isTwoDegenerate`: a 2-degenerate graph on a finite vertex type is
  `3`-colorable.

## Implementation notes

Fighting `SimpleGraph.Subgraph.coe` throughout an induction is painful, so we immediately convert
`IsTwoDegenerate` into the equivalent "`Finset`-indexed" statement
`∀ s : Finset V, s.Nonempty → ∃ u ∈ s, {v ∈ s | H.Adj u v}` has at most two elements
(see `Erdos1091.exists_mem_encard_le_two`), by instantiating the subgraph quantifier at
`(⊤ : H.Subgraph).induce s`.  The greedy colouring is then a plain strong induction on the
cardinality of a `Finset`, which never leaves the ambient type `V` and therefore needs no transport
of `IsTwoDegenerate` along induced subgraphs.
-/

namespace Erdos1091

open SimpleGraph

/-- A graph is 2-degenerate when every non-empty subgraph has a vertex of degree at most 2. -/
def IsTwoDegenerate {V : Type*} (H : SimpleGraph V) : Prop :=
  ∀ K : H.Subgraph, K.verts.Nonempty →
    ∃ u : K.verts, (K.coe.neighborSet u : Set K.verts).encard ≤ 2

variable {V : Type*} {H : SimpleGraph V}

/-- The `Set`-indexed form of 2-degeneracy: every non-empty set of vertices contains a vertex with
at most two neighbours inside that set.  This is obtained from `IsTwoDegenerate` by instantiating
the subgraph quantifier at the subgraph of `H` induced on the given set. -/
theorem exists_mem_encard_le_two (h : IsTwoDegenerate H) (s : Set V) (hs : s.Nonempty) :
    ∃ u ∈ s, {v | v ∈ s ∧ H.Adj u v}.encard ≤ 2 := by
  obtain ⟨u, hu⟩ := h ((⊤ : H.Subgraph).induce s) hs
  refine ⟨u.1, u.2, ?_⟩
  have himg : {v | v ∈ s ∧ H.Adj u.1 v} =
      Subtype.val '' (((⊤ : H.Subgraph).induce s).coe.neighborSet u) := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_image, SimpleGraph.mem_neighborSet,
      SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj]
    constructor
    · rintro ⟨hv, hadj⟩
      exact ⟨⟨v, hv⟩, ⟨u.2, hv, hadj⟩, rfl⟩
    · rintro ⟨w, ⟨_, hw, hadj⟩, rfl⟩
      exact ⟨hw, hadj⟩
  rw [himg, Subtype.val_injective.encard_image]
  exact hu

/-- Greedy colouring: if `H` is 2-degenerate then every finite set of vertices of cardinality at
most `n` carries a proper `3`-colouring (extended arbitrarily to the rest of `V`). -/
private theorem greedy [DecidableEq V] (h : IsTwoDegenerate H) :
    ∀ n : ℕ, ∀ s : Finset V, s.card ≤ n →
      ∃ C : V → Fin 3, ∀ u ∈ s, ∀ v ∈ s, H.Adj u v → C u ≠ C v := by
  intro n
  induction n with
  | zero =>
    intro s hs
    obtain rfl : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
    exact ⟨fun _ => 0, by simp⟩
  | succ n ih =>
    intro s hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, by simp⟩
    obtain ⟨u, hus, hN⟩ := exists_mem_encard_le_two h (↑s) (Finset.coe_nonempty.mpr hne)
    -- the smaller set, obtained by deleting the low-degree vertex `u`
    have hcard : (s.erase u).card ≤ n := by
      have h1 : (s.erase u).card = s.card - 1 := Finset.card_erase_of_mem hus
      have h2 : 1 ≤ s.card := Finset.card_pos.mpr hne
      omega
    obtain ⟨C', hC'⟩ := ih (s.erase u) hcard
    -- at most two colours occur on the neighbours of `u` inside `s`, so some colour is free
    obtain ⟨c, hc⟩ : ∃ c : Fin 3, c ∉ C' '' {v | v ∈ (↑s : Set V) ∧ H.Adj u v} := by
      by_contra hcon
      push Not at hcon
      have h1 : (Set.univ : Set (Fin 3)) ⊆ C' '' {v | v ∈ (↑s : Set V) ∧ H.Adj u v} :=
        fun c _ => hcon c
      have h2 := (Set.encard_le_encard h1).trans
        ((Set.encard_image_le C' {v | v ∈ (↑s : Set V) ∧ H.Adj u v}).trans hN)
      rw [Set.encard_univ] at h2
      simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at h2
      exact absurd h2 (by decide)
    have key : ∀ y, y ∈ s → H.Adj u y → C' y ≠ c := fun y hy hadj heq =>
      hc ⟨y, ⟨Finset.mem_coe.mpr hy, hadj⟩, heq⟩
    refine ⟨Function.update C' u c, ?_⟩
    intro x hx y hy hadj
    by_cases h1 : x = u
    · by_cases h2 : y = u
      · exact absurd (h1.trans h2.symm) hadj.ne
      · rw [Function.update_apply, Function.update_apply, if_pos h1, if_neg h2]
        subst h1
        exact fun hcc => key y hy hadj hcc.symm
    · by_cases h2 : y = u
      · rw [Function.update_apply, Function.update_apply, if_neg h1, if_pos h2]
        subst h2
        exact fun hcc => key x hx hadj.symm hcc
      · rw [Function.update_apply, Function.update_apply, if_neg h1, if_neg h2]
        exact hC' x (Finset.mem_erase.mpr ⟨h1, hx⟩) y (Finset.mem_erase.mpr ⟨h2, hy⟩) hadj

/-- **A 2-degenerate graph on a finite vertex type is 3-colorable.** -/
theorem colorable_three_of_isTwoDegenerate {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} (h : IsTwoDegenerate H) : H.Colorable 3 := by
  obtain ⟨C, hC⟩ := greedy h (Finset.univ : Finset V).card Finset.univ le_rfl
  exact ⟨SimpleGraph.Coloring.mk C fun {v w} hvw =>
    hC v (Finset.mem_univ v) w (Finset.mem_univ w) hvw⟩

end Erdos1091

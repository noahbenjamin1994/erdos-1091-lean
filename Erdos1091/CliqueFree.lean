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
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Lemma 4.2: `Gₘ` is `K₄`-free

The paper argues in two halves: `G'ₘ = Gₘ \ {v}` is triangle-free, so a `K₄` would have to
contain `v`; and the neighbourhood `N(v)` is a disjoint union of 4-vertex paths (one per leaf
block), hence triangle-free, so `v` cannot lie in a `K₄` either.

**In Lean the second half is subsumed by the first.** The only edges of `Gₘ` that are not edges
of `G'ₘ` are the edges at `v` itself (`Erdos1091.G_adj_mk_mk`). A `K₄` has four vertices, at
most one of which is `v`, so it contains three vertices other than `v`, and those three are
pairwise `G'ₘ`-adjacent — a triangle of `G'ₘ`. So triangle-freeness of `G'ₘ` alone finishes the
proof, and no analysis of the path structure of `N(v)` is needed.

We nevertheless record the paper's intermediate statement as
`Erdos1091.neighbor_v_cliqueFree_three`, since it is the form a reader of the paper will look
for; it too is a corollary of `Erdos1091.G'_cliqueFree_three`.

Triangle-freeness of `G'ₘ` itself splits along how many distinct blocks the triangle meets:

* **One block** — the three vertices are pairwise rim-adjacent inside one pentagon, which
  `Erdos1091.no_rim_triangle` rules out (a 5-cycle is triangle-free).
* **Two blocks** — two of the vertices lie in a common block `b` and both are joined to the
  third, in a block `b' ≠ b`. But the inter-block edge between a given pair of blocks is
  *unique*, so those two vertices would coincide (`Erdos1091.two_in_one_block`).
* **Three blocks** — the "block graph" of the caterpillar would contain a triangle. A leaf
  block has exactly one block-neighbour (its own spine block), so all three blocks would be
  spine blocks `S_i, S_j, S_k` with indices pairwise differing by exactly one, which is
  arithmetically impossible (`Erdos1091.no_block_triangle`).

## References

* [APSSV26b] arXiv:2604.06609, Lemma 4.2.
-/

namespace Erdos1091

open SimpleGraph

variable {m : ℕ}

/-! ### Two small structural helpers -/

/-- A rim edge joins two slots of one and the same block. -/
lemma block_eq_of_rimAdjVB {b₁ b₂ : ValidBlock m} {s₁ s₂ : Slot}
    (h : rimAdjVB (Vtx.mk b₁ s₁) (Vtx.mk b₂ s₂) = true) : b₁ = b₂ := by
  simp only [rimAdjVB, Vtx.mk, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- Every block is either a spine block or a leaf block. -/
lemma ValidBlock.cases' (b : ValidBlock m) :
    (∃ i : Fin (m + 1), b.val = Block.spine i) ∨
      (∃ (i : Fin (m + 1)) (x : Slot), b.val = Block.leaf i x) := by
  obtain ⟨b, hb⟩ := b
  cases b with
  | spine i => exact Or.inl ⟨i, rfl⟩
  | leaf i x => exact Or.inr ⟨i, x, rfl⟩

/-! ### Inter-block edges are unique between a given pair of blocks -/

/-- The slot at which a block meets a given neighbouring block. For a leaf block `L_{i,x}` the
attachment slot is `x` regardless of the other block; for a spine block it is `c` towards the
*next* spine block and `a` towards the previous one, and `x` towards a leaf `L_{i,x}`.

The value on non-adjacent pairs is irrelevant — the point of this function is
`Erdos1091.slots_of_interAdjVB`: the slots of an inter-block edge are determined by the two
blocks it joins, which is exactly what makes such an edge unique. -/
def Block.attachSlot : Block m → Block m → Slot
  | .leaf _ x, _ => x
  | .spine _, .leaf _ x => x
  | .spine i, .spine j => if (i : ℕ) + 1 = (j : ℕ) then Slot.c else Slot.a

/-- The slots of an inter-block edge are determined by the pair of blocks it joins. -/
lemma slots_of_interAdjVB {b b' : ValidBlock m} {s s' : Slot}
    (h : interAdjVB (Vtx.mk b s) (Vtx.mk b' s') = true) :
    s = Block.attachSlot b.val b'.val ∧ s' = Block.attachSlot b'.val b.val := by
  rw [interAdjVB_mk_mk_iff] at h
  rcases h with ⟨i, x, hb, hb', rfl, rfl⟩ | ⟨i, j, hb, hb', hij, rfl, rfl⟩
  · rw [hb, hb']; exact ⟨rfl, rfl⟩
  · rw [hb, hb']
    refine ⟨?_, ?_⟩
    · simp [Block.attachSlot, hij]
    · have : (j : ℕ) + 1 ≠ (i : ℕ) := by omega
      simp [Block.attachSlot, this]

/-- **Cross edges are inter-block edges.** Two adjacent vertices of `G'ₘ` lying in different
blocks are joined by an inter-block edge (in one orientation or the other); the rim relation
can only join vertices of one and the same block. -/
theorem G'_adj_of_ne_block {u w : Vtx m} {b₁ b₂ : ValidBlock m} {s₁ s₂ : Slot}
    (hu : u = Vtx.mk b₁ s₁) (hw : w = Vtx.mk b₂ s₂) (hne : b₁ ≠ b₂)
    (hadj : (G' m).Adj u w) :
    interAdjVB u w = true ∨ interAdjVB w u = true := by
  subst hu hw
  obtain ⟨-, h | h⟩ := hadj
  · rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact absurd (block_eq_of_rimAdjVB h') hne
    · exact Or.inl h'
  · rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact absurd (block_eq_of_rimAdjVB h').symm hne
    · exact Or.inr h'

/-- The slots of a `G'ₘ`-edge between two *different* blocks are determined by those blocks.
Note the conclusion is symmetric in the two endpoints, so it does not matter which orientation
the underlying inter-block edge has. -/
lemma slots_of_G'_adj_ne_block {b b' : ValidBlock m} {s s' : Slot} (hne : b ≠ b')
    (h : (G' m).Adj (Vtx.mk b s) (Vtx.mk b' s')) :
    s = Block.attachSlot b.val b'.val ∧ s' = Block.attachSlot b'.val b.val := by
  rcases G'_adj_of_ne_block rfl rfl hne h with h' | h'
  · exact slots_of_interAdjVB h'
  · exact (slots_of_interAdjVB h').symm

/-- **There is at most one inter-block edge between two blocks.** Hence two *distinct* vertices
of one block cannot have a common neighbour outside that block. -/
lemma two_in_one_block {b b' : ValidBlock m} {s t s' : Slot} (hne : b ≠ b') (hst : s ≠ t)
    (h₁ : (G' m).Adj (Vtx.mk b s) (Vtx.mk b' s'))
    (h₂ : (G' m).Adj (Vtx.mk b t) (Vtx.mk b' s')) : False :=
  hst <| (slots_of_G'_adj_ne_block hne h₁).1.trans (slots_of_G'_adj_ne_block hne h₂).1.symm

/-! ### The block graph of the caterpillar is triangle-free -/

/-- **A leaf block has exactly one block-neighbour: its own spine block.** This is the reason
the block graph has no triangles. -/
lemma spine_of_G'_adj_leaf {b b' : ValidBlock m} {s s' : Slot} {i : Fin (m + 1)} {x : Slot}
    (hb : b.val = Block.leaf i x) (hne : b ≠ b')
    (h : (G' m).Adj (Vtx.mk b s) (Vtx.mk b' s')) : b'.val = Block.spine i := by
  rcases G'_adj_of_ne_block rfl rfl hne h with h' | h' <;> rw [interAdjVB_mk_mk_iff] at h'
  · rcases h' with ⟨j, y, hb₁, hb₂, -, -⟩ | ⟨j, k, hb₁, -, -, -⟩
    · rw [hb] at hb₁; cases (Block.leaf.inj hb₁).1; exact hb₂
    · rw [hb] at hb₁; simp at hb₁
  · rcases h' with ⟨j, y, -, hb₂, -, -⟩ | ⟨j, k, -, hb₂, -, -, -⟩
    · rw [hb] at hb₂; simp at hb₂
    · rw [hb] at hb₂; simp at hb₂

/-- Two adjacent spine blocks have indices differing by exactly one. -/
lemma spine_adj_index {b b' : ValidBlock m} {s s' : Slot} {i j : Fin (m + 1)}
    (hb : b.val = Block.spine i) (hb' : b'.val = Block.spine j) (hne : b ≠ b')
    (h : (G' m).Adj (Vtx.mk b s) (Vtx.mk b' s')) :
    (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) := by
  rcases G'_adj_of_ne_block rfl rfl hne h with h' | h' <;> rw [interAdjVB_mk_mk_iff] at h'
  · rcases h' with ⟨k, y, hb₁, -, -, -⟩ | ⟨k, l, hb₁, hb₂, hkl, -, -⟩
    · rw [hb] at hb₁; simp at hb₁
    · rw [hb] at hb₁; rw [hb'] at hb₂
      cases Block.spine.inj hb₁; cases Block.spine.inj hb₂; exact Or.inl hkl
  · rcases h' with ⟨k, y, hb₁, -, -, -⟩ | ⟨k, l, hb₁, hb₂, hkl, -, -⟩
    · rw [hb'] at hb₁; simp at hb₁
    · rw [hb'] at hb₁; rw [hb] at hb₂
      cases Block.spine.inj hb₁; cases Block.spine.inj hb₂; exact Or.inr hkl

/-- **The block graph is triangle-free.** Three pairwise distinct, pairwise adjacent blocks
cannot exist: a leaf block has only one block-neighbour, so all three would be spine blocks,
and three spine indices cannot pairwise differ by exactly one. -/
lemma no_block_triangle {b₁ b₂ b₃ : ValidBlock m} {s₁ s₂ s₃ : Slot}
    (h12 : b₁ ≠ b₂) (h13 : b₁ ≠ b₃) (h23 : b₂ ≠ b₃)
    (a12 : (G' m).Adj (Vtx.mk b₁ s₁) (Vtx.mk b₂ s₂))
    (a13 : (G' m).Adj (Vtx.mk b₁ s₁) (Vtx.mk b₃ s₃))
    (a23 : (G' m).Adj (Vtx.mk b₂ s₂) (Vtx.mk b₃ s₃)) : False := by
  -- A leaf block among the three forces its two neighbours to be the *same* spine block,
  -- contradicting that those two are distinct. So all three blocks are spine blocks.
  obtain ⟨i, hi⟩ : ∃ i : Fin (m + 1), b₁.val = Block.spine i := by
    rcases b₁.cases' with h | ⟨i, x, hb⟩
    · exact h
    · exact absurd ((spine_of_G'_adj_leaf hb h12 a12).trans
        (spine_of_G'_adj_leaf hb h13 a13).symm) (fun h => h23 (Subtype.ext h))
  obtain ⟨j, hj⟩ : ∃ j : Fin (m + 1), b₂.val = Block.spine j := by
    rcases b₂.cases' with h | ⟨j, y, hb⟩
    · exact h
    · exact absurd ((spine_of_G'_adj_leaf hb (Ne.symm h12) a12.symm).trans
        (spine_of_G'_adj_leaf hb h23 a23).symm) (fun h => h13 (Subtype.ext h))
  obtain ⟨k, hk⟩ : ∃ k : Fin (m + 1), b₃.val = Block.spine k := by
    rcases b₃.cases' with h | ⟨k, z, hb⟩
    · exact h
    · exact absurd ((spine_of_G'_adj_leaf hb (Ne.symm h13) a13.symm).trans
        (spine_of_G'_adj_leaf hb (Ne.symm h23) a23.symm).symm) (fun h => h12 (Subtype.ext h))
  -- Three spine indices pairwise differing by one: impossible.
  have e12 := spine_adj_index hi hj h12 a12
  have e13 := spine_adj_index hi hk h13 a13
  have e23 := spine_adj_index hj hk h23 a23
  omega

/-! ### Triangle-freeness of `G'ₘ` and Lemma 4.2 -/

/-- Inside one pentagon, no three slots are pairwise rim-adjacent.

Enumeration size: `5³ = 125` slot triples, discharged by `decide` on the finite `Slot` type.
This is independent of `m`. -/
theorem no_rim_triangle (s t r : Slot) :
    ¬ (Slot.rimAdjB s t = true ∧ Slot.rimAdjB t r = true ∧ Slot.rimAdjB s r = true) := by
  revert s t r
  decide

/-- Every vertex incident to an edge of `G'ₘ` lies in a block (it is not `v`). -/
lemma exists_mk_of_G'_adj_left {u w : Vtx m} (h : (G' m).Adj u w) :
    ∃ (b : ValidBlock m) (s : Slot), u = Vtx.mk b s := by
  cases u with
  | none => exact absurd h (G'_not_adj_v w)
  | some p => exact ⟨p.1, p.2, rfl⟩

/-- A triangle of `G'ₘ`, written out on block coordinates, is impossible. -/
theorem G'_no_triangle (b₁ b₂ b₃ : ValidBlock m) (s₁ s₂ s₃ : Slot)
    (hu12 : Vtx.mk b₁ s₁ ≠ Vtx.mk b₂ s₂) (hu13 : Vtx.mk b₁ s₁ ≠ Vtx.mk b₃ s₃)
    (hu23 : Vtx.mk b₂ s₂ ≠ Vtx.mk b₃ s₃)
    (a12 : (G' m).Adj (Vtx.mk b₁ s₁) (Vtx.mk b₂ s₂))
    (a13 : (G' m).Adj (Vtx.mk b₁ s₁) (Vtx.mk b₃ s₃))
    (a23 : (G' m).Adj (Vtx.mk b₂ s₂) (Vtx.mk b₃ s₃)) : False := by
  have slot_ne : ∀ {b : ValidBlock m} {s t : Slot}, Vtx.mk b s ≠ Vtx.mk b t → s ≠ t := by
    intro b s t h hst; exact h (by rw [hst])
  by_cases h12 : b₁ = b₂
  · subst h12
    by_cases h13 : b₁ = b₃
    · -- One block: a rim triangle in a pentagon.
      subst h13
      exact no_rim_triangle s₁ s₂ s₃
        ⟨(G'_adj_same_block _ _ _).mp a12, (G'_adj_same_block _ _ _).mp a23,
          (G'_adj_same_block _ _ _).mp a13⟩
    · -- Two blocks: `s₁` and `s₂` would be the same attachment slot.
      exact two_in_one_block h13 (slot_ne hu12) a13 a23
  · by_cases h13 : b₁ = b₃
    · -- `b₁ = b₃ ≠ b₂`: the vertices in block `b₁` are `s₁` and `s₃`, both joined to `b₂`.
      subst h13
      exact two_in_one_block h12 (slot_ne hu13) a12 a23.symm
    · by_cases h23 : b₂ = b₃
      · -- `b₂ = b₃ ≠ b₁`: the vertices in block `b₂` are `s₂` and `s₃`, both joined to `b₁`.
        subst h23
        exact two_in_one_block (Ne.symm h12) (slot_ne hu23) a12.symm a13.symm
      · -- Three blocks: the block graph would have a triangle.
        exact no_block_triangle h12 h13 h23 a12 a13 a23

/-- `G'ₘ` is triangle-free: every pentagon is an induced 5-cycle, and the inter-block edges
form a tree on the blocks. -/
theorem G'_cliqueFree_three (m : ℕ) : (G' m).CliqueFree 3 := by
  intro t ht
  obtain ⟨u₁, u₂, u₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  have a12 : (G' m).Adj u₁ u₂ := ht.isClique (by simp) (by simp) h12
  have a13 : (G' m).Adj u₁ u₃ := ht.isClique (by simp) (by simp) h13
  have a23 : (G' m).Adj u₂ u₃ := ht.isClique (by simp) (by simp) h23
  obtain ⟨b₁, s₁, rfl⟩ := exists_mk_of_G'_adj_left a12
  obtain ⟨b₂, s₂, rfl⟩ := exists_mk_of_G'_adj_left a23
  obtain ⟨b₃, s₃, rfl⟩ := exists_mk_of_G'_adj_left a13.symm
  exact G'_no_triangle b₁ b₂ b₃ s₁ s₂ s₃ h12 h13 h23 a12 a13 a23

/-- The neighbours of `v` induce a triangle-free graph.

The paper identifies this induced graph precisely: in each leaf block `L_{i,x}` the neighbours
of `v` are the four vertices `L_{i,x}[Y]`, `Y ≠ X`, which form the 4-vertex path left after
deleting the attachment vertex from the pentagon, and distinct leaf blocks contribute
vertex-disjoint paths — so `N(v)` is a disjoint union of paths.

For `K₄`-freeness only triangle-freeness of `N(v)` is needed, and that already follows from
`Erdos1091.G'_cliqueFree_three`: every neighbour of `v` is distinct from `v`, and on such
vertices `Gₘ`-adjacency coincides with `G'ₘ`-adjacency. -/
theorem neighbor_v_cliqueFree_three (m : ℕ) :
    ((G m).induce ((G m).neighborSet (Vtx.v m))).CliqueFree 3 := by
  intro t ht
  -- Transport the clique along the inclusion `N(v) ↪ Vtx m` into `G'ₘ`.
  refine G'_cliqueFree_three m (t.map (Function.Embedding.subtype _)) ⟨?_, ?_⟩
  · intro u hu w hw hne
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Function.Embedding.coe_subtype] at hu hw
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨w', hw', rfl⟩ := hw
    have hadj : (G m).Adj u'.val w'.val :=
      ht.isClique hu' hw' (fun h => hne (by rw [h]))
    refine G'_adj_of_G_adj_of_ne_v hadj ?_ ?_
    · exact fun h => ((G m).ne_of_adj (u'.2)) h.symm
    · exact fun h => ((G m).ne_of_adj (w'.2)) h.symm
  · rw [Finset.card_map]; exact ht.card_eq

/-- **Lemma 4.2.** `Gₘ` is `K₄`-free.

A `K₄` contains at most one copy of `v`, hence three vertices other than `v`; those three are
pairwise `G'ₘ`-adjacent by `Erdos1091.G_adj_mk_mk`, contradicting
`Erdos1091.G'_cliqueFree_three`. -/
theorem G_cliqueFree_four (m : ℕ) : (G m).CliqueFree 4 := by
  intro t ht
  -- Drop `v` from the clique; at least three vertices survive.
  have hcard : 3 ≤ (t.erase (Vtx.v m)).card := by
    have h := Finset.pred_card_le_card_erase (s := t) (a := Vtx.v m)
    rw [ht.card_eq] at h
    omega
  obtain ⟨t', hsub, hcard'⟩ := Finset.exists_subset_card_eq hcard
  refine G'_cliqueFree_three m t' ⟨?_, hcard'⟩
  intro u hu w hw hne
  have hu' := hsub hu
  have hw' := hsub hw
  refine G'_adj_of_G_adj_of_ne_v
    (ht.isClique (Finset.mem_of_mem_erase hu') (Finset.mem_of_mem_erase hw') hne)
    (Finset.ne_of_mem_erase hu') (Finset.ne_of_mem_erase hw')

end Erdos1091

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

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum

/-!
# The graph `Gₘ` of Erdős problem 1091 (arXiv:2604.06609, Section 4)

`Gₘ` is a caterpillar of pentagonal blocks plus one special vertex `v`:

* **Spine blocks** `S₀, …, S_m`, each a 5-cycle with slots `a b c d e` in rim order.
* **Leaf blocks** `L_{i,x}`, each a 5-cycle with the same slot names. `S₀` carries leaves at
  `a, b, d, e`; each internal `S_i` carries leaves at `b, d, e`; `S_m` carries leaves at
  `b, c, d, e`. That is `4m + 6` blocks in total.
* **Inter-block edges** `S_i[x] — L_{i,x}[x]` (the leaf attaches at the slot naming it) and
  `S_i[c] — S_{i+1}[a]` along the spine.
* **The special vertex** `v` joins the four *non-attachment* vertices of every leaf block.

Every vertex except `v` has degree exactly 3, and `|V(Gₘ)| = 20m + 31`.

The endpoint asymmetry — `S₀` has no `c`-leaf, `S_m` has no `a`-leaf — is essential to
Lemma 4.4 and Proposition 4.5; it must not be "symmetrised away".

## Design notes

* Vertices are `Option (ValidBlock m × Slot)`, with `none` playing the role of `v`. Modelling
  the vertex type as an `Option` of a `Subtype` of a plain inductive means `DecidableEq` and
  `Fintype` are both inferred rather than hand-rolled, and proof irrelevance handles the
  membership proof inside `ValidBlock` for free.
* Adjacency is defined through `Bool`-valued predicates and `SimpleGraph.fromRel`. `fromRel`
  supplies symmetry and irreflexivity, and the `Bool` layer makes `DecidableRel` mechanical.
  Decidability is here to make `Fintype`/instance search go through — the mathematics is still
  proved structurally. Do **not** attempt `decide` on `Gₘ` itself: `m` is a parameter and the
  vertex count `20m + 31` is unbounded.
* The `Fintype` instances are built from explicit `Equiv`s rather than `deriving Fintype`:
  the deriving handler for `Fintype` is not available here, and `Fintype.ofInjective` is
  noncomputable, which would block the `DecidableRel` instances downstream.

## References

* [APSSV26b] Alexeev, Putterman, Sawhney, Sellke, Valiant, *Short proofs in combinatorics,
  probability and number theory II*, arXiv:2604.06609, Section 4.
-/

namespace Erdos1091

/-- A position inside a pentagon, in rim order `a → b → c → d → e → a`.

Spine and leaf blocks share these names. The paper writes leaf slots in uppercase
(`A B C D E`); "the uppercase version of `x`" is here literally `x` again, so the leaf
block `L_{i,x}` attaches to the spine at its own slot `x`. -/
inductive Slot
  | a | b | c | d | e
  deriving DecidableEq, Repr

namespace Slot

instance : Fintype Slot where
  elems := {Slot.a, Slot.b, Slot.c, Slot.d, Slot.e}
  complete := by intro x; cases x <;> decide

@[simp]
theorem card_eq : Fintype.card Slot = 5 := by decide

/-- The next slot in rim order. -/
def succ : Slot → Slot
  | a => b | b => c | c => d | d => e | e => a

/-- Rim adjacency inside one pentagon: `s` and `t` are consecutive on the 5-cycle. -/
def rimAdjB (s t : Slot) : Bool := (succ s == t) || (succ t == s)

/-- Rim adjacency is symmetric. -/
theorem rimAdjB_comm (s t : Slot) : rimAdjB s t = rimAdjB t s := by
  cases s <;> cases t <;> rfl

/-- No slot is rim-adjacent to itself: the pentagon has no loops.
Enumeration size: 5 cases. -/
theorem rimAdjB_irrefl (s : Slot) : rimAdjB s s = false := by
  cases s <;> rfl

end Slot

/-- A block of the caterpillar, before validity is imposed: either the `i`-th spine
pentagon, or the leaf pentagon hanging off slot `x` of the `i`-th spine pentagon. -/
inductive Block (m : ℕ)
  | spine (i : Fin (m + 1))
  | leaf (i : Fin (m + 1)) (x : Slot)
  deriving DecidableEq

namespace Block

/-- `Block m ≃ Fin (m+1) ⊕ (Fin (m+1) × Slot)`, used to get a computable `Fintype`. -/
def equivSum (m : ℕ) : Block m ≃ Fin (m + 1) ⊕ (Fin (m + 1) × Slot) where
  toFun b := match b with | .spine i => .inl i | .leaf i x => .inr (i, x)
  invFun s := match s with | .inl i => .spine i | .inr (i, x) => .leaf i x
  left_inv b := by cases b <;> rfl
  right_inv s := by rcases s with i | ⟨i, x⟩ <;> rfl

instance (m : ℕ) : Fintype (Block m) := Fintype.ofEquiv _ (equivSum m).symm

/-- Which leaf blocks actually exist: `b`, `d`, `e` always; an `a`-leaf only on `S₀`; a
`c`-leaf only on `S_m`. For `m ≥ 1` this gives `S₀` four leaves, each internal block three,
and `S_m` four. -/
def validB {m : ℕ} : Block m → Bool
  | .spine _ => true
  | .leaf i x =>
    match x with
    | .a => (i : ℕ) = 0
    | .c => (i : ℕ) = m
    | _ => true

end Block

/-- The blocks of the caterpillar. There are `4m + 6` of them (`Erdos1091.card_validBlock`). -/
abbrev ValidBlock (m : ℕ) := {b : Block m // b.validB = true}

/-- Vertices of `Gₘ`: a slot inside a block, or the special vertex `v` (`none`). -/
abbrev Vtx (m : ℕ) := Option (ValidBlock m × Slot)

namespace Vtx

/-- The special vertex `v`, adjacent to every non-attachment vertex of every leaf block. -/
def v (m : ℕ) : Vtx m := none

/-- The vertex at slot `s` of block `b`. -/
def mk {m : ℕ} (b : ValidBlock m) (s : Slot) : Vtx m := some (b, s)

end Vtx

variable {m : ℕ}

/-- Rim edges: two slots of one and the same block, consecutive on that pentagon. -/
def rimAdjVB (u w : Vtx m) : Bool :=
  match u, w with
  | some (b₁, s₁), some (b₂, s₂) => (b₁ == b₂) && Slot.rimAdjB s₁ s₂
  | _, _ => false

/-- Inter-block edges, oriented: `L_{i,x}[x] → S_i[x]` (leaf to its spine block) and
`S_i[c] → S_{i+1}[a]` (along the spine). `SimpleGraph.fromRel` symmetrises. -/
def interAdjVB (u w : Vtx m) : Bool :=
  match u, w with
  | some (b₁, s₁), some (b₂, s₂) =>
    match b₁.val, b₂.val with
    | .leaf i x, .spine j => (i == j) && (s₁ == x) && (s₂ == x)
    | .spine i, .spine j => ((i : ℕ) + 1 == (j : ℕ)) && (s₁ == Slot.c) && (s₂ == Slot.a)
    | _, _ => false
  | _, _ => false

/-- Edges of `G'ₘ = Gₘ \ {v}`: rim edges together with inter-block edges. -/
def blockAdjVB (u w : Vtx m) : Bool := rimAdjVB u w || interAdjVB u w

/-- Edges at the special vertex, oriented `v → L_{i,x}[y]` for every `y ≠ x`. -/
def specialAdjVB (u w : Vtx m) : Bool :=
  match u, w with
  | none, some (b, s) =>
    match b.val with
    | .leaf _ x => !(s == x)
    | .spine _ => false
  | _, _ => false

/-- Edges of `Gₘ`, oriented. -/
def rawAdjVB (u w : Vtx m) : Bool := blockAdjVB u w || specialAdjVB u w

/-- `G'ₘ := Gₘ \ {v}`: the tree of pentagons. The special vertex is isolated here, which is
the same thing as deleting it for every statement we need (it lies on no cycle and we only
ever ask about reachability between non-special vertices). -/
def G' (m : ℕ) : SimpleGraph (Vtx m) := SimpleGraph.fromRel (fun u w => blockAdjVB u w = true)

/-- The graph `Gₘ` of Theorem 4.1. -/
def G (m : ℕ) : SimpleGraph (Vtx m) := SimpleGraph.fromRel (fun u w => rawAdjVB u w = true)

instance : DecidableRel (G m).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidableRel (G' m).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

@[simp]
lemma G_adj (u w : Vtx m) :
    (G m).Adj u w ↔ u ≠ w ∧ (rawAdjVB u w = true ∨ rawAdjVB w u = true) := Iff.rfl

@[simp]
lemma G'_adj (u w : Vtx m) :
    (G' m).Adj u w ↔ u ≠ w ∧ (blockAdjVB u w = true ∨ blockAdjVB w u = true) := Iff.rfl

/-- `G'ₘ` is a subgraph of `Gₘ`: it uses the same edges minus those at `v`. -/
lemma G'_le_G : G' m ≤ G m := by
  intro u w h
  rw [G'_adj] at h
  rw [G_adj]
  refine ⟨h.1, ?_⟩
  rcases h.2 with h' | h'
  · exact Or.inl (by simp [rawAdjVB, h'])
  · exact Or.inr (by simp [rawAdjVB, h'])

/-! ### Basic adjacency interface

These lemmas are meant to be the *only* thing later files need to know about `rawAdjVB`,
`blockAdjVB`, `interAdjVB` and `specialAdjVB`. Unfolding those definitions again downstream
is a sign that an interface lemma is missing here. -/

@[simp] lemma rimAdjVB_none_left (w : Vtx m) : rimAdjVB (none : Vtx m) w = false := by
  cases w <;> rfl

@[simp] lemma rimAdjVB_none_right (u : Vtx m) : rimAdjVB u (none : Vtx m) = false := by
  cases u <;> rfl

@[simp] lemma interAdjVB_none_left (w : Vtx m) : interAdjVB (none : Vtx m) w = false := by
  cases w <;> rfl

@[simp] lemma interAdjVB_none_right (u : Vtx m) : interAdjVB u (none : Vtx m) = false := by
  cases u <;> rfl

@[simp] lemma blockAdjVB_none_left (w : Vtx m) : blockAdjVB (none : Vtx m) w = false := by
  simp [blockAdjVB]

@[simp] lemma blockAdjVB_none_right (u : Vtx m) : blockAdjVB u (none : Vtx m) = false := by
  simp [blockAdjVB]

@[simp] lemma specialAdjVB_some_left (b : ValidBlock m) (s : Slot) (w : Vtx m) :
    specialAdjVB (Vtx.mk b s) w = false := by
  cases w <;> rfl

@[simp] lemma specialAdjVB_none_right (u : Vtx m) : specialAdjVB u (none : Vtx m) = false := by
  cases u <;> rfl

/-- The special vertex is isolated in `G'ₘ`; deleting it and isolating it agree for every
statement we make about `G'ₘ`. -/
lemma G'_not_adj_v (w : Vtx m) : ¬ (G' m).Adj (Vtx.v m) w := by
  simp [G'_adj, Vtx.v]

/-- **The bridge between `Gₘ` and `G'ₘ`.** Two vertices *other than* `v` are adjacent in `Gₘ`
exactly when they are adjacent in `G'ₘ`: the edges at `v` are the only difference, and they all
have `v` as an endpoint.

This is what makes Lemma 4.2 short — a `K₄` in `Gₘ` has at least three non-`v` vertices, and
they form a triangle of `G'ₘ`, so the paper's separate analysis of `N(v)` is subsumed by
triangle-freeness of `G'ₘ`. -/
lemma G_adj_mk_mk (b₁ b₂ : ValidBlock m) (s₁ s₂ : Slot) :
    (G m).Adj (Vtx.mk b₁ s₁) (Vtx.mk b₂ s₂) ↔ (G' m).Adj (Vtx.mk b₁ s₁) (Vtx.mk b₂ s₂) := by
  simp [G_adj, G'_adj, rawAdjVB]

/-- Adjacency in `Gₘ` between two vertices neither of which is `v` is `G'ₘ`-adjacency. -/
lemma G'_adj_of_G_adj_of_ne_v {u w : Vtx m} (h : (G m).Adj u w)
    (hu : u ≠ Vtx.v m) (hw : w ≠ Vtx.v m) : (G' m).Adj u w := by
  obtain ⟨⟨b₁, s₁⟩, rfl⟩ : ∃ p, u = some p := by
    cases u with
    | none => exact absurd rfl hu
    | some p => exact ⟨p, rfl⟩
  obtain ⟨⟨b₂, s₂⟩, rfl⟩ : ∃ p, w = some p := by
    cases w with
    | none => exact absurd rfl hw
    | some p => exact ⟨p, rfl⟩
  exact (G_adj_mk_mk b₁ b₂ s₁ s₂).mp h

/-- Unfolding of `interAdjVB` on two block vertices: an inter-block edge is either a leaf
attaching to its own spine block at its own slot, or a spine edge `S_i[c] — S_{i+1}[a]`. -/
lemma interAdjVB_mk_mk_iff (b₁ b₂ : ValidBlock m) (s₁ s₂ : Slot) :
    interAdjVB (Vtx.mk b₁ s₁) (Vtx.mk b₂ s₂) = true ↔
      (∃ (i : Fin (m + 1)) (x : Slot),
          b₁.val = Block.leaf i x ∧ b₂.val = Block.spine i ∧ s₁ = x ∧ s₂ = x) ∨
      (∃ i j : Fin (m + 1), b₁.val = Block.spine i ∧ b₂.val = Block.spine j ∧
          (i : ℕ) + 1 = (j : ℕ) ∧ s₁ = Slot.c ∧ s₂ = Slot.a) := by
  obtain ⟨b₁, hb₁⟩ := b₁
  obtain ⟨b₂, hb₂⟩ := b₂
  cases b₁ <;> cases b₂ <;>
    simp only [interAdjVB, Vtx.mk, Bool.and_eq_true, beq_iff_eq, Block.leaf.injEq,
      Block.spine.injEq, reduceCtorEq, false_and, and_false, exists_false, or_false,
      false_or, exists_and_left, exists_eq_left', Bool.false_eq_true] <;>
    aesop

/-- An inter-block edge really does join two *different* blocks. Consequently, inside a single
block the only edges are the rim edges of that pentagon. -/
lemma ne_block_of_interAdjVB {b₁ b₂ : ValidBlock m} {s₁ s₂ : Slot}
    (h : interAdjVB (Vtx.mk b₁ s₁) (Vtx.mk b₂ s₂) = true) : b₁ ≠ b₂ := by
  rw [interAdjVB_mk_mk_iff] at h
  rintro rfl
  rcases h with ⟨i, x, h₁, h₂, -, -⟩ | ⟨i, j, h₁, h₂, hij, -, -⟩
  · rw [h₁] at h₂; simp at h₂
  · rw [h₁] at h₂
    cases Block.spine.inj h₂
    omega

/-- **Within one block, adjacency is rim adjacency.** A pentagon is an induced 5-cycle. -/
lemma G'_adj_same_block (b : ValidBlock m) (s₁ s₂ : Slot) :
    (G' m).Adj (Vtx.mk b s₁) (Vtx.mk b s₂) ↔ Slot.rimAdjB s₁ s₂ = true := by
  constructor
  · rintro ⟨-, h | h⟩
    · rcases Bool.or_eq_true_iff.mp h with h' | h'
      · simpa [rimAdjVB, Vtx.mk] using h'
      · exact absurd rfl (ne_block_of_interAdjVB h')
    · rcases Bool.or_eq_true_iff.mp h with h' | h'
      · rw [Slot.rimAdjB_comm]; simpa [rimAdjVB, Vtx.mk] using h'
      · exact absurd rfl (ne_block_of_interAdjVB h')
  · intro h
    refine ⟨?_, Or.inl ?_⟩
    · simp only [ne_eq, Vtx.mk, Option.some.injEq, Prod.mk.injEq, true_and]
      rintro rfl
      simp [Slot.rimAdjB_irrefl] at h
    · simp [blockAdjVB, rimAdjVB, Vtx.mk, h]

/-! ### Counting -/

/-- Expanding a sum over the 5-element type `Slot`. Enumeration size: 5 elements. -/
private theorem sum_slot {M : Type*} [AddCommMonoid M] (f : Slot → M) :
    ∑ x : Slot, f x = f .a + f .b + f .c + f .d + f .e := by
  show ∑ x ∈ ({Slot.a, Slot.b, Slot.c, Slot.d, Slot.e} : Finset Slot), f x = _
  simp [Finset.sum_insert, Finset.mem_insert, add_assoc]

/-- The `i`-th spine block carries `3` always-valid leaves (`b`, `d`, `e`), plus an
`a`-leaf iff `i = 0` and a `c`-leaf iff `i = m`. -/
private theorem sum_slot_leaf (m : ℕ) (i : Fin (m + 1)) :
    (∑ x : Slot, if (Block.leaf i x).validB = true then 1 else 0)
      = 3 + ((if (i : ℕ) = 0 then 1 else 0) + (if (i : ℕ) = m then 1 else 0)) := by
  rw [sum_slot]
  simp only [Block.validB, decide_eq_true_eq, if_true]
  split_ifs <;> omega

set_option linter.unusedVariables false in
/-- There are `4m + 6` blocks: `m + 1` spine blocks, `3(m + 1)` leaves at slots `b, d, e`,
one `a`-leaf on `S₀` and one `c`-leaf on `S_m`.

(`hm` is part of the fixed downstream signature; the count in fact also holds for `m = 0`.) -/
theorem card_validBlock (m : ℕ) (hm : 1 ≤ m) : Fintype.card (ValidBlock m) = 4 * m + 6 := by
  clear hm
  rw [Fintype.card_subtype, Finset.card_filter,
    ← Equiv.sum_comp (Block.equivSum m).symm (fun b => if b.validB = true then 1 else 0),
    Fintype.sum_sum_type, Fintype.sum_prod_type]
  show ((∑ _i : Fin (m + 1), (if (Block.spine _i : Block m).validB = true then 1 else 0))
      + ∑ i : Fin (m + 1), ∑ x : Slot,
          (if (Block.leaf i x).validB = true then 1 else 0)) = 4 * m + 6
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => sum_slot_leaf m i)]
  simp only [Block.validB, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h0 : (∑ i : Fin (m + 1), if (i : ℕ) = 0 then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single (0 : Fin (m + 1))]
    · simp
    · intro b _ hb
      rw [if_neg]
      exact fun h => hb (Fin.ext (by simpa using h))
    · intro h; exact absurd (Finset.mem_univ _) h
  have hm' : (∑ i : Fin (m + 1), if (i : ℕ) = m then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single (Fin.last m)]
    · simp
    · intro b _ hb
      rw [if_neg]
      exact fun h => hb (Fin.ext (by simpa using h))
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h0, hm']
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- `|V(Gₘ)| = 5(4m + 6) + 1 = 20m + 31`. -/
theorem card_vtx (m : ℕ) (hm : 1 ≤ m) : Fintype.card (Vtx m) = 20 * m + 31 := by
  show Fintype.card (Option (ValidBlock m × Slot)) = 20 * m + 31
  rw [Fintype.card_option, Fintype.card_prod, card_validBlock m hm, Slot.card_eq]
  omega

/-! ### Degrees

Every vertex other than `v` is incident to exactly two rim edges and exactly one edge leaving
its pentagon — for a leaf-block attachment vertex the inter-block edge to the spine, for the
other four leaf vertices the edge to `v`, and for a spine vertex the inter-block edge to a
neighbouring block. This is the engine behind Proposition 4.6. -/

set_option linter.unusedVariables false in
/-- Slot arithmetic, block helpers, degrees and connectivity.

Everything from here to the end of the file supports the three headline facts
`Erdos1091.degree_eq_three`, `Erdos1091.G'_degree_le_three` and
`Erdos1091.G'_reachable`. -/
private def degreesSectionMarker : Unit := ()

open SimpleGraph

-- `Erdos1091.degree_eq_three` and `Erdos1091.G'_reachable` both carry an `hm : 1 ≤ m`
-- hypothesis that their proofs do not use: each statement happens to hold for `m = 0` as well.
-- The hypothesis is kept because it is part of the signature the downstream files expect, so
-- the unused-variable linter is switched off for the rest of this file.
set_option linter.unusedVariables false

/-! ### Slot arithmetic -/

namespace Slot

/-- The previous slot in rim order, inverse to `Slot.succ`. -/
def pred : Slot → Slot
  | a => e | b => a | c => b | d => c | e => d

/-- Rim adjacency means "the successor or the predecessor".
Enumeration size: `5 * 5 = 25` pairs of slots. -/
theorem rimAdjB_iff (s t : Slot) : rimAdjB s t = true ↔ t = s.succ ∨ t = s.pred := by
  revert s t; decide

/-- Enumeration size: 5 slots. -/
theorem succ_ne_pred (s : Slot) : s.succ ≠ s.pred := by revert s; decide

@[simp] theorem rimAdjB_succ (s : Slot) : rimAdjB s s.succ = true := by revert s; decide

@[simp] theorem rimAdjB_pred (s : Slot) : rimAdjB s s.pred = true := by revert s; decide

end Slot

/-! ### Basic vertex/block helpers -/

/-- The `i`-th spine block, as a valid block. -/
def spineVB (i : Fin (m + 1)) : ValidBlock m := ⟨Block.spine i, rfl⟩

@[simp] theorem spineVB_val (i : Fin (m + 1)) : (spineVB i).val = Block.spine i := rfl

@[simp] theorem Vtx.mk_eq_mk {b₁ b₂ : ValidBlock m} {s₁ s₂ : Slot} :
    Vtx.mk b₁ s₁ = Vtx.mk b₂ s₂ ↔ b₁ = b₂ ∧ s₁ = s₂ := by
  simp [Vtx.mk]

@[simp] theorem Vtx.mk_ne_v (b : ValidBlock m) (s : Slot) : Vtx.mk b s ≠ Vtx.v m := by
  simp [Vtx.mk, Vtx.v]

/-- An inter-block edge yields a `G' m`-edge. -/
theorem G'_adj_of_inter {b₁ b₂ : ValidBlock m} {s₁ s₂ : Slot}
    (h : interAdjVB (Vtx.mk b₁ s₁) (Vtx.mk b₂ s₂) = true) :
    (G' m).Adj (Vtx.mk b₁ s₁) (Vtx.mk b₂ s₂) := by
  refine ⟨?_, Or.inl ?_⟩
  · have hb := ne_block_of_interAdjVB h
    simp only [Vtx.mk_eq_mk, ne_eq, not_and]
    exact fun h' _ => hb h'
  · simp [blockAdjVB, h]

/-- The leaf-attachment edge `L_{i,x}[x] — S_i[x]`. -/
theorem G'_adj_leaf_spine (i : Fin (m + 1)) (x : Slot)
    (hv : (Block.leaf i x : Block m).validB = true) :
    (G' m).Adj (Vtx.mk ⟨Block.leaf i x, hv⟩ x) (Vtx.mk (spineVB i) x) := by
  refine G'_adj_of_inter ?_
  rw [interAdjVB_mk_mk_iff]
  exact Or.inl ⟨i, x, rfl, rfl, rfl, rfl⟩

/-- The spine edge `S_i[c] — S_j[a]` whenever `i + 1 = j`. -/
theorem G'_adj_spine_spine {i j : Fin (m + 1)} (h : (i : ℕ) + 1 = (j : ℕ)) :
    (G' m).Adj (Vtx.mk (spineVB i) Slot.c) (Vtx.mk (spineVB j) Slot.a) := by
  refine G'_adj_of_inter ?_
  rw [interAdjVB_mk_mk_iff]
  exact Or.inr ⟨i, j, rfl, rfl, h, rfl, rfl⟩

/-! ### Connectivity of `G' m` away from `v` -/

/-- Inside one block every two vertices are joined by a walk: the block is a 5-cycle. -/
theorem reach_same_block (b : ValidBlock m) (s t : Slot) :
    (G' m).Reachable (Vtx.mk b s) (Vtx.mk b t) := by
  have hadj : ∀ s t : Slot, Slot.rimAdjB s t = true → (G' m).Adj (Vtx.mk b s) (Vtx.mk b t) :=
    fun s t h => (G'_adj_same_block b s t).mpr h
  have h1 := (hadj Slot.a Slot.b (by decide)).reachable
  have h2 := (hadj Slot.b Slot.c (by decide)).reachable
  have h3 := (hadj Slot.c Slot.d (by decide)).reachable
  have h4 := (hadj Slot.d Slot.e (by decide)).reachable
  have key : ∀ s : Slot, (G' m).Reachable (Vtx.mk b Slot.a) (Vtx.mk b s) := by
    intro s
    cases s
    · exact Reachable.refl _
    · exact h1
    · exact h1.trans h2
    · exact h1.trans (h2.trans h3)
    · exact h1.trans (h2.trans (h3.trans h4))
  exact (key s).symm.trans (key t)

/-- Every spine block reaches `S₀[a]`, by downward induction along the spine. -/
theorem reach_spine_aux : ∀ (n : ℕ) (i : Fin (m + 1)), (i : ℕ) = n →
    (G' m).Reachable (Vtx.mk (spineVB i) Slot.a) (Vtx.mk (spineVB (0 : Fin (m + 1))) Slot.a) := by
  intro n
  induction n with
  | zero =>
      intro i hi
      have : i = (0 : Fin (m + 1)) := by
        apply Fin.ext
        simpa using hi
      subst this
      exact Reachable.refl _
  | succ n ih =>
      intro i hi
      have hlt : n < m + 1 := by have := i.isLt; omega
      have hadj : (G' m).Adj (Vtx.mk (spineVB (⟨n, hlt⟩ : Fin (m + 1))) Slot.c)
          (Vtx.mk (spineVB i) Slot.a) := G'_adj_spine_spine (by simpa using hi.symm)
      exact (hadj.symm.reachable.trans (reach_same_block _ Slot.c Slot.a)).trans
        (ih ⟨n, hlt⟩ rfl)

/-- Every non-special vertex reaches `S₀[a]`. -/
theorem reach_root (b : ValidBlock m) (s : Slot) :
    (G' m).Reachable (Vtx.mk b s) (Vtx.mk (spineVB (0 : Fin (m + 1))) Slot.a) := by
  obtain ⟨bv, hbv⟩ := b
  cases bv with
  | spine i => exact (reach_same_block _ s Slot.a).trans (reach_spine_aux _ i rfl)
  | leaf i x =>
      exact ((reach_same_block _ s x).trans (G'_adj_leaf_spine i x hbv).reachable).trans
        ((reach_same_block _ x Slot.a).trans (reach_spine_aux _ i rfl))

/-- `G'ₘ` is connected away from `v`: the block tree is a tree and each block is a 5-cycle. -/
theorem G'_reachable (m : ℕ) (hm : 1 ≤ m) (u w : Vtx m) (hu : u ≠ Vtx.v m) (hw : w ≠ Vtx.v m) :
    (G' m).Reachable u w := by
  obtain ⟨⟨b₁, s₁⟩, rfl⟩ : ∃ p, u = some p := by
    cases u with
    | none => exact absurd rfl hu
    | some p => exact ⟨p, rfl⟩
  obtain ⟨⟨b₂, s₂⟩, rfl⟩ : ∃ p, w = some p := by
    cases w with
    | none => exact absurd rfl hw
    | some p => exact ⟨p, rfl⟩
  exact (reach_root b₁ s₁).trans (reach_root b₂ s₂).symm

/-! ### Generic degree counting

Two utilities, stated for an arbitrary finite graph: if the neighbours of `u` are exactly
three explicit pairwise-distinct vertices then `deg u = 3`, and if they are *among* three
explicit vertices then `deg u ≤ 3`. -/

section GenericDegree

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]

theorem degree_le_three_of {u n₁ n₂ n₃ : V}
    (huniq : ∀ w, H.Adj u w → w = n₁ ∨ w = n₂ ∨ w = n₃) : H.degree u ≤ 3 := by
  have hsub : H.neighborFinset u ⊆ ({n₁, n₂, n₃} : Finset V) := by
    intro w hw
    rcases huniq w (mem_neighborFinset .. |>.mp hw) with rfl | rfl | rfl <;> simp
  calc H.degree u = (H.neighborFinset u).card := rfl
    _ ≤ ({n₁, n₂, n₃} : Finset V).card := Finset.card_le_card hsub
    _ ≤ 3 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        exact Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _)
          (Nat.succ_le_succ (Finset.card_singleton _).le))

theorem degree_eq_three_of {u n₁ n₂ n₃ : V}
    (h₁ : H.Adj u n₁) (h₂ : H.Adj u n₂) (h₃ : H.Adj u n₃)
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃)
    (huniq : ∀ w, H.Adj u w → w = n₁ ∨ w = n₂ ∨ w = n₃) : H.degree u = 3 := by
  have hset : H.neighborFinset u = ({n₁, n₂, n₃} : Finset V) := by
    apply Finset.Subset.antisymm
    · intro w hw
      rcases huniq w (mem_neighborFinset .. |>.mp hw) with rfl | rfl | rfl <;> simp
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> simpa [mem_neighborFinset]
  have : ({n₁, n₂, n₃} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  calc H.degree u = (H.neighborFinset u).card := rfl
    _ = 3 := by rw [hset, this]

end GenericDegree

/-! ### Adjacency, fully unfolded -/

/-- Adjacency in `Gₘ` between two block vertices: a rim edge of a common block, or an
inter-block edge in either direction. -/
theorem G_adj_mk_iff (b₁ b₂ : ValidBlock m) (s₁ s₂ : Slot) :
    (G m).Adj (Vtx.mk b₁ s₁) (Vtx.mk b₂ s₂) ↔
      (b₁ = b₂ ∧ Slot.rimAdjB s₁ s₂ = true) ∨
      interAdjVB (Vtx.mk b₁ s₁) (Vtx.mk b₂ s₂) = true ∨
      interAdjVB (Vtx.mk b₂ s₂) (Vtx.mk b₁ s₁) = true := by
  rw [G_adj_mk_mk]
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases Bool.or_eq_true_iff.mp h with h' | h'
      · refine Or.inl ?_
        simp only [rimAdjVB, Vtx.mk, Bool.and_eq_true, beq_iff_eq] at h'
        exact ⟨h'.1, h'.2⟩
      · exact Or.inr (Or.inl h')
    · rcases Bool.or_eq_true_iff.mp h with h' | h'
      · refine Or.inl ?_
        simp only [rimAdjVB, Vtx.mk, Bool.and_eq_true, beq_iff_eq] at h'
        exact ⟨h'.1.symm, by rw [Slot.rimAdjB_comm]; exact h'.2⟩
      · exact Or.inr (Or.inr h')
  · intro h
    rcases h with ⟨rfl, hrim⟩ | h | h
    · exact (G'_adj_same_block _ _ _).mpr hrim
    · exact G'_adj_of_inter h
    · exact (G'_adj_of_inter h).symm

/-- Adjacency to the special vertex. -/
theorem G_adj_v_mk_iff (b : ValidBlock m) (s : Slot) :
    (G m).Adj (Vtx.v m) (Vtx.mk b s) ↔ specialAdjVB (Vtx.v m) (Vtx.mk b s) = true := by
  rw [G_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · simpa [rawAdjVB, Vtx.v] using h
    · simp [rawAdjVB, Vtx.mk, Vtx.v] at h
  · intro h
    exact ⟨by simp [Vtx.v, Vtx.mk], Or.inl (by simp [rawAdjVB, h])⟩

/-- `v` is adjacent to exactly the non-attachment vertices of the leaf blocks. -/
theorem specialAdjVB_mk_iff (b : ValidBlock m) (s : Slot) :
    specialAdjVB (Vtx.v m) (Vtx.mk b s) = true ↔ ∃ i x, b.val = Block.leaf i x ∧ s ≠ x := by
  obtain ⟨bv, hbv⟩ := b
  cases bv with
  | spine i => simp [specialAdjVB, Vtx.v, Vtx.mk]
  | leaf i x =>
      simp only [specialAdjVB, Vtx.v, Vtx.mk, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      constructor
      · intro h; exact ⟨i, x, rfl, h⟩
      · rintro ⟨j, y, hj, hs⟩
        cases hj
        exact hs

/-- Adjacency to `v`, seen from a block vertex. -/
theorem G_adj_mk_v_iff (b : ValidBlock m) (s : Slot) :
    (G m).Adj (Vtx.mk b s) (Vtx.v m) ↔ ∃ i x, b.val = Block.leaf i x ∧ s ≠ x := by
  rw [SimpleGraph.adj_comm, G_adj_v_mk_iff, specialAdjVB_mk_iff]

/-- Adjacency inside one block is rim adjacency, also in `Gₘ`. -/
theorem G_adj_same_block (b : ValidBlock m) (s t : Slot) :
    (G m).Adj (Vtx.mk b s) (Vtx.mk b t) ↔ Slot.rimAdjB s t = true := by
  rw [G_adj_mk_mk, G'_adj_same_block]

theorem valBlock_ne {b₁ b₂ : ValidBlock m} (h : b₁.val ≠ b₂.val) : b₁ ≠ b₂ :=
  fun hh => h (by rw [hh])

theorem mk_ne_mk_of_block_ne {b₁ b₂ : ValidBlock m} (h : b₁ ≠ b₂) (s t : Slot) :
    Vtx.mk b₁ s ≠ Vtx.mk b₂ t := by
  simp only [Vtx.mk_eq_mk, ne_eq, not_and]
  exact fun h' _ => h h'

/-- **Classification of the neighbours of a block vertex in `Gₘ`.**

A `Gₘ`-neighbour of `(b, s)` is one of: the two rim neighbours `(b, s.succ)` and `(b, s.pred)`;
the special vertex `v`; the spine attachment point of a leaf block; a leaf attached to a spine
block; or a spine neighbour in either direction. -/
theorem G_nbr_cases (b : ValidBlock m) (s : Slot) (w : Vtx m) (h : (G m).Adj (Vtx.mk b s) w) :
    (w = Vtx.mk b s.succ ∨ w = Vtx.mk b s.pred) ∨
    (w = Vtx.v m) ∨
    (∃ (i : Fin (m + 1)) (x : Slot), b.val = Block.leaf i x ∧ s = x ∧
        w = Vtx.mk (spineVB i) x) ∨
    (∃ (i : Fin (m + 1)) (x : Slot) (hv : (Block.leaf i x : Block m).validB = true),
        b.val = Block.spine i ∧ s = x ∧ w = Vtx.mk ⟨Block.leaf i x, hv⟩ x) ∨
    (∃ i j : Fin (m + 1), b.val = Block.spine i ∧ (i : ℕ) + 1 = (j : ℕ) ∧ s = Slot.c ∧
        w = Vtx.mk (spineVB j) Slot.a) ∨
    (∃ i j : Fin (m + 1), b.val = Block.spine j ∧ (i : ℕ) + 1 = (j : ℕ) ∧ s = Slot.a ∧
        w = Vtx.mk (spineVB i) Slot.c) := by
  match w with
  | none => exact Or.inr (Or.inl rfl)
  | some (b', t) =>
    rw [show (some (b', t) : Vtx m) = Vtx.mk b' t from rfl] at h ⊢
    rcases (G_adj_mk_iff b b' s t).mp h with ⟨rfl, hrim⟩ | hin | hin
    · refine Or.inl ?_
      rcases (Slot.rimAdjB_iff s t).mp hrim with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rcases (interAdjVB_mk_mk_iff b b' s t).mp hin with
        ⟨i, x, hb, hb', hs, ht⟩ | ⟨i, j, hb, hb', hij, hs, ht⟩
      · exact Or.inr (Or.inr (Or.inl ⟨i, x, hb, hs,
          Vtx.mk_eq_mk.mpr ⟨Subtype.ext hb', ht⟩⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, hb, hij, hs,
          Vtx.mk_eq_mk.mpr ⟨Subtype.ext hb', ht⟩⟩))))
    · rcases (interAdjVB_mk_mk_iff b' b t s).mp hin with
        ⟨i, x, hb', hb, ht, hs⟩ | ⟨i, j, hb', hb, hij, ht, hs⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, x, hb' ▸ b'.property, hb, hs,
          Vtx.mk_eq_mk.mpr ⟨Subtype.ext hb', ht⟩⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, j, hb, hij, hs,
          Vtx.mk_eq_mk.mpr ⟨Subtype.ext hb', ht⟩⟩))))

/-! ### The unique edge leaving a pentagon -/

/-- `w` is *the* third neighbour of `(b, s)`: the one edge leaving the pentagon of `b`. -/
def IsOutside (b : ValidBlock m) (s : Slot) (w : Vtx m) : Prop :=
  (G m).Adj (Vtx.mk b s) w ∧ w ≠ Vtx.mk b s.succ ∧ w ≠ Vtx.mk b s.pred ∧
    ∀ w', (G m).Adj (Vtx.mk b s) w' → w' = Vtx.mk b s.succ ∨ w' = Vtx.mk b s.pred ∨ w' = w

/-- A vertex in a different block is not a rim neighbour. -/
theorem outside_ne_rim {b b' : ValidBlock m} (hne : b'.val ≠ b.val) (s t : Slot) :
    Vtx.mk b' t ≠ Vtx.mk b s := mk_ne_mk_of_block_ne (valBlock_ne hne) _ _

theorem v_ne_mk (b : ValidBlock m) (s : Slot) : Vtx.v m ≠ Vtx.mk b s := by
  simp [Vtx.v, Vtx.mk]

/-- The spine case of `exists_outside`.

At slot `a` the outside edge is the `a`-leaf if `i = 0` and the spine edge to `S_{i-1}[c]`
otherwise; at slot `c` it is the `c`-leaf if `i = m` and the spine edge to `S_{i+1}[a]`
otherwise; at `b`, `d`, `e` it is always the corresponding leaf. This is exactly where the
endpoint asymmetry of the construction pays for itself. -/
theorem exists_outside_spine (i : Fin (m + 1)) (s : Slot) :
    ∃ w : Vtx m, IsOutside (spineVB i) s w := by
  have key : ∀ w : Vtx m, (G m).Adj (Vtx.mk (spineVB i) s) w →
      (w = Vtx.mk (spineVB i) s.succ ∨ w = Vtx.mk (spineVB i) s.pred) ∨
      (∃ hv : (Block.leaf i s : Block m).validB = true, w = Vtx.mk ⟨Block.leaf i s, hv⟩ s) ∨
      (∃ j : Fin (m + 1), (i : ℕ) + 1 = (j : ℕ) ∧ s = Slot.c ∧
          w = Vtx.mk (spineVB j) Slot.a) ∨
      (∃ j : Fin (m + 1), (j : ℕ) + 1 = (i : ℕ) ∧ s = Slot.a ∧
          w = Vtx.mk (spineVB j) Slot.c) := by
    intro w hw
    rcases G_nbr_cases (spineVB i) s w hw with (rfl | rfl) | rfl | ⟨i', x', hb, hs', rfl⟩ |
      ⟨i', x', hv', hb, hs', rfl⟩ | ⟨i', j', hb, hij, hs', rfl⟩ | ⟨i', j', hb, hij, hs', rfl⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · exact absurd ((G_adj_mk_v_iff _ s).mp hw) (by simp)
    · exact absurd hb (by simp)
    · obtain rfl : i' = i := by simpa [eq_comm] using hb
      subst hs'
      exact Or.inr (Or.inl ⟨hv', rfl⟩)
    · obtain rfl : i' = i := by simpa [eq_comm] using hb
      exact Or.inr (Or.inr (Or.inl ⟨j', hij, hs', rfl⟩))
    · obtain rfl : j' = i := by simpa [eq_comm] using hb
      exact Or.inr (Or.inr (Or.inr ⟨i', hij, hs', rfl⟩))
  -- the outside edge is the leaf hanging at slot `s`, when that leaf exists
  have leafcase : ∀ hv : (Block.leaf i s : Block m).validB = true,
      (∀ j : Fin (m + 1), (i : ℕ) + 1 = (j : ℕ) → s ≠ Slot.c) →
      (∀ j : Fin (m + 1), (j : ℕ) + 1 = (i : ℕ) → s ≠ Slot.a) →
      ∃ w : Vtx m, IsOutside (spineVB i) s w := by
    intro hv h3 h4
    refine ⟨Vtx.mk ⟨Block.leaf i s, hv⟩ s, G'_le_G (G'_adj_leaf_spine i s hv).symm,
      outside_ne_rim (by simp) _ _, outside_ne_rim (by simp) _ _, ?_⟩
    intro w' hw'
    rcases key w' hw' with (h | h) | ⟨hv2, h⟩ | ⟨j, hj, hsc, h⟩ | ⟨j, hj, hsa, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd hsc (h3 j hj)
    · exact absurd hsa (h4 j hj)
  -- the outside edge is a spine edge to a neighbouring spine block
  have spinecase : ∀ (j : Fin (m + 1)) (t : Slot),
      (G m).Adj (Vtx.mk (spineVB i) s) (Vtx.mk (spineVB j) t) → j ≠ i →
      ((Block.leaf i s : Block m).validB = true → False) →
      (∀ j' : Fin (m + 1), (i : ℕ) + 1 = (j' : ℕ) → s = Slot.c →
          Vtx.mk (spineVB j') Slot.a = Vtx.mk (spineVB j) t) →
      (∀ j' : Fin (m + 1), (j' : ℕ) + 1 = (i : ℕ) → s = Slot.a →
          Vtx.mk (spineVB j') Slot.c = Vtx.mk (spineVB j) t) →
      ∃ w : Vtx m, IsOutside (spineVB i) s w := by
    intro j t hadj hji hnl h3 h4
    have hne : ∀ r : Slot, Vtx.mk (spineVB j) t ≠ Vtx.mk (spineVB i) r := fun r =>
      outside_ne_rim (by simpa using hji) _ _
    refine ⟨Vtx.mk (spineVB j) t, hadj, hne _, hne _, ?_⟩
    intro w' hw'
    rcases key w' hw' with (h | h) | ⟨hv2, h⟩ | ⟨j', hj', hsc, h⟩ | ⟨j', hj', hsa, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact (hnl hv2).elim
    · exact Or.inr (Or.inr (h.trans (h3 j' hj' hsc)))
    · exact Or.inr (Or.inr (h.trans (h4 j' hj' hsa)))
  cases s with
  | a =>
      by_cases hi : (i : ℕ) = 0
      · exact leafcase (by simp [Block.validB, hi]) (fun _ _ => by decide)
          (fun j hj => ((by omega : False)).elim)
      · have hlt : (i : ℕ) - 1 < m + 1 := by have := i.isLt; omega
        refine spinecase ⟨(i : ℕ) - 1, hlt⟩ Slot.c ?_ ?_ ?_ (fun _ _ h => absurd h (by decide)) ?_
        · exact G'_le_G (G'_adj_spine_spine (show ((i : ℕ) - 1) + 1 = (i : ℕ) by omega)).symm
        · intro hh; exact hi (by have := congrArg Fin.val hh; simp at this; omega)
        · intro hh; exact hi (by simpa [Block.validB] using hh)
        · intro j' hj' _
          exact congrArg (fun k => Vtx.mk (spineVB k) Slot.c)
            (Fin.ext (show (j' : ℕ) = (i : ℕ) - 1 by omega))
  | b => exact leafcase rfl (fun _ _ => by decide) (fun _ _ => by decide)
  | c =>
      by_cases hi : (i : ℕ) = m
      · refine leafcase (by simp [Block.validB, hi]) (fun j hj => ?_) (fun _ _ => by decide)
        have := j.isLt
        omega
      · have hlt : (i : ℕ) + 1 < m + 1 := by have := i.isLt; omega
        refine spinecase ⟨(i : ℕ) + 1, hlt⟩ Slot.a ?_ ?_ ?_ ?_ (fun _ _ h => absurd h (by decide))
        · exact G'_le_G (G'_adj_spine_spine (show (i : ℕ) + 1 = ((i : ℕ) + 1) from rfl))
        · intro hh; exact absurd (congrArg Fin.val hh) (by simp)
        · intro hh; exact hi (by simpa [Block.validB] using hh)
        · intro j' hj' _
          exact congrArg (fun k => Vtx.mk (spineVB k) Slot.a)
            (Fin.ext (show (j' : ℕ) = (i : ℕ) + 1 by omega))
  | d => exact leafcase rfl (fun _ _ => by decide) (fun _ _ => by decide)
  | e => exact leafcase rfl (fun _ _ => by decide) (fun _ _ => by decide)

/-- **Every vertex other than `v` has exactly one neighbour outside its own pentagon.**
This is the whole content of `degree_eq_three`. -/
theorem exists_outside (b : ValidBlock m) (s : Slot) : ∃ w : Vtx m, IsOutside b s w := by
  obtain ⟨bv, hbv⟩ := b
  cases bv with
  | leaf i x =>
      by_cases hs : s = x
      · -- the attachment vertex: the single inter-block edge to the spine
        subst hs
        refine ⟨Vtx.mk (spineVB i) s, G'_le_G (G'_adj_leaf_spine i s hbv), ?_, ?_, ?_⟩
        · exact outside_ne_rim (by simp) _ _
        · exact outside_ne_rim (by simp) _ _
        · intro w' hw'
          rcases G_nbr_cases _ s w' hw' with (rfl | rfl) | rfl | ⟨i', x', hb, hs', rfl⟩ |
            ⟨i', x', hv', hb, hs', rfl⟩ | ⟨i', j', hb, hij, hs', rfl⟩ | ⟨i', j', hb, hij, hs', rfl⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact absurd ((G_adj_mk_v_iff _ s).mp hw') (by simp)
          · obtain ⟨rfl, rfl⟩ := Block.leaf.inj hb
            exact Or.inr (Or.inr rfl)
          · exact absurd hb (by simp)
          · exact absurd hb (by simp)
          · exact absurd hb (by simp)
      · -- a non-attachment vertex of a leaf block: the single edge to `v`
        refine ⟨Vtx.v m, (G_adj_mk_v_iff _ s).mpr ⟨i, x, rfl, hs⟩, ?_, ?_, ?_⟩
        · exact v_ne_mk _ _
        · exact v_ne_mk _ _
        · intro w' hw'
          rcases G_nbr_cases _ s w' hw' with (rfl | rfl) | rfl | ⟨i', x', hb, hs', rfl⟩ |
            ⟨i', x', hv', hb, hs', rfl⟩ | ⟨i', j', hb, hij, hs', rfl⟩ | ⟨i', j', hb, hij, hs', rfl⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · obtain ⟨rfl, rfl⟩ := Block.leaf.inj hb
            exact absurd hs' hs
          · exact absurd hb (by simp)
          · exact absurd hb (by simp)
          · exact absurd hb (by simp)
  | spine i => exact exists_outside_spine i s

/-! ### The degree theorems -/

/-- Every vertex except `v` has degree exactly 3: two rim neighbours plus the unique
neighbour outside its pentagon. -/
theorem degree_eq_three (m : ℕ) (hm : 1 ≤ m) (u : Vtx m) (hu : u ≠ Vtx.v m) :
    (G m).degree u = 3 := by
  obtain ⟨⟨b, s⟩, rfl⟩ : ∃ p, u = some p := by
    cases u with
    | none => exact absurd rfl hu
    | some p => exact ⟨p, rfl⟩
  obtain ⟨w, hadj, hw1, hw2, huniq⟩ := exists_outside b s
  refine degree_eq_three_of (n₁ := Vtx.mk b s.succ) (n₂ := Vtx.mk b s.pred) (n₃ := w)
    ((G_adj_same_block b s s.succ).mpr (by simp))
    ((G_adj_same_block b s s.pred).mpr (by simp)) hadj ?_ (Ne.symm hw1) (Ne.symm hw2) huniq
  simp only [ne_eq, Vtx.mk_eq_mk, not_and]
  exact fun _ => Slot.succ_ne_pred s

/-- All degrees in `G'ₘ` are at most 3: `v` is isolated, and every other vertex keeps at most
its three `Gₘ`-neighbours. -/
theorem G'_degree_le_three (m : ℕ) (u : Vtx m) : (G' m).degree u ≤ 3 := by
  match u with
  | none =>
      have : (G' m).neighborFinset (Vtx.v m) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro w hw
        exact G'_not_adj_v w (mem_neighborFinset .. |>.mp hw)
      show ((G' m).neighborFinset (Vtx.v m)).card ≤ 3
      rw [this]
      simp
  | some (b, s) =>
      obtain ⟨w, hadj, hw1, hw2, huniq⟩ := exists_outside b s
      refine degree_le_three_of (n₁ := Vtx.mk b s.succ) (n₂ := Vtx.mk b s.pred) (n₃ := w) ?_
      intro w' hw'
      exact huniq w' (G'_le_G hw')

end Erdos1091

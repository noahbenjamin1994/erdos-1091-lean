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
import Erdos1091.CliqueFree
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Cycle
import Mathlib.Data.Set.Card

/-!
# Lemmas 4.7–4.9 and Proposition 4.10: every cycle of `Gₘ` has at most 10 chords

`Cycle` and `Cycle.chords` are taken from the PR #5870 API
(`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Cycle`); we deliberately do not
introduce a second notion of chord.

## Method

The paper says "every inter-block edge of `G'ₘ` is a cut edge". Rather than reasoning about
connected components, we package that idea once, for an arbitrary graph, as `IsSide`:

> `IsSide G S x y` says that every edge of `G` other than `s(x, y)` has both or neither
> endpoint in `S` — i.e. `s(x, y)` is the *only* edge across the cut `(S, Sᶜ)`.

Two consequences are proved once and reused everywhere below:

* `IsSide.mem_edges` — any walk starting inside `S` and ending outside it uses `s(x, y)`.
  Hence `IsSide.isBridge`, which is the paper's "cut edge" claim.
* `IsSide.notMem_support` — a *path* whose two endpoints both avoid `S` never enters `S`
  at all. (Entering and leaving would use `s(x, y)` twice, contradicting `Walk.IsPath`.)

The whole block-tree structure of the caterpillar is then fed in through exactly two families
of sides (`isSide_leaf` and `isSide_spine`), one per kind of inter-block edge:

* a leaf block `L_{i,x}` is a side of its own attachment edge `L_{i,x}[x] — S_i[x]`;
* `{blocks with spine index ≤ i}` is a side of the spine edge `S_i[c] — S_{i+1}[a]`.

Verifying these two is a finite check on `interAdjVB`, with no walk reasoning at all.

## How cycles through `v` are counted

`exists_vPath` cuts a cycle through `v` open at `v`, leaving a `v`-avoiding path `P` in `G'ₘ`
between two neighbours `p`, `q` of `v`. The chords then split in two families.

* **Chords at `v`.** Their far endpoint is a neighbour of `v`, hence a non-attachment vertex of a
  leaf pentagon. A leaf pentagon containing neither `p` nor `q` is not visited by `P` at all
  (`IsSide.notMem_support` on `isSide_leaf`: entering and leaving would use the single attachment
  edge twice), so these chords live in at most two pentagons offering four vertices each. Two of
  those eight edges are the cycle's own edges at `v`, leaving **at most six**.
* **Chords away from `v`.** Both endpoints lie on `P`, so an inter-block chord would be a bridge
  of `G'ₘ` (Lemma 4.7) lying on a sub-walk of `P`, hence on `P` — not a chord. So every such
  chord is a rim edge of one pentagon (`sameBlock_of_chord`).

  Inside one pentagon the count is finite and decidable. Every visited vertex spends two of its
  three edges on the cycle, so it keeps at least one rim edge, and a vertex short of one rim edge
  must spend an edge leaving the pentagon. `exit_of_mem_P_edges` shows every such departure aims
  at `p` or `q`, so at most two slots are deficient — and `slot_count` then gives **at most one
  chord per pentagon**. `slot_count_nochord` sharpens this: the two deficient slots must be rim
  adjacent, which by `mem_specialBlocks` happens in only **four** pentagons (the leaf blocks of
  `p` and `q` and the two spine blocks they hang from). So **at most four** rim chords.

Total `6 + 4 = 10`. The paper's split is `4 + 4 + 1 + 1`; ours regroups the same ten edges by
"at `v`" versus "rim", which avoids having to identify which pentagon contributes which.

## References

* [APSSV26b] arXiv:2604.06609, Lemmas 4.7, 4.8, 4.9 and Proposition 4.10.
-/

namespace Erdos1091

open SimpleGraph

/-! ## A general cut-edge device

Nothing in this section knows about `Gₘ`; it is stated for an arbitrary graph so that the
caterpillar's block tree enters only through the two `IsSide` instances proved afterwards. -/

section Cut

variable {V : Type*} {G : SimpleGraph V}

/-- `S` is a **side** of the edge `s(x, y)`: the only edge of `G` with exactly one endpoint in
`S` is `s(x, y)` itself. This is the "cut edge" hypothesis of Lemma 4.7, packaged so that it
can be checked by a finite case analysis on adjacency. -/
def IsSide (G : SimpleGraph V) (S : Set V) (x y : V) : Prop :=
  ∀ u w, G.Adj u w → s(u, w) ≠ s(x, y) → (u ∈ S ↔ w ∈ S)

/-- **A walk that leaves a side must use the separating edge.** -/
theorem IsSide.mem_edges {S : Set V} {x y : V} (hS : IsSide G S x y) :
    ∀ {a b : V} (p : G.Walk a b), a ∈ S → b ∉ S → s(x, y) ∈ p.edges := by
  intro a b p
  induction p with
  | nil => exact fun ha hb => absurd ha hb
  | @cons a' b' c' h q ih =>
    intro ha hb
    by_cases he : s(a', b') = s(x, y)
    · rw [SimpleGraph.Walk.edges_cons, he]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih ((hS a' b' h he).mp ha) hb)

/-- **A side is cut off by its edge**: this is the paper's "every inter-block edge is a cut
edge", via `SimpleGraph.isBridge_iff_forall_walk_mem_edges`. -/
theorem IsSide.isBridge {S : Set V} {x y : V} (hS : IsSide G S x y) (hx : x ∈ S) (hy : y ∉ S) :
    G.IsBridge s(x, y) :=
  SimpleGraph.isBridge_iff_forall_walk_mem_edges.mpr fun p => hS.mem_edges p hx hy

/-- **A path whose endpoints avoid a side never enters it.** Entering and leaving `S` would use
the single separating edge twice, which a path cannot do.

This is what replaces the paper's informal "the blocks visited by `C \ {v}` form a path in the
block tree": a pendant block not containing an endpoint of the path is simply not visited. -/
theorem IsSide.notMem_support [DecidableEq V] {S : Set V} {x y : V} (hS : IsSide G S x y) {a b : V}
    {p : G.Walk a b} (hp : p.IsPath) (ha : a ∉ S) (hb : b ∉ S) {u : V} (hu : u ∈ p.support) :
    u ∉ S := by
  intro huS
  -- Split `p` at `u`; the first half runs from `u` back to `a ∉ S`, the second from `u` to
  -- `b ∉ S`, so each half contains `s(x, y)`.
  have h₁ : s(x, y) ∈ (p.takeUntil u hu).edges := by
    have := hS.mem_edges (p.takeUntil u hu).reverse huS ha
    rwa [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at this
  have h₂ : s(x, y) ∈ (p.dropUntil u hu).edges := hS.mem_edges _ huS hb
  -- …but `p`'s edge list is their concatenation and is duplicate-free.
  have hnd : ((p.takeUntil u hu).edges ++ (p.dropUntil u hu).edges).Nodup := by
    rw [← SimpleGraph.Walk.edges_append, p.take_spec hu]
    exact hp.edges_nodup
  exact (List.nodup_append'.mp hnd).2.2 h₁ h₂

end Cut

/-! ## The two families of sides of the caterpillar -/

variable {m : ℕ}

/-- The block a non-special vertex belongs to. -/
def blockOf {m : ℕ} : Vtx m → Option (ValidBlock m)
  | none => none
  | some (b, _) => some b

@[simp] lemma blockOf_mk (b : ValidBlock m) (s : Slot) : blockOf (Vtx.mk b s) = some b := rfl

@[simp] lemma blockOf_v : blockOf (Vtx.v m) = none := rfl

/-- The spine index of a block: `i` for `S_i` and for every leaf hanging off `S_i`. -/
def Block.idx {m : ℕ} : Block m → Fin (m + 1)
  | .spine i => i
  | .leaf i _ => i

/-- `G'ₘ`-adjacency forces both endpoints to be block vertices, since `v` is isolated there. -/
lemma exists_mk_of_G'_adj {u w : Vtx m} (h : (G' m).Adj u w) :
    ∃ (b₁ b₂ : ValidBlock m) (s₁ s₂ : Slot), u = Vtx.mk b₁ s₁ ∧ w = Vtx.mk b₂ s₂ := by
  cases u with
  | none => exact absurd h (G'_not_adj_v w)
  | some p =>
    cases w with
    | none => exact absurd h.symm (G'_not_adj_v _)
    | some q => exact ⟨p.1, q.1, p.2, q.2, rfl, rfl⟩

/-- **A leaf block is a side of its own attachment edge.** A leaf pentagon meets the rest of
`G'ₘ` only through `L_{i,x}[x] — S_i[x]`. -/
theorem isSide_leaf (i : Fin (m + 1)) (x : Slot) (hb : (Block.leaf i x).validB = true)
    (hs : (Block.spine i).validB = true) :
    IsSide (G' m) {u | blockOf u = some (⟨Block.leaf i x, hb⟩ : ValidBlock m)}
      (Vtx.mk ⟨Block.leaf i x, hb⟩ x) (Vtx.mk ⟨Block.spine i, hs⟩ x) := by
  intro u w hadj hne
  obtain ⟨b₁, b₂, s₁, s₂, rfl, rfl⟩ := exists_mk_of_G'_adj hadj
  simp only [Set.mem_ofPred_eq, blockOf_mk, Option.some.injEq]
  by_cases hbb : b₁ = b₂
  · subst hbb; rfl
  -- Distinct blocks: the edge is an inter-block edge, and a leaf block has exactly one of them,
  -- namely `L[x] — S_i[x]` — which is the edge excluded by `hne`.
  by_cases h₁ : b₁ = (⟨Block.leaf i x, hb⟩ : ValidBlock m)
  · subst h₁
    exfalso
    have hspine : b₂.val = Block.spine i := spine_of_G'_adj_leaf rfl hbb hadj
    obtain ⟨hs₁, hs₂⟩ := slots_of_G'_adj_ne_block hbb hadj
    obtain rfl : b₂ = (⟨Block.spine i, hs⟩ : ValidBlock m) := Subtype.ext hspine
    exact hne (by rw [show s₁ = x from hs₁, show s₂ = x from hs₂])
  · by_cases h₂ : b₂ = (⟨Block.leaf i x, hb⟩ : ValidBlock m)
    · subst h₂
      exfalso
      have hspine : b₁.val = Block.spine i := spine_of_G'_adj_leaf rfl (Ne.symm hbb) hadj.symm
      obtain ⟨hs₂, hs₁⟩ := slots_of_G'_adj_ne_block (Ne.symm hbb) hadj.symm
      obtain rfl : b₁ = (⟨Block.spine i, hs⟩ : ValidBlock m) := Subtype.ext hspine
      exact hne (by rw [show s₁ = x from hs₁, show s₂ = x from hs₂, Sym2.eq_swap])
    · simp [h₁, h₂]

/-- **The initial segment of the spine is a side of each spine edge.** Blocks with spine index
`≤ i` meet the rest of `G'ₘ` only through `S_i[c] — S_{i+1}[a]`. -/
theorem isSide_spine (i j : Fin (m + 1)) (hij : (i : ℕ) + 1 = (j : ℕ))
    (hi : (Block.spine i).validB = true) (hj : (Block.spine j).validB = true) :
    IsSide (G' m) {u | ∃ b : ValidBlock m, blockOf u = some b ∧ (b.val.idx : ℕ) ≤ (i : ℕ)}
      (Vtx.mk ⟨Block.spine i, hi⟩ Slot.c) (Vtx.mk ⟨Block.spine j, hj⟩ Slot.a) := by
  intro u w hadj hne
  obtain ⟨b₁, b₂, s₁, s₂, rfl, rfl⟩ := exists_mk_of_G'_adj hadj
  simp only [Set.mem_ofPred_eq, blockOf_mk, Option.some.injEq, exists_eq_left']
  by_cases hbb : b₁ = b₂
  · rw [hbb]
  -- Distinct blocks, so an inter-block edge. The claim is symmetric in the two endpoints, so we
  -- prove it once for an oriented inter-block edge and apply it to whichever orientation holds.
  have key : ∀ (c₁ c₂ : ValidBlock m) (t₁ t₂ : Slot),
      interAdjVB (Vtx.mk c₁ t₁) (Vtx.mk c₂ t₂) = true →
      s(Vtx.mk c₁ t₁, Vtx.mk c₂ t₂) ≠
        s(Vtx.mk (⟨Block.spine i, hi⟩ : ValidBlock m) Slot.c,
          Vtx.mk (⟨Block.spine j, hj⟩ : ValidBlock m) Slot.a) →
      (((c₁.val.idx : ℕ) ≤ (i : ℕ)) ↔ ((c₂.val.idx : ℕ) ≤ (i : ℕ))) := by
    intro c₁ c₂ t₁ t₂ hin hne'
    rw [interAdjVB_mk_mk_iff] at hin
    rcases hin with ⟨k, y, h₁, h₂, -, -⟩ | ⟨k, l, h₁, h₂, hkl, rfl, rfl⟩
    · -- A leaf attaches to its *own* spine block: both sides have the same index.
      rw [h₁, h₂]; exact Iff.rfl
    · -- A spine edge `S_k — S_{k+1}` separates the two sides exactly when `k = i`, and then it
      -- *is* the excluded edge.
      by_cases hk : (k : ℕ) = (i : ℕ)
      · exfalso
        have hki : k = i := Fin.ext hk
        have hlj : l = j := Fin.ext (by omega : (l : ℕ) = (j : ℕ))
        have e₁ : c₁ = (⟨Block.spine i, hi⟩ : ValidBlock m) :=
          Subtype.ext (h₁.trans (by rw [hki]))
        have e₂ : c₂ = (⟨Block.spine j, hj⟩ : ValidBlock m) :=
          Subtype.ext (h₂.trans (by rw [hlj]))
        exact hne' (by rw [e₁, e₂])
      · rw [h₁, h₂]
        simp only [Block.idx]
        exact ⟨fun _ => by omega, fun _ => by omega⟩
  rcases G'_adj_of_ne_block rfl rfl hbb hadj with hin | hin
  · exact key b₁ b₂ s₁ s₂ hin hne
  · exact (key b₂ b₁ s₂ s₁ hin (by rw [Sym2.eq_swap]; exact hne)).symm

/-! ## Lemma 4.7: cycles of `G'ₘ` live inside one pentagon block -/

/-- **Inter-block edges are bridges** (Lemma 4.7's engine). Both kinds of inter-block edge are
covered by one of the two sides above: the leaf attachment edge by its own leaf block, the spine
edge `S_i[c] — S_{i+1}[a]` by the initial segment of the spine. -/
theorem interAdj_isBridge {u w : Vtx m} (hinter : interAdjVB u w = true) :
    (G' m).IsBridge s(u, w) := by
  -- Both endpoints are block vertices.
  obtain ⟨⟨b₁, s₁⟩, rfl⟩ : ∃ p, u = some p := by
    cases u with
    | none => simp at hinter
    | some p => exact ⟨p, rfl⟩
  obtain ⟨⟨b₂, s₂⟩, rfl⟩ : ∃ p, w = some p := by
    cases w with
    | none => simp at hinter
    | some p => exact ⟨p, rfl⟩
  rw [show (some (b₁, s₁) : Vtx m) = Vtx.mk b₁ s₁ from rfl,
    show (some (b₂, s₂) : Vtx m) = Vtx.mk b₂ s₂ from rfl] at *
  rw [interAdjVB_mk_mk_iff] at hinter
  -- Peel the validity proofs off the two blocks so that the block equalities can be substituted.
  obtain ⟨bb₁, hv₁⟩ := b₁
  obtain ⟨bb₂, hv₂⟩ := b₂
  rcases hinter with ⟨i, x, h₁, h₂, e₁, e₂⟩ | ⟨i, j, h₁, h₂, hij, rfl, rfl⟩
  · -- Leaf attachment edge: the leaf block itself is a side.
    simp only at h₁ h₂
    subst h₁; subst h₂
    rw [e₁, e₂]
    exact (isSide_leaf i x hv₁ hv₂).isBridge rfl (by simp [Vtx.mk, blockOf])
  · -- Spine edge: the blocks of index `≤ i` form a side.
    simp only at h₁ h₂
    subst h₁; subst h₂
    refine (isSide_spine i j hij hv₁ hv₂).isBridge ⟨_, rfl, le_rfl⟩ ?_
    rintro ⟨b, hb, hble⟩
    rw [blockOf_mk, Option.some.injEq] at hb
    subst hb
    simp only [Block.idx] at hble
    omega

/-- A walk all of whose edges stay inside one block has constant `blockOf` along its support. -/
theorem blockOf_eq_of_walk {u w : Vtx m} (p : (G' m).Walk u w)
    (h : ∀ a b : Vtx m, s(a, b) ∈ p.edges → blockOf a = blockOf b) :
    ∀ z ∈ p.support, blockOf z = blockOf u := by
  induction p with
  | nil => intro z hz; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz; rw [hz]
  | @cons a b c hadj q ih =>
    intro z hz
    have hab : blockOf a = blockOf b := h a b (by simp)
    rcases List.mem_cons.mp hz with rfl | hz'
    · rfl
    · rw [ih (fun x y hxy => h x y (by simp [hxy])) z hz', hab]

/-- A `G'ₘ`-edge that is *not* an inter-block edge joins two slots of one and the same block. -/
lemma blockOf_eq_of_G'_adj_of_not_bridge {u w : Vtx m} (hadj : (G' m).Adj u w)
    (hbr : ¬ (G' m).IsBridge s(u, w)) : blockOf u = blockOf w := by
  obtain ⟨b₁, b₂, s₁, s₂, rfl, rfl⟩ := exists_mk_of_G'_adj hadj
  by_cases hbb : b₁ = b₂
  · rw [hbb]; rfl
  exfalso
  rcases G'_adj_of_ne_block rfl rfl hbb hadj with hin | hin
  · exact hbr (interAdj_isBridge hin)
  · exact hbr (Sym2.eq_swap ▸ interAdj_isBridge hin)

/-- **Lemma 4.7.** Every cycle of `G'ₘ` stays inside one pentagon block.

No edge of a cycle is a bridge, so by `interAdj_isBridge` no edge of the cycle is an
inter-block edge; hence `blockOf` is constant along the cycle. -/
theorem G'_cycle_within_block (c : Cycle (G' m)) :
    ∃ b : ValidBlock m, ∀ u ∈ c.walk.support, blockOf u = some b := by
  have hconst : ∀ u ∈ c.walk.support, blockOf u = blockOf c.base :=
    blockOf_eq_of_walk c.walk fun a b hab =>
      blockOf_eq_of_G'_adj_of_not_bridge (c.walk.adj_of_mem_edges hab)
        (c.not_isBridge_of_mem_edges hab)
  -- The base point of a cycle is a block vertex: `v` is isolated in `G'ₘ`, so it lies on no cycle.
  obtain ⟨⟨b, s⟩, hbase⟩ : ∃ p, c.base = some p := by
    cases hb : c.base with
    | some p => exact ⟨p, rfl⟩
    | none =>
      exfalso
      -- A cycle is not nil, so its base has a neighbour on the cycle — but `v` is isolated.
      obtain ⟨d, hd, q, -⟩ := SimpleGraph.Walk.not_nil_iff.mp c.isCycle.not_nil
      exact G'_not_adj_v d (by rw [show Vtx.v m = c.base from hb.symm]; exact hd)
  exact ⟨b, fun u hu => (hconst u hu).trans (by rw [hbase]; rfl)⟩

/-! ## Cycles avoiding `v` have at most five chords

By Lemma 4.7 such a cycle lives in one pentagon, so every chord is one of that pentagon's five
rim edges. (The paper says there are in fact *no* chords, because the cycle must be the whole
pentagon; five is already far below the bound of 10 that Proposition 4.10 needs, so we do not
prove the sharper statement.) -/

/-- The five rim edges of a pentagon, as a `Finset (Sym2 Slot)`. -/
def rimSym : Finset (Sym2 Slot) :=
  {s(Slot.a, Slot.b), s(Slot.b, Slot.c), s(Slot.c, Slot.d), s(Slot.d, Slot.e), s(Slot.e, Slot.a)}

/-- A pentagon has five rim edges. Enumeration size: the five listed elements. -/
lemma card_rimSym : rimSym.card = 5 := by decide

/-- Rim adjacency is membership in `rimSym`. Enumeration size: `5 × 5 = 25` slot pairs. -/
lemma mem_rimSym {s t : Slot} (h : Slot.rimAdjB s t = true) : s(s, t) ∈ rimSym := by
  revert h; cases s <;> cases t <;> decide

/-- A cycle of `Gₘ` that avoids `v` is a cycle of `G'ₘ`: all its edges miss `v`. -/
def toG'Cycle (c : Cycle (G m)) (hv : Vtx.v m ∉ c.walk.support) : Cycle (G' m) where
  base := c.base
  walk := c.walk.transfer (G' m) <| by
    intro e he
    induction e with
    | _ a b =>
      exact G'_adj_of_G_adj_of_ne_v (c.walk.adj_of_mem_edges he)
        (fun h => hv (h ▸ c.walk.fst_mem_support_of_mem_edges he))
        (fun h => hv (h ▸ c.walk.snd_mem_support_of_mem_edges he))
  isCycle := c.isCycle.transfer _

@[simp] lemma toG'Cycle_support (c : Cycle (G m)) (hv : Vtx.v m ∉ c.walk.support) :
    (toG'Cycle c hv).walk.support = c.walk.support :=
  SimpleGraph.Walk.support_transfer _ _

/-- **Cycles of `Gₘ` avoiding `v` have at most five chords** — they lie in a single pentagon, so
every chord is a rim edge of that pentagon. -/
theorem cycle_chords_le_five_of_notMem_v (c : Cycle (G m)) (hv : Vtx.v m ∉ c.walk.support) :
    c.chords.encard ≤ 5 := by
  obtain ⟨b, hb⟩ := G'_cycle_within_block (toG'Cycle c hv)
  rw [toG'Cycle_support] at hb
  -- Every chord is a rim edge of `b`, i.e. lies in the image of `rimSym`.
  have hsub : c.chords ⊆ ↑(rimSym.image (Sym2.map (Vtx.mk b))) := by
    intro e he
    induction e with
    | _ p q =>
      obtain ⟨hedge, hsupp, -⟩ := he
      -- Both endpoints lie on the cycle, hence in `b`, and neither is `v`.
      have hp : blockOf p = some b := hb p (hsupp p (by simp))
      have hq : blockOf q = some b := hb q (hsupp q (by simp))
      obtain ⟨sp, rfl⟩ : ∃ s, p = Vtx.mk b s := by
        cases p with
        | none => simp [blockOf] at hp
        | some r => exact ⟨r.2, by simp only [blockOf, Option.some.injEq] at hp; rw [← hp]; rfl⟩
      obtain ⟨sq, rfl⟩ : ∃ s, q = Vtx.mk b s := by
        cases q with
        | none => simp [blockOf] at hq
        | some r => exact ⟨r.2, by simp only [blockOf, Option.some.injEq] at hq; rw [← hq]; rfl⟩
      -- Inside a single block, `Gₘ`-adjacency is rim adjacency.
      have hrim : Slot.rimAdjB sp sq = true :=
        (G'_adj_same_block b sp sq).mp ((G_adj_mk_mk b b sp sq).mp hedge)
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨s(sp, sq), mem_rimSym hrim, rfl⟩
  calc c.chords.encard
      ≤ (↑(rimSym.image (Sym2.map (Vtx.mk b))) : Set (Sym2 (Vtx m))).encard :=
        Set.encard_le_encard hsub
    _ = ((rimSym.image (Sym2.map (Vtx.mk b))).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ (rimSym.card : ℕ∞) := by exact_mod_cast Finset.card_image_le
    _ = 5 := by rw [card_rimSym]; rfl

/-! ## Section A: the pentagon counting lemmas (finite, decidable) -/

section SlotCount
open Finset

/-- Rim edges (indexed by slot) with both endpoints inside `T`. -/
def rimSpanS (T : Finset Slot) : Finset Slot := T.filter (fun s => s.succ ∈ T)

/-- **The pentagon counting lemma.**
`T` = slots of a pentagon visited by a cycle `C`; `Ds` = rim edges of that pentagon lying on `C`;
`h1` = every visited slot has at least one incident rim edge on `C`;
`hX` = at most two visited slots fail to have *both* their rim edges on `C`.
Conclusion: at most one spanned rim edge is missing from `C`, and if one is missing then the
whole pentagon is visited.
Enumeration size: `2^5 * 2^5 = 1024` pairs `(T, Ds)` of subsets of `Slot`. -/
theorem slot_count (T Ds : Finset Slot)
    (hD : Ds ⊆ rimSpanS T)
    (h1 : ∀ s ∈ T, s ∈ Ds ∨ s.pred ∈ Ds)
    (hX : (T.filter (fun s => ¬ (s ∈ Ds ∧ s.pred ∈ Ds))).card ≤ 2) :
    (rimSpanS T \ Ds).card ≤ 1 ∧ ((rimSpanS T \ Ds).Nonempty → T = Finset.univ) := by
  revert T Ds hD h1 hX
  decide

set_option synthInstance.maxSize 400 in
/-- **Zero-chord criterion.** If no two deficient slots are rim adjacent, the pentagon
contributes no chord at all.
Enumeration size: `2^5 * 2^5 = 1024` pairs `(T, Ds)` of subsets of `Slot`.

The `synthInstance.maxSize` bump is needed only to *build* the `Decidable` instance for the
doubly-bounded `hX` quantifier (default 128 is too small for the nested
`Fintype.decidableForallFintype` tower); the kernel evaluation itself is cheap. -/
theorem slot_count_nochord (T Ds : Finset Slot)
    (hD : Ds ⊆ rimSpanS T)
    (h1 : ∀ s ∈ T, s ∈ Ds ∨ s.pred ∈ Ds)
    (hX : ∀ s ∈ T, ∀ t ∈ T, ¬ (s ∈ Ds ∧ s.pred ∈ Ds) → ¬ (t ∈ Ds ∧ t.pred ∈ Ds) →
            Slot.rimAdjB s t = false ∨ s = t) :
    rimSpanS T ⊆ Ds := by
  revert T Ds hD h1 hX
  decide

/-- Every rim-adjacent pair of slots is `(u, u.succ)` for exactly one `u`.
Enumeration size: `5 * 5 = 25` pairs of slots (each with a 5-way existential). -/
theorem exists_rimEdge_index {s t : Slot} (h : Slot.rimAdjB s t = true) :
    ∃ u : Slot, s(s, t) = s(u, u.succ) := by
  revert h; cases s <;> cases t <;> decide

/-- `s` and `s.succ` are rim adjacent.
Enumeration size: 5 slots. -/
theorem rimAdjB_self_succ (s : Slot) : Slot.rimAdjB s s.succ = true := by revert s; decide

/-- The two rim edges at `s` are indexed by `s` and `s.pred`.
Enumeration size: `5 * 5 = 25` pairs `(u, s)`. -/
theorem rimEdge_incident {u s : Slot} (h : s ∈ (s(u, u.succ) : Sym2 Slot)) : u = s ∨ u = s.pred := by
  revert h; cases u <;> cases s <;> decide

end SlotCount

/-! ## Section B: a cycle through `v`, cut open into a `v`-avoiding path -/

/-- A cycle through `v` is `v` followed by a `v`-avoiding path between two neighbours of `v`. -/
theorem exists_vPath (c : Cycle (G m)) (hv : Vtx.v m ∈ c.walk.support) :
    ∃ (p q : Vtx m) (P : (G' m).Walk p q),
      P.IsPath ∧
      Vtx.v m ∉ P.support ∧
      p ≠ q ∧
      (G m).Adj (Vtx.v m) p ∧
      (G m).Adj (Vtx.v m) q ∧
      (∀ u, u ∈ c.walk.support ↔ u = Vtx.v m ∨ u ∈ P.support) ∧
      (∀ e, e ∈ c.edges ↔ e = s(Vtx.v m, p) ∨ e = s(Vtx.v m, q) ∨ e ∈ P.edges) := by
  -- Step 1: rotate the cycle so that it is based at `v`, keeping only membership information.
  obtain ⟨c₁, hc₁, hsupp, hedges⟩ :
      ∃ c₁ : (G m).Walk (Vtx.v m) (Vtx.v m), c₁.IsCycle ∧
        (∀ u, u ∈ c.walk.support ↔ u ∈ c₁.support) ∧
        (∀ e, e ∈ c.edges ↔ e ∈ c₁.edges) := by
    refine ⟨c.walk.rotate (Vtx.v m) hv, c.isCycle.rotate hv, fun u => ?_, fun e => ?_⟩
    · exact (Walk.mem_support_rotate_iff _ _ _).symm
    · exact ((Walk.rotate_edges c.walk (Vtx.v m) hv).mem_iff).symm
  -- Step 2: `c₁` is not nil, so it is `cons hadj w`.
  have hlen3 : 3 ≤ c₁.length := hc₁.three_le_length
  obtain ⟨p, hadj, w, rfl⟩ := Walk.not_nil_iff.mp hc₁.not_nil
  have hwlen : 2 ≤ w.length := by
    rw [Walk.length_cons] at hlen3
    omega
  obtain ⟨hwpath, -⟩ := (Walk.cons_isCycle_iff w hadj).mp hc₁
  -- Step 3: `w.reverse` is a path starting at `v`, and it is not nil either.
  have hwrpath : w.reverse.IsPath := hwpath.reverse
  have hnotnil : ¬ w.reverse.Nil := by
    rw [Walk.not_nil_iff_lt_length, Walk.length_reverse]
    omega
  obtain ⟨q, hadj', P₀, hwreq⟩ := Walk.not_nil_iff.mp hnotnil
  rw [hwreq, Walk.cons_isPath_iff] at hwrpath
  obtain ⟨hP₀path, hnv⟩ := hwrpath
  have hP₀len : 1 ≤ P₀.length := by
    have h1 : w.reverse.length = P₀.length + 1 := by rw [hwreq, Walk.length_cons]
    rw [Walk.length_reverse] at h1
    omega
  -- Step 4: `q ≠ p`.
  have hqp : q ≠ p := by
    intro h
    exact (Walk.not_nil_iff_lt_length.mpr (by omega)) (hP₀path.nil_iff_eq.mpr h)
  -- Step 5: transfer `P₀` into `G' m`.
  have htr : ∀ e ∈ P₀.edges, e ∈ (G' m).edgeSet := by
    rintro ⟨a, b⟩ he
    have ha : a ∈ P₀.support := P₀.fst_mem_support_of_mem_edges he
    have hb : b ∈ P₀.support := P₀.snd_mem_support_of_mem_edges he
    have hab : (G m).Adj a b := P₀.adj_of_mem_edges he
    exact G'_adj_of_G_adj_of_ne_v hab (fun h => hnv (h ▸ ha)) (fun h => hnv (h ▸ hb))
  -- Step 6: bookkeeping for the support and the edges of `w`.
  have hwsupp : ∀ u, u ∈ w.support ↔ u = Vtx.v m ∨ u ∈ P₀.support := by
    intro u
    rw [← List.mem_reverse, ← Walk.support_reverse, hwreq, Walk.support_cons, List.mem_cons]
  have hwedges : ∀ e, e ∈ w.edges ↔ e = s(Vtx.v m, q) ∨ e ∈ P₀.edges := by
    intro e
    rw [← List.mem_reverse, ← Walk.edges_reverse, hwreq, Walk.edges_cons, List.mem_cons]
  refine ⟨q, p, P₀.transfer (G' m) htr, Walk.IsPath.transfer htr hP₀path, ?_, hqp, hadj', hadj,
    fun u => ?_, fun e => ?_⟩
  · rw [Walk.support_transfer]
    exact hnv
  · rw [Walk.support_transfer, hsupp u, Walk.support_cons, List.mem_cons, hwsupp u]
    tauto
  · rw [Walk.edges_transfer, hedges e, Walk.edges_cons, List.mem_cons, hwedges e]
    tauto

/-! ## Section C: exit directions -/

/-! ## Exit directions -/

/-- Leaving block `b`, which slot of `b` do you go out through to reach block `b'`? -/
def Block.exitDir {m : ℕ} : Block m → Block m → Slot
  | .leaf _ x, _ => x
  | .spine i, .spine j => if (j : ℕ) < (i : ℕ) then Slot.a else Slot.c
  | .spine i, .leaf j y =>
      if (j : ℕ) < (i : ℕ) then Slot.a else if (i : ℕ) < (j : ℕ) then Slot.c else y

/-- The slot of `b` "in the direction of" `u`: `u`'s own slot if `u ∈ b`, else the exit
direction towards `u`'s block. (`Vtx.v m` is not meaningful here; any value will do.) -/
def exitSlot {m : ℕ} (b : ValidBlock m) (u : Vtx m) : Slot :=
  match u with
  | none => Slot.a
  | some (b', t) => if b' = b then t else Block.exitDir b.val b'.val

lemma exitSlot_mk (b bu : ValidBlock m) (su : Slot) :
    exitSlot b (Vtx.mk bu su) = if bu = b then su else Block.exitDir b.val bu.val := rfl

/-- A leaf block is left through its own attachment slot, whatever the target block is. -/
lemma exitDir_leaf (i : Fin (m + 1)) (x : Slot) (c : Block m) :
    Block.exitDir (Block.leaf i x) c = x := by
  cases c <;> rfl

/-- A spine block is left towards its *own* leaf through that leaf's attachment slot. -/
lemma exitDir_spine_leaf_self (i : Fin (m + 1)) (x : Slot) :
    Block.exitDir (Block.spine i) (Block.leaf i x) = x := by
  simp [Block.exitDir]

/-- Blocks further along the spine are reached through slot `c`. -/
lemma exitDir_spine_gt {i : Fin (m + 1)} {c : Block m} (h : (i : ℕ) < (c.idx : ℕ)) :
    Block.exitDir (Block.spine i) c = Slot.c := by
  cases c with
  | spine k =>
    simp only [Block.idx] at h
    have hk : ¬ ((k : ℕ) < (i : ℕ)) := by omega
    simp [Block.exitDir, hk]
  | leaf k y =>
    simp only [Block.idx] at h
    have hk : ¬ ((k : ℕ) < (i : ℕ)) := by omega
    have hk' : (i : ℕ) < (k : ℕ) := h
    simp [Block.exitDir, hk, hk']

/-- Blocks earlier along the spine are reached through slot `a`. -/
lemma exitDir_spine_lt {j : Fin (m + 1)} {c : Block m} (h : (c.idx : ℕ) < (j : ℕ)) :
    Block.exitDir (Block.spine j) c = Slot.a := by
  cases c with
  | spine k =>
    simp only [Block.idx] at h
    simp [Block.exitDir, h]
  | leaf k y =>
    simp only [Block.idx] at h
    simp [Block.exitDir, h]

/-! ## Two trivial `IsSide` helpers -/

/-- `IsSide` does not care about the orientation of its separating edge. -/
theorem IsSide.symm_edge {V : Type*} {G : SimpleGraph V} {S : Set V} {x y : V}
    (hS : IsSide G S x y) : IsSide G S y x := fun u w hadj hne =>
  hS u w hadj fun h => hne (h.trans Sym2.eq_swap)

/-- The complement of a side is a side of the same edge. -/
theorem IsSide.compl {V : Type*} {G : SimpleGraph V} {S : Set V} {x y : V}
    (hS : IsSide G S x y) : IsSide G Sᶜ x y := by
  intro u w hadj hne
  exact not_congr (hS u w hadj hne)

/-! ## The two sides, restated for arbitrary `ValidBlock`s -/

/-- `isSide_leaf`, stated for blocks given by an equation rather than literally. -/
theorem isSide_leaf' {b b' : ValidBlock m} {i : Fin (m + 1)} {x : Slot}
    (hb : b.val = Block.leaf i x) (hb' : b'.val = Block.spine i) :
    IsSide (G' m) {z | blockOf z = some b} (Vtx.mk b x) (Vtx.mk b' x) := by
  obtain ⟨bv, hvalid⟩ := b
  obtain ⟨bv', hvalid'⟩ := b'
  replace hb : bv = Block.leaf i x := hb
  replace hb' : bv' = Block.spine i := hb'
  subst hb
  subst hb'
  exact isSide_leaf i x hvalid hvalid'

/-- `isSide_spine`, stated for blocks given by an equation rather than literally. -/
theorem isSide_spine' {b b' : ValidBlock m} {i j : Fin (m + 1)}
    (hb : b.val = Block.spine i) (hb' : b'.val = Block.spine j) (hij : (i : ℕ) + 1 = (j : ℕ)) :
    IsSide (G' m) {z | ∃ bb : ValidBlock m, blockOf z = some bb ∧ (bb.val.idx : ℕ) ≤ (i : ℕ)}
      (Vtx.mk b Slot.c) (Vtx.mk b' Slot.a) := by
  obtain ⟨bv, hvalid⟩ := b
  obtain ⟨bv', hvalid'⟩ := b'
  replace hb : bv = Block.spine i := hb
  replace hb' : bv' = Block.spine j := hb'
  subst hb
  subst hb'
  exact isSide_spine i j hij hvalid hvalid'

/-! ## The main lemma -/

/-- **Every inter-block edge of the path `P` points at one of `P`'s two endpoints.**
If `P` uses an edge leaving block `b` at slot `s`, then `s` is the exit direction of `b`
towards `p` or towards `q`. -/
theorem exit_of_mem_P_edges {p q : Vtx m} {P : (G' m).Walk p q} (hP : P.IsPath)
    (hpv : p ≠ Vtx.v m) (hqv : q ≠ Vtx.v m)
    (b : ValidBlock m) (s : Slot) (w : Vtx m)
    (hne : blockOf w ≠ some b)
    (he : s(Vtx.mk b s, w) ∈ P.edges) :
    exitSlot b p = s ∨ exitSlot b q = s := by
  by_contra hcon
  have hp : exitSlot b p ≠ s := fun h => hcon (Or.inl h)
  have hq : exitSlot b q ≠ s := fun h => hcon (Or.inr h)
  -- The edge is a genuine `G'ₘ`-edge and `w` lies on `P`.
  have hadj : (G' m).Adj (Vtx.mk b s) w := P.adj_of_mem_edges he
  have hwsupp : w ∈ P.support := P.snd_mem_support_of_mem_edges he
  -- `Vtx.v m` is isolated in `G' m`, so `w` is a block vertex.
  obtain ⟨b', t, rfl⟩ : ∃ (b' : ValidBlock m) (t : Slot), w = Vtx.mk b' t := by
    cases w with
    | none => exact absurd hadj.symm (G'_not_adj_v _)
    | some pr => exact ⟨pr.1, pr.2, rfl⟩
  have hbb : b' ≠ b := fun h => hne (by rw [blockOf_mk, h])
  -- Both endpoints of `P` are block vertices too.
  obtain ⟨bp, sp, hpe⟩ : ∃ (bp : ValidBlock m) (sp : Slot), p = Vtx.mk bp sp := by
    cases p with
    | none => exact absurd rfl hpv
    | some pr => exact ⟨pr.1, pr.2, rfl⟩
  obtain ⟨bq, sq, hqe⟩ : ∃ (bq : ValidBlock m) (sq : Slot), q = Vtx.mk bq sq := by
    cases q with
    | none => exact absurd rfl hqv
    | some pr => exact ⟨pr.1, pr.2, rfl⟩
  -- The single contradiction that closes all four cases: `w` sits on `P`, so it cannot lie in
  -- a side that both endpoints of `P` avoid.
  have contra : ∀ (S : Set (Vtx m)) (x y : Vtx m), IsSide (G' m) S x y →
      Vtx.mk b' t ∈ S → p ∉ S → q ∉ S → False := by
    intro S x y hS hmem hpS hqS
    exact hS.notMem_support hP hpS hqS hwsupp hmem
  -- Distinct blocks, so the edge is an inter-block edge; unfold it in both orientations.
  rcases G'_adj_of_ne_block rfl rfl (Ne.symm hbb) hadj with hin | hin <;>
    rw [interAdjVB_mk_mk_iff] at hin
  · rcases hin with ⟨i, x, hbv, hb'v, hsx, htx⟩ | ⟨i, j, hbv, hb'v, hij, hsc, htc⟩
    · -- (a) `b` is the leaf `L_{i,x}`, `b'` its spine block, `s = t = x`.
      -- Side: everything outside `b`.
      have hnotS : ∀ (u : Vtx m) (bu : ValidBlock m) (su : Slot), u = Vtx.mk bu su →
          exitSlot b u ≠ s → u ∉ ({z | blockOf z = some b} : Set (Vtx m))ᶜ := by
        intro u bu su hue hu hmem
        refine hu ?_
        have hbune : bu ≠ b := fun h =>
          hmem (show blockOf u = some b by rw [hue, blockOf_mk, h])
        rw [hue, exitSlot_mk, if_neg hbune, hbv, exitDir_leaf]
        exact hsx.symm
      have hmemw : Vtx.mk b' t ∈ ({z | blockOf z = some b} : Set (Vtx m))ᶜ := by
        intro hmem
        have h' : blockOf (Vtx.mk b' t) = some b := hmem
        rw [blockOf_mk] at h'
        exact hbb (Option.some_inj.mp h')
      exact contra _ _ _ (isSide_leaf' hbv hb'v).compl hmemw
        (hnotS p bp sp hpe hp) (hnotS q bq sq hqe hq)
    · -- (c) `b = S_i`, `b' = S_{i+1}`, `s = c`, `t = a`.  Side: everything with index `> i`.
      have hnotS : ∀ (u : Vtx m) (bu : ValidBlock m) (su : Slot), u = Vtx.mk bu su →
          exitSlot b u ≠ s →
          u ∉ ({z | ∃ bb : ValidBlock m, blockOf z = some bb ∧
            (bb.val.idx : ℕ) ≤ (i : ℕ)} : Set (Vtx m))ᶜ := by
        intro u bu su hue hu hmem
        refine hu ?_
        have hgt : (i : ℕ) < (bu.val.idx : ℕ) := by
          by_contra hle
          have hin' : ∃ bb : ValidBlock m, blockOf u = some bb ∧ (bb.val.idx : ℕ) ≤ (i : ℕ) :=
            ⟨bu, by rw [hue, blockOf_mk], by omega⟩
          exact hmem hin'
        have hbune : bu ≠ b := by
          intro h
          rw [h, hbv] at hgt
          simp only [Block.idx] at hgt
          omega
        rw [hue, exitSlot_mk, if_neg hbune, hbv, exitDir_spine_gt hgt]
        exact hsc.symm
      have hmemw : Vtx.mk b' t ∈ ({z | ∃ bb : ValidBlock m, blockOf z = some bb ∧
          (bb.val.idx : ℕ) ≤ (i : ℕ)} : Set (Vtx m))ᶜ := by
        intro hmem
        obtain ⟨bb, hbb1, hbb2⟩ := hmem
        rw [blockOf_mk] at hbb1
        have hbe : bb = b' := (Option.some_inj.mp hbb1).symm
        rw [hbe, hb'v] at hbb2
        simp only [Block.idx] at hbb2
        omega
      exact contra _ _ _ (isSide_spine' hbv hb'v hij).compl hmemw
        (hnotS p bp sp hpe hp) (hnotS q bq sq hqe hq)
  · rcases hin with ⟨i, x, hb'v, hbv, htx, hsx⟩ | ⟨i, j, hb'v, hbv, hij, htc, hsa⟩
    · -- (b) `b'` is the leaf `L_{i,x}`, `b = S_i` its spine block, `s = t = x`.
      -- Side: the leaf block `b'`.
      have hnotS : ∀ (u : Vtx m) (bu : ValidBlock m) (su : Slot), u = Vtx.mk bu su →
          exitSlot b u ≠ s → u ∉ ({z | blockOf z = some b'} : Set (Vtx m)) := by
        intro u bu su hue hu hmem
        refine hu ?_
        have h' : blockOf u = some b' := hmem
        rw [hue, blockOf_mk] at h'
        have hbue : bu = b' := Option.some_inj.mp h'
        have hbune : bu ≠ b := by rw [hbue]; exact hbb
        rw [hue, exitSlot_mk, if_neg hbune, hbv, hbue, hb'v, exitDir_spine_leaf_self]
        exact hsx.symm
      have hmemw : Vtx.mk b' t ∈ ({z | blockOf z = some b'} : Set (Vtx m)) := rfl
      exact contra _ _ _ (isSide_leaf' hb'v hbv) hmemw
        (hnotS p bp sp hpe hp) (hnotS q bq sq hqe hq)
    · -- (d) `b' = S_i`, `b = S_{i+1}`, `s = a`, `t = c`.  Side: everything with index `≤ i`.
      have hnotS : ∀ (u : Vtx m) (bu : ValidBlock m) (su : Slot), u = Vtx.mk bu su →
          exitSlot b u ≠ s →
          u ∉ ({z | ∃ bb : ValidBlock m, blockOf z = some bb ∧
            (bb.val.idx : ℕ) ≤ (i : ℕ)} : Set (Vtx m)) := by
        intro u bu su hue hu hmem
        refine hu ?_
        obtain ⟨bb, hbb1, hbb2⟩ := hmem
        rw [hue, blockOf_mk] at hbb1
        have hbe : bb = bu := (Option.some_inj.mp hbb1).symm
        rw [hbe] at hbb2
        have hlt : (bu.val.idx : ℕ) < (j : ℕ) := by omega
        have hbune : bu ≠ b := by
          intro h
          rw [h, hbv] at hlt
          simp only [Block.idx] at hlt
          omega
        rw [hue, exitSlot_mk, if_neg hbune, hbv, exitDir_spine_lt hlt]
        exact hsa.symm
      have hmemw : Vtx.mk b' t ∈ ({z | ∃ bb : ValidBlock m, blockOf z = some bb ∧
          (bb.val.idx : ℕ) ≤ (i : ℕ)} : Set (Vtx m)) := by
        refine ⟨b', rfl, ?_⟩
        rw [hb'v]
        exact le_rfl
      exact contra _ _ _ (isSide_spine' hb'v hbv hij) hmemw
        (hnotS p bp sp hpe hp) (hnotS q bq sq hqe hq)

/-! ## Section D: assembly -/

section Assemble
open Finset

/-! ### Every vertex of a cycle has exactly two incident cycle edges -/

/-- The two cycle-edges at a vertex of the cycle, as a pair of distinct neighbours. -/
theorem cycle_two_nbrs {V : Type*} [DecidableEq V] {Gr : SimpleGraph V} (c : Cycle Gr) {u : V}
    (hu : u ∈ c.walk.support) :
    ∃ y z : V, y ≠ z ∧ ∀ x, s(u, x) ∈ c.edges ↔ (x = y ∨ x = z) := by
  have h2 : (c.walk.toSubgraph.neighborSet u).ncard = 2 :=
    c.isCycle.ncard_neighborSet_toSubgraph_eq_two hu
  obtain ⟨y, z, hyz, hset⟩ := Set.ncard_eq_two.mp h2
  refine ⟨y, z, hyz, fun x => ?_⟩
  have : x ∈ c.walk.toSubgraph.neighborSet u ↔ s(u, x) ∈ c.edges :=
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges
  rw [← this, hset]
  simp

/-- **The local dichotomy at a vertex of the cycle.**
Every vertex of `Gₘ` other than `v` has exactly three neighbours: two rim neighbours and the
unique `w` outside its pentagon. A vertex on the cycle uses exactly two of those three edges, so
at least one rim edge is used, and if not *both* rim edges are used then the outside edge is. -/
theorem rim_or_out {b : ValidBlock m} {s : Slot} {w : Vtx m} (hout : IsOutside b s w)
    (c : Cycle (G m)) (hu : Vtx.mk b s ∈ c.walk.support) :
    (s(Vtx.mk b s, Vtx.mk b s.succ) ∈ c.edges ∨ s(Vtx.mk b s, Vtx.mk b s.pred) ∈ c.edges) ∧
      (¬ (s(Vtx.mk b s, Vtx.mk b s.succ) ∈ c.edges ∧
            s(Vtx.mk b s, Vtx.mk b s.pred) ∈ c.edges) →
        s(Vtx.mk b s, w) ∈ c.edges) := by
  obtain ⟨-, hw1, hw2, huniq⟩ := hout
  obtain ⟨y, z, hyz, hmem⟩ := cycle_two_nbrs c hu
  -- Both cycle-neighbours are among the three graph-neighbours.
  have hy3 : y = Vtx.mk b s.succ ∨ y = Vtx.mk b s.pred ∨ y = w :=
    huniq y (c.walk.adj_of_mem_edges ((hmem y).mpr (Or.inl rfl)))
  have hz3 : z = Vtx.mk b s.succ ∨ z = Vtx.mk b s.pred ∨ z = w :=
    huniq z (c.walk.adj_of_mem_edges ((hmem z).mpr (Or.inr rfl)))
  have hsp : Vtx.mk b s.succ ≠ Vtx.mk b s.pred := by
    simp only [ne_eq, Vtx.mk_eq_mk, not_and]
    exact fun _ => Slot.succ_ne_pred s
  constructor
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    -- neither rim edge is used, so both cycle-neighbours are `w`
    have hyw : y = w := by
      rcases hy3 with h | h | h
      · exact absurd ((hmem _).mpr (Or.inl h.symm)) (h ▸ h1)
      · exact absurd ((hmem _).mpr (Or.inl h.symm)) (h ▸ h2)
      · exact h
    have hzw : z = w := by
      rcases hz3 with h | h | h
      · exact absurd ((hmem _).mpr (Or.inr h.symm)) (h ▸ h1)
      · exact absurd ((hmem _).mpr (Or.inr h.symm)) (h ▸ h2)
      · exact h
    exact hyz (hyw.trans hzw.symm)
  · intro hnb
    rw [hmem]
    -- one of the two rim edges is unused, so one of `y`, `z` must be `w`
    by_contra hcon
    push Not at hcon
    obtain ⟨hyw, hzw⟩ := hcon
    have hy2 : y = Vtx.mk b s.succ ∨ y = Vtx.mk b s.pred := by tauto
    have hz2 : z = Vtx.mk b s.succ ∨ z = Vtx.mk b s.pred := by tauto
    refine hnb ⟨?_, ?_⟩ <;> rw [hmem]
    · rcases hy2 with h | h
      · exact Or.inl h.symm
      · rcases hz2 with h' | h'
        · exact Or.inr h'.symm
        · exact absurd (h.trans h'.symm) hyz
    · rcases hy2 with h | h
      · rcases hz2 with h' | h'
        · exact absurd (h.trans h'.symm) hyz
        · exact Or.inr h'.symm
      · exact Or.inl h.symm

/-! ### The visited-slot and used-rim-edge data of a block -/

variable (c : Cycle (G m))

/-- The slots of `b` visited by the cycle. -/
def visitedSlots (b : ValidBlock m) : Finset Slot :=
  univ.filter (fun s => Vtx.mk b s ∈ c.walk.support)

/-- The rim edges of `b` (indexed by their first slot) lying on the cycle. -/
def usedRim (b : ValidBlock m) : Finset Slot :=
  univ.filter (fun s => s(Vtx.mk b s, Vtx.mk b s.succ) ∈ c.edges)

variable {c}

@[simp] lemma mem_visitedSlots {b : ValidBlock m} {s : Slot} :
    s ∈ visitedSlots c b ↔ Vtx.mk b s ∈ c.walk.support := by simp [visitedSlots]

@[simp] lemma mem_usedRim {b : ValidBlock m} {s : Slot} :
    s ∈ usedRim c b ↔ s(Vtx.mk b s, Vtx.mk b s.succ) ∈ c.edges := by simp [usedRim]

/-- Enumeration size: 5 slots. -/
lemma Slot.succ_pred (s : Slot) : s.pred.succ = s := by revert s; decide

/-- The *other* rim edge at slot `s` is the one indexed by `s.pred`. -/
lemma mem_usedRim_pred {b : ValidBlock m} {s : Slot} :
    s.pred ∈ usedRim c b ↔ s(Vtx.mk b s, Vtx.mk b s.pred) ∈ c.edges := by
  rw [mem_usedRim, Slot.succ_pred, Sym2.eq_swap]

/-- `usedRim` sits inside the rim edges spanned by `visitedSlots`. -/
theorem usedRim_subset (b : ValidBlock m) : usedRim c b ⊆ rimSpanS (visitedSlots c b) := by
  intro s hs
  rw [mem_usedRim] at hs
  rw [rimSpanS, Finset.mem_filter, mem_visitedSlots, mem_visitedSlots]
  exact ⟨c.walk.fst_mem_support_of_mem_edges hs, c.walk.snd_mem_support_of_mem_edges hs⟩

/-- Every visited slot carries at least one rim edge of the cycle (`h1` of `slot_count`). -/
theorem usedRim_covers (b : ValidBlock m) :
    ∀ s ∈ visitedSlots c b, s ∈ usedRim c b ∨ s.pred ∈ usedRim c b := by
  intro s hs
  rw [mem_visitedSlots] at hs
  obtain ⟨w, hout⟩ := exists_outside b s
  rw [mem_usedRim, mem_usedRim_pred]
  exact (rim_or_out hout c hs).1

/-- A visited slot missing one of its two rim edges has its *outside* edge on the cycle. -/
theorem out_edge_of_deficient {b : ValidBlock m} {s : Slot} {w : Vtx m} (hout : IsOutside b s w)
    (hs : s ∈ visitedSlots c b) (hdef : ¬ (s ∈ usedRim c b ∧ s.pred ∈ usedRim c b)) :
    s(Vtx.mk b s, w) ∈ c.edges := by
  rw [mem_visitedSlots] at hs
  refine (rim_or_out hout c hs).2 ?_
  rwa [mem_usedRim, mem_usedRim_pred] at hdef

/-! ### Chords not through `v` are rim edges of a single block -/

/-- Two vertices on a path are joined by a walk whose edges lie on the path. -/
theorem exists_subwalk {p q : Vtx m} (P : (G' m).Walk p q) {u₁ u₂ : Vtx m}
    (h₁ : u₁ ∈ P.support) (h₂ : u₂ ∈ P.support) :
    ∃ W : (G' m).Walk u₁ u₂, ∀ e ∈ W.edges, e ∈ P.edges := by
  refine ⟨(P.takeUntil u₁ h₁).reverse.append (P.takeUntil u₂ h₂), fun e he => ?_⟩
  rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
  rcases he with he | he
  · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    exact P.edges_takeUntil_subset_edges h₁ he
  · exact P.edges_takeUntil_subset_edges h₂ he

/-- **An edge joining two vertices of the path but not lying on it stays inside one block.**
An inter-block edge is a bridge of `G'ₘ` (Lemma 4.7), so it belongs to *every* `G'ₘ`-walk between
its endpoints — in particular to the sub-walk of `P`, contradicting that it is not on `P`. -/
theorem sameBlock_of_chord {p q : Vtx m} (P : (G' m).Walk p q) {u₁ u₂ : Vtx m}
    (hadj : (G' m).Adj u₁ u₂) (h₁ : u₁ ∈ P.support) (h₂ : u₂ ∈ P.support)
    (hnot : s(u₁, u₂) ∉ P.edges) : blockOf u₁ = blockOf u₂ := by
  refine blockOf_eq_of_G'_adj_of_not_bridge hadj fun hbr => hnot ?_
  obtain ⟨W, hW⟩ := exists_subwalk P h₁ h₂
  exact hW _ (SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp hbr W)

/-! ### At most two leaf blocks are visited -/

/-- **A leaf block containing neither endpoint of `P` is not visited at all.**
This is `IsSide.notMem_support` applied to `isSide_leaf`: entering and leaving a pendant pentagon
would use its single attachment edge twice. -/
theorem leafBlock_of_mem_support {p q : Vtx m} {P : (G' m).Walk p q} (hP : P.IsPath)
    {b : ValidBlock m} {i : Fin (m + 1)} {x : Slot} (hbv : b.val = Block.leaf i x)
    {u : Vtx m} (hu : u ∈ P.support) (hub : blockOf u = some b) :
    blockOf p = some b ∨ blockOf q = some b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hp, hq⟩ := hcon
  obtain ⟨bb, hvalid⟩ := b
  simp only at hbv
  subst hbv
  exact absurd hub
    ((isSide_leaf i x hvalid rfl).notMem_support hP hp hq hu)

/-! ### Assembly -/

section Assembly

variable {c : Cycle (G m)} {p q : Vtx m} {P : (G' m).Walk p q}
variable (hP : P.IsPath) (hpv : p ≠ Vtx.v m) (hqv : q ≠ Vtx.v m)
variable (hsupp : ∀ u, u ∈ c.walk.support ↔ u = Vtx.v m ∨ u ∈ P.support)
variable (hedge : ∀ e, e ∈ c.edges ↔ e = s(Vtx.v m, p) ∨ e = s(Vtx.v m, q) ∨ e ∈ P.edges)

-- `deficient_subset` does not need `hsupp`, but keeping the hypothesis blocks uniform
-- keeps every caller in this section at the same arity.
set_option linter.unusedSectionVars false

include hP hpv hqv hsupp hedge

/-- **Every deficient slot of a block points at an endpoint of `P`.**
A visited slot missing one of its two rim edges spends a cycle edge on the single edge leaving
its pentagon; that edge is either one of the two cycle edges at `v` (and then the slot *is* an
endpoint) or an inter-block edge of `P`, which `exit_of_mem_P_edges` aims at `p` or `q`. -/
theorem deficient_subset (b : ValidBlock m) :
    (visitedSlots c b).filter (fun s => ¬ (s ∈ usedRim c b ∧ s.pred ∈ usedRim c b)) ⊆
      {exitSlot b p, exitSlot b q} := by
  intro s hs
  rw [Finset.mem_filter] at hs
  obtain ⟨hvis, hdef⟩ := hs
  obtain ⟨w, hout⟩ := exists_outside b s
  have hce : s(Vtx.mk b s, w) ∈ c.edges := out_edge_of_deficient hout hvis hdef
  -- The goal is `exitSlot b p = s ∨ exitSlot b q = s`, up to `Finset` notation.
  rw [Finset.mem_insert, Finset.mem_singleton]
  suffices h : exitSlot b p = s ∨ exitSlot b q = s by
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  -- `v` is not a block vertex, so a cycle edge at `v` forces `Vtx.mk b s` to be `p` or `q`.
  have hvcase : ∀ z : Vtx m, s(Vtx.mk b s, w) = s(Vtx.v m, z) → z = Vtx.mk b s := by
    intro z hz
    rcases Sym2.eq_iff.mp hz with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact absurd h₁ (Vtx.mk_ne_v b s)
    · exact h₁.symm
  rcases (hedge _).mp hce with h | h | h
  · refine Or.inl ?_
    have hp : p = Vtx.mk b s := hvcase p h
    rw [hp, exitSlot_mk, if_pos rfl]
  · refine Or.inr ?_
    have hq : q = Vtx.mk b s := hvcase q h
    rw [hq, exitSlot_mk, if_pos rfl]
  · -- an inter-block edge of `P`: the outside neighbour cannot be in `b`
    refine exit_of_mem_P_edges hP hpv hqv b s w ?_ h
    obtain ⟨hadj, hw1, hw2, -⟩ := hout
    intro hwb
    obtain ⟨bw, t, rfl⟩ : ∃ (bw : ValidBlock m) (t : Slot), w = Vtx.mk bw t := by
      cases w with
      | none => simp [blockOf] at hwb
      | some r => exact ⟨r.1, r.2, rfl⟩
    rw [blockOf_mk, Option.some.injEq] at hwb
    subst hwb
    -- inside one block, adjacency is rim adjacency, so `w` is one of the two rim neighbours
    rcases (Slot.rimAdjB_iff s t).mp ((G_adj_same_block _ s t).mp hadj) with rfl | rfl
    · exact hw1 rfl
    · exact hw2 rfl

/-- The `hX` hypothesis of `slot_count`: at most two slots of a block are deficient. -/
theorem deficient_card_le_two (b : ValidBlock m) :
    ((visitedSlots c b).filter
      (fun s => ¬ (s ∈ usedRim c b ∧ s.pred ∈ usedRim c b))).card ≤ 2 := by
  refine le_trans (Finset.card_le_card (deficient_subset hP hpv hqv hsupp hedge b)) ?_
  exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- **At most one chord per pentagon.** -/
theorem chordSlots_card_le_one (b : ValidBlock m) :
    (rimSpanS (visitedSlots c b) \ usedRim c b).card ≤ 1 :=
  (slot_count _ _ (usedRim_subset b) (usedRim_covers b)
    (deficient_card_le_two hP hpv hqv hsupp hedge b)).1

/-- **A pentagon with a chord has its two deficient slots rim-adjacent.**
Contrapositive of `slot_count_nochord`. -/
theorem rimAdj_exitSlots_of_chord {b : ValidBlock m}
    (hne : (rimSpanS (visitedSlots c b) \ usedRim c b).Nonempty) :
    Slot.rimAdjB (exitSlot b p) (exitSlot b q) = true := by
  by_contra hcon
  rw [Bool.not_eq_true] at hcon
  -- Every deficient slot is one of the two exit directions.
  have hmem : ∀ r, r ∈ visitedSlots c b → ¬ (r ∈ usedRim c b ∧ r.pred ∈ usedRim c b) →
      r = exitSlot b p ∨ r = exitSlot b q := by
    intro r hr hdr
    have := deficient_subset hP hpv hqv hsupp hedge b (Finset.mem_filter.mpr ⟨hr, hdr⟩)
    rwa [Finset.mem_insert, Finset.mem_singleton] at this
  -- If the two exit directions are not rim adjacent, no two deficient slots can be either.
  have hsub : rimSpanS (visitedSlots c b) ⊆ usedRim c b := by
    refine slot_count_nochord (visitedSlots c b) (usedRim c b) (usedRim_subset b)
      (usedRim_covers b) ?_
    intro s hs t ht hds hdt
    rcases hmem s hs hds with h₁ | h₁ <;> rcases hmem t ht hdt with h₂ | h₂ <;> rw [h₁, h₂]
    · exact Or.inr rfl
    · exact Or.inl hcon
    · exact Or.inl (by rw [Slot.rimAdjB_comm]; exact hcon)
    · exact Or.inr rfl
  obtain ⟨t, ht⟩ := hne
  rw [Finset.mem_sdiff] at ht
  exact ht.2 (hsub ht.1)

end Assembly

/-! ### The four blocks that can carry a chord -/

/-- Blocks whose two exit directions are rim adjacent are among four explicit ones: the leaf
blocks of `p` and of `q`, and the two spine blocks those leaves hang from. This is where the
caterpillar's tree structure finally bounds the number of chord-carrying pentagons. -/
theorem mem_specialBlocks {bp bq b : ValidBlock m} {ip iq : Fin (m + 1)} {xp xq sp sq : Slot}
    (hbp : bp.val = Block.leaf ip xp) (hbq : bq.val = Block.leaf iq xq)
    (hrim : Slot.rimAdjB (exitSlot b (Vtx.mk bp sp)) (exitSlot b (Vtx.mk bq sq)) = true) :
    b = bp ∨ b = bq ∨ b = spineVB ip ∨ b = spineVB iq := by
  rw [exitSlot_mk, exitSlot_mk] at hrim
  by_cases hp : bp = b
  · exact Or.inl hp.symm
  by_cases hq : bq = b
  · exact Or.inr (Or.inl hq.symm)
  rw [if_neg hp, if_neg hq] at hrim
  -- neither endpoint lies in `b`, so both directions are genuine exit directions
  obtain ⟨bv, hvalid⟩ := b
  cases bv with
  | leaf i x =>
    -- a leaf pentagon is left through its single attachment slot, the same for both endpoints
    rw [show (⟨Block.leaf i x, hvalid⟩ : ValidBlock m).val = Block.leaf i x from rfl,
      exitDir_leaf, exitDir_leaf] at hrim
    exact absurd hrim (by simp [Slot.rimAdjB_irrefl])
  | spine k =>
    rw [show (⟨Block.spine k, hvalid⟩ : ValidBlock m).val = Block.spine k from rfl] at hrim
    -- Off the two spine blocks `S_{ip}`, `S_{iq}` both directions are `a` or `c`, never adjacent.
    by_cases hik : (ip : ℕ) = (k : ℕ)
    · refine Or.inr (Or.inr (Or.inl (Subtype.ext ?_)))
      rw [spineVB_val]
      exact congrArg Block.spine (Fin.ext hik.symm)
    by_cases hjk : (iq : ℕ) = (k : ℕ)
    · refine Or.inr (Or.inr (Or.inr (Subtype.ext ?_)))
      rw [spineVB_val]
      exact congrArg Block.spine (Fin.ext hjk.symm)
    exfalso
    have hidxp : (bp.val.idx : ℕ) = (ip : ℕ) := by rw [hbp]; rfl
    have hidxq : (bq.val.idx : ℕ) = (iq : ℕ) := by rw [hbq]; rfl
    have hdp : Block.exitDir (Block.spine k) bp.val = Slot.a ∨
        Block.exitDir (Block.spine k) bp.val = Slot.c := by
      rcases lt_or_gt_of_ne hik with h | h
      · exact Or.inl (exitDir_spine_lt (by omega))
      · exact Or.inr (exitDir_spine_gt (by omega))
    have hdq : Block.exitDir (Block.spine k) bq.val = Slot.a ∨
        Block.exitDir (Block.spine k) bq.val = Slot.c := by
      rcases lt_or_gt_of_ne hjk with h | h
      · exact Or.inl (exitDir_spine_lt (by omega))
      · exact Or.inr (exitDir_spine_gt (by omega))
    -- Enumeration size: the 4 combinations of `{a, c} × {a, c}`; none is rim adjacent.
    rcases hdp with h₁ | h₁ <;> rcases hdq with h₂ | h₂ <;>
      rw [h₁, h₂] at hrim <;> exact absurd hrim (by decide)

/-! ### Counting the chords -/

/-- A neighbour of `v` is a non-attachment vertex of a leaf pentagon. -/
theorem leaf_of_adj_v {u : Vtx m} (h : (G m).Adj (Vtx.v m) u) :
    ∃ (b : ValidBlock m) (s : Slot) (i : Fin (m + 1)) (x : Slot),
      u = Vtx.mk b s ∧ b.val = Block.leaf i x ∧ s ≠ x := by
  obtain ⟨⟨b, s⟩, rfl⟩ : ∃ r, u = some r := by
    cases u with
    | none => exact absurd rfl h.ne'
    | some r => exact ⟨r, rfl⟩
  obtain ⟨i, x, hb, hs⟩ := specialAdjVB_mk_iff b s |>.mp ((G_adj_v_mk_iff b s).mp h)
  exact ⟨b, s, i, x, rfl, hb, hs⟩

section Count

variable {c : Cycle (G m)} {p q : Vtx m} {P : (G' m).Walk p q}
variable (hP : P.IsPath) (hpq : p ≠ q)
variable (hvp : (G m).Adj (Vtx.v m) p) (hvq : (G m).Adj (Vtx.v m) q)
variable (hsupp : ∀ u, u ∈ c.walk.support ↔ u = Vtx.v m ∨ u ∈ P.support)
variable (hedge : ∀ e, e ∈ c.edges ↔ e = s(Vtx.v m, p) ∨ e = s(Vtx.v m, q) ∨ e ∈ P.edges)

include hP hpq hvp hvq hsupp hedge

/-- **Proposition 4.10, the branch through `v`.**

Chords split in two. Those *at* `v` land in the (at most two) leaf pentagons containing the
endpoints of `P`, each of which offers `v` only four vertices, and two of the resulting eight
edges are the cycle's own edges at `v`: at most `8 - 2 = 6`. Those *away from* `v` are rim edges
of a single pentagon (`sameBlock_of_chord`, i.e. Lemma 4.7), at most one per pentagon
(`slot_count`), and only four pentagons can carry one at all (`mem_specialBlocks`): at most 4.
Total `6 + 4 = 10`. -/
theorem chords_le_ten_of_mem_v : c.chords.encard ≤ 10 := by
  classical
  obtain ⟨bp, sp, ip, xp, rfl, hbp, hspx⟩ := leaf_of_adj_v hvp
  obtain ⟨bq, sq, iq, xq, rfl, hbq, hsqx⟩ := leaf_of_adj_v hvq
  have hpv : Vtx.mk bp sp ≠ Vtx.v m := Vtx.mk_ne_v bp sp
  have hqv : Vtx.mk bq sq ≠ Vtx.v m := Vtx.mk_ne_v bq sq
  -- The chords at `v`: `v` reaches only the four non-attachment slots of each of `bp`, `bq`.
  set Sp : Finset (Sym2 (Vtx m)) :=
    (univ.erase xp).image (fun s => s(Vtx.v m, Vtx.mk bp s)) with hSp
  set Sq : Finset (Sym2 (Vtx m)) :=
    (univ.erase xq).image (fun s => s(Vtx.v m, Vtx.mk bq s)) with hSq
  set pair : Finset (Sym2 (Vtx m)) :=
    {s(Vtx.v m, Vtx.mk bp sp), s(Vtx.v m, Vtx.mk bq sq)} with hpair
  set A : Finset (Sym2 (Vtx m)) := (Sp ∪ Sq) \ pair with hA
  -- The rim chords: at most one in each of four pentagons.
  set special : Finset (ValidBlock m) := {bp, bq, spineVB ip, spineVB iq} with hspecial
  set B : Finset (Sym2 (Vtx m)) := special.biUnion (fun b =>
    (rimSpanS (visitedSlots c b) \ usedRim c b).image
      (fun s => s(Vtx.mk b s, Vtx.mk b s.succ))) with hB
  -- ## Step 1: every chord lies in `A ∪ B`.
  have hsub : c.chords ⊆ ↑(A ∪ B) := by
    intro e he
    obtain ⟨hedgeSet, hsuppe, hnotc⟩ := he
    -- a chord at `v` is an edge to a visited vertex of `bp` or `bq`
    have hvChord : ∀ w : Vtx m, (G m).Adj (Vtx.v m) w → w ∈ c.walk.support →
        s(Vtx.v m, w) ∉ c.edges → s(Vtx.v m, w) ∈ A := by
      intro w hadjw hwsupp hwnot
      obtain ⟨bw, sw, iw, xw, rfl, hbw, hswx⟩ := leaf_of_adj_v hadjw
      have hwP : Vtx.mk bw sw ∈ P.support := by
        rcases (hsupp _).mp hwsupp with h | h
        · exact absurd h (Vtx.mk_ne_v bw sw)
        · exact h
      -- a visited leaf pentagon contains an endpoint of `P`
      have hbwb : (bw = bp ∧ xw = xp) ∨ (bw = bq ∧ xw = xq) := by
        have hx : ∀ b : ValidBlock m, ∀ i x i' x' : _, b.val = Block.leaf i x →
            b.val = Block.leaf i' x' → x = x' := by
          intro b i x i' x' h₁ h₂
          rw [h₁] at h₂
          exact (Block.leaf.inj h₂).2
        rcases leafBlock_of_mem_support hP hbw hwP rfl with h | h <;>
          rw [blockOf_mk, Option.some.injEq] at h <;> subst h
        · exact Or.inl ⟨rfl, hx _ _ _ _ _ hbw hbp⟩
        · exact Or.inr ⟨rfl, hx _ _ _ _ _ hbw hbq⟩
      rw [hA, Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · rcases hbwb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨sw, Finset.mem_erase.mpr ⟨hswx, Finset.mem_univ _⟩, rfl⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨sw, Finset.mem_erase.mpr ⟨hswx, Finset.mem_univ _⟩, rfl⟩)
      · rw [hpair, Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h) <;> exact hwnot (by rw [h]; exact (hedge _).mpr (by tauto))
    induction e with
    | _ u₁ u₂ =>
      have hadj : (G m).Adj u₁ u₂ := hedgeSet
      have h₁ : u₁ ∈ c.walk.support := hsuppe u₁ (by simp)
      have h₂ : u₂ ∈ c.walk.support := hsuppe u₂ (by simp)
      rw [Finset.coe_union, Set.mem_union]
      by_cases hu₁ : u₁ = Vtx.v m
      · subst hu₁
        exact Or.inl (hvChord u₂ hadj h₂ hnotc)
      by_cases hu₂ : u₂ = Vtx.v m
      · subst hu₂
        refine Or.inl ?_
        rw [Sym2.eq_swap]
        exact hvChord u₁ hadj.symm h₁ (by rwa [Sym2.eq_swap] at hnotc)
      -- neither endpoint is `v`: a rim chord of a single pentagon
      refine Or.inr ?_
      have hP₁ : u₁ ∈ P.support := by rcases (hsupp _).mp h₁ with h | h; exacts [absurd h hu₁, h]
      have hP₂ : u₂ ∈ P.support := by rcases (hsupp _).mp h₂ with h | h; exacts [absurd h hu₂, h]
      have hadj' : (G' m).Adj u₁ u₂ := G'_adj_of_G_adj_of_ne_v hadj hu₁ hu₂
      have hnotP : s(u₁, u₂) ∉ P.edges := fun h => hnotc ((hedge _).mpr (Or.inr (Or.inr h)))
      have hblk : blockOf u₁ = blockOf u₂ := sameBlock_of_chord P hadj' hP₁ hP₂ hnotP
      -- write both endpoints in the common block
      obtain ⟨b₁, t₁, rfl⟩ : ∃ (b : ValidBlock m) (t : Slot), u₁ = Vtx.mk b t := by
        cases u₁ with
        | none => exact absurd rfl hu₁
        | some r => exact ⟨r.1, r.2, rfl⟩
      obtain ⟨b₂, t₂, rfl⟩ : ∃ (b : ValidBlock m) (t : Slot), u₂ = Vtx.mk b t := by
        cases u₂ with
        | none => exact absurd rfl hu₂
        | some r => exact ⟨r.1, r.2, rfl⟩
      rw [blockOf_mk, blockOf_mk, Option.some.injEq] at hblk
      subst hblk
      -- the chord is a rim edge, indexed by some slot
      obtain ⟨t, ht⟩ := exists_rimEdge_index ((G_adj_same_block _ t₁ t₂).mp hadj)
      have hmapt : s(Vtx.mk b₁ t₁, Vtx.mk b₁ t₂) = s(Vtx.mk b₁ t, Vtx.mk b₁ t.succ) := by
        rcases Sym2.eq_iff.mp ht with ⟨h₁', h₂'⟩ | ⟨h₁', h₂'⟩
        · rw [h₁', h₂']
        · rw [h₁', h₂', Sym2.eq_swap]
      -- that slot is spanned but unused, so this pentagon carries a chord
      have htspan : t ∈ rimSpanS (visitedSlots c b₁) \ usedRim c b₁ := by
        rw [Finset.mem_sdiff, rimSpanS, Finset.mem_filter, mem_visitedSlots, mem_visitedSlots,
          mem_usedRim]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact hsuppe _ (by rw [hmapt]; simp)
        · exact hsuppe _ (by rw [hmapt]; simp)
        · rw [← hmapt]; exact hnotc
      -- hence this pentagon is one of the four special ones
      have hspec : b₁ ∈ special := by
        have := mem_specialBlocks (sp := sp) (sq := sq) hbp hbq
          (rimAdj_exitSlots_of_chord hP hpv hqv hsupp hedge ⟨t, htspan⟩)
        rw [hspecial]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hB, Finset.mem_coe, Finset.mem_biUnion]
      exact ⟨b₁, hspec, Finset.mem_image.mpr ⟨t, htspan, hmapt.symm⟩⟩
  -- ## Step 2: `A` has at most six elements.
  have hcardA : A.card ≤ 6 := by
    have hSpq : pair ⊆ Sp ∪ Sq := by
      rw [hpair]
      intro e he
      rw [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨sp, Finset.mem_erase.mpr ⟨hspx, Finset.mem_univ _⟩, rfl⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨sq, Finset.mem_erase.mpr ⟨hsqx, Finset.mem_univ _⟩, rfl⟩)
    have hpaircard : pair.card = 2 := by
      rw [hpair, Finset.card_insert_of_notMem, Finset.card_singleton]
      rw [Finset.mem_singleton]
      intro h
      exact hpq (Sym2.congr_right.mp h)
    have hunion : (Sp ∪ Sq).card ≤ 8 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have h₁ : Sp.card ≤ 4 := by
        refine le_trans (Finset.card_image_le) ?_
        rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
        simp [Slot.card_eq]
      have h₂ : Sq.card ≤ 4 := by
        refine le_trans (Finset.card_image_le) ?_
        rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
        simp [Slot.card_eq]
      omega
    have hdisj : Disjoint A pair := Finset.sdiff_disjoint
    have : A.card + 2 ≤ 8 := by
      rw [← hpaircard, ← Finset.card_union_of_disjoint hdisj]
      exact le_trans (Finset.card_le_card (Finset.union_subset Finset.sdiff_subset hSpq)) hunion
    omega
  -- ## Step 3: `B` has at most four elements — one chord in each of four pentagons.
  have hcardB : B.card ≤ 4 := by
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 ?_) ?_
    · intro b _
      exact le_trans Finset.card_image_le (chordSlots_card_le_one hP hpv hqv hsupp hedge b)
    · rw [smul_eq_mul, mul_one, hspecial]
      refine le_trans (Finset.card_insert_le _ _) ?_
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      exact Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp))
  -- ## Step 4: add up.
  calc c.chords.encard
      ≤ (↑(A ∪ B) : Set (Sym2 (Vtx m))).encard := Set.encard_le_encard hsub
    _ = ((A ∪ B).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ (10 : ℕ) := by
        refine Nat.cast_le.mpr ?_
        exact le_trans (Finset.card_union_le _ _) (by omega)
    _ = 10 := by rfl

end Count

end Assemble

/-! ## Lemmas 4.8, 4.9 and Proposition 4.10 -/

/-- **Proposition 4.10.** Every cycle of `Gₘ` has at most 10 chords.

A cycle avoiding `v` lies in a single pentagon (Lemma 4.7), so it has at most five chords. A
cycle *through* `v` is cut open at `v` into a `v`-avoiding path `P` in `G'ₘ` between two
neighbours of `v`, and then `chords_le_ten_of_mem_v` performs the paper's count of Lemmas 4.8
and 4.9: at most six chords at `v`, and at most four rim chords, one in each of the four
pentagons that the two endpoints of `P` can reach. -/
theorem cycle_chords_le_ten (m : ℕ) (_hm : 1 ≤ m) (c : Cycle (G m)) :
    c.chords.encard ≤ 10 := by
  by_cases hv : Vtx.v m ∈ c.walk.support
  · obtain ⟨p, q, P, hP, -, hpq, hvp, hvq, hsupp, hedge⟩ := exists_vPath c hv
    exact chords_le_ten_of_mem_v hP hpq hvp hvq hsupp hedge
  · exact le_trans (cycle_chords_le_five_of_notMem_v c hv) (by decide)


end Erdos1091

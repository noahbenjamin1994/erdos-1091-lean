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
import Erdos1091.Degenerate
import Mathlib.Tactic.FinCases

/-!
# Lemmas 4.3, 4.4 and Proposition 4.5: `Gₘ` is not 3-colorable

Assume a proper 3-coloring exists. Write `α` for the colour of `v`, and `β, γ` for the other
two colours.

* **Lemma 4.3 (leaf forcing).** In each leaf block `L_{i,x}`, deleting the attachment vertex
  leaves a 4-vertex path whose vertices are all adjacent to `v`, so they only use `β, γ` and
  must alternate. The two ends of that path are the pentagon-neighbours of the attachment
  vertex and get *different* colours, so the attachment vertex can use neither `β` nor `γ`:
  it has colour `α`.
* **Lemma 4.4 (spine propagation).** Consequently every spine vertex carrying a leaf avoids
  `α`. On a spine pentagon `Q` this forces one more slot to take `α`, in three cases:
  `Q = S₀` and `Q = S_i` internal force `Q[c] = α`; the terminal `Q = S_m` forces `Q[a] = α`.
* **Proposition 4.5.** Propagating along the spine gives `S_i[c] = α` for all `i < m`, hence
  `S_m[a] ≠ α`, while Lemma 4.4(3) gives `S_m[a] = α`. Contradiction.

The asymmetry of the construction is what makes the two ends of the induction disagree:
`S₀` has no `c`-leaf (so `S₀[c]` is free to take `α`) and `S_m` has no `a`-leaf.

Together with `Erdos1091.proper_subgraph_chromaticNumber_le_three` this pins
`χ(Gₘ) = 4` exactly.

## Shape of the induction

The spine is walked once, by induction on the *natural number* index `n = (i : ℕ)` rather
than on `Fin (m+1)` — `Fin` induction would force us to carry `i.isLt` through every step.
The invariant transported from `S_i` to `S_{i+1}` is a single fact,

  `A n :  (i : ℕ) = n  →  C (S_i[a]) ≠ α`   (`spine_a_ne_alpha_aux`),

and the step is factored through the *non-recursive*

  `C (S_i[a]) ≠ α  →  C (S_i[c]) = α`       (`spine_c_of_a`, Lemma 4.4(1)/(2)),

so that Lemma 4.4 is proved once and the induction only has to chase the spine edge
`S_i[c] — S_{i+1}[a]`. The two ends of the walk use the two asymmetries of the construction:

* `n = 0` is *not* a vacuous base case — it is where the `a`-leaf of `S₀` lives, and leaf
  forcing gives `C (S₀[a]) ≠ α` outright.
* at `n = m` the `a`-leaf is *absent*, so `A m` is the only source of `C (S_m[a]) ≠ α`, while
  the `c`-leaf that only `S_m` has makes all of `b, c, d, e` avoid `α` and Lemma 4.4(3) gives
  `C (S_m[a]) = α`. That is the contradiction.

Had the construction been made symmetric, either `S₀` would lack its `a`-leaf (no base case)
or `S_m` would lack its `c`-leaf (no contradiction at the far end).

## References

* [APSSV26b] arXiv:2604.06609, Lemmas 4.3, 4.4 and Proposition 4.5.
-/

namespace Erdos1091

open SimpleGraph

variable {m : ℕ}

/-! ### Slot arithmetic used by the pentagon arguments

Walking a pentagon from a chosen slot `x`: the five slots are `x`, `x.succ`, `x.succ.succ`,
`x.succ.succ.succ`, `x.succ.succ.succ.succ`, the last of which is `x.pred`. All of the facts
below are enumerations over the 5-element type `Slot`. -/

namespace Slot

/-- Four `succ`-steps is one `pred`-step. Enumeration size: 5 slots. -/
theorem succ4_eq_pred (s : Slot) : s.succ.succ.succ.succ = s.pred := by revert s; decide

/-- The far end of the four-step walk closes the pentagon. Enumeration size: 5 slots. -/
@[simp] theorem rimAdjB_succ4_self (s : Slot) : rimAdjB s.succ.succ.succ.succ s = true := by
  revert s; decide

/-- None of the four other slots of a pentagon is the slot we started from.
Enumeration size: 5 slots each. -/
@[simp] theorem succ_ne_self (s : Slot) : s.succ ≠ s := by revert s; decide

@[simp] theorem succ2_ne_self (s : Slot) : s.succ.succ ≠ s := by revert s; decide

@[simp] theorem succ3_ne_self (s : Slot) : s.succ.succ.succ ≠ s := by revert s; decide

@[simp] theorem succ4_ne_self (s : Slot) : s.succ.succ.succ.succ ≠ s := by revert s; decide

end Slot

/-! ### Block-validity facts

Which leaf blocks exist. `b`, `d`, `e` always; the `a`-leaf only on `S₀`, the `c`-leaf only
on `S_m`. These are the two asymmetries that make Proposition 4.5 close. -/

/-- The `b`-, `d`- and `e`-leaves exist on every spine block. -/
theorem leaf_bde_valid (i : Fin (m + 1)) {x : Slot} (hx : x = .b ∨ x = .d ∨ x = .e) :
    (Block.leaf i x : Block m).validB = true := by
  rcases hx with rfl | rfl | rfl <;> rfl

/-- Spine blocks are always valid; this is the canonical form of that proof. -/
theorem spineVB_mk (i : Fin (m + 1)) (hs : (Block.spine i : Block m).validB = true) :
    (⟨Block.spine i, hs⟩ : ValidBlock m) = spineVB i := rfl

/-- Lifting a `G'ₘ`-edge to `Gₘ`. -/
theorem adj_of_adj' {u w : Vtx m} (h : (G' m).Adj u w) : (G m).Adj u w := G'_le_G h

section Coloring

variable (C : (G m).Coloring (Fin 3))

/-- The colour of the special vertex `v`; the paper's `α`. -/
def alphaColor (C : (G m).Coloring (Fin 3)) : Fin 3 := C (Vtx.v m)

/-- A 4-vertex path whose vertices all avoid one fixed colour must alternate between the
remaining two, so its endpoints receive different colours.

This is the combinatorial core of Lemma 4.3. Enumeration size: at most `3⁵ = 243` colourings
of `α` and four vertices from `Fin 3`, cut down by the three adjacency constraints; it is a
statement about `Fin 3` only and carries no dependence on `m`. -/
theorem path_four_alternates (α c₁ c₂ c₃ c₄ : Fin 3)
    (h₁ : c₁ ≠ α) (h₂ : c₂ ≠ α) (h₃ : c₃ ≠ α) (h₄ : c₄ ≠ α)
    (e₁ : c₁ ≠ c₂) (e₂ : c₂ ≠ c₃) (e₃ : c₃ ≠ c₄) :
    c₁ ≠ c₄ := by
  fin_cases α <;> fin_cases c₁ <;> fin_cases c₂ <;> fin_cases c₃ <;> fin_cases c₄ <;>
    simp_all

/-- With only three colours available, a vertex adjacent to two differently-coloured
neighbours that both avoid `α` is forced onto `α`.

This is the second half of Lemma 4.3. Enumeration size: `3⁴ = 81` colourings. -/
theorem eq_of_ne_two_ne (α c₁ c₄ d : Fin 3) (h₁ : c₁ ≠ α) (h₄ : c₄ ≠ α) (h : c₁ ≠ c₄)
    (d₁ : d ≠ c₁) (d₄ : d ≠ c₄) : d = α := by
  fin_cases α <;> fin_cases c₁ <;> fin_cases c₄ <;> fin_cases d <;> simp_all

/-- **Lemma 4.3 (leaf forcing).** In every leaf block the attachment vertex takes the colour
of `v`.

The four non-attachment slots `x.succ, x.succ.succ, x.succ.succ.succ, x.pred` are all adjacent
to `v`, so they avoid `α`; they form a path along the rim, so by `path_four_alternates` its two
ends `x.succ` and `x.pred` — which are exactly the rim neighbours of the attachment slot `x` —
disagree. `eq_of_ne_two_ne` then forces `x` onto `α`. -/
theorem leaf_attachment_eq_alpha (m : ℕ) (C : (G m).Coloring (Fin 3))
    (i : Fin (m + 1)) (x : Slot) (hb : (Block.leaf i x).validB = true) :
    C (Vtx.mk ⟨Block.leaf i x, hb⟩ x) = alphaColor C := by
  set b : ValidBlock m := ⟨Block.leaf i x, hb⟩ with hbdef
  -- every non-attachment vertex of the leaf block is adjacent to `v`, hence avoids `α`
  have hv : ∀ s : Slot, s ≠ x → C (Vtx.mk b s) ≠ alphaColor C := by
    intro s hs
    exact C.valid ((G_adj_mk_v_iff b s).mpr ⟨i, x, rfl, hs⟩)
  -- rim edges of the pentagon are edges of `Gₘ`
  have hrim : ∀ s t : Slot, Slot.rimAdjB s t = true → C (Vtx.mk b s) ≠ C (Vtx.mk b t) :=
    fun s t h => C.valid ((G_adj_same_block b s t).mpr h)
  -- the two ends of the 4-vertex path disagree
  have hends : C (Vtx.mk b x.succ) ≠ C (Vtx.mk b x.succ.succ.succ.succ) :=
    path_four_alternates _ _ _ _ _
      (hv _ (Slot.succ_ne_self x)) (hv _ (Slot.succ2_ne_self x))
      (hv _ (Slot.succ3_ne_self x)) (hv _ (Slot.succ4_ne_self x))
      (hrim _ _ (Slot.rimAdjB_succ x.succ)) (hrim _ _ (Slot.rimAdjB_succ x.succ.succ))
      (hrim _ _ (Slot.rimAdjB_succ x.succ.succ.succ))
  exact eq_of_ne_two_ne _ _ _ _ (hv _ (Slot.succ_ne_self x)) (hv _ (Slot.succ4_ne_self x))
    hends (hrim _ _ (Slot.rimAdjB_succ x)) (hrim _ _ (Slot.rimAdjB_succ4_self x)).symm

/-- Every spine vertex that carries a leaf block avoids the colour `α`: the leaf's attachment
vertex is adjacent to it and already has colour `α` by Lemma 4.3. -/
theorem spine_with_leaf_ne_alpha (m : ℕ) (C : (G m).Coloring (Fin 3))
    (i : Fin (m + 1)) (x : Slot) (hb : (Block.leaf i x).validB = true)
    (hs : (Block.spine i).validB = true) :
    C (Vtx.mk ⟨Block.spine i, hs⟩ x) ≠ alphaColor C := by
  rw [spineVB_mk i hs]
  have hadj : (G m).Adj (Vtx.mk (spineVB i) x) (Vtx.mk (⟨Block.leaf i x, hb⟩ : ValidBlock m) x) :=
    adj_of_adj' (G'_adj_leaf_spine i x hb).symm
  have := C.valid hadj
  rw [leaf_attachment_eq_alpha m C i x hb] at this
  exact this

/-- Colour propagation around one pentagon, cases (1) and (2) of Lemma 4.4: if the four slots
`a, b, d, e` all avoid `α`, then `c` takes `α`.

Enumeration size: `3⁶ = 729` colourings of `α` and the five pentagon slots, constrained by the
five rim edges; a pure `Fin 3` statement, independent of `m`. -/
theorem pentagon_forces_c (α ca cb cc cd ce : Fin 3)
    (hab : ca ≠ cb) (hbc : cb ≠ cc) (hcd : cc ≠ cd) (hde : cd ≠ ce) (hea : ce ≠ ca)
    (ha : ca ≠ α) (hb : cb ≠ α) (hd : cd ≠ α) (he : ce ≠ α) :
    cc = α := by
  fin_cases α <;> fin_cases ca <;> fin_cases cb <;> fin_cases cc <;> fin_cases cd <;>
    fin_cases ce <;> simp_all

/-- Colour propagation around one pentagon, case (3) of Lemma 4.4: if `b, c, d, e` all avoid
`α`, then `a` takes `α`. This is the terminal-block case, used only at `S_m`.

Enumeration size: `3⁶ = 729`, as above. -/
theorem pentagon_forces_a (α ca cb cc cd ce : Fin 3)
    (hab : ca ≠ cb) (hbc : cb ≠ cc) (hcd : cc ≠ cd) (hde : cd ≠ ce) (hea : ce ≠ ca)
    (hb : cb ≠ α) (hc : cc ≠ α) (hd : cd ≠ α) (he : ce ≠ α) :
    ca = α := by
  fin_cases α <;> fin_cases ca <;> fin_cases cb <;> fin_cases cc <;> fin_cases cd <;>
    fin_cases ce <;> simp_all

/-! ### Lemma 4.4 and the walk down the spine -/

/-- The rim edges of the `i`-th spine pentagon, as colour inequalities. -/
private theorem spine_rim (i : Fin (m + 1)) (s t : Slot) (h : Slot.rimAdjB s t = true) :
    C (Vtx.mk (spineVB i) s) ≠ C (Vtx.mk (spineVB i) t) :=
  C.valid ((G_adj_same_block (spineVB i) s t).mpr h)

/-- The `b`-, `d`- and `e`-slots of every spine pentagon avoid `α`, because those leaves
always exist (Lemma 4.3). -/
private theorem spine_bde_ne_alpha (i : Fin (m + 1)) {x : Slot}
    (hx : x = .b ∨ x = .d ∨ x = .e) : C (Vtx.mk (spineVB i) x) ≠ alphaColor C := by
  have := spine_with_leaf_ne_alpha m C i x (leaf_bde_valid i hx) rfl
  rwa [spineVB_mk i rfl] at this

/-- **Lemma 4.4(1)/(2), the local step.** On any spine pentagon, if `Q[a]` avoids `α` then
`Q[c]` takes `α`.

This is the paper's argument for cases (1) and (2) verbatim: `Q[b], Q[d], Q[e]` avoid `α`
because they carry leaves, `Q[a]` avoids `α` by hypothesis, and `pentagon_forces_c` closes it.
Case (1) (`Q = S₀`) and case (2) (`Q = S_i`, `1 ≤ i ≤ m-1`) differ only in *why* `Q[a]` avoids
`α` — the `a`-leaf for `S₀`, the incoming spine edge otherwise — which is exactly what
`spine_a_ne_alpha_aux` below supplies. -/
theorem spine_c_of_a (i : Fin (m + 1)) (ha : C (Vtx.mk (spineVB i) Slot.a) ≠ alphaColor C) :
    C (Vtx.mk (spineVB i) Slot.c) = alphaColor C :=
  pentagon_forces_c _ _ _ _ _ _
    (spine_rim C i .a .b (by decide)) (spine_rim C i .b .c (by decide))
    (spine_rim C i .c .d (by decide)) (spine_rim C i .d .e (by decide))
    (spine_rim C i .e .a (by decide))
    ha (spine_bde_ne_alpha C i (Or.inl rfl)) (spine_bde_ne_alpha C i (Or.inr (Or.inl rfl)))
    (spine_bde_ne_alpha C i (Or.inr (Or.inr rfl)))

/-- **The walk down the spine.** For every `i`, the slot `S_i[a]` avoids `α`.

Induction on `n = (i : ℕ)`. At `n = 0` this is leaf forcing applied to the `a`-leaf of `S₀`
(which exists precisely because the construction is asymmetric). At `n + 1` the previous
block gives `S_n[c] = α` by `spine_c_of_a`, and the spine edge `S_n[c] — S_{n+1}[a]` transfers
that to `S_{n+1}[a] ≠ α`. -/
private theorem spine_a_ne_alpha_aux :
    ∀ (n : ℕ) (i : Fin (m + 1)), (i : ℕ) = n →
      C (Vtx.mk (spineVB i) Slot.a) ≠ alphaColor C := by
  intro n
  induction n with
  | zero =>
      intro i hi
      -- the `a`-leaf lives on `S₀` and only on `S₀`
      have hb : (Block.leaf i Slot.a : Block m).validB = true := by
        simp [Block.validB, hi]
      have := spine_with_leaf_ne_alpha m C i Slot.a hb rfl
      rwa [spineVB_mk i rfl] at this
  | succ n ih =>
      intro i hi
      have hlt : n < m + 1 := by have := i.isLt; omega
      have hprev : C (Vtx.mk (spineVB (⟨n, hlt⟩ : Fin (m + 1))) Slot.c) = alphaColor C :=
        spine_c_of_a C _ (ih ⟨n, hlt⟩ rfl)
      have hadj : (G m).Adj (Vtx.mk (spineVB (⟨n, hlt⟩ : Fin (m + 1))) Slot.c)
          (Vtx.mk (spineVB i) Slot.a) :=
        adj_of_adj' (G'_adj_spine_spine (by simpa using hi.symm))
      have hne := C.valid hadj
      rw [hprev] at hne
      exact fun h => hne h.symm

set_option linter.unusedVariables false in
/-- **Lemma 4.4(1)/(2).** On `S₀` and on every internal spine block, `Q[c]` takes colour `α`.

(`hi` records the paper's range `0 ≤ i ≤ m - 1`; the argument in fact needs no constraint on
`i`, since the `b`, `d`, `e` leaves exist everywhere and `S_i[a] ≠ α` holds for every `i`.
It is at `i = m` that the *conclusion* becomes contradictory — see `G_not_colorable_three`.) -/
theorem spine_c_eq_alpha (m : ℕ) (C : (G m).Coloring (Fin 3)) (i : Fin (m + 1))
    (hi : (i : ℕ) < m) (hs : (Block.spine i).validB = true) :
    C (Vtx.mk ⟨Block.spine i, hs⟩ Slot.c) = alphaColor C := by
  rw [spineVB_mk i hs]
  exact spine_c_of_a C i (spine_a_ne_alpha_aux C (i : ℕ) i rfl)

set_option linter.unusedVariables false in
/-- **Lemma 4.4(3).** On the terminal block `S_m`, `Q[a]` takes colour `α`.

Here the `c`-leaf — which exists only on `S_m` — puts `S_m[c]` in the same position as
`S_m[b], S_m[d], S_m[e]`, so all four of `b, c, d, e` avoid `α` and `pentagon_forces_a`
applies. -/
theorem spine_last_a_eq_alpha (m : ℕ) (hm : 1 ≤ m) (C : (G m).Coloring (Fin 3))
    (i : Fin (m + 1)) (hi : (i : ℕ) = m) (hs : (Block.spine i).validB = true) :
    C (Vtx.mk ⟨Block.spine i, hs⟩ Slot.a) = alphaColor C := by
  rw [spineVB_mk i hs]
  -- the `c`-leaf lives on `S_m` and only on `S_m`
  have hc : (Block.leaf i Slot.c : Block m).validB = true := by
    simp [Block.validB, hi]
  have hcne : C (Vtx.mk (spineVB i) Slot.c) ≠ alphaColor C := by
    have := spine_with_leaf_ne_alpha m C i Slot.c hc rfl
    rwa [spineVB_mk i rfl] at this
  exact pentagon_forces_a _ _ _ _ _ _
    (spine_rim C i .a .b (by decide)) (spine_rim C i .b .c (by decide))
    (spine_rim C i .c .d (by decide)) (spine_rim C i .d .e (by decide))
    (spine_rim C i .e .a (by decide))
    (spine_bde_ne_alpha C i (Or.inl rfl)) hcne
    (spine_bde_ne_alpha C i (Or.inr (Or.inl rfl)))
    (spine_bde_ne_alpha C i (Or.inr (Or.inr rfl)))

set_option linter.unusedVariables false in
/-- Propagation along the spine: `S_i[c] = α` forces `S_{i+1}[a] ≠ α`, and by induction
`S_m[a] ≠ α`. -/
theorem spine_last_a_ne_alpha (m : ℕ) (hm : 1 ≤ m) (C : (G m).Coloring (Fin 3))
    (i : Fin (m + 1)) (hi : (i : ℕ) = m) (hs : (Block.spine i).validB = true) :
    C (Vtx.mk ⟨Block.spine i, hs⟩ Slot.a) ≠ alphaColor C := by
  rw [spineVB_mk i hs]
  exact spine_a_ne_alpha_aux C (i : ℕ) i rfl

end Coloring

set_option linter.unusedVariables false in
/-- **Proposition 4.5.** `Gₘ` is not 3-colorable.

At the terminal block `S_m`, Lemma 4.4(3) gives `S_m[a] = α` while the walk down the spine
gives `S_m[a] ≠ α`. -/
theorem G_not_colorable_three (m : ℕ) (hm : 1 ≤ m) : ¬ (G m).Colorable 3 := by
  rintro ⟨C⟩
  have hlast : ((Fin.last m : Fin (m + 1)) : ℕ) = m := by simp
  exact spine_last_a_ne_alpha m hm C (Fin.last m) hlast rfl
    (spine_last_a_eq_alpha m hm C (Fin.last m) hlast rfl)

/-! ### An explicit 4-coloring

`decide` is not an option here: `m` is a parameter. Instead we exhibit a colouring by block
*position*, using colour `3` only on `v` and on the leaf attachment vertices (which are the
only vertices not adjacent to `v`), and colours `0, 1, 2` everywhere else.

* Spine pentagons get the fixed pattern `a ↦ 0, b ↦ 1, c ↦ 2, d ↦ 0, e ↦ 1`. The rim is
  proper, and the spine edge `S_i[c] — S_{i+1}[a]` is proper because `2 ≠ 0`.
* In the leaf block `L_{i,x}` the attachment slot `x` gets `3` and the remaining four slots
  are 2-coloured `0, 1, 0, 1` along the path `x.succ, x.succ.succ, x.succ.succ.succ, x.pred`.
  This is proper on the rim (the two ends of the path, `x.succ ↦ 0` and `x.pred ↦ 1`, differ,
  and both differ from `3`), it keeps every neighbour of `v` off colour `3`, and the
  attachment edge `L_{i,x}[x] — S_i[x]` is proper because the spine never uses `3`.

All slot-level checks are enumerations over `Slot`, sizes noted at each lemma. -/

/-- The colour pattern on a spine pentagon. -/
def spineColor : Slot → Fin 4
  | .a => 0 | .b => 1 | .c => 2 | .d => 0 | .e => 1

/-- The colour pattern on the leaf block attached at slot `x`: colour `3` on the attachment
slot, then `0, 1, 0, 1` along the rim path away from it. -/
def leafColor (x s : Slot) : Fin 4 :=
  if s = x then 3 else if s = x.succ ∨ s = x.succ.succ.succ then 0 else 1

/-- Enumeration size: `5 * 5 = 25` pairs of slots. -/
theorem spineColor_rim : ∀ s t : Slot, Slot.rimAdjB s t = true → spineColor s ≠ spineColor t := by
  decide

/-- Enumeration size: 5 slots. -/
theorem spineColor_ne_three : ∀ s : Slot, spineColor s ≠ 3 := by decide

/-- Enumeration size: 5 slots. -/
@[simp] theorem leafColor_self (x : Slot) : leafColor x x = 3 := by simp [leafColor]

/-- Only the attachment slot of a leaf block uses colour `3`, so no neighbour of `v` does.
Enumeration size: `5 * 5 = 25` pairs of slots. -/
theorem leafColor_ne_three : ∀ x s : Slot, s ≠ x → leafColor x s ≠ 3 := by decide

/-- The leaf pattern is proper on the rim. Enumeration size: `5³ = 125` triples of slots. -/
theorem leafColor_rim :
    ∀ x s t : Slot, Slot.rimAdjB s t = true → leafColor x s ≠ leafColor x t := by decide

/-- The explicit 4-colouring of `Gₘ`. -/
def color4 : Vtx m → Fin 4
  | none => 3
  | some (b, s) =>
    match b.val with
    | .spine _ => spineColor s
    | .leaf _ x => leafColor x s

@[simp] theorem color4_v : color4 (Vtx.v m) = 3 := rfl

theorem color4_spine {b : ValidBlock m} {i : Fin (m + 1)} (h : b.val = Block.spine i) (s : Slot) :
    color4 (Vtx.mk b s) = spineColor s := by
  obtain ⟨bv, hbv⟩ := b
  subst h
  rfl

theorem color4_leaf {b : ValidBlock m} {i : Fin (m + 1)} {x : Slot}
    (h : b.val = Block.leaf i x) (s : Slot) : color4 (Vtx.mk b s) = leafColor x s := by
  obtain ⟨bv, hbv⟩ := b
  subst h
  rfl

/-- Adjacent vertices of `Gₘ` get different `color4` values. -/
theorem color4_valid {u w : Vtx m} (h : (G m).Adj u w) : color4 u ≠ color4 w := by
  match u, w with
  | none, none => exact absurd rfl h.ne
  | none, some (b, s) =>
      obtain ⟨i, x, hbv, hsx⟩ :=
        (specialAdjVB_mk_iff b s).mp ((G_adj_v_mk_iff b s).mp h)
      show color4 (Vtx.v m) ≠ color4 (Vtx.mk b s)
      rw [color4_v, color4_leaf hbv]
      exact (leafColor_ne_three x s hsx).symm
  | some (b, s), none =>
      obtain ⟨i, x, hbv, hsx⟩ := (G_adj_mk_v_iff b s).mp h
      show color4 (Vtx.mk b s) ≠ color4 (Vtx.v m)
      rw [color4_v, color4_leaf hbv]
      exact leafColor_ne_three x s hsx
  | some (b, s), some (b', t) =>
      show color4 (Vtx.mk b s) ≠ color4 (Vtx.mk b' t)
      rcases (G_adj_mk_iff b b' s t).mp h with ⟨rfl, hrim⟩ | hin | hin
      · -- a rim edge of a common block
        obtain ⟨bv, hbv⟩ := b
        cases bv with
        | spine i => rw [color4_spine rfl, color4_spine rfl]; exact spineColor_rim s t hrim
        | leaf i x => rw [color4_leaf rfl, color4_leaf rfl]; exact leafColor_rim x s t hrim
      · rcases (interAdjVB_mk_mk_iff b b' s t).mp hin with
          ⟨i, x, hb, hb', hs, ht⟩ | ⟨i, j, hb, hb', -, hs, ht⟩
        · -- the leaf attachment edge: the leaf side uses `3`, the spine side never does
          rw [color4_leaf hb, color4_spine hb', hs, leafColor_self]
          exact fun hh => spineColor_ne_three t hh.symm
        · -- the spine edge `S_i[c] — S_j[a]`
          rw [color4_spine hb, color4_spine hb', hs, ht]
          decide
      · rcases (interAdjVB_mk_mk_iff b' b t s).mp hin with
          ⟨i, x, hb', hb, ht, hs⟩ | ⟨i, j, hb', hb, -, ht, hs⟩
        · rw [color4_spine hb, color4_leaf hb', ht, leafColor_self]
          exact spineColor_ne_three s
        · rw [color4_spine hb, color4_spine hb', hs, ht]
          decide

set_option linter.unusedVariables false in
/-- `Gₘ` is 4-colorable, via the explicit pattern `color4`. -/
theorem G_colorable_four (m : ℕ) (hm : 1 ≤ m) : (G m).Colorable 4 :=
  ⟨Coloring.mk color4 fun {_ _} h => color4_valid h⟩

/-- `χ(Gₘ) = 4`, combining Proposition 4.5 with 4-colorability. -/
theorem G_chromaticNumber (m : ℕ) (hm : 1 ≤ m) : (G m).chromaticNumber = 4 := by
  have h : (G m).chromaticNumber = (3 : ℕ) + 1 :=
    chromaticNumber_eq_iff_colorable_not_colorable.mpr
      ⟨by simpa using G_colorable_four m hm, G_not_colorable_three m hm⟩
  rw [h]
  rfl

end Erdos1091

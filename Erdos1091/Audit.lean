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

import Erdos1091.Main

/-!
# Axiom audit

This file is **not** imported by anything else; it exists solely to be built so that the
`#print axioms` output below can be captured as machine-checkable evidence.

Every node of the Section 4 lemma tree is listed. The **only** admissible output for each line
is Mathlib's standard trio

```
'…' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Anything else — in particular the extra axioms that an unfinished proof introduces — is an
audit failure. The captured output lives in
`logs/axioms.txt` and is published as `output/erdos-1091-lean/lean/axioms.txt`.

Note that several declarations are *proved without any axioms at all*, in which case Lean
prints `does not depend on any axioms`; that is strictly stronger and also passes.
-/

namespace Erdos1091

/-! ### Construction (vertex type, adjacency, counting, degrees, connectivity) -/

#print axioms Erdos1091.card_validBlock
#print axioms Erdos1091.card_vtx
#print axioms Erdos1091.degree_eq_three
#print axioms Erdos1091.G'_degree_le_three
#print axioms Erdos1091.G'_reachable

/-! ### Lemma 4.2 — `Gₘ` is `K₄`-free -/

#print axioms Erdos1091.G'_no_triangle
#print axioms Erdos1091.G'_cliqueFree_three
#print axioms Erdos1091.neighbor_v_cliqueFree_three
#print axioms Erdos1091.G_cliqueFree_four

/-! ### Lemma 4.3 — leaf forcing -/

#print axioms Erdos1091.path_four_alternates
#print axioms Erdos1091.leaf_attachment_eq_alpha
#print axioms Erdos1091.spine_with_leaf_ne_alpha

/-! ### Lemma 4.4 — the spine pentagon forces colour α -/

#print axioms Erdos1091.pentagon_forces_c
#print axioms Erdos1091.pentagon_forces_a
#print axioms Erdos1091.spine_c_of_a
#print axioms Erdos1091.spine_c_eq_alpha

/-! ### Proposition 4.5 — `Gₘ` is not 3-colourable (and `χ = 4`) -/

#print axioms Erdos1091.G_not_colorable_three
#print axioms Erdos1091.G_colorable_four
#print axioms Erdos1091.G_chromaticNumber

/-! ### Proposition 4.6 — proper subgraphs are 2-degenerate, hence 3-colourable -/

#print axioms Erdos1091.colorable_three_of_isTwoDegenerate
#print axioms Erdos1091.proper_subgraph_isTwoDegenerate
#print axioms Erdos1091.proper_subgraph_chromaticNumber_le_three

/-! ### Lemma 4.7 — every cycle of `G'ₘ` lies inside a single pentagon block -/

#print axioms Erdos1091.IsSide.isBridge
#print axioms Erdos1091.interAdj_isBridge
#print axioms Erdos1091.G'_cycle_within_block
#print axioms Erdos1091.cycle_chords_le_five_of_notMem_v

/-! ### Lemmas 4.8 / 4.9 — chord counting for cycles through `v` -/

#print axioms Erdos1091.exists_vPath
#print axioms Erdos1091.exit_of_mem_P_edges
#print axioms Erdos1091.chordSlots_card_le_one
#print axioms Erdos1091.mem_specialBlocks
#print axioms Erdos1091.chords_le_ten_of_mem_v

/-! ### Proposition 4.10 — every cycle has at most 10 chords -/

#print axioms Erdos1091.cycle_chords_le_ten

/-! ### Transport lemmas (general-purpose, new in this development) -/

#print axioms Erdos1091.cliqueFree_map_equiv
#print axioms Erdos1091.chromaticNumber_map_equiv
#print axioms Erdos1091.subgraph_chromaticNumber_congr
#print axioms Erdos1091.subgraph_chromaticNumber_map_equiv
#print axioms Erdos1091.cycle_chords_congr
#print axioms Erdos1091.cycle_chords_map_equiv

/-! ### Theorem 4.1 and the target statement -/

#print axioms Erdos1091.size_bounds
#print axioms Erdos1091.theorem_4_1
#print axioms Erdos1091.erdos_1091.variants.counterexample

end Erdos1091

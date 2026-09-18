# STATUS —— Erdős 1091 形式化进度

> 本表由 `.work/erdos-1091-lean/formalization/gen_status.py` **扫描源码生成**,
> 每一行的 `proved`/`sorry` 都是读文件数出来的,不是凭印象写的。

**总计:217 条声明,proved 217 / sorry 0。**

| 编号 | Lean 名称 | 文件:行 | 状态 | 说明 |
|---|---|---|---|---|
|  | `IsSide` | `Erdos1091/Chords.lean:98` | ✅ proved |  |
|  | `IsSide.mem_edges` | `Erdos1091/Chords.lean:102` | ✅ proved |  |
|  | `IsSide.isBridge` | `Erdos1091/Chords.lean:116` | ✅ proved |  |
|  | `IsSide.notMem_support` | `Erdos1091/Chords.lean:125` | ✅ proved |  |
|  | `blockOf` | `Erdos1091/Chords.lean:148` | ✅ proved |  |
|  | `blockOf_mk` | `Erdos1091/Chords.lean:152` | ✅ proved |  |
|  | `blockOf_v` | `Erdos1091/Chords.lean:154` | ✅ proved |  |
|  | `Block.idx` | `Erdos1091/Chords.lean:157` | ✅ proved |  |
|  | `exists_mk_of_G'_adj` | `Erdos1091/Chords.lean:162` | ✅ proved |  |
|  | `isSide_leaf` | `Erdos1091/Chords.lean:173` | ✅ proved |  |
|  | `isSide_spine` | `Erdos1091/Chords.lean:202` | ✅ proved |  |
|  | `interAdj_isBridge` | `Erdos1091/Chords.lean:247` | ✅ proved |  |
|  | `blockOf_eq_of_walk` | `Erdos1091/Chords.lean:281` | ✅ proved |  |
|  | `blockOf_eq_of_G'_adj_of_not_bridge` | `Erdos1091/Chords.lean:294` | ✅ proved |  |
|  | `G'_cycle_within_block` | `Erdos1091/Chords.lean:308` | ✅ proved |  |
|  | `rimSym` | `Erdos1091/Chords.lean:333` | ✅ proved |  |
|  | `card_rimSym` | `Erdos1091/Chords.lean:337` | ✅ proved |  |
|  | `mem_rimSym` | `Erdos1091/Chords.lean:340` | ✅ proved |  |
|  | `toG'Cycle` | `Erdos1091/Chords.lean:344` | ✅ proved |  |
|  | `toG'Cycle_support` | `Erdos1091/Chords.lean:355` | ✅ proved |  |
|  | `cycle_chords_le_five_of_notMem_v` | `Erdos1091/Chords.lean:361` | ✅ proved |  |
|  | `rimSpanS` | `Erdos1091/Chords.lean:400` | ✅ proved |  |
|  | `slot_count` | `Erdos1091/Chords.lean:409` | ✅ proved |  |
|  | `slot_count_nochord` | `Erdos1091/Chords.lean:425` | ✅ proved |  |
|  | `exists_rimEdge_index` | `Erdos1091/Chords.lean:436` | ✅ proved |  |
|  | `rimAdjB_self_succ` | `Erdos1091/Chords.lean:442` | ✅ proved |  |
|  | `rimEdge_incident` | `Erdos1091/Chords.lean:446` | ✅ proved |  |
|  | `exists_vPath` | `Erdos1091/Chords.lean:454` | ✅ proved |  |
|  | `Block.exitDir` | `Erdos1091/Chords.lean:522` | ✅ proved |  |
|  | `exitSlot` | `Erdos1091/Chords.lean:530` | ✅ proved |  |
|  | `exitSlot_mk` | `Erdos1091/Chords.lean:535` | ✅ proved |  |
|  | `exitDir_leaf` | `Erdos1091/Chords.lean:539` | ✅ proved |  |
|  | `exitDir_spine_leaf_self` | `Erdos1091/Chords.lean:544` | ✅ proved |  |
|  | `exitDir_spine_gt` | `Erdos1091/Chords.lean:549` | ✅ proved |  |
|  | `exitDir_spine_lt` | `Erdos1091/Chords.lean:563` | ✅ proved |  |
|  | `IsSide.symm_edge` | `Erdos1091/Chords.lean:576` | ✅ proved |  |
|  | `IsSide.compl` | `Erdos1091/Chords.lean:581` | ✅ proved |  |
|  | `isSide_leaf'` | `Erdos1091/Chords.lean:589` | ✅ proved |  |
|  | `isSide_spine'` | `Erdos1091/Chords.lean:601` | ✅ proved |  |
|  | `exit_of_mem_P_edges` | `Erdos1091/Chords.lean:618` | ✅ proved |  |
|  | `cycle_two_nbrs` | `Erdos1091/Chords.lean:753` | ✅ proved |  |
|  | `rim_or_out` | `Erdos1091/Chords.lean:769` | ✅ proved |  |
|  | `visitedSlots` | `Erdos1091/Chords.lean:826` | ✅ proved |  |
|  | `usedRim` | `Erdos1091/Chords.lean:830` | ✅ proved |  |
|  | `mem_visitedSlots` | `Erdos1091/Chords.lean:835` | ✅ proved |  |
|  | `mem_usedRim` | `Erdos1091/Chords.lean:838` | ✅ proved |  |
|  | `Slot.succ_pred` | `Erdos1091/Chords.lean:842` | ✅ proved |  |
|  | `mem_usedRim_pred` | `Erdos1091/Chords.lean:845` | ✅ proved |  |
|  | `usedRim_subset` | `Erdos1091/Chords.lean:850` | ✅ proved |  |
|  | `usedRim_covers` | `Erdos1091/Chords.lean:857` | ✅ proved |  |
|  | `out_edge_of_deficient` | `Erdos1091/Chords.lean:866` | ✅ proved |  |
|  | `exists_subwalk` | `Erdos1091/Chords.lean:876` | ✅ proved |  |
|  | `sameBlock_of_chord` | `Erdos1091/Chords.lean:889` | ✅ proved |  |
|  | `leafBlock_of_mem_support` | `Erdos1091/Chords.lean:901` | ✅ proved |  |
|  | `deficient_subset` | `Erdos1091/Chords.lean:933` | ✅ proved |  |
|  | `deficient_card_le_two` | `Erdos1091/Chords.lean:976` | ✅ proved |  |
|  | `chordSlots_card_le_one` | `Erdos1091/Chords.lean:983` | ✅ proved |  |
|  | `rimAdj_exitSlots_of_chord` | `Erdos1091/Chords.lean:990` | ✅ proved |  |
|  | `mem_specialBlocks` | `Erdos1091/Chords.lean:1022` | ✅ proved |  |
|  | `leaf_of_adj_v` | `Erdos1091/Chords.lean:1071` | ✅ proved |  |
|  | `chords_le_ten_of_mem_v` | `Erdos1091/Chords.lean:1099` | ✅ proved |  |
|  | `cycle_chords_le_ten` | `Erdos1091/Chords.lean:1270` | ✅ proved |  |
|  | `block_eq_of_rimAdjVB` | `Erdos1091/CliqueFree.lean:63` | ✅ proved |  |
|  | `ValidBlock.cases'` | `Erdos1091/CliqueFree.lean:69` | ✅ proved |  |
|  | `Block.attachSlot` | `Erdos1091/CliqueFree.lean:86` | ✅ proved |  |
|  | `slots_of_interAdjVB` | `Erdos1091/CliqueFree.lean:92` | ✅ proved |  |
|  | `G'_adj_of_ne_block` | `Erdos1091/CliqueFree.lean:107` | ✅ proved |  |
|  | `slots_of_G'_adj_ne_block` | `Erdos1091/CliqueFree.lean:123` | ✅ proved |  |
|  | `two_in_one_block` | `Erdos1091/CliqueFree.lean:132` | ✅ proved |  |
|  | `spine_of_G'_adj_leaf` | `Erdos1091/CliqueFree.lean:141` | ✅ proved |  |
|  | `spine_adj_index` | `Erdos1091/CliqueFree.lean:153` | ✅ proved |  |
| L4.2 | `no_block_triangle` | `Erdos1091/CliqueFree.lean:170` | ✅ proved | the block graph has no triangle |
| L4.2 | `no_rim_triangle` | `Erdos1091/CliqueFree.lean:204` | ✅ proved | a pentagon has no rim triangle |
|  | `exists_mk_of_G'_adj_left` | `Erdos1091/CliqueFree.lean:210` | ✅ proved |  |
|  | `G'_no_triangle` | `Erdos1091/CliqueFree.lean:217` | ✅ proved |  |
| L4.2 | `G'_cliqueFree_three` | `Erdos1091/CliqueFree.lean:248` | ✅ proved | G'ₘ is triangle-free |
| L4.2 | `neighbor_v_cliqueFree_three` | `Erdos1091/CliqueFree.lean:269` | ✅ proved | N(v) is triangle-free |
| L4.2 | `G_cliqueFree_four` | `Erdos1091/CliqueFree.lean:291` | ✅ proved | Gₘ is K₄-free |
|  | `succ4_eq_pred` | `Erdos1091/Coloring.lean:88` | ✅ proved |  |
|  | `rimAdjB_succ4_self` | `Erdos1091/Coloring.lean:91` | ✅ proved |  |
|  | `succ_ne_self` | `Erdos1091/Coloring.lean:96` | ✅ proved |  |
|  | `succ2_ne_self` | `Erdos1091/Coloring.lean:98` | ✅ proved |  |
|  | `succ3_ne_self` | `Erdos1091/Coloring.lean:100` | ✅ proved |  |
|  | `succ4_ne_self` | `Erdos1091/Coloring.lean:102` | ✅ proved |  |
|  | `leaf_bde_valid` | `Erdos1091/Coloring.lean:112` | ✅ proved |  |
|  | `spineVB_mk` | `Erdos1091/Coloring.lean:117` | ✅ proved |  |
|  | `adj_of_adj'` | `Erdos1091/Coloring.lean:121` | ✅ proved |  |
|  | `alphaColor` | `Erdos1091/Coloring.lean:128` | ✅ proved |  |
| L4.3 | `path_four_alternates` | `Erdos1091/Coloring.lean:136` | ✅ proved | a 4-vertex path on 2 colours alternates |
| L4.3 | `eq_of_ne_two_ne` | `Erdos1091/Coloring.lean:147` | ✅ proved | two differing α-avoiding neighbours force α |
| L4.3 | `leaf_attachment_eq_alpha` | `Erdos1091/Coloring.lean:158` | ✅ proved | leaf attachment vertex has v's colour |
| L4.3 | `spine_with_leaf_ne_alpha` | `Erdos1091/Coloring.lean:181` | ✅ proved | a spine slot carrying a leaf avoids α |
| L4.4 | `pentagon_forces_c` | `Erdos1091/Coloring.lean:197` | ✅ proved | spine pentagon forces colour α at slot c |
| L4.4 | `pentagon_forces_a` | `Erdos1091/Coloring.lean:208` | ✅ proved | spine pentagon forces colour α at slot a |
|  | `spine_rim` | `Erdos1091/Coloring.lean:218` | ✅ proved |  |
|  | `spine_bde_ne_alpha` | `Erdos1091/Coloring.lean:224` | ✅ proved |  |
| L4.4 | `spine_c_of_a` | `Erdos1091/Coloring.lean:237` | ✅ proved | local step: S_i[a] ≠ α ⇒ S_i[c] = α |
| P4.5 | `spine_a_ne_alpha_aux` | `Erdos1091/Coloring.lean:252` | ✅ proved | the walk down the spine (induction on i) |
| L4.4 | `spine_c_eq_alpha` | `Erdos1091/Coloring.lean:282` | ✅ proved | cases (1)/(2): S_i[c] = α |
| L4.4 | `spine_last_a_eq_alpha` | `Erdos1091/Coloring.lean:294` | ✅ proved | case (3): S_m[a] = α |
| P4.5 | `spine_last_a_ne_alpha` | `Erdos1091/Coloring.lean:315` | ✅ proved | S_m[a] ≠ α, by propagation |
| P4.5 | `G_not_colorable_three` | `Erdos1091/Coloring.lean:328` | ✅ proved | Gₘ is not 3-colorable |
|  | `spineColor` | `Erdos1091/Coloring.lean:351` | ✅ proved |  |
|  | `leafColor` | `Erdos1091/Coloring.lean:356` | ✅ proved |  |
|  | `spineColor_rim` | `Erdos1091/Coloring.lean:360` | ✅ proved |  |
|  | `spineColor_ne_three` | `Erdos1091/Coloring.lean:364` | ✅ proved |  |
|  | `leafColor_self` | `Erdos1091/Coloring.lean:367` | ✅ proved |  |
|  | `leafColor_ne_three` | `Erdos1091/Coloring.lean:371` | ✅ proved |  |
|  | `leafColor_rim` | `Erdos1091/Coloring.lean:374` | ✅ proved |  |
| P4.5 | `color4` | `Erdos1091/Coloring.lean:378` | ✅ proved | the explicit 4-colouring, parameterised by m |
|  | `color4_v` | `Erdos1091/Coloring.lean:385` | ✅ proved |  |
|  | `color4_spine` | `Erdos1091/Coloring.lean:387` | ✅ proved |  |
|  | `color4_leaf` | `Erdos1091/Coloring.lean:393` | ✅ proved |  |
| P4.5 | `color4_valid` | `Erdos1091/Coloring.lean:400` | ✅ proved | color4 is a proper colouring |
| P4.5 | `G_colorable_four` | `Erdos1091/Coloring.lean:439` | ✅ proved | Gₘ is 4-colorable |
| P4.5 | `G_chromaticNumber` | `Erdos1091/Coloring.lean:443` | ✅ proved | χ(Gₘ) = 4 |
|  | `card_eq` | `Erdos1091/Construction.lean:80` | ✅ proved |  |
|  | `succ` | `Erdos1091/Construction.lean:83` | ✅ proved |  |
|  | `rimAdjB` | `Erdos1091/Construction.lean:87` | ✅ proved |  |
|  | `rimAdjB_comm` | `Erdos1091/Construction.lean:90` | ✅ proved |  |
|  | `rimAdjB_irrefl` | `Erdos1091/Construction.lean:95` | ✅ proved |  |
|  | `equivSum` | `Erdos1091/Construction.lean:110` | ✅ proved |  |
|  | `validB` | `Erdos1091/Construction.lean:121` | ✅ proved |  |
|  | `ValidBlock` | `Erdos1091/Construction.lean:132` | ✅ proved |  |
|  | `Vtx` | `Erdos1091/Construction.lean:135` | ✅ proved |  |
|  | `v` | `Erdos1091/Construction.lean:140` | ✅ proved |  |
|  | `mk` | `Erdos1091/Construction.lean:143` | ✅ proved |  |
|  | `rimAdjVB` | `Erdos1091/Construction.lean:150` | ✅ proved |  |
|  | `interAdjVB` | `Erdos1091/Construction.lean:157` | ✅ proved |  |
|  | `blockAdjVB` | `Erdos1091/Construction.lean:167` | ✅ proved |  |
|  | `specialAdjVB` | `Erdos1091/Construction.lean:170` | ✅ proved |  |
|  | `rawAdjVB` | `Erdos1091/Construction.lean:179` | ✅ proved |  |
|  | `G'` | `Erdos1091/Construction.lean:184` | ✅ proved |  |
|  | `G` | `Erdos1091/Construction.lean:187` | ✅ proved |  |
|  | `G_adj` | `Erdos1091/Construction.lean:193` | ✅ proved |  |
|  | `G'_adj` | `Erdos1091/Construction.lean:197` | ✅ proved |  |
|  | `G'_le_G` | `Erdos1091/Construction.lean:201` | ✅ proved |  |
|  | `rimAdjVB_none_left` | `Erdos1091/Construction.lean:216` | ✅ proved |  |
|  | `rimAdjVB_none_right` | `Erdos1091/Construction.lean:219` | ✅ proved |  |
|  | `interAdjVB_none_left` | `Erdos1091/Construction.lean:222` | ✅ proved |  |
|  | `interAdjVB_none_right` | `Erdos1091/Construction.lean:225` | ✅ proved |  |
|  | `blockAdjVB_none_left` | `Erdos1091/Construction.lean:228` | ✅ proved |  |
|  | `blockAdjVB_none_right` | `Erdos1091/Construction.lean:231` | ✅ proved |  |
|  | `specialAdjVB_some_left` | `Erdos1091/Construction.lean:234` | ✅ proved |  |
|  | `specialAdjVB_none_right` | `Erdos1091/Construction.lean:238` | ✅ proved |  |
|  | `G'_not_adj_v` | `Erdos1091/Construction.lean:243` | ✅ proved |  |
|  | `G_adj_mk_mk` | `Erdos1091/Construction.lean:253` | ✅ proved |  |
|  | `G'_adj_of_G_adj_of_ne_v` | `Erdos1091/Construction.lean:258` | ✅ proved |  |
|  | `interAdjVB_mk_mk_iff` | `Erdos1091/Construction.lean:272` | ✅ proved |  |
|  | `ne_block_of_interAdjVB` | `Erdos1091/Construction.lean:288` | ✅ proved |  |
|  | `G'_adj_same_block` | `Erdos1091/Construction.lean:299` | ✅ proved |  |
|  | `sum_slot` | `Erdos1091/Construction.lean:319` | ✅ proved |  |
|  | `sum_slot_leaf` | `Erdos1091/Construction.lean:326` | ✅ proved |  |
| 构造 | `card_validBlock` | `Erdos1091/Construction.lean:338` | ✅ proved | block count = 4m+6 |
| 构造 | `card_vtx` | `Erdos1091/Construction.lean:369` | ✅ proved | vertex count = 20m+31 |
|  | `degreesSectionMarker` | `Erdos1091/Construction.lean:387` | ✅ proved |  |
|  | `pred` | `Erdos1091/Construction.lean:402` | ✅ proved |  |
|  | `rimAdjB_iff` | `Erdos1091/Construction.lean:407` | ✅ proved |  |
|  | `succ_ne_pred` | `Erdos1091/Construction.lean:411` | ✅ proved |  |
|  | `rimAdjB_succ` | `Erdos1091/Construction.lean:413` | ✅ proved |  |
|  | `rimAdjB_pred` | `Erdos1091/Construction.lean:415` | ✅ proved |  |
|  | `spineVB` | `Erdos1091/Construction.lean:422` | ✅ proved |  |
|  | `spineVB_val` | `Erdos1091/Construction.lean:424` | ✅ proved |  |
|  | `Vtx.mk_eq_mk` | `Erdos1091/Construction.lean:426` | ✅ proved |  |
|  | `Vtx.mk_ne_v` | `Erdos1091/Construction.lean:430` | ✅ proved |  |
|  | `G'_adj_of_inter` | `Erdos1091/Construction.lean:434` | ✅ proved |  |
|  | `G'_adj_leaf_spine` | `Erdos1091/Construction.lean:444` | ✅ proved |  |
|  | `G'_adj_spine_spine` | `Erdos1091/Construction.lean:452` | ✅ proved |  |
|  | `reach_same_block` | `Erdos1091/Construction.lean:461` | ✅ proved |  |
|  | `reach_spine_aux` | `Erdos1091/Construction.lean:480` | ✅ proved |  |
|  | `reach_root` | `Erdos1091/Construction.lean:500` | ✅ proved |  |
| 构造 | `G'_reachable` | `Erdos1091/Construction.lean:510` | ✅ proved | G'ₘ is connected away from v |
|  | `degree_le_three_of` | `Erdos1091/Construction.lean:532` | ✅ proved |  |
|  | `degree_eq_three_of` | `Erdos1091/Construction.lean:544` | ✅ proved |  |
|  | `G_adj_mk_iff` | `Erdos1091/Construction.lean:567` | ✅ proved |  |
|  | `G_adj_v_mk_iff` | `Erdos1091/Construction.lean:592` | ✅ proved |  |
|  | `specialAdjVB_mk_iff` | `Erdos1091/Construction.lean:603` | ✅ proved |  |
|  | `G_adj_mk_v_iff` | `Erdos1091/Construction.lean:617` | ✅ proved |  |
|  | `G_adj_same_block` | `Erdos1091/Construction.lean:622` | ✅ proved |  |
|  | `valBlock_ne` | `Erdos1091/Construction.lean:626` | ✅ proved |  |
|  | `mk_ne_mk_of_block_ne` | `Erdos1091/Construction.lean:629` | ✅ proved |  |
|  | `G_nbr_cases` | `Erdos1091/Construction.lean:639` | ✅ proved |  |
|  | `IsOutside` | `Erdos1091/Construction.lean:675` | ✅ proved |  |
|  | `outside_ne_rim` | `Erdos1091/Construction.lean:680` | ✅ proved |  |
|  | `v_ne_mk` | `Erdos1091/Construction.lean:683` | ✅ proved |  |
|  | `exists_outside_spine` | `Erdos1091/Construction.lean:692` | ✅ proved |  |
|  | `exists_outside` | `Erdos1091/Construction.lean:782` | ✅ proved |  |
| 构造 | `degree_eq_three` | `Erdos1091/Construction.lean:824` | ✅ proved | every vertex ≠ v has degree 3 |
| 构造 | `G'_degree_le_three` | `Erdos1091/Construction.lean:839` | ✅ proved | G'ₘ has max degree ≤ 3 |
| P4.6 | `exists_ne_v_of_adj` | `Erdos1091/Degenerate.lean:66` | ✅ proved | every edge has an endpoint ≠ v |
|  | `isTwoDegenerate_of_forall_set` | `Erdos1091/Degenerate.lean:76` | ✅ proved |  |
|  | `neighborSet_encard_eq_three` | `Erdos1091/Degenerate.lean:96` | ✅ proved |  |
|  | `encard_le_two_of_subset_neighborSet_diff` | `Erdos1091/Degenerate.lean:107` | ✅ proved |  |
|  | `encard_le_two_of_excluded` | `Erdos1091/Degenerate.lean:119` | ✅ proved |  |
|  | `exists_missing_edge` | `Erdos1091/Degenerate.lean:130` | ✅ proved |  |
|  | `probeVtx` | `Erdos1091/Degenerate.lean:147` | ✅ proved |  |
|  | `probeVtx_ne_v` | `Erdos1091/Degenerate.lean:149` | ✅ proved |  |
|  | `probeVtx_adj_v` | `Erdos1091/Degenerate.lean:152` | ✅ proved |  |
|  | `master` | `Erdos1091/Degenerate.lean:163` | ✅ proved |  |
| P4.6 | `proper_subgraph_isTwoDegenerate` | `Erdos1091/Degenerate.lean:223` | ✅ proved | proper subgraphs are 2-degenerate |
| P4.6 | `exists_degree_le_two` | `Erdos1091/Degenerate.lean:245` | ✅ proved | a proper subgraph has a vertex of degree ≤ 2 |
| P4.6 | `proper_subgraph_chromaticNumber_le_three` | `Erdos1091/Degenerate.lean:258` | ✅ proved | proper subgraphs are 3-colorable |
|  | `IsTwoDegenerate` | `Erdos1091/DegenerateCore.lean:55` | ✅ proved |  |
|  | `exists_mem_encard_le_two` | `Erdos1091/DegenerateCore.lean:64` | ✅ proved |  |
|  | `greedy` | `Erdos1091/DegenerateCore.lean:83` | ✅ proved |  |
| 通用件 | `colorable_three_of_isTwoDegenerate` | `Erdos1091/DegenerateCore.lean:132` | ✅ proved | 2-degenerate ⇒ 3-colorable (new, not in Mathlib) |
| 搬运 | `cliqueFree_map_equiv` | `Erdos1091/Main.lean:76` | ✅ proved | CliqueFree 沿等价搬运 (Mathlib 已有,重述) |
| 搬运 | `chromaticNumber_map_equiv` | `Erdos1091/Main.lean:81` | ✅ proved | chromaticNumber 沿等价搬运 |
| 通用件 | `subgraph_chromaticNumber_congr` | `Erdos1091/Main.lean:85` | ✅ proved | 子图着色数沿图同构不变 (new, not in Mathlib) |
| 搬运 | `subgraph_chromaticNumber_map_equiv` | `Erdos1091/Main.lean:134` | ✅ proved | 子图条件沿等价搬运 |
| 通用件 | `cycle_chords_congr` | `Erdos1091/Main.lean:139` | ✅ proved | 弦上界沿图同构不变 (new, not in Mathlib) |
| 搬运 | `cycle_chords_map_equiv` | `Erdos1091/Main.lean:179` | ✅ proved | 弦上界沿等价搬运 |
| 搬运 | `vtxEquiv` | `Erdos1091/Main.lean:187` | ✅ proved | Vtx m ≃ Fin (20m+31) |
| 搬运 | `Gfin` | `Erdos1091/Main.lean:191` | ✅ proved | Gₘ 搬到 Fin (20m+31) 上 |
| T4.1 | `size_bounds` | `Erdos1091/Main.lean:197` | ✅ proved | m ≤ 20m+31 ≤ 51m(C = 51) |
| T4.1 | `theorem_4_1` | `Erdos1091/Main.lean:206` | ✅ proved | 四个结论在 Fin n 上同时成立 |
| T4.1 | `erdos_1091.variants.counterexample` | `Erdos1091/Main.lean:224` | ✅ proved | PR #5870 目标陈述,逐字一致 |


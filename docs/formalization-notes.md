---
title: Erdős 1091 反例的 Lean 4 形式化
subtitle: arXiv:2604.06609 Theorem 4.1 的机器可验重建
date: 研究范围截至 2026 年 9 月 17 日
keywords: Lean 4；形式化数学；图着色；Erdős 问题；Mathlib
abstract: |
  本文记录把 arXiv:2604.06609《Short proofs in combinatorics, probability and number theory II》第 4 节 Theorem 4.1 重建为 Lean 4 机器可验证明的全过程。该定理对 Erdős 1091 给出否定回答：对每个 m ≥ 1 存在显式的 K_4-free 图 G_m，它有 20m+31 个顶点、色数为 4、每个真子图 3-可着色，且每个圈至多携带 10 条弦。数学结论与证明属于原作者 Alexeev、Putterman、Sawhney、Sellke 与 Valiant，本工作主张的是独立的 formalizer credit。形式化成果为 3696 行自有 Lean 源码，217 条声明全部证完，零 sorry；41 条 #print axioms 的实际输出全部只含 Mathlib 标准三公理 propext、Classical.choice 与 Quot.sound，其中一条更少。顶层定理的陈述与 formal-conjectures PR #5870 逐字符一致，可直接提交为该 PR 的证明补全。本文给出完整的论文编号到 Lean 声明的映射表、形式化过程中的工程决策及其理由，以及在干净机器上复核这些结论的完整命令。
---

# Erdős 1091 反例的 Lean 4 形式化

## 1. 本工作的定位与 credit 归属

本工作把 arXiv:2604.06609《Short proofs in combinatorics, probability and number theory II》（Alexeev–Putterman–Sawhney–Sellke–Valiant，2026 年 4 月）第 4 节 Theorem 4.1 的构造与证明，重建为一份可由 Lean 4 内核检查的形式化证明。

**数学内容不属于本工作。** 图 G_m 的构造、四个结论的证明思路以及全部关键引理，均由上述五位作者完成，prover credit 完整归属原作者。本工作所主张的是独立的 **formalizer credit**，即把已有的纸面证明翻译成 Lean、补齐纸面上被略过的推理细节、并让整份证明通过内核检查这一部分劳动。凡是形式化过程中与论文路线产生偏离之处，本文第 5 节逐条列出并说明理由；这些偏离都是证明工程上的选择，不构成新的数学结论。

与 formal-conjectures 仓库 PR #5870（作者 stantheman0128）的关系如下。该 PR 是 statement-only 的：它给出了 Erdős 1091 的目标陈述，以及陈述所依赖的 `SimpleGraph.Cycle` 与 `Cycle.chords` API，但定理本身的证明是 `sorry`。本工作直接采用该 PR 的目标陈述与 API 作为基座，不另造一套弦的定义，填入的正是那条 `sorry`。目标陈述 `erdos_1091.variants.counterexample` 的签名已用脚本做过字符级比对，与 PR 中的 `FormalConjectures/ErdosProblems/1091.lean` 完全一致。PR 附带的两个基座文件随交付物一并保留，其原始版权头原样未动，那部分不是本工作的产出。

## 2. 原问题与答案

Erdős 1091 问的是：是否存在一个趋于无穷的函数 f(r)，使得每个色数为 4、且所有不超过 r 个顶点的子图都 3-可着色的图 G，都包含一个带至少 f(r) 条弦的奇圈？

**答案为否。** 反例由下述定理给出。

> **Theorem 4.1.** 对每个整数 m ≥ 1，存在显式的 K_4-free 图 G_m，它有 20m+31 个顶点，并满足：
> (1) χ(G_m) = 4；
> (2) 每个真子图 H ⊊ G_m 是 2-degenerate，因而 3-可着色；
> (3) 每个圈 C 满足 ch(C) ≤ 10。

关键在于弦数上界 10 是一个**与 m 无关的绝对常数**，而条件 (2) 使得局部可着色参数 r 可以随 m 一起任意增大。于是任何候选的 f(r) 都被这一族图压在 10 以下，f(r) → ∞ 不可能成立。

## 3. 构造 G_m

G_m 是若干五边形块拼成的毛毛虫，外加一个特殊顶点 v。

- **脊块** S_0, …, S_m，每块是一个 5-圈，顶点按环序标记为 a, b, c, d, e。
- **叶块**：S_0 挂 4 个叶块，对应槽位 a、b、d、e；中间的 S_i（1 ≤ i ≤ m−1）各挂 3 个，对应槽位 b、d、e；S_m 挂 4 个，对应槽位 b、c、d、e。每个叶块同样是一个 5-圈。块的总数为 4m+6。
- **块间边**：挂在脊块 S_i 槽位 x 上的叶块记作 L(i, x)，它通过边 S_i[x] — L(i, x)[x] 挂到脊块上；相邻脊块之间有边 S_i[c] — S(i+1)[a]，其中 0 ≤ i < m。
- **特殊顶点 v**：对每个叶块，v 连到该块中除挂接点以外的 4 个顶点。v 不与任何脊块相连。
- 记 G'_m := G_m \ {v}。除 v 以外，每个顶点的度数恰为 3。

顶点总数由此为 5(4m+6)+1 = 20m+31，与定理陈述一致；形式化中这一计数是被证明的定理 `card_vtx`，不是注释里的算术。

**不对称性是本质的，不是构造上的随意选择。** S_0 没有 c-叶块，S_m 没有 a-叶块。第 4 节的 Lemma 4.4 与 Proposition 4.5 完全依赖这一点：脊块上的颜色传播从两端各推出一个结论，而两个结论互相矛盾，矛盾才逼出“不可 3-着色”。在 Lean 源码里，这条不对称性只写在一处——`Block.validB` 这个布尔判定式的两个分支——而不是散落在各引理的附加假设中。这样做的好处是，任何试图对称化构造的改动都会在这一处立刻暴露，而不是在下游某条证明里悄悄失效。

形式化期间对上游工单里的一处数值做了更正：v 的度数不是 4·(4m+6) 而是 12m+20，因为 v 只连叶块、不连脊块，叶块数是 3m+5 而非 4m+6。该更正已经过实测确认（m = 2 时 deg(v) = 44）。这不影响定理的任何结论，但影响度数论证的中间步骤。

## 4. 引理映射表

下表是评审的入口：论文编号、对应的 Lean 声明、所在文件与行号、以及状态。行号对应交付目录 `output/erdos-1091-lean/lean/` 下的文件。状态一列全部为“已证”，依据是第 6 节所列的机械审计输出，不是主观判断。

### 4.1 构造与基本性质

表 1 构造与基本性质的引理映射

| 论文位置 | Lean 声明 | 文件:行 | 状态 |
|---|---|---|---|
| 块计数 4m+6 | `card_validBlock` | `Erdos1091/Construction.lean:338` | 已证 |
| 顶点计数 20m+31 | `card_vtx` | `Erdos1091/Construction.lean:369` | 已证 |
| 非 v 顶点度数恰为 3 | `degree_eq_three` | `Erdos1091/Construction.lean:824` | 已证 |
| G'_m 最大度 ≤ 3 | `G'_degree_le_three` | `Erdos1091/Construction.lean:839` | 已证 |
| G'_m 连通 | `G'_reachable` | `Erdos1091/Construction.lean:510` | 已证 |

### 4.2 Lemma 4.2：G_m 是 K_4-free

表 2 Lemma 4.2（K_4-free）的引理映射

| 论文位置 | Lean 声明 | 文件:行 | 状态 |
|---|---|---|---|
| 块图无三角形 | `no_block_triangle` | `Erdos1091/CliqueFree.lean:170` | 已证 |
| 五边形无 rim 三角形 | `no_rim_triangle` | `Erdos1091/CliqueFree.lean:204` | 已证 |
| G'_m 无三角形 | `G'_no_triangle` | `Erdos1091/CliqueFree.lean:217` | 已证 |
| G'_m 三角形自由 | `G'_cliqueFree_three` | `Erdos1091/CliqueFree.lean:248` | 已证 |
| N(v) 三角形自由 | `neighbor_v_cliqueFree_three` | `Erdos1091/CliqueFree.lean:269` | 已证 |
| **Lemma 4.2**：G_m 是 K_4-free | `G_cliqueFree_four` | `Erdos1091/CliqueFree.lean:291` | 已证 |

### 4.3 Lemma 4.3 与 4.4：颜色强制与脊块传播

表 3 Lemma 4.3 与 4.4（颜色强制与脊块传播）的引理映射

| 论文位置 | Lean 声明 | 文件:行 | 状态 |
|---|---|---|---|
| 4 点路径在两色上交替 | `path_four_alternates` | `Erdos1091/Coloring.lean:136` | 已证 |
| 两个相异的避 α 邻点强制 α | `eq_of_ne_two_ne` | `Erdos1091/Coloring.lean:147` | 已证 |
| **Lemma 4.3**：叶块挂接点取 v 的颜色 | `leaf_attachment_eq_alpha` | `Erdos1091/Coloring.lean:158` | 已证 |
| 带叶的脊槽位避开 α | `spine_with_leaf_ne_alpha` | `Erdos1091/Coloring.lean:181` | 已证 |
| 脊五边形在槽位 c 强制 α | `pentagon_forces_c` | `Erdos1091/Coloring.lean:197` | 已证 |
| 脊五边形在槽位 a 强制 α | `pentagon_forces_a` | `Erdos1091/Coloring.lean:208` | 已证 |
| **Lemma 4.4** 局部步：S_i[a] ≠ α ⇒ S_i[c] = α | `spine_c_of_a` | `Erdos1091/Coloring.lean:237` | 已证 |
| **Lemma 4.4** 情形 (1)(2) | `spine_c_eq_alpha` | `Erdos1091/Coloring.lean:282` | 已证 |
| **Lemma 4.4** 情形 (3) | `spine_last_a_eq_alpha` | `Erdos1091/Coloring.lean:294` | 已证 |

### 4.4 Proposition 4.5：χ(G_m) = 4

表 4 Proposition 4.5（χ(G_m) = 4）的引理映射

| 论文位置 | Lean 声明 | 文件:行 | 状态 |
|---|---|---|---|
| 沿脊块的归纳传播 | `spine_a_ne_alpha_aux` | `Erdos1091/Coloring.lean:252` | 已证 |
| 传播到末端：S_m[a] ≠ α | `spine_last_a_ne_alpha` | `Erdos1091/Coloring.lean:315` | 已证 |
| **Prop 4.5** 下界：G_m 不是 3-可着色 | `G_not_colorable_three` | `Erdos1091/Coloring.lean:328` | 已证 |
| 显式 4-着色（与 m 无关） | `color4` | `Erdos1091/Coloring.lean:378` | 已证 |
| 该着色合法 | `color4_valid` | `Erdos1091/Coloring.lean:400` | 已证 |
| **Prop 4.5** 上界：G_m 是 4-可着色 | `G_colorable_four` | `Erdos1091/Coloring.lean:439` | 已证 |
| **Prop 4.5**：χ(G_m) = 4 | `G_chromaticNumber` | `Erdos1091/Coloring.lean:443` | 已证 |

### 4.5 Proposition 4.6：真子图 2-degenerate

表 5 Proposition 4.6（真子图 2-degenerate）的引理映射

| 论文位置 | Lean 声明 | 文件:行 | 状态 |
|---|---|---|---|
| 2-degenerate 的定义 | `IsTwoDegenerate` | `Erdos1091/DegenerateCore.lean:55` | 已证 |
| 贪心着色 | `greedy` | `Erdos1091/DegenerateCore.lean:83` | 已证 |
| **通用件**：2-degenerate ⇒ 3-可着色 | `colorable_three_of_isTwoDegenerate` | `Erdos1091/DegenerateCore.lean:132` | 已证 |
| 每条边有一端不是 v | `exists_ne_v_of_adj` | `Erdos1091/Degenerate.lean:66` | 已证 |
| **Prop 4.6**：真子图 2-degenerate | `proper_subgraph_isTwoDegenerate` | `Erdos1091/Degenerate.lean:223` | 已证 |
| 真子图有度数 ≤ 2 的顶点 | `exists_degree_le_two` | `Erdos1091/Degenerate.lean:245` | 已证 |
| **Prop 4.6**：真子图 3-可着色 | `proper_subgraph_chromaticNumber_le_three` | `Erdos1091/Degenerate.lean:258` | 已证 |

### 4.6 Lemma 4.7 至 Proposition 4.10：弦数上界

表 6 Lemma 4.7 至 Proposition 4.10（弦数上界）的引理映射

| 论文位置 | Lean 声明 | 文件:行 | 状态 |
|---|---|---|---|
| 通用割边装置 | `IsSide` / `IsSide.isBridge` | `Erdos1091/Chords.lean:98` / `116` | 已证 |
| 叶块是其挂接边的一侧 | `isSide_leaf` | `Erdos1091/Chords.lean:173` | 已证 |
| 脊前段是脊边的一侧 | `isSide_spine` | `Erdos1091/Chords.lean:202` | 已证 |
| **Lemma 4.7** 引擎：块间边是割边 | `interAdj_isBridge` | `Erdos1091/Chords.lean:247` | 已证 |
| **Lemma 4.7**：G'_m 的圈含于单块 | `G'_cycle_within_block` | `Erdos1091/Chords.lean:308` | 已证 |
| 不含 v 的圈弦数 ≤ 5 | `cycle_chords_le_five_of_notMem_v` | `Erdos1091/Chords.lean:361` | 已证 |
| 五边形有限计数：每块至多一条弦 | `slot_count` | `Erdos1091/Chords.lean:409` | 已证 |
| 圈过 v 时切成无 v 路径 | `exists_vPath` | `Erdos1091/Chords.lean:454` | 已证 |
| **Lemma 4.8/4.9** 核心：出块边指向路径端点 | `exit_of_mem_P_edges` | `Erdos1091/Chords.lean:618` | 已证 |
| **Lemma 4.8/4.9**：每块至多一条弦 | `chordSlots_card_le_one` | `Erdos1091/Chords.lean:983` | 已证 |
| **Lemma 4.8/4.9**：带弦的块至多四个 | `mem_specialBlocks` | `Erdos1091/Chords.lean:1022` | 已证 |
| **Prop 4.10** 的 v ∈ C 分支 | `chords_le_ten_of_mem_v` | `Erdos1091/Chords.lean:1099` | 已证 |
| **Prop 4.10**：每个圈弦数 ≤ 10 | `cycle_chords_le_ten` | `Erdos1091/Chords.lean:1270` | 已证 |

### 4.7 Theorem 4.1 的组装

表 7 Theorem 4.1 组装与搬运引理的映射

| 论文位置 | Lean 声明 | 文件:行 | 状态 |
|---|---|---|---|
| CliqueFree 沿等价搬运 | `cliqueFree_map_equiv` | `Erdos1091/Main.lean:76` | 已证 |
| chromaticNumber 沿等价搬运 | `chromaticNumber_map_equiv` | `Erdos1091/Main.lean:81` | 已证 |
| **通用件**：子图着色数沿图同构不变 | `subgraph_chromaticNumber_congr` | `Erdos1091/Main.lean:85` | 已证 |
| **通用件**：弦上界沿图同构不变 | `cycle_chords_congr` | `Erdos1091/Main.lean:139` | 已证 |
| Vtx m ≃ Fin (20m+31) | `vtxEquiv` | `Erdos1091/Main.lean:187` | 已证 |
| 规模界 m ≤ 20m+31 ≤ 51m，即 C = 51 | `size_bounds` | `Erdos1091/Main.lean:197` | 已证 |
| **Theorem 4.1**：四个结论同时成立 | `theorem_4_1` | `Erdos1091/Main.lean:206` | 已证 |
| **目标陈述**：PR #5870 的反例 | `erdos_1091.variants.counterexample` | `Erdos1091/Main.lean:224` | 已证 |

### 4.8 依赖关系

下图给出上述结论之间的依赖走向：构造层给出顶点类型、邻接关系与度数事实，四条中间结论（Lemma 4.2、4.3、4.7 与 Prop 4.6）由构造直接推出，颜色传播与逐块弦计数各自续接一层，最后汇入 Theorem 4.1 并搬运到目标陈述。

图 1 引理依赖关系图

![引理依赖关系图：从构造 G_m 到目标陈述的推导走向](figures/fig_01_lemma_deps.png)

## 5. 形式化中的工程决策

本节记录的是纸面证明里不存在、但形式化必须回答的问题。这些也是上游 reviewer 最可能追问的地方。

### 5.1 顶点类型的选择

顶点类型定义为

    Slot        := a | b | c | d | e                   -- 五边形上的位置，rim 序 a→b→c→d→e→a
    Block m     := spine (i : Fin (m+1)) | leaf (i : Fin (m+1)) (x : Slot)
    Block.validB : Block m → Bool                      -- a-叶只在 S_0，c-叶只在 S_m
    ValidBlock m := {b : Block m // b.validB = true}
    Vtx m       := Option (ValidBlock m × Slot)        -- none 即特殊点 v

选它而不是“归纳类型加手写 Fintype”或“直接用 Fin (20m+31)”，有四条理由。

第一，`DecidableEq` 与 `Fintype` 实例全部可以自动推导，不需要手写。`Option`、乘积与 `Subtype` 在 Mathlib 里实例齐全，`Subtype` 的证明字段靠 proof irrelevance 自动相等。

第二，块结构在类型里直接可见。Lemma 4.7 至 4.9 全部是“按块分类讨论”，顶点自带“块加槽位”的结构就能直接做 case 分析；如果一开始就搬到 Fin n 上，这些信息全部丢失，每条引理都要先把编号翻译回块结构。

第三，不对称性写在 `validB` 一处，而不是散落在各引理的前提里。

第四，目标陈述要求 `SimpleGraph (Fin n)`，所以只在最后搬运一次：`Main.lean` 的 `vtxEquiv : Vtx m ≃ Fin (20m+31)` 由 `card_vtx` 经 `Fintype.equivFinOfCardEq` 得到，配四条 transport 引理把四个结论一次性搬过去。这是形式化中“工作类型”与“陈述类型”分离的标准做法：在方便证明的类型上做全部数学，只在接口处付一次搬运成本。

邻接关系用布尔谓词加 `SimpleGraph.fromRel` 构造。`fromRel` 免费给出对称性与无自环，布尔层使 `DecidableRel` 实例归结为 `Decidable` 的合取，不必手写。

### 5.2 显式搬到 Fin n 的必要性

目标陈述的形状是“存在 n 与 `SimpleGraph (Fin n)`”。这不是可以绕过的表面差异：`Vtx m` 与 `Fin (20m+31)` 是不同的类型，四个结论都要沿等价搬运，而搬运本身需要证明。其中两条在 Mathlib 里没有现成引理，见 5.4 节。

搬运引理的写法上做了一个决断：先证“沿图同构 ≃g 不变”的通用形式，再特化到 `map e.toEmbedding`。直接对 `H.map e.toEmbedding` 写会短一点，但通用形式才是可复用的，`Iso.map e H : H ≃g H.map e.toEmbedding` 负责搭桥。代价是多两条声明，收益是这两条通用件与 Erdős 1091 完全无关，可以独立上游。

### 5.3 判定策略的禁用范围与理由

邻接关系可判定，是用户明确要求的，也确实成立。**但可判定不等于用判定策略去证。** 该图的顶点数是 20m+31，其中 m 是自由参数：对它整体调用 `decide` 或 `native_decide`，既会因判定式展开而耗尽内存，对参数化命题也根本不成立，因为 `decide` 要求目标闭合。可判定性的作用是让 `Fintype` 与实例推导顺畅，主定理仍走结构化证明。

枚举只用在固定的小规模有限情形上，每一处的规模都在源码注释里标明：

表 8 枚举证明的使用位置与规模

| 位置 | 枚举规模 |
|---|---|
| `Slot.rimAdjB_irrefl` | 5 |
| `Slot.rimAdjB_comm` | 5 × 5 = 25 |
| `no_rim_triangle`（Lemma 4.2） | 5^3 = 125 |
| `path_four_alternates`（Lemma 4.3） | Fin 3 上 3^5 = 243 |
| `eq_of_ne_two_ne`（Lemma 4.3） | Fin 3 上 3^4 = 81 |
| `pentagon_forces_c` / `pentagon_forces_a`（Lemma 4.4） | Fin 3 上 3^6 = 729 |
| `slot_count`（弦计数核心） | 2^5 × 2^5 = 1024 |
| `leafColor_rim`（4-着色） | 5^3 = 125 |

全树不含 `native_decide`，这一点由机械 grep 验证。`native_decide` 会把编译器信任基扩大到 Lean 内核以外，对一份以“可验证”为卖点的交付物是不可接受的。

### 5.4 新造的通用件

三条结论在 Mathlib 里没有现成版本，本形式化从零证出，且都与 Erdős 1091 无关，可以独立上游：

- `colorable_three_of_isTwoDegenerate`（`DegenerateCore.lean:132`）：2-degenerate 图是 3-可着色的。证明走对顶点数的强归纳加贪心着色。Mathlib 有 k-degenerate 的零散片段，但没有这条。
- `subgraph_chromaticNumber_congr`（`Main.lean:85`）：子图着色数沿图同构不变。证明需要注意 `Subgraph.comap` 的邻接定义为 `G.Adj u v ∧ H.Adj (f u) (f v)`，含一个额外的合取项，构造 `map_rel_iff'` 时须由同构的 `map_rel_iff` 供出第一个分量。
- `cycle_chords_congr`（`Main.lean:139`）：弦数上界沿图同构不变。

另外 `IsSide` 这个割边装置（`Chords.lean:98`）虽然是为本证明设计的，但陈述本身对任意图成立：若除边 s(x,y) 外每条边的两端同属或同不属顶点集 S，则 s(x,y) 是割边。引入它是本形式化最省力的一处决断——验证 `IsSide` 只需要对邻接关系做有限分类讨论，完全不涉及 walk 推理，而整个毛毛虫的块树结构只通过两个 `IsSide` 实例进入证明。

### 5.5 与论文路线的三处偏离

这三处都是证明工程上的选择，不放松任何结论，也不给任何定理增加前提。

**其一，不含 v 的圈证的是 ch(C) ≤ 5 而非论文的 ch(C) = 0。** 论文说这种圈没有弦，理由是它必须恰好是整个五边形。在 Lean 里证“C_5 里的圈只能是 C_5 本身”需要额外一段论证，而 Prop 4.10 只需要 ≤ 10。由 Lemma 4.7 知圈含于单块，弦必是该五边形的 rim 边，而 rim 边只有 5 条，于是 5 ≤ 10 已经够用。代价是交付的不是论文的最强形式，这一点已写进源码注释。

**其二，含 v 的圈按弦的类型分两族求和，而非论文的逐块 4+4+1+1。** 本形式化数的是“落在 v 上的弦 ≤ 6”加“rim 弦 ≤ 4”。两种分法数的是同一批边，但按类型分不需要认定“哪个五边形贡献了哪一条”，省掉了论文里“内部脊块贡献 0”那一整段块树位置讨论。两者都恰好等于 10。

**其三，rim 弦的计数用单射代替求和。** 每条 rim 弦映到它所在的块，由 `chordSlots_card_le_one` 知每块至多一条，由 `mem_specialBlocks` 知带弦的块至多四个，于是 rim 弦不超过 4。全局求和被替换成 `Finset.card_biUnion_le`。

`cycle_chords_le_ten` 的签名在这三处偏离中逐字保留未动。

### 5.6 交付目录的自包含性

交付的 `output/erdos-1091-lean/lean/` 本身就是一个完整的 Lake 包，只依赖 Mathlib，不需要另行 clone formal-conjectures。这要求把目标陈述所依赖的 API 一并 vendor 进来。第一版只 vendor 了 `Cycle.lean`，看起来没问题，实际编译不过——`Cycle.lean` 自己 `public import` 了 `Circumference.lean`。这个缺口是把整个目录拷到别处只软链 Mathlib 后实跑才发现的，不是推断出来的。两个 vendored 文件都原样保留 PR #5870 的版权头。

开发期曾在 lakefile 里设 `warn.sorry = false`，让带 `sorry` 的中间态不至于编译失败。交付的 lakefile 没有这一行，因为现在零 `sorry`，留着只会掩盖回归。

## 6. 可验证性

### 6.1 在干净机器上完整复核

```bash
# 1) 安装 elan。刻意不装 default toolchain：
#    版本由 lean-toolchain 决定（leanprover/lean4:v4.33.1）。
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
source ~/.elan/env             # 等价于把 ~/.elan/bin 加入 PATH

cd output/erdos-1091-lean/lean

# 2) 下载 Mathlib 预编译 olean（GB 级；实测 126 秒，解包后 6.6 GB）。
#    绝不要从源码编译 Mathlib。
lake exe cache get

# 3) 编译并审计
LAKE_NUM_JOBS=2 lake build Erdos1091
```

最后一步会连 `Erdos1091/Audit.lean` 一起编译，把 41 条 `#print axioms` 的结果打印到标准输出；与随附的 `axioms.txt` 对照即可复核“无 sorry、无额外 axiom”。注意 Lake 5.0 已删除 `-j` 短选项，并发必须用环境变量 `LAKE_NUM_JOBS`。

`Audit.lean` 刻意不被任何文件 import，但放在库的 glob 里，因此 `lake build Erdos1091` 会编译它并把审计输出打进构建日志。审计由此是 CI 可复现的，而不是靠人另跑一条命令。

### 6.2 实际审计结果

下表是机械门的实际退出码与输出，不是口头描述。

表 9 机械审计门的实际结果

| 检查项 | 命令 | 结果 |
|---|---|---|
| 全树编译 | `LAKE_NUM_JOBS=2 lake build Erdos1091` | 退出 0，`Build completed successfully (1201 jobs)`，零 warning |
| 源码无 sorry / admit / axiom / native_decide | `grep -rn` 全树 | 无命中 |
| 构建日志无 `uses 'sorry'` | `grep -n` 日志 | 无命中 |
| 41 条 `#print axioms` 逐行校验 | python 解析 `axioms.txt` | 41 行，0 处违规 |
| 目标陈述与 PR #5870 逐字符比对 | python 归一化空白后比较 | 完全一致 |
| 交付目录独立编译 | 拷出后只软链 Mathlib 再 `lake build` | 退出 0 |

顶层定理的审计行为：

    'Erdos1091.erdos_1091.variants.counterexample' depends on axioms:
      [propext, Classical.choice, Quot.sound]

这正是 Mathlib 的标准三公理，也是“通过”的唯一可接受输出。41 条审计行中有一条更强：`mem_specialBlocks` 的输出是 `[propext, Quot.sound]`，没有用到 `Classical.choice`。校验脚本按子集判定，因此通过。

### 6.3 全树规模

自有 Lean 源码 3696 行，分布如下；另有 vendored 的 PR #5870 基座 536 行，不计入本工作。

表 10 自有 Lean 源码的文件规模

| 文件 | 行数 | 内容 |
|---|---|---|
| `Erdos1091/Construction.lean` | 855 | 顶点类型、邻接、可判定实例、度数、顶点计数 |
| `Erdos1091/CliqueFree.lean` | 307 | Lemma 4.2 |
| `Erdos1091/Coloring.lean` | 450 | Lemma 4.3、4.4、Prop 4.5、显式 4-着色 |
| `Erdos1091/Degenerate.lean` | 266 | Prop 4.6 |
| `Erdos1091/DegenerateCore.lean` | 138 | 通用件：2-degenerate ⇒ 3-可着色 |
| `Erdos1091/Chords.lean` | 1278 | Lemma 4.7 至 Prop 4.10 |
| `Erdos1091/Main.lean` | 234 | Theorem 4.1 组装、搬运引理、目标陈述 |
| `Erdos1091/Audit.lean` | 116 | 41 条 `#print axioms`，仅用于审计 |
| `Erdos1091.lean` | 52 | 根模块 |

声明总数 217 条，全部证完。`Chords.lean` 占全部自有代码的三分之一强，与弦数上界是本定理形式化成本最高的部分这一事实相符。

### 6.4 已知缺口

**没有。** 全树零 `sorry`、零 `admit`、零自定义 `axiom`、零 `native_decide`，41 条公理审计全部通过，目标陈述已证。上文 5.5 节列出的三处与论文路线的偏离不是缺口：它们证的是更弱但足够的中间命题，最终定理的陈述与强度未受影响。

### 6.5 非空性自检

机械审计只能证明“没有 sorry”，不能证明“构造不是退化的”。为排除“形式化成立但对象为空”这一失败模式，另跑过一组求值检查：

- `Fintype.card (Vtx 2) = 71`、`Fintype.card (Vtx 3) = 91`，与 20m+31 吻合；`Fintype.card (ValidBlock 2) = 14`，与 4m+6 吻合。
- 不对称性真实存在：`(leaf 0 c).validB = false` 且 `(leaf m a).validB = false`，而 `(leaf 0 a).validB = true` 且 `(leaf m c).validB = true`。
- `(G 2).degree (spine 0, a) = 3`，非 v 顶点度数恰为 3；`∃ u, (G 2).Adj v u` 为真。

这组检查用完即删，不进入交付源码。

## 7. 局限与后续

### 7.1 本工作的边界

本工作只形式化了论文第 4 节的 Theorem 4.1 及其支撑引理，没有触及论文其余章节。数学上没有任何新结论；形式化上，5.5 节的三处偏离意味着交付的若干中间引理弱于论文的对应命题，尽管最终定理等价。

本任务按用户诉求交付 Lean 源码与简要说明，**没有走完整研究链**，即不产出论文或文献综述。这是有意的范围决定：形式化工作的价值载体是可编译的源码本身与其审计结论，再套一层学术论文体裁不会增加可验证性。

### 7.2 提交 PR 的形态建议

交付物已经可以直接改造成 formal-conjectures 的 PR。建议形态如下。

把 `Erdos1091/`（可以不含 `Audit.lean`）与 `Erdos1091.lean` 放进 fc 树，丢掉本目录的 `lakefile.toml` 与 `FormalConjecturesForMathlib/`，因为 fc 自带这两个文件。在 `fc/lakefile.toml` 末尾追加：

```toml
[[lean_lib]]
name = "Erdos1091"
globs = ["Erdos1091", "Erdos1091.+"]
```

不要加 `warn.sorry = false`。独立立库的用处是 `lake build Erdos1091` 只编译本形式化的几个文件加它们的 Mathlib 依赖，不去碰 fc 的几千个文件，CI 时间可控。

PR 描述里应当写明：本 PR 填的是 #5870 中那条 `sorry`，签名未动；数学归原作者；新增的三条通用件可以按 reviewer 意见拆分或保留。

### 7.3 可独立上游到 Mathlib 的部分

5.4 节列出的三条通用件与 Erdős 1091 无关，建议单独提交到 Mathlib 而非埋在 fc 里：`colorable_three_of_isTwoDegenerate` 最有价值，因为 2-degenerate 到 3-可着色是图论里的常用事实而 Mathlib 目前缺失；`subgraph_chromaticNumber_congr` 与 `cycle_chords_congr` 属于同构不变性这一类样板结论，Mathlib 对其他图不变量已有对应版本，补齐这两条是自然的。

### 7.4 后续可做的加固

若要把交付物推到论文的最强形式，两项工作是明确的：把不含 v 的圈的弦数从 ≤ 5 收紧到 = 0，需要补一段“C_5 中的圈即 C_5 本身”的论证；把含 v 的圈的计数改回论文的逐块 4+4+1+1 口径，需要补“内部脊块贡献 0”的块树位置讨论。两项都不影响 Theorem 4.1，纯粹是为了让 Lean 版本与纸面版本逐条对应。

## 参考文献

**[1]** Alexeev, B., Putterman, E., Sawhney, M., Sellke, M., Valiant, G. Short proofs in combinatorics, probability and number theory II. arXiv preprint, 2026. [arXiv:2604.06609](https://arxiv.org/abs/2604.06609)

**[2]** stantheman0128. feat: Erdős problem 1091 (statement only). google-deepmind/formal-conjectures Pull Request #5870, 2026. [GitHub](https://github.com/google-deepmind/formal-conjectures/pull/5870)

**[3]** The mathlib Community. The Lean mathematical library. Proceedings of CPP 2020, 2020. [Mathlib4 仓库](https://github.com/leanprover-community/mathlib4)

**[4]** Moura, L. de, Ullrich, S. The Lean 4 Theorem Prover and Programming Language. Proceedings of CADE-28, 2021. [Lean 4 仓库](https://github.com/leanprover/lean4)

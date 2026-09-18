> 📁 **路径说明**：本文写于交付时的目录结构。整理成仓库后，Lake 包已上移到仓库根目录，说明文档移到 `docs/`。文中「本目录」= 仓库根目录；`axioms.txt` 与 `STATUS.md` 与本文同在 `docs/`。
> 仓库级说明见根目录 [`README.md`](../README.md)（英文）。

# Erdős 1091 的 Lean 4 形式化 —— `K₄`-free、4-色、每个圈弦数 ≤ 10 的反例

把 arXiv:2604.06609 *Short proofs in combinatorics, probability and number theory II*
(Alexeev–Putterman–Sawhney–Sellke–Valiant, 2026-04)**第 4 节 Theorem 4.1** 的构造与证明,
重建为机器可验证的 Lean 4 源码。

目标是一份**无 `sorry`、无额外 axiom、可提交到 `google-deepmind/formal-conjectures` 的 PR**。

**状态:已达成。** 217 条声明全部 proved,零 `sorry`;`Erdos1091/Audit.lean` 里 41 条
`#print axioms` 的输出全部只含 Mathlib 标准三条 `[propext, Classical.choice, Quot.sound]`
(证据见 [`axioms.txt`](axioms.txt),逐行机器校验过)。顶层定理
`Erdos1091.erdos_1091.variants.counterexample` 的陈述与 PR #5870 **字符级一致**。
逐条进度见 [`STATUS.md`](STATUS.md)(该表由脚本扫描源码生成,不是手写)。

## Credit

> 第 4 节的数学 —— `Gₘ` 的构造以及全部证明 —— 属于 Alexeev、Putterman、Sawhney、Sellke
> 和 Valiant,**prover credit 归原作者**。本仓主张的是独立的 **formalizer credit**,
> 即把已有的纸面证明翻译成 Lean 并让它通过内核检查这部分工作。

## 在一台干净机器上编译

本目录**就是一个自包含的 Lake 包**(`lakefile.toml` 只依赖 Mathlib),不需要再去 clone
`formal-conjectures`:目标陈述所用的 `SimpleGraph.Cycle` / `Cycle.chords` API 已经随
`FormalConjecturesForMathlib/` 一起附在这里(两个文件,原样保留了 PR #5870 的版权头,
**那部分不是本仓的工作**)。

```bash
# 1) elan(Lean 的工具链管理器)。刻意不装 default toolchain:
#    版本由本目录的 lean-toolchain 决定(leanprover/lean4:v4.33.1)。
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"

cd <本目录>

# 2) 下载 Mathlib 预编译 olean(GB 级;实测 126 秒 / 解包后 6.6 GB)
#    绝不要从源码编译 Mathlib —— 8 核上要几十小时。
lake exe cache get

# 3) 编译 + 审计
LAKE_NUM_JOBS=2 lake build Erdos1091
```

最后一步会连 `Erdos1091/Audit.lean` 一起编译,把 41 条 `#print axioms` 的结果打印到
stdout;把它和随附的 [`axioms.txt`](axioms.txt) 对照即可复核「无 `sorry`、无额外 axiom」。

🔴 **Lake 5.0 删掉了 `-j` / `--jobs`**:`lake build -j2` 会报
`unknown short option '-j'`。并发请用环境变量 `LAKE_NUM_JOBS`。

### 想改成在 formal-conjectures 树内编译(准备提 PR 时)

把 `Erdos1091/`(可不含 `Audit.lean`)与 `Erdos1091.lean` 放进 `fc/`,丢掉本目录的
`lakefile.toml` 与 `FormalConjecturesForMathlib/`(fc 自带),并在 `fc/lakefile.toml`
末尾追加:

```toml
[[lean_lib]]
name = "Erdos1091"
globs = ["Erdos1091", "Erdos1091.+"]
```

(开发期曾在这段下面加 `[lean_lib.leanOptions] warn.sorry = false`,用来让带 `sorry`
的中间态不至于 fail;现在已经零 `sorry`,**这一行应当去掉** —— 留着会掩盖回归。)

独立立库的用处:`lake build Erdos1091` 只编译我们这几个文件加它们的 Mathlib 依赖,
不会去碰 `FormalConjectures` 那几千个文件。

## 文件与引理的对应

沿用论文 §4 的编号。

| 文件 | 内容 |
|---|---|
| [`Erdos1091/Construction.lean`](Erdos1091/Construction.lean) | 顶点类型、邻接关系、`DecidableRel` 实例、度数、顶点计数 `20m+31` |
| [`Erdos1091/CliqueFree.lean`](Erdos1091/CliqueFree.lean) | **L4.2** `Gₘ` 是 `K₄`-free(`G'ₘ` 三角形自由 + `N(v)` 是不交路径之并) |
| [`Erdos1091/Degenerate.lean`](Erdos1091/Degenerate.lean) | **P4.6** 每个真子图 2-degenerate ⇒ 3-可着色 |
| [`Erdos1091/Coloring.lean`](Erdos1091/Coloring.lean) | **L4.3** 叶强制、**L4.4** 脊传播(三个 case)、**P4.5** 不可 3-着色,外加显式 4-着色 `color4` 与 `χ(Gₘ) = 4` |
| [`Erdos1091/Chords.lean`](Erdos1091/Chords.lean) | **L4.7** 圈含于单块、**L4.8/4.9** 叶块/脊块弦计数、**P4.10** `ch(C) ≤ 10` |
| [`Erdos1091/DegenerateCore.lean`](Erdos1091/DegenerateCore.lean) | **通用件**:2-degenerate ⇒ 3-可着色(Mathlib 没有) |
| [`Erdos1091/Main.lean`](Erdos1091/Main.lean) | **T4.1** 组装、两条同构搬运通用件,以及搬到 `Fin n` 上的目标陈述 |
| [`Erdos1091/Audit.lean`](Erdos1091/Audit.lean) | 41 条 `#print axioms`,只用于审计,不被任何文件 import |
| [`Erdos1091.lean`](Erdos1091.lean) | 根模块,`import` 上面全部 |

## 构造(`Gₘ`)

五边形块拼成的毛毛虫,外加一个特殊点 `v`:

- **脊块** `S₀ … S_m`,每块一个 5-圈,顶点按环序标 `a b c d e`。
- **叶块**:`S₀` 挂 4 个(`a b d e`),中间的 `S_i` 各挂 3 个(`b d e`),`S_m` 挂 4 个
  (`b c d e`)。共 `4m+6` 块。
- **块间边**:`S_i[x] — L_{i,x}[x]`,以及脊上 `S_i[c] — S_{i+1}[a]`。
- **特殊点** `v` 连到每个叶块中 4 个非挂接顶点。
- 除 `v` 外每个顶点度数恰为 3;顶点总数 `20m + 31`。

⚠ **不对称性是本质的**:`S₀` 没有 c-叶块、`S_m` 没有 a-叶块。L4.4 和 P4.5 全靠这个 ——
两端的归纳结论互相矛盾才逼出不可 3-着色。代码里这一点写在 `Block.validB` 一处。

## 与 PR #5870 的关系

- 目标陈述 `erdos_1091.variants.counterexample` 取自 PR #5870 的
  `FormalConjectures/ErdosProblems/1091.lean`,**已用脚本逐字符比对确认一致**;
  后续只填证明,不动签名。
- 弦的定义(`SimpleGraph.Cycle` / `Cycle.chords`)直接用 PR 附带的
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Cycle.lean`(475 行)作为基座,
  **不另造一套**。
- PR #5870 里这条定理的证明是 `sorry`;本仓填的就是它,现已填完。
- `Main.lean` 里另有两条**通用件**是本形式化新造、Mathlib 里没有的:
  `subgraph_chromaticNumber_congr`(子图着色数沿图同构不变)与
  `cycle_chords_congr`(弦上界沿图同构不变)。两条都对任意图成立,与 Erdős 1091 无关,
  可以独立上游。

## 关于可判定性与 `decide`

邻接关系是 `Bool` 谓词 + `SimpleGraph.fromRel`,所以 `DecidableRel`、`Fintype` 都能推出来。
但**可判定 ≠ 用 `decide` 证**:顶点数 `20m+31` 里 `m` 是参数,对 `Gₘ` 整体
`decide` / `native_decide` 既会爆内存,对参数化命题也根本不成立。

枚举只用在**固定的小规模有限情形**上,且每处都在注释里标了规模:`Slot` 上最多 `5³ = 125`,
`Fin 3` 配色上最多 `3⁶ = 729`。主定理走结构化证明。

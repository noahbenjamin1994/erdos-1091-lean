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
import Erdos1091.DegenerateCore
import Erdos1091.Degenerate
import Erdos1091.Coloring
import Erdos1091.Chords
import Erdos1091.Main

/-!
# Erdős problem 1091: a `K₄`-free 4-chromatic counterexample with boundedly many chords

A Lean 4 formalization of Section 4 of [APSSV26b], which answers Erdős problem 1091 in the
negative: there is no `f(r) → ∞` such that every 4-chromatic graph all of whose `≤ r`-vertex
subgraphs are 3-colorable contains an odd cycle with at least `f(r)` chords.

| File | Contents |
| --- | --- |
| `Erdos1091.Construction` | the vertex type, adjacency, decidability, degrees, counting |
| `Erdos1091.CliqueFree` | Lemma 4.2 — `Gₘ` is `K₄`-free |
| `Erdos1091.DegenerateCore` | *general-purpose*: 2-degenerate ⇒ 3-colorable (not in Mathlib) |
| `Erdos1091.Degenerate` | Proposition 4.6 — proper subgraphs are 2-degenerate |
| `Erdos1091.Coloring` | Lemmas 4.3, 4.4 and Proposition 4.5 — `χ(Gₘ) = 4` |
| `Erdos1091.Chords` | Lemmas 4.7–4.9 and Proposition 4.10 — `ch(C) ≤ 10` |
| `Erdos1091.Main` | Theorem 4.1 and the PR #5870 target statement |

## Credit

The mathematics is due to Alexeev, Putterman, Sawhney, Sellke and Valiant; **prover credit is
theirs**. This development claims **formalizer credit** only.

## References

* [APSSV26b] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, G. Valiant, *Short proofs in
  combinatorics, probability and number theory II*, arXiv:2604.06609 (2026), Section 4.
* [erdosproblems.com/1091](https://www.erdosproblems.com/1091)
-/

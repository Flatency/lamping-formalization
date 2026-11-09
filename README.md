> **This Lean formalization was produced using large language models (LLMs). The formal statements have not been verified by humans.**
>
> 本 Lean 形式化使用大语言模型（LLM）完成。形式化命题尚未经过人工验证。

# Lamping's algorithm in Lean

This library formalizes the closed-term case of the indexed presentation of Lamping's algorithm in Andrea Asperti and Stefano Guerrini, *The Optimal Implementation of Functional Programming Languages* (Cambridge University Press, 1998). It covers the seven graph rewrite schemas, the translation and readback of closed terms, and a terminating needed evaluator for closed terms that admit a β-normal form.

## Build and check

Install [Elan](https://github.com/leanprover/elan) and run these commands from the repository root. The [toolchain file](lean-toolchain) pins Lean 4.24.0. The package uses only modules bundled with Lean.

```sh
lake build
lake env lean Lamping/Checks/Optimality.lean
```

The build checks the library and its check modules. The second command runs the evaluator on three closed terms, with expected output `(true, true, true)`, and prints the axiom dependencies of ten declarations. The fixtures are `I`, `I I`, and `(λx. x x) I`, where `I = λx. x`. Lean checks the proofs against the statements in this repository. Comparing those statements and definitions with the mathematical claims in the source remains open to human review.

## Main results

| Declaration | What Lean checks |
| --- | --- |
| [`Lamping.AG.Readback.normalizeNeededGraph`](Lamping/Lamping/NeededGraphExecution.lean#L142) | The initialized graph evaluator terminates with β-normal readback for a closed input given a proof that the input has a β-normal form. |
| [`Lamping.AG.Readback.normalizeNeededGraph_reduces`](Lamping/Lamping/Optimality.lean#L16) | The readback is an ordinary β-reduct of the input and is in β-normal form. |
| [`Lamping.AG.Readback.normalizeNeededGraph_spec`](Lamping/Lamping/NeededGraphExecution.lean#L154) | The result has a graph trace from its original initialization with a raw labelled projection `raw`. There is a complete, needed history `prior` with `raw.derivation = prior.derivation`. |
| [`Lamping.AG.ExposureScheduling.finiteCompleteHistoryExecutable`](Lamping/Lamping/ComputedFamilyHistoryReplay.lean#L181) | Given an INIT-labelled closed term and a finite complete history from its erasure, there is an executable graph program whose final readback is the history's endpoint and whose projection is permutation-equivalent (`PermEq`) to that history. |
| [`Lamping.Lambda.CompleteDerivation.familyRoundEnumeration`](Lamping/Lambda/Optimality.lean#L8) | A complete history enumerates its contracted families by rounds. |
| [`Lamping.AG.Readback.normalizeNeededGraph_family_optimal`](Lamping/Lamping/NeededGraphFamilyOptimality.lean#L20) | The whole-family plan of the complete, needed history `prior` uses at most as many copy units as any strict copy partition of a normalizing history from the same closed input. |

The optimality result counts family copy units. The scope of this release leaves open terms, physical graph reduction costs, and garbage collection for later work.

## Relation to Theorem 5.5.5

Given any finite graph trace from the original initialization of a closed term, Lean constructs a raw labelled projection and then a complete observable family history whose endpoint matches the given final graph. The raw projection can represent graph β events with no corresponding term contraction. The observable history omits these empty rounds. [Raw projection](Lamping/Lamping/LabelledTraceProjection.lean#L63) · [Complete family projection](Lamping/Lamping/ReachableJointRepresentation.lean#L240)

Theorem 5.5.5 (printed page 146) uses the same target graph `G` on both sides of the printed equivalence. Its reverse proof proceeds by constructing a sequence of graph steps. The Lean replay theorem also constructs a program and its final graph. Its conclusion is existential in that graph, with exact endpoint readback and a projection permutation-equivalent to the requested history. The reverse implication for a preselected matching `G` is outside the scope of this result. [Executable replay](Lamping/Lamping/ComputedFamilyHistoryReplay.lean#L181)

## Source wording and formalization scope

Both offset cases of Exercise 3.5.25 have counterexamples in the initial encoding of `λx. x x`. At offset zero a fan marker remains at the new level. At offset one the resulting level is `Star (Pair □ □)`, whereas the printed formula requires a `Pair` at the outermost level. The corrected initial-loop formula composes the Cro, Bra, and Fan actions along the control path in order. [Zero offset](Lamping/Lamping/InitialOffsets.lean#L81) · [Offset one](Lamping/Lamping/InitialOffsets.lean#L148) · [Corrected formula](Lamping/Lamping/InitialOffsetFormula.lean#L23)

On printed page 140, the formalization uses conjunction between the two negated conditions in the definition of an auxiliary edge. Under the printed disjunction, the first edge of a prerequisite chain in the initial encoding of `I I` would itself count as auxiliary. [Counterexample to the printed wording](Lamping/Checks/Phase6Review/AuxiliaryWording.lean#L52)

Separately, the library compares auxiliary endpoints when both have successful prerequisite chains. An actual two-step trace from a closed initial term is a counterexample to the earlier comparison that also included pairs of endpoints with no successful chain. [Comparison domain](Lamping/Lamping/FamilyRepresentation.lean#L39) · [Reachable counterexample](Lamping/Checks/AuxiliaryUndefinedCounterexample.lean#L857)

## Library layout

- [`Lamping/Lambda`](Lamping/Lambda) contains λ-term syntax, residuals, histories, labels, families, and the copy-unit comparison.
- [`Lamping/Graph`](Lamping/Graph) contains the port-graph representation and graph operations.
- [`Lamping/Lamping`](Lamping/Lamping) contains the indexed system, paths, projection, readback, and evaluation.
- [`Lamping/Checks`](Lamping/Checks) contains Lean check modules and execution fixtures.

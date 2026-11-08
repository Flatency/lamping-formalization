> **This Lean formalization was produced using large language models (LLMs). The formal statements have not been verified by humans.**
>
> 本 Lean 形式化使用大语言模型（LLM）完成。形式化命题尚未经过人工验证。

# Lamping's algorithm in Lean

This library formalizes the closed-term case of the indexed presentation of Lamping's algorithm in Andrea Asperti and Stefano Guerrini, *The Optimal Implementation of Functional Programming* (Cambridge University Press, 1998). It covers the seven graph rewrite schemas, the translation and readback of closed terms, and a terminating needed evaluator for closed terms that admit a β-normal form.

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
| [`Lamping.AG.Readback.normalizeNeededGraph_spec`](Lamping/Lamping/NeededGraphExecution.lean#L154) | The result has a graph trace from its original initialization and a labelled projection to a complete needed history. |
| [`Lamping.AG.ExposureScheduling.finiteCompleteHistoryExecutable`](Lamping/Lamping/ComputedFamilyHistoryReplay.lean#L181) | A finite complete history can be replayed on the initialized graph under the hypotheses in the theorem. |
| [`Lamping.Lambda.CompleteDerivation.familyRoundEnumeration`](Lamping/Lambda/Optimality.lean#L8) | A complete history enumerates its contracted families by rounds. |
| [`Lamping.AG.Readback.normalizeNeededGraph_family_optimal`](Lamping/Lamping/NeededGraphFamilyOptimality.lean#L20) | The whole-family plan of the projected history uses at most as many copy units as any strict copy partition of a normalizing history from the same closed input. |

The optimality result counts family copy units. The scope of this release leaves open terms, physical graph reduction costs, and garbage collection for later work.

The formalization allows a fan string in the zero-offset case of Exercise 3.5.25 and uses conjunction in the negative definition of an auxiliary edge on printed page 140. The auxiliary-chain comparison in this library ranges over endpoints with successful prerequisite chains.

## Library layout

- [`Lamping/Lambda`](Lamping/Lambda) contains λ-term syntax, residuals, histories, labels, families, and the copy-unit comparison.
- [`Lamping/Graph`](Lamping/Graph) contains the port-graph representation and graph operations.
- [`Lamping/Lamping`](Lamping/Lamping) contains the indexed system, paths, projection, readback, and evaluation.
- [`Lamping/Checks`](Lamping/Checks) contains Lean check modules and execution fixtures.

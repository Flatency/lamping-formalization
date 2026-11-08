import Lamping.Lambda.UncreatedPrerequisiteReadings
import Lamping.Lambda.BetaPreimageLabels

namespace Lamping.Lambda.Labelled
theorem BetaEdgePreimages.length_eq (origins : BetaEdgePreimages body argument site edges oldEdges) :
    edges.length=oldEdges.length := by
  induction origins with
  | nil => rfl
  | cons origin tail ih => exact congrArg Nat.succ ih

/-- ONE induction on the actual all-old chain. Every edge is paired with its
actual beta preimage, so region changes at lexical jumps are retained. -/
theorem PrerequisiteChain.beta_uncreated_reflect
    {source target body argument : LTerm} {site start oldStart : Path} {beta alpha : Label}
    (chain : PrerequisiteChain target start edges)
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site start oldStart)
    (uncreated : ∀ edge∈edges,¬BetaCreatedIncoming body site edge) :
    ∃ oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      BetaEdgePreimages body argument site edges oldEdges := by
  induction chain generalizing oldStart with
  | @redex_app p a l b arg lookup =>
    obtain ⟨oldStamp,oldFn,oldArg,oldLookup,childOrigin,same⟩ :=
      step.beta_app_preimages redex origin lookup (uncreated _ (by simp))
    cases oldFn with
    | var => cases same
    | app => cases same
    | lam oldAlpha oldBody =>
      exact ⟨_,.redex_app oldLookup,.cons childOrigin .nil⟩
  | @redex_lam p a l b arg lookup =>
    obtain ⟨oldParent,parentOrigin⟩ := step.beta_node_preimage redex lookup
    obtain ⟨oldStamp,oldFn,oldArg,oldLookup,childOrigin,same⟩ :=
      step.beta_app_preimages redex parentOrigin lookup (uncreated _ (by simp))
    have oldStartEq := origin.unique childOrigin
    subst oldStart
    cases oldFn with
    | var => cases same
    | app => cases same
    | lam oldAlpha oldBody =>
      exact ⟨_,.redex_lam oldLookup,.cons childOrigin .nil⟩
  | @app p a fn arg es lookup notLambda tail ih =>
    obtain ⟨oldStamp,oldFn,oldArg,oldLookup,childOrigin,same⟩ :=
      step.beta_app_preimages redex origin lookup (uncreated _ (by simp))
    have oldNotLambda : ∀ l b,oldFn≠.lam l b := by
      intro l b equal
      rw [equal] at same
      cases fn with
      | var => cases same
      | app => cases same
      | lam stamp body => exact notLambda stamp body rfl
    obtain ⟨oldEdges,oldChain,edgeOrigins⟩ := ih childOrigin (by
      intro edge member; exact uncreated edge (List.mem_cons_of_mem _ member))
    exact ⟨_,.app oldLookup oldNotLambda oldChain,.cons childOrigin edgeOrigins⟩
  | @lam parent child stamp currentBody es lookup notFunction tail ih =>
    obtain ⟨oldParent,oldStamp,oldBody,oldPositionEq,oldLookup,parentOrigin⟩ :=
      step.beta_lambda_parent_preimage redex origin lookup rfl (uncreated _ (by simp))
    obtain ⟨oldEdges,oldChain,edgeOrigins⟩ := ih parentOrigin (by
      intro edge member; exact uncreated edge (List.mem_cons_of_mem _ member))
    refine ⟨oldStart::oldEdges,?_,.cons origin edgeOrigins⟩
    rw [oldPositionEq] at oldLookup ⊢
    exact .lam oldLookup notFunction oldChain
  | @var leaf stamp index parent binderStamp binderBody rest es lookup binder split depth tail ih =>
    obtain ⟨oldParent,oldStamp,oldBody,oldBinder,oldJump,parentOrigin⟩ :=
      step.beta_variable_preimage_prefix redex origin binder
        (by simpa only [depth] using lookup) split
    obtain ⟨oldEdges,oldChain,edgeOrigins⟩ := ih parentOrigin uncreated
    exact ⟨oldEdges,oldJump.close oldChain,edgeOrigins⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem PrerequisiteChain.actual_start_lookup (chain : PrerequisiteChain t start edges) :
    ∃ current,t.subterm start=some current := by
  cases chain with
  | redex_app lookup => exact ⟨_,lookup⟩
  | @redex_lam p appStamp lamStamp body arg lookup =>
    refine ⟨.lam lamStamp body,?_⟩
    rw [LTerm.subterm_append,lookup]; rfl
  | app lookup _ _ => exact ⟨_,lookup⟩
  | lam lookup _ _ => exact ⟨_,lookup⟩
  | var lookup _ _ _ _ => exact ⟨_,lookup⟩

private theorem PrerequisiteChain.actual_edge_lookup (chain : PrerequisiteChain t start edges)
    (member : edge∈edges) : ∃ current,t.subterm edge=some current := by
  rcases chain.eligible member with ⟨parent,stamp,fn,arg,equal,lookup⟩ | ⟨stamp,body,lookup⟩
  · refine ⟨fn,?_⟩
    rw [equal,LTerm.subterm_append,lookup]; cases fn <;> rfl
  · exact ⟨_,lookup⟩

/-- Backward all-old chain transport from actual syntax alone. The start
may have a created incoming label; only the chain's read edges are old.
No caller old coordinate, source chain, label equality or fixed map is input. -/
theorem StepAt.uncreated_chain_reflect
    {source target body argument : LTerm} {site start : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (chain : PrerequisiteChain target start edges)
    (uncreated : ∀ edge∈edges,¬BetaCreatedIncoming body site edge) :
    ∃ oldStart oldEdges,BetaNodePreimage body argument site start oldStart ∧
      PrerequisiteChain source oldStart oldEdges ∧
      BetaEdgePreimages body argument site edges oldEdges ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length := by
  obtain ⟨current,lookup⟩ := chain.actual_start_lookup
  obtain ⟨oldStart,origin⟩ := step.beta_node_preimage redex lookup
  obtain ⟨oldEdges,oldChain,edgeOrigins⟩ := chain.beta_uncreated_reflect step redex origin uncreated
  have labels := step.beta_preimage_ordered_labels redex edgeOrigins
    (fun edge member=>chain.actual_edge_lookup member) uncreated
  exact ⟨oldStart,oldEdges,origin,oldChain,edgeOrigins,labels,edgeOrigins.length_eq⟩
end Lamping.Lambda.Labelled
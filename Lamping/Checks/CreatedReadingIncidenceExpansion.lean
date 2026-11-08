import Lamping.Lamping.CreatedReadingIncidenceExpansion
import Lamping.Checks.ForwardOtherLastEndpoints
import Lamping.Checks.BackwardOtherLastFarSources
namespace Lamping.Checks.CreatedReadingIncidenceExpansionChecks
open Lambda Lambda.Labelled SyntaxIncidence

namespace Overlap
open DirectedReadingDecompositionChecks
def currentApp : ProperPosition target:=⟨[],Or.inl ⟨_,_,_,rfl⟩⟩
def currentLambda : ProperPosition target:=⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
def oldApp : ProperPosition source:=⟨[],Or.inl ⟨_,_,_,rfl⟩⟩
def oldArgument : ProperPosition source:=⟨[.fn,.arg],Or.inr ⟨_,_,rfl⟩⟩
def oldSelected : ProperPosition source:=⟨[.fn,.fn],Or.inr ⟨_,_,rfl⟩⟩

def forward_expansion := functionOrigin.incidence_expansion (currentFar:=some currentLambda) step (by rfl)
  (show PrerequisiteReadsDirected target [] [.fn] true from ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩)
  (show target.subterm [.fn]=some result from rfl)
  (show Target target [] (some currentApp) from Or.inl rfl)
  (show Target target [.fn] (some currentLambda) from Or.inl rfl)

def backward_expansion := contextOrigin.incidence_expansion (currentFar:=some currentApp) step (by rfl)
  (show PrerequisiteReadsDirected target [.fn] [.fn] false from ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩)
  (show target.subterm [.fn]=some result from rfl)
  (show Target target [.fn] (some currentLambda) from Or.inl rfl)
  (show Source target [.fn] (some currentApp) from ⟨.fn,_,_,rfl,rfl,.fn⟩)

/-- Both terminal singleton readings consume the actual expansion producer;
there is no invented AFTER reader. The extra selected edge is repeated. -/
theorem exact_forward_five :
    IncidenceChase source (some oldApp)
      [[.fn],[.fn,.fn],[.fn,.fn,.body],[.fn,.fn],[.fn,.arg]] [true,true,true,false,true] (some oldArgument) := by
  obtain ⟨near,far,es,ds,_,nearOrigin,walk,farOrigin,_,expansion⟩:=forward_expansion
  have knownNear : BetaVertexPreimage (.var (.atom 3) 0) arg [.fn] source target (some currentApp) (some oldApp) :=
    .proper (.context (by rintro ⟨relative,impossible⟩;cases impossible))
  have knownFar : BetaVertexPreimage (.var (.atom 3) 0) arg [.fn] source target (some currentLambda) (some oldArgument) :=
    .proper (.copied (q:=[]) (relative:=[]) rfl rfl)
  have n:=nearOrigin.unique knownNear
  have f:=farOrigin.unique knownFar
  subst near;subst far
  cases expansion with
  | resultFunction other => exact False.elim (other (.atom 3) rfl)
  | resultOverlap shape => exact walk

/-- In the reverse q=[] reading the true expanded FAR is the old context
parent, whereas triple otherLast has its selected-lambda Source. -/
theorem exact_backward_five :
    IncidenceChase source (some oldArgument)
      [[.fn,.arg],[.fn,.fn],[.fn,.fn,.body],[.fn,.fn],[.fn]] [false,true,false,false,false] (some oldApp) := by
  obtain ⟨near,far,es,ds,_,nearOrigin,walk,farOrigin,_,expansion⟩:=backward_expansion
  have knownNear : BetaVertexPreimage (.var (.atom 3) 0) arg [.fn] source target (some currentLambda) (some oldArgument) :=
    .proper (.copied (q:=[]) (relative:=[]) rfl rfl)
  have knownFar : BetaVertexPreimage (.var (.atom 3) 0) arg [.fn] source target (some currentApp) (some oldApp) :=
    .proper (.context (by rintro ⟨relative,impossible⟩;cases impossible))
  have n:=nearOrigin.unique knownNear
  have f:=farOrigin.unique knownFar
  subst near;subst far
  cases expansion with
  | copyLambda positive => exact False.elim (positive rfl)
  | copyOverlap => exact walk

theorem variable_loop : Source source [.fn,.fn,.body] (some oldSelected) ∧
    Target source [.fn,.fn,.body] (some oldSelected) :=
  ⟨⟨.body,_,_,rfl,rfl,.body⟩,Or.inr ⟨.atom 3,0,.atom 2,.var (.atom 3) 0,[],rfl,rfl,rfl,rfl⟩⟩

theorem successful_terminal_pair : PrerequisiteChain target [] [[.fn]] ∧
    PrerequisiteChain target [.fn] [[.fn]] := ⟨successful_function,successful_context⟩

/-- The expanded far preimages cannot be replaced by the old triple's
selected lambda, in either actual terminal reading. -/
theorem not_triple_far_preimages :
    ¬BetaVertexPreimage (.var (.atom 3) 0) arg [.fn] source target (some currentLambda) (some oldSelected) ∧
    ¬BetaVertexPreimage (.var (.atom 3) 0) arg [.fn] source target (some currentApp) (some oldSelected) := by
  constructor
  · intro wrong
    have actual : BetaVertexPreimage (.var (.atom 3) 0) arg [.fn] source target (some currentLambda) (some oldArgument) :=
      .proper (.copied (q:=[]) (relative:=[]) rfl rfl)
    have same : ([Step.fn,Step.fn]:Path)=[.fn,.arg] := congrArg Subtype.val (Option.some.inj (wrong.unique actual))
    cases same
  · intro wrong
    have actual : BetaVertexPreimage (.var (.atom 3) 0) arg [.fn] source target (some currentApp) (some oldApp) :=
      .proper (.context (by rintro ⟨relative,impossible⟩;cases impossible))
    have same : ([Step.fn,Step.fn]:Path)=[] := congrArg Subtype.val (Option.some.inj (wrong.unique actual))
    cases same
end Overlap

namespace BodyApp
open ForwardOtherLastEndpointsChecks.BodyApp
def near : ProperPosition target:=⟨[],Or.inl ⟨_,_,_,rfl⟩⟩
def far : ProperPosition target:=⟨[.fn],Or.inl ⟨_,_,_,rfl⟩⟩
def actual_expansion := origin.incidence_expansion (currentFar:=some far) event.turn event.redex
  (show PrerequisiteReadsDirected target [] [.fn] true from ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩)
  (show target.subterm [.fn]=some (LTerm.contract (.atom 1) (.atom 2) body arg) from rfl)
  (show Target target [] (some near) from Or.inl rfl)
  (show Target target [.fn] (some far) from Or.inl rfl)
theorem actual_after : PrerequisiteChain target [] [[.fn],[.fn,.fn]] := remaining
end BodyApp

namespace OuterBinder
open ForwardOtherLastEndpointsChecks.ArgOuterBinder
def near : ProperPosition target:=⟨site,Or.inl ⟨_,_,_,rfl⟩⟩
def far : ProperPosition target:=⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
def actual_expansion := origin.incidence_expansion (currentFar:=some far) event.turn event.redex
  (show PrerequisiteReadsDirected target site (site++[.fn]) true from ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩)
  (show target.subterm (site++[.fn])=some (.var _ 0) from rfl)
  (show Target target site (some near) from Or.inl rfl)
  (show Target target (site++[.fn]) (some far) from
    Or.inr ⟨_,0,_,_,[.fn],rfl,rfl,rfl,rfl⟩)

theorem actual_after_binder : PrerequisiteChain target site [site++[.fn],[.fn]] := remaining

/-- The returned far vertex is the original outer lambda, not the selected
lambda or a lambda chosen by its stamp. Both coordinates are locked by the
SAME concrete preimage witnesses returned by the new producer. -/
theorem exact_outer_binder_chase :
    let oldNear : ProperPosition source:=⟨site++[.fn,.body],Or.inl ⟨_,_,_,rfl⟩⟩
    let oldFar : ProperPosition source:=⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
    IncidenceChase source (some oldNear)
      [site++[.fn,.body,.fn],site++[.fn],site++[.arg]] [true,false,true] (some oldFar) ∧
      Target source (site++[.arg]) (some oldFar) := by
  dsimp only
  obtain ⟨oldNear,oldFar,es,ds,_,nearOrigin,walk,farOrigin,endSpec,expansion⟩:=actual_expansion
  let sourceNear : ProperPosition source:=⟨site++[.fn,.body],Or.inl ⟨_,_,_,rfl⟩⟩
  let sourceFar : ProperPosition source:=⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
  have knownNear : BetaVertexPreimage body arg site source target (some near) (some sourceNear) :=
    .proper (.retained (relative:=[]) rfl (by intro stamp impossible;cases impossible))
  have knownFar : BetaVertexPreimage body arg site source target (some far) (some sourceFar) :=
    .proper (.context (by
      rintro ⟨relative,eq⟩
      have len:=congrArg List.length eq
      simp only [far,site,List.length_cons,List.length_nil,List.length_append] at len
      omega))
  have n:=nearOrigin.unique knownNear
  have f:=farOrigin.unique knownFar
  subst oldNear;subst oldFar
  cases expansion with
  | copyFunction => exact ⟨walk,endSpec⟩
end OuterBinder

namespace NonemptyCopy
open BackwardOtherLastFarSourcesChecks.NonemptyCopy
def near : ProperPosition target:=⟨[.arg],Or.inr ⟨_,_,rfl⟩⟩
def far : ProperPosition target:=⟨[],Or.inl ⟨_,_,_,rfl⟩⟩
def actual_expansion := origin.incidence_expansion (currentFar:=some far) event.turn event.redex reading
  (show target.subterm [.arg]=some (.lam _ _) from rfl)
  (show Target target [.arg] (some near) from Or.inl rfl)
  (show Source target [.arg] (some far) from ⟨.arg,_,_,rfl,rfl,.arg⟩)
def terminal_expansion := terminalOrigin.incidence_expansion (currentFar:=some far) event.turn event.redex terminalRead
  (show target.subterm [.fn]=some (.lam _ _) from rfl)
  (show Target target [.fn] (some ⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩) from Or.inl rfl)
  (show Source target [.fn] (some far) from ⟨.fn,_,_,rfl,rfl,.fn⟩)
theorem actual_nonterminal : PrerequisiteChain target [.arg] [[.arg],[.fn]] := remaining
theorem actual_terminal : PrerequisiteChain target [.fn] [[.fn]] := terminalChain
end NonemptyCopy

namespace ResultContext
open BackwardOtherLastFarSourcesChecks.ResultContext
def near : ProperPosition target:=⟨[.arg],Or.inr ⟨_,_,rfl⟩⟩
def far : ProperPosition target:=⟨[],Or.inl ⟨_,_,_,rfl⟩⟩
def actual_expansion := origin.incidence_expansion (currentFar:=some far) event.turn event.redex reading
  (show target.subterm [.arg]=some (.lam _ _) from rfl)
  (show Target target [.arg] (some near) from Or.inl rfl)
  (show Source target [.arg] (some far) from ⟨.arg,_,_,rfl,rfl,.arg⟩)
theorem actual_after : PrerequisiteChain target [.arg] [[.arg],[.fn]] := remaining
end ResultContext

namespace NonemptyOldPrefix
open ForwardOtherLastEndpointsChecks.NonemptyOldPrefix
def near : ProperPosition target:=⟨[],Or.inl ⟨_,_,_,rfl⟩⟩
def far : ProperPosition target:=⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
def actual_expansion := origin.incidence_expansion (currentFar:=some far) event.turn event.redex
  (show PrerequisiteReadsDirected target [] [.fn] true from ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩)
  (show target.subterm [.fn]=some (.lam _ _) from rfl)
  (show Target target [] (some near) from Or.inl rfl)
  (show Target target [.fn] (some far) from Or.inl rfl)
theorem same_original_init : INIT original ∧Closed original.erase ∧History [[],[.arg],[.fn]] original target := same_initial_history
end NonemptyOldPrefix

namespace External
open BackwardOtherLastTargetsChecks.ResultLambda
def near : ProperPosition target:=⟨[],Or.inr ⟨_,_,rfl⟩⟩
def actual_expansion := origin.incidence_expansion (currentFar:=none) event.turn event.redex
  (show PrerequisiteReadsDirected target [] [] false from ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩)
  (show target.subterm []=some (.lam _ _) from rfl)
  (show Target target [] (some near) from Or.inl rfl)
  (show Source target [] none from rfl)
theorem no_completed_boundary : ¬∃edges,AG.EndpointChain source none edges := by rintro ⟨edges,h⟩;exact h
end External

#print axioms BetaIncomingReadingOrigin.incidence_expansion
#print axioms Overlap.exact_forward_five
#print axioms Overlap.exact_backward_five
#print axioms Overlap.variable_loop
#print axioms Overlap.successful_terminal_pair
#print axioms Overlap.not_triple_far_preimages
#print axioms BodyApp.actual_expansion
#print axioms OuterBinder.actual_expansion
#print axioms OuterBinder.exact_outer_binder_chase
#print axioms NonemptyCopy.actual_expansion
#print axioms NonemptyCopy.terminal_expansion
#print axioms ResultContext.actual_expansion
#print axioms NonemptyOldPrefix.actual_expansion
#print axioms NonemptyOldPrefix.same_original_init
#print axioms External.actual_expansion
#print axioms External.no_completed_boundary
end Lamping.Checks.CreatedReadingIncidenceExpansionChecks

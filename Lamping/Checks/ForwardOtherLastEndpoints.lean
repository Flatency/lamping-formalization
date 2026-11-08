import Lamping.Lamping.ForwardOtherLastEndpoints
import Lamping.Checks.DirectedReadingDecomposition
namespace Lamping.Checks.ForwardOtherLastEndpointsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
abbrev I : Term:=WrappedSuccessfulChains.I

private theorem event_pair_available
    {F pre : List Path} {source middle target : LTerm} {degree : Label} {site : Path}
    {edge reader oldReader first last oldEdge : Path} {after : List Path}
    (event : SelectedOldTurn F source degree pre middle target site)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge true)
    (remaining : PrerequisiteChain target reader (edge::after))
    (trace : BetaNodeHistoryPreimage event.labels last oldEdge)
    (near far : ProperPosition source) (fromNear : Source source oldEdge (some near))
    (toFar : Target source oldEdge (some far)) :
    ∃ns fs,EndpointChain source (some near) ns ∧EndpointChain source (some far) fs := by
  obtain ⟨original,oldNear,oldFar,ns,fs,lookup,oldSource,oldTarget,nc,fc⟩:=
    event.forward_original_other_last_available origin reading remaining trace
  rw [Source.unique oldSource fromNear] at nc
  rw [Target.unique oldTarget toFar] at fc
  exact ⟨ns,fs,nc,fc⟩

namespace Overlap
open DirectedReadingDecompositionChecks
abbrev F : List Path := [[.fn]]
def event : SelectedOldTurn F source (.atom 2) [] source target [.fn] where
  markedBefore := Marked.mark F source.erase
  markedAfter := .app [] (.lam (.var 0)) (.lam (.var 0))
  beforeOld := .nil _
  reduction := .appL (.redRoot _ _ _)
  member := by decide
  labels := .nil _
  turn := step
  beta := .atom 1
  body := .var (.atom 3) 0
  argument := arg
  redex := rfl

def near : ProperPosition source:=⟨[.fn,.fn],Or.inr ⟨.atom 2,.var (.atom 3) 0,rfl⟩⟩
theorem endpoint_pair : ∃ns fs,EndpointChain source (some near) ns ∧EndpointChain source (some near) fs :=
  event_pair_available event functionOrigin ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ successful_function (.nil _ _) near near
    ⟨.body,_,_,rfl,rfl,.body⟩ (Or.inr ⟨_,0,_,_,[],rfl,rfl,rfl,rfl⟩)

theorem terminal_no_after : ∃far : ProperPosition target,Target target [.fn] (some far) ∧
    far.val=[.fn] ∧EndpointChain target (some far) [[.fn]] := by
  obtain ⟨far,toFar,continuation⟩:=successful_function.forward_target_available ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
  rcases continuation with ⟨impossible,_⟩ |⟨_,same,chain⟩
  · exact False.elim (impossible rfl)
  · exact ⟨far,toFar,same,chain⟩

theorem actual_history : INIT source ∧Closed source.erase ∧History [[.fn]] source target := ⟨initial,closed,history⟩
end Overlap

namespace BodyApp
abbrev source : LTerm:=initLabels (.app (.app (.lam (.app (.var 0) I)) I) I)
abbrev body : LTerm:=.app (.atom 3) (.var (.atom 4) 0) (.lam (.atom 5) (.var (.atom 6) 0))
abbrev arg : LTerm:=.lam (.atom 7) (.var (.atom 8) 0)
abbrev target : LTerm:=.app (.atom 0) (LTerm.contract (.atom 1) (.atom 2) body arg) (.lam (.atom 9) (.var (.atom 10) 0))
def event : SelectedOldTurn [[.fn]] source (.atom 2) [] source target [.fn] where
  markedBefore := Marked.mark [[.fn]] source.erase
  markedAfter := .app [] (.app [] (.lam (.var 0)) (.lam (.var 0))) (.lam (.var 0))
  beforeOld := .nil _
  reduction := .appL (.redRoot _ _ _)
  member := by decide
  labels := .nil _
  turn := .fn (.root _ _ _ _)
  beta := .atom 1
  body := body
  argument := arg
  redex := rfl

def origin : BetaIncomingReadingOrigin body arg [.fn] [.fn] [] [] [.fn] [.fn,.fn,.body] := .resultFunction rfl rfl
def remaining : PrerequisiteChain target [] [[.fn],[.fn,.fn]] :=
  .app rfl (by intro a b impossible;cases impossible) (.redex_app rfl)
def near : ProperPosition source:=⟨[.fn,.fn],Or.inr ⟨.atom 2,body,rfl⟩⟩
def far : ProperPosition source:=⟨[.fn,.fn,.body],Or.inl ⟨.atom 3,.var (.atom 4) 0,_,rfl⟩⟩
theorem endpoint_pair : ∃ns fs,EndpointChain source (some near) ns ∧EndpointChain source (some far) fs :=
  event_pair_available event origin ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ remaining (.nil _ _) near far
    ⟨.body,_,_,rfl,rfl,.body⟩ (Or.inl rfl)
theorem actual_history : INIT source ∧Closed source.erase ∧History [[.fn]] source target :=
  ⟨init_is_INIT _,by simp [Closed,Scoped,source,initLabels,initFrom,nodeCount,LTerm.erase],.cons event.turn (.nil _)⟩
end BodyApp

namespace ArgApp
abbrev source : LTerm:=initLabels (.app (.lam (.app (.var 0) I)) (.app I I))
abbrev body : LTerm:=.app (.atom 2) (.var (.atom 3) 0) (.lam (.atom 4) (.var (.atom 5) 0))
abbrev arg : LTerm:=.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) (.lam (.atom 9) (.var (.atom 10) 0))
abbrev target : LTerm:=LTerm.contract (.atom 0) (.atom 1) body arg

def event : SelectedOldTurn [[]] source (.atom 1) [] source target [] where
  markedBefore := Marked.mark [[]] source.erase
  markedAfter := .app [] (.app [[.arg]] (.lam (.var 0)) (.lam (.var 0))) (.lam (.var 0))
  beforeOld := .nil _
  reduction := .redRoot _ _ _
  member := by decide
  labels := .nil _
  turn := .root _ _ _ _
  beta := .atom 0
  body := body
  argument := arg
  redex := rfl

def origin : BetaIncomingReadingOrigin body arg [] [.fn] [] [.fn,.body] [.fn,.body,.fn] [.arg] :=
  .copyFunction (parent:=[]) rfl rfl rfl

def remaining : PrerequisiteChain target [] [[.fn],[.fn,.fn]] :=
  .app rfl (by intro a b impossible;cases impossible) (.redex_app rfl)
def near : ProperPosition source:=⟨[],Or.inl ⟨.atom 0,.lam (.atom 1) body,arg,rfl⟩⟩
def far : ProperPosition source:=⟨[.arg],Or.inl ⟨.atom 6,_,_,rfl⟩⟩
theorem endpoint_pair : ∃ns fs,EndpointChain source (some near) ns ∧EndpointChain source (some far) fs :=
  event_pair_available event origin ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ remaining (.nil _ _) near far
    ⟨.arg,_,_,rfl,rfl,.arg⟩ (Or.inl rfl)
theorem actual_history : INIT source ∧Closed source.erase ∧History [[]] source target :=
  ⟨init_is_INIT _,by simp [Closed,Scoped,source,initLabels,initFrom,nodeCount,LTerm.erase],.cons event.turn (.nil _)⟩
end ArgApp

namespace ArgLambda
abbrev source : LTerm:=initLabels (.app (.lam (.app (.var 0) I)) I)
abbrev body : LTerm:=ArgApp.body
abbrev arg : LTerm:=.lam (.atom 6) (.var (.atom 7) 0)
abbrev target : LTerm:=LTerm.contract (.atom 0) (.atom 1) body arg

def event : SelectedOldTurn [[]] source (.atom 1) [] source target [] where
  markedBefore := Marked.mark [[]] source.erase
  markedAfter := .app [] (.lam (.var 0)) (.lam (.var 0))
  beforeOld := .nil _
  reduction := .redRoot _ _ _
  member := by decide
  labels := .nil _
  turn := .root _ _ _ _
  beta := .atom 0
  body := body
  argument := arg
  redex := rfl

def origin : BetaIncomingReadingOrigin body arg [] [.fn] [] [.fn,.body] [.fn,.body,.fn] [.arg] :=
  .copyFunction (parent:=[]) rfl rfl rfl

def near : ProperPosition source:=⟨[],Or.inl ⟨.atom 0,.lam (.atom 1) body,arg,rfl⟩⟩
def far : ProperPosition source:=⟨[.arg],Or.inr ⟨.atom 6,_,rfl⟩⟩
theorem endpoint_pair : ∃ns fs,EndpointChain source (some near) ns ∧EndpointChain source (some far) fs :=
  event_pair_available event origin ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ (.redex_app rfl) (.nil _ _) near far
    ⟨.arg,_,_,rfl,rfl,.arg⟩ (Or.inl rfl)
theorem actual_history : INIT source ∧Closed source.erase ∧History [[]] source target :=
  ⟨init_is_INIT _,by simp [Closed,Scoped,source,initLabels,initFrom,nodeCount,LTerm.erase],.cons event.turn (.nil _)⟩
end ArgLambda

namespace ArgOuterBinder
abbrev source : LTerm:=initLabels (.app (.lam (.app (.lam (.app (.var 0) (.var 0))) (.var 0))) I)
abbrev site : Path:=[.fn,.body]
abbrev body : LTerm:=.app (.atom 4) (.var (.atom 5) 0) (.var (.atom 6) 0)
abbrev arg : LTerm:=.var (.atom 7) 0
abbrev target : LTerm:=.app (.atom 0) (.lam (.atom 1) (LTerm.contract (.atom 2) (.atom 3) body arg)) (.lam (.atom 8) (.var (.atom 9) 0))

def event : SelectedOldTurn [site] source (.atom 3) [] source target site where
  markedBefore := Marked.mark [site] source.erase
  markedAfter := .app [[]] (.lam (.app [] (.var 0) (.var 0))) (.lam (.var 0))
  beforeOld := .nil _
  reduction := .appL (.lam (.redRoot _ _ _))
  member := by decide
  labels := .nil _
  turn := .fn (.body (.root _ _ _ _))
  beta := .atom 2
  body := body
  argument := arg
  redex := rfl

def origin : BetaIncomingReadingOrigin body arg site (site++[.fn]) site (site++[.fn,.body])
    (site++[.fn,.body,.fn]) (site++[.arg]) := .copyFunction (parent:=[]) rfl rfl rfl

def remaining : PrerequisiteChain target site [site++[.fn],[.fn]] := by
  apply PrerequisiteChain.app rfl (by intro a b impossible;cases impossible)
  apply PrerequisiteChain.var (parent:=[.fn]) (rest:=[.fn])
  · rfl
  · rfl
  · rfl
  · rfl
  · exact PrerequisiteChain.redex_lam (p:=[]) (t:=target) rfl

def near : ProperPosition source:=⟨site,Or.inl ⟨.atom 2,.lam (.atom 3) body,arg,rfl⟩⟩
def far : ProperPosition source:=⟨[.fn],Or.inr ⟨.atom 1,_,rfl⟩⟩
theorem endpoint_pair : ∃ns fs,EndpointChain source (some near) ns ∧EndpointChain source (some far) fs :=
  event_pair_available event origin ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ remaining (.nil _ _) near far
    ⟨.arg,_,_,rfl,rfl,.arg⟩ (Or.inr ⟨.atom 7,0,.atom 1,_,[.arg],rfl,rfl,rfl,rfl⟩)
theorem actual_history : INIT source ∧Closed source.erase ∧History [site] source target :=
  ⟨init_is_INIT _,by simp [Closed,Scoped,source,initLabels,initFrom,nodeCount,LTerm.erase],.cons event.turn (.nil _)⟩
end ArgOuterBinder

namespace BodyOuterBinder
abbrev source : LTerm:=initLabels (.app (.lam (.app (.app (.lam (.var 1)) I) I)) I)
abbrev site : Path:=[.fn,.body,.fn]
abbrev body : LTerm:=.var (.atom 5) 1
abbrev arg : LTerm:=.lam (.atom 6) (.var (.atom 7) 0)
abbrev target : LTerm:=.app (.atom 0) (.lam (.atom 1)
  (.app (.atom 2) (LTerm.contract (.atom 3) (.atom 4) body arg) (.lam (.atom 8) (.var (.atom 9) 0))))
  (.lam (.atom 10) (.var (.atom 11) 0))
def event : SelectedOldTurn [site] source (.atom 4) [] source target site where
  markedBefore := Marked.mark [site] source.erase
  markedAfter := .app [[]] (.lam (.app [] (.var 0) (.lam (.var 0)))) (.lam (.var 0))
  beforeOld := .nil _
  reduction := .appL (.lam (.appL (.redRoot _ _ _)))
  member := by decide
  labels := .nil _
  turn := .fn (.body (.fn (.root _ _ _ _)))
  beta := .atom 3
  body := body
  argument := arg
  redex := rfl

def origin : BetaIncomingReadingOrigin body arg site site [.fn,.body] [.fn,.body] site (site++[.fn,.body]) :=
  .resultFunction rfl rfl

def remaining : PrerequisiteChain target [.fn,.body] [site,[.fn]] := by
  apply PrerequisiteChain.app rfl (by intro a b impossible;cases impossible)
  apply PrerequisiteChain.var (parent:=[.fn]) (rest:=[.fn])
  · rfl
  · rfl
  · rfl
  · rfl
  · exact PrerequisiteChain.redex_lam (p:=[]) (t:=target) rfl

def near : ProperPosition source:=⟨site++[.fn],Or.inr ⟨.atom 4,body,rfl⟩⟩
def far : ProperPosition source:=⟨[.fn],Or.inr ⟨.atom 1,_,rfl⟩⟩
theorem endpoint_pair : ∃ns fs,EndpointChain source (some near) ns ∧EndpointChain source (some far) fs :=
  event_pair_available event origin ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ remaining (.nil _ _) near far
    ⟨.body,_,_,rfl,rfl,.body⟩ (Or.inr ⟨.atom 5,1,.atom 1,_,[.fn,.fn,.body],rfl,rfl,rfl,rfl⟩)
theorem actual_history : INIT source ∧Closed source.erase ∧History [site] source target :=
  ⟨init_is_INIT _,by simp [Closed,Scoped,source,initLabels,initFrom,nodeCount,LTerm.erase],.cons event.turn (.nil _)⟩
end BodyOuterBinder

namespace NonemptyOldPrefix
abbrev bare : Term:=.app (.lam (.app (.var 0) (.var 0))) (.app I I)
abbrev original : LTerm:=initLabels bare
abbrev source : LTerm:=WrappedSuccessfulChains.contractRoot original
abbrev left : LTerm:=match source with | .app _ l _=>l | t=>t
abbrev right : LTerm:=match source with | .app _ _ r=>r | t=>t
abbrev middle : LTerm:=.app source.label left (WrappedSuccessfulChains.contractRoot right)
abbrev target : LTerm:=.app source.label (WrappedSuccessfulChains.contractRoot left) (WrappedSuccessfulChains.contractRoot right)
abbrev arg : LTerm:=.lam (.atom 8) (.var (.atom 9) 0)
abbrev F : List Path:=[[.fn],[.arg]]
def firstStep : StepAt [.arg] source middle:=.arg (.root _ _ _ _)
def labels : History [[.arg]] source middle:=.cons firstStep (.nil _)
def event : SelectedOldTurn F source (.atom 6) [[.arg]] middle target [.fn] where
  markedBefore := .app [] (.red [[.fn]] (.var 0) (.lam (.var 0))) (.lam (.var 0))
  markedAfter := .app [] (.lam (.var 0)) (.lam (.var 0))
  beforeOld := .cons (.appR (.redRoot _ _ _)) (by decide) (.nil _)
  reduction := .appL (.redRoot _ _ _)
  member := by decide
  labels := labels
  turn := .fn (.root _ _ _ _)
  beta := left.label
  body := .var (.atom 7) 0
  argument := arg
  redex := rfl

def origin : BetaIncomingReadingOrigin (.var (.atom 7) 0) arg [.fn] [.fn] [] [] [.fn] [.fn,.fn,.body] :=
  .resultFunction rfl rfl

def trace : BetaNodeHistoryPreimage event.labels [.fn,.fn,.body] [.fn,.fn,.body] :=
  .one (step:=firstStep) (by rfl) (.context (by rintro ⟨rest,eq⟩;cases eq)) (.nil _ _)
def near : ProperPosition source:=⟨[.fn,.fn],Or.inr ⟨.atom 6,.var (.atom 7) 0,rfl⟩⟩
theorem endpoint_pair : ∃ns fs,EndpointChain source (some near) ns ∧EndpointChain source (some near) fs :=
  event_pair_available event origin ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ (.redex_app rfl) trace near near
    ⟨.body,_,_,rfl,rfl,.body⟩ (Or.inr ⟨.atom 7,0,.atom 6,_,[],rfl,rfl,rfl,rfl⟩)
theorem same_initial_history : INIT original ∧Closed original.erase ∧History [[],[.arg],[.fn]] original target :=
  ⟨init_is_INIT _,by simp [Closed,Scoped,original,initLabels,initFrom,nodeCount,LTerm.erase],
    .cons (.root _ _ _ _) (.cons firstStep (.cons event.turn (.nil _)))⟩
end NonemptyOldPrefix

namespace BodyLambda
open DirectedReadingDecompositionChecks

def event : SelectedOldTurn [[.fn]] rSource (.atom 2) [] rSource rTarget [.fn] where
  markedBefore := Marked.mark [[.fn]] rSource.erase
  markedAfter := .app [] (.lam (.lam (.var 0))) (.lam (.var 0))
  beforeOld := .nil _
  reduction := .appL (.redRoot _ _ _)
  member := by decide
  labels := .nil _
  turn := rStep
  beta := .atom 1
  body := rBody
  argument := .lam (.atom 5) (.var (.atom 6) 0)
  redex := rfl

def origin : BetaIncomingReadingOrigin rBody (.lam (.atom 5) (.var (.atom 6) 0)) [.fn] [.fn] []
    [] [.fn] [.fn,.fn,.body] := .resultFunction rfl rfl

def near : ProperPosition rSource:=⟨[.fn,.fn],Or.inr ⟨.atom 2,rBody,rfl⟩⟩
def far : ProperPosition rSource:=⟨[.fn,.fn,.body],Or.inr ⟨.atom 3,.var (.atom 4) 1,rfl⟩⟩
theorem endpoint_pair : ∃ns fs,EndpointChain rSource (some near) ns ∧EndpointChain rSource (some far) fs :=
  event_pair_available event origin ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ (.redex_app rfl) (.nil _ _) near far
    ⟨.body,_,_,rfl,rfl,.body⟩ (Or.inl rfl)
theorem actual_history : INIT rSource ∧Closed rSource.erase ∧History [[.fn]] rSource rTarget :=
  ⟨init_is_INIT _,by simp [Closed,Scoped,rSource,initLabels,initFrom,nodeCount,LTerm.erase],.cons event.turn (.nil _)⟩
end BodyLambda

-- Forward NEAR is a genuine parent, while a successful FAR is never the
-- external boundary. This does not assert success for arbitrary open terms.
theorem overlap_external_excluded :
    ¬Source DirectedReadingDecompositionChecks.source [.fn,.fn,.body] none ∧
    ¬Target DirectedReadingDecompositionChecks.source [.fn,.fn,.body] none := by
  constructor
  · intro impossible;cases impossible
  · exact fun impossible=>impossible

#print axioms PrerequisiteChain.forward_target_available
#print axioms SelectedOldTurn.forward_other_last_near_source
#print axioms SelectedOldTurn.forward_other_last_far_target
#print axioms SelectedOldTurn.forward_original_other_last_available
#print axioms Overlap.endpoint_pair
#print axioms Overlap.terminal_no_after
#print axioms Overlap.actual_history
#print axioms BodyApp.endpoint_pair
#print axioms BodyApp.actual_history
#print axioms ArgApp.endpoint_pair
#print axioms ArgApp.actual_history
#print axioms ArgLambda.endpoint_pair
#print axioms ArgLambda.actual_history
#print axioms ArgOuterBinder.endpoint_pair
#print axioms ArgOuterBinder.actual_history
#print axioms BodyOuterBinder.endpoint_pair
#print axioms BodyOuterBinder.actual_history
#print axioms NonemptyOldPrefix.trace
#print axioms NonemptyOldPrefix.endpoint_pair
#print axioms NonemptyOldPrefix.same_initial_history
#print axioms BodyLambda.endpoint_pair
#print axioms BodyLambda.actual_history
#print axioms overlap_external_excluded
end Lamping.Checks.ForwardOtherLastEndpointsChecks

import Lamping.Lamping.ForwardFarChainComparison
import Lamping.Checks.ForwardExpandedFarOrigins

namespace Lamping.Checks.ForwardFarChainComparisonChecks
open Graph Lambda Lambda.Labelled AG
namespace Overlap
open ForwardExpandedFarOriginsChecks.Overlap

theorem selected (name : Path) (member : name∈F) : source.degreeAt name=some (.atom 5) := by
  have same:=List.mem_singleton.mp member
  subst name
  rfl

theorem sourceSafe : source.OuterBarsSafe (fun x=>x≠Label.atom 5) := by
  dsimp [source,original,WrappedSuccessfulChains.contractRoot,initLabels,initFrom,nodeCount,I,
    LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.rename,LTerm.lift,LTerm.label,
    Label.concat,Label.over,Label.under,Label.atom]
  simp only [LTerm.OuterBarsSafe,Label.OuterBarsSafe]
  decide

private theorem no_exception : ¬ForwardFarTerminalException event [.fn] [.fn] [[.fn,.fn]] [[.fn,.fn]] := by
  rintro ⟨cut,other,_⟩
  have inside : cut.edge∈([[.fn,.fn]] : List Path) := by
    exact Eq.mp (congrArg (fun xs : List Path => cut.edge∈xs) cut.split.symm)
      (List.mem_append_right _ List.mem_cons_self)
  have chosen:=List.mem_singleton.mp inside
  have atNode : target.subterm cut.edge=some (.lam (.atom 8) (.var (.atom 9) 0)) := by rw [chosen];rfl
  have same:=Option.some.inj (cut.lookup.symm.trans atNode)
  apply cut.marked
  rw [same]
  trivial

private theorem exact_position
    (out : ForwardExpandedFarOutput event [] [.fn] [] [.fn] [.fn,.fn,.body] [[.fn,.fn]]) :
    out.sourcePosition=[.fn,.arg] ∧out.sourceEdges=[[.fn,.arg,.fn]] := by
  have middleEq:=out.nodeOrigin.unique knownNodeOrigin
  have actualSource := (out.prefixTrace.unique (.nil source out.middlePosition)).trans middleEq
  have actualChain : PrerequisiteChain source [.fn,.arg] out.sourceEdges := by
    rw [←actualSource];exact out.sourceChain
  exact ⟨actualSource,actualChain.unique sourceTail⟩

/-- The exact source-FAR labels and iso come from the NEW high comparison,
not two availability witnesses. This overlap consumer is honestly self-paired. -/
theorem actual_complete_source_far :
    ∃left : ForwardExpandedFarOutput event [] [.fn] [] [.fn] [.fn,.fn,.body] [[.fn,.fn]],
      ∃right : ForwardExpandedFarOutput event [] [.fn] [] [.fn] [.fn,.fn,.body] [[.fn,.fn]],
        ForwardFarFullComparison sourceClosed left right ∧
        left.sourcePosition=[.fn,.arg] ∧right.sourcePosition=[.fn,.arg] ∧
        left.sourceEdges=[[.fn,.arg,.fn]] ∧right.sourceEdges=[[.fn,.arg,.fn]] := by
  obtain ⟨left,right,comparison⟩:=AG.SelectedOldTurn.forward_far_chain_comparison event initial prefixHistory sourceClosed selected sourceSafe
    origin origin reading reading
    (show target.subterm [.fn]=some (LTerm.contract (.atom 4) (.atom 5) body argument) from rfl)
    (show target.subterm [.fn]=some (LTerm.contract (.atom 4) (.atom 5) body argument) from rfl)
    remaining remaining (by decide) (by decide) (.refl _)
  have good : ForwardFarFullComparison sourceClosed left right := comparison.resolve_right no_exception
  obtain ⟨lp,le⟩:=exact_position left
  obtain ⟨rp,re⟩:=exact_position right
  exact ⟨left,right,good,lp,rp,le,re⟩

theorem legal_source_rep_images
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (selection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant sourceClosed selection) :
    ∃left : ForwardExpandedFarOutput event [] [.fn] [] [.fn] [.fn,.fn,.body] [[.fn,.fn]],
      ∃right : ForwardExpandedFarOutput event [] [.fn] [] [.fn] [.fn,.fn,.body] [[.fn,.fn]],
        SameChainRepresentation selection left.sourceChain right.sourceChain := by
  obtain ⟨left,right,comparison,_⟩:=actual_complete_source_far
  exact ⟨left,right,comparison.source_images selection representation⟩
end Overlap

namespace TwoCopies
abbrev I : Term := .lam (.var 0)
abbrev source : LTerm := initLabels
  (.app (.lam (.app (.app (.var 0) I) (.app (.var 0) I))) (.app I I))
abbrev body : LTerm := .app (.atom 2)
  (.app (.atom 3) (.var (.atom 4) 0) (.lam (.atom 5) (.var (.atom 6) 0)))
  (.app (.atom 7) (.var (.atom 8) 0) (.lam (.atom 9) (.var (.atom 10) 0)))
abbrev argument : LTerm := .app (.atom 11) (.lam (.atom 12) (.var (.atom 13) 0))
  (.lam (.atom 14) (.var (.atom 15) 0))
abbrev target : LTerm := LTerm.contract (.atom 0) (.atom 1) body argument
abbrev F : List Path := [[]]
abbrev markedBody : Marked := .app [] (.app [] (.var 0) (.lam (.var 0)))
  (.app [] (.var 0) (.lam (.var 0)))
abbrev markedArgument : Marked := .app [[.arg]] (.lam (.var 0)) (.lam (.var 0))
def event : SelectedOldTurn F source (.atom 1) [] source target [] where
  markedBefore := Marked.mark F source.erase
  markedAfter := Marked.contract markedBody markedArgument
  beforeOld := .nil _
  reduction := by
    change Marked.ReductionAt [] (.red [[]] markedBody markedArgument) (Marked.contract markedBody markedArgument)
    exact .redRoot _ _ _
  member := by decide
  labels := .nil _
  turn := .root _ _ _ _
  beta := .atom 0
  body := body
  argument := argument
  redex := rfl
theorem initial : INIT source := init_is_INIT _
theorem closed : Closed source.erase := by
  simp [Closed,Scoped,source,initLabels,initFrom,nodeCount,LTerm.erase]
theorem targetClosed : Closed target.erase := event.final_history.closed closed
theorem selected (name : Path) (member : name∈F) : source.degreeAt name=some (.atom 1) := by
  have same:=List.mem_singleton.mp member
  subst name
  rfl
def leftOrigin : BetaIncomingReadingOrigin body argument [] [.fn,.fn] [.fn]
    [.fn,.body,.fn] [.fn,.body,.fn,.fn] [.arg] := .copyFunction (parent:=[.fn]) rfl rfl rfl
def rightOrigin : BetaIncomingReadingOrigin body argument [] [.arg,.fn] [.arg]
    [.fn,.body,.arg] [.fn,.body,.arg,.fn] [.arg] := .copyFunction (parent:=[.arg]) rfl rfl rfl
def leftReading : PrerequisiteReadsDirected target [.fn] [.fn,.fn] true :=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
def rightReading : PrerequisiteReadsDirected target [.arg] [.arg,.fn] true :=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
def leftTail : PrerequisiteChain target [.fn,.fn] [[.fn,.fn,.fn]] := .redex_app (p:=[.fn,.fn]) rfl
def rightTail : PrerequisiteChain target [.arg,.fn] [[.arg,.fn,.fn]] := .redex_app (p:=[.arg,.fn]) rfl
def leftRemaining : PrerequisiteChain target [.fn] [[.fn,.fn],[.fn,.fn,.fn]] :=
  .app rfl (by intro a b bad;cases bad) leftTail
def rightRemaining : PrerequisiteChain target [.arg] [[.arg,.fn],[.arg,.fn,.fn]] :=
  .app rfl (by intro a b bad;cases bad) rightTail
def sourceTail : PrerequisiteChain source [.arg] [[.arg,.fn]] := .redex_app (p:=[.arg]) rfl

private theorem no_exception :
    ¬ForwardFarTerminalException event [.fn,.fn] [.arg,.fn] [[.fn,.fn,.fn]] [[.arg,.fn,.fn]] := by
  rintro ⟨cut,other,_⟩
  have inside : cut.edge∈([[.fn,.fn,.fn]] : List Path) :=
    Eq.mp (congrArg (fun xs : List Path => cut.edge∈xs) cut.split.symm)
      (List.mem_append_right _ List.mem_cons_self)
  have chosen:=List.mem_singleton.mp inside
  have atNode : target.subterm cut.edge=some (.lam (.atom 12) (.var (.atom 13) 0)) := by rw [chosen];rfl
  have same:=Option.some.inj (cut.lookup.symm.trans atNode)
  apply cut.marked
  rw [same]
  trivial

/-- Different CURRENT copied-function starts share the actual old argument.
The NEW high theorem, with no caller old traces/chains/iso, gives full labels. -/
theorem actual_two_distinct_starts :
    ∃left : ForwardExpandedFarOutput event [.fn] [.fn,.fn] [.fn,.body,.fn]
        [.fn,.body,.fn,.fn] [.arg] [[.fn,.fn,.fn]],
      ∃right : ForwardExpandedFarOutput event [.arg] [.arg,.fn] [.fn,.body,.arg]
        [.fn,.body,.arg,.fn] [.arg] [[.arg,.fn,.fn]],
        ForwardFarFullComparison closed left right ∧left.sourcePosition=[.arg] ∧right.sourcePosition=[.arg] ∧
        left.sourceEdges=[[.arg,.fn]] ∧right.sourceEdges=[[.arg,.fn]] ∧
        ([.fn,.fn] : Path)≠[.arg,.fn] := by
  have iso:=actual_chain_iso_of_labels event.final_history initial targetClosed leftTail rightTail rfl
  obtain ⟨left,right,comparison⟩:=AG.SelectedOldTurn.forward_far_chain_comparison event initial (.nil source) closed
    selected (initial.outerBarsSafe _) leftOrigin rightOrigin leftReading rightReading
    (show target.subterm [.fn,.fn]=some (argument.prepend ((Label.atom 4).concat (Label.atom 1).under)) from rfl)
    (show target.subterm [.arg,.fn]=some (argument.prepend ((Label.atom 8).concat (Label.atom 1).under)) from rfl)
    leftRemaining rightRemaining (by decide) (by decide) (Classical.choice iso)
  have knownLeft : BetaNodePreimage body argument [] [.fn,.fn] [.arg] := by
    simpa only [List.nil_append,List.append_nil] using
      (BetaNodePreimage.copied (body:=body) (argument:=argument) (site:=[]) (q:=[.fn,.fn]) (relative:=[]) (old:=argument) rfl rfl)
  have knownRight : BetaNodePreimage body argument [] [.arg,.fn] [.arg] := by
    simpa only [List.nil_append,List.append_nil] using
      (BetaNodePreimage.copied (body:=body) (argument:=argument) (site:=[]) (q:=[.arg,.fn]) (relative:=[]) (old:=argument) rfl rfl)
  have lp:=(left.prefixTrace.unique (.nil source left.middlePosition)).trans (left.nodeOrigin.unique knownLeft)
  have rp:=(right.prefixTrace.unique (.nil source right.middlePosition)).trans (right.nodeOrigin.unique knownRight)
  have lc : PrerequisiteChain source [.arg] left.sourceEdges :=
    Eq.mp (congrArg (fun p : Path => PrerequisiteChain source p left.sourceEdges) lp) left.sourceChain
  have rc : PrerequisiteChain source [.arg] right.sourceEdges :=
    Eq.mp (congrArg (fun p : Path => PrerequisiteChain source p right.sourceEdges) rp) right.sourceChain
  exact ⟨left,right,comparison.resolve_right no_exception,lp,rp,lc.unique sourceTail,rc.unique sourceTail,by decide⟩
end TwoCopies

#print axioms Overlap.actual_complete_source_far
#print axioms Overlap.legal_source_rep_images
#print axioms TwoCopies.actual_two_distinct_starts
end Lamping.Checks.ForwardFarChainComparisonChecks

import Lamping.Lamping.ExpandedArgumentHistoryOrigins
import Lamping.Checks.ExpandedLastEndpointChains
import Lamping.Checks.CanonicalAfterFarComparison
import Lamping.Checks.SingleUnsafeCopyFunctionAppInputs
set_option maxHeartbeats 4000000
namespace Lamping.Checks.ExpandedArgumentHistoryOriginsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence

private theorem one_schedule (schedule : [step]=(pre++[site])++suffix) :
    pre=[] ∧site=step ∧suffix=[] := by
  have lengths:=congrArg List.length schedule
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  have pe : pre=[] := List.length_eq_zero_iff.mp (by omega)
  have se : suffix=[] := List.length_eq_zero_iff.mp (by omega)
  rw [pe,se] at schedule
  simp only [List.nil_append,List.append_nil,List.singleton_inj] at schedule
  exact ⟨pe,schedule.symm,se⟩

private theorem empty_coordinates {source target : LTerm} {ps : List Path} {edge oldEdge : Path}
    {labels : History ps source target}
    (trace : BetaNodeHistoryPreimage labels edge oldEdge) (empty : ps=[]) : edge=oldEdge := by
  subst ps
  cases labels
  cases trace
  rfl

namespace Normal
open ForwardFarChainComparisonChecks.TwoCopies
open CanonicalAfterFarComparisonChecks.TwoCopies

/-- A real normal FUNCTION copy is linked through its GIVEN recent frame,
not by treating its source BODYvar as the argument ancestor. -/
theorem actual_normal_argument_ancestor : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 1) true leftCut.spine leftCut.lookup leaf snapshot,
    ∃canonical : CanonicalAfterFarOutput event.final_history leftCut snapshot,
    ∃recent : RecentSpineFrame g,∃compat : RecentFarCompatibility canonical recent,
    ∃low : ExpandedLastSelectedEndpoint recent.packet.middle recent.packet.site
      (recent.packet.frame.edges.getLastD []) true (some compat.expandedProper),
    ∃out : ExpandedLastOriginalEndpoints F source recent.packet.middle (.atom 1) recent.packet.event.labels
      (recent.packet.frame.edges.getLastD []) low.node true canonical.sourceProper compat.originalEdges,
      BetaNodeHistoryPreimage event.final_history leftCut.edge out.oldEdge ∧
      out.oldEdge=[.arg] ∧out.original.label=argument.label := by
  obtain ⟨leaf,snapshot,⟨g⟩⟩:=leftCut.spine.incidence_leaf_output closed leftCut.lookup
  obtain ⟨canonical,recent,⟨compat⟩⟩:=leftCut.recent_far_compatibility event.final_history closed (by decide) g
  obtain ⟨pre,site,suffix⟩:=one_schedule recent.schedule
  have head : leftCut.edge=recent.packet.edge:=empty_coordinates recent.uncreatedSuffix.to_node suffix
  have nonresult : recent.packet.edge≠recent.packet.site := by rw [←head,site];decide
  have argEnd := recent.packet.origin.expanded_argument_end_of_nonresult recent.packet.frame.expansion nonresult
  obtain ⟨low,⟨out⟩⟩:=compat.expanded_last_endpoints selected (initial.outerBarsSafe _)
  have trace := recent.expanded_argument_history_preimage event.final_history argEnd out
  have atArgument : out.oldEdge=[.arg] := by
    have pos:out.oldEdge=recent.packet.frame.edges.getLastD [] := (empty_coordinates out.nodeTrace pre).symm
    rw [pos,argEnd,site]
    rfl
  have lookup : source.subterm [.arg]=some out.original := atArgument ▸ out.lookup
  have nodeEq : out.original=argument := Option.some.inj (lookup.symm.trans (show source.subterm [.arg]=some argument from rfl))
  exact ⟨leaf,snapshot,g,canonical,recent,compat,low,out,trace,atArgument,congrArg LTerm.label nodeEq⟩
end Normal

private theorem zero_body_argument_end
    (shape : body=.var stamp 0)
    (expansion : CreatedReadingExpansion body site first last true edges directions) :
    edges.getLastD []=site++[.arg] := by
  cases expansion with
  | resultFunction other => exact False.elim (other stamp shape)
  | resultOverlap => rfl
  | copyFunction => rfl

namespace Overlap
open ForwardExpandedFarOriginsChecks.Overlap
open RecentSpineFarOriginsChecks.ForwardOverlap

/-- The var0 overlap's true expanded LAST is ARG. Its full-history
ancestor is distinct from the BODYvar triple-LAST coordinate. -/
theorem actual_var0_argument_ancestor : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 5) true cut.spine cut.lookup leaf snapshot,
    ∃canonical : CanonicalAfterFarOutput event.final_history cut snapshot,
    ∃recent : RecentSpineFrame g,∃compat : RecentFarCompatibility canonical recent,
    ∃low : ExpandedLastSelectedEndpoint recent.packet.middle recent.packet.site
      (recent.packet.frame.edges.getLastD []) true (some compat.expandedProper),
    ∃out : ExpandedLastOriginalEndpoints F source recent.packet.middle (.atom 5) recent.packet.event.labels
      (recent.packet.frame.edges.getLastD []) low.node true canonical.sourceProper compat.originalEdges,
      BetaNodeHistoryPreimage event.final_history cut.edge out.oldEdge ∧
      out.oldEdge=[.fn,.arg] ∧out.oldEdge≠[.fn,.fn,.body] := by
  obtain ⟨leaf,snapshot,g,canonical,recent,compat,pre,site,_suffix,middleEq,_rest⟩:=actual_true_var0_arg_far
  have atEvent : source.subterm [.fn]=some (.app recent.packet.event.beta
      (.lam (.atom 5) recent.packet.event.body) recent.packet.event.argument) :=
    Eq.mp (congrArg (fun pair : LTerm×Path=>pair.1.subterm pair.2=some (.app recent.packet.event.beta
      (.lam (.atom 5) recent.packet.event.body) recent.packet.event.argument))
      (show (recent.packet.middle,recent.packet.site)=
        (ForwardExpandedFarOriginsChecks.Overlap.source,([.fn] : Path)) from Prod.ext middleEq site)) recent.packet.event.redex
  have components:=LTerm.app.inj (Option.some.inj (atEvent.symm.trans event.redex))
  have bodyEq:recent.packet.event.body=body := (LTerm.lam.inj components.2.1).2
  have argEnd:=zero_body_argument_end bodyEq recent.packet.frame.expansion
  obtain ⟨low,⟨out⟩⟩:=compat.expanded_last_endpoints selected sourceSafe
  have trace:=recent.expanded_argument_history_preimage event.final_history argEnd out
  have atArgument : out.oldEdge=[.fn,.arg] := by
    have pos:out.oldEdge=recent.packet.frame.edges.getLastD [] := (empty_coordinates out.nodeTrace pre).symm
    rw [pos,argEnd,site]
    rfl
  exact ⟨leaf,snapshot,g,canonical,recent,compat,low,out,trace,atArgument,by rw [atArgument];decide⟩
end Overlap

namespace CrossPrefix
open SingleUnsafeCopyFunctionAppInputsChecks
abbrev earlyHead : Path := [.fn,.fn,.fn]
abbrev earlyStart : Path := [.fn,.fn,.arg]
abbrev earlyEdges : List Path := [earlyStart,earlyHead,earlyHead++[.fn]]
def earlyRemaining : PrerequisiteChain target [.fn,.fn] [earlyHead,earlyHead++[.fn]] :=
  .app rfl (by intro a b impossible;cases impossible) (.redex_app (p:=earlyHead) rfl)
def earlyChain : PrerequisiteChain target earlyStart earlyEdges :=
  .lam (parent:=[.fn,.fn]) (step:=.arg) rfl (by decide) earlyRemaining
theorem earlyLookup : target.subterm earlyHead=some copiedArgument := rfl
theorem copiedMarked : ¬copiedArgument.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  intro safe
  change (Label.atom 6≠Label.atom 6) ∧True at safe
  exact safe.1 rfl
private theorem earlySafe : ∀e∈([earlyStart] : List Path),degreeReadSafe (.atom 6) (target.labelAt e) := by
  intro e member label eq
  have pos:=List.mem_singleton.mp member
  subst e
  change some (Label.atom 14)=some label at eq
  have same:=Option.some.inj eq
  subst label
  trivial
private theorem lateSafe : ∀e∈([leftStart] : List Path),degreeReadSafe (.atom 6) (target.labelAt e) := by
  intro e member label eq
  have pos:=List.mem_singleton.mp member
  subst e
  change some (Label.atom 14)=some label at eq
  have same:=Option.some.inj eq
  subst label
  trivial
def earlySegment : PrerequisitePrefix target earlyStart [earlyStart] [.fn,.fn] :=
  .lam (parent:=[.fn,.fn]) (step:=.arg) rfl (by decide) .refl
def lateSegment : PrerequisitePrefix target leftStart [leftStart] [.arg,.fn] :=
  .lam (parent:=[.arg,.fn]) (step:=.arg) rfl (by decide) .refl
def earlyReading : PrerequisiteReadsDirected target [.fn,.fn] earlyHead true :=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
def lateReading : PrerequisiteReadsDirected target [.arg,.fn] leftHead true :=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
def earlySpine : DirectedMarkerSpine F source (.atom 6) true [[.fn],[.arg]] target [some (.atom 14)] earlyHead :=
  event.final_old.directed_marker_spine event.final_history selected sourceSafe earlySegment earlyReading earlyLookup copiedMarked (by
    intro e member node lookup
    exact earlySafe e member node.label (by simp only [LTerm.labelAt,lookup,Option.map_some]))
def lateSpine : DirectedMarkerSpine F source (.atom 6) true [[.fn],[.arg]] target [some (.atom 14)] leftHead :=
  event.final_old.directed_marker_spine event.final_history selected sourceSafe lateSegment lateReading leftLookup copiedMarked (by
    intro e member node lookup
    exact lateSafe e member node.label (by simp only [LTerm.labelAt,lookup,Option.map_some]))
def earlyCut : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) earlyStart earlyEdges where
  before:=[earlyStart]
  edge:=earlyHead
  after:=[earlyHead++[.fn]]
  reader:=[.fn,.fn]
  node:=copiedArgument
  forward:=true
  split:=rfl
  segment:=earlySegment
  remaining:=earlyRemaining
  reading:=earlyReading
  lookup:=earlyLookup
  safeBefore:=earlySafe
  marked:=copiedMarked
  spine:=earlySpine
  leaf:=earlySpine.leaf_output earlyLookup
def lateCut : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) leftStart es where
  before:=[leftStart]
  edge:=leftHead
  after:=[leftHead++[.fn]]
  reader:=[.arg,.fn]
  node:=copiedArgument
  forward:=true
  split:=rfl
  segment:=lateSegment
  remaining:=leftRemaining
  reading:=lateReading
  lookup:=leftLookup
  safeBefore:=lateSafe
  marked:=copiedMarked
  spine:=lateSpine
  leaf:=lateSpine.leaf_output leftLookup

theorem actual_equal_heads_and_parent_iso :
    earlyCut.edge≠lateCut.edge ∧earlyCut.node.label=lateCut.node.label ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed earlyEdges)
        (chainSyntaxIncidence target targetClosed es) := by
  exact ⟨by decide,rfl,actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial targetClosed earlyChain leftChain rfl⟩
end CrossPrefix

#print axioms Normal.actual_normal_argument_ancestor
#print axioms Overlap.actual_var0_argument_ancestor
#print axioms CrossPrefix.actual_equal_heads_and_parent_iso
end Lamping.Checks.ExpandedArgumentHistoryOriginsChecks

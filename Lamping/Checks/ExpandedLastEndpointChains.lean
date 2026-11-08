import Lamping.Lamping.ExpandedLastEndpointChains
import Lamping.Checks.RecentSpineFarOrigins
namespace Lamping.Checks.ExpandedLastEndpointChainsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence

private theorem prefix_nil_node_safe
    {source middle : LTerm} {labels : History ps source middle}
    (empty : ps=[]) (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (lookup : middle.subterm edge=some node) : node.label.OuterBarsSafe (fun x=>x≠degree) := by
  have nilLabels : History [] source middle := Eq.mp (congrArg (fun xs=>History xs source middle) empty) labels
  have middleEq:=nilLabels.deterministic (.nil source)
  rw [middleEq] at lookup
  exact (LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ (LTerm.label_mem_of_subterm lookup)

private theorem root_variable_expanded_last
    {source : LTerm}
    (redex : source.subterm site=some (.app beta (.lam alpha (.var stamp 0)) argument))
    (origin : BetaIncomingReadingOrigin (.var stamp 0) argument site edge reader oldReader first last)
    (expansion : CreatedReadingExpansion (.var stamp 0) site first last false es ds) : es.getLastD []=site := by
  cases expansion with
  | resultLambda => rfl
  | copyOverlap => rfl
  | @copyLambda q nonroot =>
    obtain ⟨old,atOld⟩:=origin.old_prerequisite redex |>.2
    rw [List.append_assoc,LTerm.subterm_append,redex] at atOld
    cases q with
    | nil => exact False.elim (nonroot rfl)
    | cons child rest => cases child <;> simp [LTerm.subterm] at atOld

namespace EmptyCopy
open UniformOldCreatedIncomingLabelsChecks.Distinct
open ActualSpineAfterAlignmentChecks.EmptyCopy

theorem actual_older_q0_two_original_endpoints : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 7) false cut.spine cut.lookup leaf snapshot,
    ∃canonical : CanonicalAfterFarOutput labels cut snapshot,
    ∃recent : RecentSpineFrame g,∃compat : RecentFarCompatibility canonical recent,
    ∃low : ExpandedLastSelectedEndpoint recent.packet.middle recent.packet.site
      (recent.packet.frame.edges.getLastD []) false (some compat.expandedProper),
    ∃out : ExpandedLastOriginalEndpoints F source recent.packet.middle (.atom 7) recent.packet.event.labels
      (recent.packet.frame.edges.getLastD []) low.node false canonical.sourceProper compat.originalEdges,
      recent.packet.pre=[left] ∧recent.packet.site=right ∧
      compat.sourcePosition=[.arg] ∧compat.originalEdges=[[.arg],[.fn]] ∧
      SelectedOriginalSingleton F source (.atom 7) out.toVertex out.targetEdges ∧
      recent.packet.frame.edges.getLastD []=right ∧
      low.node.label.OuterBarsSafe (fun x=>x≠Label.atom 7) ∧
      out.fromVertex.val=[.arg] ∧out.sourceEdges=[[.arg],[.fn]] := by
  obtain ⟨leaf,snapshot,g,canonical,recent,compat,pre,site,_,_,_,midEq,_,pos,es,_,_⟩:=
    RecentSpineFarOriginsChecks.EmptyCopy.actual_latest_q0_source_chain
  obtain ⟨low,⟨out⟩⟩:=compat.expanded_last_endpoints selected source_safe
  have eventAt : middle.subterm right=some (.app recent.packet.event.beta (.lam (.atom 7) recent.packet.event.body) recent.packet.event.argument) :=
    Eq.mp (congrArg (fun pair : LTerm×Path=>pair.1.subterm pair.2=some
      (.app recent.packet.event.beta (.lam (.atom 7) recent.packet.event.body) recent.packet.event.argument))
      (show (recent.packet.middle,recent.packet.site)=(middle,right) from Prod.ext midEq site)) recent.packet.event.redex
  have known : middle.subterm right=some (.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) oldArgument):=rfl
  have shape:=Option.some.inj (eventAt.symm.trans known)
  injection shape with _ fnEq _
  injection fnEq with _ bodyEq
  have origin:=recent.packet.origin
  rw [bodyEq] at origin
  have expansion : CreatedReadingExpansion (.var (.atom 8) 0) recent.packet.site recent.packet.first recent.packet.last false
      recent.packet.frame.edges recent.packet.frame.directions :=
    Eq.mp (congrArg (fun b=>CreatedReadingExpansion b recent.packet.site recent.packet.first recent.packet.last false
      recent.packet.frame.edges recent.packet.frame.directions) bodyEq) recent.packet.frame.expansion
  have realRedex:=recent.packet.event.redex
  rw [bodyEq] at realRedex
  have last:=root_variable_expanded_last realRedex origin expansion
  have atLow : middle.subterm right=some low.node :=
    Eq.mp (congrArg (fun pair : LTerm×Path=>pair.1.subterm pair.2=some low.node)
      (show (recent.packet.middle,recent.packet.frame.edges.getLastD [])=(middle,right) from Prod.ext midEq (last.trans site))) low.lookup
  have nodeEq:=Option.some.inj (atLow.symm.trans known)
  have safe : low.node.label.OuterBarsSafe (fun x=>x≠Label.atom 7) := by rw [nodeEq];trivial
  have actual:=out.sourceClass.resolve_right (fun h=>h.1 safe)
  have position:=compat.sourceCoordinate.symm.trans pos
  exact ⟨leaf,snapshot,g,canonical,recent,compat,low,out,pre,site,pos,es,out.targetClass,
    last.trans site,safe,(congrArg Subtype.val actual.2.1).trans position,actual.2.2.trans es⟩
end EmptyCopy

namespace ForwardOverlap
open ForwardExpandedFarOriginsChecks.Overlap
open ForwardFarChainComparisonChecks.Overlap
open RecentSpineFarOriginsChecks.ForwardOverlap

theorem actual_var0_ARG_two_original_endpoints : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 5) true cut.spine cut.lookup leaf snapshot,
    ∃canonical : CanonicalAfterFarOutput event.final_history cut snapshot,
    ∃recent : RecentSpineFrame g,∃compat : RecentFarCompatibility canonical recent,
    ∃low : ExpandedLastSelectedEndpoint recent.packet.middle recent.packet.site
      (recent.packet.frame.edges.getLastD []) true (some compat.expandedProper),
    ∃out : ExpandedLastOriginalEndpoints F source recent.packet.middle (.atom 5) recent.packet.event.labels
      (recent.packet.frame.edges.getLastD []) low.node true canonical.sourceProper compat.originalEdges,
      recent.packet.pre=[] ∧recent.packet.site=[.fn] ∧compat.sourcePosition=[.fn,.arg] ∧
      compat.originalEdges=[[.fn,.arg,.fn]] ∧
      SelectedOriginalSingleton F source (.atom 5) out.fromVertex out.sourceEdges ∧
      out.toVertex=canonical.sourceProper ∧out.targetEdges=[[.fn,.arg,.fn]] := by
  obtain ⟨leaf,snapshot,g,canonical,recent,compat,pre,site,_,_,_,_,pos,_,es,_,_⟩:=actual_true_var0_arg_far
  obtain ⟨low,⟨out⟩⟩:=compat.expanded_last_endpoints RecentSpineFarOriginsChecks.ForwardOverlap.selected RecentSpineFarOriginsChecks.ForwardOverlap.sourceSafe
  exact ⟨leaf,snapshot,g,canonical,recent,compat,low,out,pre,site,pos,es,out.sourceClass,
    out.targetClass.1,out.targetClass.2.trans es⟩
end ForwardOverlap

namespace Inherited
open PairedCurrentChainSourceLabelsChecks.NoninitialDistinct
open ActualSpineAfterAlignmentChecks.Inherited

theorem actual_inherited_BODYAPP_two_original_endpoints : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 6) false cut.spine cut.lookup leaf snapshot,
    ∃canonical : CanonicalAfterFarOutput labels cut snapshot,
    ∃recent : RecentSpineFrame g,∃compat : RecentFarCompatibility canonical recent,
    ∃low : ExpandedLastSelectedEndpoint recent.packet.middle recent.packet.site
      (recent.packet.frame.edges.getLastD []) false (some compat.expandedProper),
    ∃out : ExpandedLastOriginalEndpoints F source recent.packet.middle (.atom 6) recent.packet.event.labels
      (recent.packet.frame.edges.getLastD []) low.node false canonical.sourceProper compat.originalEdges,
      recent.packet.pre=[] ∧recent.suffixSites=[[.arg]] ∧
      compat.sourcePosition=[.fn,.fn,.body] ∧compat.originalEdges=[[.fn,.fn,.body,.fn]] ∧
      SelectedOriginalSingleton F source (.atom 6) out.toVertex out.targetEdges ∧
      low.node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) ∧
      out.fromVertex.val=[.fn,.fn,.body] ∧out.sourceEdges=[[.fn,.fn,.body,.fn]] := by
  obtain ⟨leaf,snapshot,g,canonical,recent,compat,pre,_,suffix,_,_,pos,_,es,_,_⟩:=
    RecentSpineFarOriginsChecks.Inherited.actual_inherited_suffix_body_app
  obtain ⟨low,⟨out⟩⟩:=compat.expanded_last_endpoints selected sourceSafe
  have safe:=prefix_nil_node_safe (labels:=recent.packet.event.labels) pre sourceSafe low.lookup
  have actual:=out.sourceClass.resolve_right (fun h=>h.1 safe)
  have fromEq:=actual.2.1
  have position:=compat.sourceCoordinate.symm.trans pos
  exact ⟨leaf,snapshot,g,canonical,recent,compat,low,out,pre,suffix,pos,es,out.targetClass,safe,
    (congrArg Subtype.val fromEq).trans position,actual.2.2.trans es⟩
end Inherited

namespace MarkedLowOnly
open DirectedMarkerSpineIncidenceChecks.Nested

theorem actual_forward_marked_terminal_selected : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) true forwardSpine
      (by rfl : targetForward.subterm [.fn]=some UniformOldNodeLabelSuffixChecks.target) leaf snapshot,
    ∃recent : RecentSpineFrame g,
    ∃low : ExpandedLastSelectedEndpoint recent.packet.middle recent.packet.site
      (recent.packet.frame.edges.getLastD []) true recent.packet.frame.oldFar,
      recent.packet.pre=[[.fn]] ∧recent.suffixSites=[] ∧leaf.continuation≠[] ∧
      EndpointChain recent.packet.middle (some low.near) [recent.packet.site++[.fn]] := by
  obtain ⟨leaf,snapshot,g,recent,pre,_,suffix,continuation⟩:=
    RecentSpineFarOriginsChecks.MarkedLowOnly.forward_stops_at_recent_marked
  obtain ⟨low⟩:=recent.packet.origin.expanded_last_selected_endpoint recent.packet.event.redex
    recent.packet.frame.expansion recent.packet.frame.finalIncidence
  exact ⟨leaf,snapshot,g,recent,low,pre,suffix,continuation,low.singleton⟩

theorem actual_reverse_marked_terminal_selected : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) false reverseSpine
      (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
    ∃recent : RecentSpineFrame g,
    ∃low : ExpandedLastSelectedEndpoint recent.packet.middle recent.packet.site
      (recent.packet.frame.edges.getLastD []) false recent.packet.frame.oldFar,
      recent.packet.pre=[[.fn,.arg]] ∧recent.suffixSites=[] ∧leaf.continuation≠[] ∧
      EndpointChain recent.packet.middle (some low.near) [recent.packet.site++[.fn]] := by
  obtain ⟨leaf,snapshot,g,recent,pre,_,suffix,continuation⟩:=
    RecentSpineFarOriginsChecks.MarkedLowOnly.reverse_stops_at_recent_marked
  obtain ⟨low⟩:=recent.packet.origin.expanded_last_selected_endpoint recent.packet.event.redex
    recent.packet.frame.expansion recent.packet.frame.finalIncidence
  exact ⟨leaf,snapshot,g,recent,low,pre,suffix,continuation,low.singleton⟩
end MarkedLowOnly

#print axioms Lambda.Labelled.BetaIncomingReadingOrigin.expanded_last_selected_endpoint
#print axioms RecentFarCompatibility.expanded_last_endpoints
#print axioms EmptyCopy.actual_older_q0_two_original_endpoints
#print axioms ForwardOverlap.actual_var0_ARG_two_original_endpoints
#print axioms Inherited.actual_inherited_BODYAPP_two_original_endpoints
#print axioms MarkedLowOnly.actual_forward_marked_terminal_selected
#print axioms MarkedLowOnly.actual_reverse_marked_terminal_selected
end Lamping.Checks.ExpandedLastEndpointChainsChecks

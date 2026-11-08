import Lamping.Lambda.DirectedMarkerLeafTails
import Lamping.Lambda.UniformOldChainPreimages
import Lamping.Lambda.ResidualFunctionPreimages
namespace Lamping.Lambda.Labelled

/-- THIS safe leaf FIRST and its selected FUNCTION edge form a real complete
source chain. The reader is reflected separately from the incoming FIRST. -/
theorem DirectedMarkerLeafOutput.source_first_two_chain
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree)) :
    ∃name reader first firstNode functionBody,
      name∈F ∧source.subterm first=some firstNode ∧firstNode.label=leaf.firstNode.label ∧
      source.subterm (name++[.fn])=some (.lam degree functionBody) ∧
      BetaNodeHistoryPreimage leaf.event.labels leaf.first first ∧
      BetaNodeHistoryPreimage leaf.event.labels leaf.oldReader reader ∧
      BetaNodeHistoryPreimage leaf.event.labels (leaf.site++[.fn]) (name++[.fn]) ∧
      PrerequisiteChain source reader [first,name++[.fn]] := by
  obtain ⟨name,chosen,oldRedex,appTrace,functionTrace⟩:=
    leaf.event.beforeOld.selected_app_function_preimages leaf.event.labels leaf.event.member
  obtain ⟨beta,functionBody,argument,atOriginal⟩:=LTerm.degreeAt_redex (selected name chosen)
  have atFunction : source.subterm (name++[.fn])=some (.lam degree functionBody) := by
    rw [LTerm.subterm_append,atOriginal];rfl
  have degreeSafe := (LTerm.outerBarsSafe_iff _ _).mp sourceSafe degree (LTerm.label_mem_of_subterm atFunction)
  have eventChain:PrerequisiteChain leaf.middle leaf.oldReader [leaf.first,leaf.site++[.fn]] :=
    (leaf.origin.old_prerequisite leaf.event.redex).1
  have allSafe (edge : Path) (member : edge∈[leaf.first,leaf.site++[.fn]]) (node : LTerm)
      (lookup : leaf.middle.subterm edge=some node) : node.label.OuterBarsSafe (fun x=>x≠degree) := by
    rcases List.mem_cons.mp member with rfl | other
    · have same:=Option.some.inj (lookup.symm.trans leaf.firstLookup);subst node;exact leaf.firstSafe
    · have same:=List.mem_singleton.mp other;subst edge
      have atLambda : leaf.middle.subterm (leaf.site++[.fn])=some (.lam degree leaf.event.body) := by
        rw [LTerm.subterm_append,leaf.event.redex];rfl
      have same:=Option.some.inj (lookup.symm.trans atLambda);subst node;exact degreeSafe
  obtain ⟨reader,oldEdges,chain,startTrace,edgeTraces,labelsEq,lengthEq⟩:=
    leaf.event.beforeOld.marker_free_chain_preimages (DegreeAligned.initial source F)
      leaf.event.labels selected eventChain allSafe
  cases edgeTraces with
  | cons firstTrace rest =>
    cases rest with
    | cons lastTrace rest =>
      cases rest
      have finalEq:=lastTrace.unique functionTrace
      subst_vars
      obtain ⟨position,node,atNode,trace,sameLabel⟩:=leaf.original_first_label selected
      have firstEq:=trace.unique firstTrace
      subst position
      exact ⟨name,reader,_,node,functionBody,chosen,atNode,sameLabel,atFunction,firstTrace,startTrace,functionTrace,chain⟩

/-- Equal full directed words give equal complete two-edge READ label lists
in THIS original SOURCE. No chain isomorphism or physical comparison is an input. -/
theorem DirectedMarkerLeafOutput.compare_source_first_two_chains
    (left : DirectedMarkerLeafOutput F source degree forward leftPs leftWord)
    (right : DirectedMarkerLeafOutput F source degree forward rightPs rightWord)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree)) (same : leftWord=rightWord) :
    ∃leftName rightName leftReader rightReader leftFirst rightFirst leftNode rightNode,
      leftName∈F ∧rightName∈F ∧source.subterm leftFirst=some leftNode ∧source.subterm rightFirst=some rightNode ∧
      BetaNodeHistoryPreimage left.event.labels left.first leftFirst ∧
      BetaNodeHistoryPreimage right.event.labels right.first rightFirst ∧
      BetaNodeHistoryPreimage left.event.labels (left.site++[.fn]) (leftName++[.fn]) ∧
      BetaNodeHistoryPreimage right.event.labels (right.site++[.fn]) (rightName++[.fn]) ∧
      PrerequisiteChain source leftReader [leftFirst,leftName++[.fn]] ∧
      PrerequisiteChain source rightReader [rightFirst,rightName++[.fn]] ∧
      leftNode.label=rightNode.label ∧
      [leftFirst,leftName++[.fn]].map source.labelAt=[rightFirst,rightName++[.fn]].map source.labelAt := by
  obtain ⟨ln,lr,lf,lo,lb,lc,lat,llab,lfn,ltrace,lstart,lfunction,lchain⟩:=left.source_first_two_chain selected sourceSafe
  obtain ⟨rn,rr,rf,ro,rb,rc,rat,rlab,rfn,rtrace,rstart,rfunction,rchain⟩:=right.source_first_two_chain selected sourceSafe
  obtain ⟨_,_,_,_,firstEq,_,_⟩:=left.compare_full_tails right same
  have oldFirstEq:lo.label=ro.label:=llab.trans (firstEq.trans rlab.symm)
  refine ⟨ln,rn,lr,rr,lf,rf,lo,ro,lc,rc,lat,rat,ltrace,rtrace,lfunction,rfunction,lchain,rchain,oldFirstEq,?_⟩
  simp only [List.map_cons,List.map_nil,LTerm.labelAt,lat,rat,lfn,rfn,Option.map_some]
  change [some lo.label,some degree]=[some ro.label,some degree]
  rw [oldFirstEq]
end Lamping.Lambda.Labelled

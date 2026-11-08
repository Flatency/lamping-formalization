import Lamping.Lamping.PairedMarkerPrefixComparison

namespace Lamping.Lambda.Labelled

private theorem copy_marker (site parent : Path) (degree : Label) :
    originMarker site ((site++[.fn,.body])++(parent++[.fn])) degree=.under degree := by
  have a : (site++[.fn,.body])++(parent++[.fn])≠site := by
    intro eq
    have sizes := congrArg List.length eq
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega
  have b : (site++[.fn,.body])++(parent++[.fn])≠site++[.fn,.body] := by
    intro eq
    have sizes := congrArg List.length eq
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega
  exact if_neg (by rintro (h|h);exact a h;exact b h)

/-- Actual TRUE origins give the complete local head, including the full
contractum in the RESULTvar0 overlap. This is an output classification. -/
theorem BetaIncomingReadingOrigin.forward_complete_head
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge true)
    (lookup : target.subterm edge=some current)
    (firstLookup : source.subterm first=some firstNode) (degree : Label) :
    (originMarker site first degree=.over degree ∧current=LTerm.contract beta alpha body argument) ∨
    (originMarker site first degree=.under degree ∧
      current.label=firstNode.label.concat (alpha.under.concat argument.label)) := by
  cases origin with
  | resultFunction result function =>
    exact Or.inl ⟨by simp [originMarker],
      Option.some.inj (lookup.symm.trans (result ▸ step.contract_lookup redex))⟩
  | @copyFunction parent occurs copy read =>
    have localLookup : (LTerm.contract beta alpha body argument).subterm (parent++[.fn])=some current := by
      rw [copy,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    obtain ⟨stamp,oldLookup,labelEq⟩ := LTerm.contract_argument_incoming_label occurs localLookup
    have nonroot : parent++[.fn]≠[] := by simp
    rw [if_neg nonroot] at labelEq
    have actualFirst : source.subterm ((site++[.fn,.body])++(parent++[.fn]))=
        some (.var stamp (binderDepth (parent++[.fn]))) := by
      rw [List.append_assoc,LTerm.subterm_append,redex]
      simpa only [LTerm.subterm,Option.bind_some] using oldLookup
    have firstEq := Option.some.inj (firstLookup.symm.trans actualFirst)
    exact Or.inr ⟨copy_marker site parent degree,by rw [firstEq];exact labelEq⟩
  | resultLambda result read oldLambda =>
    have same : edge=edge++[.fn] := by simpa only [read,←result] using reading.2
    have sizes := congrArg List.length same
    simp at sizes
  | copyLambda occurs copy read oldLambda =>
    have same : edge=edge++[.fn] := by simpa only [read] using reading.2
    have sizes := congrArg List.length same
    simp at sizes

end Lamping.Lambda.Labelled

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- SAME actual event, TRUE reading: compare complete local heads, without
canceling any unknown continuation or assuming a LAST/target REP equality. -/
theorem paired_marker_same_event_forward_evaluations
    (left : DirectedMarkerLeafOutput F source degree true ps leftWord)
    (right : DirectedMarkerLeafOutput F source degree true ps rightWord)
    (leftPaired : PairedMarkerEventGeometry left (initLabels source.erase) localTarget)
    (rightPaired : PairedMarkerEventGeometry right (initLabels source.erase) localTarget)
    (samePre : left.pre=right.pre) (sameSite : left.site=right.site)
    (matching : Matches g root source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (prefixHistory : History prior original source) (initial : INIT original)
    (closed : Closed source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (physical : BetaEdge g) (sameWord : leftWord=rightWord) :
    selection.evalLabel physical leftPaired.current.label=
      selection.evalLabel physical rightPaired.current.label := by
  have rightPrefix : History left.pre (initLabels source.erase) rightPaired.middle := by
    rw [samePre]
    exact rightPaired.prefixLabels
  have sameMiddle := leftPaired.prefixLabels.deterministic rightPrefix
  have redexRight : leftPaired.middle.subterm left.site=
      some (.app rightPaired.beta (.lam rightPaired.alpha rightPaired.body) rightPaired.argument) := by
    rw [sameMiddle,sameSite]
    exact rightPaired.redex
  have components := LTerm.app.inj (Option.some.inj (leftPaired.redex.symm.trans redexRight))
  have betas := components.1
  have functions := LTerm.lam.inj components.2.1
  have arguments := components.2.2
  have first := paired_marker_first_evaluations left right leftPaired rightPaired matching selected sourceSafe
    prefixHistory initial closed sourceSelection representation selection physical sameWord
  obtain ⟨_lt,_rt,_lk,_rk,_firstGlobal,marker,_tails⟩ := left.compare_full_tails right sameWord
  have kinds := (global_leaf_marker_kind left).symm.trans (marker.trans (global_leaf_marker_kind right))
  have lhead := leftPaired.origin.forward_complete_head leftPaired.turn leftPaired.redex leftPaired.reading
    leftPaired.lookup leftPaired.firstLookup degree
  have rhead := rightPaired.origin.forward_complete_head rightPaired.turn rightPaired.redex rightPaired.reading
    rightPaired.lookup rightPaired.firstLookup degree
  rcases lhead with ⟨lk,le⟩|⟨lk,le⟩ <;> rcases rhead with ⟨rk,re⟩|⟨rk,re⟩
  · rw [le,re,betas,functions.1,functions.2,arguments]
  · rw [lk,rk] at kinds
    cases kinds
  · rw [lk,rk] at kinds
    cases kinds
  · simp only [le,re,selection.evalLabel_concat,first,functions.1,arguments]
end

#print axioms BetaIncomingReadingOrigin.forward_complete_head
#print axioms paired_marker_same_event_forward_evaluations
end Lamping.AG

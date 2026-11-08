import Lamping.Lamping.BetaOriginalWordTransport
import Lamping.Checks.Paths

namespace Lamping.Checks.BetaOriginalWordTransportChecks
open AG Graph Lambda Lambda.Labelled
private abbrev site := actualBetaSite
private abbrev edge := Paths.encodedBetaOccurrence
private abbrev fragmentCut := cutFragment site.net (pathPartition (.beta 0) Unit) site.closed
private abbrev rhs := (Schema.beta 0).right.net
private abbrev P : EdgeWord := [⟨7,false⟩,⟨11,true⟩]
private def tip : Endpoint site.net := .inl ⟨.inr (.inl ()),.inl ()⟩
private def mate : Endpoint site.net := .inr (.inr (.inr (),false))
private noncomputable def weights (e : Endpoint site.net) : EdgeWord := by
  classical
  exact if e=tip then P else if e=mate then EdgeWord.reverse P else []

private theorem source_reverse : OriginalWordReversal (g:=site.net) weights := by
  intro e
  have different : tip≠mate := by intro same; cases same
  by_cases first : e=tip
  · subst e
    change weights mate=EdgeWord.reverse (weights tip)
    simp [weights,different.symm]
  · by_cases second : e=mate
    · subst e
      have back : site.net.wire mate=tip := rfl
      rw [back]
      simp [weights,different.symm]
    · have notTip : site.net.wire e≠tip := by
        intro same
        apply second
        have back := congrArg site.net.wire.mate same
        exact (Pairing.involutive _ e).symm.trans back
      have notMate : site.net.wire e≠mate := by
        intro same
        apply first
        have back := congrArg site.net.wire.mate same
        exact (Pairing.involutive _ e).symm.trans (back.trans (Pairing.involutive _ tip))
      simp only [weights,if_neg first,if_neg second,if_neg notTip,if_neg notMate,EdgeWord.reverse]
      rfl

private theorem principal_word : physicalOriginalWord weights edge.principal=P := by
  change weights tip++(weights (.inr (.inr (.inr (),true)))++[])=P
  have otherTip : (.inr (.inr (.inr (),true)) : Endpoint site.net)≠tip := by
    intro same;cases same
  have otherMate : (.inr (.inr (.inr (),true)) : Endpoint site.net)≠mate := by
    intro same;cases same
  simp only [weights,if_neg otherTip,if_neg otherMate,List.append_nil,ite_true]

private def rootOutside : Endpoint fragmentCut := .inr (.inl (.inl (.inl ())))
private def bodyOutside : Endpoint fragmentCut := .inr (.inl (.inr (.inr true)))
private def argumentOutside : Endpoint fragmentCut := .inr (.inl (.inr (.inl true)))
private def bindingOutside : Endpoint fragmentCut :=
  fragmentCut.wire (.inr (.inl (.inr (.inr false))))
private def contextRaw : List (PlugSegment fragmentCut rhs) :=
  [.inl rootOutside,.inr (.inr (.inl (.inl false))),.inl bodyOutside]
private def contextOld : List (Endpoint site.net) :=
  site.outsideEnd rootOutside::(edge.principal++[site.outsideEnd bodyOutside])
private def bindingRaw : List (PlugSegment fragmentCut rhs) :=
  [.inl bindingOutside,.inr (.inr (.inl (.inr false))),.inl argumentOutside]
private def bindingOld : List (Endpoint site.net) :=
  site.outsideEnd bindingOutside::(edge.reverseRoute++[site.outsideEnd argumentOutside])

private theorem root_zero : weights (site.outsideEnd rootOutside)=[] := by
  change weights (.inr (.inl (.inl ())))=[]
  simp [weights,tip,mate]
private theorem body_zero : weights (site.outsideEnd bodyOutside)=[] := by
  change weights (.inl ⟨.inr (.inr ()),.inr true⟩)=[]
  simp [weights,tip,mate]
private theorem argument_zero : weights (site.outsideEnd argumentOutside)=[] := by
  change weights (.inl ⟨.inr (.inl ()),.inr true⟩)=[]
  simp [weights,tip,mate]
private theorem binding_zero : weights (site.outsideEnd bindingOutside)=[] := by
  let frontier : Endpoint fragmentCut := .inr (.inl (.inr (.inr false)))
  have zero : weights (site.outsideEnd frontier)=[] := by
    change weights (.inl ⟨.inr (.inr ()),.inr false⟩)=[]
    simp [weights,tip,mate]
  calc
    weights (site.outsideEnd bindingOutside)=weights (site.net.wire (site.outsideEnd frontier)) :=
      congrArg weights (site.outsideEnd_wire frontier).symm
    _=EdgeWord.reverse (weights (site.outsideEnd frontier)) := source_reverse _
    _=[] := by rw [zero];rfl

/-- A real encoded I I context reconnection with a nonzero two-letter
principal word. Both raw and actual target transports are consumed. -/
theorem actual_context_nonzero :
    BetaPathResidual site edge contextRaw contextOld ∧
    OriginalWordReversal (g:=site.reduce) (site.betaOriginalWordWeights edge weights) ∧
    physicalOriginalWord weights edge.principal=P ∧
    physicalOriginalWord weights contextOld=P ∧
    contextRaw.flatMap (Sum.elim (fun e => weights (site.outsideEnd e))
      (betaRhsOriginalWord 0 (physicalOriginalWord weights edge.principal)))=P ∧
    physicalOriginalWord (site.betaOriginalWordWeights edge weights)
      (contextRaw.map (plugEnd fragmentCut.label rhs.label))=P ∧P≠[] := by
  have actual : BetaPathResidual site edge contextRaw contextOld := .context rfl (.single bodyOutside)
  have raw := actual.original_word_transport site weights source_reverse
  have relation : BetaPathResidual site edge
      ((contextRaw.map (plugEnd fragmentCut.label rhs.label)).map
        (plugEnd fragmentCut.label rhs.label).invFun) contextOld := by
    simpa only [List.map_map,Function.comp_def,(plugEnd fragmentCut.label rhs.label).left_inv,
      List.map_id_fun'] using actual
  have target := relation.original_word_transport_actual site weights source_reverse
  have old : physicalOriginalWord weights contextOld=P := by
    simpa only [contextOld,physicalOriginalWord,List.flatMap_cons,List.flatMap_append,
      List.flatMap_nil,root_zero,body_zero,List.nil_append,List.append_nil] using principal_word
  exact ⟨actual,site.beta_original_word_reversal edge weights source_reverse,principal_word,
    old,raw.trans old,target.trans old,by decide⟩

/-- The actual binding reconnection reverses BOTH order and atom direction;
the exiting ARG frontier is retained rather than counted twice. -/
theorem actual_binding_nonzero :
    BetaPathResidual site edge bindingRaw bindingOld ∧
    OriginalWordReversal (g:=site.reduce) (site.betaOriginalWordWeights edge weights) ∧
    physicalOriginalWord weights edge.reverseRoute=[⟨11,false⟩,⟨7,true⟩] ∧
    physicalOriginalWord weights bindingOld=EdgeWord.reverse P ∧
    bindingRaw.flatMap (Sum.elim (fun e => weights (site.outsideEnd e))
      (betaRhsOriginalWord 0 (physicalOriginalWord weights edge.principal)))=EdgeWord.reverse P ∧
    physicalOriginalWord (site.betaOriginalWordWeights edge weights)
      (bindingRaw.map (plugEnd fragmentCut.label rhs.label))=EdgeWord.reverse P ∧
    EdgeWord.reverse P≠[] := by
  have actual : BetaPathResidual site edge bindingRaw bindingOld :=
    .binding (Pairing.involutive _ _) (.single argumentOutside)
  have raw := actual.original_word_transport site weights source_reverse
  have relation : BetaPathResidual site edge
      ((bindingRaw.map (plugEnd fragmentCut.label rhs.label)).map
        (plugEnd fragmentCut.label rhs.label).invFun) bindingOld := by
    simpa only [List.map_map,Function.comp_def,(plugEnd fragmentCut.label rhs.label).left_inv,
      List.map_id_fun'] using actual
  have target := relation.original_word_transport_actual site weights source_reverse
  have reverse := physicalOriginalWord_reverse weights source_reverse edge.principal
  have reverseExact : physicalOriginalWord weights edge.reverseRoute=[⟨11,false⟩,⟨7,true⟩] := by
    change physicalOriginalWord weights (reverseEdges edge.principal)=_
    rw [reverse,principal_word]
    rfl
  have old : physicalOriginalWord weights bindingOld=EdgeWord.reverse P := by
    simpa only [bindingOld,physicalOriginalWord,List.flatMap_cons,List.flatMap_append,
      List.flatMap_nil,binding_zero,argument_zero,List.nil_append,List.append_nil] using reverseExact
  exact ⟨actual,site.beta_original_word_reversal edge weights source_reverse,reverseExact,
    old,raw.trans old,target.trans old,by decide⟩

#print axioms actual_context_nonzero
#print axioms actual_binding_nonzero
end Lamping.Checks.BetaOriginalWordTransportChecks

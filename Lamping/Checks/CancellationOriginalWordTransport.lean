import Lamping.Lamping.CancellationOriginalWordTransport
import Lamping.Checks.FamilyRepresentation

namespace Lamping.Checks.CancellationOriginalWordTransportChecks
open AG Graph Lambda Lambda.Labelled
private abbrev site := CancellationPrefixFixture.geometrySite
private abbrev principal := CancellationPrefixFixture.geometryPrincipal
private abbrev cut := cutFragment site.net (pathPartition (.fanCancel 1) Empty) site.closed
private abbrev rhs := (Schema.fanCancel 1).right.net
private def A : EdgeWord := [⟨13,false⟩]
private def P : EdgeWord := [⟨7,false⟩,⟨11,true⟩]
private def B : EdgeWord := [⟨17,true⟩]

private def weights : Endpoint site.net → EdgeWord
  | .inl ⟨.inl _,.inl _⟩ => EdgeWord.reverse B
  | .inl ⟨.inl _,.inr _⟩ => []
  | .inl ⟨.inr (.inl _),.inl _⟩ => P
  | .inl ⟨.inr (.inr _),.inl _⟩ => EdgeWord.reverse P
  | .inl ⟨.inr (.inl _),.inr false⟩ => EdgeWord.reverse A
  | .inl ⟨.inr (.inl _),.inr true⟩ => []
  | .inl ⟨.inr (.inr _),.inr false⟩ => B
  | .inl ⟨.inr (.inr _),.inr true⟩ => []
  | .inr (.inl (.inl false)) => A
  | .inr (.inl (.inl true)) => []
  | .inr (.inl (.inr _)) => []
  | .inr (.inr ⟨.inl e,_⟩) => nomatch e
  | .inr (.inr ⟨.inr e,_⟩) => nomatch e

private theorem reversal : OriginalWordReversal weights := by
  rintro (⟨node,p⟩|((b|u)|⟨e|e,d⟩))
  · rcases node with u|(u|u)
    all_goals cases u; cases p with
      | inl u => cases u; rfl
      | inr b => cases b <;> rfl
  · cases b <;> rfl
  · cases u; rfl
  · exact nomatch e
  · exact nomatch e

private def entering (f : (Schema.fanCancel 1).Frontier) : Endpoint cut :=
  cut.wire (.inr (.inl (.inr f)))
private def leaving (f : (Schema.fanCancel 1).Frontier) : Endpoint cut :=
  .inr (.inl (.inr (wireBoundaryMate rhs f)))
private def raw (f : (Schema.fanCancel 1).Frontier) : List (PlugSegment cut rhs) :=
  [.inl (entering f),.inr (.inr (.inl f)),.inl (leaving f)]
private def target (f : (Schema.fanCancel 1).Frontier) : List (Endpoint site.reduce) :=
  (raw f).map (plugEnd cut.label rhs.label)
private def old (f : (Schema.fanCancel 1).Frontier) : List (Endpoint site.net) :=
  site.cancellation_canonical_fronts principal.edges f++[site.outsideEnd (leaving f)]

private theorem residual (f : (Schema.fanCancel 1).Frontier) :
    CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges)
      (target f) (old f) := by
  have head : (site.cancellation_canonical_fronts principal.edges f++
      [site.outsideEnd (leaving f)]).head?=some (site.outsideEnd (entering f)) := by
    rw [cancellation_fronts_literal]
    rfl
  have relation : CanonicalWireResidual cut rhs site.net site.outsideEnd
      (site.cancellation_canonical_fronts principal.edges) (raw f) (old f) :=
    .through head (.single (leaving f))
  change CanonicalWireResidual cut rhs site.net site.outsideEnd
    (site.cancellation_canonical_fronts principal.edges)
    (((raw f).map (plugEnd cut.label rhs.label)).map (plugEnd cut.label rhs.label).invFun) (old f)
  simpa only [List.map_map,Function.comp_def,Bij.left_inv,List.map_id_fun] using relation

theorem actual_nonzero_principal_and_inherited_ends :
    physicalOriginalWord weights principal.edges=[⟨7,false⟩,⟨11,true⟩] ∧
    weights (site.outsideEnd (entering (.inl false)))=[⟨13,false⟩] ∧
    weights (site.outsideEnd (leaving (.inl false)))=[⟨17,true⟩] := by
  exact ⟨rfl,rfl,rfl⟩

theorem actual_forward_residual_fold :
    CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges)
      (target (.inl false)) (old (.inl false)) ∧
    ((target (.inl false)).map (plugEnd cut.label rhs.label).invFun).flatMap
      (Sum.elim (fun outside => weights (site.outsideEnd outside))
        (cancellationRhsOriginalWord (.fanCancel 1) (physicalOriginalWord weights principal.edges)))=
        A++P++B ∧
    physicalOriginalWord (site.cancellationOriginalWordWeights principal weights) (target (.inl false))=
        A++P++B := by
  have rawFold := (residual (.inl false)).original_word_transport site (.fan 1) principal weights reversal
  have actualFold := (residual (.inl false)).original_word_transport_actual site (.fan 1) principal weights reversal
  exact ⟨residual _,rawFold,actualFold⟩

theorem actual_reverse_residual_fold :
    CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges)
      (target (.inr false)) (old (.inr false)) ∧
    ((target (.inr false)).map (plugEnd cut.label rhs.label).invFun).flatMap
      (Sum.elim (fun outside => weights (site.outsideEnd outside))
        (cancellationRhsOriginalWord (.fanCancel 1) (physicalOriginalWord weights principal.edges)))=
        EdgeWord.reverse B++EdgeWord.reverse P++EdgeWord.reverse A ∧
    physicalOriginalWord (site.cancellationOriginalWordWeights principal weights) (target (.inr false))=
        EdgeWord.reverse B++EdgeWord.reverse P++EdgeWord.reverse A := by
  have rawFold := (residual (.inr false)).original_word_transport site (.fan 1) principal weights reversal
  have actualFold := (residual (.inr false)).original_word_transport_actual site (.fan 1) principal weights reversal
  exact ⟨residual _,rawFold,actualFold⟩

theorem actual_target_wire_reversal :
    OriginalWordReversal (g:=site.reduce) (site.cancellationOriginalWordWeights principal weights) :=
  site.cancellation_original_word_reversal (.fan 1) principal weights reversal

#print axioms actual_nonzero_principal_and_inherited_ends
#print axioms actual_forward_residual_fold
#print axioms actual_reverse_residual_fold
#print axioms actual_target_wire_reversal
end Lamping.Checks.CancellationOriginalWordTransportChecks

import Lamping.Lamping.NonemptyBetaAuxiliary
import Lamping.Checks.MarkedAuxiliaryPhysicalFixture
import Lamping.Checks.SafeBetaAuxiliaryTransport

namespace Lamping.Checks.NonemptyBetaAuxiliaryChecks
open Graph Lambda Lambda.Labelled AG
namespace Marked
open MarkedAuxiliaryPhysicalFixture

theorem direct_total_aux
    (sourceSelection : OccurrenceFragmentSelection original concrete.site.net (.inl ()))
    (targetSelection : OccurrenceFragmentSelection current concrete.site.reduce (.inl ()))
    (sourceJoint : JointRepresentation closed sourceSelection) :
    AuxiliarySeparation currentClosed targetSelection := by
  obtain ⟨flow⟩:=source_flow
  obtain ⟨balance⟩:=source_indexed_balance
  exact concrete.site.beta_nonempty_auxiliary_preserve initial (.nil _) (.nil _) (.nil _) closed
    source_matching source_inputs flow source_positive balance source_root_depth source_transparency
    relative normal history sourceSelection targetSelection sourceJoint
    (by rw [exact_fiber];simp)

/-- Real original-INIT SOURCEJoint and actual nonempty TARGET selectors,
now with the NEW entire Aux predicate, not merely the old selfpair Eq. -/
theorem actual_total_aux :
    ∃sourceSelection : OccurrenceFragmentSelection original concrete.site.net (.inl ()),
      ∃targetSelection : OccurrenceFragmentSelection current concrete.site.reduce (.inl ()),
        JointRepresentation closed sourceSelection ∧AuxiliarySeparation currentClosed targetSelection := by
  obtain ⟨sourceSelection,joint⟩:=source_joint
  obtain ⟨targetSelection⟩:=target_matches.occurrence_fragment_selection currentClosed
  exact ⟨sourceSelection,targetSelection,joint,direct_total_aux sourceSelection targetSelection joint⟩
end Marked

namespace SafeArgument
open SafeBetaAuxiliaryTransportChecks.MarkedArgument

theorem direct_total_aux
    (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()))
    (sourceSelection : OccurrenceFragmentSelection original presentation.site.net (.inl ()))
    (targetSelection : OccurrenceFragmentSelection current presentation.site.reduce (.inl ()))
    (sourceJoint : JointRepresentation closed sourceSelection) :
    AuxiliarySeparation currentClosed targetSelection := by
  have matching:=presentation.sourceIso.matches (encode_closed_matches term closed 0)
  have inputs:=presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs
  obtain ⟨oldFlow⟩:=encode_flowBalance term 0
  obtain ⟨oldBalance⟩:=encode_indexed_balance term 0
  have nonempty : presentation.site.betaSyntaxFiber (.inl ()) original.erase≠[] := by
    have same : presentation.site.betaSyntaxFiber (.inl ()) original.erase=[[]] := by
      simpa only [original,erase_initLabels] using fiber presentation
    rw [same];simp
  exact presentation.site.beta_nonempty_auxiliary_preserve initial (.nil _) (.nil _) (.nil _) closed
    matching inputs (presentation.sourceIso.flowBalance oldFlow) rfl
    (presentation.sourceIso.indexed_balance oldBalance) rfl
    (presentation.sourceIso.transparency (encode_closed_transparency term closed 0))
    (relative presentation) (by simp [Marked.Normal]) history sourceSelection targetSelection sourceJoint nonempty

/-- This is a DIFFERENT actual INIT/site/history: safe ARG-variable incoming
whose endpoint chain reads a marked lambda. No READ-wide safety is assumed. -/
theorem actual_total_aux :
    ∃presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()),
      ∃sourceSelection : OccurrenceFragmentSelection original presentation.site.net (.inl ()),
        ∃targetSelection : OccurrenceFragmentSelection current presentation.site.reduce (.inl ()),
          JointRepresentation closed sourceSelection ∧AuxiliarySeparation currentClosed targetSelection := by
  obtain ⟨presentation⟩:=presentation_exists
  have originalMatches:=encode_closed_matches term closed 0
  have matching:=presentation.sourceIso.matches originalMatches
  obtain ⟨originalSelection,initialJoint⟩:=encode_initial_joint_realization original closed initial 0
  obtain ⟨sourceSelection⟩:=matching.occurrence_fragment_selection closed
  have joint:=(presentation.sourceIso.joint_representation originalMatches closed originalSelection sourceSelection).mpr initialJoint
  obtain ⟨targetSelection⟩:=(actual_target_matches presentation).occurrence_fragment_selection currentClosed
  exact ⟨presentation,sourceSelection,targetSelection,joint,
    direct_total_aux presentation sourceSelection targetSelection joint⟩
end SafeArgument

#print axioms Marked.direct_total_aux
#print axioms Marked.actual_total_aux
#print axioms SafeArgument.direct_total_aux
#print axioms SafeArgument.actual_total_aux
#print axioms SafeBetaAuxiliaryTransportChecks.MarkedArgument.incoming_safe
#print axioms SafeBetaAuxiliaryTransportChecks.MarkedArgument.parent_read_marked
end Lamping.Checks.NonemptyBetaAuxiliaryChecks

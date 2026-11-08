import Lamping.Lamping.EmptyBetaAuxiliary
import Lamping.Checks.Phase5Review.EmptyBetaInput

namespace Lamping.Checks.EmptyBetaAuxiliaryChecks
open Graph Lambda Lambda.Labelled AG
open Phase5Review.EmptyBetaInput

abbrev original : LTerm := initLabels (.lam (.var 0))

theorem closed : Closed original.erase := by
  change Closed (Term.lam (.var 0))
  change 0<1
  decide

theorem matching : Matches site.net () original.erase := by
  simpa only [original,erase_initLabels] using source_matches

theorem target_matching : Matches site.reduce () original.erase := by
  simpa only [original,erase_initLabels] using actual_empty_beta_matches

theorem relative : Marked.RelativeHistory []
    (Marked.mark (site.betaSyntaxFiber () original.erase) original.erase)
    (.lam (.var 0)) := by
  have same : site.betaSyntaxFiber () original.erase=[] := by
    simpa only [original,erase_initLabels] using fiber_empty
  rw [same]
  exact .nil _

/-- Real empty-fiber site, with an explicit SOURCEJoint premise.
This does not assert INIT reachability or a successful Aux-positive pair. -/
theorem direct_conditional_aux
    (sourceSelection : OccurrenceFragmentSelection original site.net ())
    (targetSelection : OccurrenceFragmentSelection original site.reduce ())
    (sourceJoint : JointRepresentation closed sourceSelection) :
    AuxiliarySeparation closed targetSelection := by
  exact site.beta_empty_auxiliary_preserve closed matching source_inputs flow rfl balance rfl
    source_transparency relative (by trivial) (.nil original)
    sourceSelection targetSelection sourceJoint
    (by simpa only [original,erase_initLabels] using fiber_empty)

/-- Both actual selector domains are inhabited; no SOURCEJoint truth is claimed. -/
theorem actual_selectors :
    Nonempty (OccurrenceFragmentSelection original site.net ()) ∧
    Nonempty (OccurrenceFragmentSelection original site.reduce ()) :=
  ⟨matching.occurrence_fragment_selection closed,target_matching.occurrence_fragment_selection closed⟩

/-- The actual nonroot BODY fragment is aligned to the same local INIT atom,
then retained as a literal residual by the SAME zero-history producer.
No successful endpoint is asserted for this identity normal form. -/
theorem actual_body_residual
    (sourceFragment : OccurrenceFragment original site.net () [.body])
    (targetFragment : OccurrenceFragment original site.reduce () [.body]) :
    ∃ physical : BetaEdge site.net, SiteBetaGeometry site physical ∧
      BetaPathResidual site physical
        (targetFragment.fragment.segments.map (plugEnd _ _).invFun)
        sourceFragment.fragment.segments := by
  obtain ⟨localTarget,localHistory,_erase,_targetMatching,physical,selection,geometry,all⟩ :=
    site.beta_evaluated_child_residuals closed matching source_inputs flow rfl balance rfl
      source_transparency relative (by trivial) (.nil original)
  cases localHistory
  have ctx : targetFragment.context=.lamBody (.atom 0) := by
    have occurrence : SourceSubterm [] .external original [.body] [.atom 0]
        (.lamBody (.atom 0)) (.var (.atom 1) 0) := .body .nil
    exact (targetFragment.occurrence.same_occurrence occurrence).2.1
  obtain ⟨localNode,atLocal,_sameErase,_nonempty,residual⟩ :=
    all [] .body original rfl targetFragment
      (by rw [InteriorSourceBlock.source_edge_departure,ctx]; exact .body)
  obtain ⟨env,ctx,occurrence⟩ :=
    SourceSubterm.of_lookup (initLabels original.erase) atLocal [] .external
  have localMatching : Matches site.net () (initLabels original.erase).erase := by
    simpa only [erase_initLabels] using matching
  have evaluation := selection.evalLabel_occurrence_segments (init_is_INIT original.erase)
    localMatching matching occurrence sourceFragment physical
  rw [evaluation] at residual
  exact ⟨physical,geometry,residual⟩

#print axioms closed
#print axioms matching
#print axioms target_matching
#print axioms relative
#print axioms direct_conditional_aux
#print axioms actual_selectors
#print axioms actual_body_residual
#print axioms Phase5Review.EmptyBetaInput.actual_beta_step
#print axioms Lamping.AG.PathSite.beta_empty_auxiliary_preserve
end Lamping.Checks.EmptyBetaAuxiliaryChecks

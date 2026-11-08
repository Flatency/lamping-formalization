import Lamping.Lambda.SelectedFunctionOuterExclusion
import Lamping.Checks.SelectedFunctionSurvival
import Lamping.Lamping.ForwardFarChainComparison

namespace Lamping.Checks.SelectedFunctionOuterExclusionChecks
open Lambda Lambda.Labelled

namespace Complete
open NodeLabelSuffixOriginsChecks
open SelectedFunctionSurvivalChecks.Complete

theorem selected_atom_absent : Letter.atom 4∉currentArgument.label.letters :=
  old.normal_no_selected_function_outer_atom actualHistory initial normal (by decide)
    redex_lookup actual_lookup

/-- Absence is OUTER membership only; the consumed lambda still labels bars. -/
theorem selected_payload_really_present :
    Letter.over (Label.atom 4)∈currentArgument.label.letters ∧
    Letter.under (Label.atom 4)∈currentArgument.label.letters := by decide

theorem source_prefix_atoms_remain :
    Letter.atom 3∈currentArgument.label.letters ∧Letter.atom 5∈currentArgument.label.letters := by decide

theorem unselected_atom_still_outer :
    target.subterm [.fn]=some (.lam (.atom 1) (.var (.atom 2) 0)) ∧
    Letter.atom 1∈(Label.atom 1).letters ∧ ([]:Path)∉F := ⟨rfl,by decide,by decide⟩

theorem selected_atom_present_before :
    source.subterm [.arg,.fn]=some (.lam (.atom 4) (.var (.atom 5) 0)) ∧
    Letter.atom 4∈(Label.atom 4).letters := ⟨rfl,by decide⟩
end Complete

namespace CompoundBasis
open SingleUnsafeCopyFunctionAppInputsChecks
abbrev basis : LTerm := initLabels source.erase

theorem actual_complete : Marked.Normal SingleUnsafeCopyFunctionAppInputsChecks.markedTarget := by
  change ((((True ∧ True) ∧ True) ∧ True) ∧ ((True ∧ True) ∧ True) ∧ True) ∧
    (((True ∧ True) ∧ True) ∧ True) ∧ ((True ∧ True) ∧ True) ∧ True
  decide

/-- A real compound SOURCE after its original INIT prefix keeps the SAME
selection F and schedule. The conclusion concerns only the local label. -/
theorem actual_local_annotation_caller :
    INIT original ∧ ¬INIT source ∧
    History [[.arg,.fn,.body],[]] original source ∧
    ∃localTarget stamp n body argument,
      History [[.fn],[.arg]] basis localTarget ∧
      localTarget.erase=target.erase ∧
      basis.subterm [.arg]=some (.app stamp (.lam (.atom n) body) argument) ∧
      Letter.atom n∉localTarget.label.letters := by
  have globalLabels := event.final_history
  obtain ⟨localTarget,localLabels,erased⟩ :=
    lift_history globalLabels.betaHistory basis (erase_initLabels source.erase)
  have actualBasis : ∃stamp n body argument,
      basis.subterm [.arg]=some (.app stamp (.lam (.atom n) body) argument) := ⟨_,_,_,_,rfl⟩
  obtain ⟨stamp,n,body,argument,atBasis⟩ := actualBasis
  have localOld : Marked.RelativeOldHistory F [[.fn],[.arg]]
      (Marked.mark F basis.erase) markedTarget := by
    simpa only [basis,erase_initLabels] using event.final_old
  have absent := localOld.normal_no_selected_function_outer_atom localLabels
    (init_is_INIT source.erase) actual_complete (by decide) atBasis
      (show localTarget.subterm []=some localTarget by cases localTarget <;> rfl)
  exact ⟨initial,sourceNotInit,prefixHistory,localTarget,stamp,n,body,argument,
    localLabels,erased,atBasis,absent⟩
end CompoundBasis

#print axioms Complete.selected_atom_absent
#print axioms Complete.selected_payload_really_present
#print axioms Complete.source_prefix_atoms_remain
#print axioms Complete.unselected_atom_still_outer
#print axioms Complete.selected_atom_present_before
#print axioms CompoundBasis.actual_complete
#print axioms CompoundBasis.actual_local_annotation_caller
end Lamping.Checks.SelectedFunctionOuterExclusionChecks

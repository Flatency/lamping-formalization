import Lamping.Lamping.LocalSourceFragmentEvaluation
import Lamping.Lamping.BetaEncodingIso
import Lamping.Lamping.InitialMatching
namespace Lamping.Checks.LocalSourceFragmentEvaluation
open AG Graph Lambda Lambda.Labelled
private abbrev original := initLabels identityApp
private def compound : Labelled.Label := (Labelled.Label.atom 9).concat (Labelled.Label.atom 10).over
private def current : LTerm := .app (.atom 9)
  (.lam (.atom 9) (.var (.atom 9) 0)) (.lam compound (.var compound 0))
private theorem actualMatching : Matches actualBetaSite.net (.inl ()) identityApp :=
  betaEncodingIso.matches (encode_closed_matches identityApp
    ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ 0)
private def rootPosition : Position current.erase := ⟨[],rfl⟩
private def argumentPosition : Position current.erase := ⟨[.arg],rfl⟩
private def variablePosition : Position current.erase := ⟨[.arg,.body],rfl⟩
private def rootOccurrence : SourceSubterm [] .external original [] [] .external original := .nil
private def argumentOccurrence : SourceSubterm [] .external original [.arg] [] (.appArg (.atom 0))
    (.lam (.atom 3) (.var (.atom 4) 0)) := .arg .nil
private def variableOccurrence : SourceSubterm [] .external original [.arg,.body] [.atom 3] (.lamBody (.atom 3))
    (.var (.atom 4) 0) := .arg (.body .nil)
private def localTarget : LTerm := LTerm.contract (.atom 0) (.atom 1)
  (.var (.atom 2) 0) (.lam (.atom 3) (.var (.atom 4) 0))
private def localTurn : StepAt [] (initLabels current.erase) localTarget := .root _ _ _ _
private def globalTurn : StepAt [] current
    (LTerm.contract (.atom 9) (.atom 9) (.var (.atom 9) 0) (.lam compound (.var compound 0))) :=
  .root _ _ _ _
private def copiedVariableOrigin : BetaNodePreimage (.var (.atom 9) 0) (.lam compound (.var compound 0))
    [] [.body] [.arg,.body] := .copied (q:=[]) (relative:=[.body]) rfl rfl
private abbrev globalTarget := LTerm.contract (.atom 9) (.atom 9)
  (.var (.atom 9) 0) (.lam compound (.var compound 0))
private def globalLabels : History [[]] current globalTarget := .cons globalTurn (.nil _)
private def localLabels : History [[]] (initLabels current.erase) localTarget := .cons localTurn (.nil _)
private def whole : ParallelStep [[]] current.erase globalTarget.erase := by
  refine ⟨[[]],.lam (.var 0),(Marked.completeOld_iff _ _).mpr ⟨?_,True.intro⟩,rfl⟩
  change Marked.RelativeHistory [[]] (.red [[]] (.var 0) (.lam (.var 0))) (.lam (.var 0))
  exact .cons (.root _ _ _) (.nil _)

theorem global_argument_annotation_is_not_local_atom (n : Nat) : compound≠Labelled.Label.atom n := by
  intro impossible
  cases impossible

/-- Arbitrary actual local source-edge choices and arbitrary global
occurrence choices agree at the root, lambda and variable. The global
argument annotations are compound, while the evaluator uses atoms 3/4. -/
theorem actual_local_atoms_global_fragments
    (localSelection : SourceEdgeSelection original actualBetaSite.net (.inl ()))
    (globalSelection : OccurrenceFragmentSelection current actualBetaSite.net (.inl ())) :
    localSelection.atomWord 0=(globalSelection rootPosition).fragment.segments ∧
    localSelection.atomWord 3=(globalSelection argumentPosition).fragment.segments ∧
    localSelection.atomWord 4=(globalSelection variablePosition).fragment.segments := by
  have initial := init_is_INIT identityApp
  exact ⟨localSelection.atomWord_occurrence_segments (current:=current) initial actualMatching actualMatching rootOccurrence rfl _,
    localSelection.atomWord_occurrence_segments (current:=current) initial actualMatching actualMatching argumentOccurrence rfl _,
    localSelection.atomWord_occurrence_segments (current:=current) initial actualMatching actualMatching variableOccurrence rfl _⟩

/-- No atom-index oracle is supplied to the label-evaluator version. Its
input is the actual old variable occurrence, not the global compound label. -/
theorem actual_local_label_evaluation
    (localSelection : SourceEdgeSelection original actualBetaSite.net (.inl ()))
    (globalSelection : OccurrenceFragmentSelection current actualBetaSite.net (.inl ()))
    (beta : BetaEdge actualBetaSite.net) :
    localSelection.evalLabel beta (Labelled.Label.atom 4)=
      (globalSelection variablePosition).fragment.segments :=
  localSelection.evalLabel_occurrence_segments (current:=current) (init_is_INIT identityApp) actualMatching actualMatching
    variableOccurrence (globalSelection variablePosition) beta

/-- The CURRENT local reduct's copied variable label is internally traced
through the SAME real beta preimage to the global ARG-body fragment. The
caller supplies neither a local old label nor its equality with the target. -/
theorem actual_copied_current_label_evaluation
    (localSelection : SourceEdgeSelection original actualBetaSite.net (.inl ()))
    (globalSelection : OccurrenceFragmentSelection current actualBetaSite.net (.inl ()))
    (physical : BetaEdge actualBetaSite.net) :
    localSelection.evalLabel physical (LTerm.var (Labelled.Label.atom 4) 0).label=
      (globalSelection variablePosition).fragment.segments :=
  localSelection.uncreated_local_evaluation (source:=current) actualMatching localTurn rfl
    copiedVariableOrigin (by decide) rfl (globalSelection variablePosition) physical

/-- The copied argument ROOT, unlike the strict copied variable above,
has a genuinely created incoming edge and a compound local current label. -/
theorem actual_copy_root_boundary :
    StepAt [] current (LTerm.contract (.atom 9) (.atom 9) (.var (.atom 9) 0) (.lam compound (.var compound 0))) ∧
    BetaCreatedIncoming (.var (.atom 9) 0) [] [] ∧
    (∀ n,localTarget.label≠Labelled.Label.atom n) := by
  refine ⟨globalTurn,Or.inl rfl,?_⟩
  intro n impossible
  cases impossible

/-- The actual complete OLD root fiber returns its real history-preimage
trace. Its uniqueness locks the old ARG-body coordinate before choosing the
arbitrary global selector's fragment. The global label is already compound. -/
theorem actual_whole_old_evaluation
    (localSelection : SourceEdgeSelection original actualBetaSite.net (.inl ()))
    (globalSelection : OccurrenceFragmentSelection current actualBetaSite.net (.inl ()))
    (physical : BetaEdge actualBetaSite.net) :
    localSelection.evalLabel physical (LTerm.var (Labelled.Label.atom 4) 0).label=
      (globalSelection variablePosition).fragment.segments := by
  have selected (path : Path) (member : path∈([[]] : List Path)) :
      current.degreeAt path=some (Labelled.Label.atom 9) := by
    have equal := List.mem_singleton.mp member
    subst path;rfl
  have safe : compound.OuterBarsSafe (fun payload=>payload≠Labelled.Label.atom 9) := by
    change Labelled.Label.atom 10≠Labelled.Label.atom 9
    decide
  obtain ⟨oldPosition,oldNode,_oldLookup,trace,evaluation⟩ :=
    localSelection.marker_free_local_evaluation (source:=current) (edge:=[.body]) actualMatching whole.complete.1
      (DegreeAligned.initial current [[]]) globalLabels localLabels selected
      (current:=.var compound 0) (localCurrent:=.var (.atom 4) 0) rfl rfl safe physical
  have known : BetaNodeHistoryPreimage globalLabels [.body] [.arg,.body] :=
    .one (step:=globalTurn) rfl copiedVariableOrigin (.nil globalTarget [.body])
  have equal := trace.unique known
  subst oldPosition
  exact evaluation (globalSelection variablePosition)

#print axioms SourceEdgeSelection.atomWord_occurrence_segments
#print axioms SourceEdgeSelection.evalLabel_occurrence_segments
#print axioms global_argument_annotation_is_not_local_atom
#print axioms actual_local_atoms_global_fragments
#print axioms actual_local_label_evaluation
#print axioms SourceEdgeSelection.uncreated_local_evaluation
#print axioms actual_copied_current_label_evaluation
#print axioms actual_copy_root_boundary
#print axioms SourceEdgeSelection.marker_free_local_evaluation
#print axioms actual_whole_old_evaluation
end Lamping.Checks.LocalSourceFragmentEvaluation

import Lamping.Lambda.NodeLabelSuffixOrigins
import Lamping.Checks.WrappedSuccessfulChains
namespace Lamping.Checks.NodeLabelSuffixOriginsChecks
open Lambda Lambda.Labelled
abbrev I : Term := WrappedSuccessfulChains.I
abbrev bare : Term := .app I (.app I (.app I I))
abbrev source : LTerm := initLabels bare
abbrev target : LTerm := match source with
  | .app stamp fn arg => .app stamp fn (WrappedSuccessfulChains.contractRoot arg)
  | t => t
abbrev argumentTerm : LTerm := .app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0))
  (.lam (.atom 9) (.var (.atom 10) 0))
abbrev currentArgument : LTerm := LTerm.contract (.atom 3) (.atom 4) (.var (.atom 5) 0) argumentTerm
def actualStep : StepAt [.arg] source target := .arg (.root _ _ _ _)
def actualHistory : History [[.arg]] source target := .cons actualStep (.nil _)
theorem initial : INIT source := init_is_INIT _
theorem closed : Closed source.erase := by
  change (0<1) ∧(0<1 ∧(0<1 ∧0<1))
  decide
theorem actual_lookup : target.subterm [.arg]=some currentArgument := rfl
theorem redex_lookup : source.subterm [.arg]=some
    (.app (.atom 3) (.lam (.atom 4) (.var (.atom 5) 0)) argumentTerm) := rfl
def actualOrigin : BetaNodePreimage (.var (.atom 5) 0) argumentTerm [.arg] [.arg] [.arg,.arg] :=
  .copied (q:=[]) (relative:=[]) rfl rfl

theorem actual_marked : ¬currentArgument.label.OuterBarsSafe (fun x=>x≠Label.atom 4) :=
  actualStep.created_label_not_safe redex_lookup actual_lookup (Or.inl rfl)
theorem actual_auxiliary : AuxiliaryAt target [.arg] := by
  constructor
  · rintro ⟨parent,stamp,fn,arg,split,atParent⟩
    have last := congrArg List.getLast? split
    simp at last
  · rintro ⟨stamp,body,lookup⟩
    rw [actual_lookup] at lookup
    cases lookup
-- This marked ARG APP has two genuinely available proper endpoint chains,
-- unlike an external-root auxiliary edge.
def actual_source_endpoint_chain : PrerequisiteChain target [] [[.fn]] := .redex_app rfl
def actual_target_endpoint_chain : PrerequisiteChain target [.arg] [[.arg,.fn]] := .redex_app rfl

theorem actual_overlap_word : currentArgument.label.letters=
    [.atom 3,.over (.atom 4),.atom 5,.under (.atom 4),.atom 6] := rfl

theorem actual_safe_suffix : ∃pre marker,marker.MarksDegree (.atom 4) ∧
    currentArgument.label.letters=pre++marker::(Label.atom 6).letters ∧
    currentArgument.label.readLetters false=(Label.atom 6).readLetters false++marker::pre.reverse := by
  obtain ⟨old,pre,marker,atOld,safe,marks,equation,reversed⟩ :=
    actualStep.beta_node_last_marker redex_lookup actualOrigin actual_lookup
      (initial.outerBarsSafe _) actual_marked
  have same : old=argumentTerm := Option.some.inj atOld.symm
  subst old
  exact ⟨pre,marker,marks,equation,reversed⟩

-- Both new separators exist, but the COMPLETE original node label is the
-- suffix after UNDER; OVER's immediate suffix still contains another marker.
theorem actual_last_is_under : ∃pre,
    currentArgument.label.letters=pre++(.under (.atom 4))::(Label.atom 6).letters ∧
    pre.reverse=[.atom 5,.over (.atom 4),.atom 3] := by
  obtain ⟨pre,marker,marks,equation,reversed⟩ := actual_safe_suffix
  have literalReverse : currentArgument.label.readLetters false=
      (Label.atom 6).readLetters false++(.under (.atom 4))::[.atom 5,.over (.atom 4),.atom 3] := rfl
  obtain ⟨_,sameMarker,sameTail⟩ := Label.readLetters_first_marker_unique
    (before:=.atom 6) (otherBefore:=.atom 6) (forward:=false)
    (degree:=.atom 4) (by trivial) (by trivial) marks (Or.inr rfl)
    (reversed.symm.trans literalReverse)
  subst marker
  exact ⟨pre,equation,sameTail⟩

theorem actual_reverse_core : ∃old,source.subterm [.arg,.arg]=some old ∧
    (currentArgument.label=old.label ∨∃marker post,marker.MarksDegree (.atom 4) ∧
      currentArgument.label.readLetters false=old.label.readLetters false++marker::post) :=
  actualStep.beta_node_label_suffix_reverse redex_lookup actualOrigin actual_lookup

-- The constructor origin is old ARG APP6, not the event's BODY variable5.
theorem overlap_other_last_is_different :
    source.subterm [.arg,.fn,.body]=some (.var (.atom 5) 0) ∧
    source.subterm [.arg,.arg]=some argumentTerm ∧argumentTerm.label≠(.atom 5) :=
  ⟨rfl,rfl,by decide⟩

abbrev retainedSource : LTerm := initLabels (.app (.lam (.lam (.var 0))) I)
abbrev retainedTarget : LTerm := WrappedSuccessfulChains.contractRoot retainedSource
def retainedStep : StepAt [] retainedSource retainedTarget := .root _ _ _ _
def retainedOrigin : BetaNodePreimage (.lam (.atom 2) (.var (.atom 3) 0))
    (.lam (.atom 4) (.var (.atom 5) 0)) [] [] [.fn,.body] :=
  .retained (relative:=[]) rfl (by intro stamp wrong;cases wrong)
theorem actual_retained_over : ∃old,retainedSource.subterm [.fn,.body]=some old ∧
    (retainedTarget.label=old.label ∨∃pre marker,marker.MarksDegree (.atom 1) ∧
      retainedTarget.label.letters=pre++marker::old.label.letters) :=
  retainedStep.beta_node_label_suffix (by rfl) retainedOrigin rfl

#print axioms initial
#print axioms actual_auxiliary
#print axioms actual_source_endpoint_chain
#print axioms actual_target_endpoint_chain
#print axioms actual_safe_suffix
#print axioms actual_last_is_under
#print axioms actual_reverse_core
#print axioms overlap_other_last_is_different
#print axioms actual_retained_over
end Lamping.Checks.NodeLabelSuffixOriginsChecks

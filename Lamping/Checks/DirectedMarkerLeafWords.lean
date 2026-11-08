import Lamping.Lambda.DirectedMarkerLeafWords
import Lamping.Checks.SelectedOldOtherLastOrigins
import Lamping.Checks.DirectedReadingDecomposition
namespace Lamping.Checks.DirectedMarkerLeafWordsChecks
open Lambda Lambda.Labelled
namespace NonemptyPrefix
open UniformOldCreatedIncomingLabelsChecks.Distinct

theorem produced : Nonempty
    (DirectedMarkerLeafOutput F source (.atom 7) false [left,right] (leftNode.label.readLetters false)) :=
  old.earliest_marker_leaf_output labels selected source_safe (start:=right) (before:=[]) .refl
    SelectedOldOtherLastOriginsChecks.actual_reading rfl marked (by intro e member;cases member)

theorem leaf_is_in_this_schedule : ∃leaf :
    DirectedMarkerLeafOutput F source (.atom 7) false [left,right] (leftNode.label.readLetters false),
    leaf.pre.length<2 := by
  obtain ⟨leaf⟩ := produced
  refine ⟨leaf,?_⟩
  have length:=congrArg List.length leaf.schedule
  simp only [List.length_cons,List.length_nil,List.length_append] at length
  omega

theorem actual_initial_nonempty_prefix : INIT original ∧History [[],left,right] original target ∧
    ¬middle.OuterBarsSafe (fun x=>x≠Label.atom 7) :=
  ⟨initial,globalHistory.append labels,unsafe_middle⟩
end NonemptyPrefix
namespace RootOverlap
open DirectedReadingDecompositionChecks

def old : Marked.RelativeOldHistory [[.fn]] [[.fn]] (Marked.mark [[.fn]] source.erase)
    (.app [] (.lam (.var 0)) (.lam (.var 0))) :=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.nil _)
theorem selected (p : Path) (member : p∈([[.fn]] : List Path)) : source.degreeAt p=some (.atom 2) := by
  have equal:=List.mem_singleton.mp member
  subst p;rfl

theorem produced (forward : Bool) : Nonempty
    (DirectedMarkerLeafOutput [[.fn]] source (.atom 2) forward [[.fn]] (result.label.readLetters forward)) := by
  have reading : PrerequisiteReadsDirected target (if forward then [] else [.fn]) [.fn] forward := by
    cases forward
    · exact ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
    · exact ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
  have marked : ¬result.label.OuterBarsSafe (fun x=>x≠Label.atom 2) :=
    step.created_label_not_safe (by rfl) (current:=result) rfl (Or.inl rfl)
  exact old.earliest_marker_leaf_output history selected (initial.outerBarsSafe _)
    (start:=if forward then [] else [.fn]) (before:=[]) .refl reading rfl marked
    (by intro e member;cases member)

theorem two_separators_retained :
    result.label.readLetters true=[.atom 1,.over (.atom 2),.atom 3,.under (.atom 2),.atom 4] ∧
    result.label.readLetters false=[.atom 4,.under (.atom 2),.atom 3,.over (.atom 2),.atom 1] := actual_overlap_words
end RootOverlap

namespace MarkedDescent
private abbrev I : Term := .lam (.var 0)
private abbrev caller : Term := .lam (.app (.lam (.var 0)) (.var 0))
private abbrev bare : Term := .app (.lam (.app (.var 0) (.app (.var 0) I))) caller
private abbrev original : LTerm := initLabels bare
private abbrev contractRoot : LTerm →LTerm
  | .app b (.lam a body) argument => LTerm.contract b a body argument
  | t=>t
private abbrev first : LTerm := contractRoot original
private abbrev second : LTerm := contractRoot first
private abbrev third : LTerm := match second with
  | .app b fn arg => .app b fn (contractRoot arg)
  | t=>t
private abbrev fourth : LTerm := contractRoot third
private abbrev fifth : LTerm := contractRoot fourth
private abbrev freshTail : LTerm := .lam (.atom 31) (.var (.atom 32) 0)
private abbrev wholeSource : LTerm := .app (.atom 30) third freshTail
private abbrev wrapperTarget : LTerm := .app (.atom 30) fifth freshTail
private abbrev wrappedOriginal : LTerm := .app (.atom 30) original freshTail
private abbrev F : List Path := [[.fn],[.fn,.arg]]
private def old : Marked.RelativeOldHistory F [[.fn],[.fn]] (Marked.mark F wholeSource.erase)
    (.app [] (.lam (.var 0)) (.lam (.var 0))) :=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.cons (.appL (.redRoot _ _ _)) (by decide) (.nil _))
private def labels : History [[.fn],[.fn]] wholeSource wrapperTarget :=
  .cons (.fn (.root _ _ _ _)) (.cons (.fn (.root _ _ _ _)) (.nil _))
private theorem selected (p : Path) (inside : p∈F) : wholeSource.degreeAt p=some (.atom 10) := by
  rcases List.mem_cons.mp inside with rfl | inside
  · rfl
  · have equal:=List.mem_singleton.mp inside;subst p;rfl
private theorem sourceSafe : wholeSource.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  change True ∧third.OuterBarsSafe (fun x=>x≠Label.atom 10) ∧freshTail.OuterBarsSafe (fun x=>x≠Label.atom 10)
  constructor
  · trivial
  · constructor
    · dsimp [third,second,first,original,bare,caller,I,contractRoot,initLabels,initFrom,nodeCount,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.rename,LTerm.lift,LTerm.label,Label.concat,Label.over,Label.under,Label.atom]
      simp only [LTerm.OuterBarsSafe,Label.OuterBarsSafe]
      decide
    · trivial
private theorem finalMarked : ¬fifth.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  obtain ⟨beta,body,arg,redex⟩ := LTerm.degreeAt_redex (by rfl : fourth.degreeAt []=some (.atom 10))
  have turn : StepAt [] fourth fifth := .root _ _ _ _
  exact turn.created_label_not_safe redex (current:=fifth) rfl (Or.inl rfl)

theorem produced (forward : Bool) : Nonempty
    (DirectedMarkerLeafOutput F wholeSource (.atom 10) forward [[.fn],[.fn]] (fifth.label.readLetters forward)) := by
  have reading : PrerequisiteReadsDirected wrapperTarget (if forward then [] else [.fn]) [.fn] forward := by
    cases forward
    · exact ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
    · exact ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
  exact old.earliest_marker_leaf_output labels selected sourceSafe
    (start:=if forward then [] else [.fn]) (before:=[]) .refl reading rfl finalMarked
    (by intro e member;cases member)

theorem actual_initial_prefix : INIT wrappedOriginal ∧History [[.fn],[.fn],[.fn,.arg]] wrappedOriginal wholeSource := by
  constructor
  · dsimp [wrappedOriginal,original,bare,caller,I,initLabels,initFrom,nodeCount,freshTail]
    simp [INIT,LTerm.labels,IsAtomic,Label.atom]
  · exact .cons (.fn (.root _ _ _ _)) (.cons (.fn (.root _ _ _ _)) (.cons (.fn (.arg (.root _ _ _ _))) (.nil _)))

theorem last_turn_first_is_unsafe : ¬fourth.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  obtain ⟨beta,body,arg,redex⟩ := LTerm.degreeAt_redex (by rfl : third.degreeAt []=some (.atom 10))
  have turn : StepAt [] third fourth := .root _ _ _ _
  exact turn.created_label_not_safe redex (current:=fourth) rfl (Or.inl rfl)
end MarkedDescent

#print axioms NonemptyPrefix.produced
#print axioms NonemptyPrefix.leaf_is_in_this_schedule
#print axioms NonemptyPrefix.actual_initial_nonempty_prefix
#print axioms RootOverlap.produced
#print axioms RootOverlap.two_separators_retained
#print axioms MarkedDescent.produced
#print axioms MarkedDescent.actual_initial_prefix
#print axioms MarkedDescent.last_turn_first_is_unsafe
end Lamping.Checks.DirectedMarkerLeafWordsChecks

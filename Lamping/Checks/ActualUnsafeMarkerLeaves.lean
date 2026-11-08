import Lamping.Lamping.ActualUnsafeMarkerLeaves
import Lamping.Checks.DirectedMarkerLeafWords
namespace Lamping.Checks.ActualUnsafeMarkerLeavesChecks
open Graph Lambda Lambda.Labelled AG
namespace Nonterminal
abbrev I : Term := WrappedSuccessfulChains.I
abbrev source : LTerm := initLabels (.app I (.app I I))
abbrev argument : LTerm := .lam (.atom 6) (.var (.atom 7) 0)
abbrev result : LTerm := LTerm.contract (.atom 3) (.atom 4) (.var (.atom 5) 0) argument
abbrev current : LTerm := .app (.atom 0) (.lam (.atom 1) (.var (.atom 2) 0)) result
abbrev F : List Path := [[.arg]]
abbrev edges : List Path := [[.arg],[.fn]]
def step : StepAt [.arg] source current := .arg (.root _ _ _ _)
def labels : History [[.arg]] source current := .cons step (.nil _)
theorem initial : INIT source := init_is_INIT _
theorem sourceClosed : Closed source.erase := by change (0<1) ∧(0<1) ∧0<1;decide
theorem closedCurrent : Closed current.erase := labels.closed sourceClosed
def old : Marked.RelativeOldHistory F [[.arg]] (Marked.mark F source.erase)
    (.app [[]] (.lam (.var 0)) (.lam (.var 0))) :=
  .cons (.appR (.redRoot _ _ _)) (by decide) (.nil _)
theorem selected (name : Path) (mem : name∈F) : source.degreeAt name=some (.atom 4) := by
  have eq:=List.mem_singleton.mp mem;subst name;rfl
def chain : PrerequisiteChain current [.arg] edges :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)
theorem marked : ¬degreeReadSafe (.atom 4) (current.labelAt [.arg]) := by
  intro h
  have bad:=h _ rfl
  change ((.atom 4 : Label)≠.atom 4) ∧_ at bad
  exact bad.1 rfl

private theorem cut_shape (cut : ActualUnsafeMarkerCut F [[.arg]] source current (.atom 4) [.arg] edges) :
    cut.before=[] ∧cut.edge=[.arg] ∧cut.after=[[.fn]] := by
  have split:=cut.split
  have empty : cut.before=[] := by
    cases front : cut.before with
    | nil => rfl
    | cons head tail =>
      rw [front] at split
      have eq : head=[.arg] := (List.cons.inj split).1.symm
      have safe:=cut.safeBefore head (by rw [front];exact List.mem_cons_self)
      rw [eq] at safe
      exact False.elim (marked safe)
  rw [empty,List.nil_append] at split
  exact ⟨empty,(List.cons.inj split).1.symm,(List.cons.inj split).2.symm⟩

theorem actual_nonterminal_leaves :
    ∃ left right : ActualUnsafeMarkerCut F [[.arg]] source current (.atom 4) [.arg] edges,
      left.before=[] ∧right.before=[] ∧left.edge=[.arg] ∧right.edge=[.arg] ∧
      left.after=[[.fn]] ∧right.after=[[.fn]] ∧left.forward=right.forward ∧
      Nonempty (DirectedMarkerLeafOutput F source (.atom 4) left.forward [[.arg]] (left.node.label.readLetters left.forward)) ∧
      Nonempty (DirectedMarkerLeafOutput F source (.atom 4) right.forward [[.arg]] (right.node.label.readLetters right.forward)) := by
  rcases actual_first_unsafe_marker_leaves initial (.nil source) old labels selected
      (initial.outerBarsSafe _) closedCurrent chain chain (ChainIncidenceIso.refl _) with all | cuts
  · exact False.elim (marked (all.1 [.arg] (by simp [edges])))
  · obtain ⟨left,right,len,lt,rt,ld,rd,front,head,back,tails,signs⟩:=cuts
    obtain ⟨lb,le,la⟩:=cut_shape left
    obtain ⟨rb,re,ra⟩:=cut_shape right
    have direction : left.forward=right.forward := signs.resolve_left (by rw [la];simp)
    exact ⟨left,right,lb,rb,le,re,la,ra,direction,left.leaf,right.leaf⟩
end Nonterminal

private theorem proper_zero_prefix (segment : PrerequisitePrefix t start es finish)
    (empty : es=[]) (notVar : ∀ stamp index,t.subterm start≠some (.var stamp index)) : finish=start := by
  cases segment with
  | refl => rfl
  | app lookup notLambda tail => cases empty
  | lam lookup notFunction tail => cases empty
  | var lookup binder split depth tail => exact False.elim (notVar _ _ lookup)

namespace Terminal
open DirectedReadingDecompositionChecks
abbrev closedTarget : Closed target.erase := history.closed closed
abbrev old := DirectedMarkerLeafWordsChecks.RootOverlap.old
abbrev selected := DirectedMarkerLeafWordsChecks.RootOverlap.selected

theorem actual_terminal_leaves :
    ∃ left : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [] [[.fn]],
    ∃ right : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [.fn] [[.fn]],
      left.after=[] ∧right.after=[] ∧left.forward=true ∧right.forward=false ∧
      Nonempty (DirectedMarkerLeafOutput [[.fn]] source (.atom 2) left.forward [[.fn]] (left.node.label.readLetters left.forward)) ∧
      Nonempty (DirectedMarkerLeafOutput [[.fn]] source (.atom 2) right.forward [[.fn]] (right.node.label.readLetters right.forward)) := by
  have marked : ¬degreeReadSafe (.atom 2) (target.labelAt [.fn]) := by
    intro h;have bad:=h _ rfl
    change ((.atom 2 : Label)≠.atom 2) ∧_ at bad
    exact bad.1 rfl
  rcases actual_first_unsafe_marker_leaves initial (.nil source) old history selected
      (initial.outerBarsSafe _) closedTarget successful_function successful_context (ChainIncidenceIso.refl _) with all | cuts
  · exact False.elim (marked (all.1 [.fn] (by simp)))
  · obtain ⟨left,right,len,lt,rt,ld,rd,front,head,back,tails,signs⟩:=cuts
    have length:=congrArg List.length left.split
    simp only [List.length_cons,List.length_nil,List.length_append] at length
    have empty : left.after=[] := List.length_eq_zero_iff.mp (by omega)
    have lb : left.before=[] := List.length_eq_zero_iff.mp (by omega)
    have rb : right.before=[] := List.length_eq_zero_iff.mp (by rw [←len,lb];rfl)
    have le : left.edge=[.fn] := by
      have split:=left.split;rw [lb,List.nil_append] at split
      exact (List.cons.inj split).1.symm
    have re : right.edge=[.fn] := by
      have split:=right.split;rw [rb,List.nil_append] at split
      exact (List.cons.inj split).1.symm
    have leftReader : left.reader=[] := proper_zero_prefix left.segment lb (by intro stamp index equal;cases equal)
    have rightReader : right.reader=[.fn] := proper_zero_prefix right.segment rb (by intro stamp index equal;cases equal)
    have ls : left.forward=true := by
      cases f:left.forward
      · have eq:=left.reading.2;rw [f] at eq
        change left.edge=left.reader at eq
        rw [le,leftReader] at eq;cases eq
      · rfl
    have rs : right.forward=false := by
      cases f:right.forward
      · rfl
      · have eq:=right.reading.2;rw [f] at eq
        change right.edge=right.reader++[.fn] at eq
        rw [re,rightReader] at eq;cases eq
    exact ⟨left,right,empty,tails.mp empty,ls,rs,left.leaf,right.leaf⟩
end Terminal
#print axioms actual_first_unsafe_marker_leaves
#print axioms Nonterminal.old
#print axioms Nonterminal.actual_nonterminal_leaves
#print axioms Terminal.actual_terminal_leaves
end Lamping.Checks.ActualUnsafeMarkerLeavesChecks

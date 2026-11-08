import Lamping.Lambda.TerminalReadingUncreatedSuffix
import Lamping.Checks.UniformOldCreatedIncomingLabels
namespace Lamping.Checks.TerminalReadingUncreatedSuffixChecks
open Lambda Lambda.Labelled

namespace TwoSelectedCopies
abbrev I : Term:=WrappedSuccessfulChains.I
abbrev bare : Term:=.app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.app I I) I))
abbrev original : LTerm:=initLabels bare
abbrev source : LTerm:=WrappedSuccessfulChains.contractRoot original
abbrev contractFunction (t : LTerm) : LTerm:=match t with
  | .app a fn arg => .app a (WrappedSuccessfulChains.contractRoot fn) arg
  | t=>t
abbrev middle : LTerm:=match source with
  | .app a (.lam l b) arg => .app a (.lam l (contractFunction b)) arg
  | t=>t
abbrev target : LTerm:=match middle with
  | .app a fn (.lam l b) => .app a fn (.lam l (contractFunction b))
  | t=>t
abbrev left : Path:=[.fn,.body,.fn]
abbrev right : Path:=[.arg,.body,.fn]
abbrev F : List Path:=[left,right]
abbrev arg : LTerm:=.lam (.atom 10) (.var (.atom 11) 0)
abbrev head : LTerm:=LTerm.contract (.atom 7) (.atom 8) (.var (.atom 9) 0) arg
def globalHistory : History [[]] original source:=.cons (.root _ _ _ _) (.nil _)
def firstStep : StepAt left source middle:=.fn (.body (.fn (.root _ _ _ _)))
def secondStep : StepAt right middle target:=.arg (.body (.fn (.root _ _ _ _)))
def suffix : History [right] middle target:=.cons secondStep (.nil _)
def labels : History [left,right] source target:=.cons firstStep suffix
def old : Marked.RelativeOldHistory F [left,right] (Marked.mark F source.erase)
    (.app [[]] (.lam (.app [] (.lam (.var 0)) (.lam (.var 0))))
      (.lam (.app [] (.lam (.var 0)) (.lam (.var 0))))) :=
  .cons (.appL (.lam (.appL (.redRoot _ _ _)))) (by decide)
    (.cons (.appR (.lam (.appL (.redRoot _ _ _)))) (by decide) (.nil _))
theorem selected (p : Path) (inside : p∈F) : source.degreeAt p=some (.atom 8) := by
  rcases List.mem_cons.mp inside with rfl | inside
  · rfl
  · have same:=List.mem_singleton.mp inside;subst p;rfl
def uncreatedSuffix : UncreatedNodeHistoryPreimage suffix left left :=
  .one (step:=secondStep) (by rfl)
    (.context (by rintro ⟨rest,impossible⟩;cases impossible)) (by decide) (.nil _ _)
theorem reading : PrerequisiteReadsDirected target left left false:=⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
def terminal : PrerequisiteChain target left [left]:=.redex_lam (p:=[.fn,.body]) rfl
theorem lookup : target.subterm left=some head:=rfl
theorem fresh : head.label∉source.labels:=by decide

theorem actual_nonempty_suffix_reflection :
    ([right] : List Path)≠[] ∧
    PrerequisiteReadsDirected middle left left false ∧PrerequisiteChain middle left [left] :=
  ⟨by simp,uncreatedSuffix.false_terminal_reflect reading terminal⟩

theorem actual_created_event :
    ∃pre post site m1 m2 t1 t2 beta body argument eventReader,
      [left,right]=pre++(site::post) ∧
      Marked.RelativeOldHistory F pre (Marked.mark F source.erase) m1 ∧
      Marked.RelativeOldHistory F post m2 (.app [[]] (.lam (.app [] (.lam (.var 0)) (.lam (.var 0))))
        (.lam (.app [] (.lam (.var 0)) (.lam (.var 0))))) ∧
      Marked.ReductionAt site m1 m2 ∧site∈Marked.setResidualPositions F m1 ∧
      ∃_prefix : History pre source t1,∃suffix : History post t2 target,
        StepAt site t1 t2 ∧t1.subterm site=some (.app beta (.lam (.atom 8) body) argument) ∧
        BetaCreatedIncoming body site eventReader ∧UncreatedNodeHistoryPreimage suffix left eventReader ∧
        PrerequisiteReadsDirected t2 eventReader eventReader false ∧PrerequisiteChain t2 eventReader [eventReader] ∧
        target.labelAt left=t2.labelAt eventReader ∧∃oldReader first last,
          BetaIncomingReadingOrigin body argument site eventReader eventReader oldReader first last ∧
          PrerequisiteChain t1 oldReader [first,site++[.fn]] ∧∃oldLast,t1.subterm last=some oldLast :=
  old.created_false_terminal_event_of_fresh (DegreeAligned.initial source F) labels selected reading terminal lookup fresh

theorem actual_same_initial_history : INIT original ∧History [[],left,right] original target ∧left≠right :=
  ⟨init_is_INIT _,globalHistory.append labels,by decide⟩

theorem actual_event_has_nonempty_post :
    ∃pre post site m1 t1 t2 beta body argument eventReader,
      [left,right]=pre++(site::post) ∧post≠[] ∧
      Marked.RelativeOldHistory F pre (Marked.mark F source.erase) m1 ∧
      ∃_prefix : History pre source t1,∃suffix : History post t2 target,
        StepAt site t1 t2 ∧t1.subterm site=some (.app beta (.lam (.atom 8) body) argument) ∧
        BetaCreatedIncoming body site eventReader ∧UncreatedNodeHistoryPreimage suffix left eventReader ∧
        PrerequisiteReadsDirected t2 eventReader eventReader false ∧PrerequisiteChain t2 eventReader [eventReader] := by
  obtain ⟨pre,post,site,m1,m2,t1,t2,beta,body,argument,eventReader,split,beforeOld,
    afterOld,reduction,member,segmentPrefix,eventSuffix,step,redex,created,trace,read,chain,_⟩:=actual_created_event
  have postNonempty : post≠[] := by
    intro empty
    have lastSite : site=right := by
      have rev:=congrArg List.reverse split
      simp only [empty,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] at rev
      exact (List.cons.inj rev).1.symm
    subst post
    cases eventSuffix
    cases trace
    have sourceOfEvent : t1=middle := by
      have preEq : pre=[left] := by
        rw [lastSite] at split
        have rev:=congrArg List.reverse split
        simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] at rev
        simpa using (congrArg List.reverse (List.cons.inj rev).2).symm
      have prefixEq : History [left] source t1 := preEq ▸ segmentPrefix
      exact prefixEq.deterministic (.cons firstStep (.nil _))
    subst t1
    have bodyEq : body=.var (.atom 9) 0 := by
      rw [lastSite] at redex
      have atRight : middle.subterm right=some (.app (.atom 7) (.lam (.atom 8) (.var (.atom 9) 0)) arg):=rfl
      exact (LTerm.lam.inj (LTerm.app.inj (Option.some.inj (redex.symm.trans atRight))).2.1).2
    have bad : ¬BetaCreatedIncoming body site left := by rw [bodyEq,lastSite];decide
    exact bad created
  exact ⟨pre,post,site,m1,t1,t2,beta,body,argument,eventReader,split,postNonempty,
    beforeOld,segmentPrefix,eventSuffix,step,redex,created,trace,read,chain⟩
end TwoSelectedCopies

#print axioms TwoSelectedCopies.actual_nonempty_suffix_reflection
#print axioms TwoSelectedCopies.actual_created_event
#print axioms TwoSelectedCopies.actual_same_initial_history
#print axioms TwoSelectedCopies.actual_event_has_nonempty_post
end Lamping.Checks.TerminalReadingUncreatedSuffixChecks

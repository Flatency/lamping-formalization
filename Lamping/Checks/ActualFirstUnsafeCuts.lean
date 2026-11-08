import Lamping.Lamping.ActualFirstUnsafeCuts
import Lamping.Checks.ActualChainForwardOrder
namespace Lamping.Checks.ActualFirstUnsafeCutsChecks
open Graph Lambda Lambda.Labelled AG
open ActualChainForwardOrderChecks
namespace Distinct
open ActualChainForwardOrderChecks.Distinct
abbrev safe (label : Option Label) : Prop := label≠some (.atom 6)

theorem actual_nonempty_first_cut :
    ∃ bs e as cs f ds l r,
      leftEdges=bs++e::as ∧rightEdges=cs++f::ds ∧bs.length=1 ∧cs.length=1 ∧
      current.labelAt e=current.labelAt f ∧¬safe (current.labelAt e) ∧
      PrerequisitePrefix current leftStart bs l ∧PrerequisiteReads current l e ∧
      PrerequisiteChain current l (e::as) ∧PrerequisitePrefix current rightStart cs r ∧
      PrerequisiteReads current r f ∧PrerequisiteChain current r (f::ds) := by
  rcases actual_first_unsafe_cuts history initial closedCurrent leftChain rightChain comparison safe with all | cut
  · have bad:=all.1 [.fn,.fn] (by simp [leftEdges])
    exact False.elim (bad rfl)
  · obtain ⟨n,bs,e,as,cs,f,ds,l,r,ls,rs,bl,cl,lt,rt,ld,rd,front,head,back,good,goodRight,bad,badRight,lp,lr,lc,rp,rr,rc⟩:=cut
    have frontLen:=congrArg List.length ls
    have bound : n≤1 := by simp only [leftEdges,List.length_cons,List.length_nil,List.length_append,bl] at frontLen;omega
    have notZero : n≠0 := by
      intro zero
      have empty : bs=[] := List.length_eq_zero_iff.mp (bl.trans zero)
      have edge : e=[.fn,.fn,.body,.fn] := by
        have eq:=ls
        rw [empty,List.nil_append] at eq
        exact (List.cons.inj eq).1.symm
      rw [edge] at bad
      exact bad (by decide)
    have one : n=1 := by omega
    exact ⟨bs,e,as,cs,f,ds,l,r,ls,rs,bl.trans one,cl.trans one,head,bad,lp,lr,lc,rp,rr,rc⟩

theorem actual_all_safe :
    (∀ e∈leftEdges,True) ∧(∀ e∈rightEdges,True) := by
  rcases actual_first_unsafe_cuts history initial closedCurrent leftChain rightChain comparison (fun _=>True) with all | cut
  · exact all
  · obtain ⟨n,bs,e,as,cs,f,ds,l,r,ls,rs,bl,cl,lt,rt,ld,rd,front,head,back,good,goodRight,bad,rest⟩:=cut
    exact False.elim (bad trivial)
theorem actual_degree_all_safe (degree : Label) :
    (∀ e∈leftEdges,degreeReadSafe degree (current.labelAt e)) ∧
    (∀ e∈rightEdges,degreeReadSafe degree (current.labelAt e)) := by
  have leftSafe : ∀ e∈leftEdges,degreeReadSafe degree (current.labelAt e) := by
    intro e mem
    simp only [leftEdges,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl | rfl <;> intro label eq <;> cases eq <;> trivial
  rcases actual_first_unsafe_cuts history initial closedCurrent leftChain rightChain comparison (degreeReadSafe degree) with all | cut
  · exact all
  · obtain ⟨n,bs,e,as,cs,f,ds,l,r,ls,rs,bl,cl,lt,rt,ld,rd,front,head,back,good,goodRight,bad,rest⟩:=cut
    have mem : e∈leftEdges := by rw [ls];exact List.mem_append_right _ List.mem_cons_self
    exact False.elim (bad (leftSafe e mem))
end Distinct
namespace MarkedTerminal
open DirectedReadingDecompositionChecks
abbrev closedTarget : Closed target.erase := history.closed closed
theorem actual_marked_terminal_cut :
    ∃ l r,PrerequisitePrefix target [] [] l ∧PrerequisiteReads target l [.fn] ∧
      PrerequisiteChain target l [[.fn]] ∧PrerequisitePrefix target [.fn] [] r ∧
      PrerequisiteReads target r [.fn] ∧PrerequisiteChain target r [[.fn]] ∧
      ¬degreeReadSafe (.atom 2) (target.labelAt [.fn]) := by
  have marked : ¬degreeReadSafe (.atom 2) (target.labelAt [.fn]) := by
    intro h
    have impossible:=h _ rfl
    change ((.atom 2 : Label)≠.atom 2) ∧_ at impossible
    exact impossible.1 rfl
  rcases actual_first_unsafe_cuts history initial closedTarget successful_function successful_context
      (ChainIncidenceIso.refl _) (degreeReadSafe (.atom 2)) with all | cut
  · exact False.elim (marked (all.1 [.fn] (by simp)))
  · obtain ⟨n,bs,e,as,cs,f,ds,l,r,ls,rs,bl,cl,lt,rt,ld,rd,front,head,back,good,goodRight,bad,badRight,lp,lr,lc,rp,rr,rc⟩:=cut
    have len:=congrArg List.length ls
    simp only [List.length_cons,List.length_nil,List.length_append] at len
    have empty : bs=[] := List.length_eq_zero_iff.mp (by omega)
    rw [empty,List.nil_append] at ls
    rw [empty] at lp
    have parts:=List.cons.inj ls
    have ee : e=[.fn] := parts.1.symm
    have aa : as=[] := parts.2.symm
    rw [ee,aa] at lc
    rw [ee] at lr
    have ce : cs=[] := List.length_eq_zero_iff.mp (by rw [←bl,empty] at cl;exact cl)
    rw [ce,List.nil_append] at rs
    rw [ce] at rp
    have parts:=List.cons.inj rs
    have ff : f=[.fn] := parts.1.symm
    have dd : ds=[] := parts.2.symm
    rw [ff,dd] at rc
    rw [ff] at rr
    exact ⟨l,r,lp,lr,lc,rp,rr,rc,marked⟩
end MarkedTerminal
#print axioms actual_first_unsafe_cuts
#print axioms Distinct.actual_nonempty_first_cut
#print axioms Distinct.actual_all_safe
#print axioms Distinct.actual_degree_all_safe
#print axioms MarkedTerminal.actual_marked_terminal_cut
#print axioms ActualChainForwardOrderChecks.Singleton.terminal_vertex_reverse_still_valid
end Lamping.Checks.ActualFirstUnsafeCutsChecks

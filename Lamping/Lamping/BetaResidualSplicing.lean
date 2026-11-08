import Lamping.Lamping.BetaAtomicContraction
namespace Lamping.AG
open Graph
private theorem dropLast_cons_cons {T : Type} (a b : T) (tail : List T) :
    (a::b::tail).dropLast=a::(b::tail).dropLast := by rfl
private theorem dropLast_append_nonempty {T : Type} (xs ys : List T) (nonempty : ys≠[]) :
    (xs++ys).dropLast=xs++ys.dropLast := by
  cases finish : ys.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp finish))
  | some last =>
    obtain ⟨pre,split⟩ := List.getLast?_eq_some_iff.mp finish
    rw [split,←List.append_assoc,List.dropLast_concat,List.dropLast_concat]
private theorem splice_head {T : Type} (pre after : List T) {first last : T}
    (start : pre.head?=some first) (finish : pre.getLast?=some last) (head : after.head?=some last) :
    (pre.dropLast++after).head?=some first := by
  cases pre with
  | nil => cases start
  | cons x pre =>
    have same : x=first := Option.some.inj start
    subst x
    cases pre with
    | nil =>
      have equal : first=last := Option.some.inj finish
      simpa only [equal,List.dropLast_singleton,List.nil_append] using head
    | cons y pre => simp only [dropLast_cons_cons,List.cons_append,List.head?_cons]
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
private theorem prepend_outside {edge : BetaEdge site.net} {raw old}
    (relation : BetaPathResidual site edge raw old) (first next : Endpoint cut)
    (head : raw.head?=some (.inl next)) :
    BetaPathResidual site edge (.inl first::raw) (site.outsideEnd first::old) := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp head
  rw [split] at relation ⊢
  exact .outside relation
/-- Splice two EXISTING residuals at one supplied outside segment occurrence.
The overlap is retained once in each graph; no extension or whole-path
coverage is assumed. The proof follows the finite first residual tree. -/
theorem BetaPathResidual.splice_last {edge : BetaEdge site.net} {raw old afterRaw afterOld}
    (before : BetaPathResidual site edge raw old) (after : BetaPathResidual site edge afterRaw afterOld)
    (shared : Endpoint cut) (finish : raw.getLast?=some (.inl shared))
    (head : afterRaw.head?=some (.inl shared)) :
    BetaPathResidual site edge (raw.dropLast++afterRaw) (old.dropLast++afterOld) := by
  induction before with
  | single e =>
    have equal : e=shared := Sum.inl.inj (Option.some.inj finish)
    subst shared
    simpa only [List.dropLast_singleton,List.nil_append] using after
  | @outside e f tail oldTail rest ih =>
    have restEnd : (.inl f::tail).getLast?=some (.inl shared) := by
      simpa only [List.getLast?_cons_cons] using finish
    have joined := ih restEnd
    have joinedHead := splice_head (.inl f::tail) afterRaw rfl restEnd head
    have result := prepend_outside site joined e f joinedHead
    have oldNonempty := rest.nonempty site
    have oldSplit : (site.outsideEnd e::oldTail).dropLast=site.outsideEnd e::oldTail.dropLast :=
      dropLast_append_nonempty [site.outsideEnd e] oldTail oldNonempty
    simpa only [List.cons_append,oldSplit,
      dropLast_cons_cons,List.singleton_append,List.append_assoc] using result
  | @context e tail oldTail arrival rest ih =>
    have restEnd : (.inl (.inr (.inl (.inr (.inr true))))::tail).getLast?=some (.inl shared) := by
      simpa only [List.getLast?_cons_cons] using finish
    have joined := ih restEnd
    have joinedHead := splice_head (.inl (.inr (.inl (.inr (.inr true))))::tail) afterRaw rfl restEnd head
    obtain ⟨newTail,newSplit⟩ := List.head?_eq_some_iff.mp joinedHead
    rw [newSplit] at joined
    have result := BetaPathResidual.context (site:=site) arrival joined
    rw [←newSplit] at result
    have oldNonempty := rest.nonempty site
    have oldSplit : (site.outsideEnd e::(edge.principal++oldTail)).dropLast=
        (site.outsideEnd e::edge.principal)++oldTail.dropLast := by
      exact dropLast_append_nonempty (site.outsideEnd e::edge.principal) oldTail oldNonempty
    simpa only [oldSplit,dropLast_cons_cons,List.cons_append,List.append_assoc] using result
  | @binding e tail oldTail arrival rest ih =>
    have restEnd : (.inl (.inr (.inl (.inr (.inl true))))::tail).getLast?=some (.inl shared) := by
      simpa only [List.getLast?_cons_cons] using finish
    have joined := ih restEnd
    have joinedHead := splice_head (.inl (.inr (.inl (.inr (.inl true))))::tail) afterRaw rfl restEnd head
    obtain ⟨newTail,newSplit⟩ := List.head?_eq_some_iff.mp joinedHead
    rw [newSplit] at joined
    have result := BetaPathResidual.binding (site:=site) arrival joined
    rw [←newSplit] at result
    have oldNonempty := rest.nonempty site
    have oldSplit : (site.outsideEnd e::(edge.reverseRoute++oldTail)).dropLast=
        (site.outsideEnd e::edge.reverseRoute)++oldTail.dropLast := by
      exact dropLast_append_nonempty (site.outsideEnd e::edge.reverseRoute) oldTail oldNonempty
    simpa only [oldSplit,dropLast_cons_cons,List.cons_append,List.append_assoc] using result

/-- Every finite residual really ends in a left segment; RHS excursions are
complete. This follows from its finite constructors, not a target oracle. -/
theorem BetaPathResidual.raw_last {edge : BetaEdge site.net} {raw old}
    (relation : BetaPathResidual site edge raw old) :
    ∃ last : Endpoint cut,raw.getLast?=some (.inl last) := by
  induction relation with
  | single e => exact ⟨e,rfl⟩
  | outside rest ih | context arrival rest ih | binding arrival rest ih =>
    obtain ⟨last,finish⟩ := ih
    exact ⟨last,by simpa only [List.getLast?_cons_cons] using finish⟩

/-- Recover the target's actual retained terminal from the OLD literal
terminal. It may then be transported through the genuine plug wiring. -/
theorem BetaPathResidual.reflect_finish {edge : BetaEdge site.net} {raw old}
    (relation : BetaPathResidual site edge raw old) (last : Endpoint cut)
    (finish : old.getLast?=some (site.outsideEnd last)) :
    raw.getLast?=some (.inl last) := by
  obtain ⟨actual,rawFinish⟩ := relation.raw_last site
  have oldFinish := relation.finish site rawFinish
  have same := site.outsideEnd_injective (Option.some.inj (oldFinish.symm.trans finish))
  simpa only [same] using rawFinish
end
end Lamping.AG
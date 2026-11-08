import Lamping.Lamping.TraceSeams
import Lamping.Lamping.OrdinaryEndpointExclusion
import Lamping.Lamping.OrdinaryPrefixRelabelling
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Ordinary source-local independence is reassembled into a root-based
assignment theorem at the supplied proper occurrence, without changing its
physical ordinal. This is the proper/proper component of the expanded base. -/
theorem Independence.rooted_proper_occurrence {root : B} (indep : Independence g root)
    {es cs} (trace : ContextTrace g es cs) (rooted : es.head?=some (.inr (.inl root)))
    (fw : Forward g es) (i : Nat) (e f : Endpoint g) (a b : Context)
    (m n : Nat) (sr tr : ProperRole) (atE : es[i]?=some e) (atA : cs[i]?=some a)
    (finish : es.getLast?=some (g.wire f)) (lastCtx : cs.getLast?=some b)
    (source : AtProperRole g root e sr m) (outgoing : sr.outgoing)
    (target : AtProperRole g root f tr n) (incoming : tr.incoming) :
    (∀ x,∃ ds,ContextTrace g es ds ∧ ds[i]?=some (a.replace m x)) ∧
    ∃ width,m≤width ∧ (sr=.appArg → m<width) ∧
      (∀ c,a=a.replace width c → b=b.replace (tr.terminalWidth n) c) ∧
      (∀ y,∃ ds,ContextTrace g es ds ∧ ds[i]?=some (a.replace width y) ∧
        ds.getLast?=some (b.replace (tr.terminalWidth n) y)) := by
  obtain ⟨input,head⟩ : ∃ input,cs.head?=some input := by
    cases trace <;> exact ⟨_,rfl⟩
  obtain ⟨pre,post,len,decomp,prefLabels,suffix⟩ := trace.split_segment_at i e a input b atE atA head lastCtx
  have takeEq : es.take (i+1)=pre++[e] := by
    rw [List.take_succ,atE]
    congr 1
    rw [decomp,←len,List.take_left]
  have suffixForward := fw.suffix_at i e atE
  rw [decomp,←len,List.drop_left] at suffixForward
  have suffixFinish : (e::post).getLast?=some (g.wire f) := by
    cases h : (e::post).getLast? with
    | none => have empty := List.getLast?_eq_none_iff.mp h; cases empty
    | some z =>
      rw [decomp,List.getLast?_append,h,Option.some_or] at finish
      exact finish
  obtain ⟨arbitrary,width,lower,strict,tail,sync⟩ := indep.forward_tail (e::post) e f sr tr m n a b
    rfl suffixFinish source outgoing target incoming suffixForward suffix
  have prefixReset : ∀ w,m≤w → ∀ x,∃ input,Labelling g (pre++[e]) input (a.replace w x) := by
    intro w lower x
    have shell : Context.SameShell m a (a.replace w x) := by
      intro k low
      exact (Context.replace_low _ _ (by omega : k<w)).symm
    obtain ⟨input,first⟩ := indep.rooted_source_prefix es cs trace rooted fw i e a m sr atE atA source outgoing
      ((a.replace w x).tail m)
    rw [Context.replace_of_sameShell a (a.replace w x) m shell,takeEq] at first
    exact ⟨input,first⟩
  constructor
  · intro x
    obtain ⟨output,last⟩ := arbitrary x
    obtain ⟨input,first⟩ := prefixReset m (Nat.le_refl _) x
    obtain ⟨ds,next,point,_,_⟩ := first.join_contextTrace last
    rw [←decomp] at next
    rw [len] at point
    exact ⟨ds,next,point⟩
  · refine ⟨width,lower,strict,tail,?_⟩
    intro y
    obtain ⟨input,first⟩ := prefixReset width lower y
    obtain ⟨ds,next,point,last,_⟩ := first.join_contextTrace (sync y)
    rw [←decomp] at next
    rw [len] at point
    exact ⟨ds,next,point,last⟩
/-- The complete ordinary constructor case of AG3.5.17 independence. Both
reverse-beta endpoint alternatives are excluded by actual rooted Forward
geometry, including arbitrary transparent principal subdivisions. -/
theorem Independence.expanded_ordinary_base {root : B} (indep : Independence g root)
    {es : List (Endpoint g)} (rooted : es.head?=some (.inr (.inl root))) (fw : Forward g es) :
    ExpandedIndependenceOn g root es := by
  intro cs expanded i e last a b m terminalWidth strict atE atA finish lastCtx source target
  have trace := expanded.ordinary_of_forward g fw
  cases source with
  | reversed r => exact False.elim (fw.no_reversed_source rooted i r atE)
  | proper e sr m atSource outgoing =>
    cases target with
    | reversed r last same =>
      rw [same] at finish
      exact False.elim (fw.no_reversed_target rooted r finish)
    | proper last tr n atTarget incoming =>
      have finish' : es.getLast?=some (g.wire (g.wire last)) := by simpa only [Pairing.involutive] using finish
      obtain ⟨arbitrary,width,lower,strict,tail,sync⟩ := indep.rooted_proper_occurrence trace rooted fw
        i e (g.wire last) a b m n sr tr atE atA finish' lastCtx atSource outgoing atTarget incoming
      constructor
      · intro x
        obtain ⟨ds,next,point⟩ := arbitrary x
        exact ⟨ds,next.expanded g,point⟩
      · refine ⟨width,lower,?_,tail,?_⟩
        · intro isStrict
          exact strict (of_decide_eq_true isStrict)
        · intro y
          obtain ⟨ds,next,point,last⟩ := sync y
          exact ⟨ds,next.expanded g,point,last⟩
/-- The actual ordinary generator proves existence and independence for every
nonempty physical prefix. This is the strengthened base needed by takePrefix;
no label is assumed for a longer generated partial path in later cases. -/
theorem Independence.expanded_ordinary_prefix_base {root : B} (indep : Independence g root)
    {es : List (Endpoint g)} (path : ForwardProperPath g es) (rooted : es.head?=some (.inr (.inl root)))
    (pre tail : List (Endpoint g)) (decomp : es=pre++tail) (nonempty : pre≠[]) :
    (∃ a b,ExpandedLabelling g pre a b) ∧ExpandedIndependenceOn g root pre := by
  obtain ⟨input,output,labels⟩ := path.1
  rw [decomp] at labels
  obtain ⟨middle,first⟩ := labels.prefix nonempty
  have fw := path.2
  rw [decomp] at fw
  have prefixForward := fw.prefix_of_append nonempty
  have prefixRoot : pre.head?=some (.inr (.inl root)) := by
    rw [decomp] at rooted
    cases pre with
    | nil => exact False.elim (nonempty rfl)
    | cons => exact rooted
  exact ⟨⟨input,middle,first.expanded⟩,indep.expanded_ordinary_base prefixRoot prefixForward⟩
end
end Lamping.AG




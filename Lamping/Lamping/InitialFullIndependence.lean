import Lamping.Lamping.InitialBindingPrograms
import Lamping.Lamping.InitialProgramTails
namespace Lamping.AG
open Graph Lambda

/-- The binding-terminal branch of initial Independence. Both the width
and the program are obtained from the actual physical path. -/
theorem encode_binding_target_independence (t : Term) (closed : Closed t) (level : Nat)
    (es : List (Endpoint (encode level t).net)) (e f : Endpoint (encode level t).net)
    (sr : ProperRole) (m n : Nat) (a b : Context)
    (source : AtProperRole (encode level t).net (.inl ()) e sr m) (outgoing : sr.outgoing)
    (target : AtProperRole (encode level t).net (.inl ()) f .lamBind n)
    (head : es.head?=some e) (last : es.getLast?=some ((encode level t).net.wire f))
    (labels : Labelling (encode level t).net es a b) :
    (∀ x,∃ output,Labelling (encode level t).net es (a.replace m x) output) ∧
    ∃ width,m≤width ∧(sr=.appArg → m<width) ∧
      (∀ c,b=b.replace (n+1) c → a=a.replace width c) ∧
      (∀ y,Labelling (encode level t).net es (a.replace width y) (b.replace (n+1) y)) := by
  obtain ⟨shape,word⟩ := encode_binding_program t closed level es e f sr m n source outgoing target head last labels
  have computes : ∀ {input output : Context},Labelling (encode level t).net es input output →
      output=shape.execute n input := by
    intro input output actual
    have run := InitialOffsets.InitialLabelling.events_run
      (encode_source_initial t level es e sr m source outgoing head actual)
    rw [word] at run
    exact run.functional.trans (shape.events_execute n input)
  have outputEq := computes labels
  have first : (InitialOffsets.eventsOfEdges (encode level t).net es).head?=some (.cro (n+shape.offset)) := by
    rw [word,shape.first_event]
  obtain ⟨lower,strict⟩ := encode_source_first_cro t level es e sr m (n+shape.offset) source outgoing head labels first
  refine ⟨fun x => encode_source_relabel t level es e sr m source outgoing head labels (a.replace m x),
    n+shape.offset,lower,strict,?_,?_⟩
  · intro c fixed
    have tailEq : b.tail (n+1)=a.tail (n+shape.offset) := by rw [outputEq,shape.execute_tail]
    have tailFixed : b.tail (n+1)=c := by
      calc b.tail (n+1)=(b.replace (n+1) c).tail (n+1) := congrArg (fun x : Context => x.tail (n+1)) fixed
           _=c := by simpa only [Nat.add_zero,InitialOffsets.tail_zero] using InitialOffsets.tail_replace b c (n+1) 0
    have actualTail : a.tail (n+shape.offset)=c := tailEq.symm.trans tailFixed
    rw [←actualTail]
    exact (a.replace_tail _).symm
  · intro y
    obtain ⟨output,changed⟩ := encode_source_relabel t level es e sr m source outgoing head labels
      (a.replace (n+shape.offset) y)
    have changedEq := computes changed
    rw [shape.execute_replace,←outputEq] at changedEq
    rw [changedEq] at changed
    exact changed

/-- Full Independence for the actual encoding of an arbitrary closed term,
including the appArg strict bound and simultaneous high-tail relabelling. -/
theorem encode_closed_independence (t : Term) (closed : Closed t) (level : Nat) :
    Independence (encode level t).net (.inl ()) := by
  intro es e f sr tr m n a b head last source outgoing target incoming _forward labels
  cases tr with
  | appCtx =>
    exact encode_context_target_independence t level es e f sr .appCtx m n a b
      source outgoing target (Or.inl rfl) head last labels
  | lamCtx =>
    exact encode_context_target_independence t level es e f sr .lamCtx m n a b
      source outgoing target (Or.inr rfl) head last labels
  | lamBind =>
    exact encode_binding_target_independence t closed level es e f sr m n a b
      source outgoing target head last labels
  | root | appFun | appArg | lamBody => cases incoming

theorem encode_closed_ordinary_invariants (t : Term) (closed : Closed t) (level : Nat) :
    OrdinaryPathInvariants (encode level t).net (.inl ()) :=
  ⟨encode_closed_independence t closed level,encode_nesting t level,encode_closed_transparency t closed level⟩
end Lamping.AG

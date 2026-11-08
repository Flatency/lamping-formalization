import Lamping.Lamping.InitialAccessDeterminism
namespace Lamping.AG.InitialOffsets
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
/-- A suffix starting again at this binder cannot lie strictly inside one
of its initial raw loops. No source path acyclicity hypothesis is supplied. -/
theorem NoBinderRevisit.no_strict_suffix {v : N} {es fs : List (Endpoint g)}
    (avoids : NoBinderRevisit g v es) (pre : List (Endpoint g))
    (same : es=pre++fs) (e : Endpoint g) (head : fs.head?=some e) (visit : Visits g v e) : pre=[] := by
  cases pre with
  | nil => rfl
  | cons x rest =>
    exfalso
    apply avoids e
    · cases fs with
      | nil => cases head
      | cons y ys =>
        have equal : y=e := Option.some.inj head
        cases equal
        simp [same]
    · exact visit
end

private theorem last_append_nonempty {T : Type} (pre tail : List T) (nonempty : tail≠[]) :
    (pre++tail).getLast?=tail.getLast? := by
  rw [List.getLast?_append]
  cases h : tail.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp h))
  | some => rfl

/-- Initial raw-loop suffixes ending at the same whole-path endpoint are
identical, including all transparent segment occurrences. -/
theorem encode_rawLoop_suffix_unique (t : Term) (n : Nat)
    {left right preLeft preRight : List (Endpoint (encode n t).net)}
    (first : RawLoop (encode n t).net left a b) (second : RawLoop (encode n t).net right c d)
    (whole : preLeft++left=preRight++right) : left=right := by
  let g := (encode n t).net
  have leftNonempty : left≠[] := by
    intro same
    have heads := congrArg List.head? same
    rw [first.start] at heads
    cases heads
  have rightNonempty : right≠[] := by
    intro same
    have heads := congrArg List.head? same
    rw [second.start] at heads
    cases heads
  have terminal := congrArg List.getLast? whole
  rw [last_append_nonempty _ _ leftNonempty,last_append_nonempty _ _ rightNonempty,
    first.finish,second.finish] at terminal
  have sameEnd := Option.some.inj terminal
  have nodes : first.binder=second.binder := by
    have equal := congrArg g.wire.mate sameEnd
    simp only [g,Pairing.involutive] at equal
    exact congrArg Sigma.fst (Sum.inl.inj equal)
  have firstAvoids := encode_rawLoop_no_revisit t n left a b first
  have secondAvoids := encode_rawLoop_no_revisit t n right c d second
  have firstVisit : Visits g second.binder (.inl ⟨first.binder,first.body⟩) := by
    rw [←nodes]
    exact ⟨first.body,rfl⟩
  have secondVisit : Visits g first.binder (.inl ⟨second.binder,second.body⟩) := by
    rw [nodes]
    exact ⟨second.body,rfl⟩
  by_cases lengths : preLeft.length≤preRight.length
  · have suffix : left=preRight.drop preLeft.length++right := by
      have dropped := congrArg (List.drop preLeft.length) whole
      simpa only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append,
        Nat.sub_eq_zero_of_le lengths] using dropped
    have empty := firstAvoids.no_strict_suffix _ suffix _ second.start secondVisit
    simpa only [empty,List.nil_append] using suffix
  · have reverseLengths : preRight.length≤preLeft.length := by omega
    have suffix : right=preLeft.drop preRight.length++left := by
      have dropped := congrArg (List.drop preRight.length) whole.symm
      simpa only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append,
        Nat.sub_eq_zero_of_le reverseLengths] using dropped
    have empty := secondAvoids.no_strict_suffix _ suffix _ first.start firstVisit
    exact (by simpa only [empty,List.nil_append] using suffix.symm)
end Lamping.AG.InitialOffsets

namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
def BindingLoop.rawLoop {es : List (Endpoint g)} (loop : BindingLoop g es a b) :
    InitialOffsets.RawLoop g es a b where
  binder := loop.binder
  isLam := loop.isLam
  body := loop.body
  bind := loop.bind
  body_role := loop.body_role
  bind_role := loop.bind_role
  start := loop.start
  finish := loop.finish
  proper := loop.proper
end

/-- A variable of an actual initial graph has one binding occurrence index,
with no matching, root-path or externally supplied nesting certificate. -/
theorem encode_bindingSuffix_unique (t : Term) (n : Nat)
    {es : List (Endpoint (encode n t).net)} {i j : Nat}
    (first : BindingSuffix (encode n t).net es i) (second : BindingSuffix (encode n t).net es j) : i=j := by
  obtain ⟨preLeft,left,a,b,c,leftBinding,leftCtx,leftSame,_,_,_,leftIndex⟩ := first
  obtain ⟨preRight,right,d,e,f,rightBinding,rightCtx,rightSame,_,_,_,rightIndex⟩ := second
  have loops := InitialOffsets.encode_rawLoop_suffix_unique t n
    leftBinding.rawLoop rightBinding.rawLoop (leftSame.symm.trans rightSame)
  rw [loops] at leftIndex
  exact leftIndex.trans rightIndex.symm

theorem encode_observes_var_of_suffix (t : Term) (n : Nat)
    {es : List (Endpoint (encode n t).net)} {k : Nat}
    (kind : accessKind (encode n t).net es=some .var)
    (binding : BindingSuffix (encode n t).net es k) : Observes (encode n t).net es (.var k) :=
  ⟨kind,binding,fun _ other => encode_bindingSuffix_unique t n other binding⟩
end Lamping.AG

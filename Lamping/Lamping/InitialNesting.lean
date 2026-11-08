import Lamping.Lamping.EncodedAddressing
import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG
open Graph Lambda
private theorem app_context_address {kind : Kind} (p : Port kind) (address : Path)
    (isApp : kind=.op .app) (role : HEq p appCtx) :
    syntaxPortAddress kind p address=some address ∧portKind kind p=some .app := by
  subst kind
  have same : p=appCtx := eq_of_heq role
  subst p
  exact ⟨rfl,rfl⟩
private theorem lam_context_address {kind : Kind} (p : Port kind) (address : Path)
    (isLam : kind=.op .lam) (role : HEq p (Sum.inl () : Port (.op .lam))) :
    syntaxPortAddress kind p address=some address ∧portKind kind p=some .lam := by
  subst kind
  have same : p=.inl () := eq_of_heq role
  subst p
  exact ⟨rfl,rfl⟩
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem AtProperRole.context_address {root : B} {x : Endpoint g} {role : ProperRole} {n : Nat}
    (target : AtProperRole g root x role n) (context : role=.appCtx ∨role=.lamCtx)
    (nodes : N → Path) (boundary : B → Option Path) (vertices : W → Option Path) :
    ∃ word kind,endpointAddress g nodes boundary vertices x=some word ∧endpointKind x=some kind := by
  rcases context with app | lam
  · subst role
    cases target with
    | appCtx node p level lab port =>
      obtain ⟨state,kind⟩ := app_context_address p (nodes node) (congrArg (fun l => l.sort) lab) port
      exact ⟨nodes node,.app,state,kind⟩
  · subst role
    cases target with
    | lamCtx node p level lab port =>
      obtain ⟨state,kind⟩ := lam_context_address p (nodes node) (congrArg (fun l => l.sort) lab) port
      exact ⟨nodes node,.lam,state,kind⟩
end

/-- A physical context edge of an initial graph has one syntax address, even
when comparing root accesses carrying different context assignments. -/
theorem encode_context_access_unique (t : Term) (level : Nat)
    (left right : RootAccess (encode level t).net (.inl ())) (e : Endpoint (encode level t).net)
    (leftEnd : left.val.getLast?=some e) (rightEnd : right.val.getLast?=some e)
    (role : ProperRole) (n : Nat) (context : role=.appCtx ∨role=.lamCtx)
    (target : AtProperRole (encode level t).net (.inl ()) ((encode level t).net.wire e) role n) : left=right := by
  obtain ⟨addr⟩ := encode_addressing t level
  obtain ⟨word,kind,arriving,_⟩ := target.context_address context addr.nodes (boundaryAddressAt []) addr.vertices
  have atExit : endpointAddress (encode level t).net addr.nodes (boundaryAddressAt []) addr.vertices e=some word :=
    (addr.wiring e).symm.trans arriving
  have address (access : RootAccess (encode level t).net (.inl ()))
      (last : access.val.getLast?=some e) : accessWord (encode level t).net access.val=word := by
    obtain ⟨a,b,labels⟩ := access.property.1.1
    have initial := encode_root_initial t level access.val access.property.2.1 labels
    obtain ⟨before,rootState,eq⟩ := addr.path_predecessor _ initial _ e access.property.2.1 last word atExit
    change some ([] : Path)=some before at rootState
    have empty : before=[] := (Option.some.inj rootState).symm
    simpa only [empty,List.nil_append] using eq.symm
  exact encode_accessWord_injective t level ((address left leftEnd).trans (address right rightEnd).symm)

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem ContextTrace.proper {es : List (Endpoint g)} {cs : List Context} (trace : ContextTrace g es cs) :
    ProperPath g es := by
  have nonempty : cs≠[] := by cases trace <;> simp
  cases first : cs.head? with
  | none => exact False.elim (nonempty (List.head?_eq_none_iff.mp first))
  | some a =>
    cases last : cs.getLast? with
    | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp last))
    | some b => exact ⟨a,b,trace.labelling g first last⟩
end

/-- No physical incoming context edge is visited twice on an initial rooted
proper path. This is stronger than initial Nesting and has no Closed premise. -/
theorem encode_context_no_revisit (t : Term) (level : Nat)
    (es : List (Endpoint (encode level t).net)) (proper : ProperPath (encode level t).net es)
    (rooted : es.head?=some (.inr (.inl (.inl ()))))
    (i j : Nat) (e : Endpoint (encode level t).net) (atI : es[i]?=some e) (atJ : es[j]?=some e)
    (role : ProperRole) (n : Nat) (context : role=.appCtx ∨role=.lamCtx)
    (target : AtProperRole (encode level t).net (.inl ()) ((encode level t).net.wire e) role n) : i=j := by
  have make (k : Nat) (atK : es[k]?=some e) :
      ∃ access : RootAccess (encode level t).net (.inl ()),access.val=es.take (k+1) := by
    have head : (es.take (k+1)).head?=some (.inr (.inl (.inl ()))) := by
      cases es with
      | nil => cases rooted
      | cons x tail => exact rooted
    have nonempty : es.take (k+1)≠[] := by intro empty; rw [empty] at head; cases head
    obtain ⟨a,b,labels⟩ := proper
    have splitLabels : Labelling (encode level t).net (es.take (k+1)++es.drop (k+1)) a b := by
      rw [List.take_append_drop]; exact labels
    obtain ⟨c,first⟩ := splitLabels.prefix nonempty
    have last : (es.take (k+1)).getLast?=some e := by
      simp only [List.getLast?_take,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,
        Nat.add_sub_cancel,atK,Option.some_or]
    obtain ⟨addr⟩ := encode_addressing t level
    obtain ⟨word,kind,_,incoming⟩ := target.context_address context addr.nodes (boundaryAddressAt []) addr.vertices
    have terminal : accessKind (encode level t).net (es.take (k+1))=some kind := by
      unfold accessKind
      rw [last]
      exact incoming
    exact ⟨⟨es.take (k+1),⟨⟨⟨a,c,first⟩,encode_root_forward t level _ head ⟨a,c,first⟩⟩,
      head,kind,terminal⟩⟩,rfl⟩
  obtain ⟨left,leftList⟩ := make i atI
  obtain ⟨right,rightList⟩ := make j atJ
  have lastI : left.val.getLast?=some e := by
    rw [leftList]
    simp only [List.getLast?_take,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,
      Nat.add_sub_cancel,atI,Option.some_or]
  have lastJ : right.val.getLast?=some e := by
    rw [rightList]
    simp only [List.getLast?_take,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,
      Nat.add_sub_cancel,atJ,Option.some_or]
  have same := encode_context_access_unique t level left right e lastI lastJ role n context target
  have lengths := congrArg (fun p : RootAccess (encode level t).net (.inl ()) => p.val.length) same
  dsimp only at lengths
  rw [leftList,rightList,List.length_take,List.length_take] at lengths
  obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp atI
  obtain ⟨hj,_⟩ := List.getElem?_eq_some_iff.mp atJ
  omega

theorem encode_nesting (t : Term) (level : Nat) : Nesting (encode level t).net (.inl ()) := by
  intro es cs trace rooted forward i j e a b n role strict atI atJ ctxI ctxJ context target shell
  have equal := encode_context_no_revisit t level es trace.proper rooted i j e atI atJ role n context target
  omega
end Lamping.AG

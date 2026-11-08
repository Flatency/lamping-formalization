import Lamping.Lamping.PathLabelDeterminism
import Lamping.Lamping.InitialPathConstruction
namespace Lamping.AG
open Graph Lambda
private theorem Traversal.direct_of_departure {i kind p q a b}
    (rule : Traversal i kind p q a b) (outgoing : initialPortPolarity kind q=true) :
    Passage i kind p q a b := by
  cases rule with
  | direct passage => exact passage
  | inverse passage =>
    have impossible := passage.polarities.1.symm.trans outgoing
    cases impossible

private theorem app_source {i : Nat} {kind : Kind} {p q : Port kind}
    (rule : Traversal i kind p q a b) (isApp : kind=.op .app)
    (role : HEq q (Sum.inl () : Port (.op .app)) ∨HEq q appArg) :
    HEq p appCtx ∧a=b ∧∀ c,Traversal i kind p q c c := by
  subst kind
  have out : initialPortPolarity (.op .app) q=true := by
    rcases role with fn | arg
    · have same : q=.inl () := eq_of_heq fn; subst q; rfl
    · have same : q=appArg := eq_of_heq arg; subst q; rfl
  have direct := rule.direct_of_departure out
  have source := direct.forward_ports.1
  have sameCtx : a=b := rule.proper_context
  refine ⟨source ▸ HEq.rfl,sameCtx,?_⟩
  intro c
  have sameP : p=appCtx := source
  subst p
  rcases role with fn | arg
  · have same : q=.inl () := eq_of_heq fn; subst q; exact .direct (.appFun c)
  · have same : q=appArg := eq_of_heq arg; subst q; exact .direct (.appArg c)

private theorem lam_source {i : Nat} {kind : Kind} {p q : Port kind}
    (rule : Traversal i kind p q a b) (isLam : kind=.op .lam) (role : HEq q lamBody) :
    HEq p (Sum.inl () : Port (.op .lam)) ∧a=b ∧∀ c,Traversal i kind p q c c := by
  subst kind
  have sameQ : q=lamBody := eq_of_heq role
  subst q
  have direct := rule.direct_of_departure rfl
  have source := direct.forward_ports.1
  have sameCtx : a=b := rule.proper_context
  have sameP : p=.inl () := source
  subst p
  exact ⟨HEq.rfl,sameCtx,fun c => .direct (.lamBody c)⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
private theorem LabelledTurn.proper_source {root : B} {x y : Endpoint g} {role : ProperRole} {m : Nat}
    (turn : LabelledTurn g x y a b) (source : AtProperRole g root y role m) (outgoing : role.outgoing) :
    ∃ incoming,AtProperRole g root x incoming m ∧incoming.incoming ∧
      incoming.terminalWidth m=m ∧a=b ∧∀ c,LabelledTurn g x y c c := by
  cases turn with
  | node node p q rule =>
    cases source with
    | appCtx => cases outgoing
    | lamCtx => cases outgoing
    | lamBind => cases outgoing
    | appFun node q m lab role =>
      obtain ⟨input,equal,relabel⟩ := app_source rule (congrArg (fun l => l.sort) lab) (Or.inl role)
      exact ⟨.appCtx,.appCtx node p m lab input,True.intro,rfl,equal,fun c => .node node p q (relabel c)⟩
    | appArg node q m lab role =>
      obtain ⟨input,equal,relabel⟩ := app_source rule (congrArg (fun l => l.sort) lab) (Or.inr role)
      exact ⟨.appCtx,.appCtx node p m lab input,True.intro,rfl,equal,fun c => .node node p q (relabel c)⟩
    | lamBody node q m lab role =>
      obtain ⟨input,equal,relabel⟩ := lam_source rule (congrArg (fun l => l.sort) lab) role
      exact ⟨.lamCtx,.lamCtx node p m lab input,True.intro,rfl,equal,fun c => .node node p q (relabel c)⟩
  | transparent w d a => cases source

theorem Forward.take_succ {es : List (Endpoint g)} (forward : Forward g es) (i : Nat) :
    Forward g (es.take (i+1)) := by
  induction forward generalizing i with
  | single e => cases i <;> exact .single e
  | node n p q arrives leaves direction after ih =>
    cases i with
    | zero => exact .single _
    | succ i => exact .node n p q arrives leaves direction (ih i)
  | transparent w d arrives leaves after ih =>
    cases i with
    | zero => exact .single _
    | succ i => exact .transparent w d arrives leaves (ih i)

theorem ContextTrace.take_succ {es : List (Endpoint g)} {cs : List Context}
    (trace : ContextTrace g es cs) (i : Nat) {a : Context} (atA : cs[i]?=some a) :
    ContextTrace g (es.take (i+1)) (cs.take (i+1)) := by
  induction trace generalizing i with
  | single e c =>
    cases i with
    | zero => exact .single e c
    | succ i => simp at atA
  | cons turn after ih =>
    cases i with
    | zero => exact .single _ _
    | succ i => exact .cons turn (ih i atA)

theorem ContextTrace.prefix_labels {es : List (Endpoint g)} {cs : List Context}
    (trace : ContextTrace g es cs) (i : Nat) {a input : Context}
    (atA : cs[i]?=some a) (head : cs.head?=some input) :
    Labelling g (es.take (i+1)) input a := by
  have prefixTrace := trace.take_succ i atA
  apply prefixTrace.labelling g
  · cases cs with
    | nil => cases head
    | cons c tail => exact head
  · simp only [List.getLast?_take,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,
      Nat.add_sub_cancel,atA,Option.some_or]

private theorem ContextTrace.turn_at {es : List (Endpoint g)} {cs : List Context}
    (trace : ContextTrace g es cs) (i : Nat) {e : Endpoint g} {a : Context}
    (atE : es[i+1]?=some e) (atA : cs[i+1]?=some a) :
    ∃ previous before,es[i]?=some previous ∧cs[i]?=some before ∧
      LabelledTurn g (g.wire previous) e before a := by
  induction trace generalizing i with
  | single x c => simp at atE
  | @cons x y tail input middle rest turn after ih =>
    cases i with
    | zero =>
      have sameE : y=e := Option.some.inj atE
      have sameA : middle=a := Option.some.inj atA
      subst e; subst a
      exact ⟨x,input,rfl,rfl,turn⟩
    | succ i => exact ih i atE atA

/-- Reset only the context tail at one actual outgoing occurrence in a rooted
ordinary path prefix. No arbitrary partial continuation is asserted. -/
theorem Independence.rooted_source_prefix {root : B} (indep : Independence g root)
    (es : List (Endpoint g)) (cs : List Context) (trace : ContextTrace g es cs)
    (rooted : es.head?=some (.inr (.inl root))) (forward : Forward g es)
    (i : Nat) (e : Endpoint g) (a : Context) (m : Nat) (role : ProperRole)
    (atE : es[i]?=some e) (atA : cs[i]?=some a)
    (source : AtProperRole g root e role m) (outgoing : role.outgoing) :
    ∀ x : Context,∃ input,Labelling g (es.take (i+1)) input (a.replace m x) := by
  intro x
  cases i with
  | zero =>
    cases es with
    | nil => cases rooted
    | cons first tail => exact ⟨a.replace m x,.single first _⟩
  | succ i =>
    obtain ⟨previous,before,atPrevious,atBefore,turn⟩ := trace.turn_at i atE atA
    obtain ⟨incoming,target,isIncoming,width,equal,relabel⟩ := turn.proper_source source outgoing
    subst before
    have ctxNonempty : cs≠[] := by cases trace <;> simp
    cases first : cs.head? with
    | none => exact False.elim (ctxNonempty (List.head?_eq_none_iff.mp first))
    | some initial =>
      have prefixLabels := trace.prefix_labels i atBefore first
      have prefixHead : (es.take (i+1)).head?=some (.inr (.inl root)) := by
        cases es with | nil => cases rooted | cons first tail => exact rooted
      have prefixLast : (es.take (i+1)).getLast?=some previous := by
        simp only [List.getLast?_take,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,
          Nat.add_sub_cancel,atPrevious,Option.some_or]
      obtain ⟨arbitrary,cut,lower,strict,tail,sync⟩ := indep (es.take (i+1))
        (.inr (.inl root)) (g.wire previous) .root incoming 0 m initial a
        prefixHead (by simpa only [Pairing.involutive] using prefixLast) .root True.intro
        target isIncoming (forward.take_succ i) prefixLabels
      have changed := sync x
      rw [width] at changed
      refine ⟨initial.replace cut x,?_⟩
      rw [List.take_succ,atE]
      apply changed.append_seam (.single e (a.replace m x))
      intro left right last head
      have sameLeft : left=previous := Option.some.inj (last.symm.trans prefixLast)
      have sameRight : right=e := (Option.some.inj head).symm
      rw [sameLeft,sameRight]
      exact relabel (a.replace m x)
end
end Lamping.AG

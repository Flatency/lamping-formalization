import Lamping.Lamping.BetaDetourBlocks
import Lamping.Lamping.ExpandedIndependence
namespace Lamping.AG
open Graph

private theorem no_bind {i kind p q a b}
    (rule : Traversal i kind p q a b) (sort : kind=.op .lam) (bind : HEq p lamBind) : False := by
  subst kind
  have same : p=lamBind := eq_of_heq bind
  exact rule.no_binding.1 same
private def AppConstraint : (kind : Kind) → Port kind → Port kind → Prop
  | .op .app,.inl _,q => q=appCtx
  | _,_,_ => True
private theorem app_constraint {i kind p q a b} (rule : Traversal i kind p q a b) :
    AppConstraint kind p q := by
  cases rule with
  | direct passage => cases passage <;> trivial
  | inverse passage => cases passage <;> trivial
private theorem no_function_argument {i kind p q a b}
    (rule : Traversal i kind p q a b) (sort : kind=.op .app)
    (function : HEq p (Sum.inl () : Port (.op .app))) (argument : HEq q appArg) : False := by
  subst kind
  have hp : p=.inl () := eq_of_heq function
  have hq : q=appArg := eq_of_heq argument
  have constraint := app_constraint rule
  rw [hp,hq] at constraint
  change (Sum.inr true : Port (.op .app))=Sum.inr false at constraint
  cases constraint

private theorem ordinary_reflect {i kind p q a b c d}
    (old : Traversal i kind p q a b) :
    ∀ {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
      (g : Net signature N B W) (node : N) (_sort : (g.label node).sort=kind)
      (left right : Port (g.label node).sort) (_hp : HEq left p) (_hq : HEq right q),
      ExpandedTurn g (.inl ⟨node,left⟩) (.inl ⟨node,right⟩) c d →
      LabelledTurn g (.inl ⟨node,left⟩) (.inl ⟨node,right⟩) c d := by
  intro N B W _ _ _ g node sort left right hp hq turn
  cases turn with
  | ordinary actual => exact actual
  | bindToCtx edge c =>
    exact False.elim (no_bind old (sort.symm.trans (congrArg Label.sort edge.lamLabel))
      (hp.symm.trans edge.lamBind_role))
  | funToArg edge c =>
    exact False.elim (no_function_argument old (sort.symm.trans (congrArg Label.sort edge.appLabel))
      (hp.symm.trans edge.appFun_role) (hq.symm.trans edge.appArg_role))

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private theorem actual_ordinary {e f : Endpoint g} {a b c d : Context}
    (old : LabelledTurn g e f a b) (next : ExpandedTurn g e f c d) : LabelledTurn g e f c d := by
  cases old with
  | node node p q rule => exact ordinary_reflect rule g node rfl p q HEq.rfl HEq.rfl next
  | transparent w direction a => cases next with | ordinary actual => exact actual

/-- The already supplied finite paired shape survives a new assignment on
the SAME physical list. No new list, continuation or generated witness is
postulated; reverse corridors retain their complete literal segments. -/
theorem BetaDetourBlocks.relabel {es : List (Endpoint g)} {a b c d : Context} {count : Nat}
    (path : BetaDetourBlocks g es a b count) (labels : ExpandedLabelling g es c d) :
    BetaDetourBlocks g es c d count := by
  induction path generalizing c d with
  | single e a => cases labels with | single => exact .single e c
  | ordinary turn rest ih =>
    cases labels with
    | cons first after => exact .ordinary (actual_ordinary turn first) (ih after)
  | @backward edge e tail a b count arrival head rest ih =>
    obtain ⟨suffix,tailEq⟩ := List.head?_eq_some_iff.mp head
    have full : ExpandedLabelling g (([e]++edge.reverseRoute)++edge.argEnd::suffix) c d := by
      simpa only [tailEq,List.singleton_append,List.append_assoc] using labels
    obtain ⟨middle,before,after⟩ := full.split_segment
    have corridor := (ExpandedLabelling.single (g:=g) e c).splice rfl
      (edge.reverse_labeling c).expanded edge.reverse_start (by
        change ExpandedTurn g (g.wire e) edge.ctxEnd c c
        rw [arrival]; exact .bindToCtx edge c)
    have corridorEnd : ([e]++edge.reverseRoute).getLast?=some (g.wire edge.funEnd) := by
      simp only [List.getLast?_append,edge.reverse_finish,Option.some_or]
    have block := corridor.splice corridorEnd (ExpandedLabelling.single (g:=g) edge.argEnd c) rfl
      (by simpa only [Pairing.involutive] using ExpandedTurn.funToArg (g:=g) edge c)
    have same : middle=c := before.output_unique block
    subst middle
    have afterActual : ExpandedLabelling g tail c d := by rw [tailEq]; exact after
    exact .backward edge e arrival head (ih afterActual)
end
end Lamping.AG


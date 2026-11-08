import Lamping.Lamping.MatchedControlInputs
import Lamping.Lamping.ControlLeafPrefixes
namespace Lamping.AG
open Graph

private theorem control_arrival_unique (op : Op) (control : op=.fan ∨op=.cro ∨op=.bra)
    {index : Nat} {p p' q : Port (.op op)} {a a' b : Context}
    (first : Traversal index (.op op) p q a b)
    (second : Traversal index (.op op) p' q a' b) : p=p' := by
  rcases control with same | same | same <;> subst op
  all_goals
    cases q with
    | inl u =>
      cases u
      cases p with
      | inl u => cases u; exact False.elim (first.distinct rfl)
      | inr left =>
        cases p' with
        | inl u => cases u; exact False.elim (second.distinct rfl)
        | inr right =>
          have same := first.reverse.control_auxiliary_unique (by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)) second.reverse
          exact congrArg Sum.inr same
    | inr auxiliary =>
      have one : p=.inl () := first.reverse.control_aux
      have two : p'=.inl () := second.reverse.control_aux
      exact one.trans two.symm

/-- A forward departure and its output context determine the predecessor
port and context. In particular a fan branch is decoded from O/Star. -/
theorem Traversal.forward_predecessor_unique {index : Nat} {kind : Kind}
    {p p' q : Port kind} {a a' b : Context}
    (first : Traversal index kind p q a b) (firstForward : ForwardPorts kind p q)
    (second : Traversal index kind p' q a' b) (secondForward : ForwardPorts kind p' q) :
    p=p' ∧a=a' := by
  have ports : p=p' := by
    cases kind with
    | garbage => exact False.elim firstForward
    | op op =>
      cases op with
      | app => exact firstForward.1.trans secondForward.1.symm
      | lam => exact firstForward.1.trans secondForward.1.symm
      | fan => exact control_arrival_unique .fan (Or.inl rfl) first second
      | cro => exact control_arrival_unique .cro (Or.inr (Or.inl rfl)) first second
      | bra => exact control_arrival_unique .bra (Or.inr (Or.inr rfl)) first second
  subst p'
  exact ⟨rfl,first.reverse.output_unique second.reverse⟩
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

inductive ForwardLabelledTurn : Endpoint g → Endpoint g → Context → Context → Prop where
  | node (node : N) (p q : Port (g.label node).sort) {a b : Context}
      (rule : Traversal (g.label node).index (g.label node).sort p q a b)
      (direction : ForwardPorts (g.label node).sort p q) :
      ForwardLabelledTurn (.inl ⟨node,p⟩) (.inl ⟨node,q⟩) a b
  | transparent (vertex : W) (direction : Bool) (a : Context) :
      ForwardLabelledTurn (.inr (.inr (vertex,direction))) (.inr (.inr (vertex,!direction))) a a

theorem ForwardLabelledTurn.predecessor_unique {x y z : Endpoint g} {a a' b : Context}
    (first : ForwardLabelledTurn g x z a b) (second : ForwardLabelledTurn g y z a' b) :
    x=y ∧a=a' := by
  cases first with
  | node node p q rule direction =>
    cases second with
    | node node p' q other otherDirection =>
      obtain ⟨ports,contexts⟩ := rule.forward_predecessor_unique direction other otherDirection
      exact ⟨congrArg (fun port => (.inl ⟨node,port⟩ : Endpoint g)) ports,contexts⟩
  | transparent vertex direction a =>
    generalize outputEq : (Sum.inr (Sum.inr (vertex,!direction)) : Endpoint g)=last at second
    cases second with
    | node node p q actual forward => cases outputEq
    | transparent vertex' direction' context =>
      have pairEq := Sum.inr.inj (Sum.inr.inj outputEq)
      have vertices := congrArg Prod.fst pairEq
      have directions := congrArg (fun pair => !pair.2) pairEq
      simp only [Bool.not_not] at directions
      cases vertices
      cases directions
      exact ⟨rfl,rfl⟩

private theorem forward_last (pre : List (Endpoint g)) (last : Endpoint g)
    {a b : Context} (labels : Labelling g (pre++[last]) a b)
    (forward : Forward g (pre++[last])) (nonempty : pre≠[]) :
    ∃ previous middle,pre.getLast?=some previous ∧Labelling g pre a middle ∧Forward g pre ∧
      ForwardLabelledTurn g (g.wire previous) last middle b := by
  induction pre generalizing a with
  | nil => exact False.elim (nonempty rfl)
  | cons x pre ih =>
    cases pre with
    | nil =>
      cases labels with
      | cons turn tail =>
        cases tail
        cases forward with
        | node node p q arrives leaves direction rest =>
          rw [arrives,leaves] at turn
          cases turn with
          | node node p q rule =>
            refine ⟨x,_,rfl,.single _ _,.single _,?_⟩
            rw [arrives,leaves]
            exact .node node p q rule direction
        | transparent vertex direction arrives leaves rest =>
          rw [arrives,leaves] at turn
          cases turn
          refine ⟨x,_,rfl,.single _ _,.single _,?_⟩
          rw [arrives,leaves]
          exact .transparent vertex direction _
    | cons y pre =>
      cases labels with
      | cons turn tail =>
        cases forward with
        | node node p q arrives leaves direction rest =>
          obtain ⟨previous,middle,finish,before,beforeForward,lastTurn⟩ := ih tail rest (by simp)
          exact ⟨previous,middle,by simpa only [List.getLast?_cons_cons] using finish,
            .cons turn before,.node node p q arrives leaves direction beforeForward,lastTurn⟩
        | transparent vertex direction arrives leaves rest =>
          obtain ⟨previous,middle,finish,before,beforeForward,lastTurn⟩ := ih tail rest (by simp)
          exact ⟨previous,middle,by simpa only [List.getLast?_cons_cons] using finish,
            .cons turn before,.transparent vertex direction arrives leaves beforeForward,lastTurn⟩

/-- Rooted forward paths with the same final segment and full final context
are literally equal, even when their initial contexts were different. -/
theorem Labelling.rooted_terminal_unique {root : B} {es fs : List (Endpoint g)}
    {input otherInput output : Context}
    (labels : Labelling g es input output) (forward : Forward g es)
    (rooted : es.head?=some (.inr (.inl root)))
    (other : Labelling g fs otherInput output) (otherForward : Forward g fs)
    (otherRoot : fs.head?=some (.inr (.inl root))) (lastSame : es.getLast?=fs.getLast?) :
    es=fs ∧input=otherInput := by
  obtain ⟨last,lastEq⟩ : ∃ last,es.getLast?=some last := by
    cases lastEq : es.getLast? with
    | none => exact False.elim (labels.nonempty (List.getLast?_eq_none_iff.mp lastEq))
    | some last => exact ⟨last,rfl⟩
  obtain ⟨pre,split⟩ := List.getLast?_eq_some_iff.mp lastEq
  obtain ⟨otherPre,otherSplit⟩ := List.getLast?_eq_some_iff.mp (lastSame.symm.trans lastEq)
  by_cases empty : pre=[]
  · have shape : es=[.inr (.inl root)] := by
      rw [empty,List.nil_append] at split
      have same : last=.inr (.inl root) := Option.some.inj (by simpa only [split,List.head?_cons] using rooted)
      rw [split,same]
    have finish : es.getLast?=some (.inr (.inl root)) := by rw [shape]; rfl
    have sameInput := (labels.boundary_last root finish).2
    obtain ⟨otherShape,otherInputEq⟩ := other.boundary_last root (lastSame.symm.trans finish)
    exact ⟨shape.trans otherShape.symm,sameInput.trans otherInputEq.symm⟩
  by_cases otherEmpty : otherPre=[]
  · have shape : fs=[.inr (.inl root)] := by
      rw [otherEmpty,List.nil_append] at otherSplit
      have same : last=.inr (.inl root) := Option.some.inj (by simpa only [otherSplit,List.head?_cons] using otherRoot)
      rw [otherSplit,same]
    have finish : fs.getLast?=some (.inr (.inl root)) := by rw [shape]; rfl
    have otherInputEq := (other.boundary_last root finish).2
    obtain ⟨ownShape,ownInputEq⟩ := labels.boundary_last root (lastSame.trans finish)
    exact ⟨ownShape.trans shape.symm,ownInputEq.trans otherInputEq.symm⟩
  obtain ⟨previous,middle,preLast,before,beforeForward,turn⟩ := forward_last g pre last
    (by rw [←split]; exact labels) (by rw [←split]; exact forward) empty
  obtain ⟨otherPrevious,otherMiddle,otherLast,otherBefore,otherBeforeForward,otherTurn⟩ := forward_last g otherPre last
    (by rw [←otherSplit]; exact other) (by rw [←otherSplit]; exact otherForward) otherEmpty
  obtain ⟨arrivals,contexts⟩ := turn.predecessor_unique g otherTurn
  have endpoints : previous=otherPrevious := by
    have inverse := congrArg g.wire.mate arrivals
    simpa only [Pairing.involutive] using inverse
  have preRoot : pre.head?=some (.inr (.inl root)) := by
    cases pre with
    | nil => exact False.elim (empty rfl)
    | cons x xs => simpa only [split,List.cons_append,List.head?_cons] using rooted
  have otherPreRoot : otherPre.head?=some (.inr (.inl root)) := by
    cases otherPre with
    | nil => exact False.elim (otherEmpty rfl)
    | cons x xs => simpa only [otherSplit,List.cons_append,List.head?_cons] using otherRoot
  have sameEnd : pre.getLast?=otherPre.getLast? :=
    preLast.trans ((congrArg some endpoints).trans otherLast.symm)
  cases contexts
  obtain ⟨samePre,sameInputs⟩ := before.rooted_terminal_unique beforeForward preRoot otherBefore otherBeforeForward otherPreRoot sameEnd
  exact ⟨by rw [split,otherSplit,samePre],sameInputs⟩
termination_by es.length
decreasing_by rw [split]; simp
end
end Lamping.AG



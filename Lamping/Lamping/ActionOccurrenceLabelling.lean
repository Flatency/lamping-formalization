import Lamping.Lamping.ActionResidualOccurrences
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem equal_ordinal_splits {T : Type} {left right : List T} {e f : T} {after tail : List T}
    (same : left++e::after=right++f::tail) (length : left.length=right.length) :
    left=right ∧e=f ∧after=tail := by
  induction left generalizing right with
  | nil => cases right with
    | nil => have eqs := List.cons.inj same; exact ⟨rfl,eqs.1,eqs.2⟩
    | cons h right => simp at length
  | cons h left ih => cases right with
    | nil => simp at length
    | cons k right =>
      obtain ⟨heads,rest⟩ := List.cons.inj same
      have lengths : left.length=right.length := by simpa only [List.length_cons,Nat.succ.injEq] using length
      obtain ⟨rfl,rfl,rfl⟩ := ih rest lengths
      subst k
      exact ⟨rfl,rfl,rfl⟩

theorem ActionCanonicalBlocks.split_kept_decomposition {principal : SiteActionPrincipal site} {raw old}
    (relation : ActionCanonicalBlocks site principal raw old)
    (node : K) (p : Port (kept node).sort) (pre after : List (Endpoint site.net))
    (split : old=pre++(.inl ⟨.inl node,p⟩)::after) :
    ∃ cutAt : ActionResidualOccurrence site principal raw old node p pre.length,
      cutAt.oldBefore=pre ∧cutAt.oldAfter=after := by
  have atOccurrence : old[pre.length]?=some (.inl ⟨.inl node,p⟩) := by
    rw [split,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
    rfl
  obtain ⟨cutAt⟩ := relation.split_kept_occurrence site atOccurrence
  obtain ⟨beforeEq,_,afterEq⟩ := equal_ordinal_splits (cutAt.old_eq.symm.trans split) cutAt.position
  exact ⟨cutAt,beforeEq,afterEq⟩

private theorem right_block_unique {L R : Type} {xs ys : List R} {x y : L}
    {tail post : List (L⊕R)}
    (same : xs.map Sum.inr++Sum.inl x::tail=ys.map Sum.inr++Sum.inl y::post) :
    xs=ys ∧x=y ∧tail=post := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => have eqs := List.cons.inj same; exact ⟨rfl,Sum.inl.inj eqs.1,eqs.2⟩
    | cons h ys => cases same
  | cons h xs ih =>
    cases ys with
    | nil => cases same
    | cons k ys =>
      obtain ⟨head,rest⟩ := List.cons.inj same
      have heads := Sum.inr.inj head
      obtain ⟨rfl,rfl,rfl⟩ := ih rest
      subst k
      exact ⟨rfl,rfl,rfl⟩

private theorem outside_view {e f : Endpoint cut} {tail} {a b : Context}
    (shape : PlugExcursions cut s.right.net (.inl e::.inl f::tail) a b) :
    ∃ middle,LabelledTurn cut ((cut).wire e) f a middle ∧
      PlugExcursions cut s.right.net (.inl f::tail) middle b := by
  generalize eqs : (.inl e::.inl f::tail : List (PlugSegment cut s.right.net))=raw at shape
  cases shape with
  | single => cases eqs
  | outside turn after => cases eqs; exact ⟨_,turn,after⟩
  | through path arrival after =>
    have nonempty := path.labeling.nonempty
    cases split : path.edges with
    | nil => exact False.elim (nonempty split)
    | cons h xs => rw [split,List.map_cons,List.cons_append] at eqs; cases eqs

private theorem through_view {e : Endpoint cut} {exit : s.Frontier} {inside tail} {a b : Context}
    (nonempty : inside≠[])
    (shape : PlugExcursions cut s.right.net
      (.inl e::(inside.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::tail)) a b) :
    ∃ middle,Labelling s.right.net inside a middle ∧
      PlugExcursions cut s.right.net (.inl (.inr (.inl (.inr exit)))::tail) middle b := by
  generalize eqs : (.inl e::(inside.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::tail) :
    List (PlugSegment cut s.right.net))=raw at shape
  cases shape with
  | single =>
    cases inside with
    | nil => exact False.elim (nonempty rfl)
    | cons h xs => cases eqs
  | outside turn after =>
    cases inside with
    | nil => exact False.elim (nonempty rfl)
    | cons h xs => cases eqs
  | @through first entry other post a middle b path arrival after =>
    have initial := List.cons.inj eqs
    have firstEq := Sum.inl.inj initial.1
    subst first
    obtain ⟨edgeEq,exitEq,tailEq⟩ := right_block_unique initial.2
    have exits := Sum.inr.inj (Sum.inl.inj (Sum.inr.inj exitEq))
    subst other
    subst post
    exact ⟨middle,by rw [edgeEq]; exact path.labeling,after⟩

/-- Reflect this actual raw assignment along the already chosen canonical
residual. The local relation's physical routes determine the source list;
their genuine local inverse transport proves its labels with the SAME A/B.
This does not claim arbitrary-input replay or source-to-target contraction. -/
theorem ActionCanonicalBlocks.source_labels {principal : SiteActionPrincipal site} {raw old}
    (relation : ActionCanonicalBlocks site principal raw old) {a b : Context}
    (shape : PlugExcursions cut s.right.net raw a b) : Labelling site.net old a b := by
  induction relation generalizing a b with
  | single e =>
    have labels := shape.labelling cut s.right.net
    cases labels
    exact .single _ _
  | @outside e f tail old rest ih =>
    obtain ⟨middle,turn,after⟩ := outside_view site shape
    have afterLabels := ih after
    have first := rest.head site rfl
    obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp first
    rw [split] at afterLabels ⊢
    apply Labelling.cons _ afterLabels
    rw [site.outsideEnd_wire]
    exact turn.outsideEnd site
  | @through e exit tail old inside front route start rest ih =>
    obtain ⟨middle,insideLabels,after⟩ := through_view site route.nonempty shape
    have block := route.source_labels site insideLabels
    have afterLabels := ih after
    have first := rest.head site rfl
    obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp first
    rw [split] at afterLabels ⊢
    exact block.join afterLabels
end

section Body
variable {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
variable {g : Net signature N D U}

private theorem last_turn {pre : List (Endpoint g)} {last : Endpoint g} {a b : Context}
    (labels : Labelling g (pre++[last]) a b) (nonempty : pre≠[]) :
    ∃ previous middle,pre.getLast?=some previous ∧Labelling g pre a middle ∧
      LabelledTurn g (g.wire previous) last middle b := by
  induction pre generalizing a with
  | nil => exact False.elim (nonempty rfl)
  | cons x pre ih => cases pre with
    | nil => cases labels with
      | cons turn tail => cases tail; exact ⟨x,_,rfl,.single _ _,turn⟩
    | cons y pre => cases labels with
      | cons turn tail =>
        obtain ⟨previous,middle,finish,before,lastTurn⟩ := ih tail (by simp)
        exact ⟨previous,middle,by simpa only [List.getLast?_cons_cons] using finish,.cons turn before,lastTurn⟩

private theorem body_predecessor {kind : Kind} {index : Nat} {ctx body p : Port kind} {a b : Context}
    (sort : kind=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    (rule : Traversal index kind p body a b) : p=ctx ∧a=b := by
  subst kind
  have ctxEq : ctx=.inl () := eq_of_heq ctxRole
  have bodyEq : body=lamBody := eq_of_heq bodyRole
  subst ctx
  subst body
  refine ⟨?_,rule.proper_context⟩
  cases p with
  | inl u => cases u; rfl
  | inr branch =>
    cases branch
    · exact False.elim (rule.no_binding.1 rfl)
    · exact False.elim (rule.distinct rfl)

/-- Remove the actual final lambda-body turn and retain its exact context.
This is reflection of an existing assignment, never path completion. -/
theorem Labelling.before_lambda_body {pre : List (Endpoint g)} (node : N) (ctx body : Port (g.label node).sort)
    (sort : (g.label node).sort=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    {a b : Context} (labels : Labelling g (pre++[.inl ⟨node,body⟩]) a b) (nonempty : pre≠[]) :
    Labelling g pre a b ∧pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)) := by
  obtain ⟨previous,middle,finish,before,turn⟩ := last_turn labels nonempty
  obtain ⟨port,arrives,rule⟩ := turn.reverse.from_node node body rfl
  obtain ⟨portEq,contexts⟩ := body_predecessor sort ctxRole bodyRole rule.reverse
  subst port
  subst middle
  have wired := congrArg g.wire.mate arrives
  rw [Pairing.involutive] at wired
  exact ⟨before,finish.trans (congrArg some wired)⟩
end Body
end Lamping.AG

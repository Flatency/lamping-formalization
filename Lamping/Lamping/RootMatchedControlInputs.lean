import Lamping.Lamping.RootPathInputs
import Lamping.Lamping.MatchedControlInputs
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
private theorem app_fun_rule (actual : Label signature) (ctx funPort : Port actual.sort) (index : Nat)
    (lab : actual=label .app index) (ctxRole : HEq ctx appCtx)
    (funRole : HEq funPort (Sum.inl () : Port (.op .app))) (a : Context) :
    Traversal actual.index actual.sort ctx funPort a a := by
  subst actual
  have ctxEq : ctx=appCtx := eq_of_heq ctxRole
  have funEq : funPort=.inl () := eq_of_heq funRole
  subst ctx
  subst funPort
  exact .direct (.appFun a)

/-- Choose the syntax function child ONCE. Any new given parent assignment
is the input of the SAME child's actual typed function suffix. Full labels
are supplied by source RootInputs, and the seam equality follows from the actual
application's identity turn and deterministic prefix labelling. -/
theorem Matches.function_child_input_root {t : Term} (matching : Matches g root t)
    (rootInputs : RootInputs g root) (parent : RootAccess g root)
    (node : N) (ctx funPort : Port (g.label node).sort) (index : Nat)
    (lab : g.label node=label .app index) (ctxRole : HEq ctx appCtx)
    (funRole : HEq funPort (Sum.inl () : Port (.op .app)))
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩))) :
    ∃ (child : RootAccess g root) (tail : List (Endpoint g)),
      child.val=parent.val++(.inl ⟨node,funPort⟩)::tail ∧
      accessWord g child.val=accessWord g parent.val++[.fn] ∧
      (∃ kind,accessKind g ((.inl ⟨node,funPort⟩)::tail)=some kind) ∧
      ∀ requested seam : Context,Labelling g parent.val requested seam →
        ∃ output,Labelling g child.val requested output ∧
          Labelling g ((.inl ⟨node,funPort⟩)::tail) seam output := by
  obtain ⟨child,tail,split,word⟩ := matching.function_child_access parent node ctx funPort index lab ctxRole funRole finish
  have suffixKind : ∃ kind,accessKind g ((.inl ⟨node,funPort⟩)::tail)=some kind := by
    have typed := child.property.2.2
    have last : child.val.getLast?=((.inl ⟨node,funPort⟩)::tail).getLast? := by
      rw [split,List.getLast?_append]
      cases tail with
      | nil => rfl
      | cons e tail => simp only [List.getLast?_cons,Option.some_or]
    simpa only [accessKind,last] using typed
  refine ⟨child,tail,split,word,suffixKind,?_⟩
  intro requested seam parentLabels
  obtain ⟨output,childLabels⟩ := rootInputs.access child requested
  have labels := childLabels
  rw [split] at labels
  obtain ⟨actual,prefixLabels,suffixLabels⟩ := labels.split_segment
  have identity : ExpandedLabelling g (parent.val++[.inl ⟨node,funPort⟩]) requested seam :=
    parentLabels.expanded.splice finish (.single _ seam) rfl (by
      simpa only [Pairing.involutive] using ExpandedTurn.ordinary
        (LabelledTurn.node (g:=g) node ctx funPort (app_fun_rule _ ctx funPort index lab ctxRole funRole seam)))
  have same := prefixLabels.expanded.output_unique identity
  rw [same] at suffixLabels
  exact ⟨output,childLabels,suffixLabels⟩
end

private theorem app_principal_role (op : Op) (same : op=.app) :
    HEq (Sum.inl () : Port (.op op)) (Sum.inl () : Port (.op .app)) := by
  subst op; rfl

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- The actual syntax function child fixes ONE control auxiliary for all
assignments of the given passive application prefix. The reference child
and its finite principal suffix are chosen once, before the new inputs. -/
theorem PathSite.matched_control_inputs_root {root : B} {t : Term}
    (matching : Matches site.net root t) (rootInputs : RootInputs site.net root)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (passive : s.passive=.app)
    (parent : RootAccess site.net root) (ctx : Port (.op s.passive)) (ctxRole : HEq ctx appCtx)
    (finish : parent.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),ctx⟩))) :
    ∃ q : Aux s.active,∀ requested seam : Context,Labelling site.net parent.val requested seam →
      ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr q) seam middle := by
  have lab : site.net.label (.inr (.inr ()))=label .app s.high := by
    change label s.passive s.high=label .app s.high
    rw [passive]
  have funRole : HEq (Sum.inl () : Port (.op s.passive)) (Sum.inl () : Port (.op .app)) := by
    exact app_principal_role s.passive passive
  obtain ⟨child,tail,_,_,typed,inputs⟩ := matching.function_child_input_root rootInputs parent (.inr (.inr ()))
    ctx (.inl ()) s.high lab ctxRole funRole finish
  obtain ⟨referenceInput,referenceSeam,referenceParent⟩ := parent.property.1.1
  obtain ⟨referenceOutput,_,referenceSuffix⟩ := inputs referenceInput referenceSeam referenceParent
  obtain ⟨q,uniform⟩ := site.typed_active_control_uniform control referenceSuffix typed rfl
  refine ⟨q,?_⟩
  intro requested seam parentLabels
  obtain ⟨output,_,suffixLabels⟩ := inputs requested seam parentLabels
  exact uniform seam output suffixLabels

/-- A supplied real inverse-control passage identifies the fixed auxiliary
above with the caller's original RHS branch, so constructor stability holds
on that very branch for every new parent assignment. -/
theorem PathSite.matched_control_input_root {root : B} {t : Term}
    (matching : Matches site.net root t) (rootInputs : RootInputs site.net root)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (passive : s.passive=.app)
    (parent : RootAccess site.net root) (ctx : Port (.op s.passive)) (ctxRole : HEq ctx appCtx)
    (finish : parent.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),ctx⟩)))
    (q : Aux s.active) (referenceInput referenceSeam referenceOutput : Context)
    (referenceParent : Labelling site.net parent.val referenceInput referenceSeam)
    (reference : Traversal s.low (.op s.active) (.inl ()) (.inr q) referenceSeam referenceOutput) :
    ∀ requested seam : Context,Labelling site.net parent.val requested seam →
      ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr q) seam middle := by
  obtain ⟨chosen,uniform⟩ := site.matched_control_inputs_root matching rootInputs control passive parent ctx ctxRole finish
  obtain ⟨middle,atReference⟩ := uniform referenceInput referenceSeam referenceParent
  have same := atReference.control_auxiliary_unique control reference
  subst chosen
  exact uniform

private theorem app_ctx_observed (actual : Label signature) (index : Nat) (ctx : Port actual.sort)
    (lab : actual=label .app index) (role : HEq ctx appCtx) : portKind actual.sort ctx=some .app := by
  subst actual
  have same : ctx=appCtx := eq_of_heq role
  subst ctx
  rfl

/-- Caller interface for a supplied actual labelled root prefix. Structural
flow derives its ordinary forward direction and the actual endpoint gives
its proper observation, so no RootAccess certificate is demanded of callers. -/
theorem PathSite.matched_control_input_of_prefix_root {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (rootInputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (rootPolarity : boundary root=true)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (passive : s.passive=.app)
    (pre : List (Endpoint site.net)) (ctx : Port (.op s.passive)) (ctxRole : HEq ctx appCtx)
    (referenceInput referenceSeam referenceOutput : Context)
    (referenceParent : Labelling site.net pre referenceInput referenceSeam)
    (rooted : pre.head?=some (.inr (.inl root)))
    (finish : pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),ctx⟩)))
    (q : Aux s.active)
    (reference : Traversal s.low (.op s.active) (.inl ()) (.inr q) referenceSeam referenceOutput) :
    ∀ requested seam : Context,Labelling site.net pre requested seam →
      ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr q) seam middle := by
  have lab : site.net.label (.inr (.inr ()))=label .app s.high := by
    change label s.passive s.high=label .app s.high
    rw [passive]
  have kind : accessKind site.net pre=some .app := by
    unfold accessKind
    rw [finish]
    simp only [Option.bind_some,Pairing.involutive]
    exact app_ctx_observed _ s.high ctx lab ctxRole
  let parent : RootAccess site.net root :=
    ⟨pre,⟨⟨⟨referenceInput,referenceSeam,referenceParent⟩,
      referenceParent.root_forward_of_flow flow root rooted rootPolarity⟩,rooted,⟨.app,kind⟩⟩⟩
  exact site.matched_control_input_root matching rootInputs control passive parent ctx ctxRole finish q
    referenceInput referenceSeam referenceOutput referenceParent reference
end
end Lamping.AG




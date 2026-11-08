import Lamping.Lamping.ActionLambdaOccurrences
import Lamping.Lamping.ControlShellEmbeddings
namespace Lamping.AG
open Graph

/-- The actual copied proper node associated with an active auxiliary.
Only the three schema node constructors occur, with no semantic fields. -/
inductive ActionLambdaCopy {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Label signature} : {s : Schema} →
    (site : PathSite s kept (B:=B) (W:=W) (V:=V)) → Aux s.active → s.right.N → Prop where
  | fan {f i j lt} (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V)) (branch : Bool) :
      ActionLambdaCopy site branch (.inl branch)
  | cro {f i j lt} (site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V)) :
      ActionLambdaCopy site () (.inl ())
  | bra {f i j lt} (site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V)) :
      ActionLambdaCopy site () (.inl ())

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

theorem ActionLambdaCross.canonical {principal : SiteActionPrincipal site} {aux inside old}
    (cross : ActionLambdaCross site principal aux inside old) : ActionCanonicalLocal site principal inside old := by
  cases cross with
  | fan principal branch q => exact .fan (.cross branch q)
  | @cro f i j lt actual principal q =>
    exact .cro (UnaryCanonicalLocal.cross (site:=actual) (principal:=principal) q)
  | @bra f i j lt actual principal q =>
    exact .bra (UnaryCanonicalLocal.cross (site:=actual) (principal:=principal) q)

theorem ActionLambdaCross.source_length {principal : SiteActionPrincipal site} {aux inside old}
    (cross : ActionLambdaCross site principal aux inside old) : 2≤old.length := by
  cases cross <;> simp only [SiteActionPrincipal.crossing,List.length_cons,List.length_append,List.length_nil] <;> omega

theorem ActionLambdaCopy.unique {branch : Aux s.active} {left right : s.right.N}
    (first : ActionLambdaCopy site branch left) (second : ActionLambdaCopy site branch right) : left=right := by
  cases first <;> cases second <;> rfl

/-- Read the genuine low writer from a forward lambda-body crossing. The
copied lambda ctx→body passage is identity, so the writer's input is exactly
the context at its new context prefix, not a newly chosen shell witness. -/
theorem ActionLambdaCross.body_writer {principal : SiteActionPrincipal site} {aux : Aux s.passive} {inside old}
    (cross : ActionLambdaCross site principal aux inside old) (lam : s.passive=.lam)
    (bodyRole : HEq (Sum.inr aux : Port (.op s.passive)) lamBody)
    {a b : Context} (labels : Labelling s.right.net inside a b) :
    ∃ (branch : Aux s.active) (node : s.right.N) (ctx body : Port (s.right.net.label node).sort)
      (tail : List (Endpoint s.right.net)),
      ActionLambdaCopy site branch node ∧
      (s.right.net.label node).sort=.op .lam ∧
      HEq ctx (Sum.inl () : Port (.op .lam)) ∧HEq body lamBody ∧
      inside=s.right.net.wire (.inl ⟨node,ctx⟩)::(.inl ⟨node,body⟩)::tail ∧
      Traversal s.low (.op s.active) (.inr branch) (.inl ()) a b := by
  cases cross with
  | @fan f i j lt actual principal branch q =>
    change f=.lam at lam
    subst f
    have same : q=true := Sum.inr.inj (eq_of_heq bodyRole)
    subst q
    refine ⟨branch,.inl branch,.inl (),lamBody,[.inl ⟨.inr true,.inl ()⟩],.fan actual branch,rfl,HEq.rfl,HEq.rfl,rfl,?_⟩
    cases labels with
    | @cons _ _ _ _ middle _ first after =>
      cases first with
      | node node p q rule =>
        have same : a=middle := rule.proper_context
        subst middle
        cases after with
        | cons last done => cases done; cases last with | node node p q rule => exact rule
  | @cro f i j lt actual principal q =>
    change f=.lam at lam
    subst f
    have same : q=true := Sum.inr.inj (eq_of_heq bodyRole)
    subst q
    refine ⟨(),.inl (),.inl (),lamBody,[.inl ⟨.inr true,.inl ()⟩],.cro actual,rfl,HEq.rfl,HEq.rfl,rfl,?_⟩
    cases labels with
    | @cons _ _ _ _ middle _ first after =>
      cases first with
      | node node p q rule =>
        have same : a=middle := rule.proper_context
        subst middle
        cases after with
        | cons last done => cases done; cases last with | node node p q rule => exact rule
  | @bra f i j lt actual principal q =>
    change f=.lam at lam
    subst f
    have same : q=true := Sum.inr.inj (eq_of_heq bodyRole)
    subst q
    refine ⟨(),.inl (),.inl (),lamBody,[.inl ⟨.inr true,.inl ()⟩],.bra actual,rfl,HEq.rfl,HEq.rfl,rfl,?_⟩
    cases labels with
    | @cons _ _ _ _ middle _ first after =>
      cases first with
      | node node p q rule =>
        have same : a=middle := rule.proper_context
        subst middle
        cases after with
        | cons last done => cases done; cases last with | node node p q rule => exact rule

/-- Reflect the old binder shell through the two ACTUAL low passages. Fan
reflection also identifies the same physical copy; cro/bra transport the
shell to their changed copied index. -/
theorem ActionLambdaCopy.binding_shell {firstBranch lastBranch : Aux s.active} {firstNode lastNode : s.right.N}
    (firstCopy : ActionLambdaCopy site firstBranch firstNode) (lastCopy : ActionLambdaCopy site lastBranch lastNode)
    {newMiddle oldMiddle oldOutput newOutput : Context}
    (writer : Traversal s.low (.op s.active) (.inr firstBranch) (.inl ()) newMiddle oldMiddle)
    (inverse : Traversal s.low (.op s.active) (.inl ()) (.inr lastBranch) oldOutput newOutput)
    (shell : Context.SameShell s.high oldMiddle oldOutput) :
    firstNode=lastNode ∧Context.SameShell (s.right.net.label firstNode).index newMiddle newOutput := by
  cases firstCopy with
  | @fan f i j lt actual firstBranch =>
    cases lastCopy with
    | fan actual lastBranch =>
      have firstEq := writer.output_unique (.direct (InitialOffsets.Event.apply_rel (.fan i firstBranch) newMiddle))
      have lastEq := inverse.reverse.output_unique (.direct (InitialOffsets.Event.apply_rel (.fan i lastBranch) newOutput))
      change oldMiddle=InitialOffsets.fanAt i firstBranch newMiddle at firstEq
      change oldOutput=InitialOffsets.fanAt i lastBranch newOutput at lastEq
      rw [firstEq,lastEq] at shell
      obtain ⟨same,underlying⟩ := (InitialOffsets.fanAt_same_shell_iff newMiddle newOutput i j lt firstBranch lastBranch).mp shell
      exact ⟨congrArg Sum.inl same,underlying⟩
  | @cro f i j lt actual =>
    cases lastCopy with
    | cro actual =>
      have firstEq := writer.output_unique (.direct (InitialOffsets.Event.apply_rel (.cro i) newMiddle))
      have lastEq := inverse.reverse.output_unique (.direct (InitialOffsets.Event.apply_rel (.cro i) newOutput))
      change oldMiddle=InitialOffsets.croAt i newMiddle at firstEq
      change oldOutput=InitialOffsets.croAt i newOutput at lastEq
      rw [firstEq,lastEq] at shell
      exact ⟨rfl,(InitialOffsets.croAt_same_shell_iff newMiddle newOutput i j lt).mp shell⟩
  | @bra f i j lt actual =>
    cases lastCopy with
    | bra actual =>
      have firstEq := writer.output_unique (.direct (InitialOffsets.Event.apply_rel (.bra i) newMiddle))
      have lastEq := inverse.reverse.output_unique (.direct (InitialOffsets.Event.apply_rel (.bra i) newOutput))
      change oldMiddle=InitialOffsets.braAt i newMiddle at firstEq
      change oldOutput=InitialOffsets.braAt i newOutput at lastEq
      rw [firstEq,lastEq] at shell
      exact ⟨rfl,(InitialOffsets.braAt_same_shell_iff newMiddle newOutput i j lt).mp shell⟩
end
end Lamping.AG

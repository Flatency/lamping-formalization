import Lamping.Lamping.MatchingBetaRootVisibility
import Lamping.Lamping.SourceControlWriterSuffix
import Lamping.Lamping.MatchingVariableAccess
namespace Lamping.AG
open Graph Lambda
private def AppPrincipalConstraint : (kind : Kind) → Port kind → Port kind → Prop
  | .op .app,.inl _,q => q=appCtx
  | _,_,_ => True
private theorem principal_constraint {level kind p q a b}
    (rule : Traversal level kind p q a b) : AppPrincipalConstraint kind p q := by
  cases rule with
  | direct passage => cases passage <;> trivial
  | inverse passage => cases passage <;> trivial
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- A supplied rooted access to the actual beta lambda context already
contains the application context prefix. Reverse only the given finite
principal suffix; the real application traversal forces its context port. -/
theorem PathSite.beta_lambda_access_predecessor
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (child : RootAccess site.net root)
    (finish : child.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) :
    ∃ parent : RootAccess site.net root,
      parent.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),appCtx⟩)) ∧
      ∃ tail,child.val=parent.val++tail := by
  obtain ⟨a,b,labels⟩ := child.property.1.1
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨pre,q,middle,split,rooted,last,before,rule⟩ :=
    site.rooted_control_writer_suffix principal labels root child.property.2.1 finish
  have context : q=false := by
    have same : (Sum.inr q : Port (.op .app))=appCtx := principal_constraint rule.reverse
    exact Sum.inr.inj same
  subst q
  have kind : accessKind site.net pre=some .app := by
    simp only [accessKind,last,Option.bind_some,Pairing.involutive]
    rfl
  have forward := before.root_forward_of_flow flow root rooted positive
  exact ⟨⟨pre,⟨⟨⟨a,middle,before⟩,forward⟩,rooted,⟨.app,kind⟩⟩⟩,last,principal.edges,split⟩

theorem PathSite.empty_betaSyntaxFiber_not_lambda_visible
    {root : B} {t : Term} (matching : Matches site.net root t)
    {directions : B → Bool} (flow : FlowBalance site.net directions) (positive : directions root=true)
    (empty : site.betaSyntaxFiber root t=[]) (child : RootAccess site.net root)
    (finish : child.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) : False := by
  obtain ⟨parent,parentLast,_prefix⟩ := site.beta_lambda_access_predecessor flow root positive child finish
  exact site.empty_betaSyntaxFiber_not_visible matching flow positive empty parent parentLast

/-- Source T supplies the literal binder prefix of a supplied binding access.
Consequently an empty old fiber also excludes the distinguished lambda's
binding endpoint, without claiming that arbitrary garbage paths are rooted. -/
theorem PathSite.empty_betaSyntaxFiber_not_binding_visible
    {root : B} {t : Term} (matching : Matches site.net root t)
    {directions : B → Bool} (flow : FlowBalance site.net directions) (positive : directions root=true)
    (oldT : Transparency site.net root) (empty : site.betaSyntaxFiber root t=[])
    (child : RootAccess site.net root)
    (finish : child.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),lamBind⟩))) : False := by
  obtain ⟨a,b,labels⟩ := child.property.1.1
  obtain ⟨pre,loop,middle,binding,split,binderEq,last,before⟩ := oldT
    child.val a b (.inr (.inr ())) (.inl ()) lamBody lamBind rfl HEq.rfl HEq.rfl HEq.rfl
      child.property.2.1 finish child.property.1.2 labels
  have nonempty : pre≠[] := by intro empty; rw [empty] at last; cases last
  have rooted : pre.head?=some (.inr (.inl root)) := by
    cases eqs : pre with
    | nil => exact False.elim (nonempty eqs)
    | cons e es => simpa only [split,eqs,List.cons_append,List.head?_cons] using child.property.2.1
  have kind : accessKind site.net pre=some .lam := by
    simp only [accessKind,last,Option.bind_some,Pairing.involutive]
    rfl
  let parent : RootAccess site.net root :=
    ⟨pre,⟨⟨⟨a,middle,before⟩,before.root_forward_of_flow flow root rooted positive⟩,rooted,⟨.lam,kind⟩⟩⟩
  exact site.empty_betaSyntaxFiber_not_lambda_visible matching flow positive empty parent last
end
end Lamping.AG

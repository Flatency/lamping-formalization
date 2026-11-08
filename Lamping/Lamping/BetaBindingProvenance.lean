import Lamping.Lamping.MatchingBetaLambdaVisibility
import Lamping.Lamping.PathSiteBetaLifting
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

private theorem same_context {n m : K⊕(Unit⊕Unit)}
    {p : Port (site.net.label n).sort} {q : Port (site.net.label m).sort}
    (nodes : n=m) (left : HEq p (Sum.inl () : Port (.op .lam)))
    (right : HEq q (Sum.inl () : Port (.op .lam))) :
    (.inl ⟨n,p⟩ : Endpoint site.net)=.inl ⟨m,q⟩ := by
  subst m
  have ports : p=q := eq_of_heq (left.trans right.symm)
  cases ports
  rfl

private theorem lambda_context {kind : Kind} (shape : kind=.op .lam) :
    ∃ ctx : Port kind,HEq ctx (Sum.inl () : Port (.op .lam)) := by
  subst kind
  exact ⟨.inl (),HEq.rfl⟩

/-- The supplied principal is removed from the supplied finite lambda access.
Both the physical suffix and its single syntax token are retained. -/
theorem PathSite.beta_lambda_access_predecessor_word
    (principal : SiteActionPrincipal site)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (child : RootAccess site.net root)
    (finish : child.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) :
    ∃ parent : RootAccess site.net root,
      parent.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),appCtx⟩)) ∧
      child.val=parent.val++principal.edges ∧
      accessWord site.net child.val=accessWord site.net parent.val++[.fn] := by
  obtain ⟨a,b,labels⟩ := child.property.1.1
  obtain ⟨pre,q,middle,split,rooted,last,before,rule⟩ :=
    site.rooted_control_writer_suffix principal labels root child.property.2.1 finish
  have context : q=false := by
    have same : (Sum.inr q : Port (.op .app))=appCtx := principal_constraint rule.reverse
    exact Sum.inr.inj same
  subst q
  have kind : accessKind site.net pre=some .app := by
    simp only [accessKind,last,Option.bind_some,Pairing.involutive]
    rfl
  let parent : RootAccess site.net root :=
    ⟨pre,⟨⟨⟨a,middle,before⟩,before.root_forward_of_flow flow root rooted positive⟩,
      rooted,⟨.app,kind⟩⟩⟩
  refine ⟨parent,last,split,?_⟩
  change accessWord site.net child.val=accessWord site.net pre++[.fn]
  rw [split,accessWord_append site.net pre principal.edges before.nonempty]
  have tokens := transparent_access_tokens principal.edges _ principal.first principal.transparent
  exact congrArg (accessWord site.net pre++·) tokens

/-- Source Transparency and Matches identify an actual old-fiber redex above
the supplied binding access. The lambda occurrence, its literal loop, and the
bound-variable index are extracted together; no rooted continuation is added. -/
theorem PathSite.beta_binding_access_provenance
    (principal : SiteActionPrincipal site)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true)
    {t : Term} (matching : Matches site.net root t)
    (transparent : Transparency site.net root) (child : RootAccess site.net root)
    (finish : child.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),lamBind⟩))) :
    ∃ (redex : RedexOcc t) (parent binder : RootAccess site.net root)
      (loop : List (Endpoint site.net)) (a b c : Context)
      (binding : BindingLoop site.net loop b c),
      redex.val∈site.betaSyntaxFiber root t ∧
      redex.val=accessWord site.net parent.val ∧
      binder.val=parent.val++principal.edges ∧
      child.val=binder.val++loop ∧ binding.binder=.inr (.inr ()) ∧
      Labelling site.net binder.val a b ∧
      accessWord site.net child.val=redex.val++[.fn,.body]++accessWord site.net loop ∧
      subtermAt t (accessWord site.net child.val)=
        some (.var (binderDepth (accessWord site.net loop))) := by
  obtain ⟨a,b,labels⟩ := child.property.1.1
  obtain ⟨pre,loop,middle,binding,split,binderEq,last,before⟩ := transparent
    child.val a b (.inr (.inr ())) (.inl ()) lamBody lamBind rfl HEq.rfl HEq.rfl HEq.rfl
      child.property.2.1 finish child.property.1.2 labels
  obtain ⟨oldCtx,oldRole⟩ := lambda_context binding.isLam
  have oldPort := same_context site binderEq oldRole HEq.rfl
  have suffix : BindingSuffix site.net child.val (binderDepth (accessWord site.net loop)) :=
    ⟨pre,loop,a,middle,b,binding,oldCtx,split,oldRole,
      by rw [oldPort]; exact last,before,rfl⟩
  obtain ⟨binder,loop',a',b',c',binding',ctx,split',role,last',before',kind,words,depth⟩ :=
    child.binding_prefix suffix
  have sameBinder : binding'.binder=.inr (.inr ()) := by
    have actualEnd : child.val.getLast?=some (site.net.wire (.inl ⟨binding'.binder,binding'.bind⟩)) := by
      rw [split',List.getLast?_append,binding'.finish,Option.some_or]
    have equal := congrArg site.net.wire.mate (Option.some.inj (actualEnd.symm.trans finish))
    simp only [Pairing.involutive] at equal
    exact congrArg Sigma.fst (Sum.inl.inj equal)
  have binderFinish : binder.val.getLast?=
      some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) := by
    have portEq := same_context site sameBinder role HEq.rfl
    rw [portEq] at last'
    exact last'
  obtain ⟨parent,parentLast,lambdaSplit,lambdaWord⟩ :=
    site.beta_lambda_access_predecessor_word principal flow root positive binder binderFinish
  obtain ⟨edge,geometry⟩ := site.siteBetaGeometry_exists
  have parentFinish : parent.val.getLast?=some (site.net.wire (.inl ⟨edge.app,edge.appCtx⟩)) := by
    rw [geometry.appCtx]
    exact parentLast
  obtain ⟨redex,redexWord,member⟩ := edge.root_app_visible matching flow positive parent parentFinish
  have appEq : edge.app=.inr (.inl ()) := congrArg Sigma.fst (Sum.inl.inj geometry.appCtx)
  have lamEq : edge.lam=.inr (.inr ()) := congrArg Sigma.fst (Sum.inl.inj geometry.binding)
  have inFiber : redex.val∈site.betaSyntaxFiber root t := by
    simpa only [PathSite.betaSyntaxFiber,appEq,lamEq] using member
  have childKind : accessKind site.net child.val=some .var := by
    simp only [accessKind,finish,Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨bijection,corresponds,_⟩ := matching
  obtain ⟨word,u,lookup,observes⟩ := corresponds child
  rw [←word] at lookup
  have shape : (syntaxShape u).kind=.var := Option.some.inj (observes.1.symm.trans childKind)
  have leaf : subtermAt t (accessWord site.net child.val)=
      some (.var (binderDepth (accessWord site.net loop'))) := by
    cases u with
    | app fn arg => cases shape
    | lam body => cases shape
    | var k =>
      have index := observes.2.2 _ suffix
      rw [depth] at index
      simpa only [index] using lookup
  refine ⟨redex,parent,binder,loop',a',b',c',binding',inFiber,redexWord,
    lambdaSplit,split',sameBinder,before',?_,leaf⟩
  rw [words,lambdaWord,←redexWord]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

end
end Lamping.AG

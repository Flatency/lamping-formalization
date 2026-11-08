import Lamping.Lamping.MatchingBetaPrincipalPath
import Lamping.Lamping.ActionCanonicalWords
import Lamping.Lamping.FlowRootPaths
namespace Lamping.AG
open Graph Lambda

private theorem app_fun_rule (actual : Label signature) (ctx principal : Port actual.sort)
    (i : Nat) (lab : actual=label .app i) (ctxRole : HEq ctx appCtx)
    (funRole : HEq principal (Sum.inl () : Port (.op .app))) (a : Context) :
    Traversal actual.index actual.sort ctx principal a a := by
  subst actual
  have hc : ctx=appCtx := eq_of_heq ctxRole
  have hf : principal=.inl () := eq_of_heq funRole
  subst ctx; subst principal
  exact .direct (.appFun a)

private theorem port_kind (actual : Label signature) (op : Op) (i : Nat)
    (p : Port actual.sort) (q : Port (.op op)) (lab : actual=label op i) (role : HEq p q) :
    portKind actual.sort p=portKind (.op op) q := by
  subst actual
  have same : p=q := eq_of_heq role
  subst p; rfl

private theorem fun_token (actual : Label signature) (p : Port actual.sort) (i : Nat)
    (lab : actual=label .app i) (role : HEq p (Sum.inl () : Port (.op .app))) :
    (match actual.sort,p with
    | .op .app,.inl () => [Step.fn]
    | .op .app,.inr true => [Step.arg]
    | .op .lam,.inr true => [Step.body]
    | _,_ => [])=[Step.fn] := by
  subst actual
  have same : p=.inl () := eq_of_heq role
  subst p; rfl

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {t : Term}

/-- A visible application of an actual beta edge is a real syntax redex
in that edge's physical fiber. Its lambda child is constructed by splicing
the given parent with the already supplied finite transparent principal path. -/
theorem BetaEdge.root_app_visible (beta : BetaEdge g) (matching : Matches g root t)
    {directions : B → Bool} (flow : FlowBalance g directions) (positive : directions root=true)
    (parent : RootAccess g root)
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩))) :
    ∃ redex : RedexOcc t,redex.val=accessWord g parent.val ∧
      redex.val∈physicalBetaFiberPaths g root t beta.app beta.lam := by
  obtain ⟨a,b,parentLabels⟩ := parent.property.1.1
  have nonempty : beta.principal≠[] := by
    intro empty
    have first := beta.principalStart
    rw [empty] at first
    cases first
  have routeLabels := transparent_route_labelling g beta.principal nonempty beta.transparent b
  obtain ⟨pre,parentSplit⟩ := List.getLast?_eq_some_iff.mp finish
  obtain ⟨tail,routeSplit⟩ := List.head?_eq_some_iff.mp beta.principalStart
  have left : Labelling g (pre++[g.wire (.inl ⟨beta.app,beta.appCtx⟩)]) a b := by
    simpa only [parentSplit] using parentLabels
  have right : Labelling g ((.inl ⟨beta.app,beta.appFun⟩)::tail) b b := by
    simpa only [routeSplit] using routeLabels
  have seam : LabelledTurn g (g.wire (g.wire (.inl ⟨beta.app,beta.appCtx⟩)))
      (.inl ⟨beta.app,beta.appFun⟩) b b := by
    rw [Pairing.involutive]
    exact .node beta.app beta.appCtx beta.appFun
      (app_fun_rule _ _ _ _ beta.appLabel beta.appCtx_role beta.appFun_role b)
  have childLabels : Labelling g (parent.val++beta.principal) a b := by
    simpa only [parentSplit,routeSplit,List.append_assoc,List.singleton_append] using left.splice right seam
  have childHead : (parent.val++beta.principal).head?=some (.inr (.inl root)) := by
    cases eqs : parent.val with
    | nil => have old := parent.property.2.1; rw [eqs] at old; cases old
    | cons e es => simpa only [eqs,List.cons_append,List.head?_cons] using parent.property.2.1
  have childLast : (parent.val++beta.principal).getLast?=some (g.wire (.inl ⟨beta.lam,beta.lamCtx⟩)) := by
    rw [List.getLast?_append,beta.principalEnd,Option.some_or]
  have childKind : accessKind g (parent.val++beta.principal)=some .lam := by
    simp only [accessKind,childLast,Option.bind_some,Pairing.involutive]
    exact port_kind _ .lam _ _ (.inl ()) beta.lamLabel beta.lamCtx_role
  let child : RootAccess g root :=
    ⟨parent.val++beta.principal,⟨⟨⟨a,b,childLabels⟩,
      childLabels.root_forward_of_flow flow root childHead positive⟩,childHead,⟨.lam,childKind⟩⟩⟩
  have routeTokens := transparent_access_tokens beta.principal _ beta.principalStart beta.transparent
  have token : arrivalWord g (.inl ⟨beta.app,beta.appFun⟩)=[.fn] :=
    fun_token _ _ _ beta.appLabel beta.appFun_role
  rw [token] at routeTokens
  have childWord : accessWord g child.val=accessWord g parent.val++[.fn] := by
    exact (accessWord_append g parent.val beta.principal parentLabels.nonempty).trans
      (congrArg (fun tokens => accessWord g parent.val++tokens) routeTokens)
  have parentKind : accessKind g parent.val=some .app := by
    simp only [accessKind,finish,Option.bind_some,Pairing.involutive]
    exact port_kind _ .app _ _ AG.appCtx beta.appLabel beta.appCtx_role
  have injective := matching.accessWord_injective
  obtain ⟨map,corresponds,_prefix⟩ := matching
  obtain ⟨parentWord,u,parentLookup,parentObserved⟩ := corresponds parent
  obtain ⟨childPosition,v,childLookup,childObserved⟩ := corresponds child
  have parentShape : (syntaxShape u).kind=.app := Option.some.inj (parentObserved.1.symm.trans parentKind)
  have childShape : (syntaxShape v).kind=.lam := Option.some.inj (childObserved.1.symm.trans childKind)
  have lookupParent : subtermAt t (accessWord g parent.val)=some u := by rw [parentWord]; exact parentLookup
  have lookupChild : subtermAt t (accessWord g parent.val++[.fn])=some v := by
    rw [←childWord,childPosition]; exact childLookup
  cases u with
  | var index => cases parentShape
  | lam body => cases parentShape
  | app function argument =>
    cases v with
    | var index => cases childShape
    | app fn arg => cases childShape
    | lam body =>
      rw [subtermAt_append,lookupParent] at lookupChild
      have fnEq : function=.lam body := Option.some.inj
        (by simpa only [Option.bind_some,subtermAt] using lookupChild)
      subst function
      let redex : RedexOcc t := ⟨accessWord g parent.val,_,lookupParent,trivial⟩
      have restoredMatching : Matches g root t := ⟨map,corresponds,_prefix⟩
      obtain ⟨source⟩ := restoredMatching.actual_redex_access redex
      have parents : source.parent=parent := injective source.parentWord
      have children : source.child=child := injective (source.childWord.trans childWord.symm)
      have sameApp : source.connection.app=beta.app := by
        have eqs := congrArg g.wire.mate (Option.some.inj
          (source.parentFinish.symm.trans (parents ▸ finish)))
        simp only [Pairing.involutive] at eqs
        exact congrArg Sigma.fst (Sum.inl.inj eqs)
      have sourceLast : source.child.val.getLast?=
          some (g.wire (.inl ⟨source.connection.lam,source.connection.lamPort⟩)) := by
        rw [source.split,List.getLast?_append,source.connection.finish]
        rfl
      have sameLam : source.connection.lam=beta.lam := by
        have actualLast : child.val.getLast?=some (g.wire (.inl ⟨beta.lam,beta.lamCtx⟩)) := childLast
        have eqs := congrArg g.wire.mate (Option.some.inj (sourceLast.symm.trans (children ▸ actualLast)))
        simp only [Pairing.involutive] at eqs
        exact congrArg Sigma.fst (Sum.inl.inj eqs)
      exact ⟨redex,rfl,(mem_physicalBetaFiberPaths g root t beta.app beta.lam redex.val).mpr
        ⟨redex,source,rfl,sameApp,sameLam⟩⟩

theorem BetaEdge.empty_fiber_not_visible (beta : BetaEdge g) (matching : Matches g root t)
    {directions : B → Bool} (flow : FlowBalance g directions) (positive : directions root=true)
    (empty : physicalBetaFiberPaths g root t beta.app beta.lam=[])
    (parent : RootAccess g root)
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩))) : False := by
  obtain ⟨redex,_word,member⟩ := beta.root_app_visible matching flow positive parent finish
  rw [empty] at member
  cases member
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}

/-- The empty OLD syntax fiber excludes root visibility of the actual
distinguished application context. It does not by itself assert that the
whole rewrite is invisible or that target Matches has been preserved. -/
theorem PathSite.empty_betaSyntaxFiber_not_visible
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {t : Term} (matching : Matches site.net root t)
    {directions : B → Bool} (flow : FlowBalance site.net directions) (positive : directions root=true)
    (empty : site.betaSyntaxFiber root t=[]) (parent : RootAccess site.net root)
    (finish : parent.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),appCtx⟩))) : False := by
  obtain ⟨beta,app,lam⟩ := site.distinguished_betaEdge_exists
  have endpoint : (.inl ⟨beta.app,beta.appCtx⟩ : Endpoint site.net)=.inl ⟨.inr (.inl ()),appCtx⟩ := by
    apply congrArg Sum.inl
    exact Sigma.ext app beta.appCtx_role
  have betaFinish : parent.val.getLast?=some (site.net.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
    rw [endpoint]; exact finish
  have betaEmpty : physicalBetaFiberPaths site.net root t beta.app beta.lam=[] := by
    simpa only [app,lam,PathSite.betaSyntaxFiber] using empty
  exact beta.empty_fiber_not_visible matching flow positive betaEmpty parent betaFinish
end
end Lamping.AG

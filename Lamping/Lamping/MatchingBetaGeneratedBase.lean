import Lamping.Lamping.MatchingRedexBodyLoop
import Lamping.Lamping.MatchingSourceEdges
import Lamping.Lamping.MatchingBetaPrincipalPath
import Lamping.Lamping.GeneratedExpandedLoops
namespace Lamping.AG
open Graph Lambda
private theorem argument_ports {kind : Kind} {ctx departure : Port kind}
    (roles : SyntaxChildPorts kind ctx departure .arg) :
    HEq ctx appCtx ∧HEq departure appArg := by
  cases roles
  exact ⟨HEq.rfl,HEq.rfl⟩
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
private theorem same_role_endpoint {T : Type} {canonical : T} {n m : N}
    {p : Port (g.label n).sort} {q : Port (g.label m).sort}
    (nodes : n=m) (left : HEq p canonical) (right : HEq q canonical) :
    (.inl ⟨n,p⟩ : Endpoint g)=.inl ⟨m,q⟩ := by
  subst m
  have ports := eq_of_heq (left.trans right.symm)
  cases ports
  rfl

/-- Ordinary source Matches supplies BOTH generated premises on the SAME
literal application prefix, and its actual binding loop. The beta route is
fixed physically; no generatedness, binding witness or common-prefix field
is required from the caller. This is the original-syntax insertion base. -/
theorem ActualRedexAccess.generated_binding_insert_base
    {t : Term} {redex : RedexOcc t} (source : ActualRedexAccess g root redex)
    (matching : Matches g root t) (beta : BetaEdge g)
    (app : source.connection.app=beta.app) (lam : source.connection.lam=beta.lam)
    (principal : source.connection.edges=beta.principal)
    {body argument : Term} (lookup : subtermAt t redex.val=some (.app (.lam body) argument))
    (p : Path) (variableLookup : subtermAt body p=some (.var (binderDepth p))) :
    ∃ (arg leaf : RootAccess g root) (loop suffix : List (Endpoint g)) (a b : Context)
      (binding : BindingLoop g loop a b),
      arg.val=source.parent.val++beta.argEnd::suffix ∧
      leaf.val=source.parent.val++beta.principal++loop ∧
      accessWord g arg.val=redex.val++[.arg] ∧accessWord g loop=p ∧binding.binder=beta.lam ∧
      GeneratedExpandedProperPath g root (source.parent.val++beta.argEnd::suffix) ∧
      GeneratedExpandedProperPath g root (source.parent.val++beta.principal++loop) ∧
      GeneratedExpandedProperPath g root
        (source.parent.val++beta.principal++loop++beta.reverseRoute++[beta.argEnd]++suffix) := by
  obtain ⟨leaf,loop,initial,a,b,binding,_leafWord,leafSplit,binderEq,loopWord,_childLabels⟩ :=
    source.bound_body_loop matching lookup p variableLookup
  have argLookup : subtermAt t (redex.val++[.arg])=some argument := by
    simp only [subtermAt_append,lookup,Option.bind_some,subtermAt]
  let argumentPosition : Position t := ⟨redex.val++[.arg],by rw [argLookup]; rfl⟩
  obtain ⟨arg,argWord,_⟩ := Matches.observation g matching argumentPosition
  obtain ⟨node,ctx,departure,suffix,roles,finish,argSplit,_forward,_assignments⟩ :=
    matching.syntax_child_fragment source.parent arg .arg (by rw [argWord,source.parentWord])
  obtain ⟨ctxRole,departureRole⟩ := argument_ports roles
  have wires := Option.some.inj (finish.symm.trans source.parentFinish)
  have endpoints := congrArg g.wire.mate wires
  simp only [Pairing.involutive] at endpoints
  have nodeEq : node=source.connection.app := congrArg Sigma.fst (Sum.inl.inj endpoints)
  have departureEq : (.inl ⟨node,departure⟩ : Endpoint g)=beta.argEnd :=
    same_role_endpoint (nodeEq.trans app) departureRole beta.appArg_role
  have actualArg : arg.val=source.parent.val++beta.argEnd::suffix := by
    simpa only [departureEq] using argSplit
  have actualBody : leaf.val=source.parent.val++beta.principal++loop := by
    rw [leafSplit,source.split,principal]
  have sameBinder : binding.binder=beta.lam := binderEq.trans lam
  have contextEq := same_role_endpoint (g:=g) app source.contextPrincipal beta.appCtx_role
  have preEnd : source.parent.val.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
    rw [←contextEq]
    exact source.parentFinish
  have bodyEq := same_role_endpoint (g:=g) sameBinder binding.body_role beta.lamBody_role
  have bindEq := same_role_endpoint (g:=g) sameBinder binding.bind_role beta.lamBind_role
  have loopStart : loop.head?=some (.inl ⟨beta.lam,beta.lamBody⟩) := binding.start.trans (congrArg some bodyEq)
  have loopEnd : loop.getLast?=some (g.wire (.inl ⟨beta.lam,beta.lamBind⟩)) :=
    binding.finish.trans (congrArg (fun e => some (g.wire e)) bindEq)
  have argGenerated : GeneratedExpandedProperPath g root (source.parent.val++beta.argEnd::suffix) := by
    rw [←actualArg]
    exact .base arg.property.1 arg.property.2.1
  have bodyGenerated : GeneratedExpandedProperPath g root (source.parent.val++beta.principal++loop) := by
    rw [←actualBody]
    exact .base leaf.property.1 leaf.property.2.1
  exact ⟨arg,leaf,loop,suffix,a,b,binding,actualArg,actualBody,argWord,loopWord,sameBinder,argGenerated,bodyGenerated,
    .insert beta source.parent.val loop suffix argGenerated bodyGenerated preEnd loopStart loopEnd a b binding sameBinder⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}

/-- A fixed actual graph beta site constructs this insertion for every real
old fiber redex and original body variable bound by its lambda. Its actual
principal route and rich source accesses are derived from Matches/fiber
membership, not supplied as semantic or generation certificates. -/
theorem PathSite.beta_fiber_generated_insert_base
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {t : Term} (matching : Matches site.net root t) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧beta.lam=.inr (.inr ()) ∧
      ∀ (redex : RedexOcc t),redex.val∈site.betaSyntaxFiber root t →
      ∀ {body argument},subtermAt t redex.val=some (.app (.lam body) argument) →
      ∀ p,subtermAt body p=some (.var (binderDepth p)) →
      ∃ (pre loop suffix : List (Endpoint site.net)) (a b : Context)
        (binding : BindingLoop site.net loop a b),binding.binder=beta.lam ∧
        accessWord site.net pre=redex.val ∧accessWord site.net loop=p ∧
        GeneratedExpandedProperPath site.net root (pre++beta.argEnd::suffix) ∧
        GeneratedExpandedProperPath site.net root (pre++beta.principal++loop) ∧
        GeneratedExpandedProperPath site.net root
          (pre++beta.principal++loop++beta.reverseRoute++[beta.argEnd]++suffix) := by
  obtain ⟨beta,app,lam,allSources⟩ := site.beta_fiber_principal matching
  refine ⟨beta,app,lam,?_⟩
  intro redex member body argument lookup p variableLookup
  obtain ⟨source⟩ := matching.actual_redex_access redex
  have physical := (source.physical_selection_iff site.net root t (.inr (.inl ())) (.inr (.inr ())) matching).mp member
  obtain ⟨arg,leaf,loop,suffix,a,b,binding,_argEq,_bodyEq,_argWord,loopWord,sameBinder,argGenerated,bodyGenerated,inserted⟩ :=
    source.generated_binding_insert_base matching beta (physical.1.trans app.symm) (physical.2.trans lam.symm)
      (allSources redex source member) lookup p variableLookup
  exact ⟨source.parent.val,loop,suffix,a,b,binding,sameBinder,source.parentWord,loopWord,argGenerated,bodyGenerated,inserted⟩
end
end Lamping.AG


import Lamping.Lamping.MatchingBetaGeneratedBase
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
private theorem same_port_endpoint {T : Type} {canonical : T} {n m : N}
    {p : Port (g.label n).sort} {q : Port (g.label m).sort}
    (nodes : n=m) (left : HEq p canonical) (right : HEq q canonical) :
    (.inl ⟨n,p⟩ : Endpoint g)=.inl ⟨m,q⟩ := by
  subst m
  have ports := eq_of_heq (left.trans right.symm)
  cases ports
  rfl

/-- An actual argument descendant, not merely its root, can be copied at an
original bound body variable. The continuation is cut from a real Matches
access; neither it nor either generated premise is supplied by the caller. -/
theorem ActualRedexAccess.generated_argument_position
    {t : Term} {redex : RedexOcc t} (source : ActualRedexAccess g root redex)
    (matching : Matches g root t) (beta : BetaEdge g)
    (app : source.connection.app=beta.app) (lam : source.connection.lam=beta.lam)
    (principal : source.connection.edges=beta.principal)
    {body argument : Term} (lookup : subtermAt t redex.val=some (.app (.lam body) argument))
    (p : Path) (variableLookup : subtermAt body p=some (.var (binderDepth p)))
    (q : Position argument) :
    ∃ (descendant : RootAccess g root) (loop suffix : List (Endpoint g)) (a b : Context)
      (binding : BindingLoop g loop a b),
      accessWord g descendant.val=(redex.val++[.arg])++q.val ∧
      descendant.val=source.parent.val++beta.argEnd::suffix ∧
      accessWord g loop=p ∧binding.binder=beta.lam ∧
      GeneratedExpandedProperPath g root
        (source.parent.val++beta.principal++loop++beta.reverseRoute++[beta.argEnd]++suffix) := by
  obtain ⟨arg,leaf,loop,suffix,a,b,binding,argSplit,_bodySplit,argWord,loopWord,binder,
    _argGenerated,bodyGenerated,_inserted⟩ :=
    source.generated_binding_insert_base matching beta app lam principal lookup p variableLookup
  have lookupArg : subtermAt t (redex.val++[.arg])=some argument := by
    simp only [subtermAt_append,lookup,Option.bind_some,subtermAt]
  let position : Position t := ⟨(redex.val++[.arg])++q.val,by
    simpa only [subtermAt_append,lookupArg,Option.bind_some] using q.property⟩
  obtain ⟨descendant,descendantWord,_⟩ := Matches.observation g matching position
  obtain ⟨rest,descendantSplit⟩ := matching.access_prefix arg descendant q.val (by
    simpa only [argWord] using descendantWord)
  have actualSplit : descendant.val=source.parent.val++beta.argEnd::(suffix++rest) := by
    rw [descendantSplit,argSplit]
    simp only [List.append_assoc,List.cons_append]
  have argumentGenerated : GeneratedExpandedProperPath g root
      (source.parent.val++beta.argEnd::(suffix++rest)) := by
    rw [←actualSplit]
    exact .base descendant.property.1 descendant.property.2.1
  have ctx := same_port_endpoint (g:=g) app source.contextPrincipal beta.appCtx_role
  have preEnd : source.parent.val.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
    rw [←ctx]
    exact source.parentFinish
  have bodyEnd := same_port_endpoint (g:=g) binder binding.body_role beta.lamBody_role
  have bindEnd := same_port_endpoint (g:=g) binder binding.bind_role beta.lamBind_role
  have loopStart : loop.head?=some (.inl ⟨beta.lam,beta.lamBody⟩) :=
    binding.start.trans (congrArg some bodyEnd)
  have loopEnd : loop.getLast?=some (g.wire (.inl ⟨beta.lam,beta.lamBind⟩)) :=
    binding.finish.trans (congrArg (fun e => some (g.wire e)) bindEnd)
  exact ⟨descendant,loop,suffix++rest,a,b,binding,descendantWord,actualSplit,loopWord,binder,
    .insert beta source.parent.val loop (suffix++rest) argumentGenerated bodyGenerated
      preEnd loopStart loopEnd a b binding binder⟩
end
end Lamping.AG

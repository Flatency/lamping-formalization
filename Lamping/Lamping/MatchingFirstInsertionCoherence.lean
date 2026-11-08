import Lamping.Lamping.OrdinaryInsertionCoherence
import Lamping.Lamping.MatchingBetaGeneratedArgument
import Lamping.Lamping.ReachableNesting
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
private theorem same_role_endpoint {T : Type} {canonical : T} {n m : N}
    {p : Port (g.label n).sort} {q : Port (g.label m).sort}
    (nodes : n=m) (left : HEq p canonical) (right : HEq q canonical) :
    (.inl ⟨n,p⟩ : Endpoint g)=.inl ⟨m,q⟩ := by
  subst m
  cases eq_of_heq (left.trans right.symm)
  rfl
private theorem argument_roles {kind : Kind} {ctx departure : Port kind}
    (roles : SyntaxChildPorts kind ctx departure .arg) : HEq ctx appCtx ∧HEq departure appArg := by
  cases roles
  exact ⟨HEq.rfl,HEq.rfl⟩

/-- Source Matches and ordinary structural invariants construct the SAME
physical first-copy detour with coherent labels for every root input.
No loop, prefix labelling, generatedness or inserted label is a caller field. -/
theorem ActualRedexAccess.coherent_argument_position_streams
    {t : Term} {redex : RedexOcc t} (source : ActualRedexAccess g root redex)
    (matching : Matches g root t) (inputs : RootInputs g root)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    (transparency : Transparency g root) (beta : BetaEdge g)
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
      ∀ requested : Context,∃ output,CoherentExpandedCore g root
        (source.parent.val++beta.principal++loop++beta.reverseRoute++[beta.argEnd]++suffix) requested output ∧
        BetaDetourBlocks g
          (source.parent.val++beta.principal++loop++beta.reverseRoute++[beta.argEnd]++suffix) requested output 1 := by
  obtain ⟨leaf,loop,initial,a,b,binding,_leafWord,_leafSplit,binder,loopWord,childLabels⟩ :=
    source.bound_body_loop matching lookup p variableLookup
  have contextEq := same_role_endpoint (g:=g) app source.contextPrincipal beta.appCtx_role
  have preEnd : source.parent.val.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
    rw [←contextEq]; exact source.parentFinish
  have childActual : Labelling g (source.parent.val++beta.principal) initial a := by
    simpa only [source.split,principal] using childLabels
  have preNonempty : source.parent.val≠[] := by
    intro empty; have finish := source.parentFinish; rw [empty] at finish; cases finish
  obtain ⟨middle,preLabels⟩ := childActual.prefix preNonempty
  have extended : Labelling g (source.parent.val++beta.principal) initial middle := by
    apply preLabels.append_seam (beta.principal_labeling middle)
    intro e f finish head
    have eEq := Option.some.inj (finish.symm.trans preEnd)
    have fEq := Option.some.inj (head.symm.trans beta.principalStart)
    rw [eEq,fEq,Pairing.involutive]
    exact beta.app_fun_turn middle
  have middleEq : middle=a := extended.output_unique childActual
  subst middle
  have argLookup : subtermAt t (redex.val++[.arg])=some argument := by
    simp only [subtermAt_append,lookup,Option.bind_some,subtermAt]
  let argPosition : Position t := ⟨redex.val++[.arg],by rw [argLookup]; rfl⟩
  obtain ⟨arg,argWord,_⟩ := Matches.observation g matching argPosition
  obtain ⟨node,ctx,departure,suffix,roles,finish,argSplit,_direction,_assignments⟩ :=
    matching.syntax_child_fragment source.parent arg .arg (by rw [argWord,source.parentWord])
  obtain ⟨ctxRole,departureRole⟩ := argument_roles roles
  have wires := Option.some.inj (finish.symm.trans source.parentFinish)
  have endpoints := congrArg g.wire.mate wires
  simp only [Pairing.involutive] at endpoints
  have nodeEq : node=source.connection.app := congrArg Sigma.fst (Sum.inl.inj endpoints)
  have departureEq : (.inl ⟨node,departure⟩ : Endpoint g)=beta.argEnd :=
    same_role_endpoint (nodeEq.trans app) departureRole beta.appArg_role
  have actualArg : arg.val=source.parent.val++beta.argEnd::suffix := by
    simpa only [departureEq] using argSplit
  let position : Position t := ⟨(redex.val++[.arg])++q.val,by
    simpa only [subtermAt_append,argLookup,Option.bind_some] using q.property⟩
  obtain ⟨descendant,descendantWord,_⟩ := Matches.observation g matching position
  obtain ⟨rest,descendantSplit⟩ := matching.access_prefix arg descendant q.val (by
    simpa only [argWord] using descendantWord)
  have actualDescendant : descendant.val=source.parent.val++beta.argEnd::(suffix++rest) := by
    rw [descendantSplit,actualArg]
    simp only [List.append_assoc,List.cons_append]
  exact ⟨descendant,loop,suffix++rest,a,b,binding,descendantWord,actualDescendant,loopWord,binder.trans lam,
    inputs.ordinary_insert_coherent_streams flow positive balance rootDepth (balance.nesting root rootDepth) transparency
      beta source.parent.val loop (suffix++rest) descendant actualDescendant binding (binder.trans lam)
      preLabels source.parent.property.2.1 preEnd⟩
/-- Coherence-only interface, with the actual paired-shape result available
separately above. No original caller needs a new premise. -/
theorem ActualRedexAccess.coherent_argument_position
    {t : Term} {redex : RedexOcc t} (source : ActualRedexAccess g root redex)
    (matching : Matches g root t) (inputs : RootInputs g root)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    (transparency : Transparency g root) (beta : BetaEdge g)
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
      ∀ requested : Context,∃ output,CoherentExpandedCore g root
        (source.parent.val++beta.principal++loop++beta.reverseRoute++[beta.argEnd]++suffix) requested output := by
  obtain ⟨descendant,loop,suffix,a,b,binding,word,split,loopWord,binder,allInputs⟩ :=
    source.coherent_argument_position_streams matching inputs flow positive balance rootDepth transparency
      beta app lam principal lookup p variableLookup q
  refine ⟨descendant,loop,suffix,a,b,binding,word,split,loopWord,binder,?_⟩
  intro requested
  obtain ⟨output,coherent,_paired⟩ := allInputs requested
  exact ⟨output,coherent⟩
end
end Lamping.AG


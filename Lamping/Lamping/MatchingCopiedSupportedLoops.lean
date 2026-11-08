import Lamping.Lamping.MatchingOriginalSupportedLoops
import Lamping.Lamping.MatchingBetaGeneratedBase
import Lamping.Lamping.SupportedLoopRebase
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}

private theorem same_endpoint {T : Type} {canonical : T} {n m : N}
    {p : Port (g.label n).sort} {q : Port (g.label m).sort}
    (nodes : n=m) (left : HEq p canonical) (right : HEq q canonical) :
    (.inl ⟨n,p⟩ : Endpoint g)=.inl ⟨m,q⟩ := by
  subst m
  cases eq_of_heq (left.trans right.symm)
  rfl

/-- A real original argument lambda's support is copied through a real
original bound-variable insertion. Both support trees and every generated
premise are obtained from source Matches; copy_rebase transports their
previous rooted bodies, rather than assuming a new ambient certificate. -/
theorem ActualRedexAccess.copied_original_supported_loop
    {redex : RedexOcc original.erase} (source : ActualRedexAccess g root redex)
    (matching : Matches g root original.erase) (initial : INIT original)
    (selection : SourceEdgeSelection original g root) (beta : BetaEdge g)
    (app : source.connection.app=beta.app) (lam : source.connection.lam=beta.lam)
    (principal : source.connection.edges=beta.principal)
    {appStamp degree copiedStamp : Labelled.Label} {body argument copiedBody : LTerm}
    (lookup : original.subterm redex.val=some (.app appStamp (.lam degree body) argument))
    (q : Path) (outerVariable : ArgumentOccurrence body.erase q)
    (r : Path) (atCopiedLambda : argument.subterm r=some (.lam copiedStamp copiedBody))
    (z : Path) (copiedVariable : subtermAt copiedBody.erase z=some (.var (binderDepth z))) :
    ∃ (oldParent : RootAccess g root) (outerLoop pre copiedLoop : List (Endpoint g))
      (a b c : Context) (binding : BindingLoop g copiedLoop b c),
      oldParent.val=source.parent.val++beta.argEnd::pre ∧
      Labelling g oldParent.val a b ∧
      original.sourceTrail selection.atomWord beta.principal beta.reverseRoute
        ((redex.val++[.arg])++r)=some oldParent.val ∧
      SupportedExpandedBindingLoop g root oldParent.val binding.binder copiedLoop ∧
      SupportedExpandedBindingLoop g root
        (source.parent.val++beta.principal++outerLoop++beta.reverseRoute++[beta.argEnd]++pre)
        binding.binder copiedLoop ∧
      GeneratedExpandedProperPath g root
        (source.parent.val++beta.principal++outerLoop++beta.reverseRoute++[beta.argEnd]++pre++copiedLoop) := by
  have bareLookup : subtermAt original.erase redex.val=some (.app (.lam body.erase) argument.erase) := by
    rw [←LTerm.erase_subterm,lookup]
    rfl
  have atLambda : original.subterm ((redex.val++[.arg])++r)=some (.lam copiedStamp copiedBody) := by
    rw [List.append_assoc,LTerm.subterm_append,lookup]
    exact atCopiedLambda
  obtain ⟨oldParent,oldLeaf,copiedLoop,a,b,c,binding,ctx,_parentWord,_leafWord,oldSplit,_word,
      labels,_ctxRole,_ctxEnd,parentEval,_leafEval,oldSupport,_parentGen,oldLeafGen⟩ :=
    matching.original_supported_loop initial selection beta atLambda copiedVariable
  obtain ⟨arg,_bodyLeaf,outerLoop,suffix,x,y,outerBinding,argSplit,_bodySplit,argWord,_outerWord,binder,
      _argGen,bodyGen,_inserted⟩ :=
    source.generated_binding_insert_base matching beta app lam principal bareLookup q outerVariable
  have parentWord : accessWord g oldParent.val=(redex.val++[.arg])++r := _parentWord
  obtain ⟨rest,descendantSplit⟩ := matching.access_prefix arg oldParent r (by rw [parentWord,argWord])
  have actualSplit : oldParent.val=source.parent.val++beta.argEnd::(suffix++rest) := by
    rw [descendantSplit,argSplit]
    simp only [List.append_assoc,List.cons_append]
  have actualCtx : (.inl ⟨source.connection.app,source.ctx⟩ : Endpoint g)=.inl ⟨beta.app,beta.appCtx⟩ := by
    exact same_endpoint app source.contextPrincipal beta.appCtx_role
  have stemEnd : source.parent.val.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
    rw [←actualCtx]
    exact source.parentFinish
  have outerSupport : SupportedExpandedBindingLoop g root (source.parent.val++beta.principal)
      beta.lam outerLoop := by
    rw [←binder]
    exact .base _ _ x y outerBinding
  have copiedSupport := oldSupport
  rw [actualSplit] at copiedSupport
  have rebased := outerSupport.copy_rebase beta source.parent.val outerLoop (suffix++rest)
    bodyGen stemEnd copiedSupport
  have newGenerated : GeneratedExpandedProperPath g root
      (source.parent.val++beta.principal++outerLoop++beta.reverseRoute++[beta.argEnd]++(suffix++rest)++copiedLoop) := by
    have oldGenerated : GeneratedExpandedProperPath g root
        (source.parent.val++beta.argEnd::((suffix++rest)++copiedLoop)) := by
      simpa only [oldSplit,actualSplit,List.append_assoc,List.cons_append] using oldLeafGen
    have inserted := outerSupport.insert_at_beta beta source.parent.val ((suffix++rest)++copiedLoop)
      rfl rfl oldGenerated bodyGen stemEnd
    simpa only [List.append_assoc] using inserted
  exact ⟨oldParent,outerLoop,suffix++rest,copiedLoop,a,b,c,binding,actualSplit,labels,parentEval,
    oldSupport,rebased,newGenerated⟩
end
end Lamping.AG

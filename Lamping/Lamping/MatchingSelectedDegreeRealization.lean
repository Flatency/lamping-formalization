import Lamping.Lamping.MatchingBetaPrincipalPath
import Lamping.Lamping.MatchingSourcePortUniqueness
import Lamping.Lambda.SelectedDevelopmentRoutes
import Lamping.Lambda.LabelArgumentDegreeInterior
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
private theorem function_ports (actual : Graph.Label signature) (ctx funPort : Port actual.sort)
    (lab : actual=label .app i) (ctxRole : HEq ctx appCtx)
    (funRole : HEq funPort (Sum.inl () : Port (.op .app))) :
    SyntaxChildPorts actual.sort ctx funPort .fn := by
  subst actual
  have c := eq_of_heq ctxRole
  have f := eq_of_heq funRole
  cases c; cases f
  exact .function
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}
/-- Rich provenance realizes the old function edge using its very same
literal connection suffix and original whole-path assignment. -/
theorem ActualRedexAccess.source_function_fragment
    (matching : Matches g root original.erase)
    {redex : RedexOcc original.erase} (source : ActualRedexAccess g root redex)
    (lookup : original.subterm redex.val=some (.app appId (.lam degree body) argument)) :
    ∃ fragment : SourceEdgeFragment original g root
      ⟨degree,.appFn appId,.lamContext degree⟩ (redex.val++[.fn]),
      fragment.segments=source.connection.edges := by
  obtain ⟨env,ctx,site⟩ := SourceSubterm.of_lookup original lookup [] .external
  have childSite := site.append (show SourceSubterm env ctx
    (.app appId (.lam degree body) argument) [.fn] env (.appFn appId) (.lam degree body) from .fn .nil)
  have childFinish : source.child.val.getLast?=some (g.wire (.inl ⟨source.connection.lam,source.connection.lamPort⟩)) := by
    rw [source.split,List.getLast?_append,source.connection.finish]
    rfl
  refine ⟨{
    access := source.child
    word := source.childWord
    occurrence := ⟨env,.appFn appId,.lam degree body,childSite,rfl⟩
    before := source.parent.val
    segments := source.connection.edges
    fromEndpoint := .inl ⟨source.connection.app,source.connection.appPort⟩
    toEndpoint := .inl ⟨source.connection.lam,source.connection.lamPort⟩
    fromRealizes := .departure lookup .fn source.parent source.parentWord
      (function_ports _ _ _ source.connection.appLabel source.contextPrincipal source.connection.appPrincipal) source.parentFinish
    toRealizes := .lamContext childSite.lookup source.child source.childWord
      (congrArg Graph.Label.sort source.connection.lamLabel) source.connection.lamPrincipal childFinish
    literal := source.split
    start := source.connection.start
    finish := source.connection.finish
    forward := source.connection.proper.2
    emptyWord := source.connection.emptyWord
    assignments := ?_ },rfl⟩
  obtain ⟨node,actualCtx,departure,tail,roles,finish,split,forward,assignments⟩ :=
    matching.syntax_child_fragment source.parent source.child .fn
      (by rw [source.childWord,source.parentWord])
  have edges : (.inl ⟨node,departure⟩)::tail=source.connection.edges :=
    List.append_cancel_left (split.symm.trans source.split)
  intro a b whole
  obtain ⟨middle,before,after⟩ := assignments a b whole
  rw [edges] at after
  exact ⟨middle,Or.inr before,after⟩
end
private theorem degree_lookup {original : LTerm}
    (atDegree : original.degreeAt name=some degree) :
    ∃ appId body argument,original.subterm name=some (.app appId (.lam degree body) argument) := by
  simp only [LTerm.degreeAt,Option.bind_eq_some_iff] at atDegree
  obtain ⟨term,lookup,atDegree⟩ := atDegree
  cases term with
  | var => simp [LTerm.degree] at atDegree
  | lam => simp [LTerm.degree] at atDegree
  | app appId fn argument =>
    cases fn with
    | var => simp [LTerm.degree] at atDegree
    | app => simp [LTerm.degree] at atDegree
    | lam degree' body =>
      simp only [LTerm.degree,Option.some.injEq] at atDegree
      cases atDegree
      exact ⟨appId,body,argument,lookup⟩
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
/-- Every original selected degree supplies a genuine old syntax function
edge whose actual physical fragment is the same fixed graph-site principal
route. The source degree may be non-atomic here; no reduct is reinitialized. -/
theorem PathSite.selected_degree_principal_fragment
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (matching : Matches site.net root original.erase) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
      ∀ degree,SelectedDegree original (site.betaSyntaxFiber root original.erase) degree →
      ∃ name appId body argument,name∈site.betaSyntaxFiber root original.erase ∧
        original.subterm name=some (.app appId (.lam degree body) argument) ∧
        ∃ fragment : SourceEdgeFragment original site.net root
          ⟨degree,.appFn appId,.lamContext degree⟩ (name++[.fn]),fragment.segments=beta.principal := by
  obtain ⟨beta,app,lam,allSources⟩ := site.beta_fiber_principal matching
  refine ⟨beta,app,lam,?_⟩
  intro degree selected
  obtain ⟨name,member,atDegree⟩ := selected
  obtain ⟨redex,source,equal,atApp,atLam⟩ := (mem_physicalBetaFiberPaths _ _ _ _ _ _).mp member
  obtain ⟨appId,body,argument,atPoint⟩ := degree_lookup atDegree
  obtain ⟨fragment,paths⟩ := source.source_function_fragment matching (by rw [equal]; exact atPoint)
  have whole := allSources redex source (by simpa only [equal] using member)
  refine ⟨name,appId,body,argument,member,atPoint,?_⟩
  rw [←equal]
  exact ⟨fragment,paths.trans whole⟩
end
end Lamping.AG





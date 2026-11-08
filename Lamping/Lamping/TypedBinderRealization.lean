import Lamping.Lamping.HistoryTypedPaths
import Lamping.Lamping.HistoryTypedBinders
import Lamping.Lamping.SupportedLoopPorts
import Lamping.Lamping.ExpandedTransparencySurgery

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}

private theorem supported_ports {ambient binder loop}
    (support : SupportedExpandedBindingLoop g root ambient binder loop) :
    ∃ body bind : Port (g.label binder).sort,
      HEq body lamBody ∧HEq bind lamBind ∧
      loop.head?=some (.inl ⟨binder,body⟩) ∧
      loop.getLast?=some (g.wire (.inl ⟨binder,bind⟩)) := by
  induction support with
  | base ambient es a b binding =>
    exact ⟨binding.body,binding.bind,binding.body_role,binding.bind_role,binding.start,binding.finish⟩
  | insert ambient binder edge pre inner tail _outer _nested _old _body preEnd _start _end ih _nestedIH =>
    obtain ⟨body,bind,bodyRole,bindRole,first,last⟩ := ih
    have nonempty : pre≠[] := by intro empty; rw [empty] at preEnd; cases preEnd
    refine ⟨body,bind,bodyRole,bindRole,?_,?_⟩
    · cases pre with
      | nil => exact False.elim (nonempty rfl)
      | cons x xs => exact first
    · cases tailLast : tail.getLast? <;>
        simpa [List.getLast?_append,List.getLast?_cons,tailLast] using last

/-- Consume the FOUR proved history assertions to realize a specified
current binder at every root input. Generation supplies direction, finite
support supplies ports, Q supplies the actual whole assignment, and R
supplies its SAME-assignment shell. No label or shell is extracted from
support alone and no target graph assertion is a premise. -/
theorem realize_typed_binder
    {selection : SourceEdgeSelection original g root} {beta : BetaEdge g} {current : LTerm}
    (generated : GeneratedSyntaxPaths selection beta current)
    (supported : SupportedSyntaxBinders selection beta current)
    (paths : TypedSyntaxPaths selection beta current)
    (binders : TypedSyntaxBinders selection beta current)
    {p : Path} {stamp body} (atLambda : current.subterm p=some (.lam stamp body))
    {q : Path} (atVariable : subtermAt body.erase q=some (.var (binderDepth q))) :
    ∃ (ambient loop : List (Endpoint g)) (binder : N) (ctx : Port (g.label binder).sort),
      current.sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some ambient ∧
      current.sourceTrail selection.atomWord beta.principal beta.reverseRoute (p++(.body::q))=some (ambient++loop) ∧
      (g.label binder).sort=.op .lam ∧HEq ctx (Sum.inl () : Port (.op .lam)) ∧
      ambient.getLast?=some (g.wire (.inl ⟨binder,ctx⟩)) ∧
      ∀ input : Context,∃ output seam count,
        BetaDetourBlocks g (ambient++loop) input output count ∧
        ExpandedLabelling g ambient input seam ∧
        ∃ binding : ExpandedBindingLoop g loop seam output,binding.binder=binder := by
  obtain ⟨ambient,loop,binder,ctx,ambientEval,leafEval,support,sort,ctxRole,ambientEnd⟩ :=
    supported atLambda atVariable
  obtain ⟨bodyPort,bindPort,bodyRole,bindRole,loopStart,loopEnd⟩ := supported_ports support
  obtain ⟨tail,loopSplit⟩ := List.head?_eq_some_iff.mp loopStart
  have leafExists : ∃ leaf,body.subterm q=some leaf := by
    have erased := body.erase_subterm q
    rw [atVariable] at erased
    cases lookup : body.subterm q with
    | none => rw [lookup] at erased; cases erased
    | some leaf => exact ⟨leaf,rfl⟩
  obtain ⟨leaf,bodyLookup⟩ := leafExists
  have leafLookup : current.subterm (p++(.body::q))=some leaf := by
    rw [LTerm.subterm_append,atLambda]
    exact bodyLookup
  obtain ⟨word,evaluation,direction⟩ := generated leafLookup
  have same : word=ambient++loop := Option.some.inj (evaluation.symm.trans leafEval)
  have forward : ExpandedForward g (ambient++loop) := same ▸ direction.forward g
  have nonempty : ambient≠[] := by intro empty; rw [empty] at ambientEnd; cases ambientEnd
  refine ⟨ambient,loop,binder,ctx,ambientEval,leafEval,sort,ctxRole,ambientEnd,?_⟩
  intro input
  obtain ⟨output,count,whole⟩ := paths.at_word leafLookup leafEval input
  obtain ⟨seam,ambientLabels⟩ := (whole.labelling g).prefix nonempty
  have shell := binders atLambda atVariable ambientEval leafEval sort ctxRole ambientEnd whole ambientLabels
  have finish : (ambient++loop).getLast?=some (g.wire (.inl ⟨binder,bindPort⟩)) := by
    simp only [List.getLast?_append,loopEnd,Option.some_or]
  obtain ⟨binding,sameBinder⟩ := expanded_binding_suffix binder ctx bodyPort bindPort sort ctxRole bodyRole bindRole
    ambient tail input seam output (by simpa only [loopSplit] using whole.labelling g)
    (by simpa only [loopSplit] using forward) ambientLabels ambientEnd
    (by simpa only [loopSplit] using finish) shell
  have atLoop : ∃ binding : ExpandedBindingLoop g loop seam output,binding.binder=binder := by
    rw [loopSplit]
    exact ⟨binding,sameBinder⟩
  exact ⟨output,seam,count,whole,ambientLabels,atLoop⟩

end
end Lamping.AG

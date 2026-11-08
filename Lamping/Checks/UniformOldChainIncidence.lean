import Lamping.Lamping.UniformOldChainIncidence
namespace Lamping.Checks.UniformOldChainIncidence
open Lambda Lambda.Labelled AG
private abbrev a := Label.atom 7
private abbrev identity : LTerm := .lam a (.var a 0)
private abbrev argument : LTerm := .app a (.var a 0) identity
private abbrev inner : LTerm := .app a (.lam a (.var a 0)) argument
private abbrev sibling : LTerm := .app a identity identity
private abbrev insideResult := LTerm.contract a a (.var a 0) argument
private abbrev siblingResult := LTerm.contract a a (.var a 0) identity
private abbrev source : LTerm := .app a (.lam a inner) sibling
private abbrev middle : LTerm := .app a (.lam a insideResult) sibling
private abbrev target : LTerm := .app a (.lam a insideResult) siblingResult
private theorem sourceClosed : Closed source.erase := by
  change ((0<2) ∧((0<1) ∧0<2)) ∧((0<1) ∧0<1)
  decide
private theorem targetClosed : Closed target.erase := by
  change ((0<1) ∧0<2) ∧0<1
  decide
private def first : StepAt [.fn,.body] source middle := .fn (.body (.root _ _ _ _))
private def second : StepAt [.arg] middle target := .arg (.root _ _ _ _)
private abbrev selection : List Path := [[.fn,.body],[.arg]]
private abbrev markedTarget : Marked := .app [[]] (.lam (.app [] (.var 0) (.lam (.var 0)))) (.lam (.var 0))
private def step : ParallelStep selection source.erase target.erase := by
  refine ⟨selection,markedTarget,(Marked.completeOld_iff _ _).mpr ⟨?_,?goal⟩,rfl⟩
  · change Marked.RelativeHistory selection
      (.app [[]] (.lam (.red [[.fn,.body]] (.var 0) (.app [] (.var 0) (.lam (.var 0)))))
        (.red [[.arg]] (.var 0) (.lam (.var 0)))) markedTarget
    exact .cons (.appL (.lam (.root _ _ _))) (.cons (.appR (.root _ _ _)) (.nil _))
  case goal => exact ⟨⟨True.intro,True.intro⟩,True.intro⟩
private def labels : History step.paths source target := .cons first (.cons second (.nil _))
private abbrev edges : List Path := [[.fn,.body,.arg],[.fn,.body,.fn],[.fn]]
private def chain : PrerequisiteChain target [.fn,.body,.arg] edges :=
  .lam (parent := [.fn,.body]) (step := .arg) rfl (by decide)
    (.app rfl (by intro stamp body impossible;cases impossible)
      (.var (parent := [.fn]) (rest := [.fn]) rfl rfl rfl rfl (.redex_lam (p := []) rfl)))
private theorem selected (path : Path) (member : path∈selection) : source.degreeAt path=some a := by
  rcases List.mem_cons.mp member with rfl | rest
  · rfl
  · have equal := List.mem_singleton.mp rest
    subst path;rfl
private theorem edgeLabel (edge : Path) (member : edge∈edges) : target.labelAt edge=some a := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal | equal <;> subst edge <;> rfl
private theorem markerFree (edge : Path) (member : edge∈edges) (node : LTerm)
    (lookup : target.subterm edge=some node) : node.label.OuterBarsSafe (fun payload=>payload≠a) := by
  have actual : target.labelAt edge=some node.label := by simp only [LTerm.labelAt,lookup,Option.map_some]
  have equal := Option.some.inj (actual.symm.trans (edgeLabel edge member))
  rw [equal];trivial

/-- Across two actual OLD contractions of the same degree, a true chain
reads strict copied ARG edges, then jumps to the external binder/context.
The intermediate source already contains the fired marker. -/
theorem actual_whole_schedule_mixed_chain :
    step.paths.length=2 ∧
    ¬middle.OuterBarsSafe (fun payload=>payload≠a) ∧
    ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed edges)
        (chainSyntaxIncidence source sourceClosed oldEdges) := by
  refine ⟨rfl,?_,step.marker_free_chain_incidence sourceClosed targetClosed labels selected chain markerFree⟩
  intro middleSafe
  have atResult : middle.subterm [.fn,.body]=some insideResult := rfl
  exact first.created_label_not_safe rfl atResult (Or.inl rfl)
    ((LTerm.outerBarsSafe_iff _ _).mp middleSafe _ (LTerm.label_mem_of_subterm atResult))

theorem actual_old_label_wrapper :
    ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed edges)
        (chainSyntaxIncidence source sourceClosed oldEdges) := by
  apply step.old_label_chain_incidence sourceClosed targetClosed labels selected
    (by simp [LTerm.OuterBarsSafe,Label.OuterBarsSafe,Label.atom]) chain
  intro edge member node lookup
  have actual : target.labelAt edge=some node.label := by simp only [LTerm.labelAt,lookup,Option.map_some]
  have equal := Option.some.inj (actual.symm.trans (edgeLabel edge member))
  rw [equal];decide

end Lamping.Checks.UniformOldChainIncidence
#print axioms Lamping.Lambda.Marked.RelativeOldHistory.marker_free_chain_incidence
#print axioms Lamping.Lambda.ParallelStep.marker_free_chain_incidence
#print axioms Lamping.Lambda.ParallelStep.old_label_chain_incidence
#print axioms Lamping.Checks.UniformOldChainIncidence.actual_whole_schedule_mixed_chain

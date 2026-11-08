import Lamping.Lamping.EmptyBetaNeeded
import Lamping.Lamping.ReachableJointRepresentation
import Lamping.Lambda.NeededFamilyInclusion

namespace Lamping.Lambda

private def neededFlags : {t u : Term} → ParallelHistory t u → List Prop
  | _, _, .nil _ => []
  | t, _, @ParallelHistory.cons _ _ _ F _ tail =>
      (∃ r : RedexOcc t, r.val ∈ F ∧ Needed r) :: neededFlags tail

private theorem neededFlags_append {t u v : Term}
    (prior : ParallelHistory t u) (later : ParallelHistory u v) :
    neededFlags (prior.append later) = neededFlags prior ++ neededFlags later := by
  induction prior with
  | nil => rfl
  | cons step tail ih =>
    simp only [ParallelHistory.append, neededFlags, List.cons_append, ih]

private theorem neededFlags_hold {t u : Term} {prior : ParallelHistory t u}
    (needful : CallByNeedHistory prior) : ∀ P ∈ neededFlags prior, P := by
  induction prior with
  | nil => simp [neededFlags]
  | cons step tail ih =>
    intro P member
    rw [neededFlags] at member
    rcases List.mem_cons.mp member with head | rest
    · cases head
      exact needful (.nil _) step tail rfl
    · have tailNeeded : CallByNeedHistory tail := by
        intro x y F earlier turn suffix split
        exact needful (.cons step earlier) turn suffix (congrArg (ParallelHistory.cons step) split)
      exact ih tailNeeded P rest

/-- Extend the literal strategy history by its actual step. The proof tracks
each selected batch by list concatenation, without comparing permutations. -/
theorem CallByNeedHistory.snoc {m t u : Term} {F : List Path}
    {prior : ParallelHistory m t} (needful : CallByNeedHistory prior)
    (step : ParallelStep F t u) (r : RedexOcc t)
    (member : r.val ∈ F) (needed : Needed r) :
    CallByNeedHistory (prior.append (.single step)) := by
  intro x y G earlier turn suffix split
  let P : Prop := ∃ s : RedexOcc x, s.val ∈ G ∧ Needed s
  have selected : P ∈ neededFlags (prior.append (.single step)) := by
    rw [split, neededFlags_append]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  rw [neededFlags_append] at selected
  rcases List.mem_append.mp selected with before | last
  · exact neededFlags_hold needful P before
  · change P ∈ [∃ s : RedexOcc t, s.val ∈ F ∧ Needed s] at last
    have witness : ∃ s : RedexOcc t, s.val ∈ F ∧ Needed s := ⟨r, member, needed⟩
    exact Eq.mp (List.mem_singleton.mp last).symm witness

end Lamping.Lambda

namespace Lamping.AG.Readback
open Graph Lambda Lambda.Labelled ExposureScheduling

/-- Extend the exact already accumulated strategy prior. Its labels are
transported from the actual raw graph projection by derivation equality;
no observable prior is chosen anew. -/
theorem empty_beta_recipe_extend_strategy_prior
    {original current : LTerm} (source : ExecutableNet (Boundary original.erase))
    [DecidableEq (Boundary original.erase)]
    (initial : INIT original) (originalClosed : Closed original.erase)
    {schemas : List Schema} {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      source.graph (.inl ()) schemas original current raw)
    (prior : ParallelHistory original.erase current.erase)
    (sameDerivation : raw.derivation = prior.derivation)
    (complete : CompleteDerivation prior) (needful : CallByNeedHistory prior)
    {redex : RedexOcc current.erase}
    (access : ActualRedexAccess source.graph.net (.inl ()) redex)
    {depths : Boundary original.erase → Int}
    (routeBalance : LevelBalance source.graph.net depths)
    (empty : controlWord source.graph.net access.connection.edges = [])
    (selectedLO : loRedex current.erase = some redex.val)
    {directions : Boundary original.erase → Bool} (flow : FlowBalance source.graph.net directions)
    (positive : directions (.inl ()) = true)
    {heights : Boundary original.erase → Int} (balance : IndexedLevelBalance source.graph.net heights)
    (rootDepth : heights (.inl ()) = 0) (transparent : Transparency source.graph.net (.inl ())) :
    let recipe := empty_beta_recipe source access routeBalance empty
    ∃ (target : LTerm)
      (step : ParallelStep (recipe.site.betaSyntaxFiber (.inl ()) current.erase) current.erase target.erase),
      LabelledGraphEvent (.beta access.connection.appIndex) source.graph recipe.target.graph (.inl ())
        current target (.single step) ∧
      CompleteDerivation (prior.append (.single step)) ∧
      CallByNeedHistory (prior.append (.single step)) ∧
      ∃ domain : ReadbackDomain recipe.target.graph.net (.inl ()),
        NeededParallelNext (recipe.target.readback (.inl ()) domain) current.erase := by
  let recipe := empty_beta_recipe source access routeBalance empty
  have closed := actual.label_history.closed originalClosed
  have history : History prior.derivation.paths original current := by
    rw [← sameDerivation]
    exact actual.label_history
  obtain ⟨initialFlow⟩ := encode_flowBalance original.erase 0
  obtain ⟨initialBalance⟩ := encode_indexed_balance original.erase 0
  obtain ⟨inputs, matching⟩ := actual.target_matches initialFlow rfl initialBalance rfl
    (encode_closed_independence original.erase originalClosed 0).rootInputs
    (encode_closed_transparency original.erase originalClosed 0)
    (encode_closed_matches original.erase originalClosed 0) originalClosed
  obtain ⟨target, step, event, domain, next⟩ :=
    empty_beta_recipe_needed_readback source access routeBalance empty selectedLO
      closed matching inputs flow positive balance rootDepth transparent
  have member : redex.val ∈ recipe.site.betaSyntaxFiber (.inl ()) current.erase :=
    empty_beta_recipe_fiber_member source access routeBalance empty
  have nonempty : recipe.site.betaSyntaxFiber (.inl ()) current.erase ≠ [] := by
    intro absent
    rw [absent] at member
    exact List.not_mem_nil member
  obtain ⟨selection⟩ := matching.occurrence_fragment_selection closed
  have joint := actual.initial_joint_representation initial originalClosed selection
  have siteMatching := recipe.sourceIso.matches matching
  obtain ⟨siteSelection⟩ := siteMatching.occurrence_fragment_selection closed
  have siteRepresentation : ChainRepresentationInvariant closed siteSelection := by
    intro p q left right first second
    exact (recipe.sourceIso.chain_representation matching selection siteSelection first second).trans
      (joint.1 first second)
  have extended := recipe.site.beta_extend_complete_derivation initial closed prior history complete
    siteMatching siteSelection siteRepresentation nonempty step
  exact ⟨target, step, event, extended, needful.snoc step redex member (loRedex_needed selectedLO), domain, next⟩

#print axioms Lamping.Lambda.CallByNeedHistory.snoc
#print axioms Lamping.AG.Readback.empty_beta_recipe_extend_strategy_prior

end Lamping.AG.Readback

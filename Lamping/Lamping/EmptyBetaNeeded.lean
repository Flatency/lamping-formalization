import Lamping.Lamping.EmptyControlBetaRecipe
import Lamping.Lamping.NetIsoBetaFiberTransport
import Lamping.Lamping.LabelledGraphEvents
import Lamping.Lamping.ExecutableReadback
import Lamping.Lambda.NeededAccessibility

namespace Lamping.AG.Readback
open Graph Lambda Lambda.Labelled ExposureScheduling

section
variable {B : Type} [FiniteNames B] (source : ExecutableNet B)
variable {root : B} {term : Term} {redex : RedexOcc term}

/-- Rename the actual rooted witness through the same recipe source map.
Both distinguished nodes are fixed by the recipe's actual principal ports. -/
theorem empty_beta_recipe_fiber_member
    (access : ActualRedexAccess source.graph.net root redex)
    {depths : B → Int} (balance : LevelBalance source.graph.net depths)
    (empty : controlWord source.graph.net access.connection.edges = []) :
    redex.val ∈ (empty_beta_recipe source access balance empty).site.betaSyntaxFiber root term := by
  let recipe := empty_beta_recipe source access balance empty
  have ports := empty_beta_recipe_ports source access balance empty
  have app : recipe.sourceIso.nodes access.connection.app = .inr (.inl ()) :=
    (recipe.sourceIso.port_node ⟨access.connection.app, access.connection.appPort⟩).symm.trans
      (congrArg Sigma.fst ports.1)
  have lam : recipe.sourceIso.nodes access.connection.lam = .inr (.inr ()) :=
    (recipe.sourceIso.port_node ⟨access.connection.lam, access.connection.lamPort⟩).symm.trans
      (congrArg Sigma.fst ports.2)
  change redex.val ∈ recipe.site.betaSyntaxFiber root term
  unfold PathSite.betaSyntaxFiber
  exact (mem_physicalBetaFiberPaths _ _ _ _ _ _).mpr
    ⟨redex, recipe.sourceIso.actualRedexAccess access, rfl, app, lam⟩
end

section
variable {B : Type} [FiniteNames B] [DecidableEq B] (source : ExecutableNet B)
variable {root : B} {labelled : LTerm} {redex : RedexOcc labelled.erase}

/-- The same computed empty-control recipe produces an actual labelled
event and a Needed successor for its effective target readback. All semantic
choices are local to this Prop proof. -/
theorem empty_beta_recipe_needed_readback
    (access : ActualRedexAccess source.graph.net root redex)
    {depths : B → Int} (routeBalance : LevelBalance source.graph.net depths)
    (empty : controlWord source.graph.net access.connection.edges = [])
    (selectedLO : loRedex labelled.erase = some redex.val)
    (closed : Closed labelled.erase) (matching : Matches source.graph.net root labelled.erase)
    (inputs : RootInputs source.graph.net root)
    {directions : B → Bool} (flow : FlowBalance source.graph.net directions)
    (positive : directions root = true)
    {heights : B → Int} (balance : IndexedLevelBalance source.graph.net heights)
    (rootDepth : heights root = 0) (transparency : Transparency source.graph.net root) :
    let recipe := empty_beta_recipe source access routeBalance empty
    ∃ (target : LTerm) (parallel : ParallelStep (recipe.site.betaSyntaxFiber root labelled.erase)
        labelled.erase target.erase),
      LabelledGraphEvent (.beta access.connection.appIndex) source.graph recipe.target.graph root
        labelled target (.single parallel) ∧
      ∃ domain : ReadbackDomain recipe.target.graph.net root,
        NeededParallelNext (recipe.target.readback root domain) labelled.erase := by
  let recipe := empty_beta_recipe source access routeBalance empty
  change ∃ (target : LTerm) (parallel : ParallelStep
      (recipe.site.betaSyntaxFiber root labelled.erase) labelled.erase target.erase),
    LabelledGraphEvent (.beta access.connection.appIndex) source.graph recipe.target.graph root
      labelled target (.single parallel) ∧
    ∃ domain : ReadbackDomain recipe.target.graph.net root,
      NeededParallelNext (recipe.target.readback root domain) labelled.erase
  obtain ⟨ps, marked, target, complete, history, erased, next⟩ :=
    recipe.site.beta_labelled_projection closed (recipe.sourceIso.matches matching)
      (recipe.sourceIso.rootInputs inputs) (recipe.sourceIso.flowBalance flow) positive
      (recipe.sourceIso.indexed_balance balance) rootDepth (recipe.sourceIso.transparency transparency)
  let parallel : ParallelStep (recipe.site.betaSyntaxFiber root labelled.erase)
      labelled.erase target.erase := ⟨ps, marked, complete, erased.symm⟩
  have targetMatches : Matches recipe.target.graph.net root target.erase := next
  have targetInputs := recipe.actual_step.rootInputs flow positive balance rootDepth inputs transparency matching
  have targetT := recipe.actual_step.transparency_indexed flow positive balance rootDepth transparency
  let domain : ReadbackDomain recipe.target.graph.net root :=
    ⟨targetInputs, targetT, target.erase, targetMatches⟩
  refine ⟨target, parallel,
    .beta recipe.kept recipe.site recipe.sourceIso (.refl _) complete history erased.symm,
    domain, ?_⟩
  rw [recipe.target.readback_eq_of_matches root domain targetMatches]
  exact ⟨recipe.site.betaSyntaxFiber root labelled.erase, parallel, redex,
    empty_beta_recipe_fiber_member source access routeBalance empty, loRedex_needed selectedLO⟩
end

#print axioms Lamping.AG.Readback.empty_beta_recipe_fiber_member
#print axioms Lamping.AG.Readback.empty_beta_recipe_needed_readback

end Lamping.AG.Readback

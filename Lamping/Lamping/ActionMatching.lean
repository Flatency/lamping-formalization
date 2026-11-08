import Lamping.Lamping.ActionBackwardObservations
import Lamping.Lamping.SourceActionAccess
import Lamping.Lamping.MatchingInitial
import Lamping.Lamping.RootInputAccessGeometry
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- All three actual actions preserve full Matches. Backward observation,
forward coverage, variable indices and word injectivity have independent
proofs; every target invariant used here comes from the actual rule. -/
theorem PathSite.action_matches_rootInputs (action : IsAction s)
    {directions : B → Bool} {heights : B → Int} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs site.net root) (oldT : Transparency site.net root)
    {t : Term} (matching : Matches site.net root t) : Matches site.reduce root t := by
  have newInputs := site.action_rootInputs action flow root positive balance rootDepth matching inputs oldT
  apply matches_of_access_classification site.reduce root t
  · exact site.action_access_classification action flow root positive balance rootDepth inputs oldT matching
  · intro position
    obtain ⟨source,sourceWord,_observation⟩ := Matches.observation site.net matching position
    obtain ⟨target,targetWord,_kind⟩ := site.action_access_forward action matching inputs flow positive oldT source
    exact ⟨target,targetWord.trans sourceWord⟩
  · exact fun _ _ words => newInputs.accessWord_injective words
end
section
variable {B : Type} [FiniteNames B]

theorem GraphStep.action_matches_rootInputs {s : Schema} {g h : ActualNet B}
    (step : GraphStep s g h) (action : IsAction s)
    {directions : B → Bool} {heights : B → Int} {root : B}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (oldT : Transparency g.net root)
    {t : Term} (matching : Matches g.net root t) : Matches h.net root t := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    exact targetIso.matches (site.action_matches_rootInputs action (sourceIso.flowBalance flow)
      root positive (sourceIso.indexed_balance balance) rootDepth (sourceIso.rootInputs inputs)
      (sourceIso.transparency oldT) (sourceIso.matches matching))
end
end Lamping.AG

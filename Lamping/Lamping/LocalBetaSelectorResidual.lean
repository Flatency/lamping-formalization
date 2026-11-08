import Lamping.Lamping.BetaSyntaxSelectorResidual
import Lamping.Lamping.LocalSourceFragmentEvaluation

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
variable {root : B} {source target : LTerm} {ps : List Path} {marked : Marked}

/-- Replay the SAME actual schedule only for local syntax geometry. The
global labels/history remain explicit and are not reinitialized. Every
specified global target access has the local evaluator's literal residual. -/
theorem PathSite.beta_local_selector_residuals
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target) :
    ∃ localTarget,∃ _localLabels : History ps (initLabels source.erase) localTarget,
      localTarget.erase=target.erase ∧Matches site.reduce root target.erase ∧
      ∃ edge : BetaEdge site.net,∃ selection : SourceEdgeSelection (initLabels source.erase) site.net root,
        SiteBetaGeometry site edge ∧
        ∀ {p sub},target.subterm p=some sub →∀ access : RootAccess site.reduce root,
          accessWord site.reduce access.val=p →∀ requested : Context,
          ∃ localSub,∃ _localLookup : localTarget.subterm p=some localSub,
            localSub.erase=sub.erase ∧
            ∃ finish,∃ trail : PhysicalSyntaxTrail (initLabels source.erase) root edge [] .external localTarget p localSub finish,
              ∃ output,∃ (node : K) (port : Port (kept node).sort),
              localTarget.sourceTrail selection.atomWord edge.principal edge.reverseRoute p=some trail.edges ∧
              BetaPathResidual site edge (access.val.map (plugEnd _ _).invFun) trail.edges ∧
              Labelling site.reduce access.val requested output ∧
              trail.toEndpoint=.inl ⟨.inl node,port⟩ ∧
              portKind (kept node).sort port=some (syntaxShape sub.erase).kind := by
  obtain ⟨localTarget,localLabels,sameErase⟩ := lift_history history.betaHistory
    (initLabels source.erase) (erase_initLabels source.erase)
  have initial := init_is_INIT source.erase
  have localMatching : Matches site.net root (initLabels source.erase).erase := by
    simpa only [erase_initLabels] using matching
  have localClosed : Closed (initLabels source.erase).erase := by
    simpa only [erase_initLabels] using closed
  have localRelative : Marked.RelativeHistory ps
      (Marked.mark (site.betaSyntaxFiber root (initLabels source.erase).erase) (initLabels source.erase).erase) marked := by
    simpa only [erase_initLabels] using relative
  obtain ⟨edge,selection,geometry,all⟩ := site.beta_complete_selector_residuals initial localClosed localMatching
    inputs flow positive balance rootDepth transparency localRelative normal localLabels
  have localTargetMatching := site.beta_complete_matches initial localClosed localMatching inputs flow positive
    balance rootDepth transparency localRelative normal localLabels
  have targetMatching : Matches site.reduce root target.erase := sameErase ▸ localTargetMatching
  refine ⟨localTarget,localLabels,sameErase,targetMatching,edge,selection,geometry,?_⟩
  intro p sub lookup access word requested
  have bare : (localTarget.subterm p).map LTerm.erase=some sub.erase := by
    rw [LTerm.erase_subterm,sameErase,←LTerm.erase_subterm,lookup]
    rfl
  cases localLookup : localTarget.subterm p with
  | none => rw [localLookup] at bare;cases bare
  | some localSub =>
    have sameSub : localSub.erase=sub.erase := by
      exact Option.some.inj (by simpa only [localLookup,Option.map_some] using bare)
    obtain ⟨finish,trail,output,node,port,evaluation,residual,assignment,ending,proper⟩ :=
      all localLookup access word requested
    exact ⟨localSub,rfl,sameSub,finish,trail,output,node,port,evaluation,residual,assignment,
      ending,by rw [←sameSub];exact proper⟩
end
end Lamping.AG

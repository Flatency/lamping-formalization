import Lamping.Lamping.CurrentRedexPorts
import Lamping.Lamping.BetaBindingProvenance
import Lamping.Lamping.CompleteNodeOrigins
import Lamping.Lamping.MatchingSourceEdgeRealization
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
variable {root : B} {original target : LTerm}

/-- A supplied SOURCE lambda access at the selected physical context is
really the FUNCTION child of an old redex in this same fiber. The literal
source occurrence is retained; shared physical nodes need not identify labels. -/
theorem PathSite.source_lambda_selected_origin
    (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {oldPosition : Path} {origin : Labelled.Label} {oldBody : LTerm}
    (lookup : original.subterm oldPosition=some (.lam origin oldBody))
    (access : RootAccess site.net root) (word : accessWord site.net access.val=oldPosition)
    (finish : access.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) :
    ∃ redexPosition appStamp argument,
      oldPosition=redexPosition++[.fn] ∧
      original.subterm redexPosition=some (.app appStamp (.lam origin oldBody) argument) ∧
      (⟨origin,.appFn appStamp,.lamContext origin⟩ : SourceEdge)∈sourceEdges [] .external original ∧
      SelectedDegree original (site.betaSyntaxFiber root original.erase) origin := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨parent,parentFinish,_literalSplit,lambdaWord⟩ :=
    site.beta_lambda_access_predecessor_word principal flow root positive access finish
  obtain ⟨beta,geometry⟩ := site.siteBetaGeometry_exists
  have betaFinish : parent.val.getLast?=some (site.net.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
    rw [geometry.appCtx]
    exact parentFinish
  obtain ⟨redex,redexWord,member⟩ := beta.root_app_visible matching flow positive parent betaFinish
  have appEq : beta.app=.inr (.inl ()) := congrArg Sigma.fst (Sum.inl.inj geometry.appCtx)
  have lamEq : beta.lam=.inr (.inr ()) := congrArg Sigma.fst (Sum.inl.inj geometry.binding)
  have selectedName : redex.val∈site.betaSyntaxFiber root original.erase := by
    simpa only [PathSite.betaSyntaxFiber,appEq,lamEq] using member
  have position : oldPosition=redex.val++[.fn] :=
    word.symm.trans (lambdaWord.trans (congrArg (fun p => p++[.fn]) redexWord.symm))
  rw [position,LTerm.subterm_append] at lookup
  cases headLookup : original.subterm redex.val with
  | none => simp only [headLookup,Option.bind_none] at lookup; cases lookup
  | some head =>
    rw [headLookup,Option.bind_some] at lookup
    cases head with
    | var stamp index => cases lookup
    | lam stamp body => cases lookup
    | app stamp fn arg =>
      have fnEq : fn=.lam origin oldBody := by simpa only [LTerm.subterm,Option.some.injEq] using lookup
      subst fn
      obtain ⟨env,ctx,atHead⟩ := SourceSubterm.of_lookup original headLookup [] .external
      have functionEdge : (⟨origin,.appFn stamp,.lamContext origin⟩ : SourceEdge)∈sourceEdges [] .external original :=
        atHead.edges_subset _ (List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self))
      refine ⟨redex.val,stamp,arg,position,headLookup,functionEdge,redex.val,selectedName,?_⟩
      simp only [LTerm.degreeAt,headLookup,Option.bind_some,LTerm.degree]

/-- Completion excludes this selected lambda ORIGIN, including proposed
compound current labels. The source access supplies its own old function
edge and selected degree; neither is a caller certificate. -/
theorem PathSite.complete_no_source_lambda_origin
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {ps : List Path} {marked : Marked}
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {oldPosition : Path} {origin : Labelled.Label} {oldBody : LTerm}
    (lookup : original.subterm oldPosition=some (.lam origin oldBody))
    (access : RootAccess site.net root) (word : accessWord site.net access.val=oldPosition)
    (finish : access.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)))
    {p : Path} {stamp body} (current : target.subterm p=some (.lam stamp body))
    (sameOrigin : stamp.lastAtom=origin.lastAtom) : False := by
  obtain ⟨_redexPosition,_appStamp,_argument,_position,_head,functionEdge,selected⟩ :=
    site.source_lambda_selected_origin matching flow positive lookup access word finish
  obtain ⟨n,atomic⟩ := initial.1 origin (LTerm.label_mem_of_subterm lookup)
  have last : stamp.lastAtom=some n := by rw [sameOrigin,atomic]; rfl
  exact relative_complete_no_lambda_origin initial relative normal labels functionEdge selected atomic current last

/-- A genuine occurrence-based source-port realization supplies the entire
old lookup/access provenance. No physical-node-to-origin injection is used. -/
theorem PathSite.complete_no_realized_lambda_origin
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {ps : List Path} {marked : Marked}
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {origin : Labelled.Label}
    (realizes : SourcePortRealizes original site.net root (.lamContext origin)
      (.inl ⟨.inr (.inr ()),.inl ()⟩))
    {p : Path} {stamp body} (current : target.subterm p=some (.lam stamp body))
    (sameOrigin : stamp.lastAtom=origin.lastAtom) : False := by
  cases realizes with
  | departure _lookup sourceRole _parent _word _roles _finish => cases sourceRole
  | lamContext lookup access word _shape _role finish =>
    exact site.complete_no_source_lambda_origin initial matching flow positive relative normal labels
      lookup access word finish current sameOrigin

/-- The completed current lambda trail itself supplies its original origin
and physical realization. Its fixed physical beta need not be reselected;
the forbidden endpoint is the canonical selected lambda context. -/
theorem PathSite.complete_lambda_trail_exclusion
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {ps : List Path} {marked : Marked}
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {physical : BetaEdge site.net} {env ctx p stamp body finish}
    (trail : PhysicalSyntaxTrail original root physical env ctx target p (.lam stamp body) finish)
    (atSelected : trail.toEndpoint=.inl ⟨.inr (.inr ()),.inl ()⟩) : False := by
  obtain ⟨n,lastAtom,sourceFinish⟩ := trail.image.lam_finish
  have realizes : SourcePortRealizes original site.net root finish (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
    rw [←atSelected]
    exact trail.toRealizes
  rw [sourceFinish] at realizes
  exact site.complete_no_realized_lambda_origin initial matching flow positive relative normal labels
    realizes trail.lookup (by rw [lastAtom]; rfl)
end
end Lamping.AG

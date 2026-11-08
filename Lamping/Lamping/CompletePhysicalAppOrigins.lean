import Lamping.Lamping.FunctionPortRoutes
import Lamping.Lamping.MatchingBetaRootVisibility
import Lamping.Lamping.MatchingSourceEdgeRealization

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original target : LTerm}

/-- An ACTUAL old application access at this physical beta supplies an old
selected syntax redex at that very word. In a shared graph several original
origins may realize the same physical app; no injectivity of origins into
physical nodes is assumed. -/
theorem BetaEdge.source_app_selected_origin
    (beta : BetaEdge g) (matching : Matches g root original.erase)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {oldPosition : Path} {origin : Labelled.Label} {oldFn oldArg : LTerm}
    (lookup : original.subterm oldPosition=some (.app origin oldFn oldArg))
    (access : RootAccess g root) (word : accessWord g access.val=oldPosition)
    (finish : access.val.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩))) :
    ∃ alpha body,original.subterm oldPosition=some (.app origin (.lam alpha body) oldArg) ∧
      SelectedDegree original (physicalBetaFiberPaths g root original.erase beta.app beta.lam) alpha := by
  obtain ⟨redex,redexWord,member⟩ := beta.root_app_visible matching flow positive access finish
  have atPosition : redex.val=oldPosition := redexWord.trans word
  obtain ⟨alpha,degree⟩ := degreeAt_exists original redex
  rw [atPosition] at degree member
  simp only [LTerm.degreeAt,lookup,Option.bind_some] at degree
  cases oldFn with
  | var label index => simp [LTerm.degree] at degree
  | app label fn arg => simp [LTerm.degree] at degree
  | lam label body =>
    have same : label=alpha := Option.some.inj degree
    cases same
    exact ⟨alpha,body,lookup,oldPosition,member,by simp only [LTerm.degreeAt,lookup,Option.bind_some,LTerm.degree]⟩

/-- The real source access certifies membership in THIS physical fiber.
Completion therefore excludes this application's origin in the current
syntax. This is the semantic bridge needed before dropping its direct
appCtx-to-argument turn from an actual syntax trail. -/
theorem BetaEdge.complete_no_source_app_origin
    (beta : BetaEdge g) (initial : INIT original) (matching : Matches g root original.erase)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {ps : List Path} {marked : Marked}
    (relative : Marked.RelativeHistory ps
      (Marked.mark (physicalBetaFiberPaths g root original.erase beta.app beta.lam) original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {oldPosition : Path} {origin : Labelled.Label} {oldFn oldArg : LTerm}
    (lookup : original.subterm oldPosition=some (.app origin oldFn oldArg))
    (access : RootAccess g root) (word : accessWord g access.val=oldPosition)
    (finish : access.val.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩)))
    {p : Path} {stamp fn arg} (current : target.subterm p=some (.app stamp fn arg))
    (sameOrigin : stamp.lastAtom=origin.lastAtom) : False := by
  obtain ⟨alpha,body,atRedex,selected⟩ := beta.source_app_selected_origin matching flow positive lookup access word finish
  obtain ⟨env,ctx,atHead⟩ := SourceSubterm.of_lookup original atRedex [] .external
  obtain ⟨n,atomic⟩ := initial.1 origin (LTerm.label_mem_of_subterm atRedex)
  have last : stamp.lastAtom=some n := by rw [sameOrigin,atomic]; rfl
  exact relative_complete_no_application_origin initial relative normal labels atHead selected atomic current last

/-- Consume the existing occurrence-bearing physical source-port witness.
Its actual access and old lookup are extracted rather than supplied as a
new semantic oracle, so shared origins remain distinct throughout. -/
theorem BetaEdge.complete_no_realized_app_origin
    (beta : BetaEdge g) (initial : INIT original) (matching : Matches g root original.erase)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {ps : List Path} {marked : Marked}
    (relative : Marked.RelativeHistory ps
      (Marked.mark (physicalBetaFiberPaths g root original.erase beta.app beta.lam) original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {origin : Labelled.Label}
    (realizes : SourcePortRealizes original g root (.appContext origin) (.inl ⟨beta.app,beta.appCtx⟩))
    {p : Path} {stamp fn arg} (current : target.subterm p=some (.app stamp fn arg))
    (sameOrigin : stamp.lastAtom=origin.lastAtom) : False := by
  cases realizes with
  | appContext lookup access word _shape _role finish =>
    exact beta.complete_no_source_app_origin initial matching flow positive relative normal labels
      lookup access word finish current sameOrigin
  | departure _lookup role _parent _word _roles _finish => cases role

end
end Lamping.AG

import Lamping.Lamping.BraAppAssignedChildPrefix
import Lamping.Lamping.ActionFunctionPadding
import Lamping.Lamping.ActionKeptFragmentComparison
import Lamping.Lamping.ActionRawOutsideCut

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.braAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.braAction Op.app i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => unaryRightCore Op.bra Op.app (Bij.refl _) i (j+1)
local notation "functionRaw" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitCut" => (Sum.inr (Sum.inl (Sum.inr (Sum.inl ()))) : Endpoint cut)
local notation "exitRaw" => (Sum.inl exitCut : PlugSegment cut rhs)
local notation "oldReader" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr ())) : Endpoint site.net)
local notation "copiedContext" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) appCtx) : Endpoint site.reduce)

/-- Literal OLD/actual-target crop for THIS bra/APP source occurrence.
The original rooted child a,b is preserved; the new seam is actual output.
No no-through, desired old split, frame or decreasing measure is a premise. -/
theorem ActualRedexAccess.bra_app_literal_crop
    {root : B} {current : LTerm} {redex : RedexOcc current.erase}
    (source : ActualRedexAccess site.net root redex)
    {directions : B → Bool} {depths : B → Int}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root=0)
    (transparency : Transparency site.net root)
    (sourceApp : source.parent.val.getLast?=some
      (site.net.wire (Sum.inl ⟨Sum.inr (Sum.inr ()),appCtx⟩)))
    (lamNode : K) (lamPort : Port (kept lamNode).sort)
    (sourceLam : source.child.val.getLast?=some
      (site.net.wire (Sum.inl ⟨Sum.inl lamNode,lamPort⟩)))
    {a b : Context} (sourceAssignment : Labelling site.net source.child.val a b) :
    ∃ target : ActualRedexAccess site.reduce root redex,
      Labelling site.reduce target.child.val a b ∧
      ∃ (principal : SiteActionPrincipal site) (oldTail : List (Endpoint site.net))
        (rawTail : List (PlugSegment cut rhs)) (newSeam : Context),
        source.connection.edges=reverseEdges principal.edges++oldReader::oldTail ∧
        target.connection.edges.map (plugEnd (cut).label (rhs).label).invFun=
          functionRaw::exitRaw::rawTail ∧
        ActionCanonicalBlocks site principal (exitRaw::rawTail) (oldReader::oldTail) ∧
        PlugLabelling cut rhs (exitRaw::rawTail) newSeam b := by
  obtain ⟨target,childLabels,parentFinish,rawTail,newSeam,_pieceLabels,rawPrefix,suffixLabels⟩ :=
    ActualRedexAccess.bra_app_copied_function_prefix site source matching inputs flow positive
      balance rootDepth transparency sourceApp lamNode lamPort sourceLam sourceAssignment
  obtain ⟨other,_otherLabels,_otherParentFinish,otherFinish,_readerPacket⟩ :=
    ActualRedexAccess.bra_app_assigned_child site source matching inputs flow positive
      balance rootDepth transparency sourceApp lamNode lamPort sourceLam sourceAssignment
  have targetMatches := site.action_matches_rootInputs (.bra .app i j lt)
    flow root positive balance rootDepth inputs transparency matching
  have sameChild : other.child=target.child := targetMatches.accessWord_injective
    (other.childWord.trans target.childWord.symm)
  have keptFinish : target.child.val.getLast?=some
      (site.reduce.wire (Sum.inl ⟨Sum.inl lamNode,lamPort⟩)) := by
    rw [←sameChild]
    exact otherFinish
  let rhsSplit : Bij (PlugSegment cut rhs) (Endpoint site.reduce) :=
    plugEnd (cut).label (rhs).label
  change target.connection.edges.map rhsSplit.invFun=functionRaw::exitRaw::rawTail at rawPrefix
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  have parentWord : accessWord site.net source.parent.val=accessWord site.reduce target.parent.val :=
    source.parentWord.trans target.parentWord.symm
  obtain ⟨parentInput,parentOutput,parentLabels⟩ := target.parent.property.1.1
  have parentCanonical := site.bra_function_padding_access flow root positive matching principal
    source.parent target.parent parentWord parentFinish parentLabels
  have wholeCanonical := (site.action_kept_canonical_access (.bra .app i j lt) flow root positive
    matching principal source.child target.child (source.childWord.trans target.childWord.symm)
    lamNode lamPort keptFinish childLabels).1
  change ActionCanonicalBlocks site principal
    (target.parent.val.map rhsSplit.invFun++[functionRaw,exitRaw])
    (source.parent.val++reverseEdges principal.edges++[oldReader]) at parentCanonical
  change ActionCanonicalBlocks site principal
    (target.child.val.map rhsSplit.invFun) source.child.val at wholeCanonical
  let parentRaw : List (PlugSegment cut rhs) := target.parent.val.map rhsSplit.invFun
  let wholeRaw : List (PlugSegment cut rhs) := target.child.val.map rhsSplit.invFun
  let padRaw : List (PlugSegment cut rhs) := parentRaw++[functionRaw,exitRaw]
  have rawSplit : wholeRaw=padRaw++rawTail := by
    change target.child.val.map rhsSplit.invFun=
      (target.parent.val.map rhsSplit.invFun++[functionRaw,exitRaw])++rawTail
    rw [target.split,List.map_append,rawPrefix]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have padLast : padRaw.getLast?=some exitRaw := by
    simp only [padRaw,List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,_cutSeam,oldWhole,suffixCanonical,_padLabels,_cutLabels⟩ :=
    wholeCanonical.cut_at_raw_parent site parentCanonical (childLabels.plug_decomposition cut rhs)
      rawSplit exitCut padLast
  have oldConnection : source.connection.edges=reverseEdges principal.edges++oldReader::oldTail := by
    have wholeEquality := source.split.symm.trans oldWhole
    have commonParent : source.parent.val++source.connection.edges=
        source.parent.val++(reverseEdges principal.edges++oldReader::oldTail) := by
      simpa only [List.append_assoc,List.singleton_append] using wholeEquality
    exact List.append_cancel_left commonParent
  exact ⟨target,childLabels,principal,oldTail,rawTail,newSeam,
    oldConnection,rawPrefix,suffixCanonical,suffixLabels⟩
end
end Lamping.AG

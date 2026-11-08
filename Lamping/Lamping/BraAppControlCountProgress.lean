import Lamping.Lamping.BraAppLiteralCanonicalCrop
import Lamping.Lamping.PhysicalControlWordTools
import Lamping.Lamping.CroAppEndpointLiteralCrop

namespace Lamping.AG
open Graph Lambda Lambda.Labelled ExposureScheduling
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.braAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.braAction Op.app i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => unaryRightCore Op.bra Op.app (Bij.refl Unit) i (j+1)
local notation "oldReader" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr ())) : Endpoint site.net)
local notation "functionRaw" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitRaw" => (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inl ()))) : Endpoint cut) : PlugSegment cut rhs)

/-- Complete local source blocks visit APP after their first departure. The
RHS index is explicit; this geometry does not identify bra j+1 with cro j-1. -/
private theorem unary_local_app_departure {rhsIndex : Nat}
    {principal : SiteActionPrincipal site}
    {inside : List (Endpoint (unaryRightCore Op.bra Op.app (Bij.refl Unit) i rhsIndex))}
    {old : List (Endpoint site.net)}
    (relation : UnaryCanonicalLocal (s:=schema) (k:=rhsIndex) site (Bij.refl Unit) principal inside old) :
    ∃ (before : List (Endpoint site.net)) (previous : Endpoint site.net)
      (port : Port (.op .app)) (after : List (Endpoint site.net)),
      old=before++previous::(Sum.inl ⟨Sum.inr (Sum.inr ()),port⟩)::after := by
  refine UnaryCanonicalLocal.rec (s:=schema) (k:=rhsIndex) (site:=site)
    (single:=Bij.refl Unit) (principal:=principal)
    (motive:=fun _ old _ =>
      ∃ (before : List (Endpoint site.net)) (previous : Endpoint site.net)
        (port : Port (.op .app)) (after : List (Endpoint site.net)),
        old=before++previous::(Sum.inl ⟨Sum.inr (Sum.inr ()),port⟩)::after)
    ?_ ?_ ?_ relation
  · intro q
    obtain ⟨oldPrefix,split⟩ := List.getLast?_eq_some_iff.mp principal.last
    refine ⟨site.net.wire (Sum.inl ⟨Sum.inr (Sum.inl ()),Sum.inr ()⟩)::oldPrefix,
      site.net.wire (Sum.inl ⟨Sum.inr (Sum.inr ()),Sum.inl ()⟩),Sum.inr q,[],?_⟩
    simp only [SiteActionPrincipal.crossing,split,List.cons_append,List.append_assoc]
    rfl
  · intro q
    have head : (reverseEdges principal.edges).head?=
        some (Sum.inl ⟨Sum.inr (Sum.inr ()),Sum.inl ()⟩) := by
      simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,
        Option.map_some,Pairing.involutive]
    obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp head
    refine ⟨[],site.net.wire (Sum.inl ⟨Sum.inr (Sum.inr ()),Sum.inr q⟩),Sum.inl (),
      tail++[oldReader],?_⟩
    rw [principal.reverse_crossing_edges site,split]
    rfl
  · intro p q
    exact ⟨[],site.net.wire (Sum.inl ⟨Sum.inr (Sum.inr ()),Sum.inr p⟩),Sum.inr q,[],rfl⟩

private theorem local_app_departure {principal : SiteActionPrincipal site} {inside old}
    (relation : ActionCanonicalLocal site principal inside old) :
    ∃ (before : List (Endpoint site.net)) (previous : Endpoint site.net)
      (port : Port (.op .app)) (after : List (Endpoint site.net)),
      old=before++previous::(Sum.inl ⟨Sum.inr (Sum.inr ()),port⟩)::after := by
  cases relation with
  | bra relation => exact unary_local_app_departure site (rhsIndex:=j+1) relation

/-- No through block survives in a canonical suffix of THIS connection:
each such block would provide a forbidden interior proper APP departure. -/
private theorem suffix_raw_control_word
    {principal : SiteActionPrincipal site} {raw old}
    (connection : RedexConnection site.net)
    (canonical : ActionCanonicalBlocks site principal raw old)
    (before : List (Endpoint site.net)) (sourceSplit : connection.edges=before++old)
    {a b : Context} (labels : PlugLabelling cut rhs raw a b) :
    rawControlWord cut rhs raw=controlWord site.net old := by
  induction canonical generalizing before a b with
  | single e => rfl
  | @outside e f tail old rest ih =>
    obtain ⟨middle,turn,remaining⟩ := outside_cons_view cut rhs labels
    have nextSplit : connection.edges=(before++[site.outsideEnd e])++old := by
      simpa only [List.append_assoc,List.singleton_append] using sourceSplit
    have restWord := ih (before++[site.outsideEnd e]) nextSplit remaining
    obtain ⟨oldTail,oldEq⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
    rw [oldEq] at restWord ⊢
    change endpointControlWord cut f++rawControlWord cut rhs (Sum.inl f::tail)=
      endpointControlWord site.net (site.outsideEnd f)++
        controlWord site.net (site.outsideEnd f::oldTail)
    rw [restWord,site.outside_control_port_word turn]
  | @through e exit tail old inside front route start rest ih =>
    obtain ⟨oldTail,oldEq⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
    obtain ⟨localBefore,previous,port,localAfter,localSplit⟩ := local_app_departure site route
    have actualCut : connection.edges=(before++localBefore)++previous::
        (Sum.inl ⟨Sum.inr (Sum.inr ()),port⟩)::(localAfter++oldTail) := by
      calc
        connection.edges=before++((front++[site.outsideEnd (Sum.inr (Sum.inl (Sum.inr exit)))])++oldTail) := by
          simpa only [oldEq,List.append_assoc,List.singleton_append] using sourceSplit
        _=(before++localBefore)++previous::(Sum.inl ⟨Sum.inr (Sum.inr ()),port⟩)::
            (localAfter++oldTail) := by
          rw [localSplit]
          simp only [List.append_assoc,List.cons_append]
    exact False.elim (connection.no_internal_proper_departure (Sum.inr (Sum.inr ())) port
      (Or.inl rfl) (before++localBefore) previous (localAfter++oldTail) actualCut)

/-- Actual whole suffix transport; retainedness is proved, not supplied. -/
theorem ActionCanonicalBlocks.bra_app_control_suffix_word
    {principal : SiteActionPrincipal site} {raw old}
    (connection : RedexConnection site.net)
    (canonical : ActionCanonicalBlocks site principal raw old)
    (before : List (Endpoint site.net)) (sourceSplit : connection.edges=before++old)
    {a b : Context} (labels : PlugLabelling cut rhs raw a b) :
    controlWord site.reduce (raw.map (plugEnd (cut).label (rhs).label))=
      controlWord site.net old := by
  change controlWord (plug cut rhs) (raw.map (plugEnd (cut).label (rhs).label))=
    controlWord site.net old
  rw [controlWord_plug_map cut rhs raw]
  exact suffix_raw_control_word site connection canonical before sourceSplit labels

private theorem copied_function_word (rawTail : List (PlugSegment cut rhs)) :
    controlWord site.reduce ((functionRaw::exitRaw::rawTail).map (plugEnd (cut).label (rhs).label))=
      controlWord site.reduce ((exitRaw::rawTail).map (plugEnd (cut).label (rhs).label)) := by
  change controlWord (plug cut rhs)
      ((functionRaw::exitRaw::rawTail).map (plugEnd (cut).label (rhs).label))=
    controlWord (plug cut rhs)
      ((exitRaw::rawTail).map (plugEnd (cut).label (rhs).label))
  rw [controlWord_plug_map cut rhs,controlWord_plug_map cut rhs]
  rfl

private theorem original_reader_word (principal : SiteActionPrincipal site)
    (oldTail : List (Endpoint site.net)) :
    controlWord site.net (reverseEdges principal.edges++oldReader::oldTail)=
      false::controlWord site.net (oldReader::oldTail) := by
  have head : (reverseEdges principal.edges).head?=
      some (Sum.inl ⟨Sum.inr (Sum.inr ()),Sum.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,
      Option.map_some,Pairing.involutive]
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp head
  have empty := transparent_control_word site.net (reverseEdges principal.edges)
    (transparent_reverse_turns principal.edges principal.transparent)
  rw [split] at empty ⊢
  change tail.flatMap (endpointControlWord site.net)=[] at empty
  change (tail++oldReader::oldTail).flatMap (endpointControlWord site.net)=_
  rw [List.flatMap_append,empty]
  rfl

/-- The SAME actual bra/APP target connection, with the original child a,b,
loses one reader. No desired target, no-through, frame or rank is a premise. -/
theorem ActualRedexAccess.bra_app_control_count_progress
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
      controlWord site.net source.connection.edges=false::controlWord site.reduce target.connection.edges ∧
      controlCount site.reduce target.connection.edges+1=controlCount site.net source.connection.edges ∧
      controlCount site.reduce target.connection.edges<controlCount site.net source.connection.edges := by
  obtain ⟨target,childLabels,principal,oldTail,rawTail,newSeam,oldSplit,newRaw,canonical,labels⟩ :=
    source.bra_app_literal_crop site matching inputs flow positive balance rootDepth transparency
      sourceApp lamNode lamPort sourceLam sourceAssignment
  have suffixWord := canonical.bra_app_control_suffix_word site source.connection
    (reverseEdges principal.edges) oldSplit labels
  let rhsSplit : Bij (PlugSegment cut rhs) (Endpoint site.reduce) :=
    plugEnd (cut).label (rhs).label
  change target.connection.edges.map rhsSplit.invFun=functionRaw::exitRaw::rawTail at newRaw
  have mapped := congrArg (List.map rhsSplit) newRaw
  have newLiteral : target.connection.edges=
      (functionRaw::exitRaw::rawTail).map rhsSplit := by
    simpa only [List.map_map,Function.comp_def,rhsSplit.right_inv,List.map_id_fun'] using mapped
  have actualSuffixWord : controlWord site.reduce target.connection.edges=
      controlWord site.net (oldReader::oldTail) := by
    rw [newLiteral,copied_function_word site rawTail]
    exact suffixWord
  have fullWord : controlWord site.net source.connection.edges=
      false::controlWord site.reduce target.connection.edges := by
    rw [oldSplit,original_reader_word site principal oldTail,←actualSuffixWord]
  have count : controlCount site.reduce target.connection.edges+1=
      controlCount site.net source.connection.edges := by
    change (controlWord site.reduce target.connection.edges).length+1=
      (controlWord site.net source.connection.edges).length
    rw [fullWord]
    rfl
  exact ⟨target,childLabels,fullWord,count,by omega⟩
end
end Lamping.AG

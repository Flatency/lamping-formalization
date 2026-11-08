import Lamping.Lamping.FanAppLiteralCanonicalCrop
import Lamping.Lamping.PhysicalControlWordTools
import Lamping.Lamping.CroAppEndpointLiteralCrop

namespace Lamping.AG
open Graph Lambda Lambda.Labelled ExposureScheduling
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.fanAction Op.app i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => fanRight Op.app i j
local notation "oldReader" => (fun branch : Bool =>
  (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr branch)) : Endpoint site.net))
local notation "functionRaw" => (fun branch : Bool =>
  (Sum.inr (Sum.inl (Sigma.mk (Sum.inl branch) (Sum.inl ()))) : PlugSegment cut rhs))
local notation "exitRaw" => (fun branch : Bool =>
  (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inl branch)))) : PlugSegment cut rhs))

/-- Every complete fan/APP local ancestor visits the selected APP after its
entry. Both crossing directions and passive passages retain the real branch. -/
private theorem fan_local_app_departure {principal : SiteActionPrincipal site}
    {inside : List (Endpoint rhs)} {old : List (Endpoint site.net)}
    (relation : FanCanonicalLocal site principal inside old) :
    ∃ (before : List (Endpoint site.net)) (previous : Endpoint site.net)
      (port : Port (.op .app)) (after : List (Endpoint site.net)),
      old=before++previous::(Sum.inl ⟨Sum.inr (Sum.inr ()),port⟩)::after := by
  refine FanCanonicalLocal.rec (f:=Op.app) (i:=i) (j:=j) (lt:=lt) (site:=site)
    (principal:=principal)
    (motive:=fun _ old _ =>
      ∃ (before : List (Endpoint site.net)) (previous : Endpoint site.net)
        (port : Port (.op .app)) (after : List (Endpoint site.net)),
        old=before++previous::(Sum.inl ⟨Sum.inr (Sum.inr ()),port⟩)::after)
    ?_ ?_ ?_ relation
  · intro branch q
    obtain ⟨oldPrefix,split⟩ := List.getLast?_eq_some_iff.mp principal.last
    refine ⟨site.net.wire (Sum.inl ⟨Sum.inr (Sum.inl ()),Sum.inr branch⟩)::oldPrefix,
      site.net.wire (Sum.inl ⟨Sum.inr (Sum.inr ()),Sum.inl ()⟩),Sum.inr q,[],?_⟩
    simp only [SiteActionPrincipal.crossing,split,List.cons_append,List.append_assoc]
    rfl
  · intro branch q
    have head : (reverseEdges principal.edges).head?=
        some (Sum.inl ⟨Sum.inr (Sum.inr ()),Sum.inl ()⟩) := by
      simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,
        Option.map_some,Pairing.involutive]
    obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp head
    refine ⟨[],site.net.wire (Sum.inl ⟨Sum.inr (Sum.inr ()),Sum.inr q⟩),Sum.inl (),
      tail++[oldReader branch],?_⟩
    rw [principal.reverse_crossing_edges site,split]
    rfl
  · intro _branch p q
    exact ⟨[],site.net.wire (Sum.inl ⟨Sum.inr (Sum.inr ()),Sum.inr p⟩),Sum.inr q,[],rfl⟩

private theorem retained_word {principal : SiteActionPrincipal site} {raw old}
    (connection : RedexConnection site.net) (canonical : ActionCanonicalBlocks site principal raw old)
    (before : List (Endpoint site.net)) (actualSuffix : connection.edges=before++old)
    {a b : Context} (labels : PlugLabelling cut rhs raw a b) :
    rawControlWord cut rhs raw=controlWord site.net old := by
  induction canonical generalizing before a b with
  | single e => rfl
  | @outside e f tail old rest ih =>
    obtain ⟨middle,turn,remaining⟩ := outside_cons_view cut rhs labels
    have nextSuffix : connection.edges=(before++[site.outsideEnd e])++old := by
      simpa only [List.append_assoc,List.singleton_append] using actualSuffix
    have nextWord := ih (before++[site.outsideEnd e]) nextSuffix remaining
    obtain ⟨oldTail,oldEq⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
    rw [oldEq] at nextWord ⊢
    change endpointControlWord cut f++rawControlWord cut rhs (Sum.inl f::tail)=
      endpointControlWord site.net (site.outsideEnd f)++controlWord site.net (site.outsideEnd f::oldTail)
    rw [nextWord,site.outside_control_port_word turn]
  | @through e exit tail old inside front route start rest ih =>
    obtain ⟨oldTail,oldEq⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
    have localVisit : ∃ (localBefore : List (Endpoint site.net)) (previous : Endpoint site.net)
        (port : Port (.op .app)) (localAfter : List (Endpoint site.net)),
        front++[site.outsideEnd (Sum.inr (Sum.inl (Sum.inr exit)))]=
          localBefore++previous::(Sum.inl ⟨Sum.inr (Sum.inr ()),port⟩)::localAfter := by
      cases route with
      | fan relation => exact fan_local_app_departure site relation
    obtain ⟨localBefore,previous,port,localAfter,localSplit⟩ := localVisit
    have actualCut : connection.edges=(before++localBefore)++previous::
        (Sum.inl ⟨Sum.inr (Sum.inr ()),port⟩)::(localAfter++oldTail) := by
      calc
        connection.edges=before++((front++[site.outsideEnd (Sum.inr (Sum.inl (Sum.inr exit)))])++oldTail) := by
          simpa only [oldEq,List.append_assoc,List.singleton_append] using actualSuffix
        _=(before++localBefore)++previous::(Sum.inl ⟨Sum.inr (Sum.inr ()),port⟩)::
            (localAfter++oldTail) := by
          rw [localSplit]
          simp only [List.append_assoc,List.cons_append]
    exact False.elim (connection.no_internal_proper_departure (Sum.inr (Sum.inr ())) port
      (Or.inl rfl) (before++localBefore) previous (localAfter++oldTail) actualCut)

/-- Whole-word transport of the actual suffix; NoThrough is derived from
its source connection and the actual fan local constructors. -/
theorem ActionCanonicalBlocks.fan_app_control_suffix_word
    {principal : SiteActionPrincipal site} {raw old}
    (connection : RedexConnection site.net) (canonical : ActionCanonicalBlocks site principal raw old)
    (before : List (Endpoint site.net)) (actualSuffix : connection.edges=before++old)
    {a b : Context} (labels : PlugLabelling cut rhs raw a b) :
    controlWord site.reduce (raw.map (plugEnd (cut).label (rhs).label))=controlWord site.net old := by
  change controlWord (plug cut rhs) (raw.map (plugEnd (cut).label (rhs).label))=controlWord site.net old
  rw [controlWord_plug_map cut rhs raw]
  exact retained_word site connection canonical before actualSuffix labels

private theorem copied_function_word (branch : Bool) (tail : List (PlugSegment cut rhs)) :
    controlWord site.reduce (((functionRaw branch)::(exitRaw branch)::tail).map (plugEnd (cut).label (rhs).label))=
      controlWord site.reduce (((exitRaw branch)::tail).map (plugEnd (cut).label (rhs).label)) := by
  change controlWord (plug cut rhs)
      (((functionRaw branch)::(exitRaw branch)::tail).map (plugEnd (cut).label (rhs).label))=
    controlWord (plug cut rhs)
      (((exitRaw branch)::tail).map (plugEnd (cut).label (rhs).label))
  rw [controlWord_plug_map cut rhs,controlWord_plug_map cut rhs]
  rfl

private theorem original_reader_word (principal : SiteActionPrincipal site) (branch : Bool)
    (tail : List (Endpoint site.net)) :
    controlWord site.net (reverseEdges principal.edges++(oldReader branch)::tail)=
      false::controlWord site.net ((oldReader branch)::tail) := by
  have head : (reverseEdges principal.edges).head?=
      some (Sum.inl ⟨Sum.inr (Sum.inr ()),Sum.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,
      Option.map_some,Pairing.involutive]
  obtain ⟨oldPrefix,split⟩ := List.head?_eq_some_iff.mp head
  have empty := transparent_control_word site.net (reverseEdges principal.edges)
    (transparent_reverse_turns principal.edges principal.transparent)
  rw [split] at empty ⊢
  change oldPrefix.flatMap (endpointControlWord site.net)=[] at empty
  change (oldPrefix++(oldReader branch)::tail).flatMap (endpointControlWord site.net)=_
  rw [List.flatMap_append,empty]
  rfl

/-- Fix the actual branch/target and whole child assignment before the word
identity; the SAME target connection then loses exactly one reader. -/
theorem ActualRedexAccess.fan_app_control_count_progress
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
    ∃ (_branch : Bool) (target : ActualRedexAccess site.reduce root redex),
      Labelling site.reduce target.child.val a b ∧
      controlWord site.net source.connection.edges=false::controlWord site.reduce target.connection.edges ∧
      controlCount site.reduce target.connection.edges+1=controlCount site.net source.connection.edges ∧
      controlCount site.reduce target.connection.edges<controlCount site.net source.connection.edges := by
  obtain ⟨branch,target,childLabels,principal,oldTail,rawTail,newSeam,oldSplit,newRaw,canonical,labels⟩ :=
    source.fan_app_literal_crop site matching inputs flow positive balance rootDepth transparency
      sourceApp lamNode lamPort sourceLam sourceAssignment
  have suffixWord := canonical.fan_app_control_suffix_word site source.connection
    (reverseEdges principal.edges) oldSplit labels
  let rhsSplit : Bij (PlugSegment cut rhs) (Endpoint site.reduce) :=
    plugEnd (cut).label (rhs).label
  change target.connection.edges.map rhsSplit.invFun=
    (functionRaw branch)::(exitRaw branch)::rawTail at newRaw
  have mapped := congrArg (List.map rhsSplit) newRaw
  have newLiteral : target.connection.edges=((functionRaw branch)::(exitRaw branch)::rawTail).map rhsSplit := by
    simpa only [List.map_map,Function.comp_def,rhsSplit.right_inv,List.map_id_fun'] using mapped
  have targetWord : controlWord site.reduce target.connection.edges=controlWord site.net ((oldReader branch)::oldTail) := by
    rw [newLiteral,copied_function_word site branch rawTail]
    exact suffixWord
  have fullWord : controlWord site.net source.connection.edges=false::controlWord site.reduce target.connection.edges := by
    rw [oldSplit,original_reader_word site principal branch oldTail,←targetWord]
  have count : controlCount site.reduce target.connection.edges+1=controlCount site.net source.connection.edges := by
    change (controlWord site.reduce target.connection.edges).length+1=(controlWord site.net source.connection.edges).length
    rw [fullWord]
    rfl
  exact ⟨branch,target,childLabels,fullWord,count,by omega⟩
end
end Lamping.AG

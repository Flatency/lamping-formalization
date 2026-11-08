import Lamping.Lamping.CroAppEndpointLiteralCrop
import Lamping.Lamping.ExposureControlWords

namespace Lamping.AG
open Graph Lambda Lambda.Labelled ExposureScheduling
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.croAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.croAction Op.app i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => unaryRightCore Op.cro Op.app (Bij.refl _) i (j-1)
local notation "oldExit" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr ())) : Endpoint site.net)
local notation "fnRaw" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitRaw" => (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inl ()))) : Endpoint cut) : PlugSegment cut rhs)

private def endpointWord {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    (g : Net signature N D U) : Endpoint g → List Bool
  | .inl ⟨node,p⟩ => controlPortWord (g.label node).sort p
  | .inr _ => []
private def rawWord (raw : List (PlugSegment cut rhs)) : List Bool :=
  raw.tail.flatMap (Sum.elim (endpointWord cut) (endpointWord rhs))

/-- Every complete local source block contains a selected APP departure
strictly after its entry. This is physical list geometry, not a label decoder. -/
private theorem unary_local_has_app_turn {rhsIndex : Nat}
    {principal : SiteActionPrincipal site}
    {inside : List (Endpoint (unaryRightCore Op.cro Op.app (Bij.refl Unit) i rhsIndex))}
    {old : List (Endpoint site.net)}
    (localRelation : UnaryCanonicalLocal (s:=schema) (k:=rhsIndex) site (Bij.refl Unit) principal inside old) :
    ∃ (frontBefore : List (Endpoint site.net)) (previous : Endpoint site.net)
      (port : Port (.op .app)) (frontAfter : List (Endpoint site.net)),
      old=frontBefore++previous::(.inl ⟨.inr (.inr ()),port⟩)::frontAfter := by
  refine UnaryCanonicalLocal.rec (s:=schema) (k:=rhsIndex) (site:=site)
    (single:=Bij.refl Unit) (principal:=principal)
    (motive:=fun _ old _ =>
      ∃ (frontBefore : List (Endpoint site.net)) (previous : Endpoint site.net)
        (port : Port (.op .app)) (frontAfter : List (Endpoint site.net)),
        old=frontBefore++previous::(.inl ⟨.inr (.inr ()),port⟩)::frontAfter)
    ?_ ?_ ?_ localRelation
  · intro q
    obtain ⟨routeBefore,routeEq⟩ := List.getLast?_eq_some_iff.mp principal.last
    refine ⟨site.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩)::routeBefore,
      site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩),.inr q,[],?_⟩
    simp only [SiteActionPrincipal.crossing,routeEq,List.cons_append,List.append_assoc]
    rfl
  · intro q
    have head : (reverseEdges principal.edges).head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
      simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
    obtain ⟨routeTail,routeEq⟩ := List.head?_eq_some_iff.mp head
    refine ⟨[],site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩),.inl (),
      routeTail++[oldExit],?_⟩
    rw [principal.reverse_crossing_edges site,routeEq]
    rfl
  · intro p q
    exact ⟨[],site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩),.inr q,[],rfl⟩

private theorem local_has_app_turn {principal : SiteActionPrincipal site} {inside old}
    (localRelation : ActionCanonicalLocal site principal inside old) :
    ∃ (frontBefore : List (Endpoint site.net)) (previous : Endpoint site.net)
      (port : Port (.op .app)) (frontAfter : List (Endpoint site.net)),
      old=frontBefore++previous::(.inl ⟨.inr (.inr ()),port⟩)::frontAfter := by
  cases localRelation with
  | cro localRelation => exact unary_local_has_app_turn site (rhsIndex:=j-1) localRelation

private theorem raw_outside_view {e f : Endpoint cut} {tail} {a b : Context}
    (labels : PlugLabelling cut rhs (.inl e::.inl f::tail) a b) :
    ∃ middle,LabelledTurn cut ((cut).wire e) f a middle ∧
      PlugLabelling cut rhs (.inl f::tail) middle b := by
  cases labels with
  | cons turn rest =>
    change PlugTurn cut rhs (.inl ((cut).wire e)) (.inl f) a _ at turn
    generalize arrivalEq : (cut).wire e=arrival at turn
    cases turn with
    | left localTurn => exact ⟨_,by simpa only [arrivalEq] using localTurn,rest⟩

private theorem endpoint_word_outside {e f : Endpoint cut} {a b : Context}
    (turn : LabelledTurn cut ((cut).wire e) f a b) :
    endpointWord site.net (site.outsideEnd f)=endpointWord cut f := by
  generalize arrivalEq : (cut).wire e=arrival at turn
  cases turn <;> rfl

/-- A factual suffix of THIS actual redex connection cannot contain any
through block at a cro/APP site. Its source would contain an internal proper
APP departure. This derives retained-word transport; no retained/no-through
or desired target rank certificate is a caller premise. -/
private theorem retained_suffix_raw_word
    {principal : SiteActionPrincipal site} {raw old}
    (connection : RedexConnection site.net) (canonical : ActionCanonicalBlocks site principal raw old)
    (before : List (Endpoint site.net)) (sourceSplit : connection.edges=before++old)
    {a b : Context} (labels : PlugLabelling cut rhs raw a b) :
    rawWord site raw=controlWord site.net old := by
  induction canonical generalizing before a b with
  | single e => rfl
  | @outside e f tail old rest ih =>
    obtain ⟨middle,turn,remaining⟩ := raw_outside_view site labels
    have nextSplit : connection.edges=(before++[site.outsideEnd e])++old := by
      simpa only [List.append_assoc,List.singleton_append] using sourceSplit
    have restWord := ih (before++[site.outsideEnd e]) nextSplit remaining
    obtain ⟨oldTail,oldEq⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
    rw [oldEq] at restWord ⊢
    change endpointWord cut f++rawWord site (.inl f::tail)=
      endpointWord site.net (site.outsideEnd f)++controlWord site.net (site.outsideEnd f::oldTail)
    rw [restWord,endpoint_word_outside site turn]
  | @through e exit tail old inside front route start rest ih =>
    obtain ⟨oldTail,oldEq⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
    obtain ⟨frontBefore,previous,port,frontAfter,localSplit⟩ := local_has_app_turn site route
    have actualCut : connection.edges=(before++frontBefore)++previous::
        (.inl ⟨.inr (.inr ()),port⟩)::(frontAfter++oldTail) := by
      calc
        connection.edges=before++((front++[site.outsideEnd (.inr (.inl (.inr exit)))])++oldTail) := by
          simpa only [oldEq,List.append_assoc,List.singleton_append] using sourceSplit
        _=(before++frontBefore)++previous::(.inl ⟨.inr (.inr ()),port⟩)::(frontAfter++oldTail) := by
          rw [localSplit]
          simp only [List.append_assoc,List.cons_append]
    exact False.elim (connection.no_internal_proper_departure (.inr (.inr ())) port
      (Or.inl rfl) (before++frontBefore) previous (frontAfter++oldTail) actualCut)

private theorem physical_word_raw (raw : List (PlugSegment cut rhs)) :
    controlWord site.reduce (raw.map (plugEnd (cut).label (rhs).label))=rawWord site raw := by
  cases raw with
  | nil => rfl
  | cons e tail =>
    change (tail.map (plugEnd (cut).label (rhs).label)).flatMap (endpointWord site.reduce)=
      tail.flatMap (Sum.elim (endpointWord cut) (endpointWord rhs))
    rw [List.flatMap_map]
    apply congrArg (fun f => tail.flatMap f)
    funext piece
    rcases piece with (⟨node,p⟩|((boundary|frontier)|⟨vertex,direction⟩))|
      (⟨node,p⟩|(frontier|⟨vertex,direction⟩)) <;> rfl

/-- Public form uses actual physical paths, not the private raw-word helper. -/
theorem ActionCanonicalBlocks.cro_app_control_suffix_word
    {principal : SiteActionPrincipal site} {raw old}
    (connection : RedexConnection site.net) (canonical : ActionCanonicalBlocks site principal raw old)
    (before : List (Endpoint site.net)) (sourceSplit : connection.edges=before++old)
    {a b : Context} (labels : PlugLabelling cut rhs raw a b) :
    controlWord site.reduce (raw.map (plugEnd (cut).label (rhs).label))=controlWord site.net old := by
  rw [physical_word_raw site raw]
  exact retained_suffix_raw_word site connection canonical before sourceSplit labels

private theorem glued_function_word (rawTail : List (PlugSegment cut rhs)) :
    controlWord site.reduce ((fnRaw::exitRaw::rawTail).map (plugEnd (cut).label (rhs).label))=
      controlWord site.reduce ((exitRaw::rawTail).map (plugEnd (cut).label (rhs).label)) := by
  rw [physical_word_raw,physical_word_raw]
  rfl

private theorem transparent_word {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    (g : Net signature N D U) (es : List (Endpoint g))
    (transparent : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) : controlWord g es=[] := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases es with
    | nil => rfl
    | cons f tail =>
      obtain ⟨w,d,_arrives,leaves⟩ := transparent e f (by simp)
      have rest := ih (by intro x y pair;exact transparent x y (List.mem_cons_of_mem _ pair))
      change endpointWord g f++controlWord g (f::tail)=[]
      rw [rest,leaves]
      rfl

private theorem old_cro_crop_word (principal : SiteActionPrincipal site) (oldTail : List (Endpoint site.net)) :
    controlWord site.net (reverseEdges principal.edges++oldExit::oldTail)=
      false::controlWord site.net (oldExit::oldTail) := by
  have head : (reverseEdges principal.edges).head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
  obtain ⟨routeTail,routeEq⟩ := List.head?_eq_some_iff.mp head
  have empty := transparent_word site.net (reverseEdges principal.edges)
    (transparent_reverse_turns principal.edges principal.transparent)
  rw [routeEq] at empty ⊢
  change routeTail.flatMap (endpointWord site.net)=[] at empty
  change (routeTail++oldExit::oldTail).flatMap (endpointWord site.net)=_
  rw [List.flatMap_append,empty]
  rfl

/-- One actual cro/APP endpoint action deletes precisely the first reader
from the SAME actual redex connection. Target identity/context transport is
provided by the literal crop theorem before suffix/rank reasoning. -/
theorem ActualRedexAccess.cro_app_control_count_progress
    {root : B} {current : LTerm} {redex : RedexOcc current.erase}
    (source : ActualRedexAccess site.net root redex)
    {directions : B → Bool} {depths : B → Int}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root=0)
    (oldT : Transparency site.net root)
    (sourceApp : source.parent.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)))
    (lamNode : K) (lamPort : Port (kept lamNode).sort)
    (sourceLam : source.child.val.getLast?=some (site.net.wire (.inl ⟨.inl lamNode,lamPort⟩)))
    {a b : Context} (sourceAssignment : Labelling site.net source.child.val a b) :
    ∃ target : ActualRedexAccess site.reduce root redex,
      Labelling site.reduce target.child.val a b ∧
      controlWord site.net source.connection.edges=false::controlWord site.reduce target.connection.edges ∧
      controlCount site.reduce target.connection.edges+1=controlCount site.net source.connection.edges ∧
      controlCount site.reduce target.connection.edges<controlCount site.net source.connection.edges := by
  obtain ⟨target,childLabels,principal,oldTail,rawTail,newSeam,oldSplit,newRaw,suffixCanonical,suffixLabels⟩ :=
    source.cro_app_literal_crop site matching inputs flow positive balance rootDepth oldT
      sourceApp lamNode lamPort sourceLam sourceAssignment
  have suffixWord := suffixCanonical.cro_app_control_suffix_word site source.connection
    (reverseEdges principal.edges) oldSplit suffixLabels
  have mapped := congrArg (List.map (plugEnd (cut).label (rhs).label)) newRaw
  have newLiteral : target.connection.edges=(fnRaw::exitRaw::rawTail).map (plugEnd (cut).label (rhs).label) := by
    simpa only [List.map_map,Function.comp_def,(plugEnd (cut).label (rhs).label).right_inv,
      List.map_id_fun'] using mapped
  have actualSuffixWord : controlWord site.reduce target.connection.edges=
      controlWord site.net (oldExit::oldTail) := by
    rw [newLiteral,glued_function_word site rawTail]
    exact suffixWord
  have fullWord : controlWord site.net source.connection.edges=
      false::controlWord site.reduce target.connection.edges := by
    rw [oldSplit,old_cro_crop_word site principal oldTail,←actualSuffixWord]
  have count : controlCount site.reduce target.connection.edges+1=
      controlCount site.net source.connection.edges := by
    change (controlWord site.reduce target.connection.edges).length+1=
      (controlWord site.net source.connection.edges).length
    rw [fullWord]
    rfl
  exact ⟨target,childLabels,fullWord,count,by omega⟩
end
end Lamping.AG

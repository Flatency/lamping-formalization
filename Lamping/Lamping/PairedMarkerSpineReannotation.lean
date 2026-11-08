import Lamping.Lamping.PairedMarkerLeafGeometry
import Lamping.Lamping.DirectedMarkerSpineIncidence
import Lamping.Lambda.BetaPreimageErasure
namespace Lamping.Lambda.Labelled
variable {source target : LTerm}
open SyntaxIncidence
namespace SpineReannotation
variable {source target t u s ss tt : LTerm}

theorem paired_lookup {left right node : LTerm}
    (same : left.erase=right.erase) (lookup : left.subterm p=some node) :
    ∃ other,right.subterm p=some other ∧other.erase=node.erase := by
  have bare : subtermAt right.erase p=some node.erase := by
    rw [←same,←LTerm.erase_subterm,lookup];rfl
  rw [←LTerm.erase_subterm] at bare
  exact Option.map_eq_some_iff.mp bare

theorem history_erase (left : History ps source target)
    (right : History ps localSource localTarget) (same : source.erase=localSource.erase) :
    target.erase=localTarget.erase := by
  obtain ⟨candidate,lifted,erased⟩ := lift_history left.betaHistory localSource same.symm
  rw [lifted.deterministic right] at erased
  exact erased.symm

theorem proper_reannotate (same : t.erase=u.erase) (proper : ProperAt t p) : ProperAt u p := by
  rcases proper with ⟨a,f,b,h⟩ |⟨a,b,h⟩
  · obtain ⟨other,atOther,erased⟩:=paired_lookup same h
    cases other with
    | var a i => cases erased
    | lam a b => cases erased
    | app a f b => exact Or.inl ⟨a,f,b,atOther⟩
  · obtain ⟨other,atOther,erased⟩:=paired_lookup same h
    cases other with
    | var a i => cases erased
    | app a f b => cases erased
    | lam a b => exact Or.inr ⟨a,b,atOther⟩

def vertex (same : t.erase=u.erase) : Vertex t → Vertex u
  | none => none
  | some p => some ⟨p.val,proper_reannotate same p.property⟩

theorem source_reannotate (same : t.erase=u.erase) {v : Vertex t}
    (actual : Source t e v) : Source u e (vertex same v) := by
  cases v with
  | none => exact actual
  | some p =>
    obtain ⟨s,child,port,split,lookup,departure⟩:=actual
    obtain ⟨other,otherLookup,erased⟩:=paired_lookup same lookup
    cases departure with
    | fn =>
      cases other with
      | var a i => cases erased
      | lam a b => cases erased
      | app a f b => exact ⟨_,_,_,split,otherLookup,.fn⟩
    | arg =>
      cases other with
      | var a i => cases erased
      | lam a b => cases erased
      | app a f b => exact ⟨_,_,_,split,otherLookup,.arg⟩
    | body =>
      cases other with
      | var a i => cases erased
      | app a f b => cases erased
      | lam a b => exact ⟨_,_,_,split,otherLookup,.body⟩

theorem target_reannotate (same : t.erase=u.erase) {v : Vertex t}
    (actual : Target t e v) : Target u e (vertex same v) := by
  cases v with
  | none => exact False.elim actual
  | some p =>
    rcases actual with rfl |⟨a,i,b,body,tail,lookup,binder,split,depth⟩
    · exact Or.inl rfl
    · obtain ⟨other,otherLookup,erased⟩:=paired_lookup same lookup
      obtain ⟨otherBinder,binderLookup,binderErase⟩:=paired_lookup same binder
      cases other with
      | app a f b => cases erased
      | lam a b => cases erased
      | var c j =>
        have index : j=i:=Term.var.inj erased
        cases otherBinder with
        | var a i => cases binderErase
        | app a f b => cases binderErase
        | lam c b =>
          exact Or.inr ⟨_,_,_,_,tail,otherLookup,binderLookup,split,index.trans depth⟩

def snapshot (same : t.erase=u.erase) (s : IncomingIncidenceSnapshot t e) :
    IncomingIncidenceSnapshot u e :=
  ⟨vertex same s.fromVertex,vertex same s.toVertex,
    source_reannotate same s.fromSpec,target_reannotate same s.toSpec⟩

theorem vertex_near (same : t.erase=u.erase) (s : IncomingIncidenceSnapshot t e) (d : Bool) :
    (snapshot same s).near d=vertex same (s.near d) := by cases d <;> rfl

theorem vertex_far (same : t.erase=u.erase) (s : IncomingIncidenceSnapshot t e) (d : Bool) :
    (snapshot same s).far d=vertex same (s.far d) := by cases d <;> rfl

theorem vertex_origin (sourceSame : s.erase=ss.erase) (targetSame : t.erase=tt.erase)
    (bodySame : body.erase=otherBody.erase) (argSame : arg.erase=otherArg.erase)
    (origin : BetaVertexPreimage body arg site s t current old) :
    BetaVertexPreimage otherBody otherArg site ss tt
      (vertex targetSame current) (vertex sourceSame old) := by
  cases origin with
  | boundary => exact .boundary
  | proper origin => exact .proper (origin.reannotate bodySame argSame)

theorem chase (same : t.erase=u.erase) (walk : IncidenceChase t a es ds b) :
    IncidenceChase u (vertex same a) es ds (vertex same b) := by
  induction walk with
  | nil => exact .nil
  | forward src dst rest ih => exact .forward (source_reannotate same src) (target_reannotate same dst) ih
  | backward dst src rest ih => exact .backward (target_reannotate same dst) (source_reannotate same src) ih


theorem expansion (same : body.erase=otherBody.erase)
    (actual : CreatedReadingExpansion body site first last d es ds) :
    CreatedReadingExpansion otherBody site first last d es ds := by
  cases actual with
  | resultFunction other =>
    apply CreatedReadingExpansion.resultFunction
    intro stamp shape
    have erased : body.erase=.var 0 := same.trans (congrArg LTerm.erase shape)
    cases body with
    | var a i => exact other a (by rw [Term.var.inj erased])
    | app a f b => cases erased
    | lam a b => cases erased
  | resultOverlap shape =>
    subst body
    cases otherBody with
    | var a i => exact .resultOverlap (by rw [←Term.var.inj same])
    | app a f b => cases same
    | lam a b => cases same
  | copyFunction => exact .copyFunction
  | resultLambda => exact .resultLambda
  | copyLambda nonroot => exact .copyLambda nonroot
  | copyOverlap => exact .copyOverlap

def frame (middleSame : middle.erase=localMiddle.erase)
    (targetSame : target.erase=localTarget.erase)
    (bodySame : body.erase=localBody.erase) (argSame : argument.erase=localArgument.erase)
    (f : CreatedSpineIncidenceFrame body argument site middle target first last oldReader d snap firstSnap) :
    CreatedSpineIncidenceFrame localBody localArgument site localMiddle localTarget first last oldReader d
      (snapshot targetSame snap) (snapshot middleSame firstSnap) where
  oldNear:=vertex middleSame f.oldNear
  oldFar:=vertex middleSame f.oldFar
  edges:=f.edges
  directions:=f.directions
  oldNearTarget:=target_reannotate middleSame f.oldNearTarget
  nearOrigin:=by
    rw [vertex_near]
    exact vertex_origin middleSame targetSame bodySame argSame f.nearOrigin
  farOrigin:=by
    rw [vertex_far]
    exact vertex_origin middleSame targetSame bodySame argSame f.farOrigin
  fullChase:=chase middleSame f.fullChase
  expansion:=expansion bodySame f.expansion
  nearJunction:=by rw [vertex_near,←f.nearJunction]
  tailChase:=by rw [vertex_far];exact chase middleSame f.tailChase
  finalIncidence:=by
    cases d with
    | true => exact target_reannotate middleSame f.finalIncidence
    | false => exact source_reannotate middleSame f.finalIncidence

def TailSpecification (middle : LTerm) (site : Path) (alpha : Label) (d : Bool)
    (last : LTerm) (marker : Letter) (tail : List Letter) : Prop :=
  tail=marker::last.label.readLetters d ∨
  (d=true ∧marker=.over alpha ∧∃arg,middle.subterm (site++[.arg])=some arg ∧
    tail=marker::(last.label.readLetters d++(.under alpha)::arg.label.letters)) ∨
  (d=false ∧marker=.under alpha ∧∃app,middle.subterm site=some app ∧
    tail=marker::(last.label.readLetters d++(.over alpha)::app.label.letters.reverse))

theorem full_tail (formula : ExactDirectedReadingFormula middle site alpha d first last marker current) :
    ∃tail,TailSpecification middle site alpha d last marker tail ∧
      current.label.readLetters d=first.label.readLetters d++tail := by
  rcases formula with eq |⟨dir,mark,arg,lookup,eq⟩ |⟨dir,mark,app,lookup,eq⟩
  · exact ⟨_,Or.inl rfl,eq⟩
  · exact ⟨_,Or.inr (Or.inl ⟨dir,mark,arg,lookup,rfl⟩),eq⟩
  · exact ⟨_,Or.inr (Or.inr ⟨dir,mark,app,lookup,rfl⟩),eq⟩

end SpineReannotation

namespace PairedMarkerEventGeometry
variable {leaf : DirectedMarkerLeafOutput F source degree d ps word}

def reword (pair : PairedMarkerEventGeometry leaf localSource localTarget) (eq : word=other) :
    PairedMarkerEventGeometry (leaf.reword eq) localSource localTarget :=
  {pair with}

def extend (pair : PairedMarkerEventGeometry leaf localSource localTarget) (more : List Letter) :
    PairedMarkerEventGeometry (leaf.extend more) localSource localTarget :=
  {pair with}

def snoc (pair : PairedMarkerEventGeometry leaf localSource localTarget)
    (turn : StepAt p localTarget nextTarget) :
    PairedMarkerEventGeometry (leaf.snoc p) localSource nextTarget :=
  {pair with suffix:=pair.suffix.append (.cons turn (.nil _))}

end PairedMarkerEventGeometry

/-- Each entry is indexed by the literal global creation packet, with its own
local redex degree. Local labels and vertices are not identified globally. -/
structure PairedSpineCreationFrame
    (packet : SpineCreationPacket F source degree d) (localSource : LTerm) where
  middle : LTerm
  target : LTerm
  prefixLabels : History packet.pre localSource middle
  turn : StepAt packet.site middle target
  middleErase : packet.middle.erase=middle.erase
  targetErase : packet.target.erase=target.erase
  beta : Label
  alpha : Label
  body : LTerm
  argument : LTerm
  redex : middle.subterm packet.site=some (.app beta (.lam alpha body) argument)
  bodyErase : packet.event.body.erase=body.erase
  argumentErase : packet.event.argument.erase=argument.erase
  origin : BetaIncomingReadingOrigin body argument packet.site packet.edge packet.reader packet.oldReader packet.first packet.last
  current : LTerm
  lookup : target.subterm packet.edge=some current
  reading : PrerequisiteReadsDirected target packet.reader packet.edge d
  firstNode : LTerm
  lastNode : LTerm
  firstLookup : middle.subterm packet.first=some firstNode
  lastLookup : middle.subterm packet.last=some lastNode
  marker : Letter
  marks : marker.MarksDegree alpha
  formula : ExactDirectedReadingFormula middle packet.site alpha d firstNode lastNode marker current
  tail : List Letter
  tailSpec : SpineReannotation.TailSpecification middle packet.site alpha d lastNode marker tail
  tailEquation : current.label.readLetters d=firstNode.label.readLetters d++tail
  frame : CreatedSpineIncidenceFrame body argument packet.site middle target packet.first packet.last packet.oldReader d
    (SpineReannotation.snapshot targetErase packet.snapshot)
    (SpineReannotation.snapshot middleErase packet.firstSnapshot)
  edgesSame : frame.edges=packet.frame.edges
  directionsSame : frame.directions=packet.frame.directions

theorem paired_spine_creation_frame (packet : SpineCreationPacket F source degree d)
    (history : History (packet.pre++[packet.site]) localSource localTarget)
    (same : source.erase=localSource.erase) :
    ∃pair : PairedSpineCreationFrame packet localSource,pair.target=localTarget := by
  obtain ⟨middle,prefixLabels,rest⟩:=history.split
  cases rest with
  | cons turn done =>
    cases done
    have middleSame:=SpineReannotation.history_erase packet.event.labels prefixLabels same
    have targetSame:=SpineReannotation.history_erase (.cons packet.event.turn (.nil _)) (.cons turn (.nil _)) middleSame
    obtain ⟨beta,alpha,body,argument,redex,_⟩:=turn.head_lookups
    have heads:=congrArg (fun t=>subtermAt t packet.site) middleSame
    simp only [←LTerm.erase_subterm,packet.event.redex,redex,Option.map_some,LTerm.erase] at heads
    have parts:=Term.app.inj (Option.some.inj heads)
    have bodySame:=Term.lam.inj parts.1
    have origin:=packet.origin.reannotated bodySame parts.2
    have reading:=packet.reading.reannotated targetSame
    obtain ⟨current,lookup,_⟩:=SpineReannotation.paired_lookup targetSame packet.lookup
    obtain ⟨first,last,marker,firstLookup,lastLookup,marks,formula⟩:=
      origin.directed_label_decomposition turn redex reading lookup
    obtain ⟨tail,tailSpec,tailEquation⟩:=SpineReannotation.full_tail formula
    exact ⟨⟨middle,_,prefixLabels,turn,middleSame,targetSame,beta,alpha,body,argument,redex,
      bodySame,parts.2,origin,current,lookup,reading,first,last,firstLookup,lastLookup,
      marker,marks,formula,tail,tailSpec,tailEquation,
      SpineReannotation.frame middleSame targetSame bodySame parts.2 packet.frame,rfl,rfl⟩,rfl⟩


/-- The literal inherited constructor's full operational input, extracted only
from the GIVEN data. This is not an extra hypothesis of a history. -/
structure SpineInheritedPacket (F : List Path) (source : LTerm) (degree : Label) where
  pre : List Path
  middle : LTerm
  target : LTerm
  site : Path
  event : SelectedOldTurn F source degree pre middle target site
  edge : Path
  oldEdge : Path
  current : LTerm
  old : LTerm
  lookup : target.subterm edge=some current
  oldLookup : middle.subterm oldEdge=some old
  origin : BetaNodePreimage event.body event.argument site edge oldEdge
  uncreated : ¬BetaCreatedIncoming event.body site edge
  sameLabel : current.label=old.label
  snapshot : IncomingIncidenceSnapshot target edge
  oldSnapshot : IncomingIncidenceSnapshot middle oldEdge
  transport : IncomingIncidenceTransport (body:=event.body) (argument:=event.argument) (site:=site) snapshot oldSnapshot

namespace SpineIncidenceProvenance
variable {spine : DirectedMarkerSpine F source degree d ps target before edge}
variable {lookup : target.subterm edge=some current}
variable {leaf : DirectedMarkerLeafOutput F source degree d ps (current.label.readLetters d)}
variable {snap : IncomingIncidenceSnapshot target edge}

noncomputable def inheritedSteps
    (g : SpineIncidenceProvenance F source degree d spine lookup leaf snap) :
    List (SpineInheritedPacket F source degree) := by
  induction g with
  | inherited event lookup oldLookup origin uncreated eq earlier oldGeometry snapshot transport ih =>
    exact ih++[⟨_,_,_,_,event,_,_,_,_,lookup,oldLookup,origin,uncreated,eq,snapshot,_,transport⟩]
  | safe => exact []
  | marked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
end SpineIncidenceProvenance

structure PairedSpineInheritedEvent
    (p : SpineInheritedPacket F source degree) (localSource : LTerm) where
  middle : LTerm
  target : LTerm
  prefixLabels : History p.pre localSource middle
  turn : StepAt p.site middle target
  middleErase : p.middle.erase=middle.erase
  targetErase : p.target.erase=target.erase
  beta : Label
  alpha : Label
  body : LTerm
  argument : LTerm
  redex : middle.subterm p.site=some (.app beta (.lam alpha body) argument)
  bodyErase : p.event.body.erase=body.erase
  argumentErase : p.event.argument.erase=argument.erase
  current : LTerm
  old : LTerm
  lookup : target.subterm p.edge=some current
  oldLookup : middle.subterm p.oldEdge=some old
  origin : BetaNodePreimage body argument p.site p.edge p.oldEdge
  uncreated : ¬BetaCreatedIncoming body p.site p.edge
  sameLabel : current.label=old.label
  transport : IncomingIncidenceTransport (body:=body) (argument:=argument) (site:=p.site)
    (SpineReannotation.snapshot targetErase p.snapshot)
    (SpineReannotation.snapshot middleErase p.oldSnapshot)

theorem paired_spine_inherited_event (p : SpineInheritedPacket F source degree)
    (history : History (p.pre++[p.site]) localSource localTarget)
    (same : source.erase=localSource.erase) :
    ∃pair : PairedSpineInheritedEvent p localSource,pair.target=localTarget := by
  obtain ⟨middle,prefixLabels,remaining⟩:=history.split
  cases remaining with
  | cons turn done =>
    cases done
    have middleSame:=SpineReannotation.history_erase p.event.labels prefixLabels same
    have targetSame:=SpineReannotation.history_erase (.cons p.event.turn (.nil _)) (.cons turn (.nil _)) middleSame
    obtain ⟨beta,alpha,body,argument,redex,_⟩:=turn.head_lookups
    have heads:=congrArg (fun t=>subtermAt t p.site) middleSame
    simp only [←LTerm.erase_subterm,p.event.redex,redex,Option.map_some,LTerm.erase] at heads
    have parts:=Term.app.inj (Option.some.inj heads)
    have bodySame:=Term.lam.inj parts.1
    have origin:=p.origin.reannotate bodySame parts.2
    have uncreated:=fun h=>p.uncreated ((betaCreatedIncoming_of_same_erase bodySame).mpr h)
    obtain ⟨node,lookup,_⟩:=SpineReannotation.paired_lookup targetSame p.lookup
    obtain ⟨old,oldLookup,sameLabel⟩:=turn.beta_preimage_label redex origin lookup uncreated
    exact ⟨⟨middle,_,prefixLabels,turn,middleSame,targetSame,beta,alpha,body,argument,redex,
      bodySame,parts.2,node,old,lookup,oldLookup,origin,uncreated,sameLabel.symm,
      ⟨SpineReannotation.vertex_origin middleSame targetSame bodySame parts.2 p.transport.fromOrigin,
       SpineReannotation.vertex_origin middleSame targetSame bodySame parts.2 p.transport.toOrigin⟩⟩,rfl⟩

abbrev PairedSpineInheritedEntry (F : List Path) (source : LTerm) (degree : Label) (localSource : LTerm) :=
  Sigma (fun packet : SpineInheritedPacket F source degree =>PairedSpineInheritedEvent packet localSource)

abbrev PairedSpineFrameEntry (F : List Path) (source : LTerm) (degree : Label) (d : Bool)
    (localSource : LTerm) :=
  Sigma (fun packet : SpineCreationPacket F source degree d =>PairedSpineCreationFrame packet localSource)

/-- Only a derived output: the input geometry and ONE supplied local history
are indices. Every frame retains its own local degree and actual incidences. -/
structure PairedSpineReannotation
    {spine : DirectedMarkerSpine F source degree d ps target before edge}
    {globalCurrent : LTerm}
    {lookup : target.subterm edge=some globalCurrent}
    {leaf : DirectedMarkerLeafOutput F source degree d ps (globalCurrent.label.readLetters d)}
    {snapshot : IncomingIncidenceSnapshot target edge}
    (geometry : SpineIncidenceProvenance F source degree d spine lookup leaf snapshot)
    (localHistory : History ps localSource localTarget) (same : source.erase=localSource.erase) where
  current : LTerm
  currentLookup : localTarget.subterm edge=some current
  currentErase : current.erase=globalCurrent.erase
  base : PairedMarkerEventGeometry leaf localSource localTarget
  frames : List (PairedSpineFrameEntry F source degree d localSource)
  framesNonempty : frames≠[]
  frameAlignment : frames.map Sigma.fst=geometry.creationFrames
  frameSuffix : ∀p∈frames,∃after,ps=p.1.pre++p.1.site::after ∧History after p.2.target localTarget
  inherited : List (PairedSpineInheritedEntry F source degree localSource)
  inheritedAlignment : inherited.map Sigma.fst=geometry.inheritedSteps
  inheritedSuffix : ∀p∈inherited,∃after,ps=p.1.pre++p.1.site::after ∧History after p.2.target localTarget
  localTailPieces : List (List Letter)
  tailAlignment : localTailPieces=frames.tail.map (fun p=>p.2.tail)
  wordFold : current.label.readLetters d=base.current.label.readLetters d++localTailPieces.flatten

namespace SpineReannotation
private theorem tails_append {xs : List α} (nonempty : xs≠[]) (y : α) :
    (xs++[y]).tail=xs.tail++[y] := by cases xs <;>simp_all
end SpineReannotation

namespace SpineIncidenceProvenance
variable {F : List Path} {source target localSource localTarget current : LTerm} {degree : Label} {d : Bool}
variable {ps : List Path} {before : List (Option Label)} {edge : Path}
variable {spine : DirectedMarkerSpine F source degree d ps target before edge}
variable {lookup : target.subterm edge=some current}
variable {leaf : DirectedMarkerLeafOutput F source degree d ps (current.label.readLetters d)}
variable {snapshot : IncomingIncidenceSnapshot target edge}

def leafIndex (_geometry : SpineIncidenceProvenance F source degree d spine lookup leaf snapshot) :=leaf

private def origin_site (_event : SelectedOldTurn F source degree pre middle target site) : Path:=site

theorem paired_reannotation
    (geometry : SpineIncidenceProvenance F source degree d spine lookup leaf snapshot)
    (localHistory : History ps localSource localTarget) (same : source.erase=localSource.erase) :
    Nonempty (PairedSpineReannotation geometry localHistory same) := by
  induction geometry generalizing localSource localTarget with
  | inherited event lookup oldLookup origin uncreated labelSame earlier earlierGeometry snap transport ih =>
    obtain ⟨middle,prefixLabels,remaining⟩:=localHistory.split
    cases remaining with
    | cons turn done =>
      cases done
      have middleSame:=SpineReannotation.history_erase event.labels prefixLabels same
      have targetSame:=SpineReannotation.history_erase (.cons event.turn (.nil _)) (.cons turn (.nil _)) middleSame
      obtain ⟨beta,alpha,body,argument,redex,_⟩:=turn.head_lookups
      have heads:=congrArg (fun t=>subtermAt t (origin_site event)) middleSame
      simp only [origin_site,←LTerm.erase_subterm,event.redex,redex,Option.map_some,LTerm.erase] at heads
      have parts:=Term.app.inj (Option.some.inj heads)
      have bodySame:=Term.lam.inj parts.1
      have localOrigin:=origin.reannotate bodySame parts.2
      obtain ⟨paired⟩:=ih prefixLabels same
      obtain ⟨node,atNode,nodeErase⟩:=SpineReannotation.paired_lookup targetSame lookup
      have nodeUncreated := fun created =>uncreated ((betaCreatedIncoming_of_same_erase bodySame).mpr created)
      obtain ⟨old,atOld,nodeLabel⟩:=turn.beta_preimage_label redex localOrigin atNode nodeUncreated
      have oldEq : old=paired.current:=Option.some.inj (atOld.symm.trans paired.currentLookup)
      let inheritedPacket : SpineInheritedPacket F source degree:=
        ⟨_,_,_,_,event,_,_,_,_,lookup,oldLookup,origin,uncreated,labelSame,snap,_,transport⟩
      obtain ⟨inheritedPair,atInheritedTarget⟩:=paired_spine_inherited_event inheritedPacket localHistory same
      let inheritedEntry : PairedSpineInheritedEntry F source degree localSource:=⟨inheritedPacket,inheritedPair⟩
      refine ⟨{
        current:=node,currentLookup:=atNode,currentErase:=?_,
        base:=((paired.base.reword (congrArg (Label.readLetters _) labelSame.symm)).snoc turn),
        frames:=paired.frames,framesNonempty:=paired.framesNonempty,
        frameAlignment:=paired.frameAlignment,frameSuffix:=?_,
        inherited:=paired.inherited++[inheritedEntry],inheritedAlignment:=?_,inheritedSuffix:=?_,
        localTailPieces:=paired.localTailPieces,tailAlignment:=paired.tailAlignment,wordFold:=?_}⟩
      · simpa only [lookup,Option.getD_some] using nodeErase
      · intro p member
        obtain ⟨after,schedule,suffix⟩:=paired.frameSuffix p member
        refine ⟨after++[_],?_,suffix.append (.cons turn (.nil _))⟩
        rw [schedule];simp only [List.append_assoc,List.cons_append]
      · rw [List.map_append,paired.inheritedAlignment];rfl
      · intro p member
        rcases List.mem_append.mp member with oldMember |lastMember
        · obtain ⟨after,schedule,suffix⟩:=paired.inheritedSuffix p oldMember
          refine ⟨after++[_],?_,suffix.append (.cons turn (.nil _))⟩
          rw [schedule];simp only [List.append_assoc,List.cons_append]
        · have eq:=List.mem_singleton.mp lastMember;subst p
          exact ⟨[],rfl,atInheritedTarget ▸ History.nil localTarget⟩
      · rw [←nodeLabel,oldEq];exact paired.wordFold
  | safe event reading lookup origin segment beforeEq beforeSafe firstLookup firstSafe lastLookup lastSourceLookup lastTrace marks formula snap firstSnap fr =>
    let packet : SpineCreationPacket F source degree d :=
      ⟨_,_,_,_,event,_,_,_,_,_,_,lookup,reading,origin,snap,firstSnap,fr⟩
    obtain ⟨pairedFrame,atTarget⟩:=paired_spine_creation_frame packet localHistory same
    let g := SpineIncidenceProvenance.safe event reading lookup origin segment beforeEq beforeSafe firstLookup firstSafe lastLookup lastSourceLookup lastTrace marks formula snap firstSnap fr
    let actualLeaf := leafIndex g
    obtain ⟨base⟩:=paired_marker_leaf_geometry actualLeaf localHistory same
    have sameTarget : base.target=localTarget := by
      have h : History [] base.target localTarget:=base.suffix
      exact (h.deterministic (.nil _)).symm
    have atCurrent : localTarget.subterm _=some base.current:=sameTarget ▸ base.lookup
    have erased:=SpineReannotation.history_erase (event.labels.append (.cons event.turn (.nil _))) localHistory same
    have nodeErase:=SpineReannotation.paired_lookup erased lookup
    refine ⟨{
      current:=base.current
      currentLookup:=atCurrent
      currentErase:=?_
      base:=base
      frames:=[⟨packet,pairedFrame⟩]
      framesNonempty:=by simp
      frameAlignment:=rfl
      frameSuffix:=?_
      inherited:=[]
      inheritedAlignment:=rfl
      inheritedSuffix:=by intro p h;cases h
      localTailPieces:=[]
      tailAlignment:=rfl
      wordFold:=by simp}⟩
    · obtain ⟨node,atNode,nodeSame⟩:=nodeErase
      have eq:=Option.some.inj (atNode.symm.trans atCurrent)
      simpa only [lookup,Option.getD_some,eq] using nodeSame
    · intro p member
      have eq:=List.mem_singleton.mp member;subst p
      exact ⟨[],rfl,atTarget ▸ History.nil localTarget⟩
  | marked event reading lookup origin segment beforeEq beforeSafe firstLookup firstMarked lastLookup lastSourceLookup lastTrace earlier earlierGeometry marks formula equation snap fr ih =>
    obtain ⟨middle,prefixLabels,remaining⟩:=localHistory.split
    cases remaining with
    | cons turn done =>
      cases done
      obtain ⟨paired⟩:=ih prefixLabels same
      let packet : SpineCreationPacket F source degree d :=
        ⟨_,_,_,_,event,_,_,_,_,_,_,lookup,reading,origin,snap,_,fr⟩
      obtain ⟨pairedFrame,atTarget⟩:=paired_spine_creation_frame packet localHistory same
      have middleEq : pairedFrame.middle=middle:=pairedFrame.prefixLabels.deterministic prefixLabels
      have firstEq : paired.current=pairedFrame.firstNode := by
        apply Option.some.inj
        exact paired.currentLookup.symm.trans (middleEq ▸ pairedFrame.firstLookup)
      let entry : PairedSpineFrameEntry F source degree d localSource:=⟨packet,pairedFrame⟩
      refine ⟨{
        current:=pairedFrame.current,currentLookup:=?_,currentErase:=?_,
        base:=(((paired.base.extend _).reword equation.symm).snoc turn),
        frames:=paired.frames++[entry],framesNonempty:=(by simp),
        frameAlignment:=?_,frameSuffix:=?_,
        inherited:=paired.inherited,inheritedAlignment:=paired.inheritedAlignment,inheritedSuffix:=?_,
        localTailPieces:=paired.localTailPieces++[pairedFrame.tail],
        tailAlignment:=?_,wordFold:=?_}⟩
      · exact atTarget ▸ pairedFrame.lookup
      · obtain ⟨node,atNode,nodeSame⟩:=SpineReannotation.paired_lookup pairedFrame.targetErase lookup
        have eq:=Option.some.inj (atNode.symm.trans pairedFrame.lookup)
        simpa only [lookup,Option.getD_some,eq] using nodeSame
      · change (paired.frames++[entry]).map Sigma.fst=_
        rw [List.map_append,paired.frameAlignment]
        rfl
      · intro p member
        rcases List.mem_append.mp member with earlier |last
        · obtain ⟨after,schedule,suffix⟩:=paired.frameSuffix p earlier
          refine ⟨after++[_],?_,suffix.append (.cons turn (.nil _))⟩
          rw [schedule];simp only [List.append_assoc,List.cons_append]
        · have eq:=List.mem_singleton.mp last;subst p
          exact ⟨[],rfl,atTarget ▸ History.nil localTarget⟩
      · intro p member
        obtain ⟨after,schedule,suffix⟩:=paired.inheritedSuffix p member
        refine ⟨after++[_],?_,suffix.append (.cons turn (.nil _))⟩
        rw [schedule];simp only [List.append_assoc,List.cons_append]
      · rw [SpineReannotation.tails_append paired.framesNonempty,List.map_append,←paired.tailAlignment]
        rfl
      · change pairedFrame.current.label.readLetters d=paired.base.current.label.readLetters d++_
        rw [pairedFrame.tailEquation,←firstEq,paired.wordFold]
        simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]

theorem continuation_count
    (g : SpineIncidenceProvenance F source degree d spine lookup leaf snapshot) :
    g.continuationPieces.length+1=g.creationFrames.length := by
  induction g with
  | inherited _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | safe => rfl
  | marked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simpa only [continuationPieces,creationFrames,List.length_append,List.length_singleton] using congrArg (·+1) ih

theorem schedule_count
    (g : SpineIncidenceProvenance F source degree d spine lookup leaf snapshot) :
    g.afterSites.length+1=g.creationFrames.length+g.inheritedSteps.length := by
  induction g with
  | inherited _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [afterSites,creationFrames,inheritedSteps,List.length_append,List.length_singleton] at ih ⊢
    omega
  | safe => rfl
  | marked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [afterSites,creationFrames,inheritedSteps,List.length_append,List.length_singleton] at ih ⊢
    omega

theorem multiple_of_continuation
    (g : SpineIncidenceProvenance F source degree d spine lookup leaf snapshot)
    (nonempty : leaf.continuation≠[]) : 2≤g.creationFrames.length := by
  have pieces : g.continuationPieces≠[] := by
    intro empty
    apply nonempty
    rw [←g.continuationPieces_eq,empty,List.flatten_nil]
  have positive:=List.length_pos_iff.mpr pieces
  have count:=g.continuation_count
  omega

theorem after_nonempty_of_multiple
    (g : SpineIncidenceProvenance F source degree d spine lookup leaf snapshot)
    (multiple : 2≤g.creationFrames.length) : leaf.after≠[] := by
  intro empty
  have count:=g.schedule_count
  rw [g.afterSites_eq,empty,List.length_nil] at count
  omega

end SpineIncidenceProvenance

namespace PairedSpineReannotation
variable {current : LTerm}
variable {spine : DirectedMarkerSpine F source degree d ps target before edge}
variable {lookup : target.subterm edge=some current}
variable {leaf : DirectedMarkerLeafOutput F source degree d ps (current.label.readLetters d)}
variable {snapshot : IncomingIncidenceSnapshot target edge}
variable {g : SpineIncidenceProvenance F source degree d spine lookup leaf snapshot}
variable {history : History ps localSource localTarget} {same : source.erase=localSource.erase}

theorem tail_count (pair : PairedSpineReannotation g history same) :
    pair.localTailPieces.length+1=g.creationFrames.length := by
  have len:=congrArg List.length pair.frameAlignment
  rw [List.length_map] at len
  rw [pair.tailAlignment,List.length_map]
  cases h : pair.frames with
  | nil => exact False.elim (pair.framesNonempty h)
  | cons a tail => simpa only [h,List.tail_cons,List.length_cons] using len

def currentSnapshot (_pair : PairedSpineReannotation g history same) : IncomingIncidenceSnapshot localTarget edge :=
  SpineReannotation.snapshot (SpineReannotation.history_erase spine.actual_history history same) snapshot

theorem tails_nonempty (pair : PairedSpineReannotation g history same)
    (multiple : 2≤g.creationFrames.length) : pair.localTailPieces≠[] := by
  intro empty
  have count:=pair.tail_count
  rw [empty,List.length_nil] at count
  omega

end PairedSpineReannotation
end Lamping.Lambda.Labelled

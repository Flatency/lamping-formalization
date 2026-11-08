import Lamping.Lambda.UniformOldOuterImageAlignment
import Lamping.Lamping.LocalSourceFragmentEvaluation
import Lamping.Lamping.RedexChainDegrees
import Lamping.Lambda.LabelArgumentBinderScope

namespace Lamping.Lambda.Labelled

namespace InteriorSourceBlock

def bar (over : Bool) (degree : Label) : Letter :=
  if over then .over degree else .under degree

/-- Finite literal outer-letter transitions of an actual restricted route.
The marker retains its actual selected middle route; no completion is added. -/
inductive LetterStep (edges : List SourceEdge) (allowed : Label → Prop) :
    SourcePort → Letter → SourcePort → Prop where
  | atom (member : edge∈edges) (atomic : edge.atom=Label.atom n) :
      LetterStep edges allowed edge.fromPort (.atom n) edge.toPort
  | over (selected : allowed degree)
      (middle : SelectedSourceRoute edges allowed (.appFn app) degree (.lamContext lam)) :
      LetterStep edges allowed (.appContext app) (.over degree) (.lamBody lam)
  | under (selected : allowed degree)
      (middle : SelectedSourceRoute edges allowed (.appFn app) degree (.lamContext lam)) :
      LetterStep edges allowed (.lamBind lam) (.under degree) (.appArg app)

inductive LetterWalk (edges : List SourceEdge) (allowed : Label → Prop) :
    SourcePort → List Letter → SourcePort → Prop where
  | nil (port) : LetterWalk edges allowed port [] port
  | cons (head : LetterStep edges allowed start letter middle)
      (tail : LetterWalk edges allowed middle letters finish) :
      LetterWalk edges allowed start (letter::letters) finish

theorem LetterWalk.append (first : LetterWalk edges allowed start xs middle)
    (second : LetterWalk edges allowed middle ys finish) :
    LetterWalk edges allowed start (xs++ys) finish := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head (ih second)

theorem LetterWalk.split (walk : LetterWalk edges allowed start (xs++ys) finish) :
    ∃middle,LetterWalk edges allowed start xs middle ∧LetterWalk edges allowed middle ys finish := by
  induction xs generalizing start with
  | nil => exact ⟨start,.nil _,walk⟩
  | cons letter rest ih =>
    cases walk with
    | cons head tail =>
      obtain ⟨middle,before,after⟩:=ih tail
      exact ⟨middle,.cons head before,after⟩

theorem route_walk (route : SelectedSourceRoute edges allowed start label finish) :
    LetterWalk edges allowed start label.letters finish := by
  induction route with
  | atom member atomic => exact .cons (.atom member atomic) (.nil _)
  | over _ selected middle _ leftIH _middleIH rightIH =>
    simpa only [Label.letters_concat,Label.over,Label.letters,List.singleton_append,List.append_assoc]
      using leftIH.append (.cons (.over selected middle) rightIH)
  | under _ selected middle _ leftIH _middleIH rightIH =>
    simpa only [Label.letters_concat,Label.under,Label.letters,List.singleton_append,List.append_assoc]
      using leftIH.append (.cons (.under selected middle) rightIH)

/-- Output locating a selected original redex, including its actual coordinates. -/
structure SelectedRedex (source : LTerm) (F : List Path) where
  position : Path
  member : position∈F
  beta : Label
  degree : Label
  body : LTerm
  argument : LTerm
  lookup : source.subterm position=some (.app beta (.lam degree body) argument)

def SelectedRedex.afterPort (redex : SelectedRedex source F) (over : Bool) : SourcePort :=
  if over then .lamBody redex.degree else .appArg redex.beta

def SelectedRedex.beforePort (redex : SelectedRedex source F) (over : Bool) : SourcePort :=
  if over then .appContext redex.beta else .lamBind redex.degree

theorem selected_redex_ports (initial : INIT source)
    (selected : SelectedDegree source F degree)
    (route : SelectedSourceRoute (sourceEdges [] .external source) (SelectedDegree source F)
      (.appFn app) degree (.lamContext lam)) :
    ∃redex : SelectedRedex source F,redex.beta=app ∧redex.degree=degree ∧redex.degree=lam := by
  obtain ⟨name,member,atDegree⟩:=selected
  obtain ⟨beta,body,argument,lookup⟩:=LTerm.degreeAt_redex atDegree
  obtain ⟨env,ctx,occurrence⟩:=SourceSubterm.of_lookup source lookup [] .external
  have canonicalMember : (⟨degree,.appFn beta,.lamContext degree⟩ : SourceEdge)∈sourceEdges [] .external source :=
    occurrence.edges_subset _ (by simp [sourceEdges])
  obtain ⟨n,atomic⟩:=(SelectedDegree.atomic initial ⟨name,member,atDegree⟩)
  have atomicRoute : SourceRoute (sourceEdges [] .external source) (.appFn app) (Label.atom n) (.lamContext lam) := by
    rw [←atomic];exact route.forget
  obtain ⟨edge,edgeMember,edgeAtomic,fromEq,toEq⟩:=atomicRoute.initial_atom_edge initial
  have same:=sourceEdges_unique initial edgeMember canonicalMember (edgeAtomic.trans atomic.symm)
  have betaEq : beta=app := SourcePort.appFn.inj (by simpa only [same] using fromEq)
  have degreeEq : degree=lam := SourcePort.lamContext.inj (by simpa only [same] using toEq)
  exact ⟨⟨name,member,beta,degree,body,argument,lookup⟩,betaEq,rfl,degreeEq⟩

structure WindowGeometry (source : LTerm) (F : List Path) (n : Nat) (leftKind rightKind : Bool) where
  edge : SourceEdge
  member : edge∈sourceEdges [] .external source
  atomic : edge.atom=Label.atom n
  left : SelectedRedex source F
  right : SelectedRedex source F
  departure : edge.fromPort=left.afterPort leftKind
  arrival : edge.toPort=right.beforePort rightKind

theorem marker_step_redex (initial : INIT source)
    (step : LetterStep (sourceEdges [] .external source) (SelectedDegree source F)
      start (bar kind degree) finish) :
    ∃redex : SelectedRedex source F,redex.degree=degree ∧
      start=redex.beforePort kind ∧finish=redex.afterPort kind := by
  cases kind with
  | false =>
    cases step with
    | under selected middle =>
      obtain ⟨redex,appEq,degreeEq,lamEq⟩:=selected_redex_ports initial selected middle
      exact ⟨redex,degreeEq,by simp [SelectedRedex.beforePort,lamEq],by simp [SelectedRedex.afterPort,appEq]⟩
  | true =>
    cases step with
    | over selected middle =>
      obtain ⟨redex,appEq,degreeEq,lamEq⟩:=selected_redex_ports initial selected middle
      exact ⟨redex,degreeEq,by simp [SelectedRedex.beforePort,appEq],by simp [SelectedRedex.afterPort,lamEq]⟩

theorem route_window_geometry (initial : INIT source)
    (route : SelectedSourceRoute (sourceEdges [] .external source) (SelectedDegree source F) start label finish)
    (window : label.letters=pre++[bar leftKind dl,.atom n,bar rightKind dr]++post) :
    Nonempty (WindowGeometry source F n leftKind rightKind) := by
  have walk:=route_walk route
  rw [window] at walk
  have walk' : LetterWalk (sourceEdges [] .external source) (SelectedDegree source F)
      start (pre++(bar leftKind dl::.atom n::bar rightKind dr::post)) finish := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using walk
  obtain ⟨before,_prefix,tail⟩:=walk'.split
  cases tail with
  | cons leftStep rest =>
    cases rest with
    | cons atomStep rest =>
      cases rest with
      | cons rightStep _suffix =>
        obtain ⟨left,_degreeLeft,_leftStart,leftFinish⟩:=marker_step_redex initial leftStep
        obtain ⟨right,_degreeRight,rightStart,_rightFinish⟩:=marker_step_redex initial rightStep
        cases atomStep with
        | atom member atomic => exact ⟨⟨_,member,atomic,left,right,leftFinish,rightStart⟩⟩

theorem edge_occurrence {edge : SourceEdge} (member : edge∈sourceEdges env ctx source) :
    ∃position innerEnv innerCtx node,SourceSubterm env ctx source position innerEnv innerCtx node ∧
      sourceEdge innerEnv innerCtx node=edge := by
  induction source generalizing env ctx with
  | var label index =>
    have same : edge=sourceEdge env ctx (.var label index) := by simpa only [sourceEdges,List.mem_singleton] using member
    exact ⟨[],env,ctx,_,.nil,same.symm⟩
  | lam label body ih =>
    rcases List.mem_cons.mp member with same | inside
    · exact ⟨[],env,ctx,_,.nil,same.symm⟩
    · obtain ⟨p,ie,ic,node,occ,same⟩:=ih inside
      exact ⟨.body::p,ie,ic,node,.body occ,same⟩
  | app label fn arg fnIH argIH =>
    rcases List.mem_cons.mp member with same | inside
    · exact ⟨[],env,ctx,_,.nil,same.symm⟩
    · rcases List.mem_append.mp inside with left | right
      · obtain ⟨p,ie,ic,node,occ,same⟩:=fnIH left
        exact ⟨.fn::p,ie,ic,node,.fn occ,same⟩
      · obtain ⟨p,ie,ic,node,occ,same⟩:=argIH right
        exact ⟨.arg::p,ie,ic,node,.arg occ,same⟩

theorem source_edge_label (env ctx) (node : LTerm) : (sourceEdge env ctx node).atom=node.label := by
  cases node <;> rfl

theorem source_edge_departure (env ctx) (node : LTerm) : (sourceEdge env ctx node).fromPort=ctx := by
  cases node <;> rfl

theorem SelectedRedex.function_lookup (redex : SelectedRedex source F) :
    source.subterm (redex.position++[.fn])=some (.lam redex.degree redex.body) := by
  rw [LTerm.subterm_append,redex.lookup];rfl

def departurePosition (redex : SelectedRedex source F) (kind : Bool) : Path :=
  if kind then (redex.position++[.fn])++[.body] else redex.position++[.arg]

theorem occurrence_after_marker (initial : INIT source)
    (occurrence : SourceSubterm [] .external source position env ctx node)
    (redex : SelectedRedex source F) (afterEq : ctx=redex.afterPort kind) :
    position=departurePosition redex kind := by
  rcases occurrence.last_departure with ⟨_root,context⟩ |⟨parent,step,term,split,lookup,role⟩
  · rw [context] at afterEq
    cases kind <;> simp [SelectedRedex.afterPort] at afterEq
  · cases role with
    | fn => cases kind <;> simp [SelectedRedex.afterPort] at afterEq
    | arg =>
      cases kind with
      | true => simp [SelectedRedex.afterPort] at afterEq
      | false =>
        have labelEq:=SourcePort.appArg.inj afterEq
        have parentEq:=LTerm.subterm_label_injective source initial.2 lookup redex.lookup labelEq
        simpa only [departurePosition,Bool.false_eq_true,ite_false,parentEq] using split
    | body =>
      cases kind with
      | false => simp [SelectedRedex.afterPort] at afterEq
      | true =>
        have labelEq:=SourcePort.lamBody.inj afterEq
        have parentEq:=LTerm.subterm_label_injective source initial.2 lookup redex.function_lookup labelEq
        simpa only [departurePosition,ite_true,parentEq] using split

def ArrivalAttachment (redex : SelectedRedex source F) (kind : Bool) (position : Path) (node : LTerm) : Prop :=
  if kind then position=redex.position else
    ∃stamp index rest,node=.var stamp index ∧position=(redex.position++[.fn])++(.body::rest) ∧index=binderDepth rest

theorem occurrence_before_marker (initial : INIT source)
    (occurrence : SourceSubterm [] .external source position env ctx node)
    (redex : SelectedRedex source F)
    (beforeEq : (sourceEdge env ctx node).toPort=redex.beforePort kind) :
    ArrivalAttachment redex kind position node := by
  cases kind with
  | true =>
    change (sourceEdge env ctx node).toPort=.appContext redex.beta at beforeEq
    change position=redex.position
    cases node with
    | var stamp index =>
      change sourceBinder env index=.appContext redex.beta at beforeEq
      unfold sourceBinder at beforeEq
      cases entry : env[index]? <;> rw [entry] at beforeEq <;> cases beforeEq
    | lam => cases beforeEq
    | app stamp fn arg =>
      have labelEq:=SourcePort.appContext.inj beforeEq
      exact LTerm.subterm_label_injective source initial.2 occurrence.lookup redex.lookup labelEq
  | false =>
    change (sourceEdge env ctx node).toPort=.lamBind redex.degree at beforeEq
    change ∃stamp index rest,node=.var stamp index ∧position=(redex.position++[.fn])++(.body::rest) ∧index=binderDepth rest
    cases node with
    | app => cases beforeEq
    | lam => cases beforeEq
    | var stamp index =>
      obtain ⟨parent,rest,body,split,lookup,depth⟩:=occurrence.sourceBinder_occurrence beforeEq
      have parentEq:=LTerm.subterm_label_injective source initial.2 lookup redex.function_lookup rfl
      exact ⟨stamp,index,rest,rfl,by simpa only [parentEq] using split,depth⟩

structure WindowOccurrences (source : LTerm) (F : List Path) (n : Nat) (leftKind rightKind : Bool) where
  position : Path
  env : List Label
  ctx : SourcePort
  node : LTerm
  occurrence : SourceSubterm [] .external source position env ctx node
  atomic : node.label=Label.atom n
  left : SelectedRedex source F
  right : SelectedRedex source F
  departure : position=departurePosition left leftKind
  arrival : ArrivalAttachment right rightKind position node

theorem WindowGeometry.occurrences (geometry : WindowGeometry source F n leftKind rightKind)
    (initial : INIT source) : Nonempty (WindowOccurrences source F n leftKind rightKind) := by
  obtain ⟨position,env,ctx,node,occurrence,edgeEq⟩:=edge_occurrence geometry.member
  have fromEq : ctx=geometry.left.afterPort leftKind :=
    (source_edge_departure env ctx node).symm.trans ((congrArg SourceEdge.fromPort edgeEq).trans geometry.departure)
  have toEq : (sourceEdge env ctx node).toPort=geometry.right.beforePort rightKind :=
    (congrArg SourceEdge.toPort edgeEq).trans geometry.arrival
  have atomic : node.label=Label.atom n :=
    (source_edge_label env ctx node).symm.trans ((congrArg SourceEdge.atom edgeEq).trans geometry.atomic)
  exact ⟨⟨position,env,ctx,node,occurrence,atomic,geometry.left,geometry.right,
    occurrence_after_marker initial occurrence geometry.left fromEq,
    occurrence_before_marker initial occurrence geometry.right toEq⟩⟩

theorem lookup_relabel {source node : LTerm} {position : Path}
    (lookup : source.subterm position=some node) (s : Nat → Label) :
    (source.relabel s).subterm position=some (node.relabel s) := by
  rw [LTerm.subterm_relabel,lookup];rfl

def SelectedRedex.relabel (redex : SelectedRedex source F) (s : Nat → Label) :
    SelectedRedex (source.relabel s) F :=
  ⟨redex.position,redex.member,redex.beta.relabel s,redex.degree.relabel s,
    redex.body.relabel s,redex.argument.relabel s,lookup_relabel redex.lookup s⟩

structure WindowShape (source : LTerm) (F : List Path) (position : Path) (node : LTerm)
    (leftKind rightKind : Bool) where
  lookup : source.subterm position=some node
  left : SelectedRedex source F
  right : SelectedRedex source F
  departure : position=departurePosition left leftKind
  arrival : ArrivalAttachment right rightKind position node

theorem WindowOccurrences.relabelled_shape (out : WindowOccurrences source F n leftKind rightKind)
    (s : Nat → Label) :
    Nonempty (WindowShape (source.relabel s) F out.position (out.node.relabel s) leftKind rightKind) := by
  refine ⟨⟨lookup_relabel out.occurrence.lookup s,out.left.relabel s,out.right.relabel s,?_,?_⟩⟩
  · simpa only [departurePosition,SelectedRedex.relabel] using out.departure
  · cases rightKind with
    | true => exact out.arrival
    | false =>
      obtain ⟨stamp,index,rest,nodeEq,split,depth⟩:=out.arrival
      exact ⟨stamp.relabel s,index,rest,by rw [nodeEq];rfl,split,depth⟩

def SelectedRedex.vertex (redex : SelectedRedex source F) : Bool → SyntaxIncidence.ProperPosition source
  | true => ⟨redex.position++[.fn],Or.inr ⟨redex.degree,redex.body,redex.function_lookup⟩⟩
  | false => ⟨redex.position,Or.inl ⟨redex.beta,.lam redex.degree redex.body,redex.argument,redex.lookup⟩⟩

theorem WindowShape.auxiliary (out : WindowShape source F position node leftKind rightKind) :
    AuxiliaryAt source position := by
  constructor
  · rintro ⟨parent,_stamp,_fn,_arg,split,_lookup⟩
    have last:=congrArg List.getLast? (out.departure.symm.trans split)
    cases leftKind <;> simp [departurePosition] at last
  · rintro ⟨stamp,body,atLambda⟩
    cases rightKind with
    | true =>
      have split : position=out.right.position:=out.arrival
      rw [split,out.right.lookup] at atLambda
      cases atLambda
    | false =>
      obtain ⟨label,index,_rest,nodeEq,_split,_depth⟩:=out.arrival
      have same:=out.lookup.symm.trans atLambda
      rw [nodeEq] at same
      cases same

theorem WindowShape.source_spec (out : WindowShape source F position node leftKind rightKind) :
    SyntaxIncidence.Source source position (some (out.left.vertex leftKind)) := by
  cases leftKind with
  | false =>
    exact ⟨.arg,_,.appArg out.left.beta,out.departure,out.left.lookup,.arg⟩
  | true =>
    exact ⟨.body,_,.lamBody out.left.degree,out.departure,out.left.function_lookup,.body⟩

theorem WindowShape.target_spec (out : WindowShape source F position node leftKind rightKind) :
    SyntaxIncidence.Target source position (some (out.right.vertex (!rightKind))) := by
  cases rightKind with
  | true => exact Or.inl out.arrival
  | false =>
    obtain ⟨label,index,rest,nodeEq,split,depth⟩:=out.arrival
    exact Or.inr ⟨label,index,out.right.degree,out.right.body,rest,
      nodeEq ▸ out.lookup,out.right.function_lookup,split,depth⟩

theorem SelectedRedex.chain (redex : SelectedRedex source F) (kind : Bool) :
    PrerequisiteChain source (redex.vertex kind).val [redex.position++[.fn]] := by
  cases kind with
  | false => exact .redex_app redex.lookup
  | true => exact .redex_lam redex.lookup

open Lamping.AG

theorem SelectedRedex.endpoint_iso (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some alpha)
    (left right : SelectedRedex source F) (kind : Bool) :
    SuccessfulEndpointIso source closed (some (left.vertex kind)) (some (right.vertex kind)) := by
  refine ⟨[left.position++[Step.fn]],[right.position++[Step.fn]],left.chain kind,right.chain kind,?_⟩
  exact (redex_chain_iso_iff_degree closed left.lookup right.lookup).mpr
    ((selected left.position left.member).trans (selected right.position right.member).symm)

theorem WindowShape.endpoint_isos (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some alpha)
    (left : WindowShape source F leftPosition leftNode leftKind rightKind)
    (right : WindowShape source F rightPosition rightNode leftKind rightKind) :
    SuccessfulEndpointIso source closed (some (left.left.vertex leftKind)) (some (right.left.vertex leftKind)) ∧
      SuccessfulEndpointIso source closed (some (left.right.vertex (!rightKind))) (some (right.right.vertex (!rightKind))) :=
  ⟨SelectedRedex.endpoint_iso closed selected left.left right.left leftKind,
    SelectedRedex.endpoint_iso closed selected left.right right.right (!rightKind)⟩

theorem selected_node_route (routes : SelectedTermRoutes edges allowed env ctx target)
    (lookup : target.subterm position=some node) :
    ∃innerCtx finish,SelectedSourceRoute edges allowed innerCtx node.label finish := by
  induction routes generalizing position with
  | var route =>
    cases position with
    | nil => cases lookup;exact ⟨_,_,route⟩
    | cons step rest => cases step <;> simp [LTerm.subterm] at lookup
  | lam route child ih =>
    cases position with
    | nil => cases lookup;exact ⟨_,_,route⟩
    | cons step rest =>
      cases step with
      | fn | arg => simp [LTerm.subterm] at lookup
      | body => exact ih lookup
  | app route fn arg fnIH argIH =>
    cases position with
    | nil => cases lookup;exact ⟨_,_,route⟩
    | cons step rest =>
      cases step with
      | body => simp [LTerm.subterm] at lookup
      | fn => exact fnIH lookup
      | arg => exact argIH lookup

theorem actual_old_node_route {source localTarget node : LTerm} {position : Path}
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (lookup : localTarget.subterm position=some node) :
    ∃ctx finish,SelectedSourceRoute (sourceEdges [] .external (initLabels source.erase))
      (SelectedDegree (initLabels source.erase) F) ctx node.label finish := by
  have localOld : Marked.RelativeOldHistory F ps
      (Marked.mark F (initLabels source.erase).erase) marked := by
    simpa only [erase_initLabels] using old
  have relative := (Marked.relativeOld_iff_relative (Marked.selected_mark F _)).mp localOld
  exact selected_node_route (relative_development_selected_routes (init_is_INIT _) relative localHistory) lookup

theorem label_relabel (node : LTerm) (s : Nat → Label) :
    (node.relabel s).label=node.label.relabel s := by
  cases node <;> rfl

/-- A derived SOURCE atom and its literal coordinate, not a field of history or net. -/
structure OriginalAtom (source : LTerm) (F : List Path) (n : Nat) (leftKind rightKind : Bool) where
  basisOccurrence : WindowOccurrences (initLabels source.erase) F n leftKind rightKind
  shape : WindowShape source F basisOccurrence.position (basisOccurrence.node.relabel (initialRelabelling source 0)) leftKind rightKind

theorem actual_old_interior_atom
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (lookup : localTarget.subterm position=some node)
    (window : node.label.letters=pre++[bar leftKind dl,.atom n,bar rightKind dr]++post) :
    Nonempty (OriginalAtom source F n leftKind rightKind) := by
  obtain ⟨ctx,finish,route⟩:=actual_old_node_route old localHistory lookup
  obtain ⟨geometry⟩:=route_window_geometry (init_is_INIT _) route window
  obtain ⟨occurrences⟩:=geometry.occurrences (init_is_INIT _)
  obtain ⟨shape⟩:=occurrences.relabelled_shape (initialRelabelling source 0)
  have factored : (initLabels source.erase).relabel (initialRelabelling source 0)=source :=
    initialRelabelling_factor source 0
  rw [factored] at shape
  exact ⟨⟨occurrences,shape⟩⟩

def OriginalAtom.edge (out : OriginalAtom source F n leftKind rightKind) : SyntaxIncidence.Edge source :=
  ⟨out.basisOccurrence.position,by rw [←LTerm.erase_subterm,out.shape.lookup];rfl⟩

theorem OriginalAtom.full_image (out : OriginalAtom source F n leftKind rightKind) :
    SyntaxIncidence.label source out.edge=initialRelabelling source 0 n := by
  rw [SyntaxIncidence.label_of_lookup source out.edge out.shape.lookup,label_relabel,out.basisOccurrence.atomic]
  rfl

structure Comparison (source : LTerm) (F : List Path) (n m : Nat) (leftKind rightKind : Bool)
    (closed : Closed source.erase) where
  left : OriginalAtom source F n leftKind rightKind
  right : OriginalAtom source F m leftKind rightKind
  labelEq : SyntaxIncidence.label source left.edge=SyntaxIncidence.label source right.edge
  leftAux : AuxiliaryAt source left.edge.val
  rightAux : AuxiliaryAt source right.edge.val
  sourceIso : SuccessfulEndpointIso source closed (SyntaxIncidence.source source left.edge) (SyntaxIncidence.source source right.edge)
  targetIso : SuccessfulEndpointIso source closed (SyntaxIncidence.target source closed left.edge) (SyntaxIncidence.target source closed right.edge)

def compare_original_atoms (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some alpha)
    (left : OriginalAtom source F n leftKind rightKind)
    (right : OriginalAtom source F m leftKind rightKind)
    (sameImage : initialRelabelling source 0 n=initialRelabelling source 0 m) :
    Comparison source F n m leftKind rightKind closed := by
  have isos:=WindowShape.endpoint_isos closed selected left.shape right.shape
  refine ⟨left,right,left.full_image.trans (sameImage.trans right.full_image.symm),
    left.shape.auxiliary,right.shape.auxiliary,?_,?_⟩
  · rw [SyntaxIncidence.source_eq_of_spec source left.edge left.shape.source_spec,
      SyntaxIncidence.source_eq_of_spec source right.edge right.shape.source_spec]
    exact isos.1
  · rw [SyntaxIncidence.target_eq_of_spec source closed left.edge left.shape.target_spec,
      SyntaxIncidence.target_eq_of_spec source closed right.edge right.shape.target_spec]
    exact isos.2

/-- Both actual OLD windows supply all SOURCE coordinates, both successful endpoint pairs and Aux.
Opaque image equality is lexical; no endpoint isomorphism or physical equality is a premise. -/
theorem actual_old_interior_atom_comparison (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some alpha)
    (leftOld : Marked.RelativeOldHistory F leftPs (Marked.mark F source.erase) leftMarked)
    (leftHistory : History leftPs (initLabels source.erase) leftTarget)
    (leftLookup : leftTarget.subterm leftPosition=some leftNode)
    (leftWindow : leftNode.label.letters=leftPre++[bar leftKind dl,.atom n,bar rightKind dr]++leftPost)
    (rightOld : Marked.RelativeOldHistory F rightPs (Marked.mark F source.erase) rightMarked)
    (rightHistory : History rightPs (initLabels source.erase) rightTarget)
    (rightLookup : rightTarget.subterm rightPosition=some rightNode)
    (rightWindow : rightNode.label.letters=rightPre++[bar leftKind el,.atom m,bar rightKind er]++rightPost)
    (sameImage : initialRelabelling source 0 n=initialRelabelling source 0 m) :
    Nonempty (Comparison source F n m leftKind rightKind closed) := by
  obtain ⟨left⟩:=actual_old_interior_atom leftOld leftHistory leftLookup leftWindow
  obtain ⟨right⟩:=actual_old_interior_atom rightOld rightHistory rightLookup rightWindow
  exact ⟨compare_original_atoms closed selected left right sameImage⟩

section
variable {N B W : Type} [Graph.FiniteNames N] [Graph.FiniteNames B] [Graph.FiniteNames W]
variable {g : Graph.Net signature N B W} {root : B}

theorem Comparison.atom_words_equal
    (out : Comparison source F n m leftKind rightKind closed)
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (auxiliary : AuxiliarySeparation closed sourceSelection) :
    selection.atomWord n=selection.atomWord m := by
  have localMatching : Matches g root (initLabels source.erase).erase := by
    simpa only [erase_initLabels] using matching
  have leftEval:=selection.atomWord_occurrence_segments (init_is_INIT _) localMatching matching
    out.left.basisOccurrence.occurrence out.left.basisOccurrence.atomic (sourceSelection out.left.edge)
  have rightEval:=selection.atomWord_occurrence_segments (init_is_INIT _) localMatching matching
    out.right.basisOccurrence.occurrence out.right.basisOccurrence.atomic (sourceSelection out.right.edge)
  have pieces : (sourceSelection out.left.edge).fragment.segments=(sourceSelection out.right.edge).fragment.segments := by
    apply Classical.byContradiction
    intro different
    exact auxiliary out.left.edge out.right.edge out.leftAux out.rightAux out.labelEq different ⟨out.sourceIso,out.targetIso⟩
  exact leftEval.trans (pieces.trans rightEval.symm)
end

end InteriorSourceBlock
end Lamping.Lambda.Labelled

#print axioms Lamping.Lambda.Labelled.InteriorSourceBlock.route_walk
#print axioms Lamping.Lambda.Labelled.InteriorSourceBlock.route_window_geometry
#print axioms Lamping.Lambda.Labelled.InteriorSourceBlock.WindowGeometry.occurrences
#print axioms Lamping.Lambda.Labelled.InteriorSourceBlock.WindowShape.auxiliary
#print axioms Lamping.Lambda.Labelled.InteriorSourceBlock.WindowShape.endpoint_isos
#print axioms Lamping.Lambda.Labelled.InteriorSourceBlock.actual_old_interior_atom_comparison
#print axioms Lamping.Lambda.Labelled.InteriorSourceBlock.Comparison.atom_words_equal

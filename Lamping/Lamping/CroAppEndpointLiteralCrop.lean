import Lamping.Lamping.ControlOnlyConnections
import Lamping.Lamping.ControlCorridorEndpoints
import Lamping.Lamping.ActionCopiedFunctionPrefixes
import Lamping.Lamping.ActionFunctionPadding
import Lamping.Lamping.SourceActionProperAuxAccess
import Lamping.Lamping.ActionKeptFragmentComparison
import Lamping.Lamping.ActionRawOutsideCut
import Lamping.Lamping.ActionMatching

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section Endpoints
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
private theorem pair_at_cut (before : List (Endpoint g)) (e f : Endpoint g) (after : List (Endpoint g)) :
    (e,f)∈(before++e::f::after).zip (before++e::f::after).tail := by
  induction before with
  | nil => simp
  | cons x before ih =>
    cases before with
    | nil => exact List.mem_cons_of_mem _ ih
    | cons y before => exact List.mem_cons_of_mem _ ih
private theorem proper_not_control (node : N)
    (proper : (g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) :
    ¬IsControlNode (g:=g) node := by
  rintro ⟨op,shape,control⟩
  rcases proper with app|lam
  · have same : op=.app := Kind.op.inj (shape.symm.trans app)
    subst op
    rcases control with h|h|h <;> cases h
  · have same : op=.lam := Kind.op.inj (shape.symm.trans lam)
    subst op
    rcases control with h|h|h <;> cases h

/-- An occurrence ordinal after the first departure cannot be an APP/lambda
node departure. This rules out repeated internal visits, not just distinct
endpoint values. No full-graph Independence premise is used. -/
theorem RedexConnection.no_internal_proper_departure (connection : RedexConnection g)
    (node : N) (port : Port (g.label node).sort)
    (proper : (g.label node).sort=.op .app ∨(g.label node).sort=.op .lam)
    (before : List (Endpoint g)) (previous : Endpoint g) (after : List (Endpoint g))
    (split : connection.edges=before++previous::(.inl ⟨node,port⟩)::after) : False := by
  have atPair := connection.control_only previous (.inl ⟨node,port⟩)
    (by rw [split];exact pair_at_cut before previous (.inl ⟨node,port⟩) after)
  exact proper_not_control node proper (atPair.departure_control node port)

/-- A nonfinal arrival at a proper node likewise contradicts the SAME whole
control-only connection; lambda terminal is kept as the genuine exception. -/
theorem RedexConnection.no_nonterminal_proper_arrival (connection : RedexConnection g)
    (node : N) (port : Port (g.label node).sort)
    (proper : (g.label node).sort=.op .app ∨(g.label node).sort=.op .lam)
    (before : List (Endpoint g)) (entry next : Endpoint g) (after : List (Endpoint g))
    (split : connection.edges=before++entry::next::after)
    (arrives : g.wire entry=.inl ⟨node,port⟩) : False := by
  have atPair := connection.control_only entry next
    (by rw [split];exact pair_at_cut before entry next after)
  exact proper_not_control node proper (atPair.arrival_control node port arrives)
end Endpoints

section CroApp
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.croAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.croAction Op.app i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => unaryRightCore Op.cro Op.app (Bij.refl _) i (j-1)
local notation "fnRaw" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitCut" => (Sum.inr (Sum.inl (Sum.inr (Sum.inl ()))) : Endpoint cut)
local notation "exitRaw" => (Sum.inl exitCut : PlugSegment cut rhs)
local notation "oldExit" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr ())) : Endpoint site.net)
local notation "copyCtx" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) appCtx) : Endpoint site.reduce)
local notation "copyFn" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inl ())) : Endpoint site.reduce)

/-- The copied app context endpoint is CONSTRUCTED, not a desired target
parent field. The cro reader changes its final context before the app token. -/
private theorem cro_app_parent_literal
    {root : B} {term : Term} {boundary : B → Bool}
    (matching : Matches site.net root term) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (source : RootAccess site.net root)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩))) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      target.val.getLast?=some (site.reduce.wire copyCtx) := by
  obtain ⟨a,b,labels⟩ := source.property.1.1
  obtain ⟨q,uniform⟩ := site.source_control_branch matching inputs flow positive
    (Or.inr (Or.inl rfl)) rfl source.val appCtx HEq.rfl labels source.property.2.1 finish
  obtain ⟨middle,inverse⟩ := uniform a b labels
  cases q
  let inside : List (Endpoint rhs) := [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr ()⟩]
  have insideLabels : Labelling rhs inside b middle := .cons (.node _ _ _ inverse) (.single _ _)
  obtain ⟨es,newLabels,newHead,newLast,word⟩ := site.source_pending_expansion (.cro .app i j lt)
    matching inputs flow positive labels source.property.2.1 (.inr false) finish inside insideLabels rfl
  have physicalLast : es.getLast?=some (site.reduce.wire copyCtx) := by
    change es.getLast?=some (AG.plugRight cut rhs (.inl ⟨.inr false,.inr ()⟩))
    simpa only [inside,List.getLast?_cons_cons,List.getLast?_singleton,Option.map_some] using newLast
  have sameKind : accessKind site.reduce es=accessKind site.net source.val := by
    simp only [accessKind,physicalLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := newLabels.root_forward_of_flow newFlow root newHead positive
  have typed : ∃ k,accessKind site.reduce es=some k := by rw [sameKind];exact source.property.2.2
  have noTokens : accessTokens (schema).right.net inside=[] := by
    change accessTokens rhs inside=[]
    rfl
  rw [noTokens,List.append_nil] at word
  exact ⟨⟨es,⟨⟨⟨a,middle,newLabels⟩,forward⟩,newHead,typed⟩⟩,word,physicalLast⟩

private theorem cro_kept_child_literal
    {root : B} {term : Term} {boundary : B → Bool}
    (matching : Matches site.net root term) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (source : RootAccess site.net root) (node : K) (port : Port (kept node).sort)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inl node,port⟩)))
    {a b : Context} (sourceAssignment : Labelling site.net source.val a b) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      target.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩)) ∧
      Labelling site.reduce target.val a b := by
  let last : Endpoint cut := (cut).wire (.inl ⟨node,port⟩)
  have oldLast : source.val.getLast?=some (site.outsideEnd last) :=
    finish.trans (congrArg some (site.outsideEnd_wire (.inl ⟨node,port⟩)))
  obtain ⟨es,labels,head,lastEq,word⟩ := site.action_source_outside_word (.cro .app i j lt)
    matching inputs flow positive sourceAssignment source.property.2.1 last oldLast
  have actualLast : es.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩)) :=
    lastEq.trans (congrArg some (plugLeft_wire cut rhs (.inl ⟨node,port⟩)).symm)
  have kind : accessKind site.reduce es=accessKind site.net source.val := by
    simp only [accessKind,actualLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := labels.root_forward_of_flow newFlow root head positive
  have typed : ∃ k,accessKind site.reduce es=some k := by rw [kind];exact source.property.2.2
  exact ⟨⟨es,⟨⟨⟨a,b,labels⟩,forward⟩,head,typed⟩⟩,word,actualLast,labels⟩

/-- A smallest literal endpoint crop: the copied cro/app function edge is
identified in the SAME target redex before any control-count assertion. The
rooted child's original a/b assignment is retained; the new phi seam is an
output and is not equated with the old phi entry seam. -/
theorem ActualRedexAccess.cro_app_literal_crop
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
      ∃ (principal : SiteActionPrincipal site) (oldTail : List (Endpoint site.net))
        (rawTail : List (PlugSegment cut rhs)) (newSeam : Context),
        source.connection.edges=reverseEdges principal.edges++oldExit::oldTail ∧
        target.connection.edges.map (plugEnd (cut).label (rhs).label).invFun=fnRaw::exitRaw::rawTail ∧
        ActionCanonicalBlocks site principal (exitRaw::rawTail) (oldExit::oldTail) ∧
        PlugLabelling cut rhs (exitRaw::rawTail) newSeam b := by
  obtain ⟨newParent,parentWord,parentFinish⟩ :=
    cro_app_parent_literal site matching inputs flow positive source.parent sourceApp
  obtain ⟨newChild,childWord,childFinish,childLabels⟩ :=
    cro_kept_child_literal site matching inputs flow positive source.child lamNode lamPort sourceLam sourceAssignment
  have targetMatches := site.action_matches_rootInputs (.cro .app i j lt) flow root positive balance rootDepth inputs oldT matching
  obtain ⟨target⟩ := targetMatches.actual_redex_access redex
  let rhsSplit : Bij (PlugSegment cut rhs) (Endpoint site.reduce) :=
    plugEnd (cut).label (rhs).label
  have parentEq : newParent=target.parent := targetMatches.accessWord_injective
    (parentWord.trans (source.parentWord.trans target.parentWord.symm))
  have childEq : newChild=target.child := targetMatches.accessWord_injective
    (childWord.trans (source.childWord.trans target.childWord.symm))
  have actualParentFinish : target.parent.val.getLast?=some (site.reduce.wire copyCtx) := by
    rw [←parentEq]
    exact parentFinish
  have actualChildFinish : target.child.val.getLast?=some (site.reduce.wire (.inl ⟨.inl lamNode,lamPort⟩)) := by
    rw [←childEq]
    exact childFinish
  have actualChildLabels : Labelling site.reduce target.child.val a b := by
    rw [←childEq]
    exact childLabels
  have wired := Option.some.inj (target.parentFinish.symm.trans actualParentFinish)
  have physicalPorts := congrArg site.reduce.wire.mate wired
  simp only [Pairing.involutive] at physicalPorts
  have contexts : (⟨target.connection.app,target.ctx⟩ : NodePort signature _ site.reduce.label)=
      ⟨.inr (.inl ()),appCtx⟩ := Sum.inl.inj physicalPorts
  have appEq : target.connection.app=.inr (.inl ()) := congrArg Sigma.fst contexts
  have functions : (⟨target.connection.app,target.connection.appPort⟩ : NodePort signature _ site.reduce.label)=
      ⟨.inr (.inl ()),.inl ()⟩ := Sigma.ext appEq target.connection.appPrincipal
  have start : target.connection.edges.head?=some copyFn :=
    target.connection.start.trans (congrArg (fun p => some (Sum.inl p)) functions)
  have rawHead : (target.connection.edges.map rhsSplit.invFun).head?=some fnRaw := by
    rw [List.head?_map,start]
    rfl
  obtain ⟨targetTail,targetSplit⟩ := List.head?_eq_some_iff.mp start
  have childWithCut : Labelling site.reduce (target.parent.val++copyFn::targetTail) a b := by
    rw [←targetSplit,←target.split]
    exact actualChildLabels
  obtain ⟨newSeam,_rootFnLabels,pieceLabels⟩ := childWithCut.split_segment
  have actualPieceLabels : Labelling site.reduce target.connection.edges newSeam b := by
    rw [targetSplit]
    exact pieceLabels
  have childKind : accessKind site.reduce target.connection.edges=accessKind site.reduce target.child.val := by
    simp only [accessKind,target.split,List.getLast?_append,target.connection.finish,Option.some_or]
  have pieceTyped : ∃ k,accessKind site.reduce target.connection.edges=some k := by
    rw [childKind]
    exact target.child.property.2.2
  obtain ⟨rawTail,rawPieceSplit,suffixLabels⟩ := unary_typed_function_prefix cut Op.cro (Bij.refl _) i (j-1)
    (actualPieceLabels.plug_decomposition cut rhs) rawHead
    (by simpa only [plug_decomposition_flatten] using pieceTyped)
  change List (PlugSegment cut rhs) at rawTail
  change target.connection.edges.map rhsSplit.invFun=fnRaw::exitRaw::rawTail at rawPieceSplit
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  have parentWordEq : accessWord site.net source.parent.val=accessWord site.reduce target.parent.val :=
    source.parentWord.trans target.parentWord.symm
  obtain ⟨parentInput,parentOutput,parentLabels⟩ := target.parent.property.1.1
  have paddedParent := site.cro_function_padding_access flow root positive matching principal source.parent
    target.parent parentWordEq actualParentFinish parentLabels
  have whole := (site.action_kept_canonical_access (.cro .app i j lt) flow root positive matching principal
    source.child target.child (source.childWord.trans target.childWord.symm) lamNode lamPort
    actualChildFinish actualChildLabels).1
  change ActionCanonicalBlocks site principal
    (target.parent.val.map rhsSplit.invFun++[fnRaw,exitRaw])
    (source.parent.val++reverseEdges principal.edges++[oldExit]) at paddedParent
  change ActionCanonicalBlocks site principal (target.child.val.map rhsSplit.invFun) source.child.val at whole
  let rawParent : List (PlugSegment cut rhs) := target.parent.val.map rhsSplit.invFun
  let rawWhole : List (PlugSegment cut rhs) := target.child.val.map rhsSplit.invFun
  let rawPad : List (PlugSegment cut rhs) := rawParent++[fnRaw,exitRaw]
  have wholeSplit : rawWhole=@List.append (PlugSegment cut rhs) rawPad rawTail := by
    change target.child.val.map rhsSplit.invFun=
      @List.append (PlugSegment cut rhs)
        (@List.append (PlugSegment cut rhs) (target.parent.val.map rhsSplit.invFun) [fnRaw,exitRaw]) rawTail
    rw [target.split,List.map_append,rawPieceSplit]
    exact (List.append_assoc (target.parent.val.map rhsSplit.invFun) [fnRaw,exitRaw] rawTail).symm
  have padLast : rawPad.getLast?=some exitRaw := by
    simp only [rawPad,List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,_cutSeam,oldWholeSplit,suffixCanonical,_padLabels,_cutLabels⟩ :=
    whole.cut_at_raw_parent site paddedParent (actualChildLabels.plug_decomposition cut rhs)
      wholeSplit exitCut padLast
  have oldPieceSplit : source.connection.edges=reverseEdges principal.edges++oldExit::oldTail := by
    have same := source.split.symm.trans oldWholeSplit
    have normalized : source.parent.val++source.connection.edges=
        source.parent.val++(reverseEdges principal.edges++oldExit::oldTail) := by
      simpa only [List.append_assoc,List.singleton_append] using same
    exact List.append_cancel_left normalized
  exact ⟨target,actualChildLabels,principal,oldTail,rawTail,newSeam,oldPieceSplit,
    rawPieceSplit,suffixCanonical,suffixLabels⟩
end CroApp
end Lamping.AG

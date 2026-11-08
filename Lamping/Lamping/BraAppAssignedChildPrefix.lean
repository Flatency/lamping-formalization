import Lamping.Lamping.BraAppCopiedContextAccess
import Lamping.Lamping.SourceActionKeptAccess
import Lamping.Lamping.ActionCopiedFunctionPrefixes

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.braAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.braAction Op.app i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => unaryRightCore Op.bra Op.app (Bij.refl _) i (j+1)
local notation "copiedContext" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) appCtx) : Endpoint site.reduce)
local notation "copiedFunction" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inl ())) : Endpoint site.reduce)
local notation "functionRaw" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitRaw" => (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inl ())))) : PlugSegment cut rhs)

private theorem kept_assigned_access
    {root : B} {term : Term} {directions : B → Bool}
    (matching : Matches site.net root term) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (source : RootAccess site.net root) (node : K) (port : Port (kept node).sort)
    (sourceFinish : source.val.getLast?=some (site.net.wire (Sum.inl ⟨Sum.inl node,port⟩)))
    {a b : Context} (sourceLabels : Labelling site.net source.val a b) :
    ∃ copied : RootAccess site.reduce root,
      accessWord site.reduce copied.val=accessWord site.net source.val ∧
      copied.val.getLast?=some (site.reduce.wire (Sum.inl ⟨Sum.inl node,port⟩)) ∧
      Labelling site.reduce copied.val a b := by
  let last : Endpoint cut := (cut).wire (Sum.inl ⟨node,port⟩)
  have oldLast : source.val.getLast?=some (site.outsideEnd last) :=
    sourceFinish.trans (congrArg some (site.outsideEnd_wire (Sum.inl ⟨node,port⟩)))
  obtain ⟨actual,labels,rooted,finish,word⟩ := site.action_source_outside_word
    (.bra .app i j lt) matching inputs flow positive sourceLabels source.property.2.1 last oldLast
  have keptFinish : actual.getLast?=some (site.reduce.wire (Sum.inl ⟨Sum.inl node,port⟩)) :=
    finish.trans (congrArg some (plugLeft_wire cut rhs (Sum.inl ⟨node,port⟩)).symm)
  have kind : accessKind site.reduce actual=accessKind site.net source.val := by
    simp only [accessKind,keptFinish,sourceFinish,Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := labels.root_forward_of_flow newFlow root rooted positive
  have typed : ∃ k,accessKind site.reduce actual=some k := by
    rw [kind]
    exact source.property.2.2
  exact ⟨⟨actual,⟨⟨⟨a,b,labels⟩,forward⟩,rooted,typed⟩⟩,word,keptFinish,labels⟩

/-- The actual original child assignment is preserved. The separate parent
reader packet records its own real contexts, without identifying two seams. -/
theorem ActualRedexAccess.bra_app_assigned_child
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
      target.parent.val.getLast?=some (site.reduce.wire copiedContext) ∧
      target.child.val.getLast?=some (site.reduce.wire (Sum.inl ⟨Sum.inl lamNode,lamPort⟩)) ∧
      ∃ parentInput parentOutput middle,
        Labelling site.net source.parent.val parentInput parentOutput ∧
        Labelling site.reduce target.parent.val parentInput middle ∧
        Traversal i (.op .bra) (Sum.inl ()) (Sum.inr ()) parentOutput middle := by
  obtain ⟨parentInput,parentOutput,parentLabels⟩ := source.parent.property.1.1
  obtain ⟨target,parentFinish,middle,targetParentLabels,reader⟩ :=
    ActualRedexAccess.bra_app_copied_parent site source matching inputs flow positive balance rootDepth transparency
      sourceApp parentLabels
  obtain ⟨copied,childWord,childFinish,childLabels⟩ := kept_assigned_access site
    matching inputs flow positive source.child lamNode lamPort sourceLam sourceAssignment
  have targetMatches := site.action_matches_rootInputs (.bra .app i j lt)
    flow root positive balance rootDepth inputs transparency matching
  have sameChild : copied=target.child := targetMatches.accessWord_injective
    (childWord.trans (source.childWord.trans target.childWord.symm))
  have actualLabels : Labelling site.reduce target.child.val a b := by
    rw [←sameChild]
    exact childLabels
  have actualFinish : target.child.val.getLast?=some
      (site.reduce.wire (Sum.inl ⟨Sum.inl lamNode,lamPort⟩)) := by
    rw [←sameChild]
    exact childFinish
  exact ⟨target,actualLabels,parentFinish,actualFinish,parentInput,parentOutput,middle,
    parentLabels,targetParentLabels,reader⟩

/-- The complete SAME target connection starts with the actual copied
function and glue exit. Its suffix labelling gives the NEW seam as output. -/
theorem ActualRedexAccess.bra_app_copied_function_prefix
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
      target.parent.val.getLast?=some (site.reduce.wire copiedContext) ∧
      ∃ (rawTail : List (PlugSegment cut rhs)) (newSeam : Context),
        Labelling site.reduce target.connection.edges newSeam b ∧
        target.connection.edges.map (plugEnd (cut).label (rhs).label).invFun=
          functionRaw::exitRaw::rawTail ∧
        PlugLabelling cut rhs (exitRaw::rawTail) newSeam b := by
  obtain ⟨target,childLabels,parentFinish,_childFinish,_readerPacket⟩ :=
    ActualRedexAccess.bra_app_assigned_child site source matching inputs flow positive balance rootDepth transparency
      sourceApp lamNode lamPort sourceLam sourceAssignment
  have wires := Option.some.inj (target.parentFinish.symm.trans parentFinish)
  have ports := congrArg site.reduce.wire.mate wires
  simp only [Pairing.involutive] at ports
  have contexts : (⟨target.connection.app,target.ctx⟩ : NodePort signature _ site.reduce.label)=
      ⟨Sum.inr (Sum.inl ()),appCtx⟩ := Sum.inl.inj ports
  have appEq : target.connection.app=Sum.inr (Sum.inl ()) := congrArg Sigma.fst contexts
  have functions : (⟨target.connection.app,target.connection.appPort⟩ : NodePort signature _ site.reduce.label)=
      ⟨Sum.inr (Sum.inl ()),Sum.inl ()⟩ := Sigma.ext appEq target.connection.appPrincipal
  have first : target.connection.edges.head?=some copiedFunction :=
    target.connection.start.trans (congrArg (fun p=>some (Sum.inl p)) functions)
  have rawHead : (target.connection.edges.map (plugEnd (cut).label (rhs).label).invFun).head?=
      some functionRaw := by
    rw [List.head?_map,first]
    rfl
  obtain ⟨tail,connectionSplit⟩ := List.head?_eq_some_iff.mp first
  have wholeLabels : Labelling site.reduce (target.parent.val++copiedFunction::tail) a b := by
    rw [←connectionSplit,←target.split]
    exact childLabels
  obtain ⟨newSeam,_prefixLabels,suffixLabels⟩ := wholeLabels.split_segment
  have pieceLabels : Labelling site.reduce target.connection.edges newSeam b := by
    rw [connectionSplit]
    exact suffixLabels
  have sameKind : accessKind site.reduce target.connection.edges=accessKind site.reduce target.child.val := by
    simp only [accessKind,target.split,List.getLast?_append,target.connection.finish,Option.some_or]
  have typed : ∃ kind,accessKind site.reduce target.connection.edges=some kind := by
    rw [sameKind]
    exact target.child.property.2.2
  obtain ⟨rawTail,literal,suffix⟩ := unary_typed_function_prefix cut Op.bra (Bij.refl _) i (j+1)
    (pieceLabels.plug_decomposition cut rhs) rawHead
    (by simpa only [plug_decomposition_flatten] using typed)
  exact ⟨target,childLabels,parentFinish,rawTail,newSeam,pieceLabels,literal,suffix⟩
end
end Lamping.AG

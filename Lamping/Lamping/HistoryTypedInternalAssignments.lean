import Lamping.Lamping.HistoryTypedBinders
import Lamping.Lamping.PairedDetourAssignments
import Lamping.Lamping.PairedAnchoredReset
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
private theorem lambda_body_identity {kind : Kind} {index : Nat} {ctx body : Port kind}
    (sort : kind=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    (context : Context) : Traversal index kind ctx body context context := by
  subst kind
  cases eq_of_heq ctxRole
  cases eq_of_heq bodyRole
  exact .direct (.lamBody context)
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}
/-- A beta insertion inside an earlier lambda preserves that specified
lambda's shell for the GIVEN assignment. The anchored reset preserves its
low shell even when its height exceeds the inner application height. -/
theorem TypedSyntaxBinders.internal_copied_assignment
    (selection : SourceEdgeSelection original g root) (edge : BetaEdge g)
    {current selectedBody outerBody : LTerm} {selectedPos outerPos q z : Path}
    {selectedStamp outerStamp : Labelled.Label}
    (typed : TypedSyntaxBinders selection edge current)
    (selectedLambda : current.subterm selectedPos=some (.lam selectedStamp selectedBody))
    (selectedLeaf : ArgumentOccurrence selectedBody.erase q)
    (outerLambda : current.subterm outerPos=some (.lam outerStamp outerBody))
    (outerLeaf : ArgumentOccurrence outerBody.erase z)
    (pre loop tail ambient middle : List (Endpoint g))
    (selectedEval : current.sourceTrail selection.atomWord edge.principal edge.reverseRoute selectedPos=some (pre++edge.principal))
    (selectedBodyEval : current.sourceTrail selection.atomWord edge.principal edge.reverseRoute (selectedPos++(.body::q))=some (pre++edge.principal++loop))
    (outerEval : current.sourceTrail selection.atomWord edge.principal edge.reverseRoute outerPos=some ambient)
    (outerBodyEval : current.sourceTrail selection.atomWord edge.principal edge.reverseRoute (outerPos++(.body::z))=some (pre++edge.argEnd::tail))
    {binder : N} {ctx body : Port (g.label binder).sort}
    (shape : (g.label binder).sort=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (bodyRole : HEq body lamBody)
    (outerEnd : ambient.getLast?=some (g.wire (.inl ⟨binder,ctx⟩)))
    (split : pre=ambient++(.inl ⟨binder,body⟩)::middle)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    (rooted : pre.head?=some (.inr (.inl root)))
    (preEnd : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (loopEnd : loop.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)))
    {a output seam : Context} {count : Nat}
    (whole : BetaDetourBlocks g
      (pre++edge.principal++loop++edge.reverseRoute++(edge.argEnd::tail)) a output count)
    (before : ExpandedLabelling g ambient a seam) :
    Context.SameShell (g.label binder).index seam output := by
  obtain ⟨appContext,bodyEnd,bodyCount,prefixCount,tailCount,bodyStream,prefixStream,selectedAmbient,tailStream⟩ :=
    whole.detour_assignments flow positive edge pre loop tail preEnd loopEnd
  have selectedEnd : (pre++edge.principal).getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamCtx⟩)) := by
    simp only [List.getLast?_append,edge.principalEnd,Option.some_or]
  have selectedShape : (g.label edge.lam).sort=.op .lam := by rw [edge.lamLabel]; rfl
  have shell : Context.SameShell edge.index appContext bodyEnd := by
    have actual := typed selectedLambda selectedLeaf selectedEval selectedBodyEval
      selectedShape edge.lamCtx_role selectedEnd bodyStream selectedAmbient
    simpa only [edge.lamLabel] using actual
  have bodyTurn (context : Context) : LabelledTurn g (.inl ⟨binder,ctx⟩) (.inl ⟨binder,body⟩) context context :=
    .node binder ctx body (lambda_body_identity shape ctxRole bodyRole context)
  have reference : ExpandedLabelling g (ambient++[.inl ⟨binder,body⟩]) a seam := by
    apply before.splice outerEnd (.single _ seam) rfl
    simpa only [Pairing.involutive] using ExpandedTurn.ordinary (bodyTurn seam)
  have binderLabel : g.label binder=label .lam (g.label binder).index := by
    generalize g.label binder=actual at shape ⊢
    cases actual with
    | mk sort index => cases shape; rfl
  have bodyPositive : flowEndpoint g flow.nodes boundary flow.vertices (.inl ⟨binder,body⟩)=true :=
    (AtProperRole.lamBody binder body (g.label binder).index binderLabel bodyRole).outgoing_flow
      trivial flow.nodes boundary flow.vertices positive
  have bodyDepth : endpointDepth g balance.nodes heights balance.vertices (.inl ⟨binder,body⟩)=((g.label binder).index : Int) :=
    (AtProperRole.lamBody binder body (g.label binder).index binderLabel bodyRole).outgoing_depth
      balance root rootDepth trivial
  have lastDepth : ∀ e,pre.getLast?=some e → endpointDepth g balance.nodes heights balance.vertices e=(edge.index : Int) := by
    intro e last
    have same := Option.some.inj (last.symm.trans preEnd)
    rw [same,balance.wiring]
    exact (AtProperRole.appCtx edge.app edge.appCtx edge.index edge.appLabel edge.appCtx_role).incoming_depth balance root trivial
  obtain ⟨newInput,newCut,leftCount,newPrefix,leftStream,keptShell⟩ := prefixStream.relabel_anchored_indexed
    flow positive balance rootDepth rooted split bodyPositive bodyDepth lastDepth reference shell
  have ambientNonempty : ambient≠[] := by intro empty; rw [empty] at outerEnd; cases outerEnd
  obtain ⟨newSeam,newBefore⟩ := (leftStream.labelling g).prefix ambientNonempty
  have extended : ExpandedLabelling g (ambient++[.inl ⟨binder,body⟩]) newInput newSeam := by
    apply newBefore.splice outerEnd (.single _ newSeam) rfl
    simpa only [Pairing.involutive] using ExpandedTurn.ordinary (bodyTurn newSeam)
  have sameSeam : newSeam=newCut := extended.output_unique (leftStream.labelling g)
  have transition : BetaDetourBlocks g
      (g.wire (.inl ⟨edge.app,edge.appCtx⟩)::edge.argEnd::tail) bodyEnd output tailCount := by
    apply BetaDetourBlocks.ordinary ?_ tailStream
    simpa only [Pairing.involutive] using edge.app_arg_turn bodyEnd
  have oldWhole := newPrefix.append_at_last transition preEnd
  have outerBodyEval' : current.sourceTrail selection.atomWord edge.principal edge.reverseRoute (outerPos++(.body::z))=
      some (ambient++((.inl ⟨binder,body⟩)::(middle++edge.argEnd::tail))) := by
    simpa only [split,List.append_assoc,List.cons_append] using outerBodyEval
  have oldWhole' : BetaDetourBlocks g
      (ambient++((.inl ⟨binder,body⟩)::(middle++edge.argEnd::tail))) newInput output (prefixCount+tailCount) := by
    simpa only [split,List.append_assoc,List.cons_append] using oldWhole
  have outerShell := typed outerLambda outerLeaf outerEval outerBodyEval' shape ctxRole outerEnd oldWhole' newBefore
  rw [sameSeam] at outerShell
  exact fun k low => (keptShell k low).trans (outerShell k low)
end
end Lamping.AG
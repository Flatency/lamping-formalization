import Lamping.Lamping.HistoryTypedBinders
import Lamping.Lamping.PairedDetourAssignments
import Lamping.Lamping.PairedStreamHighTails
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}
/-- Transfer the supplied copied-lambda assignment back to the two specified
OLD binder occurrences. All new argument assignments are constructed from
the given detour; neither generatedness nor a total-label premise is used. -/
theorem TypedSyntaxBinders.copied_assignment
    (selection : SourceEdgeSelection original g root) (edge : BetaEdge g)
    {current selectedBody argumentBody : LTerm} {selectedPos argumentPos q z : Path}
    {selectedStamp argumentStamp : Labelled.Label}
    (typed : TypedSyntaxBinders selection edge current)
    (selectedLambda : current.subterm selectedPos=some (.lam selectedStamp selectedBody))
    (selectedLeaf : ArgumentOccurrence selectedBody.erase q)
    (argumentLambda : current.subterm argumentPos=some (.lam argumentStamp argumentBody))
    (argumentLeaf : ArgumentOccurrence argumentBody.erase z)
    (pre loop argPre argLoop : List (Endpoint g))
    (selectedEval : current.sourceTrail selection.atomWord edge.principal edge.reverseRoute selectedPos=some (pre++edge.principal))
    (selectedBodyEval : current.sourceTrail selection.atomWord edge.principal edge.reverseRoute (selectedPos++(.body::q))=some (pre++edge.principal++loop))
    (argumentEval : current.sourceTrail selection.atomWord edge.principal edge.reverseRoute argumentPos=some (pre++edge.argEnd::argPre))
    (argumentBodyEval : current.sourceTrail selection.atomWord edge.principal edge.reverseRoute (argumentPos++(.body::z))=some (pre++edge.argEnd::(argPre++argLoop)))
    {binder : N} {ctx : Port (g.label binder).sort}
    (shape : (g.label binder).sort=.op .lam) (role : HEq ctx (Sum.inl () : Port (.op .lam)))
    (argumentEnd : (pre++edge.argEnd::argPre).getLast?=some (g.wire (.inl ⟨binder,ctx⟩)))
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    (rooted : pre.head?=some (.inr (.inl root)))
    (preEnd : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (loopEnd : loop.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)))
    {a output seam : Context} {count : Nat}
    (whole : BetaDetourBlocks g
      (pre++edge.principal++loop++edge.reverseRoute++(edge.argEnd::(argPre++argLoop))) a output count)
    (before : ExpandedLabelling g
      (pre++edge.principal++loop++edge.reverseRoute++(edge.argEnd::argPre)) a seam) :
    Context.SameShell (g.label binder).index seam output := by
  obtain ⟨appContext,bodyEnd,bodyCount,prefixCount,tailCount,bodyStream,prefixStream,ambient,tailStream⟩ :=
    whole.detour_assignments flow positive edge pre loop (argPre++argLoop) preEnd loopEnd
  have selectedEnd : (pre++edge.principal).getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamCtx⟩)) := by
    simp only [List.getLast?_append,edge.principalEnd,Option.some_or]
  have selectedShape : (g.label edge.lam).sort=.op .lam := by rw [edge.lamLabel]; rfl
  have shell : Context.SameShell edge.index appContext bodyEnd := by
    have actual := typed selectedLambda selectedLeaf selectedEval selectedBodyEval
      selectedShape edge.lamCtx_role selectedEnd bodyStream ambient
    simpa only [edge.lamLabel] using actual
  obtain ⟨newInput,newPrefix⟩ := prefixStream.relabel_app_prefix_indexed
    flow positive balance rootDepth edge rooted preEnd shell
  have bodyFinish : (pre++edge.principal++loop).getLast?=
      some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) := by
    simp only [List.getLast?_append,loopEnd,Option.some_or]
  have canonical := bodyStream.append_backward_paired edge (.single edge.argEnd bodyEnd) bodyFinish rfl
  have canonicalLabels : ExpandedLabelling g
      ((pre++edge.principal++loop++edge.reverseRoute)++[edge.argEnd]) a bodyEnd := by
    simpa only [List.append_assoc] using canonical.labelling g
  obtain ⟨actual,first,last⟩ := ExpandedLabelling.split_segment before
  have same : actual=bodyEnd := first.output_unique canonicalLabels
  subst actual
  have oldBefore : ExpandedLabelling g (pre++edge.argEnd::argPre) newInput seam := by
    apply (newPrefix.labelling g).splice preEnd last rfl
    simpa only [Pairing.involutive] using ExpandedTurn.ordinary (edge.app_arg_turn bodyEnd)
  have transition : BetaDetourBlocks g
      (g.wire (.inl ⟨edge.app,edge.appCtx⟩)::edge.argEnd::(argPre++argLoop)) bodyEnd output tailCount := by
    apply BetaDetourBlocks.ordinary ?_ tailStream
    simpa only [Pairing.involutive] using edge.app_arg_turn bodyEnd
  have oldWhole := newPrefix.append_at_last transition preEnd
  have oldBodyEval : current.sourceTrail selection.atomWord edge.principal edge.reverseRoute
      (argumentPos++(.body::z))=some ((pre++edge.argEnd::argPre)++argLoop) := by
    simpa only [List.append_assoc,List.cons_append] using argumentBodyEval
  have oldWhole' : BetaDetourBlocks g ((pre++edge.argEnd::argPre)++argLoop)
      newInput output (prefixCount+tailCount) := by
    simpa only [List.append_assoc,List.cons_append] using oldWhole
  exact typed argumentLambda argumentLeaf argumentEval oldBodyEval shape role argumentEnd oldWhole' oldBefore
end
end Lamping.AG
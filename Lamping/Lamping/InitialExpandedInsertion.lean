import Lamping.Lamping.ExpandedInsertionGeometry
import Lamping.Lamping.InitialOffsets
namespace Lamping.AG
open Graph Lambda

/-- In an actual initial encoding, the body loop extracted from the common
root assignment preserves its real binder shell. The independent grammar
BindingLoop witness is not used to supply this shell equality. -/
theorem encode_insert_actual_shell (t : Term) (level : Nat)
    (r : BetaEdge (encode level t).net) (pre loop suffix : List (Endpoint (encode level t).net))
    (cs : List Context) (trace : ExpandedContextTrace (encode level t).net (pre++r.argEnd::suffix) cs)
    (head : cs.head?=some input) (point : cs[pre.length]?=some seam)
    (preEnd : pre.getLast?=some ((encode level t).net.wire (.inl ⟨r.app,r.appCtx⟩)))
    (loopStart : loop.head?=some (.inl ⟨r.lam,r.lamBody⟩))
    (loopEnd : loop.getLast?=some ((encode level t).net.wire (.inl ⟨r.lam,r.lamBind⟩)))
    (forward : Forward (encode level t).net loop)
    (body : ExpandedLabelling (encode level t).net (pre++r.principal++loop) input output) :
    Context.SameShell r.index seam output := by
  have labels := r.common_root_loop_labeling pre loop suffix cs trace head point preEnd loopStart body
  let raw : InitialOffsets.RawLoop (encode level t).net loop seam output := {
    binder := r.lam
    isLam := congrArg Label.sort r.lamLabel
    body := r.lamBody
    bind := r.lamBind
    body_role := r.lamBody_role
    bind_role := r.lamBind_role
    start := loopStart
    finish := loopEnd
    proper := labels.ordinary_of_forward (encode level t).net forward }
  have shell := InitialOffsets.encode_rawLoop_shell t level loop seam output raw
  change Context.SameShell ((encode level t).net.label r.lam).index seam output at shell
  simpa only [r.lamLabel] using shell

/-- A genuine initial-graph insertion has an actual output assignment from
its two same-root labelled premises and its single argument independence IH.
There is no additional shell hypothesis and no use of an unrelated witness's
contexts. This is an insertion component, not the total generated theorem. -/
theorem encode_insert_labelable (t : Term) (level : Nat) {root : Boundary t}
    (r : BetaEdge (encode level t).net) (pre loop suffix : List (Endpoint (encode level t).net))
    (indep : ExpandedIndependenceOn (encode level t).net root (pre++r.argEnd::suffix))
    (cs : List Context) (trace : ExpandedContextTrace (encode level t).net (pre++r.argEnd::suffix) cs)
    (head : cs.head?=some input) (point : cs[pre.length]?=some seam) (lastCtx : cs.getLast?=some oldOutput)
    (preEnd : pre.getLast?=some ((encode level t).net.wire (.inl ⟨r.app,r.appCtx⟩)))
    (loopStart : loop.head?=some (.inl ⟨r.lam,r.lamBody⟩))
    (loopEnd : loop.getLast?=some ((encode level t).net.wire (.inl ⟨r.lam,r.lamBind⟩)))
    (forward : Forward (encode level t).net loop)
    (body : ExpandedLabelling (encode level t).net (pre++r.principal++loop) input endBody)
    (last : Endpoint (encode level t).net) (width : Nat)
    (finish : (pre++r.argEnd::suffix).getLast?=some last)
    (terminal : ExpandedTarget (encode level t).net root last width) :
    ∃ output,ExpandedLabelling (encode level t).net
      (pre++r.principal++loop++r.reverseRoute++[r.argEnd]++suffix) input output := by
  have shell := encode_insert_actual_shell t level r pre loop suffix cs trace head point preEnd loopStart loopEnd forward body
  exact r.insert_with_argument_independence pre loop suffix indep cs trace input seam endBody oldOutput
    body loopEnd point lastCtx last width finish terminal shell
end Lamping.AG

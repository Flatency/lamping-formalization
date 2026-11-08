import Lamping.Lamping.BetaResidualBars
import Lamping.Lamping.MatchingRouteSyntaxWalk
import Lamping.Lamping.ExpandedInvariantBase
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm} {beta : BetaEdge g}
/-- Actual endpoint occurrences of the literal route image. No endpoint
uniqueness is inferred from node names or equality of path labels. -/
theorem SourceRouteImage.endpoint_realizations {start stamp finish es}
    (image : SourceRouteImage original root beta start stamp finish es) :
    ∃ fromEndpoint toEndpoint,es.head?=some fromEndpoint ∧es.getLast?=some (g.wire toEndpoint) ∧
      SourcePortRealizes original g root start fromEndpoint ∧SourcePortRealizes original g root finish toEndpoint := by
  induction image with
  | atom fragment atomic => exact ⟨_,_,fragment.start,fragment.finish,fragment.fromRealizes,fragment.toRealizes⟩
  | over ports left right leftIH rightIH | under ports left right leftIH rightIH =>
    obtain ⟨first,_leftEnd,leftHead,_leftLast,fromReal,_leftReal⟩ := leftIH
    obtain ⟨_rightStart,last,_rightHead,rightLast,_rightReal,toReal⟩ := rightIH
    exact ⟨first,last,by simp only [List.head?_append,leftHead,Option.some_or],
      by simp only [List.getLast?_append,rightLast,Option.some_or],fromReal,toReal⟩
private theorem peel_tail {pre tail : List (Endpoint g)} {first : Endpoint g} {a seam b : Context}
    (head : tail.head?=some first) (canonical : ExpandedLabelling g (pre++[first]) a seam)
    (whole : ExpandedLabelling g (pre++tail) a b) : ExpandedLabelling g tail seam b := by
  obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp head
  rw [split] at whole ⊢
  obtain ⟨actual,before,after⟩ := whole.split_segment
  have same := before.output_unique canonical
  simpa only [same] using after
private theorem context_tail {left right : List (Endpoint g)} {a seam b : Context}
    (edge : BetaEdge g) (before : ExpandedLabelling g left a seam)
    (finish : left.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (head : right.head?=some (.inl ⟨edge.lam,edge.lamBody⟩))
    (whole : ExpandedLabelling g (left++edge.principal++right) a b) :
    ExpandedLabelling g right seam b := by
  have principal := before.splice finish (edge.principal_labeling seam).expanded edge.principalStart
    (by simpa only [Pairing.involutive] using ExpandedTurn.ordinary (edge.app_fun_turn seam))
  have last : (left++edge.principal).getLast?=some (g.wire edge.ctxEnd) := by
    simp only [List.getLast?_append,edge.principalEnd,Option.some_or]
    rfl
  have canonical := principal.splice last (.single (.inl ⟨edge.lam,edge.lamBody⟩) seam) rfl
    (by simpa only [Pairing.involutive] using ExpandedTurn.ordinary (edge.lam_body_turn seam))
  exact peel_tail head canonical whole
private theorem binding_tail {left right : List (Endpoint g)} {a seam b : Context}
    (edge : BetaEdge g) (before : ExpandedLabelling g left a seam)
    (finish : left.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)))
    (head : right.head?=some edge.argEnd)
    (whole : ExpandedLabelling g (left++edge.reverseRoute++right) a b) :
    ExpandedLabelling g right seam b := by
  have principal := before.splice finish (edge.reverse_labeling seam).expanded edge.reverse_start
    (by simpa only [Pairing.involutive] using ExpandedTurn.bindToCtx (g:=g) edge seam)
  have last : (left++edge.reverseRoute).getLast?=some (g.wire edge.funEnd) := by
    simp only [List.getLast?_append,edge.reverse_finish,Option.some_or]
  have canonical := principal.splice last (.single edge.argEnd seam) rfl
    (by simpa only [Pairing.involutive] using ExpandedTurn.funToArg (g:=g) edge seam)
  exact peel_tail head canonical whole
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
/-- Contract a REAL source-route image from an actual outside departure.
Atoms retain their actual ordinary fragment; bars contract THIS beta's full
ordered principal or reverse. Whole source labels determine the assignments
on both recursive pieces; no target shape, target path or coverage is input. -/
theorem SourceRouteImage.beta_contract {root : B} {original : LTerm}
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge) {start stamp finish es}
    (image : SourceRouteImage original root edge start stamp finish es)
    {a b : Context} (labels : ExpandedLabelling site.net es a b)
    (first : Endpoint cut) (head : es.head?=some (site.outsideEnd first)) :
    ∃ raw,BetaPathResidual site edge raw es ∧PlugLabelling cut (Schema.beta i).right.net raw a b := by
  induction image generalizing a b first with
  | atom fragment atomic =>
    have ordinary := labels.ordinary_of_forward site.net fragment.forward
    obtain ⟨target,residual,actual,_first,_last⟩ := site.beta_atomic_contraction edge ordinary fragment.forward fragment.emptyWord first head
    exact ⟨_,residual,actual.plug_decomposition _ _⟩
  | @over appId lamId start leftStamp xs rightStamp finish ys ports left right leftIH rightIH =>
    obtain ⟨leftStart,leftEnd,leftHead,leftLast,leftFrom,leftTo⟩ := left.endpoint_realizations
    obtain ⟨rightStart,rightEnd,rightHead,rightLast,rightFrom,rightTo⟩ := right.endpoint_realizations
    have nonempty : xs≠[] := by intro empty; rw [empty] at leftHead; cases leftHead
    have prefixWhole : ExpandedLabelling site.net (xs++(edge.principal++ys)) a b := by
      simpa only [List.append_assoc] using labels
    obtain ⟨seam,before⟩ := prefixWhole.prefix nonempty
    have startEq : xs.head?=some (site.outsideEnd first) := by
      simpa only [List.head?_append,leftHead,Option.some_or] using head
    obtain ⟨leftRaw,leftResidual,leftLabels⟩ := leftIH before first startEq
    have appEndpoint := leftTo.unique initial matching ports.appContext
    have finish : xs.getLast?=some (site.net.wire (.inl ⟨edge.app,edge.appCtx⟩)) :=
      leftLast.trans (congrArg (fun e => some (site.net.wire e)) appEndpoint)
    have bodyEndpoint := rightFrom.unique initial matching ports.lamBody
    have bodyHead := rightHead.trans (congrArg some bodyEndpoint)
    have after := context_tail edge before finish bodyHead labels
    have outsideHead : ys.head?=some (site.outsideEnd (.inr (.inl (.inr (.inr true))))) := by
      exact bodyHead.trans (congrArg some (by rw [geometry.body]; rfl))
    obtain ⟨rightRaw,rightResidual,rightLabels⟩ := rightIH after _ outsideHead
    exact leftResidual.context_splice site geometry rightResidual leftLabels rightLabels finish bodyHead
  | @under appId lamId start leftStamp xs rightStamp finish ys ports left right leftIH rightIH =>
    obtain ⟨leftStart,leftEnd,leftHead,leftLast,leftFrom,leftTo⟩ := left.endpoint_realizations
    obtain ⟨rightStart,rightEnd,rightHead,rightLast,rightFrom,rightTo⟩ := right.endpoint_realizations
    have nonempty : xs≠[] := by intro empty; rw [empty] at leftHead; cases leftHead
    have prefixWhole : ExpandedLabelling site.net (xs++(edge.reverseRoute++ys)) a b := by
      simpa only [List.append_assoc] using labels
    obtain ⟨seam,before⟩ := prefixWhole.prefix nonempty
    have startEq : xs.head?=some (site.outsideEnd first) := by
      simpa only [List.head?_append,leftHead,Option.some_or] using head
    obtain ⟨leftRaw,leftResidual,leftLabels⟩ := leftIH before first startEq
    have bindingEndpoint := leftTo.unique initial matching ports.lamBinding
    have finish : xs.getLast?=some (site.net.wire (.inl ⟨edge.lam,edge.lamBind⟩)) :=
      leftLast.trans (congrArg (fun e => some (site.net.wire e)) bindingEndpoint)
    have argumentEndpoint := rightFrom.unique initial matching ports.appArgument
    have argumentHead := rightHead.trans (congrArg some argumentEndpoint)
    have after := binding_tail edge before finish argumentHead labels
    have outsideHead : ys.head?=some (site.outsideEnd (.inr (.inl (.inr (.inl true))))) := by
      exact argumentHead.trans (congrArg some (by rw [geometry.argument]; rfl))
    obtain ⟨rightRaw,rightResidual,rightLabels⟩ := rightIH after _ outsideHead
    exact leftResidual.binding_splice site geometry rightResidual leftLabels rightLabels finish argumentHead
end
end Lamping.AG
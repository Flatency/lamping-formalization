import Lamping.Lamping.BetaResidualBars
import Lamping.Lamping.BetaAtomicWords
import Lamping.Lamping.MatchingSourceRouteContraction
import Lamping.Lamping.InitialAccessWords
import Lamping.Lamping.MatchingRouteSyntaxWalk
import Lamping.Lamping.ExpandedInvariantBase
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm} {beta : BetaEdge g}
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
private theorem raw_head {edge : BetaEdge site.net} {raw old} (relation : BetaPathResidual site edge raw old) :
    ∃ first : Endpoint cut,raw.head?=some (.inl first) := by cases relation <;> exact ⟨_,rfl⟩
private theorem reflect_head {edge : BetaEdge site.net} {raw old} (relation : BetaPathResidual site edge raw old)
    (first : Endpoint cut) (head : old.head?=some (site.outsideEnd first)) : raw.head?=some (.inl first) := by
  obtain ⟨actual,rawHead⟩ := raw_head site relation
  have same := site.outsideEnd_injective (Option.some.inj ((relation.head site rawHead).symm.trans head))
  simpa only [same] using rawHead
private theorem bar_empty_word
    (left right : List (PlugSegment cut (Schema.beta i).right.net)) (frontier exit : Bool⊕Bool)
    (nonempty : left≠[])
    (rightHead : right.head?=some (.inl (.inr (.inl (.inr exit)))))
    (leftEmpty : accessWord site.reduce (left.map (plugEnd _ _))=[])
    (rightEmpty : accessWord site.reduce (right.map (plugEnd _ _))=[]) :
    accessWord site.reduce ((left++(.inr (.inr (.inl frontier)))::right).map (plugEnd _ _))=[] := by
  have rightTokens : (right.map (plugEnd _ _)).flatMap (arrivalWord site.reduce)=[] := by
    obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp rightHead
    rw [split] at rightEmpty ⊢
    change []++(tail.map (plugEnd _ _)).flatMap (arrivalWord site.reduce)=[]
    exact rightEmpty
  have mappedNonempty : left.map (plugEnd _ _)≠[] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  rw [List.map_append,accessWord_append site.reduce _ _ mappedNonempty,leftEmpty]
  change []++([]++(right.map (plugEnd _ _)).flatMap (arrivalWord site.reduce))=[]
  rw [rightTokens]
  rfl
/-- Contract a REAL source-route image from an actual outside departure.
Atoms retain their actual ordinary fragment; bars contract THIS beta's full
ordered principal or reverse. Whole source labels determine the assignments
on both recursive pieces; no target shape, target path or coverage is input. -/
theorem SourceRouteImage.beta_contract_word {root : B} {original : LTerm}
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge) {start stamp finish es}
    (image : SourceRouteImage original root edge start stamp finish es)
    {a b : Context} (labels : ExpandedLabelling site.net es a b)
    (first : Endpoint cut) (head : es.head?=some (site.outsideEnd first)) :
    ∃ raw,BetaPathResidual site edge raw es ∧PlugLabelling cut (Schema.beta i).right.net raw a b ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=[] := by
  induction image generalizing a b first with
  | atom fragment atomic =>
    have ordinary := labels.ordinary_of_forward site.net fragment.forward
    exact site.beta_atomic_word_contraction edge ordinary fragment.forward fragment.emptyWord first head
  | @over appId lamId start leftStamp xs rightStamp finish ys ports left right leftIH rightIH =>
    obtain ⟨leftStart,leftEnd,leftHead,leftLast,leftFrom,leftTo⟩ := left.endpoint_realizations
    obtain ⟨rightStart,rightEnd,rightHead,rightLast,rightFrom,rightTo⟩ := right.endpoint_realizations
    have nonempty : xs≠[] := by intro empty; rw [empty] at leftHead; cases leftHead
    have prefixWhole : ExpandedLabelling site.net (xs++(edge.principal++ys)) a b := by
      simpa only [List.append_assoc] using labels
    obtain ⟨seam,before⟩ := prefixWhole.prefix nonempty
    have startEq : xs.head?=some (site.outsideEnd first) := by
      simpa only [List.head?_append,leftHead,Option.some_or] using head
    obtain ⟨leftRaw,leftResidual,leftLabels,leftWord⟩ := leftIH before first startEq
    have appEndpoint := leftTo.unique initial matching ports.appContext
    have finish : xs.getLast?=some (site.net.wire (.inl ⟨edge.app,edge.appCtx⟩)) :=
      leftLast.trans (congrArg (fun e => some (site.net.wire e)) appEndpoint)
    have bodyEndpoint := rightFrom.unique initial matching ports.lamBody
    have bodyHead := rightHead.trans (congrArg some bodyEndpoint)
    have after := context_tail edge before finish bodyHead labels
    have outsideHead : ys.head?=some (site.outsideEnd (.inr (.inl (.inr (.inr true))))) := by
      exact bodyHead.trans (congrArg some (by rw [geometry.body]; rfl))
    obtain ⟨rightRaw,rightResidual,rightLabels,rightWord⟩ := rightIH after _ outsideHead
    have rightRawHead := reflect_head site rightResidual _ outsideHead
    have leftNonempty : leftRaw≠[] := by intro empty; rw [empty] at leftLabels; cases leftLabels
    obtain ⟨relation,actual⟩ := leftResidual.context_splice_canonical site geometry rightResidual leftLabels rightLabels finish bodyHead
    exact ⟨_,relation,actual,bar_empty_word site leftRaw rightRaw (.inl false) (.inr true) leftNonempty rightRawHead leftWord rightWord⟩
  | @under appId lamId start leftStamp xs rightStamp finish ys ports left right leftIH rightIH =>
    obtain ⟨leftStart,leftEnd,leftHead,leftLast,leftFrom,leftTo⟩ := left.endpoint_realizations
    obtain ⟨rightStart,rightEnd,rightHead,rightLast,rightFrom,rightTo⟩ := right.endpoint_realizations
    have nonempty : xs≠[] := by intro empty; rw [empty] at leftHead; cases leftHead
    have prefixWhole : ExpandedLabelling site.net (xs++(edge.reverseRoute++ys)) a b := by
      simpa only [List.append_assoc] using labels
    obtain ⟨seam,before⟩ := prefixWhole.prefix nonempty
    have startEq : xs.head?=some (site.outsideEnd first) := by
      simpa only [List.head?_append,leftHead,Option.some_or] using head
    obtain ⟨leftRaw,leftResidual,leftLabels,leftWord⟩ := leftIH before first startEq
    have bindingEndpoint := leftTo.unique initial matching ports.lamBinding
    have finish : xs.getLast?=some (site.net.wire (.inl ⟨edge.lam,edge.lamBind⟩)) :=
      leftLast.trans (congrArg (fun e => some (site.net.wire e)) bindingEndpoint)
    have argumentEndpoint := rightFrom.unique initial matching ports.appArgument
    have argumentHead := rightHead.trans (congrArg some argumentEndpoint)
    have after := binding_tail edge before finish argumentHead labels
    have outsideHead : ys.head?=some (site.outsideEnd (.inr (.inl (.inr (.inl true))))) := by
      exact argumentHead.trans (congrArg some (by rw [geometry.argument]; rfl))
    obtain ⟨rightRaw,rightResidual,rightLabels,rightWord⟩ := rightIH after _ outsideHead
    have rightRawHead := reflect_head site rightResidual _ outsideHead
    have leftNonempty : leftRaw≠[] := by intro empty; rw [empty] at leftLabels; cases leftLabels
    obtain ⟨relation,actual⟩ := leftResidual.binding_splice_canonical site geometry rightResidual leftLabels rightLabels finish argumentHead
    exact ⟨_,relation,actual,bar_empty_word site leftRaw rightRaw (.inr false) (.inl true) leftNonempty rightRawHead leftWord rightWord⟩
end
end Lamping.AG
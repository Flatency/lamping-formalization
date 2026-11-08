import Lamping.Lamping.BetaResidualChildTurns
import Lamping.Lamping.CompleteSyntaxChildPorts

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm} {beta : BetaEdge g}

/-- Endpoint occurrences of the actual finite syntax image. -/
theorem SyntaxTrailImage.endpoint_realizations
    (image : SyntaxTrailImage original root beta env ctx target p sub finish es) :
    ∃ first last,es.head?=some first ∧es.getLast?=some (g.wire last) ∧
      SourcePortRealizes original g root ctx first ∧SourcePortRealizes original g root finish last := by
  induction image with
  | var route | lam route | app route => exact route.endpoint_realizations
  | fn route child ih | arg route child ih | body route child ih =>
    obtain ⟨first,_leftEnd,leftHead,_leftLast,fromReal,_leftReal⟩ := route.endpoint_realizations
    obtain ⟨_rightStart,last,_rightHead,rightLast,_rightReal,toReal⟩ := ih
    exact ⟨first,last,by simp only [List.head?_append,leftHead,Option.some_or],
      by simp only [List.getLast?_append,rightLast,Option.some_or],fromReal,toReal⟩

private theorem child_rule {kind : Kind} {ctx out : Port kind} {s : Step}
    (roles : SyntaxChildPorts kind ctx out s) (level : Nat) (a : Context) : Traversal level kind ctx out a a := by
  cases roles
  · exact .direct (.appFun a)
  · exact .direct (.appArg a)
  · exact .direct (.lamBody a)
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
variable {root : B} {original target : LTerm} {ps : List Path} {marked : Marked}

private theorem child_contract
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (history : History ps original target)
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {current : LTerm} {fromPort toPort s start xs ys word base stamp}
    (shape : CurrentSyntaxChild current fromPort toPort s)
    (currentStamp : current.label=stamp) (lookup : target.subterm base=some current)
    (header : SourceRouteImage original root edge start stamp fromPort xs)
    {rightStart : Endpoint site.net} (rightHead : ys.head?=some rightStart)
    (rightFrom : SourcePortRealizes original site.net root toPort rightStart)
    (recursive : ∀ {a b : Context} (_labels : ExpandedLabelling site.net ys a b)
      (first : Endpoint cut),ys.head?=some (site.outsideEnd first) →
      ∃ raw,BetaPathResidual site edge raw ys ∧PlugLabelling cut (Schema.beta i).right.net raw a b ∧
        accessWord site.reduce (raw.map (plugEnd _ _))=word)
    {a b : Context} (labels : ExpandedLabelling site.net (xs++ys) a b)
    (first : Endpoint cut) (head : (xs++ys).head?=some (site.outsideEnd first)) :
    ∃ raw,BetaPathResidual site edge raw (xs++ys) ∧PlugLabelling cut (Schema.beta i).right.net raw a b ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=s::word := by
  obtain ⟨leftStart,leftEnd,leftHead,leftLast,leftFrom,leftTo⟩ := header.endpoint_realizations
  have header' : SourceRouteImage original root edge start current.label fromPort xs := by rw [currentStamp]; exact header
  obtain ⟨node,ctx,out,roles,leftEndpoint,rightEndpoint⟩ := shape.complete_kept_ports site initial matching flow positive
    relative normal history lookup header' leftTo rightFrom
  have nonempty : xs≠[] := by intro empty; rw [empty] at leftHead; cases leftHead
  obtain ⟨seam,before⟩ := labels.prefix nonempty
  have startEq : xs.head?=some (site.outsideEnd first) := by
    simpa only [List.head?_append,leftHead,Option.some_or] using head
  have finish : xs.getLast?=some (site.net.wire (.inl ⟨.inl node,ctx⟩)) :=
    leftLast.trans (congrArg (fun e => some (site.net.wire e)) leftEndpoint)
  have childHead : ys.head?=some (.inl ⟨.inl node,out⟩) := rightHead.trans (congrArg some rightEndpoint)
  have canonical : ExpandedLabelling site.net (xs++[.inl ⟨.inl node,out⟩]) a seam := before.splice finish (ExpandedLabelling.single (g:=site.net) (.inl ⟨.inl node,out⟩) seam) rfl (by
    simpa only [Pairing.involutive] using ExpandedTurn.ordinary
      (LabelledTurn.node (g:=site.net) (.inl node) ctx out (child_rule roles (kept node).index seam)))
  obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp childHead
  have whole' := labels
  rw [split] at whole'
  obtain ⟨actual,beforeActual,after⟩ := whole'.split_segment
  have same := beforeActual.output_unique canonical
  have after' : ExpandedLabelling site.net ys seam b := by rw [split]; simpa only [same] using after
  obtain ⟨leftRaw,leftResidual,leftLabels,leftWord⟩ := header.beta_contract_word site initial matching geometry before first startEq
  obtain ⟨rightRaw,rightResidual,rightLabels,rightWord⟩ := recursive after' (.inl ⟨node,out⟩) childHead
  obtain ⟨residual,actualLabels,actualWord⟩ := leftResidual.kept_child_splice site rightResidual leftLabels rightLabels
    node ctx out s roles finish childHead leftWord word rightWord
  exact ⟨_,residual,actualLabels,actualWord⟩

/-- Contract the literal syntax trail of an actual complete development.
Every child turn is proved to occur at a retained node from actual source
provenance and completion. The source assignment constructs the new path,
its residual and its syntax word together. -/
theorem SyntaxTrailImage.beta_contract_word
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (history : History ps original target)
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {env start current p sub finish es}
    (image : SyntaxTrailImage original root edge env start current p sub finish es)
    (base : Path) (lookup : target.subterm base=some current)
    {a b : Context} (labels : ExpandedLabelling site.net es a b)
    (first : Endpoint cut) (head : es.head?=some (site.outsideEnd first)) :
    ∃ raw,BetaPathResidual site edge raw es ∧PlugLabelling cut (Schema.beta i).right.net raw a b ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=p := by
  induction image generalizing base a b first with
  | var route | lam route | app route => exact route.beta_contract_word site initial matching geometry labels first head
  | fn route child ih =>
    obtain ⟨rightStart,_rightEnd,rightHead,_rightLast,rightFrom,_rightTo⟩ := child.endpoint_realizations
    apply child_contract site initial matching flow positive relative normal history geometry .function rfl lookup route rightHead rightFrom
      (fun nextLabels nextFirst nextHead => ih (base++[.fn]) (by rw [LTerm.subterm_append,lookup]; simp [LTerm.subterm]) nextLabels nextFirst nextHead) labels first head
  | arg route child ih =>
    obtain ⟨rightStart,_rightEnd,rightHead,_rightLast,rightFrom,_rightTo⟩ := child.endpoint_realizations
    apply child_contract site initial matching flow positive relative normal history geometry .argument rfl lookup route rightHead rightFrom
      (fun nextLabels nextFirst nextHead => ih (base++[.arg]) (by rw [LTerm.subterm_append,lookup]; simp [LTerm.subterm]) nextLabels nextFirst nextHead) labels first head
  | body route child ih =>
    obtain ⟨rightStart,_rightEnd,rightHead,_rightLast,rightFrom,_rightTo⟩ := child.endpoint_realizations
    apply child_contract site initial matching flow positive relative normal history geometry .body rfl lookup route rightHead rightFrom
      (fun nextLabels nextFirst nextHead => ih (base++[.body]) (by rw [LTerm.subterm_append,lookup]; simp [LTerm.subterm]) nextLabels nextFirst nextHead) labels first head
end
end Lamping.AG

import Lamping.Lamping.BetaAtomicWords
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed

private theorem member_empty_token {A : Type} (token : A → List Step)
    {xs : List A} (empty : xs.flatMap token=[]) {x : A} (member : x∈xs) : token x=[] := by
  induction xs with
  | nil => cases member
  | cons y ys ih =>
    obtain ⟨head,tail⟩ := List.append_eq_nil_iff.mp empty
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih tail member

private theorem map_injective {A C : Type} {f : A → C} (injective : Function.Injective f)
    {xs ys : List A} (same : xs.map f=ys.map f) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => cases same
  | cons x xs ih => cases ys with
    | nil => cases same
    | cons y ys =>
      obtain ⟨head,tail⟩ := List.cons.inj same
      rw [injective head,ih tail]

/-- An empty old syntax word excludes both real beta reconnection blocks.
The first outside departure is skipped, but neither block's fn/arg token is.
No labelling, forwardness, source INIT or target syntax oracle is needed. -/
theorem BetaPathResidual.atomic_exterior {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) {raw old}
    (relation : BetaPathResidual site edge raw old)
    (emptyWord : accessWord site.net old=[]) :
    ∃ exterior : List (Endpoint cut),raw=exterior.map Sum.inl ∧old=exterior.map site.outsideEnd := by
  induction relation with
  | single e => exact ⟨[e],rfl,rfl⟩
  | @outside e f tail oldTail rest ih =>
    have noTokens : oldTail.flatMap (arrivalWord site.net)=[] := emptyWord
    have tailEmpty : accessWord site.net oldTail=[] := by
      cases oldTail with
      | nil => rfl
      | cons x xs => exact (List.append_eq_nil_iff.mp noTokens).2
    obtain ⟨exterior,rawEq,oldEq⟩ := ih tailEmpty
    exact ⟨e::exterior,by simp only [List.map_cons,←rawEq],by simp only [List.map_cons,←oldEq]⟩
  | @context e tail oldTail arrival rest ih =>
    have noTokens : (edge.principal++oldTail).flatMap (arrivalWord site.net)=[] := emptyWord
    have head : edge.principal.head?=some (.inl ⟨.inr (.inl ()),.inl ()⟩) :=
      (geometry.principal_presentation site).first
    obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp head
    have member : (.inl ⟨.inr (.inl ()),.inl ()⟩ : Endpoint site.net)∈edge.principal := by rw [split]; simp
    have token := member_empty_token (arrivalWord site.net) noTokens (List.mem_append_left _ member)
    change [Step.fn]=[] at token
    cases token
  | @binding e tail oldTail arrival rest ih =>
    have noTokens : (edge.reverseRoute++oldTail).flatMap (arrivalWord site.net)=[] := emptyWord
    have head := rest.head site rfl
    obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp head
    have member : site.outsideEnd (.inr (.inl (.inr (.inl true))))∈oldTail := by rw [split]; simp
    have token := member_empty_token (arrivalWord site.net) noTokens (List.mem_append_right _ member)
    change [Step.arg]=[] at token
    cases token

/-- Compare the supplied literal residuals, without identifying them with
any occurrence selector or silently assuming a parent-path cut. -/
theorem BetaPathResidual.atomic_equality_iff {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) {left right oldLeft oldRight}
    (first : BetaPathResidual site edge left oldLeft)
    (second : BetaPathResidual site edge right oldRight)
    (leftWord : accessWord site.net oldLeft=[])
    (rightWord : accessWord site.net oldRight=[]) : left=right ↔ oldLeft=oldRight := by
  obtain ⟨l,rfl,rfl⟩ := first.atomic_exterior site geometry leftWord
  obtain ⟨r,rfl,rfl⟩ := second.atomic_exterior site geometry rightWord
  constructor
  · intro same
    have equal : l=r := map_injective (fun _ _ same=>Sum.inl.inj same) same
    rw [equal]
  · intro same
    have equal : l=r := map_injective (site.outsideEnd_injective) same
    rw [equal]

/-- Actual target endpoint equality reflects and preserves old-piece
equality for atomic residuals of this SAME physical beta. -/
theorem BetaPathResidual.atomic_plugged_equality_iff {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) {left right oldLeft oldRight}
    (first : BetaPathResidual site edge left oldLeft)
    (second : BetaPathResidual site edge right oldRight)
    (leftWord : accessWord site.net oldLeft=[])
    (rightWord : accessWord site.net oldRight=[]) :
    left.map (plugEnd (cut).label (Schema.beta i).right.net.label)=
      right.map (plugEnd (cut).label (Schema.beta i).right.net.label) ↔ oldLeft=oldRight := by
  rw [←first.atomic_equality_iff site geometry second leftWord rightWord]
  constructor
  · intro same
    exact map_injective (fun x y same=>by
      have actual := congrArg (plugEnd (cut).label (Schema.beta i).right.net.label).invFun same
      simpa only [(plugEnd (cut).label (Schema.beta i).right.net.label).left_inv] using actual) same
  · exact congrArg (List.map (plugEnd (cut).label (Schema.beta i).right.net.label))

/-- Two actual source occurrence fragments supply their own empty-word
proofs. Their given literal target residuals can then be compared. Constructing
those residuals at specified target selector cuts is a separate obligation. -/
theorem SourceEdgeFragment.beta_atomic_equality_iff
    {root : B} {source : Lambda.Labelled.LTerm}
    {leftEdge rightEdge : Lambda.Labelled.SourceEdge} {p q : Path}
    (left : SourceEdgeFragment source site.net root leftEdge p)
    (right : SourceEdgeFragment source site.net root rightEdge q)
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {targetLeft targetRight : List (Endpoint site.reduce)}
    (leftResidual : BetaPathResidual site edge
      (targetLeft.map (plugEnd (cut).label (Schema.beta i).right.net.label).invFun) left.segments)
    (rightResidual : BetaPathResidual site edge
      (targetRight.map (plugEnd (cut).label (Schema.beta i).right.net.label).invFun) right.segments) :
    targetLeft=targetRight ↔left.segments=right.segments := by
  have comparison := leftResidual.atomic_plugged_equality_iff site geometry rightResidual
    left.emptyWord right.emptyWord
  simpa only [List.map_map,Function.comp_def,
    (plugEnd (cut).label (Schema.beta i).right.net.label).right_inv,List.map_id_fun'] using comparison
end
end Lamping.AG

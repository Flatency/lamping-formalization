import Lamping.Lamping.BetaAtomicContraction
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
private theorem no_new_token (e : Endpoint cut)
    (empty : arrivalWord site.net (site.outsideEnd e)=[]) :
    arrivalWord site.reduce (AG.plugLeft cut (Schema.beta i).right.net e)=[] := by
  rcases e with ⟨node,p⟩ | ((boundary|frontier)|⟨vertex,direction⟩)
  · exact empty
  · rfl
  · rfl
  · rfl
/-- Removing the selected proper nodes cannot introduce a syntax token on
an atomic exterior piece. Kept ports are unchanged; frontier ports become
transparent glue vertices. The first departure is skipped on both sides. -/
theorem PathSite.beta_exterior_empty_word (exterior : List (Endpoint cut))
    (empty : accessWord site.net (exterior.map site.outsideEnd)=[]) :
    accessWord site.reduce (exterior.map (AG.plugLeft cut (Schema.beta i).right.net))=[] := by
  cases exterior with
  | nil => rfl
  | cons first tail =>
    change (tail.map site.outsideEnd).flatMap (arrivalWord site.net)=[] at empty
    change (tail.map (AG.plugLeft cut (Schema.beta i).right.net)).flatMap (arrivalWord site.reduce)=[]
    induction tail with
    | nil => rfl
    | cons e tail ih =>
      have pieces := List.append_eq_nil_iff.mp empty
      change arrivalWord site.reduce (AG.plugLeft cut (Schema.beta i).right.net e)++
        (tail.map (AG.plugLeft cut (Schema.beta i).right.net)).flatMap (arrivalWord site.reduce)=[]
      rw [no_new_token site e pieces.1,ih pieces.2]
      rfl
private theorem exterior_residual (edge : BetaEdge site.net)
    {es : List (Endpoint cut)} {a b : Context} (labels : Labelling cut es a b) :
    BetaPathResidual site edge (es.map (fun e => Sum.inl e)) (es.map site.outsideEnd) := by
  induction labels with
  | single e a => exact .single e
  | cons turn rest ih => exact .outside ih
private theorem plug_left_labels {es : List (Endpoint cut)} {a b : Context}
    (labels : Labelling cut es a b) :
    PlugLabelling cut (Schema.beta i).right.net (es.map (fun e => Sum.inl e)) a b := by
  induction labels with
  | single e a => exact .single _ _
  | cons turn rest ih => exact .cons (.left turn) ih
/-- The atomic contraction supplies its actual raw residual and labels
TOGETHER with the empty target word. No word equality is a caller field. -/
theorem PathSite.beta_atomic_word_contraction (edge : BetaEdge site.net)
    {old : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net old a b) (forward : Forward site.net old)
    (emptyWord : accessWord site.net old=[])
    (first : Endpoint cut) (head : old.head?=some (site.outsideEnd first)) :
    ∃ raw,BetaPathResidual site edge raw old ∧PlugLabelling cut (Schema.beta i).right.net raw a b ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=[] := by
  obtain ⟨exterior,literal,cutLabels⟩ := site.beta_empty_word_exterior labels forward emptyWord first head
  have relation := exterior_residual site edge cutLabels
  have actualWord := site.beta_exterior_empty_word exterior (by simpa only [literal] using emptyWord)
  refine ⟨exterior.map (fun e => Sum.inl e),by simpa only [literal] using relation,plug_left_labels site cutLabels,?_⟩
  simpa only [List.map_map] using actualWord
end
end Lamping.AG
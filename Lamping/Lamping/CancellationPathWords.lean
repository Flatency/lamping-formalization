import Lamping.Lamping.CancellationUnobservedContraction
import Lamping.Lamping.UnobservedResidualWords
namespace Lamping.AG
open Graph Lambda
section
variable {K B F W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames F] [FiniteNames W]
variable (c : Net signature K (B⊕F) W) (r : Net signature Empty F Empty)

private theorem plug_wire_emission (segment : PlugSegment c r) :
    arrivalWord (plug c r) ((plugEnd c.label r.label) segment)=
      Sum.elim (arrivalWord c) (fun _ => []) segment := by
  rcases segment with (⟨node,p⟩ | ((boundary | frontier) | ⟨vertex,direction⟩)) |
    (⟨node,p⟩ | (frontier | ⟨vertex,direction⟩))
  · rfl
  · rfl
  · rfl
  · rfl
  · exact Empty.elim node
  · rfl
  · exact Empty.elim vertex
end

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

private theorem outside_emission (cancel : IsCancellation s)
    (e : Endpoint (cutFragment site.net (pathPartition s V) site.closed)) :
    arrivalWord site.net (site.outsideEnd e)=
      arrivalWord (cutFragment site.net (pathPartition s V) site.closed) e := by
  rcases e with ⟨node,p⟩ | ((boundary | frontier) | ⟨vertex,direction⟩)
  · rfl
  · rfl
  · cases cancel <;> cases frontier <;> rfl
  · rfl

/-- The strong actual residual preserves the word of the physical target
path. RHS glue vertices and retained outside departures are checked here,
separately from the earlier raw/source comparison. -/
theorem CancellationUnobservedResidual.access_word (cancel : IsCancellation s)
    {es old} (relation : CancellationUnobservedResidual site es old)
    (forward : Forward site.net old) : accessWord site.reduce es=accessWord site.net old := by
  let c := cutFragment site.net (pathPartition s V) site.closed
  let r := s.right.net
  cases cancel
  all_goals
    let raw := es.map (plugEnd c.label r.label).invFun
    change UnobservedWireResidual c r site.net site.outsideEnd raw old at relation
    have sourceWord := relation.access_word c r site.net site.outsideEnd
      (by intro f; cases f <;> rfl) forward
    have emission (segment : PlugSegment c r) :
        arrivalWord site.reduce ((plugEnd c.label r.label) segment)=
          outsideEmission c r site.net site.outsideEnd segment := by
      change arrivalWord (plug c r) ((plugEnd c.label r.label) segment)=
        outsideEmission c r site.net site.outsideEnd segment
      rw [plug_wire_emission c r segment]
      cases segment with
      | inl e => exact (outside_emission site (by constructor) e).symm
      | inr e => rfl
    have wordActual : accessWord site.reduce (raw.map (plugEnd c.label r.label))=
        outsideAccessWord c r site.net site.outsideEnd raw := by
      cases raw with
      | nil => rfl
      | cons e tail =>
        change (tail.map (plugEnd c.label r.label)).flatMap (arrivalWord site.reduce)=
          tail.flatMap (outsideEmission c r site.net site.outsideEnd)
        induction tail with
        | nil => rfl
        | cons x tail ih =>
          simp only [List.map_cons,List.flatMap_cons]
          rw [emission,ih]
    have same : raw.map (plugEnd c.label r.label)=es := plug_decomposition_flatten c r es
    rw [same] at wordActual
    exact wordActual.trans sourceWord

/-- Actual cancellation contraction preserves contexts, retained endpoints,
and the full syntax word on every supplied forward proper-ended old path. -/
theorem PathSite.cancellation_source_word_contraction (cancel : IsCancellation s)
    {old : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net old a b) (forward : Forward site.net old)
    (typed : ∃ k,accessKind site.net old=some k)
    (first last : Endpoint (cutFragment site.net (pathPartition s V) site.closed))
    (head : old.head?=some (site.outsideEnd first))
    (finish : old.getLast?=some (site.outsideEnd last)) :
    ∃ es,Labelling site.reduce es a b ∧CancellationUnobservedResidual site es old ∧
      es.head?=some (AG.plugLeft _ s.right.net first) ∧
      es.getLast?=some (AG.plugLeft _ s.right.net last) ∧
      accessWord site.reduce es=accessWord site.net old := by
  obtain ⟨es,path,residual,start,lastEq⟩ :=
    site.cancellation_unobserved_source_contraction cancel labels typed first last head finish
  exact ⟨es,path,residual,start,lastEq,residual.access_word site cancel forward⟩
end
end Lamping.AG

import Lamping.Lamping.BetaAtomicComparison
import Lamping.Lamping.Fixtures
namespace Lamping.Checks.BetaAtomicComparison
open AG Graph Lambda
private abbrev site := actualBetaSite
private abbrev fragmentCut := cutFragment site.net (pathPartition (Schema.beta 0) Unit) site.closed
private abbrev right := (Schema.beta 0).right.net
private def first : Endpoint fragmentCut := .inr (.inl (.inr (.inl true)))
private def last : Endpoint fragmentCut := .inr (.inr (.inr (),true))
private def exterior : List (Endpoint fragmentCut) := [first,last]
private def raw : List (PlugSegment fragmentCut right) := exterior.map Sum.inl
private def old : List (Endpoint site.net) := exterior.map site.outsideEnd
private theorem oldLabels (a : Context) : Labelling site.net old a a :=
  .cons (LabelledTurn.transparent (g:=site.net) (.inl (.inr ())) false a) (.single _ _)
private theorem newLabels (a : Context) :
    Labelling site.reduce (raw.map (plugEnd fragmentCut.label right.label)) a a :=
  .cons (LabelledTurn.transparent (g:=site.reduce) (.inl (.inl (.inr ()))) false a) (.single _ _)
private theorem relation (edge : BetaEdge site.net) : BetaPathResidual site edge raw old :=
  .outside (.single last)

/-- A real encoded I I argument fragment has a transparent subdivision.
Its residual is compared to a distinct singleton endpoint, with actual
source/target assignments at arbitrary contexts. -/
theorem actual_subdivided_comparison (a : Context) :
    ∃ edge : BetaEdge site.net,SiteBetaGeometry site edge ∧
      Labelling site.net old a a ∧
      Labelling site.reduce (raw.map (plugEnd fragmentCut.label right.label)) a a ∧
      BetaPathResidual site edge raw old ∧
      (raw.map (plugEnd fragmentCut.label right.label)≠
        [plugEnd fragmentCut.label right.label (Sum.inl last)]) := by
  obtain ⟨edge,geometry⟩ := site.siteBetaGeometry_exists
  have compare := (relation edge).atomic_plugged_equality_iff site geometry
    (BetaPathResidual.single last) (by rfl) (by rfl)
  refine ⟨edge,geometry,oldLabels a,newLabels a,relation edge,?_⟩
  intro same
  have equality := compare.mp same
  have impossible := congrArg List.length equality
  change 2=1 at impossible
  cases impossible

/-- Two real witnesses for this same atomic fragment are forced to agree.
The second witness is arbitrary, rather than a preselected target list. -/
theorem actual_subdivided_target_unique (edge : BetaEdge site.net)
    (geometry : SiteBetaGeometry site edge) {other}
    (otherResidual : BetaPathResidual site edge other old) : other=raw :=
  ((otherResidual.atomic_equality_iff site geometry (relation edge) (by rfl) (by rfl))).mpr rfl

private def rootOutside : Endpoint fragmentCut := .inr (.inl (.inl (.inl ())))
private def bodyOutside : Endpoint fragmentCut := .inr (.inl (.inr (.inr true)))

/-- The actual root context-to-body beta reconnection is not atomic.
Its function token lies after the skipped first outside departure. -/
theorem actual_context_reconnection_not_atomic :
    ∃ edge : BetaEdge site.net,SiteBetaGeometry site edge ∧
      BetaPathResidual site edge
        [Sum.inl rootOutside,Sum.inr (.inr (.inl (.inl false))),Sum.inl bodyOutside]
        (site.outsideEnd rootOutside::(edge.principal++[site.outsideEnd bodyOutside])) ∧
      accessWord site.net (site.outsideEnd rootOutside::
        (edge.principal++[site.outsideEnd bodyOutside]))≠[] := by
  obtain ⟨edge,geometry⟩ := site.siteBetaGeometry_exists
  have residual : BetaPathResidual site edge
      [Sum.inl rootOutside,Sum.inr (.inr (.inl (.inl false))),Sum.inl bodyOutside]
      (site.outsideEnd rootOutside::(edge.principal++[site.outsideEnd bodyOutside])) :=
    .context rfl (.single bodyOutside)
  refine ⟨edge,geometry,residual,?_⟩
  intro empty
  obtain ⟨xs,equal,_⟩ := residual.atomic_exterior site geometry empty
  cases xs with
  | nil => cases equal
  | cons x xs =>
    cases xs with
    | nil => cases equal
    | cons y ys =>
      have tails := (List.cons.inj equal).2
      have heads := (List.cons.inj tails).1
      cases heads

#print axioms BetaPathResidual.atomic_exterior
#print axioms BetaPathResidual.atomic_equality_iff
#print axioms BetaPathResidual.atomic_plugged_equality_iff
#print axioms SourceEdgeFragment.beta_atomic_equality_iff
#print axioms actual_subdivided_comparison
#print axioms actual_subdivided_target_unique
#print axioms actual_context_reconnection_not_atomic
end Lamping.Checks.BetaAtomicComparison

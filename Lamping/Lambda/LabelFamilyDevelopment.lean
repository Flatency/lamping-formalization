import Lamping.Lambda.LabelUniformDevelopment
namespace Lamping.Lambda
open Labelled

/-- A whole historical family has one common current labelled degree,
using the same original INIT and the actual prefix labels. -/
theorem CompleteFamilyStep.uniform_degree {original source target : LTerm}
    {prior : ParallelHistory original.erase source.erase} {F : List Path}
    {step : ParallelStep F source.erase target.erase} {degree : Label}
    (whole : CompleteFamilyStep prior step) (initial : INIT original)
    (labels : History prior.derivation.paths original source)
    (representative : RedexOcc source.erase) (member : representative.val∈F)
    (atDegree : source.degreeAt representative.val=some degree) :
    ∀ path∈F,source.degreeAt path=some degree := by
  intro path chosen
  let candidate : RedexOcc source.erase := ⟨path,whole.1 path chosen⟩
  have family := whole.same_family representative candidate member chosen
  have equal := (family_iff_degree original initial
    (⟨source.erase,prior,representative⟩ : RedexWithHistory original.erase)
    (⟨source.erase,prior,candidate⟩ : RedexWithHistory original.erase)).mp family
  change degreeAlong original prior.derivation.paths representative.val=
    degreeAlong original prior.derivation.paths path at equal
  rw [degreeAlong_witness labels,degreeAlong_witness labels] at equal
  exact equal.symm.trans atDegree

/-- An already-complete global prefix and its actual whole-family OLD
step classify every final label: old labels are exactly marker-free ones.
This theorem consumes whole-family membership; it does not prove REP. -/
theorem CompleteFamilyStep.label_mem_iff_marker_free {original source target current : LTerm}
    {prior : ParallelHistory original.erase source.erase} {F : List Path}
    {step : ParallelStep F source.erase target.erase} {degree : Label} {edge : Path}
    (whole : CompleteFamilyStep prior step) (initial : INIT original)
    (complete : CompleteDerivation prior)
    (priorLabels : History prior.derivation.paths original source)
    (labels : History step.paths source target)
    (representative : RedexOcc source.erase) (member : representative.val∈F)
    (atDegree : source.degreeAt representative.val=some degree)
    (lookup : target.subterm edge=some current) :
    current.label∈source.labels ↔current.label.OuterBarsSafe (fun payload=>payload≠degree) :=
  step.label_mem_iff_marker_free labels (whole.uniform_degree initial priorLabels representative member atDegree)
    (complete_prefix_outer_bars_fresh initial prior complete priorLabels representative atDegree) lookup

end Lamping.Lambda

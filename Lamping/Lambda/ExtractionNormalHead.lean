import Lamping.Lambda.RootExtractionNormality
import Lamping.Lambda.ExtractionCuts
import Lamping.Lambda.ExtractionChurchRosser
namespace Lamping.Lambda

/-- An extraction from a head followed by a normal tail must delete that
 head. A positive deletion index would give an actual extraction in the tail. -/
theorem ExtractionStep.root_of_normal_tail {R : BetaAt t p u}
    {tail : ExtractionRun u} {result : ExtractionRun t}
    (step : ExtractionStep (.of (.cons (singleContraction R) tail.history) (.cons R tail.atomic)) result)
    (normal : ExtractionNormal tail) : RootExtraction R tail result := by
  obtain ⟨n,indexed⟩ := step.has_index
  cases n with
  | succ n =>
    obtain ⟨other,extracted,_⟩ := indexed.uncons R tail
    exact False.elim (normal ⟨other,extracted.step⟩)
  | zero =>
    obtain ⟨a,b,q,pre,ha,S,rest,next,root,source,target,index⟩ := indexed
    cases ha with
    | cons A ht => simp only [ParallelHistory.length] at index; omega
    | nil =>
      have paths := congrArg (fun r => r.history.derivation.paths) source
      change p::tail.history.derivation.paths=q::rest.history.derivation.paths at paths
      obtain ⟨head,remaining⟩ := List.cons.inj paths
      cases head
      cases R.unique S
      have sameTail : tail=rest := by apply ExtractionRun.ext_paths; exact remaining
      cases sameTail
      have sameTarget : result=next := target
      cases sameTarget
      exact root

/-- Normalizing a normal tail needs at most one further extraction at its
 new head. This is a proved property of the four rules, not a strategy field. -/
theorem extraction_normal_head {R : BetaAt t p u} (tail : ExtractionRun u)
    (normal : ExtractionNormal tail) :
    ExtractionNormal (.of (.cons (singleContraction R) tail.history) (.cons R tail.atomic)) ∨
      ∃ result, RootExtraction R tail result ∧ ExtractionNormal result := by
  classical
  by_cases full : ExtractionNormal (.of (.cons (singleContraction R) tail.history) (.cons R tail.atomic))
  · exact .inl full
  · obtain ⟨result,step⟩ := Classical.not_not.mp (by
      change ¬¬∃result,ExtractionStep (.of (.cons (singleContraction R) tail.history) (.cons R tail.atomic)) result
      exact full)
    have root := step.root_of_normal_tail normal
    exact .inr ⟨result,root,root.normal_target normal⟩

theorem Extraction.normal_head_factor {R : BetaAt t p u} {tail : ExtractionRun u}
    {result : ExtractionRun t} (normal : ExtractionNormal tail)
    (steps : Extraction (.of (.cons (singleContraction R) tail.history) (.cons R tail.atomic)) result)
    (resultNormal : ExtractionNormal result) :
    result=.of (.cons (singleContraction R) tail.history) (.cons R tail.atomic) ∨
      RootExtraction R tail result := by
  rcases extraction_normal_head (R := R) tail normal with full | ⟨other,root,otherNormal⟩
  · exact .inl (full.target_eq steps).symm
  · have eq := extraction_normal_unique (Extraction.single root.step) steps otherNormal resultNormal
    cases eq
    exact .inr root

/-- A normal form of a headed run is obtained from the normal form of its
 tail by retaining the head or one actual root extraction. All normal forms
 here are actual extraction successors of the supplied runs. -/
theorem extraction_normal_head_decomposition {R : BetaAt t p u}
    {tail normalTail : ExtractionRun u} {result : ExtractionRun t}
    (tailSteps : Extraction tail normalTail) (tailNormal : ExtractionNormal normalTail)
    (fullSteps : Extraction (.of (.cons (singleContraction R) tail.history) (.cons R tail.atomic)) result)
    (fullNormal : ExtractionNormal result) :
    result=.of (.cons (singleContraction R) normalTail.history) (.cons R normalTail.atomic) ∨
      RootExtraction R normalTail result := by
  have retained := tailSteps.prepend (.single (singleContraction R)) (.single R)
  obtain ⟨common,fromResult,fromRetained⟩ := extraction_church_rosser t fullSteps retained
  have same := fullNormal.target_eq fromResult
  cases same
  exact fromRetained.normal_head_factor tailNormal fullNormal

end Lamping.Lambda

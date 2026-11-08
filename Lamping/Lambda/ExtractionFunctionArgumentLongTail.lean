import Lamping.Lambda.ExtractionFunctionArgumentPeak
import Lamping.Lambda.ExtractionRowSplits
namespace Lamping.Lambda

theorem extraction_function_argument_prefixed_peak
    (R : BetaAt t p u) (R0 : BetaAt a p b)
    (pre : ParallelHistory t a) (hp : Atomic pre)
    (bottom : ParallelHistory u b) (hb : Atomic bottom)
    (prefixRow : StepProjection (singleContraction R) pre bottom (singleContraction R0))
    (S' : BetaAt a s' v) (S : BetaAt b s w) (R' : BetaAt v p w)
    (front : StepProjection (singleContraction R0) (.single (singleContraction S'))
      (.single (singleContraction S)) (singleContraction R'))
    (upper : ParallelHistory v upperEnd) (hu : Atomic upper)
    (copy : ParallelHistory w copyEnd) (hc : Atomic copy)
    (lower : ParallelHistory b lowerEnd) (hl : Atomic lower)
    (row : StepProjection (singleContraction R') upper copy last)
    (inside : Internal (p++[.fn]) (pre.append (.cons (singleContraction S') upper)))
    (positive : 0<copy.length) (lift : ArgumentLift S copy lower) :
    ExtractionJoin
      (.of (pre.append (.cons (singleContraction S') upper)) (hp.append (.cons S' hu)))
      (.of (.cons (singleContraction R) (bottom.append lower)) (.cons R (hb.append hl))) := by
  obtain ⟨preInside,tailInside⟩ := (Internal.append_iff _ _).mp inside
  have firstInside : ∃q,s'=(p++[.fn])++q := tailInside s'
    (by change s'∈s'::upper.derivation.paths; exact List.mem_cons_self)
  have upperInside : Internal (p++[.fn]) upper := by
    intro name hq
    exact tailInside name (by change name∈s'::upper.derivation.paths; exact List.mem_cons_of_mem _ hq)
  obtain ⟨target,original,ho,K,vertical,newLift,originalInside,rowR⟩ :=
    function_argument_pullback R0 S' S R' front firstInside upper hu copy hc lower hl row upperInside lift
  have upperPositive : 0<upper.length := by have len := row.length; omega
  have originalPositive : 0<original.length := by have len := newLift.length hu ho; omega
  let common := ExtractionRun.of (pre.append original) (hp.append ho)
  refine ⟨common,Extraction.single ?_,Extraction.single ?_⟩
  · simpa only [ParallelHistory.append_assoc] using
      (ExtractionStep.argumentPart pre hp S' upper hu original ho upperPositive newLift)
  · exact ExtractionStep.functionPart (.nil _) (.nil _) R _ (hp.append ho)
      _ (hb.append hl) vertical (prefixRow.append rowR)
      (by rw [ParallelHistory.length_append]; omega)
      ((Internal.append_iff _ _).mpr ⟨preInside,originalInside⟩)

/-- LEV80 (3,4) with arbitrary ordinary prefix and arbitrary nonempty
 specified-copy program. Source occurrence reflection is proved internally. -/
theorem extraction_function_argument_long_peak
    (R : BetaAt t p u)
    (bottom : ParallelHistory u b) (hb : Atomic bottom) (S : BetaAt b s w)
    (copy : ParallelHistory w copyEnd) (hc : Atomic copy)
    (whole : ParallelHistory t upperEnd) (ha : Atomic whole)
    (row : StepProjection (singleContraction R) whole
      (bottom.append (.cons (singleContraction S) copy)) last)
    (inside : Internal (p++[.fn]) whole)
    (lower : ParallelHistory b lowerEnd) (hl : Atomic lower)
    (positive : 0<copy.length) (lift : ArgumentLift S copy lower) :
    ExtractionJoin (.of whole ha)
      (.of (.cons (singleContraction R) (bottom.append lower)) (.cons R (hb.append hl))) := by
  obtain ⟨a,K,pre,post,vertical,hpre,hpost,he,row1,row2⟩ :=
    row.split_bottom bottom (.cons (singleContraction S) copy) ha hb (.cons S hc)
  obtain ⟨preInside,postInside⟩ := (Internal.append_iff pre post).mp (he ▸ inside)
  have outside : ¬∃q,p=(p++[.fn])++q := by
    rintro ⟨q,hq⟩
    have len := congrArg List.length hq
    simp only [List.length_append,List.length_singleton] at len
    omega
  have selected : K=[p] := row1.final_selection_singleton rfl ⟨p,R.redex⟩ rfl hpre preInside outside
  subst K
  have actual := (row1.final_vertical_singleton preInside outside).2
  obtain ⟨R0,verticalEq⟩ := vertical.eq_single_contraction ⟨p,actual.redex⟩ rfl
  cases verticalEq
  cases hpost with
  | nil => have len := row2.length; simp only [ParallelHistory.length] at len; omega
  | @cons a s' v upperEnd upper S' hu =>
    have firstInside : ∃q,s'=(p++[.fn])++q := postInside s'
      (by change s'∈s'::upper.derivation.paths; exact List.mem_cons_self)
    obtain ⟨R',front,upperRow⟩ := row2.region_head R0 S' S (.inr rfl) firstInside
    have joined := extraction_function_argument_prefixed_peak R R0 pre hpre bottom hb row1
      S' S R' front upper hu copy hc lower hl upperRow (he ▸ inside) positive lift
    simpa only [←he] using joined

end Lamping.Lambda

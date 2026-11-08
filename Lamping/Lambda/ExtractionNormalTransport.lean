import Lamping.Lambda.ExtractionMirror
namespace Lamping.Lambda

theorem extraction_single_normal (R : BetaAt t p u) :
    ExtractionNormal (.of (.single (singleContraction R)) (.single R)) := by
  rintro ⟨s,step⟩
  have less := step.rank_lt
  have positive := step.positive
  change s.rank<1 at less
  omega

theorem ExtractionNormal.lift_context (normal : ExtractionNormal r) (C : SyntaxContext) :
    ExtractionNormal (C.liftRun r) := by
  rintro ⟨target,step⟩
  obtain ⟨q,hq,_⟩ := C.reflectExtractionStep step
  exact normal ⟨q,hq⟩

theorem ExtractionNormal.rename_reflect (normal : ExtractionNormal (r.rename ρ)) :
    ExtractionNormal r := by
  rintro ⟨target,step⟩
  exact normal ⟨target.rename ρ,step.rename ρ⟩

theorem ExtractionNormal.rename (normal : ExtractionNormal r)
    {ρ ν : Nat → Nat} (left : ∀i,ν (ρ i)=i) : ExtractionNormal (r.rename ρ) := by
  rintro ⟨target,step⟩
  obtain ⟨q,hq,_⟩ := step.rename_reflect left
  exact normal ⟨q,hq⟩

theorem ExtractionNormal.shift (normal : ExtractionNormal r) (k : Nat) :
    ExtractionNormal (r.rename (fun i => i+k)) :=
  normal.rename (ν := fun i => i-k) (fun i => Nat.add_sub_cancel i k)

end Lamping.Lambda

import Lamping.Lambda.ArgumentParallelization
import Lamping.Lambda.ExtractionFamilies
import Lamping.Lambda.ProjectionFamilies
namespace Lamping.Lambda

theorem RunRepresents.positive (h : RunRepresents r a) : 0<r.rank := by
  obtain ⟨last,_,history⟩ := h
  change 0<r.history.length
  rw [history,ParallelHistory.length_append]
  change 0<a.history.length+1
  omega

/-- Each actual extraction generator preserves the pointed family. In
rule (iv) the proof uses two Copy legs to a common successor, not direct
Copy between the original pointed histories. -/
theorem ExtractionStep.family {r s : ExtractionRun m} (h : ExtractionStep r s) (a b : RedexWithHistory m)
    (source : RunRepresents r a) (target : RunRepresents s b) : FamilyEq a b := by
  cases h with
  | residual ρ hρ R S S' hs =>
    let left : RedexWithHistory m := ⟨_,ρ.append (.single (singleContraction R)),⟨_,S.redex⟩⟩
    let right : RedexWithHistory m := ⟨_,ρ,⟨_,S'.redex⟩⟩
    have hl : RunRepresents
        (.of ((ρ.append (.single (singleContraction R))).append (.single (singleContraction S)))
          ((hρ.append (.single R)).append (.single S))) left :=
      ⟨S,hρ.append (.single R),rfl⟩
    have hr : RunRepresents (.of (ρ.append (.single (singleContraction S'))) (hρ.append (.single S'))) right :=
      ⟨S',hρ,rfl⟩
    have ea := source.unique hl
    have eb := target.unique hr
    rw [ea,eb]
    exact residual_extraction_family ρ R S S' hs
  | disjoint ρ hρ R σ hσ σ' hσ' last row positive site apart inside =>
    obtain ⟨c,d,hc,hd,copy⟩ := row.pointed_copy R hσ hσ' positive ρ hρ
    have ea := source.unique hd
    have eb := target.unique hc
    rw [ea,eb]
    exact .symm (.copy copy)
  | functionPart ρ hρ R σ hσ σ' hσ' last row positive inside =>
    obtain ⟨c,d,hc,hd,copy⟩ := row.pointed_copy R hσ hσ' positive ρ hρ
    have ea := source.unique hd
    have eb := target.unique hc
    rw [ea,eb]
    exact .symm (.copy copy)
  | argumentPart ρ hρ R σ hσ σ' hσ' positive lift =>
    exact .symm (lift.pointed_family hσ hσ' positive ρ hρ b a target source)

theorem Extraction.family {r s : ExtractionRun m} (h : Extraction r s) (a b : RedexWithHistory m)
    (source : RunRepresents r a) (target : RunRepresents s b) : FamilyEq a b := by
  induction h generalizing a b with
  | refl =>
    have eq := source.unique target
    cases eq
    exact .refl _
  | @cons r mid s step rest ih =>
    obtain ⟨c,hc⟩ := mid.represents_exists step.positive
    exact .trans (step.family a c source hc) (ih c b hc target)

/-- AG5.2.7: a common actual extraction successor suffices for family
equivalence. No standardness, labels, normality or confluence is assumed. -/
theorem common_extraction_family (ha : RunRepresents r a) (hb : RunRepresents s b)
    (left : Extraction r common) (right : Extraction s common) : FamilyEq a b := by
  obtain ⟨c,hc⟩ := common.represents_exists (left.positive ha.positive)
  exact .trans (left.family a c ha hc) (.symm (right.family b c hb hc))

end Lamping.Lambda

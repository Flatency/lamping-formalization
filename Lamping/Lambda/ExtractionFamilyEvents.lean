import Lamping.Lambda.ArgumentFamilyEvents
import Lamping.Lambda.PointedProjectionPrefix
import Lamping.Lambda.ExtractionFamilyInvariance
namespace Lamping.Lambda

private theorem insert_event_map (pre : ParallelHistory m t) (first : ParallelStep F t u)
    (top : ParallelHistory t v) (bottom : ParallelHistory u w)
    (transport : ∀ a, FamilyUsedAt pre top a →
      FamilyUsedAt (pre.append (.single first)) bottom a)
    (used : FamilyUsed (pre.append top) a) :
    FamilyUsed ((pre.append (.single first)).append bottom) a := by
  rcases (FamilyUsedAt.append_iff (.nil m) pre top a).mp used with earlier | later
  · apply (FamilyUsedAt.append_iff (.nil m) (pre.append (.single first)) bottom a).mpr
    exact .inl ((FamilyUsedAt.append_iff (.nil m) pre (.single first) a).mpr (.inl earlier))
  · apply (FamilyUsedAt.append_iff (.nil m) (pre.append (.single first)) bottom a).mpr
    exact .inr (transport a later)

theorem StepProjection.pointed_family_events {R : BetaAt t p u}
    (row : StepProjection (singleContraction R) top bottom last)
    (ht : Atomic top) (hb : Atomic bottom) (positive : 0<top.length)
    (pre : ParallelHistory m t) (hpre : Atomic pre)
    (source : RunRepresents (.of ((pre.append (.single (singleContraction R))).append bottom)
      ((hpre.append (.single R)).append hb)) a)
    (target : RunRepresents (.of (pre.append top) (hpre.append ht)) b) :
    ∀ c, FamilyUsed b.history c → FamilyUsed a.history c := by
  obtain ⟨a0,ha0⟩ := (ExtractionRun.of bottom hb).represents_exists (by
    change 0<bottom.length; have := row.length; omega)
  obtain ⟨b0,hb0⟩ := (ExtractionRun.of top ht).represents_exists positive
  have ea := source.unique (ha0.prepend (pre.append (.single (singleContraction R)))
    (hpre.append (.single R)))
  have eb := target.unique (hb0.prepend pre hpre)
  rw [ea,eb]
  obtain ⟨_,vertical,prefixRow⟩ := row.pointed_prefix_row ht hb ha0 hb0
  intro c used
  exact insert_event_map pre (singleContraction R) b0.history a0.history
    (fun _ h => prefixRow.family_used_forward hb0.choose_spec.1 ha0.choose_spec.1 pre h) used

theorem ArgumentLift.pointed_family_events {R : BetaAt t p u}
    (lift : ArgumentLift R copy original) (hc : Atomic copy) (ho : Atomic original)
    (positive : 0<copy.length) (pre : ParallelHistory m t) (hpre : Atomic pre)
    (source : RunRepresents (.of ((pre.append (.single (singleContraction R))).append copy)
      ((hpre.append (.single R)).append hc)) a)
    (target : RunRepresents (.of (pre.append original) (hpre.append ho)) b) :
    ∀ c, FamilyUsed b.history c → FamilyUsed a.history c := by
  obtain ⟨a0,ha0⟩ := (ExtractionRun.of copy hc).represents_exists positive
  obtain ⟨b0,hb0⟩ := (ExtractionRun.of original ho).represents_exists (by
    change 0<original.length; have := lift.length hc ho; omega)
  have ea := source.unique (ha0.prepend (pre.append (.single (singleContraction R)))
    (hpre.append (.single R)))
  have eb := target.unique (hb0.prepend pre hpre)
  rw [ea,eb]
  obtain ⟨prefixLift,_⟩ := lift.pointed_prefix hc ho a0 b0 ha0 hb0
  intro c used
  exact insert_event_map pre (singleContraction R) b0.history a0.history
    (fun _ h => prefixLift.family_used_forward ha0.choose_spec.1 hb0.choose_spec.1 pre h) used

/-- Extraction cannot introduce a family event into the proper prefix
before the last represented contraction. The last contraction is excluded. -/
theorem ExtractionStep.pointed_family_events (step : ExtractionStep r s)
    (source : RunRepresents r a) (target : RunRepresents s b) :
    ∀ c, FamilyUsed b.history c → FamilyUsed a.history c := by
  cases step with
  | residual pre hp R S S' old =>
    have ea := source.unique (show RunRepresents _
      ⟨_,pre.append (.single (singleContraction R)),⟨_,S.redex⟩⟩ from
      ⟨S,hp.append (.single R),rfl⟩)
    have eb := target.unique (show RunRepresents _ ⟨_,pre,⟨_,S'.redex⟩⟩ from ⟨S',hp,rfl⟩)
    rw [ea,eb]
    intro c used
    exact (FamilyUsedAt.append_iff (.nil _) pre (.single (singleContraction R)) c).mpr (.inl used)
  | disjoint pre hp R top ht bottom hb last row positive site apart inside =>
    exact row.pointed_family_events ht hb positive pre hp source target
  | functionPart pre hp R top ht bottom hb last row positive inside =>
    exact row.pointed_family_events ht hb positive pre hp source target
  | argumentPart pre hp R copy hc original ho positive lift =>
    exact lift.pointed_family_events hc ho positive pre hp source target

theorem Extraction.pointed_family_events (extraction : Extraction r s)
    (source : RunRepresents r a) (target : RunRepresents s b) :
    ∀ c, FamilyUsed b.history c → FamilyUsed a.history c := by
  induction extraction generalizing a b with
  | refl =>
    have same := source.unique target
    cases same
    exact fun _ h => h
  | @cons r mid s first rest ih =>
    obtain ⟨point,represented⟩ := mid.represents_exists first.positive
    exact fun c used => first.pointed_family_events source represented c (ih represented target c used)

end Lamping.Lambda

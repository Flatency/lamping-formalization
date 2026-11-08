import Lamping.Lambda.ProjectionContextLift
import Lamping.Lambda.ExtractionContexts
import Lamping.Lambda.ContextualBeta
import Lamping.Lambda.OrdinarySplits
namespace Lamping.Lambda
namespace SyntaxContext

theorem liftBeta (C : SyntaxContext) (h : BetaAt t p u) :
    BetaAt (C.plug t) (C.path++p) (C.plug u) := by
  have hh := (C.liftStep (singleContraction h)).derivation.valid
  change BetaHistory (C.liftStep (singleContraction h)).paths _ _ at hh
  rw [C.liftStep_paths] at hh
  change BetaHistory [C.path++p] _ _ at hh
  cases hh with
  | cons head tail => cases tail; exact head

private theorem reindex_heq (h : ParallelStep F t u) (eq : F=G)
    (members : ∀ q,q∈F ↔ q∈G) : HEq h (h.reindex G members) := by
  cases eq
  rfl

theorem liftStep_single_heq (C : SyntaxContext) (h : BetaAt t p u) :
    HEq (C.liftStep (singleContraction h)) (singleContraction (C.liftBeta h)) := by
  have names : C.selection [p]=[C.path++p] := by rw [C.selection_eq_map]; rfl
  let converted := (C.liftStep (singleContraction h)).reindex [C.path++p]
    (fun q => by rw [names])
  have same := reindex_heq (C.liftStep (singleContraction h)) names (fun q => by rw [names])
  obtain ⟨beta,he⟩ := converted.eq_single_contraction ⟨_,(C.liftBeta h).redex⟩ rfl
  change HEq _ converted at same
  rw [he] at same
  exact same

private theorem replace_first {h : ParallelStep F t u} {k : ParallelStep G t u}
    (eq : F=G) (he : HEq h k) (row : StepProjection h σ τ last) : StepProjection k σ τ last := by
  cases eq
  cases eq_of_heq he
  exact row

theorem liftBeta_projection (C : SyntaxContext) {R : BetaAt t p u}
    (row : StepProjection (singleContraction R) σ τ last) :
    StepProjection (singleContraction (C.liftBeta R)) (C.liftHistory σ) (C.liftHistory τ)
      (C.liftStep last) := by
  exact replace_first (by rw [C.selection_eq_map]; rfl) (C.liftStep_single_heq R)
    (C.liftProjection row)

theorem liftHistory_length (C : SyntaxContext) (h : ParallelHistory t u) :
    (C.liftHistory h).length=h.length := by
  have frame (D : SyntaxFrame) {a b : Term} (h : ParallelHistory a b) :
      (D.liftHistory h).length=h.length := by
    induction h with
    | nil => rfl
    | cons head tail ih => change 1+_=1+_; rw [ih]
  induction C with
  | hole => rfl
  | frame outer inner ih => exact (frame outer _).trans ih

theorem liftHistory_internal (C : SyntaxContext) (inside : Internal p σ) :
    Internal (C.path++p) (C.liftHistory σ) := by
  intro z hz
  rw [C.liftHistory_paths] at hz
  obtain ⟨q,hq,he⟩ := List.mem_map.mp hz
  obtain ⟨tail,ht⟩ := inside q hq
  exact ⟨tail,he.symm.trans (by rw [ht,List.append_assoc])⟩

theorem lift_disjoint (C : SyntaxContext) (apart : DisjointPositions p q) :
    DisjointPositions (C.path++p) (C.path++q) := by
  constructor
  · rintro ⟨tail,he⟩
    apply apart.1
    exact ⟨tail,List.append_cancel_left (by simpa only [List.append_assoc] using he)⟩
  · rintro ⟨tail,he⟩
    apply apart.2
    exact ⟨tail,List.append_cancel_left (by simpa only [List.append_assoc] using he)⟩

noncomputable def liftRun (C : SyntaxContext) (r : ExtractionRun t) : ExtractionRun (C.plug t) :=
  .of (C.liftHistory r.history) (C.liftAtomic r.atomic)

theorem liftRun_paths (C : SyntaxContext) (r : ExtractionRun t) :
    (C.liftRun r).history.derivation.paths=r.history.derivation.paths.map (fun q => C.path++q) :=
  C.liftHistory_paths r.history

theorem liftHistory_single (C : SyntaxContext) (R : BetaAt t p u) :
    C.liftHistory (.single (singleContraction R))=
      .single (singleContraction (C.liftBeta R)) := by
  apply (C.liftAtomic (.single R)).paths_injective (.single (C.liftBeta R))
  rw [C.liftHistory_paths]
  rfl

theorem lift_residual (C : SyntaxContext) (R : BetaAt t p u)
    (S : BetaAt u q v) (S' : BetaAt t q' v')
    (residual : (singleContraction R).derivation.Residual ⟨q',S'.redex⟩ ⟨q,S.redex⟩) :
    (singleContraction (C.liftBeta R)).derivation.Residual
      ⟨C.path++q',(C.liftBeta S').redex⟩ ⟨C.path++q,(C.liftBeta S).redex⟩ := by
  exact ((singleContraction R).derivation.prefix_residual_iff
    (singleContraction (C.liftBeta R)).derivation (C.lookup t) (by rfl)
    ⟨q',S'.redex⟩ ⟨q,S.redex⟩ _ _ rfl rfl).mpr residual

noncomputable def liftArgument (C : SyntaxContext) {R : BetaAt t p u}
    (lift : ArgumentLift R σ σ') :
    ArgumentLift (C.liftBeta R) (C.liftHistory σ) (C.liftHistory σ') where
  body := lift.body
  argument := lift.argument
  redex := by rw [subtermAt_append,C.lookup,Option.bind_some,lift.redex]
  occurrence := lift.occurrence
  isVariable := lift.isVariable
  localPaths := lift.localPaths
  copy_paths := by
    rw [C.liftHistory_paths,lift.copy_paths]
    simp only [List.map_map,Function.comp_def,List.append_assoc]
  original_paths := by
    rw [C.liftHistory_paths,lift.original_paths]
    simp only [List.map_map,Function.comp_def,List.append_assoc]
  parallelization := by
    obtain ⟨z,F,full,last,row⟩ := lift.parallelization
    exact ⟨C.plug z,C.selection F,C.liftHistory full,C.liftStep last,C.liftBeta_projection row⟩

private theorem liftRun_append (C : SyntaxContext) (ρ : ParallelHistory m t) (hρ : Atomic ρ)
    (σ : ParallelHistory t u) (hσ : Atomic σ) :
    C.liftRun (.of (ρ.append σ) (hρ.append hσ))=
      .of ((C.liftHistory ρ).append (C.liftHistory σ))
        ((C.liftAtomic hρ).append (C.liftAtomic hσ)) := by
  apply ExtractionRun.ext_paths
  simp only [liftRun_paths,ExtractionRun.of,ParallelHistory.derivation_append,Derivation.append,
    List.map_append,C.liftHistory_paths]

private theorem liftRun_head (C : SyntaxContext) (R : BetaAt t p u)
    (σ : ParallelHistory u v) (hσ : Atomic σ) :
    C.liftRun (.of (.cons (singleContraction R) σ) (.cons R hσ))=
      .of (.cons (singleContraction (C.liftBeta R)) (C.liftHistory σ))
        (.cons (C.liftBeta R) (C.liftAtomic hσ)) := by
  apply ExtractionRun.ext_paths
  change (C.liftHistory (.cons (singleContraction R) σ)).derivation.paths=
    _
  rw [C.liftHistory_paths]
  change (p::σ.derivation.paths).map (fun q => C.path++q)=
    (C.path++p)::(C.liftHistory σ).derivation.paths
  rw [List.map_cons,C.liftHistory_paths]

private theorem liftRun_prefix_head (C : SyntaxContext)
    (ρ : ParallelHistory m t) (hρ : Atomic ρ) (R : BetaAt t p u)
    (σ : ParallelHistory u v) (hσ : Atomic σ) :
    C.liftRun (.of ((ρ.append (.single (singleContraction R))).append σ)
        ((hρ.append (.single R)).append hσ))=
      .of (((C.liftHistory ρ).append (.single (singleContraction (C.liftBeta R)))).append
        (C.liftHistory σ)) (((C.liftAtomic hρ).append (.single (C.liftBeta R))).append
          (C.liftAtomic hσ)) := by
  apply ExtractionRun.ext_paths
  change (C.liftHistory _).derivation.paths=_
  rw [C.liftHistory_paths]
  simp only [ExtractionRun.of,ParallelHistory.derivation_append,Derivation.append]
  change ((ρ.derivation.paths++[p])++σ.derivation.paths).map (fun q => C.path++q)=
    ((C.liftHistory ρ).derivation.paths++[C.path++p])++(C.liftHistory σ).derivation.paths
  rw [List.map_append,List.map_append,C.liftHistory_paths,C.liftHistory_paths]
  rfl

private theorem liftRun_prefix_single (C : SyntaxContext)
    (ρ : ParallelHistory m t) (hρ : Atomic ρ) (R : BetaAt t p u) :
    C.liftRun (.of (ρ.append (.single (singleContraction R))) (hρ.append (.single R)))=
      .of ((C.liftHistory ρ).append (.single (singleContraction (C.liftBeta R))))
        ((C.liftAtomic hρ).append (.single (C.liftBeta R))) := by
  apply ExtractionRun.ext_paths
  change (C.liftHistory _).derivation.paths=_
  rw [C.liftHistory_paths]
  simp only [ExtractionRun.of,ParallelHistory.derivation_append,Derivation.append]
  change (ρ.derivation.paths++[p]).map (fun q => C.path++q)=
    (C.liftHistory ρ).derivation.paths++[C.path++p]
  rw [List.map_append,C.liftHistory_paths]
  rfl

/-- Every original extraction generator transports through a concrete syntax
context, retaining its ordinary histories and old-redex witnesses. -/
theorem liftExtractionStep (C : SyntaxContext) (step : ExtractionStep r s) :
    ExtractionStep (C.liftRun r) (C.liftRun s) := by
  cases step with
  | residual ρ hρ R S S' hs =>
    rw [C.liftRun_prefix_head ρ hρ R (.single (singleContraction S)) (.single S),
      C.liftRun_prefix_single ρ hρ S']
    have generated := ExtractionStep.residual (C.liftHistory ρ) (C.liftAtomic hρ)
      (C.liftBeta R) (C.liftBeta S) (C.liftBeta S') (C.lift_residual R S S' hs)
    have sourceEq :
        ExtractionRun.of (((C.liftHistory ρ).append (.single (singleContraction (C.liftBeta R)))).append
          (C.liftHistory (.single (singleContraction S))))
          (((C.liftAtomic hρ).append (.single (C.liftBeta R))).append (C.liftAtomic (.single S))) =
        ExtractionRun.of (((C.liftHistory ρ).append (.single (singleContraction (C.liftBeta R)))).append
          (.single (singleContraction (C.liftBeta S))))
          (((C.liftAtomic hρ).append (.single (C.liftBeta R))).append (.single (C.liftBeta S))) := by
      apply ExtractionRun.ext_paths
      simp only [ExtractionRun.of,ParallelHistory.derivation_append,Derivation.append,
        C.liftHistory_single S]
    rw [sourceEq]
    exact generated
  | disjoint ρ hρ R σ hσ σ' hσ' last row positive site apart inside =>
    rw [C.liftRun_prefix_head ρ hρ R σ' hσ',C.liftRun_append ρ hρ σ hσ]
    exact .disjoint (C.liftHistory ρ) (C.liftAtomic hρ) (C.liftBeta R)
      (C.liftHistory σ) (C.liftAtomic hσ) (C.liftHistory σ') (C.liftAtomic hσ')
      (C.liftStep last) (C.liftBeta_projection row)
      (by rw [C.liftHistory_length]; exact positive) (C.path++site)
      (C.lift_disjoint apart) (C.liftHistory_internal inside)
  | functionPart ρ hρ R σ hσ σ' hσ' last row positive inside =>
    rw [C.liftRun_prefix_head ρ hρ R σ' hσ',C.liftRun_append ρ hρ σ hσ]
    exact .functionPart (C.liftHistory ρ) (C.liftAtomic hρ) (C.liftBeta R)
      (C.liftHistory σ) (C.liftAtomic hσ) (C.liftHistory σ') (C.liftAtomic hσ')
      (C.liftStep last) (C.liftBeta_projection row)
      (by rw [C.liftHistory_length]; exact positive)
      (by simpa only [List.append_assoc] using C.liftHistory_internal inside)
  | argumentPart ρ hρ R σ hσ σ' hσ' positive lift =>
    rw [C.liftRun_prefix_head ρ hρ R σ hσ,C.liftRun_append ρ hρ σ' hσ']
    exact .argumentPart (C.liftHistory ρ) (C.liftAtomic hρ) (C.liftBeta R)
      (C.liftHistory σ) (C.liftAtomic hσ) (C.liftHistory σ') (C.liftAtomic hσ')
      (by rw [C.liftHistory_length]; exact positive) (C.liftArgument lift)

theorem liftExtraction (C : SyntaxContext) (steps : Extraction r s) :
    Extraction (C.liftRun r) (C.liftRun s) := by
  induction steps with
  | refl => exact .refl _
  | cons step rest ih => exact .cons (C.liftExtractionStep step) ih

theorem liftExtractionJoin (C : SyntaxContext) (join : ExtractionJoin r s) :
    ExtractionJoin (C.liftRun r) (C.liftRun s) := by
  obtain ⟨z,left,right⟩ := join
  exact ⟨C.liftRun z,C.liftExtraction left,C.liftExtraction right⟩

theorem normal_of_lift (C : SyntaxContext) (normal : ExtractionNormal (C.liftRun r)) :
    ExtractionNormal r := by
  rintro ⟨s,step⟩
  exact normal ⟨C.liftRun s,C.liftExtractionStep step⟩

end SyntaxContext
end Lamping.Lambda

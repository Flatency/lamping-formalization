import Lamping.Lambda.PassiveSubstitution
import Lamping.Lambda.SubstitutionBeta
import Lamping.Lambda.MaximalCopies
import Lamping.Lambda.StandardizationFactorization
import Lamping.Lambda.TraceNoDup
namespace Lamping.Lambda

theorem SelectionValid.substitute (valid : SelectionValid t F) (σ : Nat → Term) :
    SelectionValid (subst σ t) F := by
  intro p hp
  let r : RedexOcc t := ⟨p,valid p hp⟩
  obtain ⟨target,step⟩ := r.contract_exists
  exact (step.subst σ).redex

/-- Valid source selections retain the chosen complete schedule under
arbitrary capture-avoiding substitution. Newly created redexes stay passive. -/
theorem ParallelStep.substitute_exists (h : ParallelStep F t u) (σ : Nat → Term)
    (valid : SelectionValid t F) :
    ∃ k : ParallelStep F (subst σ t) (subst σ u),k.paths=h.paths := by
  let values := fun i => Marked.plain (σ i)
  have erasedValues : (fun i => (values i).erase)=σ := by funext i; exact Marked.erase_plain _
  have complete := (Marked.completeOld_iff F t).mp h.complete
  have shape : (Marked.subst values (Marked.mark F t)).skeleton =
      (Marked.mark F (subst σ t)).skeleton := by
    apply Marked.skeleton_of_shape
    · simp only [Marked.erase_subst,Marked.erase_mark,erasedValues]
    · intro p
      rw [Marked.active_subst_inactive _ values (fun i => Marked.plain_normal _),
        Marked.active_mark,Marked.active_mark]
      constructor
      · rintro ⟨selected,_⟩
        exact ⟨selected,(mem_redexPositions _ p).mpr (valid.substitute σ p selected)⟩
      · rintro ⟨selected,_⟩
        exact ⟨selected,(mem_redexPositions _ p).mpr (valid p selected)⟩
  obtain ⟨target,history,same⟩ := (complete.1.substitute values).lift_skeleton shape
  have normal := Marked.normal_of_skeleton same
    (Marked.normal_subst complete.2 (fun i => Marked.plain_normal _))
  have erased : target.erase=subst σ u := by
    have equal := congrArg Marked.erase same
    simp only [Marked.skeleton_erase,Marked.erase_subst,erasedValues,h.target_eq] at equal
    exact equal.symm
  exact ⟨⟨h.paths,target,(Marked.completeOld_iff _ _).mpr ⟨history,normal⟩,erased⟩,rfl⟩

noncomputable def ParallelStep.substitute (h : ParallelStep F t u) (σ : Nat → Term)
    (valid : SelectionValid t F) : ParallelStep F (subst σ t) (subst σ u) :=
  Classical.choose (h.substitute_exists σ valid)

@[simp] theorem ParallelStep.substitute_paths (h : ParallelStep F t u) (σ : Nat → Term)
    (valid : SelectionValid t F) : (h.substitute σ valid).paths=h.paths :=
  Classical.choose_spec (h.substitute_exists σ valid)

/-- Old valid identities retain their literal residual-list order through
the same actual substituted beta program. Fresh redex identities are excluded. -/
theorem ParallelStep.substitution_trace_eq (h : ParallelStep F t u)
    (k : ParallelStep G (subst σ t) (subst σ u)) (paths : k.paths=h.paths) (r : RedexOcc t) :
    Marked.tracePositions r.val h.markedTarget=Marked.tracePositions r.val k.markedTarget := by
  let values := fun i => Marked.plain (σ i)
  have erasedValues : (fun i => (values i).erase)=σ := by funext i; exact Marked.erase_plain _
  have valueTrace : ∀ i,Marked.tracePositions r.val (values i)=[] := fun i => Marked.plain_trace _ _
  let image : RedexOcc (subst σ t) := ⟨r.val,(SelectionValid.substitute
    (F := [r.val]) (by intro p hp; cases List.mem_singleton.mp hp; exact r.property) σ) _ (List.mem_singleton_self _)⟩
  have initialErase : (Marked.subst values (Marked.mark [] t)).erase=(Marked.mark [] (subst σ t)).erase := by
    simp only [Marked.erase_subst,Marked.erase_mark,erasedValues]
  have initialTrace : ∀q,q∈Marked.tracePositions r.val (Marked.subst values (Marked.mark [] t)) ↔
      q∈Marked.tracePositions r.val (Marked.mark [] (subst σ t)) := by
    intro q
    rw [Marked.trace_subst_untagged _ _ valueTrace,Marked.initial_trace_singleton [] t r]
    exact (congrArg (fun ps => q∈ps) (Marked.initial_trace_singleton [] (subst σ t) image)).symm.to_iff
  have first := h.tracked.substitute values
  have second := k.tracked
  rw [paths] at second
  have sourceTarget : (Marked.subst values h.markedTarget.passive).erase=k.markedTarget.passive.erase := by
    simp only [Marked.erase_subst,erasedValues,Marked.passive_erase,h.target_eq,k.target_eq]
  have equal := Marked.trace_eq_of_members sourceTarget (fun q =>
    ⟨first.trace_inclusion second initialErase (fun q => (initialTrace q).mp) q,
      second.trace_inclusion first initialErase.symm (fun q => (initialTrace q).mpr) q⟩)
  simpa only [Marked.trace_subst_untagged _ _ valueTrace,Marked.passive_trace] using equal

theorem ParallelStep.substitution_residualSet_eq (h : ParallelStep F t u)
    (k : ParallelStep G (subst σ t) (subst σ u)) (paths : k.paths=h.paths)
    (validNames : SelectionValid t names) : k.residualSet names=h.residualSet names := by
  unfold ParallelStep.residualSet Marked.setResidualPositions
  induction names with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons]
    rw [←h.substitution_trace_eq k paths ⟨p,validNames p List.mem_cons_self⟩]
    exact congrArg (List.append _) (ih (fun q hq => validNames q (List.mem_cons_of_mem _ hq)))

end Lamping.Lambda

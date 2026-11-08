import Lamping.Lambda.ArgumentParallelization
import Lamping.Lambda.HistoryCancellation
namespace Lamping.Lambda

private theorem list_last (xs : List α) (nonempty : xs≠[]) :
    ∃ (pre : List α) (last : α),xs=pre++[last] := by
  cases eq : xs.reverse with
  | nil =>
    have empty := congrArg List.reverse eq
    simp only [List.reverse_reverse,List.reverse_nil] at empty
    exact False.elim (nonempty empty)
  | cons last rest =>
    refine ⟨rest.reverse,last,?_⟩
    have same := congrArg List.reverse eq
    simpa only [List.reverse_reverse,List.reverse_cons] using same

private theorem append_last_injective (h : xs++[a]=ys++[b]) : xs=ys ∧ a=b := by
  have reversed := congrArg List.reverse h
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] at reversed
  obtain ⟨last,same⟩ := List.cons.inj reversed
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse same,last⟩

theorem ArgumentLift.pointed_coordinates {R : BetaAt t p u}
    (lift : ArgumentLift R copy original) (hc : Atomic copy) (ho : Atomic original)
    (a : RedexWithHistory u) (b : RedexWithHistory t)
    (sourceRep : RunRepresents (.of copy hc) a) (targetRep : RunRepresents (.of original ho) b) :
    ∃ (program : List Path) (last : Path),
      a.history.derivation.paths=program.map (fun q => (p++lift.occurrence)++q) ∧
      b.history.derivation.paths=program.map (fun q => (p++[.arg])++q) ∧
      a.redex.val=(p++lift.occurrence)++last ∧ b.redex.val=(p++[.arg])++last := by
  obtain ⟨lastA,_,copyEq⟩ := sourceRep
  obtain ⟨lastB,_,originalEq⟩ := targetRep
  change copy=a.history.append (.single (singleContraction lastA)) at copyEq
  change original=b.history.append (.single (singleContraction lastB)) at originalEq
  have nonempty : lift.localPaths≠[] := by
    intro empty
    have paths := lift.copy_paths
    conv at paths => lhs; rw [copyEq,ParallelHistory.derivation_append,ParallelHistory.single_derivation]
    rw [empty,List.map_nil] at paths
    have length := congrArg List.length paths
    simp only [Derivation.append,List.length_append] at length
    change a.history.derivation.paths.length+1=0 at length
    omega
  obtain ⟨program,last,localEq⟩ := list_last lift.localPaths nonempty
  have copied := lift.copy_paths
  conv at copied => lhs; rw [copyEq,ParallelHistory.derivation_append,ParallelHistory.single_derivation]
  rw [localEq,List.map_append,List.map_cons,List.map_nil] at copied
  change a.history.derivation.paths++[a.redex.val]=
    program.map (fun q => (p++lift.occurrence)++q)++[(p++lift.occurrence)++last] at copied
  have source := append_last_injective copied
  have originalPaths := lift.original_paths
  conv at originalPaths => lhs; rw [originalEq,ParallelHistory.derivation_append,ParallelHistory.single_derivation]
  rw [localEq,List.map_append,List.map_cons,List.map_nil] at originalPaths
  change b.history.derivation.paths++[b.redex.val]=
    program.map (fun q => (p++[.arg])++q)++[(p++[.arg])++last] at originalPaths
  have target := append_last_injective originalPaths
  exact ⟨program,last,source.1,target.1,source.2,target.2⟩

theorem ApartHistory.residual_inside_fixed {history : ParallelHistory t u}
    (apart : ApartHistory site history) (r : RedexOcc t) (s : RedexOcc u)
    (inside : ∃q,r.val=site++q) (residual : history.derivation.Residual r s) : s.val=r.val := by
  obtain ⟨q,hq⟩ := inside
  have paths : ∀p∈history.derivation.paths,DisjointPositions r.val p := by
    intro p hp; rw [hq]; exact (apart.paths_apart p hp).descend_left q
  obtain ⟨target,tracked,erased⟩ := history.derivation.tracked
  have fixed := tracked.trace_fixed_apart paths (fun p hp => (Marked.initial_residual [] t r p).mp hp)
  have finalTrace := (Derivation.residual_iff_tracking _ tracked r s).mp residual
  rw [fixed] at finalTrace
  exact (Marked.initial_residual [] t r s.val).mp finalTrace

/-- The specified argument copy has one possible pointed image in the
actual full projection. This is the disjoint remainder in Levy Lemma4.11;
neither canonicality nor a family-to-residual implication is assumed. -/
theorem argument_pointed_projection_fiber (R : BetaAt t p u)
    (lookup : subtermAt t p=some (.app (.lam body) argument))
    (occurs : ArgumentOccurrence body occ)
    (original : ParallelHistory t v) (ordinary : Atomic original)
    (copy : ParallelHistory u w) (copyAtomic : Atomic copy)
    (program : List Path)
    (originalPaths : original.derivation.paths=program.map (fun q => (p++[.arg])++q))
    (copyPaths : copy.derivation.paths=program.map (fun q => (p++occ)++q))
    (r : RedexOcc v) (s : RedexOcc w)
    (originalLast : r.val=(p++[.arg])++localLast) (copyLast : s.val=(p++occ)++localLast)
    {full : ParallelHistory u z} {last : ParallelStep F v z}
    (row : StepProjection (singleContraction R) original full last) :
    ∃ q : RedexOcc z,
      Copy ⟨v,original,r⟩ ⟨z,(ParallelHistory.single (singleContraction R)).append full,q⟩ ∧
      ∀ q' : RedexOcc z,Copy ⟨w,copy,s⟩ ⟨z,full,q'⟩ → q'=q := by
  obtain ⟨other,factor,apart⟩ := ordinary.argument_projection_factor (singleContraction R) rfl
    lookup occurs program originalPaths copyAtomic copyPaths row
  obtain ⟨q,position,old⟩ := apart.inside_survives s ⟨localLast,copyLast⟩
  have originalInside : Internal (p++[.arg]) original := by
    intro name hn
    rw [originalPaths] at hn
    obtain ⟨suffix,_,same⟩ := List.mem_map.mp hn
    exact ⟨suffix,same.symm⟩
  have outside : ¬∃suffix,p=(p++[.arg])++suffix := by
    rintro ⟨suffix,equal⟩
    have lengths := congrArg List.length equal
    simp only [List.length_append,List.length_singleton] at lengths
    omega
  have selected : F=[p] := row.final_selection_singleton rfl ⟨p,R.redex⟩ rfl ordinary originalInside outside
  subst F
  obtain ⟨argument',_,newLookup,_,_⟩ := original.argument_head_preserved lookup originalInside
  obtain ⟨R1,lastEq⟩ := last.eq_single_contraction ⟨p,⟨_,newLookup,True.intro⟩⟩ rfl
  have image : last.derivation.Residual r q := by
    rw [lastEq]
    apply (R1.argument_residual_iff newLookup r originalLast q).mpr
    exact ⟨occ,occurs,position.trans copyLast⟩
  refine ⟨q,⟨.single last,row.permutation.symm,?_⟩,?_⟩
  · simpa only [ParallelHistory.single_derivation] using image
  · intro q' copied
    obtain ⟨extension,perm,residual⟩ := copied
    have same : PermEq extension other := (perm.trans factor).cancel_prefix copy
    have transported := (same.residual s q').mp residual
    have fixed := apart.residual_inside_fixed s q' ⟨localLast,copyLast⟩ transported
    exact Subtype.ext (fixed.trans position.symm)

end Lamping.Lambda

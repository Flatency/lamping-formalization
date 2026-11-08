import Lamping.Lambda.ArgumentPullback
import Lamping.Lambda.ContextualResiduals
import Lamping.Lambda.RootCreation
namespace Lamping.Lambda

/-- An actual variable leaf cannot properly contain another variable leaf. -/
theorem variable_prefix_eq (hp : subtermAt b p=some (.var i))
    (hq : subtermAt b q=some (.var j)) (pre : ∃ s, q=p++s) : p=q := by
  obtain ⟨s,he⟩ := pre
  rw [he,subtermAt_append,hp,Option.bind_some] at hq
  cases s with
  | nil => simpa only [List.append_nil] using he.symm
  | cons e tail => cases e <;> simp [subtermAt] at hq

theorem ArgumentOccurrence.disjoint_of_ne (hp : ArgumentOccurrence b p)
    (hq : ArgumentOccurrence b q) (different : p≠q) : DisjointPositions p q := by
  constructor
  · intro he; exact different (variable_prefix_eq hp hq he)
  · intro he; exact different (variable_prefix_eq hq hp he).symm

theorem ArgumentOccurrence.context_disjoint (hp : ArgumentOccurrence b p)
    (hq : ArgumentOccurrence b q) (different : p≠q) (pre : Path) :
    DisjointPositions (pre++p) (pre++q) := by
  have hd := hp.disjoint_of_ne hq different
  constructor
  · rintro ⟨tail,he⟩
    exact hd.1 ⟨tail,List.append_cancel_left (by simpa only [List.append_assoc] using he)⟩
  · rintro ⟨tail,he⟩
    exact hd.2 ⟨tail,List.append_cancel_left (by simpa only [List.append_assoc] using he)⟩

/-- Every residual of an old argument redex lies in one genuine bound
variable instance, including a beta contracted in an arbitrary context. -/
theorem BetaAt.argument_residual_source (R : BetaAt t p u)
    (lookup : subtermAt t p=some (.app (.lam b) a)) (r : RedexOcc t)
    (source : r.val=(p++[.arg])++q) (z : RedexOcc u)
    (residual : (singleContraction R).derivation.Residual r z) :
    ∃ occ, ArgumentOccurrence b occ ∧ z.val=(p++occ)++q := by
  classical
  have targetLookup := R.contract_lookup lookup
  have paths : (singleContraction R).derivation.paths=
      (rootContraction b a).paths.map (fun q => p++q) := by change [p]=[p++[]]; rw [List.append_nil]
  have targetInside : ∃ s, z.val=p++s := by
    by_cases inside : ∃ s, z.val=p++s
    · exact inside
    · have same := (singleContraction R).derivation.prefix_residual_outside_target paths r z inside residual
      exact False.elim (inside ⟨[.arg]++q,by simpa only [List.append_assoc] using same.symm.trans source⟩)
  obtain ⟨s,hs⟩ := targetInside
  let localSource : RedexOcc (.app (.lam b) a) := ⟨[.arg]++q,by
    have h := r.property
    rw [source,List.append_assoc,subtermAt_append,lookup,Option.bind_some] at h
    exact h⟩
  let localTarget : RedexOcc (contract b a) := ⟨s,by
    have h := z.property
    rw [hs,subtermAt_append,targetLookup,Option.bind_some] at h
    exact h⟩
  have localResidual := (Derivation.prefix_residual_iff (rootContraction b a)
    (singleContraction R).derivation lookup paths localSource localTarget r z
    (by simpa only [List.append_assoc] using source) hs).mp residual
  rcases (root_residual_iff localSource localTarget).mp localResidual with body | ⟨occ,tail,ho,hz,hr,_⟩
  · have impossible : [.arg]++q=[.fn,.body]++s := body.1
    cases impossible
  · have same : q=tail := List.append_cancel_left hr
    refine ⟨occ,ho,?_⟩
    change s=occ++tail at hz
    rw [hs,hz,←same,List.append_assoc]

private theorem renamed_redex (h : ∃ z, subtermAt a q=some z ∧ IsRedex z) (ρ : Nat → Nat) :
    ∃ z, subtermAt (rename ρ a) q=some z ∧ IsRedex z := by
  obtain ⟨z,hz,hr⟩ := h
  refine ⟨rename (occurrenceRenaming ρ q) z,?_,(isRedex_rename_iff _ _).mpr hr⟩
  rw [subtermAt_rename,hz]
  rfl

/-- Every specified bound-variable occurrence has its own actual residual
of each old argument redex. The target redex is constructed, not assumed. -/
theorem BetaAt.argument_residual_exists (R : BetaAt t p u)
    (lookup : subtermAt t p=some (.app (.lam b) a)) (r : RedexOcc t)
    (source : r.val=(p++[.arg])++q) (ho : ArgumentOccurrence b occ) :
    ∃ z : RedexOcc u, z.val=(p++occ)++q ∧
      (singleContraction R).derivation.Residual r z := by
  have targetLookup := R.contract_lookup lookup
  have argumentRedex : ∃ z, subtermAt a q=some z ∧ IsRedex z := by
    have h := r.property
    rw [source,List.append_assoc,subtermAt_append,lookup,Option.bind_some] at h
    exact h
  have copyRedex : ∃ z, subtermAt (contract b a) (occ++q)=some z ∧ IsRedex z := by
    rw [subtermAt_append,argument_copy ho a,Option.bind_some]
    exact renamed_redex argumentRedex _
  let localTarget : RedexOcc (contract b a) := ⟨occ++q,copyRedex⟩
  let localSource : RedexOcc (.app (.lam b) a) := ⟨[.arg]++q,by
    change ∃ z,subtermAt a q=some z ∧ IsRedex z
    exact argumentRedex⟩
  let target : RedexOcc u := ⟨(p++occ)++q,by
    simpa only [List.append_assoc,subtermAt_append,targetLookup,Option.bind_some] using copyRedex⟩
  have paths : (singleContraction R).derivation.paths=
      (rootContraction b a).paths.map (fun q => p++q) := by change [p]=[p++[]]; rw [List.append_nil]
  refine ⟨target,rfl,?_⟩
  apply (Derivation.prefix_residual_iff (rootContraction b a) (singleContraction R).derivation
    lookup paths localSource localTarget r target (by simpa only [List.append_assoc] using source)
    (by simp only [target,localTarget,List.append_assoc])).mpr
  exact root_argument_residual occ q ho localSource localTarget rfl rfl

theorem BetaAt.argument_residual_iff (R : BetaAt t p u)
    (lookup : subtermAt t p=some (.app (.lam b) a)) (r : RedexOcc t)
    (source : r.val=(p++[.arg])++q) (z : RedexOcc u) :
    (singleContraction R).derivation.Residual r z ↔
      ∃ occ, ArgumentOccurrence b occ ∧ z.val=(p++occ)++q := by
  constructor
  · exact R.argument_residual_source lookup r source z
  · rintro ⟨occ,ho,hz⟩
    obtain ⟨z',he,hr⟩ := R.argument_residual_exists lookup r source ho
    have same : z'=z := Subtype.ext (he.trans hz.symm)
    simpa only [same] using hr

end Lamping.Lambda

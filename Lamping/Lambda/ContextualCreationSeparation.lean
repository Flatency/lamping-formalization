import Lamping.Lambda.CreationContexts
import Lamping.Lambda.CreationSeparation
import Lamping.Lambda.DisjointCreationSeparation
namespace Lamping.Lambda

def CreationSeparationAt (t : Term) (p q : Path) : Prop :=
  ∀ {u v w}, (hR : BetaAt t p u) → (hS : BetaAt t q v) → p ≠ q →
    (afterR : ParallelStep ((singleContraction hR).residualSet [q]) u w) →
    (afterS : ParallelStep ((singleContraction hS).residualSet [p]) v w) →
    (T1 : RedexOcc u) → (T2 : RedexOcc v) → (T : RedexOcc w) →
    afterR.derivation.Residual T1 T → afterS.derivation.Residual T2 T →
    ∃ T0 : RedexOcc t,
      ((singleContraction hR).derivation.append afterR.derivation).Residual T0 T

/-- The common-context induction step, including pointed redexes outside the
 chosen child. Residual selections are reindexed by proved membership. -/
theorem SyntaxFrame.creation_separation (C : SyntaxFrame) (ih : CreationSeparationAt t p q) :
    CreationSeparationAt (C.plug t) (C.edge :: p) (C.edge :: q) := by
  classical
  intro u v w hR hS distinct afterR afterS T1 T2 T h1 h2
  obtain ⟨u0, hR0, hu⟩ := C.beta_reflect hR
  obtain ⟨v0, hS0, hv⟩ := C.beta_reflect hS
  subst u
  subst v
  have distinct0 : p ≠ q := by intro he; exact distinct (congrArg (C.edge :: ·) he)
  let a := afterR.reindex (((singleContraction hR0).residualSet [q]).map (C.edge :: ·))
    (fun z => (singleContraction hR).residualSet_prefix_members (singleContraction hR0)
      (pre := [C.edge]) (C.lookup t) rfl (z := z) (r := q))
  let b := afterS.reindex (((singleContraction hS0).residualSet [p]).map (C.edge :: ·))
    (fun z => (singleContraction hS).residualSet_prefix_members (singleContraction hS0)
      (pre := [C.edge]) (C.lookup t) rfl (z := z) (r := p))
  obtain ⟨x, a0, hx, hpa⟩ := C.parallel_reflect a
  obtain ⟨y, b0, hy, hpb⟩ := C.parallel_reflect b
  have hxy : y = x := C.plug_injective (hy.symm.trans hx)
  subst y
  have hpa' : afterR.paths = a0.paths.map (fun p => [C.edge] ++ p) := hpa
  have hpb' : afterS.paths = b0.paths.map (fun p => [C.edge] ++ p) := hpb
  by_cases inside : ∃ tail, T.val = [C.edge] ++ tail
  · obtain ⟨z, hz⟩ := inside
    have in1 : ∃ tail, T1.val = [C.edge] ++ tail := by
      by_cases ht : ∃ tail, T1.val = [C.edge] ++ tail
      · exact ht
      · have he := afterR.derivation.prefix_residual_outside_source hpa' T1 T ht h1
        exact False.elim (ht ⟨z, he.trans hz⟩)
    have in2 : ∃ tail, T2.val = [C.edge] ++ tail := by
      by_cases ht : ∃ tail, T2.val = [C.edge] ++ tail
      · exact ht
      · have he := afterS.derivation.prefix_residual_outside_source hpb' T2 T ht h2
        exact False.elim (ht ⟨z, he.trans hz⟩)
    obtain ⟨z1, hz1⟩ := in1
    obtain ⟨z2, hz2⟩ := in2
    subst w
    let t1 := C.redex_reflect T1 z1 hz1
    let t2 := C.redex_reflect T2 z2 hz2
    let pointed := C.redex_reflect T z hz
    have hlocal1 : a0.derivation.Residual t1 pointed :=
      (a0.derivation.prefix_residual_iff afterR.derivation (pre := [C.edge])
        (C.lookup u0) hpa' t1 pointed T1 T hz1 hz).mp h1
    have hlocal2 : b0.derivation.Residual t2 pointed :=
      (b0.derivation.prefix_residual_iff afterS.derivation (pre := [C.edge])
        (C.lookup v0) hpb' t2 pointed T2 T hz2 hz).mp h2
    obtain ⟨r, hr⟩ := ih hR0 hS0 distinct0 a0 b0 t1 t2 pointed hlocal1 hlocal2
    have hpaths : ((singleContraction hR).derivation.append afterR.derivation).paths =
        ((singleContraction hR0).derivation.append a0.derivation).paths.map (fun p => [C.edge] ++ p) := by
      change [C.edge :: p] ++ afterR.paths = ([p] ++ a0.paths).map (fun p => [C.edge] ++ p)
      simp only [hpa', List.map_cons, List.cons_append, List.nil_append]
    refine ⟨C.redex_lift r, ?_⟩
    exact (((singleContraction hR0).derivation.append a0.derivation).prefix_residual_iff
      ((singleContraction hR).derivation.append afterR.derivation) (pre := [C.edge])
      (C.lookup t) hpaths r pointed (C.redex_lift r) T rfl hz).mpr hr
  · exact creation_separation_outside_prefix hR hS distinct afterR afterS p q rfl rfl
      a0.paths b0.paths hpa' hpb' T1 T2 T h1 h2 inside

/-- AG Exercise 5.2.6, for arbitrary distinct initial contractions and the
 actual two residual developments of any given parallel-moves square. -/
theorem creation_separation_at (t : Term) (p q : Path) : CreationSeparationAt t p q := by
  induction p generalizing t q with
  | nil =>
    intro u v w hR hS distinct afterR afterS T1 T2 T h1 h2
    obtain ⟨body, argument, lookup, replace⟩ := hR
    simp only [subtermAt, Option.some.injEq] at lookup
    subst t
    simp only [replaceAt, Option.some.injEq] at replace
    subst u
    have hR : BetaAt (.app (.lam body) argument) [] (contract body argument) :=
      ⟨body, argument, rfl, rfl⟩
    exact root_creation_separation hR hS (fun he => distinct he.symm) afterR afterS T1 T2 T h1 h2
  | cons e p ih =>
    cases q with
    | nil =>
      intro u v w hR hS distinct afterR afterS T1 T2 T h1 h2
      obtain ⟨body, argument, lookup, replace⟩ := hS
      simp only [subtermAt, Option.some.injEq] at lookup
      subst t
      simp only [replaceAt, Option.some.injEq] at replace
      subst v
      have hS : BetaAt (.app (.lam body) argument) [] (contract body argument) :=
        ⟨body, argument, rfl, rfl⟩
      obtain ⟨r, hr⟩ := root_creation_separation hS hR distinct afterS afterR T2 T1 T h2 h1
      let sq : ParallelMovesSquare [e :: p] [[]] (.app (.lam body) argument) u
          (contract body argument) w := ⟨singleContraction hR, singleContraction hS, afterR, afterS⟩
      exact ⟨r, (sq.residual r T).mpr hr⟩
    | cons d q =>
      by_cases he : e = d
      · subst d
        cases t with
        | var i =>
          intro hR
          obtain ⟨b, a, hl, _⟩ := hR
          cases e <;> simp [subtermAt] at hl
        | lam b =>
          cases e with
          | body => exact SyntaxFrame.body.creation_separation (ih b q)
          | fn =>
            intro hR
            obtain ⟨b, a, hl, _⟩ := hR
            simp [subtermAt] at hl
          | arg =>
            intro hR
            obtain ⟨b, a, hl, _⟩ := hR
            simp [subtermAt] at hl
        | app f a =>
          cases e with
          | fn => exact (SyntaxFrame.fn a).creation_separation (ih f q)
          | arg => exact (SyntaxFrame.arg f).creation_separation (ih a q)
          | body =>
            intro hR
            obtain ⟨b, a, hl, _⟩ := hR
            simp [subtermAt] at hl
      · intro hR hS distinct afterR afterS T1 T2 T h1 h2
        have hd : DisjointPositions (e :: p) (d :: q) := by
          constructor
          · rintro ⟨tail, ht⟩
            exact he (List.cons.inj ht).1.symm
          · rintro ⟨tail, ht⟩
            exact he (List.cons.inj ht).1
        exact disjoint_creation_separation hR hS hd afterR afterS T1 T2 T h1 h2

theorem creation_separation (hR : BetaAt t p u) (hS : BetaAt t q v) (distinct : p ≠ q)
    (afterR : ParallelStep ((singleContraction hR).residualSet [q]) u w)
    (afterS : ParallelStep ((singleContraction hS).residualSet [p]) v w)
    (T1 : RedexOcc u) (T2 : RedexOcc v) (T : RedexOcc w)
    (h1 : afterR.derivation.Residual T1 T) (h2 : afterS.derivation.Residual T2 T) :
    ∃ T0 : RedexOcc t,
      ((singleContraction hR).derivation.append afterR.derivation).Residual T0 T :=
  creation_separation_at t p q hR hS distinct afterR afterS T1 T2 T h1 h2
end Lamping.Lambda

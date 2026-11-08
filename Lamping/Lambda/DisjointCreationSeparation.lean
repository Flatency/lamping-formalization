import Lamping.Lambda.SingletonPaths
import Lamping.Lambda.FiniteSelectionReindex
import Lamping.Lambda.CreationExterior
import Lamping.Lambda.ResidualComposition
namespace Lamping.Lambda

private theorem disjoint_no_common_descendant (hd : DisjointPositions p q)
    (hp : ∃ a, x=p++a) (hq : ∃ b, x=q++b) : False := by
  obtain ⟨a,ha⟩ := hp
  obtain ⟨b,hb⟩ := hq
  rcases List.prefix_or_prefix_of_prefix (show p <+: x from ⟨a,ha.symm⟩)
      (show q <+: x from ⟨b,hb.symm⟩) with ⟨s,hs⟩ | ⟨s,hs⟩
  · exact hd.1 ⟨s,hs.symm⟩
  · exact hd.2 ⟨s,hs.symm⟩

private theorem creation_region_outside (hd : DisjointPositions p q)
    (region : (∃ a, x=p++a) ∨ p=x++[.fn]) : ¬ ∃ a, x=q++a := by
  intro inside
  rcases region with region | region
  · exact disjoint_no_common_descendant hd region inside
  · obtain ⟨a,eq⟩ := inside
    apply hd.2
    exact ⟨a++[.fn],by simpa only [List.append_assoc] using region.trans (congrArg (·++[.fn]) eq)⟩

private theorem disjoint_creation_regions (hd : DisjointPositions p q)
    (hp : (∃ a, x=p++a) ∨ p=x++[.fn])
    (hq : (∃ a, x=q++a) ∨ q=x++[.fn]) : False := by
  rcases hq with inside | parent
  · exact creation_region_outside hd hp inside
  · rcases hp with ⟨a,inside⟩ | parent'
    · exact hd.1 ⟨a++[.fn],by simpa only [List.append_assoc] using parent.trans (congrArg (·++[.fn]) inside)⟩
    · exact hd.1 ⟨[],by simp [parent,parent']⟩

private theorem one_path_beta (d : Derivation t u) (paths : d.paths=[p]) : BetaAt t p u := by
  have valid := d.valid
  rw [paths] at valid
  cases valid with
  | cons step rest => cases rest; exact step

/-- Exercise5.2.6 for disjoint initial contraction sites, with arbitrary
realizations of both residual developments. Creation regions are disjoint;
no common-endpoint identification of histories is used. -/
theorem disjoint_creation_separation (hR : BetaAt t p u) (hS : BetaAt t q v)
    (hd : DisjointPositions p q)
    (afterR : ParallelStep ((singleContraction hR).residualSet [q]) u w)
    (afterS : ParallelStep ((singleContraction hS).residualSet [p]) v w)
    (T1 : RedexOcc u) (T2 : RedexOcc v) (T : RedexOcc w)
    (h1 : afterR.derivation.Residual T1 T) (h2 : afterS.derivation.Residual T2 T) :
    ∃ T0 : RedexOcc t, ((singleContraction hR).derivation.append afterR.derivation).Residual T0 T := by
  classical
  by_cases old : ∃ T0 : RedexOcc t,
      ((singleContraction hR).derivation.append afterR.derivation).Residual T0 T
  · exact old
  · exfalso
    let sq : ParallelMovesSquare [p] [q] t u v w := ⟨singleContraction hR,singleContraction hS,afterR,afterS⟩
    have fresh1 : ¬ ∃ r : RedexOcc t, (singleContraction hR).derivation.Residual r T1 := by
      rintro ⟨r,hr⟩
      exact old ⟨r,(Derivation.residual_append _ _ r T).mpr ⟨T1,hr,h1⟩⟩
    have fresh2 : ¬ ∃ r : RedexOcc t, (singleContraction hS).derivation.Residual r T2 := by
      rintro ⟨r,hr⟩
      exact old ⟨r,(sq.residual r T).mpr ((Derivation.residual_append _ _ r T).mpr ⟨T2,hr,h2⟩)⟩
    have region1 := hR.new_redex_locality T1 fresh1
    have region2 := hS.new_redex_locality T2 fresh2
    let a := afterR.reindex [q] (fun z => by
      rw [hR.disjoint_residualSet ⟨q,hS.redex⟩ hd]; exact List.mem_singleton.symm)
    let b := afterS.reindex [p] (fun z => by
      rw [hS.disjoint_residualSet ⟨p,hR.redex⟩ ⟨hd.2,hd.1⟩]; exact List.mem_singleton.symm)
    have apaths : afterR.paths=[q] := a.singleton_paths ⟨q,by
      obtain ⟨s,hs,hr⟩ := hR.disjoint_subterm hd ▸ hS.redex
      exact ⟨s,hs,hr⟩⟩ rfl
    have bpaths : afterS.paths=[p] := b.singleton_paths ⟨p,by
      rw [hS.disjoint_subterm ⟨hd.2,hd.1⟩]
      exact hR.redex⟩ rfl
    have hS' := one_path_beta afterR.derivation apaths
    have hR' := one_path_beta afterS.derivation bpaths
    have aeq : afterR.derivation=(singleContraction hS').derivation := Derivation.ext apaths
    have beq : afterS.derivation=(singleContraction hR').derivation := Derivation.ext bpaths
    rw [aeq] at h1
    rw [beq] at h2
    have eq1 := (hS'.outside_residual_iff T1 (creation_region_outside hd region1) T).mp h1
    have eq2 := (hR'.outside_residual_iff T2 (creation_region_outside ⟨hd.2,hd.1⟩ region2) T).mp h2
    rw [eq1] at region1
    rw [eq2] at region2
    exact disjoint_creation_regions hd region1 region2
end Lamping.Lambda


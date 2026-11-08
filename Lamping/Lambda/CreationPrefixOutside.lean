import Lamping.Lambda.ParallelScopes
import Lamping.Lambda.CreationExterior
import Lamping.Lambda.ResidualComposition
namespace Lamping.Lambda

/-- Two distinct contractions and their residual developments confined to a
 common subtree cannot jointly create a pointed redex outside that subtree. -/
 theorem creation_separation_outside_prefix
     (hR : BetaAt t p u) (hS : BetaAt t q v) (distinct : p ≠ q)
     (afterR : ParallelStep ((singleContraction hR).residualSet [q]) u w)
     (afterS : ParallelStep ((singleContraction hS).residualSet [p]) v w)
     (p0 q0 : Path) (hp : p = pre ++ p0) (hq : q = pre ++ q0)
     (as bs : List Path)
     (ha : afterR.paths = as.map (fun p => pre ++ p))
     (hb : afterS.paths = bs.map (fun p => pre ++ p))
     (T1 : RedexOcc u) (T2 : RedexOcc v) (T : RedexOcc w)
     (h1 : afterR.derivation.Residual T1 T) (h2 : afterS.derivation.Residual T2 T)
     (outside : ¬ ∃ tail, T.val = pre ++ tail) :
     ∃ T0 : RedexOcc t,
       ((singleContraction hR).derivation.append afterR.derivation).Residual T0 T := by
   classical
   by_cases old : ∃ T0 : RedexOcc t,
       ((singleContraction hR).derivation.append afterR.derivation).Residual T0 T
   · exact old
   · exfalso
     let sq : ParallelMovesSquare [p] [q] t u v w :=
       ⟨singleContraction hR, singleContraction hS, afterR, afterS⟩
     have fresh1 : ¬ ∃ r, (singleContraction hR).derivation.Residual r T1 := by
       rintro ⟨r, hr⟩
       exact old ⟨r, (Derivation.residual_append _ _ r T).mpr ⟨T1, hr, h1⟩⟩
     have fresh2 : ¬ ∃ r, (singleContraction hS).derivation.Residual r T2 := by
       rintro ⟨r, hr⟩
       exact old ⟨r, (sq.residual r T).mpr ((Derivation.residual_append _ _ r T).mpr ⟨T2, hr, h2⟩)⟩
     have eq1 := afterR.derivation.prefix_residual_outside_target ha T1 T outside h1
     have eq2 := afterS.derivation.prefix_residual_outside_target hb T2 T outside h2
     have region1 := hR.new_redex_locality T1 fresh1
     have region2 := hS.new_redex_locality T2 fresh2
     rw [eq1] at region1
     rw [eq2] at region2
     have parent1 : p = T.val ++ [.fn] := by
       rcases region1 with ⟨tail, he⟩ | he
       · exact False.elim (outside ⟨p0 ++ tail, by simpa only [hp, List.append_assoc] using he⟩)
       · exact he
     have parent2 : q = T.val ++ [.fn] := by
       rcases region2 with ⟨tail, he⟩ | he
       · exact False.elim (outside ⟨q0 ++ tail, by simpa only [hq, List.append_assoc] using he⟩)
       · exact he
     exact distinct (parent1.trans parent2.symm)
end Lamping.Lambda

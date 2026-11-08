import Lamping.Lambda.ApplicationDiamond
import Lamping.Lambda.RootApplicationIdentity
import Lamping.Lambda.RootCreation
import Lamping.Lambda.TagProjection
import Lamping.Lambda.ResidualComposition
namespace Lamping.Lambda

/-- Exercise5.2.6 when the first contraction is the outer root. Two middle
redex ancestors of one square endpoint force a genuine initial ancestor.
The argument tracks all application identities, including nonredexes. -/
theorem root_creation_separation
    (hR : BetaAt (.app (.lam body) argument) [] (contract body argument))
    (hS : BetaAt (.app (.lam body) argument) q v) (distinct : q≠[])
    (afterR : ParallelStep ((singleContraction hR).residualSet [q]) (contract body argument) w)
    (afterS : ParallelStep ((singleContraction hS).residualSet [[]]) v w)
    (T1 : RedexOcc (contract body argument)) (T2 : RedexOcc v) (T : RedexOcc w)
    (h1 : afterR.derivation.Residual T1 T) (h2 : afterS.derivation.Residual T2 T) :
    ∃ T0 : RedexOcc (.app (.lam body) argument),
      ((singleContraction hR).derivation.append afterR.derivation).Residual T0 T := by
  classical
  by_cases old : ∃ T0 : RedexOcc (.app (.lam body) argument),
      ((singleContraction hR).derivation.append afterR.derivation).Residual T0 T
  · exact old
  · exfalso
    have fresh : ¬ ∃ r : RedexOcc (.app (.lam body) argument),
        (rootContraction body argument).Residual r T1 := by
      rintro ⟨r,hr⟩
      apply old
      refine ⟨r,(Derivation.residual_append _ _ r T).mpr ⟨T1,?_,h1⟩⟩
      simpa only [rootContraction_eq_single hR] using hr
    obtain ⟨abody,inner,argumentLambda,potential⟩ := root_new_redex_source T1 fresh
    let sq : ParallelMovesSquare [[]] [q] (.app (.lam body) argument)
        (contract body argument) v w := ⟨singleContraction hR,singleContraction hS,afterR,afterS⟩
    let annotations := Marked.markAll ([[]]++[q]) (.app (.lam body) argument)
    obtain ⟨target,left,right⟩ := sq.tracking_diamond annotations (Marked.skeleton_markAll _ _).symm
    have all : Marked.EveryApplicationTagged annotations := Marked.everyApplicationTagged_markAllAt _ _ []
    have one : Marked.SingleTags annotations := Marked.singleTags_markAllAt _ _ []
    have targetOne := left.singleTags one
    change Marked.History ([]::afterR.paths) annotations target at left
    change Marked.History (q::afterS.paths) annotations target at right
    cases left with
    | @cons _ _ middle _ _ firstR restR =>
      have rootHistory := Marked.allRootTracking ([[]]++[q]) body argument
      have same := (Marked.History.cons firstR (.nil _)).deterministic rootHistory
      subst middle
      cases right with
      | @cons _ _ middleS _ _ firstS restS =>
        have guard := firstS.rootHeadGuard distinct (Marked.rootHeadGuard_markAll (F:=[[]]++[q]) potential)
        have middleErase := (singleContraction hS).derivation.tracking_erase
          (.cons firstS (.nil _)) (Marked.erase_markAll _ _)
        have markedT2 := firstS.everyApplicationTagged all
        obtain ⟨id,atT2⟩ := markedT2.redex_tag (by rw [middleErase]; exact T2.property)
        obtain ⟨a,historyA,eraseA,atA⟩ := h1
        have leftIncluded : ∀ p, p∈Marked.tracePositions T1.val (Marked.mark [] (contract body argument)) →
            p∈Marked.tracePositions ([.fn,.body]++T1.val)
              (Marked.allRootTarget ([[]]++[q]) body argument) := by
          intro p hp
          have eq := (Marked.initial_residual [] (contract body argument) T1 p).mp hp
          subst p
          exact Marked.allRoot_created_identity potential
        have sameLeft : (Marked.mark [] (contract body argument)).erase =
            (Marked.allRootTarget ([[]]++[q]) body argument).erase := by
          simp [Marked.erase_mark,Marked.allRootTarget,Marked.erase_contract,Marked.erase_markAllAt]
        have finalId := historyA.trace_inclusion restR sameLeft leftIncluded T.val atA
        obtain ⟨b,historyB,eraseB,atB⟩ := h2
        have rightIncluded : ∀ p, p∈Marked.tracePositions T2.val (Marked.mark [] v) →
            p∈Marked.tracePositions id middleS := by
          intro p hp
          have eq := (Marked.initial_residual [] v T2 p).mp hp
          subst p
          exact (Marked.mem_tagsAt _ _ _).mp atT2
        have finalOther := historyB.trace_inclusion restS
          ((Marked.erase_mark [] v).trans middleErase.symm) rightIncluded T.val atB
        have sameId := targetOne.trace_unique finalId finalOther
        subst id
        exact guard.no_redex atT2 (by rw [middleErase]; exact T2.property)
end Lamping.Lambda

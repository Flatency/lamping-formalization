import Lamping.Lambda.CreationPullback
import Lamping.Lambda.SingletonProjectionRow
import Lamping.Lambda.ResidualExtractionPeak
import Lamping.Lambda.ExtractionContexts
import Lamping.Lambda.StepProjectionHead
import Lamping.Lambda.StandardizationFactorization
namespace Lamping.Lambda

private theorem descendant_outside (hd : DisjointPositions p site)
    (inside : ∃ s, q=site++s) : ¬∃ r, q=p++r := by
  obtain ⟨s,hs⟩ := inside
  rintro ⟨r,hr⟩
  rcases List.prefix_or_prefix_of_prefix (show p <+: q from ⟨r,hr.symm⟩)
      (show site <+: q from ⟨s,hs.symm⟩) with ⟨a,ha⟩ | ⟨a,ha⟩
  · exact hd.1 ⟨a,ha.symm⟩
  · exact hd.2 ⟨a,ha.symm⟩

/-- Retain the actual source predecessor and its projection for inserting
the (2,1) core into an arbitrary longer actual row. -/
theorem disjoint_residual_pullback
    (R : BetaAt t p u) (S : BetaAt u s v) (T : BetaAt v z w)
    (S' : BetaAt t s' v') (T' : BetaAt v' z' w')
    {last : ParallelStep F w' w}
    (row : StepProjection (singleContraction R)
      (.cons (singleContraction S') (.single (singleContraction T')))
      (.cons (singleContraction S) (.single (singleContraction T))) last)
    (apart : DisjointPositions p site)
    (inside : Internal site (.cons (singleContraction S') (.single (singleContraction T'))))
    (V : BetaAt u a x)
    (predecessor : (singleContraction S).derivation.Residual ⟨a,V.redex⟩ ⟨z,T.redex⟩) :
    ∃ (a' : Path) (target : Term) (original : BetaAt t a' target)
      (G : List Path) (vertical : ParallelStep G target x),
      (singleContraction S').derivation.Residual ⟨a',original.redex⟩ ⟨z',T'.redex⟩ ∧
      Internal site (.single (singleContraction original)) ∧
      StepProjection (singleContraction R) (.single (singleContraction original))
        (.single (singleContraction V)) vertical := by
  have inS : ∃ q, s'=site++q := inside s' (by change s'∈[s',z']; simp)
  have inT : ∃ q, z'=site++q := inside z' (by change z'∈[s',z']; simp)
  have distinct : p≠s' := by
    intro he
    exact descendant_outside apart inS ⟨[],by simpa only [List.append_nil] using he.symm⟩
  obtain ⟨sq,hfirst,htop,_,hside,remaining⟩ := row.head_square
  cases sq with
  | mk first top side vertical =>
    cases hfirst
    cases htop
    have back := remaining.singleton_residual T' T
    have pred : side.derivation.Residual ⟨a,V.redex⟩ ⟨z,T.redex⟩ := by rw [hside]; exact predecessor
    obtain ⟨initial,throughR,throughS⟩ := creation_predecessor_pullback R S' distinct
      side vertical ⟨a,V.redex⟩ ⟨z',T'.redex⟩ ⟨z,T.redex⟩ pred back
    have inInitial : ∃ q, initial.val=site++q := by
      classical
      by_cases hi : ∃ q, initial.val=site++q
      · exact hi
      · obtain ⟨q,hq⟩ := inS
        have paths : (singleContraction S').derivation.paths=[q].map (fun q => site++q) := by
          change [s']=_
          simp only [List.map_cons,List.map_nil,hq]
        have he := (singleContraction S').derivation.prefix_residual_outside_source paths
          initial ⟨z',T'.redex⟩ hi throughS
        obtain ⟨q',hq'⟩ := inT
        exact False.elim (hi ⟨q',he.trans hq'⟩)
    have selection := R.outside_residualSet_singleton initial (descendant_outside apart inInitial)
    have member : a∈(singleContraction R).residualSet [initial.val] :=
      (Marked.mem_setResidualPositions _ _ _).mpr
        ⟨initial.val,List.mem_singleton_self _,((singleContraction R).residual_iff initial ⟨a,V.redex⟩).mp throughR⟩
    rw [selection] at member
    have name := List.mem_singleton.mp member
    have selected : (singleContraction R).residualSet [initial.val]=[a] := by rw [selection,name]
    obtain ⟨target,original⟩ := initial.contract_exists
    obtain ⟨G,last,projected⟩ := singleton_projection_row R original V selected
    refine ⟨initial.val,target,original,G,last,throughS,?_,projected⟩
    intro q hq
    change q∈[initial.val] at hq
    cases List.mem_singleton.mp hq
    exact inInitial

/-- The actual three-contraction core of LEV80 case (2,1). The disjoint
deletion and terminal residual deletion each extract once to the same
genuine source redex. This is a core peak, not full local confluence. -/
theorem extraction_disjoint_residual_peak
    (R : BetaAt t p u) (S : BetaAt u s v) (T : BetaAt v z w)
    (S' : BetaAt t s' v') (T' : BetaAt v' z' w')
    {last : ParallelStep F w' w}
    (row : StepProjection (singleContraction R)
      (.cons (singleContraction S') (.single (singleContraction T')))
      (.cons (singleContraction S) (.single (singleContraction T))) last)
    (apart : DisjointPositions p site)
    (inside : Internal site (.cons (singleContraction S') (.single (singleContraction T'))))
    (V : BetaAt u a x)
    (predecessor : (singleContraction S).derivation.Residual ⟨a,V.redex⟩ ⟨z,T.redex⟩) :
    ExtractionJoin
      (.of (.cons (singleContraction S') (.single (singleContraction T'))) (.cons S' (.single T')))
      (.of (.cons (singleContraction R) (.single (singleContraction V))) (.cons R (.single V))) := by
  obtain ⟨a',target,original,G,last,residual,internal,projected⟩ :=
    disjoint_residual_pullback R S T S' T' row apart inside V predecessor
  refine ⟨.of (.single (singleContraction original)) (.single original),Extraction.single ?_,Extraction.single ?_⟩
  · exact ExtractionStep.residual (.nil t) (.nil t) S' T' original residual
  · exact ExtractionStep.disjoint (.nil t) (.nil t) R _ (.single original)
      _ (.single V) last projected (by change 0<1; omega) site apart internal

end Lamping.Lambda

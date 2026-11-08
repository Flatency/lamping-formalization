import Lamping.Lambda.CopyRegionCases
import Lamping.Lambda.ExtractionChurchRosser
import Lamping.Lambda.ExtractionStandardness
namespace Lamping.Lambda

private theorem represented_run {r : ExtractionRun m} {a : RedexWithHistory m}
    (last : BetaAt a.target a.redex.val r.target) (ordinary : Atomic a.history)
    (history : r.history=a.history.append (.single (singleContraction last))) :
    r=.of (a.history.append (.single (singleContraction last))) (ordinary.append (.single last)) := by
  apply ExtractionRun.ext_paths
  exact congrArg (fun h => h.derivation.paths) history

/-- AG5.2.9 for the actual Copy relation and actual four extraction rules.
Only the two pointed prefixes must be standard; full runs may be nonstandard. -/
theorem Atomic.copy_standard_join {σ : ParallelHistory m v} (targetAtomic : Atomic σ)
    (point : RedexOcc v) (a : RedexWithHistory m)
    (copy : Copy a ⟨v,σ,point⟩) (source : RunRepresents r a)
    (target : RunRepresents s ⟨v,σ,point⟩)
    (sourceStandard : Standard a.history) (targetStandard : Standard σ) : ExtractionJoin r s := by
  induction targetAtomic with
  | nil m =>
    rcases a with ⟨A,sourceHistory,sourcePoint⟩
    obtain ⟨last,ordinary,history⟩ := source
    dsimp only at ordinary last history
    cases ordinary with
    | nil =>
      have runEq := represented_run (a:=⟨m,.nil m,sourcePoint⟩) last (.nil m) history
      refine ⟨.of (.single (singleContraction last)) (.single last),?_,?_⟩
      · exact Eq.mp (congrArg (fun z => Extraction r z) runEq) (.refl r)
      · exact copy.initial_extraction sourcePoint _ target last
    | cons head rest =>
      let old : RedexOcc m := ⟨_,head.redex⟩
      have impossible := copy.source_head_deleted head _ rfl old
      exact False.elim (impossible ((Derivation.residual_nil old old).mpr rfl))
  | @cons m q t v tail R tailAtomic ih =>
    let b : RedexWithHistory t := ⟨v,tail,point⟩
    obtain ⟨targetLast,_,targetHistory⟩ := target
    let targetTailRun : ExtractionRun t := .of (tail.append (.single (singleContraction targetLast)))
      (tailAtomic.append (.single targetLast))
    have targetTailRep : RunRepresents targetTailRun b := ⟨targetLast,tailAtomic,rfl⟩
    have targetEq : s=targetTailRun.prepend (.single (singleContraction R)) (.single R) := by
      apply ExtractionRun.ext_paths
      change s.history.derivation.paths=_
      rw [targetHistory]
      rfl
    have tailStandard : Standard tail := targetStandard.suffix (ρ:=.single (singleContraction R)) (σ:=tail)
    rcases a with ⟨A,sourceHistory,sourcePoint⟩
    let a : RedexWithHistory m := ⟨A,sourceHistory,sourcePoint⟩
    obtain ⟨last,ordinary,history⟩ := source
    have sourceRep : RunRepresents r a := ⟨last,ordinary,history⟩
    have sourceEq := represented_run last ordinary history
    dsimp only at ordinary last history
    cases ordinary with
    | nil =>
      refine ⟨.of (.single (singleContraction last)) (.single last),?_,?_⟩
      · exact Eq.mp (congrArg (fun z => Extraction r z) sourceEq) (.refl r)
      · exact copy.initial_extraction sourcePoint _ ⟨targetLast,.cons R tailAtomic,targetHistory⟩ last
    | @cons m p mid A sourceTail Q sourceTailAtomic =>
      have sourceAtomic : Atomic (.cons (singleContraction Q) sourceTail) := .cons Q sourceTailAtomic
      by_cases sameHead : p=q
      · subst p
        have sameTarget := Q.unique R
        cases sameTarget
        let a' : RedexWithHistory t := ⟨A,sourceTail,sourcePoint⟩
        let sourceTailRun : ExtractionRun t := .of (sourceTail.append (.single (singleContraction last)))
          (sourceTailAtomic.append (.single last))
        have sourceTailRep : RunRepresents sourceTailRun a' := ⟨last,sourceTailAtomic,rfl⟩
        have sourceTailEq : r=sourceTailRun.prepend (.single (singleContraction R)) (.single R) := by
          apply ExtractionRun.ext_paths
          change r.history.derivation.paths=_
          rw [history]
          rfl
        have stripped : Copy a' b := copy.cancel_beta_head R a' b
        have sourceTailStandard : Standard sourceTail := sourceStandard.suffix
          (ρ:=.single (singleContraction Q)) (σ:=sourceTail)
        have joined := ih point a' stripped sourceTailRep targetTailRep sourceTailStandard tailStandard
        rw [sourceTailEq,targetEq]
        exact joined.prepend (.single (singleContraction R)) (.single R)
      · have protection := copy.protected_target_head Q R sourceTail tail rfl rfl
          sourceAtomic (.cons R tailAtomic) sourceStandard targetStandard sameHead
        obtain ⟨right,cut,cutAt,_,_⟩ := protection
        have finish (small : ExtractionRun m) (pruned : Pruning r small)
            (projected : ExtractionRun t) (d : RedexWithHistory t)
            (dRep : RunRepresents projected d) (dStandard : Standard d.history) (dCopy : Copy d b)
            (back : Extraction (projected.prepend (.single (singleContraction R)) (.single R)) small) :
            ExtractionJoin r s := by
          have joined := (ih point d dCopy dRep targetTailRep dStandard tailStandard).prepend
            (.single (singleContraction R)) (.single R)
          obtain ⟨z,left,rightJoin⟩ := joined
          obtain ⟨common,smallToCommon,zToCommon⟩ := extraction_church_rosser m back left
          refine ⟨common,pruned.extraction.trans smallToCommon,?_⟩
          rw [targetEq]
          exact rightJoin.trans zToCommon
        have reduced (small : ExtractionRun m) (pruned : Pruning r small) :
            ∃ c : RedexWithHistory m, RunRepresents small c ∧ Standard c.history ∧
              Copy c ⟨v,.cons (singleContraction R) tail,point⟩ := by
          obtain ⟨c,cRep⟩ := small.represents_exists (pruned.extraction.positive sourceRep.positive)
          obtain ⟨c',c'Rep,c'Standard⟩ := pruned.extraction.prefix_standard ⟨a,sourceRep,sourceStandard⟩
          have same := cRep.unique c'Rep
          refine ⟨c,cRep,?_,(pruned.copy a c sourceRep cRep).trans copy⟩
          rw [same]
          exact c'Standard
        rcases sourcePoint.compare cut with equal | before | after
        · have samePosition := congrArg Subtype.val equal
          have forbidden := copy.ne_protected_target_head R tail rfl right
          exact False.elim (forbidden (samePosition.trans cutAt))
        · rw [cutAt] at before
          exact copy.common_of_left_pointed right before sourceRep ⟨targetLast,.cons R tailAtomic,targetHistory⟩
        · have afterCut : LeftOf q sourcePoint.val := by simpa only [cutAt] using after
          have casesRegion := cut.after_regions sourcePoint after
          rw [cutAt] at casesRegion
          rcases casesRegion with function | argument | disjoint
          · obtain ⟨localLast,atFunction⟩ := function
            have blocks := sourceAtomic.standard_protected_blocks R right sourceStandard
            obtain ⟨V,W,fnHistory,initial,fnAtomic,fnInside,pruned⟩ := blocks.prune_function_pointed sourceAtomic last atFunction
            let small : ExtractionRun m := .of (fnHistory.append (.single (singleContraction initial))) (fnAtomic.append (.single initial))
            have prune : Pruning r small := by rw [sourceEq]; exact pruned
            obtain ⟨c,cRep,cStandard,cCopy⟩ := reduced small prune
            have smallInside : Internal (q++[.fn]) small.history := by
              intro pos hp
              change pos∈(fnHistory.append (.single (singleContraction initial))).derivation.paths at hp
              rw [ParallelHistory.derivation_append] at hp
              change pos∈fnHistory.derivation.paths++[sourcePoint.val] at hp
              rcases List.mem_append.mp hp with earlier | final
              · exact fnInside pos earlier
              · exact ⟨localLast,(List.mem_singleton.mp final).trans atFunction⟩
            obtain ⟨projected,d,dRep,dStandard,dCopy,back⟩ := cCopy.project_region_run R c b cRep cStandard (.inr rfl) smallInside
            exact finish small prune projected d dRep dStandard dCopy back
          · obtain ⟨localLast,atArgument⟩ := argument
            have blocks := sourceAtomic.standard_protected_blocks R right sourceStandard
            obtain ⟨W,argHistory,argAtomic,argInside,pruned⟩ := blocks.prune_argument_pointed sourceAtomic last atArgument
            let small : ExtractionRun m := .of argHistory argAtomic
            have prune : Pruning r small := by rw [sourceEq]; exact pruned
            obtain ⟨c,cRep,cStandard,cCopy⟩ := reduced small prune
            obtain ⟨projected,d,dRep,dStandard,dCopy,back⟩ := cCopy.project_argument_run R c b cRep cStandard argInside
            exact finish small prune projected d dRep dStandard dCopy back
          · obtain ⟨site,apart,W,otherHistory,otherAtomic,_,otherInside,pruned⟩ :=
              right.prune_right_pointed sourceAtomic last afterCut disjoint
            let small : ExtractionRun m := .of otherHistory otherAtomic
            have prune : Pruning r small := by rw [sourceEq]; exact pruned
            obtain ⟨c,cRep,cStandard,cCopy⟩ := reduced small prune
            obtain ⟨projected,d,dRep,dStandard,dCopy,back⟩ := cCopy.project_region_run R c b cRep cStandard (.inl apart) otherInside
            exact finish small prune projected d dRep dStandard dCopy back

theorem Copy.standard_common_extraction (copy : Copy a b)
    (source : RunRepresents r a) (target : RunRepresents s b)
    (sourceStandard : Standard a.history) (targetStandard : Standard b.history) : ExtractionJoin r s := by
  have ordinary : Atomic b.history := by
    obtain ⟨_,ordinary,_⟩ := target
    exact ordinary
  exact ordinary.copy_standard_join b.redex a copy source target sourceStandard targetStandard

end Lamping.Lambda


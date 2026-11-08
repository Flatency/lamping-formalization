import Lamping.Lambda.ArgumentCommutation
import Lamping.Lambda.ArgumentResidualScope
import Lamping.Lambda.ArgumentHeadPreservation
import Lamping.Lambda.PointedRuns
import Lamping.Lambda.StepProjectionHead
import Lamping.Lambda.AtomicProjection
import Lamping.Lambda.ProjectionSingletonSelection
import Lamping.Lambda.ExtractionTermination
namespace Lamping.Lambda
/-- A specified ordinary local schedule can be realized after reductions in
other copies, because those real reductions preserve the whole local term. -/
theorem Atomic.realize_after_apart {σ : ParallelHistory t u} (_atomic : Atomic σ)
    (inside : Internal site σ) {ρ : ParallelHistory t v} (outside : ApartHistory site ρ)
    (lookup : subtermAt t site=some a) :
    ∃ (w : Term) (copy : ParallelHistory v w), Atomic copy ∧ copy.derivation.paths=σ.derivation.paths := by
  obtain ⟨ps,b,paths,localHistory,_⟩ := inside.extract lookup
  have same : subtermAt v site=some a := (ρ.derivation.valid.subterm_fixed_apart outside.paths_apart).trans lookup
  obtain ⟨w,history,_⟩ := localHistory.prefix_lift same
  obtain ⟨copy,copyAtomic,copyPaths⟩ := history.atomic
  exact ⟨w,copy,copyAtomic,copyPaths.trans paths.symm⟩

private theorem chosen_residual_apart (head : BetaAt t chosen u)
    (inside : ∃ q, chosen=site++q)
    (valid : ∀ p∈F, ∃ z, subtermAt t p=some z ∧ IsRedex z)
    (scope : ∀ r : RedexOcc t, r.val∈F → r.val=chosen ∨ DisjointPositions site r.val)
    (z : RedexOcc u) (member : z.val∈(singleContraction head).residualSet F) :
    DisjointPositions site z.val := by
  obtain ⟨old,selected,trace⟩ := (Marked.mem_setResidualPositions F _ z.val).mp member
  let r : RedexOcc t := ⟨old,valid old selected⟩
  have residual := ((singleContraction head).residual_iff r z).mpr trace
  rcases scope r selected with same | apart
  · have impossible := (Marked.mem_setResidualPositions [chosen] _ z.val).mpr
      ⟨r.val,by simp [same],((singleContraction head).residual_iff r z).mp residual⟩
    rw [(singleContraction head).complete.2] at impossible
    exact False.elim (List.not_mem_nil impossible)
  · obtain ⟨q,eq⟩ := inside
    have hd : DisjointPositions chosen r.val := by rw [eq]; exact apart.descend_left q
    have fixed := (head.disjoint_residual_iff r hd z).mp residual
    rw [←fixed]; exact apart

/-- The first full parallelization selects the specified copy head and no
other selected occurrence lies in that copy subtree. This follows from the
actual argument residual classification, not a factorization certificate. -/
theorem BetaAt.argument_selection_scope (R : BetaAt t p u)
    (lookup : subtermAt t p=some (.app (.lam b) a))
    (s : RedexOcc t) (source : s.val=(p++[.arg])++q)
    (occurs : ArgumentOccurrence b occ) :
    ∃ chosen : RedexOcc u, chosen.val=(p++occ)++q ∧
      chosen.val∈(singleContraction R).residualSet [s.val] ∧
      ∀ r : RedexOcc u, r.val∈(singleContraction R).residualSet [s.val] →
        r.val=chosen.val ∨ DisjointPositions (p++occ) r.val := by
  obtain ⟨chosen,same,alive⟩ := R.argument_residual_exists lookup s source occurs
  have selected : chosen.val∈(singleContraction R).residualSet [s.val] := by
    apply ((singleContraction R).mem_residualSet_iff (by
      intro z hz; cases List.mem_singleton.mp hz; exact s.property) chosen).mpr
    exact ⟨s,by simp,alive⟩
  refine ⟨chosen,same,selected,?_⟩
  intro r member
  obtain ⟨old,oldMember,residual⟩ := ((singleContraction R).mem_residualSet_iff (by
    intro z hz; cases List.mem_singleton.mp hz; exact s.property) r).mp member
  have oldSame : old=s := Subtype.ext (List.mem_singleton.mp oldMember)
  subst old
  obtain ⟨other,otherOccurs,atOther⟩ := R.argument_residual_source lookup s source r residual
  by_cases eq : occ=other
  · exact Or.inl (by rw [same,atOther,eq])
  · exact Or.inr (by rw [atOther]; exact ((occurs.context_disjoint otherOccurs eq p).symm.descend_left q).symm)
end Lamping.Lambda
namespace Lamping.Lambda
private theorem projection_uncons {first : ParallelStep F t u} {top : ParallelStep H t v}
    {rest : ParallelHistory v x} {full : ParallelHistory u z} {last : ParallelStep G x z}
    (row : StepProjection first (.cons top rest) full last) :
    ∃ (mid : Term) (tail : ParallelHistory mid z) (sq : ParallelMovesSquare F H t u v mid),
      sq.first=first ∧ sq.second=top ∧ full=.cons sq.afterFirst tail ∧
      StepProjection sq.afterSecond rest tail last := by
  cases row with
  | cons sq tail => exact ⟨_,_,sq,rfl,rfl,rfl,tail⟩

/-- A full actual argument projection admits the specified ordinary-copy
schedule first. Remaining steps are constructed and act only on other copies. -/
theorem Atomic.argument_projection_factor {original : ParallelHistory t v}
    (ordinary : Atomic original) (vertical : ParallelStep F t u) (selected : F=[p])
    (lookup : subtermAt t p=some (.app (.lam b) a)) (occurs : ArgumentOccurrence b occ)
    (qs : List Path) (originalPaths : original.derivation.paths=qs.map (fun q => (p++[.arg])++q))
    {copy : ParallelHistory u w} (copyAtomic : Atomic copy)
    (copyPaths : copy.derivation.paths=qs.map (fun q => (p++occ)++q))
    {full : ParallelHistory u z} {last : ParallelStep G v z}
    (row : StepProjection vertical original full last) :
    ∃ other : ParallelHistory w z, PermEq full (copy.append other) ∧ ApartHistory (p++occ) other := by
  induction ordinary generalizing F u p b a occ qs w z G with
  | nil t =>
    have empty : qs=[] := by
      cases qs with
      | nil => rfl
      | cons q qs => cases originalPaths
    subst qs
    cases copyAtomic with
    | nil => cases row; exact ⟨.nil _,.refl _,.nil _⟩
    | cons head tail => change _::_=[] at copyPaths; cases copyPaths
  | @cons t s mid v original S oldAtomic ih =>
    cases qs with
    | nil => change _::_=[] at originalPaths; cases originalPaths
    | cons q qs =>
      change s::original.derivation.paths=((p++[.arg])++q)::qs.map (fun r => (p++[.arg])++r) at originalPaths
      obtain ⟨atOriginal,tailPaths⟩ := List.cons.inj originalPaths
      subst s
      cases copyAtomic with
      | nil => change []=_::_ at copyPaths; cases copyPaths
      | @cons u c copyMid w copy T copyAtomic =>
        change c::copy.derivation.paths=((p++occ)++q)::qs.map (fun r => (p++occ)++r) at copyPaths
        obtain ⟨atCopy,copyTailPaths⟩ := List.cons.inj copyPaths
        subst c
        subst F
        let root : RedexOcc t := ⟨p,⟨.app (.lam b) a,lookup,True.intro⟩⟩
        obtain ⟨R,verticalEq⟩ := vertical.eq_single_contraction root rfl
        subst vertical
        obtain ⟨fullMid,fullTail,square,firstEq,secondEq,fullEq,tailRow⟩ := projection_uncons row
        rcases square with ⟨firstVertical,firstOriginal,projected,remainingRoot⟩
        simp only at firstEq secondEq fullEq tailRow
        subst firstVertical
        subst firstOriginal
        subst full
        let sq := (⟨singleContraction R,singleContraction S,projected,remainingRoot⟩ :
          ParallelMovesSquare [p] [(p++[.arg])++q] t u mid fullMid)
        have finish : ∃ other : ParallelHistory w z,
            PermEq (.cons projected fullTail) ((ParallelHistory.cons (singleContraction T) copy).append other) ∧
            ApartHistory (p++occ) other := by
          have originalInside : Internal (p++[.arg]) (ParallelHistory.single (singleContraction S)) := by
            intro r hr
            change r∈[((p++[.arg])++q)] at hr
            exact ⟨q,List.mem_singleton.mp hr⟩
          obtain ⟨a',_,R',newLookup⟩ := (ParallelHistory.single (singleContraction S)).argument_root_exists lookup originalInside
          have rootSelection : (singleContraction S).residualSet [p]=[p] :=
            S.outside_residualSet_singleton root (by
              rintro ⟨suffix,eq⟩
              change p=(((p++[.arg])++q)++suffix) at eq
              have lengths := congrArg List.length eq
              simp only [List.length_append,List.length_singleton] at lengths
              omega)
          obtain ⟨chosen,chosenAt,chosenMember,scope⟩ :=
            R.argument_selection_scope lookup ⟨(p++[.arg])++q,S.redex⟩ rfl occurs
          have chosenEq : chosen=⟨(p++occ)++q,T.redex⟩ := Subtype.ext chosenAt
          subst chosen
          have fullValid : ∀ r∈(singleContraction R).residualSet [(p++[.arg])++q],
              ∃ child,subtermAt u r=some child ∧ IsRedex child :=
            fun r hr => (singleContraction R).residualSet_valid r hr
          obtain ⟨copyMid',first,remaining,split,_⟩ :=
            sq.afterFirst.selected_factor_apart ⟨(p++occ)++q,T.redex⟩ chosenMember ⟨q,rfl⟩ fullValid scope
          have sameMiddle := first.unique T
          subst copyMid'
          have remainingScope := chosen_residual_apart first ⟨q,rfl⟩ fullValid scope
          have remainingValid : ∀ r∈(singleContraction first).residualSet ((singleContraction R).residualSet [(p++[.arg])++q]),
              ∃ child,subtermAt copyMid r=some child ∧ IsRedex child :=
            fun r hr => (singleContraction first).residualSet_valid r hr
          have otherFirst : ApartHistory (p++occ) (ParallelHistory.single remaining) :=
            .cons remaining (.nil _) remainingValid remainingScope (.nil _)
          have initialCopy : subtermAt u (p++occ)=some (rename (fun i => i+binderDepth occ) a) := by
            rw [subtermAt_append,R.contract_lookup lookup,Option.bind_some]
            exact argument_copy occurs a
          obtain ⟨localTarget,_,_,copyLookup⟩ := T.prefix_reflect initialCopy
          have copyInside : Internal (p++occ) copy := by
            intro r hr
            rw [copyTailPaths] at hr
            obtain ⟨r,_,same⟩ := List.mem_map.mp hr
            exact ⟨r,same.symm⟩
          obtain ⟨copyEnd,copyAfter,copyAfterAtomic,copyAfterPaths⟩ :=
            copyAtomic.realize_after_apart copyInside otherFirst copyLookup
          obtain ⟨otherTail,tailPerm,otherTailApart⟩ :=
            ih sq.afterSecond rootSelection newLookup occurs qs tailPaths copyAfterAtomic
              (copyAfterPaths.trans copyTailPaths) tailRow
          have copiedInside : Internal (p++occ) copyAfter := by
            intro r hr; exact copyInside r (by rw [←copyAfterPaths]; exact hr)
          obtain ⟨copyEnd',copyBefore,otherAfter,beforeAtomic,beforePaths,commute,otherAfterApart⟩ :=
            otherFirst.pull_inside copyAfterAtomic copiedInside
          have beforeSchedule : copyBefore.derivation.paths=copy.derivation.paths := beforePaths.trans copyAfterPaths
          have sameEnd : copyEnd'=w := by
            have firstValid := copyBefore.derivation.valid
            rw [beforeSchedule] at firstValid
            exact firstValid.deterministic copy.derivation.valid
          subst copyEnd'
          have sameBefore := beforeAtomic.paths_injective copyAtomic beforeSchedule
          subst copyBefore
          refine ⟨otherAfter.append otherTail,?_,otherAfterApart.append otherTailApart⟩
          have firstPerm := split.append fullTail
          have restPerm := PermEq.prepend (ParallelHistory.single (singleContraction T))
            (PermEq.prepend (ParallelHistory.single remaining) tailPerm)
          have exchange := PermEq.prepend (ParallelHistory.single (singleContraction T)) (commute.append otherTail)
          exact .trans (by simpa only [ParallelHistory.append_assoc,ParallelHistory.append,ParallelHistory.single] using firstPerm)
            (.trans (by simpa only [ParallelHistory.append_assoc,ParallelHistory.append,ParallelHistory.single] using restPerm)
              (by simpa only [ParallelHistory.append_assoc,ParallelHistory.append,ParallelHistory.single] using exchange))
        exact finish
end Lamping.Lambda

namespace Lamping.Lambda
/-- The source ArgumentLift's exact local paths suffice for every actual
full projection, not just a newly chosen realization of its parallelization. -/
theorem ArgumentLift.factor_projection {R : BetaAt t p u} {σ : ParallelHistory u v}
    {original : ParallelHistory t w} (lift : ArgumentLift R σ original)
    (copyAtomic : Atomic σ) (originalAtomic : Atomic original)
    {full : ParallelHistory u z} {last : ParallelStep F w z}
    (row : StepProjection (singleContraction R) original full last) :
    ∃ other : ParallelHistory v z, PermEq full (σ.append other) ∧ ApartHistory (p++lift.occurrence) other :=
  originalAtomic.argument_projection_factor (singleContraction R) rfl lift.redex lift.isVariable
    lift.localPaths lift.original_paths copyAtomic lift.copy_paths row

theorem ArgumentLift.parallelized_factor {R : BetaAt t p u} {σ : ParallelHistory u v}
    {original : ParallelHistory t w} (lift : ArgumentLift R σ original)
    (copyAtomic : Atomic σ) (originalAtomic : Atomic original) :
    ∃ (z : Term) (F : List Path) (full : ParallelHistory u z) (last : ParallelStep F w z)
      (other : ParallelHistory v z),
      StepProjection (singleContraction R) original full last ∧
      PermEq full (σ.append other) ∧ ApartHistory (p++lift.occurrence) other := by
  obtain ⟨z,F,full,last,row⟩ := lift.parallelization
  obtain ⟨other,factor,apart⟩ := lift.factor_projection copyAtomic originalAtomic row
  exact ⟨z,F,full,last,other,row,factor,apart⟩

/-- Pointed prefixes before the chosen final contraction have a common Copy
successor. Both extension legs are actual residuals; the two original pointed
histories need not themselves stand in either Copy direction. -/
theorem argument_pointed_join (R : BetaAt t p u)
    (lookup : subtermAt t p=some (.app (.lam b) a)) (occurs : ArgumentOccurrence b occ)
    (original : ParallelHistory t v) (ordinary : Atomic original)
    (copy : ParallelHistory u w) (copyAtomic : Atomic copy)
    (qs : List Path)
    (originalPaths : original.derivation.paths=qs.map (fun q => (p++[.arg])++q))
    (copyPaths : copy.derivation.paths=qs.map (fun q => (p++occ)++q))
    (r : RedexOcc v) (s : RedexOcc w)
    (originalLast : r.val=(p++[.arg])++q) (copyLast : s.val=(p++occ)++q)
    (pre : ParallelHistory m t) :
    ∃ common : RedexWithHistory m,
      Copy ⟨v,pre.append original,r⟩ common ∧
      Copy ⟨w,(pre.append (.single (singleContraction R))).append copy,s⟩ common := by
  obtain ⟨z,G,full,last,row⟩ := StepProjection.exists_projection (singleContraction R) original
  obtain ⟨other,factor,otherApart⟩ := ordinary.argument_projection_factor (singleContraction R) rfl
    lookup occurs qs originalPaths copyAtomic copyPaths row
  have copyInside : ∃ tail, s.val=(p++occ)++tail := ⟨q,copyLast⟩
  obtain ⟨target,targetAt,copyResidual⟩ := otherApart.inside_survives s copyInside
  have originalInside : Internal (p++[.arg]) original := by
    intro r hr
    rw [originalPaths] at hr
    obtain ⟨r,_,same⟩ := List.mem_map.mp hr
    exact ⟨r,same.symm⟩
  let root : RedexOcc t := ⟨p,⟨.app (.lam b) a,lookup,True.intro⟩⟩
  have rootSelected : G=[p] := row.final_selection_singleton rfl root rfl ordinary originalInside (by
    rintro ⟨tail,eq⟩
    have lengths := congrArg List.length eq
    simp only [List.length_append,List.length_singleton] at lengths
    omega)
  subst G
  obtain ⟨a',_,newLookup,_,_⟩ := original.argument_head_preserved lookup originalInside
  let remainingRoot : RedexOcc v := ⟨p,⟨.app (.lam b) a',newLookup,True.intro⟩⟩
  obtain ⟨remaining,lastEq⟩ := last.eq_single_contraction remainingRoot rfl
  have originalResidual : last.derivation.Residual r target := by
    rw [lastEq]
    apply (remaining.argument_residual_iff newLookup r originalLast target).mpr
    exact ⟨occ,occurs,targetAt.trans copyLast⟩
  let common : RedexWithHistory m := ⟨z,(pre.append (.single (singleContraction R))).append full,target⟩
  refine ⟨common,⟨.single last,?_,?_⟩,⟨other,?_,copyResidual⟩⟩
  · simpa only [common,ParallelHistory.append_assoc] using (PermEq.prepend pre row.permutation).symm
  · simpa only [ParallelHistory.single_derivation] using originalResidual
  · simpa only [common,ParallelHistory.append_assoc] using
      PermEq.prepend (pre.append (.single (singleContraction R))) factor.symm
end Lamping.Lambda

namespace Lamping.Lambda
private theorem nonempty_last (xs : List α) (nonempty : xs≠[]) :
    ∃ (ys : List α) (last : α), xs=ys++[last] := by
  cases eq : xs.reverse with
  | nil =>
    have empty := congrArg List.reverse eq
    simp only [List.reverse_reverse,List.reverse_nil] at empty
    exact False.elim (nonempty empty)
  | cons last rest =>
    refine ⟨rest.reverse,last,?_⟩
    have h := congrArg List.reverse eq
    simpa only [List.reverse_reverse,List.reverse_cons] using h

private theorem append_singleton_injective (h : xs++[a]=ys++[b]) : xs=ys ∧ a=b := by
  have reversed := congrArg List.reverse h
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] at reversed
  obtain ⟨last,same⟩ := List.cons.inj reversed
  refine ⟨?_,last⟩
  have h := congrArg List.reverse same
  simpa only [List.reverse_reverse] using h

/-- Full source coverage of extraction (iv): every pair of pointed runs
represented by its two ordinary sides has a common genuine Copy successor. -/
theorem ArgumentLift.pointed_join {R : BetaAt t p u} {copy : ParallelHistory u v}
    {original : ParallelHistory t w} (lift : ArgumentLift R copy original)
    (copyAtomic : Atomic copy) (originalAtomic : Atomic original) (positive : 0<copy.length)
    (pre : ParallelHistory m t) (preAtomic : Atomic pre)
    (a b : RedexWithHistory m)
    (originalRep : RunRepresents (.of (pre.append original) (preAtomic.append originalAtomic)) a)
    (copyRep : RunRepresents (.of ((pre.append (.single (singleContraction R))).append copy)
      ((preAtomic.append (.single R)).append copyAtomic)) b) :
    ∃ common : RedexWithHistory m, Copy a common ∧ Copy b common := by
  have localNonempty : lift.localPaths≠[] := by
    intro empty
    have lengths := congrArg List.length lift.copy_paths
    rw [copyAtomic.paths_length,empty,List.map_nil] at lengths
    change copy.length=0 at lengths
    omega
  obtain ⟨qs,lastPath,localPaths⟩ := nonempty_last lift.localPaths localNonempty
  obtain ⟨copyMid,copyLast,copyPre,S,copyPreAtomic,copyEq⟩ := copyAtomic.last positive
  have originalPositive : 0<original.length := by rw [lift.length copyAtomic originalAtomic]; exact positive
  obtain ⟨originalMid,originalLast,originalPre,T,originalPreAtomic,originalEq⟩ := originalAtomic.last originalPositive
  have copyPaths := lift.copy_paths
  conv at copyPaths => lhs; rw [copyEq,ParallelHistory.derivation_append]
  rw [localPaths,List.map_append,List.map_cons,List.map_nil] at copyPaths
  change copyPre.derivation.paths++[copyLast]=
    qs.map (fun q => (p++lift.occurrence)++q)++[(p++lift.occurrence)++lastPath] at copyPaths
  obtain ⟨copyPrefixPaths,copyLastAt⟩ := append_singleton_injective copyPaths
  have originalPaths := lift.original_paths
  conv at originalPaths => lhs; rw [originalEq,ParallelHistory.derivation_append]
  rw [localPaths,List.map_append,List.map_cons,List.map_nil] at originalPaths
  change originalPre.derivation.paths++[originalLast]=
    qs.map (fun q => (p++[.arg])++q)++[(p++[.arg])++lastPath] at originalPaths
  obtain ⟨originalPrefixPaths,originalLastAt⟩ := append_singleton_injective originalPaths
  let originalPointed : RedexWithHistory m := ⟨originalMid,pre.append originalPre,⟨originalLast,T.redex⟩⟩
  let copyPointed : RedexWithHistory m := ⟨copyMid,(pre.append (.single (singleContraction R))).append copyPre,⟨copyLast,S.redex⟩⟩
  have representsOriginal : RunRepresents (.of (pre.append original) (preAtomic.append originalAtomic)) originalPointed := by
    refine ⟨T,preAtomic.append originalPreAtomic,?_⟩
    change pre.append original=(pre.append originalPre).append (.single (singleContraction T))
    rw [originalEq,ParallelHistory.append_assoc]
  have representsCopy : RunRepresents (.of ((pre.append (.single (singleContraction R))).append copy)
      ((preAtomic.append (.single R)).append copyAtomic)) copyPointed := by
    refine ⟨S,(preAtomic.append (.single R)).append copyPreAtomic,?_⟩
    change (pre.append (.single (singleContraction R))).append copy=
      ((pre.append (.single (singleContraction R))).append copyPre).append (.single (singleContraction S))
    simp only [copyEq,ParallelHistory.append_assoc]
  have originalSame := originalRep.unique representsOriginal
  have copySame := copyRep.unique representsCopy
  subst a
  subst b
  exact argument_pointed_join R lift.redex lift.isVariable originalPre originalPreAtomic copyPre copyPreAtomic
    qs originalPrefixPaths copyPrefixPaths ⟨originalLast,T.redex⟩ ⟨copyLast,S.redex⟩ originalLastAt copyLastAt pre

/-- The common-successor construction yields the family preservation of (iv),
without asserting a direct Copy relationship between the two original sides. -/
theorem ArgumentLift.pointed_family {R : BetaAt t p u} {copy : ParallelHistory u v}
    {original : ParallelHistory t w} (lift : ArgumentLift R copy original)
    (copyAtomic : Atomic copy) (originalAtomic : Atomic original) (positive : 0<copy.length)
    (pre : ParallelHistory m t) (preAtomic : Atomic pre)
    (a b : RedexWithHistory m)
    (originalRep : RunRepresents (.of (pre.append original) (preAtomic.append originalAtomic)) a)
    (copyRep : RunRepresents (.of ((pre.append (.single (singleContraction R))).append copy)
      ((preAtomic.append (.single R)).append copyAtomic)) b) : FamilyEq a b := by
  obtain ⟨common,left,right⟩ := lift.pointed_join copyAtomic originalAtomic positive pre preAtomic a b originalRep copyRep
  exact .trans (.copy left) (.symm (.copy right))
end Lamping.Lambda

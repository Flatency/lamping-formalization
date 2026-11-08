import Lamping.Lamping.BetaResidualOccurrences
import Lamping.Lamping.BetaPrincipalInternal
import Lamping.Lamping.ActionFragmentCuts
import Lamping.Lamping.FixedBetaDetourBlocks

namespace Lamping.AG
open Graph

/-- Raw RHS entry occurrences, including repeated visits of the same end. -/
def rhsVisits {A B : Type} : List (A ⊕ B) → Nat
  | [] => 0
  | .inl _ :: xs => rhsVisits xs
  | .inr _ :: xs => rhsVisits xs + 1

private theorem rhsVisits_append {A B : Type} (xs ys : List (A ⊕ B)) :
    rhsVisits (xs++ys)=rhsVisits xs+rhsVisits ys := by
  induction xs with
  | nil => simp only [List.nil_append,rhsVisits,Nat.zero_add]
  | cons x xs ih =>
    cases x <;> simp only [List.cons_append,rhsVisits,ih] <;> omega

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed

private theorem zero_rhs_old_outside {edge : BetaEdge site.net} {raw old}
    (relation : BetaPathResidual site edge raw old) :
    rhsVisits raw=0 → ∀ x∈old,∃ e : Endpoint cut,x=site.outsideEnd e := by
  induction relation with
  | single e =>
    intro _ x member
    exact ⟨e,List.mem_singleton.mp member⟩
  | @outside e f tail oldTail rest ih =>
    intro zero x member
    rcases List.mem_cons.mp member with same | inside
    · exact ⟨e,same⟩
    · exact ih zero x inside
  | context arrival rest ih =>
    intro zero
    simp only [rhsVisits] at zero
    omega
  | binding arrival rest ih =>
    intro zero
    simp only [rhsVisits] at zero
    omega

/-- A real cut after an internal OLD prefix has a strictly smaller RHS-visit
suffix. Both raw and OLD streams retain the original whole input/output. -/
theorem BetaResidualOccurrence.strict_rhs_cut
    {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge)
    {raw : List (PlugSegment cut (Schema.beta i).right.net)}
    {old : List (Endpoint site.net)} {endpoint : Endpoint cut} {ordinal : Nat}
    (cutAt : BetaResidualOccurrence site edge raw old endpoint ordinal)
    (internalPrefix : ∃ v : Bool ⊕ (V × Bool),site.internalEnd v∈cutAt.oldBefore) :
    rhsVisits (.inl endpoint::cutAt.after) < rhsVisits raw ∧
    rhsVisits raw=rhsVisits (cutAt.before++[.inl endpoint])+
      rhsVisits (.inl endpoint::cutAt.after) ∧
    ∀ {a b : Context},PlugLabelling cut (Schema.beta i).right.net raw a b →
      ∃ seam leftCount rightCount,
        PlugLabelling cut (Schema.beta i).right.net
          (cutAt.before++[.inl endpoint]) a seam ∧
        PlugLabelling cut (Schema.beta i).right.net
          (.inl endpoint::cutAt.after) seam b ∧
        FixedBetaDetourBlocks edge
          (cutAt.oldBefore++[site.outsideEnd endpoint]) a seam leftCount ∧
        FixedBetaDetourBlocks edge
          (site.outsideEnd endpoint::cutAt.oldAfter) seam b rightCount := by
  have counts : rhsVisits raw=rhsVisits (cutAt.before++[.inl endpoint])+
      rhsVisits (.inl endpoint::cutAt.after) := by
    calc
      rhsVisits raw=rhsVisits (cutAt.before++ .inl endpoint::cutAt.after) :=
        congrArg rhsVisits cutAt.raw_eq
      _=rhsVisits (cutAt.before++[.inl endpoint])+rhsVisits (.inl endpoint::cutAt.after) := by
        simp only [rhsVisits_append,rhsVisits,Nat.add_zero]
  have prefixPositive : 0<rhsVisits (cutAt.before++[.inl endpoint]) := by
    apply Nat.pos_of_ne_zero
    intro zero
    obtain ⟨v,inside⟩ := internalPrefix
    have member : site.internalEnd v∈cutAt.oldBefore++[site.outsideEnd endpoint] :=
      List.mem_append_left _ inside
    obtain ⟨e,same⟩ := zero_rhs_old_outside site cutAt.prefixResidual zero _ member
    exact site.internal_outside_ne v e same
  refine ⟨by omega,counts,?_⟩
  intro a b labels
  have split : PlugLabelling cut (Schema.beta i).right.net
      (cutAt.before++ .inl endpoint::cutAt.after) a b := by
    rw [←cutAt.raw_eq]
    exact labels
  obtain ⟨seam,leftRaw,rightRaw⟩ := PlugLabelling.split_overlap cut (Schema.beta i).right.net split
  obtain ⟨leftCount,leftOld⟩ := cutAt.prefixResidual.fixed_detour_blocks site geometry leftRaw
  obtain ⟨rightCount,rightOld⟩ := cutAt.suffixResidual.fixed_detour_blocks site geometry rightRaw
  exact ⟨seam,leftCount,rightCount,leftRaw,rightRaw,leftOld,rightOld⟩
end

#print axioms BetaResidualOccurrence.strict_rhs_cut
end Lamping.AG

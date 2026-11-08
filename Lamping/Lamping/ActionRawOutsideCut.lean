import Lamping.Lamping.ActionFragmentCuts
namespace Lamping.AG
open Graph

private theorem inr_prefix_outside_cut {L R : Type} {inside : List R}
    {entry pivot : L} {tail before after : List (L⊕R)}
    (split : inside.map Sum.inr++Sum.inl entry::tail=before++Sum.inl pivot::after) :
    ∃ rest,before=inside.map Sum.inr++rest ∧Sum.inl entry::tail=rest++Sum.inl pivot::after := by
  induction inside generalizing before with
  | nil => exact ⟨before,rfl,split⟩
  | cons e inside ih =>
    cases before with
    | nil => cases split
    | cons f before =>
      have parts := List.cons.inj split
      have first := parts.1
      subst f
      obtain ⟨rest,left,right⟩ := ih parts.2
      exact ⟨rest,congrArg (Sum.inr e::·) left,right⟩

private theorem outside_prefix_shape {L R : Type} {entry pivot : L}
    {tail before after : List (L⊕R)}
    (split : Sum.inl entry::tail=before++Sum.inl pivot::after) :
    ∃ rest,before++[Sum.inl pivot]=Sum.inl entry::rest := by
  apply List.head?_eq_some_iff.mp
  have heads := congrArg List.head? split
  simpa only [List.head?_cons,List.head?_append,List.head?_singleton] using heads.symm

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

/-- Cut at the supplied RAW outside ordinal. Equal endpoint values at other
ordinals do not determine this cut. Each residual retains the shared pivot. -/
theorem ActionCanonicalBlocks.split_at_raw_outside
    {principal : SiteActionPrincipal site} {raw old}
    (relation : ActionCanonicalBlocks site principal raw old)
    {before after : List (PlugSegment cut s.right.net)} (pivot : Endpoint cut)
    (split : raw=before++Sum.inl pivot::after) :
    ∃ oldBefore oldAfter,old=oldBefore++site.outsideEnd pivot::oldAfter ∧
      ActionCanonicalBlocks site principal (before++[Sum.inl pivot])
        (oldBefore++[site.outsideEnd pivot]) ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::after)
        (site.outsideEnd pivot::oldAfter) := by
  induction relation generalizing before after with
  | single e =>
    cases before with
    | nil =>
      have parts := List.cons.inj split
      have same := Sum.inl.inj parts.1
      subst e
      have empty := parts.2.symm
      subst after
      exact ⟨[],[],rfl,.single pivot,.single pivot⟩
    | cons x before =>
      have lengths := congrArg List.length split
      simp only [List.length_cons,List.length_append,List.length_nil] at lengths
      omega
  | @outside e f tail old rest ih =>
    cases before with
    | nil =>
      have parts := List.cons.inj split
      have same := Sum.inl.inj parts.1
      subst e
      exact ⟨[],old,rfl,.single pivot,by rw [←parts.2];exact .outside rest⟩
    | cons x before =>
      have parts := List.cons.inj split
      have first := parts.1
      subst x
      obtain ⟨oldBefore,oldAfter,oldSplit,left,right⟩ := ih parts.2
      obtain ⟨rawTail,rawShape⟩ := outside_prefix_shape parts.2
      refine ⟨site.outsideEnd e::oldBefore,oldAfter,congrArg (site.outsideEnd e::·) oldSplit,?_,right⟩
      change ActionCanonicalBlocks site principal (Sum.inl e::(before++[Sum.inl pivot]))
        (site.outsideEnd e::(oldBefore++[site.outsideEnd pivot]))
      rw [rawShape] at left ⊢
      exact .outside left
  | @through e exit tail old inside front route start rest ih =>
    cases before with
    | nil =>
      have parts := List.cons.inj split
      have same := Sum.inl.inj parts.1
      subst e
      have full : ActionCanonicalBlocks site principal
          (Sum.inl pivot::(inside.map Sum.inr++Sum.inl (.inr (.inl (.inr exit)))::tail)) (front++old) :=
        .through inside front route start rest
      have head := full.head site rfl
      obtain ⟨oldTail,oldSplit⟩ := List.head?_eq_some_iff.mp head
      refine ⟨[],oldTail,oldSplit,.single pivot,?_⟩
      rw [←parts.2,←oldSplit]
      exact full
    | cons x before =>
      have parts := List.cons.inj split
      have first := parts.1
      subst x
      obtain ⟨rawBefore,beforeSplit,remaining⟩ := inr_prefix_outside_cut parts.2
      obtain ⟨oldBefore,oldAfter,oldSplit,left,right⟩ := ih remaining
      obtain ⟨rawTail,rawShape⟩ := outside_prefix_shape remaining
      refine ⟨front++oldBefore,oldAfter,?_,?_,right⟩
      · rw [oldSplit,List.append_assoc]
      · change ActionCanonicalBlocks site principal
          (Sum.inl e::(before++[Sum.inl pivot])) ((front++oldBefore)++[site.outsideEnd pivot])
        rw [beforeSplit,List.append_assoc,rawShape,List.append_assoc]
        rw [rawShape] at left
        exact .through inside front route start left

/-- An actual raw parent prefix determines the OLD prefix as a conclusion.
Only fixed-raw source uniqueness is used, so this also applies to fan rules.
No old split or arbitrary continuation is an input. Assignments come from
the supplied whole labelling, with one genuine shared seam. -/
theorem ActionCanonicalBlocks.cut_at_raw_parent
    {principal : SiteActionPrincipal site} {raw old parentRaw parentOld newPiece}
    (whole : ActionCanonicalBlocks site principal raw old)
    (parent : ActionCanonicalBlocks site principal parentRaw parentOld)
    {a b : Context} (labels : PlugLabelling cut s.right.net raw a b)
    (rawSplit : raw=parentRaw++newPiece) (pivot : Endpoint cut)
    (parentLast : parentRaw.getLast?=some (Sum.inl pivot)) :
    ∃ oldPiece seam,old=parentOld++oldPiece ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::newPiece)
        (site.outsideEnd pivot::oldPiece) ∧
      PlugLabelling cut s.right.net parentRaw a seam ∧
      PlugLabelling cut s.right.net (Sum.inl pivot::newPiece) seam b := by
  obtain ⟨before,parentSplit⟩ := List.getLast?_eq_some_iff.mp parentLast
  have rawShape : raw=before++Sum.inl pivot::newPiece := by
    rw [rawSplit,parentSplit,List.append_assoc]
    rfl
  obtain ⟨oldBefore,oldPiece,oldShape,left,right⟩ := whole.split_at_raw_outside site pivot rawShape
  have oldParent : oldBefore++[site.outsideEnd pivot]=parentOld :=
    left.fixed_source_unique_of_eq site parent parentSplit.symm
  have oldSplit : old=parentOld++oldPiece := by
    rw [←oldParent,List.append_assoc]
    exact oldShape
  have actual : PlugLabelling cut s.right.net (before++Sum.inl pivot::newPiece) a b := by
    rw [←rawShape]
    exact labels
  obtain ⟨seam,parentLabels,pieceLabels⟩ := actual.split_overlap cut s.right.net
  exact ⟨oldPiece,seam,oldSplit,right,by rw [parentSplit];exact parentLabels,pieceLabels⟩
end
end Lamping.AG


import Lamping.Lamping.ActualCurrentAfterChains
import Lamping.Lamping.FamilyRepresentation

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

theorem canonicalChainImage_drop_cut
    (selection : OccurrenceFragmentSelection current g root)
    {start next : Path} {edges before after : List Path} {edge : Path}
    (parent : PrerequisiteChain current start edges)
    (tail : PrerequisiteChain current next after)
    (split : edges=before++edge::after) :
    (canonicalChainImage selection parent).drop (before.length+1)=
      canonicalChainImage selection tail := by
  subst edges
  simp only [canonicalChainImage,List.attach_append,List.attach_cons,List.map_append,
    List.map_cons,List.map_map,Function.comp_def]
  rw [List.drop_append]
  simp only [List.length_map,List.length_attach]
  simp only [Nat.add_sub_cancel_left,List.drop_succ_cons,List.drop_zero]
  rw [List.drop_eq_nil_of_le (by simp only [List.length_map,List.length_attach];omega),List.nil_append]
  rfl

private theorem after_lengths
    {F ps : List Path} {oldSource : LTerm} {degree : Label}
    {leftStart rightStart : Path} {es fs : List Path}
    (selection : OccurrenceFragmentSelection current g root)
    (leftParent : PrerequisiteChain current leftStart es)
    (rightParent : PrerequisiteChain current rightStart fs)
    (physical : SameChainRepresentation selection leftParent rightParent)
    (left : ActualUnsafeMarkerCut F ps oldSource current degree leftStart es)
    (right : ActualUnsafeMarkerCut F ps oldSource current degree rightStart fs)
    (sameBefore : left.before.length=right.before.length) :
    left.after.length=right.after.length := by
  have sizes := congrArg List.length physical
  change (canonicalChainImage selection leftParent).length=
    (canonicalChainImage selection rightParent).length at sizes
  rw [canonicalChainImage_length,canonicalChainImage_length] at sizes
  have ls := congrArg List.length left.split
  have rs := congrArg List.length right.split
  simp only [List.length_append,List.length_cons] at ls rs
  omega

theorem actual_cut_after_same_representation
    {F ps : List Path} {oldSource : LTerm} {degree : Label}
    {leftStart rightStart : Path} {es fs : List Path}
    (selection : OccurrenceFragmentSelection current g root)
    (leftParent : PrerequisiteChain current leftStart es)
    (rightParent : PrerequisiteChain current rightStart fs)
    (physical : SameChainRepresentation selection leftParent rightParent)
    (left : ActualUnsafeMarkerCut F ps oldSource current degree leftStart es)
    (right : ActualUnsafeMarkerCut F ps oldSource current degree rightStart fs)
    (sameBefore : left.before.length=right.before.length)
    (nonempty : left.after≠[]) :
    right.after≠[] ∧left.after.length=right.after.length ∧
      ∃ (leftNext rightNext : Path)
        (leftAfter : PrerequisiteChain current leftNext left.after)
        (rightAfter : PrerequisiteChain current rightNext right.after),
        ActualAfterStart current left.reader left.edge leftNext ∧
        ActualAfterStart current right.reader right.edge rightNext ∧
        SameChainRepresentation selection leftAfter rightAfter ∧
        left.after.length<es.length ∧right.after.length<fs.length ∧
        max left.after.length right.after.length<max es.length fs.length := by
  have lengths := after_lengths selection leftParent rightParent physical left right sameBefore
  have rightMore : right.after≠[] := by
    intro empty
    apply nonempty
    apply List.length_eq_zero_iff.mp
    rw [lengths,empty];rfl
  obtain ⟨ln,lg,lc,ll⟩ := left.current_after_chain nonempty
  obtain ⟨rn,rg,rc,rl⟩ := right.current_after_chain rightMore
  have tails := congrArg (fun image => image.drop (left.before.length+1)) physical
  change (canonicalChainImage selection leftParent).drop (left.before.length+1)=
    (canonicalChainImage selection rightParent).drop (left.before.length+1) at tails
  rw [canonicalChainImage_drop_cut selection leftParent lc left.split,sameBefore,
    canonicalChainImage_drop_cut selection rightParent rc right.split] at tails
  exact ⟨rightMore,lengths,ln,rn,lc,rc,lg,rg,tails,ll,rl,by omega⟩

theorem actual_cut_after_representation_cases
    {F ps : List Path} {oldSource : LTerm} {degree : Label}
    {leftStart rightStart : Path} {es fs : List Path}
    (selection : OccurrenceFragmentSelection current g root)
    (leftParent : PrerequisiteChain current leftStart es)
    (rightParent : PrerequisiteChain current rightStart fs)
    (physical : SameChainRepresentation selection leftParent rightParent)
    (left : ActualUnsafeMarkerCut F ps oldSource current degree leftStart es)
    (right : ActualUnsafeMarkerCut F ps oldSource current degree rightStart fs)
    (sameBefore : left.before.length=right.before.length) :
    left.after.length=right.after.length ∧
      (left.after=[] ↔right.after=[]) ∧
      ((left.after=[] ∧right.after=[]) ∨
       (left.after≠[] ∧right.after≠[] ∧
        ∃ (leftNext rightNext : Path)
          (leftAfter : PrerequisiteChain current leftNext left.after)
          (rightAfter : PrerequisiteChain current rightNext right.after),
          ActualAfterStart current left.reader left.edge leftNext ∧
          ActualAfterStart current right.reader right.edge rightNext ∧
          SameChainRepresentation selection leftAfter rightAfter ∧
          left.after.length<es.length ∧right.after.length<fs.length ∧
          max left.after.length right.after.length<max es.length fs.length)) := by
  have lengths := after_lengths selection leftParent rightParent physical left right sameBefore
  have emptyIff : left.after=[] ↔right.after=[] := by
    constructor
    · intro empty
      apply List.length_eq_zero_iff.mp
      rw [←lengths,empty];rfl
    · intro empty
      apply List.length_eq_zero_iff.mp
      rw [lengths,empty];rfl
  refine ⟨lengths,emptyIff,?_⟩
  by_cases empty : left.after=[]
  · exact Or.inl ⟨empty,emptyIff.mp empty⟩
  · obtain ⟨rm,_len,ln,rn,lc,rc,lg,rg,eq,ll,rl,mm⟩ :=
      actual_cut_after_same_representation selection leftParent rightParent physical left right sameBefore empty
    exact Or.inr ⟨empty,rm,ln,rn,lc,rc,lg,rg,eq,ll,rl,mm⟩
end
#print axioms canonicalChainImage_drop_cut
#print axioms actual_cut_after_same_representation
#print axioms actual_cut_after_representation_cases
end Lamping.AG

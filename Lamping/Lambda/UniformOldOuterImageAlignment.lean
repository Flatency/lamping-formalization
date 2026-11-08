import Lamping.Lambda.LabelExpandedCodeAlignment
import Lamping.Lambda.LabelParallelOuterBars

namespace Lamping.Lambda.Labelled

/-- Opaque original SOURCE image, or the actual outer over/under kind.
Equal keys do not identify local atoms or occurrence coordinates. -/
def Letter.outerImageKey (s : Nat → Label) : Letter → Sum Label Bool
  | .atom n => .inl (s n)
  | .over _ => .inr true
  | .under _ => .inr false

private def degreeSeparator (alpha : Label) : Letter → Bool
  | .atom _ => false
  | .over d | .under d => decide (d=alpha)

def degreeGroups (alpha : Label) : List Letter → List (Sum (List Letter) Letter)
  | [] => []
  | letter::rest =>
      if degreeSeparator alpha letter then .inr letter::degreeGroups alpha rest else
      match degreeGroups alpha rest with
      | .inl block::groups => .inl (letter::block)::groups
      | groups => .inl [letter]::groups

private theorem safe_separator {letter : Letter}
    (safe : (Label.single letter).OuterBarsSafe (fun d=>d≠alpha)) :
    degreeSeparator alpha letter=false := by
  cases letter <;> simp_all [Label.OuterBarsSafe,degreeSeparator]

private theorem safe_groups : ∀ {label : Label},
    label.OuterBarsSafe (fun d=>d≠alpha) →degreeGroups alpha label.letters=[.inl label.letters]
  | .single letter,safe => by
    simp [Label.letters,degreeGroups,safe_separator safe]
  | .cons letter rest,safe => by
    have first : degreeSeparator alpha letter=false := by
      apply safe_separator
      cases letter with
      | atom n => trivial
      | over d => exact safe.1
      | under d => exact safe.1
    have tail : rest.OuterBarsSafe (fun d=>d≠alpha) := by
      cases letter with
      | atom n => exact safe
      | over d => exact safe.2
      | under d => exact safe.2
    simp [Label.letters,degreeGroups,first,safe_groups tail]

private theorem groups_separator_append
    (separator : degreeSeparator alpha bar=true) :
    ∀ xs ys,degreeGroups alpha (xs++bar::ys)=
      degreeGroups alpha xs++(.inr bar::degreeGroups alpha ys) := by
  intro xs
  induction xs with
  | nil => intro ys;simp [degreeGroups,separator]
  | cons letter rest ih =>
    intro ys
    simp only [List.cons_append,degreeGroups,ih]
    by_cases sep : degreeSeparator alpha letter=true
    · simp [sep]
    · have notSep : degreeSeparator alpha letter=false:=Bool.eq_false_iff.mpr sep
      simp only [notSep,Bool.false_eq_true,ite_false]
      cases groups : degreeGroups alpha rest with
      | nil => rfl
      | cons first rest => cases first <;> rfl

/-- Parse EVERY original image block, allowing arbitrary older bars inside
the SOURCE images. Only the newly created outer bars map to alpha. -/
theorem Label.Alternating.uniform_relabel_groups
    {label : Label} {region : Nat → Prop} {s : Nat → Label}
    (alternating : label.Alternating)
    (imagesSafe : ∀ n,region n →(s n).OuterBarsSafe (fun d=>d≠alpha))
    (support : label.Supported region)
    (bars : label.OuterBarsSafe (fun d=>d.relabel s=alpha)) :
    degreeGroups alpha (label.relabel s).letters=label.expansionTokens s := by
  revert support bars
  induction alternating with
  | atom n =>
    intro support _bars
    exact safe_groups (imagesSafe n support)
  | @over x d y left middle right hl _hm hr =>
    intro support bars
    obtain ⟨prefixSupport,rightSupport⟩:=(Label.supported_concat _ _ _).mp support
    obtain ⟨leftSupport,_middleSupport⟩:=(Label.supported_concat _ _ _).mp prefixSupport
    obtain ⟨prefixBars,rightBars⟩:=(Label.outerBarsSafe_concat _ _ _).mp bars
    obtain ⟨leftBars,middleBars⟩:=(Label.outerBarsSafe_concat _ _ _).mp prefixBars
    have separator : degreeSeparator alpha (.over (d.relabel s))=true := by
      change d.relabel s=alpha at middleBars
      simp [degreeSeparator,middleBars]
    simp only [Label.relabel_concat,Label.relabel_over,Label.letters_concat,Label.expansionTokens_concat]
    simp only [Label.over,Label.letters,Label.expansionTokens,List.map_cons,List.map_nil,
      List.singleton_append,List.append_assoc]
    rw [groups_separator_append separator,hl leftSupport leftBars,hr rightSupport rightBars]
    rfl
  | @under x d y left middle right hl _hm hr =>
    intro support bars
    obtain ⟨prefixSupport,rightSupport⟩:=(Label.supported_concat _ _ _).mp support
    obtain ⟨leftSupport,_middleSupport⟩:=(Label.supported_concat _ _ _).mp prefixSupport
    obtain ⟨prefixBars,rightBars⟩:=(Label.outerBarsSafe_concat _ _ _).mp bars
    obtain ⟨leftBars,middleBars⟩:=(Label.outerBarsSafe_concat _ _ _).mp prefixBars
    have separator : degreeSeparator alpha (.under (d.relabel s))=true := by
      change d.relabel s=alpha at middleBars
      simp [degreeSeparator,middleBars]
    simp only [Label.relabel_concat,Label.relabel_under,Label.letters_concat,Label.expansionTokens_concat]
    simp only [Label.under,Label.letters,Label.expansionTokens,List.map_cons,List.map_nil,
      List.singleton_append,List.append_assoc]
    rw [groups_separator_append separator,hl leftSupport leftBars,hr rightSupport rightBars]
    rfl

theorem Label.Alternating.uniform_relabel_expansionTokens
    {left right : Label} {region : Nat → Prop} {s : Nat → Label}
    (leftAlt : left.Alternating) (rightAlt : right.Alternating)
    (imagesSafe : ∀ n,region n →(s n).OuterBarsSafe (fun d=>d≠alpha))
    (leftSupport : left.Supported region) (rightSupport : right.Supported region)
    (leftBars : left.OuterBarsSafe (fun d=>d.relabel s=alpha))
    (rightBars : right.OuterBarsSafe (fun d=>d.relabel s=alpha))
    (sameImage : left.relabel s=right.relabel s) :
    left.expansionTokens s=right.expansionTokens s :=
  (leftAlt.uniform_relabel_groups imagesSafe leftSupport leftBars).symm.trans
    ((congrArg (fun label : Label=>degreeGroups alpha label.letters) sameImage).trans
      (rightAlt.uniform_relabel_groups imagesSafe rightSupport rightBars))

private theorem outer_key_of_expansion {left right : Letter}
    (same : left.expansionToken s=right.expansionToken s) :
    left.outerImageKey s=right.outerImageKey s := by
  cases left with
  | atom n =>
    cases right with
    | atom m =>
      have equal : (s n).letters=(s m).letters:=Sum.inl.inj same
      exact congrArg Sum.inl (Label.letters_injective equal)
    | over d => cases same
    | under d => cases same
  | over d =>
    cases right with
    | atom n => cases same
    | over e => rfl
    | under e => cases same
  | under d =>
    cases right with
    | atom n => cases same
    | over e => cases same
    | under e => rfl

private theorem outer_keys_of_expansions {xs ys : List Letter}
    (same : xs.map (Letter.expansionToken s)=ys.map (Letter.expansionToken s)) :
    xs.map (Letter.outerImageKey s)=ys.map (Letter.outerImageKey s) := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons y ys => cases same
  | cons x xs ih =>
    cases ys with
    | nil => cases same
    | cons y ys =>
      have pair:=List.cons.inj same
      simp only [List.map_cons]
      rw [outer_key_of_expansion pair.1,ih pair.2]

theorem Label.Alternating.uniform_relabel_outer_alignment
    {left right : Label} {region : Nat → Prop} {s : Nat → Label}
    (leftAlt : left.Alternating) (rightAlt : right.Alternating)
    (imagesSafe : ∀ n,region n →(s n).OuterBarsSafe (fun d=>d≠alpha))
    (leftSupport : left.Supported region) (rightSupport : right.Supported region)
    (leftBars : left.OuterBarsSafe (fun d=>d.relabel s=alpha))
    (rightBars : right.OuterBarsSafe (fun d=>d.relabel s=alpha))
    (sameImage : left.relabel s=right.relabel s) :
    left.letters.map (Letter.outerImageKey s)=right.letters.map (Letter.outerImageKey s) :=
  outer_keys_of_expansions
    (leftAlt.uniform_relabel_expansionTokens rightAlt imagesSafe leftSupport rightSupport leftBars rightBars sameImage)

private theorem actual_local_label
    (global : History ps source target)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (atGlobal : target.subterm p=some node) (atLocal : localTarget.subterm p=some localNode) :
    localNode.label.relabel (initialRelabelling source 0)=node.label := by
  have transported:=localHistory.relabel (initialRelabelling source 0)
  have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source:=
    initialRelabelling_factor source 0
  rw [factor] at transported
  have whole:=transported.deterministic global
  have atSame:=congrArg (fun term : LTerm=>term.subterm p) whole
  change (localTarget.relabel (initialRelabelling source 0)).subterm p=target.subterm p at atSame
  rw [LTerm.subterm_relabel,atLocal,Option.map_some,atGlobal] at atSame
  have result:=congrArg LTerm.label (Option.some.inj atSame)
  cases localNode <;> exact result

end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Marked
open Labelled
variable {F ps qs : List Path}
variable {source target localTarget leftTarget rightTarget leftBasis rightBasis : LTerm}
variable {leftNode rightNode leftLocalNode rightLocalNode : LTerm} {alpha : Label}

/-- Existing OLD outer-bar preservation, on the actual local INIT history.
No separate paired-prefix induction or intermediate safety is assumed. -/
theorem RelativeOldHistory.local_outer_image_bars
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) endpoint)
    (localHistory : Labelled.History ps (initLabels source.erase) localTarget)
    (selected : ∀ p∈F,source.degreeAt p=some alpha) :
    localTarget.OuterBarsSafe (fun d=>d.relabel (initialRelabelling source 0)=alpha) := by
  have localOld : Marked.RelativeOldHistory F ps
      (Marked.mark F (initLabels source.erase).erase) endpoint := by
    simpa only [erase_initLabels] using old
  apply localOld.outerBarsSafe (DegreeAligned.initial _ F) localHistory
    ((init_is_INIT source.erase).outerBarsSafe _)
  intro p member d degree
  have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source:=
    initialRelabelling_factor source 0
  have image:=LTerm.degreeAt_relabel (initLabels source.erase) (initialRelabelling source 0) p
  rw [factor,degree,Option.map_some] at image
  exact Option.some.inj (image.symm.trans (selected p member))

/-- The complete one-sided parser equation at THIS actual current occurrence;
all later marked-LAST/overlap blocks remain present. -/
theorem RelativeOldHistory.local_outer_image_groups
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) endpoint)
    (labels : Labelled.History ps source target)
    (localHistory : Labelled.History ps (initLabels source.erase) localTarget)
    (selected : ∀ p∈F,source.degreeAt p=some alpha)
    (sourceSafe : source.OuterBarsSafe (fun d=>d≠alpha))
    (atGlobal : target.subterm p=some node) (atLocal : localTarget.subterm p=some localNode) :
    degreeGroups alpha node.label.letters=
      localNode.label.expansionTokens (initialRelabelling source 0) := by
  let region : Nat→Prop:=fun n=>Label.atom n∈(initLabels source.erase).labels
  have member:=LTerm.label_mem_of_subterm atLocal
  have alternating:=localHistory.generated_label_alternating (init_is_INIT _) member
  have support:=(LTerm.supported_iff _ _).mp (localHistory.supported (init_is_INIT _).supported) _ member
  have imagesSafe (n : Nat) (inside : region n) :
      (initialRelabelling source 0 n).OuterBarsSafe (fun d=>d≠alpha) := by
    apply (LTerm.outerBarsSafe_iff _ _).mp sourceSafe
    apply initialRelabelling_mem source 0 n (Nat.zero_le n)
    simpa only [Nat.zero_add] using LTerm.basis_atom_bound source inside
  have bars:=(LTerm.outerBarsSafe_iff _ _).mp (old.local_outer_image_bars localHistory selected) _ member
  have parsed:=alternating.uniform_relabel_groups imagesSafe support bars
  rw [Labelled.actual_local_label labels localHistory atGlobal atLocal] at parsed
  exact parsed

/-- Complete ordered original-image alignment for two actual OLD prefixes.
This is lexical only: equal opaque SOURCE labels need not be equal local atoms
or equal physical fragments. The original global history is unchanged. -/
theorem RelativeOldHistory.local_outer_image_alignment
    (leftOld : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) leftEndpoint)
    (rightOld : Marked.RelativeOldHistory F qs (Marked.mark F source.erase) rightEndpoint)
    (leftLabels : Labelled.History ps source leftTarget) (rightLabels : Labelled.History qs source rightTarget)
    (leftLocal : Labelled.History ps (initLabels source.erase) leftBasis)
    (rightLocal : Labelled.History qs (initLabels source.erase) rightBasis)
    (selected : ∀ p∈F,source.degreeAt p=some alpha)
    (sourceSafe : source.OuterBarsSafe (fun d=>d≠alpha))
    (leftAt : leftTarget.subterm p=some leftNode) (rightAt : rightTarget.subterm q=some rightNode)
    (leftLocalAt : leftBasis.subterm p=some leftLocalNode)
    (rightLocalAt : rightBasis.subterm q=some rightLocalNode)
    (sameLabel : leftNode.label=rightNode.label) :
    leftLocalNode.label.letters.map (Letter.outerImageKey (initialRelabelling source 0))=
      rightLocalNode.label.letters.map (Letter.outerImageKey (initialRelabelling source 0)) := by
  let region : Nat→Prop:=fun n=>Label.atom n∈(initLabels source.erase).labels
  have leftMember:=LTerm.label_mem_of_subterm leftLocalAt
  have rightMember:=LTerm.label_mem_of_subterm rightLocalAt
  have leftAlt:=leftLocal.generated_label_alternating (init_is_INIT _) leftMember
  have rightAlt:=rightLocal.generated_label_alternating (init_is_INIT _) rightMember
  have leftSupport:=(LTerm.supported_iff _ _).mp (leftLocal.supported (init_is_INIT _).supported) _ leftMember
  have rightSupport:=(LTerm.supported_iff _ _).mp (rightLocal.supported (init_is_INIT _).supported) _ rightMember
  have imagesSafe (n : Nat) (member : region n) :
      (initialRelabelling source 0 n).OuterBarsSafe (fun d=>d≠alpha) := by
    apply (LTerm.outerBarsSafe_iff _ _).mp sourceSafe
    apply initialRelabelling_mem source 0 n (Nat.zero_le n)
    simpa only [Nat.zero_add] using LTerm.basis_atom_bound source member
  have leftBars:=(LTerm.outerBarsSafe_iff _ _).mp (leftOld.local_outer_image_bars leftLocal selected) _ leftMember
  have rightBars:=(LTerm.outerBarsSafe_iff _ _).mp (rightOld.local_outer_image_bars rightLocal selected) _ rightMember
  have leftImage:=Labelled.actual_local_label leftLabels leftLocal leftAt leftLocalAt
  have rightImage:=Labelled.actual_local_label rightLabels rightLocal rightAt rightLocalAt
  exact leftAlt.uniform_relabel_outer_alignment rightAlt imagesSafe leftSupport rightSupport
    leftBars rightBars (leftImage.trans (sameLabel.trans rightImage.symm))

#print axioms Label.Alternating.uniform_relabel_groups
#print axioms Label.Alternating.uniform_relabel_expansionTokens
#print axioms Label.Alternating.uniform_relabel_outer_alignment
#print axioms RelativeOldHistory.local_outer_image_bars
#print axioms RelativeOldHistory.local_outer_image_groups
#print axioms RelativeOldHistory.local_outer_image_alignment
end Lamping.Lambda.Marked

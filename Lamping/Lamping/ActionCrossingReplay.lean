import Lamping.Lamping.ActionCrossingInverse
import Lamping.Lamping.ControlContextTails
import Lamping.Lamping.LocalCancellation
import Lamping.Lamping.ActionPathShapes
import Lamping.Lamping.UnaryActionPathShapes
namespace Lamping.AG
open Graph

/-- Exact replay of a fixed crossing, rather than existential shell relabeling.
This does not cover a passive-to-passive excursion. -/
theorem fanAction_cross_replay (f : Op) (i j : Nat) (lt : i<j) (branch : Bool)
    (q : Aux f) (a b : Context)
    (labels : Labelling (leftNet .fan f i j) (leftRoute .fan f i j branch q) a b) :
    Labelling (fanRight f i j)
      [.inr (.inl (.inl branch)),.inl ⟨.inl branch,.inr q⟩,.inl ⟨.inr q,.inl ()⟩] a b := by
  obtain ⟨gap,rfl⟩ : ∃ gap,j=i+1+gap := ⟨j-i-1,by omega⟩
  obtain ⟨middle,active,passive⟩ := (leftRoute_labeling_iff .fan f i (i+1+gap) branch q a b).mp labels
  have middleEq : middle=InitialOffsets.fanAt i branch a :=
    active.output_unique (.direct (InitialOffsets.Event.apply_rel (.fan i branch) a))
  have tailEq : middle.tail (i+1)=a.tail (i+1) := by
    rw [middleEq]
    exact InitialOffsets.fanAt_high_tail a i (i+1) (by omega) branch
  have high := passive.cut_prefix (i+1) (by omega)
  rw [show i+1+gap-(i+1)=gap by omega,tailEq] at high
  have pair := fanActionPaths f i gap q branch a (a.tail (i+1)) (b.tail (i+1)) (a.get i) high
  have inputEq := InitialOffsets.rebuild a i
  have source := pair.1.labeling
  have target := pair.2.labeling
  have sourceShape := pair.1.left_control_shape .fan f (Or.inl rfl) i (i+1+gap) branch q
  rw [sourceShape] at source
  obtain ⟨q',same,targetShape⟩ := fanRight_active_path_shape f i (i+1+gap) branch (.inr q)
    pair.2.edges _ _ pair.2.labeling pair.2.start pair.2.finish
  have eq : q=q' := Sum.inr.inj same
  subst q'
  rw [targetShape] at target
  rw [inputEq] at source target
  have outputEq := source.output_unique labels
  rw [outputEq] at target
  exact target
theorem croAction_cross_replay (f : Op) (i j : Nat) (lt : i<j)
    (q : Aux f) (a b : Context)
    (labels : Labelling (leftNet .cro f i j) (leftRoute .cro f i j () q) a b) :
    Labelling (unaryRightCore .cro f (Bij.refl _) i (j-1))
      [.inr (.inl (.inl ())),.inl ⟨.inl (),.inr q⟩,.inl ⟨.inr q,.inl ()⟩] a b := by
  obtain ⟨gap,rfl⟩ : ∃ gap,j=i+1+gap := ⟨j-i-1,by omega⟩
  obtain ⟨middle,active,passive⟩ := (leftRoute_labeling_iff .cro f i (i+1+gap) () q a b).mp labels
  have middleEq : middle=InitialOffsets.croAt i a :=
    active.output_unique (.direct (InitialOffsets.Event.apply_rel (.cro i) a))
  have tailEq : middle.tail (i+1)=a.tail i := by
    rw [middleEq]
    simpa only [Nat.add_sub_cancel] using InitialOffsets.croAt_high_tail a i (i+1) (by omega)
  have high := passive.cut_prefix (i+1) (by omega)
  rw [show i+1+gap-(i+1)=gap by omega,tailEq] at high
  have pair := croActionPaths f i gap q a (a.tail i) (b.tail (i+1)) high
  have source := pair.1.labeling
  have target := pair.2.labeling
  have sourceShape := pair.1.left_control_shape .cro f (Or.inr (Or.inl rfl)) i (i+1+gap) () q
  rw [sourceShape] at source
  obtain ⟨q',same,targetShape⟩ := unaryRight_active_path_shape .cro f (Bij.refl _)
    (Or.inr (Or.inl rfl)) i (i+1+gap-1) (.inr q) pair.2.edges _ _ pair.2.labeling pair.2.start pair.2.finish
  have eq : q=q' := Sum.inr.inj same
  subst q'
  rw [targetShape] at target
  rw [a.replace_tail i] at source target
  have outputEq := source.output_unique labels
  rw [outputEq] at target
  exact target

theorem braAction_cross_replay (f : Op) (i j : Nat) (lt : i<j)
    (q : Aux f) (a b : Context)
    (labels : Labelling (leftNet .bra f i j) (leftRoute .bra f i j () q) a b) :
    Labelling (unaryRightCore .bra f (Bij.refl _) i (j+1))
      [.inr (.inl (.inl ())),.inl ⟨.inl (),.inr q⟩,.inl ⟨.inr q,.inl ()⟩] a b := by
  obtain ⟨gap,rfl⟩ : ∃ gap,j=i+1+gap := ⟨j-i-1,by omega⟩
  obtain ⟨middle,active,passive⟩ := (leftRoute_labeling_iff .bra f i (i+1+gap) () q a b).mp labels
  have middleEq : middle=InitialOffsets.braAt i a :=
    active.output_unique (.direct (InitialOffsets.Event.apply_rel (.bra i) a))
  have tailEq : middle.tail (i+1)=a.tail (i+2) := by
    rw [middleEq]
    exact InitialOffsets.braAt_high_tail a i (i+1) (by omega)
  have high := passive.cut_prefix (i+1) (by omega)
  rw [show i+1+gap-(i+1)=gap by omega,tailEq] at high
  have pair := braActionPaths f i gap q a (a.tail (i+2)) (b.tail (i+1)) (a.get (i+1)) (a.get i) high
  have source := pair.1.labeling
  have target := pair.2.labeling
  have sourceShape := pair.1.left_control_shape .bra f (Or.inr (Or.inr rfl)) i (i+1+gap) () q
  rw [sourceShape] at source
  obtain ⟨q',same,targetShape⟩ := unaryRight_active_path_shape .bra f (Bij.refl _)
    (Or.inr (Or.inr rfl)) i (i+1+gap+1) (.inr q) pair.2.edges _ _ pair.2.labeling pair.2.start pair.2.finish
  have eq : q=q' := Sum.inr.inj same
  subst q'
  rw [targetShape] at target
  rw [InitialOffsets.rebuild_two a i] at source target
  have outputEq := source.output_unique labels
  rw [outputEq] at target
  exact target
end Lamping.AG



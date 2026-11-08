import Lamping.Lamping.ControlPrincipalSuffixes
import Lamping.Lamping.BackwardPathDeterminism
import Lamping.Lamping.CancellationDirection
import Lamping.Lamping.CancellationUniformRoutes
import Lamping.Lamping.CancellationResidualReplay
import Lamping.Lamping.Fixtures
namespace Lamping.Checks.Phase5Review.Cancellations
open AG Graph
private def kept : Empty → Label signature := Empty.elim
private def fanSite : PathSite (.fanCancel 2) kept (B:=Bool⊕Bool) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl k,_⟩ => nomatch k
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inl _),.inr a⟩ => .inr (.inl (.inl a))
      | .inl ⟨.inr (.inr _),.inr a⟩ => .inr (.inl (.inr a))
      | .inr (.inl (.inl a)) => .inl ⟨.inr (.inl ()),.inr a⟩
      | .inr (.inl (.inr a)) => .inl ⟨.inr (.inr ()),.inr a⟩
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
      · exact nomatch k
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · rfl
      · rfl
      · exact nomatch w
      · cases v; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩)) same
      · exact nomatch k
      · cases p <;> cases same
      · cases p <;> cases same
      · cases same
      · cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases v; cases b <;> rfl

private def croSite : PathSite (.croCancel 2) kept (B:=Unit⊕Unit) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl k,_⟩ => nomatch k
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inl _),.inr a⟩ => .inr (.inl (.inl a))
      | .inl ⟨.inr (.inr _),.inr a⟩ => .inr (.inl (.inr a))
      | .inr (.inl (.inl a)) => .inl ⟨.inr (.inl ()),.inr a⟩
      | .inr (.inl (.inr a)) => .inl ⟨.inr (.inr ()),.inr a⟩
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
      · exact nomatch k
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · rfl
      · rfl
      · exact nomatch w
      · cases v; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩)) same
      · exact nomatch k
      · cases p <;> cases same
      · cases p <;> cases same
      · cases same
      · cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases v; cases b <;> rfl

private def braSite : PathSite (.braCancel 2) kept (B:=Unit⊕Unit) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl k,_⟩ => nomatch k
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inl _),.inr a⟩ => .inr (.inl (.inl a))
      | .inl ⟨.inr (.inr _),.inr a⟩ => .inr (.inl (.inr a))
      | .inr (.inl (.inl a)) => .inl ⟨.inr (.inl ()),.inr a⟩
      | .inr (.inl (.inr a)) => .inl ⟨.inr (.inr ()),.inr a⟩
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
      · exact nomatch k
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · rfl
      · rfl
      · exact nomatch w
      · cases v; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩)) same
      · exact nomatch k
      · cases p <;> cases same
      · cases p <;> cases same
      · cases same
      · cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases v; cases b <;> rfl

private abbrev fanCut := cutFragment fanSite.net (pathPartition (.fanCancel 2) Unit) fanSite.closed
private def fanPath (branch : Bool) : List (Endpoint fanSite.reduce) :=
  [.inr (.inl (.inl branch)),
   .inr (.inr (.inr (.inl branch),true)),
   .inr (.inr (.inr (.inr branch),false))]
private def fanFirst (branch : Bool) : Endpoint fanCut := .inr (.inl (.inl (.inl branch)))
private def fanLast (branch : Bool) : Endpoint fanCut := .inr (.inl (.inr (.inr branch)))
theorem fan_target_labels (branch : Bool) (a : Context) : Labelling fanSite.reduce (fanPath branch) a a := by
  apply Labelling.cons (LabelledTurn.transparent (g:=fanSite.reduce) (.inr (.inl branch)) false a)
  apply Labelling.cons (LabelledTurn.transparent (g:=fanSite.reduce) (.inr (.inr branch)) true a)
  exact .single _ _
theorem fan_whole_ancestor (branch : Bool) (a : Context) :
    ∃ old,CancellationResidual fanSite (fanPath branch) old ∧ Labelling fanSite.net old a a ∧
      old.head?=some (fanSite.outsideEnd (fanFirst branch)) ∧
      old.getLast?=some (fanSite.outsideEnd (fanLast branch)) :=
  fanSite.cancellation_ancestor (.fan 2) (fan_target_labels branch a) (fanFirst branch) (fanLast branch) rfl rfl


private def fanReverse (branch : Bool) := reverseEdges (g:=fanSite.reduce) (fanPath branch)
private def fanReverseFirst (branch : Bool) : Endpoint fanCut := .inr (.inl (.inl (.inr branch)))
private def fanReverseLast (branch : Bool) : Endpoint fanCut := .inr (.inl (.inr (.inl branch)))
theorem fan_reverse_whole_ancestor (branch : Bool) (a : Context) :
    ∃ old,CancellationResidual fanSite (fanReverse branch) old ∧ Labelling fanSite.net old a a ∧
      old.head?=some (fanSite.outsideEnd (fanReverseFirst branch)) ∧
      old.getLast?=some (fanSite.outsideEnd (fanReverseLast branch)) :=
  fanSite.cancellation_ancestor (.fan 2) (fan_target_labels branch a).reverse
    (fanReverseFirst branch) (fanReverseLast branch) rfl rfl

private def fanSource (branch : Bool) : List (Endpoint fanSite.net) :=
  [.inr (.inl (.inl branch)),.inl ⟨.inr (.inl ()),.inl ()⟩,
   .inr (.inr (.inr (),true)),.inl ⟨.inr (.inr ()),.inr branch⟩]
theorem fan_source_labels (branch : Bool) (a : Context) : Labelling fanSite.net (fanSource branch) a a := by
  have rule := InitialOffsets.Event.apply_rel (.fan 2 branch) a
  apply Labelling.cons (LabelledTurn.node (g:=fanSite.net) (.inr (.inl ())) (.inr branch) (.inl ()) (.direct rule))
  apply Labelling.cons (LabelledTurn.transparent (g:=fanSite.net) (.inr ()) false _)
  apply Labelling.cons (LabelledTurn.node (g:=fanSite.net) (.inr (.inr ())) (.inl ()) (.inr branch) (.inverse rule))
  exact .single _ _
example (branch : Bool) : (fanSource branch).length=4 := rfl
example (branch : Bool) : (.inr (.inr (.inr (),true)) : Endpoint fanSite.net) ∈ fanSource branch := by simp [fanSource]

private def crossedFan : List (Endpoint fanSite.reduce) :=
  [.inr (.inl (.inl false)),.inr (.inr (.inr (.inl false),true)),.inr (.inr (.inr (.inr true),false))]
theorem crossed_fan_not_labelled (a b : Context) : ¬Labelling fanSite.reduce crossedFan a b := by
  intro labels
  cases labels with
  | cons first after =>
    cases after with
    | cons impossible after => cases impossible
private abbrev croCut := cutFragment croSite.net (pathPartition (.croCancel 2) Unit) croSite.closed
private def croPath : List (Endpoint croSite.reduce) :=
  [.inr (.inl (.inl ())),.inr (.inr (.inr (.inl ()),true)),.inr (.inr (.inr (.inr ()),false))]
private def croFirst : Endpoint croCut := .inr (.inl (.inl (.inl ())))
private def croLast : Endpoint croCut := .inr (.inl (.inr (.inr ())))
theorem cro_target_labels (a : Context) : Labelling croSite.reduce croPath a a := by
  apply Labelling.cons (LabelledTurn.transparent (g:=croSite.reduce) (.inr (.inl ())) false a)
  apply Labelling.cons (LabelledTurn.transparent (g:=croSite.reduce) (.inr (.inr ())) true a)
  exact .single _ _
theorem cro_whole_ancestor (a : Context) :
    ∃ old,CancellationResidual croSite croPath old ∧ Labelling croSite.net old a a ∧
      old.head?=some (croSite.outsideEnd croFirst) ∧old.getLast?=some (croSite.outsideEnd croLast) :=
  croSite.cancellation_ancestor (.cro 2) (cro_target_labels a) croFirst croLast rfl rfl
private def croReverseFirst : Endpoint croCut := .inr (.inl (.inl (.inr ())))
private def croReverseLast : Endpoint croCut := .inr (.inl (.inr (.inl ())))
theorem cro_reverse_whole_ancestor (a : Context) :
    ∃ old,CancellationResidual croSite (reverseEdges (g:=croSite.reduce) croPath) old ∧ Labelling croSite.net old a a ∧
      old.head?=some (croSite.outsideEnd croReverseFirst) ∧old.getLast?=some (croSite.outsideEnd croReverseLast) :=
  croSite.cancellation_ancestor (.cro 2) (cro_target_labels a).reverse croReverseFirst croReverseLast rfl rfl
private abbrev braCut := cutFragment braSite.net (pathPartition (.braCancel 2) Unit) braSite.closed
private def braPath : List (Endpoint braSite.reduce) :=
  [.inr (.inl (.inl ())),.inr (.inr (.inr (.inl ()),true)),.inr (.inr (.inr (.inr ()),false))]
private def braFirst : Endpoint braCut := .inr (.inl (.inl (.inl ())))
private def braLast : Endpoint braCut := .inr (.inl (.inr (.inr ())))
theorem bra_target_labels (a : Context) : Labelling braSite.reduce braPath a a := by
  apply Labelling.cons (LabelledTurn.transparent (g:=braSite.reduce) (.inr (.inl ())) false a)
  apply Labelling.cons (LabelledTurn.transparent (g:=braSite.reduce) (.inr (.inr ())) true a)
  exact .single _ _
theorem bra_whole_ancestor (a : Context) :
    ∃ old,CancellationResidual braSite braPath old ∧ Labelling braSite.net old a a ∧
      old.head?=some (braSite.outsideEnd braFirst) ∧old.getLast?=some (braSite.outsideEnd braLast) :=
  braSite.cancellation_ancestor (.bra 2) (bra_target_labels a) braFirst braLast rfl rfl
private def braReverseFirst : Endpoint braCut := .inr (.inl (.inl (.inr ())))
private def braReverseLast : Endpoint braCut := .inr (.inl (.inr (.inl ())))
theorem bra_reverse_whole_ancestor (a : Context) :
    ∃ old,CancellationResidual braSite (reverseEdges (g:=braSite.reduce) braPath) old ∧ Labelling braSite.net old a a ∧
      old.head?=some (braSite.outsideEnd braReverseFirst) ∧old.getLast?=some (braSite.outsideEnd braReverseLast) :=
  braSite.cancellation_ancestor (.bra 2) (bra_target_labels a).reverse braReverseFirst braReverseLast rfl rfl
/-- The low shell remains nonempty while the high tail is completely arbitrary. -/
def input (tail : Context) : Context := (Context.empty.cons (.star .empty)).replace 2 tail
example (tail : Context) : (input tail).get 0=.star .empty := rfl
example (tail : Context) : input tail ≠ Context.empty := by
  intro equal
  have impossible := congrArg (fun c : Context => c.get 0) equal
  cases impossible
example (tail : Context) := fan_whole_ancestor false (input tail)
example (tail : Context) := fan_whole_ancestor true (input tail)
example (tail : Context) := fan_reverse_whole_ancestor false (input tail)
example (tail : Context) := fan_reverse_whole_ancestor true (input tail)
example (tail : Context) := cro_whole_ancestor (input tail)
example (tail : Context) := cro_reverse_whole_ancestor (input tail)
example (tail : Context) := bra_whole_ancestor (input tail)
example (tail : Context) := bra_reverse_whole_ancestor (input tail)
#print axioms fan_whole_ancestor
#print axioms fan_reverse_whole_ancestor
#print axioms fan_source_labels
#print axioms crossed_fan_not_labelled
#print axioms cro_whole_ancestor
#print axioms bra_reverse_whole_ancestor
theorem fan_context_change_impossible (branch : Bool) (a b : Context) (different : a≠b) :
    ¬Labelling fanSite.reduce (fanPath branch) a b :=
  fun labels => different ((fan_target_labels branch a).output_unique labels)
theorem cro_context_change_impossible (a b : Context) (different : a≠b) :
    ¬Labelling croSite.reduce croPath a b :=
  fun labels => different ((cro_target_labels a).output_unique labels)
theorem bra_context_change_impossible (a b : Context) (different : a≠b) :
    ¬Labelling braSite.reduce braPath a b :=
  fun labels => different ((bra_target_labels a).output_unique labels)
#print axioms cro_context_change_impossible
#print axioms bra_context_change_impossible
private def fanBoundary : Bool⊕Bool → Bool := Sum.elim (fun _ => true) (fun _ => false)
private def fanFlow : FlowBalance fanSite.net fanBoundary where
  nodes := Sum.elim Empty.elim (Sum.elim (fun _ => true) (fun _ => false))
  vertices := fun _ => false
  wiring := by
    rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
    · exact nomatch k
    · cases p <;> rfl
    · cases p <;> rfl
    · rfl
    · rfl
    · exact nomatch w
    · cases d <;> rfl

theorem fan_root_direction (branch : Bool) (a : Context) :
    ∃ old,CancellationResidual fanSite (fanPath branch) old ∧ Labelling fanSite.net old a a ∧
      Forward fanSite.net old ∧ old.head?=some (.inr (.inl (.inl branch))) ∧
      old.getLast?=some (fanSite.outsideEnd (fanLast branch)) :=
  fanSite.cancellation_root_ancestor (.fan 2) fanFlow (.inl branch) rfl
    (fan_target_labels branch a) rfl (fanLast branch) rfl
#print axioms fan_root_direction

-- The one actual W route is chosen before all contexts, in both directions.
theorem fan_uniform (frontier : Bool⊕Bool) : ∃ route : List (Endpoint fanSite.net),
    ∀ a b,Labelling fanSite.net route a b ↔
      Labelling (Schema.fanCancel 2).right.net [.inr (.inl frontier)] a b := by
  obtain ⟨route,_,_,_,replay⟩ := fanSite.cancellation_uniform_replay (.fan 2) frontier
  exact ⟨route,replay⟩
theorem cro_uniform (frontier : Unit⊕Unit) : ∃ route : List (Endpoint croSite.net),
    ∀ a b,Labelling croSite.net route a b ↔
      Labelling (Schema.croCancel 2).right.net [.inr (.inl frontier)] a b := by
  obtain ⟨route,_,_,_,replay⟩ := croSite.cancellation_uniform_replay (.cro 2) frontier
  exact ⟨route,replay⟩
theorem bra_uniform (frontier : Unit⊕Unit) : ∃ route : List (Endpoint braSite.net),
    ∀ a b,Labelling braSite.net route a b ↔
      Labelling (Schema.braCancel 2).right.net [.inr (.inl frontier)] a b := by
  obtain ⟨route,_,_,_,replay⟩ := braSite.cancellation_uniform_replay (.bra 2) frontier
  exact ⟨route,replay⟩
#print axioms fan_uniform
#print axioms cro_uniform
#print axioms bra_uniform

theorem fan_fixed_ancestor_replays (branch : Bool) : ∃ old,
    CancellationResidual fanSite (fanPath branch) old ∧Labelling fanSite.net old Context.empty Context.empty ∧
    ∀ a b,Labelling fanSite.net old a b →Labelling fanSite.reduce (fanPath branch) a b := by
  obtain ⟨old,residual,labels,_,_,replay⟩ := fanSite.cancellation_relabelling_ancestor (.fan 2)
    (fan_target_labels branch Context.empty) (fanFirst branch) (fanLast branch) rfl rfl
  exact ⟨old,residual,labels,replay⟩
theorem cro_fixed_ancestor_replays : ∃ old,
    CancellationResidual croSite croPath old ∧Labelling croSite.net old Context.empty Context.empty ∧
    ∀ a b,Labelling croSite.net old a b →Labelling croSite.reduce croPath a b := by
  obtain ⟨old,residual,labels,_,_,replay⟩ := croSite.cancellation_relabelling_ancestor (.cro 2)
    (cro_target_labels Context.empty) croFirst croLast rfl rfl
  exact ⟨old,residual,labels,replay⟩
theorem bra_fixed_ancestor_replays : ∃ old,
    CancellationResidual braSite braPath old ∧Labelling braSite.net old Context.empty Context.empty ∧
    ∀ a b,Labelling braSite.net old a b →Labelling braSite.reduce braPath a b := by
  obtain ⟨old,residual,labels,_,_,replay⟩ := braSite.cancellation_relabelling_ancestor (.bra 2)
    (bra_target_labels Context.empty) braFirst braLast rfl rfl
  exact ⟨old,residual,labels,replay⟩
#print axioms fan_fixed_ancestor_replays
#print axioms cro_fixed_ancestor_replays
#print axioms bra_fixed_ancestor_replays

private def writerPath (branch : Bool) : List (Endpoint fanSite.net) := (fanSource branch).take 3
private theorem writer_labels (branch : Bool) (a : Context) :
    Labelling fanSite.net (writerPath branch) a (InitialOffsets.fanAt 2 branch a) := by
  have rule := InitialOffsets.Event.apply_rel (.fan 2 branch) a
  exact .cons (.node (g:=fanSite.net) (.inr (.inl ())) (.inr branch) (.inl ()) (.direct rule))
    (.cons (.transparent (g:=fanSite.net) (.inr ()) false _) (.single _ _))

theorem actual_writer_branch_fixed (branch : Bool) (a : Context) :
    ∃ q : Bool,q=branch ∧∀ input output,Labelling fanSite.net (writerPath branch) input output →
      ∃ before,Traversal 2 (.op .fan) (.inr q) (.inl ()) before output := by
  obtain ⟨q,uniform⟩ := fanSite.rooted_control_writer (writer_labels branch a) (.inl branch) rfl rfl
  obtain ⟨before,actual⟩ := uniform a (InitialOffsets.fanAt 2 branch a) (writer_labels branch a)
  have direct : Traversal 2 (.op .fan) (.inr branch) (.inl ()) a (InitialOffsets.fanAt 2 branch a) :=
    .direct (InitialOffsets.Event.apply_rel (.fan 2 branch) a)
  have ports := (actual.forward_predecessor_unique trivial direct trivial).1
  exact ⟨q,Sum.inr.inj ports,uniform⟩
#print axioms actual_writer_branch_fixed
end Lamping.Checks.Phase5Review.Cancellations






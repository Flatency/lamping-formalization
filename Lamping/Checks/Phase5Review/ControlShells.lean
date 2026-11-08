import Lamping.Lamping.BindingSuffixUniqueness
import Lamping.Lamping.InitialMatching
import Lamping.Lamping.InitialFullIndependence
import Lamping.Lamping.ActionTypedInputs
import Lamping.Lamping.CancellationIndependence
import Lamping.Lamping.ActionPendingReplay
import Lamping.Lamping.ControlConstructorTransport
import Lamping.Lamping.ControlShellEmbeddings
namespace Lamping.Checks.Phase5Review.ControlShells
open AG AG.InitialOffsets

theorem fan_critical (a b : Context) (left right : Bool) :
    Context.SameShell 3 (fanAt 2 left a) (fanAt 2 right b) ↔
      left=right ∧Context.SameShell 3 a b := fanAt_same_shell_iff a b 2 3 (by decide) left right

theorem wrong_fan_branch (a b : Context) :
    ¬Context.SameShell 3 (fanAt 2 false a) (fanAt 2 true b) := by
  intro same
  have impossible := (fan_critical a b false true).mp same
  cases impossible.1

theorem cro_critical (a b : Context) :
    Context.SameShell 3 (croAt 2 a) (croAt 2 b) ↔Context.SameShell 2 a b :=
  croAt_same_shell_iff a b 2 3 (by decide)

theorem bra_critical (a b : Context) :
    Context.SameShell 3 (braAt 2 a) (braAt 2 b) ↔Context.SameShell 4 a b :=
  braAt_same_shell_iff a b 2 3 (by decide)

private def lowShell := Context.empty.cons (.star .empty)
private def a := lowShell
private def croB := lowShell.replace 2 (Context.empty.cons (.star .empty))
private def braB := lowShell.replace 3 (Context.empty.cons (.star .empty))

theorem cro_unshifted_guard_false : Context.SameShell 3 (croAt 2 a) (croAt 2 croB) ∧
    ¬Context.SameShell 3 a croB := by
  constructor
  · apply (cro_critical a croB).mpr
    intro k bound
    simp only [a,croB,Context.replace]
    rw [if_pos (by omega : k<2)]
  · intro same
    have impossible := same 2 (by decide)
    change Level.empty=Level.star .empty at impossible
    cases impossible

theorem bra_unshifted_guard_false : Context.SameShell 3 a braB ∧
    ¬Context.SameShell 3 (braAt 2 a) (braAt 2 braB) := by
  constructor
  · intro k bound
    simp only [a,braB,Context.replace]
    rw [if_pos bound]
  · intro same
    have original := (bra_critical a braB).mp same
    have impossible := original 3 (by decide)
    change Level.empty=Level.star .empty at impossible
    cases impossible

example (tail : Context) : Context.SameShell 3 (fanAt 2 true (lowShell.replace 3 tail))
    (fanAt 2 true lowShell) := by
  apply (fan_critical _ _ true true).mpr
  refine ⟨rfl,?_⟩
  intro k bound
  exact Context.replace_low _ _ bound
#print axioms fan_critical
#print axioms wrong_fan_branch
#print axioms cro_unshifted_guard_false
#print axioms bra_unshifted_guard_false

theorem fan_inverse_changed_tail (tail : Context) : ∃ result,
    Traversal 2 (.op .fan) (.inl ()) (.inr false)
      (lowShell.replace 2 (tail.cons (.o .empty))) result :=
  Traversal.control_inverse_transfer (Or.inl rfl)
    (Traversal.inverse (Passage.fanO (i:=2) Context.empty Context.empty .empty)) _ rfl

theorem cro_inverse_changed_tail (tail : Context) : ∃ result,
    Traversal 2 (.op .cro) (.inl ()) (.inr ())
      (lowShell.replace 2 (tail.cons .empty)) result :=
  Traversal.control_inverse_transfer (Or.inr (Or.inl rfl))
    (Traversal.inverse (Passage.cro (i:=2) Context.empty Context.empty)) _ rfl

theorem bra_inverse_changed_tail (tail : Context) : ∃ result,
    Traversal 2 (.op .bra) (.inl ()) (.inr ())
      (lowShell.replace 2 (tail.cons (.pair (.o .empty) (.star .empty)))) result :=
  Traversal.control_inverse_transfer (Or.inr (Or.inr rfl))
    (Traversal.inverse (Passage.bra (i:=2) Context.empty Context.empty (.o .empty) (.star .empty))) _ rfl
#print axioms fan_inverse_changed_tail
#print axioms cro_inverse_changed_tail
#print axioms bra_inverse_changed_tail

#print axioms Marker.binder_shell_stable_node
#print axioms PathSite.binding_control_input_stable
#print axioms PathSite.fan_new_app_root_inputs
#print axioms PathSite.cro_new_lam_ctx_root_inputs
#print axioms PathSite.bra_new_lam_bind_root_inputs
#print axioms PathSite.cancellation_independence
#print axioms initial_cancellation_trace_independence
#print axioms PathSite.action_typed_root_inputs
/-- A genuine level-7 closed nested binder has an index-1 suffix. Every
other witness, with its own assignment, is identified by the NEW generic API. -/
theorem actual_nested_suffix_generic_unique :
    ∃ es : RootAccess (encode 7 (.lam (.lam (.app (.var 1) (.var 1))))).net (.inl ()),
      BindingSuffix (encode 7 (.lam (.lam (.app (.var 1) (.var 1))))).net es.val 1 ∧
      ∀ k,BindingSuffix (encode 7 (.lam (.lam (.app (.var 1) (.var 1))))).net es.val k → k=1 := by
  let t : Lambda.Term := .lam (.lam (.app (.var 1) (.var 1)))
  have closed : Lambda.Closed t := by change 1<2 ∧1<2; decide
  obtain ⟨es,word⟩ := encode_closed_access_coverage t closed 7
    ⟨[.body,.body,.arg],by decide⟩ Context.empty
  have lookup : Lambda.subtermAt t (accessWord (encode 7 t).net es.val)=some (.var 1) := by rw [word]; rfl
  have witness := (encode_closed_var_observes t closed 7 es 1 lookup).2.1
  have bundle := encode_closed_ordinary_invariants t closed 7
  exact ⟨es,witness,fun k other => bundle.binding_suffix_unique es other witness⟩
#print axioms actual_nested_suffix_generic_unique
end Lamping.Checks.Phase5Review.ControlShells





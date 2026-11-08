import Lamping.Lamping.RootBinderUniform
import Lamping.Lamping.MarkerBinderUniform
import Lamping.Lamping.ControlConstructorTransport
import Lamping.Lamping.ControlPrincipalSuffixes
import Lamping.Lamping.MatchedControlInputs
namespace Lamping.AG
open Graph
private theorem primary_heq {f h : Op} (same : f=h) :
    HEq (Sum.inl () : Port (.op f)) (Sum.inl () : Port (.op h)) := by subst h; rfl
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- A fixed actual root-to-binding path preserves the original low inverse
control branch across assignments. The same binder occurrence is locked by
old Nesting; its physical context prefix supplies the real control writer. -/
theorem PathSite.binding_control_input_stable_root
    {root : B} (inputs : RootInputs site.net root) (nesting : Nesting site.net root)
    (transparency : Transparency site.net root)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (lam : s.passive=.lam)
    (below : s.low<s.high)
    (body bind : Port (.op s.passive)) (bodyRole : HEq body lamBody) (bindRole : HEq bind lamBind)
    {es : List (Endpoint site.net)} {input output inverseOutput : Context}
    (labels : Labelling site.net es input output) (forward : Forward site.net es)
    (rooted : es.head?=some (.inr (.inl root)))
    (finish : es.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),bind⟩)))
    (q : Aux s.active) (reference : Traversal s.low (.op s.active) (.inl ()) (.inr q) output inverseOutput) :
    ∀ requested final,Labelling site.net es requested final →
      ∃ result,Traversal s.low (.op s.active) (.inl ()) (.inr q) final result := by
  have nodeLabel : site.net.label (.inr (.inr ()))=label .lam s.high := by
    change label s.passive s.high=label .lam s.high
    rw [lam]
  have ctxRole : HEq (Sum.inl () : Port (.op s.passive)) (Sum.inl () : Port (.op .lam)) := primary_heq lam
  obtain ⟨pre,loop,middle,binding,split,binderEq,preLast,preLabels⟩ := transparency es input output
    (.inr (.inr ())) (.inl ()) body bind (congrArg Label.sort nodeLabel) ctxRole bodyRole bindRole
    rooted finish forward labels
  have shell : Context.SameShell s.high middle output := by
    have actual := binding.shell
    rw [binderEq] at actual
    exact actual
  have stable := Marker.binder_shell_stable_node_rootInputs inputs nesting transparency (.inr (.inr ()))
    (.inl ()) body bind s.high nodeLabel ctxRole bodyRole bindRole es pre loop input middle output
    rooted forward finish labels split preLabels preLast shell
  have preRoot : pre.head?=some (.inr (.inl root)) := by
    cases pre with
    | nil => exact False.elim (preLabels.nonempty rfl)
    | cons e tail => simpa only [split,List.cons_append,List.head?_cons] using rooted
  obtain ⟨chosen,writer⟩ := site.rooted_control_writer preLabels root preRoot preLast
  obtain ⟨writerInput,referenceWriter⟩ := writer input middle preLabels
  obtain ⟨payload,atReference⟩ := referenceWriter.reverse.control_inverse_transfer control output (shell s.low below).symm
  have same := atReference.control_auxiliary_unique control reference
  subst chosen
  intro requested final changed
  obtain ⟨front,preSplit⟩ := List.getLast?_eq_some_iff.mp preLast
  have changed' := changed
  rw [split,preSplit,List.append_assoc,List.singleton_append] at changed'
  obtain ⟨newMiddle,newPrefix,newTail⟩ := changed'.split_segment
  have prefixLabels : Labelling site.net pre requested newMiddle := by simpa only [preSplit] using newPrefix
  have newShell := stable requested newMiddle final changed prefixLabels
  obtain ⟨newWriterInput,newWriter⟩ := writer requested newMiddle prefixLabels
  exact newWriter.reverse.control_inverse_transfer control final (newShell s.low below).symm
end
end Lamping.AG




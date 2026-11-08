import Lamping.Lamping.SourceControlWriterSuffix
import Lamping.Lamping.ControlConstructorTransport
import Lamping.Lamping.GlobalPathInvariants
namespace Lamping.AG
open Graph
private theorem primary_heq {f h : Op} (same : f=h) :
    HEq (Sum.inl () : Port (.op f)) (Sum.inl () : Port (.op h)) := by subst h; rfl
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- A concrete source binding access has some genuine low inverse-control
branch at its final context. The writer comes from its SAME-assignment old-T
prefix, and its real loop shell transfers the low constructor to the final
context. No RHS reference or full/root totality property is supplied. -/
theorem PathSite.source_binding_control_branch
    {root : B} (transparency : Transparency site.net root)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (lam : s.passive=.lam)
    (below : s.low<s.high)
    (body bind : Port (.op s.passive)) (bodyRole : HEq body lamBody) (bindRole : HEq bind lamBind)
    {es : List (Endpoint site.net)} {input output : Context}
    (labels : Labelling site.net es input output) (forward : Forward site.net es)
    (rooted : es.head?=some (.inr (.inl root)))
    (finish : es.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),bind⟩))) :
    ∃ (q : Aux s.active) (middle : Context),
      Traversal s.low (.op s.active) (.inl ()) (.inr q) output middle := by
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
  have preRoot : pre.head?=some (.inr (.inl root)) := by
    cases pre with
    | nil => exact False.elim (preLabels.nonempty rfl)
    | cons e tail => simpa only [split,List.cons_append,List.head?_cons] using rooted
  obtain ⟨q,writer⟩ := site.rooted_control_writer preLabels root preRoot preLast
  obtain ⟨writerInput,actual⟩ := writer input middle preLabels
  obtain ⟨result,inverse⟩ := actual.reverse.control_inverse_transfer control output (shell s.low below).symm
  exact ⟨q,result,inverse⟩
end
end Lamping.AG

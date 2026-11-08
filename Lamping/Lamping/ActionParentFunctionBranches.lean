import Lamping.Lamping.ActionFunctionBranches
import Lamping.Lamping.RootMatchedControlInputs
import Lamping.Lamping.MatchingSharedSyntaxEvaluation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- A finite original whole assignment and its specified literal prefix
fix the piece input by output determinism. There is no input-totality premise. -/
theorem SourceEdgeFragment.piece_labels_at_prefix
    {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    {a b seam : Context} (whole : Labelling site.net fragment.access.val a b)
    (before : Labelling site.net (fragment.before++[fragment.fromEndpoint]) a seam) :
    Labelling site.net fragment.segments seam b := by
  obtain ⟨tail,segments⟩ := List.head?_eq_some_iff.mp fragment.start
  rw [fragment.literal,segments] at whole
  obtain ⟨middle,prefixLabels,piece⟩ := whole.split_segment
  have same := prefixLabels.output_unique before
  subst middle
  simpa only [segments] using piece

/-- Identify a real reader branch at the specified prefix assignment of
this actual function fragment, even if other inputs do not label the path. -/
theorem SourceEdgeFragment.function_branch_at_prefix
    {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (first : fragment.fromEndpoint=.inl ⟨.inr (.inr ()),.inl ()⟩) :
    ∃ q : Aux s.active,
      (∀ input output,Labelling site.net fragment.segments input output →
        ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr q) input middle) ∧
      ∀ {input output seam},Labelling site.net fragment.access.val input output →
        Labelling site.net (fragment.before++[fragment.fromEndpoint]) input seam →
        ∀ {r middle},Traversal s.low (.op s.active) (.inl ()) (.inr r) seam middle → q=r := by
  obtain ⟨q,uniform⟩ := fragment.function_control_branch site control first
  refine ⟨q,uniform,?_⟩
  intro input output seam whole before r middle reader
  obtain ⟨actual,turn⟩ := uniform seam output (fragment.piece_labels_at_prefix site whole before)
  exact turn.control_auxiliary_unique control reader
theorem SourceEdgeFragment.parent_function_control_branch
    {current term : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (passive : s.passive=.app)
    (role : SourceDeparture term .fn edge.fromPort)
    (parent : RootAccess site.net root) (ctx : Port (.op s.passive)) (ctxRole : HEq ctx appCtx)
    (word : position=accessWord site.net parent.val++[.fn])
    (finish : parent.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),ctx⟩))) :
    ∃ q : Aux s.active,
      (∀ input output,Labelling site.net fragment.segments input output →
        ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr q) input middle) ∧
      (∀ requested seam,Labelling site.net parent.val requested seam →
        ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr q) seam middle) := by
  have lab : site.net.label (.inr (.inr ()))=label .app s.high := by
    change label s.passive s.high=label .app s.high
    rw [passive]
  have funRole : HEq (Sum.inl () : Port (.op s.passive)) (Sum.inl () : Port (.op .app)) := by
    cases s <;> cases passive <;> exact HEq.rfl
  obtain ⟨child,tail,split,childWord,_typed,relabel⟩ := matching.function_child_input_root inputs parent
    (.inr (.inr ())) ctx (.inl ()) s.high lab ctxRole funRole finish
  have same : child=fragment.access := matching.accessWord_injective
    (childWord.trans (fragment.word.trans word).symm)
  rw [same] at split
  have parentSplit := (fragment.child_prefix matching role parent word).2
  have segments : fragment.segments=(.inl ⟨.inr (.inr ()),.inl ()⟩)::tail :=
    List.append_cancel_left (parentSplit.symm.trans split)
  have start : fragment.fromEndpoint=.inl ⟨.inr (.inr ()),.inl ()⟩ :=
    Option.some.inj (fragment.start.symm.trans (by rw [segments]; rfl))
  obtain ⟨q,uniform⟩ := fragment.function_control_branch site control start
  refine ⟨q,uniform,?_⟩
  intro requested seam parentLabels
  obtain ⟨output,_whole,suffix⟩ := relabel requested seam parentLabels
  rw [←segments] at suffix
  exact uniform seam output suffix
end
end Lamping.AG
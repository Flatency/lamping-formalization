import Lamping.Lamping.CancellationFragmentTransport
import Lamping.Lamping.ControlPrincipalPrefixes
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- The actual typed function fragment fixes its reader auxiliary for every
labelling of that same literal fragment. The physical start role is explicit;
no conclusion identifying different occurrences or branches is assumed. -/
theorem SourceEdgeFragment.function_control_branch
    {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (first : fragment.fromEndpoint=.inl ⟨.inr (.inr ()),.inl ()⟩) :
    ∃ q : Aux s.active,∀ input output,Labelling site.net fragment.segments input output →
      ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr q) input middle := by
  obtain ⟨a,b,whole⟩ := fragment.access.property.1.1
  obtain ⟨middle,_before,piece⟩ := fragment.assignments a b whole
  exact site.typed_active_control_uniform control piece fragment.fragment_typed
    (fragment.start.trans (congrArg some first))

/-- Two candidate fixed branches are compared on ONE real assignment of
ONE function fragment. Their root-prefix inputs need not be identified. -/
theorem SourceEdgeFragment.function_control_branch_unique
    {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    {q r : Aux s.active}
    (left : ∀ input output,Labelling site.net fragment.segments input output →
      ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr q) input middle)
    (right : ∀ input output,Labelling site.net fragment.segments input output →
      ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr r) input middle) : q=r := by
  obtain ⟨a,b,whole⟩ := fragment.access.property.1.1
  obtain ⟨middle,_before,piece⟩ := fragment.assignments a b whole
  obtain ⟨leftOutput,leftTurn⟩ := left middle b piece
  obtain ⟨rightOutput,rightTurn⟩ := right middle b piece
  exact leftTurn.control_auxiliary_unique control rightTurn

/-- Equality concerns actual fragment literals, not syntax labels or source
edge values. It transports the fixed reader branch between two occurrences. -/
theorem SourceEdgeFragment.equal_function_control_branch
    {current : LTerm} {root : B} {edge otherEdge : SourceEdge} {position otherPosition : Path}
    (firstFragment : SourceEdgeFragment current site.net root edge position)
    (secondFragment : SourceEdgeFragment current site.net root otherEdge otherPosition)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (first : firstFragment.fromEndpoint=.inl ⟨.inr (.inr ()),.inl ()⟩)
    (same : firstFragment.segments=secondFragment.segments) :
    ∃ q : Aux s.active,
      (∀ input output,Labelling site.net firstFragment.segments input output →
        ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr q) input middle) ∧
      (∀ input output,Labelling site.net secondFragment.segments input output →
        ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr q) input middle) := by
  obtain ⟨q,uniform⟩ := firstFragment.function_control_branch site control first
  refine ⟨q,uniform,?_⟩
  intro input output labels
  exact uniform input output (same ▸ labels)
end
end Lamping.AG
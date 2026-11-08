import Lamping.Lambda.LabelHeadCutComponents
namespace Lamping.Lambda.Labelled

/-- INIT fixes the actual incoming root edge. If that edge is traversed in
either orientation, one actual traversal endpoint is the head boundary. -/
theorem SourceTraverse.root_head_boundary
    (initial : INIT t) (boundary : ctx.AtHead app lam)
    (actual : SourceTraverse (sourceEdges env ctx t) a e b)
    (root : Label.atom e.atom=t.label) : a.AtHead app lam ∨ b.AtHead app lam := by
  have rootMember : sourceEdge env ctx t∈sourceEdges env ctx t := by
    cases t <;> exact List.mem_cons_self
  have rootLabel : (sourceEdge env ctx t).atom=t.label := by cases t <;> rfl
  cases actual with
  | forward member atomic =>
    have same := sourceEdges_unique initial member rootMember (atomic.trans (root.trans rootLabel.symm))
    cases same
    have source : (sourceEdge env ctx t).fromPort=ctx := by cases t <;> rfl
    exact .inl (source.symm ▸ boundary)
  | backward member atomic =>
    have same := sourceEdges_unique initial member rootMember (atomic.trans (root.trans rootLabel.symm))
    cases same
    have source : (sourceEdge env ctx t).fromPort=ctx := by cases t <;> rfl
    exact .inr (source.symm ▸ boundary)

/-- With both endpoints away from the head, every actual incoming boundary
edge is excluded. This is derived for the selected component, and does not
remove its root application/lambda node or its outgoing internal edges. -/
theorem HeadFreeWalk.root_edge_absent
    (walk : HeadFreeWalk (sourceEdges env ctx t) app lam a word b)
    (initial : INIT t) (boundary : ctx.AtHead app lam)
    (start : ¬a.AtHead app lam) (finish : ¬b.AtHead app lam) :
    ∀ e∈word,Label.atom e.atom≠t.label := by
  induction walk with
  | edge actual =>
    intro e member same
    cases List.mem_singleton.mp member
    rcases actual.root_head_boundary initial boundary same with first | last
    · exact start first
    · exact finish last
  | @join a first middle next rest b left turn right hl hr =>
    intro e member
    rcases List.mem_append.mp member with before | after
    · exact hl start turn.avoids_head.1 e before
    · exact hr turn.avoids_head.2 finish e after

/-- The real root-head degree component has strict root-edge avoidance,
proved after selecting body versus argument from the actual generated walk. -/
theorem History.root_head_degree_strict_region {body argument : LTerm}
    (history : History ps (.app beta (.lam alpha body) argument) u)
    (initial : INIT (.app beta (.lam alpha body) argument))
    (outside : ¬alpha.Supported region) (degree : u.degreeAt p=some l)
    (support : l.Supported region) :
    (l.Supported (SourceRegion body) ∧ ∀ e∈l.edgeWord,Label.atom e.atom≠body.label) ∨
      (l.Supported (SourceRegion argument) ∧ ∀ e∈l.edgeWord,Label.atom e.atom≠argument.label) := by
  obtain ⟨appId,lamId,appDifferent,lamDifferent,route⟩ :=
    history.generated_head_free_degree initial SourceSubterm.nil outside degree support
  have start : ¬(SourcePort.appFn appId).AtHead beta alpha := appDifferent
  have finish : ¬(SourcePort.lamContext lamId).AtHead beta alpha := lamDifferent
  rcases route.head_free_walk.root_head_one_component initial appDifferent with inBody | inArgument
  · have bodyINIT : INIT body := initial.subterm (p := [.fn,.body]) (by simp [LTerm.subterm])
    exact .inl ⟨(Label.supported_iff_within _ _).mpr inBody.walk.within_source,
      inBody.root_edge_absent bodyINIT rfl start finish⟩
  · have argINIT : INIT argument := initial.subterm (p := [.arg]) (by simp [LTerm.subterm])
    exact .inr ⟨(Label.supported_iff_within _ _).mpr inArgument.walk.within_source,
      inArgument.root_edge_absent argINIT rfl start finish⟩
end Lamping.Lambda.Labelled

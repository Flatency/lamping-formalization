import Lamping.Lambda.LabelHeadCutRoots
namespace Lamping.Lambda.Labelled

/-- Each original edge of an actual contextual beta head touches a head
port. INIT identifies it globally even when its context endpoint is outside
the head subtree, so no global-root or external-port assumption is used. -/
theorem SourceTraverse.contextual_head_boundary {body argument : LTerm}
    (atHead : SourceSubterm [] .external t site env ctx (.app beta (.lam alpha body) argument))
    (initial : INIT t) (actual : SourceTraverse (sourceEdges [] .external t) a e b)
    (headAtom : Label.atom e.atom=beta ∨ Label.atom e.atom=alpha) :
    a.AtHead beta alpha ∨ b.AtHead beta alpha := by
  have betaMember : (⟨beta,ctx,.appContext beta⟩ : SourceEdge)∈sourceEdges [] .external t :=
    atHead.edges_subset _ List.mem_cons_self
  have alphaMember : (⟨alpha,.appFn beta,.lamContext alpha⟩ : SourceEdge)∈sourceEdges [] .external t :=
    atHead.edges_subset _ (List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self))
  have classify : ∀ edge∈sourceEdges [] .external t,
      (edge.atom=beta ∨ edge.atom=alpha) →
      edge.fromPort.AtHead beta alpha ∨ edge.toPort.AtHead beta alpha := by
    intro edge member same
    rcases same with betaEq | alphaEq
    · have equal := sourceEdges_unique initial member betaMember betaEq
      cases equal
      exact .inr rfl
    · have equal := sourceEdges_unique initial member alphaMember alphaEq
      cases equal
      exact .inr rfl
  cases actual with
  | forward member atomic => exact classify _ member (headAtom.imp (atomic.trans ·) (atomic.trans ·))
  | backward member atomic =>
    rcases classify _ member (headAtom.imp (atomic.trans ·) (atomic.trans ·)) with first | last
    · exact .inr first
    · exact .inl last

/-- A whole restricted walk with live endpoints cannot contain an edge
incident with a head boundary. At every join both adjacent endpoints are
also live, so no internal occurrence or reverse traversal is overlooked. -/
theorem HeadFreeWalk.excludes_boundary_atom
    (walk : HeadFreeWalk edges app lam a word b)
    (start : ¬a.AtHead app lam) (finish : ¬b.AtHead app lam)
    (boundary : ∀ {s e r},SourceTraverse edges s e r → Label.atom e.atom=label →
      s.AtHead app lam ∨ r.AtHead app lam) :
    ∀ e∈word,Label.atom e.atom≠label := by
  induction walk with
  | edge actual =>
    intro e member same
    cases List.mem_singleton.mp member
    rcases boundary actual same with first | last
    · exact start first
    · exact finish last
  | @join a first middle next rest b left turn right hl hr =>
    intro e member
    rcases List.mem_append.mp member with before | after
    · exact hl start turn.avoids_head.1 e before
    · exact hr turn.avoids_head.2 finish e after

/-- Contextual head-edge exclusion is an actual route result, not a claim
that the body and argument have disjoint external binder environments. -/
theorem History.contextual_head_atoms_absent {body argument : LTerm}
    (history : History ps t u) (initial : INIT t)
    (atHead : SourceSubterm [] .external t site env ctx (.app beta (.lam alpha body) argument))
    (outside : ¬alpha.Supported region) (degree : u.degreeAt p=some l)
    (support : l.Supported region) :
    ∀ e∈l.edgeWord,Label.atom e.atom≠beta ∧ Label.atom e.atom≠alpha := by
  obtain ⟨appId,lamId,appDifferent,lamDifferent,route⟩ :=
    history.generated_head_free_degree initial atHead outside degree support
  have walk := route.head_free_walk
  have noBeta := walk.excludes_boundary_atom appDifferent lamDifferent (fun actual same =>
    actual.contextual_head_boundary atHead initial (.inl same))
  have noAlpha := walk.excludes_boundary_atom appDifferent lamDifferent (fun actual same =>
    actual.contextual_head_boundary atHead initial (.inr same))
  exact fun e member => ⟨noBeta e member,noAlpha e member⟩
end Lamping.Lambda.Labelled

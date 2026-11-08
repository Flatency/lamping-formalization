import Lamping.Lambda.LabelContextualHeadCut
namespace Lamping.Lambda.Labelled

/-- Compose real source occurrence paths, retaining their actual binder
and incoming-port coordinates. -/
theorem SourceSubterm.append
    (outer : SourceSubterm env ctx t p middleEnv middleCtx subtree)
    (inner : SourceSubterm middleEnv middleCtx subtree q innerEnv innerCtx part) :
    SourceSubterm env ctx t (p++q) innerEnv innerCtx part := by
  induction outer with
  | nil => exact inner
  | fn _ ih => exact .fn (ih inner)
  | arg _ ih => exact .arg (ih inner)
  | body _ ih => exact .body (ih inner)

/-- Regional atomic identity selects the actual edge of an actual original
subtree; the traversal's two endpoints and orientation remain identical. -/
theorem SourceTraverse.region_restrict
    (initial : INIT t) (atRegion : SourceSubterm [] .external t site env ctx subtree)
    (actual : SourceTraverse (sourceEdges [] .external t) a e b)
    (inside : SourceRegion subtree e.atom) : SourceTraverse (sourceEdges env ctx subtree) a e b := by
  obtain ⟨edge,member,atomic⟩ := (SourceRegion.edges subtree env ctx e.atom).mp inside
  cases actual with
  | forward globalMember globalAtomic =>
    have same := sourceEdges_unique initial globalMember (atRegion.edges_subset edge member)
      (globalAtomic.trans atomic.symm)
    cases same
    exact .forward member atomic
  | backward globalMember globalAtomic =>
    have same := sourceEdges_unique initial globalMember (atRegion.edges_subset edge member)
      (globalAtomic.trans atomic.symm)
    cases same
    exact .backward member atomic

/-- Restriction preserves every actual head-free turn as well as every
signed traversal. It adds no component or current-copy choice. -/
theorem HeadFreeWalk.region_restrict
    (walk : HeadFreeWalk (sourceEdges [] .external t) app lam a word b)
    (initial : INIT t) (atRegion : SourceSubterm [] .external t site env ctx subtree)
    (inside : EdgeWord.Within (SourceRegion subtree) word) :
    HeadFreeWalk (sourceEdges env ctx subtree) app lam a word b := by
  induction walk with
  | edge actual => exact .edge (actual.region_restrict initial atRegion (inside _ List.mem_cons_self))
  | join left turn right hl hr =>
    exact .join (hl (fun e member => inside e (List.mem_append_left _ member))) turn
      (hr (fun e member => inside e (List.mem_append_right _ member)))

/-- A true region with an actual head-boundary incoming port has its incoming
edge excluded from any transported degree supported by that region. -/
theorem History.head_region_incoming_absent {body argument : LTerm}
    (history : History ps t u) (initial : INIT t)
    (atHead : SourceSubterm [] .external t headSite headEnv headCtx (.app beta (.lam alpha body) argument))
    (atRegion : SourceSubterm [] .external t regionSite env ctx subtree)
    (boundary : ctx.AtHead beta alpha) (outside : ¬alpha.Supported (SourceRegion subtree))
    (degree : u.degreeAt p=some l) (support : l.Supported (SourceRegion subtree)) :
    ∀ e∈l.edgeWord,Label.atom e.atom≠subtree.label := by
  obtain ⟨appId,lamId,appDifferent,lamDifferent,route⟩ :=
    history.generated_head_free_degree initial atHead outside degree support
  have restricted := route.head_free_walk.region_restrict initial atRegion
    ((Label.supported_iff_within _ _).mp support)
  exact restricted.root_edge_absent (initial.subterm atRegion.lookup) boundary appDifferent lamDifferent

/-- An original INIT head lambda is outside its actual argument region. -/
theorem initial_head_outside_argument {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument)) : ¬alpha.Supported (SourceRegion argument) := by
  intro support
  obtain ⟨n,atomic⟩ := initial.1 alpha
    (List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self))
  have member : alpha∈argument.labels := by rw [atomic] at support ⊢; exact support
  have disjoint := (List.nodup_append.mp (List.nodup_cons.mp initial.2).2).2.2
  exact disjoint alpha List.mem_cons_self alpha member rfl

/-- The strict incoming-edge guard needed by argument-copy transport follows
from the original argument support itself, for arbitrary contextual heads
and arbitrary actual histories. No canonical/internal schedule is assumed. -/
theorem History.argument_degree_incoming_absent {body argument : LTerm}
    (history : History ps t u) (initial : INIT t)
    (atHead : SourceSubterm [] .external t headSite env ctx (.app beta (.lam alpha body) argument))
    (degree : u.degreeAt p=some l) (support : l.Supported (SourceRegion argument)) :
    ∀ e∈l.edgeWord,Label.atom e.atom≠argument.label := by
  exact history.head_region_incoming_absent initial atHead (atHead.append (.arg .nil)) rfl
    (initial_head_outside_argument (initial.subterm atHead.lookup)) degree support

/-- The same guard for the true original body region, whose boundary is the
head lambda's body port, also follows without an extra support hypothesis. -/
theorem History.body_degree_incoming_absent {body argument : LTerm}
    (history : History ps t u) (initial : INIT t)
    (atHead : SourceSubterm [] .external t headSite env ctx (.app beta (.lam alpha body) argument))
    (degree : u.degreeAt p=some l) (support : l.Supported (SourceRegion body)) :
    ∀ e∈l.edgeWord,Label.atom e.atom≠body.label := by
  exact history.head_region_incoming_absent initial atHead (atHead.append (.fn (.body .nil))) rfl
    (initial_head_outside_body_subregion (initial.subterm atHead.lookup)
      (regionSite := []) (by simp [LTerm.subterm])) degree support
end Lamping.Lambda.Labelled


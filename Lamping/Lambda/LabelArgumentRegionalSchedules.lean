import Lamping.Lambda.LabelRegionalSchedules
namespace Lamping.Lambda.Labelled

/-- For every event of a real regional history, use its actual full prefix
from the one INIT source to derive the strict incoming-edge guard. The
prefix is not assumed internal; strictification therefore is not circular. -/
theorem RegionalHistory.strictify_head_region
    (regional : RegionalHistory (SourceRegion subtree) qs u v)
    (pre : History ps t u) (initial : INIT t)
    (atHead : SourceSubterm [] .external t headSite headEnv headCtx (.app beta (.lam alpha body) argument))
    (atRegion : SourceSubterm [] .external t regionSite env ctx subtree)
    (boundary : ctx.AtHead beta alpha) (outside : ¬alpha.Supported (SourceRegion subtree)) :
    RegionalHistory (fun n => SourceRegion subtree n ∧ Label.atom n≠subtree.label) qs u v := by
  induction regional generalizing ps with
  | nil => exact .nil _
  | cons step degree support rest ih =>
    have guard := pre.head_region_incoming_absent initial atHead atRegion boundary outside degree support
    refine .cons step degree ?_ (ih (pre.append (.cons step (.nil _))))
    apply (Label.supported_iff_within _ _).mpr
    intro e member
    exact ⟨(Label.supported_iff_within _ _).mp support e member,guard e member⟩

/-- Explicit support in the original argument at every actual event is
sufficient for whole internality. Strict guards are derived, and no
canonicality or final-degree-only premise is substituted for the colours. -/
theorem RegionalHistory.argument_internal
    (regional : RegionalHistory (SourceRegion argument) ps t u) (initial : INIT t)
    (atHead : SourceSubterm [] .external t headSite env ctx (.app beta (.lam alpha body) argument)) :
    ∀ p∈ps,∃ suffix,p=(headSite++[.arg])++suffix := by
  have atArgument := atHead.append (SourceSubterm.arg SourceSubterm.nil)
  have strict := regional.strictify_head_region (.nil t) initial atHead atArgument rfl
    (initial_head_outside_argument (initial.subterm atHead.lookup))
  exact strict.internal_of_strict_region initial atArgument.lookup

/-- The actual original function-body region has the analogous sufficient
per-event support criterion. Argument holes are not erased by assumption. -/
theorem RegionalHistory.body_internal
    (regional : RegionalHistory (SourceRegion body) ps t u) (initial : INIT t)
    (atHead : SourceSubterm [] .external t headSite env ctx (.app beta (.lam alpha body) argument)) :
    ∀ p∈ps,∃ suffix,p=(headSite++[.fn,.body])++suffix := by
  have atBody := atHead.append (SourceSubterm.fn (SourceSubterm.body SourceSubterm.nil))
  have strict := regional.strictify_head_region (.nil t) initial atHead atBody rfl
    (initial_head_outside_body_subregion (initial.subterm atHead.lookup)
      (regionSite := []) (by simp [LTerm.subterm]))
  exact strict.internal_of_strict_region initial atBody.lookup
end Lamping.Lambda.Labelled


import Lamping.Lambda.UncreatedEdgeLabels
import Lamping.Lambda.LabelFreshMarkerParsing
namespace Lamping.Lambda.Labelled

/-- Every actual created incoming edge contains an outer marker of the
fired degree. Result/copy overlap is allowed, including at the root. -/
theorem StepAt.created_label_not_safe
    {source target body argument current : LTerm} {site edge : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (lookup : target.subterm edge=some current)
    (created : BetaCreatedIncoming body site edge) :
    ¬current.label.OuterBarsSafe (fun payload=>payload≠alpha) := by
  intro safe
  rcases betaCreatedIncoming_iff.mp created with result | ⟨copySite,occurs,equal⟩
  · rw [result] at lookup
    have currentEq : current=LTerm.contract beta alpha body argument :=
      Option.some.inj (lookup.symm.trans (step.contract_lookup redex))
    rw [currentEq,LTerm.contract,label_prepend] at safe
    have overSafe := ((Label.outerBarsSafe_concat _ _ _).mp
      ((Label.outerBarsSafe_concat _ _ _).mp safe).1).2
    exact overSafe rfl
  · have localLookup : (LTerm.contract beta alpha body argument).subterm copySite=some current := by
      rw [equal,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    obtain ⟨_,_,labelEq⟩ := LTerm.contract_argument_incoming_label occurs localLookup
    rw [labelEq] at safe
    by_cases root : copySite=[]
    · rw [if_pos root] at safe
      have overSafe := ((Label.outerBarsSafe_concat _ _ _).mp
        ((Label.outerBarsSafe_concat _ _ _).mp safe).1).2
      exact overSafe rfl
    · rw [if_neg root] at safe
      have underSafe := ((Label.outerBarsSafe_concat _ _ _).mp
        ((Label.outerBarsSafe_concat _ _ _).mp safe).2).1
      exact underSafe rfl

/-- Before a fresh degree is fired, exactly the created incoming positions
carry labels absent from the old term. This is about actual positions. -/
theorem StepAt.created_iff_fresh_label
    {source target body argument current : LTerm} {site edge : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠alpha))
    (lookup : target.subterm edge=some current) :
    BetaCreatedIncoming body site edge ↔current.label∉source.labels := by
  constructor
  · intro created member
    exact step.created_label_not_safe redex lookup created
      ((LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ member)
  · exact step.created_of_fresh_label redex lookup

theorem StepAt.created_iff_marker
    {source target body argument current : LTerm} {site edge : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠alpha))
    (lookup : target.subterm edge=some current) :
    BetaCreatedIncoming body site edge ↔
      ¬current.label.OuterBarsSafe (fun payload=>payload≠alpha) := by
  constructor
  · exact step.created_label_not_safe redex lookup
  · intro marked
    apply step.created_of_fresh_label redex lookup
    intro member
    exact marked ((LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ member)

/-- The original INIT and already-complete prefix supply the freshness
condition. No current INIT or arbitrary history completion is used. -/
theorem complete_prefix_created_iff_fresh_label
    {original source target body argument current : LTerm} {site edge : Path} {beta alpha : Label}
    (initial : INIT original) (program : ParallelHistory original.erase source.erase)
    (complete : CompleteDerivation program) (labels : History program.derivation.paths original source)
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (lookup : target.subterm edge=some current) :
    BetaCreatedIncoming body site edge ↔current.label∉source.labels := by
  have degree : source.degreeAt site=some alpha := by
    simp only [LTerm.degreeAt,redex,Option.bind_some,LTerm.degree]
  let actualRedex : RedexOcc source.erase := ⟨site,step.betaAt.redex⟩
  exact step.created_iff_fresh_label redex
    (complete_prefix_outer_bars_fresh initial program complete labels actualRedex degree) lookup

/-- Under the same freshness condition, equal actual target labels cannot
mix a created incoming position with an uncreated one. -/
theorem StepAt.same_label_created_iff
    {source target body argument left right : LTerm} {site leftEdge rightEdge : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠alpha))
    (leftAt : target.subterm leftEdge=some left) (rightAt : target.subterm rightEdge=some right)
    (same : left.label=right.label) :
    BetaCreatedIncoming body site leftEdge ↔BetaCreatedIncoming body site rightEdge := by
  rw [step.created_iff_fresh_label redex sourceSafe leftAt,
    step.created_iff_fresh_label redex sourceSafe rightAt,same]

end Lamping.Lambda.Labelled

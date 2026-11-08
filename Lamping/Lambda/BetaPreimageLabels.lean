import Lamping.Lambda.UncreatedPrerequisiteTransitions
import Lamping.Lambda.FunctionResultPrefixTransport
import Lamping.Lambda.RetainedBodyPrefixTransport
namespace Lamping.Lambda.Labelled

/-- Preserve the label at THIS supplied old occurrence coordinate, rather
than choosing an unrelated old node with a matching label. Only the incoming
edge is required to be uncreated; its node may head a changed subtree. -/
theorem StepAt.beta_preimage_label
    {source target body argument current : LTerm} {site edge oldEdge : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site edge oldEdge)
    (lookup : target.subterm edge=some current)
    (notCreated : ¬BetaCreatedIncoming body site edge) :
    ∃ old,source.subterm oldEdge=some old ∧old.label=current.label := by
  cases origin with
  | context outside =>
    cases current with
    | var stamp index => exact ⟨_,step.context_variable_origin lookup outside,rfl⟩
    | lam stamp inner =>
      obtain ⟨oldBody,oldLookup⟩ := step.context_lambda_origin lookup outside
      exact ⟨_,oldLookup,rfl⟩
    | app stamp fn arg =>
      obtain ⟨oldFn,oldArg,oldLookup⟩ := step.context_app_origin lookup outside
      exact ⟨_,oldLookup,rfl⟩
  | @retained relative old oldLookup nonselected =>
    have nonroot : relative≠[] := by
      intro empty
      exact notCreated (Or.inl (by simp only [empty,List.append_nil]))
    have localLookup : (LTerm.contract beta alpha body argument).subterm relative=some current := by
      rw [LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    refine ⟨old,?_,(contract_retained_node_label oldLookup nonselected localLookup nonroot).symm⟩
    simp only [LTerm.subterm_append,redex,Option.bind_some,LTerm.subterm,oldLookup]
  | @copied copySite relative old occurs oldLookup =>
    have nonroot : relative≠[] := by
      intro empty
      apply notCreated
      apply betaCreatedIncoming_iff.mpr
      exact Or.inr ⟨copySite,occurs,by simp only [empty,List.append_nil]⟩
    have localLookup : (LTerm.contract beta alpha body argument).subterm (copySite++relative)=some current := by
      rw [List.append_assoc,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    rw [LTerm.subterm_append] at localLookup
    cases atCopy : (LTerm.contract beta alpha body argument).subterm copySite with
    | none => simp only [atCopy,Option.bind_none] at localLookup;cases localLookup
    | some copy =>
      rw [atCopy,Option.bind_some] at localLookup
      obtain ⟨original,atOriginal,labelEq⟩ :=
        (LTerm.contract_argument_copy_interior occurs atCopy).nonroot_node localLookup nonroot
      have equal : original=old := Option.some.inj (atOriginal.symm.trans oldLookup)
      refine ⟨old,?_,equal ▸ labelEq⟩
      simp only [LTerm.subterm_append,redex,Option.bind_some,LTerm.subterm,oldLookup]

theorem StepAt.beta_preimage_labelAt
    {source target body argument current : LTerm} {site edge oldEdge : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site edge oldEdge)
    (lookup : target.subterm edge=some current)
    (notCreated : ¬BetaCreatedIncoming body site edge) :
    target.labelAt edge=source.labelAt oldEdge := by
  obtain ⟨old,atOld,labels⟩ := step.beta_preimage_label redex origin lookup notCreated
  simp only [LTerm.labelAt,lookup,atOld,Option.map_some,labels]

/-- Ordered pointwise actual occurrence preimages. The data assert no
label equality or source/target chain property. -/
inductive BetaEdgePreimages (body argument : LTerm) (site : Path) : List Path →List Path →Prop where
  | nil : BetaEdgePreimages body argument site [] []
  | cons : BetaNodePreimage body argument site edge oldEdge →
      BetaEdgePreimages body argument site edges oldEdges →
      BetaEdgePreimages body argument site (edge::edges) (oldEdge::oldEdges)

/-- Pointwise occurrence preimages transport an ordered list of labels.
The relation may change from ARG to body/context at successive positions. -/
theorem StepAt.beta_preimage_ordered_labels
    {source target body argument : LTerm} {site : Path} {edges oldEdges : List Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origins : BetaEdgePreimages body argument site edges oldEdges)
    (lookups : ∀ edge∈edges,∃ current,target.subterm edge=some current)
    (uncreated : ∀ edge∈edges,¬BetaCreatedIncoming body site edge) :
    edges.map target.labelAt=oldEdges.map source.labelAt := by
  induction origins with
  | nil => rfl
  | @cons edge oldEdge edges oldEdges origin rest ih =>
    obtain ⟨current,lookup⟩ := lookups edge List.mem_cons_self
    have first := step.beta_preimage_labelAt redex origin lookup (uncreated edge List.mem_cons_self)
    have tail := ih (fun edge member=>lookups edge (List.mem_cons_of_mem _ member))
      (fun edge member=>uncreated edge (List.mem_cons_of_mem _ member))
    simp only [List.map_cons,first,tail]

end Lamping.Lambda.Labelled

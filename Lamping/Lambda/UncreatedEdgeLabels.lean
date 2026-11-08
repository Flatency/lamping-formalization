import Lamping.Lambda.FirstCreatedIncoming
import Lamping.Lambda.RetainedBodyPrefixTransport
namespace Lamping.Lambda.Labelled

/-- A strict contractum occurrence that is not an inserted argument root
has the label of an actual retained body node or strict argument node.
This is occurrence provenance, without an INIT or injectivity assumption. -/
theorem LTerm.contract_uncreated_label_origin
    (lookup : (LTerm.contract beta alpha body argument).subterm relative=some current)
    (nonroot : relative≠[])
    (notCopy : ¬ArgumentOccurrence body.erase relative) :
    (∃ old,body.subterm relative=some old ∧old.label=current.label) ∨
    (∃ site suffix old,ArgumentOccurrence body.erase site ∧relative=site++suffix ∧
      suffix≠[] ∧argument.subterm suffix=some old ∧old.label=current.label) := by
  have bareLookup : subtermAt (Lambda.contract body.erase argument.erase) relative=some current.erase := by
    rw [←LTerm.erase_contract,←LTerm.erase_subterm,lookup]; rfl
  rcases subtermAt_contract_origins bareLookup with ⟨oldBare,atOld,nonvar,_⟩ |
      ⟨k,j,atOld,other,_,_⟩ | ⟨site,suffix,split,occurs,_⟩
  · rw [←LTerm.erase_subterm] at atOld
    obtain ⟨old,oldLookup,erased⟩ := Option.map_eq_some_iff.mp atOld
    have retained : ∀ stamp,old≠.var stamp (binderDepth relative) := by
      intro stamp equal
      exact nonvar _ (erased.symm.trans (congrArg LTerm.erase equal))
    exact Or.inl ⟨old,oldLookup,(contract_retained_node_label oldLookup retained lookup nonroot).symm⟩
  · rw [←LTerm.erase_subterm] at atOld
    obtain ⟨old,oldLookup,erased⟩ := Option.map_eq_some_iff.mp atOld
    have retained : ∀ stamp,old≠.var stamp (binderDepth relative) := by
      intro stamp equal
      exact other (Term.var.inj (erased.symm.trans (congrArg LTerm.erase equal)))
    exact Or.inl ⟨old,oldLookup,(contract_retained_node_label oldLookup retained lookup nonroot).symm⟩
  · have strict : suffix≠[] := by
      intro empty
      apply notCopy
      have equal : relative=site := by simpa only [empty,List.append_nil] using split
      rw [equal]; exact occurs
    rw [split,LTerm.subterm_append] at lookup
    cases atCopy : (LTerm.contract beta alpha body argument).subterm site with
    | none => simp only [atCopy,Option.bind_none] at lookup; cases lookup
    | some copy =>
      rw [atCopy,Option.bind_some] at lookup
      obtain ⟨old,oldLookup,labels⟩ :=
        (LTerm.contract_argument_copy_interior occurs atCopy).nonroot_node lookup strict
      exact Or.inr ⟨site,suffix,old,occurs,split,strict,oldLookup,labels⟩

private theorem supported_all (t : LTerm) : t.Supported (fun _=>True) := by
  rw [LTerm.supported_iff]
  intro label _
  exact (Label.supported_iff_within _ _).mpr (by intro edge _; trivial)

private theorem StepAt.universal_cut (step : StepAt site source target) :
    RegionCut (fun _=>True) site source target := by
  induction step with
  | root => exact .here (supported_all _)
  | fn _ ih => exact .fn ih
  | arg _ ih => exact .arg ih
  | body _ ih => exact .body ih

/-- Every actual incoming edge not created by THIS beta has an actual old
occurrence with exactly its label. Different new occurrences may share that
old occurrence; the theorem does not assert injectivity or chain transport. -/
theorem StepAt.uncreated_label_origin
    {source target body argument current : LTerm} {site edge : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (lookup : target.subterm edge=some current)
    (notCreated : ¬BetaCreatedIncoming body site edge) :
    ∃ oldEdge old,source.subterm oldEdge=some old ∧old.label=current.label := by
  classical
  by_cases inside : ∃ relative,edge=site++relative
  · obtain ⟨relative,equal⟩ := inside
    have localLookup : (LTerm.contract beta alpha body argument).subterm relative=some current := by
      rw [equal,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    have nonroot : relative≠[] := by
      intro empty
      exact notCreated (Or.inl (by simpa only [empty,List.append_nil] using equal))
    have notCopy : ¬ArgumentOccurrence body.erase relative := by
      intro occurs
      exact notCreated (betaCreatedIncoming_iff.mpr (Or.inr ⟨relative,occurs,equal⟩))
    rcases LTerm.contract_uncreated_label_origin localLookup nonroot notCopy with
      ⟨old,oldLookup,labels⟩ | ⟨copySite,suffix,old,_,_,_,oldLookup,labels⟩
    · refine ⟨(site++[.fn,.body])++relative,old,?_,labels⟩
      simp only [LTerm.subterm_append,redex,Option.bind_some,LTerm.subterm,oldLookup]
    · refine ⟨(site++[.arg])++suffix,old,?_,labels⟩
      simp only [LTerm.subterm_append,redex,Option.bind_some,LTerm.subterm,oldLookup]
  · have labels := step.universal_cut.outside_labels inside
    change (target.subterm edge).map LTerm.label=(source.subterm edge).map LTerm.label at labels
    rw [lookup,Option.map_some] at labels
    obtain ⟨old,oldLookup,same⟩ := Option.map_eq_some_iff.mp labels.symm
    exact ⟨edge,old,oldLookup,same⟩

/-- The uncreated case cannot invent a label absent from the old term. -/
theorem StepAt.uncreated_label_mem
    {source target body argument current : LTerm} {site edge : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (lookup : target.subterm edge=some current)
    (notCreated : ¬BetaCreatedIncoming body site edge) : current.label∈source.labels := by
  obtain ⟨_,old,atOld,labels⟩ := step.uncreated_label_origin redex lookup notCreated
  rw [←labels]
  exact LTerm.label_mem_of_subterm atOld

/-- Label novelty implies an actual created incoming occurrence. The
converse requires freshness of the fired marker and is not assumed here. -/
theorem StepAt.created_of_fresh_label
    {source target body argument current : LTerm} {site edge : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (lookup : target.subterm edge=some current)
    (fresh : current.label∉source.labels) : BetaCreatedIncoming body site edge := by
  classical
  by_cases created : BetaCreatedIncoming body site edge
  · exact created
  · exact False.elim (fresh (step.uncreated_label_mem redex lookup created))

end Lamping.Lambda.Labelled

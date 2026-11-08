import Lamping.Lambda.LabelExpandedCodeAlignment
namespace Lamping.Lambda.Labelled

/-- The current head contractum really uses only the original head region.
The enclosing environment and all global positions are preserved. -/
theorem StepAt.inside_head_label_support {body argument : LTerm} (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (lookup : u.subterm p=some node) (inside : ∃ relative,p=head++relative) :
    node.label.Supported (SourceRegion (.app beta (.lam alpha body) argument)) := by
  obtain ⟨relative,paths⟩ := inside
  have current := step.contract_lookup source
  have localAt : (LTerm.contract beta alpha body argument).subterm relative=some node := by
    rw [paths,LTerm.subterm_append,current] at lookup
    exact lookup
  have localSource := (initial.subterm source).supported
  have localTarget := (StepAt.root beta alpha body argument).supported localSource
  exact (LTerm.supported_iff _ _).mp localTarget _ (LTerm.label_mem_of_subterm localAt)

/-- Contextual single-beta label collisions outside pure old argument
interiors are impossible. Outside the head, real old occurrences are recovered. -/
theorem StepAt.outside_argument_label_injective {body argument : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (left : u.subterm p=some node) (right : u.subterm q=some other)
    (same : node.label=other.label) (outside : ¬node.label.Supported (SourceRegion argument)) : p=q := by
  classical
  by_cases inside : ∃ relative,p=head++relative
  · have support := step.inside_head_label_support initial source left inside
    have otherSupport : other.label.Supported (SourceRegion (.app beta (.lam alpha body) argument)) := same ▸ support
    obtain ⟨rightRelative,rightPath⟩ := step.supported_head_node_internal initial source
      (regionSite := []) (regionTerm := .app beta (.lam alpha body) argument) (by simp [LTerm.subterm]) right otherSupport
    obtain ⟨leftRelative,leftPath⟩ := inside
    have current := step.contract_lookup source
    have leftAt : (LTerm.contract beta alpha body argument).subterm leftRelative=some node := by
      rw [leftPath,LTerm.subterm_append,current] at left
      exact left
    have rightAt : (LTerm.contract beta alpha body argument).subterm rightRelative=some other := by
      rw [rightPath,LTerm.subterm_append,current] at right
      exact right
    have relatives := LTerm.contract_outside_label_injective (initial.subterm source) leftAt rightAt same outside
    exact leftPath.trans ((congrArg (head++·) relatives).trans rightPath.symm)
  · have otherOutside : ¬∃ relative,q=head++relative := by
      intro otherInside
      have support := step.inside_head_label_support initial source right otherInside
      have nodeSupport : node.label.Supported (SourceRegion (.app beta (.lam alpha body) argument)) := same.symm ▸ support
      exact inside (step.supported_head_node_internal initial source (regionSite := [])
        (regionTerm := .app beta (.lam alpha body) argument) (by simp [LTerm.subterm]) left nodeSupport)
    have cut := step.region_cut initial source
    have oldLeft : (t.subterm p).map LTerm.label=some node.label := by
      change t.labelAt p=some node.label
      rw [←show u.labelAt p=t.labelAt p from cut.outside_labels inside]
      simp [LTerm.labelAt,left]
    have oldRight : (t.subterm q).map LTerm.label=some other.label := by
      change t.labelAt q=some other.label
      rw [←show u.labelAt q=t.labelAt q from cut.outside_labels otherOutside]
      simp [LTerm.labelAt,right]
    obtain ⟨old,leftOld,leftLabel⟩ := Option.map_eq_some_iff.mp oldLeft
    obtain ⟨oldOther,rightOld,rightLabel⟩ := Option.map_eq_some_iff.mp oldRight
    exact LTerm.subterm_label_injective t initial.2 leftOld rightOld (leftLabel.trans (same.trans rightLabel.symm))

/-- Different global target nodes with a common image are actual strict
argument-copy interiors, even when beta is under an outer binder. -/
theorem StepAt.label_collision_distinct_copies {body argument : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (left : u.subterm p=some node) (right : u.subterm q=some other)
    (same : node.label=other.label) (different : p≠q) :
    node.label.Supported (SourceRegion argument) ∧
    ∃ leftSite rightSite leftCopy rightCopy leftRelative rightRelative,
      ArgumentOccurrence body.erase leftSite ∧ ArgumentOccurrence body.erase rightSite ∧ leftSite≠rightSite ∧
      u.subterm (head++leftSite)=some leftCopy ∧ u.subterm (head++rightSite)=some rightCopy ∧
      p=(head++leftSite)++leftRelative ∧ q=(head++rightSite)++rightRelative ∧ leftRelative≠[] ∧ rightRelative≠[] := by
  classical
  have support : node.label.Supported (SourceRegion argument) := by
    by_cases supported : node.label.Supported (SourceRegion argument)
    · exact supported
    · exact False.elim (different (step.outside_argument_label_injective initial source left right same supported))
  have otherSupport : other.label.Supported (SourceRegion argument) := same ▸ support
  obtain ⟨leftRelative,leftPath⟩ := step.supported_head_node_internal initial source
    (regionSite := [.arg]) (regionTerm := argument) (by simp [LTerm.subterm]) left support
  obtain ⟨rightRelative,rightPath⟩ := step.supported_head_node_internal initial source
    (regionSite := [.arg]) (regionTerm := argument) (by simp [LTerm.subterm]) right otherSupport
  have current := step.contract_lookup source
  have leftAt : (LTerm.contract beta alpha body argument).subterm leftRelative=some node := by
    rw [leftPath,LTerm.subterm_append,current] at left
    exact left
  have rightAt : (LTerm.contract beta alpha body argument).subterm rightRelative=some other := by
    rw [rightPath,LTerm.subterm_append,current] at right
    exact right
  have relativeDifferent : leftRelative≠rightRelative := by
    intro equal
    exact different (leftPath.trans ((congrArg (head++·) equal).trans rightPath.symm))
  obtain ⟨a,b,c,d,r,s,ha,hb,apart,atA,atB,pa,pb,ra,rb⟩ :=
    LTerm.contract_collision_distinct_copies (initial.subterm source) leftAt rightAt same relativeDifferent
  refine ⟨support,a,b,c,d,r,s,ha,hb,apart,?_,?_,?_,?_,ra,rb⟩
  · rw [LTerm.subterm_append,current]; exact atA
  · rw [LTerm.subterm_append,current]; exact atB
  · simpa only [List.append_assoc] using leftPath.trans (congrArg (head++·) pa)
  · simpa only [List.append_assoc] using rightPath.trans (congrArg (head++·) pb)
/-- Global local-INIT edge-image uniqueness outside pure old argument
interiors, for the actual beta at any syntax position. -/
theorem StepAt.outside_argument_edge_injective {body argument : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (left : e∈sourceEdges [] .external (initLabels u.erase))
    (right : f∈sourceEdges [] .external (initLabels u.erase))
    (same : e.atom.relabel (initialRelabelling u 0)=f.atom.relabel (initialRelabelling u 0))
    (outside : ¬(e.atom.relabel (initialRelabelling u 0)).Supported (SourceRegion argument)) : e=f := by
  let basis := initLabels u.erase
  have leftMember : e.atom∈basis.labels := by
    rw [←sourceEdges_atoms basis [] .external]
    exact List.mem_map.mpr ⟨e,left,rfl⟩
  have rightMember : f.atom∈basis.labels := by
    rw [←sourceEdges_atoms basis [] .external]
    exact List.mem_map.mpr ⟨f,right,rfl⟩
  obtain ⟨p,node,leftAt,leftLabel⟩ := LTerm.label_mem_located basis leftMember
  obtain ⟨q,other,rightAt,rightLabel⟩ := LTerm.label_mem_located basis rightMember
  have currentLeft := LTerm.basis_node_transport u leftAt
  have currentRight := LTerm.basis_node_transport u rightAt
  have labels : (node.relabel (initialRelabelling u 0)).label=(other.relabel (initialRelabelling u 0)).label := by
    simpa only [LTerm.label_relabel,leftLabel,rightLabel] using same
  have notArgument : ¬(node.relabel (initialRelabelling u 0)).label.Supported (SourceRegion argument) := by
    simpa only [LTerm.label_relabel,leftLabel] using outside
  have samePath := step.outside_argument_label_injective initial source currentLeft currentRight labels notArgument
  cases samePath
  have nodes : node=other := Option.some.inj (leftAt.symm.trans rightAt)
  have atoms : e.atom=f.atom := leftLabel.symm.trans ((congrArg LTerm.label nodes).trans rightLabel)
  exact sourceEdges_unique (init_is_INIT u.erase) left right atoms
end Lamping.Lambda.Labelled



import Lamping.Lamping.CompletedLocalAtomRoles
import Lamping.Lamping.BetaEvaluatedChildResiduals
import Lamping.Checks.MarkedAuxiliaryPhysicalFixture

namespace Lamping.Checks.CompletedLocalAtomRolesChecks
open Graph Lambda Lambda.Labelled AG
open MarkedAuxiliaryPhysicalFixture

private theorem at_nonroot
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {target localTarget : LTerm} {edge : BetaEdge site.net}
    {selection : SourceEdgeSelection original site.net root}
    (all : ∀ (p : Path) (step : Step) (parentTerm : LTerm),target.subterm p=some parentTerm →
      ∀ child : OccurrenceFragment target site.reduce root (p++[step]),
        SourceDeparture parentTerm step (sourceEdge child.environment child.context child.term).fromPort →
        ∃ node,localTarget.subterm (p++[step])=some node ∧
          node.erase=child.term.erase ∧selection.evalLabel edge node.label≠[] ∧
          BetaPathResidual site edge (child.fragment.segments.map (plugEnd _ _).invFun)
            (selection.evalLabel edge node.label))
    {p : Path} (child : OccurrenceFragment target site.reduce root p) (nonroot : p≠[]) :
    ∃ node,localTarget.subterm p=some node ∧selection.evalLabel edge node.label≠[] := by
  rcases child.occurrence.last_departure with ⟨empty,_⟩ |
    ⟨parent,step,parentTerm,split,lookup,role⟩
  · exact False.elim (nonroot empty)
  · change p=parent++[step] at split
    subst p
    have departure : SourceDeparture parentTerm step
        (sourceEdge child.environment child.context child.term).fromPort := by
      cases child.term <;> exact role
    obtain ⟨node,atNode,_erase,nonempty,_residual⟩ := all parent step parentTerm lookup child departure
    exact ⟨node,atNode,nonempty⟩

/-- Actual marked Aux APP from ONE physical child producer; its literal APP3
and VAR5 letters consume the new high with THAT edge and selector. -/
theorem actual_one_producer_outer_roles :
    ∃ localTarget, History [[.arg]] (initLabels original.erase) localTarget ∧
      ∃ edge : BetaEdge concrete.site.net,
      ∃ selection : SourceEdgeSelection (initLabels original.erase) concrete.site.net (.inl ()),
        SiteBetaGeometry concrete.site edge ∧
        localTarget.subterm [.arg]=some NodeLabelSuffixOriginsChecks.currentArgument ∧
        selection.evalLabel edge NodeLabelSuffixOriginsChecks.currentArgument.label≠[] ∧
        (selection.atomWord 3≠edge.principal ∧selection.atomWord 3≠edge.reverseRoute) ∧
        (selection.atomWord 5≠edge.principal ∧selection.atomWord 5≠edge.reverseRoute) ∧
        NodeLabelSuffixOriginsChecks.currentArgument.label.letters=
          [.atom 3,.over (.atom 4),.atom 5,.under (.atom 4),.atom 6] ∧
        Letter.atom 4∉NodeLabelSuffixOriginsChecks.currentArgument.label.letters ∧
        Letter.over (.atom 4)∈NodeLabelSuffixOriginsChecks.currentArgument.label.letters ∧
        Letter.under (.atom 4)∈NodeLabelSuffixOriginsChecks.currentArgument.label.letters := by
  obtain ⟨flow⟩ := source_flow
  obtain ⟨balance⟩ := source_indexed_balance
  obtain ⟨localTarget,localHistory,_erase,targetMatches,edge,selection,geometry,all⟩ :=
    concrete.site.beta_evaluated_child_residuals closed source_matching source_inputs
      flow source_positive balance source_root_depth source_transparency relative normal history
  have basis : initLabels original.erase=original := by
    change initLabels (initLabels NodeLabelSuffixOriginsChecks.bare).erase=
      initLabels NodeLabelSuffixOriginsChecks.bare
    rw [erase_initLabels]
  have canonicalHistory : History [[.arg]] (initLabels original.erase) current := by
    rw [basis];exact history
  have sameLocal : localTarget=current := localHistory.deterministic canonicalHistory
  have actualLookup : localTarget.subterm [.arg]=some NodeLabelSuffixOriginsChecks.currentArgument := by
    rw [sameLocal];exact NodeLabelSuffixOriginsChecks.actual_lookup
  obtain ⟨targetSelection⟩ := targetMatches.occurrence_fragment_selection currentClosed
  let position : Position current.erase := ⟨[.arg],by
    rw [←LTerm.erase_subterm,NodeLabelSuffixOriginsChecks.actual_lookup];rfl⟩
  obtain ⟨node,lookup,nonempty⟩ := at_nonroot concrete.site all
    (targetSelection position) (by intro impossible;cases impossible)
  have sameNode : node=NodeLabelSuffixOriginsChecks.currentArgument :=
    Option.some.inj (lookup.symm.trans actualLookup)
  subst node
  have roles := concrete.site.complete_local_outer_atoms_not_beta_routes
    (source:=original) geometry selection source_matching flow source_positive
    relative normal localHistory lookup
  refine ⟨localTarget,localHistory,edge,selection,geometry,lookup,nonempty,
    roles 3 (by decide),roles 5 (by decide),NodeLabelSuffixOriginsChecks.actual_overlap_word,?_,?_,?_⟩
  all_goals decide

#print axioms actual_one_producer_outer_roles
end Lamping.Checks.CompletedLocalAtomRolesChecks

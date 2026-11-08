import Lamping.Lamping.PhysicalAtomCellReflection
import Lamping.Lamping.MatchingSelectedPrincipalWord
import Lamping.Checks.MarkedAuxiliaryPhysicalFixture
namespace Lamping.Checks.PhysicalAtomCellReflectionChecks
open Graph Lambda Lambda.Labelled AG
namespace Fixture
open MarkedAuxiliaryPhysicalFixture
noncomputable def selection : SourceEdgeSelection original concrete.site.net (.inl ()) :=
  source_matching.source_edge_selection closed
private theorem geometry_of_pair (edge : BetaEdge concrete.site.net)
    (app : edge.app=.inr (.inl ())) (lam : edge.lam=.inr (.inr ())) :
    SiteBetaGeometry concrete.site edge where
  appCtx := congrArg Sum.inl (Sigma.ext app edge.appCtx_role)
  body := congrArg Sum.inl (Sigma.ext lam edge.lamBody_role)
  binding := congrArg Sum.inl (Sigma.ext lam edge.lamBind_role)
  argument := congrArg Sum.inl (Sigma.ext app edge.appArg_role)
/-- A real atom4 collision in the beta1 carrier, before any role reflection. -/
theorem atom_four_principal : ∃edge : BetaEdge concrete.site.net,
    SiteBetaGeometry concrete.site edge ∧selection.atomWord 4=edge.principal := by
  obtain ⟨edge,app,lam,all⟩ := concrete.site.selected_principal_word initial source_matching
  have selected : SelectedDegree original
      (concrete.site.betaSyntaxFiber (.inl ()) original.erase) (.atom 4) :=
    ⟨[.arg],physical_member,at_degree⟩
  exact ⟨edge,geometry_of_pair edge app lam,all selection (.atom 4) selected⟩
/-- Direct low application at the genuine collision, retaining literal arg. -/
theorem actual_arg_selected_function : ∃edge : BetaEdge concrete.site.net,
    SiteBetaGeometry concrete.site edge ∧selection.atomWord 4=edge.principal ∧
    ∃appStamp body argument,(initLabels original.erase).subterm [.arg]=
      some (.app appStamp (.lam (.atom 4) body) argument) := by
  obtain ⟨edge,geometry,collision⟩ := atom_four_principal
  obtain ⟨flow⟩ := source_flow
  obtain ⟨name,stamp,body,argument,member,lookup⟩ :=
    concrete.site.atom_word_principal_selected_function (source:=original) geometry selection source_matching flow source_positive collision
  have nameEq : name=[.arg] := by
    rw [exact_fiber,List.mem_singleton] at member
    exact member
  exact ⟨edge,geometry,collision,stamp,body,argument,nameEq ▸ lookup⟩
theorem beta_one_degree_four : (1 : Nat)≠4 ∧
    original.degreeAt [.arg]=some (.atom 4) ∧
    concrete.site.betaSyntaxFiber (.inl ()) original.erase=[[.arg]] :=
  ⟨by decide,at_degree,exact_fiber⟩
theorem atom_four_not_reverse (edge : BetaEdge concrete.site.net) :
    selection.atomWord 4≠edge.reverseRoute :=
  selection.atom_word_ne_reverse_principal edge 4
/-- The actual lambda-body variable cell is subject to the generic guard too. -/
theorem binder_cell_guard (edge : BetaEdge concrete.site.net) :
    (⟨Label.atom 5,.lamBody (.atom 4),.lamBind (.atom 4)⟩ : SourceEdge)∈
      sourceEdges [] .external original ∧selection.atomWord 5≠edge.reverseRoute :=
  ⟨by decide,selection.atom_word_ne_reverse_principal edge 5⟩
/-- A genuine off-domain atom remains the empty fallback; it is not a bar. -/
theorem offdomain_cell_guard (edge : BetaEdge concrete.site.net) :
    selection.atomWord 999=[] ∧selection.atomWord 999≠edge.reverseRoute := by
  classical
  have absent : ¬∃cell : {e : SourceEdge //e∈sourceEdges [] .external original},
      cell.val.atom=Label.atom 999 := by
    rintro ⟨cell,atomic⟩
    have member : Label.atom 999∈original.labels := by
      rw [←sourceEdges_atoms original [] .external]
      exact List.mem_map.mpr ⟨cell.val,cell.property,atomic⟩
    have no : Label.atom 999∉original.labels := by decide
    exact no member
  exact ⟨by unfold SourceEdgeSelection.atomWord;rw [dif_neg absent],
    selection.atom_word_ne_reverse_principal edge 999⟩
end Fixture
#print axioms PathSite.atom_word_principal_selected_function
#print axioms SourceEdgeSelection.atom_word_ne_reverse_principal
#print axioms Fixture.atom_four_principal
#print axioms Fixture.actual_arg_selected_function
#print axioms Fixture.beta_one_degree_four
#print axioms Fixture.atom_four_not_reverse
#print axioms Fixture.binder_cell_guard
#print axioms Fixture.offdomain_cell_guard
end Lamping.Checks.PhysicalAtomCellReflectionChecks

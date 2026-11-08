import Lamping.Lamping.PhysicalAtomCellReflection
import Lamping.Lambda.SelectedFunctionOuterExclusion

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

theorem PathSite.complete_local_outer_atoms_not_beta_routes
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {source localTarget node : LTerm} {ps : List Path}
    {marked : Marked} {position : Path} {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge)
    (selection : SourceEdgeSelection (initLabels source.erase) site.net root)
    (matching : Matches site.net root source.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (lookup : localTarget.subterm position=some node) :
    ∀ n,Letter.atom n∈node.label.letters →
      selection.atomWord n≠edge.principal ∧selection.atomWord n≠edge.reverseRoute := by
  have old : Marked.RelativeOldHistory (site.betaSyntaxFiber root source.erase) ps
      (Marked.mark (site.betaSyntaxFiber root source.erase)
        (initLabels source.erase).erase) marked := by
    simpa only [erase_initLabels] using
      ((Marked.relativeOld_iff_relative
        (Marked.selected_mark (site.betaSyntaxFiber root source.erase) source.erase)).mpr relative)
  intro n outer
  refine ⟨?_,selection.atom_word_ne_reverse_principal edge n⟩
  intro collision
  obtain ⟨name,stamp,body,argument,selected,atRedex⟩ :=
    site.atom_word_principal_selected_function (source:=source)
      geometry selection matching flow positive collision
  exact (old.normal_no_selected_function_outer_atom localHistory
    (init_is_INIT source.erase) normal selected atRedex lookup) outer

#print axioms PathSite.complete_local_outer_atoms_not_beta_routes
end Lamping.AG

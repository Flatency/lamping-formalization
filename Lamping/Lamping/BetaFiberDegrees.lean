import Lamping.Lamping.RedexOccurrenceFragments
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem actual_redex_lookup (current : LTerm) (redex : RedexOcc current.erase) :
    ∃ appStamp lamStamp body arg,
      current.subterm redex.val=some (.app appStamp (.lam lamStamp body) arg) := by
  obtain ⟨stamp,degree⟩ := degreeAt_exists current redex
  simp only [LTerm.degreeAt,Option.bind_eq_some_iff] at degree
  obtain ⟨sub,lookup,degree⟩ := degree
  cases sub with
  | var label index => cases degree
  | lam label body => cases degree
  | app label fn arg =>
    cases fn with
    | var fnLabel index => cases degree
    | app fnLabel left right => cases degree
    | lam fnLabel body => exact ⟨label,fnLabel,body,arg,lookup⟩

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Conditional REP consequence for the SAME actual physical beta fiber.
A real member is required: empty physical fibers acquire no representative.
Neither current INIT nor a family-completeness certificate is assumed. -/
theorem PathSite.beta_fiber_iff_degree {root : B} {current : LTerm}
    (closed : Closed current.erase) (matching : Matches site.net root current.erase)
    (selection : OccurrenceFragmentSelection current site.net root)
    (representation : ChainRepresentationInvariant closed selection)
    (representative : RedexOcc current.erase)
    (member : representative.val∈site.betaSyntaxFiber root current.erase)
    (candidate : RedexOcc current.erase) :
    candidate.val∈site.betaSyntaxFiber root current.erase ↔
      current.degreeAt candidate.val=current.degreeAt representative.val := by
  obtain ⟨beta,app,lam,principal⟩ := site.beta_fiber_principal matching
  obtain ⟨source⟩ := matching.actual_redex_access representative
  obtain ⟨other⟩ := matching.actual_redex_access candidate
  obtain ⟨appStamp,lamStamp,body,arg,lookup⟩ := actual_redex_lookup current representative
  obtain ⟨otherApp,otherLam,otherBody,otherArg,otherLookup⟩ := actual_redex_lookup current candidate
  have sourcePrincipal := principal representative source member
  have compared := redex_chain_representation_iff_degree closed selection representation otherLookup lookup
  have fragments : SameChainRepresentation selection (PrerequisiteChain.redex_app otherLookup)
      (PrerequisiteChain.redex_app lookup) ↔other.connection.edges=source.connection.edges := by
    unfold SameChainRepresentation
    rw [canonical_redex_chain_actual matching selection other otherLookup,
      canonical_redex_chain_actual matching selection source lookup]
    exact ⟨fun same=>(List.cons.inj same).1,fun same=>congrArg (fun xs=>[xs]) same⟩
  constructor
  · intro selected
    have same := (principal candidate other selected).trans sourcePrincipal.symm
    exact compared.mp (fragments.mpr same)
  · intro degrees
    have same := (fragments.mp (compared.mpr degrees)).trans sourcePrincipal
    have pair := other.connection.beta_pair_of_principal beta same
    exact (other.physical_selection_iff site.net root current.erase (.inr (.inl ()))
      (.inr (.inr ())) matching).mpr ⟨pair.1.trans app,pair.2.trans lam⟩
end
end Lamping.AG

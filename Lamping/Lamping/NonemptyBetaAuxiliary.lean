import Lamping.Lamping.SafeBetaAuxiliaryTransport
import Lamping.Lamping.MarkedBetaAuxiliaryTransport

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

theorem PathSite.beta_nonempty_auxiliary_preserve
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original source target : LTerm} {ps : List Path} {marked : Marked}
    (initial : INIT original)
    (prior : ParallelHistory original.erase source.erase)
    (completePrior : CompleteDerivation prior)
    (prefixHistory : History prior.derivation.paths original source)
    (closed : Closed source.erase)
    (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights)
    (rootDepth : heights root=0)
    (oldT : Transparency site.net root)
    (relative : Marked.RelativeHistory ps
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked)
    (labels : History ps source target)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (nonempty : site.betaSyntaxFiber root source.erase≠[]) :
    AuxiliarySeparation (labels.closed closed) targetSelection := by
  classical
  obtain ⟨path,inside⟩:=List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨representative,_access,samePath,_app,_lam⟩:=
    (mem_physicalBetaFiberPaths site.net root source.erase (.inr (.inl ())) (.inr (.inr ())) path).mp inside
  have member : representative.val∈site.betaSyntaxFiber root source.erase:=samePath.symm ▸ inside
  obtain ⟨degree,atDegree⟩:=degreeAt_exists source representative
  intro left right leftAux rightAux sameLabel different endpoints
  obtain ⟨sourceIso,targetIso⟩:=endpoints
  by_cases safe : (SyntaxIncidence.label target left).OuterBarsSafe (fun x=>x≠degree)
  · exact different (site.beta_incoming_safe_auxiliary_pair initial prior completePrior prefixHistory closed
      matching inputs flow positive balance rootDepth oldT relative normal labels sourceSelection targetSelection
      sourceJoint representative member atDegree left right leftAux rightAux sameLabel safe sourceIso targetIso)
  · exact different (site.beta_marked_auxiliary_pair initial prior completePrior prefixHistory closed
      matching inputs flow positive balance rootDepth oldT relative normal labels sourceSelection targetSelection
      sourceJoint representative member atDegree left right leftAux rightAux sameLabel safe sourceIso targetIso)

end Lamping.AG
#print axioms Lamping.AG.PathSite.beta_nonempty_auxiliary_preserve

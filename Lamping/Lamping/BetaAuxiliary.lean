import Lamping.Lamping.NonemptyBetaAuxiliary
import Lamping.Lamping.EmptyBetaAuxiliary

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

theorem PathSite.beta_auxiliary_preserve
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
    (sourceJoint : JointRepresentation closed sourceSelection) :
    AuxiliarySeparation (labels.closed closed) targetSelection := by
  classical
  by_cases empty : site.betaSyntaxFiber root source.erase=[]
  · exact site.beta_empty_auxiliary_preserve closed matching inputs flow positive balance rootDepth
      oldT relative normal labels sourceSelection targetSelection sourceJoint empty
  · exact site.beta_nonempty_auxiliary_preserve initial prior completePrior prefixHistory closed
      matching inputs flow positive balance rootDepth oldT relative normal labels
      sourceSelection targetSelection sourceJoint empty

end Lamping.AG
#print axioms Lamping.AG.PathSite.beta_auxiliary_preserve

import Lamping.Lamping.AuxiliaryEndpointReflection
import Lamping.Lamping.BetaOldOccurrenceImages
import Lamping.Lamping.BetaFiberDegrees
import Lamping.Lambda.LabelFamilyMarkerFreshness

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

theorem PathSite.beta_incoming_safe_auxiliary_pair
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original source target : LTerm} {ps : List Path} {marked : Marked}
    {degree : Lambda.Labelled.Label}
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
    (representative : RedexOcc source.erase)
    (member : representative.val ∈ site.betaSyntaxFiber root source.erase)
    (atDegree : source.degreeAt representative.val=some degree)
    (left right : SyntaxIncidence.Edge target)
    (leftAux : AuxiliaryAt target left.val)
    (rightAux : AuxiliaryAt target right.val)
    (sameLabel : SyntaxIncidence.label target left=SyntaxIncidence.label target right)
    (leftSafe : (SyntaxIncidence.label target left).OuterBarsSafe (fun x=>x≠degree))
    (sourceIso : SuccessfulEndpointIso target (labels.closed closed)
      (SyntaxIncidence.source target left) (SyntaxIncidence.source target right))
    (targetIso : SuccessfulEndpointIso target (labels.closed closed)
      (SyntaxIncidence.target target (labels.closed closed) left)
      (SyntaxIncidence.target target (labels.closed closed) right)) :
    (targetSelection left).fragment.segments=(targetSelection right).fragment.segments := by
  have sourceSafe := complete_prefix_outer_bars_fresh initial prior completePrior prefixHistory representative atDegree
  have selected (path : Path) (inside : path∈site.betaSyntaxFiber root source.erase) :
      source.degreeAt path=some degree := by
    obtain ⟨candidate,_access,same,_app,_lam⟩ :=
      (mem_physicalBetaFiberPaths site.net root source.erase (.inr (.inl ())) (.inr (.inr ())) path).mp inside
    have chosen : candidate.val∈site.betaSyntaxFiber root source.erase := same.symm ▸ inside
    have equal := (site.beta_fiber_iff_degree closed matching sourceSelection sourceJoint.1
      representative member candidate).mp chosen
    rw [same] at equal
    exact equal.trans atDegree
  have old := (Marked.relativeOld_iff_relative
    (Marked.selected_mark (site.betaSyntaxFiber root source.erase) source.erase)).mpr relative
  obtain ⟨le,re,_ln,_rn,_ll,_rl,lt,rt,_la,_ra,_nl,_labels,_si,_ti,oldEq⟩ :=
    uniform_old_equal_auxiliary_source_pieces initial prefixHistory old labels selected sourceSafe
      closed sourceSelection sourceJoint left right leftAux rightAux sameLabel sourceIso targetIso
  let lf := targetSelection left
  let rf := targetSelection right
  have leftStamp : SyntaxIncidence.label target left=lf.term.label :=
    SyntaxIncidence.label_of_lookup target left lf.occurrence.lookup
  have rightStamp : SyntaxIncidence.label target right=rf.term.label :=
    SyntaxIncidence.label_of_lookup target right rf.occurrence.lookup
  have ls : lf.term.label.OuterBarsSafe (fun x=>x≠degree) := leftStamp ▸ leftSafe
  have rs : rf.term.label.OuterBarsSafe (fun x=>x≠degree) := by
    rw [←rightStamp,←sameLabel]
    exact leftSafe
  obtain ⟨lp,rp,ln,rn,ll,rl,ltrace,rtrace,pair⟩ :=
    site.beta_marker_free_occurrence_pair closed matching inputs flow positive balance rootDepth oldT
      relative normal labels old (DegreeAligned.initial source _) selected sourceSelection lf rf ls rs
  let ple : SyntaxIncidence.Edge source := ⟨lp,by rw [←LTerm.erase_subterm,ll];rfl⟩
  let pre : SyntaxIncidence.Edge source := ⟨rp,by rw [←LTerm.erase_subterm,rl];rfl⟩
  have lEq : ple=le := Subtype.ext (ltrace.unique lt)
  have rEq : pre=re := Subtype.ext (rtrace.unique rt)
  change lf.fragment.segments=rf.fragment.segments ↔
    (sourceSelection ple).fragment.segments=(sourceSelection pre).fragment.segments at pair
  rw [lEq,rEq] at pair
  exact pair.mpr oldEq

end Lamping.AG
#print axioms Lamping.AG.PathSite.beta_incoming_safe_auxiliary_pair

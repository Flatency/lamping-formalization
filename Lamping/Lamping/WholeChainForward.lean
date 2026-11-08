import Lamping.Lamping.MultiedgeParentComparison
import Lamping.Lamping.TerminalMarkedLambdaEvaluations
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem singleton_of_nonempty {A : Type} {xs : List A}
    (nonempty : xs≠[]) (bound : xs.length≤1) : ∃a,xs=[a] := by
  cases xs with
  | nil => exact False.elim (nonempty rfl)
  | cons a rest =>
    have empty : rest=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at bound;omega)
    exact ⟨a,by rw [empty]⟩

private theorem local_lambda_shape {localTarget target node : LTerm} {edge : Path} {stamp : Label} {body : LTerm}
    (same : localTarget.erase=target.erase)
    (lookup : localTarget.subterm edge=some node)
    (globalLookup : target.subterm edge=some (.lam stamp body)) :
    ∃localStamp localBody,node=.lam localStamp localBody := by
  have bare : some node.erase=some (Term.lam body.erase) := by
    calc
      some node.erase = (localTarget.subterm edge).map LTerm.erase := by rw [lookup];rfl
      _ = (target.subterm edge).map LTerm.erase := by rw [LTerm.erase_subterm,LTerm.erase_subterm,same]
      _ = some (Term.lam body.erase) := by rw [globalLookup];rfl
  have shape:=Option.some.inj bare
  cases node with
  | var a n => cases shape
  | app a f x => cases shape
  | lam a b => exact ⟨a,b,rfl⟩

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

theorem PathSite.beta_singleton_chain_forward
    {root : B} {source target original : LTerm} {ps F prior : List Path} {marked oldMarked : Marked}
    {ls rs : Path} {les res : List Path} {degree : Labelled.Label}
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (initial : INIT original) (prefixHistory : History prior original source)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) oldMarked)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (first : PrerequisiteChain target ls les) (second : PrerequisiteChain target rs res)
    (iso : ChainIncidenceIso (chainSyntaxIncidence target (history.closed closed) les)
      (chainSyntaxIncidence target (history.closed closed) res))
    (singleton : max les.length res.length=1) :
    SameChainRepresentation targetSelection first second := by
  obtain ⟨le,rfl⟩:=singleton_of_nonempty first.nonempty (by omega)
  obtain ⟨re,rfl⟩:=singleton_of_nonempty second.nonempty (by omega)
  obtain ⟨lastLeft,lastL,lp,la,ll,lb,larg,edgeL,leftRedex⟩:=first.last_redex
  obtain ⟨lastRight,lastR,rp,ra,rl,rb,rarg,edgeR,rightRedex⟩:=second.last_redex
  have el : le=lastLeft := by simpa using lastL
  have er : re=lastRight := by simpa using lastR
  have leq : le=lp++[.fn] := el.trans edgeL
  have req : re=rp++[.fn] := er.trans edgeR
  have leftLookup : target.subterm le=some (.lam ll lb) := by rw [leq,LTerm.subterm_append,leftRedex];rfl
  have rightLookup : target.subterm re=some (.lam rl rb) := by rw [req,LTerm.subterm_append,rightRedex];rfl
  have sameLabels:=actual_chain_labels_forward (prefixHistory.append history) initial (history.closed closed) first second iso
  have sameCurrent : ll=rl := by simpa [LTerm.labelAt,leftLookup,rightLookup,LTerm.label] using sameLabels
  by_cases safe : ll.OuterBarsSafe (fun x=>x≠degree)
  · apply (site.beta_marker_free_rep closed matching inputs flow positive balance rootDepth transparency
      relative normal history old (DegreeAligned.initial source F) selected sourceSelection targetSelection
      sourceJoint.1 first second ?_ ?_).mpr ⟨iso⟩
    · intro e inside node lookup
      have ee : e=le := by simpa using inside
      subst e
      have sameNode:=Option.some.inj (lookup.symm.trans leftLookup)
      simpa only [sameNode,LTerm.label] using safe
    · intro e inside node lookup
      have ee : e=re := by simpa using inside
      subst e
      have sameNode:=Option.some.inj (lookup.symm.trans rightLookup)
      simpa only [sameNode,LTerm.label,←sameCurrent] using safe
  · obtain ⟨localTarget,localHistory,erase,_matches,edge,selection,geometry,allChains⟩:=
      site.beta_evaluated_chain_residuals closed matching inputs flow positive balance rootDepth
        transparency relative normal history targetSelection
    obtain ⟨left⟩:=allChains first
    obtain ⟨right⟩:=allChains second
    let lm : {p : Path // p∈[le]}:=⟨le,by simp⟩
    let rm : {p : Path // p∈[re]}:=⟨re,by simp⟩
    obtain ⟨localLeft,leftBody,leftNode⟩:=local_lambda_shape erase (left.lookup lm) leftLookup
    obtain ⟨localRight,rightBody,rightNode⟩:=local_lambda_shape erase (right.lookup rm) rightLookup
    have leftLocal : localTarget.subterm (lp++[.fn])=some (.lam localLeft leftBody) := by
      rw [←leq];exact (left.lookup lm).trans (congrArg some leftNode)
    have rightLocal : localTarget.subterm (rp++[.fn])=some (.lam localRight rightBody) := by
      rw [←req];exact (right.lookup rm).trans (congrArg some rightNode)
    have evaluation:=terminal_marked_lambda_evaluations initial prefixHistory closed old history selected sourceSafe
      localHistory leftRedex rightRedex sameCurrent safe leftLocal rightLocal matching sourceSelection sourceJoint selection edge
    have pieces:=EvaluatedChainResiduals.given_member_pieces_of_evaluations site geometry left right lm rm
      (by simpa only [leftNode,rightNode,LTerm.label] using evaluation)
    change canonicalChainImage targetSelection first=canonicalChainImage targetSelection second
    change [(targetSelection (actualChainPosition first lm)).fragment.segments]=
      [(targetSelection (actualChainPosition second rm)).fragment.segments]
    exact congrArg (fun p=>[p]) pieces

theorem PathSite.beta_chain_forward
    {root : B} {source target original : LTerm} {ps F prior : List Path} {marked oldMarked : Marked}
    {ls rs : Path} {les res : List Path} {degree : Labelled.Label}
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (initial : INIT original) (prefixHistory : History prior original source)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) oldMarked)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (first : PrerequisiteChain target ls les) (second : PrerequisiteChain target rs res)
    (iso : ChainIncidenceIso (chainSyntaxIncidence target (history.closed closed) les)
      (chainSyntaxIncidence target (history.closed closed) res))
    : SameChainRepresentation targetSelection first second := by
  have all (bound : Nat) : ChainForwardBelow (history.closed closed) targetSelection bound := by
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
      intro p q es fs left right shorter isomorphic
      obtain ⟨concreteIso⟩:=isomorphic
      by_cases one : max es.length fs.length=1
      · exact site.beta_singleton_chain_forward closed matching inputs flow positive balance rootDepth transparency
          relative normal history initial prefixHistory old selected sourceSafe sourceSelection sourceJoint
          targetSelection left right concreteIso one
      · have positiveLength : 0<es.length := List.length_pos_iff.mpr left.nonempty
        have multi : 1<max es.length fs.length := by omega
        exact site.beta_multiedge_chain_forward closed matching inputs flow positive balance rootDepth transparency
          relative normal history initial prefixHistory old selected sourceSafe sourceSelection sourceJoint
          targetSelection left right concreteIso multi (ih _ shorter)
  exact all (max les.length res.length+1) first second (by omega) ⟨iso⟩
end
#print axioms PathSite.beta_singleton_chain_forward
#print axioms PathSite.beta_chain_forward
end Lamping.AG

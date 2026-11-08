import Lamping.Lamping.BetaEvaluatedChildResiduals
import Lamping.Lamping.FanLambdaSlotSynchronization
import Lamping.Lamping.BetaOldChainImages

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {target : LTerm}

/-- Literal valid positions of actual ordered chain members. -/
def actualChainPosition (chain : PrerequisiteChain target start es)
    (member : {p : Path // p∈es}) : Position target.erase :=
  ⟨member.val,by
    rcases chain.eligible member.property with ⟨parent,a,fn,arg,eq,lookup⟩ | ⟨a,body,lookup⟩
    · have child : target.subterm member.val=some fn := by
        rw [eq,LTerm.subterm_append,lookup]
        cases fn <;> rfl
      rw [←LTerm.erase_subterm,child]
      rfl
    · rw [←LTerm.erase_subterm,lookup]
      rfl⟩
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Actual evaluated blocks on ONE supplied successful chain, an output of
the real development producer. No equality/REP is a field. -/
structure EvaluatedChainResiduals {root : B} {original target localTarget : LTerm}
    (edge : BetaEdge site.net) (selection : SourceEdgeSelection original site.net root)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (chain : PrerequisiteChain target start es) where
  node : {p : Path // p∈es} → LTerm
  lookup : ∀member,localTarget.subterm member.val=some (node member)
  nonempty : ∀member,selection.evalLabel edge (node member).label≠[]
  residual : ∀member,BetaPathResidual site edge
    ((targetSelection (actualChainPosition chain member)).fragment.segments.map (plugEnd _ _).invFun)
    (selection.evalLabel edge (node member).label)

noncomputable def EvaluatedChainResiduals.blocks
    {root : B} {original target localTarget : LTerm}
    {edge : BetaEdge site.net} {selection : SourceEdgeSelection original site.net root}
    {targetSelection : OccurrenceFragmentSelection target site.reduce root}
    {chain : PrerequisiteChain target start es}
    (output : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain) :
    List (List (Endpoint site.net)) :=
  es.attach.map (fun member=>selection.evalLabel edge (output.node member).label)

private theorem evaluated_at_nonroot
    {root : B} {original target localTarget : LTerm}
    {edge : BetaEdge site.net} {selection : SourceEdgeSelection original site.net root}
    (all : ∀ (p : Path) (step : Step) (parentTerm : LTerm),target.subterm p=some parentTerm →
      ∀child : OccurrenceFragment target site.reduce root (p++[step]),
        SourceDeparture parentTerm step (sourceEdge child.environment child.context child.term).fromPort →
        ∃node,localTarget.subterm (p++[step])=some node ∧node.erase=child.term.erase ∧
          selection.evalLabel edge node.label≠[] ∧BetaPathResidual site edge
            (child.fragment.segments.map (plugEnd _ _).invFun) (selection.evalLabel edge node.label))
    {p : Path} (child : OccurrenceFragment target site.reduce root p) (nonroot : p≠[]) :
    ∃node,localTarget.subterm p=some node ∧selection.evalLabel edge node.label≠[] ∧
      BetaPathResidual site edge (child.fragment.segments.map (plugEnd _ _).invFun)
        (selection.evalLabel edge node.label) := by
  rcases child.occurrence.last_departure with ⟨empty,_⟩ |
    ⟨parent,step,parentTerm,split,lookup,role⟩
  · exact False.elim (nonroot empty)
  · change p=parent++[step] at split
    subst p
    have departure : SourceDeparture parentTerm step
        (sourceEdge child.environment child.context child.term).fromPort := by
      cases child.term <;> exact role
    obtain ⟨node,atNode,_erase,nonempty,residual⟩ := all parent step parentTerm lookup child departure
    exact ⟨node,atNode,nonempty,residual⟩

/-- Package the SAME producer's universal child conclusions in the exact
ordered member list of an actual successful chain, including marked edges. -/
theorem evaluated_chain_from_actual_children
    {root : B} {original target localTarget : LTerm}
    {edge : BetaEdge site.net} {selection : SourceEdgeSelection original site.net root}
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (all : ∀ (p : Path) (step : Step) (parentTerm : LTerm),target.subterm p=some parentTerm →
      ∀child : OccurrenceFragment target site.reduce root (p++[step]),
        SourceDeparture parentTerm step (sourceEdge child.environment child.context child.term).fromPort →
        ∃node,localTarget.subterm (p++[step])=some node ∧node.erase=child.term.erase ∧
          selection.evalLabel edge node.label≠[] ∧BetaPathResidual site edge
            (child.fragment.segments.map (plugEnd _ _).invFun) (selection.evalLabel edge node.label))
    (chain : PrerequisiteChain target start es) :
    Nonempty (EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain) := by
  classical
  have witnesses (member : {p : Path // p∈es}) := evaluated_at_nonroot site all
    (targetSelection (actualChainPosition chain member)) (chain.reading_ne_nil member.property)
  exact ⟨{
    node:=fun member=>Classical.choose (witnesses member)
    lookup:=fun member=>(Classical.choose_spec (witnesses member)).1
    nonempty:=fun member=>(Classical.choose_spec (witnesses member)).2.1
    residual:=fun member=>(Classical.choose_spec (witnesses member)).2.2 }⟩

/-- Equal actual target blocks force equal evaluated OLD blocks using the
SAME residual geometry. Coordinates and labels are not identified. -/
theorem EvaluatedChainResiduals.blocks_eq_of_target_images
    {root : B} {original target localTarget : LTerm}
    {edge : BetaEdge site.net} {selection : SourceEdgeSelection original site.net root}
    {targetSelection : OccurrenceFragmentSelection target site.reduce root}
    {leftChain : PrerequisiteChain target ls les} {rightChain : PrerequisiteChain target rs res}
    (geometry : SiteBetaGeometry site edge)
    (left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection leftChain)
    (right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection rightChain)
    (same : SameChainRepresentation targetSelection leftChain rightChain) : left.blocks site=right.blocks site := by
  have lengths := congrArg List.length same
  change (canonicalChainImage targetSelection leftChain).length=(canonicalChainImage targetSelection rightChain).length at lengths
  rw [canonicalChainImage_length,canonicalChainImage_length] at lengths
  apply List.ext_getElem (by simpa only [EvaluatedChainResiduals.blocks,List.length_map,List.length_attach] using lengths)
  intro n leftBound rightBound
  have lb : n<les.length := by simpa only [EvaluatedChainResiduals.blocks,List.length_map,List.length_attach] using leftBound
  have rb : n<res.length := by simpa only [EvaluatedChainResiduals.blocks,List.length_map,List.length_attach] using rightBound
  let lm : {p : Path // p∈les} := les.attach[n]'(by simpa using lb)
  let rm : {p : Path // p∈res} := res.attach[n]'(by simpa using rb)
  have lp : les[n]?=some (actualChainPosition leftChain lm).val := by
    rw [List.getElem?_eq_getElem lb]
    simp only [actualChainPosition,lm,List.getElem_attach]
  have rp : res[n]?=some (actualChainPosition rightChain rm).val := by
    rw [List.getElem?_eq_getElem rb]
    simp only [actualChainPosition,rm,List.getElem_attach]
  have pieces := same_chain_representation_slot targetSelection leftChain rightChain same
    (actualChainPosition leftChain lm) (actualChainPosition rightChain rm) lp rp
  have rr := right.residual rm
  rw [←pieces] at rr
  have eq := (left.residual lm).source_unique site geometry rr
  simpa only [EvaluatedChainResiduals.blocks,List.getElem_map,lm,rm] using eq

/-- ONE real normal development produces all actual ordered chain evaluator
residuals with one local history, selector, beta edge and geometry. -/
theorem PathSite.beta_evaluated_chain_residuals
    {root : B} {source target : LTerm} {ps : List Path} {marked : Marked}
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root) :
    ∃localTarget,History ps (initLabels source.erase) localTarget ∧localTarget.erase=target.erase ∧
      Matches site.reduce root target.erase ∧∃edge : BetaEdge site.net,
        ∃selection : SourceEdgeSelection (initLabels source.erase) site.net root,SiteBetaGeometry site edge ∧
          ∀{p es} (chain : PrerequisiteChain target p es),
            Nonempty (EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain) := by
  obtain ⟨localTarget,localHistory,erase,targetMatches,edge,selection,geometry,all⟩ :=
    site.beta_evaluated_child_residuals closed matching inputs flow positive balance rootDepth transparency relative normal history
  exact ⟨localTarget,localHistory,erase,targetMatches,edge,selection,geometry,
    fun chain=>evaluated_chain_from_actual_children site targetSelection all chain⟩
end

#print axioms evaluated_chain_from_actual_children
#print axioms EvaluatedChainResiduals.blocks_eq_of_target_images
#print axioms PathSite.beta_evaluated_chain_residuals
end Lamping.AG

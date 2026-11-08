import Lamping.Lamping.ReverseReadingLetterBlocks
import Lamping.Checks.BetaChainEvaluatedResiduals
import Lamping.Checks.MarkedAuxiliaryPhysicalFixture

namespace Lamping.Checks.ReverseReadingLetterBlocksChecks
open AG Graph Lambda Lambda.Labelled
open FanSuccessfulChains
open BetaChainEvaluatedResidualsChecks

private abbrev Regular {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} (block : List (Endpoint g)) : Prop := block≠[] ∧
  (∀ e f,(e,f)∈block.zip block.tail →ControlOnlyTurn (g:=g) e f) ∧
  ∃ (node : N) (port : Port (g.label node).sort),
    ((g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) ∧
      block.getLast?=some (g.wire (.inl ⟨node,port⟩))

private noncomputable def readingBlocks {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {original : LTerm} {root : B}
    (selection : SourceEdgeSelection original g root) (edge : BetaEdge g) (stamp : Label) :=
  (stamp.readLetters false).map (fun letter=>orientPhysical false (letter.sourceWord selection.atomWord edge.principal edge.reverseRoute))

/-- ONE real producer supplies the SAME local history and four actual slots.
At every common ordinal the NEW regularity theorem supplies both physical
letter decompositions, and the public parser consumes their false reversed whole evaluation Eq. -/
theorem actual_four_slot_reverse_parser
    (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ())) :
    ∃localTarget,History [[.fn]] (initLabels original.erase) localTarget ∧
      ∃edge : BetaEdge site.net,
        ∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
          SiteBetaGeometry site edge ∧
          ∃left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_lambda_chain,
            ∃right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_variable_chain,
              left.blocks site=right.blocks site ∧(left.blocks site).length=4 ∧
                ∀member : {p : Path // p∈rightEdges},
                  (∀block∈readingBlocks selection edge (left.node member).label,Regular block) ∧
                  (∀block∈readingBlocks selection edge (right.node member).label,Regular block) ∧
                  readingBlocks selection edge (left.node member).label=
                    readingBlocks selection edge (right.node member).label := by
  obtain ⟨localTarget,localHistory,edge,selection,geometry,left,right,_suppliedEq,length,_nonempty⟩:=
    actual_ordered_chain_evaluators targetSelection
  have sameBlocks:=left.blocks_eq_of_target_images site geometry right (by rfl)
  refine ⟨localTarget,localHistory,edge,selection,geometry,left,right,sameBlocks,length,?_⟩
  intro member
  have lr:=left.reverse_reading_letter_blocks_regular site (init_is_INIT _) localHistory member
  have rr:=right.reverse_reading_letter_blocks_regular site (init_is_INIT _) localHistory member
  have common:=sameBlocks
  change rightEdges.attach.map (fun p=>selection.evalLabel edge (left.node p).label)=
    rightEdges.attach.map (fun p=>selection.evalLabel edge (right.node p).label) at common
  have writingEq:=(List.map_inj_left.mp common) member (List.mem_attach rightEdges member)
  have flattened :
      (readingBlocks selection edge (left.node member).label).flatten=
        (readingBlocks selection edge (right.node member).label).flatten :=
    lr.1.trans ((congrArg reverseEdges writingEq).trans rr.1.symm)
  exact ⟨lr.2,rr.2,proper_ended_control_blocks_unique lr.2 rr.2 flattened⟩

/-- Actual Matches, not a selector oracle, inhabits this direct NEW integration. -/
theorem actual_nonempty_four_slot_reverse_parser :
    ∃targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ()),
      ∃localTarget,History [[.fn]] (initLabels original.erase) localTarget ∧
        ∃edge : BetaEdge site.net,
          ∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
            SiteBetaGeometry site edge ∧
            ∃left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_lambda_chain,
              ∃right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_variable_chain,
                (left.blocks site).length=4 ∧
                ∀member : {p : Path // p∈rightEdges},
                  readingBlocks selection edge (left.node member).label=
                    readingBlocks selection edge (right.node member).label := by
  obtain ⟨targetSelection⟩:=FanSuccessfulReachable.beta_matches.occurrence_fragment_selection targetClosed
  obtain ⟨localTarget,history,edge,selection,geometry,left,right,_eq,length,all⟩:=
    actual_four_slot_reverse_parser targetSelection
  exact ⟨targetSelection,localTarget,history,edge,selection,geometry,left,right,length,
    fun member=>(all member).2.2⟩

/-- The universal direct call includes these nonfirst APP and FUNCTION-variable
slots, not just an abstract whole-evaluator nonempty fact. -/
theorem actual_nonfirst_APP_and_FUNCTION :
    (∃a fn arg,current.subterm rightEdges[1]=some (.app a fn arg)) ∧
      (∃a,current.subterm rightEdges[2]=some (.var a 0)) := by
  exact ⟨⟨_,_,_,rfl⟩,⟨_,rfl⟩⟩

namespace RootBoundaryGuard
open MarkedAuxiliaryPhysicalFixture
private theorem external_endpoint {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {source : LTerm} {root : B} {endpoint : Endpoint g}
    (realizes : SourcePortRealizes source g root .external endpoint) : endpoint=.inr (.inl root) := by
  cases realizes with
  | external => rfl
  | departure lookup role parent word roles finish => cases role
noncomputable def selection : SourceEdgeSelection MarkedAuxiliaryPhysicalFixture.original concrete.site.net (.inl ()) :=
  source_matching.source_edge_selection closed
def cell : {e : SourceEdge //e∈sourceEdges [] .external MarkedAuxiliaryPhysicalFixture.original} :=
  ⟨sourceEdge [] .external MarkedAuxiliaryPhysicalFixture.original,by decide⟩
/-- An actual old root cell reverses to a boundary arrival. It is not a
successful CURRENT chain slot and cannot be fed to the proper-ended parser. -/
theorem actual_old_root_reverse_not_regular :
    ¬Regular (reverseEdges (selection.chosen cell).2.segments) := by
  let fragment := (selection.chosen cell).2
  have external : fragment.fromEndpoint=(.inr (.inl (.inl ()))) :=
    external_endpoint fragment.fromRealizes
  have finish : (reverseEdges fragment.segments).getLast?=
      some (concrete.site.net.wire (.inr (.inl (.inl ())))) := by
    simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,fragment.start,Option.map_some,external]
  rintro ⟨_nonempty,_turns,node,port,_shape,last⟩
  have wired := Option.some.inj (finish.symm.trans last)
  have ends := congrArg concrete.site.net.wire wired
  simp only [concrete.site.net.wire.involutive] at ends
  cases ends
end RootBoundaryGuard

#print axioms actual_four_slot_reverse_parser
#print axioms actual_nonempty_four_slot_reverse_parser
#print axioms actual_nonfirst_APP_and_FUNCTION
#print axioms RootBoundaryGuard.actual_old_root_reverse_not_regular
end Lamping.Checks.ReverseReadingLetterBlocksChecks

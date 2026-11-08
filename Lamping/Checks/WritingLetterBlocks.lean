import Lamping.Lamping.WritingLetterBlocks
import Lamping.Checks.BetaChainEvaluatedResiduals

namespace Lamping.Checks.WritingLetterBlocksChecks
open AG Graph Lambda Lambda.Labelled
open FanSuccessfulChains
open BetaChainEvaluatedResidualsChecks

private abbrev Regular {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} (block : List (Endpoint g)) : Prop := block≠[] ∧
  (∀ e f,(e,f)∈block.zip block.tail →ControlOnlyTurn (g:=g) e f) ∧
  ∃ (node : N) (port : Port (g.label node).sort),
    ((g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) ∧
      block.getLast?=some (g.wire (.inl ⟨node,port⟩))

private noncomputable def writingBlocks {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {original : LTerm} {root : B}
    (selection : SourceEdgeSelection original g root) (edge : BetaEdge g) (stamp : Label) :=
  stamp.letters.map (fun letter=>letter.sourceWord selection.atomWord edge.principal edge.reverseRoute)

/-- ONE real producer supplies the SAME local history and four actual slots.
At every common ordinal the NEW regularity theorem supplies both physical
letter decompositions, and the public parser consumes their true writing Eq. -/
theorem actual_four_slot_writing_parser
    (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ())) :
    ∃localTarget,History [[.fn]] (initLabels original.erase) localTarget ∧
      ∃edge : BetaEdge site.net,
        ∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
          SiteBetaGeometry site edge ∧
          ∃left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_lambda_chain,
            ∃right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_variable_chain,
              left.blocks site=right.blocks site ∧(left.blocks site).length=4 ∧
                ∀member : {p : Path // p∈rightEdges},
                  (∀block∈writingBlocks selection edge (left.node member).label,Regular block) ∧
                  (∀block∈writingBlocks selection edge (right.node member).label,Regular block) ∧
                  writingBlocks selection edge (left.node member).label=
                    writingBlocks selection edge (right.node member).label := by
  obtain ⟨localTarget,localHistory,edge,selection,geometry,left,right,_suppliedEq,length,_nonempty⟩:=
    actual_ordered_chain_evaluators targetSelection
  have sameBlocks:=left.blocks_eq_of_target_images site geometry right (by rfl)
  refine ⟨localTarget,localHistory,edge,selection,geometry,left,right,sameBlocks,length,?_⟩
  intro member
  have lr:=left.writing_letter_blocks_regular site (init_is_INIT _) localHistory member
  have rr:=right.writing_letter_blocks_regular site (init_is_INIT _) localHistory member
  have common:=sameBlocks
  change rightEdges.attach.map (fun p=>selection.evalLabel edge (left.node p).label)=
    rightEdges.attach.map (fun p=>selection.evalLabel edge (right.node p).label) at common
  have writingEq:=(List.map_inj_left.mp common) member (List.mem_attach rightEdges member)
  have flattened :
      (writingBlocks selection edge (left.node member).label).flatten=
        (writingBlocks selection edge (right.node member).label).flatten :=
    lr.2.1.trans (writingEq.trans rr.2.1.symm)
  exact ⟨lr.2.2,rr.2.2,proper_ended_control_blocks_unique lr.2.2 rr.2.2 flattened⟩

/-- Actual Matches, not a selector oracle, inhabits this direct NEW integration. -/
theorem actual_nonempty_four_slot_writing_parser :
    ∃targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ()),
      ∃localTarget,History [[.fn]] (initLabels original.erase) localTarget ∧
        ∃edge : BetaEdge site.net,
          ∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
            SiteBetaGeometry site edge ∧
            ∃left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_lambda_chain,
              ∃right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_variable_chain,
                (left.blocks site).length=4 ∧
                ∀member : {p : Path // p∈rightEdges},
                  writingBlocks selection edge (left.node member).label=
                    writingBlocks selection edge (right.node member).label := by
  obtain ⟨targetSelection⟩:=FanSuccessfulReachable.beta_matches.occurrence_fragment_selection targetClosed
  obtain ⟨localTarget,history,edge,selection,geometry,left,right,_eq,length,all⟩:=
    actual_four_slot_writing_parser targetSelection
  exact ⟨targetSelection,localTarget,history,edge,selection,geometry,left,right,length,
    fun member=>(all member).2.2⟩

/-- The universal direct call includes these nonfirst APP and FUNCTION-variable
slots, not just an abstract whole-evaluator nonempty fact. -/
theorem actual_nonfirst_APP_and_FUNCTION :
    (∃a fn arg,current.subterm rightEdges[1]=some (.app a fn arg)) ∧
      (∃a,current.subterm rightEdges[2]=some (.var a 0)) := by
  exact ⟨⟨_,_,_,rfl⟩,⟨_,rfl⟩⟩

#print axioms actual_four_slot_writing_parser
#print axioms actual_nonempty_four_slot_writing_parser
#print axioms actual_nonfirst_APP_and_FUNCTION
#print axioms Lamping.AG.proper_ended_control_blocks_unique
#print axioms Lamping.AG.transparent_reverse_turns
end Lamping.Checks.WritingLetterBlocksChecks

import Lamping.Lamping.FanLambdaChainPassages
import Lamping.Checks.SuccessfulAuxiliaryPhysicalPair
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanLambdaChainPassageConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable
open FanSuccessfulChains hiding current original

noncomputable abbrev sourceNet := actualFanPresentation.site.net
noncomputable abbrev targetNet := actualFanPresentation.site.reduce
abbrev selected (branch : Bool) : Path := if branch then FanSuccessfulChains.right else FanSuccessfulChains.left
abbrev starting (branch : Bool) : Path := if branch then rightBody else leftBody
abbrev fullEdges (branch : Bool) : List Path := if branch then rightBodyEdges else leftBodyEdges
abbrev remainingEdges (branch : Bool) : List Path := if branch then FanSuccessfulChains.rightEdges else FanSuccessfulChains.leftEdges

def actualChain (branch : Bool) : PrerequisiteChain current (starting branch) (fullEdges branch) := by
  cases branch
  · exact left_body_chain
  · exact right_body_chain

def actualRemainder (branch : Bool) : PrerequisiteChain current (selected branch) (remainingEdges branch) := by
  cases branch
  · exact left_lambda_chain
  · exact right_lambda_chain

def selectedPosition (branch : Bool) : Position current.erase := ⟨selected branch,by cases branch <;> rfl⟩

theorem actual_source_matches : Matches sourceNet (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := beta_certified
  exact actualFanPresentation.sourceIso.matches matching

theorem actual_target_matches : Matches targetNet (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := lambda_certified
  exact matching

theorem actual_two_step_trace :
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons actualFanPresentation.graph_step (.refl _))

/-- Each actual slot is after the body's FUNCTION edge and its genuine
zero-edge variable-to-binder jump. The remaining chain has its real 3/4 edges. -/
theorem actual_noninitial_passage
    (principal : SiteActionPrincipal actualFanPresentation.site)
    (source : OccurrenceFragmentSelection current sourceNet (.inl ())) (branch : Bool)
    {a b : Context} (whole : Labelling sourceNet (source (selectedPosition branch)).fragment.access.val a b) :
    ∃ before after pre input seam,
      fullEdges branch=before++(selected branch::after) ∧before≠[] ∧
      PrerequisitePrefix current (starting branch) before (selected branch) ∧
      PrerequisiteChain current (selected branch) (selected branch::after) ∧
      selected branch::after=remainingEdges branch ∧
      (source (selectedPosition branch)).fragment.segments∈canonicalChainImage source (actualChain branch) ∧
      (source (selectedPosition branch)).fragment.segments=pre++principal.edges ∧
      pre.head?=some (source (selectedPosition branch)).fragment.fromEndpoint ∧
      pre.getLast?=some (sourceNet.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)) ∧
      Labelling sourceNet (source (selectedPosition branch)).fragment.segments input b ∧
      Labelling sourceNet pre input seam ∧
      Traversal 0 (.op .fan) (.inr branch) (.inl ()) seam b ∧
      ((source (selectedPosition branch)).fragment.before=[] ∧input=a ∨
        Labelling sourceNet (source (selectedPosition branch)).fragment.before a input) ∧
      reverseEdges (source (selectedPosition branch)).fragment.segments=reverseEdges principal.edges++reverseEdges pre ∧
      Labelling sourceNet (reverseEdges (source (selectedPosition branch)).fragment.segments) b input ∧
      Traversal 0 (.op .fan) (.inl ()) (.inr branch) b seam := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  have member : (selectedPosition branch).val∈fullEdges branch := by
    cases branch <;> simp [selectedPosition,selected,fullEdges,leftBodyEdges,rightBodyEdges,
      FanSuccessfulChains.leftEdges,FanSuccessfulChains.rightEdges]
  obtain ⟨before,after,middle,pre,input,seam,split,segment,remainder,reads,inImage,pieceSplit,
    head,last,pieceLabels,prefixLabels,writer,beforeLabels,reverseSplit,reverseLabels,reader⟩ :=
    actualFanPresentation.site.fan_lambda_chain_writer_passage actual_source_matches
      (actualFanPresentation.sourceIso.flowBalance flow) rfl principal source (actualChain branch)
      (selectedPosition branch) member (SuccessfulAuxiliaryPhysicalPair.chosenParent branch)
      (SuccessfulAuxiliaryPhysicalPair.chosenWord branch) branch
      (SuccessfulAuxiliaryPhysicalPair.chosenFinish branch) whole
  have middleEq : middle=selected branch := by
    rcases reads with ⟨stamp,fn,arg,_lookup,equal⟩|⟨stamp,body,_lookup,equal⟩
    · have last := congrArg List.getLast? equal
      cases branch <;> simp [selectedPosition,selected,FanSuccessfulChains.left,FanSuccessfulChains.right] at last
    · exact equal.symm
  subst middle
  have beforeNonempty : before≠[] := by
    intro empty
    have first := congrArg List.head? split
    rw [empty,List.nil_append] at first
    cases branch <;> simp [fullEdges,selectedPosition,selected,leftBodyEdges,rightBodyEdges,leftVar,rightVar,
      leftBody,rightBody,FanSuccessfulChains.left,FanSuccessfulChains.right] at first
  have exactRemainder := remainder.unique (actualRemainder branch)
  exact ⟨before,after,pre,input,seam,split,beforeNonempty,segment,remainder,exactRemainder,
    inImage,pieceSplit,head,last,pieceLabels,prefixLabels,writer,beforeLabels,reverseSplit,reverseLabels,reader⟩

/-- The actual nonempty successful-chain fixture supplies both Matches,
selectors and ONE principal; each branch really occurs in a noninitial slot.
No source Joint truth or two-chain branch synchronization is asserted. -/
theorem actual_reachable_passages :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase ∧
    Closed current.erase ∧
    Nonempty (OccurrenceFragmentSelection current sourceNet (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current targetNet (.inl ())) ∧
    (∀branch,PrerequisiteChain current (starting branch) (fullEdges branch) ∧
      (fullEdges branch).length=(if branch then 5 else 4)) ∧
    ∃principal : SiteActionPrincipal actualFanPresentation.site,
      ∀ (source : OccurrenceFragmentSelection current sourceNet (.inl ())) (branch : Bool),
      ∃ a b before after pre input seam,
        Labelling sourceNet (source (selectedPosition branch)).fragment.access.val a b ∧
        fullEdges branch=before++(selected branch::after) ∧before≠[] ∧
        PrerequisitePrefix current (starting branch) before (selected branch) ∧
        PrerequisiteChain current (selected branch) (selected branch::after) ∧
        selected branch::after=remainingEdges branch ∧
        (source (selectedPosition branch)).fragment.segments∈canonicalChainImage source (actualChain branch) ∧
        (source (selectedPosition branch)).fragment.segments=pre++principal.edges ∧
        pre.getLast?=some (sourceNet.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)) ∧
        Labelling sourceNet (source (selectedPosition branch)).fragment.segments input b ∧
        Labelling sourceNet pre input seam ∧
        Traversal 0 (.op .fan) (.inr branch) (.inl ()) seam b ∧
        ((source (selectedPosition branch)).fragment.before=[] ∧input=a ∨
          Labelling sourceNet (source (selectedPosition branch)).fragment.before a input) ∧
        Labelling sourceNet (reverseEdges (source (selectedPosition branch)).fragment.segments) b input ∧
        Traversal 0 (.op .fan) (.inl ()) (.inr branch) b seam := by
  refine ⟨FanSuccessfulChains.initial,sourceClosed,actualHistory,actual_two_step_trace,
    actual_source_matches,actual_target_matches,targetClosed,
    actual_source_matches.occurrence_fragment_selection targetClosed,
    actual_target_matches.occurrence_fragment_selection targetClosed,?_,?_⟩
  · intro branch
    exact ⟨actualChain branch,by cases branch <;> rfl⟩
  · obtain ⟨principal⟩ := actualFanPresentation.site.actionPrincipal_exists
    refine ⟨principal,?_⟩
    intro source branch
    obtain ⟨a,b,whole⟩ := (source (selectedPosition branch)).fragment.access.property.1.1
    obtain ⟨before,after,pre,input,seam,split,nonempty,segment,remainder,exactSuffix,inImage,
      pieceSplit,_head,last,pieceLabels,prefixLabels,writer,beforeLabels,_reverseSplit,reverseLabels,reader⟩ :=
      actual_noninitial_passage principal source branch whole
    exact ⟨a,b,before,after,pre,input,seam,whole,split,nonempty,segment,remainder,exactSuffix,
      inImage,pieceSplit,last,pieceLabels,prefixLabels,writer,beforeLabels,reverseLabels,reader⟩

#print axioms actualChain
#print axioms actual_source_matches
#print axioms actual_target_matches
#print axioms actual_two_step_trace
#print axioms actual_noninitial_passage
#print axioms actual_reachable_passages
end Lamping.Checks.FanLambdaChainPassageConsumer
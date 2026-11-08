import Lamping.Lamping.AuxiliaryEndpointReflection
import Lamping.Checks.PairedCurrentChainSourceLabels
import Lamping.Checks.OldChainBetaFixture

namespace Lamping.Checks.AuxiliaryEndpointReflectionChecks
open Graph Lambda Lambda.Labelled AG
open SyntaxIncidence

namespace Marked
open PairedCurrentChainSourceLabelsChecks.NoninitialDistinct

def leftVertex : ProperPosition current := ⟨leftStart,Or.inr ⟨_,_,rfl⟩⟩
def rightVertex : ProperPosition current := ⟨rightStart,Or.inr ⟨_,_,rfl⟩⟩
def oldLeftVertex : ProperPosition source := ⟨leftStart,Or.inr ⟨_,_,rfl⟩⟩
def oldRightVertex : ProperPosition source := ⟨rightStart,Or.inr ⟨_,_,rfl⟩⟩

/-- Real marked READs at distinct lambda starts, after the actual non-INIT prefix. -/
theorem actual_marked_endpoint_reflection :
    SuccessfulEndpointIso source sourceClosed (some oldLeftVertex) (some oldRightVertex) :=
  same_kind_old_endpoint_iso initial prefixHistory old labels selected sourceSafe sourceClosed currentClosed
    leftVertex rightVertex oldLeftVertex oldRightVertex (.proper leftTrace) (.proper rightTrace)
    leftChain rightChain currentIso ⟨false,⟨_,_,rfl⟩,⟨_,_,rfl⟩⟩

/-- This guard retains the real variable zero-jump and its marked binder READ.
The variable is FUNCTION, so it is not relabelled as an auxiliary test. -/
theorem actual_zero_jump_scope :
    PrerequisiteChain current PairedCurrentChainSourceLabelsChecks.ZeroJump.leftLeaf leftEdges ∧
      ¬AuxiliaryAt current PairedCurrentChainSourceLabelsChecks.ZeroJump.leftLeaf ∧
      ¬degreeReadSafe (.atom 6) (current.labelAt leftStart) ∧
      SuccessfulEndpointIso source sourceClosed (some oldLeftVertex) (some oldRightVertex) := by
  refine ⟨PairedCurrentChainSourceLabelsChecks.ZeroJump.leftLeafChain,?_,marked,actual_marked_endpoint_reflection⟩
  intro aux
  exact aux.1 ⟨leftStart++[.body],_,_,_,rfl,rfl⟩
end Marked

namespace Terminal
open DirectedReadingDecompositionChecks
open PairedCurrentChainSourceLabelsChecks.Terminal

def currentVertex : ProperPosition target := ⟨[],Or.inl ⟨_,_,_,rfl⟩⟩
def oldVertex : ProperPosition source := ⟨[],Or.inl ⟨_,_,_,rfl⟩⟩

theorem actual_same_kind_terminal_reflection :
    SuccessfulEndpointIso source closed (some oldVertex) (some oldVertex) :=
  same_kind_old_endpoint_iso initial (.nil source) old history selected sourceSafe closed currentClosed
    currentVertex currentVertex oldVertex oldVertex (.proper appTrace) (.proper appTrace)
    successful_function successful_function ⟨ChainIncidenceIso.refl _⟩ ⟨true,⟨_,_,_,rfl⟩,⟨_,_,_,rfl⟩⟩

theorem generic_opposite_remains_negative :
    ¬ChainIncidenceIsomorphic
      (chainSyntaxIncidence source closed [[.fn],[.fn,.fn]])
      (chainSyntaxIncidence source closed [[.fn,.arg],[.fn,.fn]]) := no_original_bare_iso
end Terminal

namespace Physical
open OldChainBetaFixture

abbrev sourceClosed : Closed initial.erase := closed
abbrev currentClosed : Closed result.erase := history.closed sourceClosed

def edge : SyntaxIncidence.Edge result := ⟨[.fn,.body],by rfl⟩
def binder : ProperPosition result := ⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩

theorem auxiliary : AuxiliaryAt result edge.val := by
  constructor
  · rintro ⟨parent,stamp,fn,arg,split,_lookup⟩
    have last := congrArg List.getLast? split
    simp only [edge,List.getLast?_cons_cons,List.getLast?_singleton,List.getLast?_append,
      Option.some_or] at last
    cases last
  · rintro ⟨stamp,body,lookup⟩
    cases lookup

theorem source_spec : SyntaxIncidence.Source result edge.val (some binder) :=
  ⟨.body,.lam (.atom 4) (.var (.atom 5) 0),.lamBody (.atom 4),rfl,rfl,.body⟩

theorem target_spec : SyntaxIncidence.Target result edge.val (some binder) :=
  Or.inr ⟨.atom 5,0,.atom 4,.var (.atom 5) 0,[],rfl,rfl,rfl,rfl⟩

def endpoint_chain : EndpointChain result (some binder) [[.fn]] := by
  change PrerequisiteChain result ([]++[.fn]) [[]++[.fn]]
  exact PrerequisiteChain.redex_lam (by rfl)

theorem both_successful :
    SuccessfulEndpointIso result currentClosed (SyntaxIncidence.source result edge) (SyntaxIncidence.source result edge) ∧
    SuccessfulEndpointIso result currentClosed (SyntaxIncidence.target result currentClosed edge)
      (SyntaxIncidence.target result currentClosed edge) := by
  rw [SyntaxIncidence.source_eq_of_spec result edge source_spec,
    SyntaxIncidence.target_eq_of_spec result currentClosed edge target_spec]
  exact ⟨SuccessfulEndpointIso.refl_of_chain endpoint_chain,SuccessfulEndpointIso.refl_of_chain endpoint_chain⟩

def old (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :
    Marked.RelativeOldHistory (presentation.site.betaSyntaxFiber (.inl ()) initial.erase) [[]]
      (Marked.mark (presentation.site.betaSyntaxFiber (.inl ()) initial.erase) initial.erase) endpoint :=
  (Marked.relativeOld_iff_relative (Marked.selected_mark _ _)).mpr (relative presentation)

theorem selected (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()))
    (name : Path) (member : name∈presentation.site.betaSyntaxFiber (.inl ()) initial.erase) :
    initial.degreeAt name=some (.atom 1) := by
  have fiber : presentation.site.betaSyntaxFiber (.inl ()) initial.erase=[[]] := by
    simpa only [initial,erase_initLabels] using actual_fiber presentation
  rw [fiber] at member
  have same:=List.mem_singleton.mp member
  subst name;rfl

/-- Direct natural high on the genuine physical beta fixture; selfpair endpoint
success is real, not a both-undefined alternative or a lambda-incoming Aux. -/
theorem actual_physical_old_endpoint_supply
    (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :
    ∃ (oldLeft oldRight : SyntaxIncidence.Edge initial) (leftNode rightNode : LTerm),
      initial.subterm oldLeft.val=some leftNode ∧initial.subterm oldRight.val=some rightNode ∧
      BetaNodeHistoryPreimage history edge.val oldLeft.val ∧BetaNodeHistoryPreimage history edge.val oldRight.val ∧
      AuxiliaryAt initial oldLeft.val ∧AuxiliaryAt initial oldRight.val ∧
      leftNode.label=rightNode.label ∧SyntaxIncidence.label initial oldLeft=SyntaxIncidence.label initial oldRight ∧
      SuccessfulEndpointIso initial sourceClosed (SyntaxIncidence.source initial oldLeft) (SyntaxIncidence.source initial oldRight) ∧
      SuccessfulEndpointIso initial sourceClosed (SyntaxIncidence.target initial sourceClosed oldLeft)
        (SyntaxIncidence.target initial sourceClosed oldRight) :=
  uniform_old_equal_auxiliary_endpoint_isos (init_is_INIT term) (.nil initial) (old presentation)
    history (selected presentation) ((init_is_INIT term).outerBarsSafe _) sourceClosed edge edge
    auxiliary auxiliary rfl both_successful.1 both_successful.2

/-- Arbitrary source selector and honest SOURCEJoint, directly consuming the
new old-wholepiece consequence. No target wholepiece/Joint conclusion. -/
theorem actual_physical_old_pieces
    (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()))
    (selection : OccurrenceFragmentSelection initial presentation.site.net (.inl ()))
    (joint : JointRepresentation sourceClosed selection) :
    ∃ (oldLeft oldRight : SyntaxIncidence.Edge initial) (leftNode rightNode : LTerm),
      initial.subterm oldLeft.val=some leftNode ∧initial.subterm oldRight.val=some rightNode ∧
      BetaNodeHistoryPreimage history edge.val oldLeft.val ∧BetaNodeHistoryPreimage history edge.val oldRight.val ∧
      AuxiliaryAt initial oldLeft.val ∧AuxiliaryAt initial oldRight.val ∧
      leftNode.label=rightNode.label ∧SyntaxIncidence.label initial oldLeft=SyntaxIncidence.label initial oldRight ∧
      SuccessfulEndpointIso initial sourceClosed (SyntaxIncidence.source initial oldLeft) (SyntaxIncidence.source initial oldRight) ∧
      SuccessfulEndpointIso initial sourceClosed (SyntaxIncidence.target initial sourceClosed oldLeft)
        (SyntaxIncidence.target initial sourceClosed oldRight) ∧
      (selection oldLeft).fragment.segments=(selection oldRight).fragment.segments :=
  uniform_old_equal_auxiliary_source_pieces (init_is_INIT term) (.nil initial) (old presentation)
    history (selected presentation) ((init_is_INIT term).outerBarsSafe _) sourceClosed selection joint
    edge edge auxiliary auxiliary rfl both_successful.1 both_successful.2
end Physical
end Lamping.Checks.AuxiliaryEndpointReflectionChecks

#print axioms Lamping.Checks.AuxiliaryEndpointReflectionChecks.Marked.actual_marked_endpoint_reflection
#print axioms Lamping.Checks.AuxiliaryEndpointReflectionChecks.Marked.actual_zero_jump_scope
#print axioms Lamping.Checks.AuxiliaryEndpointReflectionChecks.Terminal.actual_same_kind_terminal_reflection
#print axioms Lamping.Checks.AuxiliaryEndpointReflectionChecks.Terminal.generic_opposite_remains_negative
#print axioms Lamping.Checks.AuxiliaryEndpointReflectionChecks.Physical.both_successful
#print axioms Lamping.Checks.AuxiliaryEndpointReflectionChecks.Physical.actual_physical_old_endpoint_supply
#print axioms Lamping.Checks.AuxiliaryEndpointReflectionChecks.Physical.actual_physical_old_pieces

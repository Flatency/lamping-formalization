import Lamping.Lamping.ActualChainForwardOrder
import Lamping.Checks.ActualChainIncidenceOrder
import Lamping.Lamping.UncreatedChainIncidence
namespace Lamping.Checks.ActualChainForwardOrderChecks
open Graph Lambda Lambda.Labelled AG
namespace Singleton
open DirectedReadingDecompositionChecks
abbrev closedTarget : Closed target.erase := history.closed closed
theorem actual_edge_forward :
    [[Step.fn]].length=[[Step.fn]].length ∧
    actualChainIsoImage closedTarget closedTarget successful_function successful_context (ChainIncidenceIso.refl _)=[[.fn]] :=
  actual_chain_incidence_forward history initial closedTarget successful_function successful_context (ChainIncidenceIso.refl _)
theorem actual_label_forward : [[.fn]].map target.labelAt=[[.fn]].map target.labelAt :=
  actual_chain_labels_forward history initial closedTarget successful_function successful_context (ChainIncidenceIso.refl _)
theorem terminal_vertex_reverse_still_valid :
    ∀k,(IndexedSimpleIncidencePath.mappedSlot
      ActualChainPathPresentationsChecks.Singleton.appPath.presentation
      ActualChainPathPresentationsChecks.Singleton.lamPath.presentation (ChainIncidenceIso.refl _) k).val=1-k.val :=
  ActualChainPathPresentationsChecks.Singleton.actual_forced_reverse
end Singleton

namespace Distinct
abbrev I : Term := WrappedSuccessfulChains.I
abbrev A : Term := .app (.lam (.app (.var 0) I)) I
abbrev original : LTerm := initLabels (.app (.lam (.app (.var 0) (.var 0))) A)
abbrev body : LTerm := .app (.atom 2) (.var (.atom 3) 0) (.var (.atom 4) 0)
abbrev innerBody : LTerm := .app (.atom 7) (.var (.atom 8) 0) (.lam (.atom 9) (.var (.atom 10) 0))
abbrev argument : LTerm := .app (.atom 5) (.lam (.atom 6) innerBody) (.lam (.atom 11) (.var (.atom 12) 0))
abbrev current : LTerm := LTerm.contract (.atom 0) (.atom 1) body argument
def turn : StepAt [] original current := .root _ _ _ _
def history : History [[]] original current := .cons turn (.nil _)
theorem initial : INIT original := init_is_INIT _
theorem sourceClosed : Closed original.erase := by change (0<1 ∧0<1) ∧((0<1 ∧0<2) ∧0<1);decide
theorem closedCurrent : Closed current.erase := history.closed sourceClosed
theorem current_not_init : ¬INIT current := root_contract_not_INIT _ _ _ _
abbrev leftStart : Path := [.fn,.fn,.body]
abbrev rightStart : Path := [.arg,.fn,.body]
abbrev leftEdges : List Path := [[.fn,.fn,.body,.fn],[.fn,.fn]]
abbrev rightEdges : List Path := [[.arg,.fn,.body,.fn],[.arg,.fn]]
abbrev oldStart : Path := [.arg,.fn,.body]
abbrev oldEdges : List Path := [[.arg,.fn,.body,.fn],[.arg,.fn]]
def leftChain : PrerequisiteChain current leftStart leftEdges :=
  .app rfl (by intro stamp inner equal;cases equal)
    (.var (parent:=[.fn,.fn]) (rest:=[.fn]) rfl rfl rfl rfl (.redex_lam (p:=[.fn]) rfl))
def rightChain : PrerequisiteChain current rightStart rightEdges :=
  .app rfl (by intro stamp inner equal;cases equal)
    (.var (parent:=[.arg,.fn]) (rest:=[.fn]) rfl rfl rfl rfl (.redex_lam (p:=[.arg]) rfl))
def oldChain : PrerequisiteChain original oldStart oldEdges :=
  .app rfl (by intro stamp inner equal;cases equal)
    (.var (parent:=[.arg,.fn]) (rest:=[.fn]) rfl rfl rfl rfl (.redex_lam (p:=[.arg]) rfl))
def leftOrigins : BetaEdgePreimages body argument [] leftEdges oldEdges :=
  .cons (.copied (q:=[.fn]) (relative:=[.fn,.body,.fn]) rfl rfl)
    (.cons (.copied (q:=[.fn]) (relative:=[.fn]) rfl rfl) .nil)
def rightOrigins : BetaEdgePreimages body argument [] rightEdges oldEdges :=
  .cons (.copied (q:=[.arg]) (relative:=[.fn,.body,.fn]) rfl rfl)
    (.cons (.copied (q:=[.arg]) (relative:=[.fn]) rfl rfl) .nil)
theorem leftUncreated (edge : Path) (member : edge∈leftEdges) : ¬BetaCreatedIncoming body [] edge := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> decide
theorem rightUncreated (edge : Path) (member : edge∈rightEdges) : ¬BetaCreatedIncoming body [] edge := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> decide
noncomputable def leftIso :=
  (uncreated_chain_iso sourceClosed closedCurrent turn (by rfl) leftChain oldChain leftUncreated leftOrigins).val
noncomputable def rightIso :=
  (uncreated_chain_iso sourceClosed closedCurrent turn (by rfl) rightChain oldChain rightUncreated rightOrigins).val
noncomputable def comparison := leftIso.trans rightIso.symm

theorem actual_distinct_multiedge_forward : leftEdges.length=rightEdges.length ∧
    actualChainIsoImage closedCurrent closedCurrent leftChain rightChain comparison=rightEdges :=
  actual_chain_incidence_forward history initial closedCurrent leftChain rightChain comparison
theorem actual_distinct_label_forward : leftEdges.map current.labelAt=rightEdges.map current.labelAt :=
  actual_chain_labels_forward history initial closedCurrent leftChain rightChain comparison
theorem actual_noninit_same_origin : INIT original ∧History [[]] original current ∧¬INIT current ∧
    leftStart≠rightStart ∧leftEdges≠rightEdges :=
  ⟨initial,history,current_not_init,by decide,by decide⟩
theorem reverse_image_rejected :
    actualChainIsoImage closedCurrent closedCurrent leftChain rightChain comparison≠rightEdges.reverse := by
  rw [actual_distinct_multiedge_forward.2]
  decide
end Distinct

#print axioms History.redex_edge_of_equal_label
#print axioms actual_chain_incidence_slot_forward
#print axioms actual_chain_incidence_forward
#print axioms actual_chain_labels_forward
#print axioms Singleton.actual_edge_forward
#print axioms Singleton.terminal_vertex_reverse_still_valid
#print axioms Distinct.history
#print axioms Distinct.current_not_init
#print axioms Distinct.comparison
#print axioms Distinct.actual_distinct_multiedge_forward
#print axioms Distinct.actual_distinct_label_forward
#print axioms Distinct.actual_noninit_same_origin
#print axioms Distinct.reverse_image_rejected
end Lamping.Checks.ActualChainForwardOrderChecks

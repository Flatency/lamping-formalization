import Lamping.Lamping.MarkedOldSourceEndpointIso
import Lamping.Checks.SelectedNodeSourceOrigins
namespace Lamping.Checks.MarkedOldSourceEndpointIsoChecks
open AG Lambda Lambda.Labelled
open UniformOldCreatedIncomingLabelsChecks.Distinct
open NodeIncomingFirstCreationChecks.Distinct

theorem sourceClosed : Closed source.erase := by
  change (0<2 ∧0<2) ∧(0<2 ∧0<2)
  decide

def leftParent : SyntaxIncidence.ProperPosition source :=
  ⟨left,Or.inl ⟨.atom 6,.lam (.atom 7) (.var (.atom 8) 0),oldArgument,rfl⟩⟩
theorem leftSource : SyntaxIncidence.Source source oldLeft (some leftParent) :=
  ⟨.arg,.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) oldArgument,.appArg (.atom 6),rfl,rfl,.arg⟩

/-- Two distinct actual original APP occurrences carry the same degree, but
remain distinct coordinates. The new theorem constructs their successful iso. -/
theorem actual_old_source_iso :
    SuccessfulEndpointIso source sourceClosed (some leftParent) (some sourceParent) :=
  marked_old_source_endpoint_iso sourceClosed old selected leftTrace rightTrace
    (leftCurrent:=leftNode) (rightCurrent:=leftNode) rfl rfl source_safe marked marked leftSource oldSource

theorem actual_chain_coordinates
    (leftChain : EndpointChain source (some leftParent) es)
    (rightChain : EndpointChain source (some sourceParent) fs) :
    es=[left++[.fn]] ∧fs=[right++[.fn]] := by
  exact ⟨leftChain.unique (PrerequisiteChain.redex_app (by rfl)),
    rightChain.unique (PrerequisiteChain.redex_app (by rfl))⟩

/-- The single global INIT and actual history are retained. Success comes
with real chains at both distinct source vertices, never a no-chain clause. -/
theorem actual_same_initial_history_source_iso :
    INIT original ∧History [[],left,right] original target ∧
    Closed source.erase ∧oldLeft≠oldRight ∧leftParent.val≠sourceParent.val ∧
    SyntaxIncidence.Source source oldLeft (some leftParent) ∧
    SyntaxIncidence.Source source oldRight (some sourceParent) ∧
    EndpointChain source (some leftParent) [left++[.fn]] ∧
    EndpointChain source (some sourceParent) [right++[.fn]] ∧
    SuccessfulEndpointIso source sourceClosed (some leftParent) (some sourceParent) := by
  exact ⟨initial,globalHistory.append labels,sourceClosed,by decide,by decide,leftSource,oldSource,
    PrerequisiteChain.redex_app (by rfl),PrerequisiteChain.redex_app (by rfl),actual_old_source_iso⟩
#print axioms sourceClosed
#print axioms actual_old_source_iso
#print axioms actual_chain_coordinates
#print axioms actual_same_initial_history_source_iso
end Lamping.Checks.MarkedOldSourceEndpointIsoChecks

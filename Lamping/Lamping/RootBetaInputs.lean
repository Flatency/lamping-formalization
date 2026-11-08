import Lamping.Lamping.RootTypedDetours
import Lamping.Lamping.BetaProperAncestors
import Lamping.Lamping.BetaResidualContraction
import Lamping.Lamping.ReachableNesting
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Every actually labelled reduced typed root path has all root inputs after
beta. The SAME literal ancestor is rebuilt by finite typed-block induction;
no full proper-source Independence is assumed. Nesting is obtained from
structural indexed balance, and all endpoint metadata is reflected physically. -/
theorem PathSite.beta_rootInputs {boundary : B → Bool} {heights : B → Int}
    (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs site.net root) (transparency : Transparency site.net root) :
    RootInputs site.reduce root := by
  intro es input output terminal role level labels _forward rooted finish atTerminal incoming requested
  obtain ⟨edge,old,oldFirst,oldLast,geometry,relation,_labels,_oldForward,oldHead,oldFinish,oldSource,oldTarget⟩ :=
    site.beta_proper_ancestor flow root positive labels rooted finish (.root) trivial atTerminal
  cases oldSource
  obtain ⟨count,stream⟩ := relation.detour_blocks site geometry (labels.plug_decomposition _ _)
  obtain ⟨result,coherent⟩ := stream.typed_root_inputs_indexed flow positive balance rootDepth inputs
    (balance.nesting root rootDepth) transparency oldHead oldLast role level oldFinish oldTarget incoming requested
  exact ⟨result,relation.contract_actual site geometry labels (coherent.labelling _)⟩
end
end Lamping.AG

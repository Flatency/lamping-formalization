import Lamping.Lamping.ActualPrerequisiteSignedSlots
import Lamping.Checks.ForwardFarChainComparison
import Lamping.Checks.CanonicalAfterFarComparison
import Lamping.Checks.SingleUnsafeCopyFunctionAppInputs
import Lamping.Checks.PrerequisiteIncidencePaths
namespace Lamping.Checks.ActualPrerequisiteSignedSlotsChecks
open Lambda Lambda.Labelled SyntaxIncidence AG

namespace TwoCopies
open ForwardFarChainComparisonChecks.TwoCopies

theorem actual_app_singleton_slot : ∃first signs vertices,
    Target target [.fn,.fn] (some first) ∧
    SignedProperWalk target first [[.fn,.fn,.fn]] signs vertices ∧
    ∃reader : ProperPosition target,reader.val=[.fn,.fn] ∧
      vertices[0]?=some reader ∧signs[0]?=some true := by
  exact leftTail.signed_slot rfl PrerequisitePrefix.refl
    (show PrerequisiteReadsDirected target [.fn,.fn] [.fn,.fn,.fn] true from
      ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩)

theorem actual_lambda_singleton_slot : ∃first signs vertices,
    Target target [.fn,.fn,.fn] (some first) ∧
    SignedProperWalk target first [[.fn,.fn,.fn]] signs vertices ∧
    ∃reader : ProperPosition target,reader.val=[.fn,.fn,.fn] ∧
      vertices[0]?=some reader ∧signs[0]?=some false := by
  have chain : PrerequisiteChain target [.fn,.fn,.fn] [[.fn,.fn,.fn]]:=.redex_lam (p:=[.fn,.fn]) rfl
  exact chain.signed_slot rfl PrerequisitePrefix.refl
    (show PrerequisiteReadsDirected target [.fn,.fn,.fn] [.fn,.fn,.fn] false from
      ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩)

theorem actual_same_edge_two_legal_directions : ∃a b : ProperPosition target,
    a.val=[.fn,.fn] ∧b.val=[.fn,.fn,.fn] ∧a≠b ∧
    ∃ss ts vs ws,
      SignedProperWalk target a [[.fn,.fn,.fn]] ss vs ∧
      SignedProperWalk target b [[.fn,.fn,.fn]] ts ws ∧
      ss[0]?=some true ∧ts[0]?=some false := by
  obtain ⟨a,ss,vs,ae,aw,ar,arp,atA,asign⟩:=actual_app_singleton_slot
  obtain ⟨b,ts,ws,be,bw,br,brp,atB,bsign⟩:=actual_lambda_singleton_slot
  have ap : a.val=[.fn,.fn] := by
    have proper : ProperAt target [.fn,.fn]:=Or.inl ⟨_,_,_,rfl⟩
    have eq : a=⟨_,proper⟩:=Option.some.inj (Target.unique ae (Or.inl rfl))
    exact congrArg Subtype.val eq
  have bp : b.val=[.fn,.fn,.fn] := by
    have proper : ProperAt target [.fn,.fn,.fn]:=Or.inr ⟨_,_,rfl⟩
    have eq : b=⟨_,proper⟩:=Option.some.inj (Target.unique be (Or.inl rfl))
    exact congrArg Subtype.val eq
  refine ⟨a,b,ap,bp,?_,ss,ts,vs,ws,aw,bw,asign,bsign⟩
  intro equal
  have paths:=congrArg Subtype.val equal
  rw [ap,bp] at paths
  cases paths

theorem actual_generated_context : INIT source ∧History [[]] source target ∧¬INIT target := by
  refine ⟨initial,event.final_history,?_⟩
  exact CanonicalAfterFarComparisonChecks.TwoCopies.same_initial_noninitial_current.2.2
end TwoCopies

namespace NoninitialCuts
open SingleUnsafeCopyFunctionAppInputsChecks

theorem actual_nonempty_before_slots : ∃out : SingleUnsafeCopyFunctionAppInputs event sourceClosed leftStart rightStart [.fn] [.arg] es fs,
    out.left.before=[leftStart] ∧out.right.before=[rightStart] ∧
    ∃lf rf ls rs lv rv,
      Target target leftStart (some lf) ∧Target target rightStart (some rf) ∧
      SignedProperWalk target lf es ls lv ∧SignedProperWalk target rf fs rs rv ∧
      ∃lr rr : ProperPosition target,
        lr.val=[.arg,.fn] ∧rr.val=[.arg,.arg] ∧
        lv[1]?=some lr ∧rv[1]?=some rr ∧ls[1]?=some true ∧rs[1]?=some true ∧
        lr.val≠leftStart ∧rr.val≠rightStart := by
  obtain ⟨out,conditions⟩:=actual_final_safe_leaves
  have lb:=conditions.1
  have rb:=conditions.2.1
  obtain ⟨lf,ls,lv,la,lw⟩:=leftChain.signed_path
  obtain ⟨rf,rs,rv,ra,rw⟩:=rightChain.signed_path
  obtain ⟨lr,lp,lat,las⟩:=out.left.signed_slot lw la
  obtain ⟨rr,rp,rat,ras⟩:=out.right.signed_slot rw ra
  rw [lb,List.length_singleton] at lat las
  rw [rb,List.length_singleton] at rat ras
  rw [out.leftTrue] at las
  rw [out.rightTrue] at ras
  have lpath : lr.val=[.arg,.fn]:=lp.trans out.leftReader
  have rpath : rr.val=[.arg,.arg]:=rp.trans out.rightReader
  refine ⟨out,lb,rb,lf,rf,ls,rs,lv,rv,la,ra,lw,rw,lr,rr,lpath,rpath,lat,rat,las,ras,?_,?_⟩
  · rw [lpath];decide
  · rw [rpath];decide
end NoninitialCuts

namespace BinderJump
open WrappedSuccessfulChains

/-- ANY supplied actual signed walk of this successful singleton, not a
newly chosen convenient walk, must read the real binder at ordinal zero. -/
theorem actual_zero_jump_given_walk {first : ProperPosition current}
    (walk : SignedProperWalk current first rootEdges signs vertices)
    (endpoint : Target current bodyFunction (some first)) :
    ∃reader : ProperPosition current,reader.val=[.fn] ∧reader.val≠bodyFunction ∧
      vertices[0]?=some reader ∧signs[0]?=some false := by
  obtain ⟨reader,path,atReader,atSign⟩:=variable_jump.signed_slot last_read walk endpoint
  exact ⟨reader,path,by rw [path];decide,atReader,atSign⟩

theorem actual_zero_jump_chain : ∃first signs vertices,
    Target current bodyFunction (some first) ∧SignedProperWalk current first rootEdges signs vertices ∧
    ∃reader : ProperPosition current,reader.val=[.fn] ∧reader.val≠bodyFunction ∧
      vertices[0]?=some reader ∧signs[0]?=some false := by
  obtain ⟨first,signs,vertices,endpoint,walk⟩:=PrerequisiteIncidencePathsChecks.BinderJump.variableChain.signed_path
  obtain ⟨reader,path,different,atReader,atSign⟩:=actual_zero_jump_given_walk walk endpoint
  exact ⟨first,signs,vertices,endpoint,walk,reader,path,different,atReader,atSign⟩

theorem actual_nonempty_prefix_with_zero_jump : ∃first signs vertices,
    Target current bodyApp (some first) ∧SignedProperWalk current first bodyEdges signs vertices ∧
    ∃reader : ProperPosition current,reader.val=[.fn] ∧reader.val≠bodyApp ∧
      vertices[1]?=some reader ∧signs[1]?=some false := by
  obtain ⟨first,signs,vertices,endpoint,walk⟩:=body_chain.signed_path
  obtain ⟨reader,path,atReader,atSign⟩:=body_prefix.signed_slot last_read walk endpoint
  exact ⟨first,signs,vertices,endpoint,walk,reader,path,by rw [path];decide,atReader,atSign⟩

theorem actual_one_canonical_history : INIT original ∧Closed original.erase ∧History [[.fn]] original current :=
  ⟨initial,sourceClosed,actualHistory⟩
end BinderJump

#print axioms PrerequisitePrefix.signed_slot
#print axioms PrerequisiteChain.signed_slot
#print axioms ActualUnsafeMarkerCut.signed_slot
#print axioms ActualUnsafeMarkerCut.signed_path_slot
#print axioms TwoCopies.actual_app_singleton_slot
#print axioms TwoCopies.actual_lambda_singleton_slot
#print axioms TwoCopies.actual_same_edge_two_legal_directions
#print axioms TwoCopies.actual_generated_context
#print axioms NoninitialCuts.actual_nonempty_before_slots
#print axioms SingleUnsafeCopyFunctionAppInputsChecks.actual_nonempty_history_context
#print axioms BinderJump.actual_zero_jump_given_walk
#print axioms BinderJump.actual_zero_jump_chain
#print axioms BinderJump.actual_nonempty_prefix_with_zero_jump
#print axioms BinderJump.actual_one_canonical_history
end Lamping.Checks.ActualPrerequisiteSignedSlotsChecks

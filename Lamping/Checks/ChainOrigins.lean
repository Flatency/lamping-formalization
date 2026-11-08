import Lamping.Lambda.EarliestReadingMarker
import Lamping.Lambda.DirectedReadingCreation
import Lamping.Lambda.UniformOldChainPreimages
import Lamping.Lambda.ResidualFunctionPreimages
import Lamping.Lambda.ResidualNodePreimages
import Lamping.Lambda.BetaChainExistenceReflection
import Lamping.Lambda.FirstNonoldReadingTrace
import Lamping.Lambda.UniformReadingCreationTrace
import Lamping.Lambda.UncreatedPrefixTransport
import Lamping.Lambda.PrerequisiteVertexRanks
import Lamping.Lambda.UncreatedChainTransport
import Lamping.Lambda.UncreatedPrerequisiteTransitions
import Lamping.Lambda.FirstCreatedPrefixTransport
import Lamping.Lambda.FirstCreatedIncoming
import Lamping.Lambda.CopyFunctionPrefixTransport
import Lamping.Lambda.RetainedBodyPrefixTransport
import Lamping.Lambda.PrerequisiteSubtreeEntry
import Lamping.Lambda.LambdaReadingPrefixTransport
import Lamping.Lambda.LambdaPrefixContainment
import Lamping.Lambda.CopyResultMembership
import Lamping.Lambda.FunctionResultPrefixTransport
import Lamping.Lambda.FirstNewReadingOrigins
import Lamping.Lambda.ResultRetainedPrefixTransport
import Lamping.Lambda.CopyChainPrefixTransport
import Lamping.Lambda.PrerequisiteRegionExclusion
import Lamping.Lambda.RetainedBinderPrefixOrigins
import Lamping.Lambda.CopiedBinderPrefixOrigins
import Lamping.Lambda.PrerequisitePrefixes
import Lamping.Lambda.BetaIncomingEdgeOrigins
import Lamping.Lambda.PrerequisiteChainOrigins
import Lamping.Lambda.LabelHistories
namespace Lamping.Checks.ChainOrigins
open Lambda Lambda.Labelled
private def a := Label.atom
private def body : LTerm := .app (a 2) (.var (a 3) 0) (.var (a 4) 0)
private def argument : LTerm := .lam (a 5) (.var (a 6) 0)
private def source : LTerm := .app (a 0) (.lam (a 1) body) argument
private def target : LTerm := LTerm.contract (a 0) (a 1) body argument
example : StepAt [] source target := .root _ _ _ _
example : PrerequisiteChain source [.fn,.body]
    [[.fn,.body,.fn],[.fn]] :=
  substituted_function_prerequisite (site := []) (parent := []) rfl rfl
example : PrerequisiteChain source [.arg] [[.arg],[.fn]] :=
  copied_lambda_prerequisite (site := []) rfl
example : target.subterm [.fn]=some
    (.lam (((a 3).concat (a 1).under).concat (a 5)) (.var (a 6) 0)) := rfl
-- The old opposite edge of this copied lambda is a real bound variable;
-- unlike e', it is not a lambda context edge and can be auxiliary.
example : AuxiliaryAt source [.fn,.body,.arg] := by
  constructor
  · rintro ⟨p,s,f,arg,h,look⟩
    have hlast := congrArg List.reverse h
    simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] at hlast
    cases hlast
  · rintro ⟨s,b,h⟩; cases h
private def contextual : LTerm := .lam (a 0) source
example : PrerequisiteChain contextual [.body,.arg]
    [[.body,.arg],[.body,.fn]] :=
  copied_lambda_prerequisite (site := [.body]) rfl
example : PrerequisiteChain
    (.app (a 0) (.lam (a 1) (.lam (a 2) (.var (a 3) 0))) argument)
    [.fn,.body] [[.fn,.body],[.fn]] :=
  result_lambda_prerequisite (site := []) rfl
#print axioms bound_leaf_prerequisite
#print axioms substituted_function_prerequisite
#print axioms copied_lambda_prerequisite
#print axioms result_lambda_prerequisite
end Lamping.Checks.ChainOrigins

namespace Lamping.Checks.ChainIncomingOrigins
open Lambda Lambda.Labelled
private def a := Label.atom
private def argument : LTerm := .lam (a 6) (.var (a 7) 1)
private def body : LTerm := .lam (a 2) (.app (a 3) (.var (a 4) 1) (.var (a 5) 0))
private def copied : LTerm := .lam (((a 4).concat (a 1).under).concat (a 6)) (.var (a 7) 2)
example : (LTerm.contract (a 0) (a 1) body argument).subterm [.body,.fn]=some copied := rfl
example : ∃ stamp,body.subterm [.body,.fn]=some (.var stamp 1) ∧
    copied.label=stamp.concat ((a 1).under.concat argument.label) := by
  simpa only [List.cons_ne_nil,if_false,binderDepth] using
    LTerm.contract_argument_incoming_label (body := body) (argument := argument)
      (beta := a 0) (alpha := a 1) (site := [.body,.fn]) (copy := copied) rfl rfl
private def overlapSource : LTerm := .app (a 0) (.lam (a 1) (.var (a 2) 0)) argument
private def overlapTarget : LTerm := LTerm.contract (a 0) (a 1) (.var (a 2) 0) argument
example : ∃ first,(first=[.fn,.body] ∨ first=[.arg]) ∧
    PrerequisiteChain overlapSource first [first,[.fn]] :=
  StepAt.result_lambda_old_chain (.root _ _ _ _) rfl rfl
example : overlapTarget.label=
    ((a 0).concat (a 1).over).concat ((a 2).concat ((a 1).under.concat (a 6))) := by
  simp only [overlapTarget,argument,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,
    LTerm.label,Label.concat_assoc]
-- Both newly added bars really occur at the same target incoming edge.
example : overlapTarget.label≠(a 6) := by decide
#print axioms LTerm.InsertedCopy.incoming_label
#print axioms LTerm.contract_argument_incoming_label
#print axioms LTerm.contract_root_lambda_origin
#print axioms StepAt.result_lambda_old_chain
end Lamping.Checks.ChainIncomingOrigins
namespace Lamping.Checks.ChainFunctionOrigins
open Lambda Lambda.Labelled
private def a := Label.atom
private def body : LTerm := .app (a 2) (.var (a 3) 0) (.var (a 4) 0)
private def argument : LTerm := .lam (a 5) (.var (a 6) 0)
private def redex : LTerm := .app (a 0) (.lam (a 1) body) argument
private def source : LTerm := .lam (a 0) (.app (a 0) redex argument)
example : PrerequisiteChain source [.body] [[.body,.fn],[.body,.fn,.fn]] :=
  result_function_old_chain (parent := [.body]) rfl
example : PrerequisiteChain source [.body,.fn,.fn,.body]
    [[.body,.fn,.fn,.body,.fn],[.body,.fn,.fn]] :=
  substituted_function_old_chain (site := [.body,.fn]) (parent := []) rfl rfl
#print axioms result_function_old_chain
#print axioms substituted_function_old_chain
end Lamping.Checks.ChainFunctionOrigins

namespace Lamping.Checks.ChainPrefixOrigins
open Lambda Lambda.Labelled
private def a := Label.atom
private def body : LTerm := .app (a 2) (.var (a 3) 0) (.var (a 4) 0)
private def argument : LTerm := .lam (a 5) (.var (a 6) 0)
private def source : LTerm := .app (a 0) (.lam (a 1) body) argument
private theorem actual_chain : PrerequisiteChain source [.fn,.body]
    [[.fn,.body,.fn],[.fn]] := substituted_function_old_chain (site := []) (parent := []) rfl rfl
-- A zero-edge segment can contain a real binder jump, so empty list alone
-- never identifies its starting and finishing occurrences.
example : PrerequisitePrefix source [.fn,.body,.arg] [] [.fn] :=
  .var rfl rfl rfl rfl .refl
example : ([Step.fn,Step.body,Step.arg] : Path)≠[.fn] := by decide
example : ∃ before after middle,
    [[.fn,.body,.fn],[.fn]]=before++([.fn]::after) ∧
    PrerequisitePrefix source [.fn,.body] before middle ∧
    PrerequisiteChain source middle ([.fn]::after) ∧PrerequisiteReads source middle [.fn] :=
  actual_chain.split_at_member (by simp)
example : PrerequisiteChain source [.fn,.body,.arg] [[.fn]] :=
  (PrerequisitePrefix.var (t := source) (leaf := [.fn,.body,.arg]) (parent := [.fn])
    (rest := [.arg]) rfl rfl rfl rfl .refl).close (.redex_lam (p := []) rfl)
#print axioms PrerequisitePrefix.close
#print axioms PrerequisitePrefix.append
#print axioms PrerequisiteChain.split_at_member
end Lamping.Checks.ChainPrefixOrigins

namespace Lamping.Checks.CopiedBinderPrefixOrigins
open Lambda Lambda.Labelled
private def a := Label.atom
private def argument : LTerm := .lam (a 5) (.lam (a 6)
  (.app (a 7) (.var (a 8) 1) (.var (a 9) 0)))
private def body : LTerm := .lam (a 2) (.var (a 3) 1)
private def source : LTerm := .lam (a 0) (.app (a 0) (.lam (a 1) body) argument)
private def target : LTerm := .lam (a 0) (LTerm.contract (a 0) (a 1) body argument)
private theorem actual_step : StepAt [.body] source target := .body (.root _ _ _ _)
example : ∃ s b v,source.subterm [.body,.arg]=some (.lam s b) ∧
    source.subterm [.body,.arg,.body,.body,.fn]=some (.var v 1) ∧
    PrerequisitePrefix source [.body,.arg,.body,.body,.fn] [] [.body,.arg] :=
  actual_step.copied_internal_binder_prefix (site := [.body]) (copySite := [.body])
    (relative := []) (descendant := [.body,.fn]) rfl rfl rfl rfl
example : ∃ s b v,source.subterm [.body,.arg,.body]=some (.lam s b) ∧
    source.subterm [.body,.arg,.body,.body,.arg]=some (.var v 0) ∧
    PrerequisitePrefix source [.body,.arg,.body,.body,.arg] [] [.body,.arg,.body] :=
  actual_step.copied_internal_binder_prefix (site := [.body]) (copySite := [.body])
    (relative := [.body]) (descendant := [.arg]) rfl rfl rfl rfl
-- Same actual copied lambda tree, different lexical binders. In particular
-- the internal lambda does not capture the leaf bound by the outer lambda.
example : target.subterm [.body,.body,.body,.body,.fn]=some (.var (a 8) 1) := rfl
example : target.subterm [.body,.body,.body,.body,.fn]≠some (.var (a 8) 0) := by decide
#print axioms StepAt.copied_internal_binder_prefix
end Lamping.Checks.CopiedBinderPrefixOrigins
namespace Lamping.Checks.CopiedExternalBinderPrefixOrigins
open Lambda Lambda.Labelled
private def a := Label.atom
-- The argument's free variable is bound by the actual outer source lambda.
-- Copying it under a new body lambda shifts 0→1 and cannot capture it.
private def body : LTerm := .lam (a 2) (.var (a 3) 1)
private def argument : LTerm := .var (a 4) 0
private def source : LTerm := .lam (a 0) (.app (a 0) (.lam (a 1) body) argument)
private def target : LTerm := .lam (a 0) (LTerm.contract (a 0) (a 1) body argument)
private theorem actual_step : StepAt [.body] source target := .body (.root _ _ _ _)
example : ∃ oldParent oldStamp oldBody,
    source.subterm oldParent=some (.lam oldStamp oldBody) ∧
    PrerequisitePrefix source [.body,.arg] [] oldParent ∧
    ((∃ inside,([] : Path)=[.body,.body]++inside ∧oldParent=[.body,.arg]++inside) ∨(∃ outside,([.body] : Path)=[]++(.body::outside) ∧oldParent=[])) :=
  actual_step.copied_binder_old_prefix (site := [.body]) (copySite := [.body])
    (relative := []) (parent := []) (rest := [.body]) rfl rfl rfl rfl rfl
example : target.subterm [.body,.body]=some (.var
    (((a 3).concat (a 1).under).concat (a 4)) 1) := rfl
example : target.subterm [.body,.body]≠some (.var
    (((a 3).concat (a 1).under).concat (a 4)) 0) := by decide
example : ∃ outside,([.body] : Path)=[]++(.body::outside) :=
  (copied_variable_binder_scope (argument := argument.erase) (site := [.body])
    (copySite := [.body]) (relative := []) (parent := []) (rest := [.body])
    rfl rfl).resolve_left (by rintro ⟨inside,equal⟩; cases equal)
#print axioms shifted_variable_index_gap
#print axioms copied_variable_binder_scope
#print axioms StepAt.copied_binder_old_prefix
end Lamping.Checks.CopiedExternalBinderPrefixOrigins


namespace Lamping.Checks.RetainedBinderPrefixOrigins
open Lambda Lambda.Labelled
private def a := Label.atom
private def argument : LTerm := .lam (a 5) (.var (a 6) 0)
private def insideBody : LTerm := .lam (a 2) (.var (a 3) 0)
private def insideSource : LTerm := .lam (a 0) (.app (a 0) (.lam (a 1) insideBody) argument)
private def insideTarget : LTerm := .lam (a 0) (LTerm.contract (a 0) (a 1) insideBody argument)
private theorem internal_step : StepAt [.body] insideSource insideTarget := .body (.root _ _ _ _)
example : ∃ oldParent origin oldBody,
    insideSource.subterm oldParent=some (.lam origin oldBody) ∧
    PrerequisitePrefix insideSource [.body,.fn,.body,.body] [] oldParent ∧
    ((∃ inside,([.body] : Path)=[.body]++inside ∧ oldParent=[.body,.fn,.body]++inside) ∨(∃ outside,([.body] : Path)=[.body]++(.body::outside) ∧oldParent=[.body])) :=
  internal_step.retained_binder_old_prefix (site := [.body]) (relative := [.body])
    (parent := [.body]) (rest := []) rfl rfl (by decide) rfl rfl rfl
private def outsideBody : LTerm := .lam (a 2) (.var (a 3) 2)
private def outsideSource : LTerm := .lam (a 0) (.app (a 0) (.lam (a 1) outsideBody) argument)
private def outsideTarget : LTerm := .lam (a 0) (LTerm.contract (a 0) (a 1) outsideBody argument)
private theorem external_step : StepAt [.body] outsideSource outsideTarget := .body (.root _ _ _ _)
example : ∃ oldParent origin oldBody,
    outsideSource.subterm oldParent=some (.lam origin oldBody) ∧
    PrerequisitePrefix outsideSource [.body,.fn,.body,.body] [] oldParent ∧
    ((∃ inside,([] : Path)=[.body]++inside ∧ oldParent=[.body,.fn,.body]++inside) ∨(∃ outside,([.body] : Path)=[]++(.body::outside) ∧oldParent=[])) :=
  external_step.retained_binder_old_prefix (site := [.body]) (relative := [.body])
    (parent := []) (rest := [.body]) rfl rfl (by decide) rfl rfl rfl
example : outsideTarget.subterm [.body,.body]=some (.var (a 3) 1) := rfl
example : outsideTarget.subterm [.body,.body]≠some (.var (a 3) 0) := by decide
#print axioms liftSingle_retained_index
#print axioms StepAt.retained_binder_old_prefix
end Lamping.Checks.RetainedBinderPrefixOrigins


namespace Lamping.Checks.PrerequisiteRegionExclusion
open Lambda Lambda.Labelled
private def a := Label.atom
private def inner : LTerm := .app (a 7) (.lam (a 7) (.var (a 7) 0)) (.lam (a 7) (.var (a 7) 0))
private def source : LTerm := .app (a 7) (.lam (a 7) (.var (a 7) 0)) (.lam (a 7) inner)
private theorem actual_chain : PrerequisiteChain source [.arg] [[.arg],[.fn]] := by
  exact .lam (parent := []) (step := .arg) rfl (by decide) (.redex_app rfl)
example : ([.arg,.body,.fn] : Path)∉[[.arg],[.fn]] :=
  actual_chain.excludes_lambda_body (descendant := [.fn]) rfl
#print axioms PrerequisiteChain.excludes_lambda_body
end Lamping.Checks.PrerequisiteRegionExclusion

namespace Lamping.Checks.CopyChainPrefixTransport
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 9) (.var (a 9) 0)
private def argument : LTerm := .lam (a 5) (.app (a 6) (.var (a 7) 0) (.var (a 8) 0))
private def body : LTerm := .lam (a 2) (.var (a 3) 1)
private def source : LTerm := .app (a 0) (.app (a 0) (.lam (a 1) body) argument) identity
private def target : LTerm := .app (a 0) (LTerm.contract (a 0) (a 1) body argument) identity
private def copy : LTerm := .lam (((a 3).concat (a 1).under).concat (a 5))
    (.app (a 6) (.var (a 7) 0) (.var (a 8) 0))
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_chain : PrerequisiteChain target [.fn,.body,.body]
    [[.fn,.body,.body,.fn],[.fn,.body],[.fn]] := by
  apply PrerequisiteChain.app (p := [.fn,.body,.body]) rfl
  · intro l b impossible; cases impossible
  · exact .var (parent := [.fn,.body]) (rest := [.fn]) rfl rfl rfl rfl
      (.lam (parent := [.fn]) (step := .body) rfl (by decide) (.redex_lam (p := []) rfl))
example : ∃ before after,
    [[.fn,.body,.body,.fn],[.fn,.body],[.fn]]=before++([.fn,.body]::after) ∧
    PrerequisitePrefix target [.fn,.body,.body] before [.fn,.body] ∧
    (∀ edge∈before,∃ inside,inside≠[] ∧edge=([.fn,.body] : Path)++inside) ∧
    PrerequisiteChain source [.fn,.arg,.body]
      (before.map (fun edge=>([.fn,.arg] : Path)++edge.drop 2)++[[.fn,.arg],[.fn,.fn]]) ∧
    before.map target.labelAt=(before.map (fun edge=>([.fn,.arg] : Path)++edge.drop 2)).map source.labelAt := by
  simpa only [List.cons_append,List.nil_append,List.append_nil,List.length_cons,List.length_nil] using
    actual_step.copy_chain_prefix_reflect_labelled (copySite := [.body]) (relative := [.body])
      (copy := copy) rfl rfl rfl actual_chain rfl (by simp)

private def overlapSource : LTerm := .app (a 0)
  (.app (a 0) (.lam (a 1) (.var (a 2) 0)) argument) identity
private def overlapTarget : LTerm := .app (a 0)
  (LTerm.contract (a 0) (a 1) (.var (a 2) 0) argument) identity
private theorem overlap_step : StepAt [.fn] overlapSource overlapTarget := .fn (.root _ _ _ _)
private theorem overlap_chain : PrerequisiteChain overlapTarget [.fn,.body]
    [[.fn,.body,.fn],[.fn]] := by
  apply PrerequisiteChain.app (p := [.fn,.body]) rfl
  · intro l b impossible; cases impossible
  · exact .var (parent := [.fn]) (rest := [.fn]) rfl rfl rfl rfl (.redex_lam (p := []) rfl)
example : ∃ before after,
    [[.fn,.body,.fn],[.fn]]=before++([.fn]::after) ∧
    PrerequisitePrefix overlapTarget [.fn,.body] before [.fn] ∧
    (∀ edge∈before,∃ inside,inside≠[] ∧edge=([.fn] : Path)++inside) ∧
    PrerequisiteChain overlapSource [.fn,.arg,.body]
      (before.map (fun edge=>([.fn,.arg] : Path)++edge.drop 1)++[[.fn,.arg],[.fn,.fn]]) := by
  simpa only [List.cons_append,List.nil_append,List.append_nil,List.length_cons,List.length_nil] using
    overlap_step.copy_chain_prefix_reflect (copySite := []) (relative := [.body])
      (copy := LTerm.contract (a 0) (a 1) (.var (a 2) 0) argument)
      rfl rfl rfl overlap_chain rfl (by simp)
#print axioms StepAt.copy_chain_prefix_reflect
#print axioms StepAt.copy_chain_prefix_reflect_labelled
end Lamping.Checks.CopyChainPrefixTransport
namespace Lamping.Checks.CopyLambdaPrefixTransport
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 9) (.var (a 9) 0)
private def argument : LTerm := .lam (a 5) (.lam (a 6) (.var (a 7) 1))
private def body : LTerm := .lam (a 2) (.var (a 3) 1)
private def source : LTerm := .app (a 0) (.app (a 0) (.lam (a 1) body) argument) identity
private def target : LTerm := .app (a 0) (LTerm.contract (a 0) (a 1) body argument) identity
private def copy : LTerm := .lam (((a 3).concat (a 1).under).concat (a 5)) (.lam (a 6) (.var (a 7) 1))
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_chain : PrerequisiteChain target [.fn,.body,.body]
    [[.fn,.body,.body],[.fn,.body],[.fn]] := by
  exact .lam (parent := [.fn,.body]) (step := .body) rfl (by decide)
    (.lam (parent := [.fn]) (step := .body) rfl (by decide) (.redex_lam (p := []) rfl))
example : ∃ before after,
    [[.fn,.body,.body],[.fn,.body],[.fn]]=before++([.fn,.body]::after) ∧
    PrerequisitePrefix target [.fn,.body,.body] before [.fn,.body] ∧
    (∀ edge∈before,∃ inside,inside≠[] ∧edge=([.fn,.body] : Path)++inside) ∧
    PrerequisiteChain source [.fn,.arg,.body]
      (before.map (fun edge=>([.fn,.arg] : Path)++edge.drop 2)++[[.fn,.arg],[.fn,.fn]]) := by
  simpa only [List.cons_append,List.nil_append,List.append_nil,List.length_cons,List.length_nil] using
    actual_step.copy_chain_prefix_reflect (copySite := [.body]) (relative := [.body])
      (copy := copy) rfl rfl rfl actual_chain rfl (by simp)
end Lamping.Checks.CopyLambdaPrefixTransport


namespace Lamping.Checks.ResultRetainedPrefixTransport
open Lambda Lambda.Labelled
private def a := Label.atom
private def argument : LTerm := .lam (a 5) (.var (a 6) 0)
private def body : LTerm := .lam (a 2) (.app (a 3) (.var (a 4) 0) (.var (a 7) 1))
private def source : LTerm := .app (a 0) (.app (a 0) (.lam (a 1) body) argument) argument
private def target : LTerm := .app (a 0) (LTerm.contract (a 0) (a 1) body argument) argument
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_chain : PrerequisiteChain target [.fn,.body]
    [[.fn,.body,.fn],[.fn]] := by
  apply PrerequisiteChain.app (p := [.fn,.body]) rfl
  · intro l b impossible; cases impossible
  · exact .var (parent := [.fn]) (rest := [.fn]) rfl rfl rfl rfl (.redex_lam (p := []) rfl)
-- A genuine copy is created in the unread argument sibling; the first-new
-- read is the result incoming edge, not an empty-development special case.
example : ArgumentOccurrence body.erase [.body,.arg] := rfl
private theorem copies_not_read (q : Path) (occurs : ArgumentOccurrence body.erase q) :
    ([.fn] : Path)++q∉[[.fn,.body,.fn],[.fn]] := by
  intro present
  simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with equal | equal
  · have qEq := (List.cons.inj equal).2
    subst q
    simp only [ArgumentOccurrence,body,LTerm.erase,subtermAt,binderDepth] at occurs
    cases occurs
  · have qEq := (List.cons.inj equal).2
    subst q
    cases occurs
example : ∃ before after,
    [[.fn,.body,.fn],[.fn]]=before++([.fn]::after) ∧
    PrerequisitePrefix target [.fn,.body] before [.fn] ∧
    PrerequisiteChain source [.fn,.fn,.body,.body]
      (before.map (fun edge=>([.fn,.fn,.body] : Path)++edge.drop 1)++[[.fn,.fn,.body],[.fn,.fn]]) ∧
    before.map target.labelAt=
      (before.map (fun edge=>([.fn,.fn,.body] : Path)++edge.drop 1)).map source.labelAt := by
  apply actual_step.first_result_chain_prefix_reflect_labelled
    (body := body) (relative := [.body])
    rfl ⟨a 2,_,rfl⟩ actual_chain rfl (by simp)
  intro before after equal q occurs present
  apply copies_not_read q occurs
  rw [equal]
  exact List.mem_append_left _ present
#print axioms PrerequisiteChain.split_at_incoming
#print axioms StepAt.result_retained_chain_prefix_reflect
end Lamping.Checks.ResultRetainedPrefixTransport

namespace Lamping.Checks.ResultLambdaPrefixTransport
open Lambda Lambda.Labelled
private def a := Label.atom
private def argument : LTerm := .lam (a 5) (.var (a 6) 0)
private def body : LTerm := .lam (a 2) (.lam (a 3) (.var (a 4) 2))
private def source : LTerm := .app (a 0) (.app (a 0) (.lam (a 1) body) argument) argument
private def target : LTerm := .app (a 0) (LTerm.contract (a 0) (a 1) body argument) argument
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_chain : PrerequisiteChain target [.fn,.body] [[.fn,.body],[.fn]] :=
  .lam (parent := [.fn]) (step := .body) rfl (by decide) (.redex_lam (p := []) rfl)
example : ArgumentOccurrence body.erase [.body,.body] := rfl
private theorem copies_not_read (q : Path) (occurs : ArgumentOccurrence body.erase q) :
    ([.fn] : Path)++q∉[[.fn,.body],[.fn]] := by
  intro present
  simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with equal | equal
  · have qEq := (List.cons.inj equal).2
    subst q
    cases occurs
  · have qEq := (List.cons.inj equal).2
    subst q
    cases occurs
example : ∃ before after,
    [[.fn,.body],[.fn]]=before++([.fn]::after) ∧
    PrerequisitePrefix target [.fn,.body] before [.fn] ∧
    PrerequisiteChain source [.fn,.fn,.body,.body]
      (before.map (fun edge=>([.fn,.fn,.body] : Path)++edge.drop 1)++[[.fn,.fn,.body],[.fn,.fn]]) ∧
    before.map target.labelAt=
      (before.map (fun edge=>([.fn,.fn,.body] : Path)++edge.drop 1)).map source.labelAt := by
  apply actual_step.first_result_chain_prefix_reflect_labelled
    (body := body) (relative := [.body])
    rfl ⟨a 2,_,rfl⟩ actual_chain rfl (by simp)
  intro before after equal q occurs present
  apply copies_not_read q occurs
  rw [equal]
  exact List.mem_append_left _ present
end Lamping.Checks.ResultLambdaPrefixTransport

#print axioms Lamping.Lambda.Labelled.StepAt.result_retained_chain_prefix_reflect_labelled

namespace Lamping.Checks.FirstNewReadingOrigins
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 6) (.var (a 7) 0)
private def body : LTerm := .var (a 3) 0
private def argument : LTerm := .lam (a 4) (.var (a 5) 0)
private def source : LTerm := .app (a 0) (.app (a 1) (.lam (a 2) body) argument) identity
private def target : LTerm := .app (a 0) (LTerm.contract (a 1) (a 2) body argument) identity
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem forward_chain : PrerequisiteChain target [] [[.fn]] := .redex_app rfl
private theorem backward_chain : PrerequisiteChain target [.fn] [[.fn]] := .redex_lam (p := []) rfl
private theorem empty_at_proper (segment : PrerequisitePrefix t p [] finish)
    (nonvar : ∀ stamp index,t.subterm p≠some (.var stamp index)) : p=finish := by
  cases segment with
  | refl => rfl
  | var lookup => exact False.elim (nonvar _ _ lookup)
-- One physical syntax edge has two real reading directions. Its overlapping
-- RESULT/COPY bars choose different old first edges, without label guessing.
example : ∃ before after middle oldStart last,
    [[.fn]]=before++([.fn]::after) ∧PrerequisitePrefix target [] before middle ∧
    BetaIncomingReadingOrigin body argument [.fn] [.fn] middle oldStart [.fn] last ∧
    PrerequisiteChain source oldStart [[.fn],[.fn,.fn]] ∧
    ∃ oldLast,source.subterm last=some oldLast := by
  obtain ⟨before,after,middle,oldStart,first,last,equal,segment,remainder,origin,oldChain,oldLast⟩ :=
    actual_step.created_chain_reading_origins (body := body) (argument := argument) rfl forward_chain
      (edge := [.fn]) (by simp) (Or.inl rfl)
  have noBefore : before=[] := by
    have sizes := congrArg List.length equal
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    exact List.eq_nil_of_length_eq_zero (by omega)
  have middleEq : middle=[] := by
    rw [noBefore] at segment
    exact (empty_at_proper segment (by intro s n bad; cases bad)).symm
  subst middle
  have firstEq : first=([.fn] : Path) := by
    cases origin with
    | resultFunction => rfl
    | resultLambda result reading => cases reading
    | copyFunction occurs copy =>
      have sizes := congrArg List.length copy
      simp only [List.length_append,List.length_cons,List.length_nil] at sizes
      omega
    | copyLambda occurs copy reading => cases reading
  subst first
  exact ⟨before,after,[],oldStart,last,equal,segment,origin,oldChain,oldLast⟩

example : ∃ before after middle oldStart last,
    [[.fn]]=before++([.fn]::after) ∧PrerequisitePrefix target [.fn] before middle ∧
    BetaIncomingReadingOrigin body argument [.fn] [.fn] middle oldStart [.fn,.arg] last ∧
    PrerequisiteChain source oldStart [[.fn,.arg],[.fn,.fn]] ∧
    ∃ oldLast,source.subterm last=some oldLast := by
  obtain ⟨before,after,middle,oldStart,first,last,equal,segment,remainder,origin,oldChain,oldLast⟩ :=
    actual_step.created_chain_reading_origins (body := body) (argument := argument) rfl backward_chain
      (edge := [.fn]) (by simp) (Or.inl rfl)
  have noBefore : before=[] := by
    have sizes := congrArg List.length equal
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    exact List.eq_nil_of_length_eq_zero (by omega)
  have middleEq : middle=([.fn] : Path) := by
    rw [noBefore] at segment
    exact (empty_at_proper segment (by intro s n bad; cases bad)).symm
  subst middle
  have firstEq : first=([.fn,.arg] : Path) := by
    cases origin with
    | resultFunction result function => cases function
    | resultLambda result reading oldLambda => cases oldLambda
    | copyFunction occurs copy =>
      have sizes := congrArg List.length copy
      simp only [List.length_append,List.length_cons,List.length_nil] at sizes
      omega
    | copyLambda => rfl
  subst first
  exact ⟨before,after,[.fn],oldStart,last,equal,segment,origin,oldChain,oldLast⟩
example : AuxiliaryAt source [.fn,.fn,.body] := by
  rw [auxiliaryAt_iff_not_eligible]
  rintro (⟨parent,stamp,fn,arg,equal,lookup⟩ | ⟨stamp,inner,lookup⟩)
  · have reversed := congrArg List.reverse equal
    simp only [List.reverse_cons,List.reverse_nil,List.reverse_append,List.cons_append,List.nil_append] at reversed
    cases reversed
  · cases lookup
example : (LTerm.contract (a 1) (a 2) body argument).label=
    ((a 1).concat (a 2).over).concat ((a 3).concat ((a 2).under.concat (a 4))) := rfl
#print axioms StepAt.created_chain_reading_origins
#print axioms BetaIncomingReadingOrigin.old_prerequisite
end Lamping.Checks.FirstNewReadingOrigins
namespace Lamping.Checks.FirstNewCopyFunction
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 6) (.var (a 7) 0)
private def body : LTerm := .app (a 3) (.var (a 4) 0) identity
private def source : LTerm := .app (a 0) (.app (a 1) (.lam (a 2) body) identity) identity
private def target : LTerm := .app (a 0) (LTerm.contract (a 1) (a 2) body identity) identity
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_chain : PrerequisiteChain target [.fn] [[.fn,.fn]] := .redex_app rfl
example : ∃ before after middle oldStart first last,
    [[.fn,.fn]]=before++([.fn,.fn]::after) ∧PrerequisitePrefix target [.fn] before middle ∧
    PrerequisiteChain target middle ([.fn,.fn]::after) ∧
    BetaIncomingReadingOrigin body identity [.fn] [.fn,.fn] middle oldStart first last ∧
    PrerequisiteChain source oldStart [first,[.fn,.fn]] ∧
    ∃ oldLast,source.subterm last=some oldLast := by
  exact actual_step.created_chain_reading_origins rfl actual_chain (by simp)
    (Or.inr ⟨[.fn],rfl,rfl⟩)
end Lamping.Checks.FirstNewCopyFunction

namespace Lamping.Checks.FirstNewResultLambda
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 6) (.var (a 7) 0)
private def body : LTerm := .lam (a 3) (.var (a 4) 0)
private def source : LTerm := .app (a 0) (.app (a 1) (.lam (a 2) body) identity) identity
private def target : LTerm := .app (a 0) (LTerm.contract (a 1) (a 2) body identity) identity
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_chain : PrerequisiteChain target [.fn] [[.fn]] := .redex_lam (p := []) rfl
example : ∃ before after middle oldStart first last,
    [[.fn]]=before++([.fn]::after) ∧PrerequisitePrefix target [.fn] before middle ∧
    PrerequisiteChain target middle ([.fn]::after) ∧
    BetaIncomingReadingOrigin body identity [.fn] [.fn] middle oldStart first last ∧
    PrerequisiteChain source oldStart [first,[.fn,.fn]] ∧
    ∃ oldLast,source.subterm last=some oldLast := by
  exact actual_step.created_chain_reading_origins rfl actual_chain (by simp) (Or.inl rfl)
end Lamping.Checks.FirstNewResultLambda

namespace Lamping.Checks.FunctionResultPrefixTransport
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 6) (.var (a 7) 0)
private def argument : LTerm := .lam (a 8) (.app (a 9) (.var (a 10) 0) identity)
private def body : LTerm := .lam (a 3) (.var (a 4) 0)
private def source : LTerm := .app (a 0) (.app (a 1) (.lam (a 2) body) identity) argument
private def target : LTerm := .app (a 0) (LTerm.contract (a 1) (a 2) body identity) argument
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_segment : PrerequisitePrefix target [.arg,.body]
    [[.arg,.body,.fn],[.arg]] [] := by
  apply PrerequisitePrefix.app (p := [.arg,.body]) rfl
  · intro l b impossible; cases impossible
  · exact .var (parent := [.arg]) (rest := [.fn]) rfl rfl rfl rfl
      (.lam (parent := []) (step := .arg) rfl (by decide) .refl)
private theorem actual_chain : PrerequisiteChain target [.arg,.body]
    [[.arg,.body,.fn],[.arg],[.fn]] := actual_segment.close (.redex_app rfl)
example : BetaIncomingReadingOrigin body identity [.fn] [.fn] [] [] [.fn] [.fn,.fn,.body] ∧
    PrerequisiteChain source [.arg,.body]
    [[.arg,.body,.fn],[.arg],[.fn],[.fn,.fn]] ∧
    ([[.arg,.body,.fn],[.arg]] : List Path).map target.labelAt=
      ([[.arg,.body,.fn],[.arg]] : List Path).map source.labelAt :=
  ⟨.resultFunction rfl rfl,
    actual_step.function_result_prefix_old_chain (parent := []) rfl rfl rfl actual_segment⟩

-- Read the actual branch selected internally from the supplied chain.
example : ∃ before after middle oldStart first last,
    [[.arg,.body,.fn],[.arg],[.fn]]=before++([.fn]::after) ∧
    BetaIncomingReadingOrigin body identity [.fn] [.fn] middle oldStart first last ∧
    (middle=[] →PrerequisiteChain source [.arg,.body] (before++[[.fn],[.fn,.fn]]) ∧
      before.map target.labelAt=before.map source.labelAt) := by
  obtain ⟨before,after,middle,oldStart,first,last,equal,segment,remainder,origin,oldChain,oldLast⟩ :=
    actual_step.created_chain_reading_origins rfl actual_chain (by simp) (Or.inl rfl)
  refine ⟨before,after,middle,oldStart,first,last,equal,origin,?_⟩
  intro middleEq
  subst middle
  exact actual_step.function_result_prefix_old_chain (parent := []) rfl rfl rfl segment

-- The source result edge is genuinely not a redex edge: its child is an
-- application. The target result reading is a new redex FUNCTION edge.
example : ¬PrerequisiteRedexEdge source [.fn] := by
  rintro ⟨parent,appStamp,lamStamp,inner,arg,equal,lookup⟩
  have rev := congrArg List.reverse equal
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] at rev
  have parentEmpty : parent=[] := by
    have zero := (List.cons.inj rev).2
    have len := congrArg List.length zero
    simp only [List.length_reverse,List.length_nil] at len
    exact List.eq_nil_of_length_eq_zero len.symm
  subst parent
  cases lookup
#print axioms StepAt.function_result_prefix_reflect
#print axioms StepAt.function_result_prefix_old_chain
end Lamping.Checks.FunctionResultPrefixTransport

namespace Lamping.Checks.CopyResultMembership
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 9) (.var (a 9) 0)
private def argument : LTerm := .lam (a 5) (.app (a 6) (.var (a 7) 0) (.var (a 8) 0))
private def body : LTerm := .lam (a 2) (.var (a 3) 1)
private def source : LTerm := .app (a 0) (.app (a 0) (.lam (a 1) body) argument) identity
private def target : LTerm := .app (a 0) (LTerm.contract (a 0) (a 1) body argument) identity
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_chain : PrerequisiteChain target [.fn,.body,.body]
    [[.fn,.body,.body,.fn],[.fn,.body],[.fn]] := by
  apply PrerequisiteChain.app (p := [.fn,.body,.body]) rfl
  · intro l b impossible; cases impossible
  · exact .var (parent := [.fn,.body]) (rest := [.fn]) rfl rfl rfl rfl
      (.lam (parent := [.fn]) (step := .body) rfl (by decide) (.redex_lam (p := []) rfl))
example : ([.fn,.body] : Path)∈[[.fn,.body,.body,.fn],[.fn,.body],[.fn]] :=
  actual_step.copy_root_on_chain_to_result (copySite := [.body]) (relative := [.body])
    rfl rfl actual_chain rfl (by simp)
example : ∃ before after,
    [[.fn,.body,.body,.fn],[.fn,.body],[.fn]]=before++([.fn]::after) ∧
    PrerequisitePrefix target [.fn,.body,.body] before [.fn] ∧([.fn,.body] : Path)∈before :=
  actual_step.copy_start_forces_before_result (copySite := [.body]) (relative := [.body])
    rfl ⟨a 2,_,rfl⟩ rfl actual_chain rfl (by simp)
end Lamping.Checks.CopyResultMembership

namespace Lamping.Checks.CopyResultExternalJump
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 10) (.var (a 11) 0)
private def body : LTerm := .lam (a 2) (.var (a 3) 1)
private def source : LTerm := .app (a 0) identity
    (.lam (a 9) (.app (a 4) (.lam (a 1) body) (.var (a 5) 0)))
private def target : LTerm := .app (a 0) identity
    (.lam (a 9) (LTerm.contract (a 4) (a 1) body (.var (a 5) 0)))
private theorem actual_step : StepAt [.arg,.body] source target := .arg (.body (.root _ _ _ _))
private theorem actual_chain : PrerequisiteChain target [.arg,.body,.body] [[.arg],[.fn]] := by
  exact .var (parent := [.arg]) (rest := [.body]) rfl rfl rfl rfl
    (.lam (parent := []) (step := .arg) rfl (by decide) (.redex_app rfl))
private theorem copied_root_aux : AuxiliaryAt target [.arg,.body,.body] := by
  rw [auxiliaryAt_iff_not_eligible]
  rintro (⟨parent,stamp,fn,arg,equal,lookup⟩ | ⟨stamp,inner,lookup⟩)
  · have reversed := congrArg List.reverse equal
    simp only [List.reverse_cons,List.reverse_nil,List.reverse_append,List.cons_append,List.nil_append] at reversed
    cases reversed
  · cases lookup
-- A genuine outside-binder jump exists, but it cannot bypass the copy root
-- and then read the RESULT site. The proof uses the automatic membership top.
example : ([.arg,.body] : Path)∉[[.arg],[.fn]] := by
  intro resultMember
  have copyMember := actual_step.copy_root_on_chain_to_result (copySite := [.body]) (relative := [])
    rfl rfl actual_chain rfl resultMember
  exact actual_chain.not_auxiliary copyMember copied_root_aux
example : target.subterm [.arg,.body,.body]=some (.var ((a 3).concat ((a 1).under.concat (a 5))) 1) := rfl
example : target.subterm [.arg,.body,.body]≠some (.var ((a 3).concat ((a 1).under.concat (a 5))) 0) := by decide
#print axioms StepAt.copy_root_on_chain_to_result
#print axioms StepAt.copy_start_forces_before_result
#print axioms StepAt.first_result_retained_start
#print axioms StepAt.first_result_chain_prefix_reflect_labelled
end Lamping.Checks.CopyResultExternalJump

namespace Lamping.Checks.LambdaPrefixContainment
open Lambda Lambda.Labelled
-- Repeated stamps do not identify the containing lexical occurrence.
private def source : LTerm := .lam (Label.atom 7)
  (.app (Label.atom 7) (.var (Label.atom 7) 0) (.lam (Label.atom 7) (.var (Label.atom 7) 0)))
private theorem actual_prefix : PrerequisitePrefix source [.body] [[.body,.fn]] [] :=
  .app rfl (by intro l b impossible; cases impossible)
    (.var (parent := []) (rest := [.fn]) rfl rfl rfl rfl .refl)
example : ∃ relative,([.body] : Path)=[]++relative :=
  actual_prefix.lambda_finish_contains_start rfl
private theorem zero_edge_jump : PrerequisitePrefix source [.body,.fn] [] [] :=
  .var (parent := []) (rest := [.fn]) rfl rfl rfl rfl .refl
example : ∃ relative,([.body,.fn] : Path)=[]++relative :=
  zero_edge_jump.lambda_finish_contains_start rfl
example : ([.body,.fn] : Path)≠[] := by decide
-- A real redex's FUNCTION lambda cannot be entered from its application by
-- a nonterminal dependency prefix; the chase stops at the application.
private def identity : LTerm := .lam (Label.atom 0) (.var (Label.atom 0) 0)
private def redex : LTerm := .app (Label.atom 0) identity identity
example : ¬PrerequisitePrefix redex [] before [.fn] := by
  intro alleged
  obtain ⟨relative,equal⟩ := alleged.lambda_finish_contains_start rfl
  have sizes := congrArg List.length equal
  simp only [List.length_nil,List.length_append,List.length_cons] at sizes
  omega
#print axioms PrerequisitePrefix.lambda_finish_contains_start
end Lamping.Checks.LambdaPrefixContainment

namespace Lamping.Checks.ResultLambdaReading
open Lambda Lambda.Labelled
private def a := Label.atom
private def argument : LTerm := .lam (a 5) (.var (a 6) 0)
private def body : LTerm := .lam (a 2) (.app (a 3) (.var (a 4) 0) (.var (a 7) 1))
private def source : LTerm := .app (a 0) (.app (a 0) (.lam (a 1) body) argument) argument
private def target : LTerm := .app (a 0) (LTerm.contract (a 0) (a 1) body argument) argument
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_reading : PrerequisitePrefix target [.fn,.body] [[.fn,.body,.fn]] [.fn] :=
  .app rfl (by intro l b impossible; cases impossible)
    (.var (parent := [.fn]) (rest := [.fn]) rfl rfl rfl rfl .refl)
private theorem actual_chain : PrerequisiteChain target [.fn,.body] [[.fn,.body,.fn],[.fn]] :=
  actual_reading.close (.redex_lam (p := []) rfl)
private theorem copies_not_read (q : Path) (occurs : ArgumentOccurrence body.erase q) :
    ([.fn] : Path)++q∉[[.fn,.body,.fn],[.fn]] := by
  intro present
  simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with equal | equal
  · have qEq := (List.cons.inj equal).2
    subst q
    cases occurs
  · have qEq := (List.cons.inj equal).2
    subst q
    cases occurs
example : ∃ before after,
    [[.fn,.body,.fn],[.fn]]=before++([.fn]::after) ∧
    PrerequisitePrefix target [.fn,.body] before [.fn] ∧
    PrerequisiteChain source [.fn,.fn,.body,.body]
      (before.map (fun edge=>([.fn,.fn,.body] : Path)++edge.drop 1)++[[.fn,.fn,.body],[.fn,.fn]]) ∧
    before.map target.labelAt=(before.map (fun edge=>([.fn,.fn,.body] : Path)++edge.drop 1)).map source.labelAt := by
  obtain ⟨relative,oldRoot,before,after,startEq,origin,equal,segment,oldChain,labels⟩ :=
    actual_step.result_lambda_reading_prefix_reflect (body := body) (argument := argument)
      rfl rfl actual_chain (by simp) actual_reading (by
        intro before after equal q occurs present
        apply copies_not_read q occurs
        rw [equal]
        exact List.mem_append_left _ present)
  have rootEq : oldRoot=([.fn,.fn,.body] : Path) := by
    rcases origin with ⟨eq,_⟩ | ⟨_,stamp,as,ab,bodyEq,_⟩
    · exact eq
    · cases bodyEq
  have relativeEq : relative=([.body] : Path) := (List.cons.inj startEq).2.symm
  subst oldRoot
  subst relative
  exact ⟨before,after,equal,segment,oldChain,labels⟩
-- This is a genuine unread copy in the same reduction, not a copy-free case.
example : ArgumentOccurrence body.erase [.body,.arg] := rfl
end Lamping.Checks.ResultLambdaReading
namespace Lamping.Checks.OverlapLambdaReading
open Lambda Lambda.Labelled
private def a := Label.atom
private def argument : LTerm := .lam (a 4) (.var (a 5) 0)
private def body : LTerm := .var (a 3) 0
private def source : LTerm := .app (a 0) (.app (a 1) (.lam (a 2) body) argument) argument
private def target : LTerm := .app (a 0) (LTerm.contract (a 1) (a 2) body argument) argument
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_reading : PrerequisitePrefix target [.fn,.body] [] [.fn] :=
  .var (parent := [.fn]) (rest := []) rfl rfl rfl rfl .refl
private theorem actual_chain : PrerequisiteChain target [.fn,.body] [[.fn]] :=
  actual_reading.close (.redex_lam (p := []) rfl)
example : ∃ before after,
    [[.fn]]=before++([.fn]::after) ∧PrerequisitePrefix target [.fn,.body] before [.fn] ∧
    PrerequisiteChain source [.fn,.arg,.body]
      (before.map (fun edge=>([.fn,.arg] : Path)++edge.drop 1)++[[.fn,.arg],[.fn,.fn]]) ∧
    before.map target.labelAt=(before.map (fun edge=>([.fn,.arg] : Path)++edge.drop 1)).map source.labelAt := by
  obtain ⟨relative,oldRoot,before,after,startEq,origin,equal,segment,oldChain,labels⟩ :=
    actual_step.result_lambda_reading_prefix_reflect (body := body) (argument := argument)
      rfl rfl actual_chain (by simp) actual_reading (by
        intro before after equal q occurs present
        have sizes := congrArg List.length equal
        simp only [List.length_append,List.length_cons,List.length_nil] at sizes
        have empty : before=[] := List.eq_nil_of_length_eq_zero (by omega)
        rw [empty] at present
        cases present)
  have rootEq : oldRoot=([.fn,.arg] : Path) := by
    rcases origin with ⟨_,stamp,inner,bodyEq⟩ | ⟨eq,_⟩
    · cases bodyEq
    · exact eq
  have relativeEq : relative=([.body] : Path) := (List.cons.inj startEq).2.symm
  subst oldRoot
  subst relative
  exact ⟨before,after,equal,segment,oldChain,labels⟩
example : ¬∃ stamp inner,body=.lam stamp inner := by rintro ⟨stamp,inner,equal⟩; cases equal
end Lamping.Checks.OverlapLambdaReading

namespace Lamping.Checks.CopyLambdaReading
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 9) (.var (a 9) 0)
private def argument : LTerm := .lam (a 5) (.app (a 6) (.var (a 7) 0) (.var (a 8) 0))
private def body : LTerm := .lam (a 2) (.var (a 3) 1)
private def source : LTerm := .app (a 0) (.app (a 0) (.lam (a 1) body) argument) identity
private def target : LTerm := .app (a 0) (LTerm.contract (a 0) (a 1) body argument) identity
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_reading : PrerequisitePrefix target [.fn,.body,.body]
    [[.fn,.body,.body,.fn]] [.fn,.body] :=
  .app rfl (by intro l b impossible; cases impossible)
    (.var (parent := [.fn,.body]) (rest := [.fn]) rfl rfl rfl rfl .refl)
private theorem actual_chain : PrerequisiteChain target [.fn,.body,.body]
    [[.fn,.body,.body,.fn],[.fn,.body],[.fn]] :=
  actual_reading.close (.lam (parent := [.fn]) (step := .body) rfl (by decide) (.redex_lam (p := []) rfl))
example : ∃ relative before after,
    ([.fn,.body,.body] : Path)=[.fn,.body]++relative ∧
    [[.fn,.body,.body,.fn],[.fn,.body],[.fn]]=before++([.fn,.body]::after) ∧
    PrerequisitePrefix target [.fn,.body,.body] before [.fn,.body] ∧
    PrerequisiteChain source (([.fn,.arg] : Path)++relative)
      (before.map (fun edge=>([.fn,.arg] : Path)++edge.drop 2)++[[.fn,.arg],[.fn,.fn]]) ∧
    before.map target.labelAt=(before.map (fun edge=>([.fn,.arg] : Path)++edge.drop 2)).map source.labelAt := by
  exact actual_step.copy_lambda_reading_prefix_reflect (copySite := [.body])
    rfl rfl rfl actual_chain (by simp) actual_reading
#print axioms StepAt.copy_lambda_reading_prefix_reflect
#print axioms StepAt.result_lambda_reading_prefix_reflect
end Lamping.Checks.CopyLambdaReading

namespace Lamping.Checks.PrerequisiteSubtreeEntry
open Lambda Lambda.Labelled
private def identity : LTerm := .lam (Label.atom 7) (.var (Label.atom 7) 0)
private def source : LTerm := .app (Label.atom 7)
  (.app (Label.atom 7) (.var (Label.atom 7) 0) identity) identity
private theorem actual_entry : PrerequisitePrefix source [] [[.fn]] [.fn] :=
  .app rfl (by intro l b impossible; cases impossible) .refl
example : ([.fn] : Path)∈[[.fn]] := by
  rcases actual_entry.subtree_entry (head := [.fn]) (relative := []) rfl with ⟨inside,equal⟩ | read
  · have sizes := congrArg List.length equal
    simp only [List.length_nil,List.length_append,List.length_cons] at sizes
    omega
  · exact read
private theorem internal : PrerequisitePrefix source [.fn,.arg] [[.fn,.arg]] [.fn] :=
  .lam (parent := [.fn]) (step := .arg) rfl (by decide) .refl
example : ∃ inside,([.fn,.arg] : Path)=[.fn]++inside :=
  internal.start_inside_of_unread (head := [.fn]) (relative := []) rfl (by decide)
example : ¬PrerequisitePrefix source [] [] [.fn] := by
  intro alleged
  obtain ⟨inside,equal⟩ := alleged.start_inside_of_unread (head := [.fn]) (relative := []) rfl (by simp)
  have sizes := congrArg List.length equal
  simp only [List.length_nil,List.length_append,List.length_cons] at sizes
  omega
#print axioms PrerequisitePrefix.subtree_entry
#print axioms PrerequisitePrefix.start_inside_of_unread
end Lamping.Checks.PrerequisiteSubtreeEntry

namespace Lamping.Checks.RetainedBodyPrefixTransport
open Lambda Lambda.Labelled
private def a := Label.atom
private def argument : LTerm := .lam (a 6) (.var (a 7) 0)
private def body : LTerm := .app (a 3) (.var (a 4) 1) (.var (a 5) 0)
private def source : LTerm := .app (a 0) (.lam (a 1) body) argument
private def target : LTerm := LTerm.contract (a 0) (a 1) body argument
private theorem actual_step : StepAt [] source target := .root _ _ _ _
private theorem actual_prefix : PrerequisitePrefix target [] [[.fn]] [.fn] :=
  .app rfl (by intro l b impossible; cases impossible) .refl
private theorem copies_not_read (q : Path) (occurs : ArgumentOccurrence body.erase q) :
    ([] : Path)++q∉[[.fn]] := by
  intro present
  have equal : q=([.fn] : Path) := by simpa only [List.nil_append,List.mem_singleton] using present
  subst q
  cases occurs
example : PrerequisitePrefix source [.fn,.body] [[.fn,.body,.fn]] [.fn,.body,.fn] ∧
    ([[.fn]] : List Path).map target.labelAt=([[.fn,.body,.fn]] : List Path).map source.labelAt := by
  exact actual_step.retained_body_prefix_reflect_labelled (relative := []) (ending := [.fn])
    (old := body) rfl actual_prefix rfl rfl rfl (by intro stamp impossible; cases impossible) copies_not_read
-- The generic reflected endpoint genuinely need not have any chain. It is
-- the free variable old1 (current0), not a hidden successful endpoint oracle.
example : ¬PrerequisiteChain source [.fn,.body,.fn] edges := by
  intro alleged
  obtain ⟨parent,rest,origin,inner,split,depth,binder,tail⟩ := alleged.variable_cases (a := a 4) (index := 1) rfl
  have depths := congrArg binderDepth split
  simp only [binderDepth_append,binderDepth] at depths
  omega
example : target.subterm [.fn]=some (.var (a 4) 0) := rfl
example : ¬∃ stamp inner,body=.lam stamp inner := by rintro ⟨stamp,inner,equal⟩; cases equal
example : ArgumentOccurrence body.erase [.arg] := rfl
#print axioms StepAt.retained_body_prefix_reflect_labelled
end Lamping.Checks.RetainedBodyPrefixTransport

namespace Lamping.Checks.CopyFunctionPrefixTransport
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 9) (.var (a 10) 0)
private def sibling : LTerm := .lam (a 5) (.app (a 6) (.var (a 7) 0) identity)
private def body : LTerm := .app (a 3) (.var (a 4) 0) sibling
private def source : LTerm := .app (a 0) (.app (a 1) (.lam (a 2) body) identity) identity
private def target : LTerm := .app (a 0) (LTerm.contract (a 1) (a 2) body identity) identity
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_reading : PrerequisitePrefix target [.fn,.arg,.body]
    [[.fn,.arg,.body,.fn],[.fn,.arg]] [.fn] :=
  .app rfl (by intro l b impossible; cases impossible)
    (.var (parent := [.fn,.arg]) (rest := [.fn]) rfl rfl rfl rfl
      (.lam (parent := [.fn]) (step := .arg) rfl (by decide) .refl))
private theorem actual_chain : PrerequisiteChain target [.fn,.arg,.body]
    [[.fn,.arg,.body,.fn],[.fn,.arg],[.fn,.fn]] :=
  actual_reading.close (.redex_app rfl)
private theorem copies_unread (q : Path) (occurs : ArgumentOccurrence body.erase q) :
    ([.fn] : Path)++q∉[[.fn,.arg,.body,.fn],[.fn,.arg]] := by
  intro present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with equal | equal
  · have qEq : q=([.arg,.body,.fn] : Path) := List.append_cancel_left equal
    subst q
    cases occurs
  · have qEq : q=([.arg] : Path) := List.append_cancel_left equal
    subst q
    cases occurs
example : BetaIncomingReadingOrigin body identity [.fn] [.fn,.fn] [.fn]
    [.fn,.fn,.body] [.fn,.fn,.body,.fn] [.fn,.arg] ∧
    PrerequisiteChain source [.fn,.fn,.body,.arg,.body]
      [[.fn,.fn,.body,.arg,.body,.fn],[.fn,.fn,.body,.arg],[.fn,.fn,.body,.fn],[.fn,.fn]] ∧
    ([[.fn,.arg,.body,.fn],[.fn,.arg]] : List Path).map target.labelAt=
      ([[.fn,.fn,.body,.arg,.body,.fn],[.fn,.fn,.body,.arg]] : List Path).map source.labelAt := by
  obtain ⟨relative,startEq,oldChain,labels⟩ := actual_step.copy_function_prefix_reflect_labelled
    (parent := []) rfl rfl rfl actual_reading (by decide) copies_unread
  have relativeEq : relative=([.arg,.body] : Path) := (List.cons.inj startEq).2.symm
  subst relative
  exact ⟨.copyFunction (parent := []) rfl rfl rfl,oldChain,labels⟩
example : PrerequisiteChain target [.fn,.arg,.body]
    [[.fn,.arg,.body,.fn],[.fn,.arg],[.fn,.fn]] := actual_chain
-- If the RESULT edge was already read, COPY-FUNCTION is not first-new.
-- There is a real such prefix, and the claimed inside coordinate is false.
private theorem earlier_result : PrerequisitePrefix target [] [[.fn]] [.fn] :=
  .app rfl (by intro l b impossible; cases impossible) .refl
example : ([.fn] : Path)∈[[.fn]] := by decide
example : ¬∃ relative,([] : Path)=[.fn]++relative := by
  rintro ⟨relative,equal⟩
  have sizes := congrArg List.length equal
  simp only [List.length_nil,List.length_append,List.length_cons] at sizes
  omega
example : PrerequisitePrefix target [] [[.fn]] [.fn] := earlier_result
#print axioms StepAt.copy_function_prefix_reflect_labelled
end Lamping.Checks.CopyFunctionPrefixTransport

namespace Lamping.Checks.FirstCreatedIncoming
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 9) (.var (a 10) 0)
private def sibling : LTerm := .lam (a 5) (.app (a 6) (.var (a 7) 0) identity)
private def body : LTerm := .app (a 3) (.var (a 4) 0) sibling
private def source : LTerm := .app (a 0) (.app (a 1) (.lam (a 2) body) identity) identity
private def target : LTerm := .app (a 0) (LTerm.contract (a 1) (a 2) body identity) identity
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_reading : PrerequisitePrefix target [.fn,.arg,.body]
    [[.fn,.arg,.body,.fn],[.fn,.arg]] [.fn] :=
  .app rfl (by intro l b impossible; cases impossible)
    (.var (parent := [.fn,.arg]) (rest := [.fn]) rfl rfl rfl rfl
      (.lam (parent := [.fn]) (step := .arg) rfl (by decide) .refl))
private theorem actual_chain : PrerequisiteChain target [.fn,.arg,.body]
    [[.fn,.arg,.body,.fn],[.fn,.arg],[.fn,.fn]] :=
  actual_reading.close (.redex_app rfl)
private def edges : List Path := [[.fn,.arg,.body,.fn],[.fn,.arg],[.fn,.fn]]
private theorem computed : firstCreatedCut body [.fn] edges =
    some ([[.fn,.arg,.body,.fn],[.fn,.arg]],[.fn,.fn],[]) := rfl
example : ∃ middle oldStart first last,
    PrerequisitePrefix target [.fn,.arg,.body] [[.fn,.arg,.body,.fn],[.fn,.arg]] middle ∧
    PrerequisiteReads target middle [.fn,.fn] ∧
    BetaIncomingReadingOrigin body identity [.fn] [.fn,.fn] middle oldStart first last ∧
    PrerequisiteChain source oldStart [first,[.fn,.fn]] := by
  obtain ⟨before,edge,after,middle,oldStart,first,last,cutComputed,split,segment,remainder,reads,
      origin,oldChain,oldLast,created,unread⟩ := actual_step.first_created_reading_origins
        (body := body) (argument := identity) rfl actual_chain
        ⟨[.fn,.fn],by simp,by exact betaCreatedIncoming_iff.mpr (Or.inr ⟨[.fn],rfl,rfl⟩)⟩
  have exactCut : (before,edge,after)=
      ([[.fn,.arg,.body,.fn],[.fn,.arg]],[.fn,.fn],[]) := Option.some.inj (cutComputed.symm.trans computed)
  cases exactCut
  exact ⟨middle,oldStart,first,last,segment,reads,origin,oldChain⟩
example : firstCreatedCut body [.fn] [[.fn],[.fn,.fn]] = some ([],[.fn],[[.fn,.fn]]) := rfl
example : firstCreatedCut body [.fn] [[.fn,.arg,.body,.fn],[.fn,.arg]] = none := rfl
-- Repeating labels does not make old syntax edges into created heads.
example : ¬BetaCreatedIncoming body [.fn] [.fn,.arg] := by decide
#print axioms StepAt.first_created_reading_origins
#print axioms PrerequisiteChain.first_created_cut
#print axioms PrerequisiteChain.first_created_result_before
end Lamping.Checks.FirstCreatedIncoming
namespace Lamping.Checks.FirstCreatedPrefixConsumer
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 9) (.var (a 10) 0)
private def sibling : LTerm := .lam (a 5) (.app (a 6) (.var (a 7) 0) identity)
private def body : LTerm := .app (a 3) (.var (a 4) 0) sibling
private def source : LTerm := .app (a 0) (.app (a 1) (.lam (a 2) body) identity) identity
private def target : LTerm := .app (a 0) (LTerm.contract (a 1) (a 2) body identity) identity
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_reading : PrerequisitePrefix target [.fn,.arg,.body]
    [[.fn,.arg,.body,.fn],[.fn,.arg]] [.fn] :=
  .app rfl (by intro l b impossible; cases impossible)
    (.var (parent := [.fn,.arg]) (rest := [.fn]) rfl rfl rfl rfl
      (.lam (parent := [.fn]) (step := .arg) rfl (by decide) .refl))
-- No caller-provided result/copy-unread proof: these are read directly
-- from the computation, then consumed by the actual old-prefix theorem.
example : PrerequisiteChain source [.fn,.fn,.body,.arg,.body]
    [[.fn,.fn,.body,.arg,.body,.fn],[.fn,.fn,.body,.arg],[.fn,.fn,.body,.fn],[.fn,.fn]] := by
  have computed : firstCreatedCut body [.fn]
      [[.fn,.arg,.body,.fn],[.fn,.arg],[.fn,.fn]] =
      some ([[.fn,.arg,.body,.fn],[.fn,.arg]],[.fn,.fn],[]) := rfl
  obtain ⟨equal,created,unread⟩ := firstCreatedCut_sound computed
  obtain ⟨resultUnread,copiesUnread⟩ := first_created_unread_heads unread
  obtain ⟨relative,startEq,oldChain,labels⟩ := actual_step.copy_function_prefix_reflect_labelled
    (parent := []) rfl rfl rfl actual_reading resultUnread copiesUnread
  have relativeEq : relative=([.arg,.body] : Path) := (List.cons.inj startEq).2.symm
  subst relative
  exact oldChain
end Lamping.Checks.FirstCreatedPrefixConsumer
namespace Lamping.Checks.FirstCreatedWholePrefix
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 9) (.var (a 10) 0)
private def sibling : LTerm := .lam (a 5) (.app (a 6) (.var (a 7) 0) identity)
private def body : LTerm := .app (a 3) (.var (a 4) 0) sibling
private def source : LTerm := .app (a 0) (.app (a 1) (.lam (a 2) body) identity) identity
private def target : LTerm := .app (a 0) (LTerm.contract (a 1) (a 2) body identity) identity
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem actual_reading : PrerequisitePrefix target [.fn,.arg,.body]
    [[.fn,.arg,.body,.fn],[.fn,.arg]] [.fn] :=
  .app rfl (by intro l b impossible; cases impossible)
    (.var (parent := [.fn,.arg]) (rest := [.fn]) rfl rfl rfl rfl
      (.lam (parent := [.fn]) (step := .arg) rfl (by decide) .refl))
private theorem actual_chain : PrerequisiteChain target [.fn,.arg,.body]
    [[.fn,.arg,.body,.fn],[.fn,.arg],[.fn,.fn]] :=
  actual_reading.close (.redex_app rfl)
private def edges : List Path := [[.fn,.arg,.body,.fn],[.fn,.arg],[.fn,.fn]]
private theorem computed : firstCreatedCut body [.fn]
    [[.fn,.arg,.body,.fn],[.fn,.arg],[.fn,.fn]] =
    some ([[.fn,.arg,.body,.fn],[.fn,.arg]],[.fn,.fn],[]) := rfl
example : ∃ region : BetaPrefixRegion,∃ first last,
    PrerequisiteChain source (region.reindex [.fn] [.fn,.arg,.body])
      (([[.fn,.arg,.body,.fn],[.fn,.arg]] : List Path).map (region.reindex [.fn])++[first,[.fn,.fn]]) ∧
    ([[.fn,.arg,.body,.fn],[.fn,.arg]] : List Path).map target.labelAt=
      (([[.fn,.arg,.body,.fn],[.fn,.arg]] : List Path).map (region.reindex [.fn])).map source.labelAt ∧
    ∃ oldLast,source.subterm last=some oldLast := by
  obtain ⟨before,edge,after,middle,oldMiddle,first,last,region,cutComputed,split,segment,remainder,
      reads,origin,oldChain,labels,lastLookup,created,unread⟩ := actual_step.first_created_prefix_reflect
        (body := body) (argument := identity) rfl actual_chain
        ⟨[.fn,.fn],by simp,by exact betaCreatedIncoming_iff.mpr (Or.inr ⟨[.fn],rfl,rfl⟩)⟩
  have exactCut : (before,edge,after)=
      ([[.fn,.arg,.body,.fn],[.fn,.arg]],[.fn,.fn],[]) := Option.some.inj (cutComputed.symm.trans computed)
  cases exactCut
  exact ⟨region,first,last,oldChain,labels,lastLookup⟩
#print axioms StepAt.first_created_prefix_reflect
end Lamping.Checks.FirstCreatedWholePrefix
namespace Lamping.Checks.FirstCreatedOverlap
open Lambda Lambda.Labelled
private def a := Label.atom
private def argument : LTerm := .lam (a 4) (.var (a 5) 0)
private def body : LTerm := .var (a 3) 0
private def source : LTerm := .app (a 0) (.app (a 1) (.lam (a 2) body) argument) argument
private def target : LTerm := .app (a 0) (LTerm.contract (a 1) (a 2) body argument) argument
private theorem actual_step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private theorem atSource : source.subterm [.fn]=some (.app (a 1) (.lam (a 2) body) argument) := rfl
-- The same literal edge is both RESULT and root COPY. It is computed once.
example : firstCreatedCut body [.fn] [[.fn]]=some ([],[.fn],[]) := rfl
example : BetaCreatedIncoming body [.fn] [.fn] ∧ArgumentOccurrence body.erase [] := ⟨Or.inl rfl,rfl⟩
-- Read FUNCTION from the outer app: the public top supplies old prefix/chain.
example : ∃ middle oldMiddle first last,∃ region : BetaPrefixRegion,
    BetaIncomingReadingOrigin body argument [.fn] [.fn] middle oldMiddle first last ∧
    PrerequisiteChain source (region.reindex [.fn] []) [first,[.fn,.fn]] ∧
    ∃ oldLast,source.subterm last=some oldLast := by
  have chain : PrerequisiteChain target [] [[.fn]] := .redex_app rfl
  obtain ⟨before,edge,after,middle,oldMiddle,first,last,region,computed,split,segment,remainder,
      reads,origin,oldChain,labels,lastLookup,created,unread⟩ :=
    actual_step.first_created_prefix_reflect atSource chain ⟨[.fn],by simp,Or.inl rfl⟩
  have equal : (before,edge,after)=([],[.fn],[]) := Option.some.inj computed.symm
  cases equal
  exact ⟨middle,oldMiddle,first,last,region,origin,oldChain,lastLookup⟩
-- Read lambda CONTEXT from the selected result: SAME cut, separate origin.
example : ∃ middle oldMiddle first last,∃ region : BetaPrefixRegion,
    BetaIncomingReadingOrigin body argument [.fn] [.fn] middle oldMiddle first last ∧
    PrerequisiteChain source (region.reindex [.fn] [.fn]) [first,[.fn,.fn]] ∧
    ∃ oldLast,source.subterm last=some oldLast := by
  have chain : PrerequisiteChain target [.fn] [[.fn]] := .redex_lam (p := []) rfl
  obtain ⟨before,edge,after,middle,oldMiddle,first,last,region,computed,split,segment,remainder,
      reads,origin,oldChain,labels,lastLookup,created,unread⟩ :=
    actual_step.first_created_prefix_reflect atSource chain ⟨[.fn],by simp,Or.inl rfl⟩
  have equal : (before,edge,after)=([],[.fn],[]) := Option.some.inj computed.symm
  cases equal
  exact ⟨middle,oldMiddle,first,last,region,origin,oldChain,lastLookup⟩
#print axioms PrerequisiteChain.first_created_split_unique
end Lamping.Checks.FirstCreatedOverlap
namespace Lamping.Checks.UncreatedPrerequisiteTransitions
open Lambda Lambda.Labelled
private def a := Label.atom
private def body : LTerm := .lam (a 7) (.var (a 7) 1)
private def argument : LTerm := .var (a 7) 0
private def source : LTerm := .lam (a 7) (.app (a 7) (.lam (a 7) body) argument)
private def target : LTerm := .lam (a 7) (LTerm.contract (a 7) (a 7) body argument)
private def stamp := (a 7).concat ((a 7).under.concat (a 7))
private theorem actual_step : StepAt [.body] source target := .body (.root _ _ _ _)
private theorem actual_redex : source.subterm [.body]=some (.app (a 7) (.lam (a 7) body) argument) := rfl
private theorem actual_leaf : target.subterm [.body,.body]=some (.var stamp 1) := rfl
private theorem copied : BetaNodePreimage body argument [.body] [.body,.body] [.body,.arg] := by
  simpa only [List.append_nil] using
    (BetaNodePreimage.copied (body := body) (site := [.body]) (q := [.body]) (relative := [])
      (old := argument) (by rfl) (by rfl))
-- All labels repeat. An actual copied free variable shifts 0 to 1 and jumps
-- outside the beta head; its old jump genuinely changes coordinate region.
example : PrerequisitePrefix source [.body,.arg] [] [] ∧
    BetaNodePreimage body argument [.body] [] [] := by
  obtain ⟨oldLeaf,automatic⟩ := actual_step.beta_node_preimage actual_redex actual_leaf
  have same : oldLeaf=([.body,.arg] : Path) := automatic.unique copied
  subst oldLeaf
  obtain ⟨oldParent,oldStamp,oldBody,oldBinder,oldJump,nextOrigin⟩ :=
    actual_step.beta_variable_preimage_prefix actual_redex automatic
      (parent := []) (rest := [.body]) rfl actual_leaf rfl
  have outside : BetaNodePreimage body argument [.body] [] [] := .context (by rintro ⟨r,impossible⟩; cases impossible)
  have parentEq : oldParent=[] := nextOrigin.unique outside
  subst oldParent
  exact ⟨oldJump,nextOrigin⟩
example : Closed source.erase := by change (1<3 ∧0<1); omega
example : Closed target.erase := by change 1<2; omega
example : ¬BetaNodePreimage body argument [.body] [.body,.body] [.body,.fn,.body,.body] := by
  intro wrong
  have impossible := wrong.unique copied
  cases impossible
#print axioms StepAt.beta_node_preimage
#print axioms BetaNodePreimage.unique
#print axioms StepAt.beta_variable_preimage_prefix
end Lamping.Checks.UncreatedPrerequisiteTransitions
namespace Lamping.Checks.UncreatedRetainedJump
open Lambda Lambda.Labelled
private def a := Label.atom
private def body : LTerm := .lam (a 7) (.var (a 7) 2)
private def argument : LTerm := .lam (a 7) (.var (a 7) 0)
private def source : LTerm := .lam (a 7) (.app (a 7) (.lam (a 7) body) argument)
private def target : LTerm := .lam (a 7) (LTerm.contract (a 7) (a 7) body argument)
private theorem actual_step : StepAt [.body] source target := .body (.root _ _ _ _)
private theorem actual_redex : source.subterm [.body]=some (.app (a 7) (.lam (a 7) body) argument) := rfl
example : PrerequisitePrefix source [.body,.fn,.body,.body] [] [] := by
  have known : BetaNodePreimage body argument [.body] [.body,.body] [.body,.fn,.body,.body] :=
    .retained (relative := [.body]) (old := .var (a 7) 2) rfl (by intro stamp impossible; cases impossible)
  obtain ⟨oldLeaf,automatic⟩ := actual_step.beta_node_preimage actual_redex
    (show target.subterm [.body,.body]=some (.var (a 7) 1) from rfl)
  have same := automatic.unique known
  subst oldLeaf
  obtain ⟨oldParent,oldStamp,oldBody,oldBinder,oldJump,nextOrigin⟩ :=
    actual_step.beta_variable_preimage_prefix actual_redex automatic
      (parent := []) (rest := [.body]) rfl (by rfl) rfl
  have outside : BetaNodePreimage body argument [.body] [] [] := .context (by rintro ⟨r,impossible⟩; cases impossible)
  have equal := nextOrigin.unique outside
  subst oldParent
  exact oldJump
end Lamping.Checks.UncreatedRetainedJump

namespace Lamping.Checks.UncreatedInternalCopyJump
open Lambda Lambda.Labelled
private def a := Label.atom
private def body : LTerm := .lam (a 7) (.var (a 7) 1)
private def argument : LTerm := .lam (a 7) (.var (a 7) 0)
private def source : LTerm := .lam (a 7) (.app (a 7) (.lam (a 7) body) argument)
private def target : LTerm := .lam (a 7) (LTerm.contract (a 7) (a 7) body argument)
private def stamp := (a 7).concat ((a 7).under.concat (a 7))
private theorem actual_step : StepAt [.body] source target := .body (.root _ _ _ _)
private theorem actual_redex : source.subterm [.body]=some (.app (a 7) (.lam (a 7) body) argument) := rfl
example : PrerequisitePrefix source [.body,.arg,.body] [] [.body,.arg] ∧
    BetaNodePreimage body argument [.body] [.body,.body] [.body,.arg] := by
  have known : BetaNodePreimage body argument [.body] [.body,.body,.body] [.body,.arg,.body] :=
    .copied (q := [.body]) (relative := [.body]) (old := .var (a 7) 0) rfl rfl
  obtain ⟨oldLeaf,automatic⟩ := actual_step.beta_node_preimage actual_redex
    (show target.subterm [.body,.body,.body]=some (.var (a 7) 0) from rfl)
  have same := automatic.unique known
  subst oldLeaf
  obtain ⟨oldParent,oldStamp,oldBody,oldBinder,oldJump,nextOrigin⟩ :=
    actual_step.beta_variable_preimage_prefix actual_redex automatic
      (parent := [.body,.body]) (rest := [])
      (show target.subterm [.body,.body]=some (.lam stamp (.var (a 7) 0)) from rfl) (by rfl) rfl
  have binderKnown : BetaNodePreimage body argument [.body] [.body,.body] [.body,.arg] := by
    simpa only [List.append_nil] using
      (BetaNodePreimage.copied (body := body) (site := [.body]) (q := [.body]) (relative := [])
        (old := argument) (by rfl) (by rfl))
  have equal := nextOrigin.unique binderKnown
  subst oldParent
  exact ⟨oldJump,nextOrigin⟩
end Lamping.Checks.UncreatedInternalCopyJump
namespace Lamping.Checks.OutsideContextOrigins
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 7) (.var (a 7) 0)
private def source : LTerm := .lam (a 7) (.app (a 7)
  (.app (a 7) (.lam (a 7) identity) identity) (.var (a 7) 0))
private def target : LTerm := .lam (a 7) (.app (a 7)
  (LTerm.contract (a 7) (a 7) identity identity) (.var (a 7) 0))
private theorem actual_step : StepAt [.body,.fn] source target := .body (.fn (.root _ _ _ _))
example : ∃ oldFn oldArg,source.subterm [.body]=some (.app (a 7) oldFn oldArg) := by
  exact actual_step.context_app_origin (by rfl) (by rintro ⟨r,impossible⟩; cases impossible)
example : ∃ oldBody,source.subterm []=some (.lam (a 7) oldBody) := by
  exact actual_step.context_lambda_origin (by rfl) (by rintro ⟨r,impossible⟩; cases impossible)
example : source.subterm [.body,.arg]=some (.var (a 7) 0) := by
  exact actual_step.context_variable_origin (by rfl) (by rintro ⟨r,impossible⟩; cases impossible)
#print axioms StepAt.context_app_origin
#print axioms StepAt.context_lambda_origin
#print axioms StepAt.context_variable_origin
end Lamping.Checks.OutsideContextOrigins
namespace Lamping.Checks.UncreatedWholeChain
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 7) (.var (a 7) 0)
private def body : LTerm := .lam (a 7) (.var (a 7) 1)
private def argument : LTerm := .var (a 7) 0
private def source : LTerm := .app (a 7)
  (.lam (a 7) (.app (a 7) (.lam (a 7) body) argument)) identity
private def target : LTerm := .app (a 7)
  (.lam (a 7) (LTerm.contract (a 7) (a 7) body argument)) identity
private def stamp := (a 7).concat ((a 7).under.concat (a 7))
private theorem actual_step : StepAt [.fn,.body] source target := .fn (.body (.root _ _ _ _))
private theorem actual_redex : source.subterm [.fn,.body]=some (.app (a 7) (.lam (a 7) body) argument) := rfl
private theorem actual_leaf : target.subterm [.fn,.body,.body]=some (.var stamp 1) := rfl
private theorem actual_chain : PrerequisiteChain target [.fn,.body,.body] [[.fn]] :=
  .var (parent := [.fn]) (rest := [.body]) actual_leaf rfl rfl rfl (.redex_lam (p := []) rfl)
private theorem all_old (edge : Path) (member : edge∈[[.fn]]) :
    ¬BetaCreatedIncoming body [.fn,.body] edge := by
  have equal : edge=([.fn] : Path) := by simpa only [List.mem_singleton] using member
  subst edge
  decide
example : ∃ oldEdges,PrerequisiteChain source [.fn,.body,.arg] oldEdges ∧
    BetaEdgePreimages body argument [.fn,.body] [[.fn]] oldEdges := by
  obtain ⟨oldStart,automatic⟩ := actual_step.beta_node_preimage actual_redex actual_leaf
  have copied : BetaNodePreimage body argument [.fn,.body] [.fn,.body,.body] [.fn,.body,.arg] := by
    simpa only [List.append_nil] using
      (BetaNodePreimage.copied (body := body) (site := [.fn,.body]) (q := [.body])
        (relative := []) (old := argument) (by rfl) (by rfl))
  have equal := automatic.unique copied
  subst oldStart
  exact actual_chain.beta_uncreated_reflect actual_step actual_redex automatic all_old
-- The start's incoming COPY is genuinely new, although NONE of the chain's
-- actual read edges is new. The top imposes no notCreated-node premise.
example : BetaCreatedIncoming body [.fn,.body] [.fn,.body,.body] :=
  betaCreatedIncoming_iff.mpr (Or.inr ⟨[.body],rfl,rfl⟩)
example : PrerequisiteChain source [.fn,.body,.arg] [[.fn]] :=
  .var (parent := [.fn]) (rest := [.arg]) rfl rfl rfl rfl (.redex_lam (p := []) rfl)
example : Closed source.erase := by change (1<3 ∧0<1) ∧0<1; omega
example : Closed target.erase := by change 1<2 ∧0<1; omega
-- The automatic top chooses the old start itself and preserves the ordered
-- read labels, although the current start has a freshly minted copy label.
example : ∃ oldEdges,PrerequisiteChain source [.fn,.body,.arg] oldEdges ∧
    BetaEdgePreimages body argument [.fn,.body] [[.fn]] oldEdges ∧
    ([[.fn]] : List Path).map target.labelAt=oldEdges.map source.labelAt := by
  obtain ⟨oldStart,oldEdges,origin,oldChain,edgeOrigins,labels,lengths⟩ :=
    actual_step.uncreated_chain_reflect actual_redex actual_chain all_old
  have copied : BetaNodePreimage body argument [.fn,.body] [.fn,.body,.body] [.fn,.body,.arg] := by
    simpa only [List.append_nil] using
      (BetaNodePreimage.copied (body := body) (site := [.fn,.body]) (q := [.body])
        (relative := []) (old := argument) (by rfl) (by rfl))
  have equal := origin.unique copied
  subst oldStart
  exact ⟨oldEdges,oldChain,edgeOrigins,labels⟩
#print axioms StepAt.uncreated_chain_reflect#print axioms PrerequisiteChain.beta_uncreated_reflect
end Lamping.Checks.UncreatedWholeChain
namespace Lamping.Checks.UncreatedLongContextChain
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 7) (.var (a 7) 0)
private def inner : LTerm := .lam (a 7) (.app (a 7) (.var (a 7) 0) identity)
private def outer : LTerm := .lam (a 7) (.app (a 7) (.var (a 7) 0) inner)
private def source : LTerm := .app (a 7) outer (.app (a 7) identity identity)
private def target : LTerm := .app (a 7) outer
  (LTerm.contract (a 7) (a 7) (.var (a 7) 0) identity)
private theorem actual_step : StepAt [.arg] source target := .arg (.root _ _ _ _)
private theorem actual_redex : source.subterm [.arg]=some (.app (a 7) (.lam (a 7) (.var (a 7) 0)) identity) := rfl
private def start : Path := [.fn,.body,.arg,.body]
private def edges : List Path :=
  [[.fn,.body,.arg,.body,.fn],[.fn,.body,.arg],[.fn,.body,.fn],[.fn]]
private theorem actual_chain : PrerequisiteChain target start edges :=
  .app rfl (by intro stamp b impossible; cases impossible)
    (.var (parent := [.fn,.body,.arg]) (rest := [.fn]) rfl rfl rfl rfl
      (.lam (parent := [.fn,.body]) (step := .arg) rfl (by decide)
        (.app rfl (by intro stamp b impossible; cases impossible)
          (.var (parent := [.fn]) (rest := [.fn]) rfl rfl rfl rfl (.redex_lam (p := []) rfl)))))
private theorem all_old (edge : Path) (member : edge∈edges) :
    ¬BetaCreatedIncoming (.var (a 7) 0) [.arg] edge := by
  simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal | equal | equal <;> subst edge <;> decide
-- The true four-edge chase includes app reads, lexical jumps, a lambda ARG
-- ascent, and a terminal redex. The edited graph-side-sibling is not read.
example : ∃ oldEdges,PrerequisiteChain source start oldEdges ∧
    edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length := by
  obtain ⟨oldStart,oldEdges,origin,oldChain,edgeOrigins,labels,lengths⟩ :=
    actual_step.uncreated_chain_reflect actual_redex actual_chain all_old
  have context : BetaNodePreimage (.var (a 7) 0) identity [.arg] start start :=
    .context (by rintro ⟨r,impossible⟩; cases impossible)
  have equal := origin.unique context
  subst oldStart
  exact ⟨oldEdges,oldChain,labels,lengths⟩
-- A supplied app-side redex chain also reflects through the SAME actual step.
example : ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
    ([[.fn]] : List Path).map target.labelAt=oldEdges.map source.labelAt := by
  have chain : PrerequisiteChain target [] [[.fn]] := .redex_app rfl
  obtain ⟨oldStart,oldEdges,origin,oldChain,edgeOrigins,labels,lengths⟩ :=
    actual_step.uncreated_chain_reflect actual_redex chain (by
      intro edge member
      have equal : edge=([.fn] : Path) := by simpa only [List.mem_singleton] using member
      subst edge
      decide)
  exact ⟨oldStart,oldEdges,oldChain,labels⟩
end Lamping.Checks.UncreatedLongContextChain
namespace Lamping.Checks.UncreatedCopiedMixedChain
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 7) (.var (a 7) 0)
private def body : LTerm := .var (a 7) 0
private def argument : LTerm := .app (a 7) (.var (a 7) 0) identity
private def source : LTerm := .app (a 7) (.lam (a 7) (.app (a 7) (.lam (a 7) body) argument)) identity
private def target : LTerm := .app (a 7) (.lam (a 7) (LTerm.contract (a 7) (a 7) body argument)) identity
private theorem actual_step : StepAt [.fn,.body] source target := .fn (.body (.root _ _ _ _))
private theorem actual_redex : source.subterm [.fn,.body]=some (.app (a 7) (.lam (a 7) body) argument) := rfl
private def edges : List Path := [[.fn,.body,.arg],[.fn,.body,.fn],[.fn]]
private theorem actual_chain : PrerequisiteChain target [.fn,.body,.arg] edges :=
  .lam (parent := [.fn,.body]) (step := .arg) rfl (by decide)
    (.app rfl (by intro stamp b impossible; cases impossible)
      (.var (parent := [.fn]) (rest := [.fn]) rfl rfl rfl rfl (.redex_lam (p := []) rfl)))
private theorem all_old (edge : Path) (member : edge∈edges) :
    ¬BetaCreatedIncoming body [.fn,.body] edge := by
  simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal | equal <;> subst edge <;> decide
-- The actual three-edge chain reads two strict ARG-copy edges, then switches
-- through its copied variable to the external context/function edge.
example : ∃ oldEdges,PrerequisiteChain source [.fn,.body,.arg,.arg] oldEdges ∧
    BetaEdgePreimages body argument [.fn,.body] edges oldEdges ∧
    edges.map target.labelAt=oldEdges.map source.labelAt := by
  obtain ⟨oldStart,oldEdges,origin,oldChain,edgeOrigins,labels,lengths⟩ :=
    actual_step.uncreated_chain_reflect actual_redex actual_chain all_old
  have known : BetaNodePreimage body argument [.fn,.body] [.fn,.body,.arg] [.fn,.body,.arg,.arg] := by
    simpa only [List.append_nil] using
      (BetaNodePreimage.copied (body := body) (site := [.fn,.body]) (q := []) (relative := [.arg])
        (old := identity) (by rfl) (by rfl))
  have equal := origin.unique known
  subst oldStart
  exact ⟨oldEdges,oldChain,edgeOrigins,labels⟩
end Lamping.Checks.UncreatedCopiedMixedChain

namespace Lamping.Checks.UncreatedRetainedMixedChain
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 7) (.var (a 7) 0)
private def body : LTerm := .app (a 7) (.var (a 7) 1) identity
private def argument : LTerm := identity
private def source : LTerm := .app (a 7) (.lam (a 7) (.app (a 7) (.lam (a 7) body) argument)) identity
private def target : LTerm := .app (a 7) (.lam (a 7) (LTerm.contract (a 7) (a 7) body argument)) identity
private theorem actual_step : StepAt [.fn,.body] source target := .fn (.body (.root _ _ _ _))
private theorem actual_redex : source.subterm [.fn,.body]=some (.app (a 7) (.lam (a 7) body) argument) := rfl
private def edges : List Path := [[.fn,.body,.arg],[.fn,.body,.fn],[.fn]]
private theorem actual_chain : PrerequisiteChain target [.fn,.body,.arg] edges :=
  .lam (parent := [.fn,.body]) (step := .arg) rfl (by decide)
    (.app rfl (by intro stamp b impossible; cases impossible)
      (.var (parent := [.fn]) (rest := [.fn]) rfl rfl rfl rfl (.redex_lam (p := []) rfl)))
private theorem all_old (edge : Path) (member : edge∈edges) :
    ¬BetaCreatedIncoming body [.fn,.body] edge := by
  simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal | equal <;> subst edge <;> decide
-- The same physical shape instead has two retained-body origins; old index1
-- is current0, and the chain then enters the outside lexical binder.
example : ∃ oldEdges,PrerequisiteChain source [.fn,.body,.fn,.body,.arg] oldEdges ∧
    BetaEdgePreimages body argument [.fn,.body] edges oldEdges ∧
    edges.map target.labelAt=oldEdges.map source.labelAt := by
  obtain ⟨oldStart,oldEdges,origin,oldChain,edgeOrigins,labels,lengths⟩ :=
    actual_step.uncreated_chain_reflect actual_redex actual_chain all_old
  have known : BetaNodePreimage body argument [.fn,.body] [.fn,.body,.arg] [.fn,.body,.fn,.body,.arg] :=
    .retained (relative := [.arg]) (old := identity) rfl (by intro stamp impossible; cases impossible)
  have equal := origin.unique known
  subst oldStart
  exact ⟨oldEdges,oldChain,edgeOrigins,labels⟩
#print axioms StepAt.preimage_node_constructor
#print axioms StepAt.beta_app_preimages
#print axioms StepAt.beta_lambda_parent_preimage
#print axioms BetaEdgePreimages.length_eq
end Lamping.Checks.UncreatedRetainedMixedChain
namespace Lamping.Checks.PrerequisiteVertexRanks
open Lambda Lambda.Labelled
private def a := Label.atom
private def identity : LTerm := .lam (a 1) (.var (a 2) 0)
private def redex : LTerm := .app (a 0) identity identity
-- The terminal app and lambda have SAME singleton rank, but distinct kinds.
example : PrerequisiteChain redex [] [[.fn]] ∧
    PrerequisiteChain redex [.fn] [[.fn]] ∧ ([] : Path)≠[.fn] ∧
    redex.constructorTag≠identity.constructorTag := by
  exact ⟨.redex_app rfl,.redex_lam (p:=[]) rfl,by decide,by decide⟩
-- A singleton real redex supplies both endpoint chains to the rank theorem.
example {p q : Path} {left right : LTerm} {pe qe : List Path}
    (ip : PrerequisiteIncident redex [[.fn]] p)
    (iq : PrerequisiteIncident redex [[.fn]] q)
    (pc : PrerequisiteChain redex p pe) (qc : PrerequisiteChain redex q qe)
    (lp : redex.subterm p=some left) (lq : redex.subterm q=some right)
    (same : left.constructorTag=right.constructorTag)
    (rank : pe.length=qe.length) : p=q := by
  have chain : PrerequisiteChain redex [] [[.fn]] := .redex_app rfl
  exact chain.incident_rank_constructor_injective ip iq pc qc lp lq same rank
private def dupBody : LTerm := .app (a 2) (.var (a 3) 0) (.var (a 4) 0)
private def argument : LTerm := .lam (a 5) (.var (a 6) 0)
private def dupSource : LTerm := .app (a 0) (.lam (a 1) dupBody) argument
private def dupTarget : LTerm := LTerm.contract (a 0) (a 1) dupBody argument
example : StepAt [] dupSource dupTarget ∧
    (∃ stamp b,dupTarget.subterm [.fn]=some (.lam stamp b)) ∧
    (∃ stamp b,dupTarget.subterm [.arg]=some (.lam stamp b)) := by
  exact ⟨.root _ _ _ _,⟨_,_,rfl⟩,⟨_,_,rfl⟩⟩
-- Global node preimages really merge two proper lambda copies. Thus the
-- all-old ONE-chain premise of the public injectivity theorem is essential.
example : BetaNodePreimage dupBody argument [] [.fn] [.arg] ∧
    BetaNodePreimage dupBody argument [] [.arg] [.arg] ∧
    ([.fn] : Path)≠[.arg] := by
  exact ⟨by simpa using (BetaNodePreimage.copied (body:=dupBody) (argument:=argument)
    (site:=[]) (q:=[.fn]) (relative:=[]) (old:=argument) rfl rfl),
    by simpa using (BetaNodePreimage.copied (body:=dupBody) (argument:=argument)
    (site:=[]) (q:=[.arg]) (relative:=[]) (old:=argument) rfl rfl),by decide⟩
#print axioms PrerequisiteChain.incident_chain
#print axioms PrerequisiteChain.incident_rank_constructor_injective
#print axioms StepAt.incident_preimage_injective
end Lamping.Checks.PrerequisiteVertexRanks

namespace Lamping.Checks.UncreatedCopiedMixedChain
open Lambda Lambda.Labelled
-- The accepted mixed ARG-copy -> external binder chain instantiates the
-- full step theorem, including its actual non-root beta and all-old reads.
example {p q old : Path}
    (ip : PrerequisiteIncident target edges p)
    (iq : PrerequisiteIncident target edges q)
    (po : BetaNodePreimage body argument [.fn,.body] p old)
    (qo : BetaNodePreimage body argument [.fn,.body] q old) : p=q := by
  exact actual_step.incident_preimage_injective actual_redex actual_chain all_old ip iq po qo
end Lamping.Checks.UncreatedCopiedMixedChain

namespace Lamping.Checks.FirstCreatedWholePrefix
open Lambda Lambda.Labelled
-- Only the supplied finite BEFORE and next lambda reading are reflected.
-- The genuine remaining chain still reads a created COPY-FUNCTION edge.
private theorem early_prefix : PrerequisitePrefix target [.fn,.arg,.body]
    [[.fn,.arg,.body,.fn]] [.fn,.arg] :=
  .app rfl (by intro l b impossible; cases impossible)
    (.var (parent := [.fn,.arg]) (rest := [.fn]) rfl rfl rfl rfl .refl)
example : ∃ oldStart oldFinish oldEdges oldEdge,
    PrerequisitePrefix source oldStart oldEdges oldFinish ∧
    PrerequisiteReads source oldFinish oldEdge ∧
    ([[.fn,.arg,.body,.fn]] : List Path).map target.labelAt=oldEdges.map source.labelAt ∧
    target.labelAt [.fn,.arg]=source.labelAt oldEdge := by
  obtain ⟨oldStart,oldFinish,oldEdges,oldEdge,_,oldSegment,_,_,reads,_,labels,chosen⟩ :=
    actual_step.uncreated_prefix_reading (body:=body) (argument:=identity) rfl early_prefix
      (Or.inr ⟨_,_,rfl,rfl⟩) (by
        intro edge member
        have equal : edge=([.fn,.arg,.body,.fn] : Path) := by simpa using member
        subst edge
        decide) (by decide)
  exact ⟨oldStart,oldFinish,oldEdges,oldEdge,oldSegment,reads,labels,chosen⟩
example : PrerequisiteChain target [.fn,.arg,.body]
    [[.fn,.arg,.body,.fn],[.fn,.arg],[.fn,.fn]] ∧
    BetaCreatedIncoming body [.fn] [.fn,.fn] :=
  ⟨actual_chain,betaCreatedIncoming_iff.mpr (Or.inr ⟨[.fn],rfl,rfl⟩)⟩
-- There is no old chain at the arbitrary endpoint of a zero-edge prefix.
example : PrerequisitePrefix (.var (.atom 7) 0) [] [] [] := .refl
#print axioms PrerequisitePrefix.beta_uncreated_reflect
#print axioms StepAt.beta_uncreated_reading
#print axioms StepAt.uncreated_prefix_reading
end Lamping.Checks.FirstCreatedWholePrefix

namespace Lamping.Checks.NestedUniformReadingCreation
open Lambda Lambda.Labelled
private def I : Term := .lam (.var 0)
private def caller : Term := .lam (.app (.lam (.var 0)) (.var 0))
private def bare : Term := .app (.lam (.app (.var 0) (.app (.var 0) I))) caller
private def original : LTerm := initLabels bare
private def rootContract : LTerm →LTerm
  | .app b (.lam a body) argument => LTerm.contract b a body argument
  | t => t
private def first : LTerm := rootContract original
private def second : LTerm := rootContract first
private def third : LTerm := match second with
  | .app b fn arg => .app b fn (rootContract arg)
  | t => t
example : StepAt [] original first := by exact .root _ _ _ _
example : StepAt [] first second := by exact .root _ _ _ _
example : StepAt [.arg] second third := by exact .arg (.root _ _ _ _)
example : History [[],[],[.arg]] original third :=
  .cons (.root _ _ _ _) (.cons (.root _ _ _ _) (.cons (.arg (.root _ _ _ _)) (.nil _)))
example : third.erase=.app I (.app I I) := rfl
example : third.degreeAt []=some (.atom 10) ∧third.degreeAt [.arg]=some (.atom 10) := ⟨rfl,rfl⟩
private def fourth : LTerm := rootContract third
private def fifth : LTerm := rootContract fourth
private def F : List Path := [[],[.arg]]
private def completeNested : ParallelStep F third.erase fifth.erase := by
  refine ⟨[[],[]],.lam (.var 0),(Marked.completeOld_iff _ _).mpr ⟨?_,?goal⟩,rfl⟩
  · exact .cons (.root _ _ _) (.cons (.root _ _ _) (.nil _))
  case goal => exact True.intro
example : ParallelStep F third.erase fifth.erase := completeNested
example : History completeNested.paths third fifth :=
  .cons (.root _ _ _ _) (.cons (.root _ _ _ _) (.nil _))
example : fourth.degreeAt []=some (.atom 10) := rfl
example : ¬fourth.OuterBarsSafe (fun payload=>payload≠Label.atom 10) := by
  intro safe
  have one : StepAt [] third fourth := .root _ _ _ _
  have degree : third.degreeAt []=some (.atom 10) := rfl
  obtain ⟨beta,body,arg,lookup⟩ := LTerm.degreeAt_redex degree
  have rootSafe := (LTerm.outerBarsSafe_iff _ _).mp safe fourth.label (LTerm.label_mem_of_subterm (p:=[]) rfl)
  exact one.created_label_not_safe lookup (edge:=[]) rfl (Or.inl rfl) rootSafe
private theorem nestedLabels : History completeNested.paths third fifth :=
  .cons (.root _ _ _ _) (.cons (.root _ _ _ _) (.nil _))
private theorem selected (p : Path) (inside : p∈F) : third.degreeAt p=some (.atom 10) := by
  rcases List.mem_cons.mp inside with rfl | rest
  · rfl
  · have equal : p=[.arg] := List.mem_singleton.mp rest
    subst p;rfl
example : CreatedReadingEvent F completeNested.paths (Marked.mark F third.erase)
    completeNested.markedTarget third fifth (.atom 10) [] (fifth.labelAt []) := by
  exact completeNested.complete.1.created_reading_event_of_fresh
    (DegreeAligned.initial third F) nestedLabels selected .refl
    (Or.inr ⟨_,_,rfl,rfl⟩) (by intro e inside;cases inside) (current:=fifth) rfl (by decide)
#print axioms Marked.RelativeOldHistory.inherited_reading_or_created_event
#print axioms Marked.RelativeOldHistory.created_reading_event_of_fresh
end Lamping.Checks.NestedUniformReadingCreation

namespace Lamping.Checks.ReadingCreationWithCreatedSuffix
open Lambda Lambda.Labelled
private def a := Label.atom
private def I : LTerm := .lam (a 3) (.var (a 4) 0)
private def body : LTerm := .var (a 2) 0
private def redex : LTerm := .app (a 0) (.lam (a 1) body) I
private def result : LTerm := LTerm.contract (a 0) (a 1) body I
private def source : LTerm := .app (a 5) redex redex
private def middle : LTerm := .app (a 5) result redex
private def target : LTerm := .app (a 5) result result
private def F : List Path := [[.fn],[.arg]]
private def completeTwo : ParallelStep F source.erase target.erase := by
  refine ⟨F,.app [] (.lam (.var 0)) (.lam (.var 0)),(Marked.completeOld_iff _ _).mpr ⟨?_,?goal⟩,rfl⟩
  · exact .cons (.appL (.root _ _ _)) (.cons (.appR (.root _ _ _)) (.nil _))
  case goal => exact ⟨True.intro,True.intro⟩
private def labels : History completeTwo.paths source target :=
  .cons (.fn (.root _ _ _ _)) (.cons (.arg (.root _ _ _ _)) (.nil _))
private theorem selected (p : Path) (inside : p∈F) : source.degreeAt p=some (.atom 1) := by
  rcases List.mem_cons.mp inside with rfl | rest
  · rfl
  · have equal : p=[.arg] := List.mem_singleton.mp rest
    subst p;rfl
-- The chosen left label is inherited through a later ordinary beta which
-- really creates the right incoming edge. No all-old suffix is supplied.
example : CreatedReadingEvent F completeTwo.paths (Marked.mark F source.erase)
    completeTwo.markedTarget source target (.atom 1) [] (target.labelAt [.fn]) := by
  exact completeTwo.complete.1.created_reading_event_of_fresh
    (DegreeAligned.initial source F) labels selected .refl
    (Or.inr ⟨_,_,rfl,rfl⟩) (by intro e inside;cases inside) (current:=result) rfl (by decide)
example : StepAt [.arg] middle target ∧BetaCreatedIncoming body [.arg] [.arg] ∧
    target.labelAt [.fn]=middle.labelAt [.fn] :=
  ⟨.arg (.root _ _ _ _),Or.inl rfl,rfl⟩
end Lamping.Checks.ReadingCreationWithCreatedSuffix

namespace Lamping.Checks.FirstCreatedWholePrefix
open Lambda Lambda.Labelled
-- COPY-FUNCTION: genuine nonempty app/var/lambda before, no supplied
-- continuation chain at the reading endpoint.
example : ∃ oldStart oldBefore first,
    PrerequisiteChain source oldStart (oldBefore++[first,[.fn,.fn]]) ∧
    ([[.fn,.arg,.body,.fn],[.fn,.arg]] : List Path).map target.labelAt=oldBefore.map source.labelAt := by
  obtain ⟨oldStart,oldBefore,oldMiddle,first,last,_,_,_,_,oldChain,labels,_⟩ :=
    actual_step.created_prefix_old_chain (body:=body) (argument:=identity) rfl actual_reading
      (Or.inl ⟨_,_,_,rfl,rfl⟩)
      (betaCreatedIncoming_iff.mpr (Or.inr ⟨[.fn],rfl,rfl⟩)) (by
        intro edge member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> decide)
  exact ⟨oldStart,oldBefore,first,oldChain,labels⟩
end Lamping.Checks.FirstCreatedWholePrefix
namespace Lamping.Checks.CopyLambdaReading
open Lambda Lambda.Labelled
-- COPY-CONTEXT: the internal lambda binder jump is reflected in the old ARG.
example : ∃ oldStart oldBefore first,
    PrerequisiteChain source oldStart (oldBefore++[first,[.fn,.fn]]) := by
  obtain ⟨oldStart,oldBefore,oldMiddle,first,last,_,_,_,_,oldChain,_,_⟩ :=
    actual_step.created_prefix_old_chain (body:=body) (argument:=argument) rfl actual_reading
      (Or.inr ⟨_,_,rfl,rfl⟩)
      (betaCreatedIncoming_iff.mpr (Or.inr ⟨[.body],rfl,rfl⟩)) (by
        intro edge member
        have equal : edge=([.fn,.body,.body,.fn] : Path) := by simpa using member
        subst edge;decide)
  exact ⟨oldStart,oldBefore,first,oldChain⟩
end Lamping.Checks.CopyLambdaReading
namespace Lamping.Checks.FirstNewResultLambda
open Lambda Lambda.Labelled
-- Retained RESULT-CONTEXT case is separate from copy/root overlap.
example : ∃ oldStart oldBefore first,
    PrerequisiteChain source oldStart (oldBefore++[first,[.fn,.fn]]) := by
  obtain ⟨oldStart,oldBefore,oldMiddle,first,last,_,_,_,_,oldChain,_,_⟩ :=
    actual_step.created_prefix_old_chain (body:=body) (argument:=identity) rfl
      (start:=[.fn]) .refl (Or.inr ⟨_,_,rfl,rfl⟩) (Or.inl rfl)
      (by intro edge member;cases member)
  exact ⟨oldStart,oldBefore,first,oldChain⟩
end Lamping.Checks.FirstNewResultLambda
namespace Lamping.Checks.FirstCreatedOverlap
open Lambda Lambda.Labelled
-- The exact same overlap edge read as FUNCTION has its context preimage,
-- whereas the copy lambda reading above has the old ARG preimage.
example : ∃ oldStart oldBefore first,
    PrerequisiteChain source oldStart (oldBefore++[first,[.fn,.fn]]) := by
  obtain ⟨oldStart,oldBefore,oldMiddle,first,last,_,_,_,_,oldChain,_,_⟩ :=
    actual_step.created_prefix_old_chain atSource (start:=[]) .refl
      (Or.inl ⟨_,_,_,rfl,rfl⟩) (Or.inl rfl) (by intro edge member;cases member)
  exact ⟨oldStart,oldBefore,first,oldChain⟩
#print axioms BetaIncomingReadingOrigin.middle_preimage
#print axioms StepAt.created_prefix_old_chain
end Lamping.Checks.FirstCreatedOverlap

namespace Lamping.Checks.NestedUniformReadingCreation
open Lambda Lambda.Labelled
private def wrapperTail : LTerm := .lam (.atom 21) (.var (.atom 22) 0)
private def wrapperInitial : LTerm := .app (.atom 20) original wrapperTail
private def wrapperSource : LTerm := .app (.atom 20) third wrapperTail
private def wrapperTarget : LTerm := .app (.atom 20) fifth wrapperTail
example : INIT wrapperInitial := by
  constructor
  · intro l mem
    simp only [wrapperInitial,wrapperTail,LTerm.labels,List.mem_cons,List.mem_append,
      List.not_mem_nil,or_false] at mem
    rcases mem with rfl | old | rfl | rfl
    · exact ⟨_,rfl⟩
    · exact (init_is_INIT bare).1 l old
    · exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
  · decide
example : History [[.fn],[.fn],[.fn,.arg]] wrapperInitial wrapperSource :=
  .cons (.fn (.root _ _ _ _)) (.cons (.fn (.root _ _ _ _))
    (.cons (.fn (.arg (.root _ _ _ _))) (.nil _)))
private def wrapperF : List Path := [[.fn],[.fn,.arg]]
private def wrapperStep : ParallelStep wrapperF wrapperSource.erase wrapperTarget.erase := by
  refine ⟨[[.fn],[.fn]],.app [] (.lam (.var 0)) (.lam (.var 0)),
    (Marked.completeOld_iff _ _).mpr ⟨?_,?goal⟩,rfl⟩
  · exact .cons (.appL (.root _ _ _)) (.cons (.appL (.root _ _ _)) (.nil _))
  case goal => exact ⟨True.intro,True.intro⟩
private def wrapperLabels : History wrapperStep.paths wrapperSource wrapperTarget :=
  .cons (.fn (.root _ _ _ _)) (.cons (.fn (.root _ _ _ _)) (.nil _))
private theorem wrapperSelected (p : Path) (mem : p∈wrapperF) :
    wrapperSource.degreeAt p=some (.atom 10) := by
  rcases List.mem_cons.mp mem with rfl | rest
  · rfl
  · have equal : p=[.fn,.arg] := List.mem_singleton.mp rest
    subst p;rfl
example : ∃ before edge after middle current,
    [[.fn]]=before++(edge::after) ∧
    PrerequisitePrefix wrapperTarget [] before middle ∧
    PrerequisiteReads wrapperTarget middle edge ∧
    (∀ e∈before,∃ old,wrapperTarget.labelAt e=some old ∧old∈wrapperSource.labels) ∧
    wrapperTarget.subterm edge=some current ∧current.label∉wrapperSource.labels ∧
    CreatedReadingEvent wrapperF wrapperStep.paths (Marked.mark wrapperF wrapperSource.erase)
      wrapperStep.markedTarget wrapperSource wrapperTarget (.atom 10)
      (before.map wrapperTarget.labelAt) (wrapperTarget.labelAt edge) := by
  exact wrapperStep.first_nonold_reading_creation wrapperLabels wrapperSelected
    (by
      dsimp [wrapperSource,wrapperTail,third,second,first,rootContract,original,bare,caller,I,
        initLabels,initFrom,LTerm.contract,LTerm.subst,LTerm.prepend,LTerm.single,
        LTerm.lift,LTerm.rename,Label.atom,Label.over,Label.under,Label.concat,LTerm.OuterBarsSafe,Label.OuterBarsSafe]
      decide) (.redex_app rfl) ⟨[.fn],by simp,fifth,rfl,by decide⟩
#print axioms ParallelStep.first_nonold_reading_creation
end Lamping.Checks.NestedUniformReadingCreation

namespace Lamping.Checks.BetaChainExistenceReflection
open Lambda Lambda.Labelled
private def a := Label.atom
private def body : LTerm := .var (a 7) 0
private def source : LTerm := .lam (a 7) (.app (a 7) (.lam (a 7) body) body)
private def target : LTerm := .lam (a 7) (LTerm.contract (a 7) (a 7) body body)
private theorem step : StepAt [.body] source target := .body (.root _ _ _ _)
private theorem redex : source.subterm [.body]=some (.app (a 7) (.lam (a 7) body) body) := rfl
private theorem origin : BetaNodePreimage body body [.body] [.body] [.body,.arg] := by
  simpa only [List.append_nil] using
    (BetaNodePreimage.copied (body:=body) (argument:=body) (site:=[.body])
      (q:=[]) (relative:=[]) (old:=body) rfl rfl)
private theorem oldUndefined : NoPrerequisite source [.body,.arg] :=
  (no_prerequisite_variable_iff (by rfl : source.subterm [.body,.arg]=some (.var (a 7) 0))
    (by rfl : source.subterm []=some (.lam (a 7) (.app (a 7) (.lam (a 7) body) body)))
    rfl rfl).mpr (no_prerequisite_root_lambda rfl)
-- A genuine newly created result/copy incoming variable still has no chain,
-- inherited from its ACTUAL old ARG occurrence, not from label identity.
example : NoPrerequisite target [.body] ∧BetaCreatedIncoming body [.body] [.body] :=
  ⟨step.no_prerequisite_at_preimage redex origin oldUndefined,Or.inl rfl⟩
example : NoPrerequisite target [] :=
  step.no_prerequisite_at_preimage redex
    (.context (by rintro ⟨r,equal⟩;cases equal)) (no_prerequisite_root_lambda rfl)
private def I : LTerm := .lam (a 7) body
private def appSource : LTerm := .app (a 7) (.app (a 7) I I) I
private def appTarget : LTerm := .app (a 7) (LTerm.contract (a 7) (a 7) body I) I
private theorem appStep : StepAt [.fn] appSource appTarget := .fn (.root _ _ _ _)
-- This target chain READS the newly created overlap edge. It uses the created
-- prefix branch, rather than the all-old theorem or a caller source chain.
example : ∃ oldEdges,PrerequisiteChain appSource [] oldEdges := by
  exact appStep.chain_reflect_at_preimage rfl
    (.context (by rintro ⟨r,equal⟩;cases equal)) (.redex_app rfl)
example : BetaCreatedIncoming body [.fn] [.fn] := Or.inl rfl
-- Existence is not an equivalence: a beta may erase the source chain.
private def lostSource : LTerm := .app (a 7) I I
private def lostTarget : LTerm := LTerm.contract (a 7) (a 7) body I
example : StepAt [] lostSource lostTarget ∧PrerequisiteChain lostSource [] [[.fn]] ∧
    NoPrerequisite lostTarget [] := ⟨.root _ _ _ _,.redex_app rfl,no_prerequisite_root_lambda rfl⟩
#print axioms StepAt.chain_preimage_exists
#print axioms StepAt.chain_reflect_at_preimage
#print axioms StepAt.no_prerequisite_at_preimage
end Lamping.Checks.BetaChainExistenceReflection

namespace Lamping.Checks.NestedUniformReadingCreation
open Lambda Lambda.Labelled
private def wrapperMiddle : LTerm := .app (.atom 20) fourth wrapperTail
private theorem firstOld : StepAt [.fn] wrapperSource wrapperMiddle := .fn (.root _ _ _ _)
private theorem lastOld : StepAt [.fn] wrapperMiddle wrapperTarget := .fn (.root _ _ _ _)
-- The same target chain is reflected through BOTH genuinely nested OLD events.
-- The first reverse source already has marker10; neither call assumes safe.
example : ∃ es,PrerequisiteChain wrapperSource [] es := by
  have finalChain : PrerequisiteChain wrapperTarget [] [[.fn]] := .redex_app rfl
  obtain ⟨lastBeta,lastBody,lastArgument,lastRedex⟩ := LTerm.degreeAt_redex
    (by rfl : wrapperMiddle.degreeAt [.fn]=some (.atom 10))
  have lastOrigin : BetaNodePreimage lastBody lastArgument [.fn] [] [] :=
    .context (by rintro ⟨r,equal⟩;cases equal)
  obtain ⟨es,middleChain⟩ := lastOld.chain_reflect_at_preimage lastRedex lastOrigin finalChain
  obtain ⟨firstBeta,firstBody,firstArgument,firstRedex⟩ := LTerm.degreeAt_redex
    (by rfl : wrapperSource.degreeAt [.fn]=some (.atom 10))
  have firstOrigin : BetaNodePreimage firstBody firstArgument [.fn] [] [] :=
    .context (by rintro ⟨r,equal⟩;cases equal)
  exact firstOld.chain_reflect_at_preimage firstRedex firstOrigin middleChain
end Lamping.Checks.NestedUniformReadingCreation

namespace Lamping.Checks.BetaChainExistenceReflection
open Lambda Lambda.Labelled
private def labels : History [[.body]] source target := .cons step (.nil _)
private theorem knownTrace : BetaNodeHistoryPreimage labels [.body] [.body,.arg] :=
  .one (step:=step) redex origin (.nil target [.body])
-- Auto-construction recovers THIS old ARG leaf coordinate even though the
-- target label is compound; uniqueness is coordinate-only, not label equality.
example : ∃ old,source.subterm [.body,.arg]=some old ∧
    BetaNodeHistoryPreimage labels [.body] [.body,.arg] := by
  obtain ⟨oldPosition,old,atOld,trace⟩ := labels.node_preimage_from_lookup
    (by rfl : target.subterm [.body]=some (LTerm.contract (a 7) (a 7) body body))
  have equal := trace.unique knownTrace
  subst oldPosition
  exact ⟨old,atOld,trace⟩
example : NoPrerequisite target [.body] := knownTrace.no_prerequisite oldUndefined
example (p : Path) : BetaNodeHistoryPreimage (History.nil source) p p := .nil _ _
#print axioms History.node_preimage_from_lookup
#print axioms BetaNodeHistoryPreimage.unique
#print axioms BetaNodeHistoryPreimage.no_prerequisite
end Lamping.Checks.BetaChainExistenceReflection
namespace Lamping.Checks.NestedUniformReadingCreation
open Lambda Lambda.Labelled
-- The trace is indexed by the SAME genuine nested OLD schedule, whose first
-- reverse source is already marker10-unsafe. It does not reset annotations.
example : ∃ oldPosition old,wrapperSource.subterm oldPosition=some old ∧
    BetaNodeHistoryPreimage wrapperLabels [.fn] oldPosition := by
  exact wrapperLabels.node_preimage_from_lookup (by rfl : wrapperTarget.subterm [.fn]=some fifth)
end Lamping.Checks.NestedUniformReadingCreation
namespace Lamping.Checks.PrerequisiteVertexRanks
open Lambda Lambda.Labelled
private def duplicatedLabels : History [[]] dupSource dupTarget := .cons (.root _ _ _ _) (.nil _)
-- Forward uniqueness fixes the old coordinate for a fixed target. Conversely,
-- two real proper lambda copies still share one old ARG coordinate.
example : BetaNodeHistoryPreimage duplicatedLabels [.fn] [.arg] ∧
    BetaNodeHistoryPreimage duplicatedLabels [.arg] [.arg] ∧([.fn] : Path)≠[.arg] := by
  refine ⟨?_,?_,by decide⟩
  · apply BetaNodeHistoryPreimage.one (step:=StepAt.root _ _ _ _) (redex:=by rfl)
    · simpa only [List.nil_append,List.append_nil] using
        (BetaNodePreimage.copied (body:=dupBody) (argument:=argument) (site:=[])
          (q:=[.fn]) (relative:=[]) (old:=argument) rfl rfl)
    · exact .nil _ _
  · apply BetaNodeHistoryPreimage.one (step:=StepAt.root _ _ _ _) (redex:=by rfl)
    · simpa only [List.nil_append,List.append_nil] using
        (BetaNodePreimage.copied (body:=dupBody) (argument:=argument) (site:=[])
          (q:=[.arg]) (relative:=[]) (old:=argument) rfl rfl)
    · exact .nil _ _
end Lamping.Checks.PrerequisiteVertexRanks

namespace Lamping.Checks.ResidualNodePreimages
open Lambda Lambda.Labelled
private def a := Label.atom
private def I : LTerm := .lam (a 8) (.var (a 9) 0)
private def body : LTerm := .app (a 2) (.var (a 3) 0) (.var (a 4) 0)
private def argument : LTerm := .app (a 5) (.lam (a 6) (.var (a 7) 0)) I
private def source : LTerm := .app (a 0) (.lam (a 1) body) argument
private def target : LTerm := LTerm.contract (a 0) (a 1) body argument
private def F : List Path := [[],[.arg]]
private def markedTarget : Marked := .app [] (.red [[.arg]] (.var 0) (.lam (.var 0)))
  (.red [[.arg]] (.var 0) (.lam (.var 0)))
private def old : Marked.RelativeOldHistory F [[]] (Marked.mark F source.erase) markedTarget :=
  .cons (.redRoot _ _ _) (by decide) (.nil _)
private def labels : History [[]] source target := .cons (.root _ _ _ _) (.nil _)
example : INIT source := by change INIT (initLabels source.erase);exact init_is_INIT _
-- Current function and argument APP occurrences are distinct actual copies,
-- but both carry the SAME original ARG app name, not the contracted root name.
example : BetaNodeHistoryPreimage labels [.fn] [.arg] ∧
    BetaNodeHistoryPreimage labels [.arg] [.arg] ∧([.fn] : Path)≠[.arg] := by
  have general := ((Marked.relativeOld_iff_relative (Marked.selected_mark F source.erase)).mp old).general
  obtain ⟨_,left⟩ := general.initial_name_node_preimage labels
    (by decide : [.fn]∈Marked.tracePositions [.arg] markedTarget)
  obtain ⟨_,right⟩ := general.initial_name_node_preimage labels
    (by decide : [.arg]∈Marked.tracePositions [.arg] markedTarget)
  exact ⟨left,right,by decide⟩
example : ∃ name∈F,(∃ beta alpha b arg,source.subterm name=some (.app beta (.lam alpha b) arg)) ∧
    BetaNodeHistoryPreimage labels [.fn] name :=
  old.selected_node_preimage labels (by decide)
example {coordinate : Path} (trace : BetaNodeHistoryPreimage labels [.fn] coordinate) : coordinate=[.arg] := by
  have general := ((Marked.relativeOld_iff_relative (Marked.selected_mark F source.erase)).mp old).general
  have exactTrace := (general.initial_name_node_preimage labels
    (by decide : [.fn]∈Marked.tracePositions [.arg] markedTarget)).2
  exact trace.unique exactTrace
-- F's root tag was consumed; no coincidental new shape can recover that name.
example : ([] : Path)∉Marked.tracePositions [] markedTarget := by decide
example : ([] : Path)∉Marked.setResidualPositions F markedTarget := by decide
private def retainedBody : LTerm := .app (a 2) (.lam (a 3) (.var (a 4) 0)) I
private def retainedSource : LTerm := .app (a 0) (.lam (a 1) retainedBody) I
private def retainedTarget : LTerm := LTerm.contract (a 0) (a 1) retainedBody I
private def retainedF : List Path := [[],[.fn,.body]]
private def retainedMark : Marked := .red [[.fn,.body]] (.var 0) (.lam (.var 0))
private def retainedOld : Marked.RelativeOldHistory retainedF [[]]
    (Marked.mark retainedF retainedSource.erase) retainedMark :=
  .cons (.redRoot _ _ _) (by decide) (.nil _)
private def retainedLabels : History [[]] retainedSource retainedTarget := .cons (.root _ _ _ _) (.nil _)
-- A retained old APP may have a NEW compound incoming edge at the target.
example : BetaNodeHistoryPreimage retainedLabels [] [.fn,.body] ∧
    BetaCreatedIncoming retainedBody [] [] := by
  have general := ((Marked.relativeOld_iff_relative (Marked.selected_mark retainedF retainedSource.erase)).mp retainedOld).general
  have exactTrace := (general.initial_name_node_preimage retainedLabels
    (by decide : []∈Marked.tracePositions [.fn,.body] retainedMark)).2
  exact ⟨exactTrace,Or.inl rfl⟩
private def captureBody : LTerm := .lam (a 3) (.var (a 4) 1)
private def captureArg : LTerm := .app (a 5) (.lam (a 6) (.var (a 7) 0)) (.var (a 8) 0)
private def captureSource : LTerm := .lam (a 0) (.app (a 1) (.lam (a 2) captureBody) captureArg)
private def captureTarget : LTerm := .lam (a 0) (LTerm.contract (a 1) (a 2) captureBody captureArg)
private def captureF : List Path := [[.body],[.body,.arg]]
private def captureMark : Marked := .lam (.lam (.red [[.body,.arg]] (.var 0) (.var 1)))
private def captureOld : Marked.RelativeOldHistory captureF [[.body]]
    (Marked.mark captureF captureSource.erase) captureMark :=
  .cons (.lam (.redRoot _ _ _)) (by decide) (.nil _)
private def captureLabels : History [[.body]] captureSource captureTarget :=
  .cons (.body (.root _ _ _ _)) (.nil _)
example : INIT captureSource := by change INIT (initLabels captureSource.erase);exact init_is_INIT _
example : BetaNodeHistoryPreimage captureLabels [.body,.body] [.body,.arg] ∧
    captureArg.subterm [.arg]=some (.var (a 8) 0) ∧
    captureTarget.subterm [.body,.body,.arg]=some (.var (a 8) 1) := by
  have general := ((Marked.relativeOld_iff_relative (Marked.selected_mark captureF captureSource.erase)).mp captureOld).general
  have exactTrace := (general.initial_name_node_preimage captureLabels
    (by decide : [.body,.body]∈Marked.tracePositions [.body,.arg] captureMark)).2
  exact ⟨exactTrace,rfl,rfl⟩
#print axioms Marked.ReductionAt.trace_node_preimage
#print axioms Marked.History.trace_node_history_preimage
#print axioms Marked.History.initial_name_node_preimage
#print axioms Marked.RelativeOldHistory.selected_node_preimage
#print axioms Marked.RelativeOldHistory.selected_preimage_mem
end Lamping.Checks.ResidualNodePreimages


namespace Lamping.Checks.ResidualNodePreimages
open Lambda Lambda.Labelled
example : BetaNodeHistoryPreimage labels [.fn,.fn] [.arg,.fn] ∧
    BetaNodeHistoryPreimage labels [.arg,.fn] [.arg,.fn] := by
  have general := ((Marked.relativeOld_iff_relative (Marked.selected_mark F source.erase)).mp old).general
  exact ⟨general.initial_name_function_preimage labels (by decide : [.fn]∈Marked.tracePositions [.arg] markedTarget),
    general.initial_name_function_preimage labels (by decide : [.arg]∈Marked.tracePositions [.arg] markedTarget)⟩
example : ∃ name∈F,(∃ beta alpha b arg,source.subterm name=some (.app beta (.lam alpha b) arg)) ∧
    BetaNodeHistoryPreimage labels [.fn] name ∧
    BetaNodeHistoryPreimage labels [.fn,.fn] (name++[.fn]) :=
  old.selected_app_function_preimages labels (by decide)
-- The fired lambda and the residual lambda both have physical function roles,
-- but SAME actual History locks the latter to the original ARG lambda.
example : ¬BetaNodeHistoryPreimage labels [.fn,.fn] [.fn] := by
  intro wrong
  have general := ((Marked.relativeOld_iff_relative (Marked.selected_mark F source.erase)).mp old).general
  have actual := general.initial_name_function_preimage labels
    (by decide : [.fn]∈Marked.tracePositions [.arg] markedTarget)
  have impossible := wrong.unique actual
  cases impossible
example : BetaNodeHistoryPreimage retainedLabels [.fn] [.fn,.body,.fn] := by
  have general := ((Marked.relativeOld_iff_relative (Marked.selected_mark retainedF retainedSource.erase)).mp retainedOld).general
  exact general.initial_name_function_preimage retainedLabels
    (by decide : []∈Marked.tracePositions [.fn,.body] retainedMark)
example : BetaNodeHistoryPreimage captureLabels [.body,.body,.fn] [.body,.arg,.fn] := by
  have general := ((Marked.relativeOld_iff_relative (Marked.selected_mark captureF captureSource.erase)).mp captureOld).general
  exact general.initial_name_function_preimage captureLabels
    (by decide : [.body,.body]∈Marked.tracePositions [.body,.arg] captureMark)
#print axioms BetaNodePreimage.redex_function_child
#print axioms Marked.History.trace_function_history_preimage
#print axioms Marked.History.initial_name_function_preimage
#print axioms Marked.RelativeOldHistory.selected_app_function_preimages
end Lamping.Checks.ResidualNodePreimages
namespace Lamping.Checks.UniformChainPreimages
open Lambda Lambda.Labelled
private abbrev a := Label.atom 7
private abbrev I : LTerm := .lam a (.var a 0)
private abbrev left : LTerm := .lam a (.app a (.var a 0) I)
private abbrev nested : LTerm := .app a I (.app a I I)
private abbrev nested1 : LTerm := LTerm.contract a a (.var a 0) (.app a I I)
private abbrev nested2 : LTerm := LTerm.contract nested1.label a (.var a 0) I
private abbrev source : LTerm := .app a left nested
private abbrev middle : LTerm := .app a left nested1
private abbrev target : LTerm := .app a left nested2
private abbrev F : List Path := [[.arg],[.arg,.arg]]
private abbrev targetMarked : Marked := .app [[]] (.lam (.app [] (.var 0) (.lam (.var 0)))) (.lam (.var 0))
private def old : Marked.RelativeOldHistory F [[.arg],[.arg]] (Marked.mark F source.erase) targetMarked :=
  .cons (.appR (.redRoot _ _ _)) (by decide) (.cons (.appR (.redRoot _ _ _)) (by decide) (.nil _))
private def labels : History [[.arg],[.arg]] source target :=
  .cons (.arg (.root _ _ _ _)) (.cons (.arg (.root _ _ _ _)) (.nil _))
private abbrev edges : List Path := [[.fn,.body,.arg],[.fn,.body,.fn],[.fn]]
private def chain : PrerequisiteChain target [.fn,.body,.arg] edges :=
  .lam (parent := [.fn,.body]) (step := .arg) rfl (by decide)
    (.app rfl (by intro stamp body impossible;cases impossible)
      (.var (parent := [.fn]) (rest := [.fn]) rfl rfl rfl rfl (.redex_lam (p := []) rfl)))
private theorem selected (p : Path) (member : p∈F) : source.degreeAt p=some a := by
  rcases List.mem_cons.mp member with rfl | inside
  · rfl
  · have same := List.mem_singleton.mp inside;subst p;rfl
private theorem safe (e : Path) (member : e∈edges) (node : LTerm) (lookup : target.subterm e=some node) :
    node.label.OuterBarsSafe (fun x=>x≠a) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> cases lookup <;> trivial
example : ¬middle.OuterBarsSafe (fun x=>x≠a) := by
  intro h
  have turn : StepAt [.arg] source middle := .arg (.root _ _ _ _)
  exact turn.created_label_not_safe (by rfl) (by rfl : middle.subterm [.arg]=some nested1)
    (Or.inl rfl) ((LTerm.outerBarsSafe_iff _ _).mp h _ (LTerm.label_mem_of_subterm (p:=[.arg]) rfl))
example : ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
    BetaNodeHistoryPreimage labels [.fn,.body,.arg] oldStart ∧
    BetaEdgeHistoryPreimages labels edges oldEdges ∧
    edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length :=
  old.marker_free_chain_preimages (DegreeAligned.initial source F) labels selected chain safe
end Lamping.Checks.UniformChainPreimages
#print axioms Lamping.Lambda.Marked.RelativeOldHistory.marker_free_chain_preimages
#print axioms Lamping.Lambda.Labelled.BetaEdgeHistoryPreimages.prepend
#print axioms Lamping.Lambda.Labelled.BetaEdgeHistoryPreimages.unique

namespace Lamping.Checks.DirectedCreation
open Lambda Lambda.Labelled
private abbrev a := Label.atom
private abbrev identity (n : Nat) : LTerm := .lam (a n) (.var (a (n+1)) 0)
private abbrev inner : LTerm := .app (a 0) (.lam (a 1) (.var (a 2) 0)) (identity 3)
private abbrev result := LTerm.contract (a 0) (a 1) (.var (a 2) 0) (identity 3)
private abbrev source : LTerm := .app (a 5) inner (identity 6)
private abbrev target : LTerm := .app (a 5) result (identity 6)
private def step : StepAt [.fn] source target := .fn (.root _ _ _ _)
private def functionOrigin : BetaIncomingReadingOrigin (.var (a 2) 0) (identity 3) [.fn] [.fn] [] [] [.fn] [.fn,.fn,.body] :=
  .resultFunction rfl rfl
private def lambdaOrigin : BetaIncomingReadingOrigin (.var (a 2) 0) (identity 3) [.fn] [.fn] [.fn]
    [.fn,.arg] [.fn,.arg] [.fn,.fn,.body] := .copyLambda (q:=[]) rfl rfl rfl rfl
example : INIT source := by simp [INIT,LTerm.labels,IsAtomic,a,Label.atom]
example : ∃ first last marker rest,source.subterm [.fn]=some first ∧source.subterm [.fn,.fn,.body]=some last ∧
    marker.MarksDegree (a 1) ∧result.label.readLetters true=first.label.readLetters true++marker::rest :=
  functionOrigin.directed_label_prefix step rfl
    ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ rfl
example : ∃ first last marker rest,source.subterm [.fn,.arg]=some first ∧source.subterm [.fn,.fn,.body]=some last ∧
    marker.MarksDegree (a 1) ∧result.label.readLetters false=first.label.readLetters false++marker::rest :=
  lambdaOrigin.directed_label_prefix step rfl
    ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ rfl
example : result.label.readLetters true=[.atom 0,.over (a 1),.atom 2,.under (a 1),.atom 3] ∧
    result.label.readLetters false=[.atom 3,.under (a 1),.atom 2,.over (a 1),.atom 0] := ⟨rfl,rfl⟩
example : ∀ rest,result.label.readLetters false≠[.atom 3]++(.over (a 1))::rest := by
  intro rest impossible
  have heads := List.cons.inj (List.cons.inj impossible).2
  cases heads.1
example : ∃ reader,PrerequisitePrefix source [.fn,.arg] [] reader ∧
    PrerequisiteReadsDirected source reader [.fn,.arg] false :=
  lambdaOrigin.old_directed_reading (target:=target) (forward:=false) rfl ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
private abbrev rBody : LTerm := .lam (a 2) (.var (a 3) 1)
private abbrev rSource : LTerm := .app (a 0) (.lam (a 1) rBody) (identity 4)
private abbrev rResult := LTerm.contract (a 0) (a 1) rBody (identity 4)
example : ∃ first last marker rest,rSource.subterm [.fn,.body]=some first ∧rSource.subterm []=some last ∧
    marker.MarksDegree (a 1) ∧rResult.label.readLetters false=first.label.readLetters false++marker::rest := by
  exact (BetaIncomingReadingOrigin.resultLambda (site:=[]) (edge:=[]) (middle:=[]) rfl rfl rfl).directed_label_prefix
    (StepAt.root _ _ _ _) rfl ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ rfl
private abbrev cBody : LTerm := .app (a 3) (.var (a 4) 0) (.var (a 5) 0)
private abbrev cSource : LTerm := .lam (a 0) (.app (a 1) (.lam (a 2) cBody) (.var (a 6) 0))
private abbrev cTarget : LTerm := .lam (a 0) (LTerm.contract (a 1) (a 2) cBody (.var (a 6) 0))
private def cStep : StepAt [.body] cSource cTarget := .body (.root _ _ _ _)
private def cOrigin : BetaIncomingReadingOrigin cBody (.var (a 6) 0) [.body] [.body,.fn] [.body]
    [.body,.fn,.body] [.body,.fn,.body,.fn] [.body,.arg] := .copyFunction (parent:=[]) rfl rfl rfl
example : ∃ first last marker rest,cSource.subterm [.body,.fn,.body,.fn]=some first ∧cSource.subterm [.body,.arg]=some last ∧
    marker.MarksDegree (a 2) ∧(cTarget.subterm [.body,.fn]).map (fun t=>t.label.readLetters true)=
      some (first.label.readLetters true++marker::rest) := by
  obtain ⟨first,last,marker,rest,firstAt,lastAt,marked,equal⟩ := cOrigin.directed_label_prefix (forward:=true) cStep rfl
    ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ (current:=.var (((a 4).concat (a 2).under).concat (a 6)) 0) rfl
  exact ⟨first,last,marker,rest,firstAt,lastAt,marked,congrArg some equal⟩
example : NoPrerequisite cSource [.body,.arg] :=
  (no_prerequisite_variable_iff (current:=cSource) (parent:=[]) (rest:=[.arg]) (by rfl) (by rfl) rfl rfl).mpr
    (no_prerequisite_root_lambda (by rfl))
#print axioms BetaIncomingReadingOrigin.directed_label_prefix
#print axioms BetaIncomingReadingOrigin.old_directed_reading
end Lamping.Checks.DirectedCreation
namespace Lamping.Checks.DirectedNestedCreation
open Lambda Lambda.Labelled
private def I : Term := .lam (.var 0)
private def caller : Term := .lam (.app (.lam (.var 0)) (.var 0))
private def bare : Term := .app (.lam (.app (.var 0) (.app (.var 0) I))) caller
private def original : LTerm := initLabels bare
private def rootContract : LTerm →LTerm
  | .app b (.lam a body) argument => LTerm.contract b a body argument
  | t => t
private def first : LTerm := rootContract original
private def second : LTerm := rootContract first
private def third : LTerm := match second with
  | .app b fn arg => .app b fn (rootContract arg)
  | t => t
private def fourth : LTerm := rootContract third
private def fifth : LTerm := rootContract fourth
example : INIT original := init_is_INIT _
example : History [[],[],[.arg]] original third :=
  .cons (.root _ _ _ _) (.cons (.root _ _ _ _) (.cons (.arg (.root _ _ _ _)) (.nil _)))
private def F : List Path := [[],[.arg]]
private def old : Marked.RelativeOldHistory F [[],[]] (Marked.mark F third.erase) (.lam (.var 0)) :=
  .cons (.redRoot _ _ _) (by decide) (.cons (.redRoot _ _ _) (by decide) (.nil _))
example : History [[],[]] third fifth := .cons (.root _ _ _ _) (.cons (.root _ _ _ _) (.nil _))
example : third.degreeAt []=some (.atom 10) ∧third.degreeAt [.arg]=some (.atom 10) ∧fourth.degreeAt []=some (.atom 10) :=
  ⟨rfl,rfl,rfl⟩
private theorem firstMarkerPresent : ¬fourth.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  intro safe
  obtain ⟨beta,body,arg,redex⟩ := LTerm.degreeAt_redex (by rfl : third.degreeAt []=some (.atom 10))
  have step : StepAt [] third fourth := .root _ _ _ _
  exact step.created_label_not_safe redex (current:=fourth) rfl (Or.inl rfl) safe
private def wrapperSource : LTerm := .app (.atom 30) fourth (initLabels I)
private def wrapperTarget : LTerm := .app (.atom 30) fifth (initLabels I)
private def step : StepAt [.fn] wrapperSource wrapperTarget := .fn (.root _ _ _ _)
-- The literal label is created NOW, but its oriented old first endpoint
-- already contains the same degree's earlier marker. No mid-source Safe.
example : ∃ firstNode lastNode marker rest,
    wrapperSource.subterm [.fn]=some firstNode ∧
    wrapperSource.subterm [.fn,.fn,.body]=some lastNode ∧
    marker.MarksDegree (.atom 10) ∧
    fifth.label.readLetters true=firstNode.label.readLetters true++marker::rest ∧
    ¬firstNode.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  obtain ⟨beta,body,arg,redex⟩ := LTerm.degreeAt_redex (by rfl : fourth.degreeAt []=some (.atom 10))
  have actual : wrapperSource.subterm [.fn]=some (.app beta (.lam (.atom 10) body) arg) := redex
  have origin : BetaIncomingReadingOrigin body arg [.fn] [.fn] [] [] [.fn] [.fn,.fn,.body] := .resultFunction rfl rfl
  obtain ⟨node,last,marker,rest,atFirst,atLast,marked,equal⟩ := origin.directed_label_prefix step actual
    (forward:=true) ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ (current:=fifth) rfl
  have firstEq : node=fourth := Option.some.inj atFirst.symm
  exact ⟨node,last,marker,rest,atFirst,atLast,marked,equal,firstEq ▸ firstMarkerPresent⟩
end Lamping.Checks.DirectedNestedCreation
namespace Lamping.Checks.EarliestNestedCreation
open Lambda Lambda.Labelled
private def I : Term := .lam (.var 0)
private def caller : Term := .lam (.app (.lam (.var 0)) (.var 0))
private def bare : Term := .app (.lam (.app (.var 0) (.app (.var 0) I))) caller
private def original : LTerm := initLabels bare
private def rootContract : LTerm →LTerm
  | .app b (.lam a body) argument => LTerm.contract b a body argument
  | t => t
private def first : LTerm := rootContract original
private def second : LTerm := rootContract first
private def third : LTerm := match second with
  | .app b fn arg => .app b fn (rootContract arg)
  | t => t
private def fourth : LTerm := rootContract third
private def fifth : LTerm := rootContract fourth
example : INIT original := init_is_INIT _
example : History [[],[],[.arg]] original third :=
  .cons (.root _ _ _ _) (.cons (.root _ _ _ _) (.cons (.arg (.root _ _ _ _)) (.nil _)))
private def F : List Path := [[],[.arg]]
private def old : Marked.RelativeOldHistory F [[],[]] (Marked.mark F third.erase) (.lam (.var 0)) :=
  .cons (.redRoot _ _ _) (by decide) (.cons (.redRoot _ _ _) (by decide) (.nil _))
example : History [[],[]] third fifth := .cons (.root _ _ _ _) (.cons (.root _ _ _ _) (.nil _))
example : third.degreeAt []=some (.atom 10) ∧third.degreeAt [.arg]=some (.atom 10) ∧fourth.degreeAt []=some (.atom 10) :=
  ⟨rfl,rfl,rfl⟩
private theorem firstMarkerPresent : ¬fourth.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  intro safe
  obtain ⟨beta,body,arg,redex⟩ := LTerm.degreeAt_redex (by rfl : third.degreeAt []=some (.atom 10))
  have step : StepAt [] third fourth := .root _ _ _ _
  exact step.created_label_not_safe redex (current:=fourth) rfl (Or.inl rfl) safe
private def freshTail : LTerm := .lam (.atom 31) (.var (.atom 32) 0)
private def wrapperSource : LTerm := .app (.atom 30) fourth freshTail
private def wrapperTarget : LTerm := .app (.atom 30) fifth freshTail
private def step : StepAt [.fn] wrapperSource wrapperTarget := .fn (.root _ _ _ _)
-- The literal label is created NOW, but its oriented old first endpoint
-- already contains the same degree's earlier marker. No mid-source Safe.
example : ∃ firstNode lastNode marker rest,
    wrapperSource.subterm [.fn]=some firstNode ∧
    wrapperSource.subterm [.fn,.fn,.body]=some lastNode ∧
    marker.MarksDegree (.atom 10) ∧
    fifth.label.readLetters true=firstNode.label.readLetters true++marker::rest ∧
    ¬firstNode.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  obtain ⟨beta,body,arg,redex⟩ := LTerm.degreeAt_redex (by rfl : fourth.degreeAt []=some (.atom 10))
  have actual : wrapperSource.subterm [.fn]=some (.app beta (.lam (.atom 10) body) arg) := redex
  have origin : BetaIncomingReadingOrigin body arg [.fn] [.fn] [] [] [.fn] [.fn,.fn,.body] := .resultFunction rfl rfl
  obtain ⟨node,last,marker,rest,atFirst,atLast,marked,equal⟩ := origin.directed_label_prefix step actual
    (forward:=true) ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ (current:=fifth) rfl
  have firstEq : node=fourth := Option.some.inj atFirst.symm
  exact ⟨node,last,marker,rest,atFirst,atLast,marked,equal,firstEq ▸ firstMarkerPresent⟩

private def wholeSource : LTerm := .app (.atom 30) third freshTail
private def wrappedOriginal : LTerm := .app (.atom 30) original freshTail
example : INIT wrappedOriginal := by
  dsimp [wrappedOriginal,original,bare,caller,I,initLabels,initFrom,nodeCount,freshTail]
  simp [INIT,LTerm.labels,IsAtomic,Label.atom]
example : History [[.fn],[.fn],[.fn,.arg]] wrappedOriginal wholeSource :=
  .cons (.fn (.root _ _ _ _)) (.cons (.fn (.root _ _ _ _))
    (.cons (.fn (.arg (.root _ _ _ _))) (.nil _)))
private def markedFinal : Marked := .app [] (.lam (.var 0)) (.lam (.var 0))
private def wholeF : List Path := [[.fn],[.fn,.arg]]
private def wholeOld : Marked.RelativeOldHistory wholeF [[.fn],[.fn]] (Marked.mark wholeF wholeSource.erase) markedFinal :=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.cons (.appL (.redRoot _ _ _)) (by decide) (.nil _))
private def wholeLabels : History [[.fn],[.fn]] wholeSource wrapperTarget :=
  .cons (.fn (.root _ _ _ _)) (.cons (.fn (.root _ _ _ _)) (.nil _))
private theorem wholeSelected (p : Path) (inside : p∈wholeF) : wholeSource.degreeAt p=some (.atom 10) := by
  rcases List.mem_cons.mp inside with rfl | inside
  · rfl
  · have equal := List.mem_singleton.mp inside;subst p;rfl
private theorem sourceFresh : wholeSource.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  change True ∧ third.OuterBarsSafe (fun x=>x≠Label.atom 10) ∧ freshTail.OuterBarsSafe (fun x=>x≠Label.atom 10)
  constructor
  · trivial
  · constructor
    · dsimp [third,second,first,original,bare,caller,I,rootContract,initLabels,initFrom,nodeCount,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.rename,LTerm.lift,LTerm.label,Label.concat,Label.over,Label.under,Label.atom]
      simp only [LTerm.OuterBarsSafe,Label.OuterBarsSafe]
      decide
    · trivial
private theorem finalMarked : ¬fifth.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  intro safe
  obtain ⟨beta,body,arg,redex⟩ := LTerm.degreeAt_redex (by rfl : fourth.degreeAt []=some (.atom 10))
  have step : StepAt [] fourth fifth := .root _ _ _ _
  exact step.created_label_not_safe redex (current:=fifth) rfl (Or.inl rfl) safe
-- Unlike the one-event kernel, this consumes the actual length recursion.
-- The final literal creation has unsafe oldFirst, forcing the earlier OLD.
example : DirectedMarkerSpine wholeF wholeSource (.atom 10) true [[.fn],[.fn]] wrapperTarget [] [.fn] := by
  exact wholeOld.directed_marker_spine wholeLabels wholeSelected sourceFresh
    (start:=[]) .refl ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ (current:=fifth) rfl finalMarked
    (by intro e inside;cases inside)
end Lamping.Checks.EarliestNestedCreation

namespace Lamping.Checks.EarliestNestedCreation
open Lambda Lambda.Labelled
-- Both readings use ONE actual initial history and ONE two-event OLD schedule.
-- The last literal creation's oldFirst is already marked, so these consumers
-- need the strict-length recursion rather than a single-event freshness rule.
example (forward : Bool) :
    ∃ sourceStart sourceBefore sourceReader sourceFirst name sourceFirstNode marker rest,
      name∈wholeF ∧wholeSource.subterm sourceFirst=some sourceFirstNode ∧
      sourceFirstNode.label.OuterBarsSafe (fun x=>x≠Label.atom 10) ∧
      PrerequisitePrefix wholeSource sourceStart sourceBefore sourceReader ∧
      PrerequisiteReadsDirected wholeSource sourceReader sourceFirst forward ∧
      PrerequisiteChain wholeSource sourceStart (sourceBefore++[sourceFirst,name++[.fn]]) ∧
      sourceBefore.map wholeSource.labelAt=[] ∧marker.MarksDegree (.atom 10) ∧
      fifth.label.readLetters forward=sourceFirstNode.label.readLetters forward++marker::rest := by
  have reading : PrerequisiteReadsDirected wrapperTarget (if forward then [] else [.fn]) [.fn] forward := by
    cases forward
    · exact ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
    · exact ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
  have result := wholeOld.earliest_marker_prefix wholeLabels wholeSelected sourceFresh
    (start:=if forward then [] else [.fn]) (before:=[]) .refl reading
    (current:=fifth) rfl finalMarked (by intro e inside;cases inside)
  obtain ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,safe,segment,reads,chain,labels,marked,equation⟩ := result.2
  exact ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,safe,segment,reads,chain,labels.symm,marked,equation⟩
end Lamping.Checks.EarliestNestedCreation

namespace Lamping.Checks.EarliestNestedCreation
open Lambda Lambda.Labelled
-- A genuinely nonempty safe BEFORE, read at the untouched argument lambda,
-- precedes the marked FUNCTION at the application parent.
example : ∃ s es f name node marker rest,
    name∈wholeF ∧wholeSource.subterm f=some node ∧
    PrerequisiteChain wholeSource s (es++[f,name++[.fn]]) ∧
    [wrapperTarget.labelAt [.arg]]=es.map wholeSource.labelAt ∧
    marker.MarksDegree (.atom 10) ∧
    fifth.label.readLetters true=node.label.readLetters true++marker::rest := by
  have segment : PrerequisitePrefix wrapperTarget [.arg] [[.arg]] [] :=
    .lam (parent:=[]) (step:=.arg) rfl (by decide) .refl
  have beforeSafe : ∀e∈[[.arg]],∀node,wrapperTarget.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
    intro e inside node lookup
    have same := List.mem_singleton.mp inside
    subst e
    have same : node=freshTail := Option.some.inj lookup.symm
    subst node
    trivial
  have result := wholeOld.earliest_marker_prefix wholeLabels wholeSelected sourceFresh segment
    (forward:=true) ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ (current:=fifth) rfl finalMarked beforeSafe
  obtain ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,_,_,_,chain,labels,marked,equation⟩ := result.2
  exact ⟨s,es,f,name,node,marker,rest,chosen,atNode,chain,labels,marked,equation⟩
end Lamping.Checks.EarliestNestedCreation

#print axioms Lamping.Lambda.Marked.RelativeOldHistory.directed_marker_spine
#print axioms Lamping.Lambda.Labelled.DirectedMarkerSpine.source_marker_prefix
#print axioms Lamping.Lambda.Marked.RelativeOldHistory.earliest_marker_prefix

namespace Lamping.Checks.EarliestNestedCreation
open Lambda Lambda.Labelled
-- A genuinely nonempty safe BEFORE, read at the untouched argument lambda,
-- precedes the marked FUNCTION at the application parent.
example : ∃ s es f name node marker rest,
    name∈wholeF ∧wholeSource.subterm f=some node ∧
    PrerequisiteChain wholeSource s (es++[f,name++[.fn]]) ∧
    [wrapperTarget.labelAt [.arg]]=es.map wholeSource.labelAt ∧
    marker.MarksDegree (.atom 10) ∧
    fifth.label.readLetters true=node.label.readLetters true++marker::rest ∧
    BetaNodeHistoryPreimage wholeLabels [.arg] s := by
  have segment : PrerequisitePrefix wrapperTarget [.arg] [[.arg]] [] :=
    .lam (parent:=[]) (step:=.arg) rfl (by decide) .refl
  have beforeSafe : ∀e∈[[.arg]],∀node,wrapperTarget.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
    intro e inside node lookup
    have same := List.mem_singleton.mp inside
    subst e
    have same : node=freshTail := Option.some.inj lookup.symm
    subst node
    trivial
  have result := wholeOld.earliest_marker_prefix_at_start wholeLabels wholeSelected sourceFresh segment
    (forward:=true) ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ (current:=fifth) rfl finalMarked beforeSafe
  obtain ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,_,_,_,chain,labels,marked,equation,trace⟩ := result.2
  exact ⟨s,es,f,name,node,marker,rest,chosen,atNode,chain,labels,marked,equation,trace⟩
end Lamping.Checks.EarliestNestedCreation

namespace Lamping.Checks.EarliestNestedCreation
open Lambda Lambda.Labelled
-- Both actual reading directions now return THIS sourceStart ancestry under
-- the SAME two-event labels, alongside exactly that sourceStart's prefix.
example (forward : Bool) :
    ∃ sourceStart sourceBefore sourceReader sourceFirst name sourceFirstNode marker rest,
      name∈wholeF ∧wholeSource.subterm sourceFirst=some sourceFirstNode ∧
      PrerequisitePrefix wholeSource sourceStart sourceBefore sourceReader ∧
      PrerequisiteChain wholeSource sourceStart (sourceBefore++[sourceFirst,name++[.fn]]) ∧
      sourceBefore.map wholeSource.labelAt=[] ∧marker.MarksDegree (.atom 10) ∧
      fifth.label.readLetters forward=sourceFirstNode.label.readLetters forward++marker::rest ∧
      BetaNodeHistoryPreimage wholeLabels (if forward then [] else [.fn]) sourceStart := by
  have reading : PrerequisiteReadsDirected wrapperTarget (if forward then [] else [.fn]) [.fn] forward := by
    cases forward
    · exact ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
    · exact ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
  have result := wholeOld.earliest_marker_prefix_at_start wholeLabels wholeSelected sourceFresh
    (start:=if forward then [] else [.fn]) (before:=[]) .refl reading
    (current:=fifth) rfl finalMarked (by intro e inside;cases inside)
  obtain ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,_,segment,_,chain,labels,marked,equation,trace⟩ := result.2
  exact ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,segment,chain,labels.symm,marked,equation,trace⟩
-- An empty BEFORE does NOT identify the prefix start with its reader:
-- this final variable first jumps to its lambda, then reads its marked context.
private def zeroJump : PrerequisitePrefix wrapperTarget [.fn,.body] [] [.fn] :=
  .var (parent:=[.fn]) (rest:=[]) rfl rfl rfl rfl .refl
example : ([.fn,.body] : Path)≠[.fn] := by decide
example : ∃ s es r f name node marker rest,
    name∈wholeF ∧wholeSource.subterm f=some node ∧
    PrerequisitePrefix wholeSource s es r ∧
    PrerequisiteChain wholeSource s (es++[f,name++[.fn]]) ∧
    marker.MarksDegree (.atom 10) ∧
    fifth.label.readLetters false=node.label.readLetters false++marker::rest ∧
    BetaNodeHistoryPreimage wholeLabels [.fn,.body] s := by
  have result := wholeOld.earliest_marker_prefix_at_start wholeLabels wholeSelected sourceFresh zeroJump
    (forward:=false) ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ (current:=fifth) rfl finalMarked
    (by intro e inside;cases inside)
  obtain ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,_,segment,_,chain,_,marked,equation,trace⟩ := result.2
  exact ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,segment,chain,marked,equation,trace⟩
end Lamping.Checks.EarliestNestedCreation

#print axioms Lamping.Lambda.Marked.RelativeOldHistory.earliest_marker_prefix_at_start

namespace Lamping.Checks.EarliestNestedCreation
open Lambda Lambda.Labelled
-- One returned existential package supplies both the exact prefix and its
-- ordered source slots; the untouched trace locks each coordinate separately.
theorem nonempty_before_origins_consumer :
    ∃ r f name node marker rest,
      name∈wholeF ∧wholeSource.subterm f=some node ∧
      PrerequisitePrefix wholeSource [.arg] [[.arg]] r ∧
      PrerequisiteChain wholeSource [.arg] ([[.arg]]++[f,name++[.fn]]) ∧
      BetaEdgeHistoryPreimages wholeLabels [[.arg]] [[.arg]] ∧
      BetaNodeHistoryPreimage wholeLabels [.arg] [.arg] ∧
      marker.MarksDegree (.atom 10) ∧
      fifth.label.readLetters true=node.label.readLetters true++marker::rest := by
  have segment : PrerequisitePrefix wrapperTarget [.arg] [[.arg]] [] :=
    .lam (parent:=[]) (step:=.arg) rfl (by decide) .refl
  have beforeSafe : ∀e∈[[.arg]],∀node,wrapperTarget.subterm e=some node →
      node.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
    intro e inside node lookup
    have same := List.mem_singleton.mp inside
    subst e
    have same : node=freshTail := Option.some.inj lookup.symm
    subst node
    trivial
  have untouched : BetaNodeHistoryPreimage wholeLabels [.arg] [.arg] :=
    .one (step:=(show StepAt [.fn] wholeSource wrapperSource from .fn (.root _ _ _ _)))
      (by rfl) (.context (by rintro ⟨rest,same⟩;cases same))
      (.one (step:=step) (by rfl) (.context (by rintro ⟨rest,same⟩;cases same)) (.nil _ _))
  have result := wholeOld.earliest_marker_prefix_with_before_origins wholeLabels wholeSelected
    sourceFresh segment (forward:=true) ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
    (current:=fifth) rfl finalMarked beforeSafe
  obtain ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,_,sourcePrefix,_,sourceChain,_,marked,
    equation,startTrace,origins⟩ := result.2
  have sameStart := startTrace.unique untouched
  subst s
  cases origins with
  | cons edgeTrace tail =>
    cases tail
    have sameEdge := edgeTrace.unique untouched
    subst_vars
    exact ⟨r,f,name,node,marker,rest,chosen,atNode,sourcePrefix,sourceChain,
      .cons edgeTrace .nil,startTrace,marked,equation⟩
end Lamping.Checks.EarliestNestedCreation
#print axioms Lamping.Lambda.Marked.RelativeOldHistory.earliest_marker_prefix_with_before_origins
#print axioms Lamping.Checks.EarliestNestedCreation.nonempty_before_origins_consumer

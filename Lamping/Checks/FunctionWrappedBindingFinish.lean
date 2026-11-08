import Lamping.Checks.FunctionWrappedBodyParent
import Lamping.Lamping.OccurrencePhysicalNodes
namespace Lamping.Checks.FunctionWrappedBindingFinish
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable FunctionWrappedBodyParent
set_option maxHeartbeats 4000000

/-- The actual variable observation has the SAME lexical binder as the
specified rooted lambda occurrence. No physical node injectivity is used. -/
theorem variable_finish (lambdaParent : RootAccess finalNet (.inl ()))
    (lambdaWord : accessWord finalNet lambdaParent.val=[.fn])
    (lambdaFinish : lambdaParent.val.getLast?=some (finalNet.wire (.inl ⟨finalLambda,.inl ()⟩)))
    (leafAccess : RootAccess finalNet (.inl ()))
    (variableWord : accessWord finalNet leafAccess.val=[.fn,.body,.fn]) :
    leafAccess.val.getLast?=some (finalNet.wire (.inl ⟨finalLambda,lamBind⟩)) := by
  have matching := actual_final_matches
  obtain ⟨parent,loop,a,b,c,binding,ctx,body,split,ctxRole,parentFinish,
    _parentLabels,_lookup,words,depth⟩ := matching.variable_binding_access leafAccess (k:=0)
      (by rw [variableWord];rfl)
  have coordinates := binding_prefix_depth_unique
    (parent:=[.fn]) (tail:=[.fn]) (other:=accessWord finalNet parent.val)
    (rest:=accessWord finalNet loop) (variableWord.symm.trans words) depth
  have parents : parent=lambdaParent := matching.accessWord_injective
    (coordinates.1.symm.trans lambdaWord.symm)
  have sameLast := (congrArg (fun x : RootAccess finalNet (.inl ()) =>x.val.getLast?) parents)
  have wires := Option.some.inj (parentFinish.symm.trans (sameLast.trans lambdaFinish))
  have ends:=congrArg finalNet.wire wires
  simp only [Pairing.involutive] at ends
  have sameNode : binding.binder=finalLambda := congrArg Sigma.fst (Sum.inl.inj ends)
  have sameBind : (.inl ⟨binding.binder,binding.bind⟩ : Endpoint finalNet)=.inl ⟨finalLambda,lamBind⟩ :=
    congrArg Sum.inl (Sigma.ext sameNode binding.bind_role)
  rw [split,List.getLast?_append,binding.finish,sameBind]
  rfl
#print axioms variable_finish
end Lamping.Checks.FunctionWrappedBindingFinish

import Lamping.Checks.WrappedLambdaParent
import Lamping.Checks.BraArgumentParent
import Lamping.Lamping.OccurrencePhysicalNodes
set_option maxHeartbeats 4000000

namespace Lamping.Checks.UnaryBindingReachable.Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable FunctionWrappedBodyParent WrappedLambdaParent

noncomputable def lambdaEdges : List (Endpoint croLambda.site.reduce) := [
  .inr (.inl (.inl ())),.inl ⟨.inl outerKept2,.inl ()⟩,
  .inr (.inr (.inl (.inl outerOutside2),true)),
  .inr (.inr (.inl (.inl contextOutside2),true)),
  .inr (.inr (.inl (.inl bodyOutside2),false)),
  .inr (.inr (.inl (.inl oldBodyOutside2),true)),
  .inr (.inr (.inr (.inl ()),true))]
theorem lambdaLabels (a : Context) : Labelling croLambda.site.reduce lambdaEdges a a := by
  apply Labelling.cons (by rw [lambda_root];exact LabelledTurn.node (g:=croLambda.site.reduce) (.inl outerKept2) appCtx (.inl ()) (.direct (.appFun a)))
  apply Labelling.cons (by rw [lambda_outer];exact .transparent _ false a)
  apply Labelling.cons (by rw [lambda_outer_finish];exact .transparent _ false a)
  apply Labelling.cons (by rw [lambda_context];exact .transparent _ true a)
  apply Labelling.cons (by rw [lambda_body];exact .transparent _ false a)
  exact .cons (by rw [WrappedLambdaParent.lambda_body_finish];exact .transparent _ false a) (.single _ a)
theorem lambdaWord : accessWord croLambda.site.reduce lambdaEdges=[.fn] := rfl
theorem lambdaFinish : lambdaEdges.getLast?=some (croLambda.site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
  have inverse:=congrArg croLambda.site.reduce.wire lambda_context_finish
  simp only [Pairing.involutive] at inverse
  simpa only [lambdaEdges,List.getLast?_cons_cons,List.getLast?_singleton] using congrArg some inverse
noncomputable def lambdaParent : RootAccess croLambda.site.reduce (.inl ()) := by
  let flow := Classical.choose lambda_certified
  exact ⟨lambdaEdges,⟨⟨⟨Context.empty,Context.empty,lambdaLabels _⟩,
    (lambdaLabels Context.empty).root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [lambdaFinish]
      simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩

theorem source_matches : Matches croLambda.site.net (.inl ()) current.erase :=
  croLambda.sourceIso.matches beta_matches

theorem target_matches : Matches croLambda.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := lambda_certified
  exact matching

theorem variable_finish (lambdaParent : RootAccess croLambda.site.reduce (.inl ()))
    (lambdaWord : accessWord croLambda.site.reduce lambdaParent.val=[.fn])
    (lambdaFinish : lambdaParent.val.getLast?=some (croLambda.site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (leafAccess : RootAccess croLambda.site.reduce (.inl ()))
    (variableWord : accessWord croLambda.site.reduce leafAccess.val=[.fn,.body,.fn]) :
    leafAccess.val.getLast?=some (croLambda.site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩)) := by
  have matching := target_matches
  obtain ⟨parent,loop,a,b,c,binding,ctx,body,split,ctxRole,parentFinish,
    _parentLabels,_lookup,words,depth⟩ := matching.variable_binding_access leafAccess (k:=0)
      (by rw [variableWord];rfl)
  have coordinates := binding_prefix_depth_unique
    (parent:=[.fn]) (tail:=[.fn]) (other:=accessWord croLambda.site.reduce parent.val)
    (rest:=accessWord croLambda.site.reduce loop) (variableWord.symm.trans words) depth
  have parents : parent=lambdaParent := matching.accessWord_injective
    (coordinates.1.symm.trans lambdaWord.symm)
  have sameLast := (congrArg (fun x : RootAccess croLambda.site.reduce (.inl ()) =>x.val.getLast?) parents)
  have wires := Option.some.inj (parentFinish.symm.trans (sameLast.trans lambdaFinish))
  have ends:=congrArg croLambda.site.reduce.wire wires
  simp only [Pairing.involutive] at ends
  have sameNode : binding.binder=.inr (.inl ()) := congrArg Sigma.fst (Sum.inl.inj ends)
  have sameBind : (.inl ⟨binding.binder,binding.bind⟩ : Endpoint croLambda.site.reduce)=.inl ⟨.inr (.inl ()),lamBind⟩ :=
    congrArg Sum.inl (Sigma.ext sameNode binding.bind_role)
  rw [split,List.getLast?_append,binding.finish,sameBind]
  rfl

#print axioms lambdaParent
#print axioms source_matches
#print axioms target_matches
#print axioms variable_finish
theorem actual_variable_finish (leafAccess : RootAccess croLambda.site.reduce (.inl ()))
    (word : accessWord croLambda.site.reduce leafAccess.val=[.fn,.body,.fn]) :
    leafAccess.val.getLast?=some (croLambda.site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩)) :=
  variable_finish lambdaParent lambdaWord lambdaFinish leafAccess word
#print axioms actual_variable_finish
end Lamping.Checks.UnaryBindingReachable.Cro

namespace Lamping.Checks.UnaryBindingReachable.Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable BraFunctionBodyParent BraArgumentParent

noncomputable def lambdaEdges : List (Endpoint braLambda.site.reduce) := [
  .inr (.inl (.inl ())),
  .inr (.inr (.inl (.inl contextOutside2),true)),
  .inr (.inr (.inl (.inl bodyContextOutside2),false)),
  .inr (.inr (.inl (.inl bodyOutside2),true)),
  .inl ⟨.inl rootKept2,appArg⟩,
  .inr (.inr (.inl (.inl argRootOutside2),true)),
  .inl ⟨.inl readerKept2,.inl ()⟩,
  .inr (.inr (.inl (.inl argFreeOutside2),false)),
  .inr (.inr (.inr (.inl ()),true))]

private theorem empty_replace (n : Nat) : Context.empty.replace n Context.empty=Context.empty := by
  ext k;simp [Context.replace]

private theorem emptyCro (n : Nat) : Traversal n (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
  simpa only [Context.cons_empty,empty_replace] using
    (Traversal.direct (Passage.cro (i:=n) Context.empty Context.empty))

theorem lambdaLabels : Labelling braLambda.site.reduce lambdaEdges Context.empty Context.empty := by
  apply Labelling.cons (by rw [lambda_root];exact LabelledTurn.transparent (g:=braLambda.site.reduce) _ false Context.empty)
  apply Labelling.cons (by rw [lambda_context];exact LabelledTurn.transparent (g:=braLambda.site.reduce) _ true Context.empty)
  apply Labelling.cons (by rw [lambda_body];exact LabelledTurn.transparent (g:=braLambda.site.reduce) _ false Context.empty)
  apply Labelling.cons (by rw [BraArgumentParent.lambda_body_finish];exact LabelledTurn.node (g:=braLambda.site.reduce) (.inl rootKept2) appCtx appArg (.direct (.appArg Context.empty)))
  apply Labelling.cons (by rw [lambda_arg];exact LabelledTurn.transparent (g:=braLambda.site.reduce) _ false Context.empty)
  apply Labelling.cons (by rw [lambda_arg_finish];exact LabelledTurn.node (g:=braLambda.site.reduce) (.inl readerKept2) (.inr ()) (.inl ()) (emptyCro 1))
  apply Labelling.cons (by rw [lambda_reader];exact LabelledTurn.transparent (g:=braLambda.site.reduce) _ true Context.empty)
  exact .cons (by rw [lambda_reader_finish];exact LabelledTurn.transparent (g:=braLambda.site.reduce) _ false Context.empty) (.single _ _)

theorem lambdaWord : accessWord braLambda.site.reduce lambdaEdges=[.arg] := rfl

theorem lambdaFinish : lambdaEdges.getLast?=some (braLambda.site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
  have inverse:=congrArg braLambda.site.reduce.wire lambda_context_finish
  simp only [Pairing.involutive] at inverse
  simpa only [lambdaEdges,List.getLast?_cons_cons,List.getLast?_singleton] using congrArg some inverse

noncomputable def lambdaParent : RootAccess braLambda.site.reduce (.inl ()) := by
  let flow := Classical.choose lambda_certified
  exact ⟨lambdaEdges,⟨⟨⟨Context.empty,Context.empty,lambdaLabels⟩,
    lambdaLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [lambdaFinish]
      simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩

theorem source_matches : Matches braLambda.site.net (.inl ()) current.erase :=
  braLambda.sourceIso.matches beta_matches

theorem target_matches : Matches braLambda.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := lambda_certified
  exact matching

theorem variable_finish (lambdaParent : RootAccess braLambda.site.reduce (.inl ()))
    (lambdaWord : accessWord braLambda.site.reduce lambdaParent.val=[.arg])
    (lambdaFinish : lambdaParent.val.getLast?=some (braLambda.site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (leafAccess : RootAccess braLambda.site.reduce (.inl ()))
    (variableWord : accessWord braLambda.site.reduce leafAccess.val=[.arg,.body,.fn]) :
    leafAccess.val.getLast?=some (braLambda.site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩)) := by
  have matching := target_matches
  obtain ⟨parent,loop,a,b,c,binding,ctx,body,split,ctxRole,parentFinish,
    _parentLabels,_lookup,words,depth⟩ := matching.variable_binding_access leafAccess (k:=0)
      (by rw [variableWord];rfl)
  have coordinates := binding_prefix_depth_unique
    (parent:=[.arg]) (tail:=[.fn]) (other:=accessWord braLambda.site.reduce parent.val)
    (rest:=accessWord braLambda.site.reduce loop) (variableWord.symm.trans words) depth
  have parents : parent=lambdaParent := matching.accessWord_injective
    (coordinates.1.symm.trans lambdaWord.symm)
  have sameLast := (congrArg (fun x : RootAccess braLambda.site.reduce (.inl ()) =>x.val.getLast?) parents)
  have wires := Option.some.inj (parentFinish.symm.trans (sameLast.trans lambdaFinish))
  have ends:=congrArg braLambda.site.reduce.wire wires
  simp only [Pairing.involutive] at ends
  have sameNode : binding.binder=.inr (.inl ()) := congrArg Sigma.fst (Sum.inl.inj ends)
  have sameBind : (.inl ⟨binding.binder,binding.bind⟩ : Endpoint braLambda.site.reduce)=.inl ⟨.inr (.inl ()),lamBind⟩ :=
    congrArg Sum.inl (Sigma.ext sameNode binding.bind_role)
  rw [split,List.getLast?_append,binding.finish,sameBind]
  rfl

#print axioms lambdaParent
#print axioms source_matches
#print axioms target_matches
#print axioms variable_finish
theorem actual_variable_finish (leafAccess : RootAccess braLambda.site.reduce (.inl ()))
    (word : accessWord braLambda.site.reduce leafAccess.val=[.arg,.body,.fn]) :
    leafAccess.val.getLast?=some (braLambda.site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩)) :=
  variable_finish lambdaParent lambdaWord lambdaFinish leafAccess word
#print axioms actual_variable_finish
end Lamping.Checks.UnaryBindingReachable.Bra

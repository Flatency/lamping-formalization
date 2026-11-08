import Lamping.Lambda.FunctionParentPreimages
import Lamping.Lambda.ActualNodeLabelAncestry

namespace Lamping.Lambda.Labelled

/-- The SAME actual history transports a genuine old redex's FUNCTION
lambda ancestry together with its real APP parent. No marked tag or
selected-residual membership is assumed or concluded here. -/
theorem BetaNodeHistoryPreimage.function_redex_parent
    {ps : List Path} {source target oldBody oldArg currentBody : LTerm}
    {name currentFn : Path} {oldApp oldLam currentLam : Label}
    {labels : History ps source target}
    (oldRedex : source.subterm name=some (.app oldApp (.lam oldLam oldBody) oldArg))
    (trace : BetaNodeHistoryPreimage labels currentFn (name++[.fn]))
    (lookup : target.subterm currentFn=some (.lam currentLam currentBody)) :
    ∃currentParent currentApp currentArg,
      currentFn=currentParent++[.fn] ∧
      target.subterm currentParent=some (.app currentApp (.lam currentLam currentBody) currentArg) ∧
      BetaNodeHistoryPreimage labels currentParent name := by
  generalize oldFnEq : name++[.fn]=oldFn at trace
  induction trace generalizing name oldBody oldArg currentBody oldApp oldLam currentLam with
  | nil =>
    have equal : LTerm.lam oldLam oldBody=.lam currentLam currentBody := by
      rw [←oldFnEq,LTerm.subterm_append,oldRedex] at lookup
      simpa only [LTerm.subterm,Option.bind_some,Option.some.injEq] using lookup
    refine ⟨name,oldApp,oldArg,oldFnEq.symm,?_,.nil _ _⟩
    rw [←equal]
    exact oldRedex
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step rest redex origin tail ih =>
      obtain ⟨middle,atMiddle,_last,constructor⟩:=tail.lastAtom_constructor lookup
      cases middle with
      | var => cases constructor
      | app => cases constructor
      | lam middleLam middleBody =>
        obtain ⟨middleParent,middleApp,middleArg,middleFn,middleLookup,middleOrigin⟩:=
          step.function_preimage_redex_parent redex oldRedex (by simpa only [oldFnEq] using origin) atMiddle
        obtain ⟨parent,app,arg,fnEq,parentLookup,parentTrace⟩:=ih middleLookup lookup middleFn.symm
        exact ⟨parent,app,arg,fnEq,parentLookup,.one (step:=step) (remaining:=rest) redex middleOrigin parentTrace⟩

end Lamping.Lambda.Labelled
#print axioms Lamping.Lambda.Labelled.BetaNodeHistoryPreimage.function_redex_parent

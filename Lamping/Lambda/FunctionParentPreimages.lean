import Lamping.Lambda.UncreatedPrerequisiteReadings
import Lamping.Lambda.ResidualFunctionPreimages

namespace Lamping.Lambda.Labelled

private theorem split_parent {root relative parent : Path}
    (equal : root++relative=parent++[.fn]) (nonempty : relative≠[]) :
    ∃ inside,relative=inside++[.fn] ∧parent=root++inside := by
  rcases List.append_eq_append_iff.mp equal with ⟨inside,parentEq,relativeEq⟩ | ⟨extra,rootEq,childEq⟩
  · exact ⟨inside,relativeEq,parentEq⟩
  · cases extra with
    | nil => exact ⟨[],by simpa only [List.nil_append] using childEq.symm,
        by simpa only [List.append_nil] using rootEq.symm⟩
    | cons head rest =>
      have lengths := congrArg List.length childEq
      have positive : 0<relative.length := List.length_pos_iff.mpr nonempty
      simp only [List.length_cons,List.length_nil,List.length_append] at lengths
      omega

private theorem fn_parent_lookup {target currentBody : LTerm} {parent : Path} {stamp : Label}
    (lookup : target.subterm (parent++[.fn])=some (.lam stamp currentBody)) :
    ∃ appStamp argument,target.subterm parent=some (.app appStamp (.lam stamp currentBody) argument) := by
  rw [LTerm.subterm_append] at lookup
  cases atParent : target.subterm parent with
  | none => rw [atParent] at lookup;cases lookup
  | some node =>
    rw [atParent,Option.bind_some] at lookup
    cases node with
    | var => cases lookup
    | lam => cases lookup
    | app appStamp fn argument =>
      have equal : fn=.lam stamp currentBody := by simpa only [LTerm.subterm,Option.some.injEq] using lookup
      exact ⟨appStamp,argument,by rw [equal]⟩

/-- Actual FUNCTION-lambda ancestry constructs its real redex parent.
The parent lookup is obtained from THIS current FUNCTION lookup; no
current-parent, uncreated, or marked residual oracle is assumed. -/
theorem StepAt.function_preimage_redex_parent
    {source target body argument oldBody oldArgument currentBody : LTerm}
    {site currentFn oldParent : Path}
    {beta alpha oldAppLabel oldLambdaLabel currentLabel : Label}
    (step : StepAt site source target)
    (redex : source.subterm site = some (.app beta (.lam alpha body) argument))
    (oldRedex : source.subterm oldParent =
      some (.app oldAppLabel (.lam oldLambdaLabel oldBody) oldArgument))
    (origin : BetaNodePreimage body argument site currentFn (oldParent ++ [.fn]))
    (lookup : target.subterm currentFn = some (.lam currentLabel currentBody)) :
    ∃ currentParent currentAppLabel currentArgument,
      currentFn = currentParent ++ [.fn] ∧
      target.subterm currentParent =
        some (.app currentAppLabel (.lam currentLabel currentBody) currentArgument) ∧
      BetaNodePreimage body argument site currentParent oldParent := by
  have _actualStep := step
  rcases origin.coordinates with ⟨equal,outside⟩ |
      ⟨relative,old,atCurrent,atOld,oldLookup,nonselected⟩ |
      ⟨q,relative,old,occurs,atCurrent,atOld,oldLookup⟩
  · have parentOutside : ¬∃ r,oldParent=site++r := by
      rintro ⟨r,split⟩
      exact outside ⟨r++[.fn],by simp only [equal,split,List.append_assoc]⟩
    obtain ⟨stamp,arg,parentLookup⟩:=fn_parent_lookup (equal ▸ lookup)
    exact ⟨oldParent,stamp,arg,equal,parentLookup,.context parentOutside⟩
  · have nonempty : relative≠[] := by
      intro empty
      have ends:=congrArg List.getLast? atOld
      simp only [empty,List.append_nil,List.getLast?_append,List.getLast?_cons,
        List.getLast?_nil,Option.some_or] at ends
      cases ends
    obtain ⟨inside,split,parentEq⟩:=split_parent atOld.symm nonempty
    have parentLookup : body.subterm inside=some (.app oldAppLabel (.lam oldLambdaLabel oldBody) oldArgument) := by
      rw [parentEq,List.append_assoc,LTerm.subterm_append,redex] at oldRedex
      simpa only [LTerm.subterm,Option.bind_some] using oldRedex
    have currentEq : currentFn=(site++inside)++[.fn] := by simp only [atCurrent,split,List.append_assoc]
    obtain ⟨stamp,arg,atParent⟩:=fn_parent_lookup (currentEq ▸ lookup)
    refine ⟨site++inside,stamp,arg,currentEq,atParent,?_⟩
    rw [parentEq]
    exact .retained parentLookup (by intro stamp impossible;cases impossible)
  · have nonempty : relative≠[] := by
      intro empty
      have ends:=congrArg List.getLast? atOld
      simp only [empty,List.append_nil,List.getLast?_append,List.getLast?_cons,
        List.getLast?_nil,Option.some_or] at ends
      cases ends
    obtain ⟨inside,split,parentEq⟩:=split_parent atOld.symm nonempty
    have parentLookup : argument.subterm inside=some (.app oldAppLabel (.lam oldLambdaLabel oldBody) oldArgument) := by
      rw [parentEq,List.append_assoc,LTerm.subterm_append,redex] at oldRedex
      simpa only [LTerm.subterm,Option.bind_some] using oldRedex
    have currentEq : currentFn=((site++q)++inside)++[.fn] := by simp only [atCurrent,split,List.append_assoc]
    obtain ⟨stamp,arg,atParent⟩:=fn_parent_lookup (currentEq ▸ lookup)
    refine ⟨(site++q)++inside,stamp,arg,currentEq,atParent,?_⟩
    rw [parentEq]
    exact .copied occurs parentLookup

end Lamping.Lambda.Labelled
#print axioms Lamping.Lambda.Labelled.StepAt.function_preimage_redex_parent

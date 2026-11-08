import Lamping.Lambda.ArgumentCopies
import Lamping.Lambda.PrerequisiteChains
namespace Lamping.Lambda.Labelled
variable {source body argument : LTerm} {site q parent : Path}
variable {beta alpha stamp : Label}

theorem bound_leaf_prerequisite (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (leaf : body.subterm q=some (.var stamp (binderDepth q))) :
    PrerequisiteChain source (site++[.fn,.body]++q) [site++[.fn]] := by
  apply PrerequisiteChain.var (parent := site++[.fn]) (rest := q)
  · rw [List.append_assoc,LTerm.subterm_append,redex]
    simpa only [LTerm.subterm,Option.bind_some] using leaf
  · rw [LTerm.subterm_append,redex]; rfl
  · simp only [List.append_assoc,List.cons_append,List.nil_append]
  · rfl
  · exact .redex_lam redex

theorem substituted_function_prerequisite
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (parentLookup : body.subterm parent=some (.app stamp (.var variableStamp (binderDepth (parent++[.fn]))) sibling)) :
    PrerequisiteChain source (site++[.fn,.body]++parent)
      [site++[.fn,.body]++(parent++[.fn]),site++[.fn]] := by
  have leaf : body.subterm (parent++[.fn])=some (.var variableStamp (binderDepth (parent++[.fn]))) := by
    rw [LTerm.subterm_append,parentLookup]; rfl
  have tail : PrerequisiteChain source ((site++[.fn,.body]++parent)++[.fn]) [site++[.fn]] := by
    simpa only [List.append_assoc] using bound_leaf_prerequisite redex leaf
  have globalParent : source.subterm (site++[.fn,.body]++parent)=
      some (.app stamp (.var variableStamp (binderDepth (parent++[.fn]))) sibling) := by
    rw [List.append_assoc,LTerm.subterm_append,redex]
    simpa only [LTerm.subterm,Option.bind_some] using parentLookup
  simpa only [List.append_assoc] using
    (PrerequisiteChain.app globalParent (by intro l b impossible; cases impossible) tail)

theorem copied_lambda_prerequisite
    (redex : source.subterm site=some (.app beta (.lam alpha body) (.lam stamp inner))) :
    PrerequisiteChain source (site++[.arg]) [site++[.arg],site++[.fn]] := by
  apply PrerequisiteChain.lam (parent := site) (step := .arg)
  · rw [LTerm.subterm_append,redex]; rfl
  · decide
  · exact .redex_app redex

theorem result_lambda_prerequisite
    (redex : source.subterm site=some (.app beta (.lam alpha (.lam stamp inner)) argument)) :
    PrerequisiteChain source (site++[.fn,.body]) [site++[.fn,.body],site++[.fn]] := by
  have bodyLookup : source.subterm ((site++[.fn])++[.body])=some (.lam stamp inner) := by
    rw [LTerm.subterm_append,LTerm.subterm_append,redex]; rfl
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using
    (PrerequisiteChain.lam bodyLookup (by decide : Step.body≠Step.fn) (.redex_lam redex))
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Labelled
/-- A redex occurring as an actual function child has an old application
prerequisite prefix through that incoming edge and its own redex edge. -/
theorem result_function_old_chain
    (redex : source.subterm (parent++[.fn])=some (.app beta (.lam alpha body) argument)) :
    PrerequisiteChain source parent [parent++[.fn],(parent++[.fn])++[.fn]] := by
  rw [LTerm.subterm_append] at redex
  cases atParent : source.subterm parent with
  | none => rw [atParent] at redex; cases redex
  | some old =>
    rw [atParent,Option.bind_some] at redex
    cases old with
    | var => cases redex
    | lam => cases redex
    | app stamp fn arg =>
      have same : fn=.app beta (.lam alpha body) argument := by
        simpa only [LTerm.subterm,Option.some.injEq] using redex
      subst fn
      apply PrerequisiteChain.app atParent
      · intro l b impossible; cases impossible
      · exact .redex_app (by rw [LTerm.subterm_append,atParent]; rfl)

/-- Actual variable occurrence at a function edge supplies its old parent
shape; callers do not have to package that shape as an origin certificate. -/
theorem substituted_function_old_chain
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase (parent++[.fn])) :
    PrerequisiteChain source (site++[.fn,.body]++parent)
      [site++[.fn,.body]++(parent++[.fn]),site++[.fn]] := by
  change subtermAt body.erase (parent++[.fn])=some (.var (binderDepth (parent++[.fn]))) at occurs
  rw [subtermAt_append,←LTerm.erase_subterm] at occurs
  cases atParent : body.subterm parent with
  | none => rw [atParent] at occurs; cases occurs
  | some old =>
    rw [atParent,Option.map_some,Option.bind_some] at occurs
    cases old with
    | var => cases occurs
    | lam => cases occurs
    | app stamp fn arg =>
      cases fn with
      | app => cases occurs
      | lam => cases occurs
      | var variableStamp index =>
        have equal : index=binderDepth (parent++[.fn]) := by
          simpa only [LTerm.erase,subtermAt,Option.some.injEq,Term.var.injEq] using occurs
        subst index
        exact substituted_function_prerequisite redex atParent
end Lamping.Lambda.Labelled



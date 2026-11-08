import Lamping.Lambda.SubstitutionPositionOrigins
namespace Lamping.Lambda
/-- All actual beta-contractum positions: retained nonvariable body syntax,
a retained body variable not bound by this beta, or one actual argument
instance with its exact lifted argument-relative path. -/
theorem subtermAt_contract_origins {body argument target : Term} {p : Path}
    (lookup : subtermAt (contract body argument) p=some target) :
    (∃ old,subtermAt body p=some old ∧ (∀ k,old≠.var k) ∧
      target=subst (liftSubN (binderDepth p) (singleSub argument)) old) ∨
    (∃ k j,subtermAt body p=some (.var k) ∧ k≠binderDepth p ∧
      liftSubN (binderDepth p) (singleSub argument) k=.var j ∧ target=.var j) ∨
    (∃ q r,p=q++r ∧ ArgumentOccurrence body q ∧
      subtermAt (rename (fun i => i+binderDepth q) argument) r=some target) := by
  rcases subtermAt_subst_origins lookup with retained | ⟨q,r,k,split,atVariable,replacement⟩
  · exact Or.inl retained
  · by_cases isArgument : k=binderDepth q
    · right; right
      refine ⟨q,r,split,?_,?_⟩
      · simpa only [ArgumentOccurrence,isArgument] using atVariable
      · rw [isArgument,liftSubN_self] at replacement
        exact replacement
    · obtain ⟨j,atLift⟩ := liftSingle_other (binderDepth q) k argument isArgument
      rw [atLift] at replacement
      have suffixEmpty : r=[] := (variable_descendant_lookup
        (show subtermAt (.var j) []=some (.var j) from rfl) replacement).1
      subst r
      simp only [List.append_nil] at split
      subst p
      exact Or.inr (Or.inl ⟨k,j,atVariable,isArgument,atLift,(Option.some.inj replacement).symm⟩)
/-- An actual argument occurrence and a position in its correctly renamed
copy reconstruct the target position, including the empty/root-copy suffix. -/
theorem subtermAt_contract_from_argument {body argument target : Term} {q r : Path}
    (occurs : ArgumentOccurrence body q)
    (copyLookup : subtermAt (rename (fun i => i+binderDepth q) argument) r=some target) :
    subtermAt (contract body argument) (q++r)=some target := by
  rw [subtermAt_append,argument_copy occurs argument,Option.bind_some]
  exact copyLookup
/-- The copy and relative position are unique for one actual target path;
this permits duplication at different paths, and does not select arbitrary copies. -/
theorem contract_argument_origin_unique {body : Term} {q r other suffix : Path}
    (first : ArgumentOccurrence body q) (second : ArgumentOccurrence body other)
    (split : q++r=other++suffix) : q=other ∧ r=suffix :=
  (variable_origin_prefix_unique first second split).imp_right And.left
/-- An old variable not bound by this beta cannot be reassigned to an
argument-copy origin of that same target position. -/
theorem retained_variable_not_argument_origin {body : Term} {p q r : Path} {k : Nat}
    (atOld : subtermAt body p=some (.var k)) (notBound : k≠binderDepth p)
    (occurs : ArgumentOccurrence body q) (split : p=q++r) : False := by
  have unique := variable_origin_prefix_unique atOld occurs
    (show p++[]=q++r by simpa only [List.append_nil] using split)
  exact notBound (by simpa only [←unique.1] using unique.2.2)
end Lamping.Lambda



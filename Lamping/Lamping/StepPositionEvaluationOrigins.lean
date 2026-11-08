import Lamping.Lambda.BetaBoundVariableOrigins
import Lamping.Lamping.ContextualSourceEvaluation
import Lamping.Lambda.ContractumPositionOrigins
namespace Lamping.Lambda.Labelled
open LTerm
/-- Option definedness depends only on the literal syntax path, even when
an atom's selected physical word is empty outside its legitimate domain. -/
private theorem trail_isSome {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (t : LTerm) (p : Path) :
    (t.sourceTrail atoms overWord underWord p).isSome=(t.subterm p).isSome := by
  induction p generalizing t with
  | nil => cases t <;> rfl
  | cons step rest ih => cases t <;> cases step <;> simp only [sourceTrail,LTerm.subterm,Option.isSome_map,Option.isSome_none,ih]

/-- Every actual target position either has the SAME whole evaluated word
as a real old position, or lies in one specified actual argument copy.
Outside includes strict ancestors, whose subterm may change internally. -/
theorem StepAt.sourceTrail_position_origins {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {site position : Path} {source target body argument sub : LTerm} {beta alpha : Label}
    (step : StepAt site source target)
    (lookup : source.subterm site=some (.app beta (.lam alpha body) argument))
    (active : alpha.sourceWord atoms overWord underWord=overWord)
    (targetLookup : target.subterm position=some sub) :
    (∃ oldPosition oldSub,source.subterm oldPosition=some oldSub ∧
      target.sourceTrail atoms overWord underWord position=source.sourceTrail atoms overWord underWord oldPosition) ∨
    (∃ q r argSub,position=site++(q++r) ∧ ArgumentOccurrence body.erase q ∧ argument.subterm r=some argSub) := by
  classical
  by_cases below : ∃ p,position=site++p
  · obtain ⟨p,split⟩ := below
    subst position
    have localLookup : (LTerm.contract beta alpha body argument).subterm p=some sub := by
      rw [LTerm.subterm_append,step.contractum_at_site lookup,Option.bind_some] at targetLookup
      exact targetLookup
    have bareLookup : subtermAt (Lambda.contract body.erase argument.erase) p=some sub.erase := by
      rw [←erase_contract,←erase_subterm,localLookup]
      rfl
    rcases subtermAt_contract_origins bareLookup with ⟨old,oldLookup,nonvar,_⟩ |
      ⟨index,j,oldLookup,other,_,_⟩ | ⟨q,r,path,occurs,copyLookup⟩
    · have liftedLookup : (body.subterm p).map LTerm.erase=some old := by rw [erase_subterm]; exact oldLookup
      obtain ⟨oldSub,oldAt,oldShape⟩ := Option.map_eq_some_iff.mp liftedLookup
      refine Or.inl ⟨site++(.fn::.body::p),oldSub,?_,?_⟩
      · rw [LTerm.subterm_append,lookup,Option.bind_some]
        exact oldAt
      · apply step.sourceTrail_retained_nonvariable atoms overWord underWord lookup active oldAt
        intro stamp k equal
        exact nonvar k (oldShape.symm.trans (congrArg LTerm.erase equal))
    · have liftedLookup : (body.subterm p).map LTerm.erase=some (.var index) := by rw [erase_subterm]; exact oldLookup
      obtain ⟨oldSub,oldAt,_⟩ := Option.map_eq_some_iff.mp liftedLookup
      refine Or.inl ⟨site++(.fn::.body::p),oldSub,?_,?_⟩
      · rw [LTerm.subterm_append,lookup,Option.bind_some]
        exact oldAt
      · exact step.sourceTrail_retained_variable atoms overWord underWord lookup active oldLookup other
    · rw [subtermAt_rename] at copyLookup
      obtain ⟨oldBare,atBare,_⟩ := Option.map_eq_some_iff.mp copyLookup
      have liftedLookup : (argument.subterm r).map LTerm.erase=some oldBare := by rw [erase_subterm]; exact atBare
      obtain ⟨argSub,atArgument,_⟩ := Option.map_eq_some_iff.mp liftedLookup
      exact Or.inr ⟨q,r,argSub,congrArg (site++·) path,occurs,atArgument⟩
  · have wordEq := step.sourceTrail_outside atoms overWord underWord position below
    obtain ⟨word,currentWord⟩ := sourceTrail_exists atoms overWord underWord targetLookup
    have oldValid : (source.subterm position).isSome=true := by
      rw [←trail_isSome atoms overWord underWord,←wordEq,currentWord]
      rfl
    cases atOld : source.subterm position with
    | none => rw [atOld] at oldValid; cases oldValid
    | some oldSub => exact Or.inl ⟨position,oldSub,atOld,wordEq⟩
/-- A genuinely disjoint edit preserves the COMPLETE labelled subtree.
This requires disjointness, unlike the evaluated-word theorem for ancestors. -/
theorem StepAt.disjoint_subterm (step : StepAt site source target)
    (apart : DisjointPositions site position) : target.subterm position=source.subterm position := by
  induction step generalizing position with
  | root => exact False.elim (DisjointPositions.nil_left apart)
  | fn step ih =>
    cases position with
    | nil => exact False.elim (DisjointPositions.nil_right apart)
    | cons child rest => cases child with
      | body | arg => rfl
      | fn => exact ih apart.child
  | arg step ih =>
    cases position with
    | nil => exact False.elim (DisjointPositions.nil_right apart)
    | cons child rest => cases child with
      | body | fn => rfl
      | arg => exact ih apart.child
  | body step ih =>
    cases position with
    | nil => exact False.elim (DisjointPositions.nil_right apart)
    | cons child rest => cases child with
      | fn | arg => rfl
      | body => exact ih apart.child
/-- A current leaf bound by the retained outer lambda either inherits a
real old bound-leaf word, or is in a specified copy of an old argument
leaf bound by that same outer lambda. All coordinate premises are derived. -/
theorem StepAt.outer_bound_variable_evaluation_origins {X : Type}
    (atoms : Nat → List X) (overWord underWord : List X)
    {site position : Path} {source target body argument : LTerm} {beta alpha : Label}
    (step : StepAt site source target)
    (lookup : source.subterm site=some (.app beta (.lam alpha body) argument))
    (active : alpha.sourceWord atoms overWord underWord=overWord)
    (leaf : ArgumentOccurrence target.erase position) :
    (∃ oldPosition,ArgumentOccurrence source.erase oldPosition ∧
      target.sourceTrail atoms overWord underWord position=source.sourceTrail atoms overWord underWord oldPosition) ∨
    (∃ q r,position=site++(q++r) ∧ ArgumentOccurrence body.erase q ∧
      subtermAt argument.erase r=some (.var (binderDepth site+binderDepth r))) := by
  have redex : subtermAt source.erase site=some (.app (.lam body.erase) argument.erase) := by
    rw [←erase_subterm,lookup]
    rfl
  rcases step.betaAt.all_outer_bound_variable_sources redex leaf with ⟨apart,oldLeaf⟩ | ⟨p,path,inside⟩
  · exact Or.inl ⟨position,oldLeaf,step.sourceTrail_outside atoms overWord underWord position apart.1⟩
  · subst position
    rcases inside with retained | ⟨q,r,split,occurs,argLeaf,_⟩
    · have oldBody : subtermAt body.erase p=some (.var (binderDepth (site++p)+1)) := by
        simpa only [List.append_assoc,subtermAt_append,redex,Option.bind_some,subtermAt] using retained
      refine Or.inl ⟨site++(.fn::.body::p),?_,?_⟩
      · change subtermAt source.erase (site++(.fn::.body::p))=some (.var (binderDepth (site++(.fn::.body::p))))
        simpa only [List.append_assoc,binderDepth_append,binderDepth,Nat.add_assoc,Nat.add_right_comm] using retained
      · exact step.sourceTrail_retained_variable atoms overWord underWord lookup active oldBody (by
          rw [binderDepth_append]
          omega)
    · exact Or.inr ⟨q,r,congrArg (site++·) split,occurs,argLeaf⟩
end Lamping.Lambda.Labelled

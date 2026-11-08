import Lamping.Lamping.RootInputAccessGeometry
import Lamping.Lamping.MatchingSubtermAccess
import Lamping.Lamping.MatchingInitial

namespace Lamping.AG
open Graph Lambda

private theorem child_exists_of_parent_kind {kind : Kind} {ctx child : Port kind}
    {step : Step} (roles : SyntaxChildPorts kind ctx child step) (u : Term)
    (parentKind : portKind kind ctx=some (syntaxShape u).kind) :
    ∃ v,subtermAt u [step]=some v := by
  cases roles <;> cases u <;>
    simp_all [portKind,syntaxShape,AccessShape.kind,subtermAt,appCtx]

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {t : Term}

/-- Full forward observation coverage classifies EVERY existing root access.
The induction cuts the last syntax token of the supplied finite path; it
never extends a partial path. RootInputs only aligns two existing accesses
at one common input for literal word injectivity. -/
theorem RootInputs.classify_of_observation_coverage (inputs : RootInputs g root)
    (coverage : ∀ position : Position t,∃ access : RootAccess g root,Corresponds g access.val t position)
    (access : RootAccess g root) :
    ∃ u,subtermAt t (accessWord g access.val)=some u ∧Observes g access.val (syntaxShape u) := by
  have classify : ∀ reverse : Path,∀ access : RootAccess g root,
      accessWord g access.val=reverse.reverse →
      ∃ u,subtermAt t reverse.reverse=some u ∧Observes g access.val (syntaxShape u) := by
    intro reverse
    induction reverse with
    | nil =>
      intro actual word
      let rootPosition : Position t := ⟨[],by cases t <;> rfl⟩
      obtain ⟨covered,coveredWord,u,lookup,observed⟩ := coverage rootPosition
      have same : actual=covered := inputs.accessWord_injective (word.trans coveredWord.symm)
      exact ⟨u,lookup,by simpa only [same] using observed⟩
    | cons step reverse ih =>
      intro actual word
      have whole : accessWord g actual.val=reverse.reverse++[step] := by
        simpa only [List.reverse_cons] using word
      obtain ⟨parent,node,ctx,child,tail,roles,parentWord,finish,_split⟩ :=
        actual.before_syntax_token reverse.reverse step whole
      obtain ⟨u,parentLookup,parentObserved⟩ := ih parent parentWord
      have parentKind := parentObserved.1
      have childExists : ∃ v,subtermAt u [step]=some v := by
        unfold accessKind at parentKind
        rw [finish] at parentKind
        simp only [Option.bind_some,Pairing.involutive] at parentKind
        exact child_exists_of_parent_kind roles u parentKind
      obtain ⟨v,childLookup⟩ := childExists
      have lookup : subtermAt t (reverse.reverse++[step])=some v := by
        rw [subtermAt_append,parentLookup,Option.bind_some]
        exact childLookup
      let position : Position t := ⟨reverse.reverse++[step],by rw [lookup]; rfl⟩
      obtain ⟨covered,coveredWord,w,coveredLookup,observed⟩ := coverage position
      have same : actual=covered := inputs.accessWord_injective (whole.trans coveredWord.symm)
      have termSame : w=v := Option.some.inj (coveredLookup.symm.trans lookup)
      refine ⟨v,?_,?_⟩
      · simpa only [List.reverse_cons] using lookup
      · simpa only [same,termSame] using observed
  simpa only [List.reverse_reverse] using
    classify (accessWord g access.val).reverse access (by rw [List.reverse_reverse])

/-- Uniform root inputs and full forward observation coverage suffice for
Matches. Backward coverage is derived by cutting existing accesses, not
assumed, and no graph reachability or general path completion is used. -/
theorem RootInputs.matches_of_observation_coverage (inputs : RootInputs g root)
    (coverage : ∀ position : Position t,∃ access : RootAccess g root,Corresponds g access.val t position) :
    Matches g root t := by
  apply matches_of_access_classification g root t
  · exact inputs.classify_of_observation_coverage coverage
  · intro position
    obtain ⟨access,word,_lookup⟩ := coverage position
    exact ⟨access,word⟩
  · exact fun first second word => inputs.accessWord_injective word

end
end Lamping.AG

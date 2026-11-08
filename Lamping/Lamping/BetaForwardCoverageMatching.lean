import Lamping.Lamping.RootObservationCoverage
import Lamping.Lamping.RootBindingSuffixUniqueness
import Lamping.Lamping.RootBetaInputs
import Lamping.Lamping.IndexedBetaTransparency
import Lamping.Lamping.GraphIndexedBalance
namespace Lamping.AG
open Graph Lambda

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {t : Term}

/-- Actual kind coverage with an actual variable suffix needs no assumed
uniqueness: root inputs, nesting and transparency select its unique index. -/
theorem RootInputs.matches_of_kind_binding_coverage
    (inputs : RootInputs g root) (nesting : Nesting g root)
    (transparency : Transparency g root)
    (coverage : ∀ position : Position t, ∃ (access : RootAccess g root) (u : Term),
      subtermAt t position.val=some u ∧ accessWord g access.val=position.val ∧
      accessKind g access.val=some (syntaxShape u).kind ∧
      (match u with | .var k => BindingSuffix g access.val k | _ => True)) :
    Matches g root t := by
  apply inputs.matches_of_observation_coverage
  intro position
  obtain ⟨access,u,lookup,word,kind,suffix⟩ := coverage position
  refine ⟨access,word,u,lookup,kind,?_⟩
  cases u with
  | var k =>
    exact ⟨suffix,fun j other =>
      inputs.binding_suffix_unique nesting transparency access other suffix⟩
  | lam body => trivial
  | app fn arg => trivial
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}

/-- A canonical beta rule derives the target root and binding invariants.
The remaining hypothesis is explicit forward geometry: every target syntax
position has an actual access of its kind, and variable positions have an
actual binding suffix. No target Matches or suffix uniqueness is assumed. -/
theorem PathSite.beta_matches_of_kind_binding_coverage
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {boundary : B → Bool} {heights : B → Int}
    (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs site.net root) (transparency : Transparency site.net root)
    (t : Term)
    (coverage : ∀ position : Position t, ∃ (access : RootAccess site.reduce root) (u : Term),
      subtermAt t position.val=some u ∧ accessWord site.reduce access.val=position.val ∧
      accessKind site.reduce access.val=some (syntaxShape u).kind ∧
      (match u with | .var k => BindingSuffix site.reduce access.val k | _ => True)) :
    Matches site.reduce root t := by
  have targetInputs := site.beta_rootInputs flow root positive balance rootDepth inputs transparency
  obtain ⟨targetBalance⟩ := site.reduce_indexed_balance balance
  have targetNesting := targetBalance.nesting root rootDepth
  have targetTransparency := site.beta_transparency_indexed flow root positive balance rootDepth transparency
  exact targetInputs.matches_of_kind_binding_coverage targetNesting targetTransparency coverage
end
end Lamping.AG

import Lamping.Lamping.ActionBindingAccess
import Lamping.Lamping.RootActionTypedInputs
import Lamping.Lamping.RootBindingSuffixUniqueness
import Lamping.Lamping.ActionTransparency
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Every actual target access observes the same source syntax, including
the de Bruijn index. This is the backward classification half of Matches;
forward coverage is a separate obligation. Target invariants are derived
from the real rule, not supplied as correctness fields. -/
theorem PathSite.action_access_classification (action : IsAction s)
    {directions : B → Bool} {heights : B → Int} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs site.net root) (oldT : Transparency site.net root)
    {t : Term} (matching : Matches site.net root t) (target : RootAccess site.reduce root) :
    ∃ u,subtermAt t (accessWord site.reduce target.val)=some u ∧
      Observes site.reduce target.val (syntaxShape u) := by
  have newInputs := site.action_rootInputs action flow root positive balance rootDepth matching inputs oldT
  obtain ⟨newBalance⟩ := site.reduce_indexed_balance balance
  have newN := newBalance.nesting root rootDepth
  have newT := site.action_transparency action flow root positive oldT
  obtain ⟨map,corresponds,_prefix⟩ := matching
  obtain ⟨kind,observedKind⟩ := target.property.2.2
  cases kind with
  | app =>
    obtain ⟨source,word,kind⟩ := site.action_root_access_backward action flow root positive target
    obtain ⟨sourceWord,u,lookup,observed⟩ := corresponds source
    have lookupTarget : subtermAt t (accessWord site.reduce target.val)=some u := by
      rw [←word,sourceWord]; exact lookup
    have sameKind : (syntaxShape u).kind=.app :=
      Option.some.inj (observed.1.symm.trans (kind.trans observedKind))
    cases u with
    | var index => cases sameKind
    | lam body => cases sameKind
    | app fn arg => exact ⟨_,lookupTarget,observedKind,trivial⟩
  | lam =>
    obtain ⟨source,word,kind⟩ := site.action_root_access_backward action flow root positive target
    obtain ⟨sourceWord,u,lookup,observed⟩ := corresponds source
    have lookupTarget : subtermAt t (accessWord site.reduce target.val)=some u := by
      rw [←word,sourceWord]; exact lookup
    have sameKind : (syntaxShape u).kind=.lam :=
      Option.some.inj (observed.1.symm.trans (kind.trans observedKind))
    cases u with
    | var index => cases sameKind
    | app fn arg => cases sameKind
    | lam body => exact ⟨_,lookupTarget,observedKind,trivial⟩
  | var =>
    obtain ⟨source,word,kind,index,sourceSuffix,targetSuffix⟩ :=
      site.action_variable_binding_access action flow root positive oldT target observedKind
    obtain ⟨sourceWord,u,lookup,observed⟩ := corresponds source
    have lookupTarget : subtermAt t (accessWord site.reduce target.val)=some u := by
      rw [←word,sourceWord]; exact lookup
    have sameKind : (syntaxShape u).kind=.var :=
      Option.some.inj (observed.1.symm.trans (kind.trans observedKind))
    cases u with
    | app fn arg => cases sameKind
    | lam body => cases sameKind
    | var sourceIndex =>
      have indices : index=sourceIndex := observed.2.2 index sourceSuffix
      subst index
      refine ⟨_,lookupTarget,observedKind,targetSuffix,?_⟩
      intro other suffix
      exact newInputs.binding_suffix_unique newN newT target suffix targetSuffix
end
end Lamping.AG

import Lamping.Lamping.ActionSyntaxObservationKinds
import Lamping.Lamping.ChainFragmentUniqueness
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Actual typed lambda access has exactly a kept port or a copied context. -/
theorem PathSite.fan_lambda_access_cases {root : B} (path : RootAccess site.reduce root)
    (typed : accessKind site.reduce path.val=some .lam) :
    (∃port : NodePort signature K kept,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∨
    (∃branch : Bool,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩))) := by
  rcases site.action_access_node_cases (.fan .lam i j lt) path with kept |⟨node,port,passive,finish⟩
  · exact Or.inl kept
  · cases passive with
    | fan branch =>
      have actual := accessKind_at_actual_finish typed (.inr (.inl branch)) port finish
      cases port with
      | inl u => cases u;exact Or.inr ⟨branch,finish⟩
      | inr aux => cases aux <;> cases actual
end
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
/-- A real lookup and THIS actual access word determine its lambda kind. -/
theorem Matches.lambda_access_typed (matching : Matches g root current.erase)
    (lookup : current.subterm p=some (.lam stamp body))
    (path : RootAccess g root) (word : accessWord g path.val=p) :
    accessKind g path.val=some .lam := by
  let pos : Position current.erase := ⟨p,by rw [←LTerm.erase_subterm,lookup];rfl⟩
  obtain ⟨observed,observedWord,sub,observedLookup,observes⟩ := Matches.observation g matching pos
  have erased : subtermAt current.erase p=some (.lam body.erase) := by
    rw [←LTerm.erase_subterm,lookup];rfl
  have subEq : sub=.lam body.erase := Option.some.inj (observedLookup.symm.trans erased)
  subst sub
  have same : path=observed := matching.accessWord_injective (word.trans observedWord.symm)
  rw [same]
  exact observes.1
end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_lambda_access_cases
#print axioms Lamping.AG.Matches.lambda_access_typed

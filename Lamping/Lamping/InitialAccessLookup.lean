import Lamping.Lamping.InitialAccessPrefix
namespace Lamping.AG
open Graph Lambda
/-- Retain the exact endpoint kind as well as the address in closed coverage. -/
theorem encode_closed_position_access (t : Term) (closed : Closed t) (n : Nat)
    (address : Path) (u : Term) (lookup : subtermAt t address=some u) (input : Context) :
    Nonempty (EncodedAccess t n address (syntaxShape u).kind input) := by
  cases u with
  | var k =>
    have scope := scoped_subterm closed lookup
    change k<0+binderDepth address at scope
    exact encode_boundvar_access t n address k lookup (by simpa only [Nat.zero_add] using scope) input
  | app f arg => exact encode_nonvar_access t n address (.app f arg) lookup (by intro same; cases same) input
  | lam body => exact encode_nonvar_access t n address (.lam body) lookup (by intro same; cases same) input

private theorem first_invalid_step (t : Term) (address : Path)
    (invalid : subtermAt t address=none) :
    ∃ pre s rest u,address=pre++s::rest ∧subtermAt t pre=some u ∧subtermAt u [s]=none := by
  induction address generalizing t with
  | nil => cases t <;> cases invalid
  | cons s rest ih =>
    cases child : subtermAt t [s] with
    | none => exact ⟨[],s,rest,t,rfl,(by cases t <;> rfl),child⟩
    | some v =>
      have after : subtermAt v rest=none := by
        have h := subtermAt_append t [s] rest
        rw [child] at h
        exact h.symm.trans invalid
      obtain ⟨pre,next,tail,u,eq,lookup,bad⟩ := ih v after
      refine ⟨s::pre,next,tail,u,congrArg (s::·) eq,?_,bad⟩
      have h := subtermAt_append t [s] pre
      rw [child] at h
      exact h.trans lookup

private theorem allowed_lookup (u : Term) (s : Step) (allowed : (syntaxShape u).kind.allows s) :
    ∃ child,subtermAt u [s]=some child := by
  cases u <;> cases s <;> simp_all [syntaxShape,AccessShape.kind,AccessKind.allows,subtermAt]

/-- There are no extra invalid syntax addresses among genuine root accesses
of a closed initial translation. Coverage alone is not the argument: physical
prefix reflection and the actual next proper-node turn rule exclude them. -/
theorem encode_closed_access_lookup (t : Term) (closed : Closed t) (n : Nat)
    (es : RootAccess (encode n t).net (.inl ())) :
    ∃ u,subtermAt t (accessWord (encode n t).net es.val)=some u ∧
      accessKind (encode n t).net es.val=some (syntaxShape u).kind := by
  have valid : (subtermAt t (accessWord (encode n t).net es.val)).isSome := by
    cases lookup : subtermAt t (accessWord (encode n t).net es.val) with
    | some u => rfl
    | none =>
      obtain ⟨pre,s,rest,u,eq,present,bad⟩ := first_invalid_step t _ lookup
      obtain ⟨witness⟩ := encode_closed_position_access t closed n pre u present Context.empty
      have allowed := encode_access_extension_token t n witness.rootAccess es s rest
        (eq.trans (congrArg (fun p => p++s::rest) witness.word.symm))
        (syntaxShape u).kind witness.terminal
      obtain ⟨child,childEq⟩ := allowed_lookup u s allowed
      rw [bad] at childEq
      cases childEq
  obtain ⟨u,lookup⟩ := Option.isSome_iff_exists.mp valid
  obtain ⟨witness⟩ := encode_closed_position_access t closed n _ u lookup Context.empty
  have same : es=witness.rootAccess := encode_accessWord_injective t n witness.word.symm
  exact ⟨u,lookup,by rw [same]; exact witness.terminal⟩
end Lamping.AG

import Lamping.Lamping.InitialBoundObservations
import Lamping.Lamping.MatchingInitial
namespace Lamping.AG
open Graph Lambda
/-- The binder witness constructed from a closed syntax position agrees with
any actual initial root access at that address, by physical word injectivity. -/
theorem encode_closed_var_observes (t : Term) (closed : Closed t) (n : Nat)
    (es : RootAccess (encode n t).net (.inl ())) (k : Nat)
    (lookup : subtermAt t (accessWord (encode n t).net es.val)=some (.var k)) :
    Observes (encode n t).net es.val (.var k) := by
  have scope := scoped_subterm closed lookup
  change k<0+binderDepth (accessWord (encode n t).net es.val) at scope
  obtain ⟨ss,raw,rooted,tokens,kind⟩ := initial_bound_binding_access t n _ k lookup
    (by simpa only [Nat.zero_add] using scope)
  have binding := raw.binding t n
  have proper := BindingSuffix.labelling (encode n t).net binding
  let target : RootAccess (encode n t).net (.inl ()) :=
    ⟨ss,⟨⟨proper,encode_root_forward t n ss rooted proper⟩,rooted,.var,kind⟩⟩
  have word : accessWord (encode n t).net target.val=accessWord (encode n t).net es.val :=
    (accessTokens_eq_accessWord _ (.inl ()) rooted).symm.trans tokens
  have same : target=es := encode_accessWord_injective t n word
  have targetBinding : BindingSuffix (encode n t).net target.val k := binding
  have targetKind : accessKind (encode n t).net target.val=some .var := kind
  rw [same] at targetBinding targetKind
  exact encode_observes_var_of_suffix t n targetKind targetBinding

/-- Every physical access of a closed initial translation has its actual
syntax node and binding-occurrence observation. No Matches premise is used. -/
theorem encode_closed_access_observes (t : Term) (closed : Closed t) (n : Nat)
    (es : RootAccess (encode n t).net (.inl ())) :
    ∃ u,subtermAt t (accessWord (encode n t).net es.val)=some u ∧
      Observes (encode n t).net es.val (syntaxShape u) := by
  obtain ⟨u,lookup,kind⟩ := encode_closed_access_lookup t closed n es
  refine ⟨u,lookup,?_⟩
  cases u with
  | app f arg => exact ⟨kind,True.intro⟩
  | lam body => exact ⟨kind,True.intro⟩
  | var k => exact encode_closed_var_observes t closed n es k lookup

/-- The actual initial translation of every closed term matches its complete
syntax tree, with actual variable binding occurrences and prefix order.
This establishes the initial case only, not preservation under graph rewrites. -/
theorem encode_closed_matches (t : Term) (closed : Closed t) (n : Nat) :
    Matches (encode n t).net (.inl ()) t :=
  encode_matches_of_access_classification t n (encode_closed_access_observes t closed n)
    (fun p => encode_closed_access_coverage t closed n p Context.empty)
end Lamping.AG

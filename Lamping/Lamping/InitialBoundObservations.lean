import Lamping.Lamping.BindingSuffixEmbeddings
namespace Lamping.AG
open Graph Lambda
private theorem lambda_entry {i : Nat} {q : Port (.op .lam)}
    (rule : Traversal i (.op .lam) (.inl ()) q a b) : q=lamBody ∧a=b := by
  have direct := rule.direct_of_polarity rfl
  exact ⟨direct.forward_ports.2,rule.proper_context⟩
/-- A specified free occurrence of index zero in a lambda body supplies the
actual outer binding suffix, including its full child and both seam segments. -/
theorem initial_new_binding_access (body : Term) (occ : InitialOffsets.FreeOccurrence body 0) (n : Nat) :
    ∃ es : List (Endpoint (encode n (.lam body)).net),
      RawBindingSuffix (encode n (.lam body)).net es (binderDepth occ.path) ∧
      es.head?=some (.inr (.inl (.inl ()))) ∧
      accessTokens (encode n (.lam body)).net es=.body::occ.path ∧
      accessKind (encode n (.lam body)).net es=some .var := by
  have used : free body 0 := occ.free
  obtain ⟨output,child,childWord⟩ := occ.realized n Context.empty
  dsimp only [encode]
  rw [dif_pos used]
  let c := lambdaUsed n body used
  let r := (encode n body).net
  let g := plug c r
  obtain ⟨es,labels,rooted,tokens,last⟩ :=
    LocalPath.enter_return c r (initialLambdaUsedBody n body used Context.empty) child
  have fullWord : accessTokens g es=.body::occ.path := by rw [tokens,childWord]; rfl
  have terminal : accessKind g es=some .var := by unfold accessKind; rw [last]; rfl
  refine ⟨es,?_,rooted,fullWord,terminal⟩
  cases labels with
  | single e a =>
    have same : e=.inr (.inl (.inl ())) := Option.some.inj rooted
    subst e
    cases last
  | @cons e f tail a b d turn after =>
    have same : e=.inr (.inl (.inl ())) := Option.some.inj rooted
    subst e
    change LabelledTurn g (.inl ⟨.inl (),.inl ()⟩) f Context.empty b at turn
    cases turn with
    | node node p q rule =>
      obtain ⟨port,context⟩ := lambda_entry (q:=q) rule
      subst q
      subst b
      have loopWord : accessWord g (.inl ⟨.inl (),lamBody⟩::tail)=occ.path := by
        change Step.body::(tail.flatMap (arrivalWord g))=Step.body::occ.path at fullWord
        exact (List.cons.inj fullWord).2
      let raw : InitialOffsets.RawLoop g (.inl ⟨.inl (),lamBody⟩::tail) Context.empty output := {
        binder := .inl ()
        isLam := rfl
        body := lamBody
        bind := lamBind
        body_role := HEq.rfl
        bind_role := HEq.rfl
        start := rfl
        finish := by simpa only [List.getLast?_cons_cons] using last
        proper := after }
      refine ⟨[.inr (.inl (.inl ()))],.inl ⟨.inl (),lamBody⟩::tail,Context.empty,Context.empty,output,raw,.inl (),rfl,HEq.rfl,rfl,.single _ _,?_⟩
      rw [loopWord]

end Lamping.AG

namespace Lamping.AG
open Graph Lambda
/-- Every syntactically bound variable position carries an actual raw binding
suffix. Shell/direction follow separately from the initial encoding theorem. -/
theorem initial_bound_binding_access (t : Term) (n : Nat) (address : Path) (k : Nat)
    (lookup : subtermAt t address=some (.var k)) (bound : k<binderDepth address) :
    ∃ es : List (Endpoint (encode n t).net),RawBindingSuffix (encode n t).net es k ∧
      es.head?=some (.inr (.inl (.inl ()))) ∧accessTokens (encode n t).net es=address ∧
      accessKind (encode n t).net es=some .var := by
  induction t generalizing n address k with
  | var j =>
    cases address with
    | nil => simp [binderDepth] at bound
    | cons s rest => simp [subtermAt] at lookup
  | lam body ih =>
    cases address with
    | nil => cases lookup
    | cons s rest =>
      cases s with
      | fn => simp [subtermAt] at lookup
      | arg => simp [subtermAt] at lookup
      | body =>
        by_cases inside : k<binderDepth rest
        · obtain ⟨child,raw,head,word,kind⟩ := ih n rest k lookup inside
          dsimp only [encode]
          by_cases used : free body 0
          · rw [dif_pos used]
            obtain ⟨joined,binding,rooted,tokens,terminal⟩ := raw.enter_child (lambdaUsed n body used)
              (encode n body).net head kind (initialLambdaUsedBody n body used) [.body] (fun _ => rfl)
            exact ⟨joined,binding,rooted,by rw [tokens,word]; rfl,terminal⟩
          · rw [dif_neg used]
            obtain ⟨joined,binding,rooted,tokens,terminal⟩ := raw.enter_child (lambdaUnused n body used)
              (encode n body).net head kind (initialLambdaUnusedBody n body used) [.body] (fun _ => rfl)
            exact ⟨joined,binding,rooted,by rw [tokens,word]; rfl,terminal⟩
        · have same : k=binderDepth rest := by change k<binderDepth rest+1 at bound; omega
          subst k
          obtain ⟨occ,word⟩ := InitialOffsets.freeOccurrence_of_lookup body rest 0
            (by simpa only [Nat.zero_add] using lookup)
          obtain ⟨es,raw,rooted,tokens,terminal⟩ := initial_new_binding_access body occ n
          rw [word] at raw tokens
          exact ⟨es,raw,rooted,tokens,terminal⟩
  | app f arg hf ha =>
    cases address with
    | nil => cases lookup
    | cons s rest =>
      cases s with
      | body => simp [subtermAt] at lookup
      | fn =>
        obtain ⟨child,raw,head,word,kind⟩ := hf n rest k lookup bound
        let mapped := child.map (InitialOffsets.unionL (encode n f).net (encode (n+1) arg).net)
        have rawUnion := raw.unionLeft (encode n f).net (encode (n+1) arg).net
        have headUnion : mapped.head?=some (.inr (.inl (.inl (.inl ())))) := by
          rw [List.head?_map,head]; rfl
        have kindUnion : accessKind (unionNet (encode n f).net (encode (n+1) arg).net) mapped=some .var :=
          (accessKind_unionL _ _ child).trans kind
        obtain ⟨joined,binding,rooted,tokens,terminal⟩ := rawUnion.enter_child (appPatch n f arg)
          (unionNet (encode n f).net (encode (n+1) arg).net) headUnion kindUnion
          (initialAppFunction n f arg) [.fn] (fun _ => rfl)
        refine ⟨joined,binding,rooted,?_,terminal⟩
        dsimp only [encode]
        rw [tokens,accessTokens_unionL,word]; rfl
      | arg =>
        obtain ⟨child,raw,head,word,kind⟩ := ha (n+1) rest k lookup bound
        let mapped := child.map (InitialOffsets.unionR (encode n f).net (encode (n+1) arg).net)
        have rawUnion := raw.unionRight (encode n f).net (encode (n+1) arg).net
        have headUnion : mapped.head?=some (.inr (.inl (.inr (.inl ())))) := by
          rw [List.head?_map,head]; rfl
        have kindUnion : accessKind (unionNet (encode n f).net (encode (n+1) arg).net) mapped=some .var :=
          (accessKind_unionR _ _ child).trans kind
        obtain ⟨joined,binding,rooted,tokens,terminal⟩ := rawUnion.enter_child (appPatch n f arg)
          (unionNet (encode n f).net (encode (n+1) arg).net) headUnion kindUnion
          (initialAppArgument n f arg) [.arg] (fun _ => rfl)
        refine ⟨joined,binding,rooted,?_,terminal⟩
        dsimp only [encode]
        rw [tokens,accessTokens_unionR,word]; rfl
end Lamping.AG



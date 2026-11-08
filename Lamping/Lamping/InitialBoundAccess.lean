import Lamping.Lamping.InitialPositionAccess
namespace Lamping.AG.InitialOffsets
open Graph Lambda
/-- Syntactic lookup identifies an actual free occurrence, without choosing an
occurrence from the truth of the FV predicate alone. -/
theorem freeOccurrence_of_lookup (t : Term) (address : Path) (k : Nat)
    (lookup : subtermAt t address=some (.var (k+binderDepth address))) :
    ∃ occ : FreeOccurrence t k,occ.path=address := by
  induction address generalizing t k with
  | nil =>
    simp only [binderDepth,Nat.add_zero,subtermAt,Option.some.injEq] at lookup
    subst t
    exact ⟨.leaf k,rfl⟩
  | cons s rest ih =>
    cases t with
    | var j => cases s <;> simp [subtermAt] at lookup
    | lam body =>
      cases s with
      | fn => simp [subtermAt] at lookup
      | arg => simp [subtermAt] at lookup
      | body =>
        obtain ⟨occ,word⟩ := ih body (k+1) (by simpa only [subtermAt,binderDepth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using lookup)
        exact ⟨.lambda occ,congrArg (Step.body::·) word⟩
    | app f arg =>
      cases s with
      | body => simp [subtermAt] at lookup
      | fn =>
        obtain ⟨occ,word⟩ := ih f k lookup
        exact ⟨.function arg occ,congrArg (Step.fn::·) word⟩
      | arg =>
        obtain ⟨occ,word⟩ := ih arg k lookup
        exact ⟨.argument f occ,congrArg (Step.arg::·) word⟩
end Lamping.AG.InitialOffsets

namespace Lamping.AG
open Graph Lambda
/-- Every variable bound within the translated term has a genuine root access
ending at a lambda binding port. BindingSuffix/Observes is a separate obligation. -/
theorem encode_boundvar_access (t : Term) (n : Nat) (address : Path) (k : Nat)
    (lookup : subtermAt t address=some (.var k)) (bound : k<binderDepth address)
    (input : Context) : Nonempty (EncodedAccess t n address .var input) := by
  induction t generalizing n address k input with
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
        · obtain ⟨child⟩ := ih n rest k lookup inside input
          dsimp only [EncodedAccess,encode]
          by_cases used : free body 0
          · rw [dif_pos used]
            obtain ⟨es,labels,rooted,tokens,terminal⟩ :=
              child.labels.enter_child (lambdaUsed n body used) (encode n body).net
                (initialLambdaUsedBody n body used input) child.rooted
            refine ⟨⟨child.output,es,labels,rooted,?_,terminal.trans child.terminal⟩⟩
            rw [tokens,child.tokens]; rfl
          · rw [dif_neg used]
            obtain ⟨es,labels,rooted,tokens,terminal⟩ :=
              child.labels.enter_child (lambdaUnused n body used) (encode n body).net
                (initialLambdaUnusedBody n body used input) child.rooted
            refine ⟨⟨child.output,es,labels,rooted,?_,terminal.trans child.terminal⟩⟩
            rw [tokens,child.tokens]; rfl
        · have same : k=binderDepth rest := by change k<binderDepth rest+1 at bound; omega
          subst k
          obtain ⟨occ,word⟩ := InitialOffsets.freeOccurrence_of_lookup body rest 0
            (by simpa only [Nat.zero_add] using lookup)
          have used : free body 0 := occ.free
          obtain ⟨output,child,childWord⟩ := occ.realized n input
          dsimp only [EncodedAccess,encode]
          rw [dif_pos used]
          obtain ⟨es,labels,rooted,tokens,last⟩ :=
            LocalPath.enter_return (lambdaUsed n body used) (encode n body).net
              (initialLambdaUsedBody n body used input) child
          refine ⟨⟨output,es,labels,rooted,?_,?_⟩⟩
          · rw [tokens,childWord,word]; rfl
          · unfold accessKind
            rw [last]
            rfl
  | app f arg hf ha =>
    cases address with
    | nil => cases lookup
    | cons s rest =>
      cases s with
      | body => simp [subtermAt] at lookup
      | fn =>
        obtain ⟨child⟩ := hf n rest k lookup bound input
        have labels := Labelling.unionLeft (encode n f).net (encode (n+1) arg).net child.labels
        have head : (child.edges.map (InitialOffsets.unionL (encode n f).net (encode (n+1) arg).net)).head?=
            some (.inr (.inl (.inl (.inl ())))) := by rw [List.head?_map,child.rooted]; rfl
        obtain ⟨es,joined,rooted,tokens,terminal⟩ :=
          labels.enter_child (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net)
            (initialAppFunction n f arg input) head
        refine ⟨⟨child.output,es,joined,rooted,?_,?_⟩⟩
        · dsimp only [encode]
          rw [tokens,accessTokens_unionL,child.tokens]; rfl
        · dsimp only [encode]
          rw [terminal,accessKind_unionL,child.terminal]
      | arg =>
        obtain ⟨child⟩ := ha (n+1) rest k lookup bound input
        have labels := Labelling.unionRight (encode n f).net (encode (n+1) arg).net child.labels
        have head : (child.edges.map (InitialOffsets.unionR (encode n f).net (encode (n+1) arg).net)).head?=
            some (.inr (.inl (.inr (.inl ())))) := by rw [List.head?_map,child.rooted]; rfl
        obtain ⟨es,joined,rooted,tokens,terminal⟩ :=
          labels.enter_child (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net)
            (initialAppArgument n f arg input) head
        refine ⟨⟨child.output,es,joined,rooted,?_,?_⟩⟩
        · dsimp only [encode]
          rw [tokens,accessTokens_unionR,child.tokens]; rfl
        · dsimp only [encode]
          rw [terminal,accessKind_unionR,child.terminal]

/-- All syntax positions of a closed initial term are covered by physical root
accesses. This proves coverage only; it does not assume or conclude Matches. -/
theorem encode_closed_access_coverage (t : Term) (closed : Closed t) (n : Nat)
    (p : Position t) (input : Context) :
    ∃ es : RootAccess (encode n t).net (.inl ()),accessWord (encode n t).net es.val=p.val := by
  obtain ⟨u,lookup⟩ := Option.isSome_iff_exists.mp p.property
  have covered : Nonempty (EncodedAccess t n p.val (syntaxShape u).kind input) := by
    cases u with
    | var k =>
      have scope := scoped_subterm closed lookup
      change k<0+binderDepth p.val at scope
      exact encode_boundvar_access t n p.val k lookup (by simpa only [Nat.zero_add] using scope) input
    | app f arg => exact encode_nonvar_access t n p.val (.app f arg) lookup (by intro same; cases same) input
    | lam body => exact encode_nonvar_access t n p.val (.lam body) lookup (by intro same; cases same) input
  obtain ⟨a⟩ := covered
  exact ⟨a.rootAccess,a.word⟩
end Lamping.AG




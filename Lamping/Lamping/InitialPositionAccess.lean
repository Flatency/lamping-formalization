import Lamping.Lamping.InitialRootLifting
namespace Lamping.AG
open Graph Lambda
/-- A labelled physical root access to a specified syntax address/kind.
No matching or source-term lookup is built into this witness. -/
structure RootAccessWitness {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (root : B) (address : Path) (kind : AccessKind) (input : Context) where
  output : Context
  edges : List (Endpoint g)
  labels : Labelling g edges input output
  rooted : edges.head?=some (.inr (.inl root))
  tokens : accessTokens g edges=address
  terminal : accessKind g edges=some kind

abbrev EncodedAccess (t : Term) (n : Nat) (address : Path) (kind : AccessKind) (input : Context) :=
  RootAccessWitness (encode n t).net (.inl ()) address kind input

def EncodedAccess.rootAccess (a : EncodedAccess t n address kind input) :
    RootAccess (encode n t).net (.inl ()) :=
  ⟨a.edges,⟨⟨⟨input,a.output,a.labels⟩,encode_root_forward t n a.edges a.rooted ⟨input,a.output,a.labels⟩⟩,
    a.rooted,kind,a.terminal⟩⟩

theorem EncodedAccess.word (a : EncodedAccess t n address kind input) :
    accessWord (encode n t).net a.rootAccess.val=address :=
  (accessTokens_eq_accessWord _ (.inl ()) a.rooted).symm.trans a.tokens

/-- Every application or lambda syntax position has a genuine access in the
actual initial translation, at every supplied input context. Variables require
an additional binding/FV distinction and are deliberately not inferred here. -/
theorem encode_nonvar_access (t : Term) (n : Nat) (address : Path) (u : Term)
    (lookup : subtermAt t address=some u) (nonvar : (syntaxShape u).kind≠.var)
    (input : Context) : Nonempty (EncodedAccess t n address (syntaxShape u).kind input) := by
  induction t generalizing n address u input with
  | var k =>
    cases address with
    | nil => cases lookup; exact False.elim (nonvar rfl)
    | cons s rest => simp [subtermAt] at lookup
  | lam body ih =>
    cases address with
    | nil =>
      cases lookup
      dsimp only [EncodedAccess,encode]
      by_cases used : free body 0
      · rw [dif_pos used]
        exact ⟨⟨input,[.inr (.inl (.inl ()))],.single _ _,rfl,rfl,rfl⟩⟩
      · rw [dif_neg used]
        exact ⟨⟨input,[.inr (.inl (.inl ()))],.single _ _,rfl,rfl,rfl⟩⟩
    | cons s rest =>
      cases s with
      | fn => simp [subtermAt] at lookup
      | arg => simp [subtermAt] at lookup
      | body =>
        obtain ⟨child⟩ := ih n rest u lookup nonvar input
        dsimp only [EncodedAccess,encode]
        by_cases used : free body 0
        · rw [dif_pos used]
          obtain ⟨es,labels,rooted,tokens,terminal⟩ :=
            child.labels.enter_child (lambdaUsed n body used) (encode n body).net
              (initialLambdaUsedBody n body used input) child.rooted
          refine ⟨⟨child.output,es,labels,rooted,?_,terminal.trans child.terminal⟩⟩
          rw [tokens,child.tokens]
          rfl
        · rw [dif_neg used]
          obtain ⟨es,labels,rooted,tokens,terminal⟩ :=
            child.labels.enter_child (lambdaUnused n body used) (encode n body).net
              (initialLambdaUnusedBody n body used input) child.rooted
          refine ⟨⟨child.output,es,labels,rooted,?_,terminal.trans child.terminal⟩⟩
          rw [tokens,child.tokens]
          rfl
  | app f arg hf ha =>
    cases address with
    | nil =>
      cases lookup
      exact ⟨⟨input,[.inr (.inl (.inl ()))],.single _ _,rfl,rfl,rfl⟩⟩
    | cons s rest =>
      cases s with
      | body => simp [subtermAt] at lookup
      | fn =>
        obtain ⟨child⟩ := hf n rest u lookup nonvar input
        have labels := Labelling.unionLeft (encode n f).net (encode (n+1) arg).net child.labels
        have head : (child.edges.map (InitialOffsets.unionL (encode n f).net (encode (n+1) arg).net)).head?=
            some (.inr (.inl (.inl (.inl ())))) := by rw [List.head?_map,child.rooted]; rfl
        obtain ⟨es,joined,rooted,tokens,terminal⟩ :=
          labels.enter_child (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net)
            (initialAppFunction n f arg input) head
        refine ⟨⟨child.output,es,joined,rooted,?_,?_⟩⟩
        · dsimp only [encode]
          rw [tokens,accessTokens_unionL,child.tokens]
          rfl
        · dsimp only [encode]
          rw [terminal,accessKind_unionL,child.terminal]
      | arg =>
        obtain ⟨child⟩ := ha (n+1) rest u lookup nonvar input
        have labels := Labelling.unionRight (encode n f).net (encode (n+1) arg).net child.labels
        have head : (child.edges.map (InitialOffsets.unionR (encode n f).net (encode (n+1) arg).net)).head?=
            some (.inr (.inl (.inr (.inl ())))) := by rw [List.head?_map,child.rooted]; rfl
        obtain ⟨es,joined,rooted,tokens,terminal⟩ :=
          labels.enter_child (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net)
            (initialAppArgument n f arg input) head
        refine ⟨⟨child.output,es,joined,rooted,?_,?_⟩⟩
        · dsimp only [encode]
          rw [tokens,accessTokens_unionR,child.tokens]
          rfl
        · dsimp only [encode]
          rw [terminal,accessKind_unionR,child.terminal]
end Lamping.AG

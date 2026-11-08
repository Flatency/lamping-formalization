import Lamping.Lamping.InitialFreeRoutes
namespace Lamping.AG.InitialOffsets
open Graph Lambda
private theorem functionFV_tokens (n : Nat) (f arg : Term) (x : FV f) (input : Context) :
    accessTokens (appPatch n f arg) (initialFunctionFV n f arg x input).2.edges=[] := by
  by_cases shared : AG.free arg x.val
  · unfold initialFunctionFV
    rw [dif_pos shared]
    rfl
  · unfold initialFunctionFV
    rw [dif_neg shared]
    rfl

private theorem argumentFV_tokens (n : Nat) (f arg : Term) (x : FV arg) (input : Context) :
    accessTokens (appPatch n f arg) (initialArgumentFV n f arg x input).2.edges=[] := by
  by_cases shared : AG.free f x.val
  · dsimp only [initialArgumentFV]
    rw [dif_pos shared]
    rfl
  · dsimp only [initialArgumentFV]
    rw [dif_neg shared]
    rfl

/-- Every chosen free occurrence is realized by an actual root-to-FV path,
with all seam segments, controls and the exact syntax address preserved.
This is geometric existence, not an effective graph execution procedure. -/
theorem FreeOccurrence.realized {t : Term} {k : Nat} (occ : FreeOccurrence t k)
    (n : Nat) (input : Context) :
    ∃ output, ∃ p : LocalPath (encode n t).net (.inl ()) (.inr ⟨k,occ.free⟩) input output,
      accessTokens (encode n t).net p.edges=occ.path := by
  induction occ generalizing n input with
  | leaf k =>
    let p : LocalPath (encode n (.var k)).net (.inl ()) (.inr ⟨k,rfl⟩)
        input (input.replace n ((input.tail n).cons .empty)) :=
      ⟨(initialVarPath n k input (input.tail n)).edges,rfl,rfl,
        by simpa only [Context.replace_tail] using (initialVarPath n k input (input.tail n)).labeling⟩
    exact ⟨_,p,rfl⟩
  | @lambda body k occ ih =>
    obtain ⟨output,child,word⟩ := ih n input
    dsimp only [encode]
    by_cases used : AG.free body 0
    · rw [dif_pos used]
      refine ⟨output,LocalPath.plugThree (lambdaUsed n body used) (encode n body).net
        (initialLambdaUsedBody n body used input) child
        (initialLambdaUsedFV n body used k occ.free output),?_⟩
      change accessTokens (plug (lambdaUsed n body used) (encode n body).net) (_++_++_)=_
      rw [accessTokens_three_pieces,word]
      change [Step.body]++occ.path++[]=Step.body::occ.path
      simp only [List.append_nil,List.cons_append,List.nil_append]
    · rw [dif_neg used]
      refine ⟨output,LocalPath.plugThree (lambdaUnused n body used) (encode n body).net
        (initialLambdaUnusedBody n body used input) child
        (initialLambdaUnusedFV n body used k occ.free output),?_⟩
      change accessTokens (plug (lambdaUnused n body used) (encode n body).net) (_++_++_)=_
      rw [accessTokens_three_pieces,word]
      change [Step.body]++occ.path++[]=Step.body::occ.path
      simp only [List.append_nil,List.cons_append,List.nil_append]
  | @function f k arg occ ih =>
    obtain ⟨output,child,word⟩ := ih n input
    let suffix := initialFunctionFV n f arg ⟨k,occ.free⟩ output
    refine ⟨suffix.1,LocalPath.plugThree (appPatch n f arg)
      (unionNet (encode n f).net (encode (n+1) arg).net)
      (initialAppFunction n f arg input)
      (LocalPath.unionLeft (encode n f).net (encode (n+1) arg).net child) suffix.2,?_⟩
    change accessTokens (plug (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net)) (_++_++_)=_
    rw [accessTokens_three_pieces]
    simp only [LocalPath.unionLeft,accessTokens_unionL]
    rw [word]
    rw [show accessTokens (appPatch n f arg) suffix.2.edges=[] from functionFV_tokens n f arg _ output]
    change [Step.fn]++occ.path++[]=Step.fn::occ.path
    simp only [List.append_nil,List.cons_append,List.nil_append]
  | @argument f arg k occ ih =>
    obtain ⟨output,child,word⟩ := ih (n+1) input
    let suffix := initialArgumentFV n f arg ⟨k,occ.free⟩ output
    refine ⟨suffix.1,LocalPath.plugThree (appPatch n f arg)
      (unionNet (encode n f).net (encode (n+1) arg).net)
      (initialAppArgument n f arg input)
      (LocalPath.unionRight (encode n f).net (encode (n+1) arg).net child) suffix.2,?_⟩
    change accessTokens (plug (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net)) (_++_++_)=_
    rw [accessTokens_three_pieces]
    simp only [LocalPath.unionRight,accessTokens_unionR]
    rw [word]
    rw [show accessTokens (appPatch n f arg) suffix.2.edges=[] from argumentFV_tokens n f arg _ output]
    change [Step.arg]++occ.path++[]=Step.arg::occ.path
    simp only [List.append_nil,List.cons_append,List.nil_append]
end Lamping.AG.InitialOffsets

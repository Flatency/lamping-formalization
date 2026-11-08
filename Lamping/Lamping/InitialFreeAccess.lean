import Lamping.Lamping.InitialAccessWords
namespace Lamping.AG.InitialOffsets
open Graph Lambda

def FreeOccurrence.path : {t : Term} → {k : Nat} → FreeOccurrence t k → Path
  | _,_,.leaf _ => []
  | _,_,.lambda p => .body::p.path
  | _,_,.function _ p => .fn::p.path
  | _,_,.argument _ p => .arg::p.path

theorem FreeOccurrence.path_cast {t : Term} {i j : Nat} (same : i=j) (p : FreeOccurrence t i) :
    (same ▸ p).path=p.path := by cases same; rfl

theorem FreeOccurrence.lookup {t : Term} {k : Nat} (p : FreeOccurrence t k) :
    subtermAt t p.path=some (.var (k+binderDepth p.path)) := by
  induction p with
  | leaf k => rfl
  | lambda p ih =>
    simpa [FreeOccurrence.path,subtermAt,binderDepth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih
  | function arg p ih => simpa only [FreeOccurrence.path,subtermAt,binderDepth] using ih
  | argument fn p ih => simpa only [FreeOccurrence.path,subtermAt,binderDepth] using ih

/-- Actual initial root-to-FV paths name a genuine syntax occurrence.
Control words alone are not substituted for syntax access paths. -/
theorem encode_FV_tokens (t : Term) (n : Nat) (x : FV t) {a b : Context}
    (p : LocalPath (encode n t).net (.inl ()) (.inr x) a b) :
    ∃ occurrence : FreeOccurrence t x.val,
      accessTokens (encode n t).net p.edges=occurrence.path := by
  induction t generalizing n a b with
  | var k =>
    obtain ⟨value,freeValue⟩ := x
    change value=k at freeValue
    subst value
    obtain ⟨eq,_⟩ := p.labeling.one_turn_boundary p.start () (.inr ()) (.inl ()) rfl
      (fun _ _ _ rule => rule.control_aux) (.inr ⟨k,rfl⟩) (.inr ⟨k,rfl⟩) rfl p.finish
    exact ⟨.leaf k,by rw [eq]; rfl⟩
  | lam body ih =>
    revert p
    dsimp only [encode]
    obtain ⟨vp,rflow⟩ := encode_flow body n
    by_cases used : free body 0
    · rw [dif_pos used]
      intro p
      obtain ⟨z,z',mid,last,first,middle,suffix,entry,exit,eq⟩ := LocalPath.outer_child
        (lambdaUsed n body used) (encode n body).net (lambdaUsed_flow n body used) rflow
        (lambdaUsed_noReturn n body used) (.inl ()) (.inr x) rfl
        (fun _ _ path => LocalPath.no_proper_to_variable path (lambdaUsed_variableSeparated n body used) rfl rfl) p
      obtain ⟨firstEq,rfl,_⟩ := lambdaUsed_root_to_child n body used z first
      cases z' with
      | inl u => cases exit
      | inr fv =>
        obtain ⟨value,suffixEq,_⟩ := lambdaUsed_FV_external_shape n body used fv x suffix
        rcases fv with ⟨k,hk⟩
        dsimp at value; subst k
        obtain ⟨occ,word⟩ := ih n ⟨x.val+1,hk⟩ middle
        refine ⟨.lambda occ,?_⟩
        rw [eq,accessTokens_three_pieces,firstEq,suffixEq]
        change [.body]++accessTokens (encode n body).net middle.edges++[]=.body::occ.path
        simpa only [List.singleton_append,List.append_nil] using congrArg (Step.body::·) word
    · rw [dif_neg used]
      intro p
      obtain ⟨z,z',mid,last,first,middle,suffix,entry,exit,eq⟩ := LocalPath.outer_child
        (lambdaUnused n body used) (encode n body).net (lambdaUnused_flow n body used) rflow
        (lambdaUnused_noReturn n body used) (.inl ()) (.inr x) rfl
        (fun _ _ path => LocalPath.no_proper_to_variable path (lambdaUnused_variableSeparated n body used) rfl rfl) p
      obtain ⟨firstEq,rfl,_⟩ := lambdaUnused_root_to_child n body used z first
      cases z' with
      | inl u => cases exit
      | inr fv =>
        obtain ⟨value,suffixEq,_⟩ := lambdaUnused_FV_external_shape n body used fv x suffix
        rcases fv with ⟨k,hk⟩
        dsimp at value; subst k
        obtain ⟨occ,word⟩ := ih n ⟨x.val+1,hk⟩ middle
        refine ⟨.lambda occ,?_⟩
        rw [eq,accessTokens_three_pieces,firstEq,suffixEq]
        change [.body]++accessTokens (encode n body).net middle.edges++[]=.body::occ.path
        simpa only [List.singleton_append,List.append_nil] using congrArg (Step.body::·) word
  | app f arg hf ha =>
    dsimp only [encode] at p ⊢
    obtain ⟨wp,fnFlow⟩ := encode_flow f n
    obtain ⟨vp,argFlow⟩ := encode_flow arg (n+1)
    have unionFlow := FlowOn.union (g:=(encode n f).net) (h:=(encode (n+1) arg).net)
      (bp:=initialBoundaryPolarity) (cp:=initialBoundaryPolarity) (wp:=wp) (vp:=vp) fnFlow argFlow
    obtain ⟨z,z',mid,last,first,middle,suffix,entry,exit,eq⟩ := LocalPath.outer_child
      (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net)
      (appPatch_flow n f arg) unionFlow (appPatch_noReturn n f arg) (.inl ()) (.inr x) rfl
      (fun _ _ path => LocalPath.no_proper_to_variable path (appPatch_variableSeparated n f arg) rfl rfl) p
    rcases appPatch_root_to_child n f arg z first with ⟨rfl,firstEq,_⟩ | ⟨rfl,firstEq,_⟩
    · obtain ⟨v,rfl,child,childEq⟩ := LocalPath.unionL_source (encode n f).net (encode (n+1) arg).net (.inl ()) z' middle
      cases v with
      | inl u => cases exit
      | inr fv =>
        obtain ⟨value,suffixEq⟩ := appPatch_function_FV_shape n f arg fv x suffix
        obtain ⟨occ,word⟩ := hf n fv child
        let occurrence : FreeOccurrence (.app f arg) x.val := value.symm ▸ FreeOccurrence.function arg occ
        refine ⟨occurrence,?_⟩
        have occurrencePath : occurrence.path=.fn::occ.path := FreeOccurrence.path_cast value.symm _
        rw [eq,accessTokens_three_pieces,firstEq,childEq,accessTokens_unionL,occurrencePath]
        by_cases shared : free arg fv.val
        · rw [dif_pos shared] at suffixEq
          rw [suffixEq]
          change [.fn]++accessTokens (encode n f).net child.edges++[]=.fn::occ.path
          simpa only [List.singleton_append,List.append_nil] using congrArg (Step.fn::·) word
        · rw [dif_neg shared] at suffixEq
          rw [suffixEq]
          change [.fn]++accessTokens (encode n f).net child.edges++[]=.fn::occ.path
          simpa only [List.singleton_append,List.append_nil] using congrArg (Step.fn::·) word
    · obtain ⟨v,rfl,child,childEq⟩ := LocalPath.unionR_source (encode n f).net (encode (n+1) arg).net (.inl ()) z' middle
      cases v with
      | inl u => cases exit
      | inr fv =>
        obtain ⟨value,suffixEq⟩ := appPatch_argument_FV_shape n f arg fv x suffix
        obtain ⟨occ,word⟩ := ha (n+1) fv child
        let occurrence : FreeOccurrence (.app f arg) x.val := value.symm ▸ FreeOccurrence.argument f occ
        refine ⟨occurrence,?_⟩
        have occurrencePath : occurrence.path=.arg::occ.path := FreeOccurrence.path_cast value.symm _
        rw [eq,accessTokens_three_pieces,firstEq,childEq,accessTokens_unionR,occurrencePath]
        by_cases shared : free f fv.val
        · rw [dif_pos shared] at suffixEq
          rw [suffixEq]
          change [.arg]++accessTokens (encode (n+1) arg).net child.edges++[]=.arg::occ.path
          simpa only [List.singleton_append,List.append_nil] using congrArg (Step.arg::·) word
        · rw [dif_neg shared] at suffixEq
          rw [suffixEq]
          change [.arg]++accessTokens (encode (n+1) arg).net child.edges++[]=.arg::occ.path
          simpa only [List.singleton_append,List.append_nil] using congrArg (Step.arg::·) word

theorem encode_FV_accessWord (t : Term) (n : Nat) (x : FV t) {a b : Context}
    (p : LocalPath (encode n t).net (.inl ()) (.inr x) a b) :
    ∃ occurrence : FreeOccurrence t x.val,
      accessWord (encode n t).net p.edges=occurrence.path := by
  obtain ⟨occ,word⟩ := encode_FV_tokens t n x p
  exact ⟨occ,(accessTokens_eq_accessWord _ _ p.start).symm.trans word⟩
end Lamping.AG.InitialOffsets

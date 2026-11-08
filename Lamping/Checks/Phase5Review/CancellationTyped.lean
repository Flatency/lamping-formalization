import Lamping.Lamping.CancellationSourceContraction
import Lamping.Lamping.UnobservedPathWords
import Lamping.Lamping.CancellationPathWords
import Lamping.Lamping.Fixtures
namespace Lamping.Checks.Phase5Review.CancellationTyped
open AG Graph
private def kept (_ : Bool) : Label signature := ⟨.op .lam,5⟩
private def site : PathSite (.fanCancel 2) kept (B:=Bool) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl b,.inl _⟩ => .inl ⟨.inr (.inr ()),.inr b⟩
      | .inl ⟨.inl b,.inr false⟩ => .inl ⟨.inl b,.inr true⟩
      | .inl ⟨.inl b,.inr true⟩ => .inl ⟨.inl b,.inr false⟩
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inl _),.inr b⟩ => .inr (.inl b)
      | .inl ⟨.inr (.inr _),.inr b⟩ => .inl ⟨.inl b,.inl ()⟩
      | .inr (.inl b) => .inl ⟨.inr (.inl ()),.inr b⟩
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨b|(u|u),p⟩ | (b | ⟨w|v,d⟩))
      · cases p with | inl u => cases u; rfl | inr q => cases q <;> rfl
      · cases u; cases p with | inl u => cases u; rfl | inr q => rfl
      · cases u; cases p with | inl u => cases u; rfl | inr q => rfl
      · rfl
      · exact nomatch w
      · cases v; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨b|(u|u),p⟩ | (b | ⟨w|v,d⟩)) same
      · cases p with
        | inl u => cases same
        | inr q => cases q <;> cases same
      · cases p <;> cases same
      · cases p <;> cases same
      · cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases v; cases b <;> rfl

private def old (branch : Bool) : List (Endpoint site.net) :=
  [.inr (.inl branch),.inl ⟨.inr (.inl ()),.inl ()⟩,
   .inr (.inr (.inr (),true)),.inl ⟨.inr (.inr ()),.inr branch⟩]

theorem old_labels (branch : Bool) (a : Context) : Labelling site.net (old branch) a a := by
  have rule := InitialOffsets.Event.apply_rel (.fan 2 branch) a
  exact .cons (.node _ _ _ (.direct rule))
    (.cons (.transparent _ _ _) (.cons (.node _ _ _ (.inverse rule)) (.single _ _)))

theorem old_typed (branch : Bool) : accessKind site.net (old branch)=some .lam := rfl

theorem incomplete_is_not_typed (branch : Bool) : accessKind site.net ((old branch).take 3)=none := rfl

/-- Both real branches cross one W and end at their own retained lambda.
The reduced path is constructed by the general algorithm, not supplied. -/
theorem both_branches_contract (branch : Bool) (a : Context) :
    ∃ es,Labelling site.reduce es a a ∧ CancellationResidual site es (old branch) ∧
      es.head?=some (AG.plugLeft _ (Schema.fanCancel 2).right.net (.inr (.inl (.inl branch)))) ∧
      es.getLast?=some (AG.plugLeft _ (Schema.fanCancel 2).right.net (.inr (.inl (.inr (.inr branch))))) := by
  exact site.cancellation_source_contraction (.fan 2) (old_labels branch a) ⟨.lam,old_typed branch⟩
    (.inr (.inl (.inl branch))) (.inr (.inl (.inr (.inr branch)))) rfl rfl

#print axioms old_labels
#print axioms both_branches_contract
#print axioms incomplete_is_not_typed
/-- A real application departure has no proper arrival (it enters the W),
but its own departure token is still fn. Only accessWord skips that token. -/
theorem unobserved_first_token_is_retained :
    accessKind actualBetaSite.net [(.inl ⟨.inr (.inl ()),.inl ()⟩)]=none ∧
    accessTokens actualBetaSite.net [(.inl ⟨.inr (.inl ()),.inl ()⟩)]=[.fn] ∧
    accessWord actualBetaSite.net [(.inl ⟨.inr (.inl ()),.inl ()⟩)]=[] := by
  exact ⟨rfl,rfl,rfl⟩
#print axioms unobserved_first_token_is_retained
theorem old_forward (branch : Bool) : Forward site.net (old branch) := by
  exact .node (.inr (.inl ())) (.inr branch) (.inl ()) rfl rfl trivial
    (.transparent (.inr ()) false rfl rfl
      (.node (.inr (.inr ())) (.inl ()) (.inr branch) rfl rfl trivial (.single _)))

/-- The same nonvacuous typed whole paths consume the strengthened word
contraction, with a chosen real unobserved residual rather than the bare one. -/
theorem both_branch_words_contract (branch : Bool) (a : Context) :
    ∃ es,Labelling site.reduce es a a ∧CancellationUnobservedResidual site es (old branch) ∧
      es.head?=some (AG.plugLeft _ (Schema.fanCancel 2).right.net (.inr (.inl (.inl branch)))) ∧
      es.getLast?=some (AG.plugLeft _ (Schema.fanCancel 2).right.net (.inr (.inl (.inr (.inr branch))))) ∧
      accessWord site.reduce es=accessWord site.net (old branch) := by
  exact site.cancellation_source_word_contraction (.fan 2) (old_labels branch a) (old_forward branch)
    ⟨.lam,old_typed branch⟩ (.inr (.inl (.inl branch))) (.inr (.inl (.inr (.inr branch)))) rfl rfl
#print axioms both_branch_words_contract
end Lamping.Checks.Phase5Review.CancellationTyped





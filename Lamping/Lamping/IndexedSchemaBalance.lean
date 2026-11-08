import Lamping.Lamping.IndexedLevelBalance
import Lamping.Lamping.SchemaBalance
namespace Lamping.AG
open Graph

theorem Schema.indexed_balance_preservation (s : Schema) (boundary : s.Frontier → Int)
    (old : IndexedLevelBalance s.left boundary) :
    Nonempty (IndexedLevelBalance s.right.net boundary) := by
  have active := old.bounded (.inl ())
  have passive := old.bounded (.inr ())
  cases s with
  | beta i | fanCancel i | croCancel i | braCancel i =>
    obtain ⟨rhs⟩ := Schema.balance_preservation _ boundary old.toLevelBalance
    exact ⟨{ toLevelBalance := rhs, bounded := fun n => nomatch n }⟩
  | fanAction f i j less =>
    change ControlIndexBound (label f j) (old.nodes (.inr ())) at passive
    refine ⟨{ toLevelBalance := (fanRight_balance f i j (old.nodes (.inl ()))
        (old.nodes (.inr ())) boundary old.toLevelBalance.active_auxiliary
        old.toLevelBalance.passive_auxiliary old.toLevelBalance.principal_pair),
              bounded := ?_ }⟩
    rintro (b | a)
    · exact passive
    · change (i : Int) < portDepth j (.op f) (old.nodes (.inr ())) (.inr a)
      cases f <;> simp only [ControlIndexBound,label] at passive
      all_goals cases a <;> simp only [portDepth] <;> omega
  | croAction f i j less =>
    change ControlIndexBound (label f j) (old.nodes (.inr ())) at passive
    refine ⟨{ toLevelBalance := (croRight_balance f i j (by omega) (old.nodes (.inl ()))
        (old.nodes (.inr ())) boundary (old.toLevelBalance.active_auxiliary ())
        old.toLevelBalance.passive_auxiliary old.toLevelBalance.principal_pair),
              bounded := ?_ }⟩
    rintro (u | a)
    · change ControlIndexBound (label f (j-1)) (old.nodes (.inr ())-1)
      cases f <;> simp only [ControlIndexBound,label] at passive ⊢ <;> try trivial
      all_goals omega
    · change (i : Int) ≤ portDepth j (.op f) (old.nodes (.inr ())) (.inr a)-1
      cases f <;> simp only [ControlIndexBound,label] at passive
      all_goals cases a <;> simp only [portDepth] <;> omega
  | braAction f i j less =>
    change ControlIndexBound (label f j) (old.nodes (.inr ())) at passive
    refine ⟨{ toLevelBalance := (braRight_balance f i j (old.nodes (.inl ()))
        (old.nodes (.inr ())) boundary (old.toLevelBalance.active_auxiliary ())
        old.toLevelBalance.passive_auxiliary old.toLevelBalance.principal_pair),
              bounded := ?_ }⟩
    rintro (u | a)
    · change ControlIndexBound (label f (j+1)) (old.nodes (.inr ())+1)
      cases f <;> simp only [ControlIndexBound,label] at passive ⊢ <;> try trivial
      all_goals omega
    · change (i : Int) < portDepth j (.op f) (old.nodes (.inr ())) (.inr a)
      cases f <;> simp only [ControlIndexBound,label] at passive
      all_goals cases a <;> simp only [portDepth] <;> omega
end Lamping.AG






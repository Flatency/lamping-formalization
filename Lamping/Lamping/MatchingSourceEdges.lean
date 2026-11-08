import Lamping.Lamping.MatchingSourceBinders
import Lamping.Lamping.CorridorBoundaryTurns
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
/-- For supplied actual matching accesses, syntax-word prefix reflects to a
literal physical prefix. The induction only cuts existing accesses. -/
theorem Matches.access_prefix {t : Term} (matching : Matches g root t)
    (parent child : RootAccess g root) (suffix : Path)
    (word : accessWord g child.val=accessWord g parent.val++suffix) :
    ∃ tail,child.val=parent.val++tail := by
  have reversed : ∀ reverse : Path,∀ given : RootAccess g root,
      accessWord g given.val=accessWord g parent.val++reverse.reverse →
      ∃ tail,given.val=parent.val++tail := by
    intro reverse
    induction reverse with
    | nil =>
      intro given words
      have equal : given=parent := matching.accessWord_injective (by simpa using words)
      exact ⟨[],by rw [equal,List.append_nil]⟩
    | cons step reverse ih =>
      intro given words
      have splitWord : accessWord g given.val=(accessWord g parent.val++reverse.reverse)++[step] := by
        simpa only [List.reverse_cons,List.append_assoc] using words
      obtain ⟨middle,node,ctx,departure,tail,_,middleWord,_,split⟩ :=
        given.before_syntax_token (accessWord g parent.val++reverse.reverse) step splitWord
      obtain ⟨prefixTail,prefixEqual⟩ := ih middle middleWord
      exact ⟨prefixTail++(.inl ⟨node,departure⟩)::tail,by rw [split,prefixEqual,List.append_assoc]⟩
  exact reversed suffix.reverse child (by simpa only [List.reverse_reverse] using word)
end

private theorem SyntaxChildPorts.traversal_context_eq {kind : Kind} {ctx departure : Port kind}
    (roles : SyntaxChildPorts kind ctx departure step) (turn : Traversal level kind ctx departure a b) : a=b := by
  cases turn with
  | direct passage => cases passage <;> first | rfl | cases roles
  | inverse passage => cases passage <;> first | rfl | cases roles
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
private theorem SyntaxChildPorts.turn_context_eq
    {node : N} {ctx departure : Port (g.label node).sort}
    (roles : SyntaxChildPorts (g.label node).sort ctx departure step)
    (turn : LabelledTurn g (.inl ⟨node,ctx⟩) (.inl ⟨node,departure⟩) a b) : a=b := by
  cases turn with
  | node _ _ _ traversal => exact roles.traversal_context_eq traversal
/-- One actual syntax edge has a nonempty literal suffix beginning at its
specified physical departure. Every whole assignment splits at the SAME
parent context; no new label assignment or root path is manufactured. -/
theorem Matches.syntax_child_fragment {t : Term} (matching : Matches g root t)
    (parent child : RootAccess g root) (step : Step)
    (word : accessWord g child.val=accessWord g parent.val++[step]) :
    ∃ (node : N) (ctx departure : Port (g.label node).sort) (tail : List (Endpoint g)),
      SyntaxChildPorts (g.label node).sort ctx departure step ∧
      parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩)) ∧
      child.val=parent.val++(.inl ⟨node,departure⟩)::tail ∧
      Forward g ((.inl ⟨node,departure⟩)::tail) ∧
      (∀ a b,Labelling g child.val a b → ∃ middle,
        Labelling g parent.val a middle ∧ Labelling g ((.inl ⟨node,departure⟩)::tail) middle b) := by
  obtain ⟨actualParent,node,ctx,departure,tail,roles,parentWord,finish,split⟩ :=
    child.before_syntax_token (accessWord g parent.val) step word
  have sameParent : actualParent=parent := matching.accessWord_injective parentWord
  rw [sameParent] at finish split
  have ordinal : child.val[parent.val.length]?=some (.inl ⟨node,departure⟩) := by
    rw [split,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]; rfl
  have forward := child.property.1.2.suffix_at parent.val.length _ ordinal
  rw [split,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at forward
  refine ⟨node,ctx,departure,tail,roles,finish,split,forward,?_⟩
  intro a b whole
  rw [split] at whole
  obtain ⟨middle,prefixLabels,suffixLabels⟩ := whole.split_segment
  obtain ⟨initial,previous,before,preSplit,preLabels,turn⟩ :=
    prefixLabels.last_turn parent.property.1.1.walk.nonempty
  have previousLast : parent.val.getLast?=some previous := by rw [preSplit]; simp
  have previousEqual : previous=g.wire (.inl ⟨node,ctx⟩) :=
    Option.some.inj (previousLast.symm.trans finish)
  rw [previousEqual,Pairing.involutive] at turn
  have contexts : before=middle := roles.turn_context_eq turn
  rw [←preSplit] at preLabels
  exact ⟨middle,by simpa only [contexts] using preLabels,suffixLabels⟩
end
end Lamping.AG



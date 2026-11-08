import Lamping.Lamping.PlugPathDecomposition
namespace Lamping.AG
open Graph
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

theorem PlugTurn.right_cases {x : Endpoint r} {y : PlugSegment c r}
    (turn : PlugTurn c r (.inr x) y a b) :
    (∃ z,y=.inr z ∧LabelledTurn r x z a b) ∨
      (∃ f,x=.inr (.inl f) ∧y=.inl (.inr (.inl (.inr f))) ∧a=b) := by
  cases turn with
  | right localTurn => exact Or.inl ⟨_,rfl,localTurn⟩
  | leave f a => exact Or.inr ⟨f,rfl,rfl,rfl⟩

theorem PlugTurn.left_cases {x : Endpoint c} {y : PlugSegment c r}
    (turn : PlugTurn c r (.inl x) y a b) :
    (∃ z,y=.inl z ∧LabelledTurn c x z a b) ∨
      (∃ f,x=.inr (.inl (.inr f)) ∧y=.inr (.inr (.inl f)) ∧a=b) := by
  cases turn with
  | left localTurn => exact Or.inl ⟨_,rfl,localTurn⟩
  | enter f a => exact Or.inr ⟨f,rfl,rfl,rfl⟩

/-- An arbitrary finite raw path beginning inside the RHS either remains
there or has a first exit. All preceding RHS segments and the exact original
seam context are retained. No simplicity or frontier-distinctness is used. -/
theorem PlugLabelling.right_first {x : Endpoint r} {tail : List (PlugSegment c r)}
    (labels : PlugLabelling c r (.inr x::tail) a b) :
    (∃ xs : List (Endpoint r),tail=xs.map Sum.inr ∧Labelling r (x::xs) a b) ∨
    ∃ (xs : List (Endpoint r)) (f : F) (rest : List (PlugSegment c r)) (middle : Context),
      tail=xs.map Sum.inr ++ .inl (.inr (.inl (.inr f)))::rest ∧
      Labelling r (x::xs) a middle ∧
      (x::xs).getLast?=some (r.wire (.inr (.inl f))) ∧
      PlugLabelling c r (.inl (.inr (.inl (.inr f)))::rest) middle b := by
  induction tail generalizing x a b with
  | nil => cases labels; exact Or.inl ⟨[],rfl,.single _ _⟩
  | cons next tail ih =>
    cases labels with
    | cons turn after =>
      rcases turn.right_cases c r with ⟨y,same,localTurn⟩ | ⟨f,arrival,nextEq,contexts⟩
      · subst next
        rcases ih after with ⟨xs,same,inside⟩ | ⟨xs,f,rest,middle,same,inside,last,afterExit⟩
        · exact Or.inl ⟨y::xs,congrArg (Sum.inr y::·) same,.cons localTurn inside⟩
        · refine Or.inr ⟨y::xs,f,rest,middle,congrArg (Sum.inr y::·) same,.cons localTurn inside,?_,afterExit⟩
          simpa only [List.getLast?_cons_cons] using last
      · subst next
        subst contexts
        refine Or.inr ⟨[],f,tail,_,rfl,.single _ _,?_,after⟩
        have same : x=r.wire (.inr (.inl f)) := by
          have wired := congrArg r.wire.mate arrival
          simpa only [Pairing.involutive] using wired
        exact congrArg some same
end
end Lamping.AG

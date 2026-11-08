import Lamping.Lamping.InitialPathConstruction
namespace Lamping.AG
open Graph Lambda
/-- A function FV takes its actual optional sharing-Fan route. -/
def initialFunctionFV (n : Nat) (f arg : Term) (x : FV f) (input : Context) :
    (output : Context) × LocalPath (appPatch n f arg)
      (.inr (.inl (.inr x))) (.inl (.inr ⟨x.val,Or.inl x.property⟩)) input output := by
  by_cases shared : free arg x.val
  · let fan : AppNodes f arg := .inr (.inr ⟨⟨x.val,shared⟩,x.property⟩)
    let output := InitialOffsets.Event.apply (.fan n false) input
    refine ⟨output,⟨[.inr (.inl (.inr (.inl (.inr x)))),.inl ⟨fan,.inl ()⟩],rfl,?_,?_⟩⟩
    · simp [appPatch,appMate,shared,fan,x.property]
    · apply Labelling.cons (b:=output) _ (.single _ _)
      have arrival : (appPatch n f arg).wire (.inr (.inl (.inr (.inl (.inr x)))))=
          .inl ⟨fan,fanO⟩ := by simp [appPatch,appMate,shared,fan,fanO]
      rw [arrival]
      exact .node fan _ _ (.direct (InitialOffsets.Event.apply_rel (.fan n false) input))
  · refine ⟨input,⟨[.inr (.inl (.inr (.inl (.inr x))))],rfl,?_,.single _ _⟩⟩
    simp [appPatch,appMate,shared]

/-- An argument FV takes its actual Bra and optional sharing-Fan route. -/
def initialArgumentFV (n : Nat) (f arg : Term) (x : FV arg) (input : Context) :
    (output : Context) × LocalPath (appPatch n f arg)
      (.inr (.inr (.inr x))) (.inl (.inr ⟨x.val,Or.inr x.property⟩)) input output := by
  let afterBra := InitialOffsets.Event.apply (.bra n) input
  by_cases shared : free f x.val
  · let fan : AppNodes f arg := .inr (.inr ⟨x,shared⟩)
    let output := InitialOffsets.Event.apply (.fan n true) afterBra
    refine ⟨output,⟨[.inr (.inl (.inr (.inr (.inr x)))),.inl ⟨.inr (.inl x),.inl ()⟩,
      .inl ⟨fan,.inl ()⟩],rfl,?_,?_⟩⟩
    · simp [appPatch,appMate,shared,fan,x.property]
    · apply Labelling.cons (b:=afterBra)
        (LabelledTurn.node (g:=appPatch n f arg) (Sum.inr (Sum.inl x)) _ _ (.direct (InitialOffsets.Event.apply_rel (.bra n) input)))
      apply Labelling.cons (b:=output) _ (.single _ _)
      have arrival : (appPatch n f arg).wire (.inl ⟨.inr (.inl x),.inl ()⟩)=.inl ⟨fan,fanStar⟩ := by
        simp [appPatch,appMate,shared,fan,fanStar]
      rw [arrival]
      exact .node fan _ _ (.direct (InitialOffsets.Event.apply_rel (.fan n true) afterBra))
  · refine ⟨afterBra,⟨[.inr (.inl (.inr (.inr (.inr x)))),.inl ⟨.inr (.inl x),.inl ()⟩],rfl,?_,?_⟩⟩
    · simp [appPatch,appMate,shared,x.property]
    · exact .cons (LabelledTurn.node (g:=appPatch n f arg) (Sum.inr (Sum.inl x)) _ _ (.direct (InitialOffsets.Event.apply_rel (.bra n) input))) (.single _ _)
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
/-- A free index above the newly bound variable crosses the actual used
lambda patch without any control node. -/
def initialLambdaUsedFV (n : Nat) (body : Term) (used : free body 0)
    (k : Nat) (present : free body (k+1)) (input : Context) :
    LocalPath (lambdaUsed n body used) (.inr (.inr ⟨k+1,present⟩))
      (.inl (.inr ⟨k,present⟩)) input input where
  edges := [.inr (.inl (.inr (.inr ⟨k+1,present⟩)))]
  start := rfl
  finish := rfl
  labeling := .single _ _

def initialLambdaUnusedFV (n : Nat) (body : Term) (unused : ¬free body 0)
    (k : Nat) (present : free body (k+1)) (input : Context) :
    LocalPath (lambdaUnused n body unused) (.inr (.inr ⟨k+1,present⟩))
      (.inl (.inr ⟨k,present⟩)) input input where
  edges := [.inr (.inl (.inr (.inr ⟨k+1,present⟩)))]
  start := rfl
  finish := rfl
  labeling := .single _ _
end Lamping.AG

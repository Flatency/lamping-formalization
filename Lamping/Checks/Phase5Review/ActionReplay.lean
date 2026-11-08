import Lamping.Lamping.ActionCrossingReplay
import Lamping.Lamping.ActionPassiveReplay
import Lamping.Checks.Phase5Review.ActionShapes
namespace Lamping.Checks.Phase5Review.ActionReplay
open AG Graph ActionShapes

theorem fan_replay (branch : Bool) (shell tail : Context) (x : Level) :
    Labelling (fanRight .app 2 3)
      [.inr (.inl (.inl branch)),.inl ⟨.inl branch,appCtx⟩,.inl ⟨.inr false,.inl ()⟩]
      (shell.replace 2 (tail.cons x)) (shell.replace 2 (tail.cons (if branch then .star x else .o x))) :=
  fanAction_cross_replay .app 2 3 (by decide) branch false _ _ (fan_cross_critical branch shell tail x)

theorem cro_replay (shell tail : Context) :
    Labelling (unaryRightCore .cro .app (Bij.refl _) 2 2)
      [.inr (.inl (.inl ())),.inl ⟨.inl (),appCtx⟩,.inl ⟨.inr false,.inl ()⟩]
      (shell.replace 2 tail) (shell.replace 2 (tail.cons .empty)) :=
  croAction_cross_replay .app 2 3 (by decide) false _ _ (cro_cross_critical shell tail)

theorem bra_replay (shell tail : Context) (x y : Level) :
    Labelling (unaryRightCore .bra .app (Bij.refl _) 2 4)
      [.inr (.inl (.inl ())),.inl ⟨.inl (),appCtx⟩,.inl ⟨.inr false,.inl ()⟩]
      (shell.replace 2 ((tail.cons x).cons y)) (shell.replace 2 (tail.cons (.pair x y))) :=
  braAction_cross_replay .app 2 3 (by decide) false _ _ (bra_cross_critical shell tail x y)

example (tail : Context) := fan_replay false (Context.empty.cons (.star .empty)) tail (.o .empty)
example (tail : Context) := fan_replay true (Context.empty.cons (.star .empty)) tail (.star .empty)
example (tail : Context) := cro_replay (Context.empty.cons (.star .empty)) tail
example (tail : Context) := bra_replay (Context.empty.cons (.star .empty)) tail (.o .empty) (.star .empty)
#print axioms fan_replay
#print axioms cro_replay
#print axioms bra_replay

theorem fan_passive_replay (branch : Bool) (shell tail : Context) (x : Level) :
    Labelling (fanRight .app 2 3)
      [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr branch⟩,
        .inl ⟨.inl branch,appArg⟩,.inl ⟨.inr true,.inl ()⟩]
      (shell.replace 2 (tail.cons (if branch then .star x else .o x)))
      (shell.replace 2 (tail.cons (if branch then .star x else .o x))) := by
  apply fanAction_passive_replay 2 3 branch _ (shell.replace 2 (tail.cons x))
  cases branch with
  | false => exact .inverse (.fanO shell tail x)
  | true => exact .inverse (.fanStar shell tail x)

theorem cro_passive_replay (shell tail : Context) :
    Labelling (unaryRightCore .cro .app (Bij.refl _) 2 2)
      [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr ()⟩,
        .inl ⟨.inl (),appArg⟩,.inl ⟨.inr true,.inl ()⟩]
      (shell.replace 2 (tail.cons .empty)) (shell.replace 2 (tail.cons .empty)) :=
  unaryAction_passive_replay .cro (Bij.refl _) 2 2 _ _ (.inverse (.cro shell tail))

theorem bra_passive_replay (shell tail : Context) (x y : Level) :
    Labelling (unaryRightCore .bra .app (Bij.refl _) 2 4)
      [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr ()⟩,
        .inl ⟨.inl (),appArg⟩,.inl ⟨.inr true,.inl ()⟩]
      (shell.replace 2 (tail.cons (.pair x y))) (shell.replace 2 (tail.cons (.pair x y))) :=
  unaryAction_passive_replay .bra (Bij.refl _) 2 4 _ _ (.inverse (.bra shell tail x y))

example (tail : Context) := fan_passive_replay false (Context.empty.cons (.star .empty)) tail (.o .empty)
example (tail : Context) := fan_passive_replay true (Context.empty.cons (.star .empty)) tail (.star .empty)
example (tail : Context) := cro_passive_replay (Context.empty.cons (.star .empty)) tail
example (tail : Context) := bra_passive_replay (Context.empty.cons (.star .empty)) tail (.o .empty) (.star .empty)
#print axioms fan_passive_replay
#print axioms cro_passive_replay
#print axioms bra_passive_replay
end Lamping.Checks.Phase5Review.ActionReplay


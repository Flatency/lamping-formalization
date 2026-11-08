import Lamping.Lamping.UnaryActionPathShapes
import Lamping.Lamping.ActionCrossingInverse
import Lamping.Lamping.ActionPassiveInverse
import Lamping.Lamping.ActionLocalAncestors
namespace Lamping.Checks.Phase5Review.ActionShapes
open AG Graph

/-- The classifier is invoked on an arbitrary genuine passive local path,
including all passive operator kinds and all actual auxiliary positions. -/
theorem fan_arbitrary_passive_complete (f : Op) (i j : Nat) (q : Aux f)
    (exit : Bool⊕Aux f) (p : LocalPath (fanRight f i j) (.inr q) exit a b) :
    p.edges.length=3 ∨ p.edges.length=4 := by
  rcases fanRight_passive_path_shape f i j q exit p.edges a b p.labeling p.start p.finish with
    short | long
  · obtain ⟨branch,endpoint,same⟩ := short
    exact Or.inl (by rw [same]; rfl)
  · obtain ⟨branch,r,endpoint,same⟩ := long
    exact Or.inr (by rw [same]; rfl)

theorem fan_app_four (i k : Nat) (branch : Bool) (shell tail : Context) (x : Level) :
    (fanActionPassiveApp i k branch shell tail x).edges.length=4 := by
  let p := fanActionPassiveApp i k branch shell tail x
  rcases fanRight_passive_path_shape .app i (i+1+k) false (.inr true) p.edges _ _
      p.labeling p.start p.finish with short | long
  · obtain ⟨chosen,impossible,same⟩ := short
    cases impossible
  · obtain ⟨chosen,r,endpoint,same⟩ := long
    rw [same]
    rfl

theorem cro_app_four (i k : Nat) (shell tail : Context) :
    (croActionPassiveApp i k shell tail).edges.length=4 := by
  let p := croActionPassiveApp i k shell tail
  rcases unaryRight_passive_path_shape .cro .app (Bij.refl _) (Or.inr (Or.inl rfl))
      i (i+1+k-1) false (.inr true) p.edges _ _ p.labeling p.start p.finish with short | long
  · cases short.1
  · obtain ⟨r,endpoint,same⟩ := long
    rw [same]
    rfl

theorem bra_app_four (i k : Nat) (shell tail : Context) (x y : Level) :
    (braActionPassiveApp i k shell tail x y).edges.length=4 := by
  let p := braActionPassiveApp i k shell tail x y
  rcases unaryRight_passive_path_shape .bra .app (Bij.refl _) (Or.inr (Or.inr rfl))
      i (i+1+k+1) false (.inr true) p.edges _ _ p.labeling p.start p.finish with short | long
  · cases short.1
  · obtain ⟨r,endpoint,same⟩ := long
    rw [same]
    rfl

/-- Shape classification cannot manufacture labels for an empty fan head. -/
example : ¬Nonempty (LocalPath (fanRight .app 0 3) (.inr false) (.inr true)
    Context.empty Context.empty) := by
  rintro ⟨p⟩
  rcases fanRight_passive_path_shape .app 0 3 false (.inr true) p.edges _ _
      p.labeling p.start p.finish with short | long
  · obtain ⟨branch,impossible,same⟩ := short
    cases impossible
  · obtain ⟨branch,r,endpoint,same⟩ := long
    have labels := p.labeling
    rw [same] at labels
    have marked := Labelling.first_marked (g:=fanRight .app 0 3) labels
    exact marked rfl

/-- Keeping the ordinary-labelled prefix does not make it a complete local
path: the first three segments have not yet exited the RHS. -/
example (branch : Bool) (shell tail : Context) (x : Level) :
    (fanActionPassiveApp 2 1 branch shell tail x).edges.take 3 ≠
      (fanActionPassiveApp 2 1 branch shell tail x).edges := by
  intro same
  have lengths := congrArg List.length same
  change 3=4 at lengths
  omega
example (branch : Bool) (shell tail : Context) (x : Level) :
    ((fanActionPassiveApp 2 1 branch shell tail x).edges.take 3).getLast? ≠
      some ((fanRight .app 2 4).wire (.inr (.inl (.inr true)))) := by
  intro impossible
  cases impossible

example (branch : Bool) (tail : Context) :
    (fanActionPassiveApp 2 1 branch (Context.empty.cons (.star .empty)) tail (.o .empty)).edges.length=4 :=
  fan_app_four _ _ _ _ _ _
example (tail : Context) :
    (croActionPassiveApp 2 1 (Context.empty.cons (.star .empty)) tail).edges.length=4 := cro_app_four _ _ _ _
example (tail : Context) :
    (braActionPassiveApp 2 1 (Context.empty.cons (.star .empty)) tail (.o .empty) (.star .empty)).edges.length=4 :=
  bra_app_four _ _ _ _ _ _

#print axioms fan_arbitrary_passive_complete
#print axioms fan_app_four
#print axioms cro_app_four
#print axioms bra_app_four
#print axioms unaryRight_active_path_shape
#print axioms unaryRight_passive_path_shape
/-- The exact A/B assignment is transported at the critical strict gap j=i+1. -/
theorem fan_cross_critical (branch : Bool) (shell tail : Context) (x : Level) :
    Labelling (leftNet .fan .app 2 3) (leftRoute .fan .app 2 3 branch false)
      (shell.replace 2 (tail.cons x))
      (shell.replace 2 (tail.cons (if branch then .star x else .o x))) := by
  have actual := (fanActionPaths .app 2 0 false branch shell tail tail x (.inverse (.appFun tail))).2.labeling
  exact fanAction_cross_inverse .app 2 3 (by decide) branch false _ _ actual

theorem cro_cross_critical (shell tail : Context) :
    Labelling (leftNet .cro .app 2 3) (leftRoute .cro .app 2 3 () false)
      (shell.replace 2 tail) (shell.replace 2 (tail.cons .empty)) := by
  have actual := (croActionPaths .app 2 0 false shell tail tail (.inverse (.appFun tail))).2.labeling
  exact croAction_cross_inverse .app 2 3 (by decide) false _ _ actual

theorem bra_cross_critical (shell tail : Context) (x y : Level) :
    Labelling (leftNet .bra .app 2 3) (leftRoute .bra .app 2 3 () false)
      (shell.replace 2 ((tail.cons x).cons y)) (shell.replace 2 (tail.cons (.pair x y))) := by
  have actual := (braActionPaths .app 2 0 false shell tail tail x y (.inverse (.appFun tail))).2.labeling
  exact braAction_cross_inverse .app 2 3 (by decide) false _ _ actual

example (shell tail : Context) :
    shell.replace 2 (tail.cons (.star .empty)) ≠
      shell.replace 2 ((tail.cons (.star .empty)).cons .empty) := by
  intro equal
  have impossible := congrArg (fun c : Context => c.get 2) equal
  change Level.star .empty=Level.empty at impossible
  cases impossible
#print axioms fan_cross_critical
#print axioms cro_cross_critical
#print axioms bra_cross_critical
theorem fan_passive_critical (branch : Bool) (shell tail : Context) (x : Level) :
    Labelling (leftNet .fan .app 2 3) [.inr (.inl (.inr false)),.inl ⟨.inr (),appArg⟩]
      (shell.replace 2 (tail.cons (if branch then .star x else .o x)))
      (shell.replace 2 (tail.cons (if branch then .star x else .o x))) := by
  have actual := (fanActionPassiveApp 2 0 branch shell tail x).labeling
  exact fanAction_passive_inverse .app 2 3 branch false true _ _ actual

theorem cro_passive_critical (shell tail : Context) :
    Labelling (leftNet .cro .app 2 3) [.inr (.inl (.inr false)),.inl ⟨.inr (),appArg⟩]
      (shell.replace 2 (tail.cons .empty)) (shell.replace 2 (tail.cons .empty)) := by
  have actual := (croActionPassiveApp 2 0 shell tail).labeling
  exact unaryAction_passive_inverse .cro .app (Bij.refl _) 2 2 3 false true _ _ actual

theorem bra_passive_critical (shell tail : Context) (x y : Level) :
    Labelling (leftNet .bra .app 2 3) [.inr (.inl (.inr false)),.inl ⟨.inr (),appArg⟩]
      (shell.replace 2 (tail.cons (.pair x y))) (shell.replace 2 (tail.cons (.pair x y))) := by
  have actual := (braActionPassiveApp 2 0 shell tail x y).labeling
  exact unaryAction_passive_inverse .bra .app (Bij.refl _) 2 4 3 false true _ _ actual
#print axioms fanAction_passive_inverse
#print axioms unaryAction_passive_inverse
#print axioms fan_passive_critical
#print axioms cro_passive_critical
#print axioms bra_passive_critical
/-- All passive operators' genuine high traversals also test the reverse-entry
branch of the complete LocalPath assembler, preserving the reversed A/B. -/
theorem fan_arbitrary_reverse (f : Op) (i k : Nat) (q : Aux f) (branch : Bool)
    (shell a b : Context) (x : Level) (rule : Traversal k (.op f) (.inl ()) (.inr q) a b) :
    Nonempty (LocalPath (leftNet .fan f i (i+1+k)) (.inr q) (.inl branch)
      (shell.replace i (b.cons (if branch then .star x else .o x))) (shell.replace i (a.cons x))) :=
  fanAction_local_ancestor f i (i+1+k) (by omega) (.inr q) (.inl branch) _ _
    (fanActionPaths f i k q branch shell a b x rule).2.reverse

theorem cro_arbitrary_reverse (f : Op) (i k : Nat) (q : Aux f) (shell a b : Context)
    (rule : Traversal k (.op f) (.inl ()) (.inr q) a b) :
    Nonempty (LocalPath (leftNet .cro f i (i+1+k)) (.inr q) (.inl ())
      (shell.replace i (b.cons .empty)) (shell.replace i a)) :=
  croAction_local_ancestor f i (i+1+k) (by omega) (.inr q) (.inl ()) _ _
    (croActionPaths f i k q shell a b rule).2.reverse

theorem bra_arbitrary_reverse (f : Op) (i k : Nat) (q : Aux f) (shell a b : Context) (x y : Level)
    (rule : Traversal k (.op f) (.inl ()) (.inr q) a b) :
    Nonempty (LocalPath (leftNet .bra f i (i+1+k)) (.inr q) (.inl ())
      (shell.replace i (b.cons (.pair x y))) (shell.replace i ((a.cons x).cons y))) :=
  braAction_local_ancestor f i (i+1+k) (by omega) (.inr q) (.inl ()) _ _
    (braActionPaths f i k q shell a b x y rule).2.reverse

example (branch : Bool) (shell tail : Context) (x : Level) :
    Nonempty (LocalPath (leftNet .fan .app 2 3) (.inr false) (.inr true)
      (shell.replace 2 (tail.cons (if branch then .star x else .o x)))
      (shell.replace 2 (tail.cons (if branch then .star x else .o x)))) :=
  fanAction_local_ancestor .app 2 3 (by decide) _ _ _ _ (fanActionPassiveApp 2 0 branch shell tail x)
example (shell tail : Context) :
    Nonempty (LocalPath (leftNet .cro .app 2 3) (.inr false) (.inr true)
      (shell.replace 2 (tail.cons .empty)) (shell.replace 2 (tail.cons .empty))) :=
  croAction_local_ancestor .app 2 3 (by decide) _ _ _ _ (croActionPassiveApp 2 0 shell tail)
example (shell tail : Context) (x y : Level) :
    Nonempty (LocalPath (leftNet .bra .app 2 3) (.inr false) (.inr true)
      (shell.replace 2 (tail.cons (.pair x y))) (shell.replace 2 (tail.cons (.pair x y)))) :=
  braAction_local_ancestor .app 2 3 (by decide) _ _ _ _ (braActionPassiveApp 2 0 shell tail x y)
#print axioms fanAction_local_ancestor
#print axioms croAction_local_ancestor
#print axioms braAction_local_ancestor
#print axioms fan_arbitrary_reverse
end Lamping.Checks.Phase5Review.ActionShapes






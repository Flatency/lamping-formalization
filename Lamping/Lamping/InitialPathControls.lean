import Lamping.Lamping.InitialPaths
import Lamping.Lamping.PathSiteTransport
namespace Lamping.AG
open Graph Lambda

/-- The actual variable encoding inserts an empty level at n on its control input. -/
def initialVarPath (n k : Nat) (shell tail : Context) :
    LocalPath (varNet n k) (.inl ()) (.inr ⟨k,rfl⟩)
      (shell.replace n tail) (shell.replace n (tail.cons .empty)) where
  edges := [.inr (.inl (.inl ())),.inl ⟨(),.inl ()⟩]
  start := rfl
  finish := rfl
  labeling := .cons (LabelledTurn.node (g := varNet n k) () (.inr ()) (.inl ())
    (.direct (.cro shell tail))) (.single _ _)

theorem initialVarPath_forward (n k : Nat) (shell tail : Context) :
    Forward (varNet n k) (initialVarPath n k shell tail).edges :=
  .node () (.inr ()) (.inl ()) rfl rfl True.intro (.single _)

def initialLambdaUsedBody (n : Nat) (b : Term) (used : free b 0) (a : Context) :
    LocalPath (lambdaUsed n b used) (.inl (.inl ())) (.inr (.inl ())) a a where
  edges := [.inr (.inl (.inl (.inl ()))),.inl ⟨(),lamBody⟩]
  start := rfl
  finish := rfl
  labeling := .cons (LabelledTurn.node (g := lambdaUsed n b used) () (.inl ()) lamBody
    (.direct (.lamBody a))) (.single _ _)

def initialLambdaUnusedBody (n : Nat) (b : Term) (unused : ¬free b 0) (a : Context) :
    LocalPath (lambdaUnused n b unused) (.inl (.inl ())) (.inr (.inl ())) a a where
  edges := [.inr (.inl (.inl (.inl ()))),.inl ⟨.inl (),lamBody⟩]
  start := rfl
  finish := rfl
  labeling := .cons (LabelledTurn.node (g := lambdaUnused n b unused) (.inl ()) (.inl ()) lamBody
    (.direct (.lamBody a))) (.single _ _)

def initialAppFunction (n : Nat) (f a : Term) (ctx : Context) :
    LocalPath (appPatch n f a) (.inl (.inl ())) (.inr (.inl (.inl ()))) ctx ctx where
  edges := [.inr (.inl (.inl (.inl ()))),.inl ⟨.inl (),.inl ()⟩]
  start := rfl
  finish := rfl
  labeling := .cons (LabelledTurn.node (g := appPatch n f a) (.inl ()) appCtx (.inl ())
    (.direct (.appFun ctx))) (.single _ _)

def initialAppArgument (n : Nat) (f a : Term) (ctx : Context) :
    LocalPath (appPatch n f a) (.inl (.inl ())) (.inr (.inr (.inl ()))) ctx ctx where
  edges := [.inr (.inl (.inl (.inl ()))),.inl ⟨.inl (),appArg⟩]
  start := rfl
  finish := rfl
  labeling := .cons (LabelledTurn.node (g := appPatch n f a) (.inl ()) appCtx appArg
    (.direct (.appArg ctx))) (.single _ _)

section Glue
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R]
  [FiniteNames B] [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B ⊕ F) W) (r : Net signature R F V)

def plugLeft (e : Endpoint c) : Endpoint (plug c r) := plugEnd c.label r.label (.inl e)
theorem plugLeft_wire (e : Endpoint c) :
    (plug c r).wire (plugLeft c r e) = plugLeft c r (c.wire e) :=
  Pairing.rename_apply _ _ _

theorem LabelledTurn.plugLeft {x y : Endpoint c} {a b : Context}
    (h : LabelledTurn c x y a b) :
    LabelledTurn (plug c r) (AG.plugLeft c r x) (AG.plugLeft c r y) a b := by
  cases h with
  | node n p q ht => exact LabelledTurn.node (g := plug c r) (.inl n) p q ht
  | transparent w d a => exact LabelledTurn.transparent (g := plug c r) (.inl (.inl w)) d a

theorem Labelling.plugLeft {es : List (Endpoint c)} {a b : Context}
    (h : Labelling c es a b) : Labelling (plug c r) (es.map (AG.plugLeft c r)) a b := by
  induction h with
  | single e a => exact .single _ a
  | cons ht _ ih =>
    have ht' := LabelledTurn.plugLeft (c := c) (r := r) ht
    rw [← plugLeft_wire] at ht'
    exact .cons ht' ih

theorem plug_frontier_turn (x : F) (a : Context) :
    LabelledTurn (plug c r) (.inr (.inr (.inr x,false)))
      (.inr (.inr (.inr x,true))) a a :=
  LabelledTurn.transparent (g := plug c r) (.inr x) false a
end Glue

/-- General initial binding-loop base, on the actual recursively glued encoding
of lambda 0. This does not claim all of Exercise 3.5.25. -/
def identityBindingLoop (n : Nat) (shell tail : Context) :
    BindingLoop (encode n (.lam (.var 0))).net
      [.inl ⟨.inl (),lamBody⟩,
       .inr (.inr (.inr (.inl ()),true)),
       .inl ⟨.inr (),.inl ()⟩,
       .inr (.inr (.inr (.inr ⟨0,rfl⟩),false))]
      (shell.replace n tail) (shell.replace n (tail.cons .empty)) where
  binder := .inl ()
  isLam := rfl
  body := lamBody
  bind := lamBind
  body_role := HEq.rfl
  bind_role := HEq.rfl
  start := rfl
  finish := rfl
  proper := .cons
    (LabelledTurn.transparent (g := (encode n (.lam (.var 0))).net) (.inr (.inl ())) false _)
    (.cons (LabelledTurn.node (g := (encode n (.lam (.var 0))).net) (.inr ()) (.inr ()) (.inl ())
      (.direct (.cro shell tail)))
      (.cons (LabelledTurn.transparent (g := (encode n (.lam (.var 0))).net)
        (.inr (.inr ⟨0,rfl⟩)) true _) (.single _ _)))
  forward := .transparent (.inr (.inl ())) false rfl rfl
    (.node (.inr ()) (.inr ()) (.inl ()) rfl rfl True.intro
      (.transparent (.inr (.inr ⟨0,rfl⟩)) true rfl rfl (.single _)))
  shell := by intro k hk; change k < n at hk; simp [Context.replace,hk]

end Lamping.AG

import Lamping.Lamping.Context
import Lamping.Lamping.PathRewrite
namespace Lamping.AG
open Graph
/-- The six configurations in AG98 Def.3.4.2, in the printed forward direction. -/
inductive Passage (i : Nat) : (k : Kind) → Port k → Port k → Context → Context → Prop
  | fanO (a b : Context) (x : Level) : Passage i (.op .fan) fanO (.inl ())
      (a.replace i (b.cons x)) (a.replace i (b.cons (.o x)))
  | fanStar (a b : Context) (x : Level) : Passage i (.op .fan) fanStar (.inl ())
      (a.replace i (b.cons x)) (a.replace i (b.cons (.star x)))
  | cro (a b : Context) : Passage i (.op .cro) (.inr ()) (.inl ())
      (a.replace i b) (a.replace i (b.cons .empty))
  | bra (a b : Context) (x y : Level) : Passage i (.op .bra) (.inr ()) (.inl ())
      (a.replace i ((b.cons x).cons y)) (a.replace i (b.cons (.pair x y)))
  | appFun (a) : Passage i (.op .app) appCtx (.inl ()) a a
  | appArg (a) : Passage i (.op .app) appCtx appArg a a
  | lamBody (a) : Passage i (.op .lam) (.inl ()) lamBody a a
/-- Control passages can face either way. Proper-node reversals are recorded explicitly. -/
inductive Traversal (i : Nat) : (k : Kind) → Port k → Port k → Context → Context → Prop
  | direct {k p q a b} : Passage i k p q a b → Traversal i k p q a b
  | inverse {k p q a b} : Passage i k p q a b → Traversal i k q p b a
namespace Traversal
theorem reverse {i k p q a b} (h : Traversal i k p q a b) : Traversal i k q p b a := by
  cases h with
  | direct h => exact .inverse h
  | inverse h => exact .direct h
theorem distinct {i k p q a b} (h : Traversal i k p q a b) : p ≠ q := by
  cases h with
  | direct h => cases h <;> (intro e; cases e)
  | inverse h => cases h <;> (intro e; cases e)
end Traversal
/-- Exact direction convention, independent of labels; binding is never a turn. -/
def ForwardPorts : (k : Kind) → Port k → Port k → Prop
  | .op .app,p,q => p=appCtx ∧ (q=(.inl ()) ∨ q=appArg)
  | .op .lam,p,q => p=(.inl ()) ∧ q=lamBody
  | .op .fan,_,_ | .op .cro,_,_ | .op .bra,_,_ => True
  | .garbage,_,_ => False
section NetPaths
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
abbrev Endpoint := End signature N B W g.label
/-- Consecutive directed segments: the first arrives at x, the next leaves at y. -/
inductive Turn : (Endpoint g) → (Endpoint g) → Prop
  | node (n : N) (p q : Port (g.label n).sort) (different : p≠q) :
      Turn (.inl ⟨n,p⟩) (.inl ⟨n,q⟩)
  | transparent (w : W) (d : Bool) : Turn (.inr (.inr (w,d))) (.inr (.inr (w,!d)))
/-- A path stores directed segment occurrences, so repeated edges remain repeated. -/
inductive Walk : List (Endpoint g) → Prop
  | single (e) : Walk [e]
  | cons {e f es} : Turn g (g.wire e) f → Walk (f::es) → Walk (e::f::es)
/-- A labelled turn has genuine graph incidence and the AG context relation. -/
inductive LabelledTurn : (Endpoint g) → (Endpoint g) → Context → Context → Prop
  | node (n : N) (p q : Port (g.label n).sort) {a b}
      (rule : Traversal (g.label n).index (g.label n).sort p q a b) :
      LabelledTurn (.inl ⟨n,p⟩) (.inl ⟨n,q⟩) a b
  | transparent (w : W) (d : Bool) (a) :
      LabelledTurn (.inr (.inr (w,d))) (.inr (.inr (w,!d))) a a
namespace LabelledTurn
theorem turn {x y a b} (h : LabelledTurn g x y a b) : Turn g x y := by
  cases h with
  | node n p q rule => exact .node n p q rule.distinct
  | transparent w d a => exact .transparent w d
theorem reverse {x y a b} (h : LabelledTurn g x y a b) : LabelledTurn g y x b a := by
  cases h with
  | node n p q rule => exact .node n q p rule.reverse
  | transparent w d a => simpa using LabelledTurn.transparent (g:=g) w (!d) a
end LabelledTurn
/-- Labels are witnesses, not part of path identity. A single segment has any context. -/
inductive Labelling : List (Endpoint g) → Context → Context → Prop
  | single (e) (a) : Labelling [e] a a
  | cons {e f es a b c} : LabelledTurn g (g.wire e) f a b →
      Labelling (f::es) b c → Labelling (e::f::es) a c
def ProperPath (es : List (Endpoint g)) : Prop := ∃ a b, Labelling g es a b
/-- All local proper-node turns have the forward orientation. -/
inductive Forward : List (Endpoint g) → Prop
  | single (e) : Forward [e]
  | node {e f es} (n : N) (p q : Port (g.label n).sort)
      (arrives : g.wire e=.inl ⟨n,p⟩) (leaves : f=.inl ⟨n,q⟩)
      (direction : ForwardPorts (g.label n).sort p q) : Forward (f::es) → Forward (e::f::es)
  | transparent {e f es} (w : W) (d : Bool)
      (arrives : g.wire e=.inr (.inr (w,d))) (leaves : f=.inr (.inr (w,!d))) :
      Forward (f::es) → Forward (e::f::es)
def ForwardProperPath (es : List (Endpoint g)) : Prop := ProperPath g es ∧ Forward g es
/-- A loop remembers the same physical lambda and the two endpoint occurrences. -/
structure BindingLoop (es : List (Endpoint g)) (a b : Context) where
  binder : N
  isLam : (g.label binder).sort=.op .lam
  body : Port (g.label binder).sort
  bind : Port (g.label binder).sort
  body_role : HEq body lamBody
  bind_role : HEq bind lamBind
  start : es.head?=some (.inl ⟨binder,body⟩)
  finish : es.getLast?=some (g.wire (.inl ⟨binder,bind⟩))
  proper : Labelling g es a b
  forward : Forward g es
  shell : Context.SameShell (g.label binder).index a b
end NetPaths
end Lamping.AG



namespace Lamping.AG
open Graph
/-- Roles of the proper-node endpoint occurrences used in Prop.3.5.4. -/
inductive ProperRole where
  | root | appCtx | appFun | appArg | lamCtx | lamBody | lamBind
  deriving DecidableEq
namespace ProperRole
def outgoing : ProperRole → Prop
  | .root | .appFun | .appArg | .lamBody => True
  | _ => False
def incoming : ProperRole → Prop
  | .appCtx | .lamCtx | .lamBind => True
  | _ => False
def terminalWidth (n : Nat) : ProperRole → Nat
  | .lamBind => n+1
  | _ => n
end ProperRole
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W) (root : B)
/-- An endpoint role is checked against an actual port and label, not a node name
 chosen independently of the graph. Root is the designated boundary only. -/
inductive AtProperRole : Endpoint g → ProperRole → Nat → Prop
  | root : AtProperRole (.inr (.inl root)) .root 0
  | appCtx (n : N) (p : Port (g.label n).sort) (i : Nat)
      (lab : g.label n=label .app i) (role : HEq p AG.appCtx) : AtProperRole (.inl ⟨n,p⟩) .appCtx i
  | appFun (n : N) (p : Port (g.label n).sort) (i : Nat)
      (lab : g.label n=label .app i) (role : HEq p (Sum.inl () : Port (.op .app))) : AtProperRole (.inl ⟨n,p⟩) .appFun i
  | appArg (n : N) (p : Port (g.label n).sort) (i : Nat)
      (lab : g.label n=label .app i) (role : HEq p AG.appArg) : AtProperRole (.inl ⟨n,p⟩) .appArg i
  | lamCtx (n : N) (p : Port (g.label n).sort) (i : Nat)
      (lab : g.label n=label .lam i) (role : HEq p (Sum.inl () : Port (.op .lam))) : AtProperRole (.inl ⟨n,p⟩) .lamCtx i
  | lamBody (n : N) (p : Port (g.label n).sort) (i : Nat)
      (lab : g.label n=label .lam i) (role : HEq p AG.lamBody) : AtProperRole (.inl ⟨n,p⟩) .lamBody i
  | lamBind (n : N) (p : Port (g.label n).sort) (i : Nat)
      (lab : g.label n=label .lam i) (role : HEq p AG.lamBind) : AtProperRole (.inl ⟨n,p⟩) .lamBind i
/-- The precise OLD-GRAPH source property of AG98 Prop.3.5.4, not a transport
 certificate and not a theorem about arbitrary graphs. Future SND must prove it. -/
def Independence : Prop :=
  ∀ (es : List (Endpoint g)) (e f : Endpoint g) (sr tr : ProperRole) (m n : Nat)
    (a b : Context),
    es.head?=some e → es.getLast?=some (g.wire f) →
    AtProperRole g root e sr m → sr.outgoing →
    AtProperRole g root f tr n → tr.incoming →
    Forward g es → Labelling g es a b →
    (∀ x, ∃ b', Labelling g es (a.replace m x) b') ∧
    ∃ width, m≤width ∧ (sr=.appArg → m<width) ∧
      (∀ c, b=b.replace (tr.terminalWidth n) c → a=a.replace width c) ∧
      (∀ y, Labelling g es (a.replace width y) (b.replace (tr.terminalWidth n) y))
end
end Lamping.AG

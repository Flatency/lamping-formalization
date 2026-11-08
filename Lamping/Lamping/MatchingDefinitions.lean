import Lamping.Lamping.ExpandedPaths
import Lamping.Lamping.PathSplicing
import Lamping.Lambda.Occurrences
namespace Lamping.AG
open Graph Lambda

/-- The observable syntax at a proper endpoint; variable indices are retained. -/
inductive AccessShape where
  | app | lam | var (index : Nat)
  deriving DecidableEq, Repr
inductive AccessKind where
  | app | lam | var
  deriving DecidableEq, Repr

def AccessShape.kind : AccessShape → AccessKind
  | .app => .app | .lam => .lam | .var _ => .var

def syntaxShape : Term → AccessShape
  | .app _ _ => .app | .lam _ => .lam | .var k => .var k

/-- Tokens of a proper-node turn. Controls emit no syntax edge. -/
def portWord : (k : Kind) → Port k → Port k → Path
  | .op .app, .inr false, .inl () => [.fn]
  | .op .app, .inr false, .inr true => [.arg]
  | .op .lam, .inl (), .inr true => [.body]
  | _, _, _ => []

def portKind : (k : Kind) → Port k → Option AccessKind
  | .op .app, .inr false => some .app
  | .op .lam, .inl () => some .lam
  | .op .lam, .inr false => some .var
  | _, _ => none

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

/-- At a genuine walk turn the arriving and leaving node coincide. Thus the
arriving port and the leaving port determine the syntax token without node equality. -/
def arrivalWord : Endpoint g → Path
  | .inl ⟨n,p⟩ =>
    match (g.label n).sort, p with
    | .op .app, .inl () => [.fn]
    | .op .app, .inr true => [.arg]
    | .op .lam, .inr true => [.body]
    | _, _ => []
  | _ => []

/-- Only departures following actual turns emit syntax tokens; the first
segment starts at the boundary and the last arrival is a terminal observation. -/
def accessWord : List (Endpoint g) → Path
  | [] => []
  | _ :: es => es.flatMap (arrivalWord g)

def accessKind (es : List (Endpoint g)) : Option AccessKind :=
  es.getLast?.bind fun e =>
    match g.wire e with
    | .inl ⟨n,p⟩ => portKind (g.label n).sort p
    | _ => none

/-- A root access ends at an application context, lambda context, or binding
port. Repeated visits and transparent segments remain part of path identity. -/
def IsRootAccess (root : B) (es : List (Endpoint g)) : Prop :=
  ForwardProperPath g es ∧ es.head? = some (.inr (.inl root)) ∧
    ∃ k, accessKind g es = some k
abbrev RootAccess (root : B) := {es : List (Endpoint g) // IsRootAccess g root es}

/-- The chosen suffix begins at an actual body departure; the preceding
segment reaches the same lambda context. The full path's labelling is split at
this occurrence, so an unrelated relabelling of a suffix cannot select a binder. -/
def BindingSuffix (es : List (Endpoint g)) (index : Nat) : Prop :=
  ∃ (pre loop : List (Endpoint g)) (a b c : Context)
    (binding : BindingLoop g loop b c)
    (ctx : Port (g.label binding.binder).sort),
    es = pre ++ loop ∧
    HEq ctx (Sum.inl () : Port (.op .lam)) ∧
    pre.getLast? = some (g.wire (.inl ⟨binding.binder,ctx⟩)) ∧
    Labelling g pre a b ∧
    index = binderDepth (accessWord g loop)

private theorem lambda_body_turn (k : Kind) (i : Nat) (ctx body : Port k)
    (isLam : k = .op .lam)
    (hc : HEq ctx (Sum.inl () : Port (.op .lam))) (hb : HEq body lamBody) (a : Context) :
    Traversal i k ctx body a a := by
  subst k
  have hc' : ctx = .inl () := eq_of_heq hc
  have hb' : body = lamBody := eq_of_heq hb
  subst ctx; subst body
  exact .direct (.lamBody a)

/-- The prefix/suffix seam is a genuine lambda-body passage. This is about
BindingSuffix witnesses only, and does not assert that arbitrary paths have one. -/
theorem BindingSuffix.labelling {es : List (Endpoint g)} {k : Nat}
    (h : BindingSuffix g es k) : ProperPath g es := by
  obtain ⟨pre,loop,a,b,c,binding,ctx,he,hctx,hpre,hlabels,_⟩ := h
  obtain ⟨xs,hxs⟩ := List.getLast?_eq_some_iff.mp hpre
  obtain ⟨ys,hys⟩ := List.head?_eq_some_iff.mp binding.start
  have seam : LabelledTurn g (.inl ⟨binding.binder,ctx⟩)
      (.inl ⟨binding.binder,binding.body⟩) b b :=
    .node binding.binder ctx binding.body
      (lambda_body_turn _ _ _ _ binding.isLam hctx binding.body_role b)
  refine ⟨a,c,?_⟩
  rw [hxs] at hlabels
  have labels := binding.proper
  rw [hys] at labels
  have glued := hlabels.splice labels (by simpa only [g.wire.involutive] using seam)
  simpa only [he,hxs,hys,List.append_assoc,List.singleton_append] using glued
/-- Variables additionally identify their unique binding *occurrence*, measured
by the number of subsequent lambda-body turns, rather than by physical node name. -/
def Observes (es : List (Endpoint g)) (shape : AccessShape) : Prop :=
  accessKind g es = some shape.kind ∧
    match shape with
    | .var k => BindingSuffix g es k ∧ ∀ j, BindingSuffix g es j → j = k
    | _ => True

/-- Definition 3.5.13: same proper-node order and ports, and the variable's binder. -/
def Corresponds (es : List (Endpoint g)) (t : Term) (p : Position t) : Prop :=
  accessWord g es = p.val ∧
    ∃ u, subtermAt t p.val = some u ∧ Observes g es (syntaxShape u)

/-- Prefixes are required only between actual proper-ended root accesses. -/
def Matches (root : B) (t : Term) : Prop :=
  ∃ f : Bij (RootAccess g root) (Position t),
    (∀ es, Corresponds g es.val t (f es)) ∧
    (∀ es fs, (∃ suffix, fs.val = es.val ++ suffix) →
      ∃ q, (f fs).val = (f es).val ++ q)

 theorem Observes.unique {es : List (Endpoint g)} {a b : AccessShape}
    (ha : Observes g es a) (hb : Observes g es b) : a = b := by
  rcases ha with ⟨hka,ha⟩
  rcases hb with ⟨hkb,hb⟩
  have hk : a.kind = b.kind := Option.some.inj (hka.symm.trans hkb)
  cases a <;> cases b <;> simp_all [AccessShape.kind]

 theorem Corresponds.word {es : List (Endpoint g)} {t : Term} {p : Position t}
    (h : Corresponds g es t p) : accessWord g es = p.val := h.1

 theorem Matches.observation {root : B} {t : Term} (h : Matches g root t)
    (p : Position t) :
    ∃ es : RootAccess g root, accessWord g es.val = p.val ∧
      ∃ u, subtermAt t p.val = some u ∧ Observes g es.val (syntaxShape u) := by
  obtain ⟨f,hf,_⟩ := h
  refine ⟨f.invFun p, ?_⟩
  have hc := hf (f.invFun p)
  rw [f.right_inv] at hc
  exact hc
end
end Lamping.AG



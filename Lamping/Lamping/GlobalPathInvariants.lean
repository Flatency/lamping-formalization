import Lamping.Lamping.MatchingDefinitions
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

/-- One actual context per directed segment occurrence. Repeated physical
edges have separate positions in both lists. -/
inductive ContextTrace : List (Endpoint g) → List Context → Prop where
  | single (e a) : ContextTrace [e] [a]
  | cons {e f es a b cs} (turn : LabelledTurn g (g.wire e) f a b)
      (tail : ContextTrace (f::es) (b::cs)) : ContextTrace (e::f::es) (a::b::cs)

theorem ContextTrace.length {es cs} (trace : ContextTrace g es cs) : es.length=cs.length := by
  induction trace with
  | single => rfl
  | cons turn tail ih => simpa only [List.length_cons] using congrArg Nat.succ ih

theorem Labelling.contextTrace {es : List (Endpoint g)} {a b : Context} (labels : Labelling g es a b) :
    ∃ cs,ContextTrace g es cs ∧ cs.head?=some a ∧ cs.getLast?=some b := by
  induction labels with
  | single e a => exact ⟨[a],.single _ _,rfl,rfl⟩
  | @cons e f es a b c turn tail ih =>
    obtain ⟨cs,trace,first,last⟩ := ih
    cases cs with
    | nil => cases first
    | cons x cs =>
      have equal : x=b := Option.some.inj first
      cases equal
      exact ⟨a::b::cs,.cons turn trace,rfl,by simpa only [List.getLast?_cons_cons] using last⟩

theorem ContextTrace.labelling {es : List (Endpoint g)} {cs : List Context}
    (trace : ContextTrace g es cs) (first : cs.head?=some a) (last : cs.getLast?=some b) :
    Labelling g es a b := by
  induction trace generalizing a b with
  | single e c =>
    have sameA : c=a := Option.some.inj first
    have sameB : c=b := Option.some.inj last
    cases sameA; cases sameB
    exact .single _ _
  | cons turn tail ih =>
    have same := Option.some.inj first
    cases same
    exact .cons turn (ih rfl (by simpa only [List.getLast?_cons_cons] using last))

/-- Only forward incoming context-port occurrences are compared. In
particular a reversed beta traversal is not treated as a second arrival. -/
def Nesting (root : B) : Prop :=
  ∀ (es : List (Endpoint g)) (cs : List Context),ContextTrace g es cs →
    es.head?=some (.inr (.inl root)) → Forward g es →
    ∀ (i j : Nat) (e : Endpoint g) (a b : Context) (n : Nat) (role : ProperRole),
      i<j → es[i]?=some e → es[j]?=some e → cs[i]?=some a → cs[j]?=some b →
      (role=.appCtx ∨ role=.lamCtx) → AtProperRole g root (g.wire e) role n →
      ¬Context.SameShell n a b

/-- Every given rooted proper labelling ending at a binding port has a
binding-loop suffix with the very same seam and final contexts. -/
def Transparency (root : B) : Prop :=
  ∀ (es : List (Endpoint g)) (a b : Context) (n : N)
    (ctx body bind : Port (g.label n).sort),
    (g.label n).sort=.op .lam → HEq ctx (Sum.inl () : Port (.op .lam)) →
    HEq body lamBody → HEq bind lamBind →
    es.head?=some (.inr (.inl root)) → es.getLast?=some (g.wire (.inl ⟨n,bind⟩)) →
    Forward g es → Labelling g es a b →
    ∃ (pre loop : List (Endpoint g)) (middle : Context) (binding : BindingLoop g loop middle b),
      es=pre++loop ∧ binding.binder=n ∧
      pre.getLast?=some (g.wire (.inl ⟨n,ctx⟩)) ∧ Labelling g pre a middle

/-- The ordinary OLD-GRAPH hypotheses of AG3.5.17. This is a theorem target
for reachable graphs, never a presumed field of the graph representation. -/
structure OrdinaryPathInvariants (root : B) : Prop where
  independence : Independence g root
  nesting : Nesting g root
  transparency : Transparency g root
end
end Lamping.AG

import Lamping.Lamping.GlobalPathInvariants
import Lamping.Lamping.GeneratedExpandedLoops
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

/-- Expanded turns retain one context for every physical segment occurrence. -/
inductive ExpandedContextTrace : List (Endpoint g) → List Context → Prop where
  | single (e a) : ExpandedContextTrace [e] [a]
  | cons {e f es a b cs} (turn : ExpandedTurn g (g.wire e) f a b)
      (tail : ExpandedContextTrace (f::es) (b::cs)) :
      ExpandedContextTrace (e::f::es) (a::b::cs)

 theorem ExpandedContextTrace.length {es cs} (h : ExpandedContextTrace g es cs) :
    es.length=cs.length := by
  induction h with
  | single => rfl
  | cons turn tail ih => simpa only [List.length_cons] using congrArg Nat.succ ih

 theorem ContextTrace.expanded {es cs} (h : ContextTrace g es cs) : ExpandedContextTrace g es cs := by
  induction h with
  | single e a => exact .single e a
  | cons turn tail ih => exact .cons (.ordinary turn) ih

 theorem ExpandedLabelling.contextTrace {es : List (Endpoint g)} {a b : Context}
    (h : ExpandedLabelling g es a b) :
    ∃ cs, ExpandedContextTrace g es cs ∧ cs.head?=some a ∧ cs.getLast?=some b := by
  induction h with
  | single e a => exact ⟨[a],.single _ _,rfl,rfl⟩
  | @cons e f es a b c turn tail ih =>
    obtain ⟨cs,trace,first,last⟩ := ih
    cases cs with
    | nil => cases first
    | cons x cs =>
      have equal : x=b := Option.some.inj first
      cases equal
      exact ⟨a::b::cs,.cons turn trace,rfl,by simpa only [List.getLast?_cons_cons] using last⟩

 theorem ExpandedContextTrace.labelling {es : List (Endpoint g)} {cs : List Context}
    (trace : ExpandedContextTrace g es cs) (first : cs.head?=some a) (last : cs.getLast?=some b) :
    ExpandedLabelling g es a b := by
  induction trace generalizing a b with
  | single e c =>
    have ha : c=a := Option.some.inj first
    have hb : c=b := Option.some.inj last
    cases ha; cases hb
    exact .single _ _
  | cons turn tail ih =>
    have same := Option.some.inj first
    cases same
    exact .cons turn (ih rfl (by simpa only [List.getLast?_cons_cons] using last))

/-- Proper outgoing ports and the departure of a reversed physical beta route.
Only the latter and application arguments demand a strictly wider tail. -/
inductive ExpandedSource (root : B) : Endpoint g → Nat → Bool → Prop where
  | proper (e : Endpoint g) (role : ProperRole) (index : Nat)
      (atPort : AtProperRole g root e role index) (outgoing : role.outgoing) :
      ExpandedSource root e index (decide (role=.appArg))
  | reversed (r : BetaEdge g) : ExpandedSource root r.ctxEnd r.index true

/-- For a binding arrival or the end of a reversed beta route, the terminal
width is n+1; context ports use n. The physical reverse route can have W vertices. -/
inductive ExpandedTarget (root : B) : Endpoint g → Nat → Prop where
  | proper (e : Endpoint g) (role : ProperRole) (index : Nat)
      (atPort : AtProperRole g root (g.wire e) role index) (incoming : role.incoming) :
      ExpandedTarget root e (role.terminalWidth index)
  | reversed (r : BetaEdge g) (e : Endpoint g)
      (finish : e = g.wire r.funEnd) : ExpandedTarget root e (r.index+1)


/-- Typed-terminal existence is independent of given-assignment independence.
No generic labellability claim is imposed on arbitrary partial control paths. -/
def ExpandedTerminalLabellability (root : B) : Prop :=
  ∀ es, GeneratedExpandedProperPath g root es →
    ∀ last width, es.getLast?=some last → ExpandedTarget g root last width →
      ∃ a b, ExpandedLabelling g es a b
/-- Exact direction of Lemma3.5.17 independence: a source tail determines
the terminal tail. This is deliberately opposite the ordinary Prop3.5.4 premise. -/
def ExpandedIndependence (root : B) : Prop :=
  ∀ (es : List (Endpoint g)) (cs : List Context),
    GeneratedExpandedProperPath g root es → ExpandedContextTrace g es cs →
    ∀ (i : Nat) (e last : Endpoint g) (a b : Context) (m terminalWidth : Nat) (strict : Bool),
      es[i]?=some e → cs[i]?=some a → es.getLast?=some last → cs.getLast?=some b →
      ExpandedSource g root e m strict → ExpandedTarget g root last terminalWidth →
      (∀ x, ∃ ds, ExpandedContextTrace g es ds ∧ ds[i]?=some (a.replace m x)) ∧
      ∃ width, m≤width ∧ (strict=true → m<width) ∧
        (∀ c, a=a.replace width c → b=b.replace terminalWidth c) ∧
        (∀ y, ∃ ds, ExpandedContextTrace g es ds ∧
          ds[i]?=some (a.replace width y) ∧ ds.getLast?=some (b.replace terminalWidth y))

/-- A single-path induction conclusion. Generation is supplied separately,
so a constructor induction uses its two path hypotheses without assuming the
global expanded theorem it is trying to prove. -/
def ExpandedIndependenceOn (root : B) (es : List (Endpoint g)) : Prop :=
  ∀ (cs : List Context), ExpandedContextTrace g es cs →
    ∀ (i : Nat) (e last : Endpoint g) (a b : Context) (m terminalWidth : Nat) (strict : Bool),
      es[i]?=some e → cs[i]?=some a → es.getLast?=some last → cs.getLast?=some b →
      ExpandedSource g root e m strict → ExpandedTarget g root last terminalWidth →
      (∀ x, ∃ ds, ExpandedContextTrace g es ds ∧ ds[i]?=some (a.replace m x)) ∧
      ∃ width, m≤width ∧ (strict=true → m<width) ∧
        (∀ c, a=a.replace width c → b=b.replace terminalWidth c) ∧
        (∀ y, ∃ ds, ExpandedContextTrace g es ds ∧
          ds[i]?=some (a.replace width y) ∧ ds.getLast?=some (b.replace terminalWidth y))

 theorem ExpandedIndependence.on {root : B} (indep : ExpandedIndependence g root)
     {es : List (Endpoint g)} (generated : GeneratedExpandedProperPath g root es) :
     ExpandedIndependenceOn g root es := by
  intro cs trace
  exact indep es cs generated trace
/-- Context-port visits are forward visits. The reversal's lamCtx departure
ends at appFun, so it is excluded by these actual incoming-role tests. -/
def ExpandedNesting (root : B) : Prop :=
  ∀ (es : List (Endpoint g)) (cs : List Context),
    GeneratedExpandedProperPath g root es → ExpandedContextTrace g es cs →
    ∀ (i j : Nat) (e : Endpoint g) (a b : Context) (n : Nat) (role : ProperRole),
      i<j → es[i]?=some e → es[j]?=some e → cs[i]?=some a → cs[j]?=some b →
      (role=.appCtx ∨ role=.lamCtx) → AtProperRole g root (g.wire e) role n →
      ¬Context.SameShell n a b

/-- The suffix and its seam contexts are taken from the given expanded
labelling, with the physical binder retained. -/
def ExpandedTransparency (root : B) : Prop :=
  ∀ (es : List (Endpoint g)) (a b : Context) (n : N)
    (ctx body bind : Port (g.label n).sort),
    (g.label n).sort=.op .lam → HEq ctx (Sum.inl () : Port (.op .lam)) →
    HEq body lamBody → HEq bind lamBind →
    GeneratedExpandedProperPath g root es →
    es.getLast?=some (g.wire (.inl ⟨n,bind⟩)) → ExpandedLabelling g es a b →
    ∃ (pre loop : List (Endpoint g)) (middle : Context)
      (binding : ExpandedBindingLoop g loop middle b),
      es=pre++loop ∧ binding.binder=n ∧
      pre.getLast?=some (g.wire (.inl ⟨n,ctx⟩)) ∧ ExpandedLabelling g pre a middle
end
end Lamping.AG





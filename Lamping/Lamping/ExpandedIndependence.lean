import Lamping.Lamping.ExpandedInvariantBase
namespace Lamping.AG.Context

/-- A replacement fixed point says exactly which tail the context contains. -/
theorem replace_fixed_iff_tail (a c : Context) (n : Nat) :
    a=a.replace n c ↔ a.tail n=c := by
  constructor
  · intro h
    ext k
    have hk := congrArg (fun d : Context => d.get (n+k)) h
    simpa only [tail,replace_high _ _ (by omega : n≤n+k),Nat.add_sub_cancel_left] using hk
  · intro h
    rw [←h]
    exact (replace_tail a n).symm

/-- Ordinary independence's tail implication is symmetric once all tails are
quantified: both formulas identify the same source and terminal tails. -/
theorem tail_implication_reverse (a b : Context) (m n : Nat)
    (h : ∀ c, b=b.replace n c → a=a.replace m c) :
    ∀ c, a=a.replace m c → b=b.replace n c := by
  have ha : a.tail m=b.tail n :=
    (replace_fixed_iff_tail a (b.tail n) m).mp (h _ (replace_tail b n).symm)
  intro c hc
  apply (replace_fixed_iff_tail b c n).mpr
  exact ha.symm.trans ((replace_fixed_iff_tail a c m).mp hc)
end Lamping.AG.Context

namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Split at one selected segment, retaining it in both pieces and retaining
the actual seam context. All repeated physical occurrences remain distinct. -/
theorem Labelling.split_segment {pre post : List (Endpoint g)} {e : Endpoint g}
    (h : Labelling g (pre++e::post) a b) :
    ∃ middle, Labelling g (pre++[e]) a middle ∧ Labelling g (e::post) middle b := by
  induction pre generalizing a with
  | nil => exact ⟨a,.single _ _,h⟩
  | cons x pre ih =>
    cases pre with
    | nil =>
      cases h with
      | cons turn tail => exact ⟨_,.cons turn (.single _ _),tail⟩
    | cons y pre =>
      cases h with
      | cons turn tail =>
        obtain ⟨middle,first,last⟩ := ih tail
        exact ⟨middle,.cons turn first,last⟩

 theorem ExpandedLabelling.split_segment {pre post : List (Endpoint g)} {e : Endpoint g}
    (h : ExpandedLabelling g (pre++e::post) a b) :
    ∃ middle, ExpandedLabelling g (pre++[e]) a middle ∧
      ExpandedLabelling g (e::post) middle b := by
  induction pre generalizing a with
  | nil => exact ⟨a,.single _ _,h⟩
  | cons x pre ih =>
    cases pre with
    | nil =>
      cases h with
      | cons turn tail => exact ⟨_,.cons turn (.single _ _),tail⟩
    | cons y pre =>
      cases h with
      | cons turn tail =>
        obtain ⟨middle,first,last⟩ := ih tail
        exact ⟨middle,.cons turn first,last⟩

/-- Ordinary source independence already gives the forward tail direction
needed at the terminal edge of Lemma3.5.17. This lemma is for a path starting
at the selected source; lifting its relabelling over a root prefix is separate. -/
theorem Independence.forward_tail {root : B} (indep : Independence g root)
    (es : List (Endpoint g)) (e f : Endpoint g) (sr tr : ProperRole) (m n : Nat)
    (a b : Context) (start : es.head?=some e) (finish : es.getLast?=some (g.wire f))
    (source : AtProperRole g root e sr m) (outgoing : sr.outgoing)
    (target : AtProperRole g root f tr n) (incoming : tr.incoming)
    (fw : Forward g es) (labels : Labelling g es a b) :
    (∀ x, ∃ b', Labelling g es (a.replace m x) b') ∧
    ∃ width, m≤width ∧ (sr=.appArg → m<width) ∧
      (∀ c, a=a.replace width c → b=b.replace (tr.terminalWidth n) c) ∧
      (∀ y, Labelling g es (a.replace width y) (b.replace (tr.terminalWidth n) y)) := by
  obtain ⟨relabel,width,lower,strict,oldDirection,sync⟩ :=
    indep es e f sr tr m n a b start finish source outgoing target incoming fw labels
  exact ⟨relabel,width,lower,strict,Context.tail_implication_reverse _ _ _ _ oldDirection,sync⟩

/-- Once both existence and expanded independence have been established,
root level zero gives every input context on a proper/reversed-terminal path.
The terminal hypothesis is essential; no such claim is made for all prefixes. -/
theorem ExpandedIndependence.root_input {root : B}
    (indep : ExpandedIndependence g root)
    {es : List (Endpoint g)} (generated : GeneratedExpandedProperPath g root es)
    {a b : Context} (labels : ExpandedLabelling g es a b)
    (last : Endpoint g) (width : Nat) (finish : es.getLast?=some last)
    (terminal : ExpandedTarget g root last width) (input : Context) :
    ∃ output, ExpandedLabelling g es input output := by
  obtain ⟨cs,trace,first,lastCtx⟩ := labels.contextTrace g
  have source : ExpandedSource g root (.inr (.inl root)) 0 false :=
    .proper _ .root 0 (.root) True.intro
  have start : es[0]?=some (.inr (.inl root)) := by
    cases es <;> simpa using generated.rooted g
  have contextStart : cs[0]?=some a := by
    cases cs with
    | nil => cases first
    | cons => exact first
  obtain ⟨arbitrary,_⟩ := indep es cs generated trace 0 (.inr (.inl root)) last a b 0 width false
    start contextStart finish lastCtx source terminal
  obtain ⟨ds,relabel,atRoot⟩ := arbitrary input
  have firstInput : ds.head?=some input := by
    cases ds with
    | nil => cases atRoot
    | cons => simpa using atRoot
  cases hd : ds.getLast? with
  | none =>
    have empty := List.getLast?_eq_none_iff.mp hd
    rw [empty] at firstInput
    cases firstInput
  | some output => exact ⟨output,relabel.labelling g firstInput hd⟩
end
end Lamping.AG




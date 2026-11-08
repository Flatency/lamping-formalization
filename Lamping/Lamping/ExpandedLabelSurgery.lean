import Lamping.Lamping.PathLabelDeterminism
import Lamping.Lamping.ConstantPathLabelling
namespace Lamping.AG
open Graph Lambda
namespace Context
 theorem replace_of_sameShell (a b : Context) (n : Nat) (h : SameShell n a b) :
    a.replace n (b.tail n)=b := by
  ext k
  by_cases low : k<n
  · simpa only [replace_low _ _ low] using h k low
  · rw [replace_high _ _ (by omega)]
    change b.get (n+(k-n))=b.get k
    congr 1
    omega
end Context

private theorem head_drop {T : Type} (xs : List T) (i : Nat) :
    (xs.drop i).head?=xs[i]? := by
  induction i generalizing xs with
  | zero => cases xs <;> rfl
  | succ i ih => cases xs with
    | nil => rfl
    | cons x xs => simpa only [List.drop_succ_cons,List.getElem?_cons_succ] using ih xs

private theorem access_at_append {T : Type} (xs : List T) (e : T) (ys : List T) :
    (xs++e::ys)[xs.length]?=some e := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.cons_append,List.length_cons,List.getElem?_cons_succ] using ih

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

 theorem ExpandedContextTrace.start_labelling {es : List (Endpoint g)} {cs : List Context}
    (trace : ExpandedContextTrace g es cs) (first : cs.head?=some a) :
    ∃ b, ExpandedLabelling g es a b := by
  induction trace generalizing a with
  | single e c =>
    have eq : c=a := Option.some.inj first
    cases eq
    exact ⟨_,.single _ _⟩
  | cons turn tail ih =>
    have eq := Option.some.inj first
    cases eq
    obtain ⟨b,hb⟩ := ih rfl
    exact ⟨b,.cons turn hb⟩

 theorem ExpandedContextTrace.drop {es : List (Endpoint g)} {cs : List Context}
    (trace : ExpandedContextTrace g es cs) (i : Nat) (within : i<es.length) :
    ExpandedContextTrace g (es.drop i) (cs.drop i) := by
  induction trace generalizing i with
  | single e a =>
    cases i with
    | zero => exact .single e a
    | succ i => simp at within
  | cons turn tail ih =>
    cases i with
    | zero => exact .cons turn tail
    | succ i =>
      exact ih i (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using within)

 theorem ExpandedContextTrace.suffix_labelling {es : List (Endpoint g)} {cs : List Context}
    (trace : ExpandedContextTrace g es cs) (i : Nat) (within : i<es.length)
    (point : cs[i]?=some a) : ∃ b, ExpandedLabelling g (es.drop i) a b := by
  apply (trace.drop i within).start_labelling
  exact (head_drop cs i).trans point

/-- Exact backward-beta surgery. The body end context is carried unchanged
through every transparent reverse segment and is the argument suffix input. -/
theorem BetaEdge.insert_labeling (r : BetaEdge g) (pre loop suffix : List (Endpoint g))
    (body : ExpandedLabelling g (pre++r.principal++loop) a b)
    (loopEnd : loop.getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩)))
    (argumentTail : ExpandedLabelling g (r.argEnd::suffix) b c) :
    ExpandedLabelling g (pre++r.principal++loop++r.reverseRoute++[r.argEnd]++suffix) a c := by
  have bodyEnd : (pre++r.principal++loop).getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩)) := by
    simp only [List.getLast?_append,loopEnd,Option.some_or]
  have first : ExpandedLabelling g ((pre++r.principal++loop)++r.reverseRoute) a b := by
    apply body.splice bodyEnd (r.reverse_labeling b).expanded r.reverse_start
    simpa only [Pairing.involutive] using ExpandedTurn.bindToCtx (g:=g) r b
  have firstEnd : ((pre++r.principal++loop)++r.reverseRoute).getLast?=some (g.wire r.funEnd) := by
    simp only [List.getLast?_append,r.reverse_finish,Option.some_or]
  have final := first.splice firstEnd argumentTail rfl
    (by simpa only [Pairing.involutive] using ExpandedTurn.funToArg (g:=g) r b)
  simpa only [List.append_assoc,List.singleton_append] using final

/-- Use a *proper/reversed-terminal* argument-path independence hypothesis to
obtain a newly labelled suffix at the same selected physical occurrence. This
is one induction-step component, not a theorem asserting independence itself. -/
theorem ExpandedIndependence.argument_suffix {root : B}
    (indep : ExpandedIndependence g root) (r : BetaEdge g) (pre suffix : List (Endpoint g))
    (generated : GeneratedExpandedProperPath g root (pre++r.argEnd::suffix))
    (cs : List Context) (trace : ExpandedContextTrace g (pre++r.argEnd::suffix) cs)
    (a b desired : Context) (point : cs[pre.length]?=some a) (lastCtx : cs.getLast?=some b)
    (last : Endpoint g) (width : Nat)
    (finish : (pre++r.argEnd::suffix).getLast?=some last)
    (terminal : ExpandedTarget g root last width)
    (shell : Context.SameShell r.index a desired) :
    ∃ output, ExpandedLabelling g (r.argEnd::suffix) desired output := by
  have source : ExpandedSource g root r.argEnd r.index true :=
    .proper _ .appArg _ (.appArg r.app r.appArg r.index r.appLabel r.appArg_role) True.intro
  obtain ⟨relabel,_⟩ := indep _ cs generated trace pre.length r.argEnd last a b r.index width true
    (access_at_append pre _ suffix) point finish lastCtx source terminal
  obtain ⟨ds,next,atPoint⟩ := relabel (desired.tail r.index)
  rw [Context.replace_of_sameShell a desired r.index shell] at atPoint
  have within : pre.length<(pre++r.argEnd::suffix).length := by simp
  obtain ⟨output,labels⟩ := next.suffix_labelling pre.length within atPoint
  refine ⟨output,?_⟩
  simpa using labels
/-- Single-path version usable as a constructor induction hypothesis. No
global expanded theorem is required to relabel this actual argument suffix. -/
theorem ExpandedIndependenceOn.argument_suffix {root : B}
    (r : BetaEdge g) (pre suffix : List (Endpoint g))
    (indep : ExpandedIndependenceOn g root (pre++r.argEnd::suffix))
    (cs : List Context) (trace : ExpandedContextTrace g (pre++r.argEnd::suffix) cs)
    (a b desired : Context) (point : cs[pre.length]?=some a) (lastCtx : cs.getLast?=some b)
    (last : Endpoint g) (width : Nat) (finish : (pre++r.argEnd::suffix).getLast?=some last)
    (terminal : ExpandedTarget g root last width) (shell : Context.SameShell r.index a desired) :
    ∃ output,ExpandedLabelling g (r.argEnd::suffix) desired output := by
  have source : ExpandedSource g root r.argEnd r.index true :=
    .proper _ .appArg _ (.appArg r.app r.appArg r.index r.appLabel r.appArg_role) True.intro
  obtain ⟨relabel,_⟩ := indep cs trace pre.length r.argEnd last a b r.index width true
    (access_at_append pre _ suffix) point finish lastCtx source terminal
  obtain ⟨ds,next,atPoint⟩ := relabel (desired.tail r.index)
  rw [Context.replace_of_sameShell a desired r.index shell] at atPoint
  obtain ⟨output,labels⟩ := next.suffix_labelling pre.length (by simp) atPoint
  exact ⟨output,by simpa using labels⟩

/-- Complete insertion assembly once the *actual* common-root seam shell is
established. That shell is an explicit remaining geometric obligation, not a
consequence of an unrelated BindingLoop witness assignment. -/
theorem BetaEdge.insert_with_argument_independence {root : B}
    (r : BetaEdge g) (pre loop suffix : List (Endpoint g))
    (indep : ExpandedIndependenceOn g root (pre++r.argEnd::suffix))
    (cs : List Context) (trace : ExpandedContextTrace g (pre++r.argEnd::suffix) cs)
    (input seam endBody oldOutput : Context)
    (body : ExpandedLabelling g (pre++r.principal++loop) input endBody)
    (loopEnd : loop.getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩)))
    (point : cs[pre.length]?=some seam) (lastCtx : cs.getLast?=some oldOutput)
    (last : Endpoint g) (width : Nat) (finish : (pre++r.argEnd::suffix).getLast?=some last)
    (terminal : ExpandedTarget g root last width) (shell : Context.SameShell r.index seam endBody) :
    ∃ output,ExpandedLabelling g
      (pre++r.principal++loop++r.reverseRoute++[r.argEnd]++suffix) input output := by
  obtain ⟨output,tail⟩ := indep.argument_suffix r pre suffix cs trace seam oldOutput endBody
    point lastCtx last width finish terminal shell
  exact ⟨output,r.insert_labeling pre loop suffix body loopEnd tail⟩

/-- Any physical cut within the reversed principal route carries the actual
body-end context unchanged. Label existence is inherited from the labelled
body, without demanding universal input on an arbitrary longer partial path. -/
theorem BetaEdge.insert_reverse_prefix_labeling (r : BetaEdge g) (pre loop cut tail : List (Endpoint g))
    (decomp : r.reverseRoute=cut++tail)
    (body : ExpandedLabelling g (pre++r.principal++loop) a b)
    (loopEnd : loop.getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩))) :
    ExpandedLabelling g (pre++r.principal++loop++cut) a b := by
  cases cut with
  | nil => simpa only [List.append_nil] using body
  | cons x cut =>
    have reverseLabels := r.reverse_constant_labelling b
    rw [decomp] at reverseLabels
    have labels : Labelling g (x::cut) b b := (reverseLabels.prefix (by simp)).label
    have first : (x::cut).head?=some r.ctxEnd := by simpa only [decomp,List.cons_append] using r.reverse_start
    have endBody : (pre++r.principal++loop).getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩)) := by
      simp only [List.getLast?_append,loopEnd,Option.some_or]
    exact body.splice endBody labels.expanded first
      (by simpa only [Pairing.involutive] using ExpandedTurn.bindToCtx (g:=g) r b)
end
end Lamping.AG




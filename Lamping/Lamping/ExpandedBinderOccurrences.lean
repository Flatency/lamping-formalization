import Lamping.Lamping.TraceSeams
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

 theorem ExpandedContextTrace.take_succ {es cs} (trace : ExpandedContextTrace g es cs)
     (i : Nat) {a : Context} (atA : cs[i]?=some a) :
     ExpandedContextTrace g (es.take (i+1)) (cs.take (i+1)) := by
  induction trace generalizing i with
  | single e c => cases i with
    | zero => exact .single e c
    | succ i => simp at atA
  | cons turn tail ih => cases i with
    | zero => exact .single _ _
    | succ i => exact .cons turn (ih i atA)

 theorem ExpandedContextTrace.prefix_labels {es cs} (trace : ExpandedContextTrace g es cs)
     (i : Nat) {a input : Context} (atA : cs[i]?=some a) (head : cs.head?=some input) :
     ExpandedLabelling g (es.take (i+1)) input a := by
  apply (trace.take_succ i atA).labelling g
  · cases cs with
    | nil => cases head
    | cons => exact head
  · simp only [List.getLast?_take,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,
      Nat.add_sub_cancel,atA,Option.some_or]

/-- The supplied prefix label is reflected into the supplied full trace at
its precise ordinal; repeated physical edges are never identified here. -/
theorem ExpandedContextTrace.labelled_prefix_point {es pre tail : List (Endpoint g)}
    {ds : List Context} (trace : ExpandedContextTrace g es ds)
    {input middle : Context} (head : ds.head?=some input)
    (decomp : es=pre++tail) (nonempty : pre≠[]) (labels : ExpandedLabelling g pre input middle) :
    ds[pre.length-1]?=some middle := by
  have positive : 0<pre.length := List.length_pos_iff.mpr nonempty
  have within : pre.length-1<ds.length := by
    have length := trace.length g
    rw [decomp,List.length_append] at length
    omega
  let actual := ds[pre.length-1]
  have atActual : ds[pre.length-1]?=some actual := List.getElem?_eq_getElem within
  have prefixLabels := trace.prefix_labels (pre.length-1) atActual head
  have takeEq : es.take (pre.length-1+1)=pre := by
    rw [Nat.sub_add_cancel (by omega),decomp,List.take_left]
  rw [takeEq] at prefixLabels
  have same := prefixLabels.output_unique labels
  simpa only [same] using atActual

/-- Two actual same-assignment binding candidates ending at one context-port
edge and sharing the final binder shell must be the same root occurrence. -/
theorem ExpandedNesting.binding_prefix_unique {root : B} (nest : ExpandedNesting g root)
    {es : List (Endpoint g)} {ds : List Context} (generated : GeneratedExpandedProperPath g root es)
    (trace : ExpandedContextTrace g es ds) (input final a b : Context) (head : ds.head?=some input)
    (pre tail other rest : List (Endpoint g)) (first : es=pre++tail) (second : es=other++rest)
    (preNonempty : pre≠[]) (otherNonempty : other≠[])
    (preLabel : ExpandedLabelling g pre input a) (otherLabel : ExpandedLabelling g other input b)
    (e : Endpoint g) (preEnd : pre.getLast?=some e) (otherEnd : other.getLast?=some e)
    (role : ProperRole) (index : Nat) (context : role=.appCtx ∨role=.lamCtx)
    (atRole : AtProperRole g root (g.wire e) role index)
    (preShell : Context.SameShell index a final) (otherShell : Context.SameShell index b final) :
    pre.length=other.length := by
  have positive := List.length_pos_iff.mpr preNonempty
  have otherPositive := List.length_pos_iff.mpr otherNonempty
  have point := trace.labelled_prefix_point head first preNonempty preLabel
  have otherPoint := trace.labelled_prefix_point head second otherNonempty otherLabel
  have atE : es[pre.length-1]?=some e := by
    rw [first,List.getElem?_append_left (by omega)]
    exact (List.getLast?_eq_getElem?).symm.trans preEnd
  have otherAtE : es[other.length-1]?=some e := by
    rw [second,List.getElem?_append_left (by omega)]
    exact (List.getLast?_eq_getElem?).symm.trans otherEnd
  have shell : Context.SameShell index a b := by
    intro k low
    exact (preShell k low).trans (otherShell k low).symm
  apply Classical.byContradiction
  intro different
  rcases Nat.lt_or_gt_of_ne different with lt | gt
  · exact nest es ds generated trace (pre.length-1) (other.length-1) e a b index role
      (by omega) atE otherAtE point otherPoint context atRole shell
  · exact nest es ds generated trace (other.length-1) (pre.length-1) e b a index role
      (by omega) otherAtE atE otherPoint point context atRole (by intro k low; exact (shell k low).symm)
/-- Equal actual binder occurrences recover the literal ordered prefix and
suffix lists, so their access words and de Bruijn distances also agree. -/
theorem ExpandedNesting.binding_split_unique {root : B} (nest : ExpandedNesting g root)
    {es : List (Endpoint g)} {ds : List Context} (generated : GeneratedExpandedProperPath g root es)
    (trace : ExpandedContextTrace g es ds) (input final a b : Context) (head : ds.head?=some input)
    (pre tail other rest : List (Endpoint g)) (first : es=pre++tail) (second : es=other++rest)
    (preNonempty : pre≠[]) (otherNonempty : other≠[])
    (preLabel : ExpandedLabelling g pre input a) (otherLabel : ExpandedLabelling g other input b)
    (e : Endpoint g) (preEnd : pre.getLast?=some e) (otherEnd : other.getLast?=some e)
    (role : ProperRole) (index : Nat) (context : role=.appCtx ∨role=.lamCtx)
    (atRole : AtProperRole g root (g.wire e) role index)
    (preShell : Context.SameShell index a final) (otherShell : Context.SameShell index b final) :
    pre=other ∧tail=rest := by
  have len := nest.binding_prefix_unique generated trace input final a b head pre tail other rest
    first second preNonempty otherNonempty preLabel otherLabel e preEnd otherEnd role index context atRole preShell otherShell
  have left : es.take pre.length=pre := by rw [first,List.take_left]
  have right : es.take pre.length=other := by rw [len,second,List.take_left]
  have same : pre=other := left.symm.trans right
  refine ⟨same,?_⟩
  rw [←same] at second
  have ordered := congrArg (List.drop pre.length) (first.symm.trans second)
  simpa only [List.drop_left] using ordered
end
end Lamping.AG




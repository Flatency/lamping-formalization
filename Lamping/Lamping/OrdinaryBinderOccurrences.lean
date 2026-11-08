import Lamping.Lamping.MarkerBinderUniform
import Lamping.Lamping.OrdinaryPrefixRelabelling
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Two actual same-assignment binding candidates ending at one context-port
edge and sharing the final binder shell must be the same root occurrence. -/
theorem Nesting.binding_prefix_unique {root : B} (nest : Nesting g root)
    {es : List (Endpoint g)} {ds : List Context} (rooted : es.head?=some (.inr (.inl root))) (forward : Forward g es)
    (trace : ContextTrace g es ds) (input final a b : Context) (head : ds.head?=some input)
    (pre tail other rest : List (Endpoint g)) (first : es=pre++tail) (second : es=other++rest)
    (preNonempty : pre≠[]) (otherNonempty : other≠[])
    (preLabel : Labelling g pre input a) (otherLabel : Labelling g other input b)
    (e : Endpoint g) (preEnd : pre.getLast?=some e) (otherEnd : other.getLast?=some e)
    (role : ProperRole) (index : Nat) (context : role=.appCtx ∨role=.lamCtx)
    (atRole : AtProperRole g root (g.wire e) role index)
    (preShell : Context.SameShell index a final) (otherShell : Context.SameShell index b final) :
    pre.length=other.length := by
  have positive := List.length_pos_iff.mpr preNonempty
  have otherPositive := List.length_pos_iff.mpr otherNonempty
  have point := trace.expanded.labelled_prefix_point head first preNonempty preLabel.expanded
  have otherPoint := trace.expanded.labelled_prefix_point head second otherNonempty otherLabel.expanded
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
  · exact nest es ds trace rooted forward (pre.length-1) (other.length-1) e a b index role
      (by omega) atE otherAtE point otherPoint context atRole shell
  · exact nest es ds trace rooted forward (other.length-1) (pre.length-1) e b a index role
      (by omega) otherAtE atE otherPoint point context atRole (by intro k low; exact (shell k low).symm)
/-- Equal actual binder occurrences recover the literal ordered prefix and
suffix lists, so their access words and de Bruijn distances also agree. -/
theorem Nesting.binding_split_unique {root : B} (nest : Nesting g root)
    {es : List (Endpoint g)} {ds : List Context} (rooted : es.head?=some (.inr (.inl root))) (forward : Forward g es)
    (trace : ContextTrace g es ds) (input final a b : Context) (head : ds.head?=some input)
    (pre tail other rest : List (Endpoint g)) (first : es=pre++tail) (second : es=other++rest)
    (preNonempty : pre≠[]) (otherNonempty : other≠[])
    (preLabel : Labelling g pre input a) (otherLabel : Labelling g other input b)
    (e : Endpoint g) (preEnd : pre.getLast?=some e) (otherEnd : other.getLast?=some e)
    (role : ProperRole) (index : Nat) (context : role=.appCtx ∨role=.lamCtx)
    (atRole : AtProperRole g root (g.wire e) role index)
    (preShell : Context.SameShell index a final) (otherShell : Context.SameShell index b final) :
    pre=other ∧tail=rest := by
  have len := nest.binding_prefix_unique rooted forward trace input final a b head pre tail other rest
    first second preNonempty otherNonempty preLabel otherLabel e preEnd otherEnd role index context atRole preShell otherShell
  have left : es.take pre.length=pre := by rw [first,List.take_left]
  have right : es.take pre.length=other := by rw [len,second,List.take_left]
  have same : pre=other := left.symm.trans right
  refine ⟨same,?_⟩
  rw [←same] at second
  have ordered := congrArg (List.drop pre.length) (first.symm.trans second)
  simpa only [List.drop_left] using ordered
/-- Different assignments select the same literal binder occurrence, provided
both are genuine same-lambda shell candidates. The second candidate's shell
is transported at its original ordinal, then ordinary Nesting compares them. -/
theorem OrdinaryPathInvariants.binder_split_unique {root : B}
    (invariants : OrdinaryPathInvariants g root)
    (node : N) (ctx body bind : Port (g.label node).sort) (level : Nat)
    (nodeLabel : g.label node=label .lam level)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (bodyRole : HEq body lamBody) (bindRole : HEq bind lamBind)
    (es pre loop other rest : List (Endpoint g))
    (input middle output otherInput otherMiddle otherOutput : Context)
    (rooted : es.head?=some (.inr (.inl root))) (forward : Forward g es)
    (finish : es.getLast?=some (g.wire (.inl ⟨node,bind⟩)))
    (firstLabels : Labelling g es input output)
    (secondLabels : Labelling g es otherInput otherOutput)
    (first : es=pre++loop) (second : es=other++rest)
    (prefixLabels : Labelling g pre input middle)
    (otherLabels : Labelling g other otherInput otherMiddle)
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (otherEnd : other.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (shell : Context.SameShell level middle output)
    (otherShell : Context.SameShell level otherMiddle otherOutput) :
    pre=other ∧ loop=rest := by
  obtain ⟨cs,trace,head,_last⟩ := firstLabels.contextTrace g
  have otherNonempty := otherLabels.nonempty
  have positive := List.length_pos_iff.mpr otherNonempty
  have within : other.length-1<cs.length := by
    have lengths := trace.length g
    rw [second,List.length_append] at lengths
    omega
  let chosen := cs[other.length-1]
  have point : cs[other.length-1]?=some chosen := List.getElem?_eq_getElem within
  have otherAtInput := trace.prefix_labels (other.length-1) point head
  have takeEq : es.take (other.length-1+1)=other := by
    rw [Nat.sub_add_cancel (by omega),second,List.take_left]
  rw [takeEq] at otherAtInput
  have transported := Marker.binder_shell_stable_node invariants.independence invariants.nesting
    invariants.transparency node ctx body bind level nodeLabel ctxRole bodyRole bindRole
    es other rest otherInput otherMiddle otherOutput rooted forward finish secondLabels second
    otherLabels otherEnd otherShell input chosen output firstLabels otherAtInput
  have atRole : AtProperRole g root (g.wire (g.wire (.inl ⟨node,ctx⟩))) .lamCtx level := by
    simpa only [Pairing.involutive] using
      AtProperRole.lamCtx (g:=g) (root:=root) node ctx level nodeLabel ctxRole
  exact invariants.nesting.binding_split_unique rooted forward trace input output middle chosen head
    pre loop other rest first second prefixLabels.nonempty otherNonempty prefixLabels otherAtInput
    (g.wire (.inl ⟨node,ctx⟩)) prefixEnd otherEnd .lamCtx level (Or.inr rfl) atRole shell transported
end
end Lamping.AG

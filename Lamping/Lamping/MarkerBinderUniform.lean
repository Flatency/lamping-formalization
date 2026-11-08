import Lamping.Lamping.MarkerBinderCandidates
namespace Lamping.AG.Marker
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

private theorem expression_point {es : List (Endpoint g)} {expressions : List ExprContext}
    (input : Context) (trace : ContextTrace g es (expressions.map (fun c => c.eval input)))
    (i : Nat) (within : i<es.length) :
    (expressions.map (fun c => c.eval input))[i]? =
      some ((expressions[i]?.getD ExprContext.initial).eval input) := by
  have lengths := trace.length g
  rw [List.length_map] at lengths
  have valid : i<expressions.length := by omega
  let here := expressions[i]
  have atHere : expressions[i]?=some here := List.getElem?_eq_getElem valid
  simp only [List.getElem?_map,atHere,Option.map_some,Option.getD_some]

private theorem expression_prefix_value {es pre tail : List (Endpoint g)} {expressions : List ExprContext}
    (input middle : Context) (trace : ContextTrace g es (expressions.map (fun c => c.eval input)))
    (first : expressions.head?=some ExprContext.initial) (split : es=pre++tail)
    (nonempty : pre≠[]) (labels : Labelling g pre input middle) :
    ((expressions[pre.length-1]?.getD ExprContext.initial).eval input)=middle := by
  have traceFirst : (expressions.map (fun c => c.eval input)).head?=some input := by
    rw [List.head?_map,first]
    simp
  have point := trace.expanded.labelled_prefix_point traceFirst split nonempty labels.expanded
  rw [List.getElem?_map] at point
  cases atHere : expressions[pre.length-1]? with
  | none => rw [atHere] at point; cases point
  | some here =>
    rw [atHere] at point
    exact Option.some.inj point

/-- Shell stability for the SAME ordinary rooted binder occurrence across
assignments. Total labels come from the typed root-to-binding use of old I;
old T plus finite marker separation produces a uniform actual ordinal, and
old Nesting identifies it with the given original prefix ordinal. This does
not promote an unrelated BindingLoop witness to all assignments. -/
theorem binder_shell_stable (independence : Independence g root) (nesting : Nesting g root)
    (transparency : Transparency g root) (edge : BetaEdge g)
    (es pre tail : List (Endpoint g)) (input middle output : Context)
    (rooted : es.head?=some (.inr (.inl root))) (forward : Forward g es)
    (finish : es.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)))
    (labels : Labelling g es input output) (split : es=pre++tail)
    (prefixLabels : Labelling g pre input middle)
    (prefixEnd : pre.getLast?=some (g.wire edge.ctxEnd))
    (shell : Context.SameShell edge.index middle output) :
    ∀ newInput newMiddle newOutput : Context,
      Labelling g es newInput newOutput → Labelling g pre newInput newMiddle →
      Context.SameShell edge.index newMiddle newOutput := by
  obtain ⟨allInputs,_⟩ := independence es (.inr (.inl root)) (.inl ⟨edge.lam,edge.lamBind⟩)
    .root .lamBind 0 edge.index input output rooted finish (.root) trivial
    (.lamBind edge.lam edge.lamBind edge.index edge.lamLabel edge.lamBind_role) trivial forward labels
  have total : ∀ context : Context, ∃ result, Labelling g es context result := by
    intro context
    obtain ⟨result,actual⟩ := allInputs context
    exact ⟨result,by simpa only [Context.replace_zero] using actual⟩
  obtain ⟨expressions,final,i,first,last,traces,within,atPort,uniform⟩ :=
    Lamping.AG.Marker.Transparency.uniform_binder_candidate transparency es edge.lam edge.lamCtx edge.lamBody edge.lamBind
      (congrArg Label.sort edge.lamLabel) edge.lamCtx_role edge.lamBody_role edge.lamBind_role
      rooted finish forward total
  have index : (g.label edge.lam).index=edge.index := by rw [edge.lamLabel]; rfl
  rw [index] at uniform
  have preNonempty := prefixLabels.nonempty
  have prePositive := List.length_pos_iff.mpr preNonempty
  let j := pre.length-1
  have withinJ : j<es.length := by rw [split,List.length_append]; omega
  have atPortJ : es[j]?=some (g.wire edge.ctxEnd) := by
    rw [split,List.getElem?_append_left (by omega)]
    exact (List.getLast?_eq_getElem?).symm.trans prefixEnd
  have trace := traces input
  have traceFirst : (expressions.map (fun c => c.eval input)).head?=some input := by
    rw [List.head?_map,first]
    simp
  have traceLast : (expressions.map (fun c => c.eval input)).getLast?=some (final.eval input) := by
    rw [List.getLast?_map,last]
    rfl
  have finalValue := (trace.labelling g traceFirst traceLast).output_unique labels
  have prefixValue := expression_prefix_value input middle trace first split preNonempty prefixLabels
  have pointI := expression_point input trace i within
  have pointJ := expression_point input trace j withinJ
  have sharedShell : Context.SameShell edge.index
      ((expressions[i]?.getD ExprContext.initial).eval input)
      ((expressions[j]?.getD ExprContext.initial).eval input) := by
    intro k low
    have uniformLow := uniform input k low
    rw [finalValue] at uniformLow
    rw [show j=pre.length-1 from rfl,prefixValue]
    exact uniformLow.trans (shell k low).symm
  have actualPort : AtProperRole g root (g.wire (g.wire edge.ctxEnd)) .lamCtx edge.index := by
    simpa only [Pairing.involutive] using AtProperRole.lamCtx (g:=g) (root:=root)
      edge.lam edge.lamCtx edge.index edge.lamLabel edge.lamCtx_role
  have sameOrdinal : i=j := by
    apply Classical.byContradiction
    intro different
    rcases Nat.lt_or_gt_of_ne different with lt | gt
    · exact nesting es _ trace rooted forward i j (g.wire edge.ctxEnd) _ _ edge.index .lamCtx
        lt atPort atPortJ pointI pointJ (Or.inr rfl) actualPort sharedShell
    · exact nesting es _ trace rooted forward j i (g.wire edge.ctxEnd) _ _ edge.index .lamCtx
        gt atPortJ atPort pointJ pointI (Or.inr rfl) actualPort (by intro k low; exact (sharedShell k low).symm)
  intro newInput newMiddle newOutput newLabels newPrefix
  have newTrace := traces newInput
  have newFirst : (expressions.map (fun c => c.eval newInput)).head?=some newInput := by
    rw [List.head?_map,first]
    simp
  have newLast : (expressions.map (fun c => c.eval newInput)).getLast?=some (final.eval newInput) := by
    rw [List.getLast?_map,last]
    rfl
  have newFinalValue := (newTrace.labelling g newFirst newLast).output_unique newLabels
  have newPrefixValue := expression_prefix_value newInput newMiddle newTrace first split preNonempty newPrefix
  have newShell := uniform newInput
  rw [sameOrdinal,show j=pre.length-1 from rfl,newPrefixValue,newFinalValue] at newShell
  exact newShell

/-- The same occurrence-stability proof for actual lambda metadata; no beta edge is required. -/
theorem binder_shell_stable_node (independence : Independence g root) (nesting : Nesting g root)
    (transparency : Transparency g root) (node : N)
    (ctx body bind : Port (g.label node).sort) (level : Nat)
    (nodeLabel : g.label node=label .lam level)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody) (bindRole : HEq bind lamBind)
    (es pre tail : List (Endpoint g)) (input middle output : Context)
    (rooted : es.head?=some (.inr (.inl root))) (forward : Forward g es)
    (finish : es.getLast?=some (g.wire (.inl ⟨node,bind⟩)))
    (labels : Labelling g es input output) (split : es=pre++tail)
    (prefixLabels : Labelling g pre input middle)
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (shell : Context.SameShell level middle output) :
    ∀ newInput newMiddle newOutput : Context,
      Labelling g es newInput newOutput → Labelling g pre newInput newMiddle →
      Context.SameShell level newMiddle newOutput := by
  obtain ⟨allInputs,_⟩ := independence es (.inr (.inl root)) (.inl ⟨node,bind⟩)
    .root .lamBind 0 level input output rooted finish (.root) trivial
    (.lamBind node bind level nodeLabel bindRole) trivial forward labels
  have total : ∀ context : Context, ∃ result, Labelling g es context result := by
    intro context
    obtain ⟨result,actual⟩ := allInputs context
    exact ⟨result,by simpa only [Context.replace_zero] using actual⟩
  obtain ⟨expressions,final,i,first,last,traces,within,atPort,uniform⟩ :=
    Lamping.AG.Marker.Transparency.uniform_binder_candidate transparency es node ctx body bind
      (congrArg Label.sort nodeLabel) ctxRole bodyRole bindRole
      rooted finish forward total
  have index : (g.label node).index=level := by rw [nodeLabel]; rfl
  rw [index] at uniform
  have preNonempty := prefixLabels.nonempty
  have prePositive := List.length_pos_iff.mpr preNonempty
  let j := pre.length-1
  have withinJ : j<es.length := by rw [split,List.length_append]; omega
  have atPortJ : es[j]?=some (g.wire (.inl ⟨node,ctx⟩)) := by
    rw [split,List.getElem?_append_left (by omega)]
    exact (List.getLast?_eq_getElem?).symm.trans prefixEnd
  have trace := traces input
  have traceFirst : (expressions.map (fun c => c.eval input)).head?=some input := by
    rw [List.head?_map,first]
    simp
  have traceLast : (expressions.map (fun c => c.eval input)).getLast?=some (final.eval input) := by
    rw [List.getLast?_map,last]
    rfl
  have finalValue := (trace.labelling g traceFirst traceLast).output_unique labels
  have prefixValue := expression_prefix_value input middle trace first split preNonempty prefixLabels
  have pointI := expression_point input trace i within
  have pointJ := expression_point input trace j withinJ
  have sharedShell : Context.SameShell level
      ((expressions[i]?.getD ExprContext.initial).eval input)
      ((expressions[j]?.getD ExprContext.initial).eval input) := by
    intro k low
    have uniformLow := uniform input k low
    rw [finalValue] at uniformLow
    rw [show j=pre.length-1 from rfl,prefixValue]
    exact uniformLow.trans (shell k low).symm
  have actualPort : AtProperRole g root (g.wire (g.wire (.inl ⟨node,ctx⟩))) .lamCtx level := by
    simpa only [Pairing.involutive] using AtProperRole.lamCtx (g:=g) (root:=root)
      node ctx level nodeLabel ctxRole
  have sameOrdinal : i=j := by
    apply Classical.byContradiction
    intro different
    rcases Nat.lt_or_gt_of_ne different with lt | gt
    · exact nesting es _ trace rooted forward i j (g.wire (.inl ⟨node,ctx⟩)) _ _ level .lamCtx
        lt atPort atPortJ pointI pointJ (Or.inr rfl) actualPort sharedShell
    · exact nesting es _ trace rooted forward j i (g.wire (.inl ⟨node,ctx⟩)) _ _ level .lamCtx
        gt atPortJ atPort pointJ pointI (Or.inr rfl) actualPort (by intro k low; exact (sharedShell k low).symm)
  intro newInput newMiddle newOutput newLabels newPrefix
  have newTrace := traces newInput
  have newFirst : (expressions.map (fun c => c.eval newInput)).head?=some newInput := by
    rw [List.head?_map,first]
    simp
  have newLast : (expressions.map (fun c => c.eval newInput)).getLast?=some (final.eval newInput) := by
    rw [List.getLast?_map,last]
    rfl
  have newFinalValue := (newTrace.labelling g newFirst newLast).output_unique newLabels
  have newPrefixValue := expression_prefix_value newInput newMiddle newTrace first split preNonempty newPrefix
  have newShell := uniform newInput
  rw [sameOrdinal,show j=pre.length-1 from rfl,newPrefixValue,newFinalValue] at newShell
  exact newShell
end
end Lamping.AG.Marker



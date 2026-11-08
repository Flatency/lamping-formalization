import Lamping.Lamping.MarkerExpressionPaths
import Lamping.Lamping.ExpandedBinderOccurrences
namespace Lamping.AG.Marker
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Enumerate actual incoming context-port occurrences, preserving ordinals.
The finite separating input selects one whose shell equations are identities. -/
theorem uniform_shell_ordinal (es : List (Endpoint g)) (expressions : List ExprContext)
    (final : ExprContext) (port : Endpoint g) (width : Nat)
    (cover : ∀ input : Context, ∃ i, i<es.length ∧ es[i]?=some port ∧
      Context.SameShell width ((expressions[i]?.getD ExprContext.initial).eval input) (final.eval input)) :
    ∃ i, i<es.length ∧ es[i]?=some port ∧ ∀ input : Context,
      Context.SameShell width ((expressions[i]?.getD ExprContext.initial).eval input) (final.eval input) := by
  classical
  let indices := (List.range es.length).filter (fun i => decide (es[i]?=some port))
  let system := fun i : Nat => (expressions[i]?.getD ExprContext.initial).shellEquations final width
  have covers : ∀ input : Context, ∃ candidate∈indices.map system,
      ∀ pair∈candidate, pair.1.eval input.get=pair.2.eval input.get := by
    intro input
    obtain ⟨i,within,atPort,shell⟩ := cover input
    have member : i∈indices := List.mem_filter.mpr ⟨List.mem_range.mpr within,by simpa using atPort⟩
    exact ⟨system i,List.mem_map.mpr ⟨i,member,rfl⟩,
      ((expressions[i]?.getD ExprContext.initial).shellEquations_eval final width input).mpr shell⟩
  obtain ⟨candidate,member,identities⟩ := LevelExpr.uniform_system_candidate_finite (indices.map system) covers
  obtain ⟨i,inIndices,same⟩ := List.mem_map.mp member
  subst candidate
  obtain ⟨inRange,atPort⟩ := List.mem_filter.mp inIndices
  refine ⟨i,List.mem_range.mp inRange,by simpa using atPort,?_⟩
  exact (expressions[i]?.getD ExprContext.initial).shellEquations_identity final width identities

/-- Ordinary Transparency on each actual assigned root path yields a uniform
physical binder-context occurrence. Total path labels are supplied explicitly
here; the typed ordinary-Independence corollary supplies them below. -/
theorem Transparency.uniform_binder_candidate {root : B} (transparency : Transparency g root)
    (es : List (Endpoint g)) (node : N) (ctx body bind : Port (g.label node).sort)
    (isLam : (g.label node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body AG.lamBody) (bindRole : HEq bind AG.lamBind)
    (rooted : es.head?=some (.inr (.inl root)))
    (finish : es.getLast?=some (g.wire (.inl ⟨node,bind⟩))) (forward : Forward g es)
    (total : ∀ input : Context, ∃ output, Labelling g es input output) :
    ∃ (expressions : List ExprContext) (final : ExprContext) (i : Nat),
      expressions.head?=some ExprContext.initial ∧ expressions.getLast?=some final ∧
      (∀ input : Context, ContextTrace g es (expressions.map (fun c => c.eval input))) ∧
      i<es.length ∧ es[i]?=some (g.wire (.inl ⟨node,ctx⟩)) ∧
      ∀ input : Context, Context.SameShell (g.label node).index
        ((expressions[i]?.getD ExprContext.initial).eval input) (final.eval input) := by
  obtain ⟨expressions,first,traces⟩ := Labelling.expression_trace es ExprContext.initial (by simpa using total)
  have nonempty : expressions≠[] := by intro empty; rw [empty] at first; cases first
  have hasLast : ∃ final, expressions.getLast?=some final := by
    cases last : expressions.getLast? with
    | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp last))
    | some final => exact ⟨final,rfl⟩
  obtain ⟨final,last⟩ := hasLast
  have coverage : ∀ input : Context, ∃ i, i<es.length ∧ es[i]?=some (g.wire (.inl ⟨node,ctx⟩)) ∧
      Context.SameShell (g.label node).index ((expressions[i]?.getD ExprContext.initial).eval input) (final.eval input) := by
    intro input
    have trace := traces input
    have traceFirst : (expressions.map (fun c => c.eval input)).head?=some input := by
      rw [List.head?_map,first]
      simp
    have traceLast : (expressions.map (fun c => c.eval input)).getLast?=some (final.eval input) := by
      rw [List.getLast?_map,last]
      rfl
    have labels := trace.labelling g traceFirst traceLast
    obtain ⟨pre,loop,seam,binding,split,sameBinder,preEnd,preLabels⟩ :=
      transparency es input (final.eval input) node ctx body bind isLam ctxRole bodyRole bindRole
        rooted finish forward labels
    have preNonempty : pre≠[] := by intro empty; rw [empty] at preEnd; cases preEnd
    have positive : 0<pre.length := List.length_pos_iff.mpr preNonempty
    let i := pre.length-1
    have within : i<es.length := by rw [split,List.length_append]; omega
    have atPort : es[i]?=some (g.wire (.inl ⟨node,ctx⟩)) := by
      rw [split,List.getElem?_append_left (by omega)]
      exact (List.getLast?_eq_getElem?).symm.trans preEnd
    have point := trace.expanded.labelled_prefix_point traceFirst split preNonempty preLabels.expanded
    have withinExpressions : i<expressions.length := by
      have lengths := trace.length g
      rw [List.length_map] at lengths
      omega
    let here := expressions[i]
    have atHere : expressions[i]?=some here := List.getElem?_eq_getElem withinExpressions
    have equal : here.eval input=seam := by
      rw [List.getElem?_map,atHere] at point
      exact Option.some.inj point
    have shell : Context.SameShell (g.label node).index seam (final.eval input) := by
      simpa only [sameBinder] using binding.shell
    refine ⟨i,within,atPort,?_⟩
    simpa only [atHere,Option.getD_some,equal] using shell
  obtain ⟨i,within,atPort,uniform⟩ := uniform_shell_ordinal es expressions final
    (g.wire (.inl ⟨node,ctx⟩)) (g.label node).index coverage
  exact ⟨expressions,final,i,first,last,traces,within,atPort,uniform⟩
end
end Lamping.AG.Marker

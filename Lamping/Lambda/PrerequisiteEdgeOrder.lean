import Lamping.Lambda.PrerequisiteOrder
namespace Lamping.Lambda.Labelled
private theorem function_order_lt (lookup : t.subterm p=some (.app a fn arg)) :
    prerequisiteOrder t (p++[.fn])<prerequisiteOrder t p := by
  obtain ⟨offset,same⟩ := prerequisiteOrder_subtree lookup
  have root := same []
  have child := same [.fn]
  simp only [List.append_nil,prerequisiteOrder] at root child
  have bound := prerequisiteOrder_root_bound fn
  omega

private theorem lookup_parent {t : LTerm} (lookup : t.subterm (parent++[step])=some sub) :
    ∃ term,t.subterm parent=some term := by
  rw [LTerm.subterm_append] at lookup
  cases actual : t.subterm parent with
  | none => rw [actual] at lookup; cases lookup
  | some term => exact ⟨term,rfl⟩

private theorem edge_bounds (chain : PrerequisiteChain t p edges) :
    (∀ edge∈edges,prerequisiteOrder t edge≤prerequisiteOrder t p) ∧
    ((∀ a body,t.subterm p≠some (.lam a body)) →
      ∀ edge∈edges,prerequisiteOrder t edge<prerequisiteOrder t p) := by
  induction chain with
  | @redex_app p a l b arg lookup =>
    have less := function_order_lt lookup
    have strict : ∀ e∈[p++[.fn]],prerequisiteOrder t e<prerequisiteOrder t p := by
      intro e member
      have same := List.mem_singleton.mp member
      subst e; exact less
    exact ⟨fun e member=>Nat.le_of_lt (strict e member),fun _=>strict⟩
  | @redex_lam p a l b arg lookup =>
    refine ⟨?_,?_⟩
    · intro e member
      have same := List.mem_singleton.mp member
      subst e; exact Nat.le_refl _
    · intro notLambda
      have child : t.subterm (p++[.fn])=some (.lam l b) := by rw [LTerm.subterm_append,lookup]; rfl
      exact False.elim (notLambda _ _ child)
  | @app p a fn arg es lookup notLambda tail ih =>
    have less := function_order_lt lookup
    have strict : ∀ e∈(p++[.fn])::es,prerequisiteOrder t e<prerequisiteOrder t p := by
      intro e member
      rcases List.mem_cons.mp member with same | below
      · subst e; exact less
      · have bound := ih.1 e below; omega
    exact ⟨fun e member=>Nat.le_of_lt (strict e member),fun _=>strict⟩
  | @lam parent step a body es lookup notFunction tail ih =>
    obtain ⟨parentTerm,atParent⟩ := lookup_parent lookup
    have less := (PrerequisiteDependency.lam atParent lookup notFunction).order_lt
    refine ⟨?_,?_⟩
    · intro e member
      rcases List.mem_cons.mp member with same | below
      · subst e; exact Nat.le_refl _
      · have bound := ih.1 e below; omega
    · intro notLambda
      exact False.elim (notLambda _ _ lookup)
  | @var leaf a index parent origin body rest es lookup binder split depth tail ih =>
    have less := (PrerequisiteDependency.var lookup binder split depth).order_lt
    have strict : ∀ e∈es,prerequisiteOrder t e<prerequisiteOrder t leaf := by
      intro e member
      have bound := ih.1 e member
      omega
    exact ⟨fun e member=>Nat.le_of_lt (strict e member),fun _=>strict⟩

/-- Every edge of a genuine chain lies no later than its selected node. -/
theorem PrerequisiteChain.edge_order_le (chain : PrerequisiteChain t p edges)
    (member : edge∈edges) : prerequisiteOrder t edge≤prerequisiteOrder t p :=
  (edge_bounds chain).1 edge member

/-- An application or variable node strictly follows each prerequisite edge. -/
theorem PrerequisiteChain.edge_order_lt (chain : PrerequisiteChain t p edges)
    (notLambda : ∀ a body,t.subterm p≠some (.lam a body))
    (member : edge∈edges) : prerequisiteOrder t edge<prerequisiteOrder t p :=
  (edge_bounds chain).2 notLambda edge member

/-- Passing from the chain sequence to its edge-membership subgraph loses no multiplicity: this is proved, not a path assumption. -/
theorem PrerequisiteChain.nodup (chain : PrerequisiteChain t p edges) : edges.Nodup := by
  induction chain with
  | redex_app => simp
  | redex_lam => simp
  | @app p a fn arg es lookup notLambda tail ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro member
    have actual : t.subterm (p++[.fn])=some fn := by
      rw [LTerm.subterm_append,lookup]; cases fn <;> rfl
    have notLambdaAt : ∀ a body,t.subterm (p++[.fn])≠some (.lam a body) := by
      intro a body wrong
      exact notLambda a body (Option.some.inj (actual.symm.trans wrong))
    have less := tail.edge_order_lt notLambdaAt member
    omega
  | @lam parent step a body es lookup notFunction tail ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro member
    obtain ⟨parentTerm,atParent⟩ := lookup_parent lookup
    have less := (PrerequisiteDependency.lam atParent lookup notFunction).order_lt
    have bound := tail.edge_order_le member
    omega
  | var _ _ _ _ _ ih => exact ih
end Lamping.Lambda.Labelled
import Lamping.Lamping.ChainInitialRigidity
import Lamping.Lamping.ChainFragmentUniqueness

namespace Lamping.Lambda.Labelled

/-- Actual prerequisite edge ranks strictly decrease along the whole list.
The relation concerns occurrences, without an INIT or label hypothesis. -/
theorem PrerequisiteChain.edges_strict (chain : PrerequisiteChain t p edges) :
    edges.Pairwise (fun left right=>prerequisiteOrder t right<prerequisiteOrder t left) := by
  induction chain with
  | redex_app => exact .cons (by simp) .nil
  | redex_lam => exact .cons (by simp) .nil
  | @app p a fn arg es lookup notLambda tail ih =>
    apply List.Pairwise.cons _ ih
    intro edge member
    apply tail.edge_order_lt _ member
    intro a body wrong
    have actual : t.subterm (p++[.fn])=some fn := by
      rw [LTerm.subterm_append,lookup]; cases fn <;> rfl
    exact notLambda a body (Option.some.inj (actual.symm.trans wrong))
  | @lam parent step a body es lookup notFunction tail ih =>
    apply List.Pairwise.cons _ ih
    intro edge member
    have atParent : ∃ term,t.subterm parent=some term := by
      rw [LTerm.subterm_append] at lookup
      cases actual : t.subterm parent with
      | none => rw [actual] at lookup; cases lookup
      | some term => exact ⟨term,rfl⟩
    obtain ⟨term,atParent⟩ := atParent
    have less := (PrerequisiteDependency.lam atParent lookup notFunction).order_lt
    have bound := tail.edge_order_le member
    omega
  | var _ _ _ _ _ ih => exact ih

private theorem strict_rank_list_unique {α : Type} (rank : α → Nat)
    {left right : List α}
    (leftOrder : left.Pairwise (fun a b=>rank b<rank a))
    (rightOrder : right.Pairwise (fun a b=>rank b<rank a))
    (same : ∀ a,a∈left ↔a∈right) : left=right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons a tail => exact False.elim (List.not_mem_nil ((same a).mpr (by simp)))
  | cons a tail ih =>
    cases right with
    | nil => exact False.elim (List.not_mem_nil ((same a).mp (by simp)))
    | cons b rest =>
      obtain ⟨leftHead,leftTail⟩ := List.pairwise_cons.mp leftOrder
      obtain ⟨rightHead,rightTail⟩ := List.pairwise_cons.mp rightOrder
      have heads : a=b := by
        rcases List.mem_cons.mp ((same a).mp (by simp)) with equal | member
        · exact equal
        · rcases List.mem_cons.mp ((same b).mpr (by simp)) with equal | other
          · exact equal.symm
          · have first := leftHead b other
            have second := rightHead a member
            omega
      subst b
      apply congrArg (a::·)
      apply ih leftTail rightTail
      intro x
      constructor
      · intro member
        rcases List.mem_cons.mp ((same x).mp (List.mem_cons_of_mem _ member)) with equal | other
        · have less := leftHead x member
          rw [equal] at less
          omega
        · exact other
      · intro member
        rcases List.mem_cons.mp ((same x).mpr (List.mem_cons_of_mem _ member)) with equal | other
        · have less := rightHead x member
          rw [equal] at less
          omega
        · exact other

/-- For genuine chains, equality of actual edge membership loses neither
multiplicity nor sequence order. It does not identify chase directions. -/
theorem PrerequisiteChain.eq_edges_of_membership
    (first : PrerequisiteChain t p left) (second : PrerequisiteChain t q right)
    (same : ∀ edge,edge∈left ↔edge∈right) : left=right :=
  strict_rank_list_unique (prerequisiteOrder t) first.edges_strict second.edges_strict same

private theorem PrerequisiteChain.valid_edge (chain : PrerequisiteChain t p edges)
    (member : edge∈edges) : (subtermAt t.erase edge).isSome := by
  rcases chain.eligible member with ⟨parent,a,fn,arg,equal,lookup⟩ |⟨a,body,lookup⟩
  · have actual : t.subterm edge=some fn := by
      rw [equal,LTerm.subterm_append,lookup]; cases fn <;> rfl
    rw [←LTerm.erase_subterm,actual]; rfl
  · rw [←LTerm.erase_subterm,lookup]; rfl
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- Only at INIT: a bare incidence isomorphism of two genuine chains in the
same syntax term determines their literal occurrence lists. -/
theorem chainSyntaxIncidence_initial_sequences
    (current : LTerm) (closed : Closed current.erase) (initial : INIT current)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (iso : ChainIncidenceIso (chainSyntaxIncidence current closed left)
      (chainSyntaxIncidence current closed right)) : left=right := by
  apply first.eq_edges_of_membership second
  intro edge
  constructor
  · intro member
    exact (chainSyntaxIncidence_initial_selected_iff current closed initial left right iso
      ⟨edge,first.valid_edge member⟩).mp member
  · intro member
    exact (chainSyntaxIncidence_initial_selected_iff current closed initial left right iso
      ⟨edge,second.valid_edge member⟩).mpr member

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

/-- Initial syntax rigidity gives equality of canonical source-direction
blocks under any two actual selectors. This is a one-way initial bridge,
not a definition or a general-history equivalence for REP. -/
theorem initial_iso_canonical_blocks
    (matching : Matches g root current.erase) (closed : Closed current.erase)
    (initial : INIT current)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (iso : ChainIncidenceIso (chainSyntaxIncidence current closed left)
      (chainSyntaxIncidence current closed right))
    (selectLeft selectRight : OccurrenceFragmentSelection current g root) :
    canonicalChainImage selectLeft first=canonicalChainImage selectRight second := by
  have equal := chainSyntaxIncidence_initial_sequences current closed initial first second iso
  subst right
  have sameProof : canonicalChainImage selectRight first=canonicalChainImage selectRight second := rfl
  exact (canonicalChainImage_choice_independent matching selectLeft selectRight first).trans sameProof
end
end Lamping.AG

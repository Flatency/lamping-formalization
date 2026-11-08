import Lamping.Lamping.BackwardPathDeterminism
import Lamping.Lamping.ReachableTailInvariants
import Lamping.Lamping.OrdinaryPrefixRelabelling
import Lamping.Lamping.PrimitiveTailTransport
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Int}

/-- Structural tail synchronization and reversible ordinary turns imply
Nesting. Each actual context prefix is independently relabelled to a common
terminal tail; backward uniqueness permits their root inputs to differ. -/
theorem IndexedLevelBalance.nesting (balance : IndexedLevelBalance g boundary)
    (root : B) (rootDepth : boundary root=0) : Nesting g root := by
  intro es cs trace rooted forward i j e a b n role earlier atI atJ contextI contextJ contextRole atPort sameShell
  obtain ⟨input,contextHead⟩ : ∃ input,cs.head?=some input := by
    cases trace with
    | single e c => exact ⟨c,rfl⟩
    | cons turn rest => exact ⟨_,rfl⟩
  have firstLabels := trace.prefix_labels i contextI contextHead
  have secondLabels := trace.prefix_labels j contextJ contextHead
  have firstForward := forward.take_succ i
  have secondForward := forward.take_succ j
  have firstRoot : (es.take (i+1)).head?=some (.inr (.inl root)) := by
    cases es with
    | nil => cases rooted
    | cons x xs => simpa only [List.take_succ_cons,List.head?_cons] using rooted
  have secondRoot : (es.take (j+1)).head?=some (.inr (.inl root)) := by
    cases es with
    | nil => cases rooted
    | cons x xs => simpa only [List.take_succ_cons,List.head?_cons] using rooted
  have firstLast : (es.take (i+1)).getLast?=some e := by
    simp only [List.getLast?_take,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,
      Nat.add_sub_cancel,atI,Option.some_or]
  have secondLast : (es.take (j+1)).getLast?=some e := by
    simp only [List.getLast?_take,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,
      Nat.add_sub_cancel,atJ,Option.some_or]
  have incoming : role.incoming := by rcases contextRole with same | same <;> subst role <;> trivial
  have width : role.terminalWidth n=n := by rcases contextRole with same | same <;> subst role <;> rfl
  obtain ⟨firstWidth,_,_,_,firstSync⟩ := balance.independence_tail root rootDepth (es.take (i+1))
    (.inr (.inl root)) (g.wire e) .root role 0 n input a firstRoot
    (by simpa only [Pairing.involutive] using firstLast) (.root) trivial atPort incoming firstForward firstLabels
  obtain ⟨secondWidth,_,_,_,secondSync⟩ := balance.independence_tail root rootDepth (es.take (j+1))
    (.inr (.inl root)) (g.wire e) .root role 0 n input b secondRoot
    (by simpa only [Pairing.involutive] using secondLast) (.root) trivial atPort incoming secondForward secondLabels
  have firstChanged := firstSync Context.empty
  have secondChanged := secondSync Context.empty
  rw [width] at firstChanged secondChanged
  have outputEq := Context.replace_same_shell sameShell Context.empty
  rw [←outputEq] at secondChanged
  obtain ⟨paths,_⟩ := Labelling.rooted_terminal_unique g firstChanged firstForward firstRoot secondChanged
    secondForward secondRoot (firstLast.trans secondLast.symm)
  have equalLengths := congrArg List.length paths
  have firstBound : i<es.length := by
    by_cases bound : i<es.length
    · exact bound
    · have impossible := List.getElem?_eq_none (by omega : es.length≤i)
      rw [atI] at impossible
      cases impossible
  have secondBound : j<es.length := by
    by_cases bound : j<es.length
    · exact bound
    · have impossible := List.getElem?_eq_none (by omega : es.length≤j)
      rw [atJ] at impossible
      cases impossible
  simp only [List.length_take] at equalLengths
  rw [Nat.min_eq_left (by omega : i+1≤es.length),Nat.min_eq_left (by omega : j+1≤es.length)] at equalLengths
  omega
end

/-- Nesting holds after every actual finite rewrite trace, independently of
the pending Matches/Transparency and smaller-input-existence proofs. -/
theorem initial_trace_nesting (t : Term) (target : ActualNet (Boundary t)) (schemas : List Schema)
    (trace : GraphTrace (ActualNet.initial t) target schemas) : Nesting target.net (.inl ()) := by
  obtain ⟨balance⟩ := initial_trace_indexed_balance t target schemas trace
  exact balance.nesting (.inl ()) rfl
end Lamping.AG



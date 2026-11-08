import Lamping.Lamping.BetaDetourBlocks
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Concatenate two actual paired streams sharing their selected last/first
segment and assignment. The common segment occurs once in the result. -/
theorem BetaDetourBlocks.append_at_last
    {pre suffix : List (Endpoint g)} {last : Endpoint g}
    {a seam b : Context} {leftCount rightCount : Nat}
    (before : BetaDetourBlocks g pre a seam leftCount)
    (after : BetaDetourBlocks g (last::suffix) seam b rightCount)
    (finish : pre.getLast?=some last) :
    BetaDetourBlocks g (pre++suffix) a b (leftCount+rightCount) := by
  induction before with
  | single e a =>
    have equal : e=last := Option.some.inj finish
    subst last
    simpa only [Nat.zero_add,List.singleton_append] using after
  | ordinary turn rest ih =>
    exact .ordinary turn (ih after (by simpa only [List.getLast?_cons_cons] using finish))
  | @backward edge e tail a middle count arrival head rest ih =>
    have tailLast : tail.getLast?=some last := by
      cases tailEq : tail.getLast? with
      | none =>
        have empty := List.getLast?_eq_none_iff.mp tailEq
        rw [empty] at head
        cases head
      | some endpoint =>
        simpa only [List.getLast?_cons,List.getLast?_append,tailEq,Option.some_or,Option.getD_some] using finish
    have tailStream := ih after tailLast
    have newHead : (tail++suffix).head?=some edge.argEnd := by
      simp only [List.head?_append,head,Option.some_or]
    have result := BetaDetourBlocks.backward edge e arrival newHead tailStream
    have countEq : count+rightCount+1=(count+1)+rightCount := by omega
    simpa only [List.cons_append,List.append_assoc,countEq] using result

/-- Append one new backward block to an already paired body, rather than
requiring that body's entire root prefix to be ordinary. -/
theorem BetaDetourBlocks.append_backward_paired (edge : BetaEdge g)
    {pre tail : List (Endpoint g)} {a seam b : Context} {bodyCount tailCount : Nat}
    (body : BetaDetourBlocks g pre a seam bodyCount)
    (rest : BetaDetourBlocks g tail seam b tailCount)
    (finish : pre.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)))
    (head : tail.head?=some edge.argEnd) :
    BetaDetourBlocks g (pre++edge.reverseRoute++tail) a b (bodyCount+tailCount+1) := by
  have extension : BetaDetourBlocks g
      (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)::(edge.reverseRoute++tail)) seam b (tailCount+1) :=
    .backward edge _ (by simp only [Pairing.involutive]) head rest
  have result := body.append_at_last extension finish
  simpa only [List.append_assoc,Nat.add_assoc] using result
end
end Lamping.AG

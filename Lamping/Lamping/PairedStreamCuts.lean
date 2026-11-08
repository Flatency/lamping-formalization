import Lamping.Lamping.PairedStreamHighTails
namespace Lamping.AG
open Graph
private theorem cut_after_excluded {X : Type} {front back pre post : List X} {cut : X}
    (equal : front++back=pre++cut::post) (excluded : cut∉front) :
    ∃ rest,pre=front++rest ∧ back=rest++cut::post := by
  rcases List.append_eq_append_iff.mp equal with ⟨rest,left,right⟩ | ⟨rest,left,right⟩
  · exact ⟨rest,left,right⟩
  · cases rest with
    | nil => exact ⟨[],by simpa using left.symm,by simpa using right.symm⟩
    | cons x xs =>
      have same : cut=x := (List.cons.inj right).1
      exact False.elim (excluded (by rw [left,←same]; simp))
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {boundary : B → Bool}

/-- Every departure of the COMPLETE reversed principal has negative flow.
Hence no positive cut can lie inside such a block. -/
theorem BetaEdge.reverse_departures_negative (edge : BetaEdge g)
    (flow : FlowBalance g boundary) (positive : boundary root=true)
    {e : Endpoint g} (member : e∈edge.reverseRoute) :
    flowEndpoint g flow.nodes boundary flow.vertices e=false := by
  have allPositive := (edge.principal_labeling Context.empty).positive_departures flow (by
    intro first head
    have equal := Option.some.inj (head.symm.trans edge.principalStart)
    rw [equal]
    exact (AtProperRole.appFun edge.app edge.appFun edge.index edge.appLabel edge.appFun_role).outgoing_flow
      trivial flow.nodes boundary flow.vertices positive)
  change e∈edge.principal.reverse.map g.wire.mate at member
  obtain ⟨old,oldMember,equal⟩ := List.mem_map.mp member
  have oldPositive := allPositive old (List.mem_reverse.mp oldMember)
  rw [←equal,flow.wiring,oldPositive]
  rfl

private theorem prepend_turn {xs : List (Endpoint g)} {e f : Endpoint g}
    {a middle b : Context} {count : Nat}
    (turn : LabelledTurn g (g.wire e) f a middle)
    (head : xs.head?=some f) (path : BetaDetourBlocks g xs middle b count) :
    BetaDetourBlocks g (e::xs) a b count := by
  cases xs with
  | nil => cases head
  | cons x xs =>
    have same : x=f := Option.some.inj head
    subst x
    exact .ordinary turn path

/-- Split a supplied finite paired stream at a supplied positive departure.
The selected physical occurrence is retained in both pieces. Counts add;
the middle assignment is extracted, not reset or guessed. -/
theorem BetaDetourBlocks.split_at_positive
    (flow : FlowBalance g boundary) (positive : boundary root=true)
    {es : List (Endpoint g)} {a b : Context} {count : Nat}
    (path : BetaDetourBlocks g es a b count)
    (pre : List (Endpoint g)) (cut : Endpoint g) (post : List (Endpoint g))
    (split : es=pre++cut::post)
    (cutPositive : flowEndpoint g flow.nodes boundary flow.vertices cut=true) :
    ∃ middle leftCount rightCount,
      BetaDetourBlocks g (pre++[cut]) a middle leftCount ∧
      BetaDetourBlocks g (cut::post) middle b rightCount ∧ count=leftCount+rightCount := by
  induction path generalizing pre with
  | single e a =>
    cases pre with
    | nil =>
      have pair := List.cons.inj split
      have same := pair.1
      have empty : post=[] := pair.2.symm
      subst cut; subst post
      exact ⟨a,0,0,.single _ _,.single _ _,rfl⟩
    | cons x xs =>
      have lengths := congrArg List.length split
      simp only [List.length_cons,List.length_nil,List.length_append] at lengths
      omega
  | @ordinary e f tail a seam b count turn rest ih =>
    cases pre with
    | nil =>
      have whole : BetaDetourBlocks g (cut::post) a b count := by
        have current := BetaDetourBlocks.ordinary turn rest
        rw [split] at current
        exact current
      exact ⟨a,0,count,.single _ _,whole,by omega⟩
    | cons x xs =>
      have pair := List.cons.inj split
      have equal := pair.1
      subst x
      obtain ⟨middle,leftCount,rightCount,before,after,counts⟩ := ih xs pair.2
      have head : (xs++[cut]).head?=some f := by
        cases xs <;> simpa only [List.nil_append,List.head?_cons,List.cons_append] using congrArg List.head? pair.2.symm
      exact ⟨middle,leftCount,rightCount,prepend_turn turn head before,after,counts⟩
  | @backward edge e tail a b count arrival tailHead rest ih =>
    cases pre with
    | nil =>
      have whole : BetaDetourBlocks g (cut::post) a b (count+1) := by
        have current := BetaDetourBlocks.backward edge e arrival tailHead rest
        rw [split] at current
        exact current
      exact ⟨a,0,count+1,.single _ _,whole,by omega⟩
    | cons x xs =>
      have pair := List.cons.inj split
      have equal := pair.1
      subst x
      have excluded : cut∉edge.reverseRoute := by
        intro member
        have negative := edge.reverse_departures_negative flow positive member
        rw [cutPositive] at negative
        cases negative
      obtain ⟨stemPart,oldPrefix,tailSplit⟩ := cut_after_excluded pair.2 excluded
      obtain ⟨middle,leftCount,rightCount,before,after,counts⟩ := ih stemPart tailSplit
      have head : (stemPart++[cut]).head?=some edge.argEnd := by
        have localHead := tailHead
        rw [tailSplit] at localHead
        cases stemPart <;> simpa only [List.nil_append,List.head?_cons,List.cons_append] using localHead
      have front := BetaDetourBlocks.backward edge e arrival head before
      refine ⟨middle,leftCount+1,rightCount,?_,after,by omega⟩
      simpa only [oldPrefix,List.cons_append,List.append_assoc] using front

/-- A supplied prefix assignment fixes the actual seam extracted by the
positive cut, even when that prefix already contains backward blocks. -/
theorem BetaDetourBlocks.suffix_at_positive_assignment
    (flow : FlowBalance g boundary) (positive : boundary root=true)
    {pre post : List (Endpoint g)} {cut : Endpoint g} {a middle b : Context} {count : Nat}
    (path : BetaDetourBlocks g (pre++cut::post) a b count)
    (before : ExpandedLabelling g (pre++[cut]) a middle)
    (cutPositive : flowEndpoint g flow.nodes boundary flow.vertices cut=true) :
    ∃ tailCount,tailCount≤count ∧ BetaDetourBlocks g (cut::post) middle b tailCount := by
  obtain ⟨actual,leftCount,rightCount,prefixPath,suffixPath,counts⟩ :=
    path.split_at_positive flow positive pre cut post rfl cutPositive
  have same := (prefixPath.labelling g).output_unique before
  exact ⟨rightCount,by omega,by simpa only [same] using suffixPath⟩

/-- Recover an actual paired prefix at a positive terminal occurrence,
with the output fixed by an already supplied prefix labelling. -/
theorem BetaDetourBlocks.prefix_at_positive_assignment
    (flow : FlowBalance g boundary) (positive : boundary root=true)
    {pre tail : List (Endpoint g)} {cut : Endpoint g} {a middle b : Context} {count : Nat}
    (path : BetaDetourBlocks g (pre++tail) a b count)
    (before : ExpandedLabelling g pre a middle)
    (finish : pre.getLast?=some cut)
    (cutPositive : flowEndpoint g flow.nodes boundary flow.vertices cut=true) :
    ∃ prefixCount,prefixCount≤count ∧ BetaDetourBlocks g pre a middle prefixCount := by
  obtain ⟨front,preSplit⟩ := List.getLast?_eq_some_iff.mp finish
  have split : pre++tail=front++cut::tail := by rw [preSplit]; simp only [List.append_assoc,List.singleton_append]
  obtain ⟨actual,leftCount,rightCount,prefixPath,_suffixPath,counts⟩ :=
    path.split_at_positive flow positive front cut tail split cutPositive
  have exactPrefix : BetaDetourBlocks g pre a actual leftCount := by rw [preSplit]; exact prefixPath
  have same := (exactPrefix.labelling g).output_unique before
  exact ⟨leftCount,by omega,by simpa only [same] using exactPrefix⟩
end
end Lamping.AG

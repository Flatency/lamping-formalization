import Lamping.Lamping.EmptyBetaAccessBackward
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed

theorem PathSite.empty_beta_frontier_not_visible
    {root : B} {t : Term} (matching : Matches site.net root t)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (empty : site.betaSyntaxFiber root t=[])
    {pre : List (Endpoint site.net)} {a b : Context} (labels : Labelling site.net pre a b)
    (rooted : pre.head?=some (.inr (.inl root)))
    (f : (Schema.beta i).Frontier)
    (finish : pre.getLast?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr f)))))) : False := by
  have member := List.mem_of_getLast? finish
  have polarity := labels.root_positive_departures flow root rooted positive _ member
  rw [flow.wiring] at polarity
  rcases f with d | d <;> cases d
  · have kind : accessKind site.net pre=some .app := by
      simp only [accessKind,finish,Option.bind_some,Pairing.involutive]; rfl
    exact site.empty_betaSyntaxFiber_not_visible matching flow positive empty
      ⟨pre,⟨⟨⟨a,b,labels⟩,labels.root_forward_of_flow flow root rooted positive⟩,rooted,⟨.app,kind⟩⟩⟩ finish
  · cases polarity
  · have kind : accessKind site.net pre=some .var := by
      simp only [accessKind,finish,Option.bind_some,Pairing.involutive]; rfl
    exact site.empty_betaSyntaxFiber_not_binding_visible matching flow positive oldT empty
      ⟨pre,⟨⟨⟨a,b,labels⟩,labels.root_forward_of_flow flow root rooted positive⟩,rooted,⟨.var,kind⟩⟩⟩ finish
  · cases polarity

private theorem outside_turn
    {e f : Endpoint cut} {next : Endpoint site.net} {a b : Context}
    (arrival : (cut).wire e=f)
    (notFrontier : ∀ x,f≠.inr (.inl (.inr x)))
    (turn : LabelledTurn site.net (site.net.wire (site.outsideEnd e)) next a b) :
    ∃ target : Endpoint cut,next=site.outsideEnd target ∧LabelledTurn cut ((cut).wire e) target a b := by
  rw [site.outsideEnd_wire,arrival] at turn
  rcases f with ⟨node,p⟩ | ((boundary|frontier)|⟨vertex,direction⟩)
  · change LabelledTurn site.net (.inl ⟨.inl node,p⟩) next a b at turn
    cases turn with
    | node _ _ q rule => exact ⟨.inl ⟨node,q⟩,rfl,by rw [arrival]; exact .node node p q rule⟩
  · exact False.elim (turn.not_boundary boundary rfl)
  · exact False.elim (notFrontier frontier rfl)
  · change LabelledTurn site.net (.inr (.inr (.inl vertex,direction))) next a b at turn
    cases turn with
    | transparent _ _ _ => exact ⟨.inr (.inr (vertex,!direction)),rfl,by rw [arrival]; exact .transparent vertex direction a⟩

private theorem exterior_stream
    {root : B} {t : Term} (matching : Matches site.net root t)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (empty : site.betaSyntaxFiber root t=[])
    {es : List (Endpoint site.net)} {a b : Context} (labels : Labelling site.net es a b)
    {pre : List (Endpoint site.net)} {initial : Context} (before : Labelling site.net pre initial a)
    (rooted : pre.head?=some (.inr (.inl root)))
    {first : Endpoint cut} (head : es.head?=some (site.outsideEnd first))
    (finish : pre.getLast?=some (site.outsideEnd first)) :
    ∃ outside : List (Endpoint cut),es=outside.map site.outsideEnd ∧Labelling cut outside a b := by
  induction labels generalizing pre initial first with
  | single e a =>
    have same := Option.some.inj head
    exact ⟨[first],by simp only [List.map_cons,List.map_nil,same],.single first a⟩
  | @cons e f tail a middle b turn after ih =>
    have same := Option.some.inj head
    subst e
    have notFrontier : ∀ x,(cut).wire first≠.inr (.inl (.inr x)) := by
      intro x hx
      apply site.empty_beta_frontier_not_visible matching flow positive oldT empty before rooted x
      rw [←hx,←site.outsideEnd_wire,Pairing.involutive]
      exact finish
    obtain ⟨next,nextEq,actual⟩ := outside_turn site rfl notFrontier turn
    have joined : Labelling site.net (pre++[f]) initial middle := by
      apply before.append_seam (.single _ _)
      intro x y hx hy
      have xeq := Option.some.inj (hx.symm.trans finish)
      have yeq := Option.some.inj hy
      rw [xeq,←yeq]
      exact turn
    have joinedRoot : (pre++[f]).head?=some (.inr (.inl root)) := by
      rw [List.head?_append,rooted]; rfl
    obtain ⟨outside,eqs,rest⟩ := ih joined joinedRoot (first:=next) (by simp only [List.head?_cons,nextEq])
      (by simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or,nextEq])
    have restHead : outside.head?=some next := by
      have h := congrArg List.head? eqs
      rw [List.head?_map,List.head?_cons,nextEq] at h
      cases split : outside with
      | nil => rw [split] at h; cases h
      | cons x xs =>
        rw [split] at h
        have inject : Function.Injective site.outsideEnd := by
          intro x y he
          let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition (Schema.beta i) V)
          have same := congrArg split he
          change split (split.invFun (.inl x))=split (split.invFun (.inl y)) at same
          simp only [split.right_inv] at same
          exact Sum.inl.inj same
        exact congrArg some (inject (Option.some.inj h).symm)
    obtain ⟨post,outsideEq⟩ := List.head?_eq_some_iff.mp restHead
    refine ⟨first::outside,?_,?_⟩
    · simp only [List.map_cons,←eqs]
    · rw [outsideEq] at rest ⊢
      exact .cons actual rest

/-- Every existing source rooted labelled path is already wholly exterior
when the actual old syntax fiber is empty. No endpoint typing is needed. -/
theorem PathSite.empty_beta_source_exterior
    {root : B} {t : Term} (matching : Matches site.net root t)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (empty : site.betaSyntaxFiber root t=[])
    {es : List (Endpoint site.net)} {a b : Context} (labels : Labelling site.net es a b)
    (rooted : es.head?=some (.inr (.inl root))) :
    ∃ outside : List (Endpoint cut),es=outside.map site.outsideEnd ∧Labelling cut outside a b := by
  exact exterior_stream site matching flow positive oldT empty labels
    (.single (.inr (.inl root)) a) rfl (first:=.inr (.inl (.inl root))) rooted rfl
end
end Lamping.AG




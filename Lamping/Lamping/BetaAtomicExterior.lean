import Lamping.Lamping.BetaPrincipalInternal
import Lamping.Lamping.BetaResidualOccurrences
import Lamping.Lamping.ActionSourceDirection
import Lamping.Lamping.MatchingSourceEdgeRealization
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
private theorem no_frontier_turn {e : Endpoint cut} {f : Endpoint site.net} {tail : List (Endpoint site.net)}
    {a middle : Context} (frontier : (Schema.beta i).Frontier)
    (arrival : (cut).wire e=.inr (.inl (.inr frontier)))
    (turn : LabelledTurn site.net (site.net.wire (site.outsideEnd e)) f a middle)
    (forward : Forward site.net (site.outsideEnd e::f::tail))
    (token : arrivalWord site.net f=[]) : False := by
  have arrives : site.net.wire (site.outsideEnd e)=site.outsideEnd (.inr (.inl (.inr frontier))) := by
    rw [site.outsideEnd_wire,arrival]
  have firstEq : site.outsideEnd e=site.net.wire (site.outsideEnd (.inr (.inl (.inr frontier)))) := by
    have same := congrArg site.net.wire.mate arrives
    simpa only [Pairing.involutive] using same
  rw [arrives] at turn
  rw [firstEq] at forward
  rcases frontier with p|p
  · change LabelledTurn site.net (.inl ⟨.inr (.inl ()),.inr p⟩) f a middle at turn
    obtain ⟨q,departure,_rule⟩ := turn.from_node (.inr (.inl ())) (.inr p) rfl
    subst f
    have direction := forward.actual_node_ports (g:=site.net) (.inr (.inl ())) (.inr p) q tail
    change Sum.inr p=appCtx ∧(q=Sum.inl () ∨q=appArg) at direction
    rcases direction.2 with rfl|rfl
    · change [Step.fn]=[] at token
      cases token
    · change [Step.arg]=[] at token
      cases token
  · change LabelledTurn site.net (.inl ⟨.inr (.inr ()),.inr p⟩) f a middle at turn
    obtain ⟨q,departure,_rule⟩ := turn.from_node (.inr (.inr ())) (.inr p) rfl
    subst f
    have direction := forward.actual_node_ports (g:=site.net) (.inr (.inr ())) (.inr p) q tail
    change Sum.inr p=Sum.inl () ∧_ at direction
    cases direction.1
private theorem outside_turn {e f : Endpoint cut} {next : Endpoint site.net} {a b : Context}
    (arrival : (cut).wire e=f) (notFrontier : ∀ x,f≠.inr (.inl (.inr x)))
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
/-- A real forward atomic fragment beginning outside cannot cross either
removed proper node: every such forward turn would emit a syntax token.
This is a finite statement about the supplied path, with no empty-fiber,
root reachability, target label, or completion premise. -/
theorem PathSite.beta_empty_word_exterior {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (forward : Forward site.net es)
    (emptyWord : accessWord site.net es=[])
    (first : Endpoint cut) (head : es.head?=some (site.outsideEnd first)) :
    ∃ exterior : List (Endpoint cut),es=exterior.map site.outsideEnd ∧Labelling cut exterior a b := by
  induction labels generalizing first with
  | single e a =>
    have same := Option.some.inj head
    exact ⟨[first],by simp only [List.map_cons,List.map_nil,same],.single first a⟩
  | @cons e f tail a middle b turn after ih =>
    have same := Option.some.inj head
    subst e
    have words : arrivalWord site.net f=[] ∧tail.flatMap (arrivalWord site.net)=[] := by
      exact List.append_eq_nil_iff.mp emptyWord
    have notFrontier : ∀ frontier,(cut).wire first≠.inr (.inl (.inr frontier)) := by
      intro frontier arrival
      exact no_frontier_turn site frontier arrival turn forward words.1
    obtain ⟨next,nextEq,actual⟩ := outside_turn site rfl notFrontier turn
    have tailForward : Forward site.net (f::tail) := by cases forward <;> assumption
    obtain ⟨exterior,equal,remaining⟩ := ih tailForward words.2 next (by simp only [List.head?_cons,nextEq])
    have exteriorHead : exterior.head?=some next := by
      have same := congrArg List.head? equal
      rw [List.head?_cons,List.head?_map,nextEq] at same
      cases exterior with
      | nil => cases same
      | cons x xs =>
        have endpointEq := Option.some.inj same
        exact congrArg some ((site.outsideEnd_injective endpointEq).symm)
    obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp exteriorHead
    refine ⟨first::exterior,?_,?_⟩
    · simp only [List.map_cons,←equal]
    · rw [split] at remaining ⊢
      exact .cons actual remaining
end
end Lamping.AG
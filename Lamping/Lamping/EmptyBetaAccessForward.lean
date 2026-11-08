import Lamping.Lamping.EmptyBetaSourceExterior
import Lamping.Lamping.BetaResidualOccurrences
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
local notation "rhs" => wires Bool Bool boolFlip

private theorem outside_word {es : List (Endpoint cut)} {a b : Context}
    (labels : Labelling cut es a b) :
    accessWord site.net (es.map site.outsideEnd)=accessWord cut es := by
  induction labels with
  | single e a => rfl
  | @cons e f tail a middle b turn after ih =>
    have word : arrivalWord site.net (site.outsideEnd f)=arrivalWord cut f := by
      rcases f with ⟨node,p⟩ | ((boundary|frontier)|⟨vertex,direction⟩)
      · rfl
      · exact False.elim (turn.reverse.not_boundary (.inl boundary) rfl)
      · exact False.elim (turn.reverse.not_boundary (.inr frontier) rfl)
      · rfl
    change arrivalWord site.net (site.outsideEnd f)++
      (tail.map site.outsideEnd).flatMap (arrivalWord site.net)=
      arrivalWord cut f++tail.flatMap (arrivalWord cut)
    change (tail.map site.outsideEnd).flatMap (arrivalWord site.net)=
      tail.flatMap (arrivalWord cut) at ih
    rw [word,ih]

/-- Both directions use the unchanged literal exterior path. The full word
and endpoint kind survive an actual beta with empty old syntax fiber. -/
theorem PathSite.empty_beta_access_forward
    {root : B} {t : Term} (matching : Matches site.net root t)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (empty : site.betaSyntaxFiber root t=[])
    (source : RootAccess site.net root) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  obtain ⟨a,b,labels⟩ := source.property.1.1
  obtain ⟨outside,physical,cutLabels⟩ :=
    site.empty_beta_source_exterior matching flow positive oldT empty labels source.property.2.1
  have head : outside.head?=some (.inr (.inl (.inl root))) := by
    have raw := source.property.2.1
    rw [physical,List.head?_map] at raw
    cases h : outside with
    | nil => rw [h] at raw; cases raw
    | cons e es =>
      rw [h] at raw
      have same := site.outsideEnd_injective (show site.outsideEnd e=site.outsideEnd (.inr (.inl (.inl root))) from Option.some.inj raw)
      exact congrArg some same
  have newLabels := cutLabels.plugLeft cut rhs
  have newRoot : (outside.map (AG.plugLeft cut rhs)).head?=some (.inr (.inl root)) := by
    rw [List.head?_map,head]; rfl
  have kind : accessKind site.reduce (outside.map (AG.plugLeft cut rhs))=accessKind site.net source.val := by
    rw [physical]
    cases last : outside.getLast? with
    | none => simp only [accessKind,List.getLast?_map,last,Option.map_none,Option.bind_none]
    | some e =>
      simp only [accessKind,List.getLast?_map,last,Option.map_some,Option.bind_some]
      have wired : site.reduce.wire (AG.plugLeft cut rhs e)=AG.plugLeft cut rhs ((cut).wire e) :=
        plugLeft_wire cut rhs e
      rw [wired,site.outsideEnd_wire]
      generalize arrival : (cut).wire e=terminal
      rcases terminal with ⟨node,p⟩ | ((boundary|frontier)|⟨vertex,direction⟩)
      · rfl
      · rfl
      · exact False.elim (site.empty_beta_frontier_not_visible matching flow positive oldT empty labels
          source.property.2.1 frontier (by
            rw [physical,List.getLast?_map,last]
            exact congrArg some (by rw [←arrival,←site.outsideEnd_wire,Pairing.involutive])))
      · rfl
  have typed : ∃ k,accessKind site.reduce (outside.map (AG.plugLeft cut rhs))=some k := by
    rw [kind]; exact source.property.2.2
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  refine ⟨⟨outside.map (AG.plugLeft cut rhs),⟨⟨⟨a,b,newLabels⟩,
    newLabels.root_forward_of_flow newFlow root newRoot positive⟩,newRoot,typed⟩⟩,?_,kind⟩
  rw [physical]
  exact (accessWord_plugLeft cut rhs outside).trans (outside_word site cutLabels).symm
end
end Lamping.AG



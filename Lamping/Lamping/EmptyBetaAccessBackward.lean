import Lamping.Lamping.EmptyBetaExcursions
import Lamping.Lamping.ReducedOutsideRoles
import Lamping.Lamping.InitialAccessWords
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed


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

/-- Every reduced root access is literally an exterior path when the actual
old beta syntax fiber is empty. The original labelling assignments are kept. -/
theorem PathSite.empty_beta_access_exterior
    {root : B} {t : Term} (matching : Matches site.net root t)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (empty : site.betaSyntaxFiber root t=[])
    (target : RootAccess site.reduce root) :
    ∃ (outside : List (Endpoint cut)) (a b : Context),
      target.val=outside.map (AG.plugLeft cut ((Schema.beta i).right.net)) ∧ Labelling cut outside a b ∧
      outside.head?=some (.inr (.inl (.inl root))) := by
  obtain ⟨terminal,role,level,finish,atPort,incoming⟩ := target.incoming_endpoint
  obtain ⟨node,p,same⟩ := site.reduced_incoming_kept (fun e => nomatch e) atPort incoming
  rw [same] at finish
  let first : Endpoint cut := .inr (.inl (.inl root))
  let last : Endpoint cut := (cut).wire (.inl ⟨node,p⟩)
  have targetLast : target.val.getLast?=some (AG.plugLeft cut ((Schema.beta i).right.net) last) := by
    rw [finish]
    exact congrArg some (plugLeft_wire cut ((Schema.beta i).right.net) (.inl ⟨node,p⟩))
  obtain ⟨a,b,labels⟩ := target.property.1.1
  have excursions := labels.wire_excursions cut ((Schema.beta i).right.net) first last target.property.2.1 targetLast
  have rawRoot : ((target.val.map (plugEnd (cut).label ((Schema.beta i).right.net).label).invFun).map
      (plugEnd (cut).label ((Schema.beta i).right.net).label)).head?=some (.inr (.inl root)) := by
    rw [plug_decomposition_flatten]
    exact target.property.2.1
  have directions := excursions.beta_entries_forward site flow root positive rawRoot
  have rawHead : (target.val.map (plugEnd (cut).label ((Schema.beta i).right.net).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,target.property.2.1]
    exact congrArg some ((plugEnd (cut).label ((Schema.beta i).right.net).label).left_inv (.inl first))
  obtain ⟨outside,eqs,outsideLabels⟩ := excursions.empty_beta_outside site matching flow positive oldT empty
    directions (Labelling.single (.inr (.inl root)) a) rfl rawHead rfl
  have outsideHead : outside.head?=some first := by
    rw [eqs,List.head?_map] at rawHead
    cases split : outside with
    | nil => rw [split] at rawHead; cases rawHead
    | cons e es => rw [split] at rawHead; exact congrArg some (Sum.inl.inj (Option.some.inj rawHead))
  refine ⟨outside,a,b,?_,outsideLabels,outsideHead⟩
  have flat := plug_decomposition_flatten cut ((Schema.beta i).right.net) target.val
  rw [eqs,List.map_map] at flat
  exact flat.symm

/-- An actual empty-fiber target access reflects with its full word and kind.
This alone does not assert variable-index preservation or forward coverage. -/
theorem PathSite.empty_beta_access_backward
    {root : B} {t : Term} (matching : Matches site.net root t)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (empty : site.betaSyntaxFiber root t=[])
    (target : RootAccess site.reduce root) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val := by
  obtain ⟨outside,a,b,physical,labels,head⟩ :=
    site.empty_beta_access_exterior matching flow positive oldT empty target
  have sourceLabels := labels.outsideEnd site
  have sourceRoot : (outside.map site.outsideEnd).head?=some (.inr (.inl root)) := by
    rw [List.head?_map,head]
    rfl
  obtain ⟨terminal,role,level,finish,atPort,incoming⟩ := target.incoming_endpoint
  obtain ⟨node,p,same⟩ := site.reduced_incoming_kept (fun e => nomatch e) atPort incoming
  rw [same,physical,List.getLast?_map] at finish
  have outsideLast : outside.getLast?=some ((cut).wire (.inl ⟨node,p⟩)) := by
    have original := plugLeft_wire cut ((Schema.beta i).right.net) (.inl ⟨node,p⟩)
    change site.reduce.wire (.inl ⟨.inl node,p⟩)=_ at original
    rw [original] at finish
    cases h : outside.getLast? with
    | none => rw [h] at finish; cases finish
    | some e =>
      rw [h] at finish
      have same := (plugEnd (cut).label ((Schema.beta i).right.net).label).injective (Option.some.inj finish)
      exact congrArg some (Sum.inl.inj same)
  have sourceLast : (outside.map site.outsideEnd).getLast?=
      some (site.net.wire (.inl ⟨.inl node,p⟩)) := by
    rw [List.getLast?_map,outsideLast]
    exact congrArg some (site.outsideEnd_wire (.inl ⟨node,p⟩)).symm
  have kind : accessKind site.net (outside.map site.outsideEnd)=accessKind site.reduce target.val := by
    have targetEnd : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,p⟩)) := by
      rw [physical,List.getLast?_map,outsideLast]
      exact congrArg some (plugLeft_wire cut ((Schema.beta i).right.net) (.inl ⟨node,p⟩)).symm
    simp only [accessKind,sourceLast,targetEnd,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ k,accessKind site.net (outside.map site.outsideEnd)=some k := by
    rw [kind]
    exact target.property.2.2
  refine ⟨⟨outside.map site.outsideEnd,⟨⟨⟨a,b,sourceLabels⟩,
    sourceLabels.root_forward_of_flow flow root sourceRoot positive⟩,sourceRoot,typed⟩⟩,?_,kind⟩
  rw [physical]
  exact (outside_word site labels).trans (accessWord_plugLeft cut ((Schema.beta i).right.net) outside).symm
end
end Lamping.AG



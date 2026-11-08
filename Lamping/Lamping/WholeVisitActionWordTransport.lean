import Lamping.Lamping.WholeControlVisitDecomposition
import Lamping.Lamping.ExposureControlWords
import Lamping.Lamping.ActionCanonicalAssembly
import Lamping.Lamping.ActionCrossingReplay

namespace Lamping.AG
open Graph
namespace ExposureScheduling
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

def departureWord (g : Net signature N B W) : Endpoint g → List Bool
  | .inl ⟨node,p⟩ => controlPortWord (g.label node).sort p
  | .inr _ => []

private theorem transparent_controlWord (g : Net signature N B W)
    (es : List (Endpoint g))
    (transparent : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) :
    controlWord g es=[] := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases es with
    | nil => rfl
    | cons f tail =>
      obtain ⟨w,d,_arrival,leaves⟩ := transparent e f (by simp)
      have rest := ih (by intro x y pair; exact transparent x y (List.mem_cons_of_mem _ pair))
      change departureWord g f++controlWord g (f::tail)=[]
      rw [rest,leaves]
      rfl
end

/-- Parallel exchanges are ordered on the complete word. The same outside
keptWord is kept on both sides; each counted block exchanges exactly WR to RW.
This relation is produced below, never a caller premise for physical expansion. -/
inductive ParallelControlExchanges : List Bool → List Bool → Nat → Prop where
  | nil : ParallelControlExchanges [] [] 0
  | keep (keptWord : List Bool) {new old n}
      (rest : ParallelControlExchanges new old n) :
      ParallelControlExchanges (keptWord++new) (keptWord++old) n
  | swap {new old n} (rest : ParallelControlExchanges new old n) :
      ParallelControlExchanges (false::true::new) (true::false::old) (n+1)

private theorem readers_append' (xs ys : List Bool) : readers (xs++ys)=readers xs+readers ys := by
  induction xs with
  | nil => simp [readers]
  | cons b bs ih => cases b <;> simp [readers,ih,Nat.add_assoc]
private theorem writers_append' (xs ys : List Bool) : writers (xs++ys)=writers xs+writers ys := by
  induction xs with
  | nil => simp [writers]
  | cons b bs ih => cases b <;> simp [writers,ih,Nat.add_assoc]
private theorem inversions_append' (xs ys : List Bool) :
    inversions (xs++ys)=inversions xs+inversions ys+writers xs*readers ys := by
  induction xs with
  | nil => simp [inversions,writers]
  | cons b bs ih =>
    cases b <;> simp [inversions,writers,readers_append',ih,Nat.add_mul] <;> omega

/-- All simultaneous, possibly repeated-site exchanges lower inversions by
the derived visit count. No sequential single-occurrence rewrite is assumed. -/
theorem ParallelControlExchanges.statistics {new old n}
    (relation : ParallelControlExchanges new old n) :
    new.length=old.length ∧readers new=readers old ∧writers new=writers old ∧
      inversions old=inversions new+n := by
  induction relation with
  | nil => simp [readers,writers,inversions]
  | keep keptWord rest ih =>
    rcases ih with ⟨length,r,w,i⟩
    refine ⟨by simp [length],by simp [readers_append',r],by simp [writers_append',w],?_⟩
    rw [inversions_append',inversions_append',←r,i]
    omega
  | swap rest ih =>
    rcases ih with ⟨length,r,w,i⟩
    refine ⟨by simp [length],?_,?_,?_⟩
    · simp [readers,r]
    · simp [writers,w]
    · simp [inversions,readers,r] at i ⊢
      omega

theorem ParallelControlExchanges.strict_of_positive {new old n}
    (relation : ParallelControlExchanges new old n) (positive : 0<n) :
    new.length=old.length ∧inversions new<inversions old := by
  obtain ⟨length,_r,_w,inversionsEq⟩ := relation.statistics
  exact ⟨length,by omega⟩
end ExposureScheduling

open ExposureScheduling
private theorem op_control_principal_letter (op : Op)
    (control : op=.fan ∨op=.cro ∨op=.bra) :
    controlPortWord (.op op) (.inl ())=[true] := by
  rcases control with rfl |rfl |rfl <;> rfl

private theorem op_control_auxiliary_letter (op : Op) (p : Aux op)
    (control : op=.fan ∨op=.cro ∨op=.bra) :
    controlPortWord (.op op) (.inr p)=[false] := by
  rcases control with rfl |rfl |rfl <;> rfl

section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem crossing_control_word
    (activeControl : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (principal : SiteActionPrincipal site) (p : Aux s.active) (q : Aux s.passive)
    (tail : List (Endpoint site.net)) :
    controlWord site.net (principal.crossing site p q++tail)=
      true::false::controlWord site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::tail) := by
  obtain ⟨rest,shape⟩ := List.head?_eq_some_iff.mp principal.first
  have transparent := transparent_controlWord site.net principal.edges principal.transparent
  rw [shape] at transparent
  change rest.flatMap (departureWord site.net)=[] at transparent
  change ((principal.edges++[(.inl ⟨.inr (.inr ()),.inr q⟩ : Endpoint site.net)])++tail).flatMap
      (departureWord site.net)=true::false::controlWord site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::tail)
  rw [List.flatMap_append,List.flatMap_append,shape,List.flatMap_cons,transparent]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change (controlPortWord (.op s.active) (.inl ()) ++
      controlPortWord (.op s.passive) (.inr q)) ++ tail.flatMap (departureWord site.net) =
    true::false::tail.flatMap (departureWord site.net)
  rw [op_control_principal_letter s.active activeControl,
    op_control_auxiliary_letter s.passive q passiveControl] <;> rfl

private theorem backward_control_word
    (activeControl : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (principal : SiteActionPrincipal site) (p : Aux s.active) (q : Aux s.passive)
    (tail : List (Endpoint site.net)) :
    controlWord site.net (reverseEdges (principal.crossing site p q)++tail)=
      true::false::controlWord site.net ((.inl ⟨.inr (.inl ()),.inr p⟩)::tail) := by
  have head : (reverseEdges principal.edges).head?=
      some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
  obtain ⟨rest,shape⟩ := List.head?_eq_some_iff.mp head
  have transparent := transparent_controlWord site.net (reverseEdges principal.edges)
    (transparent_reverse_turns principal.edges principal.transparent)
  rw [shape] at transparent
  change rest.flatMap (departureWord site.net)=[] at transparent
  rw [principal.reverse_crossing_edges site]
  change ((reverseEdges principal.edges++[(.inl ⟨.inr (.inl ()),.inr p⟩ : Endpoint site.net)])++tail).flatMap
      (departureWord site.net)=true::false::controlWord site.net ((.inl ⟨.inr (.inl ()),.inr p⟩)::tail)
  rw [List.flatMap_append,List.flatMap_append,shape,List.flatMap_cons,transparent]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change (controlPortWord (.op s.passive) (.inl ()) ++
      controlPortWord (.op s.active) (.inr p)) ++ tail.flatMap (departureWord site.net) =
    true::false::tail.flatMap (departureWord site.net)
  rw [op_control_principal_letter s.passive passiveControl,
    op_control_auxiliary_letter s.active p activeControl] <;> rfl

/-- The raw word reads actual cut/RHS node departures, ignoring glue vertices. -/
def actionRawControlWord (raw : List (PlugSegment cut s.right.net)) : List Bool :=
  raw.tail.flatMap (Sum.elim (departureWord cut) (departureWord s.right.net))

private theorem physical_control_word_raw (raw : List (PlugSegment cut s.right.net)) :
    controlWord site.reduce (raw.map (plugEnd (cut).label s.right.net.label))=
      actionRawControlWord site raw := by
  cases raw with
  | nil => rfl
  | cons e raw =>
    have tags : (fun piece => departureWord site.reduce
        ((plugEnd (cut).label s.right.net.label) piece))=
        Sum.elim (departureWord cut) (departureWord s.right.net) := by
      funext piece
      rcases piece with (⟨node,p⟩|((boundary|frontier)|⟨vertex,direction⟩))|
        (⟨node,p⟩|(frontier|⟨vertex,direction⟩)) <;> rfl
    change (raw.map (plugEnd (cut).label s.right.net.label)).flatMap
      (departureWord site.reduce)=raw.flatMap (Sum.elim (departureWord cut) (departureWord s.right.net))
    rw [List.flatMap_map]
    change raw.flatMap (fun piece => departureWord site.reduce
      ((plugEnd (cut).label s.right.net.label) piece))=_
    rw [tags]

private theorem outside_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have mapped := congrArg split same
  change split (split.invFun (.inl e))=split (split.invFun (.inl f)) at mapped
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

private theorem reflect_retained_turn {e f : Endpoint cut} {a b : Context}
    (geometry : ∃ x y,LabelledTurn cut ((cut).wire e) f x y)
    (actual : LabelledTurn site.net (site.net.wire (site.outsideEnd e)) (site.outsideEnd f) a b) :
    LabelledTurn cut ((cut).wire e) f a b := by
  obtain ⟨x,y,geometry⟩ := geometry
  rw [site.outsideEnd_wire] at actual
  generalize shape : (cut).wire e=arrival at geometry actual ⊢
  cases geometry with
  | node node p q rule =>
    change LabelledTurn site.net (.inl ⟨.inl node,p⟩) (.inl ⟨.inl node,q⟩) a b at actual
    cases actual with | node node p q actualRule => exact .node _ _ _ actualRule
  | transparent w d x =>
    change LabelledTurn site.net (.inr (.inr (.inl w,d))) (.inr (.inr (.inl w,!d))) a b at actual
    cases actual
    exact .transparent _ _ _

private theorem retained_departure_word {e f : Endpoint cut}
    (geometry : ∃ x y,LabelledTurn cut ((cut).wire e) f x y) :
    departureWord site.net (site.outsideEnd f)=departureWord cut f := by
  obtain ⟨x,y,turn⟩ := geometry
  generalize arrivalEq : (cut).wire e = arrival at turn
  cases turn <;> rfl

private theorem raw_outside_word (e f : Endpoint cut) (tail : List (PlugSegment cut s.right.net)) :
    actionRawControlWord site (.inl e::.inl f::tail)=
      departureWord cut f++actionRawControlWord site (.inl f::tail) := rfl

private theorem raw_through_word (e : Endpoint cut) {enter exit : s.Frontier}
    {a b : Context} (inside : LocalPath s.right.net enter exit a b)
    (tail : List (PlugSegment cut s.right.net)) :
    actionRawControlWord site (.inl e::(inside.edges.map Sum.inr++
      .inl (.inr (.inl (.inr exit)))::tail))=
      controlWord s.right.net inside.edges++
        actionRawControlWord site (.inl (.inr (.inl (.inr exit)))::tail) := by
  obtain ⟨rest,shape⟩ := List.head?_eq_some_iff.mp inside.start
  rw [shape]
  simp [actionRawControlWord,controlWord,List.flatMap_append,List.flatMap_map,
    departureWord] <;> rfl

private theorem complete_cross_expansion
    (action : IsAction s) (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (principal : SiteActionPrincipal site) (p : Aux s.active) (q : Aux s.passive)
    {a b : Context} (labels : Labelling site.net (principal.crossing site p q) a b) :
    ∃ inside : LocalPath s.right.net (.inl p) (.inr q) a b,
      ActionCanonicalLocal site principal inside.edges (principal.crossing site p q) ∧
      controlWord s.right.net inside.edges=[false,true] := by
  have localLabels := (principal.crossing_labels_iff site p q a b).mp labels
  cases action with
  | fan f i j lt =>
    let inside : LocalPath (fanRight f i j) (.inl p) (.inr q) a b :=
      ⟨fanCrossEdges p q,rfl,rfl,fanAction_cross_replay f i j lt p q a b localLabels⟩
    exact ⟨inside,.fan (.cross p q),fan_control_crossing_word f i j passiveControl p q⟩
  | cro f i j lt =>
    cases p
    let inside : LocalPath (unaryRightCore .cro f (Bij.refl _) i (j-1)) (.inl ()) (.inr q) a b :=
      ⟨unaryCrossEdges (s:=.croAction f i j lt) (k:=(j-1)) (Bij.refl _) q,rfl,rfl,
        croAction_cross_replay f i j lt q a b localLabels⟩
    exact ⟨inside,.cro (.cross q),
      unary_control_crossing_word .cro f i (j-1) (Or.inl rfl) passiveControl (Bij.refl _) q⟩
  | bra f i j lt =>
    cases p
    let inside : LocalPath (unaryRightCore .bra f (Bij.refl _) i (j+1)) (.inl ()) (.inr q) a b :=
      ⟨unaryCrossEdges (s:=.braAction f i j lt) (k:=(j+1)) (Bij.refl _) q,rfl,rfl,
        braAction_cross_replay f i j lt q a b localLabels⟩
    exact ⟨inside,.bra (.cross q),
      unary_control_crossing_word .bra f i (j+1) (Or.inr rfl) passiveControl (Bij.refl _) q⟩

private theorem complete_backward_expansion
    (action : IsAction s) (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (principal : SiteActionPrincipal site) (p : Aux s.active) (q : Aux s.passive)
    {a b : Context} (labels : Labelling site.net (reverseEdges (principal.crossing site p q)) a b) :
    ∃ inside : LocalPath s.right.net (.inr q) (.inl p) a b,
      ActionCanonicalLocal site principal inside.edges (reverseEdges (principal.crossing site p q)) ∧
      controlWord s.right.net inside.edges=[false,true] := by
  have forwardLabels := labels.reverse
  rw [reverseEdges_involutive] at forwardLabels
  have localLabels := (principal.crossing_labels_iff site p q b a).mp forwardLabels
  cases action with
  | fan f i j lt =>
    let inside : LocalPath (fanRight f i j) (.inl p) (.inr q) b a :=
      ⟨fanCrossEdges p q,rfl,rfl,fanAction_cross_replay f i j lt p q b a localLabels⟩
    exact ⟨inside.reverse,.fan (.backward p q),fan_control_reverse_word f i j passiveControl p q⟩
  | cro f i j lt =>
    cases p
    let inside : LocalPath (unaryRightCore .cro f (Bij.refl _) i (j-1)) (.inl ()) (.inr q) b a :=
      ⟨unaryCrossEdges (s:=.croAction f i j lt) (k:=(j-1)) (Bij.refl _) q,rfl,rfl,
        croAction_cross_replay f i j lt q b a localLabels⟩
    exact ⟨inside.reverse,.cro (.backward q),
      unary_control_reverse_word .cro f i (j-1) (Or.inl rfl) passiveControl (Bij.refl _) q⟩
  | bra f i j lt =>
    cases p
    let inside : LocalPath (unaryRightCore .bra f (Bij.refl _) i (j+1)) (.inl ()) (.inr q) b a :=
      ⟨unaryCrossEdges (s:=.braAction f i j lt) (k:=(j+1)) (Bij.refl _) q,rfl,rfl,
        braAction_cross_replay f i j lt q b a localLabels⟩
    exact ⟨inside.reverse,.bra (.backward q),
      unary_control_reverse_word .bra f i (j+1) (Or.inr rfl) passiveControl (Bij.refl _) q⟩

private theorem active_control_of_action (action : IsAction s) :
    s.active=.fan ∨s.active=.cro ∨s.active=.bra := by
  cases action with
  | fan => exact Or.inl rfl
  | cro => exact Or.inr (Or.inl rfl)
  | bra => exact Or.inr (Or.inr rfl)

/-- Expand every visit of the SAME source list into the actual canonical RHS.
Neither a root-keptWord replay oracle nor a target reference is required: the
control/control partition has already eliminated every passive local branch.
The constructed raw word performs all n exchanges, not just the selected one. -/
theorem WholeControlVisits.action_word_expansion
    (action : IsAction s) (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    {principal : SiteActionPrincipal site} {es n}
    (visits : WholeControlVisits site principal es n)
    {a b : Context} (labels : Labelling site.net es a b)
    (first last : Endpoint cut) (head : es.head?=some (site.outsideEnd first))
    (finish : es.getLast?=some (site.outsideEnd last)) :
    ∃ raw : List (PlugSegment cut s.right.net),
      PlugExcursions cut s.right.net raw a b ∧
      ActionCanonicalBlocks site principal raw es ∧
      raw.head?=some (.inl first) ∧raw.getLast?=some (.inl last) ∧
      ParallelControlExchanges (actionRawControlWord site raw) (controlWord site.net es) n := by
  have activeControl := active_control_of_action action
  induction visits generalizing a b first last with
  | single e =>
    have firstEq : e=first := outside_injective site (Option.some.inj head)
    have lastEq : e=last := outside_injective site (Option.some.inj finish)
    subst first
    subst last
    cases labels
    exact ⟨[.inl e],.single e _,.single e,rfl,rfl,.nil⟩
  | outside e f tail geometry rest ih =>
    have firstEq : e=first := outside_injective site (Option.some.inj head)
    subst first
    cases labels with
    | @cons _ _ _ _ middle _ sourceTurn sourceRest =>
      have localTurn := reflect_retained_turn site geometry sourceTurn
      have suffixFinish : (site.outsideEnd f::tail).getLast?=some (site.outsideEnd last) := by
        simpa only [List.getLast?_cons_cons] using finish
      obtain ⟨raw,path,canonical,rawHead,rawLast,exchange⟩ := ih sourceRest f last rfl suffixFinish
      obtain ⟨rawTail,rawEq⟩ := List.head?_eq_some_iff.mp rawHead
      rw [rawEq] at path canonical rawLast exchange
      refine ⟨.inl e::.inl f::rawTail,.outside localTurn path,.outside canonical,rfl,?_,?_⟩
      · simpa only [List.getLast?_cons_cons] using rawLast
      · have oldWord : controlWord site.net (site.outsideEnd e::site.outsideEnd f::tail)=
            departureWord cut f++controlWord site.net (site.outsideEnd f::tail) := by
          change departureWord site.net (site.outsideEnd f)++_=departureWord cut f++_
          rw [retained_departure_word site geometry]
          rfl
        rw [raw_outside_word,oldWord]
        exact .keep (departureWord cut f) exchange
  | @cross p q tail n rest ih =>
    let exit : Endpoint site.net := .inl ⟨.inr (.inr ()),.inr q⟩
    let pre := site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::principal.edges
    have frontEq : principal.crossing site p q=pre++[exit] := rfl
    have overlapLabels : Labelling site.net (pre++exit::tail) a b := by
      simpa only [frontEq,List.append_assoc,List.singleton_append] using labels
    obtain ⟨middle,frontLabels,suffixLabels⟩ := overlapLabels.split_segment
    have crossingLabels : Labelling site.net (principal.crossing site p q) a middle := by
      simpa only [frontEq] using frontLabels
    obtain ⟨inside,localCanonical,rhsWord⟩ :=
      complete_cross_expansion site action passiveControl principal p q crossingLabels
    let exitCut : Endpoint cut := .inr (.inl (.inr (.inr q)))
    have lastSame : ((principal.crossing site p q)++tail).getLast?=(exit::tail).getLast? := by
      simp only [frontEq,List.append_assoc,List.singleton_append,List.getLast?_append,
        List.getLast?_cons,Option.some_or]
    have suffixFinish : (exit::tail).getLast?=some (site.outsideEnd last) := lastSame.symm.trans finish
    obtain ⟨raw,path,canonical,rawHead,rawLast,exchange⟩ := ih suffixLabels exitCut last rfl suffixFinish
    obtain ⟨rawTail,rawEq⟩ := List.head?_eq_some_iff.mp rawHead
    rw [rawEq] at path canonical rawLast exchange
    have firstImage : site.outsideEnd first=site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩) := by
      simpa only [SiteActionPrincipal.crossing,List.cons_append,List.head?_cons] using (Option.some.inj head).symm
    have arrival : (cut).wire first=.inr (.inl (.inr (.inl p))) := by
      apply outside_injective site
      rw [←site.outsideEnd_wire,firstImage,Pairing.involutive]
      rfl
    have localResidual : ActionCanonicalLocal site principal inside.edges
        (pre++[site.outsideEnd exitCut]) := localCanonical
    have start : (pre++[site.outsideEnd exitCut]).head?=some (site.outsideEnd first) := by
      change some (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩))=some (site.outsideEnd first)
      exact congrArg some firstImage.symm
    refine ⟨.inl first::(inside.edges.map Sum.inr++.inl exitCut::rawTail),
      .through inside arrival path,?_,rfl,?_,?_⟩
    · simpa only [frontEq,List.append_assoc,List.singleton_append] using
        (ActionCanonicalBlocks.through (site:=site) inside.edges pre localResidual start canonical)
    · simpa only [List.getLast?_cons_cons,List.getLast?_append,List.getLast?_cons,Option.some_or] using rawLast
    · rw [raw_through_word site first inside rawTail,rhsWord,
        crossing_control_word site activeControl passiveControl principal p q tail]
      exact .swap exchange
  | @backward p q tail n rest ih =>
    let exit : Endpoint site.net := .inl ⟨.inr (.inl ()),.inr p⟩
    let pre := site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)::reverseEdges principal.edges
    have frontEq : reverseEdges (principal.crossing site p q)=pre++[exit] :=
      principal.reverse_crossing_edges site p q
    have overlapLabels : Labelling site.net (pre++exit::tail) a b := by
      simpa only [frontEq,List.append_assoc,List.singleton_append] using labels
    obtain ⟨middle,frontLabels,suffixLabels⟩ := overlapLabels.split_segment
    have crossingLabels : Labelling site.net (reverseEdges (principal.crossing site p q)) a middle := by
      simpa only [frontEq] using frontLabels
    obtain ⟨inside,localCanonical,rhsWord⟩ :=
      complete_backward_expansion site action passiveControl principal p q crossingLabels
    let exitCut : Endpoint cut := .inr (.inl (.inr (.inl p)))
    have lastSame : (reverseEdges (principal.crossing site p q)++tail).getLast?=(exit::tail).getLast? := by
      simp only [frontEq,List.append_assoc,List.singleton_append,List.getLast?_append,
        List.getLast?_cons,Option.some_or]
    have suffixFinish : (exit::tail).getLast?=some (site.outsideEnd last) := lastSame.symm.trans finish
    obtain ⟨raw,path,canonical,rawHead,rawLast,exchange⟩ := ih suffixLabels exitCut last rfl suffixFinish
    obtain ⟨rawTail,rawEq⟩ := List.head?_eq_some_iff.mp rawHead
    rw [rawEq] at path canonical rawLast exchange
    have firstImage : site.outsideEnd first=site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩) := by
      have sourceHead : (reverseEdges (principal.crossing site p q)++tail).head?=
          some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) := by
        simp only [principal.reverse_crossing_edges site p q,List.cons_append,List.head?_cons]
      exact Option.some.inj (head.symm.trans sourceHead)
    have arrival : (cut).wire first=.inr (.inl (.inr (.inr q))) := by
      apply outside_injective site
      rw [←site.outsideEnd_wire,firstImage,Pairing.involutive]
      rfl
    have localResidual : ActionCanonicalLocal site principal inside.edges
        (pre++[site.outsideEnd exitCut]) := by
      simpa only [frontEq] using localCanonical
    have start : (pre++[site.outsideEnd exitCut]).head?=some (site.outsideEnd first) := by
      change some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩))=some (site.outsideEnd first)
      exact congrArg some firstImage.symm
    refine ⟨.inl first::(inside.edges.map Sum.inr++.inl exitCut::rawTail),
      .through inside arrival path,?_,rfl,?_,?_⟩
    · simpa only [frontEq,List.append_assoc,List.singleton_append] using
        (ActionCanonicalBlocks.through (site:=site) inside.edges pre localResidual start canonical)
    · simpa only [List.getLast?_cons_cons,List.getLast?_append,List.getLast?_cons,Option.some_or] using rawLast
    · rw [raw_through_word site first inside rawTail,rhsWord,
        backward_control_word site activeControl passiveControl principal p q tail]
      exact .swap exchange

/-- The physically plugged RHS has the SAME complete labels and canonical
source list, and its word makes all exchanges simultaneously. -/
theorem WholeControlVisits.action_physical_word_transport
    (action : IsAction s) (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    {principal : SiteActionPrincipal site} {es n}
    (visits : WholeControlVisits site principal es n)
    {a b : Context} (labels : Labelling site.net es a b)
    (first last : Endpoint cut) (head : es.head?=some (site.outsideEnd first))
    (finish : es.getLast?=some (site.outsideEnd last)) :
    ∃ target : List (Endpoint site.reduce),
      Labelling site.reduce target a b ∧
      ActionCanonicalBlocks site principal
        (target.map (plugEnd (cut).label s.right.net.label).invFun) es ∧
      target.head?=some (AG.plugLeft cut s.right.net first) ∧
      target.getLast?=some (AG.plugLeft cut s.right.net last) ∧
      ParallelControlExchanges (controlWord site.reduce target) (controlWord site.net es) n := by
  obtain ⟨raw,path,canonical,rawHead,rawLast,exchange⟩ :=
    visits.action_word_expansion site action passiveControl labels first last head finish
  refine ⟨raw.map (plugEnd (cut).label s.right.net.label),
    (path.labelling cut s.right.net).actual cut s.right.net,?_,?_,?_,?_⟩
  · simpa only [List.map_map,Function.comp_def,(plugEnd (cut).label s.right.net.label).left_inv,List.map_id_fun'] using canonical
  · rw [List.head?_map,rawHead]
    rfl
  · rw [List.getLast?_map,rawLast]
    rfl
  · rw [physical_control_word_raw]
    exact exchange

/-- Positive complete visits supply genuine whole-word strict decrease for
this constructed physical RHS, without assuming a caller rank law. -/
theorem WholeControlVisits.action_physical_strict_decrease
    (action : IsAction s) (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    {principal : SiteActionPrincipal site} {es n}
    (visits : WholeControlVisits site principal es n) (positive : 0<n)
    {a b : Context} (labels : Labelling site.net es a b)
    (first last : Endpoint cut) (head : es.head?=some (site.outsideEnd first))
    (finish : es.getLast?=some (site.outsideEnd last)) :
    ∃ target : List (Endpoint site.reduce),
      Labelling site.reduce target a b ∧
      ActionCanonicalBlocks site principal
        (target.map (plugEnd (cut).label s.right.net.label).invFun) es ∧
      (controlWord site.reduce target).length=(controlWord site.net es).length ∧
      inversions (controlWord site.reduce target)<inversions (controlWord site.net es) := by
  obtain ⟨target,actual,canonical,_head,_finish,relation⟩ :=
    visits.action_physical_word_transport site action passiveControl labels first last head finish
  obtain ⟨length,less⟩ := relation.strict_of_positive positive
  exact ⟨target,actual,canonical,length,less⟩
end
end Lamping.AG

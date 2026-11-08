import Lamping.Lamping.WholeControlVisitDecomposition
import Lamping.Lamping.WholeVisitActionWordTransport
import Lamping.Lamping.SelectedCancellationConnectionTransport
import Lamping.Lamping.CancellationCanonicalComparison

namespace Lamping.AG
open Graph Lambda Lambda.Labelled ExposureScheduling

/-- All counted cancellation crossings are deleted, with the SAME ordered
outside word retained. This is derived below from actual paths/residuals. -/
inductive ParallelControlErasures : List Bool → List Bool → Nat → Prop where
  | nil : ParallelControlErasures [] [] 0
  | keep (keptWord : List Bool) {new old n} (rest : ParallelControlErasures new old n) :
      ParallelControlErasures (keptWord++new) (keptWord++old) n
  | erase {new old n} (rest : ParallelControlErasures new old n) :
      ParallelControlErasures new (true::false::old) (n+1)

theorem ParallelControlErasures.count {new old n} (relation : ParallelControlErasures new old n) :
    old.length=new.length+2*n := by
  induction relation with
  | nil => rfl
  | keep keptWord rest ih => simp only [List.length_append]; omega
  | erase rest ih => simp only [List.length_cons]; omega

theorem ParallelControlErasures.strict_of_positive {new old n}
    (relation : ParallelControlErasures new old n) (positive : 0<n) : new.length<old.length := by
  have count := relation.count
  omega

section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

/-- Merely packages the actual existing wire-only RHS relation after the
three constructors have reduced its Empty node/vertex carriers. -/
def CancellationRawPath (cancel : IsCancellation s)
    (raw : List (PlugSegment cut s.right.net)) (a b : Context) : Prop := by
  cases s with
  | fanCancel i =>
    let c := cutFragment site.net (pathPartition (.fanCancel i) V) site.closed
    let r := (Schema.fanCancel i).right.net
    exact WireExcursions c r raw a b
  | croCancel i =>
    let c := cutFragment site.net (pathPartition (.croCancel i) V) site.closed
    let r := (Schema.croCancel i).right.net
    exact WireExcursions c r raw a b
  | braCancel i =>
    let c := cutFragment site.net (pathPartition (.braCancel i) V) site.closed
    let r := (Schema.braCancel i).right.net
    exact WireExcursions c r raw a b
  | _ => exact False.elim (by cases cancel)

def CancellationRawResidual (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    (raw : List (PlugSegment cut s.right.net)) (old : List (Endpoint site.net)) : Prop := by
  cases s with
  | fanCancel i =>
    let c := cutFragment site.net (pathPartition (.fanCancel i) V) site.closed
    let r := (Schema.fanCancel i).right.net
    exact CanonicalWireResidual c r site.net site.outsideEnd (site.cancellation_canonical_fronts principal.edges) raw old
  | croCancel i =>
    let c := cutFragment site.net (pathPartition (.croCancel i) V) site.closed
    let r := (Schema.croCancel i).right.net
    exact CanonicalWireResidual c r site.net site.outsideEnd (site.cancellation_canonical_fronts principal.edges) raw old
  | braCancel i =>
    let c := cutFragment site.net (pathPartition (.braCancel i) V) site.closed
    let r := (Schema.braCancel i).right.net
    exact CanonicalWireResidual c r site.net site.outsideEnd (site.cancellation_canonical_fronts principal.edges) raw old
  | _ => exact False.elim (by cases cancel)

private theorem raw_path_head (cancel : IsCancellation s) {raw a b}
    (path : CancellationRawPath site cancel raw a b) :
    ∃ first,raw.head?=some (.inl first) := by
  cases cancel
  all_goals
    cases path with
    | single e a => exact ⟨e,rfl⟩
    | @outside e f tail a b c turn rest => exact ⟨e,rfl⟩
    | @through e f tail a b arrival rest => exact ⟨e,rfl⟩

private theorem raw_residual_head (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    {raw old e} (relation : CancellationRawResidual site cancel principal raw old)
    (head : raw.head?=some (.inl e)) : old.head?=some (site.outsideEnd e) := by
  let c := cut
  let r := s.right.net
  let fronts := site.cancellation_canonical_fronts principal.edges
  cases cancel
  all_goals exact CanonicalWireResidual.head c r site.net site.outsideEnd fronts relation head

private theorem raw_path_actual (cancel : IsCancellation s) {raw a b}
    (path : CancellationRawPath site cancel raw a b) :
    Labelling site.reduce (raw.map (plugEnd (cut).label s.right.net.label)) a b := by
  let c := cut
  let r := s.right.net
  cases cancel
  all_goals exact (path.labelling c r).actual c r

private theorem raw_residual_actual (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    {raw old} (relation : CancellationRawResidual site cancel principal raw old) :
    CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges)
      (raw.map (plugEnd (cut).label s.right.net.label)) old := by
  let c := cut
  let r := s.right.net
  let fronts := site.cancellation_canonical_fronts principal.edges
  cases cancel
  all_goals
    change CanonicalWireResidual c r site.net site.outsideEnd fronts
      ((raw.map (plugEnd c.label r.label)).map (plugEnd c.label r.label).invFun) old
    simpa only [List.map_map,Function.comp_def,(plugEnd c.label r.label).left_inv,
      List.map_id_fun'] using relation

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

private theorem retained_word {e f : Endpoint cut}
    (geometry : ∃ x y,LabelledTurn cut ((cut).wire e) f x y) :
    departureWord site.net (site.outsideEnd f)=departureWord cut f := by
  obtain ⟨x,y,turn⟩ := geometry
  generalize arrivalEq : (cut).wire e=arrival at turn
  cases turn <;> rfl

private theorem crossing_cancel_facts (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    (p : Aux s.active) (q : Aux s.passive) {a b : Context}
    (labels : Labelling site.net (principal.crossing site p q) a b) :
    cancellationMate s (.inl p)=.inr q ∧a=b := by
  have localLabels := (principal.crossing_labels_iff site p q a b).mp labels
  obtain ⟨middle,writer,reader⟩ :=
    (leftRoute_labeling_iff s.active s.passive s.low s.high p q a b).mp localLabels
  cases cancel
  all_goals
    obtain ⟨branch,context⟩ := writer.control_cancellation
      (by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)) reader
    subst q
    exact ⟨rfl,context⟩

private theorem backward_cancel_facts (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    (p : Aux s.active) (q : Aux s.passive) {a b : Context}
    (labels : Labelling site.net (reverseEdges (principal.crossing site p q)) a b) :
    cancellationMate s (.inr q)=.inl p ∧a=b := by
  have forward := labels.reverse
  rw [reverseEdges_involutive] at forward
  obtain ⟨mate,context⟩ := crossing_cancel_facts site cancel principal p q forward
  have swapped : cancellationMate s (.inr q)=.inl p := by
    cases cancel
    all_goals
      have same : p=q := Sum.inr.inj mate
      subst q
      rfl
  exact ⟨swapped,context.symm⟩

private theorem cancel_controls (cancel : IsCancellation s) :
    (s.active=.fan ∨s.active=.cro ∨s.active=.bra) ∧
    (s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra) := by
  cases cancel with
  | fan => exact ⟨Or.inl rfl,Or.inl rfl⟩
  | cro => exact ⟨Or.inr (Or.inl rfl),Or.inr (Or.inl rfl)⟩
  | bra => exact ⟨Or.inr (Or.inr rfl),Or.inr (Or.inr rfl)⟩

private theorem cancel_raw_single (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    (e : Endpoint cut) (a : Context) :
    CancellationRawPath site cancel [.inl e] a a ∧
    CancellationRawResidual site cancel principal [.inl e] [site.outsideEnd e] := by
  cases cancel
  all_goals exact ⟨.single e a,.single e⟩

private theorem cancel_raw_outside (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    {e f : Endpoint cut} {tail old} {a middle b : Context}
    (turn : LabelledTurn cut ((cut).wire e) f a middle)
    (path : CancellationRawPath site cancel (.inl f::tail) middle b)
    (residual : CancellationRawResidual site cancel principal (.inl f::tail) old) :
    CancellationRawPath site cancel (.inl e::.inl f::tail) a b ∧
    CancellationRawResidual site cancel principal (.inl e::.inl f::tail) (site.outsideEnd e::old) := by
  cases cancel
  all_goals exact ⟨.outside turn path,.outside residual⟩

private theorem cancel_raw_through (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    (entry : s.Frontier) {e : Endpoint cut} {tail old} {a b : Context}
    (arrival : (cut).wire e=.inr (.inl (.inr entry)))
    (start : (site.cancellation_canonical_fronts principal.edges entry++
      [site.outsideEnd (.inr (.inl (.inr (cancellationMate s entry))))]).head?=some (site.outsideEnd e))
    (path : CancellationRawPath site cancel
      (.inl (.inr (.inl (.inr (cancellationMate s entry))))::tail) a b)
    (residual : CancellationRawResidual site cancel principal
      (.inl (.inr (.inl (.inr (cancellationMate s entry))))::tail) old) :
    CancellationRawPath site cancel
      (.inl e::.inr (.inr (.inl entry))::.inl (.inr (.inl (.inr (cancellationMate s entry))))::tail) a b ∧
    CancellationRawResidual site cancel principal
      (.inl e::.inr (.inr (.inl entry))::.inl (.inr (.inl (.inr (cancellationMate s entry))))::tail)
      (site.cancellation_canonical_fronts principal.edges entry++old) := by
  cases cancel
  all_goals
    cases entry
    all_goals exact ⟨.through arrival path,.through start residual⟩

private theorem transparent_word {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    (g : Net signature N D U) (es : List (Endpoint g))
    (transparent : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) : controlWord g es=[] := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases es with
    | nil => rfl
    | cons f tail =>
      obtain ⟨w,d,_arrives,leaves⟩ := transparent e f (by simp)
      have rest := ih (by intro x y pair; exact transparent x y (List.mem_cons_of_mem _ pair))
      change departureWord g f++controlWord g (f::tail)=[]
      rw [rest,leaves]
      rfl

private theorem cancel_cross_word (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    (p : Aux s.active) (q : Aux s.passive) (tail : List (Endpoint site.net)) :
    controlWord site.net (principal.crossing site p q++tail)=
      true::false::controlWord site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::tail) := by
  obtain ⟨routeTail,routeEq⟩ := List.head?_eq_some_iff.mp principal.first
  have empty := transparent_word site.net principal.edges principal.transparent
  rw [routeEq] at empty
  change routeTail.flatMap (departureWord site.net)=[] at empty
  change ((principal.edges++[(.inl ⟨.inr (.inr ()),.inr q⟩ : Endpoint site.net)])++tail).flatMap (departureWord site.net)=_
  rw [List.flatMap_append,List.flatMap_append,routeEq,List.flatMap_cons,empty]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change (controlPortWord (.op s.active) (.inl ()) ++
      controlPortWord (.op s.passive) (.inr q)) ++ tail.flatMap (departureWord site.net) =
    true::false::tail.flatMap (departureWord site.net)
  cases cancel <;> rfl

private theorem cancel_backward_word (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    (p : Aux s.active) (q : Aux s.passive) (tail : List (Endpoint site.net)) :
    controlWord site.net (reverseEdges (principal.crossing site p q)++tail)=
      true::false::controlWord site.net ((.inl ⟨.inr (.inl ()),.inr p⟩)::tail) := by
  have first : (reverseEdges principal.edges).head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
  obtain ⟨routeTail,routeEq⟩ := List.head?_eq_some_iff.mp first
  have empty := transparent_word site.net (reverseEdges principal.edges)
    (transparent_reverse_turns principal.edges principal.transparent)
  rw [routeEq] at empty
  change routeTail.flatMap (departureWord site.net)=[] at empty
  rw [principal.reverse_crossing_edges site]
  change ((reverseEdges principal.edges++[(.inl ⟨.inr (.inl ()),.inr p⟩ : Endpoint site.net)])++tail).flatMap (departureWord site.net)=_
  rw [List.flatMap_append,List.flatMap_append,routeEq,List.flatMap_cons,empty]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change (controlPortWord (.op s.passive) (.inl ()) ++
      controlPortWord (.op s.active) (.inr p)) ++ tail.flatMap (departureWord site.net) =
    true::false::tail.flatMap (departureWord site.net)
  cases cancel <;> rfl

private theorem raw_wire_word (entry : s.Frontier) (e : Endpoint cut)
    (tail : List (PlugSegment cut s.right.net)) :
    actionRawControlWord site (.inl e::.inr (.inr (.inl entry))::
      .inl (.inr (.inl (.inr (cancellationMate s entry))))::tail)=
      actionRawControlWord site (.inl (.inr (.inl (.inr (cancellationMate s entry))))::tail) := rfl

private theorem physical_raw_word (raw : List (PlugSegment cut s.right.net)) :
    controlWord site.reduce (raw.map (plugEnd (cut).label s.right.net.label))=actionRawControlWord site raw := by
  cases raw with
  | nil => rfl
  | cons e tail =>
    change (tail.map (plugEnd (cut).label s.right.net.label)).flatMap (departureWord site.reduce)=
      tail.flatMap (Sum.elim (departureWord cut) (departureWord s.right.net))
    rw [List.flatMap_map]
    apply congrArg (fun f => tail.flatMap f)
    funext piece
    rcases piece with (⟨node,p⟩|((boundary|frontier)|⟨vertex,direction⟩))|
      (⟨node,p⟩|(frontier|⟨vertex,direction⟩)) <;> rfl

private theorem front_cross_shape (principal : SiteActionPrincipal site)
    (p : Aux s.active) (q : Aux s.passive) (tail : List (Endpoint site.net)) :
    site.cancellation_canonical_fronts principal.edges (.inl p)++
      (.inl ⟨.inr (.inr ()),.inr q⟩)::tail=principal.crossing site p q++tail := by
  rw [cancellation_fronts_literal]
  rw [←site.outsideEnd_wire]
  simp only [cancellationFrontRoute,SiteActionPrincipal.crossing,List.cons_append,
    List.append_assoc]
  rfl

private theorem front_backward_shape (principal : SiteActionPrincipal site)
    (p : Aux s.active) (q : Aux s.passive) (tail : List (Endpoint site.net)) :
    site.cancellation_canonical_fronts principal.edges (.inr q)++
      (.inl ⟨.inr (.inl ()),.inr p⟩)::tail=reverseEdges (principal.crossing site p q)++tail := by
  rw [cancellation_fronts_literal]
  rw [←site.outsideEnd_wire,principal.reverse_crossing_edges site p q]
  simp only [cancellationFrontRoute,List.cons_append,List.append_assoc]
  rfl

/-- Every original complete visit is really deleted. The actual labelled
crossing forces both its paired branch and the SAME context at its two ends.
No reference target, desired deletion relation or decreasing rank is assumed. -/
theorem WholeControlVisits.cancellation_word_contraction
    (cancel : IsCancellation s) {principal : SiteActionPrincipal site} {es n}
    (visits : WholeControlVisits site principal es n)
    {a b : Context} (labels : Labelling site.net es a b) :
    ∃ raw : List (PlugSegment cut s.right.net),
      CancellationRawPath site cancel raw a b ∧
      CancellationRawResidual site cancel principal raw es ∧
      ParallelControlErasures (actionRawControlWord site raw) (controlWord site.net es) n := by
  induction visits generalizing a b with
  | single e =>
    cases labels
    obtain ⟨path,residual⟩ := cancel_raw_single site cancel principal e a
    exact ⟨[.inl e],path,residual,.nil⟩
  | outside e f tail geometry rest ih =>
    cases labels with
    | @cons _ _ _ _ middle _ sourceTurn sourceRest =>
      have turn := reflect_retained_turn site geometry sourceTurn
      obtain ⟨raw,path,residual,deletions⟩ := ih sourceRest
      obtain ⟨actualFirst,rawHead⟩ := raw_path_head site cancel path
      have oldHead := raw_residual_head site cancel principal residual rawHead
      have same : actualFirst=f := outside_injective site (Option.some.inj oldHead).symm
      subst actualFirst
      obtain ⟨rawTail,rawEq⟩ := List.head?_eq_some_iff.mp rawHead
      rw [rawEq] at path residual deletions
      obtain ⟨wholePath,wholeResidual⟩ := cancel_raw_outside site cancel principal turn path residual
      refine ⟨.inl e::.inl f::rawTail,wholePath,wholeResidual,?_⟩
      have oldWord : controlWord site.net (site.outsideEnd e::site.outsideEnd f::tail)=
          departureWord cut f++controlWord site.net (site.outsideEnd f::tail) := by
        change departureWord site.net (site.outsideEnd f)++_=departureWord cut f++_
        rw [retained_word site geometry]
        rfl
      have newWord : actionRawControlWord site (.inl e::.inl f::rawTail)=
          departureWord cut f++actionRawControlWord site (.inl f::rawTail) := rfl
      rw [oldWord,newWord]
      exact .keep _ deletions
  | @cross p q tail n rest ih =>
    let exit : Endpoint site.net := .inl ⟨.inr (.inr ()),.inr q⟩
    let pre := site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::principal.edges
    have frontEq : principal.crossing site p q=pre++[exit] := rfl
    have overlap : Labelling site.net (pre++exit::tail) a b := by
      simpa only [frontEq,List.append_assoc,List.singleton_append] using labels
    obtain ⟨middle,frontLabels,suffixLabels⟩ := overlap.split_segment
    have crossingLabels : Labelling site.net (principal.crossing site p q) a middle := by
      simpa only [frontEq] using frontLabels
    obtain ⟨mate,context⟩ := crossing_cancel_facts site cancel principal p q crossingLabels
    subst middle
    obtain ⟨raw,path,residual,deletions⟩ := ih suffixLabels
    let exitCut : Endpoint cut := .inr (.inl (.inr (.inr q)))
    obtain ⟨actualFirst,rawHead⟩ := raw_path_head site cancel path
    have oldHead := raw_residual_head site cancel principal residual rawHead
    have same : actualFirst=exitCut := outside_injective site (Option.some.inj oldHead).symm
    subst actualFirst
    obtain ⟨rawTail,rawEq⟩ := List.head?_eq_some_iff.mp rawHead
    rw [rawEq] at path residual deletions
    let first : Endpoint cut := (cut).wire (.inr (.inl (.inr (.inl p))))
    have arrival : (cut).wire first=.inr (.inl (.inr (.inl p))) := (cut).wire.involutive _
    have start : (site.cancellation_canonical_fronts principal.edges (.inl p)++
        [site.outsideEnd (.inr (.inl (.inr (cancellationMate s (.inl p)))))]).head?=
        some (site.outsideEnd first) := by
      rw [cancellation_fronts_literal]
      rfl
    have pathMate : CancellationRawPath site cancel
        (.inl (.inr (.inl (.inr (cancellationMate s (.inl p)))))::rawTail) a b := by
      rw [mate]
      exact path
    have residualMate : CancellationRawResidual site cancel principal
        (.inl (.inr (.inl (.inr (cancellationMate s (.inl p)))))::rawTail) (exit::tail) := by
      rw [mate]
      exact residual
    obtain ⟨wholePath,wholeResidual⟩ := cancel_raw_through site cancel principal (.inl p)
      arrival start pathMate residualMate
    rw [front_cross_shape site principal p q tail] at wholeResidual
    refine ⟨.inl first::.inr (.inr (.inl (.inl p)))::
      .inl (.inr (.inl (.inr (cancellationMate s (.inl p)))))::rawTail,
      wholePath,wholeResidual,?_⟩
    rw [raw_wire_word,mate,cancel_cross_word site cancel principal p q tail]
    exact .erase deletions
  | @backward p q tail n rest ih =>
    let exit : Endpoint site.net := .inl ⟨.inr (.inl ()),.inr p⟩
    let pre := site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)::reverseEdges principal.edges
    have frontEq : reverseEdges (principal.crossing site p q)=pre++[exit] :=
      principal.reverse_crossing_edges site p q
    have overlap : Labelling site.net (pre++exit::tail) a b := by
      simpa only [frontEq,List.append_assoc,List.singleton_append] using labels
    obtain ⟨middle,frontLabels,suffixLabels⟩ := overlap.split_segment
    have crossingLabels : Labelling site.net (reverseEdges (principal.crossing site p q)) a middle := by
      simpa only [frontEq] using frontLabels
    obtain ⟨mate,context⟩ := backward_cancel_facts site cancel principal p q crossingLabels
    subst middle
    obtain ⟨raw,path,residual,deletions⟩ := ih suffixLabels
    let exitCut : Endpoint cut := .inr (.inl (.inr (.inl p)))
    obtain ⟨actualFirst,rawHead⟩ := raw_path_head site cancel path
    have oldHead := raw_residual_head site cancel principal residual rawHead
    have same : actualFirst=exitCut := outside_injective site (Option.some.inj oldHead).symm
    subst actualFirst
    obtain ⟨rawTail,rawEq⟩ := List.head?_eq_some_iff.mp rawHead
    rw [rawEq] at path residual deletions
    let first : Endpoint cut := (cut).wire (.inr (.inl (.inr (.inr q))))
    have arrival : (cut).wire first=.inr (.inl (.inr (.inr q))) := (cut).wire.involutive _
    have start : (site.cancellation_canonical_fronts principal.edges (.inr q)++
        [site.outsideEnd (.inr (.inl (.inr (cancellationMate s (.inr q)))))]).head?=
        some (site.outsideEnd first) := by
      rw [cancellation_fronts_literal]
      rfl
    have pathMate : CancellationRawPath site cancel
        (.inl (.inr (.inl (.inr (cancellationMate s (.inr q)))))::rawTail) a b := by
      rw [mate]
      exact path
    have residualMate : CancellationRawResidual site cancel principal
        (.inl (.inr (.inl (.inr (cancellationMate s (.inr q)))))::rawTail) (exit::tail) := by
      rw [mate]
      exact residual
    obtain ⟨wholePath,wholeResidual⟩ := cancel_raw_through site cancel principal (.inr q)
      arrival start pathMate residualMate
    rw [front_backward_shape site principal p q tail] at wholeResidual
    refine ⟨.inl first::.inr (.inr (.inl (.inr q)))::
      .inl (.inr (.inl (.inr (cancellationMate s (.inr q)))))::rawTail,
      wholePath,wholeResidual,?_⟩
    rw [raw_wire_word,mate,cancel_backward_word site cancel principal p q tail]
    exact .erase deletions

/-- The complete actual physical RHS, not a scalar fold, loses all counted
WR blocks and retains the same a/b labels and canonical source list. -/
theorem WholeControlVisits.cancellation_physical_word_transport
    (cancel : IsCancellation s) {principal : SiteActionPrincipal site} {es n}
    (visits : WholeControlVisits site principal es n)
    {a b : Context} (labels : Labelling site.net es a b) :
    ∃ target : List (Endpoint site.reduce),Labelling site.reduce target a b ∧
      CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges) target es ∧
      ParallelControlErasures (controlWord site.reduce target) (controlWord site.net es) n := by
  obtain ⟨raw,path,residual,deletions⟩ := visits.cancellation_word_contraction site cancel labels
  refine ⟨raw.map (plugEnd (cut).label s.right.net.label),raw_path_actual site cancel path,
    raw_residual_actual site cancel principal residual,?_⟩
  rw [physical_raw_word site raw]
  exact deletions

/-- SAME current/redex progress. The target connection is identified by the
actual canonical residual BEFORE transferring deletion/count to it. -/
theorem ActualRedexAccess.cancellation_control_count_progress
    (cancel : IsCancellation s) {directions : B → Bool} {depths : B → Int} {root : B}
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (inputs : RootInputs site.net root) (balance : IndexedLevelBalance site.net depths)
    (rootDepth : depths root=0) (oldT : Transparency site.net root)
    {current : LTerm} (closed : Closed current.erase) (matching : Matches site.net root current.erase)
    (redex : RedexOcc current.erase) (appStamp lamStamp : Lambda.Labelled.Label) (body arg : LTerm)
    (lookup : current.subterm redex.val=some (.app appStamp (.lam lamStamp body) arg))
    (source : ActualRedexAccess site.net root redex) {a b : Context}
    (sourceAssignment : Labelling site.net source.connection.edges a b)
    (selected : (.inl ⟨.inr (.inl ()),.inl ()⟩ : Endpoint site.net)∈source.connection.edges) :
    ∃ target : ActualRedexAccess site.reduce root redex,
      Labelling site.reduce target.connection.edges a b ∧
      ∃ n,0<n ∧ParallelControlErasures (controlWord site.reduce target.connection.edges)
        (controlWord site.net source.connection.edges) n ∧
      (controlWord site.reduce target.connection.edges).length<
        (controlWord site.net source.connection.edges).length := by
  obtain ⟨principal,_targetMatches,actualTransport⟩ := site.cancellation_selected_connection cancel flow root positive
    inputs balance rootDepth oldT closed matching
  obtain ⟨target,actualResidual,_unique⟩ :=
    actualTransport redex appStamp lamStamp body arg lookup source
  obtain ⟨activeControl,passiveControl⟩ := cancel_controls cancel
  obtain ⟨n,visits⟩ := source.whole_control_visits site activeControl passiveControl principal
  have nPositive := visits.positive_of_principal_occurs site selected
  obtain ⟨constructed,labels,residual,deletions⟩ :=
    visits.cancellation_physical_word_transport site cancel sourceAssignment
  have same : target.connection.edges=constructed :=
    CanonicalCancellationResidual.target_unique site cancel principal actualResidual residual
  have actualLabels : Labelling site.reduce target.connection.edges a b := by rw [same];exact labels
  have actualDeletions : ParallelControlErasures (controlWord site.reduce target.connection.edges)
      (controlWord site.net source.connection.edges) n := by rw [same];exact deletions
  exact ⟨target,actualLabels,n,nPositive,actualDeletions,actualDeletions.strict_of_positive nPositive⟩
end
end Lamping.AG

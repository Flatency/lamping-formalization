import Lamping.Lamping.UnaryCanonicalUniqueness
import Lamping.Lamping.ActionPrincipalInternal
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

theorem cut_turn_output_original {e f : Endpoint cut} {a b : Context}
    (turn : LabelledTurn cut e f a b) :
    (∃ node port,site.outsideEnd f=.inl ⟨.inl node,port⟩) ∨
      ∃ w d,site.outsideEnd f=.inr (.inr (.inl w,d)) := by
  cases turn with
  | node node p q rule => exact Or.inl ⟨node,q,rfl⟩
  | transparent w d a => exact Or.inr ⟨w,!d,rfl⟩

theorem cut_turn_output_not_selected {e f : Endpoint cut} {a b : Context}
    (turn : LabelledTurn cut e f a b) (node : Unit⊕Unit)
    (port : Port (site.net.label (.inr node)).sort) :
    site.outsideEnd f≠.inl ⟨.inr node,port⟩ := by
  rcases cut_turn_output_original site turn with ⟨n,p,same⟩|⟨w,d,same⟩
  · rw [same]; intro impossible; cases impossible
  · rw [same]; intro impossible; cases impossible
theorem canonical_local_second_selected {principal : SiteActionPrincipal site} {rhs old}
    (route : ActionCanonicalLocal site principal rhs old) :
    ∃ (first : Endpoint site.net) (node : Unit⊕Unit) (port : Port (site.net.label (.inr node)).sort) (rest : List (Endpoint site.net)),
      old=first::(.inl ⟨.inr node,port⟩)::rest := by
  have crossShape (p : Aux s.active) (q : Aux s.passive) :
      ∃ rest,principal.crossing site p q=site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::
        (.inl ⟨.inr (.inl ()),.inl ()⟩)::rest := by
    obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp principal.first
    rw [SiteActionPrincipal.crossing,split]
    exact ⟨tail++[.inl ⟨.inr (.inr ()),.inr q⟩],rfl⟩
  have backShape (p : Aux s.active) (q : Aux s.passive) :
      ∃ rest,reverseEdges (principal.crossing site p q)=site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)::
        (.inl ⟨.inr (.inr ()),.inl ()⟩)::rest := by
    have head : (reverseEdges principal.edges).head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
      simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
    obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp head
    rw [principal.reverse_crossing_edges site p q,split]
    exact ⟨tail++[.inl ⟨.inr (.inl ()),.inr p⟩],rfl⟩
  cases route with
  | fan inside => cases inside with
    | cross p q => obtain ⟨tail,shape⟩:=crossShape p q; exact ⟨_,.inl (),.inl (),tail,shape⟩
    | backward p q => obtain ⟨tail,shape⟩:=backShape p q; exact ⟨_,.inr (),.inl (),tail,shape⟩
    | passive branch p q => exact ⟨_,.inr (),.inr q,[],rfl⟩
  | cro inside => cases inside with
    | cross q => obtain ⟨tail,shape⟩:=crossShape () q; exact ⟨_,.inl (),.inl (),tail,shape⟩
    | backward q => obtain ⟨tail,shape⟩:=backShape () q; exact ⟨_,.inr (),.inl (),tail,shape⟩
    | passive p q => exact ⟨_,.inr (),.inr q,[],rfl⟩
  | bra inside => cases inside with
    | cross q => obtain ⟨tail,shape⟩:=crossShape () q; exact ⟨_,.inl (),.inl (),tail,shape⟩
    | backward q => obtain ⟨tail,shape⟩:=backShape () q; exact ⟨_,.inr (),.inl (),tail,shape⟩
    | passive p q => exact ⟨_,.inr (),.inr q,[],rfl⟩
theorem canonical_through_not_outside_turn
    {principal : SiteActionPrincipal site} {rhs : List (Endpoint s.right.net)} {front suffix tail : List (Endpoint site.net)}
    {entry next exit : Endpoint cut} {a b : Context}
    (turn : LabelledTurn cut ((cut).wire entry) next a b)
    (route : ActionCanonicalLocal site principal rhs (front++[site.outsideEnd exit]))
    (suffixHead : suffix.head?=some (site.outsideEnd exit)) :
    site.outsideEnd entry::site.outsideEnd next::tail≠front++suffix := by
  intro same
  obtain ⟨after,suffixEq⟩ := List.head?_eq_some_iff.mp suffixHead
  have joined : front++suffix=(front++[site.outsideEnd exit])++after := by
    rw [suffixEq,List.append_assoc]; rfl
  obtain ⟨first,node,port,rest,shape⟩ := canonical_local_second_selected site route
  rw [joined,shape,List.cons_append,List.cons_append] at same
  have second := (List.cons.inj (List.cons.inj same).2).1
  exact cut_turn_output_not_selected site turn node port second
section Unary
variable (single : Bij Unit (Aux s.active)) {k : Nat}
private theorem drop_cross (principal : SiteActionPrincipal site) (p : Aux s.active) (q : Aux s.passive) :
    (principal.crossing site p q).dropLast=
      site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::principal.edges := by
  change ((site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::principal.edges)++[_]).dropLast=_
  exact List.dropLast_concat
private theorem drop_back (principal : SiteActionPrincipal site) (p : Aux s.active) (q : Aux s.passive) :
    (reverseEdges (principal.crossing site p q)).dropLast=
      site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)::reverseEdges principal.edges := by
  rw [principal.reverse_crossing_edges site p q]
  change ((site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)::reverseEdges principal.edges)++[_]).dropLast=_
  exact List.dropLast_concat
private theorem last_cross (principal : SiteActionPrincipal site) (p : Aux s.active) (q : Aux s.passive) :
    (principal.crossing site p q).getLast?=some (.inl ⟨.inr (.inr ()),.inr q⟩) := by
  change ((site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::principal.edges)++[_]).getLast?=_
  rw [List.getLast?_append]; rfl
private theorem last_back (principal : SiteActionPrincipal site) (p : Aux s.active) (q : Aux s.passive) :
    (reverseEdges (principal.crossing site p q)).getLast?=some (.inl ⟨.inr (.inl ()),.inr p⟩) := by
  rw [principal.reverse_crossing_edges site p q]
  change ((site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)::reverseEdges principal.edges)++[_]).getLast?=_
  rw [List.getLast?_append]; rfl
theorem unary_front_split_unique {principal : SiteActionPrincipal site}
    {rhs otherRhs : List (Endpoint (unaryRightCore s.active s.passive single s.low k))}
    {old other front otherFront suffix otherSuffix : List (Endpoint site.net)} {ending otherEnding : Endpoint site.net}
    (left : UnaryCanonicalLocal site single principal rhs old)
    (right : UnaryCanonicalLocal site single principal otherRhs other)
    (leftSplit : old=front++[ending]) (rightSplit : other=otherFront++[otherEnding])
    (leftHead : suffix.head?=some ending) (rightHead : otherSuffix.head?=some otherEnding)
    (same : front++suffix=otherFront++otherSuffix) :
    front=otherFront ∧suffix=otherSuffix := by
  have wireEq (e f : Endpoint site.net) : site.net.wire e=site.net.wire f ↔e=f := by
    constructor
    · intro same
      have actual := congrArg site.net.wire.mate same
      simpa only [Pairing.involutive] using actual
    · exact congrArg site.net.wire.mate
  have reverseHead : (reverseEdges principal.edges).head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
  have frontEq : front=old.dropLast := by rw [leftSplit,List.dropLast_concat]
  have otherFrontEq : otherFront=other.dropLast := by rw [rightSplit,List.dropLast_concat]
  have oldLast : old.getLast?=some ending := by rw [leftSplit,List.getLast?_append]; rfl
  have otherLast : other.getLast?=some otherEnding := by rw [rightSplit,List.getLast?_append]; rfl
  clear leftSplit rightSplit
  subst front
  subst otherFront
  cases left <;> cases right <;>
    simp_all [drop_cross,drop_back,last_cross,last_back,PathSite.passiveCanonical]
  case backward.cross =>
    have impossible := same.1.trans oldLast.symm
    cases impossible
  case backward.passive =>
    have heads := congrArg List.head? same.2
    rw [List.head?_append,reverseHead,Option.some_or,rightHead] at heads
    have impossible := (Option.some.inj heads).trans otherLast.symm
    cases impossible
  case passive.backward =>
    have impossible := leftHead.trans oldLast.symm
    cases impossible
end Unary
section GenericLabels
variable {A R D F U Z : Type} [FiniteNames A] [FiniteNames R] [FiniteNames D]
  [FiniteNames F] [FiniteNames U] [FiniteNames Z]
variable {c : Net signature A (D⊕F) U} {r : Net signature R F Z}
theorem PlugLabelling.suffix_labels {pre tail : List (PlugSegment c r)} {a b : Context}
    (labels : PlugLabelling c r (pre++tail) a b) (nonempty : tail≠[]) :
    ∃ middle,PlugLabelling c r tail middle b := by
  induction pre generalizing a with
  | nil => exact ⟨a,labels⟩
  | cons e pre ih =>
    cases pre with
    | nil =>
      cases tail with
      | nil => exact False.elim (nonempty rfl)
      | cons f tail => cases labels with | cons turn rest => exact ⟨_,rest⟩
    | cons f pre => cases labels with | cons turn rest => exact ih rest

theorem PlugLabelling.left_step {e f : Endpoint c} {tail : List (PlugSegment c r)} {a b : Context}
    (labels : PlugLabelling c r (.inl e::.inl f::tail) a b) :
    ∃ middle,LabelledTurn c (c.wire e) f a middle ∧PlugLabelling c r (.inl f::tail) middle b := by
  cases labels with
  | cons turn rest =>
    change PlugTurn c r (.inl (c.wire e)) (.inl f) _ _ at turn
    rcases turn.left_cases c r with ⟨next,same,actual⟩|⟨entry,_wire,same,_contexts⟩
    · have targetEq : f=next := Sum.inl.inj same
      subst next
      exact ⟨_,actual,rest⟩
    · cases same
end GenericLabels

theorem ActionCanonicalLocal.unary_front_unique
    (unary : s.active≠.fan) {principal : SiteActionPrincipal site} {rhs otherRhs old other}
    {front otherFront suffix otherSuffix : List (Endpoint site.net)} {ending otherEnding : Endpoint site.net}
    (left : ActionCanonicalLocal site principal rhs old)
    (right : ActionCanonicalLocal site principal otherRhs other)
    (leftSplit : old=front++[ending]) (rightSplit : other=otherFront++[otherEnding])
    (leftHead : suffix.head?=some ending) (rightHead : otherSuffix.head?=some otherEnding)
    (same : front++suffix=otherFront++otherSuffix) :
    front=otherFront ∧suffix=otherSuffix := by
  cases left with
  | fan route => exact False.elim (unary rfl)
  | cro route => cases right with | cro other =>
      exact unary_front_split_unique _ (Bij.refl _) route other leftSplit rightSplit leftHead rightHead same
  | bra route => cases right with | bra other =>
      exact unary_front_split_unique _ (Bij.refl _) route other leftSplit rightSplit leftHead rightHead same

theorem ActionCanonicalLocal.unary_target_unique
    (unary : s.active≠.fan) {principal : SiteActionPrincipal site} {rhs otherRhs old other}
    (left : ActionCanonicalLocal site principal rhs old)
    (right : ActionCanonicalLocal site principal otherRhs other) (same : old=other) : rhs=otherRhs := by
  cases left with
  | fan route => exact False.elim (unary rfl)
  | cro route => cases right with | cro other => exact route.fixed_target_unique _ (Bij.refl _) other same
  | bra route => cases right with | bra other => exact route.fixed_target_unique _ (Bij.refl _) other same

theorem canonical_front_nonempty {principal : SiteActionPrincipal site} {rhs front ending}
    (route : ActionCanonicalLocal site principal rhs (front++[ending])) : front≠[] := by
  obtain ⟨first,node,port,rest,shape⟩ := canonical_local_second_selected site route
  intro empty
  rw [empty] at shape
  simp only [List.nil_append] at shape
  have lengths := congrArg List.length shape
  simp only [List.length_cons,List.length_nil] at lengths
  omega
private theorem outside_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have mapped := congrArg split same
  change split (split.invFun (.inl e))=split (split.invFun (.inl f)) at mapped
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

private theorem through_length_ge_two {principal : SiteActionPrincipal site} {rhs front ending suffix}
    (route : ActionCanonicalLocal site principal rhs (front++[ending]))
    (head : suffix.head?=some ending) : 2≤(front++suffix).length := by
  have frontNonempty := canonical_front_nonempty site route
  have suffixNonempty : suffix≠[] := by intro empty; rw [empty] at head; cases head
  have positiveFront := List.length_pos_iff.mpr frontNonempty
  have positiveSuffix := List.length_pos_iff.mpr suffixNonempty
  rw [List.length_append]
  omega

/-- Actual labels distinguish an ordinary outside step from a selected local block.
For unary rules, same canonical old wholes therefore have the same literal RHS.
The two assignments may differ; no injectivity of the bare block relation is asserted. -/
theorem ActionCanonicalBlocks.unary_target_unique_of_labels
    (unary : s.active≠.fan) {principal : SiteActionPrincipal site}
    {raw otherRaw : List (PlugSegment cut s.right.net)} {old otherOld : List (Endpoint site.net)}
    (left : ActionCanonicalBlocks site principal raw old)
    (right : ActionCanonicalBlocks site principal otherRaw otherOld)
    {a b c d : Context} (labels : PlugLabelling cut s.right.net raw a b)
    (otherLabels : PlugLabelling cut s.right.net otherRaw c d) (same : old=otherOld) : raw=otherRaw := by
  induction left generalizing otherRaw otherOld a b c d with
  | single e =>
    cases right with
    | single f =>
      have first := outside_injective site (List.cons.inj same).1
      subst f
      rfl
    | @outside f next tail other rest =>
      obtain ⟨after,shape⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
      rw [shape] at same
      have lengths := congrArg List.length same
      simp only [List.length_cons,List.length_nil] at lengths
      omega
    | through inside front route start rest =>
      have bound := through_length_ge_two site route (rest.head site rfl)
      rw [←same] at bound
      simp only [List.length_cons,List.length_nil] at bound
      omega
  | @outside e f tail old rest ih =>
    obtain ⟨middle,actual,remaining⟩ := labels.left_step
    cases right with
    | single h =>
      obtain ⟨after,shape⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
      rw [shape] at same
      have lengths := congrArg List.length same
      simp only [List.length_cons,List.length_nil] at lengths
      omega
    | @outside h next post other otherRest =>
      obtain ⟨nextMiddle,_nextTurn,nextLabels⟩ := otherLabels.left_step
      have splits := List.cons.inj same
      have first := outside_injective site splits.1
      subst h
      have tails := ih otherRest remaining nextLabels splits.2
      exact congrArg (_::·) tails
    | through inside front route start otherRest =>
      obtain ⟨after,shape⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
      rw [shape] at same
      exact False.elim (canonical_through_not_outside_turn site actual route (otherRest.head site rfl) same)
  | @through e exit tail old inside front route start rest ih =>
    have rawNonempty : (.inl (.inr (.inl (.inr exit)))::tail : List (PlugSegment cut s.right.net))≠[] := by simp
    obtain ⟨middle,remaining⟩ := labels.suffix_labels (pre:=.inl e::inside.map Sum.inr) rawNonempty
    cases right with
    | single f =>
      have bound := through_length_ge_two site route (rest.head site rfl)
      rw [same] at bound
      simp only [List.length_cons,List.length_nil] at bound
      omega
    | @outside f next post other otherRest =>
      obtain ⟨nextMiddle,actual,_nextLabels⟩ := otherLabels.left_step
      obtain ⟨after,shape⟩ := List.head?_eq_some_iff.mp (otherRest.head site rfl)
      rw [shape] at same
      exact False.elim (canonical_through_not_outside_turn site actual route (rest.head site rfl) same.symm)
    | @through f otherExit post other otherInside otherFront otherRoute otherStart otherRest =>
      have leftHead := rest.head site rfl
      have rightHead := otherRest.head site rfl
      obtain ⟨frontEq,tailEq⟩ := route.unary_front_unique site unary otherRoute rfl rfl leftHead rightHead same
      have endings : site.outsideEnd (.inr (.inl (.inr exit)))=
          site.outsideEnd (.inr (.inl (.inr otherExit))) := by
        exact Option.some.inj (leftHead.symm.trans ((congrArg List.head? tailEq).trans rightHead))
      have localEq : front++[site.outsideEnd (.inr (.inl (.inr exit)))]=
          otherFront++[site.outsideEnd (.inr (.inl (.inr otherExit)))] := by rw [frontEq,endings]
      have insideEq := route.unary_target_unique site unary otherRoute localEq
      have otherNonempty : (.inl (.inr (.inl (.inr otherExit)))::post : List (PlugSegment cut s.right.net))≠[] := by simp
      obtain ⟨nextMiddle,nextLabels⟩ := otherLabels.suffix_labels (pre:=.inl f::otherInside.map Sum.inr) otherNonempty
      have tails := ih otherRest remaining nextLabels tailEq
      have first : e=f := outside_injective site (Option.some.inj
        ((ActionCanonicalBlocks.head site (.through inside front route start rest) rfl).symm.trans
          ((congrArg List.head? same).trans (ActionCanonicalBlocks.head site
            (.through otherInside otherFront otherRoute otherStart otherRest) rfl))))
      subst f
      rw [insideEq]
      exact congrArg (_::·) (congrArg (List.append _) tails)
end
end Lamping.AG
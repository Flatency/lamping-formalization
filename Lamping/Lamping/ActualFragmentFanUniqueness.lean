import Lamping.Lamping.ActionEmptyWordPassages
import Lamping.Lamping.UnaryCanonicalComparison
import Lamping.Lamping.CanonicalChildDeparture
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {f : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction f i j lt) V) site.closed
local notation "rhs" => fanRight f i j
private def NoPassive (old : List (Endpoint site.net)) : Prop :=
  ∀ (p q : Aux f) (pre post : List (Endpoint site.net)),
    old≠pre++site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::(.inl ⟨.inr (.inr ()),.inr q⟩)::post
private theorem NoPassive.suffix {pre old : List (Endpoint site.net)}
    (safe : NoPassive site (pre++old)) : NoPassive site old := by
  intro p q before after same
  exact safe p q (pre++before) after (by rw [same];simp only [List.append_assoc])
private theorem crossing_head (principal : SiteActionPrincipal site) (p : Aux .fan) (q : Aux f) :
    (principal.crossing site p q).head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)) := rfl
private theorem crossing_last (principal : SiteActionPrincipal site) (p : Aux .fan) (q : Aux f) :
    (principal.crossing site p q).getLast?=some (.inl ⟨.inr (.inr ()),.inr q⟩) := by
  change (((site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩))::principal.edges)++[(.inl ⟨.inr (.inr ()),.inr q⟩ : Endpoint site.net)]).getLast?=_
  rw [List.getLast?_append];rfl
private theorem backward_head (principal : SiteActionPrincipal site) (p : Aux .fan) (q : Aux f) :
    (reverseEdges (principal.crossing site p q)).head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) := by
  rw [principal.reverse_crossing_edges site p q];rfl
private theorem crossing_injective {principal : SiteActionPrincipal site} {p r : Aux .fan} {q s : Aux f}
    (same : principal.crossing site p q=principal.crossing site r s) : p=r ∧q=s := by
  have heads := congrArg List.head? same
  rw [crossing_head,crossing_head] at heads
  have ports := congrArg site.net.wire (Option.some.inj heads)
  simp only [Pairing.involutive] at ports
  have pEq : p=r := by cases ports;rfl
  have lasts := congrArg List.getLast? same
  rw [crossing_last,crossing_last] at lasts
  have qEq : q=s := by cases Option.some.inj lasts;rfl
  exact ⟨pEq,qEq⟩
private theorem crossing_not_backward (principal : SiteActionPrincipal site) (p r : Aux .fan) (q s : Aux f) :
    principal.crossing site p q≠reverseEdges (principal.crossing site r s) := by
  intro same
  have heads := congrArg List.head? same
  rw [crossing_head,backward_head] at heads
  have ports := congrArg site.net.wire (Option.some.inj heads)
  simp only [Pairing.involutive] at ports
  cases ports
private theorem local_target_unique {principal : SiteActionPrincipal site} {raw otherRaw old otherOld}
    (left : FanCanonicalLocal site principal raw old)
    (right : FanCanonicalLocal site principal otherRaw otherOld)
    (same : old=otherOld) (safe : ∀p q,old≠site.passiveCanonical p q) : raw=otherRaw := by
  cases left with
  | cross p q =>
    cases right with
    | cross r s => obtain ⟨rfl,rfl⟩ := crossing_injective site same;rfl
    | backward r s => exact False.elim (crossing_not_backward site principal p r q s same)
    | passive branch r s => exact False.elim (safe r s same)
  | backward p q =>
    cases right with
    | cross r s => exact False.elim (crossing_not_backward site principal r p s q same.symm)
    | backward r s =>
      have forward := congrArg reverseEdges same
      simp only [reverseEdges_involutive] at forward
      obtain ⟨rfl,rfl⟩ := crossing_injective site forward;rfl
    | passive branch r s => exact False.elim (safe r s same)
  | passive branch p q => exact False.elim (safe p q rfl)
private theorem NoPassive.front {front suffix : List (Endpoint site.net)} {ending : Endpoint site.net}
    (safe : NoPassive site (front++suffix)) (head : suffix.head?=some ending) :
    ∀p q,(front++[ending])≠site.passiveCanonical p q := by
  intro p q equal
  obtain ⟨tail,suffixEq⟩ := List.head?_eq_some_iff.mp head
  apply safe p q [] tail
  rw [suffixEq]
  simpa only [List.nil_append,List.append_assoc,List.singleton_append] using
    congrArg (fun xs=>xs++tail) equal
private theorem local_front_length {principal : SiteActionPrincipal site} {raw old front suffix ending}
    (route : FanCanonicalLocal site principal raw old)
    (split : old=front++[ending]) (head : suffix.head?=some ending)
    (safe : NoPassive site (front++suffix)) : front.length=principal.edges.length+1 := by
  have nonpassive (p q : Aux f) : old≠site.passiveCanonical p q := by
    rw [split];exact safe.front site head p q
  cases route with
  | cross p q =>
    have lengths := congrArg List.length split
    simp only [SiteActionPrincipal.crossing,List.length_append,List.length_cons] at lengths
    omega
  | backward p q =>
    have lengths := congrArg List.length split
    simp only [reverseEdges,List.length_map,List.length_reverse,SiteActionPrincipal.crossing,List.length_append,List.length_cons] at lengths
    omega
  | passive branch p q => exact False.elim (nonpassive p q rfl)

private theorem action_front_length {principal : SiteActionPrincipal site} {raw old front suffix ending}
    (route : ActionCanonicalLocal site principal raw old)
    (split : old=front++[ending]) (head : suffix.head?=some ending)
    (safe : NoPassive site (front++suffix)) : front.length=principal.edges.length+1 := by
  cases route with
  | fan route => exact local_front_length site route split head safe
private theorem action_target_unique {principal : SiteActionPrincipal site} {raw otherRaw old otherOld}
    (left : ActionCanonicalLocal site principal raw old)
    (right : ActionCanonicalLocal site principal otherRaw otherOld)
    (same : old=otherOld) (safe : ∀p q,old≠site.passiveCanonical p q) : raw=otherRaw := by
  cases left with
  | fan left => cases right with
    | fan right => exact local_target_unique site left right same safe
private theorem outside_injective : Function.Injective site.outsideEnd := by
  intro e h same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition (Schema.fanAction f i j lt) V)
  have mapped := congrArg split same
  change split (split.invFun (.inl e))=split (split.invFun (.inl h)) at mapped
  simpa only [split.right_inv,Sum.inl.injEq] using mapped
private theorem through_length_ge_two {principal : SiteActionPrincipal site} {raw front ending suffix}
    (route : ActionCanonicalLocal site principal raw (front++[ending]))
    (head : suffix.head?=some ending) : 2≤(front++suffix).length := by
  have frontNonempty := canonical_front_nonempty site route
  have suffixNonempty : suffix≠[] := by intro empty; rw [empty] at head; cases head
  have positiveFront := List.length_pos_iff.mpr frontNonempty
  have positiveSuffix := List.length_pos_iff.mpr suffixNonempty
  rw [List.length_append]
  omega
/-- Private structural induction. Its local exclusion is derived by the public
actual-fragment wrapper, rather than supplied as a desired branch profile. -/
private theorem blocks_unique {principal : SiteActionPrincipal site}
    {raw otherRaw : List (PlugSegment cut rhs)} {old otherOld : List (Endpoint site.net)}
    (left : ActionCanonicalBlocks site principal raw old)
    (right : ActionCanonicalBlocks site principal otherRaw otherOld)
    {a b c d : Context} (labels : PlugLabelling cut rhs raw a b)
    (otherLabels : PlugLabelling cut rhs otherRaw c d)
    (same : old=otherOld) (safe : NoPassive site old) : raw=otherRaw := by
  induction left generalizing otherRaw otherOld a b c d with
  | single e =>
    cases right with
    | single f =>
      have first := outside_injective site (List.cons.inj same).1
      subst f;rfl
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
      have safeTail : NoPassive site old := by
        apply NoPassive.suffix site (pre:=[site.outsideEnd e]);exact safe
      have tails := ih otherRest remaining nextLabels splits.2 safeTail
      exact congrArg (_::·) tails
    | through inside front route start otherRest =>
      obtain ⟨after,shape⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
      rw [shape] at same
      exact False.elim (canonical_through_not_outside_turn site actual route (otherRest.head site rfl) same)
  | @through e exit tail old inside front route start rest ih =>
    have rawNonempty : (.inl (.inr (.inl (.inr exit)))::tail : List (PlugSegment cut rhs))≠[] := by simp
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
      have leftLength := action_front_length site route rfl leftHead safe
      have rightSafe : NoPassive site (otherFront++other) := same ▸ safe
      have rightLength := action_front_length site otherRoute rfl rightHead rightSafe
      have frontEq := List.append_inj_left same (leftLength.trans rightLength.symm)
      have tailEq : old=other := by rw [frontEq] at same;exact List.append_cancel_left same
      have endings : site.outsideEnd (.inr (.inl (.inr exit)))=
          site.outsideEnd (.inr (.inl (.inr otherExit))) :=
        Option.some.inj (leftHead.symm.trans ((congrArg List.head? tailEq).trans rightHead))
      have localEq : front++[site.outsideEnd (.inr (.inl (.inr exit)))]=
          otherFront++[site.outsideEnd (.inr (.inl (.inr otherExit)))] := by rw [frontEq,endings]
      have insideEq := action_target_unique site route otherRoute localEq (safe.front site leftHead)
      have otherNonempty : (.inl (.inr (.inl (.inr otherExit)))::post : List (PlugSegment cut rhs))≠[] := by simp
      obtain ⟨nextMiddle,nextLabels⟩ := otherLabels.suffix_labels (pre:=.inl f::otherInside.map Sum.inr) otherNonempty
      have tails := ih otherRest remaining nextLabels tailEq (safe.suffix site)
      have first : e=f := outside_injective site (Option.some.inj
        ((ActionCanonicalBlocks.head site (.through inside front route start rest) rfl).symm.trans
          ((congrArg List.head? same).trans (ActionCanonicalBlocks.head site
            (.through otherInside otherFront otherRoute otherStart otherRest) rfl))))
      subst f
      rw [insideEq]
      exact congrArg (_::·) (congrArg (List.append _) tails)
/-- Canonical fan raw uniqueness on a contiguous part of THIS actual source
fragment. Both finite RHS labelings are real, but their assignments may differ.
No Aux, representation invariant, branch profile or common input is assumed. -/
theorem SourceEdgeFragment.fan_target_unique_of_contiguous_source
    {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    {principal : SiteActionPrincipal site} {raw otherRaw : List (PlugSegment cut rhs)}
    {old otherOld pre post : List (Endpoint site.net)}
    (left : ActionCanonicalBlocks site principal raw old)
    (right : ActionCanonicalBlocks site principal otherRaw otherOld)
    {a b c d : Context} (labels : PlugLabelling cut rhs raw a b)
    (otherLabels : PlugLabelling cut rhs otherRaw c d)
    (same : old=otherOld) (contiguous : fragment.segments=pre++old++post) : raw=otherRaw := by
  have safe : NoPassive site old := by
    intro p q before after equal
    apply fragment.no_complete_passive site p q (pre++before) (after++post)
    rw [contiguous,equal]
    simp only [List.append_assoc,List.cons_append]
  exact blocks_unique site left right labels otherLabels same safe
/-- A single added pivot can only create a passive pair at the boundary.
A real kept-parent fragment head rules that out; tail pairs use the existing
actual-fragment exclusion. No claim that the augmented word is a subword. -/
private theorem SourceEdgeFragment.augmented_kept_no_passive
    {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    (parentNode : K) (departure : Port (kept parentNode).sort)
    (head : fragment.segments.head?=some (.inl ⟨.inl parentNode,departure⟩))
    (pivot : Endpoint site.net) : NoPassive site (pivot::fragment.segments) := by
  intro p q before after equal
  cases before with
  | nil =>
    have tail := (List.cons.inj equal).2
    have heads := congrArg List.head? tail
    rw [head] at heads
    cases Option.some.inj heads
  | cons e before =>
    have tail := (List.cons.inj equal).2
    exact fragment.no_complete_passive site p q before after tail
/-- The augmented OLD word is not asserted to lie inside the fragment.
The actual parent prefix pins its pivot, and the kept physical parent pins
its first departure. Both facts are obtained from the SAME supplied access. -/
theorem SourceEdgeFragment.fan_target_unique_of_kept_parent_fragment
    {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    (matching : Matches site.net root current.erase)
    {parentTerm : LTerm} {step : Step} (role : SourceDeparture parentTerm step edge.fromPort)
    (parent : RootAccess site.net root)
    (word : position=accessWord site.net parent.val++[step])
    (parentNode : K) (parentPort : Port (kept parentNode).sort)
    (finish : parent.val.getLast?=some (site.net.wire (.inl ⟨.inl parentNode,parentPort⟩)))
    (pivot : Endpoint cut) (parentAtPivot : parent.val.getLast?=some (site.outsideEnd pivot))
    {principal : SiteActionPrincipal site} {raw otherRaw : List (PlugSegment cut rhs)}
    (left : ActionCanonicalBlocks site principal raw (site.outsideEnd pivot::fragment.segments))
    (right : ActionCanonicalBlocks site principal otherRaw (site.outsideEnd pivot::fragment.segments))
    {a b c d : Context} (labels : PlugLabelling cut rhs raw a b)
    (otherLabels : PlugLabelling cut rhs otherRaw c d) :
    site.outsideEnd pivot=site.net.wire (.inl ⟨.inl parentNode,parentPort⟩) ∧raw=otherRaw := by
  have actualPivot := Option.some.inj (parentAtPivot.symm.trans finish)
  obtain ⟨departure,head⟩ := fragment.head_node_of_parent matching role parent word
    (.inl parentNode) parentPort finish
  have safe := fragment.augmented_kept_no_passive site parentNode departure head (site.outsideEnd pivot)
  exact ⟨actualPivot,blocks_unique site left right labels otherLabels rfl safe⟩
/-- Reverse passive routes are already covered by the same p/q-quantified
source-fragment exclusion, rather than a new orientation assumption. -/
theorem passive_reverse_swaps (p q : Aux f) :
    reverseEdges (site.passiveCanonical p q)=site.passiveCanonical q p := by
  simp [PathSite.passiveCanonical,reverseEdges,Pairing.involutive]
end
end Lamping.AG


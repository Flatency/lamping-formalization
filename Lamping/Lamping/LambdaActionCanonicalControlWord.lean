import Lamping.Lamping.PhysicalControlWordTools
import Lamping.Lamping.UnaryCanonicalComparison
import Lamping.Lamping.ActionSourceCanonicalBlocks
import Lamping.Lamping.ActionRawOutsideCut

namespace Lamping.AG
open Graph Lambda Lambda.Labelled ExposureScheduling

private theorem control_principal_word (op : Op) (control : op=.fan ∨op=.cro ∨op=.bra) :
    controlPortWord (.op op) (Sum.inl ())=[true] := by
  rcases control with rfl|rfl|rfl <;> rfl
private theorem control_aux_word (op : Op) (control : op=.fan ∨op=.cro ∨op=.bra) (p : Aux op) :
    controlPortWord (.op op) (Sum.inr p)=[false] := by
  rcases control with rfl|rfl|rfl <;> rfl
private theorem lambda_principal_word (op : Op) (same : op=.lam) :
    controlPortWord (.op op) (Sum.inl ())=[] := by subst op;rfl
private theorem lambda_aux_word (op : Op) (same : op=.lam) (p : Aux op) :
    controlPortWord (.op op) (Sum.inr p)=[] := by subst op;rfl
private theorem lambda_no_aux_aux (op : Op) (same : op=.lam) (index : Nat)
    (p q : Aux op) {a b : Context}
    (turn : Traversal index (.op op) (Sum.inr p) (Sum.inr q) a b) : False := by
  subst op
  exact turn.aux_aux

private theorem word_overlap {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (before : List (Endpoint g)) (pivot : Endpoint g) (after : List (Endpoint g)) :
    controlWord g (before++pivot::after)=controlWord g (before++[pivot])++controlWord g (pivot::after) := by
  cases before with
  | nil => rfl
  | cons first before =>
    change (before++pivot::after).flatMap (endpointControlWord g)=
      (before++[pivot]).flatMap (endpointControlWord g)++after.flatMap (endpointControlWord g)
    rw [List.flatMap_append,List.flatMap_append,List.flatMap_cons,List.flatMap_singleton]
    exact (List.append_assoc _ _ _).symm

section Principal
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
private theorem principal_tokens (principal : SiteActionPrincipal site)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) :
    principal.edges.flatMap (endpointControlWord site.net)=[true] := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp principal.first
  have empty := transparent_control_word site.net principal.edges principal.transparent
  rw [split] at empty ⊢
  change tail.flatMap (endpointControlWord site.net)=[] at empty
  change controlPortWord (.op s.active) (Sum.inl ())++tail.flatMap (endpointControlWord site.net)=[true]
  rw [control_principal_word s.active control]
  exact congrArg (fun xs : List Bool => [true]++xs) empty
private theorem reverse_principal_tokens (principal : SiteActionPrincipal site) (passive : s.passive=.lam) :
    (reverseEdges principal.edges).flatMap (endpointControlWord site.net)=[] := by
  have head : (reverseEdges principal.edges).head?=some (Sum.inl ⟨Sum.inr (Sum.inr ()),Sum.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp head
  have empty := transparent_control_word site.net (reverseEdges principal.edges)
    (transparent_reverse_turns principal.edges principal.transparent)
  rw [split] at empty ⊢
  change tail.flatMap (endpointControlWord site.net)=[] at empty
  change controlPortWord (.op s.passive) (Sum.inl ())++tail.flatMap (endpointControlWord site.net)=[]
  rw [lambda_principal_word s.passive passive]
  exact empty
private theorem source_cross_word (principal : SiteActionPrincipal site)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (passive : s.passive=.lam)
    (p : Aux s.active) (q : Aux s.passive) :
    controlWord site.net (principal.crossing site p q)=[true] := by
  change (principal.edges++[(Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inr q)) : Endpoint site.net)]).flatMap (endpointControlWord site.net)=[true]
  rw [List.flatMap_append,principal_tokens site principal control,List.flatMap_singleton]
  change [true]++controlPortWord (.op s.passive) (Sum.inr q)=[true]
  exact congrArg (fun xs : List Bool => [true]++xs) (lambda_aux_word s.passive passive q)
private theorem source_back_word (principal : SiteActionPrincipal site)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (passive : s.passive=.lam)
    (p : Aux s.active) (q : Aux s.passive) :
    controlWord site.net (reverseEdges (principal.crossing site p q))=[false] := by
  rw [principal.reverse_crossing_edges site]
  change (reverseEdges principal.edges++[(Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr p)) : Endpoint site.net)]).flatMap
    (endpointControlWord site.net)=[false]
  rw [List.flatMap_append,reverse_principal_tokens site principal passive,List.flatMap_singleton]
  change controlPortWord (.op s.active) (Sum.inr p)=[false]
  exact control_aux_word s.active control p
private theorem passive_impossible (passive : s.passive=.lam) (p q : Aux s.passive) {a b : Context}
    (labels : Labelling site.net (site.passiveCanonical p q) a b) : False := by
  cases labels with
  | cons turn finish =>
    rw [Pairing.involutive] at turn
    cases finish
    cases turn with
    | node node incoming outgoing rule => exact lambda_no_aux_aux s.passive passive s.high p q rule
end Principal

private theorem fan_rhs_cross (high : Op) (same : high=.lam) (i j : Nat) (branch : Bool) (q : Aux high) :
    controlWord (fanRight high i j) (fanCrossEdges branch q)=[true] := by subst high;rfl
private theorem fan_rhs_back (high : Op) (same : high=.lam) (i j : Nat) (branch : Bool) (q : Aux high) :
    controlWord (fanRight high i j) (reverseEdges (fanCrossEdges branch q))=[false] := by subst high;rfl
private theorem unary_rhs_cross (low high : Op) (single : Bij Unit (Aux low)) (i k : Nat)
    (control : low=.fan ∨low=.cro ∨low=.bra) (same : high=.lam) (q : Aux high) :
    controlWord (unaryRightCore low high single i k)
      [Sum.inr (Sum.inl (Sum.inl ())),Sum.inl ⟨Sum.inl (),Sum.inr q⟩,Sum.inl ⟨Sum.inr q,Sum.inl ()⟩]=[true] := by
  subst high
  rcases control with rfl|rfl|rfl <;> rfl
private theorem unary_rhs_back (low high : Op) (single : Bij Unit (Aux low)) (i k : Nat)
    (control : low=.fan ∨low=.cro ∨low=.bra) (same : high=.lam) (q : Aux high) :
    controlWord (unaryRightCore low high single i k)
      (reverseEdges [Sum.inr (Sum.inl (Sum.inl ())),Sum.inl ⟨Sum.inl (),Sum.inr q⟩,
        Sum.inl ⟨Sum.inr q,Sum.inl ()⟩])=[false] := by
  subst high
  rcases control with rfl|rfl|rfl <;> rfl

section Unary
variable {s : Schema} {k : Nat} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
variable (single : Bij Unit (Aux s.active))
local notation "rhs" => unaryRightCore s.active s.passive single s.low k
private theorem unary_word (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (passive : s.passive=.lam)
    {principal : SiteActionPrincipal site} {inside : List (Endpoint rhs)} {old : List (Endpoint site.net)}
    (relation : UnaryCanonicalLocal (s:=s) (k:=k) site single principal inside old)
    {a b : Context} (labels : Labelling site.net old a b) :
    controlWord rhs inside=controlWord site.net old := by
  refine UnaryCanonicalLocal.rec (s:=s) (k:=k) (site:=site) (single:=single) (principal:=principal)
    (motive:=fun inside old _ => ∀ {a b : Context},Labelling site.net old a b →
      controlWord rhs inside=controlWord site.net old) ?_ ?_ ?_ relation labels
  · intro q a b _labels
    unfold unaryCrossEdges
    rw [unary_rhs_cross s.active s.passive single s.low k control passive q]
    exact (source_cross_word site principal control passive (single ()) q).symm
  · intro q a b _labels
    unfold unaryCrossEdges
    rw [unary_rhs_back s.active s.passive single s.low k control passive q]
    exact (source_back_word site principal control passive (single ()) q).symm
  · intro p q a b labels
    exact False.elim (passive_impossible site passive p q labels)
private theorem unary_head {principal : SiteActionPrincipal site} {inside : List (Endpoint rhs)} {old}
    (relation : UnaryCanonicalLocal (s:=s) (k:=k) site single principal inside old) :
    ∃ entry : Unit⊕Aux s.passive,inside.head?=some (Sum.inr (Sum.inl entry)) := by
  refine UnaryCanonicalLocal.rec (s:=s) (k:=k) (site:=site) (single:=single) (principal:=principal)
    (motive:=fun inside _ _ => ∃ entry : Unit⊕Aux s.passive,inside.head?=some (Sum.inr (Sum.inl entry)))
    ?_ ?_ ?_ relation
  · intro q;exact ⟨Sum.inl (),rfl⟩
  · intro q;exact ⟨Sum.inr q,rfl⟩
  · intro p q;exact ⟨Sum.inr p,rfl⟩
end Unary

section Fan
variable {f : Op} {i j : Nat} {lt : i<j} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature}
variable (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))
private theorem fan_word (passive : f=.lam) {principal : SiteActionPrincipal site}
    {inside : List (Endpoint (fanRight f i j))} {old : List (Endpoint site.net)}
    (relation : FanCanonicalLocal site principal inside old) {a b : Context}
    (labels : Labelling site.net old a b) :
    controlWord (fanRight f i j) inside=controlWord site.net old := by
  refine FanCanonicalLocal.rec (f:=f) (i:=i) (j:=j) (lt:=lt) (site:=site) (principal:=principal)
    (motive:=fun inside old _ => ∀ {a b : Context},Labelling site.net old a b →
      controlWord (fanRight f i j) inside=controlWord site.net old) ?_ ?_ ?_ relation labels
  · intro branch q a b _labels
    rw [fan_rhs_cross f passive i j branch q]
    exact (source_cross_word site principal (Or.inl rfl) passive branch q).symm
  · intro branch q a b _labels
    rw [fan_rhs_back f passive i j branch q]
    exact (source_back_word site principal (Or.inl rfl) passive branch q).symm
  · intro _branch p q a b labels
    exact False.elim (passive_impossible site passive p q labels)
private theorem fan_head {principal : SiteActionPrincipal site} {inside : List (Endpoint (fanRight f i j))} {old}
    (relation : FanCanonicalLocal site principal inside old) :
    ∃ entry : Bool⊕Aux f,inside.head?=some (Sum.inr (Sum.inl entry)) := by
  refine FanCanonicalLocal.rec (f:=f) (i:=i) (j:=j) (lt:=lt) (site:=site) (principal:=principal)
    (motive:=fun inside _ _ => ∃ entry : Bool⊕Aux f,inside.head?=some (Sum.inr (Sum.inl entry)))
    ?_ ?_ ?_ relation
  · intro branch q;exact ⟨Sum.inl branch,rfl⟩
  · intro branch q;exact ⟨Sum.inr q,rfl⟩
  · intro branch p q;exact ⟨Sum.inr p,rfl⟩
end Fan

section Whole
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
private theorem local_word (passive : s.passive=.lam) {principal : SiteActionPrincipal site} {inside old}
    (relation : ActionCanonicalLocal site principal inside old) {a b : Context}
    (labels : Labelling site.net old a b) : controlWord s.right.net inside=controlWord site.net old := by
  cases relation with
  | fan relation => exact fan_word _ passive relation labels
  | @cro f i j lt actual principal inside old relation =>
    exact unary_word (s:=.croAction f i j lt) (k:=j-1) actual (Bij.refl Unit)
      (Or.inr (Or.inl rfl)) passive relation labels
  | @bra f i j lt actual principal inside old relation =>
    exact unary_word (s:=.braAction f i j lt) (k:=j+1) actual (Bij.refl Unit)
      (Or.inr (Or.inr rfl)) passive relation labels
private theorem local_head {principal : SiteActionPrincipal site} {inside old}
    (relation : ActionCanonicalLocal site principal inside old) :
    ∃ entry : s.Frontier,inside.head?=some (Sum.inr (Sum.inl entry)) := by
  cases relation with
  | fan relation => exact fan_head _ relation
  | @cro f i j lt actual principal inside old relation =>
    exact unary_head (s:=.croAction f i j lt) (k:=j-1) actual (Bij.refl Unit) relation
  | @bra f i j lt actual principal inside old relation =>
    exact unary_head (s:=.braAction f i j lt) (k:=j+1) actual (Bij.refl Unit) relation
private theorem raw_through_word (e : Endpoint cut) (inside : List (Endpoint s.right.net))
    (exit : s.Frontier) (tail : List (PlugSegment cut s.right.net))
    (head : ∃ entry : s.Frontier,inside.head?=some (Sum.inr (Sum.inl entry))) :
    rawControlWord cut s.right.net
      (Sum.inl e::(inside.map Sum.inr++Sum.inl (Sum.inr (Sum.inl (Sum.inr exit)))::tail))=
      controlWord s.right.net inside++rawControlWord cut s.right.net (Sum.inl (Sum.inr (Sum.inl (Sum.inr exit)))::tail) := by
  obtain ⟨entry,first⟩ := head
  obtain ⟨insideTail,split⟩ := List.head?_eq_some_iff.mp first
  rw [split]
  simp [rawControlWord,controlWord,List.flatMap_append,List.flatMap_map,endpointControlWord] <;> rfl

/-- Every actual labelled administrative canonical block whose passive node
is lambda preserves the complete control word. Covers fan/cro/bra without
NoThrough, context equality, rank or a desired residual-word premise. -/
theorem ActionCanonicalBlocks.lambda_control_word (passive : s.passive=.lam)
    {principal : SiteActionPrincipal site} {raw old}
    (canonical : ActionCanonicalBlocks site principal raw old)
    {a b c d : Context} (oldLabels : Labelling site.net old a b)
    (rawLabels : PlugLabelling cut s.right.net raw c d) :
    rawControlWord cut s.right.net raw=controlWord site.net old := by
  induction canonical generalizing a b c d with
  | single e => rfl
  | @outside e f tail old rest ih =>
    obtain ⟨rawMiddle,turn,remainingRaw⟩ := outside_cons_view cut s.right.net rawLabels
    obtain ⟨oldTail,oldEq⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
    rw [oldEq] at oldLabels
    cases oldLabels with
    | @cons _ _ _ _ oldMiddle _ _oldTurn remainingOld =>
      have oldRest : Labelling site.net old oldMiddle b := by simpa only [oldEq] using remainingOld
      have next := ih oldRest remainingRaw
      rw [oldEq] at next ⊢
      change endpointControlWord cut f++rawControlWord cut s.right.net (Sum.inl f::tail)=
        endpointControlWord site.net (site.outsideEnd f)++controlWord site.net (site.outsideEnd f::oldTail)
      rw [next,site.outside_control_port_word turn]
  | @through e exit tail old inside front route start rest ih =>
    obtain ⟨oldTail,oldEq⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
    have actualOld : Labelling site.net
        (front++site.outsideEnd (Sum.inr (Sum.inl (Sum.inr exit)))::oldTail) a b := by
      simpa only [oldEq] using oldLabels
    obtain ⟨oldMiddle,localLabels,remainingOld⟩ := actualOld.split_segment
    have oldRest : Labelling site.net old oldMiddle b := by simpa only [oldEq] using remainingOld
    have actualRaw : PlugLabelling cut s.right.net
        ((Sum.inl e::inside.map Sum.inr)++Sum.inl (Sum.inr (Sum.inl (Sum.inr exit)))::tail) c d := rawLabels
    obtain ⟨rawMiddle,remainingRaw⟩ := actualRaw.suffix_labels (by intro empty;cases empty)
    have next := ih oldRest remainingRaw
    have block := local_word site passive route localLabels
    rw [raw_through_word site e inside exit tail (local_head site route),next,block]
    rw [oldEq]
    exact (word_overlap site.net front (site.outsideEnd (Sum.inr (Sum.inl (Sum.inr exit)))) oldTail).symm
end Whole
end Lamping.AG

import Lamping.Lamping.PhysicalControlWordTools
import Lamping.Lamping.UnaryCanonicalComparison
import Lamping.Lamping.ActionSourceCanonicalBlocks
import Lamping.Lamping.ActionRawOutsideCut

namespace Lamping.AG
open Graph Lambda Lambda.Labelled ExposureScheduling

private theorem controlWord_overlap {N B W : Type}
    [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (before : List (Endpoint g))
    (pivot : Endpoint g) (after : List (Endpoint g)) :
    controlWord g (before++pivot::after)=
      controlWord g (before++[pivot])++controlWord g (pivot::after) := by
  cases before with
  | nil => rfl
  | cons first before =>
    change (before++pivot::after).flatMap (endpointControlWord g)=
      (before++[pivot]).flatMap (endpointControlWord g)++after.flatMap (endpointControlWord g)
    rw [List.flatMap_append,List.flatMap_append,List.flatMap_cons,List.flatMap_singleton]
    exact (List.append_assoc _ _ _).symm

private theorem lambda_no_aux_aux (index : Nat) (p q : Bool) {a b : Context}
    (turn : Traversal index (Kind.op Op.lam) (Sum.inr p : Port (Kind.op Op.lam))
      (Sum.inr q : Port (Kind.op Op.lam)) a b) : False := by
  exact turn.aux_aux

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.croAction Op.lam i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => unaryRightCore Op.cro Op.lam (Bij.refl Unit) i (j-1)

private theorem principal_tokens (principal : SiteActionPrincipal site) :
    principal.edges.flatMap (endpointControlWord site.net)=[true] := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp principal.first
  have empty := transparent_control_word site.net principal.edges principal.transparent
  rw [split] at empty ⊢
  change tail.flatMap (endpointControlWord site.net)=[] at empty
  change [true]++tail.flatMap (endpointControlWord site.net)=[true]
  rw [empty]
  rfl

private theorem reverse_principal_tokens (principal : SiteActionPrincipal site) :
    (reverseEdges principal.edges).flatMap (endpointControlWord site.net)=[] := by
  have head : (reverseEdges principal.edges).head?=
      some (Sum.inl ⟨Sum.inr (Sum.inr ()),Sum.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,
      Option.map_some,Pairing.involutive]
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp head
  have empty := transparent_control_word site.net (reverseEdges principal.edges)
    (transparent_reverse_turns principal.edges principal.transparent)
  rw [split] at empty ⊢
  change tail.flatMap (endpointControlWord site.net)=[] at empty
  change []++tail.flatMap (endpointControlWord site.net)=[]
  rw [empty]
  rfl

private theorem passive_impossible (p q : Bool) {a b : Context}
    (labels : Labelling site.net (site.passiveCanonical p q) a b) : False := by
  cases labels with
  | cons turn finish =>
    rw [Pairing.involutive] at turn
    cases finish
    cases turn with
    | node node incoming outgoing rule =>
      exact lambda_no_aux_aux j p q rule

private theorem unary_local_word {principal : SiteActionPrincipal site}
    {inside : List (Endpoint rhs)} {old : List (Endpoint site.net)}
    (relation : UnaryCanonicalLocal (s:=schema) (k:=j-1) site (Bij.refl Unit) principal inside old)
    {a b : Context} (labels : Labelling site.net old a b) :
    controlWord rhs inside=controlWord site.net old := by
  refine UnaryCanonicalLocal.rec (s:=schema) (k:=j-1) (site:=site)
    (single:=Bij.refl Unit) (principal:=principal)
    (motive:=fun inside old _ => ∀ {a b : Context},Labelling site.net old a b →
      controlWord rhs inside=controlWord site.net old)
    ?_ ?_ ?_ relation labels
  · intro q a b _labels
    change [true]=(principal.edges++[(Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inr q)) : Endpoint site.net)]).flatMap
      (endpointControlWord site.net)
    rw [List.flatMap_append,principal_tokens site principal]
    rfl
  · intro q a b _labels
    rw [principal.reverse_crossing_edges site]
    change [false]=(reverseEdges principal.edges++[(Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr ())) : Endpoint site.net)]).flatMap
      (endpointControlWord site.net)
    rw [List.flatMap_append,reverse_principal_tokens site principal]
    rfl
  · intro p q a b labels
    exact False.elim (passive_impossible site p q labels)

private theorem local_word {principal : SiteActionPrincipal site} {inside old}
    (relation : ActionCanonicalLocal site principal inside old)
    {a b : Context} (labels : Labelling site.net old a b) :
    controlWord rhs inside=controlWord site.net old := by
  cases relation with
  | cro relation => exact unary_local_word site relation labels

private theorem unary_boundary_head {principal : SiteActionPrincipal site}
    {inside : List (Endpoint rhs)} {old : List (Endpoint site.net)}
    (relation : UnaryCanonicalLocal (s:=schema) (k:=j-1) site (Bij.refl Unit) principal inside old) :
    ∃ entry : Unit⊕Bool,inside.head?=some (Sum.inr (Sum.inl entry)) := by
  refine UnaryCanonicalLocal.rec (s:=schema) (k:=j-1) (site:=site)
    (single:=Bij.refl Unit) (principal:=principal)
    (motive:=fun inside _ _ => ∃ entry : Unit⊕Bool,inside.head?=some (Sum.inr (Sum.inl entry)))
    ?_ ?_ ?_ relation
  · intro q
    exact ⟨Sum.inl (),rfl⟩
  · intro q
    exact ⟨Sum.inr q,rfl⟩
  · intro p q
    exact ⟨Sum.inr p,rfl⟩

private theorem local_boundary_head {principal : SiteActionPrincipal site} {inside old}
    (relation : ActionCanonicalLocal site principal inside old) :
    ∃ entry : Unit⊕Bool,inside.head?=some (Sum.inr (Sum.inl entry)) := by
  cases relation with
  | cro relation => exact unary_boundary_head site relation

private theorem raw_through_word (e : Endpoint cut) (inside : List (Endpoint rhs))
    (exit : Unit⊕Bool) (tail : List (PlugSegment cut rhs))
    (head : ∃ entry : Unit⊕Bool,inside.head?=some (Sum.inr (Sum.inl entry))) :
    rawControlWord cut rhs
      (Sum.inl e::(inside.map Sum.inr++Sum.inl (Sum.inr (Sum.inl (Sum.inr exit)))::tail))=
      controlWord rhs inside++rawControlWord cut rhs (Sum.inl (Sum.inr (Sum.inl (Sum.inr exit)))::tail) := by
  obtain ⟨entry,first⟩ := head
  obtain ⟨insideTail,split⟩ := List.head?_eq_some_iff.mp first
  rw [split]
  simp [rawControlWord,controlWord,List.flatMap_append,List.flatMap_map,endpointControlWord] <;> rfl

/-- Complete labelled cro/lambda canonical blocks retain their whole control
word. Passive blocks are excluded by actual lambda traversal, not NoThrough.
Input/output contexts may differ on the two sides and are never identified. -/
theorem ActionCanonicalBlocks.cro_lam_control_word
    {principal : SiteActionPrincipal site} {raw old}
    (canonical : ActionCanonicalBlocks site principal raw old)
    {a b c d : Context} (oldLabels : Labelling site.net old a b)
    (rawLabels : PlugLabelling cut rhs raw c d) :
    rawControlWord cut rhs raw=controlWord site.net old := by
  induction canonical generalizing a b c d with
  | single e => rfl
  | @outside e f tail old rest ih =>
    obtain ⟨rawMiddle,turn,remainingRaw⟩ := outside_cons_view cut rhs rawLabels
    obtain ⟨oldTail,oldEq⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
    rw [oldEq] at oldLabels
    cases oldLabels with
    | @cons _ _ _ _ oldMiddle _ _oldTurn remainingOld =>
      have oldRest : Labelling site.net old oldMiddle b := by simpa only [oldEq] using remainingOld
      have next := ih oldRest remainingRaw
      rw [oldEq] at next ⊢
      change endpointControlWord cut f++rawControlWord cut rhs (Sum.inl f::tail)=
        endpointControlWord site.net (site.outsideEnd f)++controlWord site.net (site.outsideEnd f::oldTail)
      rw [next,site.outside_control_port_word turn]
  | @through e exit tail old inside front route start rest ih =>
    obtain ⟨oldTail,oldEq⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
    have actualOld : Labelling site.net
        (front++site.outsideEnd (Sum.inr (Sum.inl (Sum.inr exit)))::oldTail) a b := by
      simpa only [oldEq] using oldLabels
    obtain ⟨oldMiddle,localLabels,remainingOld⟩ := actualOld.split_segment
    have oldRest : Labelling site.net old oldMiddle b := by simpa only [oldEq] using remainingOld
    have actualRaw : PlugLabelling cut rhs
        ((Sum.inl e::inside.map Sum.inr)++Sum.inl (Sum.inr (Sum.inl (Sum.inr exit)))::tail) c d := rawLabels
    obtain ⟨rawMiddle,remainingRaw⟩ := actualRaw.suffix_labels (by intro empty;cases empty)
    have next := ih oldRest remainingRaw
    have block := local_word site route localLabels
    rw [raw_through_word site e inside exit tail (local_boundary_head site route),next,block]
    rw [oldEq]
    exact (controlWord_overlap site.net front (site.outsideEnd (Sum.inr (Sum.inl (Sum.inr exit)))) oldTail).symm
end
end Lamping.AG

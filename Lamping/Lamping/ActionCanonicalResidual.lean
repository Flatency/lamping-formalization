import Lamping.Lamping.ActionCanonicalRoutes
import Lamping.Lamping.ActionLocalAncestors
import Lamping.Lamping.ActionAncestor
namespace Lamping.AG
open Graph
section
variable {f : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))

def fanCrossEdges (branch : Bool) (q : Aux f) : List (Endpoint (fanRight f i j)) :=
  [.inr (.inl (.inl branch)),.inl ⟨.inl branch,.inr q⟩,.inl ⟨.inr q,.inl ()⟩]

def fanPassiveEdges (branch : Bool) (p q : Aux f) : List (Endpoint (fanRight f i j)) :=
  [.inr (.inl (.inr p)),.inl ⟨.inr p,.inr branch⟩,
    .inl ⟨.inl branch,.inr q⟩,.inl ⟨.inr q,.inl ()⟩]

/-- Literal canonical source routes, chosen once from the actual site's
principal component. No semantic replay property is part of this relation. -/
inductive FanCanonicalLocal (principal : SiteActionPrincipal site) :
    List (Endpoint (fanRight f i j)) → List (Endpoint site.net) → Prop where
  | cross (branch : Bool) (q : Aux f) :
      FanCanonicalLocal principal (fanCrossEdges branch q) (principal.crossing site branch q)
  | backward (branch : Bool) (q : Aux f) :
      FanCanonicalLocal principal (reverseEdges (fanCrossEdges branch q))
        (reverseEdges (principal.crossing site branch q))
  | passive (branch : Bool) (p q : Aux f) :
      FanCanonicalLocal principal (fanPassiveEdges branch p q) (site.passiveCanonical p q)

theorem FanCanonicalLocal.source_labels {principal : SiteActionPrincipal site}
    {rhs old} (relation : FanCanonicalLocal site principal rhs old) {a b : Context}
    (labels : Labelling (fanRight f i j) rhs a b) : Labelling site.net old a b := by
  cases relation with
  | cross branch q =>
    exact (principal.crossing_labels_iff site branch q a b).mpr
      (fanAction_cross_inverse f i j lt branch q a b labels)
  | backward branch q =>
    have forwardLabels := labels.reverse
    rw [reverseEdges_involutive] at forwardLabels
    exact ((principal.crossing_labels_iff site branch q b a).mpr
      (fanAction_cross_inverse f i j lt branch q b a forwardLabels)).reverse
  | passive branch p q =>
    exact (site.passiveCanonical_labels_iff p q a b).mpr
      (fanAction_passive_inverse f i j branch p q a b labels)

/-- Finite actual local-path reflection fixes a canonical old route for every
complete fan RHS excursion, including reverse and passive passages. -/
theorem fan_canonical_local (principal : SiteActionPrincipal site)
    (entry exit : Bool⊕Aux f) (a b : Context)
    (path : LocalPath (fanRight f i j) entry exit a b) :
    ∃ old,FanCanonicalLocal site principal path.edges old ∧Labelling site.net old a b := by
  have reflected : ∃ old,FanCanonicalLocal site principal path.edges old := by
    cases entry with
    | inl branch =>
      obtain ⟨q,rfl,shape⟩ := fanRight_active_path_shape f i j branch exit path.edges a b
        path.labeling path.start path.finish
      rw [shape]
      exact ⟨_,.cross branch q⟩
    | inr p =>
      rcases fanRight_passive_path_shape f i j p exit path.edges a b
        path.labeling path.start path.finish with ⟨branch,rfl,shape⟩ |⟨branch,q,rfl,shape⟩
      · rw [shape]
        exact ⟨_,by simpa [fanCrossEdges,reverseEdges,fanRight] using
          (FanCanonicalLocal.backward (site:=site) (principal:=principal) branch p)⟩
      · rw [shape]
        exact ⟨_,.passive branch p q⟩
  obtain ⟨old,relation⟩ := reflected
  exact ⟨old,relation,relation.source_labels site path.labeling⟩

theorem FanCanonicalLocal.source_endpoints {principal : SiteActionPrincipal site}
    {rhs old} (relation : FanCanonicalLocal site principal rhs old)
    (entry exit : Bool⊕Aux f)
    (start : rhs.head?=some (.inr (.inl entry)))
    (finish : rhs.getLast?=some ((fanRight f i j).wire (.inr (.inl exit)))) :
    old.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr entry))))) ∧
    old.getLast?=some (site.outsideEnd (.inr (.inl (.inr exit)))) := by
  cases relation with
  | cross branch q =>
    have entryEq : entry=.inl branch := (Sum.inl.inj (Sum.inr.inj (Option.some.inj start))).symm
    subst entry
    have exitEq : exit=.inr q := by
      cases exit <;> simp_all [fanCrossEdges,fanRight]
    subst exit
    constructor
    · rfl
    · simp only [SiteActionPrincipal.crossing,List.getLast?_cons,List.getLast?_append,
        List.getLast?_cons,List.getLast?_nil,Option.some_or]
      rfl
  | backward branch q =>
    have entryEq : entry=.inr q := by
      simpa [fanCrossEdges,reverseEdges,fanRight] using start.symm
    subst entry
    have exitEq : exit=.inl branch := by
      cases exit <;> simp_all [fanCrossEdges,reverseEdges,fanRight]
    subst exit
    constructor
    · simp only [reverseEdges,List.head?_map,List.head?_reverse,
        SiteActionPrincipal.crossing,List.getLast?_cons,List.getLast?_append,
        List.getLast?_cons,List.getLast?_nil,Option.some_or,Option.map_some]
      rfl
    · simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,
        SiteActionPrincipal.crossing,List.head?_cons,Option.map_some,Pairing.involutive]
      rfl
  | passive branch p q =>
    have entryEq : entry=.inr p := (Sum.inl.inj (Sum.inr.inj (Option.some.inj start))).symm
    subst entry
    have exitEq : exit=.inr q := by
      cases exit <;> simp_all [fanPassiveEdges,fanRight]
    subst exit
    exact ⟨rfl,rfl⟩
end

section Unary
variable {s : Schema} {k : Nat}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
variable (single : Bij Unit (Aux s.active))

def unaryCrossEdges (q : Aux s.passive) :
    List (Endpoint (unaryRightCore s.active s.passive single s.low k)) :=
  [.inr (.inl (.inl ())),.inl ⟨.inl (),.inr q⟩,.inl ⟨.inr q,.inl ()⟩]

def unaryPassiveEdges (p q : Aux s.passive) :
    List (Endpoint (unaryRightCore s.active s.passive single s.low k)) :=
  [.inr (.inl (.inr p)),.inl ⟨.inr p,.inr (single ())⟩,
    .inl ⟨.inl (),.inr q⟩,.inl ⟨.inr q,.inl ()⟩]

inductive UnaryCanonicalLocal (principal : SiteActionPrincipal site) :
    List (Endpoint (unaryRightCore s.active s.passive single s.low k)) →
    List (Endpoint site.net) → Prop where
  | cross (q : Aux s.passive) :
      UnaryCanonicalLocal principal (unaryCrossEdges single q) (principal.crossing site (single ()) q)
  | backward (q : Aux s.passive) :
      UnaryCanonicalLocal principal (reverseEdges (unaryCrossEdges single q))
        (reverseEdges (principal.crossing site (single ()) q))
  | passive (p q : Aux s.passive) :
      UnaryCanonicalLocal principal (unaryPassiveEdges single p q) (site.passiveCanonical p q)

theorem UnaryCanonicalLocal.source_labels {principal : SiteActionPrincipal site}
    (crossInverse : ∀ q a b,Labelling (unaryRightCore s.active s.passive single s.low k)
      (unaryCrossEdges single q) a b →
      Labelling s.left (leftRoute s.active s.passive s.low s.high (single ()) q) a b)
    {rhs old} (relation : UnaryCanonicalLocal site single principal rhs old) {a b : Context}
    (labels : Labelling (unaryRightCore s.active s.passive single s.low k) rhs a b) :
    Labelling site.net old a b := by
  cases relation with
  | cross q => exact (principal.crossing_labels_iff site (single ()) q a b).mpr (crossInverse q a b labels)
  | backward q =>
    have forwardLabels := labels.reverse
    rw [reverseEdges_involutive] at forwardLabels
    exact ((principal.crossing_labels_iff site (single ()) q b a).mpr
      (crossInverse q b a forwardLabels)).reverse
  | passive p q =>
    exact (site.passiveCanonical_labels_iff p q a b).mpr
      (unaryAction_passive_inverse s.active s.passive single s.low k s.high p q a b labels)

theorem unary_canonical_local (principal : SiteActionPrincipal site)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (crossInverse : ∀ q a b,Labelling (unaryRightCore s.active s.passive single s.low k)
      (unaryCrossEdges single q) a b →
      Labelling s.left (leftRoute s.active s.passive s.low s.high (single ()) q) a b)
    (entry exit : Unit⊕Aux s.passive) (a b : Context)
    (path : LocalPath (unaryRightCore s.active s.passive single s.low k) entry exit a b) :
    ∃ old,UnaryCanonicalLocal site single principal path.edges old ∧Labelling site.net old a b := by
  have reflected : ∃ old,UnaryCanonicalLocal site single principal path.edges old := by
    cases entry with
    | inl u =>
      cases u
      obtain ⟨q,rfl,shape⟩ := unaryRight_active_path_shape s.active s.passive single control s.low k exit path.edges a b
        path.labeling path.start path.finish
      rw [shape]
      exact ⟨_,.cross q⟩
    | inr p =>
      rcases unaryRight_passive_path_shape s.active s.passive single control s.low k p exit path.edges a b
        path.labeling path.start path.finish with ⟨rfl,shape⟩ |⟨q,rfl,shape⟩
      · rw [shape]
        exact ⟨_,by simpa [unaryCrossEdges,reverseEdges,unaryRightCore] using
          (UnaryCanonicalLocal.backward (site:=site) (single:=single) (principal:=principal) (k:=k) p)⟩
      · rw [shape]
        exact ⟨_,.passive p q⟩
  obtain ⟨old,relation⟩ := reflected
  exact ⟨old,relation,relation.source_labels site single crossInverse path.labeling⟩

theorem UnaryCanonicalLocal.source_endpoints {principal : SiteActionPrincipal site}
    {rhs old} (relation : UnaryCanonicalLocal site single principal rhs old)
    (entry exit : Unit⊕Aux s.passive)
    (start : rhs.head?=some (.inr (.inl entry)))
    (finish : rhs.getLast?=some ((unaryRightCore s.active s.passive single s.low k).wire (.inr (.inl exit)))) :
    old.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr (entry.map single id)))))) ∧
    old.getLast?=some (site.outsideEnd (.inr (.inl (.inr (exit.map single id))))) := by
  cases relation with
  | cross q =>
    have entryEq : entry=.inl () := (Sum.inl.inj (Sum.inr.inj (Option.some.inj start))).symm
    subst entry
    have exitEq : exit=.inr q := by
      cases exit <;> simp_all [unaryCrossEdges,unaryRightCore]
    subst exit
    constructor
    · rfl
    · simp only [SiteActionPrincipal.crossing,List.getLast?_cons,List.getLast?_append,
        List.getLast?_cons,List.getLast?_nil,Option.some_or]
      rfl
  | backward q =>
    have entryEq : entry=.inr q := by
      simpa [unaryCrossEdges,reverseEdges,unaryRightCore] using start.symm
    subst entry
    have exitEq : exit=.inl () := by
      cases exit with
      | inl u => cases u; rfl
      | inr r => simp [unaryCrossEdges,reverseEdges,unaryRightCore] at finish
    subst exit
    constructor
    · simp only [reverseEdges,List.head?_map,List.head?_reverse,
        SiteActionPrincipal.crossing,List.getLast?_cons,List.getLast?_append,
        List.getLast?_cons,List.getLast?_nil,Option.some_or,Option.map_some]
      rfl
    · simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,
        SiteActionPrincipal.crossing,List.head?_cons,Option.map_some,Pairing.involutive]
      rfl
  | passive p q =>
    have entryEq : entry=.inr p := (Sum.inl.inj (Sum.inr.inj (Option.some.inj start))).symm
    subst entry
    have exitEq : exit=.inr q := by
      cases exit <;> simp_all [unaryPassiveEdges,unaryRightCore]
    subst exit
    exact ⟨rfl,rfl⟩
end Unary

section UnaryInstances
variable {f : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}

theorem cro_canonical_local
    (site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    (principal : SiteActionPrincipal site) (entry exit : Unit⊕Aux f) (a b : Context)
    (path : LocalPath (unaryRightCore .cro f (Bij.refl _) i (j-1)) entry exit a b) :
    ∃ old,UnaryCanonicalLocal site (Bij.refl _) principal path.edges old ∧Labelling site.net old a b := by
  exact unary_canonical_local site (Bij.refl _) principal (Or.inr (Or.inl rfl))
    (fun q a b labels => croAction_cross_inverse f i j lt q a b labels) entry exit a b path

theorem bra_canonical_local
    (site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    (principal : SiteActionPrincipal site) (entry exit : Unit⊕Aux f) (a b : Context)
    (path : LocalPath (unaryRightCore .bra f (Bij.refl _) i (j+1)) entry exit a b) :
    ∃ old,UnaryCanonicalLocal site (Bij.refl _) principal path.edges old ∧Labelling site.net old a b := by
  exact unary_canonical_local site (Bij.refl _) principal (Or.inr (Or.inr rfl))
    (fun q a b labels => braAction_cross_inverse f i j lt q a b labels) entry exit a b path
end UnaryInstances

section Actions
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}

inductive ActionCanonicalLocal : {s : Schema} →
    (site : PathSite s kept (B:=B) (W:=W) (V:=V)) → SiteActionPrincipal site →
    List (Endpoint s.right.net) → List (Endpoint site.net) → Prop where
  | fan {f i j lt} {site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V)}
      {principal rhs old} (relation : FanCanonicalLocal site principal rhs old) :
      ActionCanonicalLocal site principal rhs old
  | cro {f i j lt} {site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V)}
      {principal rhs old} (relation : UnaryCanonicalLocal site (Bij.refl _) principal rhs old) :
      ActionCanonicalLocal site principal rhs old
  | bra {f i j lt} {site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V)}
      {principal rhs old} (relation : UnaryCanonicalLocal site (Bij.refl _) principal rhs old) :
      ActionCanonicalLocal site principal rhs old

variable {s : Schema} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

theorem action_canonical_local (action : IsAction s) (principal : SiteActionPrincipal site)
    (entry exit : s.Frontier) (a b : Context) (path : LocalPath s.right.net entry exit a b) :
    ∃ old,ActionCanonicalLocal site principal path.edges old ∧Labelling site.net old a b := by
  cases action with
  | fan f i j lt =>
    obtain ⟨old,relation,labels⟩ := fan_canonical_local site principal entry exit a b path
    exact ⟨old,.fan relation,labels⟩
  | cro f i j lt =>
    obtain ⟨old,relation,labels⟩ := cro_canonical_local site principal entry exit a b path
    exact ⟨old,.cro relation,labels⟩
  | bra f i j lt =>
    obtain ⟨old,relation,labels⟩ := bra_canonical_local site principal entry exit a b path
    exact ⟨old,.bra relation,labels⟩

theorem ActionCanonicalLocal.source_endpoints {principal : SiteActionPrincipal site}
    {rhs old} (relation : ActionCanonicalLocal site principal rhs old)
    (entry exit : s.Frontier)
    (start : rhs.head?=some (.inr (.inl entry)))
    (finish : rhs.getLast?=some (s.right.net.wire (.inr (.inl exit)))) :
    old.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr entry))))) ∧
    old.getLast?=some (site.outsideEnd (.inr (.inl (.inr exit)))) := by
  cases relation with
  | fan relation => exact FanCanonicalLocal.source_endpoints _ relation entry exit start finish
  | cro relation =>
    simpa only [Bij.refl,Sum.map_id_id] using UnaryCanonicalLocal.source_endpoints _
      (Bij.refl _) relation entry exit start finish
  | bra relation =>
    simpa only [Bij.refl,Sum.map_id_id] using UnaryCanonicalLocal.source_endpoints _
      (Bij.refl _) relation entry exit start finish

theorem ActionCanonicalLocal.source_labels {principal : SiteActionPrincipal site}
    {rhs old} (relation : ActionCanonicalLocal site principal rhs old) {a b : Context}
    (labels : Labelling s.right.net rhs a b) : Labelling site.net old a b := by
  cases relation with
  | fan relation => exact relation.source_labels _ labels
  | @cro f i j lt actual principal rhs old relation =>
    exact relation.source_labels actual (Bij.refl _)
      (fun q a b labels => croAction_cross_inverse f i j lt q a b labels) labels
  | @bra f i j lt actual principal rhs old relation =>
    exact relation.source_labels actual (Bij.refl _)
      (fun q a b labels => braAction_cross_inverse f i j lt q a b labels) labels

theorem ActionCanonicalLocal.nonempty {principal : SiteActionPrincipal site}
    {rhs old} (relation : ActionCanonicalLocal site principal rhs old) : rhs≠[] := by
  cases relation with
  | fan relation => cases relation <;> simp [fanCrossEdges,fanPassiveEdges,reverseEdges,fanRight]
  | cro relation => cases relation <;> simp [unaryCrossEdges,unaryPassiveEdges,reverseEdges,unaryRightCore]
  | bra relation => cases relation <;> simp [unaryCrossEdges,unaryPassiveEdges,reverseEdges,unaryRightCore]
end Actions
end Lamping.AG


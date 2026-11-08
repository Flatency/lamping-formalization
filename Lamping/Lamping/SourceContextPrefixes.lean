import Lamping.Lamping.ActionContextPrefixes
import Lamping.Lamping.ControlContextTails
import Lamping.Lamping.PrincipalCrossings
import Lamping.Lamping.PathSiteBetaAncestor
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

def PathSite.passiveAuxPrefix (q : Aux s.passive) : List (Endpoint site.net) :=
  [site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)]

theorem PathSite.passiveAuxPrefix_labels (q : Aux s.passive) (a : Context) :
    Labelling site.net (site.passiveAuxPrefix q) a a := .single _ _

/-- A real source prefix reaches the passive principal through the active
control and every selected subdivision; the terminal context is explicit. -/
theorem PathSite.active_principal_prefix (p : Aux s.active) (a b : Context)
    (rule : Traversal s.low (.op s.active) (.inr p) (.inl ()) a b) :
    ∃ es : List (Endpoint site.net),
      es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)) ∧
      es.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧Labelling site.net es a b := by
  obtain ⟨route,start,finish,turns⟩ := site.principal_route
  have nonempty : route≠[] := by intro empty; rw [empty] at start; cases start
  have labels := transparent_route_labelling site.net route nonempty turns b
  refine ⟨site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::route,rfl,?_,?_⟩
  · cases route with
    | nil => exact False.elim (nonempty rfl)
    | cons x route => simpa only [List.getLast?_cons_cons] using finish
  · cases route with
    | nil => exact False.elim (nonempty rfl)
    | cons x route =>
      have same : x=.inl ⟨.inr (.inl ()),.inl ()⟩ := Option.some.inj start
      subst x
      apply Labelling.cons
      · rw [Pairing.involutive]
        exact LabelledTurn.node (g:=site.net) (.inr (.inl ())) _ _ rule
      · exact labels
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {f : Op} {i j : Nat} {lt : i<j}

/-- Copied auxiliary prefixes map to the actual old auxiliary endpoint.
Only the high terminal tails coincide; the full contexts may differ. -/
theorem PathSite.fan_aux_context_ancestor
    (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    (branch : Bool) (q : Aux f) (entry : Bool⊕Aux f)
    (es : List (Endpoint (fanRight f i j))) (a b : Context)
    (labels : Labelling (fanRight f i j) es a b)
    (start : es.head?=some (.inr (.inl entry)))
    (finish : es.getLast?=some ((fanRight f i j).wire (.inl ⟨.inl branch,.inr q⟩))) :
    entry=.inr q ∧Labelling site.net (site.passiveAuxPrefix q) a a ∧a.tail j=b.tail j := by
  obtain ⟨same,_,inverse⟩ := fanRight_copied_aux_prefix f i j branch q entry es a b labels start finish
  exact ⟨same,site.passiveAuxPrefix_labels q a,inverse.fan_inverse_high_tail lt⟩

theorem PathSite.cro_aux_context_ancestor
    (site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    (q : Aux f) (entry : Unit⊕Aux f)
    (es : List (Endpoint (unaryRightCore .cro f (Bij.refl _) i (j-1)))) (a b : Context)
    (labels : Labelling (unaryRightCore .cro f (Bij.refl _) i (j-1)) es a b)
    (start : es.head?=some (.inr (.inl entry)))
    (finish : es.getLast?=some ((unaryRightCore .cro f (Bij.refl _) i (j-1)).wire (.inl ⟨.inl (),.inr q⟩))) :
    entry=.inr q ∧Labelling site.net (site.passiveAuxPrefix q) a a ∧a.tail j=b.tail (j-1) := by
  obtain ⟨same,_,inverse⟩ := unaryRight_copied_aux_prefix .cro f (Bij.refl _) (Or.inr (Or.inl rfl))
    i (j-1) q entry es a b labels start finish
  exact ⟨same,site.passiveAuxPrefix_labels q a,inverse.cro_inverse_high_tail lt⟩

theorem PathSite.bra_aux_context_ancestor
    (site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    (q : Aux f) (entry : Unit⊕Aux f)
    (es : List (Endpoint (unaryRightCore .bra f (Bij.refl _) i (j+1)))) (a b : Context)
    (labels : Labelling (unaryRightCore .bra f (Bij.refl _) i (j+1)) es a b)
    (start : es.head?=some (.inr (.inl entry)))
    (finish : es.getLast?=some ((unaryRightCore .bra f (Bij.refl _) i (j+1)).wire (.inl ⟨.inl (),.inr q⟩))) :
    entry=.inr q ∧Labelling site.net (site.passiveAuxPrefix q) a a ∧a.tail j=b.tail (j+1) := by
  obtain ⟨same,_,inverse⟩ := unaryRight_copied_aux_prefix .bra f (Bij.refl _) (Or.inr (Or.inr rfl))
    i (j+1) q entry es a b labels start finish
  exact ⟨same,site.passiveAuxPrefix_labels q a,inverse.bra_inverse_high_tail lt⟩
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}

theorem PathSite.fan_lam_context_ancestor
    (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    (branch : Bool) (entry : Bool⊕Bool) (es : List (Endpoint (fanRight .lam i j))) (a b : Context)
    (labels : Labelling (fanRight .lam i j) es a b)
    (start : es.head?=some (.inr (.inl entry)))
    (finish : es.getLast?=some ((fanRight .lam i j).wire (.inl ⟨.inl branch,.inl ()⟩))) :
    entry=.inl branch ∧∃ old : List (Endpoint site.net),
      old.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      Labelling site.net old a (InitialOffsets.fanAt i branch b) ∧
      (InitialOffsets.fanAt i branch b).tail j=b.tail j := by
  obtain ⟨same,_,inputs⟩ := fanRight_lam_context_prefix i j branch entry es a b labels start finish
  subst b
  obtain ⟨old,head,last,oldLabels⟩ := site.active_principal_prefix branch a _
    (.direct (InitialOffsets.Event.apply_rel (.fan i branch) a))
  exact ⟨same,old,head,last,oldLabels,InitialOffsets.fanAt_high_tail a i j lt branch⟩

theorem PathSite.cro_lam_context_ancestor
    (site : PathSite (.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    (entry : Unit⊕Bool) (es : List (Endpoint (unaryRightCore .cro .lam (Bij.refl _) i (j-1)))) (a b : Context)
    (labels : Labelling (unaryRightCore .cro .lam (Bij.refl _) i (j-1)) es a b)
    (start : es.head?=some (.inr (.inl entry)))
    (finish : es.getLast?=some ((unaryRightCore .cro .lam (Bij.refl _) i (j-1)).wire (.inl ⟨.inl (),.inl ()⟩))) :
    entry=.inl () ∧∃ old : List (Endpoint site.net),
      old.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩)) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      Labelling site.net old a (InitialOffsets.croAt i b) ∧
      (InitialOffsets.croAt i b).tail j=b.tail (j-1) := by
  obtain ⟨same,_,inputs⟩ := unaryRight_lam_context_prefix .cro (Bij.refl _) i (j-1) entry es a b labels start finish
  subst b
  obtain ⟨old,head,last,oldLabels⟩ := site.active_principal_prefix () a _
    (.direct (InitialOffsets.Event.apply_rel (.cro i) a))
  exact ⟨same,old,head,last,oldLabels,InitialOffsets.croAt_high_tail a i j lt⟩

theorem PathSite.bra_lam_context_ancestor
    (site : PathSite (.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    (entry : Unit⊕Bool) (es : List (Endpoint (unaryRightCore .bra .lam (Bij.refl _) i (j+1)))) (a b : Context)
    (labels : Labelling (unaryRightCore .bra .lam (Bij.refl _) i (j+1)) es a b)
    (start : es.head?=some (.inr (.inl entry)))
    (finish : es.getLast?=some ((unaryRightCore .bra .lam (Bij.refl _) i (j+1)).wire (.inl ⟨.inl (),.inl ()⟩))) :
    entry=.inl () ∧∃ old : List (Endpoint site.net),
      old.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩)) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      Labelling site.net old a (InitialOffsets.braAt i b) ∧
      (InitialOffsets.braAt i b).tail j=b.tail (j+1) := by
  obtain ⟨same,_,inputs⟩ := unaryRight_lam_context_prefix .bra (Bij.refl _) i (j+1) entry es a b labels start finish
  subst b
  obtain ⟨old,head,last,oldLabels⟩ := site.active_principal_prefix () a _
    (.direct (InitialOffsets.Event.apply_rel (.bra i) a))
  exact ⟨same,old,head,last,oldLabels,InitialOffsets.braAt_high_tail a i j lt⟩
end
end Lamping.AG

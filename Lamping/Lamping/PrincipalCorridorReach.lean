import Lamping.Lamping.ClosedPrincipalSites
import Lamping.Lamping.GlobalGraphSteps
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (corridor : SelectedCorridor s kept (B:=B) (W:=W) (V:=V))
local notation "naming" => fragmentEnd (B:=B) (W:=W) corridor.net.label (pathPartition s V)

private theorem zip_right_member {A C : Type} {xs : List A} {ys : List C} {a : A} {b : C}
    (member : (a,b)∈xs.zip ys) : b∈ys := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons x xs ih =>
    cases ys with
    | nil => simp at member
    | cons y ys =>
      rcases List.mem_cons.mp member with same |rest
      · exact List.mem_cons.mpr (Or.inl (congrArg Prod.snd same))
      · exact List.mem_cons_of_mem _ (ih rest)

private theorem selected_turns (e f : Endpoint corridor.net)
    (pair : (e,f)∈corridor.edges.zip corridor.edges.tail) :
    ∃ v d,corridor.wire e=.inr (.inr (.inr v,d)) ∧f=.inr (.inr (.inr v,!d)) := by
  obtain ⟨w,d,arrives,leaves⟩ := corridor.transparent e f pair
  have member : f∈corridor.edges := List.mem_of_mem_tail (zip_right_member pair)
  have selected : ∃ v,w=.inr v := (corridor.selectedVertices w).mp
    ⟨!d,by rw [←leaves]; exact member⟩
  obtain ⟨v,same⟩ := selected
  subst w
  exact ⟨v,d,arrives,leaves⟩

private theorem reach_departures (e : Endpoint corridor.net) (tail : List (Endpoint corridor.net))
    (start : Bool ⊕ (V × Bool)) (first : naming e=.inr start)
    (turns : ∀ x y,(x,y)∈(e::tail).zip (e::tail).tail →
      ∃ v d,corridor.wire x=.inr (.inr (.inr v,d)) ∧y=.inr (.inr (.inr v,!d))) :
    ∀ z∈e::tail,∃ i,naming z=.inr i ∧InternalReach corridor.internalPairing start i := by
  induction tail generalizing e start with
  | nil =>
    intro z member
    have same := List.mem_singleton.mp member
    subst z
    exact ⟨start,first,.refl _⟩
  | cons f tail ih =>
    obtain ⟨v,d,arrives,leaves⟩ := turns e f (by simp)
    have next : naming f=.inr (.inr (v,!d)) := by rw [leaves]; rfl
    have mate : corridor.internalPairing start=.inr (v,d) := by
      have commute := Pairing.rename_apply corridor.wire naming e
      rw [first,corridor.internal_wiring,arrives] at commute
      change Sum.inr (corridor.internalPairing start)=Sum.inr (.inr (v,d)) at commute
      exact Sum.inr.inj commute
    have pass : InternalReach corridor.internalPairing start (.inr (v,!d)) := by
      have step : InternalReach corridor.internalPairing start (.inr (v,d)) := by
        simpa only [mate] using InternalReach.segment (p:=corridor.internalPairing) start
      exact .trans step (.vertex v d)
    have remaining : ∀ x y,(x,y)∈(f::tail).zip (f::tail).tail →
        ∃ v d,corridor.wire x=.inr (.inr (.inr v,d)) ∧y=.inr (.inr (.inr v,!d)) := by
      intro x y pair
      exact turns x y (List.mem_cons_of_mem _ pair)
    intro z member
    rcases List.mem_cons.mp member with rfl |member
    · exact ⟨start,first,.refl _⟩
    · obtain ⟨i,atI,reach⟩ := ih f (.inr (v,!d)) next remaining z member
      exact ⟨i,atI,.trans pass reach⟩

/-- Every actual departure of the supplied finite route is reachable in the
computed internal pairing. Repeated physical vertices cause no problem. -/
theorem SelectedCorridor.departure_reachable (z : Endpoint corridor.net)
    (member : z∈corridor.edges) :
    ∃ i,naming z=.inr i ∧InternalReach corridor.internalPairing (.inl false) i := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp corridor.start
  have turns := selected_turns corridor
  rw [split] at member turns
  exact reach_departures corridor _ tail (.inl false) rfl turns z member

/-- Every selected vertex, both ends, and the passive principal are connected
to the active principal by the actual finite corridor and its wire steps. -/
theorem SelectedCorridor.internal_connected (i : Bool ⊕ (V × Bool)) :
    InternalReach corridor.internalPairing (.inl false) i := by
  cases i with
  | inl d =>
    cases d with
    | false => exact .refl _
    | true =>
      let passive : Endpoint corridor.net := .inl ⟨.inr (.inr ()),.inl ()⟩
      obtain ⟨before,split⟩ := List.getLast?_eq_some_iff.mp corridor.finish
      have member : corridor.wire passive∈corridor.edges := by
        dsimp only [passive]
        rw [split]; simp
      obtain ⟨j,atJ,reach⟩ := corridor.departure_reachable _ member
      have mate : corridor.internalPairing j=.inl true := by
        have commute := Pairing.rename_apply corridor.wire naming (corridor.wire passive)
        rw [atJ,corridor.internal_wiring,Pairing.involutive] at commute
        change Sum.inr (corridor.internalPairing j)=Sum.inr (.inl true) at commute
        exact Sum.inr.inj commute
      have step : InternalReach corridor.internalPairing j (.inl true) := by
        simpa only [mate] using InternalReach.segment (p:=corridor.internalPairing) j
      exact .trans reach step
  | inr vd =>
    obtain ⟨v,d⟩ := vd
    obtain ⟨side,member⟩ := (corridor.selectedVertices (.inr v)).mpr ⟨v,rfl⟩
    obtain ⟨j,atJ,reach⟩ := corridor.departure_reachable _ member
    have same : j=.inr (v,side) := (Sum.inr.inj atJ).symm
    subst j
    by_cases equal : d=side
    · subst d; exact reach
    · have opposite : d= !side := by cases d <;> cases side <;> simp_all
      rw [opposite]
      exact .trans reach (.vertex v side)

/-- A physical selected corridor computes a genuine PathSite: its internal
pairing and connectedness are proved, rather than supplied by the caller. -/
def SelectedCorridor.pathSite : PathSite s kept (B:=B) (W:=W) (V:=V) where
  wire := corridor.wire
  internal := corridor.internalPairing
  connected := corridor.internal_connected
  wiring := corridor.internal_wiring

theorem SelectedCorridor.graph_step :
    GraphStep s (ActualNet.ofNet corridor.net) (ActualNet.ofNet corridor.pathSite.reduce) :=
  GraphStep.site kept corridor.pathSite
end
end Lamping.AG

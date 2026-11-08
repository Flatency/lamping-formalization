import Lamping.Lamping.PathSiteBeta
import Lamping.Lamping.LocalTransport
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

theorem transparent_route_labelling (es : List (Endpoint g)) (nonempty : es≠[])
    (turns : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) (a : Context) : Labelling g es a a := by
  induction es with
  | nil => exact False.elim (nonempty rfl)
  | cons e tail ih =>
    cases tail with
    | nil => exact .single _ _
    | cons f tail =>
      obtain ⟨w,d,arrival,departure⟩ := turns e f (by simp)
      apply Labelling.cons
      · rw [arrival,departure]
        exact .transparent w d a
      · apply ih (by simp)
        intro x y member
        exact turns x y (by simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons]; exact Or.inr member)

theorem transparent_route_forward (es : List (Endpoint g)) (nonempty : es≠[])
    (turns : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) : Forward g es := by
  induction es with
  | nil => exact False.elim (nonempty rfl)
  | cons e tail ih =>
    cases tail with
    | nil => exact .single _
    | cons f tail =>
      obtain ⟨w,d,arrival,departure⟩ := turns e f (by simp)
      apply Forward.transparent w d arrival departure
      apply ih (by simp)
      intro x y member
      exact turns x y (by simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons]; exact Or.inr member)
end
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Every schema's matched principal wire has an actual finite directed
route. Its full physical subdivisions come from the matched internal
component, rather than being supplied as a semantic transport certificate. -/
theorem PathSite.principal_route :
    ∃ es : List (Endpoint site.net),
      es.head?=some (.inl ⟨.inr (.inl ()),.inl ()⟩) ∧
      es.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      (∀ e f,(e,f)∈es.zip es.tail →
        ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) := by
  obtain ⟨es,start,finish,turns⟩ := (site.connected (.inl true)).principal_route.realize
  refine ⟨es.map site.internalEnd,?_,?_,?_⟩
  · rw [List.head?_map,start]
    rfl
  · rw [List.getLast?_map,finish]
    change some (site.internalEnd (site.internal (.inl true)))=some (site.net.wire (site.internalEnd (.inl true)))
    rw [site.internalEnd_wire]
  · intro e f member
    rw [←List.map_tail,List.zip_map] at member
    obtain ⟨⟨x,y⟩,pair,equal⟩ := List.mem_map.mp member
    cases equal
    obtain ⟨v,d,arrival,departure⟩ := turns x y pair
    refine ⟨.inr v,d,?_,?_⟩
    · rw [site.internalEnd_wire,arrival]
      rfl
    · rw [departure]
      rfl

theorem PathSite.principal_route_labelled :
    ∃ es : List (Endpoint site.net),
      es.head?=some (.inl ⟨.inr (.inl ()),.inl ()⟩) ∧
      es.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      Forward site.net es ∧∀ a,Labelling site.net es a a := by
  obtain ⟨es,start,finish,turns⟩ := site.principal_route
  have nonempty : es≠[] := by intro empty; rw [empty] at start; cases start
  exact ⟨es,start,finish,transparent_route_forward _ es nonempty turns,
    transparent_route_labelling _ es nonempty turns⟩
end
end Lamping.AG

import Lamping.Lamping.ComputedFocusMappedPrincipal
import Lamping.Lamping.WholeControlVisitDecomposition

namespace Lamping.AG
open Graph Lambda

section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- A visit is detected by any actual internal segment, in either orientation. -/
theorem WholeControlVisits.positive_of_internal_occurs
    {principal : SiteActionPrincipal site} {es n}
    (visits : WholeControlVisits site principal es n)
    (i : Bool ⊕ (V × Bool)) (occurs : site.internalEnd i ∈ es) : 0<n := by
  by_cases zero : n=0
  · obtain ⟨outside,same⟩ := visits.outside_of_zero site zero _ occurs
    exact False.elim (site.internal_outside_ne i outside same)
  · omega
end

namespace ExposureScheduling
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq W]
variable {g : Net signature N B W} {root : B} {depths : B → Int}
variable {boundary : B → Bool}

/-- The unreversed original connection contains a genuine internal
departure of the returned recipe's site. On the reverse branch it is
the wire mate of the active principal. -/
theorem executableComputedFocusRecipe_internal_occurs {t : Term} {redex : RedexOcc t}
    (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (flow : Nonempty (FlowBalance g boundary)) (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g access.connection.edges=some focus)
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData access.connection focus=some data) :
    ∃ selected, ∃ (recipe : Readback.ExplicitRewriteRecipe (Readback.ExecutableNet.ofNet g) selected.1),
      computeFocusSchema data=some selected ∧
      executableComputedFocusRecipe access inputs balance rootDepth flow focus chosen data computed=
        some ⟨selected.1,recipe⟩ ∧
      ∃ i, recipe.site.internalEnd i ∈ access.connection.edges.map recipe.sourceIso.ends := by
  let route := FocusCorridorData.toTransparentCorridor access.connection focus chosen data computed
  obtain ⟨selected,recipe,table,result,left,_right⟩ :=
    executableComputedFocusRecipe_result access inputs balance rootDepth flow focus chosen data computed
  refine ⟨selected,recipe,table,result,?_⟩
  have partition := computeFocusCorridorData_partition access.connection focus chosen data computed
  have includeRoute (e : Endpoint g) (member : e∈route.edges) : e∈access.connection.edges := by
    change e∈data.edges at member
    rw [partition]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member)))
  cases direction : selected.2 with
  | false =>
    have port := left
    change recipe.sourceIso.ports (orientSchemaCorridor route selected.2).first = _ at port
    rw [direction] at port
    change recipe.sourceIso.ports route.first = _ at port
    obtain ⟨tail,shape⟩ := List.head?_eq_some_iff.mp route.start
    have member : Sum.inl route.first ∈ route.edges := by rw [shape]; simp
    refine ⟨.inl false,List.mem_map.mpr ⟨_,includeRoute _ member,?_⟩⟩
    rw [recipe.sourceIso.node_end,port] <;> rfl
  | true =>
    have port := left
    change recipe.sourceIso.ports (orientSchemaCorridor route selected.2).first = _ at port
    rw [direction] at port
    change recipe.sourceIso.ports route.last = _ at port
    obtain ⟨pref,shape⟩ := List.getLast?_eq_some_iff.mp route.finish
    have member : g.wire (Sum.inl route.last) ∈ route.edges := by rw [shape]; simp
    refine ⟨recipe.site.internal (.inl false),List.mem_map.mpr ⟨_,includeRoute _ member,?_⟩⟩
    have image : recipe.sourceIso.ends (Sum.inl route.last) =
        recipe.site.internalEnd (.inl false) :=
      (recipe.sourceIso.node_end route.last).trans
        (congrArg (fun p => (Sum.inl p : Endpoint recipe.site.net)) port)
    exact (recipe.sourceIso.wiring (Sum.inl route.last)).trans
      ((congrArg (fun e => recipe.site.net.wire e) image).trans
        (recipe.site.internalEnd_wire (.inl false)))
end
end ExposureScheduling
end Lamping.AG

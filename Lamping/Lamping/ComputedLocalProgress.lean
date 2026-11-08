import Lamping.Lamping.ComputedEndpointProgressDispatch
import Lamping.Lamping.ComputedFocusInternalVisit
import Lamping.Lamping.RecipeSiteOriginalWordProgress
import Lamping.Lamping.ActualConnectionListUniqueness

namespace Lamping.AG.ExposureScheduling
open Graph Lambda Lambda.Labelled

/-- Lexicographic decrease of length and inversion count. -/
def ControlWordDecrease (new old : List Bool) : Prop :=
  new.length<old.length ∨ new.length=old.length ∧ inversions new<inversions old

private def ControlOp (op : Op) : Prop := op=.fan ∨ op=.cro ∨ op=.bra

private theorem controlSchemaCase (schema : Schema) (active : ControlOp schema.active) :
    IsCancellation schema ∨ IsAction schema := by
  cases schema with
  | beta _ => simp [ControlOp,Schema.active] at active
  | fanCancel i => exact Or.inl (.fan i)
  | croCancel i => exact Or.inl (.cro i)
  | braCancel i => exact Or.inl (.bra i)
  | fanAction op i j lt => exact Or.inr (.fan op i j lt)
  | croAction op i j lt => exact Or.inr (.cro op i j lt)
  | braAction op i j lt => exact Or.inr (.bra op i j lt)

private theorem orientedControl {selected : Schema × Bool} {left right : Op} {i j : Nat}
    (fit : OrientedControlSchemaFits selected left right i j)
    (lc : ControlOp left) (rc : ControlOp right) :
    ControlOp selected.1.active ∧ ControlOp selected.1.passive := by
  rcases selected with ⟨schema,direction⟩
  cases direction
  · exact ⟨fit.1.symm ▸ lc,fit.2.1.symm ▸ rc⟩
  · exact ⟨fit.1.symm ▸ rc,fit.2.1.symm ▸ lc⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq W]
variable {g : Net signature N B W} {root : B} {depths : B → Int}
variable {directions : B → Bool}

omit [DecidableEq N] [DecidableEq W] in
private theorem internalTableControls (connection : RedexConnection g)
    (index : Nat) (writer reader : ControlOccurrence g)
    (chosen : selectPhysicalControlFocus g connection.edges=some (.internalPeak index writer reader))
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData connection (.internalPeak index writer reader)=some data)
    (selected : Schema × Bool) (table : computeFocusSchema data=some selected) :
    ControlOp selected.1.active ∧ ControlOp selected.1.passive := by
  obtain ⟨left,right,entry,ls,rs,result,fit⟩ :=
    computedInternalPeakSchema connection index writer reader chosen data computed
  have eqEntry : computeFocusSchema data=some entry := by
    simpa only [computeFocusSchema,ls,rs] using result
  have same := Option.some.inj (eqEntry.symm.trans table)
  subst entry
  obtain ⟨a,b,labels⟩ := connection.proper.1
  have spec := selectPhysicalControlFocus_sound g connection.edges
    (.internalPeak index writer reader) chosen
  obtain ⟨l,tagL,lc,_writer,_reader⟩ :=
    ControlOccurrence.principal_roles labels writer (List.mem_of_getElem? spec.1)
  obtain ⟨r,tagR,rc,_,readerRole⟩ :=
    ControlOccurrence.principal_roles labels reader (List.mem_of_getElem? spec.2.1)
  obtain ⟨incoming,arrives,_principal⟩ := readerRole spec.2.2.2.1
  have wire : g.wire reader.entry=Sum.inl (Sigma.mk reader.node incoming) := arrives
  have shape := computed
  simp only [computeFocusCorridorData,wire,nodePortOfEndpoint,Option.map_some,
    Option.some.injEq] at shape
  subst data
  have leftEq : l=left := Kind.op.inj (tagL.symm.trans ls)
  have rightEq : r=right := Kind.op.inj (tagR.symm.trans rs)
  exact orientedControl fit (leftEq ▸ lc) (rightEq ▸ rc)

/-- Every computed nonempty focus gives a strict successor at its actual
returned recipe target for the same syntactic redex. -/
theorem computedLocalProgress {current : LTerm} {redex : RedexOcc current.erase}
    (access : ActualRedexAccess g root redex) (matching : Matches g root current.erase)
    (closed : Closed current.erase) (inputs : RootInputs g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (flow : Nonempty (FlowBalance g directions)) (positive : directions root=true)
    (oldT : Transparency g root)
    (appStamp lamStamp : Lambda.Labelled.Label) (body arg : LTerm)
    (lookup : current.subterm redex.val=some (.app appStamp (.lam lamStamp body) arg))
    (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g access.connection.edges=some focus)
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData access.connection focus=some data) :
    ∃ schema, ∃ (recipe : Readback.ExplicitRewriteRecipe (Readback.ExecutableNet.ofNet g) schema),
      executableComputedFocusRecipe access inputs balance rootDepth flow focus chosen data computed=
        some ⟨schema,recipe⟩ ∧
      ∃ target : ActualRedexAccess recipe.target.graph.net root redex,
        ControlWordDecrease (controlWord recipe.target.graph.net target.connection.edges)
          (controlWord g access.connection.edges) := by
  cases focus with
  | initialReader reader =>
    obtain ⟨schema,recipe,run,target,strict⟩ := computedEndpointProgress access matching inputs
      balance rootDepth flow positive oldT (.initialReader reader) chosen data computed trivial
    exact ⟨schema,recipe,run,target,Or.inl strict⟩
  | terminalWriter writer =>
    obtain ⟨schema,recipe,run,target,strict⟩ := computedEndpointProgress access matching inputs
      balance rootDepth flow positive oldT (.terminalWriter writer) chosen data computed trivial
    exact ⟨schema,recipe,run,target,Or.inl strict⟩
  | internalPeak index writer reader =>
    let focus : PhysicalControlFocus g := .internalPeak index writer reader
    obtain ⟨selected,recipe,table,run,principal,_route,_partition⟩ :=
      executableComputedFocusRecipe_mapped_principal access inputs balance rootDepth flow focus
        chosen data computed
    obtain ⟨other,otherRecipe,otherTable,otherRun,internal,member⟩ :=
      executableComputedFocusRecipe_internal_occurs access inputs balance rootDepth flow focus
        chosen data computed
    have same := Option.some.inj (otherTable.symm.trans table)
    subst other
    have sameRecipe : otherRecipe=recipe :=
      eq_of_heq (Sigma.mk.inj (Option.some.inj (otherRun.symm.trans run))).2
    subst otherRecipe
    obtain ⟨active,passive⟩ :=
      internalTableControls access.connection index writer reader chosen data computed selected table
    rcases controlSchemaCase selected.1 active with cancel | action
    · obtain ⟨target,strict⟩ := recipe.cancellationProgress_original cancel closed access
        matching inputs flow positive ⟨balance⟩ rootDepth oldT
        appStamp lamStamp body arg lookup internal member
      exact ⟨_,recipe,run,target,Or.inl strict⟩
    · obtain ⟨target,length,strict⟩ := recipe.internalActionProgress_original (current:=current)
        action active passive access matching inputs flow positive ⟨balance⟩ rootDepth oldT
        principal internal member
      exact ⟨_,recipe,run,target,Or.inr ⟨length,strict⟩⟩

/-- Any fixed target access for this matched occurrence has the same strict
measure, by literal equality of the entire ordered connection. -/
theorem controlWordDecrease_of_same_target {t : Term} {redex : RedexOcc t}
    (target : ActualNet B) (matching : Matches target.net root t)
    (fixed witness : ActualRedexAccess target.net root redex) (old : List Bool)
    (strict : ControlWordDecrease (controlWord target.net witness.connection.edges) old) :
    ControlWordDecrease (controlWord target.net fixed.connection.edges) old := by
  rw [ActualRedexAccess.connection_edges_unique matching fixed witness]
  exact strict
end
end Lamping.AG.ExposureScheduling

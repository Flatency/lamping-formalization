import Lamping.Lamping.ComputedCroAppProgress
import Lamping.Lamping.ComputedBraAppProgress
import Lamping.Lamping.ComputedFanAppProgress
import Lamping.Lamping.ComputedCroLambdaProgress
import Lamping.Lamping.ComputedBraLambdaProgress
import Lamping.Lamping.ComputedFanLambdaProgress

namespace Lamping.AG.ExposureScheduling
open Graph Lambda Lambda.Labelled

private theorem properActionCases (schema : Schema) (passive : Op)
    (proper : passive=.app ∨ passive=.lam)
    (notBeta : schema.active≠.app) (tag : schema.passive=passive) :
    (∃ i j, ∃ (lt : i<j), schema=.fanAction passive i j lt) ∨
    (∃ i j, ∃ (lt : i<j), schema=.croAction passive i j lt) ∨
    (∃ i j, ∃ (lt : i<j), schema=.braAction passive i j lt) := by
  cases schema with
  | beta i => exact False.elim (notBeta rfl)
  | fanCancel i => rcases proper with rfl|rfl <;> cases tag
  | croCancel i => rcases proper with rfl|rfl <;> cases tag
  | braCancel i => rcases proper with rfl|rfl <;> cases tag
  | fanAction op i j lt =>
    change op=passive at tag
    subst op
    exact Or.inl ⟨i,j,lt,rfl⟩
  | croAction op i j lt =>
    change op=passive at tag
    subst op
    exact Or.inr (Or.inl ⟨i,j,lt,rfl⟩)
  | braAction op i j lt =>
    change op=passive at tag
    subst op
    exact Or.inr (Or.inr ⟨i,j,lt,rfl⟩)

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq W]
variable {g : Net signature N B W} {root : B} {depths : B → Int}
variable {directions : B → Bool}

/-- All computed endpoint actions decrease the original control count at the
actual returned recipe target. -/
theorem computedEndpointProgress {current : LTerm} {redex : RedexOcc current.erase}
    (access : ActualRedexAccess g root redex) (matching : Matches g root current.erase)
    (inputs : RootInputs g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (flow : Nonempty (FlowBalance g directions)) (positive : directions root=true)
    (oldT : Transparency g root) (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g access.connection.edges=some focus)
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData access.connection focus=some data)
    (endpoint : match focus with | .internalPeak .. => False | _ => True) :
    ∃ schema, ∃ (recipe : Readback.ExplicitRewriteRecipe (Readback.ExecutableNet.ofNet g) schema),
      executableComputedFocusRecipe access inputs balance rootDepth flow focus chosen data computed=
        some ⟨schema,recipe⟩ ∧
      ∃ target : ActualRedexAccess recipe.target.graph.net root redex,
        (controlWord recipe.target.graph.net target.connection.edges).length <
          (controlWord g access.connection.edges).length := by
  cases focus with
  | internalPeak index writer reader => exact False.elim endpoint
  | initialReader reader =>
    obtain ⟨right,schema,ls,rs,result,fit⟩ :=
      computedInitialReaderSchema access inputs balance rootDepth reader chosen data computed
    have table : computeFocusSchema data=some (schema,true) := by
      simpa only [computeFocusSchema,ls,rs] using result
    have passive : schema.passive=.app := fit.2.1
    have notBeta : schema.active≠.app := by
      cases schema <;> simp_all [Schema.active,Schema.passive]
    rcases properActionCases schema .app (Or.inl rfl) notBeta passive with
      ⟨i,j,lt,rfl⟩ | ⟨i,j,lt,rfl⟩ | ⟨i,j,lt,rfl⟩
    · obtain ⟨recipe,run,successor⟩ := computedFanAppProgress access matching inputs
        balance rootDepth flow positive oldT reader chosen data computed lt table
      exact ⟨_,recipe,run,successor⟩
    · obtain ⟨recipe,run,successor⟩ := computedCroAppProgress access matching inputs
        balance rootDepth flow positive oldT reader chosen data computed lt table
      exact ⟨_,recipe,run,successor⟩
    · obtain ⟨recipe,run,successor⟩ := computedBraAppProgress access matching inputs
        balance rootDepth flow positive oldT reader chosen data computed lt table
      exact ⟨_,recipe,run,successor⟩
  | terminalWriter writer =>
    obtain ⟨left,schema,ls,rs,result,fit⟩ :=
      computedTerminalWriterSchema access.connection balance rootDepth writer chosen data computed
    have table : computeFocusSchema data=some (schema,false) := by
      simpa only [computeFocusSchema,ls,rs] using result
    have passive : schema.passive=.lam := fit.2.1
    have active : schema.active=left := fit.1
    obtain ⟨a,b,labels⟩ := access.connection.proper.1
    have spec := selectPhysicalControlFocus_sound g access.connection.edges
      (.terminalWriter writer) chosen
    have member : writer∈controlOccurrences g access.connection.edges := by
      obtain ⟨pref,split⟩ := List.getLast?_eq_some_iff.mp spec.1
      rw [split]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    obtain ⟨op,sort,control,_writer,_reader⟩ := ControlOccurrence.principal_roles labels writer member
    have shape := computed
    simp only [computeFocusCorridorData,Option.some.injEq] at shape
    subst data
    have same : op=left := Kind.op.inj (sort.symm.trans ls)
    have notBeta : schema.active≠.app := by
      rw [active,←same]
      rcases control with h|h|h <;> simp [h]
    rcases properActionCases schema .lam (Or.inr rfl) notBeta passive with
      ⟨i,j,lt,rfl⟩ | ⟨i,j,lt,rfl⟩ | ⟨i,j,lt,rfl⟩
    · obtain ⟨recipe,run,successor⟩ := computedFanLambdaProgress access matching inputs
        balance rootDepth flow positive oldT writer chosen _ computed lt table
      exact ⟨_,recipe,run,successor⟩
    · obtain ⟨recipe,run,successor⟩ := computedCroLambdaProgress access matching inputs
        balance rootDepth flow positive oldT writer chosen _ computed lt table
      exact ⟨_,recipe,run,successor⟩
    · obtain ⟨recipe,run,successor⟩ := computedBraLambdaProgress access matching inputs
        balance rootDepth flow positive oldT writer chosen _ computed lt table
      exact ⟨_,recipe,run,successor⟩
end
end Lamping.AG.ExposureScheduling

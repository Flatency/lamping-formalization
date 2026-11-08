import Lamping.Lamping.ComputedGivenFamilyStage
import Lamping.Lamping.ExecutableReadback

namespace Lamping.AG.ExposureScheduling
open Graph Lambda Lambda.Labelled Readback

namespace Program

variable {B : Type} [FiniteNames B] {source : ExecutableNet B}

/-- Compose actual programs at the literal executable endpoint. -/
def append {source : ExecutableNet B} (first : ExecutableProgram source) :
    ExecutableProgram first.result → ExecutableProgram source :=
  match first with
  | .stop _ => fun last => last
  | .rewrite recipe tail => fun last => .rewrite recipe (append tail last)
  | .rename target same tail => fun last => .rename target same (append tail last)
termination_by structural first

theorem append_result (first : ExecutableProgram source) (last : ExecutableProgram first.result) :
    (append first last).result=last.result := by
  induction first with
  | stop => rfl
  | rewrite recipe tail ih =>
    simpa only [append, ExecutableProgram.result] using ih last
  | rename target same tail ih =>
    simpa only [append, ExecutableProgram.result] using ih last

theorem append_schemas (first : ExecutableProgram source) (last : ExecutableProgram first.result) :
    (append first last).schemas=first.schemas++last.schemas := by
  induction first with
  | stop => rfl
  | rewrite recipe tail ih =>
    exact congrArg (fun schemas => _ :: schemas) (ih last)
  | rename target same tail ih =>
    simpa only [append, ExecutableProgram.schemas] using ih last

theorem cast_result {target : ExecutableNet B} (same : source=target)
    (program : ExecutableProgram source) : (show ExecutableProgram target from same ▸ program).result=program.result := by
  cases same
  rfl

theorem cast_schemas {target : ExecutableNet B} (same : source=target)
    (program : ExecutableProgram source) : (show ExecutableProgram target from same ▸ program).schemas=program.schemas := by
  cases same
  rfl

end Program

variable {original : LTerm} [DecidableEq (Boundary original.erase)]
variable {directions : Boundary original.erase → Bool}

structure ComputedFamilyReplayState {term : Term}
    (requested : ParallelHistory original.erase term) where
  graph : ExecutableNet (Boundary original.erase)
  program : ExecutableProgram (ExecutableNet.initial original.erase)
  programResult : program.result=graph
  domain : AuxExposureDomain graph.graph (.inl ()) term directions
  aligned : ∃ (current : LTerm) (schemas : List Schema)
      (raw : ParallelHistory original.erase current.erase) (endpoint : current.erase=term),
    LabelledGraphProjection (ActualNet.initial original.erase) graph.graph (.inl ())
      schemas original current raw ∧ PermEq (endpoint ▸ raw) requested ∧ schemas=program.schemas

/-- The runtime target is computed from the actual graph and the requested
selection. The labelled state is used only to verify the computation. -/
def ComputedFamilyReplayState.advance {t u : Term} {F : List Path}
    {prior : ParallelHistory original.erase t}
    (state : ComputedFamilyReplayState (directions := directions) prior)
    (initial : INIT original) (closed : Closed original.erase)
    (given : ParallelStep F t u) (family : CompleteFamilyStep prior given) :
    ComputedFamilyReplayState (directions := directions) (prior.append (.single given)) := by
  have labelled : ∀ r : RedexOcc t, LabelledExposureOccurrence t r := by
    obtain ⟨current,_schemas,_raw,endpoint,projection,_perm,_schemasExact⟩ := state.aligned
    cases endpoint
    exact fun r => labelledExposureOccurrence_of_redex current (projection.label_history.closed closed) r
  let exposed := computeGivenFamilyExposure state.graph state.domain family labelled
  let beta : ExecutableProgram exposed.target :=
    .rewrite exposed.betaRecipe (.stop exposed.betaRecipe.target)
  let batch := Program.append exposed.program (exposed.programResult.symm ▸ beta)
  let program := Program.append state.program (state.programResult.symm ▸ batch)
  have result : program.result=exposed.betaRecipe.target := by
    change (Program.append state.program (state.programResult.symm ▸ batch)).result=_
    rw [Program.append_result,Program.cast_result]
    change (Program.append exposed.program (exposed.programResult.symm ▸ beta)).result=_
    rw [Program.append_result,Program.cast_result] <;> rfl
  have programSchemas :
      program.schemas=(state.program.schemas++exposed.schemas)++[.beta exposed.access.connection.appIndex] := by
    change (Program.append state.program (state.programResult.symm ▸ batch)).schemas=_
    rw [Program.append_schemas,Program.cast_schemas]
    change state.program.schemas++(Program.append exposed.program (exposed.programResult.symm ▸ beta)).schemas=_
    rw [Program.append_schemas,Program.cast_schemas,exposed.programSchemas,List.append_assoc] <;> rfl
  have sound :
      AuxExposureDomain exposed.betaRecipe.target.graph (.inl ()) u directions ∧
      (∃ (current : LTerm) (schemas : List Schema)
        (raw : ParallelHistory original.erase current.erase) (endpoint : current.erase=u),
        LabelledGraphProjection (ActualNet.initial original.erase) exposed.betaRecipe.target.graph
          (.inl ()) schemas original current raw ∧
        PermEq (endpoint ▸ raw) (prior.append (.single given)) ∧ schemas=program.schemas) := by
    obtain ⟨current,schemas,raw,endpoint,projection,perm,schemasExact⟩ := state.aligned
    cases endpoint
    obtain ⟨target,nextRaw,nextEndpoint,nextProjection,nextPerm,nextDomain⟩ :=
      computedGivenFamilyStage state.graph initial closed projection state.domain prior perm given family
    exact ⟨nextDomain,⟨target,_,nextRaw,nextEndpoint,nextProjection,nextPerm,
      (congrArg (fun earlierSchemas : List Schema =>
        (earlierSchemas++exposed.schemas)++[.beta exposed.access.connection.appIndex])
        schemasExact).trans programSchemas.symm⟩⟩
  exact ⟨exposed.betaRecipe.target,program,result,sound.1,sound.2⟩

/-- Empty requested selections advance the verification index while retaining
the executable graph exactly. -/
def ComputedFamilyReplayState.skip {t u : Term}
    {prior : ParallelHistory original.erase t}
    (state : ComputedFamilyReplayState (directions := directions) prior)
    (given : ParallelStep [] t u) :
    ComputedFamilyReplayState (directions := directions) (prior.append (.single given)) := by
  have endpoint : u=t := given.endpoint (ParallelStep.empty t)
  subst u
  refine ⟨state.graph,state.program,state.programResult,state.domain,?_⟩
  obtain ⟨current,schemas,raw,eq,projection,perm,schemasExact⟩ := state.aligned
  refine ⟨current,schemas,raw,eq,projection,.trans perm ?_,schemasExact⟩
  have deleted := PermEq.prepend prior (PermEq.empty given)
  rw [ParallelHistory.append_nil] at deleted
  exact deleted.symm

/-- Replay an actual finite history value. Its certificate checks each
requested selection at its prescribed prefix and is erased by execution. -/
def replayComputedFamilyHistory {t u : Term}
    (suffix : ParallelHistory t u)
    (prior : ParallelHistory original.erase t)
    (state : ComputedFamilyReplayState (directions := directions) prior)
    (certified : FamilyStepsOrSilent prior suffix)
    (initial : INIT original) (closed : Closed original.erase) :
    ComputedFamilyReplayState (directions := directions) (prior.append suffix) :=
  (match (motive := (start finish : Term) → (history : ParallelHistory start finish) →
      (earlier : ParallelHistory original.erase start) →
      ComputedFamilyReplayState (directions := directions) earlier →
      FamilyStepsOrSilent earlier history →
      ComputedFamilyReplayState (directions := directions) (earlier.append history))
      t, u, suffix with
  | _, _, .nil _ => fun prior state _ => by
    simpa only [ParallelHistory.append_nil] using state
  | _, _, @ParallelHistory.cons t middle target F given tail => fun prior state certified => by
    have head : F=[] ∨ CompleteFamilyStep prior given := by
      cases certified with
      | cons head _ => exact head
    have rest : FamilyStepsOrSilent (prior.append (.single given)) tail := by
      cases certified with
      | cons _ rest => exact rest
    let next : ComputedFamilyReplayState (directions := directions) (prior.append (.single given)) :=
      if empty : F=[] then by
        subst F
        exact state.skip given
      else
        state.advance initial closed given (head.resolve_left empty)
    simpa only [ParallelHistory.append_assoc,ParallelHistory.single,ParallelHistory.append] using
      replayComputedFamilyHistory tail (prior.append (.single given)) next rest initial closed) prior state certified
termination_by structural suffix

private theorem familySuffix_snoc {m t u v : Term} {F : List Path}
    {prior : ParallelHistory m t} {suffix : ParallelHistory t u}
    (valid : FamilyStepsOrSilent prior suffix) (step : ParallelStep F u v)
    (whole : CompleteFamilyStep (prior.append suffix) step) :
    FamilyStepsOrSilent prior (suffix.append (.single step)) := by
  induction valid with
  | nil prior =>
    exact .cons (.inr (by simpa only [ParallelHistory.append_nil] using whole)) (.nil _)
  | cons head rest ih =>
    apply FamilyStepsOrSilent.cons head
    apply ih
    simpa only [ParallelHistory.append_assoc,ParallelHistory.single,ParallelHistory.append] using whole

private theorem completeFamilySuffix {m t : Term} {history : ParallelHistory m t}
    (complete : CompleteDerivation history) : FamilyStepsOrSilent (.nil m) history := by
  induction complete with
  | nil => exact .nil _
  | step _ whole ih => exact familySuffix_snoc ih _ whole

omit [DecidableEq (Boundary original.erase)] in
/-- Realize the supplied finite complete history as one actual program
from the closed initial executable encoding. -/
theorem finiteCompleteHistoryExecutable (initial : INIT original) (closed : Closed original.erase)
    {last : Term} (requested : ParallelHistory original.erase last)
    (complete : CompleteDerivation requested) :
    ∃ program : ExecutableProgram (ExecutableNet.initial original.erase),
      readbackProgram original.erase closed program=last ∧
      ∃ (current : LTerm) (raw : ParallelHistory original.erase current.erase)
        (erased : current.erase=last),
        LabelledGraphProjection (ActualNet.initial original.erase) program.result.graph (.inl ())
          program.schemas original current raw ∧ PermEq (erased ▸ raw) requested := by
  let graph := ExecutableNet.initial original.erase
  have domain : AuxExposureDomain graph.graph (.inl ()) original.erase initialBoundaryPolarity :=
    ⟨(encode_closed_independence original.erase closed 0).rootInputs,
      encode_closed_matches original.erase closed 0,encode_closed_transparency original.erase closed 0,
      encode_flowBalance original.erase 0,rfl,boundaryDepthAt 0,rfl,encode_indexed_balance original.erase 0⟩
  let start : ComputedFamilyReplayState (original := original)
      (directions := initialBoundaryPolarity) (.nil original.erase) :=
    ⟨graph,.stop graph,rfl,domain,original,[],.nil _,rfl,.iso (.refl _),.refl _,rfl⟩
  let finish := replayComputedFamilyHistory requested (.nil _) start (completeFamilySuffix complete)
    initial closed
  obtain ⟨current,schemas,raw,erased,projection,permutation,schemasExact⟩ := finish.aligned
  have matchFinal : Matches finish.program.result.graph.net (.inl ()) last := by
    rw [finish.programResult]
    exact finish.domain.matching
  refine ⟨finish.program,readbackProgram_eq_of_matches original.erase closed finish.program matchFinal,
    current,raw,erased,?_,permutation⟩
  rw [finish.programResult,←schemasExact]
  exact projection

end Lamping.AG.ExposureScheduling

import Lamping.Lamping.ReadbackTermination
import Lamping.Lamping.ReadbackEffectiveRun
import Lamping.Lamping.ExecutableRewritePrograms
import Lamping.Lamping.ReachableTransparency

namespace Lamping.AG.Readback
open Graph Lambda

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

/-- A proof-only semantic domain. This is neither a field of the graph nor
data from which the executable output is selected. -/
def ReadbackDomain (g : Net signature N B W) (root : B) : Prop :=
  RootInputs g root ∧Transparency g root ∧∃ term,Matches g root term

variable [DecidableEq N] [DecidableEq B] [DecidableEq W]
variable {g : Net signature N B W} {root : B}

theorem ReadbackDomain.successful (domain : ReadbackDomain g root) :
    ∃ fuel term,machineFuel g fuel (initialState g root)=.done term := by
  obtain ⟨inputs,transparency,term,matching⟩ := domain
  obtain ⟨fuel,run⟩ := readbackFuel_terminates matching inputs transparency
  exact ⟨fuel,term,run⟩

/-- Unbounded effective readback. The domain proof is erased; the term is
obtained only by the actual machineStep loop, with no supplied/chosen fuel. -/
def readback (g : Net signature N B W) (root : B) (domain : ReadbackDomain g root) : Term :=
  runCertified g (initialState g root) domain.successful

theorem readback_eq_of_matches (domain : ReadbackDomain g root) {term : Term}
    (matching : Matches g root term) : readback g root domain=term := by
  obtain ⟨fuel,run⟩ := readbackFuel_terminates matching domain.1 domain.2.1
  exact runCertified_of_fuel g domain.successful run

theorem readback_eq_of_fuel (domain : ReadbackDomain g root) {term : Term} {fuel : Nat}
    (run : readbackFuel g root fuel=.done term) : readback g root domain=term :=
  runCertified_of_fuel g domain.successful run

end

namespace ExecutableNet
section
variable {B : Type} [FiniteNames B] [DecidableEq B]

def readback (source : ExecutableNet B) (root : B)
    (domain : ReadbackDomain source.graph.net root) : Term := by
  letI := source.nodeEquality
  letI := source.wireEquality
  exact AG.Readback.readback source.graph.net root domain

theorem readback_eq_of_matches (source : ExecutableNet B) (root : B)
    (domain : ReadbackDomain source.graph.net root) {term : Term}
    (matching : Matches source.graph.net root term) : source.readback root domain=term := by
  letI := source.nodeEquality
  letI := source.wireEquality
  exact AG.Readback.readback_eq_of_matches domain matching

theorem readback_eq_of_fuel (source : ExecutableNet B) (root : B)
    (domain : ReadbackDomain source.graph.net root) {term : Term} {fuel : Nat}
    (run : source.runFuel root fuel=.done term) : source.readback root domain=term := by
  letI := source.nodeEquality
  letI := source.wireEquality
  exact AG.Readback.readback_eq_of_fuel domain run

end
end ExecutableNet

/-- A finite explicit recipe program supplies the semantic proof from its
actual derived trace; intermediate matches and termination are not inputs. -/
theorem initial_program_readback_domain (term : Term) (closed : Closed term)
    (program : ExecutableProgram (ExecutableNet.initial term)) :
    ReadbackDomain program.result.graph.net (.inl ()) := by
  obtain ⟨result,reductions,inputs,matching⟩ := initial_program_soundness term closed program
  exact ⟨inputs,initial_trace_transparency term closed program.result.graph program.schemas program.actual_trace,
    result,matching⟩

/-- Effective endpoint computation followed by actual unbounded readback.
The closedness proof is erased, and no semantic reduct/fuel is chosen. -/
def readbackProgram (term : Term) (closed : Closed term)
    (program : ExecutableProgram (ExecutableNet.initial term)) : Term :=
  program.result.readback (.inl ()) (initial_program_readback_domain term closed program)

theorem readbackProgram_eq_of_matches (term : Term) (closed : Closed term)
    (program : ExecutableProgram (ExecutableNet.initial term)) {result : Term}
    (matching : Matches program.result.graph.net (.inl ()) result) :
    readbackProgram term closed program=result :=
  ExecutableNet.readback_eq_of_matches program.result (.inl ())
    (initial_program_readback_domain term closed program) matching

theorem readbackProgram_eq_of_fuel (term : Term) (closed : Closed term)
    (program : ExecutableProgram (ExecutableNet.initial term)) {result : Term} {fuel : Nat}
    (run : program.runFuel (.inl ()) fuel=.done result) :
    readbackProgram term closed program=result :=
  ExecutableNet.readback_eq_of_fuel program.result (.inl ())
    (initial_program_readback_domain term closed program) run

/-- The program endpoint reads back a genuine beta reduct of the original
closed term and matches that endpoint. This is not arbitrary graph completion. -/
theorem readbackProgram_sound (term : Term) (closed : Closed term)
    (program : ExecutableProgram (ExecutableNet.initial term)) :
    Betas term (readbackProgram term closed program) ∧
      Matches program.result.graph.net (.inl ()) (readbackProgram term closed program) := by
  obtain ⟨result,reductions,inputs,matching⟩ := initial_program_soundness term closed program
  rw [readbackProgram_eq_of_matches term closed program matching]
  exact ⟨reductions,matching⟩

def readbackInitial (term : Term) (closed : Closed term) : Term :=
  readbackProgram term closed (.stop (ExecutableNet.initial term))

theorem readbackInitial_eq (term : Term) (closed : Closed term) :
    readbackInitial term closed=term :=
  readbackProgram_eq_of_matches term closed (.stop (ExecutableNet.initial term))
    (encode_closed_matches term closed 0)

end Lamping.AG.Readback

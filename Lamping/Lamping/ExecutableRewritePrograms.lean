import Lamping.Lamping.ExecutableNetTransport
import Lamping.Lamping.GraphTraceSoundness

namespace Lamping.AG.Readback
open Graph Lambda

section
variable {B : Type} [FiniteNames B]

/-- A finite program contains explicit sites and renamings, rather than an
existential graph trace or a promised readback answer. No search strategy is
asserted here; later exposure algorithms must construct these data. -/
inductive ExecutableProgram : ExecutableNet B → Type 1 where
  | stop (source : ExecutableNet B) : ExecutableProgram source
  | rewrite {source : ExecutableNet B} {schema : Schema}
      (recipe : ExplicitRewriteRecipe source schema)
      (tail : ExecutableProgram recipe.target) : ExecutableProgram source
  | rename {source : ExecutableNet B} (target : ActualNet B)
      (same : NetIso source.graph.net target.net)
      (tail : ExecutableProgram (source.transport target same)) : ExecutableProgram source

namespace ExecutableProgram
def result {source : ExecutableNet B} : ExecutableProgram source → ExecutableNet B
  | .stop source => source
  | .rewrite _ tail => result tail
  | .rename _ _ tail => result tail

def schemas {source : ExecutableNet B} : ExecutableProgram source → List Schema
  | .stop _ => []
  | .rewrite (schema:=schema) _ tail => schema::schemas tail
  | .rename _ _ tail => schemas tail

/-- The erased trace is derived from each supplied actual site, including
zero-step carrier changes; it is not an input field of the program. -/
theorem actual_trace {source : ExecutableNet B} (program : ExecutableProgram source) :
    GraphTrace source.graph program.result.graph program.schemas := by
  induction program with
  | stop source => exact .refl source.graph
  | rewrite recipe tail ih => exact .cons recipe.actual_step ih
  | rename target same tail ih => exact ih.iso_source same

def runFuel [DecidableEq B] {source : ExecutableNet B}
    (program : ExecutableProgram source) (root : B) (fuel : Nat) : MachineRun program.result.graph.net :=
  program.result.runFuel root fuel

end ExecutableProgram
end

/-- Every explicitly executed finite recipe program from a closed encoding
supplies the P06 semantic witnesses at its computed effective endpoint.
Readback correctness and termination still require the P10 machine proof. -/
theorem initial_program_soundness (term : Term) (closed : Closed term)
    (program : ExecutableProgram (ExecutableNet.initial term)) :
    ∃ result,Betas term result ∧RootInputs program.result.graph.net (.inl ()) ∧
      Matches program.result.graph.net (.inl ()) result :=
  initial_trace_soundness term closed program.result.graph program.schemas program.actual_trace

end Lamping.AG.Readback

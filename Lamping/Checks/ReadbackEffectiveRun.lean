import Lamping.Lamping.ReadbackEffectiveRun
import Lamping.Checks.ExecutableRecipes

namespace Lamping.Checks.ReadbackEffectiveRun
open AG Graph Lambda AG.Readback ExecutableRecipes

private abbrev identityNet := (ExecutableNet.initial (.lam (.var 0))).graph.net
local instance : DecidableEq (ExecutableNet.initial (.lam (.var 0))).graph.Node :=
  (ExecutableNet.initial (.lam (.var 0))).nodeEquality
local instance : DecidableEq (ExecutableNet.initial (.lam (.var 0))).graph.Wire :=
  (ExecutableNet.initial (.lam (.var 0))).wireEquality
private theorem identity_success :
    ∃ fuel term,machineFuel identityNet fuel (initialState identityNet (.inl ()))=.done term :=
  ⟨20,.lam (.var 0),rfl⟩

/-- The output is obtained from actual unbounded execution; fuel occurs only
inside the erased domain proof. -/
def actualIdentity : Term :=
  runCertified identityNet (initialState identityNet (.inl ())) identity_success

theorem actual_identity_correct : actualIdentity=.lam (.var 0) :=
  runCertified_of_fuel identityNet identity_success (show machineFuel identityNet 20 _=.done (.lam (.var 0)) from rfl)

private abbrev resultNet := programWithRename.result.graph.net
local instance : DecidableEq programWithRename.result.graph.Node :=
  programWithRename.result.nodeEquality
local instance : DecidableEq programWithRename.result.graph.Wire :=
  programWithRename.result.wireEquality
private theorem result_success :
    ∃ fuel term,machineFuel resultNet fuel (initialState resultNet (.inl ()))=.done term :=
  ⟨60,.lam (.var 0),rfl⟩

/-- A real carrier rename and beta rewrite are consumed by the executable
entry, with no externally supplied runtime fuel. -/
def actualProgramResult : Term :=
  runCertified resultNet (initialState resultNet (.inl ())) result_success

theorem actual_program_result_correct : actualProgramResult=.lam (.var 0) :=
  runCertified_of_fuel resultNet result_success (show machineFuel resultNet 60 _=.done (.lam (.var 0)) from rfl)

#eval actualIdentity == Term.lam (.var 0)
#eval actualProgramResult == Term.lam (.var 0)
#print axioms runOnAccessible
#print axioms runAccessible
#print axioms runCertified
#print axioms runCertified_of_fuel
#print axioms actualIdentity
#print axioms actualProgramResult
#print axioms actual_identity_correct
#print axioms actual_program_result_correct
end Lamping.Checks.ReadbackEffectiveRun

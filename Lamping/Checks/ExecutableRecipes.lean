import Lamping.Lamping.ExecutableNetTransport
import Lamping.Lamping.ExecutableRewritePrograms
import Lamping.Checks.Phase6Projection

namespace Lamping.Checks.ExecutableRecipes
open AG Graph Lambda AG.Readback SoundnessBetaAncestor

theorem transported_bool_comparison :
    @decide (false=true) (boolFlip.transportDecidableEq inferInstance false true)=false := rfl

theorem initial_identity_computes :
    (ExecutableNet.initial (.lam (.var 0))).runFuel (.inl ()) 20=.done (.lam (.var 0)) := by rfl

def canonicalSource : ExecutableNet (Boundary identityApp) :=
  (ExecutableNet.initial identityApp).transport (ActualNet.ofNet actualBetaSite.net) betaEncodingIso

theorem transported_source_computes : canonicalSource.runFuel (.inl ()) 60=.done identityApp := by rfl

/-- A genuine source-carrier isomorphism and real beta site form an explicit
recipe; no extraction from an existential GraphStep is used by the program. -/
def actualRecipe : ExplicitRewriteRecipe (ExecutableNet.initial identityApp) (.beta 0) where
  Kept := _
  OutsideWire := _
  InternalWire := _
  keptFinite := inferInstance
  outsideFinite := inferInstance
  internalFinite := inferInstance
  kept := _
  site := actualBetaSite
  sourceIso := betaEncodingIso

theorem actual_recipe_is_standard_step :
    GraphStep (.beta 0) (ActualNet.initial identityApp) actualRecipe.target.graph :=
  actualRecipe.actual_step

theorem actual_reduced_graph_computes :
    actualRecipe.target.runFuel (.inl ()) 60=.done (.lam (.var 0)) := by rfl

#print axioms Bij.transportDecidableEq
#print axioms ExecutableNet.transport
#print axioms ExplicitRewriteRecipe.target
#print axioms ExplicitRewriteRecipe.actual_step
#print axioms initial_identity_computes
#print axioms transported_source_computes
#print axioms actual_reduced_graph_computes

def canonicalRecipe : ExplicitRewriteRecipe canonicalSource (.beta 0) where
  Kept := _
  OutsideWire := _
  InternalWire := _
  keptFinite := inferInstance
  outsideFinite := inferInstance
  internalFinite := inferInstance
  kept := _
  site := actualBetaSite
  sourceIso := .refl _

def programWithRename : ExecutableProgram (ExecutableNet.initial identityApp) :=
  .rename (ActualNet.ofNet actualBetaSite.net) betaEncodingIso
    (.rewrite canonicalRecipe (.stop _))

theorem renaming_is_not_a_schema_event : programWithRename.schemas=[.beta 0] := rfl

theorem explicit_program_computes_identity :
    programWithRename.runFuel (.inl ()) 60=.done (.lam (.var 0)) := by rfl

theorem explicit_program_has_actual_trace :
    GraphTrace (ActualNet.initial identityApp) programWithRename.result.graph [.beta 0] :=
  programWithRename.actual_trace

theorem explicit_program_constructs_semantics :
    ∃ result,Betas identityApp result ∧RootInputs programWithRename.result.graph.net (.inl ()) ∧
      Matches programWithRename.result.graph.net (.inl ()) result :=
  initial_program_soundness identityApp ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ programWithRename

#print axioms ExecutableProgram.result
#print axioms ExecutableProgram.actual_trace
#print axioms explicit_program_computes_identity
#print axioms explicit_program_constructs_semantics
end Lamping.Checks.ExecutableRecipes

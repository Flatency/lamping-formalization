import Lamping.Lambda.BetaIncidencePreimages
namespace Lamping.Checks.BetaIncidencePreimages
open Lambda Lambda.Labelled SyntaxIncidence
private abbrev body : LTerm := .lam (.atom 3) (.app (.atom 4) (.var (.atom 5) 0) (.var (.atom 6) 1))
private abbrev argumentBody : LTerm := .app (.atom 20) (.var (.atom 9) 0) (.var (.atom 10) 0)
private abbrev argument : LTerm := .lam (.atom 7) argumentBody
private abbrev redex : LTerm := .app (.atom 1) (.lam (.atom 2) body) argument
private abbrev contractum := LTerm.contract (.atom 1) (.atom 2) body argument
private abbrev source : LTerm := .lam (.atom 20) redex
private abbrev target : LTerm := .lam (.atom 20) contractum
private def turn : StepAt [.body] source target := .body (.root _ _ _ _)
private abbrev copyStamp := (Label.atom 6).concat ((Label.atom 2).under.concat (.atom 7))
private def copyLambda : ProperPosition target :=
  ⟨[.body,.body,.arg],Or.inr ⟨copyStamp,argumentBody,rfl⟩⟩
private def copyApp : ProperPosition target :=
  ⟨[.body,.body,.arg,.body],Or.inl ⟨.atom 20,.var (.atom 9) 0,.var (.atom 10) 0,rfl⟩⟩
private def rootLambda : ProperPosition target := ⟨[],Or.inr ⟨.atom 20,contractum,rfl⟩⟩

/-- Both ends of a real strict copied edge have genuine old incidence
preimages. Its parent is itself a created copy root, which is allowed. -/
theorem strict_copy_directed_endpoints :
    ∃ oldSource oldTarget,
      Source source [.body,.arg,.body] oldSource ∧Target source [.body,.arg,.body] oldTarget ∧
      BetaVertexPreimage body argument [.body] source target (some copyLambda) oldSource ∧
      BetaVertexPreimage body argument [.body] source target (some copyApp) oldTarget := by
  have origin : BetaNodePreimage body argument [.body] [.body,.body,.arg,.body] [.body,.arg,.body] :=
    .copied (q := [.body,.arg]) (relative := [.body]) rfl rfl
  have atSource : Source target [.body,.body,.arg,.body] (some copyLambda) :=
    ⟨.body,.lam copyStamp argumentBody,.lamBody copyStamp,rfl,rfl,.body⟩
  obtain ⟨oldSource,oldAtSource,sourceOrigin⟩ := turn.beta_incidence_source_preimage rfl origin
    (current := argumentBody) rfl (by decide) atSource
  obtain ⟨oldTarget,oldAtTarget,targetOrigin⟩ := turn.beta_incidence_target_preimage rfl origin
    (show Target target [.body,.body,.arg,.body] (some copyApp) from Or.inl rfl)
  exact ⟨oldSource,oldTarget,oldAtSource,oldAtTarget,sourceOrigin,targetOrigin⟩

theorem actual_external_source :
    ∃ oldVertex,Source source [] oldVertex ∧
      BetaVertexPreimage body argument [.body] source target none oldVertex := by
  apply turn.beta_incidence_source_preimage rfl
    (.context (by rintro ⟨rest,impossible⟩;cases impossible)) (current := target) rfl
  · decide
  · rfl

private abbrev variableBody : LTerm := .var (.atom 3) 0
private abbrev freeArgument : LTerm := .var (.atom 7) 0
private abbrev freeRedex : LTerm := .app (.atom 1) (.lam (.atom 2) variableBody) freeArgument
private abbrev freeContractum := LTerm.contract (.atom 1) (.atom 2) variableBody freeArgument
private abbrev freeSource : LTerm := .lam (.atom 20) freeRedex
private abbrev freeTarget : LTerm := .lam (.atom 20) freeContractum
private def freeTurn : StepAt [.body] freeSource freeTarget := .body (.root _ _ _ _)
private def currentBinder : ProperPosition freeTarget := ⟨[],Or.inr ⟨.atom 20,freeContractum,rfl⟩⟩
private def removedApp : ProperPosition freeSource :=
  ⟨[.body],Or.inl ⟨.atom 1,.lam (.atom 2) variableBody,freeArgument,rfl⟩⟩

/-- A created variable-copy incoming edge still has its true external
lexical binder target preimage. No notCreated premise belongs here. -/
theorem created_variable_external_binder :
    ∃ oldVertex,Target freeSource [.body,.arg] oldVertex ∧
      BetaVertexPreimage variableBody freeArgument [.body] freeSource freeTarget (some currentBinder) oldVertex := by
  apply freeTurn.beta_incidence_target_preimage rfl
    (.copied (q := []) (relative := []) rfl rfl)
  exact Or.inr ⟨freeContractum.label,0,.atom 20,freeContractum,[],rfl,rfl,rfl,rfl⟩

/-- The source parent of that created edge was removed. It cannot be the
preimage of the new parent, even though target endpoint transport succeeds. -/
theorem created_edge_source_cannot_transport :
    BetaCreatedIncoming variableBody [.body] [.body] ∧
    ¬BetaVertexPreimage variableBody freeArgument [.body] freeSource freeTarget
      (some currentBinder) (some removedApp) := by
  refine ⟨Or.inl rfl,?_⟩
  intro wrong
  cases wrong with
  | proper origin =>
    have equal := origin.unique (.context (by rintro ⟨rest,impossible⟩;cases impossible))
    cases equal
end Lamping.Checks.BetaIncidencePreimages
#print axioms Lamping.Lambda.Labelled.PrerequisitePrefix.target_of_no_edges
#print axioms Lamping.Lambda.Labelled.BetaVertexPreimage.unique
#print axioms Lamping.Lambda.Labelled.StepAt.beta_incidence_target_preimage
#print axioms Lamping.Lambda.Labelled.StepAt.beta_incidence_source_preimage
#print axioms Lamping.Checks.BetaIncidencePreimages.strict_copy_directed_endpoints
#print axioms Lamping.Checks.BetaIncidencePreimages.created_variable_external_binder

import Lamping.Checks.WrappedSuccessfulChains
namespace Lamping.Checks.BraSuccessfulChains
open Lambda Lambda.Labelled
abbrev I : Term := WrappedSuccessfulChains.I
abbrev caller : Term := WrappedSuccessfulChains.caller
abbrev bare : Term := .app (.lam (.app I (.var 0))) caller
abbrev original : LTerm := initLabels bare
abbrev current : LTerm := WrappedSuccessfulChains.contractRoot original
abbrev argumentLabel : Label := ((Label.atom 5).concat (Label.atom 1).under).concat (Label.atom 6)
def actualStep : StepAt [] original current := .root _ _ _ _
def actualHistory : History [[]] original current := .cons actualStep (.nil _)
theorem initial : INIT original := init_is_INIT _
theorem sourceClosed : Closed original.erase := by
  change ((0<2) ∧0<1) ∧(0<1 ∧0<2)
  decide
theorem targetClosed : Closed current.erase := actualHistory.closed sourceClosed
theorem target_shape : current.erase=.app I caller := rfl
/-- There really is another initial syntactic redex. The graph root-fiber
proof must distinguish its function origin, rather than assert uniqueness. -/
theorem initial_redexes : redexPositions original.erase=[[],[.fn,.body]] := rfl
theorem distinct_initial_degrees : original.degreeAt []=some (.atom 1) ∧
    original.degreeAt [.fn,.body]=some (.atom 3) ∧(Label.atom 1)≠(.atom 3) := ⟨rfl,rfl,by decide⟩
abbrev bodyApp : Path := [.arg,.body]
abbrev bodyFunction : Path := [.arg,.body,.fn]
abbrev bodyEdges : List Path := [bodyFunction,[.arg],[.fn]]
abbrev rootEdges : List Path := [[.fn]]
theorem body_app_lookup : ∃fn arg,current.subterm bodyApp=some (.app (.atom 7) fn arg) := ⟨_,_,rfl⟩
theorem variable_lookup : current.subterm bodyFunction=some (.var (.atom 8) 0) := rfl
theorem argument_lambda_lookup : ∃body,current.subterm [.arg]=some (.lam argumentLabel body) := ⟨_,rfl⟩
theorem root_redex_lookup : ∃body arg,current.subterm []=some (.app (((Label.atom 0).concat (Label.atom 1).over).concat (.atom 2)) (.lam (.atom 3) body) arg) := ⟨_,_,rfl⟩
def body_chain : PrerequisiteChain current bodyApp bodyEdges :=
  .app rfl (by intro l b same;cases same)
    (.var (parent:=[.arg]) (rest:=[.fn]) rfl rfl rfl rfl
      (.lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)))
def root_chain : PrerequisiteChain current [] rootEdges := .redex_app rfl
def variable_jump : PrerequisitePrefix current bodyFunction [] [.arg] :=
  .var (parent:=[.arg]) (rest:=[.fn]) rfl rfl rfl rfl .refl
def body_prefix : PrerequisitePrefix current bodyApp [bodyFunction,[.arg]] [] :=
  .app rfl (by intro l b same;cases same)
    (.var (parent:=[.arg]) (rest:=[.fn]) rfl rfl rfl rfl
      (.lam (parent:=[]) (step:=.arg) rfl (by decide) .refl))
theorem first_read : PrerequisiteReadsDirected current bodyApp bodyFunction true :=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
theorem argument_context_read : PrerequisiteReadsDirected current [.arg] [.arg] false :=
  ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
theorem root_read : PrerequisiteReadsDirected current [] [.fn] true :=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
theorem exact_body_labels : bodyEdges.map current.labelAt=[some (.atom 8),some argumentLabel,some (.atom 3)] := rfl
theorem exact_root_labels : rootEdges.map current.labelAt=[some (.atom 3)] := rfl
theorem old_body_lookup : original.subterm [.arg,.body]=current.subterm bodyApp := rfl
theorem old_variable_lookup : original.subterm [.arg,.body,.fn]=current.subterm bodyFunction := rfl
#print axioms initial
#print axioms targetClosed
#print axioms body_chain
#print axioms root_chain
#print axioms body_prefix
#print axioms exact_body_labels
#print axioms distinct_initial_degrees
end Lamping.Checks.BraSuccessfulChains

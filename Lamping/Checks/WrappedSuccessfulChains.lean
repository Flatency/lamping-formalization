import Lamping.Lambda.DirectedReadingCreation
namespace Lamping.Checks.WrappedSuccessfulChains
open Lambda Lambda.Labelled
abbrev I : Term := .lam (.var 0)
abbrev caller : Term := .lam (.app (.var 0) I)
abbrev bare : Term := .app (.app I caller) I
abbrev original : LTerm := initLabels bare
abbrev contractRoot : LTerm →LTerm
  | .app b (.lam a body) arg => LTerm.contract b a body arg
  | t => t
abbrev current : LTerm := match original with
  | .app b fn arg => .app b (contractRoot fn) arg
  | t => t
abbrev functionLabel : Label :=
  (((Label.atom 1).concat (Label.atom 2).over).concat
    (((Label.atom 3).concat (Label.atom 2).under).concat (Label.atom 4)))
def actualStep : StepAt [.fn] original current := .fn (.root _ _ _ _)
def actualHistory : History [[.fn]] original current := .cons actualStep (.nil _)
theorem initial : INIT original := init_is_INIT _
theorem sourceClosed : Closed original.erase := by
  change ((0<1) ∧(0<1 ∧0<2)) ∧0<1
  decide
theorem targetClosed : Closed current.erase := actualHistory.closed sourceClosed
theorem target_shape : current.erase=.app caller I := rfl
abbrev bodyApp : Path := [.fn,.body]
abbrev bodyFunction : Path := [.fn,.body,.fn]
abbrev bodyEdges : List Path := [bodyFunction,[.fn]]
abbrev rootEdges : List Path := [[.fn]]
theorem body_app_lookup : ∃fn arg,current.subterm bodyApp=some (.app (.atom 5) fn arg) := ⟨_,_,rfl⟩
theorem body_function_lookup : current.subterm bodyFunction=some (.var (.atom 6) 0) := rfl
theorem function_lambda_lookup : ∃body,current.subterm [.fn]=some (.lam functionLabel body) := ⟨_,rfl⟩
theorem root_redex_lookup : ∃body arg,current.subterm []=some (.app (.atom 0) (.lam functionLabel body) arg) := ⟨_,_,rfl⟩
/-- The actual body APP reads its variable FUNCTION edge, jumps to the
lexical lambda at [fn], and stops at that applied lambda's redex edge. -/
def body_chain : PrerequisiteChain current bodyApp bodyEdges :=
  .app rfl (by intro l b same;cases same)
    (.var (parent:=[.fn]) (rest:=[.fn]) rfl rfl rfl rfl (.redex_lam (p:=[]) rfl))
def root_chain : PrerequisiteChain current [] rootEdges := .redex_app rfl
/-- This finite prefix exposes the literal first reading and the following
zero-edge variable jump. Its finish is the applied lambda, not the body APP. -/
def body_prefix : PrerequisitePrefix current bodyApp [bodyFunction] [.fn] :=
  .app rfl (by intro l b same;cases same)
    (.var (parent:=[.fn]) (rest:=[.fn]) rfl rfl rfl rfl .refl)
def variable_jump : PrerequisitePrefix current bodyFunction [] [.fn] :=
  .var (parent:=[.fn]) (rest:=[.fn]) rfl rfl rfl rfl .refl
theorem first_read : PrerequisiteReadsDirected current bodyApp bodyFunction true :=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
theorem last_read : PrerequisiteReadsDirected current [.fn] [.fn] false :=
  ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
theorem root_read : PrerequisiteReadsDirected current [] [.fn] true :=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
theorem exact_body_labels : bodyEdges.map current.labelAt=[some (.atom 6),some functionLabel] := rfl
theorem exact_root_labels : rootEdges.map current.labelAt=[some functionLabel] := rfl
theorem same_history_old_body_lookup : original.subterm [.fn,.arg,.body]=current.subterm bodyApp := rfl
theorem same_history_old_variable_lookup : original.subterm [.fn,.arg,.body,.fn]=current.subterm bodyFunction := rfl
theorem root_is_actual_redex : ∃body arg,subtermAt current.erase []=some (.app (.lam body) arg) := ⟨_,_,rfl⟩
#print axioms initial
#print axioms targetClosed
#print axioms body_chain
#print axioms root_chain
#print axioms body_prefix
#print axioms exact_body_labels
end Lamping.Checks.WrappedSuccessfulChains

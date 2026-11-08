import Lamping.Lamping.UncreatedChainIncidence
namespace Lamping.Checks.UncreatedChainIncidence
open Graph Lambda Lambda.Labelled AG
private abbrev a := Label.atom 7
private abbrev identity : LTerm := .lam a (.var a 0)
private abbrev body : LTerm := .var a 0
private abbrev argument : LTerm := .app a (.var a 0) identity
private abbrev source : LTerm := .app a (.lam a (.app a (.lam a body) argument)) identity
private abbrev target : LTerm := .app a (.lam a (LTerm.contract a a body argument)) identity
private def turn : StepAt [.fn,.body] source target := .fn (.body (.root _ _ _ _))
private theorem sourceClosed : Closed source.erase := by
  change ((0<2) ∧((0<1) ∧0<2)) ∧0<1
  decide
private theorem targetClosed : Closed target.erase := by
  change ((0<1) ∧0<2) ∧0<1
  decide
private abbrev edges : List Path := [[.fn,.body,.arg],[.fn,.body,.fn],[.fn]]
private abbrev oldEdges : List Path := [[.fn,.body,.arg,.arg],[.fn,.body,.arg,.fn],[.fn]]
private def chain : PrerequisiteChain target [.fn,.body,.arg] edges :=
  .lam (parent := [.fn,.body]) (step := .arg) rfl (by decide)
    (.app rfl (by intro stamp inner impossible;cases impossible)
      (.var (parent := [.fn]) (rest := [.fn]) rfl rfl rfl rfl (.redex_lam (p := []) rfl)))
private def oldChain : PrerequisiteChain source [.fn,.body,.arg,.arg] oldEdges :=
  .lam (parent := [.fn,.body,.arg]) (step := .arg) rfl (by decide)
    (.app rfl (by intro stamp inner impossible;cases impossible)
      (.var (parent := [.fn]) (rest := [.arg,.fn]) rfl rfl rfl rfl (.redex_lam (p := []) rfl)))
private theorem uncreated (edge : Path) (member : edge∈edges) :
    ¬BetaCreatedIncoming body [.fn,.body] edge := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal | equal <;> subst edge <;> decide
private def origins : BetaEdgePreimages body argument [.fn,.body] edges oldEdges :=
  .cons (.copied (q := []) (relative := [.arg]) rfl rfl)
    (.cons (.copied (q := []) (relative := [.fn]) rfl rfl)
      (.cons (.context (by rintro ⟨rest,impossible⟩;cases impossible)) .nil))

/-- The actual copied ARG/context chain has a bare directed incidence
isomorphism with the explicit old chain. Its maps retain real occurrence
preimages even though all labels repeat. -/
theorem real_copy_context_directed_iso :
    ∃ iso : ChainIncidenceIso (chainSyntaxIncidence target targetClosed edges)
      (chainSyntaxIncidence source sourceClosed oldEdges),
      (∀ edge,BetaNodePreimage body argument [.fn,.body] edge.val.val (iso.edges edge).val.val) ∧
      ∀ vertex,BetaVertexPreimage body argument [.fn,.body] source target vertex.val (iso.vertices vertex).val := by
  obtain ⟨iso,edgeOrigins,vertexOrigins⟩ :=
    uncreated_chain_iso sourceClosed targetClosed turn rfl chain oldChain uncreated origins
  exact ⟨iso,edgeOrigins,vertexOrigins⟩

/-- The automatic entry point reconstructs its own source chain and
directed iso. Neither the old list nor a node/edge bijection is supplied. -/
theorem automatic_old_chain_directed_iso :
    ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed edges)
        (chainSyntaxIncidence source sourceClosed oldEdges) := by
  obtain ⟨oldStart,oldEdges,oldChain,_,_,iso,_,_⟩ :=
    uncreated_chain_incidence sourceClosed targetClosed turn rfl chain uncreated
  exact ⟨oldStart,oldEdges,oldChain,⟨iso⟩⟩

end Lamping.Checks.UncreatedChainIncidence
#print axioms Lamping.AG.uncreated_chain_iso
#print axioms Lamping.AG.uncreated_chain_incidence
#print axioms Lamping.Checks.UncreatedChainIncidence.real_copy_context_directed_iso
#print axioms Lamping.Checks.UncreatedChainIncidence.automatic_old_chain_directed_iso

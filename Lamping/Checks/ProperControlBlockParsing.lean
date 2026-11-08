import Lamping.Lamping.ProperControlBlockParsing
import Lamping.Lamping.ControlPrincipalPrefixes
import Lamping.Lamping.MatchingBetaPrincipalPath
import Lamping.Checks.OldChainBetaFixture
namespace Lamping.Checks.ProperControlBlockParsingChecks
open AG Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private abbrev Regular (block : List (Endpoint g)) : Prop := block≠[] ∧
  (∀ e f,(e,f)∈block.zip block.tail →ControlOnlyTurn (g:=g) e f) ∧
  ∃(node : N) (port : Port (g.label node).sort),
    ((g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) ∧
      block.getLast?=some (g.wire (.inl ⟨node,port⟩))

private theorem principal_regular (beta : BetaEdge g) : Regular beta.principal := by
  refine ⟨?_,?_,beta.lam,beta.lamCtx,Or.inr (congrArg Label.sort beta.lamLabel),beta.principalEnd⟩
  · intro empty
    have start:=beta.principalStart
    rw [empty] at start
    cases start
  · intro e f member
    exact Or.inl (beta.transparent e f member)

private theorem reverse_regular (beta : BetaEdge g) : Regular beta.reverseRoute := by
  have endEq : beta.reverseRoute.getLast?=some (g.wire (.inl ⟨beta.app,beta.appFun⟩)) := by
    simp only [BetaEdge.reverseRoute,List.getLast?_map,List.getLast?_reverse,beta.principalStart,Option.map_some]
  refine ⟨?_,?_,beta.app,beta.appFun,Or.inl (congrArg Label.sort beta.appLabel),endEq⟩
  · intro empty
    rw [empty] at endEq
    cases endEq
  · intro e f member
    exact Or.inl (transparent_reverse_turns beta.principal beta.transparent e f member)

theorem actual_principal_one_unique (beta : BetaEdge g) {other : List (List (Endpoint g))}
    (regular : ∀block∈other,Regular block) (same : other.flatten=beta.principal) :
    other=[beta.principal] := by
  apply proper_ended_control_blocks_unique regular ?_ (by simpa using same)
  intro block member
  have eq : block=beta.principal := by simpa using member
  subst block
  exact principal_regular beta

theorem actual_principal_and_reverse_unique (beta : BetaEdge g) {other : List (List (Endpoint g))}
    (regular : ∀block∈other,Regular block)
    (same : other.flatten=beta.principal++beta.reverseRoute) :
    other=[beta.principal,beta.reverseRoute] := by
  apply proper_ended_control_blocks_unique regular ?_ (by simpa using same)
  intro block member
  rcases List.mem_cons.mp member with rfl|member
  · exact principal_regular beta
  · have eq : block=beta.reverseRoute := by simpa using member
    subst block
    exact reverse_regular beta

theorem merged_proper_blocks_rejected (beta : BetaEdge g) :
    ¬Regular (beta.principal++beta.reverseRoute) := by
  intro merged
  have eq:=actual_principal_and_reverse_unique beta (other:=[beta.principal++beta.reverseRoute])
    (by intro b member;have same : b=beta.principal++beta.reverseRoute := by simpa using member
        subst b;exact merged) (by simp)
  have lengths:=congrArg List.length eq
  simp at lengths

theorem empty_block_not_regular : ¬Regular (g:=g) [] := by
  intro regular
  exact regular.1 rfl
end

/-- The finite parsing premises are inhabited on a real closed encoded beta site.
No new marked CURRENT label or backward REP claim is made. -/
theorem actual_closed_site_parser :
    ∃presentation : PhysicalCorridorPresentation OldChainBetaFixture.net (.beta 0)
      OldChainBetaFixture.app OldChainBetaFixture.lam (.inl ()) (.inl ()),
      ∃ beta : BetaEdge presentation.site.net,
        ∀(other : List (List (Endpoint presentation.site.net))),
          (∀block∈other,Regular block) →
          other.flatten=beta.principal++beta.reverseRoute →
          other=[beta.principal,beta.reverseRoute] := by
  obtain ⟨presentation⟩:=OldChainBetaFixture.actual_presentation
  obtain ⟨beta,_app,_lam⟩:=presentation.site.distinguished_betaEdge_exists
  exact ⟨presentation,beta,fun _ regular same=>actual_principal_and_reverse_unique beta regular same⟩

theorem empty_insertion_flatten_collision {X : Type} :
    ([[]] : List (List X)).flatten=[] ∧([[]] : List (List X))≠[] := ⟨rfl,by simp⟩

#print axioms actual_principal_one_unique
#print axioms actual_principal_and_reverse_unique
#print axioms merged_proper_blocks_rejected
#print axioms empty_block_not_regular
#print axioms actual_closed_site_parser
#print axioms empty_insertion_flatten_collision
end Lamping.Checks.ProperControlBlockParsingChecks

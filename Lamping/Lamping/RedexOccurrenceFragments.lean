import Lamping.Lamping.RedexChainDegrees
import Lamping.Lamping.MatchingBetaPrincipalPath
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}

/-- Actual redex provenance and the occurrence selector identify the SAME
literal function-edge suffix, not just its physical endpoints. -/
theorem ActualRedexAccess.occurrence_fragment_segments
    (matching : Matches g root current.erase) {redex : RedexOcc current.erase}
    (source : ActualRedexAccess g root redex)
    (lookup : current.subterm redex.val=some (.app appStamp (.lam lamStamp body) arg))
    (fragment : OccurrenceFragment current g root (redex.val++[.fn])) :
    fragment.fragment.segments=source.connection.edges := by
  rcases fragment with ⟨sub,env,ctx,occurrence,fragment⟩
  obtain ⟨actualEnv,parentPort,parentOccurrence⟩ := SourceSubterm.of_lookup current lookup [] .external
  have expected : SourceSubterm [] .external current (redex.val++[.fn])
      actualEnv (.appFn appStamp) (.lam lamStamp body) :=
    parentOccurrence.append (.fn .nil)
  obtain ⟨rfl,rfl,rfl⟩ := occurrence.same_occurrence expected
  have whole : fragment.access=source.child :=
    matching.accessWord_injective (fragment.word.trans source.childWord.symm)
  have word : redex.val++[.fn]=accessWord g source.parent.val++[.fn] := by rw [source.parentWord]
  have cut := fragment.child_prefix (term:=.app appStamp (.lam lamStamp body) arg) matching .fn source.parent word
  have literal := congrArg Subtype.val whole
  rw [cut.2,source.split] at literal
  exact List.append_cancel_left literal

theorem canonical_redex_chain_actual (matching : Matches g root current.erase)
    (selection : OccurrenceFragmentSelection current g root)
    {redex : RedexOcc current.erase} (source : ActualRedexAccess g root redex)
    (lookup : current.subterm redex.val=some (.app appStamp (.lam lamStamp body) arg)) :
    canonicalChainImage selection (PrerequisiteChain.redex_app lookup)=[source.connection.edges] := by
  let position : Position current.erase := ⟨redex.val++[.fn],by
    rw [←LTerm.erase_subterm,LTerm.subterm_append,lookup];rfl⟩
  change [(selection position).fragment.segments]=[source.connection.edges]
  exact congrArg (fun xs=>[xs])
    (source.occurrence_fragment_segments matching lookup (selection position))

/-- Literal equality with a supplied principal route determines its physical
pair by actual head and wire(last), without a converse endpoint-only claim. -/
theorem RedexConnection.beta_pair_of_principal (connection : RedexConnection g)
    (beta : BetaEdge g) (same : connection.edges=beta.principal) :
    connection.app=beta.app ∧connection.lam=beta.lam := by
  have heads := connection.start.symm.trans ((congrArg List.head? same).trans beta.principalStart)
  have first := Sum.inl.inj (Option.some.inj heads)
  have app := congrArg Sigma.fst first
  have lasts := connection.finish.symm.trans ((congrArg List.getLast? same).trans beta.principalEnd)
  have arrivals := Option.some.inj lasts
  have ends := congrArg g.wire.mate arrivals
  simp only [Pairing.involutive] at ends
  have last := Sum.inl.inj ends
  exact ⟨app,congrArg Sigma.fst last⟩
end
end Lamping.AG

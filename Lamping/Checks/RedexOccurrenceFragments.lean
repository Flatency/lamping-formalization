import Lamping.Lamping.RedexOccurrenceFragments
import Lamping.Lamping.BetaEncodingIso
import Lamping.Lamping.InitialMatching
import Lamping.Checks.Paths
namespace Lamping.Checks.RedexOccurrenceFragments
open AG Graph Lambda Lambda.Labelled
private def current : LTerm := .app (.atom 9)
  (.lam (.atom 9) (.var (.atom 9) 0)) (.lam (.atom 9) (.var (.atom 9) 0))
private theorem closed : Closed current.erase := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
private def redex : RedexOcc current.erase := ⟨[],_,rfl,True.intro⟩

theorem actual_repeated_labels_not_init : ¬INIT current := by
  intro initial
  have distinct := initial.2
  simp [current,LTerm.labels] at distinct

/-- The actual I I beta carrier internally supplies redex provenance and a
selector even when every current syntax label is the same. -/
theorem actual_redex_piece_and_canonical_chain :
    ∃ source : ActualRedexAccess actualBetaSite.net (.inl ()) redex,
    ∃ selection : OccurrenceFragmentSelection current actualBetaSite.net (.inl ()),
      canonicalChainImage selection (PrerequisiteChain.redex_app (p:=[]) (by rfl))=
        [source.connection.edges] ∧
      ∀ fragment : OccurrenceFragment current actualBetaSite.net (.inl ()) [.fn],
        fragment.fragment.segments=source.connection.edges := by
  have matching : Matches actualBetaSite.net (.inl ()) current.erase :=
    betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  obtain ⟨source⟩ := matching.actual_redex_access redex
  obtain ⟨selection⟩ := matching.occurrence_fragment_selection closed
  refine ⟨source,selection,canonical_redex_chain_actual matching selection source rfl,?_⟩
  intro fragment
  exact source.occurrence_fragment_segments matching rfl fragment

private abbrev beta := Paths.encodedBetaOccurrence
private def connection : RedexConnection actualBetaSite.net where
  app := beta.app
  lam := beta.lam
  appPort := beta.appFun
  lamPort := beta.lamCtx
  appIndex := beta.index
  lamIndex := beta.index
  appLabel := beta.appLabel
  lamLabel := beta.lamLabel
  appPrincipal := beta.appFun_role
  lamPrincipal := beta.lamCtx_role
  edges := beta.principal
  proper := ⟨⟨Context.empty,Context.empty,beta.principal_labeling _⟩,beta.principal_forward⟩
  start := beta.principalStart
  finish := beta.principalEnd
  emptyWord := by rfl

theorem actual_two_segment_principal_reflects_pair :
    connection.app=beta.app ∧connection.lam=beta.lam :=
  connection.beta_pair_of_principal beta rfl

#print axioms ActualRedexAccess.occurrence_fragment_segments
#print axioms canonical_redex_chain_actual
#print axioms RedexConnection.beta_pair_of_principal
#print axioms actual_repeated_labels_not_init
#print axioms actual_redex_piece_and_canonical_chain
#print axioms actual_two_segment_principal_reflects_pair
end Lamping.Checks.RedexOccurrenceFragments

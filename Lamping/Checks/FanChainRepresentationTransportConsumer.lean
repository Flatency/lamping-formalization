import Lamping.Lamping.FanChainRepresentationTransport
import Lamping.Checks.FanVariableReadDispatcherConsumer
namespace Lamping.Checks.FanChainRepresentationTransportConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable
open FanSuccessfulChains hiding current original
open FanLambdaChainPassageConsumer FanCurrentVariableBinderConsumer

/-- Every whole successful chain pair on the actual FIRST fan-lambda site
calls the complete ordered top; this is a local equivalence, not REP truth. -/
theorem actual_arbitrary_chains (principal : SiteActionPrincipal actualFanPresentation.site)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current targetNet (.inl ()))
    {p q : Path} {leftReads rightReads : List Path}
    (first : PrerequisiteChain current p leftReads) (second : PrerequisiteChain current q rightReads) :
    (SameChainRepresentation targetFirst first second ↔SameChainRepresentation sourceFirst first second) ∧
      (SameChainRepresentation targetSecond first second ↔SameChainRepresentation sourceSecond first second) ∧
      (ChainRepresentationInvariant targetClosed targetFirst ↔ChainRepresentationInvariant targetClosed sourceFirst) ∧
      (ChainRepresentationInvariant targetClosed targetSecond ↔ChainRepresentationInvariant targetClosed sourceSecond) := by
  obtain ⟨flow,_,_,transparency,_⟩ := beta_certified
  have actualFlow := actualFanPresentation.sourceIso.flowBalance flow
  have actualT := actualFanPresentation.sourceIso.transparency transparency
  exact ⟨actualFanPresentation.site.fan_lambda_chain_representation
      FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
      actualFlow rfl actualT principal sourceFirst targetFirst first second,
    actualFanPresentation.site.fan_lambda_chain_representation
      FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
      actualFlow rfl actualT principal sourceSecond targetSecond first second,
    actualFanPresentation.site.fan_lambda_chain_invariant
      FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
      actualFlow rfl actualT principal targetClosed sourceFirst targetFirst,
    actualFanPresentation.site.fan_lambda_chain_invariant
      FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
      actualFlow rfl actualT principal targetClosed sourceSecond targetSecond⟩

/-- Four arbitrary legal choices on genuine four/five-edge wholechains.
Forward and reflection are directly invoked on samechain reflexivity.
Cross-choice ordered image equality explicitly uses existing choice independence. -/
theorem actual_complete_pair (principal : SiteActionPrincipal actualFanPresentation.site)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool) :
    SameChainRepresentation targetFirst (actualChain branch) (actualChain branch) ∧
      SameChainRepresentation sourceSecond (actualChain branch) (actualChain branch) ∧
      canonicalChainImage sourceFirst (actualChain branch)=canonicalChainImage sourceSecond (actualChain branch) ∧
      canonicalChainImage targetFirst (actualChain branch)=canonicalChainImage targetSecond (actualChain branch) ∧
      (ChainRepresentationInvariant targetClosed targetFirst ↔ChainRepresentationInvariant targetClosed sourceFirst) ∧
      (ChainRepresentationInvariant targetClosed targetSecond ↔ChainRepresentationInvariant targetClosed sourceSecond) := by
  obtain ⟨flow,_,_,transparency,_⟩ := beta_certified
  have forward := actualFanPresentation.site.fan_lambda_chain_representation_forward
    FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl (actualFanPresentation.sourceIso.transparency transparency)
    principal sourceFirst targetFirst (actualChain branch) (actualChain branch) rfl
  have reflection := actualFanPresentation.site.fan_lambda_chain_representation_reflect
    FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl principal sourceSecond targetSecond
    (actualChain branch) (actualChain branch) rfl
  have clauses := actual_arbitrary_chains principal sourceFirst sourceSecond targetFirst targetSecond
    (actualChain branch) (actualChain branch)
  exact ⟨forward,reflection,
    canonicalChainImage_choice_independent FanLambdaChainPassageConsumer.actual_source_matches sourceFirst sourceSecond (actualChain branch),
    canonicalChainImage_choice_independent FanLambdaChainPassageConsumer.actual_target_matches targetFirst targetSecond (actualChain branch),
    clauses.2.2.1,clauses.2.2.2⟩

/-- Genuine original INIT/history and two-rule trace with both matches,
Transparency, nonempty selectors and 4/5-edge successful chains. Only a chain
clause equivalence is produced; no source invariant, Aux or Joint truth is assumed. -/
theorem actual_reachable_complete_supply :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase ∧
    Transparency sourceNet (.inl ()) ∧
    Nonempty (OccurrenceFragmentSelection current sourceNet (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current targetNet (.inl ())) ∧
    ∃_principal : SiteActionPrincipal actualFanPresentation.site,
      ∀ (sourceFirst sourceSecond : OccurrenceFragmentSelection current sourceNet (.inl ()))
        (targetFirst targetSecond : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool),
        PrerequisiteChain current (starting branch) (fullEdges branch) ∧
        (fullEdges branch).length=(if branch then 5 else 4) ∧
        SameChainRepresentation targetFirst (actualChain branch) (actualChain branch) ∧
        SameChainRepresentation sourceSecond (actualChain branch) (actualChain branch) ∧
        canonicalChainImage sourceFirst (actualChain branch)=canonicalChainImage sourceSecond (actualChain branch) ∧
        canonicalChainImage targetFirst (actualChain branch)=canonicalChainImage targetSecond (actualChain branch) ∧
        (ChainRepresentationInvariant targetClosed targetFirst ↔ChainRepresentationInvariant targetClosed sourceFirst) ∧
        (ChainRepresentationInvariant targetClosed targetSecond ↔ChainRepresentationInvariant targetClosed sourceSecond) := by
  obtain ⟨_flow,_balance,_inputs,transparency,_matching⟩ := beta_certified
  refine ⟨FanSuccessfulChains.initial,sourceClosed,actualHistory,targetClosed,
    FanLambdaChainPassageConsumer.actual_two_step_trace,
    FanLambdaChainPassageConsumer.actual_source_matches,FanLambdaChainPassageConsumer.actual_target_matches,
    actualFanPresentation.sourceIso.transparency transparency,
    FanLambdaChainPassageConsumer.actual_source_matches.occurrence_fragment_selection targetClosed,
    FanLambdaChainPassageConsumer.actual_target_matches.occurrence_fragment_selection targetClosed,?_⟩
  obtain ⟨principal⟩ := actualFanPresentation.site.actionPrincipal_exists
  refine ⟨principal,?_⟩
  intro sourceFirst sourceSecond targetFirst targetSecond branch
  exact ⟨actualChain branch,(by cases branch <;> rfl),
    actual_complete_pair principal sourceFirst sourceSecond targetFirst targetSecond branch⟩
end Lamping.Checks.FanChainRepresentationTransportConsumer
#print axioms Lamping.AG.PathSite.fan_read_same_slot_forward
#print axioms Lamping.AG.PathSite.fan_read_same_slot_reflect
#print axioms Lamping.AG.PathSite.fan_lambda_chain_representation_forward
#print axioms Lamping.AG.PathSite.fan_lambda_chain_representation_reflect
#print axioms Lamping.AG.PathSite.fan_lambda_chain_representation
#print axioms Lamping.AG.PathSite.fan_lambda_chain_invariant
#print axioms Lamping.Checks.FanChainRepresentationTransportConsumer.actual_arbitrary_chains
#print axioms Lamping.Checks.FanChainRepresentationTransportConsumer.actual_complete_pair
#print axioms Lamping.Checks.FanChainRepresentationTransportConsumer.actual_reachable_complete_supply

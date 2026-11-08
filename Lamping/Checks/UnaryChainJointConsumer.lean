import Lamping.Lamping.UnaryChainJointRepresentation
import Lamping.Checks.UnaryOccurrenceConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.UnaryChainJointConsumer.CroLambda
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable

/-- Directly consumes all four local unary lifts. Neither side's Joint truth
is assumed or asserted; successful chains remain actual given finite chains. -/
theorem actual_lifts
    (source : OccurrenceFragmentSelection current croLambda.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current croLambda.site.reduce (.inl ())) :
    (∀ (p q : Path) (left right : List Path)
      (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right),
      SameChainRepresentation target first second ↔SameChainRepresentation source first second) ∧
    (ChainRepresentationInvariant WrappedSuccessfulChains.targetClosed target ↔ChainRepresentationInvariant WrappedSuccessfulChains.targetClosed source) ∧
    (AuxiliarySeparation WrappedSuccessfulChains.targetClosed target ↔AuxiliarySeparation WrappedSuccessfulChains.targetClosed source) ∧
    (JointRepresentation WrappedSuccessfulChains.targetClosed target ↔JointRepresentation WrappedSuccessfulChains.targetClosed source) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := croLambda.site.actionPrincipal_exists
  constructor
  · intro p q left right first second
    exact croLambda.site.unary_chain_representation (IsAction.cro .lam 0 1 (by decide))
      (by intro wrong;cases wrong) (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl
      UnaryBindingReachable.Cro.source_matches UnaryBindingReachable.Cro.target_matches principal source target first second
  constructor
  · exact croLambda.site.unary_chain_invariant (IsAction.cro .lam 0 1 (by decide))
      (by intro wrong;cases wrong) (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl WrappedSuccessfulChains.targetClosed
      UnaryBindingReachable.Cro.source_matches UnaryBindingReachable.Cro.target_matches principal source target
  constructor
  · exact croLambda.site.unary_auxiliary_separation (IsAction.cro .lam 0 1 (by decide))
      (by intro wrong;cases wrong) (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl WrappedSuccessfulChains.targetClosed
      UnaryBindingReachable.Cro.source_matches UnaryBindingReachable.Cro.target_matches principal source target
  · exact croLambda.site.unary_joint_representation (IsAction.cro .lam 0 1 (by decide))
      (by intro wrong;cases wrong) (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl WrappedSuccessfulChains.targetClosed
      UnaryBindingReachable.Cro.source_matches UnaryBindingReachable.Cro.target_matches principal source target

/-- Same original INIT/history and genuine two/four-rule trace, closed current,
both Matches, actual successful body/root chains and nonempty lawful selector
supply precede every local equivalence. This is not a global Joint proof. -/
theorem actual_reachable_transport :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croLambda.site.reduce) [.beta 0,.croAction .lam 0 1 (by decide)] ∧
    Matches croLambda.site.net (.inl ()) current.erase ∧Matches croLambda.site.reduce (.inl ()) current.erase ∧
    Closed current.erase ∧
    PrerequisiteChain current WrappedSuccessfulChains.bodyApp WrappedSuccessfulChains.bodyEdges ∧
    PrerequisiteChain current [] [[.fn]] ∧
    Nonempty (OccurrenceFragmentSelection current croLambda.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current croLambda.site.reduce (.inl ())) ∧
    ∀ (source : OccurrenceFragmentSelection current croLambda.site.net (.inl ()))
      (target : OccurrenceFragmentSelection current croLambda.site.reduce (.inl ())),
    (∀ (p q : Path) (left right : List Path)
      (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right),
      SameChainRepresentation target first second ↔SameChainRepresentation source first second) ∧
    (ChainRepresentationInvariant WrappedSuccessfulChains.targetClosed target ↔ChainRepresentationInvariant WrappedSuccessfulChains.targetClosed source) ∧
    (AuxiliarySeparation WrappedSuccessfulChains.targetClosed target ↔AuxiliarySeparation WrappedSuccessfulChains.targetClosed source) ∧
    (JointRepresentation WrappedSuccessfulChains.targetClosed target ↔JointRepresentation WrappedSuccessfulChains.targetClosed source) := by
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,UnaryBindingConsumer.Cro.actual_two_rule_trace,
    UnaryBindingReachable.Cro.source_matches,UnaryBindingReachable.Cro.target_matches,WrappedSuccessfulChains.targetClosed,WrappedSuccessfulChains.body_chain,WrappedSuccessfulChains.root_chain,
    UnaryBindingReachable.Cro.source_matches.occurrence_fragment_selection WrappedSuccessfulChains.targetClosed,
    UnaryBindingReachable.Cro.target_matches.occurrence_fragment_selection WrappedSuccessfulChains.targetClosed,actual_lifts⟩

#print axioms actual_lifts
#print axioms actual_reachable_transport
end Lamping.Checks.UnaryChainJointConsumer.CroLambda
namespace Lamping.Checks.UnaryChainJointConsumer.CroApp
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable

/-- Directly consumes all four local unary lifts. Neither side's Joint truth
is assumed or asserted; successful chains remain actual given finite chains. -/
theorem actual_lifts
    (source : OccurrenceFragmentSelection current croApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current croApp.site.reduce (.inl ())) :
    (∀ (p q : Path) (left right : List Path)
      (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right),
      SameChainRepresentation target first second ↔SameChainRepresentation source first second) ∧
    (ChainRepresentationInvariant WrappedSuccessfulChains.targetClosed target ↔ChainRepresentationInvariant WrappedSuccessfulChains.targetClosed source) ∧
    (AuxiliarySeparation WrappedSuccessfulChains.targetClosed target ↔AuxiliarySeparation WrappedSuccessfulChains.targetClosed source) ∧
    (JointRepresentation WrappedSuccessfulChains.targetClosed target ↔JointRepresentation WrappedSuccessfulChains.targetClosed source) := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := croApp.site.actionPrincipal_exists
  constructor
  · intro p q left right first second
    exact croApp.site.unary_chain_representation (IsAction.cro .app 0 1 (by decide))
      (by intro wrong;cases wrong) (croApp.sourceIso.flowBalance flow) (.inl ()) rfl
      FunctionWrappedConsumer.source_matches actual_final_matches principal source target first second
  constructor
  · exact croApp.site.unary_chain_invariant (IsAction.cro .app 0 1 (by decide))
      (by intro wrong;cases wrong) (croApp.sourceIso.flowBalance flow) (.inl ()) rfl WrappedSuccessfulChains.targetClosed
      FunctionWrappedConsumer.source_matches actual_final_matches principal source target
  constructor
  · exact croApp.site.unary_auxiliary_separation (IsAction.cro .app 0 1 (by decide))
      (by intro wrong;cases wrong) (croApp.sourceIso.flowBalance flow) (.inl ()) rfl WrappedSuccessfulChains.targetClosed
      FunctionWrappedConsumer.source_matches actual_final_matches principal source target
  · exact croApp.site.unary_joint_representation (IsAction.cro .app 0 1 (by decide))
      (by intro wrong;cases wrong) (croApp.sourceIso.flowBalance flow) (.inl ()) rfl WrappedSuccessfulChains.targetClosed
      FunctionWrappedConsumer.source_matches actual_final_matches principal source target

/-- Same original INIT/history and genuine two/four-rule trace, closed current,
both Matches, actual successful body/root chains and nonempty lawful selector
supply precede every local equivalence. This is not a global Joint proof. -/
theorem actual_reachable_transport :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croApp.site.reduce) [.beta 0,.croAction .lam 0 1 (by decide),.croAction .cro 0 1 (by decide),.croAction .app 0 1 (by decide)] ∧
    Matches croApp.site.net (.inl ()) current.erase ∧Matches croApp.site.reduce (.inl ()) current.erase ∧
    Closed current.erase ∧
    PrerequisiteChain current WrappedSuccessfulChains.bodyApp WrappedSuccessfulChains.bodyEdges ∧
    PrerequisiteChain current [] [[.fn]] ∧
    Nonempty (OccurrenceFragmentSelection current croApp.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current croApp.site.reduce (.inl ())) ∧
    ∀ (source : OccurrenceFragmentSelection current croApp.site.net (.inl ()))
      (target : OccurrenceFragmentSelection current croApp.site.reduce (.inl ())),
    (∀ (p q : Path) (left right : List Path)
      (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right),
      SameChainRepresentation target first second ↔SameChainRepresentation source first second) ∧
    (ChainRepresentationInvariant WrappedSuccessfulChains.targetClosed target ↔ChainRepresentationInvariant WrappedSuccessfulChains.targetClosed source) ∧
    (AuxiliarySeparation WrappedSuccessfulChains.targetClosed target ↔AuxiliarySeparation WrappedSuccessfulChains.targetClosed source) ∧
    (JointRepresentation WrappedSuccessfulChains.targetClosed target ↔JointRepresentation WrappedSuccessfulChains.targetClosed source) := by
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,actual_four_step_trace,
    FunctionWrappedConsumer.source_matches,actual_final_matches,WrappedSuccessfulChains.targetClosed,WrappedSuccessfulChains.body_chain,WrappedSuccessfulChains.root_chain,
    FunctionWrappedConsumer.source_matches.occurrence_fragment_selection WrappedSuccessfulChains.targetClosed,
    actual_final_matches.occurrence_fragment_selection WrappedSuccessfulChains.targetClosed,actual_lifts⟩

#print axioms actual_lifts
#print axioms actual_reachable_transport
end Lamping.Checks.UnaryChainJointConsumer.CroApp
namespace Lamping.Checks.UnaryChainJointConsumer.BraLambda
open AG Graph Lambda Lambda.Labelled BraFunctionReachable

/-- Directly consumes all four local unary lifts. Neither side's Joint truth
is assumed or asserted; successful chains remain actual given finite chains. -/
theorem actual_lifts
    (source : OccurrenceFragmentSelection current braLambda.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current braLambda.site.reduce (.inl ())) :
    (∀ (p q : Path) (left right : List Path)
      (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right),
      SameChainRepresentation target first second ↔SameChainRepresentation source first second) ∧
    (ChainRepresentationInvariant BraSuccessfulChains.targetClosed target ↔ChainRepresentationInvariant BraSuccessfulChains.targetClosed source) ∧
    (AuxiliarySeparation BraSuccessfulChains.targetClosed target ↔AuxiliarySeparation BraSuccessfulChains.targetClosed source) ∧
    (JointRepresentation BraSuccessfulChains.targetClosed target ↔JointRepresentation BraSuccessfulChains.targetClosed source) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := braLambda.site.actionPrincipal_exists
  constructor
  · intro p q left right first second
    exact braLambda.site.unary_chain_representation (IsAction.bra .lam 0 1 (by decide))
      (by intro wrong;cases wrong) (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl
      UnaryBindingReachable.Bra.source_matches UnaryBindingReachable.Bra.target_matches principal source target first second
  constructor
  · exact braLambda.site.unary_chain_invariant (IsAction.bra .lam 0 1 (by decide))
      (by intro wrong;cases wrong) (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl BraSuccessfulChains.targetClosed
      UnaryBindingReachable.Bra.source_matches UnaryBindingReachable.Bra.target_matches principal source target
  constructor
  · exact braLambda.site.unary_auxiliary_separation (IsAction.bra .lam 0 1 (by decide))
      (by intro wrong;cases wrong) (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl BraSuccessfulChains.targetClosed
      UnaryBindingReachable.Bra.source_matches UnaryBindingReachable.Bra.target_matches principal source target
  · exact braLambda.site.unary_joint_representation (IsAction.bra .lam 0 1 (by decide))
      (by intro wrong;cases wrong) (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl BraSuccessfulChains.targetClosed
      UnaryBindingReachable.Bra.source_matches UnaryBindingReachable.Bra.target_matches principal source target

/-- Same original INIT/history and genuine two/four-rule trace, closed current,
both Matches, actual successful body/root chains and nonempty lawful selector
supply precede every local equivalence. This is not a global Joint proof. -/
theorem actual_reachable_transport :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braLambda.site.reduce) [.beta 0,.braAction .lam 0 1 (by decide)] ∧
    Matches braLambda.site.net (.inl ()) current.erase ∧Matches braLambda.site.reduce (.inl ()) current.erase ∧
    Closed current.erase ∧
    PrerequisiteChain current BraSuccessfulChains.bodyApp BraSuccessfulChains.bodyEdges ∧
    PrerequisiteChain current [] [[.fn]] ∧
    Nonempty (OccurrenceFragmentSelection current braLambda.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current braLambda.site.reduce (.inl ())) ∧
    ∀ (source : OccurrenceFragmentSelection current braLambda.site.net (.inl ()))
      (target : OccurrenceFragmentSelection current braLambda.site.reduce (.inl ())),
    (∀ (p q : Path) (left right : List Path)
      (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right),
      SameChainRepresentation target first second ↔SameChainRepresentation source first second) ∧
    (ChainRepresentationInvariant BraSuccessfulChains.targetClosed target ↔ChainRepresentationInvariant BraSuccessfulChains.targetClosed source) ∧
    (AuxiliarySeparation BraSuccessfulChains.targetClosed target ↔AuxiliarySeparation BraSuccessfulChains.targetClosed source) ∧
    (JointRepresentation BraSuccessfulChains.targetClosed target ↔JointRepresentation BraSuccessfulChains.targetClosed source) := by
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,UnaryBindingConsumer.Bra.actual_two_rule_trace,
    UnaryBindingReachable.Bra.source_matches,UnaryBindingReachable.Bra.target_matches,BraSuccessfulChains.targetClosed,BraSuccessfulChains.body_chain,BraSuccessfulChains.root_chain,
    UnaryBindingReachable.Bra.source_matches.occurrence_fragment_selection BraSuccessfulChains.targetClosed,
    UnaryBindingReachable.Bra.target_matches.occurrence_fragment_selection BraSuccessfulChains.targetClosed,actual_lifts⟩

#print axioms actual_lifts
#print axioms actual_reachable_transport
end Lamping.Checks.UnaryChainJointConsumer.BraLambda
namespace Lamping.Checks.UnaryChainJointConsumer.BraApp
open AG Graph Lambda Lambda.Labelled BraFunctionReachable

/-- Directly consumes all four local unary lifts. Neither side's Joint truth
is assumed or asserted; successful chains remain actual given finite chains. -/
theorem actual_lifts
    (source : OccurrenceFragmentSelection current braApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current braApp.site.reduce (.inl ())) :
    (∀ (p q : Path) (left right : List Path)
      (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right),
      SameChainRepresentation target first second ↔SameChainRepresentation source first second) ∧
    (ChainRepresentationInvariant BraSuccessfulChains.targetClosed target ↔ChainRepresentationInvariant BraSuccessfulChains.targetClosed source) ∧
    (AuxiliarySeparation BraSuccessfulChains.targetClosed target ↔AuxiliarySeparation BraSuccessfulChains.targetClosed source) ∧
    (JointRepresentation BraSuccessfulChains.targetClosed target ↔JointRepresentation BraSuccessfulChains.targetClosed source) := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := braApp.site.actionPrincipal_exists
  constructor
  · intro p q left right first second
    exact braApp.site.unary_chain_representation (IsAction.bra .app 0 1 (by decide))
      (by intro wrong;cases wrong) (braApp.sourceIso.flowBalance flow) (.inl ()) rfl
      BraFunctionConsumer.source_matches actual_final_matches principal source target first second
  constructor
  · exact braApp.site.unary_chain_invariant (IsAction.bra .app 0 1 (by decide))
      (by intro wrong;cases wrong) (braApp.sourceIso.flowBalance flow) (.inl ()) rfl BraSuccessfulChains.targetClosed
      BraFunctionConsumer.source_matches actual_final_matches principal source target
  constructor
  · exact braApp.site.unary_auxiliary_separation (IsAction.bra .app 0 1 (by decide))
      (by intro wrong;cases wrong) (braApp.sourceIso.flowBalance flow) (.inl ()) rfl BraSuccessfulChains.targetClosed
      BraFunctionConsumer.source_matches actual_final_matches principal source target
  · exact braApp.site.unary_joint_representation (IsAction.bra .app 0 1 (by decide))
      (by intro wrong;cases wrong) (braApp.sourceIso.flowBalance flow) (.inl ()) rfl BraSuccessfulChains.targetClosed
      BraFunctionConsumer.source_matches actual_final_matches principal source target

/-- Same original INIT/history and genuine two/four-rule trace, closed current,
both Matches, actual successful body/root chains and nonempty lawful selector
supply precede every local equivalence. This is not a global Joint proof. -/
theorem actual_reachable_transport :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braApp.site.reduce) [.beta 0,.braAction .lam 0 1 (by decide),.braAction .cro 0 1 (by decide),.braAction .app 0 1 (by decide)] ∧
    Matches braApp.site.net (.inl ()) current.erase ∧Matches braApp.site.reduce (.inl ()) current.erase ∧
    Closed current.erase ∧
    PrerequisiteChain current BraSuccessfulChains.bodyApp BraSuccessfulChains.bodyEdges ∧
    PrerequisiteChain current [] [[.fn]] ∧
    Nonempty (OccurrenceFragmentSelection current braApp.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current braApp.site.reduce (.inl ())) ∧
    ∀ (source : OccurrenceFragmentSelection current braApp.site.net (.inl ()))
      (target : OccurrenceFragmentSelection current braApp.site.reduce (.inl ())),
    (∀ (p q : Path) (left right : List Path)
      (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right),
      SameChainRepresentation target first second ↔SameChainRepresentation source first second) ∧
    (ChainRepresentationInvariant BraSuccessfulChains.targetClosed target ↔ChainRepresentationInvariant BraSuccessfulChains.targetClosed source) ∧
    (AuxiliarySeparation BraSuccessfulChains.targetClosed target ↔AuxiliarySeparation BraSuccessfulChains.targetClosed source) ∧
    (JointRepresentation BraSuccessfulChains.targetClosed target ↔JointRepresentation BraSuccessfulChains.targetClosed source) := by
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,actual_four_step_trace,
    BraFunctionConsumer.source_matches,actual_final_matches,BraSuccessfulChains.targetClosed,BraSuccessfulChains.body_chain,BraSuccessfulChains.root_chain,
    BraFunctionConsumer.source_matches.occurrence_fragment_selection BraSuccessfulChains.targetClosed,
    actual_final_matches.occurrence_fragment_selection BraSuccessfulChains.targetClosed,actual_lifts⟩

#print axioms actual_lifts
#print axioms actual_reachable_transport
end Lamping.Checks.UnaryChainJointConsumer.BraApp

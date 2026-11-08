import Lamping.Lamping.UnaryOccurrenceDispatcher
import Lamping.Checks.UnaryAppContextConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.UnaryOccurrenceConsumer.CroLambda
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable

/-- This is the complete dispatcher, not a preselected role/class leaf. -/
theorem actual_all_positions
    (source : OccurrenceFragmentSelection current croLambda.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current croLambda.site.reduce (.inl ()))
    (p q : Position current.erase) :
    (target p).fragment.segments=(target q).fragment.segments ↔
      (source p).fragment.segments=(source q).fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := croLambda.site.actionPrincipal_exists
  exact croLambda.site.unary_occurrence_equality (IsAction.cro .lam 0 1 (by decide))
    (by intro wrong;cases wrong) (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl
    UnaryBindingReachable.Cro.source_matches UnaryBindingReachable.Cro.target_matches principal (source p) (target p) (source q) (target q)

/-- Same original INIT and labelled history, actual nonempty graph trace,
two real Matches and actual selector supply precede the full all-position test.
This does not assert that this concrete graph inhabits every finite class. -/
theorem actual_reachable_dispatcher :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croLambda.site.reduce) [.beta 0,.croAction .lam 0 1 (by decide)] ∧
    Matches croLambda.site.net (.inl ()) current.erase ∧Matches croLambda.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current croLambda.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current croLambda.site.reduce (.inl ())) ∧
    ∀ (source : OccurrenceFragmentSelection current croLambda.site.net (.inl ()))
      (target : OccurrenceFragmentSelection current croLambda.site.reduce (.inl ())) (p q : Position current.erase),
      (target p).fragment.segments=(target q).fragment.segments ↔
        (source p).fragment.segments=(source q).fragment.segments := by
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,UnaryBindingConsumer.Cro.actual_two_rule_trace,
    UnaryBindingReachable.Cro.source_matches,UnaryBindingReachable.Cro.target_matches,
    UnaryBindingReachable.Cro.source_matches.occurrence_fragment_selection WrappedSuccessfulChains.targetClosed,
    UnaryBindingReachable.Cro.target_matches.occurrence_fragment_selection WrappedSuccessfulChains.targetClosed,actual_all_positions⟩

#print axioms actual_all_positions
#print axioms actual_reachable_dispatcher
end Lamping.Checks.UnaryOccurrenceConsumer.CroLambda
namespace Lamping.Checks.UnaryOccurrenceConsumer.CroApp
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable

/-- This is the complete dispatcher, not a preselected role/class leaf. -/
theorem actual_all_positions
    (source : OccurrenceFragmentSelection current croApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current croApp.site.reduce (.inl ()))
    (p q : Position current.erase) :
    (target p).fragment.segments=(target q).fragment.segments ↔
      (source p).fragment.segments=(source q).fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := croApp.site.actionPrincipal_exists
  exact croApp.site.unary_occurrence_equality (IsAction.cro .app 0 1 (by decide))
    (by intro wrong;cases wrong) (croApp.sourceIso.flowBalance flow) (.inl ()) rfl
    FunctionWrappedConsumer.source_matches actual_final_matches principal (source p) (target p) (source q) (target q)

/-- Same original INIT and labelled history, actual nonempty graph trace,
two real Matches and actual selector supply precede the full all-position test.
This does not assert that this concrete graph inhabits every finite class. -/
theorem actual_reachable_dispatcher :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croApp.site.reduce) [.beta 0,.croAction .lam 0 1 (by decide),.croAction .cro 0 1 (by decide),.croAction .app 0 1 (by decide)] ∧
    Matches croApp.site.net (.inl ()) current.erase ∧Matches croApp.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current croApp.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current croApp.site.reduce (.inl ())) ∧
    ∀ (source : OccurrenceFragmentSelection current croApp.site.net (.inl ()))
      (target : OccurrenceFragmentSelection current croApp.site.reduce (.inl ())) (p q : Position current.erase),
      (target p).fragment.segments=(target q).fragment.segments ↔
        (source p).fragment.segments=(source q).fragment.segments := by
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,actual_four_step_trace,
    FunctionWrappedConsumer.source_matches,actual_final_matches,
    FunctionWrappedConsumer.source_matches.occurrence_fragment_selection WrappedSuccessfulChains.targetClosed,
    actual_final_matches.occurrence_fragment_selection WrappedSuccessfulChains.targetClosed,actual_all_positions⟩

#print axioms actual_all_positions
#print axioms actual_reachable_dispatcher
end Lamping.Checks.UnaryOccurrenceConsumer.CroApp
namespace Lamping.Checks.UnaryOccurrenceConsumer.BraLambda
open AG Graph Lambda Lambda.Labelled BraFunctionReachable

/-- This is the complete dispatcher, not a preselected role/class leaf. -/
theorem actual_all_positions
    (source : OccurrenceFragmentSelection current braLambda.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current braLambda.site.reduce (.inl ()))
    (p q : Position current.erase) :
    (target p).fragment.segments=(target q).fragment.segments ↔
      (source p).fragment.segments=(source q).fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := braLambda.site.actionPrincipal_exists
  exact braLambda.site.unary_occurrence_equality (IsAction.bra .lam 0 1 (by decide))
    (by intro wrong;cases wrong) (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl
    UnaryBindingReachable.Bra.source_matches UnaryBindingReachable.Bra.target_matches principal (source p) (target p) (source q) (target q)

/-- Same original INIT and labelled history, actual nonempty graph trace,
two real Matches and actual selector supply precede the full all-position test.
This does not assert that this concrete graph inhabits every finite class. -/
theorem actual_reachable_dispatcher :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braLambda.site.reduce) [.beta 0,.braAction .lam 0 1 (by decide)] ∧
    Matches braLambda.site.net (.inl ()) current.erase ∧Matches braLambda.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current braLambda.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current braLambda.site.reduce (.inl ())) ∧
    ∀ (source : OccurrenceFragmentSelection current braLambda.site.net (.inl ()))
      (target : OccurrenceFragmentSelection current braLambda.site.reduce (.inl ())) (p q : Position current.erase),
      (target p).fragment.segments=(target q).fragment.segments ↔
        (source p).fragment.segments=(source q).fragment.segments := by
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,UnaryBindingConsumer.Bra.actual_two_rule_trace,
    UnaryBindingReachable.Bra.source_matches,UnaryBindingReachable.Bra.target_matches,
    UnaryBindingReachable.Bra.source_matches.occurrence_fragment_selection BraSuccessfulChains.targetClosed,
    UnaryBindingReachable.Bra.target_matches.occurrence_fragment_selection BraSuccessfulChains.targetClosed,actual_all_positions⟩

#print axioms actual_all_positions
#print axioms actual_reachable_dispatcher
end Lamping.Checks.UnaryOccurrenceConsumer.BraLambda
namespace Lamping.Checks.UnaryOccurrenceConsumer.BraApp
open AG Graph Lambda Lambda.Labelled BraFunctionReachable

/-- This is the complete dispatcher, not a preselected role/class leaf. -/
theorem actual_all_positions
    (source : OccurrenceFragmentSelection current braApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current braApp.site.reduce (.inl ()))
    (p q : Position current.erase) :
    (target p).fragment.segments=(target q).fragment.segments ↔
      (source p).fragment.segments=(source q).fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := braApp.site.actionPrincipal_exists
  exact braApp.site.unary_occurrence_equality (IsAction.bra .app 0 1 (by decide))
    (by intro wrong;cases wrong) (braApp.sourceIso.flowBalance flow) (.inl ()) rfl
    BraFunctionConsumer.source_matches actual_final_matches principal (source p) (target p) (source q) (target q)

/-- Same original INIT and labelled history, actual nonempty graph trace,
two real Matches and actual selector supply precede the full all-position test.
This does not assert that this concrete graph inhabits every finite class. -/
theorem actual_reachable_dispatcher :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braApp.site.reduce) [.beta 0,.braAction .lam 0 1 (by decide),.braAction .cro 0 1 (by decide),.braAction .app 0 1 (by decide)] ∧
    Matches braApp.site.net (.inl ()) current.erase ∧Matches braApp.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current braApp.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current braApp.site.reduce (.inl ())) ∧
    ∀ (source : OccurrenceFragmentSelection current braApp.site.net (.inl ()))
      (target : OccurrenceFragmentSelection current braApp.site.reduce (.inl ())) (p q : Position current.erase),
      (target p).fragment.segments=(target q).fragment.segments ↔
        (source p).fragment.segments=(source q).fragment.segments := by
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,actual_four_step_trace,
    BraFunctionConsumer.source_matches,actual_final_matches,
    BraFunctionConsumer.source_matches.occurrence_fragment_selection BraSuccessfulChains.targetClosed,
    actual_final_matches.occurrence_fragment_selection BraSuccessfulChains.targetClosed,actual_all_positions⟩

#print axioms actual_all_positions
#print axioms actual_reachable_dispatcher
end Lamping.Checks.UnaryOccurrenceConsumer.BraApp

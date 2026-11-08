import Lamping.Lamping.FanProperOccurrenceCases
import Lamping.Checks.AuxiliaryUndefinedCounterexample
namespace Lamping.Checks.FanProperOccurrenceCasesChecks
open AG Graph Lambda Lambda.Labelled
open FanUndefinedReachable
noncomputable abbrev site := actualFanPresentation.site

def Classified (path : RootAccess site.reduce (.inl ())) : Prop :=
  (∃port : NodePort signature actualFanPresentation.Kept actualFanPresentation.kept,
    path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∨
  ∃copy : Bool,
    path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl copy),.inl ()⟩)) ∨
    path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl copy),lamBind⟩))

theorem actual_access_cases (path : RootAccess site.reduce (.inl ())) : Classified path :=
  site.fan_lam_access_cases path

theorem actual_all_positions (p : Position result.erase) :
    ∃path : RootAccess site.reduce (.inl ()),accessWord site.reduce path.val=p.val ∧Classified path := by
  obtain ⟨path,word,_⟩ := Matches.observation _ actual_final_matches p
  exact ⟨path,word,actual_access_cases path⟩

/-- An actual closed canonical INIT, beta, FAN-lambda corridor and real
Matches supply the classified accesses. No fragment equality is asserted. -/
theorem actual_same_initial_reachable_classification :
    INIT initial ∧Closed term ∧History [[]] initial result ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches site.reduce (.inl ()) result.erase ∧
    ∀p : Position result.erase,
      ∃path : RootAccess site.reduce (.inl ()),accessWord site.reduce path.val=p.val ∧Classified path :=
  ⟨init_is_INIT _,closed,history,actual_two_rule_trace,actual_final_matches,actual_all_positions⟩

#print axioms actual_access_cases
#print axioms actual_all_positions
#print axioms actual_same_initial_reachable_classification
end Lamping.Checks.FanProperOccurrenceCasesChecks

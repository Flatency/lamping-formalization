import Lamping.Lamping.HistoryEndpointAvailability
import Lamping.Checks.AuxiliaryEndpointAvailability
namespace Lamping.Checks.HistoryEndpointAvailabilityChecks
open Lambda Lambda.Labelled AG
open NodeLabelSuffixOriginsChecks
abbrev middle : LTerm := target
abbrev lastArgument : LTerm := .lam (.atom 9) (.var (.atom 10) 0)
abbrev finalArgument : LTerm := LTerm.contract currentArgument.label (.atom 7) (.var (.atom 8) 0) lastArgument
abbrev final : LTerm := .app (.atom 0) (.lam (.atom 1) (.var (.atom 2) 0)) finalArgument

def lastStep : StepAt [.arg] middle final := .arg (.root _ _ _ _)
def labels : History [[.arg],[.arg]] source final :=
  .cons actualStep (.cons lastStep (.nil _))

def trace : BetaNodeHistoryPreimage labels [.arg] [.arg,.arg,.arg] := by
  apply BetaNodeHistoryPreimage.one (step:=actualStep) redex_lookup
    (BetaNodePreimage.copied (q:=[]) (relative:=[.arg]) (old:=lastArgument) (by rfl) (by rfl))
  exact BetaNodeHistoryPreimage.one (step:=lastStep)
    (show middle.subterm [.arg]=some (.app currentArgument.label (.lam (.atom 7) (.var (.atom 8) 0)) lastArgument) from rfl)
    (BetaNodePreimage.copied (q:=[]) (relative:=[]) (old:=lastArgument) (by rfl) (by rfl)) (.nil _ _)

theorem different_degrees : source.degreeAt [.arg]=some (.atom 4) ∧
    middle.degreeAt [.arg]=some (.atom 7) ∧(Label.atom 4)≠(.atom 7) := ⟨rfl,rfl,by decide⟩

def currentFrom : SyntaxIncidence.ProperPosition final :=
  ⟨[],Or.inl ⟨.atom 0,.lam (.atom 1) (.var (.atom 2) 0),finalArgument,rfl⟩⟩
def currentTo : SyntaxIncidence.ProperPosition final :=
  ⟨[.arg],Or.inr ⟨finalArgument.label,.var (.atom 10) 0,rfl⟩⟩
def oldFrom : SyntaxIncidence.ProperPosition source :=
  ⟨[.arg,.arg],Or.inl ⟨.atom 6,.lam (.atom 7) (.var (.atom 8) 0),lastArgument,rfl⟩⟩
def oldTo : SyntaxIncidence.ProperPosition source :=
  ⟨[.arg,.arg,.arg],Or.inr ⟨.atom 9,.var (.atom 10) 0,rfl⟩⟩

theorem fromSpec : SyntaxIncidence.Source final [.arg] (some currentFrom) :=
  ⟨.arg,final,.appArg (.atom 0),rfl,rfl,.arg⟩
theorem toSpec : SyntaxIncidence.Target final [.arg] (some currentTo) := Or.inl rfl

def sourceChain : EndpointChain final (some currentFrom) [[.fn]] := PrerequisiteChain.redex_app (by rfl)
def targetChain : EndpointChain final (some currentTo) [[.arg],[.fn]] := by
  change PrerequisiteChain final ([]++[.arg]) (([]++[.arg])::[[]++[.fn]])
  exact .lam (by rfl) (by decide) (.redex_app (by rfl))

theorem actual_two_step_availability : ∃old oldFromVertex oldToVertex es fs,
    source.subterm [.arg,.arg,.arg]=some old ∧
    SyntaxIncidence.Source source [.arg,.arg,.arg] oldFromVertex ∧
    SyntaxIncidence.Target source [.arg,.arg,.arg] oldToVertex ∧
    EndpointChain source oldFromVertex es ∧EndpointChain source oldToVertex fs :=
  history_edge_endpoint_availability trace (current:=finalArgument) rfl fromSpec toSpec sourceChain targetChain

theorem oldFromSpec : SyntaxIncidence.Source source [.arg,.arg,.arg] (some oldFrom) :=
  ⟨.arg,.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) lastArgument,.appArg (.atom 6),rfl,rfl,.arg⟩
theorem oldToSpec : SyntaxIncidence.Target source [.arg,.arg,.arg] (some oldTo) := Or.inl rfl

def oldSourceChain : EndpointChain source (some oldFrom) [[.arg,.arg,.fn]] :=
  PrerequisiteChain.redex_app (by rfl)
def oldTargetChain : EndpointChain source (some oldTo) [[.arg,.arg,.arg],[.arg,.arg,.fn]] := by
  change PrerequisiteChain source ([.arg,.arg]++[.arg]) (([.arg,.arg]++[.arg])::[[.arg,.arg]++[.fn]])
  exact .lam (by rfl) (by decide) (.redex_app (by rfl))

-- THIS initial edge, not a same-label occurrence: actual incidence and chain
-- uniqueness fix the returned old endpoint lists after the two actual betas.
theorem actual_old_lists : ∃es fs,EndpointChain source (some oldFrom) es ∧
    EndpointChain source (some oldTo) fs ∧es=[[.arg,.arg,.fn]] ∧fs=[[.arg,.arg,.arg],[.arg,.arg,.fn]] := by
  obtain ⟨old,a,b,es,fs,lookup,fromActual,toActual,left,right⟩ := actual_two_step_availability
  have fromEq:=SyntaxIncidence.Source.unique fromActual oldFromSpec
  have toEq:=SyntaxIncidence.Target.unique toActual oldToSpec
  have l : EndpointChain source (some oldFrom) es := fromEq ▸ left
  have r : EndpointChain source (some oldTo) fs := toEq ▸ right
  exact ⟨es,fs,l,r,EndpointChain.unique l oldSourceChain,EndpointChain.unique r oldTargetChain⟩

theorem external_never_successful (es : List Path) : ¬EndpointChain final none es := fun h=>h
#print axioms initial
#print axioms labels
#print axioms trace
#print axioms different_degrees
#print axioms sourceChain
#print axioms targetChain
#print axioms actual_two_step_availability
#print axioms actual_old_lists
#print axioms external_never_successful
end Lamping.Checks.HistoryEndpointAvailabilityChecks

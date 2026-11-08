import Lamping.Lamping.FanArgumentVariableAuxiliary
import Lamping.Checks.FanArgumentVariableReachable
namespace Lamping.Checks.FanArgumentVariableAuxiliaryConsumer
open AG Graph Lambda Lambda.Labelled FanArgumentVariableReachable
noncomputable abbrev sourceNet := outerFan.site.net
noncomputable abbrev targetNet := outerFan.site.reduce
abbrev binderPath (branch : Bool) : Path := if branch then [.arg] else [.fn]
abbrev parentPath (branch : Bool) : Path := binderPath branch++[.body]
abbrev variablePath (branch : Bool) : Path := parentPath branch++[.arg]
def variablePosition (branch : Bool) : SyntaxIncidence.Edge current := ⟨variablePath branch,by cases branch <;> rfl⟩

theorem variableLookup (branch : Bool) : current.subterm (variablePath branch)=some (.var (.atom 9) 0) := by
  cases branch <;> rfl

theorem argumentLookup (branch : Bool) : ∃parent stamp fn,(variablePosition branch).val=parent++[.arg] ∧
    current.subterm parent=some (.app stamp fn (.var (.atom 9) 0)) := by
  exact ⟨parentPath branch,_,_,rfl,by cases branch <;> rfl⟩

def parentVertex (branch : Bool) : SyntaxIncidence.Vertex current :=
  some ⟨parentPath branch,Or.inl ⟨_,_,_,by cases branch <;> rfl⟩⟩
def binderVertex : Bool →SyntaxIncidence.Vertex current
  | false => some ⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
  | true => some ⟨[.arg],Or.inr ⟨_,_,rfl⟩⟩

theorem actualSource (branch : Bool) : SyntaxIncidence.source current (variablePosition branch)=parentVertex branch :=
  SyntaxIncidence.source_eq_of_spec current (variablePosition branch)
    ⟨.arg,_,_,rfl,(by cases branch <;> rfl),.arg⟩

theorem actualTarget (branch : Bool) : SyntaxIncidence.target current currentClosed (variablePosition branch)=binderVertex branch := by
  cases branch <;>
    exact SyntaxIncidence.target_eq_of_spec current currentClosed _
      (Or.inr ⟨_,0,_,_,[.arg],rfl,rfl,rfl,rfl⟩)

abbrev parentEdges (branch : Bool) : List Path := [parentPath branch++[.fn]]
abbrev binderEdges (branch : Bool) : List Path := if branch then [[.arg],[.fn]] else [[.fn]]
def actualParentChain (branch : Bool) : PrerequisiteChain current (parentPath branch) (parentEdges branch) := by
  cases branch <;> exact .redex_app rfl

def actualBinderChain (branch : Bool) : PrerequisiteChain current (binderPath branch) (binderEdges branch) := by
  cases branch
  · exact .redex_lam (p:=[]) rfl
  · exact .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)

theorem actual_auxiliary (branch : Bool) : AuxiliaryAt current (variablePath branch) := by
  constructor
  · rintro ⟨other,a,fn,arg,split,_lookup⟩
    have last := congrArg List.getLast? split
    cases branch <;> simp [variablePath,parentPath,binderPath] at last
  · rintro ⟨a,body,lookup⟩
    rw [variableLookup branch] at lookup
    cases lookup

theorem actual_endpoint_success (branch : Bool) :
    EndpointChain current (SyntaxIncidence.source current (variablePosition branch)) (parentEdges branch) ∧
      EndpointChain current (SyntaxIncidence.target current currentClosed (variablePosition branch)) (binderEdges branch) ∧
      SuccessfulEndpointIso current currentClosed (SyntaxIncidence.source current (variablePosition branch))
        (SyntaxIncidence.source current (variablePosition branch)) ∧
      SuccessfulEndpointIso current currentClosed (SyntaxIncidence.target current currentClosed (variablePosition branch))
        (SyntaxIncidence.target current currentClosed (variablePosition branch)) := by
  rw [actualSource,actualTarget]
  have first : EndpointChain current (parentVertex branch) (parentEdges branch) := actualParentChain branch
  have second : EndpointChain current (binderVertex branch) (binderEdges branch) := by
    cases branch with
    | false => exact actualBinderChain false
    | true => exact actualBinderChain true
  exact ⟨first,second,SuccessfulEndpointIso.refl_of_chain first,SuccessfulEndpointIso.refl_of_chain second⟩

/-- Actual candidate geometry directly calls the natural high top. The
source Joint and two endpoint isos are explicit valid conditions, never truth
claimed for distinct positions or encoded into the graph fixture. -/
theorem actual_conditional_pair (principal : SiteActionPrincipal outerFan.site)
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (target : OccurrenceFragmentSelection current targetNet (.inl ()))
    (sourceJoint : JointRepresentation currentClosed source)
    (leftBranch rightBranch : Bool)
    (sourceIso : SuccessfulEndpointIso current currentClosed (SyntaxIncidence.source current (variablePosition leftBranch))
      (SyntaxIncidence.source current (variablePosition rightBranch)))
    (targetIso : SuccessfulEndpointIso current currentClosed (SyntaxIncidence.target current currentClosed (variablePosition leftBranch))
      (SyntaxIncidence.target current currentClosed (variablePosition rightBranch))) :
    (target (variablePosition leftBranch)).fragment.segments=(target (variablePosition rightBranch)).fragment.segments := by
  obtain ⟨flow,_,_,transparency,_⟩ := beta_certified
  exact outerFan.site.fan_argument_variable_endpoint_equality actual_source_matches actual_target_matches
    (outerFan.sourceIso.flowBalance flow) rfl (outerFan.sourceIso.transparency transparency) principal
    currentClosed source target sourceJoint (variablePosition leftBranch) (variablePosition rightBranch)
    (variableLookup leftBranch) (variableLookup rightBranch) (argumentLookup leftBranch) (argumentLookup rightBranch)
    (by cases leftBranch <;> cases rightBranch <;> rfl) sourceIso targetIso

/-- Four arbitrary legal selections with REAL successful samevertex endpoint
isos. Choice equality is explicitly occurrence uniqueness, not a false
all-occurrence fan transport theorem. SOURCEJoint remains conditional. -/
theorem actual_four_choices (principal : SiteActionPrincipal outerFan.site)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current targetNet (.inl ()))
    (firstIH : JointRepresentation currentClosed sourceFirst)
    (secondIH : JointRepresentation currentClosed sourceSecond) (branch : Bool) :
    (targetFirst (variablePosition branch)).fragment.segments=(targetFirst (variablePosition branch)).fragment.segments ∧
      (targetSecond (variablePosition branch)).fragment.segments=(targetSecond (variablePosition branch)).fragment.segments ∧
      (sourceFirst (variablePosition branch)).fragment.segments=(sourceSecond (variablePosition branch)).fragment.segments ∧
      (targetFirst (variablePosition branch)).fragment.segments=(targetSecond (variablePosition branch)).fragment.segments := by
  have success := actual_endpoint_success branch
  exact ⟨actual_conditional_pair principal sourceFirst targetFirst firstIH branch branch success.2.2.1 success.2.2.2,
    actual_conditional_pair principal sourceSecond targetSecond secondIH branch branch success.2.2.1 success.2.2.2,
    OccurrenceFragment.segments_unique actual_source_matches _ _,
    OccurrenceFragment.segments_unique actual_target_matches _ _⟩

/-- Restricted Aux consequence on the actual physical candidate, separately
invoking the second new high top without supplying old or new piece equality. -/
theorem actual_conditional_separation (principal : SiteActionPrincipal outerFan.site)
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (target : OccurrenceFragmentSelection current targetNet (.inl ()))
    (sourceJoint : JointRepresentation currentClosed source)
    (leftBranch rightBranch : Bool)
    (different : (target (variablePosition leftBranch)).fragment.segments≠(target (variablePosition rightBranch)).fragment.segments) :
    ¬(SuccessfulEndpointIso current currentClosed (SyntaxIncidence.source current (variablePosition leftBranch))
      (SyntaxIncidence.source current (variablePosition rightBranch)) ∧
      SuccessfulEndpointIso current currentClosed (SyntaxIncidence.target current currentClosed (variablePosition leftBranch))
      (SyntaxIncidence.target current currentClosed (variablePosition rightBranch))) := by
  obtain ⟨flow,_,_,transparency,_⟩ := beta_certified
  exact outerFan.site.fan_argument_variable_auxiliary_separation actual_source_matches actual_target_matches
    (outerFan.sourceIso.flowBalance flow) rfl (outerFan.sourceIso.transparency transparency) principal
    currentClosed source target sourceJoint (variablePosition leftBranch) (variablePosition rightBranch)
    (variableLookup leftBranch) (variableLookup rightBranch) (argumentLookup leftBranch) (argumentLookup rightBranch)
    (by cases leftBranch <;> cases rightBranch <;> rfl) different

/-- SAME original INIT and actual two-rule trace; both APP ARG variable
selfpairs have real successful source/target endpoints. No actual SOURCEJoint
or distinct-pair successful iso is asserted. -/
theorem actual_reachable_supply :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet) [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase ∧
    Transparency sourceNet (.inl ()) ∧
    Nonempty (OccurrenceFragmentSelection current sourceNet (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current targetNet (.inl ())) ∧
    (∀branch,AuxiliaryAt current (variablePath branch) ∧
      EndpointChain current (SyntaxIncidence.source current (variablePosition branch)) (parentEdges branch) ∧
      EndpointChain current (SyntaxIncidence.target current currentClosed (variablePosition branch)) (binderEdges branch)) ∧
    ∃_principal : SiteActionPrincipal outerFan.site,
      ∀ (sourceFirst sourceSecond : OccurrenceFragmentSelection current sourceNet (.inl ()))
        (targetFirst targetSecond : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool),
        JointRepresentation currentClosed sourceFirst →JointRepresentation currentClosed sourceSecond →
        (targetFirst (variablePosition branch)).fragment.segments=(targetFirst (variablePosition branch)).fragment.segments ∧
        (targetSecond (variablePosition branch)).fragment.segments=(targetSecond (variablePosition branch)).fragment.segments ∧
        (sourceFirst (variablePosition branch)).fragment.segments=(sourceSecond (variablePosition branch)).fragment.segments ∧
        (targetFirst (variablePosition branch)).fragment.segments=(targetSecond (variablePosition branch)).fragment.segments := by
  obtain ⟨flow,_,_,transparency,_⟩ := beta_certified
  refine ⟨initial,closed,actualHistory,currentClosed,actual_two_step_trace,actual_source_matches,actual_target_matches,
    outerFan.sourceIso.transparency transparency,
    actual_source_matches.occurrence_fragment_selection currentClosed,
    actual_target_matches.occurrence_fragment_selection currentClosed,?_,?_⟩
  · intro branch
    have success := actual_endpoint_success branch
    exact ⟨actual_auxiliary branch,success.1,success.2.1⟩
  · obtain ⟨principal⟩ := outerFan.site.actionPrincipal_exists
    refine ⟨principal,?_⟩
    intro sourceFirst sourceSecond targetFirst targetSecond branch firstIH secondIH
    exact actual_four_choices principal sourceFirst sourceSecond targetFirst targetSecond firstIH secondIH branch
end Lamping.Checks.FanArgumentVariableAuxiliaryConsumer
#print axioms Lamping.AG.PathSite.fan_argument_variable_endpoint_equality
#print axioms Lamping.AG.PathSite.fan_argument_variable_auxiliary_separation
#print axioms Lamping.Checks.FanArgumentVariableAuxiliaryConsumer.actualParentChain
#print axioms Lamping.Checks.FanArgumentVariableAuxiliaryConsumer.actualBinderChain
#print axioms Lamping.Checks.FanArgumentVariableAuxiliaryConsumer.actual_auxiliary
#print axioms Lamping.Checks.FanArgumentVariableAuxiliaryConsumer.actual_endpoint_success
#print axioms Lamping.Checks.FanArgumentVariableAuxiliaryConsumer.actual_conditional_pair
#print axioms Lamping.Checks.FanArgumentVariableAuxiliaryConsumer.actual_four_choices
#print axioms Lamping.Checks.FanArgumentVariableAuxiliaryConsumer.actual_conditional_separation
#print axioms Lamping.Checks.FanArgumentVariableAuxiliaryConsumer.actual_reachable_supply

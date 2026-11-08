import Lamping.Lamping.FanBodyContextNextSlots
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Lamping.GlobalGraphSteps
import Lamping.Checks.WrappedSuccessfulChains
namespace Lamping.Checks.FanBodyContextConsumer
open AG Graph Lambda Lambda.Labelled
abbrev K : Term := .lam (.lam (.var 1))
abbrev bare : Term := .app (.lam (.app (.var 0) (.var 0))) K
abbrev original : LTerm := initLabels bare
abbrev current : LTerm := WrappedSuccessfulChains.contractRoot original
abbrev functionTerm : LTerm := match current with | .app _ fn _ => fn | t => t
abbrev argumentTerm : LTerm := match current with | .app _ _ arg => arg | t => t
abbrev functionBody : LTerm := match functionTerm with | .lam _ body => body | t => t
abbrev argumentBody : LTerm := match argumentTerm with | .lam _ body => body | t => t
abbrev innerBody : LTerm := match functionBody with | .lam _ body => body | t => t
abbrev otherInnerBody : LTerm := match argumentBody with | .lam _ body => body | t => t
abbrev left : Path := [.fn,.body]
abbrev right : Path := [.arg,.body]
abbrev leftEdges : List Path := [left,[.fn]]
abbrev rightEdges : List Path := [right,[.arg],[.fn]]
def actualStep : StepAt [] original current := .root _ _ _ _
def actualHistory : History [[]] original current := .cons actualStep (.nil _)
theorem initial : INIT original := init_is_INIT _
theorem closed : Closed original.erase := by change (0<1 ∧0<1) ∧1<2;decide
theorem targetClosed : Closed current.erase := actualHistory.closed closed
theorem targetShape : current.erase=.app K K := rfl

def leftOccurrence : SourceSubterm [] .external current left [functionTerm.label]
    (.lamBody functionTerm.label) functionBody := .fn (.body .nil)
def rightOccurrence : SourceSubterm [] .external current right [argumentTerm.label]
    (.lamBody argumentTerm.label) argumentBody := .arg (.body .nil)
def leftChain : PrerequisiteChain current left leftEdges :=
  .lam (parent:=[.fn]) (step:=.body) rfl (by decide) (.redex_lam (p:=[]) rfl)
def rightChain : PrerequisiteChain current right rightEdges :=
  .lam (parent:=[.arg]) (step:=.body) rfl (by decide)
    (.lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl))

/-- Genuine generated CURRENT BODY lambda reads: each step consumes [child],
not the zero-edge variable binder jump. The next ordinal is derived by core. -/
theorem actual_current_next_slots :
    (∃ stamp body more,current.subterm [.fn]=some (.lam stamp body) ∧
      PrerequisiteChain current [.fn] more ∧leftEdges[1]?=some [.fn] ∧
      PrerequisitePrefix current left [left] [.fn]) ∧
    (∃ stamp body more,current.subterm [.arg]=some (.lam stamp body) ∧
      PrerequisiteChain current [.arg] more ∧rightEdges[1]?=some [.arg] ∧
      PrerequisitePrefix current right [right] [.arg]) := by
  constructor
  · obtain ⟨parent,stamp,body,more,lexical,lookup,next,slot,segment⟩ :=
      leftChain.body_context_next_slot (n:=0) rfl
        (show current.subterm left=some (.lam functionBody.label innerBody) from rfl)
        leftOccurrence ⟨_,rfl⟩
    have same : parent=[.fn] := (List.append_cancel_right lexical).symm
    rw [same] at lookup next slot segment
    exact ⟨stamp,body,more,lookup,next,slot,segment⟩
  · obtain ⟨parent,stamp,body,more,lexical,lookup,next,slot,segment⟩ :=
      rightChain.body_context_next_slot (n:=0) rfl
        (show current.subterm right=some (.lam argumentBody.label otherInnerBody) from rfl)
        rightOccurrence ⟨_,rfl⟩
    have same : parent=[.arg] := (List.append_cancel_right lexical).symm
    rw [same] at lookup next slot segment
    exact ⟨stamp,body,more,lookup,next,slot,segment⟩

abbrev originalArgument : LTerm := match original with | .app _ _ arg => arg | t => t
abbrev originalArgumentBody : LTerm := match originalArgument with | .lam _ body => body | t => t
abbrev originalInnerBody : LTerm := match originalArgumentBody with | .lam _ body => body | t => t
abbrev initialBody : Path := [.arg,.body]
abbrev initialEdges : List Path := [initialBody,[.arg],[.fn]]
def initialOccurrence : SourceSubterm [] .external original initialBody [originalArgument.label]
    (.lamBody originalArgument.label) originalArgumentBody := .arg (.body .nil)
def initialChain : PrerequisiteChain original initialBody initialEdges :=
  .lam (parent:=[.arg]) (step:=.body) rfl (by decide)
    (.lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl))
def initialPosition : Position original.erase := ⟨initialBody,by rfl⟩
def initialParentPosition : Position original.erase := ⟨[.arg],by rfl⟩
noncomputable abbrev initialNet := (encode 0 original.erase).net
theorem initialMatches : Matches initialNet (.inl ()) original.erase := encode_closed_matches original.erase closed 0

/-- A real physical source is supplied by the original INIT encoding. This
is a zero-rule source stage, NOT an unconstructed fan-action instance. -/
theorem actual_initial_body_source :
    Nonempty (OccurrenceFragmentSelection original initialNet (.inl ())) ∧
    ∀selection : OccurrenceFragmentSelection original initialNet (.inl ()),
      ∃ (parent : RootAccess initialNet (.inl ())) (stamp : Label) (body : LTerm) (more : List Path),
        accessWord initialNet (selection initialPosition).fragment.access.val=initialBody ∧
        accessWord initialNet parent.val=[.arg] ∧
        original.subterm [.arg]=some (.lam stamp body) ∧
        PrerequisiteChain original [.arg] more ∧initialEdges[1]?=some [.arg] ∧
        PrerequisitePrefix original initialBody [initialBody] [.arg] := by
  refine ⟨initialMatches.occurrence_fragment_selection closed,?_⟩
  intro selection
  have ctx := ((selection initialPosition).occurrence.same_occurrence initialOccurrence).2.1
  obtain ⟨parentPath,stamp,body,more,lexical,lookup,next,slot,segment⟩ :=
    initialChain.body_context_next_slot (n:=0) rfl
      (show original.subterm initialBody=some (.lam originalArgumentBody.label originalInnerBody) from rfl)
      (selection initialPosition).occurrence ⟨_,ctx⟩
  have same : parentPath=[.arg] := (List.append_cancel_right lexical).symm
  rw [same] at lookup next slot segment
  obtain ⟨parent,parentWord,_⟩ := Matches.observation initialNet initialMatches initialParentPosition
  exact ⟨parent,stamp,body,more,(selection initialPosition).fragment.word,parentWord,lookup,next,slot,segment⟩

/-- Both original INIT source accesses and generated K K syntax chains are
real, but no actual fan-lambda site/copied Bool path is claimed here. -/
theorem actual_body_next_slot_supply :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧Closed current.erase ∧
    current.erase=.app K K ∧
    GraphTrace (ActualNet.initial original.erase) (ActualNet.ofNet initialNet) [] ∧
    Matches initialNet (.inl ()) original.erase ∧
    Nonempty (OccurrenceFragmentSelection original initialNet (.inl ())) ∧
    PrerequisiteChain current left leftEdges ∧PrerequisiteChain current right rightEdges ∧
    leftEdges.length=2 ∧rightEdges.length=3 ∧
    (∃ stamp body more,current.subterm [.fn]=some (.lam stamp body) ∧
      PrerequisiteChain current [.fn] more ∧leftEdges[1]?=some [.fn] ∧
      PrerequisitePrefix current left [left] [.fn]) ∧
    (∃ stamp body more,current.subterm [.arg]=some (.lam stamp body) ∧
      PrerequisiteChain current [.arg] more ∧rightEdges[1]?=some [.arg] ∧
      PrerequisitePrefix current right [right] [.arg]) := by
  exact ⟨initial,closed,actualHistory,targetClosed,targetShape,.refl _,initialMatches,
    actual_initial_body_source.1,leftChain,rightChain,rfl,rfl,actual_current_next_slots⟩
#print axioms PrerequisiteChain.body_context_next_slot
#print axioms PathSite.fan_body_context_adjacent_branches
#print axioms PathSite.fan_body_context_joint_adjacent_branches
#print axioms actualStep
#print axioms actualHistory
#print axioms initial
#print axioms actual_current_next_slots
#print axioms actual_initial_body_source
#print axioms actual_body_next_slot_supply
end Lamping.Checks.FanBodyContextConsumer

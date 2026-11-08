import Lamping.Lamping.FanCopiedBodyBindingCuts
import Lamping.Checks.FanBodyBindingIdentityReachable
import Lamping.Lamping.FanCurrentVariableBinders
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanCopiedBodyBindingChecks
open AG Graph Lambda Lambda.Labelled FanBodyBindingIdentityReachable
noncomputable abbrev sourceNet := outerFan.site.net
noncomputable abbrev targetNet := outerFan.site.reduce
noncomputable abbrev bodyCut := cut2
abbrev bodyRight := (Schema.fanAction .lam 0 1 (by decide)).right.net
abbrev functionTerm : LTerm := match current with | .app _ f _ => f | t => t
abbrev functionBody : LTerm := match functionTerm with | .lam _ b => b | t => t
abbrev argumentTerm : LTerm := match current with | .app _ _ a => a | t => t
abbrev argumentBody : LTerm := match argumentTerm with | .lam _ b => b | t => t
def bodyPosition : SyntaxIncidence.Edge current := ⟨[.fn,.body],rfl⟩
def bodyOccurrence : SourceSubterm [] .external current bodyPosition.val [functionTerm.label]
    (.lamBody functionTerm.label) functionBody := .fn (.body .nil)
def bodyEdge := sourceEdge [functionTerm.label] (.lamBody functionTerm.label) functionBody
def bodyRole : SourceDeparture functionTerm .body bodyEdge.fromPort := .body
noncomputable def sourceFlow : FlowBalance sourceNet initialBoundaryPolarity :=
  outerFan.sourceIso.flowBalance (Classical.choose beta_certified)
theorem source_inputs_transparency : RootInputs sourceNet (.inl ()) ∧Transparency sourceNet (.inl ()) := by
  obtain ⟨_,_,inputs,transparency,_⟩ := beta_certified
  exact ⟨outerFan.sourceIso.rootInputs inputs,outerFan.sourceIso.transparency transparency⟩

/-- The copied binding finish is DERIVED from the actual CURRENT lexical
binder and its real copied context access, not supplied as a desired profile. -/
theorem actual_binding_finish (leaf : RootAccess targetNet (.inl ()))
    (word : accessWord targetNet leaf.val=bodyPosition.val) :
    leaf.val.getLast?=some (targetNet.wire (.inl ⟨.inr (.inl false),lamBind⟩)) := by
  obtain ⟨loop,a,b,c,binding,ctx,split,_loopWord,_ctxRole,parentFinish,_parentLabels⟩ :=
    actual_target_matches.current_lexical_binding_access
      (show current.subterm bodyPosition.val=some (.var functionBody.label 0) from rfl)
      (parentPath:=[.fn]) (rest:=[]) rfl rfl leaf lambdaParent word lambdaWord
  have wires := Option.some.inj (parentFinish.symm.trans lambdaFinish)
  have ends := congrArg targetNet.wire wires
  simp only [Pairing.involutive] at ends
  have sameNode : binding.binder=.inr (.inl false) := congrArg Sigma.fst (Sum.inl.inj ends)
  have sameBind : (.inl ⟨binding.binder,binding.bind⟩ : Endpoint targetNet)=.inl ⟨.inr (.inl false),lamBind⟩ :=
    congrArg Sum.inl (Sigma.ext sameNode binding.bind_role)
  rw [split,List.getLast?_append,binding.finish,sameBind]
  rfl

/-- Positive actual CC cell: the complete new cut is invoked on THIS whole
labelling and ONE supplied principal, with the returned real pending.middle. -/
theorem actual_direct_cut (principal : SiteActionPrincipal outerFan.site)
    (source : OccurrenceFragment current sourceNet (.inl ()) bodyPosition.val)
    (target : OccurrenceFragment current targetNet (.inl ()) bodyPosition.val) :
    ∃ (a b : Context)
      (pending : PendingRhsBlock bodyCut bodyRight
        (target.fragment.access.val.map (plugEnd (bodyCut).label (bodyRight).label).invFun) a b)
      (rawTail : List (PlugSegment bodyCut bodyRight)) (oldTail : List (Endpoint sourceNet)) (seam : Context),
      Labelling targetNet target.fragment.access.val a b ∧
      source.fragment.segments=.inl ⟨.inr (.inr ()),lamBody⟩::oldTail ∧
      target.fragment.segments.map (plugEnd (bodyCut).label (bodyRight).label).invFun=
        .inr (.inl ⟨.inl false,lamBody⟩):: .inr (.inl ⟨.inr true,.inl ()⟩)::
          .inl (.inr (.inl (.inr (.inr true))))::
          (rawTail++[.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr false⟩)]) ∧
      ActionCanonicalBlocks outerFan.site principal
        (.inl (.inr (.inl (.inr (.inr true))))::rawTail) source.fragment.segments ∧
      PlugLabelling bodyCut bodyRight (.inl (.inr (.inl (.inr (.inr true))))::rawTail) seam pending.middle ∧
      ActionCanonicalBlocks outerFan.site principal pending.pre source.fragment.access.val := by
  rcases source with ⟨sub,env,ctx,occ,source⟩
  obtain ⟨rfl,rfl,rfl⟩ := occ.same_occurrence bodyOccurrence
  rcases target with ⟨sub,env,ctx,tocc,target⟩
  obtain ⟨rfl,rfl,rfl⟩ := tocc.same_occurrence bodyOccurrence
  obtain ⟨parent,parentWord,_⟩ := Matches.observation _ actual_source_matches
    (show Position current.erase from ⟨[.fn],rfl⟩)
  obtain ⟨a,b,labels⟩ := target.access.property.1.1
  obtain ⟨pending,rawTail,oldTail,seam,sourcePiece,shape,relation,pieceLabels,whole,_trim⟩ :=
    source.fan_copied_body_binding_cut outerFan.site sourceFlow (.inl ()) rfl
      actual_source_matches actual_target_matches principal target bodyRole parent lambdaParent
      (by rw [parentWord];rfl) (by change bodyPosition.val=accessWord targetNet lambdaEdges++[.body];rw [lambdaWord];rfl)
      false false lambdaFinish (actual_binding_finish target.access target.word) labels
  refine ⟨a,b,pending,rawTail,oldTail,seam,labels,sourcePiece,shape,?_,pieceLabels,whole⟩
  simpa only [sourcePiece] using relation

/-- All four legal choices at the actual BODY occurrence call complete low
transport. SOURCE equality is internally actual-occurrence uniqueness. -/
theorem actual_four_choices_forward
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current targetNet (.inl ())) :
    (targetFirst bodyPosition).fragment.segments=(targetSecond bodyPosition).fragment.segments := by
  have oldEq := (sourceFirst bodyPosition).segments_unique actual_source_matches (sourceSecond bodyPosition)
  let ls := sourceFirst bodyPosition
  let rs := sourceSecond bodyPosition
  let lt := targetFirst bodyPosition
  let rt := targetSecond bodyPosition
  change lt.fragment.segments=rt.fragment.segments
  change ls.fragment.segments=rs.fragment.segments at oldEq
  rcases ls with ⟨_,_,_,locc,ls⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence bodyOccurrence
  rcases rs with ⟨_,_,_,rocc,rs⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence bodyOccurrence
  rcases lt with ⟨_,_,_,ltocc,lt⟩
  obtain ⟨rfl,rfl,rfl⟩ := ltocc.same_occurrence bodyOccurrence
  rcases rt with ⟨_,_,_,rtocc,rt⟩
  obtain ⟨rfl,rfl,rfl⟩ := rtocc.same_occurrence bodyOccurrence
  obtain ⟨parent,parentWord,_⟩ := Matches.observation _ actual_source_matches
    (show Position current.erase from ⟨[.fn],rfl⟩)
  obtain ⟨principal⟩ := outerFan.site.actionPrincipal_exists
  exact ls.fan_copied_body_binding_forward outerFan.site sourceFlow (.inl ()) rfl
    actual_source_matches actual_target_matches principal lt rs rt bodyRole bodyRole
    parent parent lambdaParent lambdaParent
    (by rw [parentWord];rfl) (by rw [parentWord];rfl)
    (by change bodyPosition.val=accessWord targetNet lambdaEdges++[.body];rw [lambdaWord];rfl)
    (by change bodyPosition.val=accessWord targetNet lambdaEdges++[.body];rw [lambdaWord];rfl)
    false false lambdaFinish lambdaFinish
    (actual_binding_finish lt.access lt.word) (actual_binding_finish rt.access rt.word) oldEq

abbrev leftEdges : List Path := [[.fn]]
abbrev rightEdges : List Path := [[.arg],[.fn]]
def leftChain : PrerequisiteChain current [.fn] leftEdges := .redex_lam (p:=[]) rfl
def rightChain : PrerequisiteChain current [.arg] rightEdges :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)
def parentVertex : SyntaxIncidence.Vertex current := some ⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
theorem sourceVertex : SyntaxIncidence.source current bodyPosition=parentVertex :=
  SyntaxIncidence.source_eq_of_spec current bodyPosition ⟨.body,_,_,rfl,rfl,.body⟩
theorem targetVertex : SyntaxIncidence.target current currentClosed bodyPosition=parentVertex :=
  SyntaxIncidence.target_eq_of_spec current currentClosed bodyPosition (Or.inr ⟨_,0,_,_,[],rfl,rfl,rfl,rfl⟩)
theorem actual_successful_endpoints :
    EndpointChain current (SyntaxIncidence.source current bodyPosition) leftEdges ∧
    EndpointChain current (SyntaxIncidence.target current currentClosed bodyPosition) leftEdges ∧
    SuccessfulEndpointIso current currentClosed (SyntaxIncidence.source current bodyPosition)
      (SyntaxIncidence.source current bodyPosition) ∧
    SuccessfulEndpointIso current currentClosed (SyntaxIncidence.target current currentClosed bodyPosition)
      (SyntaxIncidence.target current currentClosed bodyPosition) := by
  rw [sourceVertex,targetVertex]
  have chain : EndpointChain current parentVertex leftEdges := leftChain
  exact ⟨chain,chain,SuccessfulEndpointIso.refl_of_chain chain,SuccessfulEndpointIso.refl_of_chain chain⟩
theorem actual_nonempty_four_choices :
    Nonempty (OccurrenceFragmentSelection current sourceNet (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current sourceNet (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current targetNet (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current targetNet (.inl ())) :=
  ⟨actual_source_matches.occurrence_fragment_selection currentClosed,
    actual_source_matches.occurrence_fragment_selection currentClosed,
    actual_target_matches.occurrence_fragment_selection currentClosed,
    actual_target_matches.occurrence_fragment_selection currentClosed⟩
theorem actual_auxiliary : AuxiliaryAt current bodyPosition.val := by
  constructor
  · rintro ⟨other,a,fn,arg,split,_lookup⟩
    have last := congrArg List.getLast? split
    simp [bodyPosition] at last
  · rintro ⟨a,body,lookup⟩
    have varLookup : current.subterm bodyPosition.val=some (.var functionBody.label 0) := rfl
    rw [varLookup] at lookup
    cases lookup
/-- Same original INIT/history and actual events, not a reinitialized result. -/
theorem actual_original_history_trace :
    INIT original ∧Closed term ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase :=
  ⟨initial,closed,actualHistory,actual_two_step_trace,actual_source_matches,actual_target_matches⟩
#print axioms source_inputs_transparency
#print axioms actual_auxiliary
#print axioms actual_original_history_trace
#print axioms actual_binding_finish
#print axioms actual_direct_cut
#print axioms actual_four_choices_forward
#print axioms leftChain
#print axioms rightChain
#print axioms actual_successful_endpoints
#print axioms actual_nonempty_four_choices
end Lamping.Checks.FanCopiedBodyBindingChecks
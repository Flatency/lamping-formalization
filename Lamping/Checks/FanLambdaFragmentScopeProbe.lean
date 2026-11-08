import Lamping.Checks.AuxiliaryUndefinedCounterexample
import Lamping.Lamping.ActionPendingLambdaBranches
import Lamping.Lamping.TypedTransparentPrefixes
import Lamping.Lamping.CancellationFragmentTransport
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanLambdaFragmentScopeProbe
open AG Graph Lambda Lambda.Labelled FanUndefinedReachable
noncomputable abbrev sourceNet := actualFanPresentation.site.net
abbrev left : Path := [.body,.fn,.arg,.body]
abbrev right : Path := [.body,.arg,.body]

theorem source_matches : Matches sourceNet (.inl ()) result.erase :=
  actualFanPresentation.sourceIso.matches (target_matches concrete)

theorem source_flow : Nonempty (FlowBalance sourceNet initialBoundaryPolarity) := by
  obtain ⟨flow⟩ := encode_flowBalance term 0
  obtain ⟨first⟩ := concrete.graph_step.flowBalance flow
  exact ⟨actualFanPresentation.sourceIso.flowBalance first⟩

/-- The actual copied-lambda endpoint reflects its source parent to the
selected passive lambda. This uses the genuine supplied target path. -/
theorem source_parent_finish
    (fragment : OccurrenceFragment result sourceNet (.inl ()) p)
    (target : RootAccess RootFanShared.finalNet (.inl ()))
    (word : p=accessWord RootFanShared.finalNet target.val) (branch : Bool)
    (finish : target.val.getLast?=some (RootFanShared.finalNet.wire (.inl ⟨.inr (.inl branch),.inl ()⟩))) :
    fragment.fragment.access.val.getLast?=some (sourceNet.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) := by
  obtain ⟨flow⟩ := source_flow
  obtain ⟨principal⟩ := actualFanPresentation.site.actionPrincipal_exists
  obtain ⟨pre,split,_last⟩ := fragment.fragment.target_lambda_writer actualFanPresentation.site
    source_matches flow rfl principal target word branch finish
  simp only [fragment.fragment.literal,split,List.getLast?_append,principal.last,Option.some_or]

/-- The body departure port is recovered from its genuine syntax token. -/
theorem body_head
    (parent : OccurrenceFragment result sourceNet (.inl ()) p)
    (child : OccurrenceFragment result sourceNet (.inl ()) (p++[.body]))
    (atParent : result.subterm p=some (.lam stamp body))
    (parentFinish : parent.fragment.access.val.getLast?=some (sourceNet.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) :
    child.fragment.segments.head?=some (.inl ⟨.inr (.inr ()),lamBody⟩) := by
  obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup result atParent [] .external
  have actual := occurrence.append (SourceSubterm.body SourceSubterm.nil)
  obtain ⟨_envEq,ctxEq,_subEq⟩ := child.occurrence.same_occurrence actual
  have word : p++[.body]=accessWord sourceNet parent.fragment.access.val++[.body] := by
    rw [parent.fragment.word]
  have fromCtx : (sourceEdge child.environment child.context child.term).fromPort=child.context := by cases child.term <;> rfl
  have role : SourceDeparture (.lam stamp body) .body (sourceEdge child.environment child.context child.term).fromPort := by
    rw [fromCtx,ctxEq]; exact .body
  obtain ⟨departure,head⟩ := child.fragment.head_node_of_parent source_matches
    role parent.fragment.access word (.inr (.inr ())) (.inl ()) parentFinish
  have token := child.fragment.fromRealizes.syntax_departure_word role
  have fromEq := Option.some.inj (child.fragment.start.symm.trans head)
  rw [fromEq] at token
  cases departure with
  | inl u => cases u;cases token
  | inr q => cases q with
    | false => cases token
    | true => exact head

def oldArgVar : (encode 0 term).N := .inr (.inr (.inr ()))
def argBodyWire : (encode 0 term).W := .inl (.inr (.inr (.inr (.inl ()))))
def argBindingWire : (encode 0 term).W := .inl (.inr (.inr (.inr (.inr ⟨0,rfl⟩))))
theorem original_body_wire : net.wire (.inl ⟨oldArgLam,lamBody⟩)=.inr (.inr (argBodyWire,false)) := rfl
theorem original_body_arrival : net.wire (.inr (.inr (argBodyWire,true)))=.inl ⟨oldArgVar,.inr ()⟩ := rfl
theorem original_binding_wire : net.wire (.inl ⟨oldArgVar,.inl ()⟩)=.inr (.inr (argBindingWire,true)) := rfl
theorem original_binding_finish : net.wire (.inr (.inr (argBindingWire,false)))=.inl ⟨oldArgLam,lamBind⟩ := rfl

theorem source_passive_body_original :
    actualFanPresentation.sourceIso.symm.ends (.inl ⟨.inr (.inr ()),lamBody⟩)=
      .inl ⟨rhsLambda,lamBody⟩ := rfl
def argVarKept : RemainingNodes app lam := ⟨oldArgVar,by constructor <;> intro h <;> cases h⟩
def bodyOutside : concrete.Outside := ⟨argBodyWire,by
  rintro ⟨d,h⟩;simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def bindingOutside : concrete.Outside := ⟨argBindingWire,by
  rintro ⟨d,h⟩;simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
noncomputable abbrev betaNet := concrete.site.reduce
noncomputable def bodyStart : Endpoint betaNet := .inl ⟨rhsLambda,lamBody⟩
noncomputable def bodyTransit : Endpoint betaNet := .inr (.inr (.inl (.inl bodyOutside),true))
noncomputable def bodyCro : concrete.Kept⊕Empty := .inl argVarKept
noncomputable def bindingStart : Endpoint betaNet := .inl ⟨bodyCro,.inl ()⟩
noncomputable def bindingTransit : Endpoint betaNet := .inr (.inr (.inl (.inl bindingOutside),false))

theorem beta_body_wire : betaNet.wire bodyStart=.inr (.inr (.inl (.inl bodyOutside),false)) := by
  have wire : actualCut.wire (.inl ⟨argKept,lamBody⟩)=.inr (.inr (bodyOutside,false)) :=
    RootFanShared.first_cut_wire _ _ original_body_wire
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net (.inl ⟨argKept,lamBody⟩)).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) wire)
theorem beta_body_arrival : betaNet.wire bodyTransit=.inl ⟨bodyCro,.inr ()⟩ := by
  have wire : actualCut.wire (.inr (.inr (bodyOutside,true)))=.inl ⟨argVarKept,.inr ()⟩ :=
    RootFanShared.first_cut_wire _ _ original_body_arrival
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net (.inr (.inr (bodyOutside,true)))).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) wire)
theorem beta_binding_wire : betaNet.wire bindingStart=.inr (.inr (.inl (.inl bindingOutside),true)) := by
  have wire : actualCut.wire (.inl ⟨argVarKept,.inl ()⟩)=.inr (.inr (bindingOutside,true)) :=
    RootFanShared.first_cut_wire _ _ original_binding_wire
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net (.inl ⟨argVarKept,.inl ()⟩)).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) wire)
theorem beta_binding_finish : betaNet.wire bindingTransit=.inl ⟨rhsLambda,lamBind⟩ := by
  have wire : actualCut.wire (.inr (.inr (bindingOutside,false)))=.inl ⟨argKept,lamBind⟩ :=
    RootFanShared.first_cut_wire _ _ original_binding_finish
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net (.inr (.inr (bindingOutside,false)))).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) wire)

/-- Any already given typed path at this actual body port has the fixed
four-segment binding fragment. No partial path is completed. -/
theorem beta_body_piece_exact {es : List (Endpoint betaNet)} {a b : Context}
    (labels : Labelling betaNet es a b) (typed : ∃k,accessKind betaNet es=some k)
    (head : es.head?=some bodyStart) :
    es=[bodyStart,bodyTransit,bindingStart,bindingTransit] := by
  obtain ⟨suffix,split,first,remaining⟩ := labels.typed_transparent_prefix typed [bodyStart,bodyTransit]
    (by simp) head (by
      intro e f member
      have same := List.mem_singleton.mp member
      cases same
      exact ⟨.inl (.inl bodyOutside),false,beta_body_wire,rfl⟩)
  have sameLast : es.getLast?=suffix.getLast? := by
    rw [split]
    cases suffix with
    | nil => cases first
    | cons e rest => rfl
  have suffixTyped : ∃k,accessKind betaNet suffix=some k := by
    simpa only [accessKind,sameLast] using typed
  obtain ⟨port,rest,middle,departure,rule,tail⟩ := remaining.typed_nonterminal_departure suffixTyped
    bodyTransit first bodyCro (.inr ()) beta_body_arrival rfl
  cases port with
  | inr u => cases u;exact False.elim (rule.distinct rfl)
  | inl u =>
    cases u
    obtain ⟨ending,cut,atEnd,endLabels⟩ := tail.typed_transparent_prefix
      (by simpa only [departure,accessKind,List.getLast?_cons_cons] using suffixTyped)
      [bindingStart,bindingTransit] (by simp) rfl (by
        intro e f member
        have same := List.mem_singleton.mp member
        cases same
        exact ⟨.inl (.inl bindingOutside),true,beta_binding_wire,rfl⟩)
    have endingExact : ending=[bindingTransit] := by
      cases ending with
      | nil => cases atEnd
      | cons e es =>
        have eq : e=bindingTransit := Option.some.inj atEnd
        subst e
        cases es with
        | nil => rfl
        | cons next rest =>
          cases endLabels with
          | cons turn _ =>
            rw [beta_binding_finish] at turn
            obtain ⟨q,_same,bad⟩ := turn.from_node rhsLambda lamBind rfl
            exact False.elim (bad.no_binding.1 rfl)
    rw [split,departure,cut,endingExact]
    rfl
/-- Reflection through the actual boundary-fixing presentation preserves
this literal four-segment source binding fragment. -/
theorem source_body_piece_exact
    (fragment : OccurrenceFragment result sourceNet (.inl ()) p)
    (head : fragment.fragment.segments.head?=some (.inl ⟨.inr (.inr ()),lamBody⟩)) :
    fragment.fragment.segments.map actualFanPresentation.sourceIso.symm.ends=
      [bodyStart,bodyTransit,bindingStart,bindingTransit] := by
  obtain ⟨a,b,labels⟩ := fragment.fragment.fragment_labels
  apply beta_body_piece_exact (actualFanPresentation.sourceIso.symm.labelling labels)
  · obtain ⟨kind,typed⟩ := fragment.fragment.fragment_typed
    exact ⟨kind,(actualFanPresentation.sourceIso.symm.accessKind _).trans typed⟩
  · rw [List.head?_map,head]
    exact congrArg some source_passive_body_original

theorem source_body_pieces_equal
    (selection : OccurrenceFragmentSelection result sourceNet (.inl ())) :
    (selection ⟨left,rfl⟩).fragment.segments=(selection ⟨right,rfl⟩).fragment.segments := by
  have leftFinish := source_parent_finish (selection ⟨[.body,.fn,.arg],rfl⟩)
    RootFanLeft.leftParent RootFanLeft.leftWord.symm false RootFanLeft.leftFinish
  have rightFinish := source_parent_finish (selection ⟨[.body,.arg],rfl⟩)
    rightParent rightWord.symm true rightFinish
  have leftHead := body_head (selection ⟨[.body,.fn,.arg],rfl⟩) (selection ⟨left,rfl⟩) rfl leftFinish
  have rightHead := body_head (selection ⟨[.body,.arg],rfl⟩) (selection ⟨right,rfl⟩) rfl rightFinish
  have same := (source_body_piece_exact _ leftHead).trans (source_body_piece_exact _ rightHead).symm
  exact (actualFanPresentation.sourceIso.path_roundtrip _).symm.trans
    ((congrArg (List.map actualFanPresentation.sourceIso.ends) same).trans
      (actualFanPresentation.sourceIso.path_roundtrip _))

/-- A scope regression for the stronger all-occurrence Eqiff. Both selected
BODY edges are auxiliary, and every syntax endpoint here has no successful
prerequisite chain; this is neither REP nor corrected Aux failure. -/
theorem actual_scope_probe
    (source : OccurrenceFragmentSelection result sourceNet (.inl ()))
    (target : OccurrenceFragmentSelection result RootFanShared.finalNet (.inl ())) :
    (source ⟨left,rfl⟩).fragment.segments=(source ⟨right,rfl⟩).fragment.segments ∧
    (target ⟨left,rfl⟩).fragment.segments≠(target ⟨right,rfl⟩).fragment.segments ∧
    ¬((target ⟨left,rfl⟩).fragment.segments=(target ⟨right,rfl⟩).fragment.segments ↔
      (source ⟨left,rfl⟩).fragment.segments=(source ⟨right,rfl⟩).fragment.segments) := by
  have oldEqual := source_body_pieces_equal source
  have newDifferent : (target ⟨left,rfl⟩).fragment.segments≠(target ⟨right,rfl⟩).fragment.segments := by
    intro same
    exact two_body_heads_different target (congrArg List.head? same)
  exact ⟨oldEqual,newDifferent,fun iff=>newDifferent (iff.mpr oldEqual)⟩

/-- The actual original INIT and two-rule trace supply both sides' lawful
fragments. The negative conclusion only concerns all-occurrence transport. -/
theorem actual_reachable_scope_probe :
    INIT initial ∧Closed term ∧History [[]] initial result ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet RootFanShared.finalNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) result.erase ∧
    Matches RootFanShared.finalNet (.inl ()) result.erase ∧
    Nonempty (OccurrenceFragmentSelection result sourceNet (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection result RootFanShared.finalNet (.inl ())) ∧
    AuxiliaryAt result left ∧AuxiliaryAt result right ∧
    (∀p,NoPrerequisite result p) ∧
    (∀ (source : OccurrenceFragmentSelection result sourceNet (.inl ()))
       (target : OccurrenceFragmentSelection result RootFanShared.finalNet (.inl ())),
      (source ⟨left,rfl⟩).fragment.segments=(source ⟨right,rfl⟩).fragment.segments ∧
      (target ⟨left,rfl⟩).fragment.segments≠(target ⟨right,rfl⟩).fragment.segments ∧
      ¬((target ⟨left,rfl⟩).fragment.segments=(target ⟨right,rfl⟩).fragment.segments ↔
        (source ⟨left,rfl⟩).fragment.segments=(source ⟨right,rfl⟩).fragment.segments)) := by
  exact ⟨init_is_INIT term,closed,history,actual_two_rule_trace,source_matches,actual_final_matches,
    source_matches.occurrence_fragment_selection (history.closed closed),
    actual_final_matches.occurrence_fragment_selection (history.closed closed),
    NormalAuxiliaryCandidate.leftAux,NormalAuxiliaryCandidate.rightAux,
    NormalAuxiliaryCandidate.noChain,actual_scope_probe⟩

#print axioms source_parent_finish
#print axioms body_head
#print axioms beta_body_piece_exact
#print axioms source_body_piece_exact
#print axioms source_body_pieces_equal
#print axioms actual_scope_probe
#print axioms actual_reachable_scope_probe
end Lamping.Checks.FanLambdaFragmentScopeProbe

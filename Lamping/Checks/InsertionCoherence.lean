import Lamping.Lamping.MatchingFirstContractumCoherence
import Lamping.Lamping.PairedStreamOrdinarySuffix
import Lamping.Lamping.SupportedExpandedLoops
import Lamping.Lamping.MatchingSupportedLoopBase
import Lamping.Lamping.SupportedLoopPorts
import Lamping.Lamping.SupportedLoopRebase
import Lamping.Lamping.PairedStreamHighTails
import Lamping.Lamping.PairedStreamCuts
import Lamping.Lamping.PairedStreamAppend
import Lamping.Lamping.PairedExpandedInsertion
import Lamping.Lamping.BetaBindingProvenance
import Lamping.Lamping.FixedBetaDetourBlocks
import Lamping.Lamping.HistoryTypedPaths
import Lamping.Lamping.HistoryTypedCopyStep
import Lamping.Lamping.HistoryTypedPathStep
import Lamping.Lamping.FixedCoherentAncestors
import Lamping.Lamping.CompleteDegreeExhaustion
import Lamping.Lamping.LambdaFunctionSink
import Lamping.Lamping.FunctionLambdaOccurrences
import Lamping.Lamping.FunctionPortRoutes
import Lamping.Lamping.CompleteNodeOrigins
import Lamping.Lamping.CompletePhysicalAppOrigins
import Lamping.Lamping.CompleteAppTrailExclusion
import Lamping.Lamping.RootObservationCoverage
import Lamping.Lamping.TypedBinderRealization
import Lamping.Lamping.BindingObservationWords
import Lamping.Lamping.CompleteSyntaxChildPorts
import Lamping.Lamping.ReachableNormalForms
import Lamping.Lamping.OutsideControlWriterSuffix
import Lamping.Checks.Soundness

-- Nonvacuous encode0 (I I) instances live in the soundness owner's Checks.
-- These commands audit public proof dependencies, not fixture coverage.
#print axioms Lamping.AG.RootInputs.ordinary_insert_coherent
#print axioms Lamping.AG.ActualRedexAccess.coherent_argument_position
#print axioms Lamping.AG.ActualRedexAccess.first_contractum_coherent_positions
#print axioms Lamping.AG.BetaDetourBlocks.relabel
#print axioms Lamping.AG.RootInputs.ordinary_insert_coherent_streams
#print axioms Lamping.AG.ActualRedexAccess.coherent_argument_position_streams
#print axioms Lamping.AG.BetaDetourBlocks.ordinary_suffix
#print axioms Lamping.AG.SupportedExpandedBindingLoop.erase
#print axioms Lamping.AG.SupportedExpandedBindingLoop.insert_admissible
#print axioms Lamping.AG.PathSite.beta_fiber_supported_loop_base
#print axioms Lamping.AG.SupportedExpandedBindingLoop.beta_endpoints
#print axioms Lamping.AG.SupportedExpandedBindingLoop.insert_at_beta
#print axioms Lamping.AG.SupportedExpandedBindingLoop.rebase
#print axioms Lamping.AG.SupportedExpandedBindingLoop.copy_rebase
#print axioms Lamping.AG.BetaDetourBlocks.high_tail_sync_indexed
#print axioms Lamping.AG.BetaDetourBlocks.relabel_app_prefix_indexed
#print axioms Lamping.AG.BetaEdge.reverse_departures_negative
#print axioms Lamping.AG.BetaDetourBlocks.split_at_positive
#print axioms Lamping.AG.BetaDetourBlocks.suffix_at_positive_assignment
#print axioms Lamping.AG.BetaDetourBlocks.append_at_last
#print axioms Lamping.AG.BetaDetourBlocks.append_backward_paired
#print axioms Lamping.AG.BetaDetourBlocks.prefix_at_positive_assignment
#print axioms Lamping.AG.ExpandedBindingLoop.beta_ports
#print axioms Lamping.AG.RootInputs.insert_expanded_paired_body
#print axioms Lamping.AG.PathSite.beta_lambda_access_predecessor_word
#print axioms Lamping.AG.PathSite.beta_binding_access_provenance
#print axioms Lamping.AG.FixedBetaDetourBlocks.erase
#print axioms Lamping.AG.FixedBetaDetourBlocks.first_backward
#print axioms Lamping.AG.FixedBetaDetourBlocks.first_backward_root
#print axioms Lamping.AG.BetaPathResidual.fixed_detour_blocks
#print axioms Lamping.AG.PathSite.fixed_stream_old_fiber
#print axioms Lamping.AG.TypedSyntaxPaths.at_word
#print axioms Lamping.AG.Matches.typed_syntax_paths
#print axioms Lamping.AG.PathSite.relative_typed_copy_step
#print axioms Lamping.AG.PathSite.relative_typed_paths_step
#print axioms Lamping.AG.FixedCoherentCore.erase
#print axioms Lamping.AG.FixedBetaDetourBlocks.fixed_coherent
#print axioms Lamping.Lambda.Labelled.relative_complete_no_selected_degree
#print axioms Lamping.Lambda.Labelled.SourceRoute.function_lambda_sink

namespace Lamping.Checks.TypedInitialPaths
open AG Graph Lambda Lambda.Labelled SoundnessInitialInsertion

/-- Actual closed I I, its existing physical beta, and one source selector
supply every original syntax path for every root input. -/
theorem actual_original_typed_paths :
    ∃ selection : SourceEdgeSelection (initLabels identityApp) (encode 0 identityApp).net (.inl ()),
      TypedSyntaxPaths selection (edge 0) (initLabels identityApp) := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have matching : Matches (encode 0 identityApp).net (.inl ()) (initLabels identityApp).erase :=
    encode_closed_matches identityApp closed 0
  exact ⟨matching.source_edge_selection closed,matching.typed_syntax_paths
    (init_is_INIT identityApp) (encode_closed_independence identityApp closed 0).rootInputs _ (edge 0)⟩

#print axioms actual_original_typed_paths
end Lamping.Checks.TypedInitialPaths

namespace Lamping.Checks.FixedCoherentInitialAncestor
open AG Graph Lambda SoundnessBetaAncestor

/-- The actual two-reconnection reduced I I path yields a positive finite
tree at one physical beta, at its original input and output assignments. -/
theorem actual_fixed_coherent_ancestor :
    ∃ (edge : BetaEdge actualBetaSite.net) (old : List (Endpoint actualBetaSite.net)) (count : Nat),
      0<count ∧ FixedCoherentCore (.inl ()) edge old Context.empty (Context.empty.cons .empty) count := by
  obtain ⟨edge,old,geometry,relation,_labels,first,_last⟩ := actual_ancestor Context.empty
  obtain ⟨count,stream⟩ := relation.fixed_detour_blocks actualBetaSite geometry
    ((reduced_labels Context.empty).plug_decomposition _ _)
  have entry : (.inr (.inr (.inl (.inr false)))) ∈ reduced.map (plugEnd _ _).invFun := by
    exact List.mem_map.mpr ⟨.inr (.inr (.inr (.inr false),true)),by simp [reduced],rfl⟩
  have positive := stream.erase.positive_count actualBetaSite.net actualFlow (.inl ()) rfl first edge
    (relation.reverse_occurs actualBetaSite entry)
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  exact ⟨edge,old,count,positive,stream.fixed_coherent actualFlow rfl
    (betaEncodingIso.indexed_balance balance) rfl transparency first⟩

#print axioms actual_fixed_coherent_ancestor
end Lamping.Checks.FixedCoherentInitialAncestor

namespace Lamping.Checks.CompleteSelectedDegree
open AG Graph Lambda Lambda.Labelled

private abbrev term : Term := .app (.app (.lam (.var 0)) (.lam (.var 0))) (.lam (.var 0))
private abbrev original : LTerm := initLabels term
private abbrev target : LTerm := .app (.atom 0)
  (LTerm.contract (.atom 1) (.atom 2) (.var (.atom 3) 0) (.lam (.atom 4) (.var (.atom 5) 0)))
  (.lam (.atom 6) (.var (.atom 7) 0))

/-- The real selected inner development is complete, yet its result still
has a newly created root redex. Exhaustion eliminates selected degrees only. -/
theorem actual_complete_preserves_a_new_redex :
    (∀ p,target.degreeAt p≠some (.atom 2)) ∧ IsRedex target.erase := by
  have relative : Marked.RelativeHistory [[.fn]] (Marked.mark [[.fn]] original.erase)
      (.app [] (.lam (.var 0)) (.lam (.var 0))) := by
    change Marked.RelativeHistory [[.fn]]
      (.app [] (.red [[.fn]] (.var 0) (.lam (.var 0))) (.lam (.var 0))) _
    exact .cons (.appL (.root [[.fn]] (.var 0) (.lam (.var 0)))) (.nil _)
  have labels : History [[.fn]] original target := .cons (.fn (.root _ _ _ _)) (.nil _)
  have normal : Marked.Normal (.app [] (.lam (.var 0)) (.lam (.var 0))) := ⟨True.intro,True.intro⟩
  have selected : SelectedDegree original [[.fn]] (.atom 2) := ⟨[.fn],by simp,rfl⟩
  constructor
  · intro p atDegree
    exact relative_complete_no_selected_degree (init_is_INIT term) relative normal labels atDegree selected
  · trivial

#print axioms actual_complete_preserves_a_new_redex
end Lamping.Checks.CompleteSelectedDegree

namespace Lamping.Checks.ActualTraceSoundness
open AG Graph Lambda SoundnessBetaAncestor

/-- A real beta from the original encoded I I, not an assumed target
Matches certificate or a schema with semantic fields. -/
theorem actual_beta_from_encoding : GraphStep (.beta 0) (ActualNet.initial identityApp)
    (ActualNet.ofNet actualBetaSite.reduce) :=
  (GraphStep.site betaKeptLabels actualBetaSite).iso_source betaEncodingIso

theorem actual_nonempty_trace_has_identity :
    Betas identityApp identity ∧ RootInputs actualBetaSite.reduce (.inl ()) ∧
      Matches actualBetaSite.reduce (.inl ()) identity := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  obtain ⟨u,reductions,inputs,matching⟩ := initial_trace_soundness identityApp closed
    (ActualNet.ofNet actualBetaSite.reduce) [.beta 0] (.single actual_beta_from_encoding)
  have canonical : Matches actualBetaSite.reduce (.inl ()) identity :=
    SoundnessFirstHistoryEvaluation.actual_complete_beta_matches
  have same : u=identity := matching.unique canonical
  exact same ▸ ⟨reductions,inputs,matching⟩

/-- The zero-step branch retains actual carrier isomorphisms and the
uncontracted redex; SND does not assert that its endpoint is normal. -/
theorem actual_zero_trace_retains_redex :
    ∃ u, Betas identityApp u ∧ Matches (encode 0 identityApp).net (.inl ()) u ∧ IsRedex u := by
  obtain ⟨u,reductions,_inputs,matching⟩ := initial_trace_soundness identityApp
    ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ (ActualNet.initial identityApp) [] (.refl _)
  have same : u=identityApp := matching.unique
    (encode_closed_matches identityApp ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ 0)
  subst u
  exact ⟨identityApp,reductions,matching,True.intro⟩

#print axioms GraphStep.beta_soundness
#print axioms GraphStep.soundness
#print axioms GraphTrace.soundness
#print axioms initial_trace_soundness
#print axioms initial_trace_normal_form
#print axioms initial_reachable_normal_form
#print axioms actual_nonempty_trace_has_identity
#print axioms actual_zero_trace_retains_redex
end Lamping.Checks.ActualTraceSoundness

namespace Lamping.Checks.RootCoverageBoundary
open AG Graph Lambda

private abbrev original : Term := .lam (.lam (.var 0))
private abbrev wrong : Term := .lam (.lam (.var 1))

private theorem same_kinds (p : Path) (v : Term) (lookup : subtermAt wrong p=some v) :
    ∃ u,subtermAt original p=some u ∧(syntaxShape u).kind=(syntaxShape v).kind := by
  cases p with
  | nil => cases lookup; exact ⟨_,rfl,rfl⟩
  | cons step rest => cases step with
    | fn | arg => simp [subtermAt] at lookup
    | body =>
      cases rest with
      | nil => cases lookup; exact ⟨_,rfl,rfl⟩
      | cons step rest => cases step with
        | fn | arg => simp [subtermAt] at lookup
        | body =>
          cases rest with
          | nil => cases lookup; exact ⟨_,rfl,rfl⟩
          | cons step rest => cases step <;> simp [subtermAt] at lookup

/-- Both terms are closed and have the same node kinds at every position.
The real graph covers all those words and kinds, yet cannot match the
different binder index. Full Observes in the coverage theorem is essential. -/
theorem actual_kind_coverage_does_not_determine_binder :
    (∀ position : Position wrong,∃ access : RootAccess (encode 0 original).net (.inl ()),
      accessWord (encode 0 original).net access.val=position.val ∧
      ∃ v,subtermAt wrong position.val=some v ∧
        accessKind (encode 0 original).net access.val=some (syntaxShape v).kind) ∧
    ¬Matches (encode 0 original).net (.inl ()) wrong := by
  have closed : Closed original := by change 0<2; decide
  have matching := encode_closed_matches original closed 0
  constructor
  · intro position
    obtain ⟨v,lookup⟩ := Option.isSome_iff_exists.mp position.property
    obtain ⟨u,oldLookup,kinds⟩ := same_kinds position.val v lookup
    let oldPosition : Position original := ⟨position.val,by rw [oldLookup]; rfl⟩
    obtain ⟨access,word,w,actualLookup,observed⟩ := Matches.observation _ matching oldPosition
    have same : w=u := Option.some.inj (actualLookup.symm.trans oldLookup)
    refine ⟨access,word,v,lookup,?_⟩
    simpa only [same,kinds] using observed.1
  · intro proposed
    have same := matching.unique proposed
    have impossible : (0 : Nat)=1 := Term.var.inj (Term.lam.inj (Term.lam.inj same))
    cases impossible

#print axioms RootInputs.classify_of_observation_coverage
#print axioms RootInputs.matches_of_observation_coverage
#print axioms BetaEdge.complete_app_trail_exclusion
#print axioms actual_kind_coverage_does_not_determine_binder
end Lamping.Checks.RootCoverageBoundary

namespace Lamping.Checks.TypedBinderActual
open AG Graph Lambda SoundnessBetaAncestor

/-- The actual developed I I joint provides a genuinely labelled expanded
binding loop for EVERY requested input, with its actual binder retained.
No loop assignment or shell is a fixture premise. -/
theorem actual_joint_realizes_expanded_binding :
    ∃ (ambient loop : List (Endpoint actualBetaSite.net)) (binder : _),
      ∀ input : Context,∃ output seam,
        ExpandedLabelling actualBetaSite.net ambient input seam ∧
        ∃ binding : ExpandedBindingLoop actualBetaSite.net loop seam output,binding.binder=binder := by
  obtain ⟨beta,selection,generated,supported,paths,binders⟩ :=
    SoundnessFirstHistoryEvaluation.actual_typed_joint_history
  obtain ⟨ambient,loop,binder,_ctx,_ambientEval,_leafEval,_sort,_ctxRole,_end,realize⟩ :=
    realize_typed_binder generated supported paths binders (p:=[]) (q:=[]) rfl rfl
  refine ⟨ambient,loop,binder,?_⟩
  intro input
  obtain ⟨output,seam,_count,_whole,ambientLabels,binding⟩ := realize input
  exact ⟨output,seam,ambientLabels,binding⟩

#print axioms realize_typed_binder
#print axioms actual_joint_realizes_expanded_binding
#print axioms RootAccess.binding_suffix_of_same_seam
#print axioms SourceSyntaxStep.actual_ports
#print axioms CurrentSyntaxChild.complete_kept_ports
#print axioms PathSite.complete_app_context_kept
#print axioms PathSite.complete_lambda_context_kept
end Lamping.Checks.TypedBinderActual

namespace Lamping.Checks.PhysicalSourceOrigin
open AG Graph Lambda Lambda.Labelled SoundnessBetaAncestor

/-- The actual named I I graph supplies its old selected origin via the
root access and real flow, rather than an assumed syntax-fiber member. -/
theorem actual_old_origin_from_physical_access :
    ∃ beta : BetaEdge actualBetaSite.net,
      SelectedDegree (initLabels identityApp)
        (physicalBetaFiberPaths actualBetaSite.net (.inl ()) identityApp beta.app beta.lam) (.atom 1) := by
  obtain ⟨beta,_app,_lam,_fun,_ctx,_arg,_bind,_body,appCtx⟩ := actualBetaSite.betaEdge_identified
  let access : RootAccess actualBetaSite.net (.inl ()) :=
    ⟨[.inr (.inl (.inl ()))],⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,rfl,⟨.app,rfl⟩⟩⟩
  have finish : access.val.getLast?=some (actualBetaSite.net.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
    rw [appCtx]
    rfl
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have matching : Matches actualBetaSite.net (.inl ()) (initLabels identityApp).erase :=
    betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  obtain ⟨alpha,body,lookup,selected⟩ := beta.source_app_selected_origin matching actualFlow rfl
    (show (initLabels identityApp).subterm []=some (.app (.atom 0)
      (.lam (.atom 1) (.var (.atom 2) 0)) (.lam (.atom 3) (.var (.atom 4) 0))) from rfl)
    access rfl finish
  have same : alpha=.atom 1 := by
    have shape := Option.some.inj lookup
    exact (LTerm.lam.inj (LTerm.app.inj shape).2.1).1.symm
  exact ⟨beta,same ▸ selected⟩

#print axioms BetaEdge.source_app_selected_origin
#print axioms BetaEdge.complete_no_source_app_origin
#print axioms BetaEdge.complete_no_realized_app_origin
#print axioms actual_old_origin_from_physical_access
end Lamping.Checks.PhysicalSourceOrigin

namespace Lamping.Checks.FunctionLambdaSink
open AG Graph Lambda Lambda.Labelled

private abbrev term : Term := .app (.lam (.var 0)) (.lam (.var 0))
private abbrev original : LTerm := initLabels term
private theorem functionEdge : (⟨.atom 1,.appFn (.atom 0),.lamContext (.atom 1)⟩ : SourceEdge)
    ∈sourceEdges [] .external original := by decide
private theorem rootEdge : (⟨.atom 0,.external,.appContext (.atom 0)⟩ : SourceEdge)
    ∈sourceEdges [] .external original := by decide
private theorem variableEdge : (⟨.atom 2,.lamBody (.atom 1),.lamBind (.atom 1)⟩ : SourceEdge)
    ∈sourceEdges [] .external original := by decide
private theorem argumentEdge : (⟨.atom 3,.appArg (.atom 0),.lamContext (.atom 3)⟩ : SourceEdge)
    ∈sourceEdges [] .external original := by decide

theorem actual_function_route_and_external_exclusion :
    SourceRoute (sourceEdges [] .external original) (.appFn (.atom 0)) (.atom 1) (.lamContext (.atom 1)) ∧
      ∀ stamp,¬SourceRoute (sourceEdges [] .external original) .external stamp (.lamContext (.atom 1)) := by
  refine ⟨.atom functionEdge rfl,?_⟩
  intro stamp route
  have impossible := (route.function_lambda_sink (init_is_INIT term) functionEdge rfl).1
  cases impossible

private abbrev copiedLabel : Label := ((Label.atom 0).concat (Label.atom 1).over).concat
  (((Label.atom 2).concat (Label.atom 1).under).concat (Label.atom 3))

/-- The different argument lambda really admits a compound root route.
Thus the original FUNCTION-edge hypothesis is essential to the sink rule. -/
theorem actual_argument_lambda_compound_route :
    SourceRoute (sourceEdges [] .external original) .external copiedLabel (.lamContext (.atom 3)) ∧
      copiedLabel≠.atom 3 := by
  constructor
  · exact .over (.atom rootEdge rfl) (.atom functionEdge rfl)
      (.under (.atom variableEdge rfl) (.atom functionEdge rfl) (.atom argumentEdge rfl))
  · decide

#print axioms actual_function_route_and_external_exclusion
#print axioms actual_argument_lambda_compound_route
end Lamping.Checks.FunctionLambdaSink

namespace Lamping.Checks.CompleteSelectedDegree
open AG Graph Lambda Lambda.Labelled

/-- The selected old function lambda disappears even though this actual
complete development creates a different redex at the root. -/
theorem actual_complete_function_lambda_disappears :
    (∀ p body,target.subterm p≠some (.lam (.atom 2) body)) ∧IsRedex target.erase := by
  have relative : Marked.RelativeHistory [[.fn]] (Marked.mark [[.fn]] original.erase)
      (.app [] (.lam (.var 0)) (.lam (.var 0))) := by
    change Marked.RelativeHistory [[.fn]]
      (.app [] (.red [[.fn]] (.var 0) (.lam (.var 0))) (.lam (.var 0))) _
    exact .cons (.appL (.root [[.fn]] (.var 0) (.lam (.var 0)))) (.nil _)
  have labels : History [[.fn]] original target := .cons (.fn (.root _ _ _ _)) (.nil _)
  have normal : Marked.Normal (.app [] (.lam (.var 0)) (.lam (.var 0))) := ⟨True.intro,True.intro⟩
  have selected : SelectedDegree original [[.fn]] (.atom 2) := ⟨[.fn],by simp,rfl⟩
  have edge : (⟨.atom 2,.appFn (.atom 1),.lamContext (.atom 2)⟩ : SourceEdge)
      ∈sourceEdges [] .external original := by decide
  exact ⟨fun _ _ lookup => relative_complete_no_function_lambda (init_is_INIT term)
    relative normal labels edge selected lookup,True.intro⟩

#print axioms actual_complete_function_lambda_disappears
#print axioms TermRoutes.function_lambda_occurrence
#print axioms relative_complete_no_function_lambda

/-- Actual completion also removes applications with the selected app's
original origin. The unrelated original outer app is retained. -/
theorem actual_complete_application_origin_disappears :
    (∀ p stamp fn arg,target.subterm p=some (.app stamp fn arg) →stamp.lastAtom≠some 1) ∧
      (∃ fn arg,target.subterm []=some (.app (.atom 0) fn arg)) := by
  have relative : Marked.RelativeHistory [[.fn]] (Marked.mark [[.fn]] original.erase)
      (.app [] (.lam (.var 0)) (.lam (.var 0))) := by
    change Marked.RelativeHistory [[.fn]]
      (.app [] (.red [[.fn]] (.var 0) (.lam (.var 0))) (.lam (.var 0))) _
    exact .cons (.appL (.root [[.fn]] (.var 0) (.lam (.var 0)))) (.nil _)
  have labels : History [[.fn]] original target := .cons (.fn (.root _ _ _ _)) (.nil _)
  have normal : Marked.Normal (.app [] (.lam (.var 0)) (.lam (.var 0))) := ⟨True.intro,True.intro⟩
  have selected : SelectedDegree original [[.fn]] (.atom 2) := ⟨[.fn],by simp,rfl⟩
  have atHead : SourceSubterm [] .external original [.fn] [] (.appFn (.atom 0))
      (.app (.atom 1) (.lam (.atom 2) (.var (.atom 3) 0)) (.lam (.atom 4) (.var (.atom 5) 0))) := .fn .nil
  constructor
  · intro p stamp fn arg lookup lastAtom
    exact relative_complete_no_application_origin (init_is_INIT term) relative normal labels
      atHead selected rfl lookup lastAtom
  · exact ⟨_,_,rfl⟩

#print axioms SourceRoute.head_function_destination
#print axioms TermRoutes.head_function_lambda
#print axioms TermRoutes.head_function_degree
#print axioms TermRoutes.application_last_atom_degree
#print axioms relative_complete_no_application_origin
#print axioms actual_complete_application_origin_disappears

/-- Excluding only literal atomic labels would miss a proposed compound
label with the same origin. This consumes the full origin exclusion. -/
theorem actual_complete_lambda_origin_disappears :
    ∀ p stamp body,target.subterm p=some (.lam stamp body) →stamp.lastAtom≠some 2 := by
  have relative : Marked.RelativeHistory [[.fn]] (Marked.mark [[.fn]] original.erase)
      (.app [] (.lam (.var 0)) (.lam (.var 0))) := by
    change Marked.RelativeHistory [[.fn]]
      (.app [] (.red [[.fn]] (.var 0) (.lam (.var 0))) (.lam (.var 0))) _
    exact .cons (.appL (.root [[.fn]] (.var 0) (.lam (.var 0)))) (.nil _)
  have labels : History [[.fn]] original target := .cons (.fn (.root _ _ _ _)) (.nil _)
  have normal : Marked.Normal (.app [] (.lam (.var 0)) (.lam (.var 0))) := ⟨True.intro,True.intro⟩
  have selected : SelectedDegree original [[.fn]] (.atom 2) := ⟨[.fn],by simp,rfl⟩
  have edge : (⟨.atom 2,.appFn (.atom 1),.lamContext (.atom 2)⟩ : SourceEdge)
      ∈sourceEdges [] .external original := by decide
  intro p stamp body lookup lastAtom
  exact relative_complete_no_lambda_origin (init_is_INIT term) relative normal labels
    edge selected rfl lookup lastAtom

#print axioms TermRoutes.function_lambda_label
#print axioms relative_complete_no_lambda_origin
#print axioms actual_complete_lambda_origin_disappears
end Lamping.Checks.CompleteSelectedDegree


namespace Lamping.Checks.OutsideWriterActual
open AG Graph
private def kept : Unit⊕Bool → Graph.Label signature := Sum.elim (fun _ => label .lam 1) (fun _ => garbage)
private abbrev schema : Schema := .fanAction .lam 0 1 (by decide)
private def internal : Pairing (Bool⊕(Empty×Bool)) where
  mate := fun x => match x with | .inl b => .inl (!b) | .inr (e,_) => nomatch e
  involutive := by rintro (b|⟨e,d⟩); cases b <;> rfl; exact nomatch e
  fixedPointFree := by rintro (b|⟨e,d⟩); cases b <;> (intro h; cases h); exact nomatch e

def site : PathSite schema kept (B:=Unit) (W:=Empty) (V:=Empty) where
  wire := {
    mate := fun x => match x with
      | .inl ⟨.inl (.inl _),.inl _⟩ => .inl ⟨.inl (.inr true),()⟩
      | .inl ⟨.inl (.inl _),.inr false⟩ => .inl ⟨.inr (.inr ()),.inr true⟩
      | .inl ⟨.inl (.inl _),.inr true⟩ => .inl ⟨.inr (.inl ()),.inr false⟩
      | .inl ⟨.inl (.inr false),_⟩ => .inr (.inl ())
      | .inl ⟨.inl (.inr true),_⟩ => .inl ⟨.inl (.inl ()),.inl ()⟩
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inl ⟨.inr (.inr ()),.inl ()⟩
      | .inl ⟨.inr (.inl _),.inr false⟩ => .inl ⟨.inl (.inl ()),.inr true⟩
      | .inl ⟨.inr (.inl _),.inr true⟩ => .inl ⟨.inr (.inr ()),.inr false⟩
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inl ⟨.inr (.inr _),.inr false⟩ => .inl ⟨.inr (.inl ()),.inr true⟩
      | .inl ⟨.inr (.inr _),.inr true⟩ => .inl ⟨.inl (.inl ()),.inr false⟩
      | .inr (.inl _) => .inl ⟨.inl (.inr false),()⟩
      | .inr (.inr (.inl e,_)) => nomatch e
      | .inr (.inr (.inr e,_)) => nomatch e
    involutive := by
      rintro (⟨node,p⟩ | (u | ⟨e,d⟩))
      · rcases node with (u|b)|(v|w)
        · cases u; cases p with | inl u => cases u; rfl | inr b => cases b <;> rfl
        · cases b <;> cases p <;> rfl
        · cases v; cases p with | inl u => cases u; rfl | inr b => cases b <;> rfl
        · cases w; cases p with | inl u => cases u; rfl | inr b => cases b <;> rfl
      · cases u; rfl
      · cases e with | inl e => exact nomatch e | inr e => exact nomatch e
    fixedPointFree := by
      rintro (⟨node,p⟩ | (u | ⟨e,d⟩))
      · rcases node with (u|b)|(v|w)
        · cases p with | inl u => intro h; cases h | inr b => cases b <;> (intro h; cases h)
        · cases b <;> (intro h; cases h)
        · cases p with | inl u => intro h; cases h | inr b => cases b <;> (intro h; cases h)
        · cases p with | inl u => intro h; cases h | inr b => cases b <;> (intro h; cases h)
      · intro h; cases h
      · cases e with | inl e => exact nomatch e | inr e => exact nomatch e }
  internal := internal
  connected := by rintro (b|⟨e,d⟩); cases b; exact .refl _; exact .segment _; exact nomatch e
  wiring := by rintro (b|⟨e,d⟩); cases b <;> rfl; exact nomatch e

private def principal : SiteActionPrincipal site where
  edges := [.inl ⟨.inr (.inl ()),.inl ()⟩]
  first := rfl
  last := rfl
  transparent := by intro e f h; cases h

private abbrev source : Endpoint site.net := .inl ⟨.inl (.inl ()),lamBody⟩
private abbrev path : List (Endpoint site.net) := [source,.inl ⟨.inr (.inl ()),.inl ()⟩]
private abbrev sourceCut : Endpoint (cutFragment site.net (pathPartition schema Empty) site.closed) :=
  .inl ⟨.inl (),lamBody⟩

/-- This source is a kept lambda body in a component separated from the root
by actual Garbage incidence. The helper assumes no reachable-encoding claim. -/
theorem actual_nonroot_proper_writer (a : Context) :
    AtProperRole site.net () source .lamBody 1 ∧
    site.net.wire (.inr (.inl ()))=.inl ⟨.inl (.inr false),()⟩ ∧
    site.net.wire (.inl ⟨.inl (.inl ()),.inl ()⟩)=.inl ⟨.inl (.inr true),()⟩ ∧
    ∃ pre q middle,
      path=pre++principal.edges ∧pre.head?=some source ∧
      Labelling site.net pre a middle ∧
      Traversal 0 (.op .fan) (.inr q) (.inl ()) middle (InitialOffsets.fanAt 0 false a) := by
  have labels : Labelling site.net path a (InitialOffsets.fanAt 0 false a) :=
    .cons (.node (g:=site.net) (.inr (.inl ())) (.inr false) (.inl ())
      (.direct (InitialOffsets.Event.apply_rel (.fan 0 false) a))) (.single _ _)
  obtain ⟨pre,q,middle,split,first,_last,preLabels,writer⟩ :=
    site.outside_control_writer_suffix principal labels sourceCut rfl rfl
  exact ⟨.lamBody _ _ _ rfl HEq.rfl,rfl,rfl,pre,q,middle,split,first,preLabels,writer⟩

/-- The root is really sealed by its own Garbage node: a labelled path
from it cannot take even a second segment into the source component. -/
theorem actual_root_path_is_single {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (first : es.head?=some (.inr (.inl ()))) :
    es=[.inr (.inl ())] := by
  obtain ⟨tail,same⟩ := List.head?_eq_some_iff.mp first
  subst es
  cases tail with
  | nil => rfl
  | cons next tail =>
    cases labels with
    | cons turn rest =>
      obtain ⟨q,_departure,rule⟩ := turn.from_node (g:=site.net) (.inl (.inr false)) () rfl
      exact False.elim (rule.distinct (Subsingleton.elim (α:=Unit) _ _))

#print axioms PathSite.outside_control_writer_suffix
#print axioms actual_nonroot_proper_writer
#print axioms actual_root_path_is_single
end Lamping.Checks.OutsideWriterActual

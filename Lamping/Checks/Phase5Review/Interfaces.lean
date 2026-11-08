import Lamping.Lamping.GraphFlowPreservation
import Lamping.Lamping.GraphBalancePreservation
import Lamping.Lamping.EncodedBalance
import Lamping.Lamping.InitialTraceInvariants
import Lamping.Lamping.NetIsoInvariantTransport
import Lamping.Lamping.InitialFullIndependence
import Lamping.Lamping.InitialControlWords
import Lamping.Lamping.ExpandedBinderOccurrences
import Lamping.Lambda.LabelRegionalOrigins
import Lamping.Lamping.InitialIndependence
import Lamping.Lamping.InitialSourcePaths
import Lamping.Lambda.LabelRegionTransport
import Lamping.Lamping.EncodedHeights
import Lamping.Lamping.InitialNodeAccess
import Lamping.Lamping.ExpandedOrdinaryIndependence
import Lamping.Lambda.LabelAtomicFamilies
import Lamping.Lamping.TraceSeams
import Lamping.Lamping.OrdinaryPrefixRelabelling
import Lamping.Lamping.InitialNesting
import Lamping.Lamping.MarkerRigidity
import Lamping.Lamping.GlobalGraphSteps
import Lamping.Lamping.MatchingDefinitions
import Lamping.Lamping.MatchingUniqueness
import Lamping.Lamping.NetIsoPathTransport
import Lamping.Lambda.LabelRelabelling
import Lamping.Lambda.LabelResiduals
import Lamping.Lambda.LabelInitialRelabelling
import Lamping.Lambda.LabelDevelopments
import Lamping.Lambda.LabelPermutation
import Lamping.Lambda.LabelRoutes
import Lamping.Lambda.LabelBoundaryAtoms
import Lamping.Lambda.LabelPathInjective
import Lamping.Lambda.LabelEdgeSubstitution
import Lamping.Lamping.GeneratedExpandedLoops
import Lamping.Lamping.InitialAccessDeterminism
import Lamping.Lamping.InitialBindingSuffix
import Lamping.Lamping.PathLabelDeterminism
import Lamping.Lamping.InitialFreeConstruction
import Lamping.Lamping.InitialPositionAccess
import Lamping.Lamping.MarkerTransport
import Lamping.Lamping.MarkerNoCopy
import Lamping.Lamping.MarkerReplay
import Lamping.Lamping.InitialBoundAccess
import Lamping.Lamping.InitialAccessPrefix
import Lamping.Lamping.InitialAccessLookup
import Lamping.Lamping.InitialBoundObservations
import Lamping.Lamping.InitialMatching
import Lamping.Lamping.InitialTransparency
import Lamping.Lambda.LabelRegions
import Lamping.Lambda.LabelCanonicalInternality

namespace Lamping.Checks.Phase5Review
open Graph AG Lambda

section
variable {B : Type} [FiniteNames B]
variable {g h k : ActualNet B} {ss tt : List Schema}

example (a : GraphTrace g h ss) (b : GraphTrace h k tt) :
    GraphTrace g k (ss ++ tt) := a.trans b

example (a : NetIso g.net h.net) : GraphTrace g h [] := .iso a

example (normal : GraphNormal g) (s : Schema) :
    ¬ GraphStep s g h := normal s h
end

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {t : Term}

example (matched : Matches g root t) (p : Position t) :
    ∃ es : RootAccess g root, accessWord g es.val = p.val := by
  obtain ⟨es,word,_⟩ := Matches.observation g matched p
  exact ⟨es,word⟩

example {es : List (Endpoint g)} {a b : AccessShape}
    (ha : Observes g es a) (hb : Observes g es b) : a = b :=
  Observes.unique g ha hb

example {u : Term} (ht : Matches g root t) (hu : Matches g root u) : t = u :=
  ht.unique hu
end

section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V}
example (iso : NetIso g h) {root : B} {t : Term} :
    Matches g root t ↔ Matches h root t := iso.matches_iff
example (iso : NetIso g h) (es : List (Endpoint g)) :
    accessWord h (es.map iso.ends) = accessWord g es := iso.accessWord es
end

section
open Lambda.Labelled
example {m n : Term} (h : Derivation m n) (t : LTerm) (ht : t.erase=m) :
    ∃ u, History h.paths t u ∧ u.erase=n ∧ ∀ v, History h.paths t v → v=u :=
  Lambda.Labelled.Derivation.label_transport h t ht

example {t u : LTerm} {ps : List Path} (h : History ps t u) (s : Nat → Label) :
    History ps (t.relabel s) (u.relabel s) := h.relabel s

example {m n : Term} (h : Derivation m n) (t u : LTerm)
    (source : t.erase=m) (transport : History h.paths t u)
    (r : RedexOcc m) (s : RedexOcc n) (residual : h.Residual r s) :
    u.degreeAt s.val=t.degreeAt r.val :=
  Lambda.Labelled.Derivation.residual_degree h t u source transport r s residual
end

#print axioms AG.GraphTrace.trans
#print axioms AG.Matches.observation
#print axioms AG.Observes.unique
#print axioms AG.Matches.unique
#print axioms Graph.NetIso.matches_iff
#print axioms Graph.NetIso.bindingSuffix_iff
#print axioms Lambda.Labelled.Derivation.label_transport
#print axioms Lambda.Labelled.replay_exists
#print axioms Lambda.Labelled.History.relabel
#print axioms Lambda.Labelled.Derivation.residual_degree
#print axioms AG.GeneratedExpandedProperPath.forward
#print axioms AG.InitialLabelling.access_word_unique
#print axioms AG.encode_accessWord_injective
#print axioms Lambda.Labelled.History.initial_relabelling
#print axioms Lambda.Labelled.History.local_initial_basis
#print axioms Lambda.Labelled.DevelopmentEval.complete_unique
#print axioms Lambda.Labelled.PermEq.labelled_unique
#print axioms Lambda.Labelled.FamilyEq.degreeAlong
#print axioms AG.encode_bindingSuffix_unique
#print axioms Lambda.Labelled.History.generated_label_alternating
#print axioms Lambda.Labelled.History.generated_source_routes
#print axioms AG.ExpandedIndependence.root_input
#print axioms AG.Traversal.output_unique
#print axioms AG.ExpandedContextTrace.input_unique
#print axioms Lambda.Labelled.History.degree_walk
#print axioms Lambda.Labelled.SourceRoute.lam_last_atom
#print axioms AG.InitialOffsets.encode_FV_accessWord
#print axioms AG.InitialOffsets.FreeOccurrence.realized
#print axioms AG.encode_nonvar_access
#print axioms Lambda.Labelled.Label.pathCode_injective
#print axioms Lambda.Labelled.History.generated_label_path_injective
#print axioms AG.Marker.path_origin_attribution
#print axioms AG.encode_closed_access_coverage
#print axioms AG.Marker.actual_writer_attribution
#print axioms AG.encode_accessWord_prefix
#print axioms AG.encode_closed_access_lookup
#print axioms Lambda.Labelled.History.induced_path_transport
#print axioms AG.Marker.actual_path_no_copy
#print axioms AG.initial_bound_binding_access
#print axioms AG.encode_closed_matches
#print axioms Lambda.Labelled.History.internal_region_degree
#print axioms Lambda.Labelled.normal_head_not_argument_copy
#print axioms AG.Marker.old_marker_replay
#print axioms AG.encode_closed_transparency
#print axioms Lambda.Labelled.normal_head_not_disjoint_internal
#print axioms Lambda.Labelled.TermRoutes.atomic_origin_exists
#print axioms Lambda.Labelled.History.induced_atomic_node_routes
#print axioms Lambda.Labelled.History.region_original_lambda
#print axioms AG.Marker.written_marker_fixed
#print axioms Lambda.Labelled.History.argument_region_origins
#print axioms AG.Marker.no_written_terminal_tail
#print axioms AG.encode_addressing
#print axioms AG.encode_context_no_revisit
#print axioms AG.encode_nesting
#print axioms AG.Independence.rooted_source_prefix
#print axioms AG.Labelling.join_contextTrace
#print axioms AG.encode_context_port_identity
#print axioms AG.Independence.rooted_proper_occurrence
#print axioms Lambda.Labelled.atomic_family_iff_degree
#print axioms AG.Forward.no_reversed_target
#print axioms AG.Independence.expanded_ordinary_base
#print axioms AG.encode_heighting
#print axioms AG.Heighting.first_cro_lower
#print axioms AG.encode_source_relabel
#print axioms AG.Heighting.path_height
#print axioms Lambda.Labelled.History.local_degree_region_reflection
#print axioms Lambda.Labelled.canonical_of_prepend
#print axioms AG.encode_context_target_independence
#print axioms AG.BetaEdge.insert_reverse_prefix_labeling
#print axioms AG.Independence.expanded_ordinary_prefix_base
#print axioms AG.ExpandedNesting.binding_prefix_unique
#print axioms Lambda.Labelled.normal_two_events_argument_internal
#print axioms Lambda.Labelled.StepAt.regional_degree_residual
#print axioms AG.encode_source_prefix_no_events
#print axioms Lambda.Labelled.rank_two_compound_normal
#print axioms AG.encode_closed_independence
#print axioms AG.encode_closed_ordinary_invariants
#print axioms AG.InitialOffsets.Shape.execute_replace
#print axioms Lambda.Labelled.RegionalOrigins.history_of_initial_outside
#print axioms Lambda.Labelled.History.redex_uses_initial_degree
#print axioms Graph.NetIso.ordinaryInvariants
#print axioms AG.initial_empty_trace_invariants
#print axioms AG.encode_balance
#print axioms AG.LevelBalance.proper_principal_indices
#print axioms AG.Schema.balance_preservation
#print axioms AG.PathSite.reduce_balance
#print axioms AG.initial_trace_balance
#print axioms AG.initial_trace_flowBalance
#print axioms AG.PathSite.principal_flow
end Lamping.Checks.Phase5Review






















import Lamping.Lamping.ProperNodeAncestry
import Lamping.Lamping.PrincipalSiteRealization
import Lamping.Graph.CarrierRenaming
import Lamping.Lamping.ProperSourceReaderExpressions
import Lamping.Lambda.ClosedVariableBinders
import Lamping.Lamping.BetaForwardCoverageMatching
import Lamping.Lamping.CompletePhysicalLambdaOrigins
import Lamping.Lamping.PhysicalCorridorTypedHistories
import Lamping.Lamping.NetIsoBetaFiberTransport
import Lamping.Lamping.RelativeHistoryTyped
import Lamping.Lamping.PhysicalCorridorSites
import Lamping.Lamping.PairedAnchoredReset
import Lamping.Checks.Soundness
import Lamping.Lamping.MatchingSpecifiedBindingShell
import Lamping.Lamping.BindingSuffixUniqueness
import Lamping.Lamping.InitialTransparency
import Lamping.Lamping.StepPositionEvaluationOrigins
import Lamping.Lamping.RetainedLambdaEvaluation
import Lamping.Lambda.CopiedLambdaBodies
import Lamping.Lambda.BetaBoundVariableOrigins
import Lamping.Lamping.MatchingSharedSyntaxEvaluation
import Lamping.Lamping.SourceRouteEvaluation
import Lamping.Lambda.NestedBinderCoordinates
import Lamping.Lamping.MatchingRouteSyntaxWalk
import Lamping.Lamping.MatchingSelectedRouteWalk
import Lamping.Lamping.MatchingSelectedRoutePorts
import Lamping.Lamping.MatchingSelectedDegreeRealization
import Lamping.Lamping.BetaEncodingIso
import Lamping.Checks.Paths
import Lamping.Lamping.MatchingBetaPrincipalPath
import Lamping.Lamping.InitialNesting
import Lamping.Lamping.MatchingSourcePortUniqueness
import Lamping.Lamping.MatchingSourceEdgeRealization
import Lamping.Lamping.MatchingSourceEdges
import Lamping.Lamping.MatchingSourceBinders
import Lamping.Lambda.SourceBinderOccurrences
import Lamping.Lambda.SelectedDevelopmentRoutes
import Lamping.Lambda.MarkedDevelopmentOrigins
import Lamping.Lambda.ContractumPositionOrigins
import Lamping.Lambda.SubstitutionPositionOrigins
import Lamping.Lamping.MatchingBetaFiber
import Lamping.Lamping.MatchingRedexEndpointUniqueness
import Lamping.Lamping.MatchingVariableAccess
import Lamping.Lamping.MatchingSubtermAccess
import Lamping.Lamping.InitialMatching
import Lamping.Lambda.FiniteRedexFibers
import Lamping.Lambda.LabelFamilyDegreeEquivalence
import Lamping.Lambda.LabelCanonicalDegreeUniqueness
import Lamping.Lambda.LabelContractedDegreeReflection
import Lamping.Lambda.LabelAnchoredWalkReflection
import Lamping.Lambda.LabelImageTraversal
import Lamping.Lambda.LabelSharedBinderPorts
import Lamping.Lambda.LabelArgumentBinderScope
import Lamping.Lambda.LabelCopyBinderOrigins
import Lamping.Lambda.LabelContextualImageCollisions
import Lamping.Lambda.LabelExpandedCodeAlignment
import Lamping.Lambda.LabelHeadMarkerParsing
import Lamping.Lambda.LabelAncestorBinderProtection
import Lamping.Lambda.LabelContractedOccurrences
import Lamping.Lambda.LabelCanonicalFirstRedex
import Lamping.Lambda.LabelCanonicalSupport
import Lamping.Lambda.LabelSilentHeadProjection
import Lamping.Lambda.LabelSilentHeadLocality
import Lamping.Lambda.LabelProtectedHeadCut
import Lamping.Lambda.LabelArgumentRegionalSchedules
import Lamping.Lambda.LabelRegionalSchedules
import Lamping.Lambda.LabelArgumentDegreeInterior
import Lamping.Lambda.LabelContextualHeadCut
import Lamping.Lambda.LabelHeadCutRoots
import Lamping.Lambda.LabelHeadCutComponents
import Lamping.Lambda.LabelHeadFreeWalks
import Lamping.Lambda.LabelFunctionPullback
import Lamping.Lambda.LabelRegionalBodyPullback
import Lamping.Lambda.LabelRegionalReflection
import Lamping.Lambda.LabelInternalRegions
import Lamping.Lambda.LabelContextualCopyCover
import Lamping.Lambda.LabelContextualRegions
import Lamping.Lambda.LabelDisjointRegions
import Lamping.Lambda.LabelBodySubregions
import Lamping.Lambda.LabelSubstitutionRegions
import Lamping.Lambda.LabelArgumentSubregions
import Lamping.Lambda.LabelCopyInteriors
import Lamping.Lambda.LabelBetaCopyCover
import Lamping.Lambda.LabelSubstitutionCopies
import Lamping.Lambda.LabelCopyComponents
import Lamping.Lambda.LabelFirstCandidateOrder
import Lamping.Lambda.LabelDegreeAtoms
import Lamping.Lambda.LabelPathInjective
import Lamping.Lambda.LabelEdgeSubstitution
import Lamping.Lambda.LabelRegions
import Lamping.Lambda.LabelCanonicalInternality
import Lamping.Lambda.LabelAtomicOrigins
import Lamping.Lambda.LabelAtomicFamilies
import Lamping.Lambda.LabelRegionTransport
import Lamping.Lambda.LabelRegionalOrigins
import Lamping.Lambda.LabelFirstRedex
import Lamping.Lambda.LabelHeadPorts
import Lamping.Lambda.LabelRoutes
import Lamping.Lambda.SingleContraction
import Lamping.Lambda.DegreeFamily
import Lamping.Lambda.LabelResiduals
import Lamping.Lambda.LabelPermutation
namespace Lamping.Checks.DegreeFamily
open Lamping.Lambda Lamping.Lambda.Labelled
private def a := Label.atom 0
example : (Label.under (a.concat a)).length = 1 := rfl
example : ¬ IsAtomic (Label.under a) := by
  rintro ⟨n,h⟩; cases h

def identity : Term := .lam (.var 0)
def duplicateSource : Term := .app (.lam (.app (.var 0) (.var 0))) (.app identity identity)
def duplicateInitial : LTerm := initLabels duplicateSource
def duplicateTarget : LTerm := LTerm.contract (Label.atom 0) (Label.atom 1)
    (.app (Label.atom 2) (.var (Label.atom 3) 0) (.var (Label.atom 4) 0))
    (.app (Label.atom 5) (.lam (Label.atom 6) (.var (Label.atom 7) 0))
      (.lam (Label.atom 8) (.var (Label.atom 9) 0)))
theorem duplication_init : INIT duplicateInitial := init_is_INIT _
theorem actual_duplication : StepAt [] duplicateInitial duplicateTarget := .root _ _ _ _
theorem duplication_history : History [[]] duplicateInitial duplicateTarget :=
  .cons actual_duplication (.nil _)
theorem copied_degrees_equal : duplicateTarget.degreeAt [.fn]=some (Label.atom 6) ∧
    duplicateTarget.degreeAt [.arg]=some (Label.atom 6) := ⟨rfl,rfl⟩
theorem degree_original_transport : degreeAlong duplicateInitial [[]] [.fn]=some (Label.atom 6) := rfl

def creationSource : Term := .app (.app identity identity) identity
def creationInitial : LTerm := initLabels creationSource
def creationTarget : LTerm :=
  .app (Label.atom 0)
    (LTerm.contract (Label.atom 1) (Label.atom 2) (.var (Label.atom 3) 0)
      (.lam (Label.atom 4) (.var (Label.atom 5) 0)))
    (.lam (Label.atom 6) (.var (Label.atom 7) 0))
theorem actual_creation : StepAt [.fn] creationInitial creationTarget := .fn (.root _ _ _ _)
theorem created_degree : creationTarget.degreeAt []=some
    ((Label.atom 1).concat ((Label.atom 2).over.concat
      ((Label.atom 3).concat ((Label.atom 2).under.concat (Label.atom 4))))) := rfl
theorem no_reinitialization : degreeAlong creationInitial [[.fn]] [] ≠
    degreeAlong (initLabels creationTarget.erase) [] [] := by decide

def eraseInitial : LTerm := initLabels (.app (.lam identity) (.app identity identity))
theorem actual_erasure : StepAt [] eraseInitial
    (LTerm.contract (Label.atom 0) (Label.atom 1)
      (.lam (Label.atom 2) (.var (Label.atom 3) 0))
      (.app (Label.atom 4) (.lam (Label.atom 5) (.var (Label.atom 6) 0))
        (.lam (Label.atom 7) (.var (Label.atom 8) 0)))) := .root _ _ _ _
example : (LTerm.contract a a (.lam a (.var a 1)) (.var a 0)).erase = .lam (.var 1) := rfl

-- The directed edge substitution must reverse a substituted backwards edge.
example : EdgeWord.substitute (fun n => [⟨n,false⟩,⟨n+1,false⟩]) [⟨2,true⟩] =
    [⟨3,true⟩,⟨2,true⟩] := rfl
example : (Label.atom 2).under.edgeWord ≠ (Label.atom 2).edgeWord := by decide

-- INIT uniqueness is essential: arbitrary repeated labels do not separate redexes.
def badInitial : LTerm := .app a
    (.app a (.lam a (.var a 0)) (.var a 0))
    (.app a (.lam a (.var a 0)) (.var a 0))
example : badInitial.degreeAt [.fn]=badInitial.degreeAt [.arg] := rfl
example : ¬ INIT badInitial := by intro h; exact (by decide : ¬ badInitial.labels.Nodup) h.2
example : ([Step.fn] : Path) ≠ [.arg] := by decide

#print axioms actual_duplication
#print axioms copied_degrees_equal
#print axioms no_reinitialization
#print axioms LTerm.initial_degree_injective
#print axioms Label.edgeWord_relabel


def duplicateDerivation : Derivation duplicateSource (.app (.app identity identity) (.app identity identity)) :=
  ⟨[[]],.cons ⟨_,_,rfl,rfl⟩ (.nil _)⟩
def originalArgumentRedex : RedexOcc duplicateSource := ⟨[.arg],_,rfl,True.intro⟩
def copiedLeftRedex : RedexOcc (.app (.app identity identity) (.app identity identity)) :=
  ⟨[.fn],_,rfl,True.intro⟩
def duplicateMarkedTarget : Marked := Marked.contract
  (.app [] (.var 0) (.var 0))
  (.app [[.arg]] (.lam (.var 0)) (.lam (.var 0)))
theorem true_copied_residual : duplicateDerivation.Residual originalArgumentRedex copiedLeftRedex :=
  ⟨duplicateMarkedTarget,
    .cons (.appRoot [[]] (.app [] (.var 0) (.var 0))
      (.app [[.arg]] (.lam (.var 0)) (.lam (.var 0)))) (.nil _),
    rfl,by decide⟩
theorem copied_residual_degree : duplicateTarget.degreeAt copiedLeftRedex.val=
    duplicateInitial.degreeAt originalArgumentRedex.val :=
  Labelled.Derivation.residual_degree duplicateDerivation duplicateInitial duplicateTarget rfl
    duplication_history originalArgumentRedex copiedLeftRedex true_copied_residual
#print axioms Labelled.Derivation.residual_degree
#print axioms copied_residual_degree


def duplicateParallelStep : ParallelStep [[]] duplicateSource
    (.app (.app identity identity) (.app identity identity)) := singleContraction ⟨_,_,rfl,rfl⟩
def initialPoint : RedexWithHistory duplicateSource := ⟨_,.nil _,originalArgumentRedex⟩
def copiedPoint : RedexWithHistory duplicateSource := ⟨_,.single duplicateParallelStep,copiedLeftRedex⟩
theorem cross_history_family : FamilyEq initialPoint copiedPoint := by
  apply FamilyEq.copy
  refine ⟨.single duplicateParallelStep,.refl _,?_⟩
  have eq : (ParallelHistory.single duplicateParallelStep).derivation=duplicateDerivation :=
    Lamping.Lambda.Derivation.ext rfl
  rw [eq]
  exact true_copied_residual
theorem cross_history_degree : degreeAlong duplicateInitial initialPoint.history.derivation.paths
    initialPoint.redex.val=degreeAlong duplicateInitial copiedPoint.history.derivation.paths copiedPoint.redex.val :=
  Labelled.FamilyEq.degreeAlong cross_history_family duplicateInitial rfl
#print axioms Labelled.PermEq.labelled_unique
#print axioms Labelled.FamilyEq.degreeAlong
#print axioms cross_history_degree



def nestedSource : Term := .app (.lam (.lam (.var 1))) identity
def nestedInitial : LTerm := initLabels nestedSource
def nestedTarget : LTerm :=
  .lam (((Label.atom 0).concat (Label.atom 1).over).concat (Label.atom 2))
    (.lam (((Label.atom 3).concat (Label.atom 1).under).concat (Label.atom 4))
      (.var (Label.atom 5) 0))
theorem nested_step : StepAt [] nestedInitial nestedTarget := .root _ _ _ _
private theorem atom_route (edges : List SourceEdge) (n : Nat) (a b : SourcePort)
    (member : (⟨Label.atom n,a,b⟩ : SourceEdge)∈edges) : SourceRoute edges a (Label.atom n) b :=
  .atom member rfl

/-- The surviving lambda has a compound current label but original binder
identity atom2; the copied inner lambda remains atom4, never either compound. -/
theorem nested_origin_routes : TermRoutes (sourceEdges [] .external nestedInitial) [] .external nestedTarget := by
  apply TermRoutes.lam (origin := Label.atom 2)
  · exact .over (appId := Label.atom 0) (lamId := Label.atom 1) (atom_route _ 0 _ _ (by decide)) (atom_route _ 1 _ _ (by decide))
      (atom_route _ 2 _ _ (by decide))
  · apply TermRoutes.lam (origin := Label.atom 4)
    · exact .under (appId := Label.atom 0) (lamId := Label.atom 1) (atom_route _ 3 _ _ (by decide)) (atom_route _ 1 _ _ (by decide))
        (atom_route _ 4 _ _ (by decide))
    · exact .var (atom_route _ 5 _ _ (by decide))

def captureSource : Term := .app (.lam (.lam (.var 1))) (.var 0)
def captureInitial : LTerm := initLabels captureSource
def captureTarget : LTerm :=
  .lam (((Label.atom 0).concat (Label.atom 1).over).concat (Label.atom 2))
    (.var (((Label.atom 3).concat (Label.atom 1).under).concat (Label.atom 4)) 1)
theorem capture_step : StepAt [] captureInitial captureTarget := .root _ _ _ _
theorem capture_routes : TermRoutes (sourceEdges [] .external captureInitial) [] .external captureTarget := by
  apply TermRoutes.lam (origin := Label.atom 2)
  · exact .over (appId := Label.atom 0) (lamId := Label.atom 1) (atom_route _ 0 _ _ (by decide)) (atom_route _ 1 _ _ (by decide))
      (atom_route _ 2 _ _ (by decide))
  · exact .var (.under (appId := Label.atom 0) (lamId := Label.atom 1) (atom_route _ 3 _ _ (by decide)) (atom_route _ 1 _ _ (by decide))
      (atom_route _ 4 _ _ (by decide)))
#print axioms nested_origin_routes
#print axioms capture_routes
#print axioms History.generated_source_routes



def commutingSource : Term := .app (.app identity identity) (.app identity identity)
def commutingInitial : LTerm := initLabels commutingSource
def createdFunction : LTerm := LTerm.contract (Label.atom 1) (Label.atom 2) (.var (Label.atom 3) 0)
    (.lam (Label.atom 4) (.var (Label.atom 5) 0))
def independentArgument : LTerm := LTerm.contract (Label.atom 6) (Label.atom 7) (.var (Label.atom 8) 0)
    (.lam (Label.atom 9) (.var (Label.atom 10) 0))
def commutingLeft : LTerm := .app (Label.atom 0) createdFunction
    (.app (Label.atom 6) (.lam (Label.atom 7) (.var (Label.atom 8) 0))
      (.lam (Label.atom 9) (.var (Label.atom 10) 0)))
def commutingRight : LTerm := .app (Label.atom 0) createdFunction independentArgument
theorem commuting_left_history : History [[.fn]] commutingInitial commutingLeft := .cons (.fn (.root _ _ _ _)) (.nil _)
theorem commuting_right_history : History [[.arg],[.fn]] commutingInitial commutingRight :=
  .cons (.arg (.root _ _ _ _)) (.cons (.fn (.root _ _ _ _)) (.nil _))

theorem compound_cross_history_path_injective :
    createdFunction.label=createdFunction.label :=
  History.generated_label_path_injective commuting_left_history commuting_right_history (init_is_INIT _)
    (List.mem_cons_of_mem _ (List.mem_append_left _ (label_mem_labels createdFunction)))
    (List.mem_cons_of_mem _ (List.mem_append_left _ (label_mem_labels createdFunction))) rfl

-- The full code distinguishes bar structure that arbitrary edgeWord erases.
example : (Label.atom 0).edgeWord=(Label.atom 0).over.edgeWord := rfl
example : (Label.atom 0).pathCode false ≠ (Label.atom 0).over.pathCode false := by decide
#print axioms compound_cross_history_path_injective
#print axioms History.generated_label_path_injective

/-- The local target's first atomic edge actually expands to a compound
original route; reversing it reverses every edge and its order. -/
theorem compound_reverse_path_transport :
    ∃ nodes : Nat → Label,
      GraphWalk (sourceEdges [] .external nestedInitial)
        ((SourcePort.lamContext (Label.atom 0)).relabel nodes)
        (EdgeWord.reverse nestedTarget.label.edgeWord) .external := by
  have history : History [[]] nestedInitial nestedTarget := .cons nested_step (.nil _)
  obtain ⟨nodes,transport⟩ := history.induced_path_transport (init_is_INIT _)
  have walk : GraphWalk (sourceEdges [] .external (initLabels nestedTarget.erase))
      (.lamContext (Label.atom 0)) [⟨0,true⟩] .external :=
    .edge (.backward (e := ⟨Label.atom 0,.external,.lamContext (Label.atom 0)⟩) (by decide) rfl)
  refine ⟨nodes,?_⟩
  exact transport walk

example : EdgeWord.substitute
    (fun _ => [⟨0,false⟩,⟨1,true⟩,⟨2,false⟩]) [⟨7,true⟩]=
      [⟨2,true⟩,⟨1,false⟩,⟨0,true⟩] := rfl
#print axioms compound_reverse_path_transport
#print axioms History.induced_path_transport

def regionalInitial : LTerm := initLabels (.lam creationSource)
def regionalTarget : LTerm := .lam (Label.atom 0)
  (.app (Label.atom 1)
    (LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
      (.lam (Label.atom 5) (.var (Label.atom 6) 0)))
    (.lam (Label.atom 7) (.var (Label.atom 8) 0)))
theorem regional_history : History [[.body,.fn]] regionalInitial regionalTarget :=
  .cons (.body (.fn (.root _ _ _ _))) (.nil _)
theorem compound_degree_stays_in_region :
    EdgeWord.Within (SourceRegion (initFrom 1 creationSource))
      (((Label.atom 2).concat ((Label.atom 3).over.concat
        ((Label.atom 4).concat ((Label.atom 3).under.concat (Label.atom 5))))).edgeWord) := by
  exact regional_history.internal_region_degree (init_is_INIT _) (site := [.body]) rfl
    (by intro p member; have eq := List.mem_singleton.mp member; exact ⟨[.fn],eq⟩)
    (suffix := []) rfl

/-- Degree support alone cannot force an arbitrary history to be internal:
an unrelated function-body step leaves this argument degree unchanged. -/
def irrelevantInitial : LTerm := initLabels
  (.app (.lam (.app identity (.var 0))) (.app identity identity))
def irrelevantTarget : LTerm := .app (Label.atom 0)
  (.lam (Label.atom 1)
    (LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0) (.var (Label.atom 5) 0)))
  (.app (Label.atom 6) (.lam (Label.atom 7) (.var (Label.atom 8) 0))
    (.lam (Label.atom 9) (.var (Label.atom 10) 0)))
theorem irrelevant_history : History [[.fn,.body]] irrelevantInitial irrelevantTarget :=
  .cons (.fn (.body (.root _ _ _ _))) (.nil _)
theorem irrelevant_degree_inside : irrelevantTarget.degreeAt [.arg]=some (Label.atom 7) ∧
    EdgeWord.Within (SourceRegion (initFrom 6 (.app identity identity))) (Label.atom 7).edgeWord := by
  exact ⟨rfl,by simp [EdgeWord.Within,SourceRegion,initFrom,identity,LTerm.labels]⟩
theorem irrelevant_history_not_internal :
    ¬ (∀ p∈([[.fn,.body]] : List Path),∃ suffix,p=[.arg]++suffix) := by
  intro inside
  obtain ⟨suffix,wrong⟩ := inside [.fn,.body] List.mem_cons_self
  cases wrong
#print axioms compound_degree_stays_in_region
#print axioms irrelevant_history_not_internal

def duplicateRootBeta : BetaAt duplicateSource []
    (.app (.app identity identity) (.app identity identity)) := ⟨_,_,rfl,rfl⟩
def copiedBeta : BetaAt (.app (.app identity identity) (.app identity identity)) [.fn]
    (.app identity (.app identity identity)) := ⟨_,_,rfl,rfl⟩
def copiedTail : ParallelHistory (.app (.app identity identity) (.app identity identity))
    (.app identity (.app identity identity)) := .single (singleContraction copiedBeta)

/-- The canonical hypothesis excludes contraction of the duplicator followed
by a program wholly inside just its left argument copy: rule (iv) is real. -/
theorem copied_tail_not_normal :
    ¬ ExtractionNormal (.of (.cons (singleContraction duplicateRootBeta) copiedTail)
      (.cons duplicateRootBeta (.single copiedBeta))) := by
  intro normal
  apply normal_head_not_argument_copy duplicateRootBeta (body := .app (.var 0) (.var 0))
    (argument := .app identity identity) rfl (occurrence := [.fn]) rfl copiedTail
    (.single copiedBeta) (by decide) normal
  intro p member
  have eq : p=[.fn] := by
    simpa [copiedTail,ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using member
  exact ⟨[],eq⟩
#print axioms copied_tail_not_normal

def regionalDegree : Label := (Label.atom 2).concat ((Label.atom 3).over.concat
  ((Label.atom 4).concat ((Label.atom 3).under.concat (Label.atom 5))))

/-- The compound current degree originates in the second original lambda of
this subtree (atom5), rather than its first lambda (atom3). -/
theorem compound_region_original_second_lambda :
    ∃ appId body,SourceRoute (sourceEdges [] .external regionalInitial)
      (.appFn appId) regionalDegree (.lamContext (Label.atom 5)) ∧
      regionalInitial.subterm [.body,.fn,.arg]=some (.lam (Label.atom 5) body) := by
  obtain ⟨appId,lamId,suffix,body,route,located⟩ :=
    regional_history.region_original_lambda (init_is_INIT _) (site := [.body])
      (subtree := initFrom 1 creationSource) rfl (p := [.body])
      (l := regionalDegree) rfl compound_degree_stays_in_region
  obtain ⟨n,last,origin⟩ := route.lam_last_atom
  have lastEq : (some 5 : Option Nat)=some n := last
  have nn : n=5 := (Option.some.inj lastEq).symm
  have eq : lamId=Label.atom 5 := by simpa only [nn] using origin
  have known : regionalInitial.subterm [.body,.fn,.arg]=
      some (.lam (Label.atom 5) (.var (Label.atom 6) 0)) := rfl
  have path := LTerm.subterm_label_injective regionalInitial (init_is_INIT _).2 located known eq
  rw [path] at located
  exact ⟨appId,body,eq ▸ route,eq ▸ located⟩
#print axioms compound_region_original_second_lambda

/-- Even after actual duplication, the copy's degree locates both original
nodes inside the old argument. It does not assert a unique later copy. -/
theorem copied_degree_original_argument_nodes :
    ∃ appId lamId appSuffix lamSuffix f arg body,
      SourceRoute (sourceEdges [] .external duplicateInitial) (.appFn appId)
        (Label.atom 6) (.lamContext lamId) ∧
      duplicateInitial.subterm ([.arg]++appSuffix)=some (.app appId f arg) ∧
      duplicateInitial.subterm ([.arg]++lamSuffix)=some (.lam lamId body) := by
  apply duplication_history.argument_region_node_occurrences duplication_init
    (site := [.arg]) (innerEnv := []) (parent := Label.atom 0)
    (subtree := initFrom 5 (.app identity identity)) (SourceSubterm.arg .nil)
    (p := [.fn]) rfl
  simp [EdgeWord.Within,SourceRegion,initFrom,identity,LTerm.labels]
#print axioms copied_degree_original_argument_nodes

theorem copied_atomic_has_actual_old_residual :
    ∃ r : RedexOcc duplicateInitial.erase,
      (⟨[[]],duplication_history.betaHistory⟩ : Derivation _ _).Residual r copiedLeftRedex :=
  duplication_history.atomic_degree_residual copiedLeftRedex (Label.atom 6) rfl ⟨6,rfl⟩
#print axioms History.atomic_degree_residual
#print axioms copied_atomic_has_actual_old_residual

theorem degree_reflects_actual_copy_family : FamilyEq initialPoint copiedPoint :=
  (initial_family_iff_degree duplicateInitial duplication_init originalArgumentRedex copiedPoint).mpr rfl

def afterCopyPoint : RedexWithHistory duplicateSource :=
  ⟨.app identity (.app identity identity),
    .cons duplicateParallelStep (.single (singleContraction copiedBeta)),
    ⟨[.arg],_,rfl,True.intro⟩⟩

/-- The two histories differ by a real left-copy contraction; equality of
the remaining atomic degrees reflects the existing family relation. -/
theorem two_histories_atomic_degree_reflects_family : FamilyEq copiedPoint afterCopyPoint :=
  (atomic_family_iff_degree duplicateInitial duplication_init copiedPoint afterCopyPoint ⟨6,rfl⟩).mpr rfl
#print axioms initial_family_iff_degree
#print axioms atomic_family_iff_degree
#print axioms History.atomic_degree_normal_prefix_empty
#print axioms two_histories_atomic_degree_reflects_family

/-- The local target's atomic degree reflects the existing compound global
degree in the original body region, after an actual internal contraction. -/
theorem compound_local_region_reflection :
    ∃ basisSubtree,(initLabels regionalTarget.erase).subterm [.body]=some basisSubtree ∧
      regionalTarget.degreeAt [.body]=some regionalDegree ∧
      (regionalDegree.Supported (SourceRegion (initFrom 1 creationSource)) ↔
        (Label.atom 2).Supported (SourceRegion basisSubtree)) := by
  exact regional_history.local_degree_region_reflection (init_is_INIT _) (site := [.body])
    (subtree := initFrom 1 creationSource) rfl
    (by intro p member; exact ⟨[.fn],List.mem_singleton.mp member⟩)
    (.nil regionalTarget) (.nil (initLabels regionalTarget.erase)) (p := [.body])
    (l := Label.atom 2) rfl

theorem outside_node_stays_unsupported :
    ¬ (Label.atom 0).Supported (SourceRegion (initFrom 1 creationSource)) := by
  intro support
  have reflected := regional_history.internal_label_support_iff (init_is_INIT _) (site := [.body])
    (subtree := initFrom 1 creationSource) rfl
    (by intro p member; exact ⟨[.fn],List.mem_singleton.mp member⟩)
    (p := []) (node := regionalTarget) (by simp [LTerm.subterm])
  obtain ⟨suffix,wrong⟩ := reflected.mp support
  cases wrong
#print axioms History.local_degree_region_reflection
#print axioms compound_local_region_reflection
#print axioms outside_node_stays_unsupported

def argCreationInitial : LTerm := initLabels (.app identity creationSource)
def argCreationTarget : LTerm := .app (Label.atom 0) (.lam (Label.atom 1) (.var (Label.atom 2) 0))
  (.app (Label.atom 3)
    (LTerm.contract (Label.atom 4) (Label.atom 5) (.var (Label.atom 6) 0)
      (.lam (Label.atom 7) (.var (Label.atom 8) 0)))
    (.lam (Label.atom 9) (.var (Label.atom 10) 0)))
def argCreatedDegree : Label := (Label.atom 4).concat ((Label.atom 5).over.concat
  ((Label.atom 6).concat ((Label.atom 5).under.concat (Label.atom 7))))
theorem arg_creation_step : StepAt [.arg,.fn] argCreationInitial argCreationTarget := .arg (.fn (.root _ _ _ _))
def argCreationLast : BetaAt argCreationTarget.erase [.arg] (.app identity identity) := ⟨_,_,rfl,rfl⟩
def argCreationPoint : RedexWithHistory argCreationInitial.erase :=
  ⟨argCreationTarget.erase,.single (singleContraction arg_creation_step.betaAt),⟨[.arg],argCreationLast.redex⟩⟩
def argCreationRun : ExtractionRun argCreationInitial.erase := .of
  (.cons (singleContraction arg_creation_step.betaAt) (.single (singleContraction argCreationLast)))
  (.cons arg_creation_step.betaAt (.single argCreationLast))
theorem arg_creation_represents : RunRepresents argCreationRun argCreationPoint :=
  ⟨argCreationLast,.single arg_creation_step.betaAt,rfl⟩
theorem arg_creation_normal : ExtractionNormal argCreationRun := by
  apply rank_two_compound_normal argCreationInitial (init_is_INIT _) argCreationRun rfl
    argCreationPoint arg_creation_represents
  rintro ⟨k,equal⟩
  change some argCreatedDegree=some (Label.atom k) at equal
  have lengths := congrArg Label.length (Option.some.inj equal)
  change 5=1 at lengths
  omega
theorem arg_creation_canonical : CanonicalRun argCreationRun :=
  canonical_of_normal_prefix arg_creation_normal
    ⟨argCreationPoint,arg_creation_represents,Standard.single_step _
      ⟨[.arg,.fn],arg_creation_step.betaAt.redex⟩ (leftmost_singleton _)⟩

/-- Both events of this genuinely canonical compound-created redex run are
proved internal to the original outer redex's argument. -/
theorem arg_creation_whole_run_internal : Internal [.arg] argCreationRun.history := by
  apply normal_two_events_argument_internal arg_creation_step argCreationLast arg_creation_normal
    (init_is_INIT _) (site := []) (subtree := initFrom 3 creationSource) rfl
    (lastDegree := argCreatedDegree) rfl
  simp [argCreatedDegree,Label.atom,Label.over,Label.under,Label.Supported,Letter.Supported,Label.concat,
    SourceRegion,initFrom,identity,creationSource,LTerm.labels,nodeCount]

theorem arg_creation_first_degree_support (region : Nat → Prop)
    (supported : argCreatedDegree.Supported region) : region 5 :=
  normal_two_events_support arg_creation_step argCreationLast arg_creation_normal
    (headDegree := Label.atom 5) rfl (lastDegree := argCreatedDegree) rfl supported
#print axioms normal_two_events_support
#print axioms normal_two_events_argument_internal
#print axioms arg_creation_canonical
#print axioms arg_creation_whole_run_internal

/-- This actual two-step history includes an independent argument contraction;
the compound root degree still has a genuine initial-redex degree atom. -/
theorem compound_history_initial_degree_candidate :
    ∃ r : RedexOcc commutingInitial.erase,∃ n,
      commutingInitial.degreeAt r.val=some (Label.atom n) ∧
        ∃ e∈createdFunction.label.edgeWord,e.atom=n :=
  commuting_right_history.redex_uses_initial_degree (init_is_INIT _) (p := []) rfl
#print axioms RegionalOrigins.history_of_initial_outside
#print axioms History.redex_uses_initial_degree
#print axioms compound_history_initial_degree_candidate

def commutingFunctionRedex : RedexOcc commutingInitial.erase := ⟨[.fn],_,rfl,True.intro⟩
theorem compound_lo_candidate_is_function :
    LeftmostSelected (degreeCandidates commutingInitial createdFunction.label) commutingFunctionRedex := by
  obtain ⟨r,selected⟩ := commuting_right_history.degree_candidate_exists (init_is_INIT _) (p := []) rfl
  have candidates : degreeCandidates commutingInitial createdFunction.label=[[.fn]] := rfl
  have point : r.val=[.fn] := List.mem_singleton.mp (candidates ▸ selected.1)
  have equal : r=commutingFunctionRedex := Subtype.ext point
  exact equal ▸ selected

-- This genuine history starts at [arg], whereas its degree's unique LO
-- source candidate is [fn]. Canonicality is essential for First Redex.
example : commutingFunctionRedex.val≠([.arg] : Path) := by decide
#print axioms History.degree_candidate_exists
#print axioms degree_candidate_unique
#print axioms compound_lo_candidate_is_function

/-- The actual unrelated argument head is absent from the final compound
degree, so all its original application/lambda turns are excluded as well. -/
theorem compound_degree_avoids_unrelated_head :
    ∃ appId lamId,appId≠Label.atom 6 ∧ lamId≠Label.atom 7 ∧
      HeadFreeRoute (sourceEdges [] .external commutingInitial) (Label.atom 6) (Label.atom 7)
        (.appFn appId) createdFunction.label (.lamContext lamId) := by
  apply commuting_right_history.generated_head_free_degree (init_is_INIT _)
    (p := [.arg]) (env := []) (ctx := .appArg (Label.atom 0))
    (body := .var (Label.atom 8) 0) (argument := .lam (Label.atom 9) (.var (Label.atom 10) 0))
    (SourceSubterm.arg .nil) (region := fun n => n≠7)
    (by intro support; exact support rfl) (q := []) rfl
  simp [Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under]
#print axioms SourceSubterm.head_function_edge_unique
#print axioms History.generated_head_free_degree
#print axioms compound_degree_avoids_unrelated_head
/-- The compound-created argument redex really uses the earlier atomic
source degree; event existence retains the entire actual pointed schedule. -/
theorem compound_pointed_fires_source_atom :
    ∃ v,StepAt [.arg] argCreationTarget v ∧
      FiresAtom [[.arg,.fn],[.arg]] argCreationInitial v 5 := by
  obtain ⟨v,last,erased⟩ := lift_betaAt (t := argCreationTarget) argCreationLast
  refine ⟨v,last,?_⟩
  exact (History.cons arg_creation_step (.nil _)).pointed_fires_initial_atom last (init_is_INIT _)
    (p := [.arg,.fn]) (env := []) (ctx := .appFn (Label.atom 3))
    (body := .var (Label.atom 6) 0) (argument := .lam (Label.atom 7) (.var (Label.atom 8) 0))
    (SourceSubterm.arg (SourceSubterm.fn .nil)) (l := argCreatedDegree) rfl (by
      simp [argCreatedDegree,Label.supported_concat,Label.Supported,Letter.Supported,
        Label.atom,Label.over,Label.under])

/-- This property concerns all bar payloads, not just the outer pieces. -/
example : ¬argCreatedDegree.BarsSafe (fun n => n≠5) := by
  simp [argCreatedDegree,Label.barsSafe_concat,Label.BarsSafe,Letter.BarsSafe,
    Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under]
#print axioms SourceRoute.initial_atom_exposure
#print axioms History.pointed_fires_initial_atom
#print axioms FiresAtom.initial_residual
#print axioms compound_pointed_fires_source_atom
def argCreationSourceRedex : RedexOcc argCreationInitial.erase :=
  ⟨[.arg,.fn],_,rfl,True.intro⟩

/-- The degree atom is converted all the way to actual frozen UsedSource,
not just to a syntactic occurrence in the final compound word. -/
theorem compound_candidate_is_actually_used :
    ∃ v,∃ last : StepAt [.arg] argCreationTarget v,
      UsedSource (.cons (singleContraction arg_creation_step.betaAt)
        (.single (singleContraction last.betaAt))) argCreationSourceRedex := by
  obtain ⟨v,last,erased⟩ := lift_betaAt (t := argCreationTarget) argCreationLast
  have event : FiresAtom [[.arg,.fn],[.arg]] argCreationInitial v 5 := by
    exact (History.cons arg_creation_step (.nil _)).pointed_fires_initial_atom last (init_is_INIT _)
      (p := [.arg,.fn]) (env := []) (ctx := .appFn (Label.atom 3))
      (body := .var (Label.atom 6) 0) (argument := .lam (Label.atom 7) (.var (Label.atom 8) 0))
      (SourceSubterm.arg (SourceSubterm.fn .nil)) (l := argCreatedDegree) rfl (by
        simp [argCreatedDegree,Label.supported_concat,Label.Supported,Letter.Supported,
          Label.atom,Label.over,Label.under])
  have used := event.used_source (init_is_INIT _) argCreationSourceRedex rfl
    (.cons (singleContraction arg_creation_step.betaAt) (.single (singleContraction last.betaAt)))
    (.cons arg_creation_step.betaAt (.single last.betaAt)) rfl
  exact ⟨v,last,used⟩
#print axioms History.degree_candidate_used
#print axioms History.candidate_not_left_of_head
#print axioms History.head_le_degree_candidate
#print axioms compound_candidate_is_actually_used
def binderCopySource : LTerm := initLabels (.lam
  (.app (.lam (.app (.var 0) (.var 0))) (.app (.var 0) (.var 0))))
def binderCopyTarget : LTerm := .lam (Label.atom 0)
  (LTerm.contract (Label.atom 1) (Label.atom 2)
    (.app (Label.atom 3) (.var (Label.atom 4) 0) (.var (Label.atom 5) 0))
    (.app (Label.atom 6) (.var (Label.atom 7) 0) (.var (Label.atom 8) 0)))
theorem binder_copy_step : StepAt [.body] binderCopySource binderCopyTarget := .body (.root _ _ _ _)
def binderCopyBasis : LTerm := initLabels binderCopyTarget.erase

/-- Two actual argument copies retain variable edges at the same outer
binder. The root app nodes remain available; only their incoming edges are
excluded. The general syntax/port kernel forbids the cross-copy turn. -/
theorem copied_variables_cannot_cross_external_binder :
    ¬SourceTurn (.lamBind (Label.atom 0)) (.lamBind (Label.atom 0)) := by
  let left : LTerm := .app (Label.atom 2) (.var (Label.atom 3) 0) (.var (Label.atom 4) 0)
  let right : LTerm := .app (Label.atom 5) (.var (Label.atom 6) 0) (.var (Label.atom 7) 0)
  have leftSite : SourceSubterm [] .external binderCopyBasis [.body,.fn]
      [Label.atom 0] (.appFn (Label.atom 1)) left := .body (.fn .nil)
  have rightSite : SourceSubterm [] .external binderCopyBasis [.body,.arg]
      [Label.atom 0] (.appArg (Label.atom 1)) right := .body (.arg .nil)
  have edgeLeft : SourceTraverse (sourceEdges [Label.atom 0] (.appFn (Label.atom 1)) left)
      (.appFn (Label.atom 2)) ⟨3,false⟩ (.lamBind (Label.atom 0)) :=
    .forward (e := ⟨Label.atom 3,.appFn (Label.atom 2),.lamBind (Label.atom 0)⟩)
      (by simp [left,sourceEdges,sourceBinder]) rfl
  have edgeRight : SourceTraverse (sourceEdges [Label.atom 0] (.appArg (Label.atom 1)) right)
      (.lamBind (Label.atom 0)) ⟨6,true⟩ (.appFn (Label.atom 5)) :=
    .backward (e := ⟨Label.atom 6,.appFn (Label.atom 5),.lamBind (Label.atom 0)⟩)
      (by simp [right,sourceEdges,sourceBinder]) rfl
  exact SourceTraverse.no_cross_copy_turn leftSite rightSite (init_is_INIT _)
    ((DisjointPositions.head_ne (by intro equal; cases equal) :
      DisjointPositions [.fn] [.arg]).prefix [.body]) edgeLeft edgeRight (by decide) (by decide)
#print axioms SourceSubterm.binder_not_in_disjoint
#print axioms SourceTraverse.no_cross_copy_turn
#print axioms SourceWalk.one_component
#print axioms copied_variables_cannot_cross_external_binder
/-- A copied lambda is located strictly below an actual argument copy root;
that root itself retains the old nonregional variable prefix. -/
theorem copied_node_located_in_actual_argument :
    ∃ site copy suffix,ArgumentOccurrence (.app (.var 0) (.var 0)) site ∧
      duplicateTarget.subterm site=some copy ∧ [.fn,.fn]=site++suffix ∧
      suffix≠[] ∧ ¬copy.label.Supported (SourceRegion (initFrom 5 (.app identity identity))) := by
  apply LTerm.contract_supported_node_in_copy
    (body := .app (Label.atom 2) (.var (Label.atom 3) 0) (.var (Label.atom 4) 0))
    (node := .lam (Label.atom 6) (.var (Label.atom 7) 0))
  · intro l member
    simp only [LTerm.labels,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp only [Label.atom,Label.Supported,Letter.Supported,SourceRegion] <;> decide
  · rfl
  · change Label.atom 6∈(initFrom 5 (.app identity identity)).labels
    decide
#print axioms LTerm.subst_supported_node_in_copy
#print axioms LTerm.contract_supported_node_in_copy
#print axioms copied_node_located_in_actual_argument
/-- The selected copy is derived from the actual degree and induced map.
Two copies exist; no copy site is supplied to the localization theorem. -/
theorem copied_degree_selects_one_actual_copy :
    ∃ site env ctx copy,ArgumentOccurrence (.app (.var 0) (.var 0)) site ∧
      SourceSubterm [] .external (initLabels duplicateTarget.erase) site env ctx copy ∧
      (Label.atom 2).Supported (SourceRegion copy) ∧
      ∀ e∈(Label.atom 2).edgeWord,Label.atom e.atom≠copy.label := by
  apply root_beta_argument_degree_one_copy duplication_init
    (.nil duplicateTarget) (.nil (initLabels duplicateTarget.erase))
    (p := [.fn]) (globalLabel := Label.atom 6) rfl rfl
  change Label.atom 6∈(initFrom 5 (.app identity identity)).labels
  decide
#print axioms root_beta_argument_edge_cover
#print axioms root_beta_argument_walk_one_copy
#print axioms root_beta_argument_degree_one_copy
#print axioms copied_degree_selects_one_actual_copy
def creationDuplicateInitial : LTerm := initLabels
  (.app (.lam (.app (.var 0) (.var 0))) creationSource)
def creationDuplicateArgument : LTerm := initFrom 5 creationSource
def creationDuplicateTarget : LTerm := LTerm.contract (Label.atom 0) (Label.atom 1)
  (.app (Label.atom 2) (.var (Label.atom 3) 0) (.var (Label.atom 4) 0)) creationDuplicateArgument
def creationDuplicateAfter : LTerm := .app creationDuplicateTarget.label
  (.app (((creationDuplicateArgument.prepend (Label.atom 1).under).prepend (Label.atom 3)).label)
    (LTerm.contract (Label.atom 6) (Label.atom 7) (.var (Label.atom 8) 0)
      (.lam (Label.atom 9) (.var (Label.atom 10) 0)))
    (.lam (Label.atom 11) (.var (Label.atom 12) 0)))
  ((creationDuplicateArgument.prepend (Label.atom 1).under).prepend (Label.atom 4))
def creationDuplicateBasisAfter : LTerm := .app (Label.atom 0)
  (.app (Label.atom 1)
    (LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
      (.lam (Label.atom 5) (.var (Label.atom 6) 0)))
    (.lam (Label.atom 7) (.var (Label.atom 8) 0))) (initFrom 9 creationSource)
def copiedCreatedLocalDegree : Label :=
  (LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
    (.lam (Label.atom 5) (.var (Label.atom 6) 0))).label

theorem creation_duplication_step : StepAt [] creationDuplicateInitial creationDuplicateTarget := .root _ _ _ _
theorem creation_copy_step : StepAt [.fn,.fn] creationDuplicateTarget creationDuplicateAfter := .fn (.fn (.root _ _ _ _))
theorem creation_basis_copy_step : StepAt [.fn,.fn] (initLabels creationDuplicateTarget.erase) creationDuplicateBasisAfter :=
  .fn (.fn (.root _ _ _ _))

/-- Localization also consumes a compound degree created after duplication,
with a real nonempty global/local tail and no chosen copy parameter. -/
theorem copied_compound_degree_selects_one_actual_copy :
    ∃ site env ctx copy,ArgumentOccurrence (.app (.var 0) (.var 0)) site ∧
      SourceSubterm [] .external (initLabels creationDuplicateTarget.erase) site env ctx copy ∧
      copiedCreatedLocalDegree.Supported (SourceRegion copy) ∧
      ∀ e∈copiedCreatedLocalDegree.edgeWord,Label.atom e.atom≠copy.label := by
  apply root_beta_argument_degree_one_copy (show INIT creationDuplicateInitial from init_is_INIT _)
    (.cons creation_copy_step (.nil _)) (.cons creation_basis_copy_step (.nil _))
    (p := [.fn]) (globalLabel := (LTerm.contract (Label.atom 6) (Label.atom 7) (.var (Label.atom 8) 0)
      (.lam (Label.atom 9) (.var (Label.atom 10) 0))).label) rfl rfl
  simp only [LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
    Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under,SourceRegion]
  decide
#print axioms copied_compound_degree_selects_one_actual_copy
def captureCopiedArgument : LTerm := .lam (Label.atom 5) (.var (Label.atom 6) 1)
def captureCopyBody : LTerm := .lam (Label.atom 3) (.var (Label.atom 4) 1)
def captureActualCopy : LTerm :=
  .lam ((Label.atom 4).concat ((Label.atom 2).under.concat (Label.atom 5))) (.var (Label.atom 6) 2)
def captureCopyContract : LTerm := LTerm.contract (Label.atom 1) (Label.atom 2) captureCopyBody captureCopiedArgument

theorem capture_actual_argument_interior : LTerm.CopyInterior captureCopiedArgument captureActualCopy :=
  LTerm.contract_argument_copy_interior (body := captureCopyBody) (argument := captureCopiedArgument)
    (site := [.body]) (by rfl)
    (beta := Label.atom 1) (alpha := Label.atom 2) rfl

/-- The actual copied variable is shifted to index 2 while its original node
label and source-relative path still point to the index-1 argument variable. -/
theorem capture_copy_nonroot_node_origin :
    ∃ old,captureCopiedArgument.subterm [.body]=some old ∧ old.label=Label.atom 6 := by
  exact capture_actual_argument_interior.nonroot_node
    (node := .var (Label.atom 6) 2) (p := [.body]) rfl (by decide)

/-- Regional localization uses the old atom identity, even across the real
capture-avoiding binder shift in the target. -/
theorem capture_copy_region_located : ∃ suffix : Path,([.body] : Path)=[.body]++suffix := by
  apply capture_actual_argument_interior.region_locates
    (show INIT captureCopiedArgument from ⟨by
      intro l member
      simp only [captureCopiedArgument,LTerm.labels,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> exact ⟨_,rfl⟩,by decide⟩)
    (regionTerm := .var (Label.atom 6) 1) (site := [.body]) rfl
    (node := .var (Label.atom 6) 2) (p := [.body]) rfl
  change Label.atom 6∈(.var (Label.atom 6) 1 : LTerm).labels
  decide
#print axioms LTerm.contract_argument_copy_interior
#print axioms LTerm.CopyInterior.region_locates
#print axioms capture_copy_nonroot_node_origin
#print axioms capture_copy_region_located
def properRegionDuplicateInitial : LTerm := initLabels
  (.app (.lam (.app (.var 0) (.var 0))) (.lam creationSource))
def properRegionArgument : LTerm := initFrom 5 (.lam creationSource)
def properRegionDuplicateTarget : LTerm := LTerm.contract (Label.atom 0) (Label.atom 1)
  (.app (Label.atom 2) (.var (Label.atom 3) 0) (.var (Label.atom 4) 0)) properRegionArgument

theorem proper_region_degree_selects_actual_copy :
    ∃ occurrence env ctx copy,ArgumentOccurrence (.app (.var 0) (.var 0)) occurrence ∧
      SourceSubterm [] .external (initLabels properRegionDuplicateTarget.erase)
        (occurrence++[.body]) env ctx copy ∧
      (Label.atom 4).Supported (SourceRegion copy) ∧
      ∀ e∈(Label.atom 4).edgeWord,Label.atom e.atom≠copy.label := by
  apply root_beta_argument_subregion_degree_one_copy
    (show INIT properRegionDuplicateInitial from init_is_INIT _)
    (regionSite := [.body]) (regionTerm := initFrom 6 creationSource) rfl
    (.nil properRegionDuplicateTarget) (.nil (initLabels properRegionDuplicateTarget.erase))
    (p := [.fn,.body,.fn]) (globalLabel := Label.atom 8) rfl rfl
  · change Label.atom 8∈(initFrom 6 creationSource).labels
    decide
  · change Label.atom 8≠Label.atom 6
    decide
#print axioms root_beta_argument_subregion_edge_cover
#print axioms root_beta_argument_subregion_walk_one_copy
#print axioms root_beta_argument_subregion_degree_one_copy
#print axioms proper_region_degree_selects_actual_copy
/-- The copied function lambda is a supported proper subregion, but its
redex application is outside that region. The incoming root-edge guard is
therefore necessary even for a real one-event pointed program. -/
theorem proper_region_root_guard_necessary :
    (Label.atom 6).Supported (SourceRegion (initFrom 6 identity)) ∧
      ¬(Label.atom 6).Supported (fun n => Label.atom n≠(initFrom 6 identity).label) ∧
      ¬Internal [.fn,.fn] (.single (singleContraction copiedBeta)) := by
  refine ⟨?_,?_,?_⟩
  · change Label.atom 6∈(initFrom 6 identity).labels
    decide
  · intro support
    exact support rfl
  · intro inside
    obtain ⟨suffix,equal⟩ := inside [.fn] (by change ([.fn] : Path)∈[[.fn]]; exact List.mem_cons_self)
    have lengths := congrArg List.length equal
    simp only [List.length_cons,List.length_nil,List.length_append] at lengths
    omega
#print axioms proper_region_root_guard_necessary
def retainedBody : LTerm := initFrom 2 (.app identity identity)
def outsideArgument : LTerm := initFrom 7 identity
def retainedBodyTarget : LTerm := LTerm.contract (Label.atom 0) (Label.atom 1) retainedBody outsideArgument

/-- The real contraction retains the original body lambda node; regional
support cannot be supplied by the unrelated substituted argument. -/
theorem supported_target_has_retained_body_node :
    ∃ old,retainedBody.subterm [.fn]=some old ∧ old.label=Label.atom 3 := by
  apply LTerm.contract_supported_body_node_origin
    (body := retainedBody) (argument := outsideArgument)
    (node := .lam (Label.atom 3) (.var (Label.atom 4) 0)) (p := [.fn])
    (beta := Label.atom 0) (alpha := Label.atom 1) (region := SourceRegion retainedBody)
  · intro l member
    simp only [outsideArgument,initFrom,identity,LTerm.labels,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;>
      simp only [Label.atom,Label.Supported,Letter.Supported,SourceRegion] <;> decide
  · change ¬Label.atom 1∈retainedBody.labels
    decide
  · rfl
  · change Label.atom 3∈retainedBody.labels
    decide

/-- The body root atom survives as a required part of the current root label,
even though beta has prepended its own nonregional compound prefix. -/
theorem retained_body_root_atom_cannot_be_avoided :
    ¬retainedBodyTarget.label.Supported (fun n => n≠2) := by
  obtain ⟨current,lookup,reflects⟩ := LTerm.contract_subterm_root_reflect
    (body := retainedBody) (argument := outsideArgument)
    (beta := Label.atom 0) (alpha := Label.atom 1) (p := [])
    (old := retainedBody) (by simp [LTerm.subterm])
  have same : current=retainedBodyTarget := by
    simpa only [LTerm.subterm,Option.some.injEq] using lookup.symm
  cases same
  intro support
  exact reflects _ support rfl
#print axioms LTerm.subst_supported_node_origin
#print axioms LTerm.contract_subterm_root_reflect
#print axioms LTerm.contract_supported_body_node_origin
#print axioms supported_target_has_retained_body_node
#print axioms retained_body_root_atom_cannot_be_avoided
def bodyRegionInitial : LTerm := initLabels (.app (.lam (.lam creationSource)) identity)
def bodyRegionContract : LTerm := LTerm.contract (Label.atom 0) (Label.atom 1)
  (initFrom 2 (.lam creationSource)) (initFrom 11 identity)
def bodyRegionAfter : LTerm := .lam bodyRegionContract.label
  (.app (Label.atom 3)
    (LTerm.contract (Label.atom 4) (Label.atom 5) (.var (Label.atom 6) 0)
      (.lam (Label.atom 7) (.var (Label.atom 8) 0)))
    (.lam (Label.atom 9) (.var (Label.atom 10) 0)))
def bodyRegionBasisAfter : LTerm := .lam (Label.atom 0)
  (.app (Label.atom 1)
    (LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
      (.lam (Label.atom 5) (.var (Label.atom 6) 0)))
    (.lam (Label.atom 7) (.var (Label.atom 8) 0)))
def bodyRegionLocalDegree : Label :=
  (LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
    (.lam (Label.atom 5) (.var (Label.atom 6) 0))).label

theorem body_region_head_step : StepAt [] bodyRegionInitial bodyRegionContract := .root _ _ _ _
theorem body_region_creation_step : StepAt [.body,.fn] bodyRegionContract bodyRegionAfter := .body (.fn (.root _ _ _ _))
theorem body_region_basis_creation_step : StepAt [.body,.fn] (initLabels bodyRegionContract.erase) bodyRegionBasisAfter :=
  .body (.fn (.root _ _ _ _))

/-- A genuine compound-created degree, after an ancestor beta, localizes to
the surviving proper body subregion in the exact same local tail schedule. -/
theorem compound_body_degree_stays_in_actual_subregion :
    ∃ env ctx copy,SourceSubterm [] .external (initLabels bodyRegionContract.erase) [.body] env ctx copy ∧
      bodyRegionLocalDegree.Supported (SourceRegion copy) ∧
      ∀ e∈bodyRegionLocalDegree.edgeWord,Label.atom e.atom≠copy.label := by
  apply root_beta_body_subregion_degree (show INIT bodyRegionInitial from init_is_INIT _)
    (regionSite := [.body]) (regionTerm := initFrom 3 creationSource) rfl
    (.cons body_region_creation_step (.nil _)) (.cons body_region_basis_creation_step (.nil _))
    (p := [.body]) (globalLabel := (LTerm.contract (Label.atom 4) (Label.atom 5) (.var (Label.atom 6) 0)
      (.lam (Label.atom 7) (.var (Label.atom 8) 0))).label) rfl rfl
  · simp only [LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
      Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under,SourceRegion]
    decide
  · simp only [LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
      Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under]
    decide
#print axioms root_beta_body_subregion_walk
#print axioms root_beta_body_subregion_degree
#print axioms compound_body_degree_stays_in_actual_subregion
def disjointRegionInitial : LTerm := initLabels (.app creationSource (.app identity identity))
def disjointRegionArgument : LTerm := LTerm.contract (Label.atom 9) (Label.atom 10) (.var (Label.atom 11) 0)
  (.lam (Label.atom 12) (.var (Label.atom 13) 0))
def disjointRegionAfterHead : LTerm := .app (Label.atom 0) (initFrom 1 creationSource) disjointRegionArgument
def disjointRegionAfterTail : LTerm := .app (Label.atom 0)
  (.app (Label.atom 1)
    (LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
      (.lam (Label.atom 5) (.var (Label.atom 6) 0)))
    (.lam (Label.atom 7) (.var (Label.atom 8) 0))) disjointRegionArgument
def disjointRegionBasisAfterTail : LTerm := .app (Label.atom 0)
  (.app (Label.atom 1)
    (LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
      (.lam (Label.atom 5) (.var (Label.atom 6) 0)))
    (.lam (Label.atom 7) (.var (Label.atom 8) 0))) (initFrom 9 identity)

theorem disjoint_region_head_step : StepAt [.arg] disjointRegionInitial disjointRegionAfterHead := .arg (.root _ _ _ _)
theorem disjoint_region_tail_step : StepAt [.fn,.fn] disjointRegionAfterHead disjointRegionAfterTail := .fn (.fn (.root _ _ _ _))
theorem disjoint_region_basis_tail_step : StepAt [.fn,.fn] (initLabels disjointRegionAfterHead.erase) disjointRegionBasisAfterTail :=
  .fn (.fn (.root _ _ _ _))

/-- An unrelated real argument contraction precedes creation of a compound
redex in the function region. Its exact tail still localizes there. -/
theorem disjoint_head_compound_degree_localizes :
    ∃ env ctx copy,SourceSubterm [] .external (initLabels disjointRegionAfterHead.erase) [.fn] env ctx copy ∧
      copiedCreatedLocalDegree.Supported (SourceRegion copy) ∧
      ∀ e∈copiedCreatedLocalDegree.edgeWord,Label.atom e.atom≠copy.label := by
  apply disjoint_region_head_step.disjoint_subregion_degree (init_is_INIT _)
    (headTerm := initFrom 9 (.app identity identity)) rfl
    (regionTerm := initFrom 1 creationSource) (site := [.fn]) rfl
    (DisjointPositions.head_ne (by intro same; cases same))
    (.cons disjoint_region_tail_step (.nil _)) (.cons disjoint_region_basis_tail_step (.nil _))
    (p := [.fn]) (globalLabel := copiedCreatedLocalDegree) rfl rfl
  · simp only [copiedCreatedLocalDegree,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
      Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under,SourceRegion]
    decide
  · simp only [copiedCreatedLocalDegree,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
      Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under]
    decide
#print axioms RegionCut.disjoint_subterm
#print axioms StepAt.disjoint_subregion_edge_cover
#print axioms StepAt.disjoint_subregion_degree
#print axioms disjoint_head_compound_degree_localizes
def contextualCaptureSource : LTerm := initLabels
  (.lam (.app (.lam (.lam (.var 1))) (.lam (.var 1))))
def contextualCaptureTarget : LTerm := .lam (Label.atom 0) captureCopyContract

theorem contextual_capture_step : StepAt [.body] contextualCaptureSource contextualCaptureTarget := .body (.root _ _ _ _)

/-- The real head lies below an outer binder, and the inserted argument lies
below another surviving binder. Global paths and original atom6 are retained
while the copied variable has index2. No local INIT offset is identified. -/
theorem contextual_capture_subregion_node_locates :
    ∃ occurrence copy suffix,ArgumentOccurrence captureCopyBody.erase occurrence ∧
      contextualCaptureTarget.subterm ([.body]++occurrence)=some copy ∧
      LTerm.CopyInterior captureCopiedArgument copy ∧
      ([.body,.body,.body] : Path)=(([.body]++occurrence)++[.body])++suffix := by
  apply contextual_capture_step.argument_subregion_node_locates (init_is_INIT _)
    (body := captureCopyBody) (argument := captureCopiedArgument)
    (beta := Label.atom 1) (alpha := Label.atom 2) rfl
    (regionSite := [.body]) (regionTerm := .var (Label.atom 6) 1) rfl
    (node := .var (Label.atom 6) 2) (p := [.body,.body,.body]) rfl
  change Label.atom 6∈(.var (Label.atom 6) 1 : LTerm).labels
  decide
#print axioms INIT.subterm
#print axioms StepAt.head_lookups
#print axioms StepAt.argument_subregion_node_locates
#print axioms StepAt.body_subregion_node_locates
#print axioms contextual_capture_subregion_node_locates
def contextualCreationSource : LTerm := initLabels
  (.lam (.app (.lam (.app (.var 0) (.var 0))) creationSource))
def contextualCreationArgument : LTerm := initFrom 6 creationSource
def contextualCreationContract : LTerm := LTerm.contract (Label.atom 1) (Label.atom 2)
  (.app (Label.atom 3) (.var (Label.atom 4) 0) (.var (Label.atom 5) 0)) contextualCreationArgument
def contextualCreationTarget : LTerm := .lam (Label.atom 0) contextualCreationContract
def contextualCreationAfter : LTerm := .lam (Label.atom 0) (.app contextualCreationContract.label
  (.app (((contextualCreationArgument.prepend (Label.atom 2).under).prepend (Label.atom 4)).label)
    (LTerm.contract (Label.atom 7) (Label.atom 8) (.var (Label.atom 9) 0)
      (.lam (Label.atom 10) (.var (Label.atom 11) 0)))
    (.lam (Label.atom 12) (.var (Label.atom 13) 0)))
  ((contextualCreationArgument.prepend (Label.atom 2).under).prepend (Label.atom 5)))
def contextualCreationBasisAfter : LTerm := .lam (Label.atom 0) (.app (Label.atom 1)
  (.app (Label.atom 2)
    (LTerm.contract (Label.atom 3) (Label.atom 4) (.var (Label.atom 5) 0)
      (.lam (Label.atom 6) (.var (Label.atom 7) 0)))
    (.lam (Label.atom 8) (.var (Label.atom 9) 0))) (initFrom 10 creationSource))
def contextualCreationLocalDegree : Label :=
  (LTerm.contract (Label.atom 3) (Label.atom 4) (.var (Label.atom 5) 0)
    (.lam (Label.atom 6) (.var (Label.atom 7) 0))).label

theorem contextual_creation_head_step : StepAt [.body] contextualCreationSource contextualCreationTarget := .body (.root _ _ _ _)
theorem contextual_creation_tail_step : StepAt [.body,.fn,.fn] contextualCreationTarget contextualCreationAfter :=
  .body (.fn (.fn (.root _ _ _ _)))
theorem contextual_creation_basis_tail_step : StepAt [.body,.fn,.fn] (initLabels contextualCreationTarget.erase) contextualCreationBasisAfter :=
  .body (.fn (.fn (.root _ _ _ _)))

/-- A real nonroot head duplicates its argument, then the chosen degree is
created by a real nonempty tail. Whole global/local INIT coordinates differ,
and the actual copy under the outer binder is selected without a site input. -/
theorem contextual_compound_degree_selects_copy :
    ∃ occurrence env ctx copy,ArgumentOccurrence (.app (.var 0) (.var 0)) occurrence ∧
      SourceSubterm [] .external (initLabels contextualCreationTarget.erase) (([.body]++occurrence)++[]) env ctx copy ∧
      contextualCreationLocalDegree.Supported (SourceRegion copy) ∧
      ∀ e∈contextualCreationLocalDegree.edgeWord,Label.atom e.atom≠copy.label := by
  apply contextual_creation_head_step.argument_subregion_degree (init_is_INIT _)
    (body := .app (Label.atom 3) (.var (Label.atom 4) 0) (.var (Label.atom 5) 0))
    (argument := contextualCreationArgument) (beta := Label.atom 1) (alpha := Label.atom 2) rfl
    (regionSite := []) (regionTerm := contextualCreationArgument) (by simp [LTerm.subterm])
    (.cons contextual_creation_tail_step (.nil _)) (.cons contextual_creation_basis_tail_step (.nil _))
    (p := [.body,.fn]) (globalLabel := (LTerm.contract (Label.atom 7) (Label.atom 8) (.var (Label.atom 9) 0)
      (.lam (Label.atom 10) (.var (Label.atom 11) 0))).label) rfl rfl
  · simp only [LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
      Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under,SourceRegion]
    decide
  · simp only [LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
      Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under]
    decide
#print axioms StepAt.argument_subregion_edge_cover
#print axioms StepAt.argument_subregion_walk
#print axioms StepAt.argument_subregion_degree
#print axioms StepAt.body_subregion_degree
#print axioms contextual_compound_degree_selects_copy
/-- Strict support reflects across a real internal prefix and the exact
local INIT coordinate change, preserving avoidance of the new region root. -/
theorem internal_compound_strict_region_transport :
    ∃ copy,(initLabels regionalTarget.erase).subterm [.body]=some copy ∧
      (Label.atom 2).Supported (SourceRegion copy) ∧
      ∀ e∈(Label.atom 2).edgeWord,Label.atom e.atom≠copy.label := by
  apply regional_history.internal_strict_region_transport (init_is_INIT _)
    (site := [.body]) (subtree := initFrom 1 creationSource) rfl
    (by intro p member; exact ⟨[.fn],List.mem_singleton.mp member⟩)
    (.nil regionalTarget) (.nil (initLabels regionalTarget.erase))
    (p := [.body]) (globalLabel := regionalDegree) rfl rfl
  · exact (Label.supported_iff_within _ _).mpr compound_degree_stays_in_region
  · simp only [regionalDegree,Label.supported_concat,Label.Supported,Letter.Supported,
      Label.atom,Label.over,Label.under]
    decide

/-- An actual contracted root continues to require its old application atom;
its compound prefix cannot be discarded by the coordinate change. -/
theorem contracted_root_preserves_old_root_atom :
    ¬(LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
      (.lam (Label.atom 5) (.var (Label.atom 6) 0))).label.Supported (fun n => n≠2) := by
  intro support
  have reflected := (StepAt.root (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
    (.lam (Label.atom 5) (.var (Label.atom 6) 0))).root_support support
  exact reflected rfl
#print axioms StepAt.root_support
#print axioms History.internal_strict_region_transport
#print axioms internal_compound_strict_region_transport
#print axioms contracted_root_preserves_old_root_atom
def reflectionBody : LTerm := .lam (Label.atom 1)
  (.app (Label.atom 2) (.lam (Label.atom 3) (.var (Label.atom 4) 0)) (.var (Label.atom 5) 1))
def reflectionValue : LTerm := .lam (Label.atom 20) (.var (Label.atom 21) 1)
def reflectionSigma := LTerm.single reflectionValue
def reflectionTarget : LTerm := .lam (Label.atom 1)
  (LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
    ((reflectionValue.rename Nat.succ).prepend (Label.atom 5)))

theorem regional_substitution_actual_step : StepAt [.body] (reflectionBody.subst reflectionSigma) reflectionTarget :=
  .body (.root _ _ _ _)

theorem regional_substitution_history : RegionalHistory (fun n => n<10) [[.body]]
    (reflectionBody.subst reflectionSigma) reflectionTarget :=
  .cons regional_substitution_actual_step rfl (by change 3<10; decide) (.nil _)

/-- The exact actual body-step schedule is reflected through a substitution
whose free argument has really been shifted below a surviving lambda. -/
theorem regional_substitution_program_reflects :
    ∃ oldTarget,History [[.body]] reflectionBody oldTarget ∧ reflectionTarget=oldTarget.subst reflectionSigma := by
  apply regional_substitution_history.subst_reflect
  intro i value put
  cases i with
  | succ i => cases put
  | zero =>
    have same : reflectionValue=value := LTerm.SubValue.put.inj put
    rw [←same]
    intro l member
    simp only [reflectionValue,LTerm.labels,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;>
      simp only [Label.atom,Label.Supported,Letter.Supported] <;> decide

/-- Without the outside-value condition a substituted variable may become a
lambda and create an actual redex absent from the original body. -/
theorem substitution_boundary_creation_blocks_unguarded_reflection :
    (LTerm.app (Label.atom 2) (.var (Label.atom 3) 0) (.var (Label.atom 4) 1)).degreeAt []=none ∧
      ∃ target,StepAt []
        ((LTerm.app (Label.atom 2) (.var (Label.atom 3) 0) (.var (Label.atom 4) 1)).subst
          (LTerm.single (.lam (Label.atom 5) (.var (Label.atom 6) 0)))) target :=
  ⟨rfl,_,.root _ _ _ _⟩
#print axioms LTerm.degreeAt_subst_reflect
#print axioms StepAt.subst_reflect
#print axioms RegionalHistory.subst_reflect
#print axioms regional_substitution_program_reflects
#print axioms substitution_boundary_creation_blocks_unguarded_reflection
/-- A true post-beta body step, including both the outer beta prefix and
an under-prefixed argument subsequently shifted under the surviving lambda. -/
def contractReflectionBodyTarget : LTerm := .lam (Label.atom 1)
  (LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0) (.var (Label.atom 5) 1))

theorem regional_contract_actual_step : StepAt [.body]
    (LTerm.contract (Label.atom 40) (Label.atom 41) reflectionBody reflectionValue)
    (LTerm.contract (Label.atom 40) (Label.atom 41) contractReflectionBodyTarget reflectionValue) :=
  ((StepAt.body (StepAt.root (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
    (.var (Label.atom 5) 1))).subst (LTerm.single (reflectionValue.prepend (Label.atom 41).under))).prepend _

theorem regional_contract_body_program_reflects :
    ∃ oldTarget,History [[.body]] reflectionBody oldTarget ∧
      LTerm.contract (Label.atom 40) (Label.atom 41) contractReflectionBodyTarget reflectionValue=
        LTerm.contract (Label.atom 40) (Label.atom 41) oldTarget reflectionValue := by
  have coloured : RegionalHistory (fun n => n<10) [[.body]]
      (LTerm.contract (Label.atom 40) (Label.atom 41) reflectionBody reflectionValue)
      (LTerm.contract (Label.atom 40) (Label.atom 41) contractReflectionBodyTarget reflectionValue) :=
    .cons regional_contract_actual_step rfl (by change 3<10; decide) (.nil _)
  apply coloured.contract_body_reflect
  intro l member
  simp only [reflectionValue,LTerm.labels,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;>
    simp only [Label.atom,Label.Supported,Letter.Supported] <;> decide
#print axioms LTerm.degreeAt_prepend
#print axioms StepAt.prepend_reflect
#print axioms RegionalHistory.prepend_reflect
#print axioms RegionalHistory.contract_body_reflect
#print axioms regional_contract_body_program_reflects

/-- The actual capture-sensitive body history admits an actual rule-(iii)
extraction. This consumes the constructed projection, rather than providing
its row or an extraction as a fixture assumption. -/
theorem regional_contract_function_extraction :
    ∃ tail : ParallelHistory (contract reflectionBody.erase reflectionValue.erase)
        (contract contractReflectionBodyTarget.erase reflectionValue.erase),
      ∃ ordinary : Atomic tail,tail.derivation.paths=[[.body]] ∧
      ¬ExtractionNormal (.of (.cons (singleContraction
        (show BetaAt (.app (.lam reflectionBody.erase) reflectionValue.erase) []
          (contract reflectionBody.erase reflectionValue.erase) from ⟨_,_,rfl,rfl⟩)) tail)
        (.cons ⟨_,_,rfl,rfl⟩ ordinary)) := by
  have history : BetaHistory [[.body]] (contract reflectionBody.erase reflectionValue.erase)
      (contract contractReflectionBodyTarget.erase reflectionValue.erase) :=
    .cons (by simpa only [LTerm.erase_contract] using regional_contract_actual_step.betaAt) (.nil _)
  obtain ⟨tail,ordinary,paths⟩ := history.atomic
  refine ⟨tail,ordinary,paths,?_⟩
  have coloured : RegionalHistory (fun n => n<10) [[.body]]
      (LTerm.contract (Label.atom 40) (Label.atom 41) reflectionBody reflectionValue)
      (LTerm.contract (Label.atom 40) (Label.atom 41) contractReflectionBodyTarget reflectionValue) :=
    .cons regional_contract_actual_step rfl (by change 3<10; decide) (.nil _)
  apply coloured.contract_not_normal ?_ (by decide) tail ordinary paths
  intro l member
  simp only [reflectionValue,LTerm.labels,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;>
    simp only [Label.atom,Label.Supported,Letter.Supported] <;> decide
#print axioms body_program_function_projection
#print axioms body_program_not_normal
#print axioms RegionalHistory.contract_not_normal
#print axioms regional_contract_function_extraction

/-- The actual compound degree has a head-restricted oriented walk, as does
its full under-style reversal, across two genuine commuting histories. -/
theorem compound_degree_restricted_walk :
    ∃ appId lamId,
      HeadFreeWalk (sourceEdges [] .external commutingInitial) (Label.atom 6) (Label.atom 7)
        (.appFn appId) createdFunction.label.edgeWord (.lamContext lamId) ∧
      HeadFreeWalk (sourceEdges [] .external commutingInitial) (Label.atom 6) (Label.atom 7)
        (.lamContext lamId) (EdgeWord.reverse createdFunction.label.edgeWord) (.appFn appId) := by
  obtain ⟨appId,lamId,_,_,route⟩ := compound_degree_avoids_unrelated_head
  exact ⟨appId,lamId,route.head_free_walk,route.head_free_walk.reverse⟩

/-- An ordinary binding-to-context turn at the blocked lambda is real but
cannot be used to join two edges in the restricted source component. -/
theorem head_binding_turn_is_blocked :
    SourceTurn (.lamBind (Label.atom 7)) (.lamContext (Label.atom 7)) ∧
    ¬HeadFreeTurn (Label.atom 6) (Label.atom 7) (.lamBind (Label.atom 7)) (.lamContext (Label.atom 7)) := by
  refine ⟨.lamUnder _,?_⟩
  intro turn
  exact turn.avoids_head.1 rfl
#print axioms HeadFreeTurn.avoids_head
#print axioms HeadFreeRoute.head_free_walk
#print axioms compound_degree_restricted_walk
#print axioms head_binding_turn_is_blocked

/-- Static root-head geometry selects the original argument from a real
compound-created degree, without a component or cover supplied by the test. -/
theorem compound_root_head_cut_selects_argument :
    argCreatedDegree.Supported (SourceRegion (initFrom 3 creationSource)) := by
  have actual := History.cons arg_creation_step (.nil _)
  have cut := actual.root_head_degree_region (body := .var (Label.atom 2) 0)
    (argument := initFrom 3 creationSource) (initial := init_is_INIT (.app identity creationSource))
    (region := fun n => n≠1) (by intro support; exact support rfl)
    (p := [.arg]) (l := argCreatedDegree) rfl (by
      simp [argCreatedDegree,Label.supported_concat,Label.Supported,Letter.Supported,
        Label.atom,Label.over,Label.under])
  rcases cut with inBody | inArgument
  · simp [argCreatedDegree,Label.supported_concat,Label.Supported,Letter.Supported,
      Label.atom,Label.over,Label.under,SourceRegion,LTerm.labels] at inBody
  · exact inArgument
#print axioms HeadFreeWalk.excludes_isolated
#print axioms HeadFreeWalk.one_component
#print axioms SourceTraverse.root_head_isolated
#print axioms HeadFreeWalk.root_head_one_component
#print axioms History.root_head_degree_region
#print axioms compound_root_head_cut_selects_argument

def bodyCutInitial : LTerm := initLabels (.app (.lam creationSource) identity)
def bodyCutTarget : LTerm := .app (Label.atom 0) (.lam (Label.atom 1)
  (.app (Label.atom 2)
    (LTerm.contract (Label.atom 3) (Label.atom 4) (.var (Label.atom 5) 0)
      (.lam (Label.atom 6) (.var (Label.atom 7) 0)))
    (.lam (Label.atom 8) (.var (Label.atom 9) 0))))
  (.lam (Label.atom 10) (.var (Label.atom 11) 0))
def bodyCutDegree : Label := (LTerm.contract (Label.atom 3) (Label.atom 4) (.var (Label.atom 5) 0)
  (.lam (Label.atom 6) (.var (Label.atom 7) 0))).label

theorem body_cut_creation_step : StepAt [.fn,.body,.fn] bodyCutInitial bodyCutTarget :=
  .fn (.body (.fn (.root _ _ _ _)))

/-- The other root-head component is also selected from a genuine compound
created degree, with no preselected component or edge cover premise. -/
theorem compound_root_head_cut_selects_body : bodyCutDegree.Supported (SourceRegion (initFrom 2 creationSource)) := by
  have actual := History.cons body_cut_creation_step (.nil _)
  have cut := actual.root_head_degree_region (body := initFrom 2 creationSource)
    (argument := initFrom 10 identity) (initial := init_is_INIT (.app (.lam creationSource) identity))
    (region := fun n => n≠1) (by intro support; exact support rfl)
    (p := [.fn,.body]) (l := bodyCutDegree) rfl (by
      simp [bodyCutDegree,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
        Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under])
  rcases cut with inBody | inArgument
  · exact inBody
  · simp [bodyCutDegree,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
      Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under,
      SourceRegion,initFrom,identity,LTerm.labels] at inArgument
#print axioms compound_root_head_cut_selects_body

/-- The incoming edge of the automatically selected original body is absent,
although its root application node and internal outgoing edges are retained. -/
theorem compound_body_cut_avoids_incoming_root :
    ∀ e∈bodyCutDegree.edgeWord,Label.atom e.atom≠Label.atom 2 := by
  have actual := History.cons body_cut_creation_step (.nil _)
  have cut := actual.root_head_degree_strict_region (body := initFrom 2 creationSource)
    (argument := initFrom 10 identity) (initial := init_is_INIT (.app (.lam creationSource) identity))
    (region := fun n => n≠1) (by intro support; exact support rfl)
    (p := [.fn,.body]) (l := bodyCutDegree) rfl (by
      simp [bodyCutDegree,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
        Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under])
  rcases cut with ⟨_,strict⟩ | ⟨inArgument,_⟩
  · exact strict
  · simp [bodyCutDegree,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
      Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under,
      SourceRegion,initFrom,identity,LTerm.labels] at inArgument

/-- Allowing a walk endpoint on the head boundary really permits its incoming
root edge. The live endpoint hypotheses of strict avoidance are necessary. -/
theorem head_boundary_endpoint_keeps_incoming_edge :
    HeadFreeWalk (sourceEdges [Label.atom 1] (.lamBody (Label.atom 1))
      (.lam (Label.atom 2) (.var (Label.atom 3) 0))) (Label.atom 0) (Label.atom 1)
      (.lamBody (Label.atom 1)) [⟨2,false⟩] (.lamContext (Label.atom 2)) ∧
      (⟨2,false⟩ : OrientedAtom)∈[⟨2,false⟩] ∧
      (SourcePort.lamBody (Label.atom 1)).AtHead (Label.atom 0) (Label.atom 1) :=
  ⟨.edge (.forward List.mem_cons_self rfl),List.mem_cons_self,rfl⟩
#print axioms SourceTraverse.root_head_boundary
#print axioms HeadFreeWalk.root_edge_absent
#print axioms History.root_head_degree_strict_region
#print axioms compound_body_cut_avoids_incoming_root
#print axioms head_boundary_endpoint_keeps_incoming_edge

/-- The actual contextual head is below a surviving outer lambda; its
incoming port is an application argument port, and its binder environment
is nonempty. The final degree is compound and follows two actual steps. -/
theorem nested_contextual_head_edges_absent :
    ∀ e∈createdFunction.label.edgeWord,Label.atom e.atom≠Label.atom 6 ∧ Label.atom e.atom≠Label.atom 7 := by
  have history : History [[.body,.arg],[.body,.fn]] (.lam (Label.atom 20) commutingInitial)
      (.lam (Label.atom 20) commutingRight) :=
    .cons (.body (.arg (.root _ _ _ _))) (.cons (.body (.fn (.root _ _ _ _))) (.nil _))
  have initial : INIT (.lam (Label.atom 20) commutingInitial) := by
    constructor
    · intro l member
      rcases List.mem_cons.mp member with same | old
      · cases same; exact ⟨20,rfl⟩
      · exact (init_is_INIT commutingSource).1 l old
    · exact List.nodup_cons.mpr ⟨by decide,(init_is_INIT commutingSource).2⟩
  apply history.contextual_head_atoms_absent initial (site := [.body,.arg])
    (env := [Label.atom 20]) (ctx := .appArg (Label.atom 0))
    (body := .var (Label.atom 8) 0) (argument := .lam (Label.atom 9) (.var (Label.atom 10) 0))
    (SourceSubterm.body (SourceSubterm.arg .nil))
    (region := fun n => n≠7) (by intro support; exact support rfl)
    (p := [.body]) rfl
  simp [Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under]
#print axioms SourceTraverse.contextual_head_boundary
#print axioms HeadFreeWalk.excludes_boundary_atom
#print axioms History.contextual_head_atoms_absent
#print axioms nested_contextual_head_edges_absent

/-- After a real nonroot duplication and compound creation in one copy,
the strict original-argument root guard follows from support alone. No
strict guard, canonicality, or internal-history premise is supplied. -/
theorem contextual_argument_compound_guard_derived :
    ∀ e∈(LTerm.contract (Label.atom 7) (Label.atom 8) (.var (Label.atom 9) 0)
      (.lam (Label.atom 10) (.var (Label.atom 11) 0))).label.edgeWord,
      Label.atom e.atom≠contextualCreationArgument.label := by
  have history := History.cons contextual_creation_head_step (.cons contextual_creation_tail_step (.nil _))
  apply history.argument_degree_incoming_absent (init_is_INIT
    (.lam (.app (.lam (.app (.var 0) (.var 0))) creationSource)))
    (headSite := [.body]) (env := [Label.atom 0]) (ctx := .lamBody (Label.atom 0))
    (body := .app (Label.atom 3) (.var (Label.atom 4) 0) (.var (Label.atom 5) 0))
    (argument := contextualCreationArgument) (SourceSubterm.body .nil)
    (p := [.body,.fn]) rfl
  simp only [
    Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under,SourceRegion]
  decide

/-- Its actual first duplication is outside that original argument: strict
support remains a path fact and does not make an arbitrary history internal. -/
theorem contextual_argument_guard_does_not_imply_internal :
    ¬(∀ p∈([[.body],[.body,.fn,.fn]] : List Path),∃ suffix,p=[.body,.arg]++suffix) := by
  intro inside
  obtain ⟨suffix,equal⟩ := inside [.body] (List.mem_cons_self)
  have lengths := congrArg List.length equal
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  omega
#print axioms SourceSubterm.append
#print axioms SourceTraverse.region_restrict
#print axioms History.argument_degree_incoming_absent
#print axioms History.body_degree_incoming_absent
#print axioms contextual_argument_compound_guard_derived
#print axioms contextual_argument_guard_does_not_imply_internal

def argCreationFinal : LTerm := .app (Label.atom 0) (.lam (Label.atom 1) (.var (Label.atom 2) 0))
  (LTerm.contract (Label.atom 3) argCreatedDegree (.var (Label.atom 8) 0)
    (.lam (Label.atom 9) (.var (Label.atom 10) 0)))

theorem arg_creation_last_labelled : StepAt [.arg] argCreationTarget argCreationFinal := .arg (.root _ _ _ _)

/-- Both actual events have strict original-argument colours. The second
colour is compound, and neither event colour is inferred from canonicality. -/
theorem arg_creation_strict_coloured_history :
    RegionalHistory (fun n => SourceRegion (initFrom 3 creationSource) n ∧
      Label.atom n≠(initFrom 3 creationSource).label)
      [[.arg,.fn],[.arg]] argCreationInitial argCreationFinal := by
  refine .cons arg_creation_step rfl ?_ (.cons arg_creation_last_labelled rfl ?_ (.nil _))
  · change (Label.atom 5).Supported _
    simp only [Label.atom,Label.Supported,Letter.Supported,SourceRegion]
    decide
  · change argCreatedDegree.Supported _
    simp only [argCreatedDegree,Label.supported_concat,Label.atom,Label.over,Label.under,
      Label.Supported,Letter.Supported,SourceRegion]
    decide

/-- Whole internality is derived from the explicit per-event colours by
accumulating real internal prefixes, including the compound final event. -/
theorem strict_colours_derive_whole_argument_schedule : Internal [.arg] argCreationRun.history := by
  have inside := arg_creation_strict_coloured_history.internal_of_strict_region
    (init_is_INIT (.app identity creationSource)) (site := [.arg]) rfl
  intro p member
  exact inside p member
#print axioms Path.fn_parent_region
#print axioms History.next_strict_degree_internal
#print axioms RegionalHistory.internal_of_strict_region
#print axioms arg_creation_strict_coloured_history
#print axioms strict_colours_derive_whole_argument_schedule

/-- Only the two actual degree supports are supplied. Each strict root guard
is recovered separately from its true prefix before whole internality. -/
theorem regional_colours_derive_whole_argument_schedule : Internal [.arg] argCreationRun.history := by
  have coloured : RegionalHistory (SourceRegion (initFrom 3 creationSource))
      [[.arg,.fn],[.arg]] argCreationInitial argCreationFinal := by
    refine .cons arg_creation_step rfl ?_ (.cons arg_creation_last_labelled rfl ?_ (.nil _))
    · change Label.atom 5∈(initFrom 3 creationSource).labels
      decide
    · change argCreatedDegree.Supported _
      simp only [argCreatedDegree,Label.supported_concat,Label.atom,Label.over,Label.under,
        Label.Supported,Letter.Supported,SourceRegion]
      decide
  have inside := coloured.argument_internal (init_is_INIT (.app identity creationSource))
    (headSite := []) (env := []) (ctx := .external)
    (body := .var (Label.atom 2) 0) SourceSubterm.nil
  intro p member
  exact inside p member

/-- Body support alone at the real creation event gives the actual old-body
schedule; the outside argument and root guards follow from INIT geometry. -/
theorem regional_colours_derive_whole_body_schedule :
    ∀ p∈([[.fn,.body,.fn]] : List Path),∃ suffix,p=[.fn,.body]++suffix := by
  have coloured : RegionalHistory (SourceRegion (initFrom 2 creationSource)) [[.fn,.body,.fn]]
      bodyCutInitial bodyCutTarget := by
    refine .cons body_cut_creation_step rfl ?_ (.nil _)
    change Label.atom 4∈(initFrom 2 creationSource).labels
    decide
  exact coloured.body_internal (init_is_INIT (.app (.lam creationSource) identity))
    (headSite := []) (env := []) (ctx := .external) (argument := initFrom 10 identity) SourceSubterm.nil
#print axioms RegionalHistory.strictify_head_region
#print axioms RegionalHistory.argument_internal
#print axioms RegionalHistory.body_internal
#print axioms regional_colours_derive_whole_argument_schedule
#print axioms regional_colours_derive_whole_body_schedule

private theorem function_app_has_no_left_redex (old : RedexOcc (.app (.app f arg) other)) :
    ¬LeftOf old.val [.fn] := by
  rcases old with ⟨p,redex⟩
  cases p with
  | nil =>
    intro before
    obtain ⟨node,lookup,isRedex⟩ := redex
    simp only [subtermAt,Option.some.injEq] at lookup
    cases lookup
    exact isRedex
  | cons edge p =>
    intro before
    cases edge with
    | fn => cases before with | child _ prior => cases prior
    | arg => cases before
    | body => cases before

def protectedCutInitial : LTerm := initLabels
  (.app (.app (.lam identity) identity) (.app identity identity))
def protectedCutMiddle : LTerm := .app (Label.atom 0)
  (LTerm.contract (Label.atom 1) (Label.atom 2) (.lam (Label.atom 3) (.var (Label.atom 4) 0))
    (.lam (Label.atom 5) (.var (Label.atom 6) 0))) (initFrom 7 (.app identity identity))
def protectedCutFinal : LTerm := .app (Label.atom 0)
  (LTerm.contract (Label.atom 1) (Label.atom 2) (.lam (Label.atom 3) (.var (Label.atom 4) 0))
    (.lam (Label.atom 5) (.var (Label.atom 6) 0)))
  (LTerm.contract (Label.atom 7) (Label.atom 8) (.var (Label.atom 9) 0)
    (.lam (Label.atom 10) (.var (Label.atom 11) 0)))
theorem protected_cut_head : StepAt [.fn] protectedCutInitial protectedCutMiddle := .fn (.root _ _ _ _)
theorem protected_cut_tail : StepAt [.arg] protectedCutMiddle protectedCutFinal := .arg (.root _ _ _ _)

theorem protected_cut_standard : Standard (.cons (singleContraction protected_cut_head.betaAt)
    (.single (singleContraction protected_cut_tail.betaAt))) := by
  refine .cons _ ⟨[.fn],protected_cut_head.betaAt.redex⟩ (leftmost_singleton _) ?_ (Standard.single_step _
    ⟨[.arg],protected_cut_tail.betaAt.redex⟩ (leftmost_singleton _))
  intro old before
  exact False.elim (function_app_has_no_left_redex old before)

/-- The actual right-sibling event remains outside the protected cut, while
the head-created ancestor root redex is tainted and cannot be an avoiding event. -/
theorem real_protected_head_tail_geometry :
    ∀ q∈([[.arg]] : List Path),(∃ suffix,q=[.fn]++suffix) ∨
      (LeftOf [.fn] q ∧ DisjointPositions [.fn] q) := by
  have regional : RegionalHistory (fun n => n≠2) [[.arg]] protectedCutMiddle protectedCutFinal :=
    .cons protected_cut_tail rfl (by change 8≠2; decide) (.nil _)
  exact regional.head_tail_geometry protected_cut_head
    (init_is_INIT (.app (.app (.lam identity) identity) (.app identity identity))) rfl
    (.single (singleContraction protected_cut_tail.betaAt)) (.single _) protected_cut_standard rfl

theorem new_ancestor_degree_is_head_tainted :
    ¬(LTerm.contract (Label.atom 1) (Label.atom 2) (.lam (Label.atom 3) (.var (Label.atom 4) 0))
      (.lam (Label.atom 5) (.var (Label.atom 6) 0))).label.Supported (fun n => n≠2) := by
  have cut := protected_cut_head.protected_head_cut (a := 2) rfl
  have result := cut.left_degree (q := []) (LeftOf.outer .fn []) (l :=
    (LTerm.contract (Label.atom 1) (Label.atom 2) (.lam (Label.atom 3) (.var (Label.atom 4) 0))
      (.lam (Label.atom 5) (.var (Label.atom 6) 0))).label) rfl
  rcases result with old | tainted
  · simp [protectedCutInitial,initLabels,initFrom,identity,nodeCount,LTerm.degreeAt,LTerm.subterm,LTerm.degree] at old
  · exact tainted

def commutingArgFirst : LTerm := .app (Label.atom 0) (initFrom 1 (.app identity identity)) independentArgument
theorem commuting_arg_first_step : StepAt [.arg] commutingInitial commutingArgFirst := .arg (.root _ _ _ _)
theorem commuting_fn_second_step : StepAt [.fn] commutingArgFirst commutingRight := .fn (.root _ _ _ _)

/-- A genuine left event whose degree avoids the first atom really occurs
without Standardness. The core theorem detects why this schedule is not Standard. -/
theorem avoid_head_atom_does_not_replace_standard :
    ¬Standard (.cons (singleContraction commuting_arg_first_step.betaAt)
      (.single (singleContraction commuting_fn_second_step.betaAt))) := by
  intro standard
  have cut := commuting_arg_first_step.protected_head_cut (a := 7) rfl
  have notLeft := cut.event_not_left (init_is_INIT commutingSource)
    (.cons commuting_arg_first_step (.nil _)) commuting_fn_second_step (.nil _)
    (l := Label.atom 2) rfl (by change 2≠7; decide)
    commuting_arg_first_step.betaAt (.single (singleContraction commuting_fn_second_step.betaAt))
    (.single _) standard rfl
  exact notLeft (LeftOf.branch [] [])
#print axioms ProtectedHeadCut.left_degree
#print axioms ProtectedHeadCut.event_not_left
#print axioms RegionalHistory.head_tail_geometry
#print axioms real_protected_head_tail_geometry
#print axioms new_ancestor_degree_is_head_tainted
#print axioms avoid_head_atom_does_not_replace_standard

/-- The actual right-sibling tail is excluded by normality, using the new
protected geometry and the genuine right-sibling extraction. -/
theorem right_sibling_silent_head_is_not_normal :
    ¬ExtractionNormal (.of (.cons (singleContraction protected_cut_head.betaAt)
      (.single (singleContraction protected_cut_tail.betaAt)))
      (.cons protected_cut_head.betaAt (.single protected_cut_tail.betaAt))) := by
  intro normal
  have regional : RegionalHistory (fun n => n≠2) [[.arg]] protectedCutMiddle protectedCutFinal :=
    .cons protected_cut_tail rfl (by change 8≠2; decide) (.nil _)
  have inside := regional.normal_head_internal protected_cut_head
    (init_is_INIT (.app (.app (.lam identity) identity) (.app identity identity))) rfl
    (.single (singleContraction protected_cut_tail.betaAt)) (.single _) protected_cut_standard rfl (by decide) normal
  obtain ⟨suffix,equal⟩ := inside [.arg] (by change ([.arg] : Path)∈[[.fn],[.arg]]; decide)
  have wrong := (List.cons.inj equal).1
  cases wrong

/-- Replacing recursive atom avoidance by inequality of whole degrees is
false even for a genuinely canonical compound-created two-event run. -/
theorem canonical_compound_tail_refutes_degree_inequality_guard :
    CanonicalRun argCreationRun ∧ argCreatedDegree≠Label.atom 5 ∧
      ¬argCreatedDegree.Supported (fun n => n≠5) := by
  refine ⟨arg_creation_canonical,?_,?_⟩
  · intro equal
    have lengths := congrArg Label.length equal
    change 5=1 at lengths
    omega
  · simp [argCreatedDegree,Label.supported_concat,Label.Supported,Letter.Supported,
      Label.atom,Label.over,Label.under]
#print axioms normal_head_internal_of_right_geometry
#print axioms RegionalHistory.normal_head_internal
#print axioms right_sibling_silent_head_is_not_normal
#print axioms canonical_compound_tail_refutes_degree_inequality_guard

def contextualBodyReflectionSource : LTerm := .lam (Label.atom 50)
  (.app (Label.atom 40) (.lam (Label.atom 41) reflectionBody) reflectionValue)
def contextualBodyReflectionMiddle : LTerm := .lam (Label.atom 50)
  (LTerm.contract (Label.atom 40) (Label.atom 41) reflectionBody reflectionValue)
def contextualBodyReflectionFinal : LTerm := .lam (Label.atom 50)
  (LTerm.contract (Label.atom 40) (Label.atom 41) contractReflectionBodyTarget reflectionValue)

theorem contextual_body_reflection_initial : INIT contextualBodyReflectionSource := by
  constructor
  · intro l member
    simp only [contextualBodyReflectionSource,reflectionBody,reflectionValue,LTerm.labels,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_,rfl⟩
  · decide

theorem contextual_body_reflection_head : StepAt [.body] contextualBodyReflectionSource contextualBodyReflectionMiddle :=
  .body (.root _ _ _ _)
theorem contextual_body_reflection_tail : StepAt [.body,.body] contextualBodyReflectionMiddle contextualBodyReflectionFinal :=
  .body regional_contract_actual_step

/-- The global head is under an actual outer binder, and the body event is
under another surviving lambda. The argument's free index is shifted in the
real put substitution; rule (iii) is constructed without a supplied row. -/
theorem contextual_capture_body_silent_head_not_normal :
    ¬ExtractionNormal (.of (.cons (singleContraction contextual_body_reflection_head.betaAt)
      (.single (singleContraction contextual_body_reflection_tail.betaAt)))
      (.cons contextual_body_reflection_head.betaAt (.single contextual_body_reflection_tail.betaAt))) := by
  have regional : RegionalHistory (SourceRegion reflectionBody) [[.body,.body]]
      contextualBodyReflectionMiddle contextualBodyReflectionFinal := by
    refine .cons contextual_body_reflection_tail rfl ?_ (.nil _)
    change Label.atom 3∈reflectionBody.labels
    decide
  apply regional.contextual_body_not_normal contextual_body_reflection_head contextual_body_reflection_initial
    (body := reflectionBody) (argument := reflectionValue) (beta := Label.atom 40) (alpha := Label.atom 41) rfl
    (by intro q member; exact ⟨[.body],List.mem_singleton.mp member⟩)
    (.single (singleContraction contextual_body_reflection_tail.betaAt)) (.single _) rfl
  decide
#print axioms RegionalHistory.subterm_internal
#print axioms contextual_body_function_projection
#print axioms contextual_body_program_not_normal
#print axioms RegionalHistory.contextual_body_not_normal
#print axioms contextual_capture_body_silent_head_not_normal
/-- Consume the general length induction, rather than the previous rank-two
special theorem: no per-event colours are supplied by this fixture. -/
theorem general_canonical_compound_support (region : Nat → Prop)
    (supported : argCreatedDegree.Supported region) :
    RegionalHistory region [[.arg,.fn],[.arg]] argCreationInitial argCreationFinal := by
  exact (History.cons arg_creation_step (.nil _)).canonical_degree_support arg_creation_last_labelled
    (init_is_INIT _) argCreationRun arg_creation_canonical rfl rfl supported
#print axioms History.canonical_degree_support
#print axioms general_canonical_compound_support
/-- General Exercise 6.2.15 consumes only the final compound degree's
argument support and actual canonicality, without a supplied colour history. -/
theorem general_canonical_argument_internal : Internal [.arg] argCreationRun.history := by
  apply (History.cons arg_creation_step (.nil _)).canonical_argument_internal arg_creation_last_labelled
    (init_is_INIT _) argCreationRun arg_creation_canonical rfl (l := argCreatedDegree) rfl
    (argument := initFrom 3 creationSource) ?_ SourceSubterm.nil
  simp [argCreatedDegree,Label.atom,Label.over,Label.under,Label.Supported,Letter.Supported,Label.concat,
    SourceRegion,initFrom,identity,creationSource,LTerm.labels,nodeCount]

theorem general_canonical_first_is_lo :
    LeftmostSelected (degreeCandidates argCreationInitial argCreatedDegree)
      (⟨[.arg,.fn],arg_creation_step.betaAt.redex⟩ : RedexOcc argCreationInitial.erase) :=
  History.canonical_first_leftmost arg_creation_step (.nil _) arg_creation_last_labelled
    (init_is_INIT _) argCreationRun arg_creation_canonical rfl rfl

theorem general_canonical_compound_head_not_silent :
    ¬argCreatedDegree.Supported (fun n => n≠5) :=
  History.canonical_head_not_silent arg_creation_step (.nil _) arg_creation_last_labelled
    (init_is_INIT _) argCreationRun arg_creation_canonical rfl rfl rfl
#print axioms History.canonical_argument_internal
#print axioms History.canonical_first_leftmost
#print axioms History.canonical_head_not_silent
#print axioms general_canonical_argument_internal
#print axioms general_canonical_first_is_lo
#print axioms general_canonical_compound_head_not_silent
/-- The local INIT substitution is really noninjective after actual copying.
Both 2 and 7 are valid local source edge identities, with common image 6. -/
theorem actual_beta_basis_substitution_not_injective :
    ¬Function.Injective (initialRelabelling duplicateTarget 0) := by
  intro injective
  have wrong : (2 : Nat)=7 := injective (show initialRelabelling duplicateTarget 0 2=
    initialRelabelling duplicateTarget 0 7 from rfl)
  exact (by decide : (2 : Nat)≠7) wrong

def duplicateLeftCopy : LTerm :=
  ((initFrom 5 (.app identity identity)).prepend (Label.atom 1).under).prepend (Label.atom 3)

/-- An incoming copy-root stamp retains its unique old body variable, so it
is a genuine outside anchor despite the noninjective interior map. -/
theorem actual_beta_copy_root_anchor_unique (lookup : duplicateTarget.subterm p=some node)
    (same : node.label=duplicateLeftCopy.label) : p=[.fn] := by
  apply LTerm.contract_outside_label_injective (body := .app (Label.atom 2)
    (.var (Label.atom 3) 0) (.var (Label.atom 4) 0)) (argument := initFrom 5 (.app identity identity))
    duplication_init lookup (q := [.fn]) (other := duplicateLeftCopy) rfl same
  intro supported
  have supportedRoot : duplicateLeftCopy.label.Supported (SourceRegion (initFrom 5 (.app identity identity))) := same ▸ supported
  have member := Label.Supported.firstAtom supportedRoot (n := 3) rfl
  change Label.atom 3∈(initFrom 5 (.app identity identity)).labels at member
  simp [initFrom,identity,nodeCount,LTerm.labels,Label.atom] at member

theorem actual_beta_collision_has_distinct_copies :
    ∃ p q,ArgumentOccurrence (.app (.var 0) (.var 0)) p ∧
      ArgumentOccurrence (.app (.var 0) (.var 0)) q ∧ p≠q ∧
      (∃ r,[.fn,.fn]=p++r ∧ r≠[]) ∧ (∃ r,[.arg,.fn]=q++r ∧ r≠[]) := by
  obtain ⟨p,q,left,right,r,s,hp,hq,different,_,_,leftPath,rightPath,leftStrict,rightStrict⟩ :=
    LTerm.contract_collision_distinct_copies (body := .app (Label.atom 2)
      (.var (Label.atom 3) 0) (.var (Label.atom 4) 0)) (argument := initFrom 5 (.app identity identity))
      duplication_init (p := [.fn,.fn]) (q := [.arg,.fn])
      (node := .lam (Label.atom 6) (.var (Label.atom 7) 0))
      (other := .lam (Label.atom 6) (.var (Label.atom 7) 0)) rfl rfl rfl (by decide)
  exact ⟨p,q,hp,hq,different,⟨r,leftPath,leftStrict⟩,⟨s,rightPath,rightStrict⟩⟩
#print axioms LTerm.contract_nonroot_first_origin
#print axioms LTerm.contract_outside_label_injective
#print axioms LTerm.contract_collision_distinct_copies
#print axioms root_beta_outside_edge_injective
#print axioms actual_beta_basis_substitution_not_injective
#print axioms actual_beta_copy_root_anchor_unique
#print axioms actual_beta_collision_has_distinct_copies
def stampCaptureBody : LTerm := .lam (Label.atom 2) (.app (Label.atom 3)
  (.var (Label.atom 4) 1) (.var (Label.atom 5) 1))
def stampCaptureArgument : LTerm := .lam (Label.atom 6) (.var (Label.atom 7) 1)
def stampCaptureTarget : LTerm := LTerm.contract (Label.atom 0) (Label.atom 1) stampCaptureBody stampCaptureArgument

theorem stamp_capture_initial : INIT (.app (Label.atom 0) (.lam (Label.atom 1) stampCaptureBody) stampCaptureArgument) :=
  init_is_INIT (.app (.lam (.lam (.app (.var 1) (.var 1)))) (.lam (.var 1)))
theorem stamp_capture_actual : StepAt [] (.app (Label.atom 0) (.lam (Label.atom 1) stampCaptureBody)
    stampCaptureArgument) stampCaptureTarget := .root _ _ _ _

/-- The put value really crosses a surviving binder: its free index 1 becomes
2, while its original node-label 7 is retained in two distinct interiors. -/
theorem actual_capture_collision_support :
    stampCaptureTarget.subterm [.body,.fn,.body]=some (.var (Label.atom 7) 2) ∧
    stampCaptureTarget.subterm [.body,.arg,.body]=some (.var (Label.atom 7) 2) ∧
    (Label.atom 7).Supported (SourceRegion stampCaptureArgument) := by
  refine ⟨rfl,rfl,?_⟩
  exact LTerm.contract_label_collision_argument stamp_capture_initial
    (p := [.body,.fn,.body]) (q := [.body,.arg,.body])
    (node := .var (Label.atom 7) 2) (other := .var (Label.atom 7) 2) rfl rfl rfl (by decide)

theorem capture_collision_is_not_unshifted :
    stampCaptureTarget.subterm [.body,.fn,.body]≠some (.var (Label.atom 7) 1) := by decide
#print axioms actual_capture_collision_support
#print axioms capture_collision_is_not_unshifted
private theorem lambda_function_app_has_no_left (old : RedexOcc (.lam (.app (.app f arg) other))) :
    ¬LeftOf old.val [.body,.fn] := by
  rcases old with ⟨p,redex⟩
  cases p with
  | nil =>
    intro before
    obtain ⟨node,lookup,isRedex⟩ := redex
    simp only [subtermAt,Option.some.injEq] at lookup
    cases lookup
    exact isRedex
  | cons edge p =>
    intro before
    cases edge with
    | fn => cases before
    | arg => cases before
    | body =>
      cases before with
      | child _ prior => exact function_app_has_no_left_redex ⟨p,redex⟩ prior

def protectedOuterSource : LTerm := .lam (Label.atom 50) creationInitial
def protectedOuterMiddle : LTerm := .lam (Label.atom 50) creationTarget
def protectedOuterDegree : Label := (Label.atom 1).concat ((Label.atom 2).over.concat
  ((Label.atom 3).concat ((Label.atom 2).under.concat (Label.atom 4))))
def protectedOuterFinal : LTerm := .lam (Label.atom 50)
  (LTerm.contract (Label.atom 0) protectedOuterDegree (.var (Label.atom 5) 0)
    (.lam (Label.atom 6) (.var (Label.atom 7) 0)))

theorem protected_outer_initial : INIT protectedOuterSource := by
  constructor
  · intro l member
    rcases List.mem_cons.mp member with same | inner
    · exact ⟨50,same⟩
    · exact (init_is_INIT creationSource).1 l inner
  · decide

theorem protected_outer_head : StepAt [.body,.fn] protectedOuterSource protectedOuterMiddle := .body actual_creation
theorem protected_outer_last : StepAt [.body] protectedOuterMiddle protectedOuterFinal := .body (.root _ _ _ _)
theorem protected_outer_standard : Standard (.cons (singleContraction protected_outer_head.betaAt)
    (.single (singleContraction protected_outer_last.betaAt))) := by
  refine .cons _ ⟨[.body,.fn],protected_outer_head.betaAt.redex⟩ (leftmost_singleton _) ?_
    (Standard.single_step _ ⟨[.body],protected_outer_last.betaAt.redex⟩ (leftmost_singleton _))
  intro old before
  exact False.elim (lambda_function_app_has_no_left old before)

/-- The original outer binder 50 remains protected while the actual final
redex degree is a new compound word containing the fired head atom 2. -/
theorem compound_degree_avoids_actual_ancestor : protectedOuterDegree.Supported (fun n => n≠50) := by
  exact (History.cons protected_outer_head (.nil _)).standard_ancestor_degree_avoid protected_outer_last
    protected_outer_initial (n := 50) (site := []) (body := creationInitial) (by simp [protectedOuterSource,LTerm.subterm])
    protected_outer_head.betaAt (.single (singleContraction protected_outer_last.betaAt)) (.single _)
    protected_outer_standard rfl rfl rfl

theorem actual_standard_ancestor_survives :
    RegionalHistory (fun n => n≠50) [[.body,.fn],[.body]] protectedOuterSource protectedOuterFinal ∧
      ∃ body,protectedOuterFinal.subterm []=some (.lam (Label.atom 50) body) := by
  have result := (History.cons protected_outer_head (.cons protected_outer_last (.nil _))).standard_ancestor_binder_protection
    protected_outer_initial (n := 50) (site := []) (body := creationInitial) (by simp [protectedOuterSource,LTerm.subterm])
    protected_outer_head.betaAt (.single (singleContraction protected_outer_last.betaAt)) (.single _)
    protected_outer_standard rfl rfl
  exact ⟨result.1,result.2.current_lookup⟩

/-- The contracted head lambda is not a surviving strict ancestor; its atom
really occurs inside the new compound degree and cannot be excluded. -/
theorem contracted_head_is_not_protected_ancestor : ¬protectedOuterDegree.Supported (fun n => n≠2) := by
  simp [protectedOuterDegree,Label.supported_concat,Label.Supported,Letter.Supported,Label.atom,Label.over,Label.under]
#print axioms History.standard_ancestor_binder_protection
#print axioms History.standard_ancestor_degree_avoid
#print axioms compound_degree_avoids_actual_ancestor
#print axioms actual_standard_ancestor_survives
#print axioms contracted_head_is_not_protected_ancestor
def ancestorFiredInitial : LTerm := initLabels (.app (.lam creationSource) identity)
def ancestorFiredBody : LTerm := .app (Label.atom 2)
  (LTerm.contract (Label.atom 3) (Label.atom 4) (.var (Label.atom 5) 0)
    (.lam (Label.atom 6) (.var (Label.atom 7) 0))) (.lam (Label.atom 8) (.var (Label.atom 9) 0))
def ancestorFiredMiddle : LTerm := .app (Label.atom 0) (.lam (Label.atom 1) ancestorFiredBody)
  (.lam (Label.atom 10) (.var (Label.atom 11) 0))
def ancestorFiredFinal : LTerm := LTerm.contract (Label.atom 0) (Label.atom 1) ancestorFiredBody
  (.lam (Label.atom 10) (.var (Label.atom 11) 0))
theorem ancestor_fired_first : StepAt [.fn,.body,.fn] ancestorFiredInitial ancestorFiredMiddle :=
  .fn (.body (.fn (.root _ _ _ _)))
theorem ancestor_fired_last : StepAt [] ancestorFiredMiddle ancestorFiredFinal := .root _ _ _ _

/-- The same real closed source admits an inside-first schedule which later
fires the original enclosing binder. The missing Standard condition is real. -/
theorem firing_original_ancestor_is_not_standard :
    ¬Standard (.cons (singleContraction ancestor_fired_first.betaAt)
      (.single (singleContraction ancestor_fired_last.betaAt))) := by
  intro standard
  have avoid := (History.cons ancestor_fired_first (.nil _)).standard_ancestor_degree_avoid ancestor_fired_last
    (init_is_INIT _) (site := [.fn]) (n := 1) (body := initFrom 2 creationSource) rfl
    ancestor_fired_first.betaAt (.single (singleContraction ancestor_fired_last.betaAt)) (.single _) standard
    rfl rfl (l := Label.atom 1) rfl
  exact avoid rfl
#print axioms firing_original_ancestor_is_not_standard
def markerSource : LTerm := initLabels (.app creationSource identity)
def markerImage : Label := (LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
  (.lam (Label.atom 5) (.var (Label.atom 6) 0))).label
def markerMiddle : LTerm := .app (Label.atom 0)
  (.app (Label.atom 1)
    (LTerm.contract (Label.atom 2) (Label.atom 3) (.var (Label.atom 4) 0)
      (.lam (Label.atom 5) (.var (Label.atom 6) 0))) (.lam (Label.atom 7) (.var (Label.atom 8) 0)))
  (.lam (Label.atom 9) (.var (Label.atom 10) 0))
def markerAfter : LTerm := .app (Label.atom 0)
  (LTerm.contract (Label.atom 1) markerImage (.var (Label.atom 6) 0)
    (.lam (Label.atom 7) (.var (Label.atom 8) 0))) (.lam (Label.atom 9) (.var (Label.atom 10) 0))
def markerBasisAfter : LTerm := .app (Label.atom 0)
  (LTerm.contract (Label.atom 1) (Label.atom 2) (.var (Label.atom 3) 0)
    (.lam (Label.atom 4) (.var (Label.atom 5) 0))) (.lam (Label.atom 6) (.var (Label.atom 7) 0))
def markerGlobalDegree : Label := (LTerm.contract (Label.atom 1) markerImage (.var (Label.atom 6) 0)
  (.lam (Label.atom 7) (.var (Label.atom 8) 0))).label
def markerLocalDegree : Label := (LTerm.contract (Label.atom 1) (Label.atom 2) (.var (Label.atom 3) 0)
  (.lam (Label.atom 4) (.var (Label.atom 5) 0))).label

theorem marker_first : StepAt [.fn,.fn] markerSource markerMiddle := .fn (.fn (.root _ _ _ _))
theorem marker_second : StepAt [.fn] markerMiddle markerAfter := .fn (.root _ _ _ _)
theorem marker_basis_second : StepAt [.fn] (initLabels markerMiddle.erase) markerBasisAfter := .fn (.root _ _ _ _)

/-- A real nested compound: the first beta's literal over/under(3) bars are
inside one atomic image, while the next actual contraction adds bars whose
payload is that whole compound image. The parser keeps their levels distinct. -/
theorem actual_nested_marker_block_alignment :
    headGroups 3 markerGlobalDegree.letters=markerLocalDegree.expansionTokens (initialRelabelling markerMiddle 0) := by
  exact marker_first.local_degree_outer_alignment (q := []) (init_is_INIT _) rfl
    (.cons marker_second (.nil _)) (.cons marker_basis_second (.nil _)) rfl rfl

theorem actual_head_image_is_one_block : headGroups 3 markerImage.letters=[.inl markerImage.letters] := by
  have flat := marker_first.headFlat (init_is_INIT _) rfl
  have member : markerImage∈markerMiddle.labels := LTerm.label_mem_of_subterm
    (show markerMiddle.subterm [.fn,.fn]=some (.lam markerImage (.var (Label.atom 6) 0)) from rfl)
  exact ((LTerm.headFlat_iff _ _).mp flat markerImage member).headGroups

theorem literal_head_bar_is_not_runtime_bar :
    (Letter.over (Label.atom 3)).headSeparator 3=false ∧
    (Letter.over markerImage).headSeparator 3=true := by decide

/-- The HeadFlat property is exactly for the common one-step basis; it is
false for the real second-step label containing a compound bar payload. -/
theorem subsequent_compound_is_not_headFlat : ¬markerGlobalDegree.HeadFlat 3 := by
  simp [markerGlobalDegree,markerImage,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
    Label.HeadFlat,Letter.HeadFlat,Label.concat,Label.atom,Label.over,Label.under]
#print axioms StepAt.headFlat
#print axioms Label.Alternating.relabel_headGroups
#print axioms StepAt.same_degree_outer_alignment
#print axioms actual_nested_marker_block_alignment
#print axioms actual_head_image_is_one_block
#print axioms literal_head_bar_is_not_runtime_bar
#print axioms subsequent_compound_is_not_headFlat
def creationDuplicateRightAfter : LTerm := .app creationDuplicateTarget.label
  ((creationDuplicateArgument.prepend (Label.atom 1).under).prepend (Label.atom 3))
  (.app (((creationDuplicateArgument.prepend (Label.atom 1).under).prepend (Label.atom 4)).label)
    (LTerm.contract (Label.atom 6) (Label.atom 7) (.var (Label.atom 8) 0)
      (.lam (Label.atom 9) (.var (Label.atom 10) 0))) (.lam (Label.atom 11) (.var (Label.atom 12) 0)))
def creationDuplicateBasisRightAfter : LTerm := .app (Label.atom 0) (initFrom 1 creationSource)
  (.app (Label.atom 9)
    (LTerm.contract (Label.atom 10) (Label.atom 11) (.var (Label.atom 12) 0)
      (.lam (Label.atom 13) (.var (Label.atom 14) 0))) (.lam (Label.atom 15) (.var (Label.atom 16) 0)))
def copiedRightLocalDegree : Label := (LTerm.contract (Label.atom 10) (Label.atom 11) (.var (Label.atom 12) 0)
  (.lam (Label.atom 13) (.var (Label.atom 14) 0))).label

theorem creation_right_copy_step : StepAt [.arg,.fn] creationDuplicateTarget creationDuplicateRightAfter := .arg (.fn (.root _ _ _ _))
theorem creation_right_basis_step : StepAt [.arg,.fn] (initLabels creationDuplicateTarget.erase) creationDuplicateBasisRightAfter :=
  .arg (.fn (.root _ _ _ _))

/-- Two actual different copy tails have different local compound degrees.
Their full image codes, including under-payload orientation, still agree.
This is the remaining genuine copy ambiguity, not a claimed inverse theorem. -/
theorem two_real_compound_copies_full_code_align (direction : Bool) :
    copiedCreatedLocalDegree.imageCode (initialRelabelling creationDuplicateTarget 0) direction=
      copiedRightLocalDegree.imageCode (initialRelabelling creationDuplicateTarget 0) direction := by
  exact creation_duplication_step.same_degree_imageCode (init_is_INIT _) rfl
    (.cons creation_copy_step (.nil _)) (.cons creation_basis_copy_step (.nil _))
    (.cons creation_right_copy_step (.nil _)) (.cons creation_right_basis_step (.nil _))
    (q := [.fn]) (r := [.arg])
    (l := (LTerm.contract (Label.atom 6) (Label.atom 7) (.var (Label.atom 8) 0)
      (.lam (Label.atom 9) (.var (Label.atom 10) 0))).label) rfl rfl rfl rfl direction

theorem equal_image_codes_do_not_identify_local_compounds : copiedCreatedLocalDegree≠copiedRightLocalDegree := by decide

theorem compound_code_retains_reverse_edge :
    (Sum.inl (Label.atom 7,true) : ExpandedCodeToken)∈
      copiedCreatedLocalDegree.imageCode (initialRelabelling creationDuplicateTarget 0) false := by
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  exact List.mem_cons_self

theorem compound_code_direction_is_not_ignored :
    copiedCreatedLocalDegree.imageCode (initialRelabelling creationDuplicateTarget 0) true≠
      copiedCreatedLocalDegree.imageCode (initialRelabelling creationDuplicateTarget 0) false := by decide
#print axioms Label.Alternating.relabel_imageCode
#print axioms StepAt.same_degree_imageCode
#print axioms two_real_compound_copies_full_code_align
#print axioms equal_image_codes_do_not_identify_local_compounds
#print axioms compound_code_retains_reverse_edge
#print axioms compound_code_direction_is_not_ignored
/-- A genuine nonroot beta under the original outer binder creates two
copies. Equal lambda-8 images locate different actual argument occurrences
with their full global prefix, rather than collapsing local node identities. -/
theorem contextual_equal_images_select_distinct_global_copies :
    ∃ p q,ArgumentOccurrence (.app (.var 0) (.var 0)) p ∧
      ArgumentOccurrence (.app (.var 0) (.var 0)) q ∧ p≠q ∧
      (∃ r,[.body,.fn,.fn,.fn]=([.body]++p)++r ∧ r≠[]) ∧
      (∃ r,[.body,.arg,.fn,.fn]=([.body]++q)++r ∧ r≠[]) := by
  obtain ⟨_,p,q,left,right,r,s,hp,hq,different,_,_,leftPath,rightPath,leftStrict,rightStrict⟩ :=
    contextual_creation_head_step.label_collision_distinct_copies (init_is_INIT _)
      (body := .app (Label.atom 3) (.var (Label.atom 4) 0) (.var (Label.atom 5) 0))
      (argument := contextualCreationArgument) (beta := Label.atom 1) (alpha := Label.atom 2) rfl
      (p := [.body,.fn,.fn,.fn]) (q := [.body,.arg,.fn,.fn])
      (node := .lam (Label.atom 8) (.var (Label.atom 9) 0))
      (other := .lam (Label.atom 8) (.var (Label.atom 9) 0)) rfl rfl rfl (by decide)
  exact ⟨p,q,hp,hq,different,⟨r,leftPath,leftStrict⟩,⟨s,rightPath,rightStrict⟩⟩

/-- The unchanged ancestor lambda is outside the head region. Its actual
label locks its global empty occurrence, independently of the duplicated part. -/
theorem contextual_old_outer_anchor_unique (lookup : contextualCreationTarget.subterm p=some node)
    (same : node.label=Label.atom 0) : p=[] := by
  apply contextual_creation_head_step.outside_argument_label_injective (init_is_INIT _)
    (body := .app (Label.atom 3) (.var (Label.atom 4) 0) (.var (Label.atom 5) 0))
    (argument := contextualCreationArgument) (beta := Label.atom 1) (alpha := Label.atom 2) rfl
    lookup (q := []) (other := .lam (Label.atom 0) contextualCreationContract) rfl same
  intro support
  have impossible : (Label.atom 0).Supported (SourceRegion contextualCreationArgument) := same ▸ support
  change Label.atom 0∈contextualCreationArgument.labels at impossible
  simp [contextualCreationArgument,initFrom,creationSource,identity,nodeCount,LTerm.labels,Label.atom] at impossible

theorem contextual_beta_basis_map_is_not_injective :
    ¬Function.Injective (initialRelabelling contextualCreationTarget 0) := by
  intro injective
  have wrong : (4 : Nat)=12 := injective (show initialRelabelling contextualCreationTarget 0 4=
    initialRelabelling contextualCreationTarget 0 12 from rfl)
  exact (by decide : (4 : Nat)≠12) wrong
#print axioms StepAt.outside_argument_label_injective
#print axioms StepAt.label_collision_distinct_copies
#print axioms StepAt.outside_argument_edge_injective
#print axioms contextual_equal_images_select_distinct_global_copies
#print axioms contextual_old_outer_anchor_unique
#print axioms contextual_beta_basis_map_is_not_injective
def stampCaptureBodyAfter : LTerm := .app (Label.atom 3)
  (.lam ((Label.atom 4).concat ((Label.atom 1).under.concat (Label.atom 6))) (.var (Label.atom 7) 2))
  (.lam ((Label.atom 5).concat ((Label.atom 1).under.concat (Label.atom 6))) (.var (Label.atom 7) 2))

/-- The actual lambda above both inserted copies is old body-lambda 2,
not either argument-lambda 6 or its free variable 7. Its full incoming label
is compound, so origin recovery must really use lastAtom. -/
theorem actual_capture_copy_outer_binder_origin :
    ∃ n,stampCaptureTarget.label.lastAtom=some n ∧ Label.atom n∈stampCaptureBody.labels ∧
      Label.atom n∉stampCaptureArgument.labels := by
  exact LTerm.contract_copy_ancestor_origin_outside stamp_capture_initial
    (site := [.body,.fn]) (before := []) (suffix := [.fn]) rfl rfl
    (nodeLabel := stampCaptureTarget.label) (current := stampCaptureBodyAfter) rfl

theorem copy_outer_binder_full_label_is_not_old_atom :
    stampCaptureTarget.label≠Label.atom 2 ∧ stampCaptureTarget.label.lastAtom=some 2 := by decide

/-- The genuine put variable shifts past the retained body binder, rather
than referring to its index 1. This keeps the capture countercheck explicit. -/
theorem copy_free_variable_is_not_captured_by_retained_body_binder :
    stampCaptureTarget.subterm [.body,.fn,.body]≠some (.var (Label.atom 7) 1) :=
  capture_collision_is_not_unshifted
#print axioms LTerm.contract_copy_ancestor_origin
#print axioms LTerm.contract_copy_ancestor_origin_outside
#print axioms actual_capture_copy_outer_binder_origin
#print axioms copy_outer_binder_full_label_is_not_old_atom
#print axioms copy_free_variable_is_not_captured_by_retained_body_binder

def scopedCaptureSource : LTerm := .lam (Label.atom 50)
  (.app (Label.atom 0) (.lam (Label.atom 1) stampCaptureBody) stampCaptureArgument)
def scopedCaptureTarget : LTerm := .lam (Label.atom 50) stampCaptureTarget

theorem scoped_capture_initial : INIT scopedCaptureSource := by
  constructor
  · intro l member
    rcases List.mem_cons.mp member with equal | old
    · cases equal; exact ⟨50,rfl⟩
    · exact stamp_capture_initial.1 l old
  · exact List.nodup_cons.mpr ⟨by decide,stamp_capture_initial.2⟩
theorem scoped_capture_step : StepAt [.body] scopedCaptureSource scopedCaptureTarget :=
  .body stamp_capture_actual

/-- The two genuinely shifted copied variables share the old outer binder,
not the retained body lambda at local basis node 1. -/
theorem actual_copy_shared_outer_binding_edges :
    (⟨Label.atom 4,.lamBody (Label.atom 3),.lamBind (Label.atom 0)⟩ : SourceEdge)∈
      sourceEdges [] .external (initLabels scopedCaptureTarget.erase) ∧
    (⟨Label.atom 6,.lamBody (Label.atom 5),.lamBind (Label.atom 0)⟩ : SourceEdge)∈
      sourceEdges [] .external (initLabels scopedCaptureTarget.erase) := by decide

/-- Consume the actual replacement/scope theorem with an original label 50
and global local-basis label 0. No equality of those coordinate systems is used. -/
theorem actual_copy_external_binder_is_old_outer_lambda :
    ∃ n tail oldBody,([.body] : Path)=[]++(.body::tail) ∧
      initialRelabelling scopedCaptureTarget 0 0=Label.atom n ∧
      scopedCaptureSource.subterm []=some (.lam (Label.atom n) oldBody) := by
  apply scoped_capture_step.argument_copy_external_binder scoped_capture_initial
    (body := stampCaptureBody) (argument := stampCaptureArgument) (beta := Label.atom 0) (alpha := Label.atom 1) rfl
    (copySite := [.body,.fn]) (binderSite := []) (suffix := [.body,.fn]) rfl rfl
    (j := 0) (current := initFrom 1 stampCaptureTarget.erase) rfl
    actual_copy_shared_outer_binding_edges.1 rfl rfl
  decide

/-- The copied atom really cannot use the retained body binder. This is an
actual induced-edge countercheck, not merely an index inequality. -/
theorem actual_copy_retained_body_binder_impossible
    (target : (⟨Label.atom 4,.lamBody (Label.atom 3),.lamBind (Label.atom 0)⟩ : SourceEdge).toPort=
      .lamBind (Label.atom 1)) : False := by
  apply scoped_capture_step.argument_atom_not_body_copy_binder scoped_capture_initial
    (body := stampCaptureBody) (argument := stampCaptureArgument) (beta := Label.atom 0) (alpha := Label.atom 1) rfl
    (copySite := [.body,.fn]) (before := []) (suffix := [.fn]) rfl rfl
    (j := 1) (current := initFrom 2 stampCaptureBodyAfter.erase) rfl
    actual_copy_shared_outer_binding_edges.1 target rfl
  decide
#print axioms SourceRoute.initial_atom_edge
#print axioms SourceSubterm.argument_atom_not_body_binder
#print axioms StepAt.argument_atom_not_body_copy_binder
#print axioms StepAt.argument_copy_external_binder
#print axioms History.standard_argument_copy_binder_avoid
#print axioms actual_copy_external_binder_is_old_outer_lambda
#print axioms actual_copy_retained_body_binder_impossible


/-- Both real copied variable edges, with no supplied copy sites or binder
lookup, force the shared binder to be the original head ancestor. -/
theorem actual_shared_binding_collision_forces_old_ancestor :
    ∃ n site tail oldBody,([.body] : Path)=site++(.body::tail) ∧
      initialRelabelling scopedCaptureTarget 0 0=Label.atom n ∧
      scopedCaptureSource.subterm site=some (.lam (Label.atom n) oldBody) := by
  exact scoped_capture_step.shared_binding_collision_ancestor scoped_capture_initial
    (body := stampCaptureBody) (argument := stampCaptureArgument) (beta := Label.atom 0) (alpha := Label.atom 1) rfl
    actual_copy_shared_outer_binding_edges.1 actual_copy_shared_outer_binding_edges.2 rfl
    (by decide) rfl rfl

/-- Edge-image collisions recover actual distinct copies and a genuine old
argument atom, despite both variables binding the same outer lambda. -/
theorem actual_shared_binding_collision_recovers_copies :
    ∃ m p q envA ctxA a envB ctxB b,
      (⟨Label.atom 4,.lamBody (Label.atom 3),.lamBind (Label.atom 0)⟩ : SourceEdge).atom.relabel
        (initialRelabelling scopedCaptureTarget 0)=Label.atom m ∧ Label.atom m∈stampCaptureArgument.labels ∧
      ArgumentOccurrence stampCaptureBody.erase p ∧ ArgumentOccurrence stampCaptureBody.erase q ∧ p≠q ∧
      SourceSubterm [] .external (initLabels scopedCaptureTarget.erase) ([.body]++p) envA ctxA a ∧
      SourceSubterm [] .external (initLabels scopedCaptureTarget.erase) ([.body]++q) envB ctxB b ∧
      (⟨Label.atom 4,.lamBody (Label.atom 3),.lamBind (Label.atom 0)⟩ : SourceEdge)∈sourceEdges envA ctxA a ∧
      (⟨Label.atom 6,.lamBody (Label.atom 5),.lamBind (Label.atom 0)⟩ : SourceEdge)∈sourceEdges envB ctxB b ∧ Label.atom 4≠a.label ∧ Label.atom 6≠b.label := by
  exact scoped_capture_step.edge_image_collision_strict_copies scoped_capture_initial
    (body := stampCaptureBody) (argument := stampCaptureArgument) (beta := Label.atom 0) (alpha := Label.atom 1) rfl
    actual_copy_shared_outer_binding_edges.1 actual_copy_shared_outer_binding_edges.2 rfl (by decide)
#print axioms SourceSubterm.shared_binding_above
#print axioms StepAt.edge_image_collision_copies
#print axioms StepAt.edge_image_collision_strict_copies
#print axioms StepAt.shared_binding_collision_ancestor
#print axioms History.standard_shared_binding_collision_avoid
#print axioms actual_shared_binding_collision_forces_old_ancestor
#print axioms actual_shared_binding_collision_recovers_copies


def sharedBinderLeftCode : List PathCodeToken :=
  [.edge ⟨0,false⟩,.closeTok true true,.edge ⟨4,true⟩]
def sharedBinderRightCode : List PathCodeToken :=
  [.edge ⟨0,false⟩,.closeTok true true,.edge ⟨6,true⟩]

/-- These are genuine signed walks with the same old outer-lambda anchor.
An arbitrary CodedWalk alone still permits the shared-binding branch. -/
theorem actual_shared_binder_two_anchored_walks :
    CodedWalk (sourceEdges [] .external (initLabels scopedCaptureTarget.erase))
      .external sharedBinderLeftCode (.lamBody (Label.atom 3)) ∧
    CodedWalk (sourceEdges [] .external (initLabels scopedCaptureTarget.erase))
      .external sharedBinderRightCode (.lamBody (Label.atom 5)) := by
  have incoming : (⟨Label.atom 0,.external,.lamContext (Label.atom 0)⟩ : SourceEdge)∈
      sourceEdges [] .external (initLabels scopedCaptureTarget.erase) := by decide
  exact ⟨.cons (.forward incoming rfl) (.underCloseRev _) (.last (.backward actual_copy_shared_outer_binding_edges.1 rfl)),
    .cons (.forward incoming rfl) (.underCloseRev _) (.last (.backward actual_copy_shared_outer_binding_edges.2 rfl))⟩

theorem actual_anchored_walks_have_equal_image_but_different_code :
    sharedBinderLeftCode.map (PathCodeToken.imageToken (initialRelabelling scopedCaptureTarget 0))=
      sharedBinderRightCode.map (PathCodeToken.imageToken (initialRelabelling scopedCaptureTarget 0)) ∧
    sharedBinderLeftCode≠sharedBinderRightCode := by decide

/-- The concrete shared port is recovered from the actual collision; it is
not assumed to be a fresh-copy vertex or inferred from node identity alone. -/
theorem actual_common_port_collision_is_binding :
    ∃ j,SourcePort.lamBind (Label.atom 0)=.lamBind (Label.atom j) ∧
      (⟨Label.atom 4,.lamBody (Label.atom 3),.lamBind (Label.atom 0)⟩ : SourceEdge).toPort=.lamBind (Label.atom 0) ∧
      (⟨Label.atom 6,.lamBody (Label.atom 5),.lamBind (Label.atom 0)⟩ : SourceEdge).toPort=.lamBind (Label.atom 0) := by
  exact scoped_capture_step.edge_image_collision_common_port scoped_capture_initial
    (body := stampCaptureBody) (argument := stampCaptureArgument) (beta := Label.atom 0) (alpha := Label.atom 1) rfl
    actual_copy_shared_outer_binding_edges.1 actual_copy_shared_outer_binding_edges.2 rfl (by decide)
    rfl (.inr rfl) (.inr rfl)

/-- The actual ambiguous segment cannot occur inside the final local degree
of a whole Standard schedule with that first contraction. -/
theorem actual_shared_binder_segment_excluded_by_standard {localDegree : Label}
    (history : History ps scopedCaptureSource v) (last : StepAt q v z)
    (tail : ParallelHistory scopedCaptureTarget.erase z.erase) (ordinary : Atomic tail)
    (standard : Standard (.cons (singleContraction scoped_capture_step.betaAt) tail))
    (paths : (ParallelHistory.cons (singleContraction scoped_capture_step.betaAt) tail).derivation.paths=ps++[q])
    (degree : v.degreeAt q=some l)
    (image : localDegree.relabel (initialRelabelling scopedCaptureTarget 0)=l)
    (member : (⟨0,false⟩ : OrientedAtom)∈localDegree.edgeWord) : False := by
  have incoming : (⟨Label.atom 0,.external,.lamContext (Label.atom 0)⟩ : SourceEdge)∈
      sourceEdges [] .external (initLabels scopedCaptureTarget.erase) := by decide
  have equal := history.standard_next_edge_image_injective scoped_capture_step scoped_capture_initial
    (body := stampCaptureBody) (argument := stampCaptureArgument) (beta := Label.atom 0) (alpha := Label.atom 1) rfl
    (.forward incoming rfl) (.underCloseRev _)
    actual_copy_shared_outer_binding_edges.1 actual_copy_shared_outer_binding_edges.2 rfl
    (.inr rfl) (.inr rfl) last tail ordinary standard paths degree image member
  exact (by decide : (⟨Label.atom 4,.lamBody (Label.atom 3),.lamBind (Label.atom 0)⟩ : SourceEdge)≠
    ⟨Label.atom 6,.lamBody (Label.atom 5),.lamBind (Label.atom 0)⟩) equal
#print axioms StepAt.edge_image_collision_common_port
#print axioms History.standard_next_edge_image_injective
#print axioms actual_shared_binder_two_anchored_walks
#print axioms actual_anchored_walks_have_equal_image_but_different_code
#print axioms actual_shared_binder_segment_excluded_by_standard


def markerFinal : LTerm := LTerm.contract (Label.atom 0) markerGlobalDegree
  (.var (Label.atom 8) 0) (.lam (Label.atom 9) (.var (Label.atom 10) 0))
theorem marker_last : StepAt [] markerAfter markerFinal := .root _ _ _ _

theorem marker_three_steps_standard : Standard (.cons (singleContraction marker_first.betaAt)
    (.cons (singleContraction marker_second.betaAt) (.single (singleContraction marker_last.betaAt)))) := by
  refine .cons _ ⟨[.fn,.fn],marker_first.betaAt.redex⟩ (leftmost_singleton _) ?_ ?_
  · intro old before
    have member := (mem_redexPositions markerSource.erase old.val).mpr old.property
    have same : old.val=[.fn,.fn] := List.mem_singleton.mp member
    have bad : False := LeftOf.irrefl _ (same ▸ before)
    cases bad
  · refine .cons _ ⟨[.fn],marker_second.betaAt.redex⟩ (leftmost_singleton _) ?_
      (Standard.single_step _ ⟨[],marker_last.betaAt.redex⟩ (leftmost_singleton _))
    intro old before
    have member := (mem_redexPositions markerMiddle.erase old.val).mpr old.property
    have same : old.val=[.fn] := List.mem_singleton.mp member
    have bad : False := LeftOf.irrefl _ (same ▸ before)
    cases bad

/-- A genuinely nested compound local degree has an anchor in a bar payload,
so full-code reflection really propagates left and right of that anchor. -/
theorem actual_nested_degree_code_reflects {a b : SourcePort}
    (other : CodedWalk (sourceEdges [] .external (initLabels markerMiddle.erase)) a code b)
    (same : markerLocalDegree.imageCode (initialRelabelling markerMiddle 0) false=
      code.map (PathCodeToken.imageToken (initialRelabelling markerMiddle 0))) :
    markerLocalDegree.pathCode false=code := by
  have localHistory : History [[.fn]] (initLabels markerMiddle.erase) markerBasisAfter := .cons marker_basis_second (.nil _)
  obtain ⟨appId,lamId,route⟩ := (localHistory.generated_source_routes (init_is_INIT _)).degree_route
    (p := []) (l := markerLocalDegree) rfl
  have actualHistory : History [[.fn,.fn],[.fn]] markerSource markerAfter :=
    .cons marker_first (.cons marker_second (.nil _))
  have localImage : markerLocalDegree.relabel (initialRelabelling markerMiddle 0)=markerGlobalDegree :=
    Option.some.inj ((History.cons marker_second (.nil _)).local_degree_transport localHistory (p := []) rfl).1.symm
  have anchor : ∃ e∈markerLocalDegree.edgeWord,
      ¬(initialRelabelling markerMiddle 0 e.atom).Supported
        (SourceRegion (.lam (Label.atom 5) (.var (Label.atom 6) 0))) := by
    refine ⟨⟨2,false⟩,by decide,?_⟩
    intro support
    exact (by change Label.atom 2∉[Label.atom 5,Label.atom 6]; decide : ¬SourceRegion (.lam (Label.atom 5) (.var (Label.atom 6) 0)) 2)
      (Label.Supported.firstAtom support (n := 2) rfl)
  exact (actualHistory.standard_anchored_degree_code_reflection marker_first (init_is_INIT _)
    (body := .var (Label.atom 4) 0) (argument := .lam (Label.atom 5) (.var (Label.atom 6) 0))
    (beta := Label.atom 2) (alpha := Label.atom 3) rfl marker_last
    (.cons (singleContraction marker_second.betaAt) (.single (singleContraction marker_last.betaAt)))
    (.cons marker_second.betaAt (.single marker_last.betaAt)) marker_three_steps_standard rfl rfl localImage
    route.pathCode other same anchor).2.2
#print axioms History.standard_next_traversal_image_injective
#print axioms History.standard_anchored_degree_code_reflection
#print axioms marker_three_steps_standard
#print axioms actual_nested_degree_code_reflects


def argCreationCurrentArgument : LTerm := .app (Label.atom 3)
  (LTerm.contract (Label.atom 4) (Label.atom 5) (.var (Label.atom 6) 0)
    (.lam (Label.atom 7) (.var (Label.atom 8) 0))) (.lam (Label.atom 9) (.var (Label.atom 10) 0))
def argCreationMoved : LTerm := LTerm.contract (Label.atom 0) (Label.atom 1) (.var (Label.atom 2) 0) argCreationCurrentArgument
def argCreationMovedBasis : LTerm := LTerm.contract (Label.atom 0) (Label.atom 1) (.var (Label.atom 2) 0)
  (initFrom 3 argCreationCurrentArgument.erase)
theorem arg_creation_move_step : StepAt [] argCreationTarget argCreationMoved := .root _ _ _ _
theorem arg_creation_move_basis_step : StepAt [] (initLabels argCreationTarget.erase) argCreationMovedBasis := .root _ _ _ _

/-- Canonicality itself now supplies the non-argument anchor; there is no
anchor or per-edge support premise on this compound-created example. -/
theorem actual_canonical_degree_has_image_anchor :
    ∃ e∈(Label.atom 4).edgeWord,
      ¬(initialRelabelling argCreationTarget 0 e.atom).Supported
        (SourceRegion (.lam (Label.atom 7) (.var (Label.atom 8) 0))) := by
  exact History.canonical_degree_image_anchor arg_creation_step (.nil _) arg_creation_last_labelled (init_is_INIT _)
    (body := .var (Label.atom 6) 0) (argument := .lam (Label.atom 7) (.var (Label.atom 8) 0))
    (beta := Label.atom 4) (alpha := Label.atom 5) rfl argCreationRun arg_creation_canonical rfl
    (l := argCreatedDegree) rfl rfl

/-- The competing actual tail fires the outer redex and moves the created
redex from [arg] to root. It need not be canonical: left canonicality and the
original unchanged global degree suffice for common local-INIT reflection. -/
theorem actual_contracted_degree_reflects_across_redex_move :
    (initLabels argCreationTarget.erase).degreeAt [.arg]=argCreationMovedBasis.degreeAt [] := by
  have equal := arg_creation_step.canonical_same_degree_local_reflection (init_is_INIT _)
    (.nil argCreationTarget) (.nil (initLabels argCreationTarget.erase)) arg_creation_last_labelled
    (.cons arg_creation_move_step (.nil _)) (.cons arg_creation_move_basis_step (.nil _))
    argCreationRun arg_creation_canonical rfl (r := []) (l := argCreatedDegree) (localLeft := Label.atom 4) (localRight := Label.atom 4) rfl rfl rfl rfl
  exact congrArg some equal

/-- The histories and pointed sites genuinely differ although the original
compound degree agrees; this is not a replay-determinism fixture. -/
theorem moved_redex_fixture_is_not_same_schedule :
    ([] : List Path)≠[[]] ∧ ([.arg] : Path)≠[] ∧
      argCreationMoved.degreeAt []=some argCreatedDegree := by decide
#print axioms History.canonical_degree_image_anchor
#print axioms StepAt.canonical_same_degree_local_reflection
#print axioms actual_canonical_degree_has_image_anchor
#print axioms actual_contracted_degree_reflects_across_redex_move
#print axioms moved_redex_fixture_is_not_same_schedule


def argCreationMovedLast : BetaAt argCreationMoved.erase [] identity := ⟨_,_,rfl,rfl⟩
def argCreationMovedRun : ExtractionRun argCreationInitial.erase := .of
  (.cons (singleContraction arg_creation_step.betaAt)
    (.cons (singleContraction arg_creation_move_step.betaAt) (.single (singleContraction argCreationMovedLast))))
  (.cons arg_creation_step.betaAt (.cons arg_creation_move_step.betaAt (.single argCreationMovedLast)))

/-- The real moved-redex history from the contracted-label fixture is not
canonical. Equal compound degrees force canonical schedules to coincide,
whereas these actual schedules have lengths two and three. -/
theorem actual_moved_compound_run_is_not_canonical : ¬CanonicalRun argCreationMovedRun := by
  intro canonical
  obtain ⟨target,last,erased⟩ := lift_betaAt (t := argCreationMoved) argCreationMovedLast
  have left : History [[.arg,.fn]] argCreationInitial argCreationTarget := .cons arg_creation_step (.nil _)
  have right : History [[.arg,.fn],[]] argCreationInitial argCreationMoved :=
    .cons arg_creation_step (.cons arg_creation_move_step (.nil _))
  have equal := left.canonical_degree_paths_unique arg_creation_last_labelled right last (init_is_INIT _)
    argCreationRun argCreationMovedRun arg_creation_canonical canonical rfl rfl
    (l := argCreatedDegree) rfl rfl
  have lengths := congrArg List.length equal
  change 2=3 at lengths
  omega

/-- Any genuinely canonical competitor with this compound-created degree
has the whole actual canonical run, rather than just the same endpoint. -/
theorem actual_compound_degree_determines_canonical_run
    (history : History ps argCreationInitial u) (last : StepAt q u v)
    (run : ExtractionRun argCreationInitial.erase) (canonical : CanonicalRun run)
    (paths : run.history.derivation.paths=ps++[q]) (degree : u.degreeAt q=some argCreatedDegree) :
    run=argCreationRun := by
  have left : History [[.arg,.fn]] argCreationInitial argCreationTarget := .cons arg_creation_step (.nil _)
  exact (left.canonical_degree_runs_unique arg_creation_last_labelled history last (init_is_INIT _)
    argCreationRun run arg_creation_canonical canonical rfl paths rfl degree).symm
#print axioms History.canonical_degree_paths_unique
#print axioms History.canonical_degree_runs_unique
#print axioms actual_moved_compound_run_is_not_canonical
#print axioms actual_compound_degree_determines_canonical_run


def compoundCopyOuterSource : LTerm := .lam (Label.atom 50) creationDuplicateInitial
theorem compound_copy_outer_initial : INIT compoundCopyOuterSource := by
  constructor
  · intro l member
    rcases List.mem_cons.mp member with equal | inside
    · cases equal; exact ⟨50,rfl⟩
    · exact (init_is_INIT _).1 l inside
  · exact List.nodup_cons.mpr ⟨by decide,(init_is_INIT _).2⟩

def compoundCopyOuterLeft : RedexWithHistory compoundCopyOuterSource.erase :=
  ⟨(LTerm.lam (Label.atom 50) creationDuplicateAfter).erase,
    .cons (singleContraction (StepAt.body creation_duplication_step).betaAt)
      (.single (singleContraction (StepAt.body creation_copy_step).betaAt)),
    ⟨[.body,.fn],.app identity identity,rfl,True.intro⟩⟩
def compoundCopyOuterRight : RedexWithHistory compoundCopyOuterSource.erase :=
  ⟨(LTerm.lam (Label.atom 50) creationDuplicateRightAfter).erase,
    .cons (singleContraction (StepAt.body creation_duplication_step).betaAt)
      (.single (singleContraction (StepAt.body creation_right_copy_step).betaAt)),
    ⟨[.body,.arg],.app identity identity,rfl,True.intro⟩⟩



/-- The general inverse constructs a genuine historical family witness for
new compound redexes created in different actual copies. The original INIT
uses outer atom 50, so this also exercises arbitrary initial naming. -/
theorem different_actual_compound_copies_are_historical_family :
    FamilyEq compoundCopyOuterLeft compoundCopyOuterRight := by
  apply (family_iff_degree compoundCopyOuterSource compound_copy_outer_initial _ _).mpr
  have left : History [[.body],[.body,.fn,.fn]] compoundCopyOuterSource
      (.lam (Label.atom 50) creationDuplicateAfter) :=
    .cons (.body creation_duplication_step) (.cons (.body creation_copy_step) (.nil _))
  have right : History [[.body],[.body,.arg,.fn]] compoundCopyOuterSource
      (.lam (Label.atom 50) creationDuplicateRightAfter) :=
    .cons (.body creation_duplication_step) (.cons (.body creation_right_copy_step) (.nil _))
  change degreeAlong compoundCopyOuterSource [[.body],[.body,.fn,.fn]] [.body,.fn]=
    degreeAlong compoundCopyOuterSource [[.body],[.body,.arg,.fn]] [.body,.arg]
  rw [degreeAlong_witness left,degreeAlong_witness right]
  rfl

/-- Both compared degrees are genuinely newly created compounds, the
pointed schedules differ, and the named source is closed. -/
theorem compound_inverse_fixture_is_genuine :
    compoundCopyOuterLeft.history.derivation.paths≠compoundCopyOuterRight.history.derivation.paths ∧
    ∃ l,degreeAlong compoundCopyOuterSource compoundCopyOuterLeft.history.derivation.paths compoundCopyOuterLeft.redex.val=some l ∧
      1<l.length ∧ Closed compoundCopyOuterSource.erase := by
  refine ⟨by decide,?_,?_⟩
  · exact (LTerm.contract (Label.atom 6) (Label.atom 7) (.var (Label.atom 8) 0) (.lam (Label.atom 9) (.var (Label.atom 10) 0))).label
  · constructor
    · rfl
    · constructor
      · decide
      · simp [compoundCopyOuterSource,LTerm.erase,creationDuplicateInitial,erase_initLabels,creationSource,identity,Closed,Scoped]

def repeatedLeftPoint : RedexWithHistory badInitial.erase := ⟨badInitial.erase,.nil _,⟨[.fn],_,rfl,True.intro⟩⟩
def repeatedRightPoint : RedexWithHistory badInitial.erase := ⟨badInitial.erase,.nil _,⟨[.arg],_,rfl,True.intro⟩⟩

/-- Equal repeated labels do not define families. The genuine old historical
families are separated using an independent valid INIT labelling. -/
theorem repeated_labels_equal_but_families_different :
    degreeAlong badInitial [] [.fn]=degreeAlong badInitial [] [.arg] ∧
      ¬FamilyEq repeatedLeftPoint repeatedRightPoint := by
  constructor
  · rfl
  · intro family
    have wrong := (family_iff_degree_of_erase repeatedLeftPoint repeatedRightPoint (initLabels badInitial.erase)
      (init_is_INIT _) (erase_initLabels _)).mp family
    exact (by decide : degreeAlong (initLabels badInitial.erase) [] [.fn]≠
      degreeAlong (initLabels badInitial.erase) [] [.arg]) wrong
#print axioms canonical_point_degree_unique
#print axioms family_iff_degree
#print axioms family_iff_degree_of_erase
#print axioms different_actual_compound_copies_are_historical_family
#print axioms compound_inverse_fixture_is_genuine
#print axioms repeated_labels_equal_but_families_different


-- P06 finite syntax fibers: independent of graph-u exactness and Matches.
def fiberOmegaBody : Term := .app (.var 0) (.var 0)
def fiberOmega : Term := .app (.lam fiberOmegaBody) (.lam fiberOmegaBody)
def fiberOmegaMarked : Marked := .app [] (.lam (.app [] (.var 0) (.var 0))) (.lam (.app [] (.var 0) (.var 0)))

theorem omega_fiber_is_explicit_finite :
    redexFiberPaths fiberOmega (fun _ => true)=[[]] ∧
      (Graph.FiniteNames.all : List (RedexFiber fiberOmega (fun _ => true))).map Subtype.val=[[]] := ⟨rfl,rfl⟩

theorem omega_fiber_actual_complete :
    Marked.CompleteOldDevelopment (redexFiberPaths fiberOmega (fun _ => true)) fiberOmega [[]] fiberOmegaMarked := by
  apply (Marked.completeOld_iff _ _).mpr
  refine ⟨.cons (.root _ _ _) (.nil _),?_⟩
  exact ⟨⟨True.intro,True.intro⟩,⟨True.intro,True.intro⟩⟩

/-- Nonempty old selection, a genuine nonempty complete beta history,
exhausted old name, and an identical source/target term coexist. -/
theorem omega_nonempty_development_can_return_to_itself :
    BetaHistory [[]] fiberOmega fiberOmega ∧
      Marked.tracePositions [] fiberOmegaMarked=[] ∧ fiberOmegaMarked.erase=fiberOmega := by
  refine ⟨?_,redexFiber_complete_exhausted omega_fiber_actual_complete (by decide),rfl⟩
  exact redexFiber_complete_betaHistory omega_fiber_actual_complete

/-- The positive theorem consumes the real complete development, without
assuming an endpoint inequality or a supplied nonempty schedule. -/
theorem omega_fiber_positive_history :
    ∃ p rest middle,([[]] : List Path)=p::rest ∧ BetaAt fiberOmega p middle ∧
      BetaHistory rest middle fiberOmegaMarked.erase :=
  redexFiber_complete_nonempty omega_fiber_actual_complete (by decide)

/-- A graph-side predicate may select no redex even when the syntax has one.
Every complete development of that empty fiber is then exactly reflexive. -/
theorem empty_fiber_is_reflexive_even_for_a_redex
    (complete : Marked.CompleteOldDevelopment (redexFiberPaths (.app identity identity) (fun _ => false))
      (.app identity identity) ps marked) : ps=[] ∧ marked.erase=.app identity identity :=
  redexFiber_complete_empty_endpoint complete rfl

/-- Complete finite fiber existence is actual old-residual reduction and
syntax beta multi-reduction, including an empty predicate. -/
theorem empty_fiber_has_real_complete :
    ∃ ps marked,Marked.CompleteOldDevelopment (redexFiberPaths (.app identity identity) (fun _ => false))
      (.app identity identity) ps marked ∧ ps=[] ∧ marked.erase=.app identity identity := by
  obtain ⟨ps,marked,complete⟩ := redexFiber_complete_exists (.app identity identity) (fun _ => false)
  exact ⟨ps,marked,complete,empty_fiber_is_reflexive_even_for_a_redex complete⟩

/-- New root redex creation is not reselected by an old finite fiber. -/
theorem two_old_fiber_events_leave_a_new_redex
    (complete : Marked.CompleteOldDevelopment
      (redexFiberPaths (.app (.app identity identity) (.app identity identity)) (fun _ => true))
      (.app (.app identity identity) (.app identity identity)) ps marked) :
    marked.erase=.app identity identity ∧ Marked.activePositions marked=[] := by
  have endpoint := redexFiber_complete_endpoint complete
  constructor
  · rw [endpoint]
    rfl
  · exact (Marked.normal_iff_active_empty _).mp ((Marked.completeOld_iff _ _).mp complete).2

/-- Actual capture-avoiding development shifts the free variable beneath the
surviving lambda. The fiber endpoint is not a textual substitution. -/
theorem fiber_capture_avoids_binding
    (complete : Marked.CompleteOldDevelopment
      (redexFiberPaths (.app (.lam (.lam (.var 1))) (.var 0)) (fun _ => true))
      (.app (.lam (.lam (.var 1))) (.var 0)) ps marked) : marked.erase=.lam (.var 1) := by
  rw [redexFiber_complete_endpoint complete]
  rfl
#print axioms redexFiber_complete_exists
#print axioms redexFiber_complete_empty_iff
#print axioms redexFiber_complete_nonempty
#print axioms redexFiber_complete_exhausted
#print axioms redexFiber_complete_residuals
#print axioms omega_fiber_actual_complete
#print axioms omega_nonempty_development_can_return_to_itself
#print axioms omega_fiber_positive_history
#print axioms empty_fiber_has_real_complete
#print axioms two_old_fiber_events_leave_a_new_redex
#print axioms fiber_capture_avoids_binding


namespace P06Children
open Lamping.AG Lamping.Graph

/-- At nonzero level 7, the actual matching body access is cut back to its
physical lambda parent and rebuilt from that same parent/port by the API. -/
theorem encoded_identity_actual_body_child :
    ∃ (parent child : RootAccess (encode 7 identity).net (.inl ()))
      (node : (encode 7 identity).N) (ctx body : Port ((encode 7 identity).net.label node).sort)
      (tail : List (Endpoint (encode 7 identity).net)),
      SyntaxChildPorts ((encode 7 identity).net.label node).sort ctx body .body ∧
      accessWord (encode 7 identity).net parent.val=[] ∧ accessWord (encode 7 identity).net child.val=[.body] ∧
      child.val=parent.val++(.inl ⟨node,body⟩)::tail := by
  have matching := encode_closed_matches identity (by change 0<1; decide) 7
  obtain ⟨access,word,_⟩ := Matches.observation (encode 7 identity).net matching (⟨[.body],rfl⟩ : Position identity)
  obtain ⟨parent,node,ctx,body,_,roles,parentWord,finish,_⟩ := access.before_syntax_token [] .body word
  obtain ⟨shape,ctxRole,bodyRole⟩ := roles.body_roles
  obtain ⟨child,tail,split,childWord⟩ := matching.body_child_access parent node ctx body shape ctxRole bodyRole finish
  exact ⟨parent,child,node,ctx,body,tail,roles,parentWord,by simpa only [parentWord,List.nil_append] using childWord,split⟩

/-- A real encoded application has its actual argument access extending
that very physical app context, not merely another equal-kind access. -/
theorem encoded_application_actual_argument_child :
    ∃ (parent child : RootAccess (encode 7 (.app identity identity)).net (.inl ()))
      (node : (encode 7 (.app identity identity)).N)
      (ctx argument : Port ((encode 7 (.app identity identity)).net.label node).sort)
      (tail : List (Endpoint (encode 7 (.app identity identity)).net)),
      SyntaxChildPorts ((encode 7 (.app identity identity)).net.label node).sort ctx argument .arg ∧
      accessWord (encode 7 (.app identity identity)).net parent.val=[] ∧
      accessWord (encode 7 (.app identity identity)).net child.val=[.arg] ∧
      child.val=parent.val++(.inl ⟨node,argument⟩)::tail := by
  have matching := encode_closed_matches (.app identity identity) (by constructor <;> change 0<1 <;> decide) 7
  obtain ⟨access,word,_⟩ := Matches.observation (encode 7 (.app identity identity)).net matching (⟨[.arg],rfl⟩ : Position (.app identity identity))
  obtain ⟨parent,node,ctx,argument,_,roles,parentWord,finish,_⟩ := access.before_syntax_token [] .arg word
  obtain ⟨shape,ctxRole,argRole⟩ := roles.argument_roles
  obtain ⟨child,tail,split,childWord⟩ := matching.argument_child_access parent node ctx argument shape ctxRole argRole finish
  exact ⟨parent,child,node,ctx,argument,tail,roles,parentWord,by simpa only [parentWord,List.nil_append] using childWord,split⟩

/-- Same-node binding is not a body edge; syntax child roles retain the exact
port distinction and cannot be inferred from node equality alone. -/
theorem lambda_binding_port_is_not_body_child :
    ¬SyntaxChildPorts (.op .lam) (.inl ()) lamBind .body := by intro roles; cases roles

#print axioms RootAccess.before_syntax_token
#print axioms Matches.child_access
#print axioms Matches.argument_child_access
#print axioms Matches.body_child_access
#print axioms encoded_identity_actual_body_child
#print axioms encoded_application_actual_argument_child
#print axioms lambda_binding_port_is_not_body_child
end P06Children

end Lamping.Checks.DegreeFamily

namespace Lamping.Checks.DegreeFamily.P06Variables
open Lamping Lambda AG Graph
private def outerBound : Term := .lam (.lam (.var 1))
theorem actual_outer_binder_prefix :
    ∃ (access parent : RootAccess (encode 7 outerBound).net (.inl ()))
      (loop : List (Endpoint (encode 7 outerBound).net)) (a b c : Context)
      (binding : BindingLoop (encode 7 outerBound).net loop b c)
      (ctx : Port ((encode 7 outerBound).net.label binding.binder).sort),
      accessWord (encode 7 outerBound).net access.val=[.body,.body] ∧
      accessWord (encode 7 outerBound).net parent.val=[] ∧
      access.val=parent.val++loop ∧ HEq ctx (Sum.inl () : Port (.op .lam)) ∧
      parent.val.getLast?=some ((encode 7 outerBound).net.wire (.inl ⟨binding.binder,ctx⟩)) ∧
      Labelling (encode 7 outerBound).net parent.val a b ∧
      binderDepth (accessWord (encode 7 outerBound).net loop)=1 := by
  have matching := encode_closed_matches outerBound (by change 1<2; decide) 7
  obtain ⟨access,word,_⟩ := Matches.observation (encode 7 outerBound).net matching
    (⟨[.body,.body],rfl⟩ : Position outerBound)
  obtain ⟨parent,loop,a,b,c,binding,ctx,body,split,role,finish,labels,_,words,depth⟩ :=
    matching.variable_binding_access access (by rw [word]; rfl)
  have loopNonempty : accessWord (encode 7 outerBound).net loop≠[] := by
    intro empty
    rw [empty] at depth
    cases depth
  have lengthEq := congrArg List.length words
  rw [word,List.length_append,List.length_cons] at lengthEq
  have positive : 0<(accessWord (encode 7 outerBound).net loop).length := List.length_pos_iff.mpr loopNonempty
  have parentEmpty : accessWord (encode 7 outerBound).net parent.val=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons,List.length_nil] at lengthEq; omega)
  exact ⟨access,parent,loop,a,b,c,binding,ctx,word,parentEmpty,split,role,finish,labels,depth.symm⟩
theorem inner_lambda_is_not_var_one_binder :
    ¬∃ loop : Path, [.body,.body]=[.body]++(.body::loop) ∧ binderDepth loop=1 := by
  rintro ⟨loop,eq,depth⟩
  have empty : loop=[] := by simpa using eq.symm
  subst loop
  cases depth
#print axioms RootAccess.binding_prefix
#print axioms Matches.variable_binding_access
#print axioms actual_outer_binder_prefix
#print axioms inner_lambda_is_not_var_one_binder
end Lamping.Checks.DegreeFamily.P06Variables



















































namespace Lamping.Checks.DegreeFamily.P06RedexProvenance
open Lamping Lambda AG Graph
private def nestedRedex : Term := .lam (.app (.lam (.var 0)) (.var 0))
private def actualRedex : RedexOcc nestedRedex := ⟨[.body],by exact ⟨_,rfl,True.intro⟩⟩
theorem nonroot_actual_provenance :
    ∃ source : ActualRedexAccess (encode 7 nestedRedex).net (.inl ()) actualRedex,
      accessWord (encode 7 nestedRedex).net source.parent.val=[.body] ∧
      accessWord (encode 7 nestedRedex).net source.child.val=[.body,.fn] ∧
      source.child.val=source.parent.val++source.connection.edges ∧
      ForwardProperPath (encode 7 nestedRedex).net source.connection.edges := by
  have matching := encode_closed_matches nestedRedex (by change (0<2) ∧ 0<1; decide) 7
  obtain ⟨source⟩ := matching.actual_redex_access actualRedex
  exact ⟨source,source.parentWord,source.childWord,source.split,source.connection.proper⟩
theorem any_two_actual_provenances_have_same_endpoints
    (first second : ActualRedexAccess (encode 7 nestedRedex).net (.inl ()) actualRedex) :
    first.parent=second.parent ∧ first.child=second.child ∧
      first.connection.app=second.connection.app ∧ first.connection.lam=second.connection.lam :=
  ActualRedexAccess.endpoints_unique
    (encode_closed_matches nestedRedex (by change (0<2) ∧ 0<1; decide) 7) first second
private def twins : Term := .app (.app (.lam (.var 0)) (.lam (.var 0))) (.app (.lam (.var 0)) (.lam (.var 0)))
private def leftRedex : RedexOcc twins := ⟨[.fn],by exact ⟨_,rfl,True.intro⟩⟩
private def rightRedex : RedexOcc twins := ⟨[.arg],by exact ⟨_,rfl,True.intro⟩⟩
theorem different_occurrences_keep_different_literal_parents :
    ∃ (left : ActualRedexAccess (encode 7 twins).net (.inl ()) leftRedex)
      (right : ActualRedexAccess (encode 7 twins).net (.inl ()) rightRedex),
      left.parent≠right.parent := by
  have matching := encode_closed_matches twins (by change ((0<1) ∧ 0<1) ∧ ((0<1) ∧ 0<1); decide) 7
  obtain ⟨left⟩ := matching.actual_redex_access leftRedex
  obtain ⟨right⟩ := matching.actual_redex_access rightRedex
  refine ⟨left,right,?_⟩
  intro eq
  have words := left.parentWord.symm.trans ((congrArg (fun p => accessWord (encode 7 twins).net p.val) eq).trans right.parentWord)
  cases words
#print axioms Matches.actual_redex_access
#print axioms ActualRedexAccess.endpoints_unique
#print axioms nonroot_actual_provenance
#print axioms any_two_actual_provenances_have_same_endpoints
#print axioms different_occurrences_keep_different_literal_parents
end Lamping.Checks.DegreeFamily.P06RedexProvenance


namespace Lamping.Checks.DegreeFamily.P06BetaFiber
open Lamping Lambda AG Graph
private def pairTerm : Term := .app (.lam (.var 0)) (.lam (.var 0))
private def pairRedex : RedexOcc pairTerm := ⟨[],by exact ⟨_,rfl,True.intro⟩⟩
theorem actual_pair_fiber_has_real_positive_development :
    ∃ (source : ActualRedexAccess (encode 7 pairTerm).net (.inl ()) pairRedex) (ps : List Path) (marked : Marked),
      []∈physicalBetaFiberPaths (encode 7 pairTerm).net (.inl ()) pairTerm source.connection.app source.connection.lam ∧
      Marked.CompleteOldDevelopment
        (physicalBetaFiberPaths (encode 7 pairTerm).net (.inl ()) pairTerm source.connection.app source.connection.lam)
        pairTerm ps marked ∧
      ∃ p rest middle,ps=p::rest ∧ BetaAt pairTerm p middle ∧ BetaHistory rest middle marked.erase := by
  have matching := encode_closed_matches pairTerm (by change (0<1) ∧ 0<1; decide) 7
  obtain ⟨source⟩ := matching.actual_redex_access pairRedex
  have member : []∈physicalBetaFiberPaths (encode 7 pairTerm).net (.inl ()) pairTerm source.connection.app source.connection.lam :=
    (mem_physicalBetaFiberPaths _ _ _ _ _ _).mpr ⟨pairRedex,source,rfl,rfl,rfl⟩
  obtain ⟨ps,marked,complete⟩ := physicalBetaFiber_complete_exists (encode 7 pairTerm).net (.inl ()) pairTerm source.connection.app source.connection.lam
  have positive : physicalBetaFiberPaths (encode 7 pairTerm).net (.inl ()) pairTerm source.connection.app source.connection.lam≠[] := by
    intro empty
    rw [empty] at member
    cases member
  exact ⟨source,ps,marked,member,complete,physicalBetaFiber_complete_nonempty complete positive⟩
theorem any_rich_witness_selects_the_same_physical_pair
    (first second : ActualRedexAccess (encode 7 pairTerm).net (.inl ()) pairRedex) :
    pairRedex.val∈physicalBetaFiberPaths (encode 7 pairTerm).net (.inl ()) pairTerm first.connection.app first.connection.lam ↔
      second.connection.app=first.connection.app ∧ second.connection.lam=first.connection.lam :=
  ActualRedexAccess.physical_selection_iff _ _ _ _ _
    (encode_closed_matches pairTerm (by change (0<1) ∧ 0<1; decide) 7) second
theorem no_syntax_redex_gives_empty_fiber (app lam : (encode 7 (.lam (.var 0))).N) :
    physicalBetaFiberPaths (encode 7 (.lam (.var 0))).net (.inl ()) (.lam (.var 0)) app lam=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p member
  have valid := redexFiberPaths_valid member
  change p∈([] : List Path) at valid
  cases valid
#print axioms ActualRedexAccess.physical_selection_iff
#print axioms physicalBetaFiber_complete_exists
#print axioms physicalBetaFiber_complete_nonempty
#print axioms PathSite.betaSyntaxFiber_complete_exists
#print axioms actual_pair_fiber_has_real_positive_development
#print axioms any_rich_witness_selects_the_same_physical_pair
#print axioms no_syntax_redex_gives_empty_fiber
end Lamping.Checks.DegreeFamily.P06BetaFiber


namespace Lamping.Checks.DegreeFamily.P06SubstitutionOrigins
open Lamping Lambda
private def payload : Term := .app (.var 0) (.lam (.var 0))
private def captureSource : Term := .lam (.var 1)
/-- A copied free variable under one surviving binder is var 1, and the
actual inverse decomposition returns the old var-1 leaf and payload fn path. -/
theorem capture_free_variable_has_exact_origin :
    ∃ q r k, q=[.body] ∧ r=[.fn] ∧ k=1 ∧
      [.body,.fn]=q++r ∧ subtermAt captureSource q=some (.var k) ∧
      subtermAt (liftSubN (binderDepth q) (singleSub payload) k) r=some (.var 1) := by
  have target : subtermAt (subst (singleSub payload) captureSource) [.body,.fn]=some (.var 1) := rfl
  rcases subtermAt_subst_origins target with ⟨old,atOld,_,_⟩ | ⟨q,r,k,split,atVar,replacement⟩
  · simp [captureSource,subtermAt] at atOld
  · have unique := variable_origin_prefix_unique atVar
      (show subtermAt captureSource [.body]=some (.var 1) from rfl) split.symm
    exact ⟨q,r,k,unique.1,unique.2.1,unique.2.2,split,atVar,replacement⟩
/-- The lambda *inside* the copied payload retains its own var 0; it is not
shifted to var 1 merely because the payload was lifted under the outer binder. -/
theorem copied_internal_binder_has_exact_origin :
    ∃ q r k,q=[.body] ∧ r=[.arg,.body] ∧ k=1 ∧
      subtermAt (liftSubN (binderDepth q) (singleSub payload) k) r=some (.var 0) := by
  have target : subtermAt (subst (singleSub payload) captureSource) [.body,.arg,.body]=some (.var 0) := rfl
  rcases subtermAt_subst_origins target with ⟨old,atOld,_,_⟩ | ⟨q,r,k,split,atVar,replacement⟩
  · simp [captureSource,subtermAt] at atOld
  · have unique := variable_origin_prefix_unique atVar
      (show subtermAt captureSource [.body]=some (.var 1) from rfl) split.symm
    exact ⟨q,r,k,unique.1,unique.2.1,unique.2.2,replacement⟩
theorem retained_lambda_is_the_nonvariable_branch :
    ∃ old, subtermAt captureSource []=some old ∧ (∀ k,old≠.var k) ∧
      subst (singleSub payload) captureSource=subst (liftSubN (binderDepth []) (singleSub payload)) old := by
  have target : subtermAt (subst (singleSub payload) captureSource) []=
      some (subst (singleSub payload) captureSource) := rfl
  rcases subtermAt_subst_origins target with retained | ⟨q,r,k,split,atVar,_⟩
  · exact retained
  · have contradiction := nonvariable_origin_not_variable_prefix
      (show subtermAt captureSource []=some captureSource from rfl)
      (show ∀ j,captureSource≠.var j from by intro j eq; cases eq) atVar split
    exact False.elim contradiction
theorem replacement_forward_lookup_reconstructs_capture :
    subtermAt (subst (singleSub payload) captureSource) ([.body]++[.fn])=some (.var 1) :=
  subtermAt_subst_from_variable (show subtermAt captureSource [.body]=some (.var 1) from rfl) rfl
theorem wrong_free_shift_is_false :
    subtermAt (subst (singleSub payload) captureSource) [.body,.fn]≠some (.var 0) := by decide
theorem wrong_internal_shift_is_false :
    subtermAt (subst (singleSub payload) captureSource) [.body,.arg,.body]≠some (.var 1) := by decide
#print axioms subtermAt_subst_origins
#print axioms variable_origin_prefix_unique
#print axioms nonvariable_origin_not_variable_prefix
#print axioms subtermAt_subst_from_variable
#print axioms capture_free_variable_has_exact_origin
#print axioms copied_internal_binder_has_exact_origin
#print axioms retained_lambda_is_the_nonvariable_branch
#print axioms replacement_forward_lookup_reconstructs_capture
#print axioms wrong_free_shift_is_false
#print axioms wrong_internal_shift_is_false
/-- Equal copied lambda subterms may have distinct actual old variable leaves.
The uniqueness theorem is relative to a single target path. -/
theorem equal_copies_have_distinct_old_prefixes :
    ∃ qLeft qRight rLeft rRight kLeft kRight,
      subtermAt (.app (.var 0) (.var 0)) qLeft=some (.var kLeft) ∧
      subtermAt (.app (.var 0) (.var 0)) qRight=some (.var kRight) ∧
      subtermAt (liftSubN (binderDepth qLeft) (singleSub payload) kLeft) rLeft=some (.lam (.var 0)) ∧
      subtermAt (liftSubN (binderDepth qRight) (singleSub payload) kRight) rRight=some (.lam (.var 0)) ∧
      qLeft≠qRight := by
  have left : subtermAt (subst (singleSub payload) (.app (.var 0) (.var 0))) [.fn,.arg]=some (.lam (.var 0)) := rfl
  have right : subtermAt (subst (singleSub payload) (.app (.var 0) (.var 0))) [.arg,.arg]=some (.lam (.var 0)) := rfl
  rcases subtermAt_subst_origins left with ⟨_,impossible,_,_⟩ | ⟨ql,rl,kl,sl,vl,pl⟩
  · simp [subtermAt] at impossible
  rcases subtermAt_subst_origins right with ⟨_,impossible,_,_⟩ | ⟨qr,rr,kr,sr,vr,pr⟩
  · simp [subtermAt] at impossible
  have leftOrigin := variable_origin_prefix_unique vl
    (show subtermAt (.app (.var 0) (.var 0)) [.fn]=some (.var 0) from rfl) sl.symm
  have rightOrigin := variable_origin_prefix_unique vr
    (show subtermAt (.app (.var 0) (.var 0)) [.arg]=some (.var 0) from rfl) sr.symm
  refine ⟨ql,qr,rl,rr,kl,kr,vl,vr,pl,pr,?_⟩
  rw [leftOrigin.1,rightOrigin.1]
  decide
#print axioms equal_copies_have_distinct_old_prefixes
end Lamping.Checks.DegreeFamily.P06SubstitutionOrigins


namespace Lamping.Checks.DegreeFamily.P06ContractumOrigins
open Lamping Lambda
/-- A protected inner binder is a retained old variable, not an inserted
argument, even when the external argument has a very different free index. -/
theorem protected_variable_is_retained :
    ∃ k j,subtermAt (.lam (.var 0)) [.body]=some (.var k) ∧
      k≠binderDepth [.body] ∧
      liftSubN (binderDepth [.body]) (singleSub (.var 99)) k=.var j ∧ (.var 0 : Term)=.var j := by
  have target : subtermAt (contract (.lam (.var 0)) (.var 99)) [.body]=some (.var 0) := rfl
  rcases subtermAt_contract_origins target with ⟨old,atOld,nonvar,_⟩ | retained | ⟨q,r,split,occurs,_⟩
  · have eq : old=.var 0 := (Option.some.inj atOld).symm
    exact False.elim (nonvar 0 eq)
  · exact retained
  · exact False.elim (retained_variable_not_argument_origin
      (show subtermAt (.lam (.var 0)) [.body]=some (.var 0) from rfl)
      (by decide) occurs split)
/-- Free old variables beyond the removed binder drop one index and are
still retained-body origins, rather than argument instances. -/
theorem free_external_variable_is_retained :
    ∃ k j,subtermAt (.lam (.var 2)) [.body]=some (.var k) ∧
      k≠binderDepth [.body] ∧
      liftSubN (binderDepth [.body]) (singleSub (.lam (.var 0))) k=.var j ∧ (.var 1 : Term)=.var j := by
  have target : subtermAt (contract (.lam (.var 2)) (.lam (.var 0))) [.body]=some (.var 1) := rfl
  rcases subtermAt_contract_origins target with ⟨old,atOld,nonvar,_⟩ | retained | ⟨q,r,split,occurs,_⟩
  · have eq : old=.var 2 := (Option.some.inj atOld).symm
    exact False.elim (nonvar 2 eq)
  · exact retained
  · exact False.elim (retained_variable_not_argument_origin
      (show subtermAt (.lam (.var 2)) [.body]=some (.var 2) from rfl)
      (by decide) occurs split)
/-- The body itself may be the contracted variable. The argument copy then
starts at the empty source occurrence and has a nonempty relative body path. -/
theorem root_variable_copy_has_actual_empty_origin :
    ∃ q r,q=[] ∧ r=[.body] ∧ ArgumentOccurrence (.var 0) q ∧
      subtermAt (rename (fun i => i+binderDepth q) (.lam (.var 0))) r=some (.var 0) := by
  have target : subtermAt (contract (.var 0) (.lam (.var 0))) [.body]=some (.var 0) := rfl
  rcases subtermAt_contract_origins target with ⟨_,atOld,_,_⟩ | ⟨_,_,atOld,_,_,_⟩ | ⟨q,r,split,occurs,copy⟩
  · simp [subtermAt] at atOld
  · simp [subtermAt] at atOld
  · have unique := contract_argument_origin_unique occurs
      (show ArgumentOccurrence (.var 0) [] from rfl) split.symm
    exact ⟨q,r,unique.1,unique.2,occurs,copy⟩
theorem actual_capture_copy_reconstructs_target :
    subtermAt (contract (.lam (.var 1)) (.app (.var 0) (.lam (.var 0)))) ([.body]++[.fn])=some (.var 1) :=
  subtermAt_contract_from_argument (show ArgumentOccurrence (.lam (.var 1)) [.body] from rfl) rfl
theorem external_variable_is_not_argument_bound :
    ¬ArgumentOccurrence (.lam (.var 2)) [.body] := by change ¬some (.var 2 : Term)=some (.var 1); decide
#print axioms subtermAt_contract_origins
#print axioms contract_argument_origin_unique
#print axioms retained_variable_not_argument_origin
#print axioms protected_variable_is_retained
#print axioms free_external_variable_is_retained
#print axioms root_variable_copy_has_actual_empty_origin
#print axioms actual_capture_copy_reconstructs_target
#print axioms external_variable_is_not_argument_bound
/-- A copied argument root itself has an empty relative path; this is not
silently excluded when choosing a syntax origin. -/
theorem argument_root_keeps_empty_relative_path :
    ∃ q r,q=[] ∧ r=[] ∧ ArgumentOccurrence (.var 0) q ∧
      subtermAt (rename (fun i => i+binderDepth q) (.lam (.var 0))) r=some (.lam (.var 0)) := by
  have target : subtermAt (contract (.var 0) (.lam (.var 0))) []=some (.lam (.var 0)) := rfl
  rcases subtermAt_contract_origins target with ⟨old,atOld,nonvar,_⟩ | ⟨k,_,atOld,notBound,_,_⟩ | ⟨q,r,split,occurs,copy⟩
  · exact False.elim (nonvar 0 ((Option.some.inj atOld).symm))
  · have eq : k=0 := Term.var.inj (Option.some.inj atOld).symm
    exact False.elim (notBound eq)
  · have unique := contract_argument_origin_unique occurs
      (show ArgumentOccurrence (.var 0) [] from rfl) split.symm
    exact ⟨q,r,unique.1,unique.2,occurs,copy⟩
#print axioms argument_root_keeps_empty_relative_path
end Lamping.Checks.DegreeFamily.P06ContractumOrigins



namespace Lamping.Checks.DegreeFamily.P06SelectedOrigins
open Lamping Lambda Labelled
private def ident : Term := .lam (.var 0)
private def source : Term := .app (.lam (.app (.var 0) (.var 0))) (.app ident ident)
private def initial : LTerm := initLabels source
private def selected : List Path := [[],[.arg]]
private def oldArg : Marked := .red [[.arg]] (.var 0) (.lam (.var 0))
private def endpoint : Marked := .app [] (.lam (.var 0)) (.lam (.var 0))
/-- One old argument redex is actually copied and its two residuals are
contracted, while the final newly exposed root stays passive. -/
theorem real_duplicate_relative_development :
    Marked.RelativeHistory [[],[.fn],[.arg]] (Marked.mark selected source) endpoint :=
  .cons (.root [[]] (.app [] (.var 0) (.var 0)) oldArg)
    (.cons (.appL (.root [[.arg]] (.var 0) (.lam (.var 0))))
      (.cons (.appR (.root [[.arg]] (.var 0) (.lam (.var 0)))) (.nil _)))
theorem actual_copied_development_uses_only_original_selected_degrees :
    ∃ target,History [[],[.fn],[.arg]] initial target ∧
      GuardedDegreeHistory (SelectedDegree initial selected) [[],[.fn],[.arg]] initial target ∧
      target.BarsFrom (SelectedDegree initial selected) ∧
      IsRedex target.erase := by
  obtain ⟨target,history,erased⟩ := lift_history real_duplicate_relative_development.general.betaHistory initial rfl
  have derived := relative_development_origin_guards (show INIT initial from init_is_INIT source)
    real_duplicate_relative_development history
  refine ⟨target,history,derived.1,derived.2,?_⟩
  rw [erased]
  trivial
theorem all_selected_payloads_are_original_atoms (degree : Label)
    (member : SelectedDegree initial selected degree) : IsAtomic degree :=
  member.atomic (init_is_INIT source)
/-- Atom support alone would permit this compound payload, although it is
neither permitted original degree. BarsFrom rejects that false strengthening. -/
theorem atom_support_does_not_imply_exact_payload_membership :
    ((Label.atom 1).concat (Label.atom 6)).over.BarsSafe (fun n => n=1 ∨ n=6) ∧
      ¬((Label.atom 1).concat (Label.atom 6)).over.BarsFrom
        (fun d => d=Label.atom 1 ∨ d=Label.atom 6) := by
  constructor
  · exact ⟨Or.inl rfl,Or.inr rfl⟩
  · intro safe
    rcases safe.1 with eq | eq <;> cases eq
/-- Even a permitted outer bar must check the bars nested INSIDE its payload. -/
theorem nested_payload_guard_is_not_omitted :
    ¬(Label.atom 2).over.over.BarsFrom (fun d => d=(Label.atom 2).over) := by
  intro safe
  have impossible := safe.2.1
  cases impossible
#print axioms DegreeAligned.relative_guarded
#print axioms relative_development_origin_guards
#print axioms SelectedDegree.atomic
#print axioms real_duplicate_relative_development
#print axioms actual_copied_development_uses_only_original_selected_degrees
#print axioms atom_support_does_not_imply_exact_payload_membership
#print axioms nested_payload_guard_is_not_omitted
end Lamping.Checks.DegreeFamily.P06SelectedOrigins

namespace Lamping.Checks.DegreeFamily.P06SelectedRoutes
open Lamping Lambda Labelled
private def ident : Term := .lam (.var 0)
private def source : Term := .app (.lam (.app (.var 0) (.var 0))) (.app ident ident)
private def original : LTerm := initLabels source
private def old : List Path := [[],[.arg]]
private def argument : Marked := .red [[.arg]] (.var 0) (.lam (.var 0))
private def markedEnd : Marked := .app [] (.lam (.var 0)) (.lam (.var 0))
private theorem actual_relative :
    Marked.RelativeHistory [[],[.fn],[.arg]] (Marked.mark old source) markedEnd :=
  .cons (.root [[]] (.app [] (.var 0) (.var 0)) argument)
    (.cons (.appL (.root [[.arg]] (.var 0) (.lam (.var 0))))
      (.cons (.appR (.root [[.arg]] (.var 0) (.lam (.var 0)))) (.nil _)))
theorem copied_relative_development_has_selected_routes :
    ∃ target,History [[],[.fn],[.arg]] original target ∧
      SelectedTermRoutes (sourceEdges [] .external original) (SelectedDegree original old) [] .external target := by
  obtain ⟨target,history,_⟩ := lift_history actual_relative.general.betaHistory original rfl
  exact ⟨target,history,relative_development_selected_routes (init_is_INIT source) actual_relative history⟩
private def captureTerm : Term := .app (.lam (.lam (.var 1))) (.var 0)
private def captureOriginal : LTerm := initLabels captureTerm
private def rootLabel : Label := ((Label.atom 0).concat (Label.atom 1).over).concat (Label.atom 2)
private def variableLabel : Label := ((Label.atom 3).concat (Label.atom 1).under).concat (Label.atom 4)
private def captureTarget : LTerm := .lam rootLabel (.var variableLabel 1)
private theorem captureRelative : Marked.RelativeHistory [[]]
    (Marked.mark [[]] captureTerm) (.lam (.var 1)) :=
  .cons (.root [[]] (.lam (.var 1)) (.var 0)) (.nil _)
private theorem captureHistory : History [[]] captureOriginal captureTarget := .cons (.root _ _ _ _) (.nil _)
/-- The top theorem supplies real original-source ports: the surviving lambda
origin is atom2 (not its compound current label), and captured var1 still
reaches free0 in the old graph rather than that lambda's binding port. -/
theorem selected_capture_preserves_original_binder_and_free_port :
    SelectedSourceRoute (sourceEdges [] .external captureOriginal) (SelectedDegree captureOriginal [[]])
      .external rootLabel (.lamContext (Label.atom 2)) ∧
    SelectedSourceRoute (sourceEdges [] .external captureOriginal) (SelectedDegree captureOriginal [[]])
      (.lamBody (Label.atom 2)) variableLabel (.free 0) := by
  have routes := relative_development_selected_routes (show INIT captureOriginal from init_is_INIT captureTerm)
    captureRelative captureHistory
  cases routes with
  | lam route bodyRoutes =>
    rename_i origin
    obtain ⟨n,edge,last,member,atomic,finish⟩ := route.forget.last_atom
    have sameAtom : 2=n := Option.some.inj last
    subst n
    have edgeSame := sourceEdges_unique (show INIT captureOriginal from init_is_INIT captureTerm) member
      (show (⟨Label.atom 2,.lamBody (Label.atom 1),.lamContext (Label.atom 2)⟩ : SourceEdge)∈
        sourceEdges [] .external captureOriginal from by decide) atomic
    rw [edgeSame] at finish
    have originSame : origin=Label.atom 2 := (SourcePort.lamContext.inj finish).symm
    subst origin
    cases bodyRoutes with
    | var variableRoute => exact ⟨route,variableRoute⟩
theorem current_compound_lambda_is_not_original_origin : rootLabel≠Label.atom 2 := by decide
#print axioms relative_development_selected_routes
#print axioms SourceRoute.selected
#print axioms copied_relative_development_has_selected_routes
#print axioms selected_capture_preserves_original_binder_and_free_port
#print axioms current_compound_lambda_is_not_original_origin
/-- Empty selection really uses the reflexive old-history on the same
original source, rather than assuming every graph shortcut is inaccessible. -/
theorem empty_selection_has_actual_reflexive_routes :
    SelectedTermRoutes (sourceEdges [] .external captureOriginal) (SelectedDegree captureOriginal [])
      [] .external captureOriginal :=
  relative_development_selected_routes (init_is_INIT captureTerm) (.nil _) (.nil _)
theorem empty_guard_cannot_reuse_the_created_compound_route :
    ¬SelectedSourceRoute (sourceEdges [] .external captureOriginal) (SelectedDegree captureOriginal [])
      .external rootLabel (.lamContext (Label.atom 2)) := by
  intro route
  have atomic := route.atomic_of_no_insertions (by intro degree; rintro ⟨name,member,_⟩; cases member)
  obtain ⟨n,impossible⟩ := atomic
  cases impossible
#print axioms empty_selection_has_actual_reflexive_routes
#print axioms empty_guard_cannot_reuse_the_created_compound_route
end Lamping.Checks.DegreeFamily.P06SelectedRoutes


namespace Lamping.Checks.DegreeFamily.P06SourceBinders
open Lamping Lambda Labelled
private def sharedLabel : Label := Label.atom 7
private def variableLabel : Label := Label.atom 8
private def outerBound : LTerm := .lam sharedLabel (.lam sharedLabel (.var variableLabel 1))
private def innerBound : LTerm := .lam sharedLabel (.lam sharedLabel (.var variableLabel 0))
private theorem outerSite : SourceSubterm [] .external outerBound [.body,.body]
    [sharedLabel,sharedLabel] (.lamBody sharedLabel) (.var variableLabel 1) := .body (.body .nil)
private theorem innerSite : SourceSubterm [] .external innerBound [.body,.body]
    [sharedLabel,sharedLabel] (.lamBody sharedLabel) (.var variableLabel 0) := .body (.body .nil)
/-- Both lambda labels are deliberately identical. Index 1 still selects the
actual outer occurrence, even though the inner lambda has the same origin label. -/
theorem repeated_origin_label_outer_occurrence :
    ∃ parent tail body,parent=[] ∧ tail=[.body] ∧
      outerBound.subterm parent=some (.lam sharedLabel body) ∧
      [.body,.body]=parent++(.body::tail) ∧ 1=binderDepth tail := by
  obtain ⟨parent,tail,body,split,lookup,depth⟩ := outerSite.sourceBinder_occurrence (index := 1) (origin := sharedLabel) rfl
  have unique := binding_prefix_depth_unique (show parent++(.body::tail)=[]++[.body,.body] from split.symm)
    (show binderDepth tail=binderDepth [.body] from depth.symm)
  exact ⟨parent,tail,body,unique.1,unique.2,lookup,split,depth⟩
/-- Index 0 shadows the outer same-labelled lambda and selects the inner one. -/
theorem repeated_origin_label_inner_shadow :
    ∃ parent tail body,parent=[.body] ∧ tail=[] ∧
      innerBound.subterm parent=some (.lam sharedLabel body) ∧
      [.body,.body]=parent++(.body::tail) ∧ 0=binderDepth tail := by
  obtain ⟨parent,tail,body,split,lookup,depth⟩ := innerSite.sourceBinder_occurrence (index := 0) (origin := sharedLabel) rfl
  have unique := binding_prefix_depth_unique
    (show parent++(.body::tail)=[.body]++[.body] from split.symm)
    (show binderDepth tail=binderDepth [] from depth.symm)
  exact ⟨parent,tail,body,unique.1,unique.2,lookup,split,depth⟩
/-- In a general incoming environment, the entry may genuinely be external
to this subterm; it must not be fabricated as a lambda ancestor inside it. -/
theorem incoming_environment_remains_outside :
    ∃ j,1=j+binderDepth [.body] ∧ [Label.atom 1][j]?=some (Label.atom 1) := by
  have site : SourceSubterm [Label.atom 1] .external
      (.lam (Label.atom 2) (.var variableLabel 1)) [.body]
      [Label.atom 2,Label.atom 1] (.lamBody (Label.atom 2)) (.var variableLabel 1) := .body .nil
  rcases site.binder_origin (show [Label.atom 2,Label.atom 1][1]?=some (Label.atom 1) from rfl) with
    ⟨parent,tail,body,split,_,depth⟩ | outside
  · have nonempty : tail≠[] := by intro empty; rw [empty] at depth; cases depth
    have positive := List.length_pos_iff.mpr nonempty
    have lengths := congrArg List.length split
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  · exact outside
/-- A capture-shifted var1 below one lambda is free0 relative to the original
empty environment; equal lambda kind/label is not enough to call it bound. -/
theorem capture_free_port_is_not_a_bound_port :
    sourceBinder [sharedLabel] 1=.free 0 ∧ sourceBinder [sharedLabel] 1≠.lamBind sharedLabel := by
  exact ⟨rfl,by decide⟩
theorem same_label_cannot_select_the_wrong_inner_occurrence :
    outerBound.subterm []=some (.lam sharedLabel (.lam sharedLabel (.var variableLabel 1))) ∧
      outerBound.subterm [.body]=some (.lam sharedLabel (.var variableLabel 1)) ∧
      ¬(1=binderDepth ([] : Path)) := by exact ⟨rfl,rfl,by decide⟩
/-- Exact depth identifies the same body-prefix even across fn/arg turns. -/
theorem two_literal_decompositions_identify_one_occurrence (parent tail : Path)
    (word : [.body,.fn,.body,.arg]=parent++(.body::tail))
    (depth : binderDepth tail=1) : parent=[] ∧ tail=[.fn,.body,.arg] :=
  binding_prefix_depth_unique word.symm depth
#print axioms SourceSubterm.binder_origin
#print axioms SourceSubterm.sourceBinder_occurrence
#print axioms binding_prefix_depth_unique
#print axioms repeated_origin_label_outer_occurrence
#print axioms repeated_origin_label_inner_shadow
#print axioms incoming_environment_remains_outside
#print axioms capture_free_port_is_not_a_bound_port
#print axioms same_label_cannot_select_the_wrong_inner_occurrence
#print axioms two_literal_decompositions_identify_one_occurrence
end Lamping.Checks.DegreeFamily.P06SourceBinders


namespace Lamping.Checks.DegreeFamily.P06PhysicalSourceBinders
open Lamping Lambda Lambda.Labelled AG Graph
private def shared : Label := Label.atom 7
private def tag : Label := Label.atom 8
private def outerSource : LTerm := .lam shared (.lam shared (.var tag 1))
private def innerSource : LTerm := .lam shared (.lam shared (.var tag 0))
/-- This fixture result retains the real original assignments and physical
lambda-context incidence, not merely equality of source labels or node kind. -/
private def ActualBinderWitness (original : LTerm) (origin : Label) (expected : Path) (index : Nat) : Prop :=
  ∃ (access parent : RootAccess (encode 7 original.erase).net (.inl ()))
    (loop : List (Endpoint (encode 7 original.erase).net)) (a b c : Context)
    (binding : BindingLoop (encode 7 original.erase).net loop b c)
    (ctx : Port ((encode 7 original.erase).net.label binding.binder).sort) (body : LTerm),
    accessWord (encode 7 original.erase).net access.val=[.body,.body] ∧
    accessWord (encode 7 original.erase).net parent.val=expected ∧
    original.subterm (accessWord (encode 7 original.erase).net parent.val)=some (.lam origin body) ∧
    access.val=parent.val++loop ∧ HEq ctx (Sum.inl () : Port (.op .lam)) ∧
    parent.val.getLast?=some ((encode 7 original.erase).net.wire (.inl ⟨binding.binder,ctx⟩)) ∧
    Labelling (encode 7 original.erase).net parent.val a b ∧ index=binderDepth (accessWord (encode 7 original.erase).net loop)
private theorem actual_two_lambda_binder (original : LTerm) (closed : Closed original.erase)
    (site : SourceSubterm [] .external original [.body,.body] env atPort (.var varLabel index))
    (bound : sourceBinder env index=.lamBind origin)
    (decomposition : [.body,.body]=expected++(.body::suffix)) (depth : index=binderDepth suffix) :
    ActualBinderWitness original origin expected index := by
  have lookup : subtermAt original.erase [.body,.body]=some (.var index) := by
    rw [←LTerm.erase_subterm,site.lookup]; rfl
  have matching := encode_closed_matches original.erase closed 7
  obtain ⟨access,word,_⟩ := Matches.observation (encode 7 original.erase).net matching
    (⟨[.body,.body],by rw [lookup]; rfl⟩ : Position original.erase)
  obtain ⟨parent,loop,a,b,c,binding,ctx,body,split,role,finish,labels,atBinder,words,actualDepth⟩ :=
    matching.original_source_binder site bound access word
  have unique := binding_prefix_depth_unique (words.symm.trans decomposition) (actualDepth.symm.trans depth)
  exact ⟨access,parent,loop,a,b,c,binding,ctx,body,word,unique.1,atBinder,split,role,finish,labels,actualDepth⟩
/-- A real closed encode7 source has repeated lambda labels in the separate
syntax labelling, but var1 chooses the physical outer lambda root access. -/
theorem actual_repeated_label_outer : ActualBinderWitness outerSource shared [] 1 :=
  actual_two_lambda_binder outerSource (by change 1<2; decide)
    (show SourceSubterm [] .external outerSource [.body,.body] [shared,shared] (.lamBody shared) (.var tag 1) from .body (.body .nil))
    rfl rfl rfl
/-- Var0 in the corresponding closed syntax chooses the inner physical
lambda access, despite exactly the same repeated static origin labels. -/
theorem actual_repeated_label_inner : ActualBinderWitness innerSource shared [.body] 0 :=
  actual_two_lambda_binder innerSource (by change 0<2; decide)
    (show SourceSubterm [] .external innerSource [.body,.body] [shared,shared] (.lamBody shared) (.var tag 0) from .body (.body .nil))
    rfl rfl rfl
private def captureBefore : LTerm := .lam (Label.atom 50)
  (.app (Label.atom 0) (.lam (Label.atom 1) (.lam (Label.atom 2) (.var (Label.atom 3) 2))) (.var (Label.atom 4) 0))
private def currentInner : Label := ((Label.atom 0).concat (Label.atom 1).over).concat (Label.atom 2)
private def captureAfter : LTerm := .lam (Label.atom 50) (.lam currentInner (.var (Label.atom 3) 1))
/-- An actual capture-avoiding beta changes var2 to var1. The independently
encoded closed target syntax still locates that variable's physical OUTER
binder; this does not assert graph-rewrite target Matches. -/
theorem actual_capture_shift_then_physical_original_binder :
    StepAt [.body] captureBefore captureAfter ∧ ActualBinderWitness captureAfter (Label.atom 50) [] 1 := by
  refine ⟨.body (.root _ _ _ _),?_⟩
  exact actual_two_lambda_binder captureAfter (by change 1<2; decide)
    (show SourceSubterm [] .external captureAfter [.body,.body] [currentInner,Label.atom 50]
      (.lamBody currentInner) (.var (Label.atom 3) 1) from .body (.body .nil)) rfl rfl rfl
theorem repeated_static_labels_do_not_supply_INIT : ¬INIT outerSource := by
  intro initial
  exact (by decide : ¬outerSource.labels.Nodup) initial.2
theorem same_origin_cannot_change_literal_prefix_depth :
    ¬([.body,.body]=[.body]++(.body::([] : Path)) ∧ (1=binderDepth ([] : Path))) := by decide
#print axioms Matches.original_source_binder
#print axioms actual_repeated_label_outer
#print axioms actual_repeated_label_inner
#print axioms actual_capture_shift_then_physical_original_binder
#print axioms repeated_static_labels_do_not_supply_INIT
#print axioms same_origin_cannot_change_literal_prefix_depth
end Lamping.Checks.DegreeFamily.P06PhysicalSourceBinders

namespace Lamping.Checks.DegreeFamily.P06SourceEdges
open Lamping Lambda AG Graph
private def ident : Term := .lam (.var 0)
private def deep : Term := .lam (.app ident ident)
/-- The general Matches-only prefix theorem cuts a genuine three-token
access at the original root, without constructing another path. -/
theorem actual_multistep_syntax_prefix_is_literal :
    ∃ (parent child : RootAccess (encode 7 deep).net (.inl ())) (tail : List (Endpoint (encode 7 deep).net)),
      accessWord (encode 7 deep).net parent.val=[] ∧
      accessWord (encode 7 deep).net child.val=[.body,.fn,.body] ∧
      child.val=parent.val++tail ∧ tail≠[] := by
  have matching := encode_closed_matches deep (by change (0<2) ∧ 0<2; decide) 7
  obtain ⟨parent,parentWord,_⟩ := Matches.observation (encode 7 deep).net matching (⟨[],rfl⟩ : Position deep)
  obtain ⟨child,childWord,_⟩ := Matches.observation (encode 7 deep).net matching (⟨[.body,.fn,.body],rfl⟩ : Position deep)
  obtain ⟨tail,split⟩ := matching.access_prefix parent child [.body,.fn,.body]
    (by rw [parentWord,childWord]; rfl)
  refine ⟨parent,child,tail,parentWord,childWord,split,?_⟩
  intro empty
  rw [empty,List.append_nil] at split
  have same := congrArg (accessWord (encode 7 deep).net) split
  rw [parentWord,childWord] at same
  cases same
private def sharing : Term := .lam (.app (.var 0) (.var 0))
private def ActualChildFragment (step : Step) : Prop :=
  ∃ (parent child : RootAccess (encode 7 sharing).net (.inl ()))
    (node : (encode 7 sharing).N) (ctx departure : Port ((encode 7 sharing).net.label node).sort)
    (tail : List (Endpoint (encode 7 sharing).net)) (a middle b : Context),
    accessWord (encode 7 sharing).net parent.val=[.body] ∧
    accessWord (encode 7 sharing).net child.val=[.body,step] ∧
    SyntaxChildPorts ((encode 7 sharing).net.label node).sort ctx departure step ∧
    parent.val.getLast?=some ((encode 7 sharing).net.wire (.inl ⟨node,ctx⟩)) ∧
    child.val=parent.val++(.inl ⟨node,departure⟩)::tail ∧
    Forward (encode 7 sharing).net ((.inl ⟨node,departure⟩)::tail) ∧
    Labelling (encode 7 sharing).net child.val a b ∧
    Labelling (encode 7 sharing).net parent.val a middle ∧
    Labelling (encode 7 sharing).net ((.inl ⟨node,departure⟩)::tail) middle b
private theorem sharing_child_fragment (step : Step) (selected : step=.fn ∨ step=.arg) : ActualChildFragment step := by
  have matching := encode_closed_matches sharing (by change (0<1) ∧ 0<1; decide) 7
  obtain ⟨parent,parentWord,_⟩ := Matches.observation (encode 7 sharing).net matching (⟨[.body],rfl⟩ : Position sharing)
  let childPosition : Position sharing := ⟨[.body,step],by rcases selected with rfl | rfl <;> rfl⟩
  obtain ⟨child,childWord,_⟩ := Matches.observation (encode 7 sharing).net matching childPosition
  have word : accessWord (encode 7 sharing).net child.val=[.body,step] := childWord
  obtain ⟨node,ctx,departure,tail,roles,finish,split,forward,allAssignments⟩ :=
    matching.syntax_child_fragment parent child step (by rw [parentWord,word]; rfl)
  obtain ⟨a,b,whole⟩ := child.property.1.1
  obtain ⟨middle,before,after⟩ := allAssignments a b whole
  exact ⟨parent,child,node,ctx,departure,tail,a,middle,b,parentWord,word,roles,finish,split,forward,whole,before,after⟩
/-- Both fan-sharing variable branches use their actual original whole
assignment and preserve the exact parent/fragment context at the seam. -/
theorem actual_function_fragment_preserves_original_assignment : ActualChildFragment .fn := sharing_child_fragment .fn (Or.inl rfl)
theorem actual_argument_fragment_preserves_original_assignment : ActualChildFragment .arg := sharing_child_fragment .arg (Or.inr rfl)
theorem context_binding_port_is_not_a_syntax_child :
    ¬SyntaxChildPorts (.op .lam) (Sum.inl ()) lamBind .body := by intro roles; cases roles
#print axioms Matches.access_prefix
#print axioms Matches.syntax_child_fragment
#print axioms actual_multistep_syntax_prefix_is_literal
#print axioms actual_function_fragment_preserves_original_assignment
#print axioms actual_argument_fragment_preserves_original_assignment
#print axioms context_binding_port_is_not_a_syntax_child
end Lamping.Checks.DegreeFamily.P06SourceEdges


namespace Lamping.Checks.DegreeFamily.P06BaseSourceEdges
open Lamping Lambda Lambda.Labelled AG Graph
private def term : Term := .lam (.app (.var 0) (.var 0))
private def original : LTerm := initLabels term
private def body : LTerm := .app (Labelled.Label.atom 1) (.var (Labelled.Label.atom 2) 0) (.var (Labelled.Label.atom 3) 0)
private def rootEdge : SourceEdge := ⟨Labelled.Label.atom 0,.external,.lamContext (Labelled.Label.atom 0)⟩
private def bodyEdge : SourceEdge := ⟨Labelled.Label.atom 1,.lamBody (Labelled.Label.atom 0),.appContext (Labelled.Label.atom 1)⟩
private def fnEdge : SourceEdge := ⟨Labelled.Label.atom 2,.appFn (Labelled.Label.atom 1),.lamBind (Labelled.Label.atom 0)⟩
private def argEdge : SourceEdge := ⟨Labelled.Label.atom 3,.appArg (Labelled.Label.atom 1),.lamBind (Labelled.Label.atom 0)⟩
private theorem closed : Closed original.erase := by change (0<1) ∧ 0<1; decide
private theorem matching : Matches (encode 7 term).net (.inl ()) original.erase := encode_closed_matches term closed 7

theorem actual_root_edge : Nonempty (SourceEdgeFragment original (encode 7 term).net (.inl ()) rootEdge []) :=
  matching.base_source_edge_fragment closed (show SourceSubterm [] .external original [] [] .external original from .nil)
theorem actual_body_edge : Nonempty (SourceEdgeFragment original (encode 7 term).net (.inl ()) bodyEdge [.body]) :=
  matching.base_source_edge_fragment closed
    (show SourceSubterm [] .external original [.body] [Labelled.Label.atom 0] (.lamBody (Labelled.Label.atom 0)) body from .body .nil)
theorem actual_function_binding_edge : Nonempty (SourceEdgeFragment original (encode 7 term).net (.inl ()) fnEdge [.body,.fn]) :=
  matching.base_source_edge_fragment closed
    (show SourceSubterm [] .external original [.body,.fn] [Labelled.Label.atom 0] (.appFn (Labelled.Label.atom 1)) (.var (Labelled.Label.atom 2) 0) from .body (.fn .nil))
theorem actual_argument_binding_edge : Nonempty (SourceEdgeFragment original (encode 7 term).net (.inl ()) argEdge [.body,.arg]) :=
  matching.base_source_edge_fragment closed
    (show SourceSubterm [] .external original [.body,.arg] [Labelled.Label.atom 0] (.appArg (Labelled.Label.atom 1)) (.var (Labelled.Label.atom 3) 0) from .body (.arg .nil))
private def PhysicalRootBinding (terminal : Endpoint (encode 7 term).net) : Prop :=
  ∃ (node : (encode 7 term).N) (ctx binding : Port ((encode 7 term).net.label node).sort)
    (parent : RootAccess (encode 7 term).net (.inl ())),
    accessWord (encode 7 term).net parent.val=[] ∧
    ((encode 7 term).net.label node).sort=.op .lam ∧
    HEq ctx (Sum.inl () : Port (.op .lam)) ∧ HEq binding lamBind ∧
    parent.val.getLast?=some ((encode 7 term).net.wire (.inl ⟨node,ctx⟩)) ∧ terminal=.inl ⟨node,binding⟩
/-- The variable edge terminates at the binding port of the original ROOT
lambda occurrence, rather than merely some same-kind lambda node. -/
theorem actual_variable_edge_recovers_physical_root_binder :
    ∃ fragment : SourceEdgeFragment original (encode 7 term).net (.inl ()) fnEdge [.body,.fn],
      PhysicalRootBinding fragment.toEndpoint := by
  obtain ⟨fragment⟩ := actual_function_binding_edge
  refine ⟨fragment,?_⟩
  have realizes := fragment.toRealizes
  generalize terminalEq : fragment.toEndpoint=terminal
  rw [terminalEq] at realizes
  cases realizes with
  | departure _ role _ _ _ _ => cases role
  | binding lookup parent word shape contextRole bindingRole finish =>
    have oldRoot := LTerm.subterm_label_injective original (init_is_INIT term).2 lookup
      (show original.subterm []=some original from rfl) rfl
    exact ⟨_,_,_,parent,word.trans oldRoot,shape,contextRole,bindingRole,finish,rfl⟩
/-- Forward and reversed edge segments retain the actual whole source
assignment. Reversal swaps contexts/endpoints without dropping wire vertices. -/
theorem actual_binding_fragment_reversal_keeps_assignment :
    ∃ (fragment : SourceEdgeFragment original (encode 7 term).net (.inl ()) fnEdge [.body,.fn]) (a b middle : Context),
      Labelling (encode 7 term).net fragment.access.val a b ∧
      (fragment.before=[] ∧ middle=a ∨ Labelling (encode 7 term).net fragment.before a middle) ∧
      Labelling (encode 7 term).net fragment.segments middle b ∧
      Labelling (encode 7 term).net (reverseEdges fragment.segments) b middle ∧
      accessWord (encode 7 term).net fragment.segments=[] ∧
      (reverseEdges fragment.segments).head?=some fragment.toEndpoint ∧
      (reverseEdges fragment.segments).getLast?=some ((encode 7 term).net.wire fragment.fromEndpoint) := by
  obtain ⟨fragment⟩ := actual_function_binding_edge
  obtain ⟨a,b,whole⟩ := fragment.access.property.1.1
  obtain ⟨middle,before,after⟩ := fragment.assignments a b whole
  exact ⟨fragment,a,b,middle,whole,before,after,after.reverse,fragment.emptyWord,fragment.reverse_endpoints⟩
theorem binding_port_cannot_be_a_lambda_context : lamBind≠(Sum.inl () : Port (.op .lam)) := by intro impossible; cases impossible
#print axioms Matches.source_edge_terminal
#print axioms Matches.base_source_edge_fragment
#print axioms SourceEdgeFragment.reverse_endpoints
#print axioms SourceEdgeFragment.reverse_assignment
#print axioms actual_root_edge
#print axioms actual_body_edge
#print axioms actual_function_binding_edge
#print axioms actual_argument_binding_edge
#print axioms actual_variable_edge_recovers_physical_root_binder
#print axioms actual_binding_fragment_reversal_keeps_assignment
#print axioms binding_port_cannot_be_a_lambda_context
private def identity : Term := .lam (.var 0)
private def betaTerm : Term := .app identity identity
private def betaOriginal : LTerm := initLabels betaTerm
private def principalEdge : SourceEdge :=
  ⟨Labelled.Label.atom 1,.appFn (Labelled.Label.atom 0),.lamContext (Labelled.Label.atom 1)⟩
/-- The old redex's actual function/lambda edge is also realized; this is
still a source edge, before any claim that it equals a chosen graph-site route. -/
theorem actual_old_redex_function_edge :
    Nonempty (SourceEdgeFragment betaOriginal (encode 7 betaTerm).net (.inl ()) principalEdge [.fn]) := by
  have scope : Closed betaOriginal.erase := by change (0<1) ∧ 0<1; decide
  have sourceMatches : Matches (encode 7 betaTerm).net (.inl ()) betaOriginal.erase := encode_closed_matches betaTerm scope 7
  exact sourceMatches.base_source_edge_fragment scope
    (show SourceSubterm [] .external betaOriginal [.fn] [] (.appFn (Labelled.Label.atom 0))
      (.lam (Labelled.Label.atom 1) (.var (Labelled.Label.atom 2) 0)) from .fn .nil)
#print axioms actual_old_redex_function_edge
/-- This consumes actual original-edge membership directly, matching the
SourceRoute atom constructor rather than presupposing an occurrence witness. -/
theorem actual_listed_edge_has_physical_fragment :
    ∃ p,Nonempty (SourceEdgeFragment original (encode 7 term).net (.inl ()) fnEdge p) :=
  matching.source_edge_member_fragment closed (by decide)
#print axioms Matches.source_edge_member_fragment
#print axioms actual_listed_edge_has_physical_fragment
end Lamping.Checks.DegreeFamily.P06BaseSourceEdges





namespace Lamping.Checks.DegreeFamily.P06SourcePortUniqueness
open Lamping Lambda Lambda.Labelled AG Graph
private def term : Term := .lam (.app (.var 0) (.var 0))
private def original : LTerm := initLabels term
private theorem matching : Matches (encode 7 term).net (.inl ()) original.erase :=
  encode_closed_matches term (by change (0<1) ∧ 0<1; decide) 7
/-- Two independently realized variable edges share the original root binder. -/
theorem actual_shared_binding_endpoint :
    ∃ (left right : SourceEdgeFragment original (encode 7 term).net (.inl ())
      ⟨Labelled.Label.atom 2,.appFn (Labelled.Label.atom 1),.lamBind (Labelled.Label.atom 0)⟩ [.body,.fn])
      (arg : SourceEdgeFragment original (encode 7 term).net (.inl ())
      ⟨Labelled.Label.atom 3,.appArg (Labelled.Label.atom 1),.lamBind (Labelled.Label.atom 0)⟩ [.body,.arg]),
      left.fromEndpoint=right.fromEndpoint ∧ left.toEndpoint=arg.toEndpoint := by
  have closed : Closed original.erase := by change (0<1) ∧ 0<1; decide
  obtain ⟨left⟩ := matching.base_source_edge_fragment closed
    (show SourceSubterm [] .external original [.body,.fn] [Labelled.Label.atom 0]
      (.appFn (Labelled.Label.atom 1)) (.var (Labelled.Label.atom 2) 0) from .body (.fn .nil))
  obtain ⟨right⟩ := matching.base_source_edge_fragment closed
    (show SourceSubterm [] .external original [.body,.fn] [Labelled.Label.atom 0]
      (.appFn (Labelled.Label.atom 1)) (.var (Labelled.Label.atom 2) 0) from .body (.fn .nil))
  obtain ⟨arg⟩ := matching.base_source_edge_fragment closed
    (show SourceSubterm [] .external original [.body,.arg] [Labelled.Label.atom 0]
      (.appArg (Labelled.Label.atom 1)) (.var (Labelled.Label.atom 3) 0) from .body (.arg .nil))
  exact ⟨left,right,arg,left.fromRealizes.unique (init_is_INIT term) matching right.fromRealizes,
    left.toRealizes.unique (init_is_INIT term) matching arg.toRealizes⟩
private def repeated : LTerm := .lam (Labelled.Label.atom 7)
  (.lam (Labelled.Label.atom 7) (.var (Labelled.Label.atom 8) 1))
/-- Without INIT, the very same static lambda port has two different actual
physical realizations in one closed encoded graph. -/
theorem repeated_label_is_not_a_physical_port_map :
    ∃ e f,SourcePortRealizes repeated (encode 7 repeated.erase).net (.inl ())
      (.lamContext (Labelled.Label.atom 7)) e ∧
      SourcePortRealizes repeated (encode 7 repeated.erase).net (.inl ())
      (.lamContext (Labelled.Label.atom 7)) f ∧ e≠f := by
  have sourceMatches := encode_closed_matches repeated.erase (by change 1<2; decide) 7
  obtain ⟨a,ha,oa⟩ := Matches.observation (encode 7 repeated.erase).net sourceMatches
    (⟨[],rfl⟩ : Position repeated.erase)
  obtain ⟨b,hb,ob⟩ := Matches.observation (encode 7 repeated.erase).net sourceMatches
    (⟨[.body],rfl⟩ : Position repeated.erase)
  obtain ⟨u,lookupA,oa⟩ := oa
  change some repeated.erase=some u at lookupA
  cases lookupA
  obtain ⟨v,lookupB,ob⟩ := ob
  change some (.lam (.var 1))=some v at lookupB
  cases lookupB
  obtain ⟨n,p,i,lab,role,finish⟩ := a.lambda_endpoint oa.1
  obtain ⟨m,q,j,lab',role',finish'⟩ := b.lambda_endpoint ob.1
  refine ⟨.inl ⟨n,p⟩,.inl ⟨m,q⟩,
    .lamContext rfl a ha (congrArg (fun l => l.sort) lab) role finish,
    .lamContext rfl b hb (congrArg (fun l => l.sort) lab') role' finish',?_⟩
  intro equal
  have common : b.val.getLast?=some ((encode 7 repeated.erase).net.wire (.inl ⟨n,p⟩)) := by
    rw [equal]; exact finish'
  have target : AtProperRole (encode 7 repeated.erase).net (.inl ())
      ((encode 7 repeated.erase).net.wire ((encode 7 repeated.erase).net.wire (.inl ⟨n,p⟩))) .lamCtx i := by
    simpa only [Pairing.involutive] using (AtProperRole.lamCtx n p i lab role)
  have accesses := encode_context_access_unique repeated.erase 7 a b _ finish common .lamCtx i (Or.inr rfl) target
  have impossible := ha.symm.trans ((congrArg (fun access : RootAccess (encode 7 repeated.erase).net (.inl ()) =>
    accessWord (encode 7 repeated.erase).net access.val) accesses).trans hb)
  cases impossible
#print axioms SourcePortRealizes.unique
#print axioms actual_shared_binding_endpoint
#print axioms repeated_label_is_not_a_physical_port_map
end Lamping.Checks.DegreeFamily.P06SourcePortUniqueness


namespace Lamping.Checks.DegreeFamily.P06BetaPrincipalPath
open Lamping AG Graph Lambda
private def labels : Bool → Label signature
  | false => label .app 3
  | true => label .lam 3
private def twoW : Net signature Bool (Bool⊕Bool) Bool where
  label := labels
  wire := {
    mate := fun e => match e with
      | .inl ⟨false,.inl _⟩ => .inr (.inr (false,false))
      | .inl ⟨true,.inl _⟩ => .inr (.inr (true,true))
      | .inl ⟨false,.inr d⟩ => .inr (.inl (.inl d))
      | .inl ⟨true,.inr d⟩ => .inr (.inl (.inr d))
      | .inr (.inl (.inl d)) => .inl ⟨false,.inr d⟩
      | .inr (.inl (.inr d)) => .inl ⟨true,.inr d⟩
      | .inr (.inr (false,false)) => .inl ⟨false,.inl ()⟩
      | .inr (.inr (false,true)) => .inr (.inr (true,false))
      | .inr (.inr (true,false)) => .inr (.inr (false,true))
      | .inr (.inr (true,true)) => .inl ⟨true,.inl ()⟩
    involutive := by
      rintro (⟨node,p⟩ | ((d|d) | ⟨v,d⟩))
      · cases node <;> cases p <;> rfl
      · rfl
      · rfl
      · cases v <;> cases d <;> rfl
    fixedPointFree := by
      rintro (⟨node,p⟩ | ((d|d) | ⟨v,d⟩)) equal
      · cases node <;> cases p <;> cases equal
      · cases equal
      · cases equal
      · cases v <;> cases d <;> cases equal }
private def beta : BetaEdge twoW where
  app := false
  lam := true
  index := 3
  appLabel := rfl
  lamLabel := rfl
  appFun := .inl ()
  appCtx := .inr false
  appArg := .inr true
  lamCtx := .inl ()
  lamBody := .inr true
  lamBind := .inr false
  appFun_role := HEq.rfl
  appCtx_role := HEq.rfl
  appArg_role := HEq.rfl
  lamCtx_role := HEq.rfl
  lamBody_role := HEq.rfl
  lamBind_role := HEq.rfl
  principal := [.inl ⟨false,.inl ()⟩,.inr (.inr (false,true)),.inr (.inr (true,true))]
  principalStart := rfl
  principalEnd := rfl
  transparent := by
    intro e f pair
    change (e,f)∈[(.inl ⟨false,.inl ()⟩,.inr (.inr (false,true))),
      (.inr (.inr (false,true)),.inr (.inr (true,true)))] at pair
    rcases List.mem_cons.mp pair with equal | last
    · cases equal; exact ⟨false,false,rfl,rfl⟩
    · have equal := List.mem_singleton.mp last
      cases equal; exact ⟨true,false,rfl,rfl⟩
private def connection : RedexConnection twoW where
  app := false
  lam := true
  appPort := .inl ()
  lamPort := .inl ()
  appIndex := 3
  lamIndex := 3
  appLabel := rfl
  lamLabel := rfl
  appPrincipal := HEq.rfl
  lamPrincipal := HEq.rfl
  edges := beta.principal
  proper := ⟨⟨Context.empty,Context.empty,beta.principal_labeling _⟩,beta.principal_forward⟩
  start := rfl
  finish := rfl
  emptyWord := rfl
/-- The actual two-W connection consumes the new literal-route theorem. -/
theorem actual_two_w_connection : connection.edges=beta.principal :=
  connection.beta_principal_unique beta rfl rfl
/-- Every genuine finite candidate with this physical pair has exactly all
three departures, without an input simplicity/no-repetition certificate. -/
theorem any_actual_two_w_candidate (candidate : RedexConnection twoW)
    (app : candidate.app=false) (lam : candidate.lam=true) :
    candidate.edges=[.inl ⟨false,.inl ()⟩,.inr (.inr (false,true)),.inr (.inr (true,true))] :=
  candidate.beta_principal_unique beta app lam
/-- Stopping after the first transparent vertex is not a principal route. -/
theorem truncated_two_w_is_not_finished :
    ([.inl ⟨false,.inl ()⟩,.inr (.inr (false,true))] : List (Endpoint twoW)).getLast?≠
      some (twoW.wire (.inl ⟨true,.inl ()⟩)) := by intro equal; cases equal
/-- Continuing at the final lambda cannot satisfy the actual control-only
condition, even though ordinary forward lambda/body traversal is meaningful. -/
theorem lambda_continuation_is_not_control_only :
    ¬ControlOnlyTurn (g:=twoW) (.inr (.inr (true,true))) (.inl ⟨true,.inr true⟩) := by
  rintro (⟨w,d,entry,exit⟩ | ⟨node,p,q,op,shape,control,entry,exit⟩)
  · cases entry
  · have nodes : true=node := congrArg Sigma.fst (Sum.inl.inj entry)
    subst node
    have equal : Op.lam=op := Kind.op.inj shape
    subst op
    rcases control with impossible | impossible | impossible <;> cases impossible
#print axioms RedexConnection.beta_principal_unique
#print axioms PathSite.distinguished_betaEdge_exists
#print axioms PathSite.beta_fiber_principal
#print axioms actual_two_w_connection
#print axioms any_actual_two_w_candidate
#print axioms truncated_two_w_is_not_finished
#print axioms lambda_continuation_is_not_control_only
end Lamping.Checks.DegreeFamily.P06BetaPrincipalPath

namespace Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
open Lamping Lambda Lambda.Labelled AG Graph
private def original : LTerm := initLabels identityApp
private def redex : RedexOcc original.erase := ⟨[],⟨_,rfl,True.intro⟩⟩
private def parent : RootAccess actualBetaSite.net (.inl ()) :=
  ⟨[.inr (.inl (.inl ()))],⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,rfl,⟨.app,rfl⟩⟩⟩
private def childEdges : List (Endpoint actualBetaSite.net) :=
  [.inr (.inl (.inl ())),.inl ⟨.inr (.inl ()),.inl ()⟩,.inr (.inr (.inr (),true))]
private theorem childLabels : Labelling actualBetaSite.net childEdges Context.empty Context.empty :=
  Labelling.cons (g:=actualBetaSite.net) (LabelledTurn.node (g:=actualBetaSite.net) (.inr (.inl ())) appCtx (Sum.inl ()) (.direct (.appFun _)))
    (Paths.encodedBetaOccurrence.principal_labeling _)
private theorem childForward : Forward actualBetaSite.net childEdges :=
  .node (.inr (.inl ())) appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩ Paths.encodedBetaOccurrence.principal_forward
private def child : RootAccess actualBetaSite.net (.inl ()) :=
  ⟨childEdges,⟨⟨⟨Context.empty,Context.empty,childLabels⟩,childForward⟩,rfl,⟨.lam,rfl⟩⟩⟩
private def connection : RedexConnection actualBetaSite.net where
  app := .inr (.inl ())
  lam := .inr (.inr ())
  appPort := .inl ()
  lamPort := .inl ()
  appIndex := 0
  lamIndex := 0
  appLabel := rfl
  lamLabel := rfl
  appPrincipal := HEq.rfl
  lamPrincipal := HEq.rfl
  edges := Paths.encodedBetaOccurrence.principal
  proper := ⟨⟨Context.empty,Context.empty,Paths.encodedBetaOccurrence.principal_labeling _⟩,
    Paths.encodedBetaOccurrence.principal_forward⟩
  start := rfl
  finish := rfl
  emptyWord := rfl
private def rich : ActualRedexAccess actualBetaSite.net (.inl ()) redex where
  connection := connection
  parent := parent
  child := child
  ctx := appCtx
  contextPrincipal := HEq.rfl
  parentWord := rfl
  childWord := rfl
  parentFinish := rfl
  split := rfl
private theorem matching : Matches actualBetaSite.net (.inl ()) original.erase :=
  betaEncodingIso.matches (encode_closed_matches identityApp (by change (0<1) ∧ 0<1; decide) 0)
private theorem member : []∈actualBetaSite.betaSyntaxFiber (.inl ()) original.erase :=
  (mem_physicalBetaFiberPaths _ _ _ _ _ _).mpr ⟨redex,rich,rfl,rfl,rfl⟩
/-- A real selected OLD degree is realized by the complete physical one-W
principal route, retaining its actual source access and original labels. -/
theorem actual_selected_degree_has_the_fixed_principal :
    ∃ appId body argument,
      original.subterm []=some (.app appId (.lam (Labelled.Label.atom 1) body) argument) ∧
      ∃ fragment : SourceEdgeFragment original actualBetaSite.net (.inl ())
        ⟨Labelled.Label.atom 1,.appFn appId,.lamContext (Labelled.Label.atom 1)⟩ [.fn],
        fragment.segments=Paths.encodedBetaOccurrence.principal ∧ fragment.segments.length=2 := by
  obtain ⟨beta,app,lam,allDegrees⟩ := actualBetaSite.selected_degree_principal_fragment matching
  obtain ⟨name,appId,body,argument,selected,lookup,fragment,segments⟩ :=
    allDegrees (Labelled.Label.atom 1) ⟨[],member,rfl⟩
  have sameName : name=[] := by
    have degreeAtName : original.degreeAt name=some (Labelled.Label.atom 1) := by
      simp only [LTerm.degreeAt,lookup]; rfl
    exact LTerm.initial_degree_injective (init_is_INIT identityApp) degreeAtName rfl
  subst name
  have principal := connection.beta_principal_unique beta app.symm lam.symm
  have actual : fragment.segments=Paths.encodedBetaOccurrence.principal := segments.trans principal.symm
  exact ⟨appId,body,argument,lookup,fragment,actual,by rw [actual]; rfl⟩
/-- The supplied actual rich witness gives a real source fragment using the
same exact connection, not a newly chosen path between its endpoints. -/
theorem actual_rich_fragment_keeps_its_literal_connection :
    ∃ fragment : SourceEdgeFragment original actualBetaSite.net (.inl ())
      ⟨Labelled.Label.atom 1,.appFn (Labelled.Label.atom 0),.lamContext (Labelled.Label.atom 1)⟩ [.fn],
      fragment.segments=rich.connection.edges :=
  rich.source_function_fragment matching rfl
/-- The other original lambda label is genuinely present, but is not a
selected redex degree for this actual physical beta site. -/
theorem argument_lambda_is_not_a_selected_degree :
    ¬SelectedDegree original (actualBetaSite.betaSyntaxFiber (.inl ()) original.erase) (Labelled.Label.atom 3) := by
  rintro ⟨name,selected,atDegree⟩
  have valid := redexFiberPaths_valid selected
  change name∈[[]] at valid
  have same := List.mem_singleton.mp valid
  subst name
  cases atDegree
#print axioms argument_lambda_is_not_a_selected_degree
#print axioms ActualRedexAccess.source_function_fragment
#print axioms PathSite.selected_degree_principal_fragment
#print axioms actual_selected_degree_has_the_fixed_principal
#print axioms actual_rich_fragment_keeps_its_literal_connection
end Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical




namespace Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
open Lamping Lambda Lambda.Labelled AG Graph
private theorem oldFunctionRoute : SourceRoute (sourceEdges [] .external original)
    (.appFn (Labelled.Label.atom 0)) (Labelled.Label.atom 1) (.lamContext (Labelled.Label.atom 1)) :=
  .atom (e:=⟨Labelled.Label.atom 1,.appFn (Labelled.Label.atom 0),.lamContext (Labelled.Label.atom 1)⟩) (by decide) rfl
/-- The actual selected syntax route's exact original ports, not merely the
degree's atoms, are realized by the fixed physical beta principal path. -/
theorem actual_selected_route_has_the_fixed_ports :
    ∃ p,∃ fragment : SourceEdgeFragment original actualBetaSite.net (.inl ())
      ⟨Labelled.Label.atom 1,.appFn (Labelled.Label.atom 0),.lamContext (Labelled.Label.atom 1)⟩ p,
      fragment.segments=Paths.encodedBetaOccurrence.principal := by
  obtain ⟨beta,app,lam,allRoutes⟩ :=
    actualBetaSite.selected_route_principal_fragment (init_is_INIT identityApp) matching
  obtain ⟨p,fragment,segments⟩ := allRoutes ⟨[],member,rfl⟩ oldFunctionRoute
  have actual := connection.beta_principal_unique beta app.symm lam.symm
  exact ⟨p,fragment,segments.trans actual.symm⟩
/-- Equal degree does not authorize a different original lambda port. -/
theorem wrong_lambda_origin_cannot_be_the_selected_route :
    ¬SourceRoute (sourceEdges [] .external original) (.appFn (Labelled.Label.atom 0))
      (Labelled.Label.atom 1) (.lamContext (Labelled.Label.atom 99)) := by
  intro route
  obtain ⟨edge,edgeMember,atomic,fromEq,toEq⟩ := route.initial_atom_edge (init_is_INIT identityApp)
  have unique := sourceEdges_unique (init_is_INIT identityApp) edgeMember
    (show (⟨Labelled.Label.atom 1,.appFn (Labelled.Label.atom 0),.lamContext (Labelled.Label.atom 1)⟩ : SourceEdge)
      ∈sourceEdges [] .external original from by decide) atomic
  have wrong := (congrArg SourceEdge.toPort unique).symm.trans toEq
  cases wrong
#print axioms SourceEdgeFragment.source_member
#print axioms PathSite.selected_route_principal_fragment
#print axioms actual_selected_route_has_the_fixed_ports
#print axioms wrong_lambda_origin_cannot_be_the_selected_route
end Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical

namespace Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
open Lamping Lambda Lambda.Labelled AG Graph
private abbrev allowed := SelectedDegree original (actualBetaSite.betaSyntaxFiber (.inl ()) original.erase)
private def underLabel : Labelled.Label :=
  ((Labelled.Label.atom 2).concat (Labelled.Label.atom 1).under).concat (Labelled.Label.atom 3)
private def fullLabel : Labelled.Label :=
  ((Labelled.Label.atom 0).concat (Labelled.Label.atom 1).over).concat underLabel
private theorem selectedFunction : SelectedSourceRoute (sourceEdges [] .external original) allowed
    (.appFn (Labelled.Label.atom 0)) (Labelled.Label.atom 1) (.lamContext (Labelled.Label.atom 1)) :=
  .atom (e:=⟨Labelled.Label.atom 1,.appFn (Labelled.Label.atom 0),.lamContext (Labelled.Label.atom 1)⟩) (by decide) rfl
private theorem underRoute : SelectedSourceRoute (sourceEdges [] .external original) allowed
    (.lamBody (Labelled.Label.atom 1)) underLabel (.lamContext (Labelled.Label.atom 3)) :=
  .under
    (.atom (e:=⟨Labelled.Label.atom 2,.lamBody (Labelled.Label.atom 1),.lamBind (Labelled.Label.atom 1)⟩) (by decide) rfl)
    ⟨[],member,rfl⟩ selectedFunction
    (.atom (e:=⟨Labelled.Label.atom 3,.appArg (Labelled.Label.atom 0),.lamContext (Labelled.Label.atom 3)⟩) (by decide) rfl)
private theorem fullRoute : SelectedSourceRoute (sourceEdges [] .external original) allowed
    .external fullLabel (.lamContext (Labelled.Label.atom 3)) :=
  .over
    (.atom (e:=⟨Labelled.Label.atom 0,.external,.appContext (Labelled.Label.atom 0)⟩) (by decide) rfl)
    ⟨[],member,rfl⟩ selectedFunction underRoute
/-- The actual I I contractum route uses both bars: full forward principal,
original body/binder edge, full REVERSED principal, then the old argument.
Its literal image is directional, with no Generated or arbitrary-label claim. -/
theorem actual_both_bar_route_is_a_physical_expanded_walk :
    ∃ beta : BetaEdge actualBetaSite.net,
      beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
      ∃ walk : PhysicalSourceWalk original (.inl ()) beta .external fullLabel (.lamContext (Labelled.Label.atom 3)),
      walk.edges.head?=some (.inr (.inl (.inl ()))) ∧
      ExpandedForward actualBetaSite.net walk.edges ∧
      SourceRouteImage original (.inl ()) beta .external fullLabel (.lamContext (Labelled.Label.atom 3)) walk.edges ∧
      walk.edges≠[] := by
  obtain ⟨beta,app,lam,allWalks⟩ := actualBetaSite.selected_source_route_walk
    (init_is_INIT identityApp) (by change (0<1) ∧ 0<1; decide) matching
  obtain ⟨walk⟩ := allWalks fullRoute
  have rootPort : walk.fromEndpoint=.inr (.inl (.inl ())) := by
    have realizes := walk.fromRealizes
    generalize equation : walk.fromEndpoint=endpoint
    rw [equation] at realizes
    cases realizes with
    | external => rfl
    | departure _ role => cases role
  exact ⟨beta,app,lam,walk,walk.head.trans (congrArg some rootPort),walk.forward,walk.image,walk.nonempty⟩
/-- The lower insertion is already a real expanded walk without pretending
that its starting body port is a root boundary. -/
theorem actual_under_route_keeps_its_source_body_port :
    ∃ beta : BetaEdge actualBetaSite.net,
      ∃ walk : PhysicalSourceWalk original (.inl ()) beta (.lamBody (Labelled.Label.atom 1)) underLabel (.lamContext (Labelled.Label.atom 3)),
      SourcePortRealizes original actualBetaSite.net (.inl ()) (.lamBody (Labelled.Label.atom 1)) walk.fromEndpoint ∧
      ExpandedForward actualBetaSite.net walk.edges := by
  obtain ⟨beta,app,lam,allWalks⟩ := actualBetaSite.selected_source_route_walk
    (init_is_INIT identityApp) (by change (0<1) ∧ 0<1; decide) matching
  obtain ⟨walk⟩ := allWalks underRoute
  exact ⟨beta,walk,walk.fromRealizes,walk.forward⟩
/-- The special reversed beta turn is expanded, and is not an ordinary
lambda-context-to-body or binder-to-body proper passage. -/
theorem binding_to_context_is_not_ordinary_forward :
    ¬ForwardPorts (.op .lam) lamBind (Sum.inl ()) := by
  intro direction
  have impossible := direction.1
  cases impossible
#print axioms PathSite.selected_beta_source_ports
#print axioms PathSite.selected_source_route_walk
#print axioms actual_both_bar_route_is_a_physical_expanded_walk
#print axioms actual_under_route_keeps_its_source_body_port
#print axioms binding_to_context_is_not_ordinary_forward
end Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical

namespace Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
open Lamping Lambda Lambda.Labelled AG Graph
private def developed : LTerm := .lam fullLabel (.var (Labelled.Label.atom 4) 0)
private theorem labelHistory : History [[]] original developed := .cons (.root _ _ _ _) (.nil _)
private theorem actualRelative : Marked.RelativeHistory [[]]
    (Marked.mark (actualBetaSite.betaSyntaxFiber (.inl ()) original.erase) original.erase) (.lam (.var 0)) := by
  change Marked.RelativeHistory [[]]
    (if ([] : Path)∈actualBetaSite.betaSyntaxFiber (.inl ()) original.erase then
      .red [[]] (.var 0) (.lam (.var 0)) else .app [[]] (.lam (.var 0)) (.lam (.var 0))) (.lam (.var 0))
  rw [if_pos member]
  exact
    (show Marked.RelativeHistory [[]] (.red [[]] (.var 0) (.lam (.var 0))) (.lam (.var 0)) from
      .cons (.root [[]] (.var 0) (.lam (.var 0))) (.nil _))
/-- The real P04 event and same label event produce a WHOLE root-boundary
trail to the target var0, through the compound surviving lambda. Its binder
is original ARGUMENT lambda atom3, not the compound label or old lambda1. -/
theorem actual_development_target_body_has_original_argument_binder :
    ∃ (beta : BetaEdge actualBetaSite.net) (finish : SourcePort)
      (trail : PhysicalSyntaxTrail original (.inl ()) beta [] .external developed [.body]
        (.var (Labelled.Label.atom 4) 0) finish),
      trail.edges.head?=some (.inr (.inl (.inl ()))) ∧
      ExpandedForward actualBetaSite.net trail.edges ∧ finish=.lamBind (Labelled.Label.atom 3) := by
  obtain ⟨beta,app,lam,allPositions⟩ := actualBetaSite.relative_development_syntax_trail
    (init_is_INIT identityApp) (by change (0<1) ∧ 0<1; decide) matching actualRelative labelHistory
  obtain ⟨finish,trail⟩ := allPositions (p:=[.body]) (sub:=.var (Labelled.Label.atom 4) 0) rfl
  obtain ⟨trail⟩ := trail
  have binder : finish=.lamBind (Labelled.Label.atom 3) := by
    have image := trail.image
    generalize equal : trail.edges=edges at image
    cases image with
    | body first child =>
      obtain ⟨n,last,origin⟩ := first.lambda_origin
      have number : 3=n := Option.some.inj last
      subst n
      cases child with
      | var _ => exact congrArg SourcePort.lamBind origin
  exact ⟨beta,finish,trail,trail.rooted,trail.forward,binder⟩
/-- The same literal de Bruijn index 0 BEFORE the contraction refers to the
original FUNCTION lambda atom1. This uses a real empty relative history,
not a reinitialization of the reduct. -/
theorem actual_original_function_body_has_different_binder :
    ∃ (beta : BetaEdge actualBetaSite.net) (finish : SourcePort)
      (trail : PhysicalSyntaxTrail original (.inl ()) beta [] .external original [.fn,.body]
        (.var (Labelled.Label.atom 2) 0) finish),
      trail.edges.head?=some (.inr (.inl (.inl ()))) ∧
      ExpandedForward actualBetaSite.net trail.edges ∧ finish=.lamBind (Labelled.Label.atom 1) := by
  obtain ⟨beta,app,lam,allPositions⟩ := actualBetaSite.relative_development_syntax_trail
    (init_is_INIT identityApp) (by change (0<1) ∧ 0<1; decide) matching
    (Marked.RelativeHistory.nil _) (History.nil original)
  obtain ⟨finish,trail⟩ := allPositions (p:=[.fn,.body]) (sub:=.var (Labelled.Label.atom 2) 0) rfl
  obtain ⟨trail⟩ := trail
  have binder : finish=.lamBind (Labelled.Label.atom 1) := by
    have image := trail.image
    generalize equal : trail.edges=edges at image
    cases image with
    | fn first child =>
      cases child with
      | body first child =>
        obtain ⟨n,last,origin⟩ := first.lambda_origin
        have number : 1=n := Option.some.inj last
        subst n
        cases child with
        | var _ => exact congrArg SourcePort.lamBind origin
  exact ⟨beta,finish,trail,trail.rooted,trail.forward,binder⟩
theorem compound_current_label_is_not_original_binder_identity : fullLabel≠Labelled.Label.atom 3 := by decide
theorem function_and_argument_original_binders_differ :
    SourcePort.lamBind (Labelled.Label.atom 1)≠.lamBind (Labelled.Label.atom 3) := by decide
#print axioms SourceSyntaxStep.direction
#print axioms PhysicalSyntaxTrail.lookup
#print axioms PhysicalSyntaxTrail.rooted
#print axioms PathSite.selected_term_syntax_trail
#print axioms PathSite.relative_development_syntax_trail
#print axioms actual_development_target_body_has_original_argument_binder
#print axioms actual_original_function_body_has_different_binder
#print axioms compound_current_label_is_not_original_binder_identity
#print axioms function_and_argument_original_binders_differ
end Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical

namespace Lamping.Checks.DegreeFamily.P06NestedCaptureCoordinates
open Lamping Lambda Lambda.Labelled AG Graph
private def identity : Term := .lam (.var 0)
private def innerBody : Term := .lam (.var 1)
private def outerBody : Term := .lam (.app (.lam innerBody) (.var 1))
private def source : Term := .app (.lam outerBody) identity
private def middle : Term := .app (.lam (.lam (.lam (.var 2)))) identity
private def target : Term := .lam (.lam identity)
private def oldNames : List Path := [[],[.fn,.body,.body]]
private def y : Path := [.body]
private def q : Path := [.body]
private def z : Path := []
private theorem closed : Closed source := by change ((1<4) ∧ 1<2) ∧ 0<1; decide
/-- A genuine inner-first, outer-second development of two original names.
Both original body depth and copy depth are nonzero. -/
theorem actual_nested_capture_relative : Marked.RelativeHistory [[.fn,.body,.body],[]]
    (Marked.mark oldNames source) (.lam (.lam (.lam (.var 0)))) :=
  .cons (.redL (.lam (.root [[.fn,.body,.body]] (.lam (.var 1)) (.var 1))))
    (.cons (.root [[]] (.lam (.lam (.var 2))) (.lam (.var 0))) (.nil _))
theorem actual_inner_then_outer : BetaAt source [.fn,.body,.body] middle ∧ BetaAt middle [] target :=
  ⟨⟨innerBody,.var 1,rfl,rfl⟩,⟨.lam (.lam (.var 2)),identity,rfl,rfl⟩⟩
theorem actual_two_beta_history : BetaHistory [[.fn,.body,.body],[]] source target :=
  .cons actual_inner_then_outer.1 (.cons actual_inner_then_outer.2 (.nil _))
/-- Correct lifting transforms the old outer-bound var1 into var2 under q;
using an unchanged de Bruijn index would point at the wrong binder. -/
theorem actual_copy_depth_and_binder :
    binderDepth y=1 ∧ binderDepth q=1 ∧
    ArgumentOccurrence innerBody q ∧
    subtermAt (.var 1) z=some (.var (binderDepth y+binderDepth z)) ∧
    subtermAt (rename (fun i => i+binderDepth q) (.var 1)) z=some (.var 2) ∧
    subtermAt (contract innerBody (.var 1)) (q++z)=some (.var 2) ∧
    2=binderDepth (y++q++z) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,rfl⟩
  exact subtermAt_contract_from_argument (show ArgumentOccurrence innerBody q from rfl) rfl
/-- The three ordinary source positions needed for the nested_insert
premises are actual syntax leaves, before either contraction. -/
theorem three_original_generated_premise_coordinates :
    subtermAt source [.arg,.body]=some (.var 0) ∧
    subtermAt source [.fn,.body,.body,.arg]=some (.var 1) ∧
    subtermAt source [.fn,.body,.body,.fn,.body,.body]=some (.var 1) ∧
    subtermAt outerBody (y++[.arg]++z)=some (.var (binderDepth (y++[.arg]++z))) ∧
    subtermAt innerBody q=some (.var (binderDepth q)) := ⟨rfl,rfl,rfl,rfl,rfl⟩
/-- The full original INIT labeling lifts along the SAME two-event schedule.
The second step consumes the correctly shifted var2; no label reset occurs. -/
theorem actual_two_event_label_lift :
    ∃ labelledTarget,History [[.fn,.body,.body],[]] (initLabels source) labelledTarget ∧ labelledTarget.erase=target :=
  lift_history actual_two_beta_history (initLabels source) (erase_initLabels source)
/-- The exact target copy origin is the nonempty inner q; it cannot be
replaced by the empty copy prefix merely because both denote the same arg. -/
theorem inner_copy_origin_is_exact :
    ∃ old relative,([.body] : Path)=old++relative ∧ ArgumentOccurrence innerBody old ∧
      subtermAt (rename (fun i => i+binderDepth old) (.var 1)) relative=some (.var 2) ∧
      ∀ other suffix,ArgumentOccurrence innerBody other → [.body]=other++suffix → other=old ∧ suffix=relative := by
  refine ⟨q,z,rfl,rfl,rfl,?_⟩
  intro other suffix occurrence split
  exact contract_argument_origin_unique occurrence (show ArgumentOccurrence innerBody q from rfl) split.symm
/-- These wrong alternatives fail as actual term equalities, not just
because a predicate is unavailable. -/
theorem unchanged_index_is_not_the_copy :
    rename (fun i => i+binderDepth q) (.var 1)≠(.var 1) ∧
    contract innerBody (.var 1)≠.lam (.var 1) := by constructor <;> decide
theorem outer_copy_protects_argument_internal_binder :
    rename (fun i => i+binderDepth (y++q)) identity=identity ∧
    subtermAt target [.body,.body,.body]=some (.var 0) := ⟨rfl,rfl⟩
/-- All three premise words refer to actual root accesses of this closed
initial graph, so they can feed the original Matches binding/prefix APIs. -/
theorem actual_original_three_root_accesses :
    ∃ (argument reducedBody nestedBody : RootAccess (encode 7 source).net (.inl ())),
      accessWord (encode 7 source).net argument.val=[.arg,.body] ∧
      accessWord (encode 7 source).net reducedBody.val=[.fn,.body,.body,.arg] ∧
      accessWord (encode 7 source).net nestedBody.val=[.fn,.body,.body,.fn,.body,.body] := by
  have matching := encode_closed_matches source closed 7
  obtain ⟨argument,argumentWord,_⟩ := Matches.observation (encode 7 source).net matching
    (⟨[.arg,.body],rfl⟩ : Position source)
  obtain ⟨reducedBody,bodyWord,_⟩ := Matches.observation (encode 7 source).net matching
    (⟨[.fn,.body,.body,.arg],rfl⟩ : Position source)
  obtain ⟨nestedBody,nestedWord,_⟩ := Matches.observation (encode 7 source).net matching
    (⟨[.fn,.body,.body,.fn,.body,.body],rfl⟩ : Position source)
  exact ⟨argument,reducedBody,nestedBody,argumentWord,bodyWord,nestedWord⟩
private def atom (n : Nat) : Labelled.Label := Labelled.Label.atom n
private def copiedVariableLabel : Labelled.Label := ((atom 6).concat (atom 4).under).concat (atom 7)
private def survivingLambdaLabel : Labelled.Label := ((atom 3).concat (atom 4).over).concat (atom 5)
private def midLabels : LTerm := .app (atom 0)
  (.lam (atom 1) (.lam (atom 2) (.lam survivingLambdaLabel (.var copiedVariableLabel 2))))
  (.lam (atom 8) (.var (atom 9) 0))
private theorem firstLabelHistory : History [[.fn,.body,.body]] (initLabels source) midLabels :=
  .cons (.fn (.body (.body (.root _ _ _ _)))) (.nil _)
/-- The actual first labeled contraction keeps the old C-lambda origin5
and still routes the shifted var2 to OUTER origin1, not surviving origin2. -/
theorem actual_shifted_variable_still_uses_original_outer_binder :
    SourceRoute (sourceEdges [] .external (initLabels source))
      (.lamBody (atom 5)) copiedVariableLabel (.lamBind (atom 1)) := by
  have routes := firstLabelHistory.generated_source_routes (init_is_INIT source)
  cases routes with
  | app root fn arg =>
    cases fn with
    | lam outer body =>
      obtain ⟨n,last,origin⟩ := outer.lam_last_atom
      have number : 1=n := Option.some.inj last
      subst n
      subst origin
      cases body with
      | lam preserved inner =>
        cases inner with
        | lam surviving leaf =>
          obtain ⟨n,last,origin⟩ := surviving.lam_last_atom
          have number : 5=n := Option.some.inj last
          subst n
          subst origin
          cases leaf with
          | var route => exact route
/-- The same actual source-origin stack distinguishes the missing-shift
error: index1 would bind the old intermediate lambda origin2. -/
theorem missing_shift_points_to_the_wrong_surviving_binder :
    sourceBinder [atom 5,atom 2,atom 1] 2=.lamBind (atom 1) ∧
    sourceBinder [atom 5,atom 2,atom 1] 1=.lamBind (atom 2) ∧
    SourcePort.lamBind (atom 1)≠.lamBind (atom 2) := by
  exact ⟨rfl,rfl,by decide⟩
#print axioms actual_shifted_variable_still_uses_original_outer_binder
#print axioms missing_shift_points_to_the_wrong_surviving_binder
#print axioms actual_nested_capture_relative
#print axioms actual_inner_then_outer
#print axioms actual_two_beta_history
#print axioms actual_copy_depth_and_binder
#print axioms three_original_generated_premise_coordinates
#print axioms actual_two_event_label_lift
#print axioms inner_copy_origin_is_exact
#print axioms unchanged_index_is_not_the_copy
#print axioms outer_copy_protects_argument_internal_binder
#print axioms actual_original_three_root_accesses
end Lamping.Checks.DegreeFamily.P06NestedCaptureCoordinates



namespace Lamping.Checks.DegreeFamily.P06NestedBinderReflection
open Lamping Lambda
private def inner : Term := .lam (.var 1)
private def argument : Term := .lam (.var 2)
private def before : Term := .lam (.app (.lam inner) argument)
private def after : Term := .lam (.lam (.lam (.var 3)))
private def site : Path := [.body]
private def copySite : Path := [.body]
private def relativeSite : Path := [.body]
private theorem event : BetaAt before site after := ⟨inner,argument,rfl,rfl⟩
private theorem occurs : ArgumentOccurrence inner copySite := rfl
/-- All three binder contributions are nonzero: the surrounding original
body site, the copied occurrence, and the position INSIDE the argument. -/
theorem three_nonzero_depths_reflect_actual_outer_binding :
    (subtermAt after (site++(copySite++relativeSite))=
      some (.var (binderDepth (site++(copySite++relativeSite)))) ↔
    subtermAt argument relativeSite=some (.var (binderDepth site+binderDepth relativeSite))) ∧
    binderDepth site=1 ∧ binderDepth copySite=1 ∧ binderDepth relativeSite=1 :=
  ⟨event.nested_copied_outer_variable_iff rfl occurs relativeSite,rfl,rfl,rfl⟩
/-- The forward and reverse interfaces are both consumed on genuine
lookups: original var2 becomes var3, and actual var3 recovers ORIGINAL var2. -/
theorem actual_var3_recovers_original_var2 :
    subtermAt after [.body,.body,.body]=some (.var 3) ∧
    subtermAt argument [.body]=some (.var 2) := by
  have iff := event.nested_copied_outer_variable_iff rfl occurs relativeSite
  exact ⟨iff.mpr rfl,iff.mp rfl⟩
/-- This reflected index belongs to the outer lambda, rather than the
lambda INSIDE the argument. Renaming never turns that bound0 into var2. -/
theorem protected_internal_binder_is_not_outer :
    rename (fun i => i+1) (.lam (.var 0))=.lam (.var 0) ∧
    ¬subtermAt (rename (fun i => i+1) (.lam (.var 0))) [.body]=some (.var 2) := by
  exact ⟨rfl,by decide⟩
/-- The complete surrounding example is closed and has the actual two
contractions; the lemma is not tested on an unscoped dummy variable alone. -/
theorem actual_closed_two_event_example :
    Closed (.app (.lam before) (.lam (.var 0))) ∧
    BetaAt (.app (.lam before) (.lam (.var 0))) [.fn,.body,.body]
      (.app (.lam after) (.lam (.var 0))) ∧
    BetaAt (.app (.lam after) (.lam (.var 0))) []
      (.lam (.lam (.lam (.lam (.var 0))))) := by
  exact ⟨by change ((1<4) ∧ 2<3) ∧ 0<1; decide,
    ⟨inner,argument,rfl,rfl⟩,⟨after,.lam (.var 0),rfl,rfl⟩⟩
#print axioms occurrenceRenaming_free_index
#print axioms shifted_outer_variable_iff
#print axioms contract_copied_outer_variable_iff
#print axioms BetaAt.nested_copied_outer_variable_iff
#print axioms three_nonzero_depths_reflect_actual_outer_binding
#print axioms actual_var3_recovers_original_var2
#print axioms protected_internal_binder_is_not_outer
#print axioms actual_closed_two_event_example
end Lamping.Checks.DegreeFamily.P06NestedBinderReflection

namespace Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
open Lamping Lambda Lambda.Labelled AG Graph
/-- One actual selector serves both bar routes at once; neither route gets
its own existential atom choices. -/
theorem actual_two_routes_share_one_finite_selector :
    ∃ beta : BetaEdge actualBetaSite.net,
    ∃ selection : SourceEdgeSelection original actualBetaSite.net (.inl ()),
    ∃ whole : PhysicalSourceWalk original (.inl ()) beta .external fullLabel (.lamContext (Labelled.Label.atom 3)),
    ∃ lower : PhysicalSourceWalk original (.inl ()) beta (.lamBody (Labelled.Label.atom 1)) underLabel (.lamContext (Labelled.Label.atom 3)),
      whole.edges=selection.evalLabel beta fullLabel ∧
      lower.edges=selection.evalLabel beta underLabel ∧
      ExpandedForward actualBetaSite.net whole.edges ∧ ExpandedForward actualBetaSite.net lower.edges := by
  obtain ⟨beta,_,_,selection,allRoutes⟩ := actualBetaSite.shared_source_route_evaluation
    (init_is_INIT identityApp) (by change (0<1) ∧ 0<1; decide) matching
  obtain ⟨whole,wholeEq⟩ := allRoutes fullRoute
  obtain ⟨lower,lowerEq⟩ := allRoutes underRoute
  exact ⟨beta,selection,whole,lower,wholeEq,lowerEq,whole.forward,lower.forward⟩
#print axioms actual_two_routes_share_one_finite_selector
end Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical

namespace Lamping.Checks.DegreeFamily.P06SharedRouteEvaluation
open Lamping Lambda Lambda.Labelled AG Graph
private def atomWord (n : Nat) : List Nat := [n]
private def body : LTerm := .lam (Labelled.Label.atom 1) (.var (Labelled.Label.atom 2) 1)
private def argument : LTerm := .lam (Labelled.Label.atom 3) (.var (Labelled.Label.atom 4) 1)
private theorem occurs : ArgumentOccurrence body.erase [.body] := rfl
/-- q and r each cross a lambda. Actual capture renames the outer var1 to
var2, while the literal graph word keeps both OLD ancestor edge words. -/
theorem actual_capture_copy_has_the_exact_literal_word :
    (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) body argument).subterm [.body,.body]=
      some (.var (Labelled.Label.atom 4) 2) ∧
    (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) body argument).sourceTrail
      atomWord [90] [91] [.body,.body]=some [20,90,1,2,91,3,4] := by
  refine ⟨rfl,?_⟩
  have exactWord := LTerm.sourceTrail_contract_copy atomWord [90] [91]
    (Labelled.Label.atom 20) (Labelled.Label.atom 10) (argument:=argument) occurs [.body]
  exact exactWord.trans rfl
/-- Invalid syntax positions stay None even through substitution; the
fallback used for irrelevant original atom numbers never creates a path. -/
theorem invalid_argument_suffix_stays_none :
    (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) body argument).sourceTrail
      atomWord [90] [91] [.body,.arg]=none := by
  have exactWord := LTerm.sourceTrail_contract_copy atomWord [90] [91]
    (Labelled.Label.atom 20) (Labelled.Label.atom 10) (argument:=argument) occurs [.arg]
  exact exactWord.trans rfl
/-- The retained root lambda uses only the old body edge and forward
principal word. This consumes the actual nonvariable origin interface. -/
theorem retained_root_uses_the_same_evaluation :
    (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) body argument).sourceTrail
      atomWord [90] [91] []=some [20,90,1] := by
  have exactWord := LTerm.sourceTrail_contract_nonvariable atomWord [90] [91]
    (Labelled.Label.atom 20) (Labelled.Label.atom 10)
    (body:=body) (old:=body) (p:=[]) rfl (by intro stamp k eq; cases eq) argument
  exact exactWord.trans rfl
/-- The prefix equation is literal and shares the same atom evaluator. -/
theorem exact_common_prefix_equation :
    body.sourceTrail atomWord [90] [91] ([.body]++[])=
      (body.sourceStem atomWord [90] [91] [.body]).bind (fun stem =>
        ((.var (Labelled.Label.atom 2) 1 : LTerm).sourceTrail atomWord [90] [91] []).map (stem++·)) :=
  LTerm.sourceTrail_split atomWord [90] [91] rfl []
#print axioms PathSite.shared_source_route_evaluation
#print axioms LTerm.sourceTrail_contract_copy
#print axioms LTerm.sourceTrail_contract_nonvariable
#print axioms LTerm.sourceTrail_split
#print axioms LTerm.sourceTrail_exists
#print axioms actual_capture_copy_has_the_exact_literal_word
#print axioms invalid_argument_suffix_stays_none
#print axioms retained_root_uses_the_same_evaluation
#print axioms exact_common_prefix_equation
end Lamping.Checks.DegreeFamily.P06SharedRouteEvaluation
namespace Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
open Lamping Lambda Lambda.Labelled AG Graph
/-- One shared selector interprets the actual compound reduct AND the two
original ordinary accesses with identical var0 syntax but different binders.
The physical lists are equated literally, not just at their endpoints. -/
theorem current_whole_trail_and_original_accesses_share_the_evaluator :
    ∃ beta : BetaEdge actualBetaSite.net,
    ∃ selection : SourceEdgeSelection original actualBetaSite.net (.inl ()),
    ∃ (oldFunction oldArgument : RootAccess actualBetaSite.net (.inl ()))
      (finish : SourcePort)
      (trail : PhysicalSyntaxTrail original (.inl ()) beta [] .external developed [.body]
        (.var (Labelled.Label.atom 4) 0) finish),
      original.sourceTrail selection.atomWord beta.principal beta.reverseRoute [.fn,.body]=some oldFunction.val ∧
      original.sourceTrail selection.atomWord beta.principal beta.reverseRoute [.arg,.body]=some oldArgument.val ∧
      developed.sourceTrail selection.atomWord beta.principal beta.reverseRoute [.body]=some trail.edges ∧
      oldFunction.val≠oldArgument.val ∧ ExpandedForward actualBetaSite.net trail.edges := by
  obtain ⟨beta,_,_,selection,allPositions⟩ := actualBetaSite.relative_development_shared_syntax_evaluation
    (init_is_INIT identityApp) (by change (0<1) ∧ 0<1; decide) matching actualRelative labelHistory
  obtain ⟨finish,trail,currentEq⟩ := allPositions (p:=[.body]) (sub:=.var (Labelled.Label.atom 4) 0) rfl
  let functionPosition : Position original.erase := ⟨[.fn,.body],by decide⟩
  let argumentPosition : Position original.erase := ⟨[.arg,.body],by decide⟩
  obtain ⟨oldFunction,functionWord,_⟩ := Matches.observation actualBetaSite.net matching functionPosition
  obtain ⟨oldArgument,argumentWord,_⟩ := Matches.observation actualBetaSite.net matching argumentPosition
  have different : oldFunction.val≠oldArgument.val := by
    intro equal
    have words := functionWord.symm.trans ((congrArg (accessWord actualBetaSite.net) equal).trans argumentWord)
    cases words
  exact ⟨beta,selection,oldFunction,oldArgument,finish,trail,
    selection.original_access_evaluation (init_is_INIT identityApp) matching
      (p:=[.fn,.body]) (sub:=.var (Labelled.Label.atom 2) 0) rfl oldFunction functionWord,
    selection.original_access_evaluation (init_is_INIT identityApp) matching
      (p:=[.arg,.body]) (sub:=.var (Labelled.Label.atom 4) 0) rfl oldArgument argumentWord,
    currentEq,different,trail.forward⟩
/-- The empty original syntax position is the entire ordinary root access,
not an empty endpoint list or the unvalidated atom fallback. -/
theorem original_root_evaluation_is_the_whole_actual_access :
    ∃ (beta : BetaEdge actualBetaSite.net)
      (selection : SourceEdgeSelection original actualBetaSite.net (.inl ()))
      (access : RootAccess actualBetaSite.net (.inl ())),
      original.sourceTrail selection.atomWord beta.principal beta.reverseRoute []=some access.val ∧ access.val≠[] := by
  obtain ⟨beta,_,_,selection,_⟩ := actualBetaSite.shared_source_route_evaluation
    (init_is_INIT identityApp) (by change (0<1) ∧ 0<1; decide) matching
  let position : Position original.erase := ⟨[],by decide⟩
  obtain ⟨access,word,_⟩ := Matches.observation actualBetaSite.net matching position
  exact ⟨beta,selection,access,
    selection.original_access_evaluation (init_is_INIT identityApp) matching (sub:=original) rfl access word,
    access.property.1.1.walk.nonempty⟩
#print axioms SourceEdgeFragment.external_segments
#print axioms SourceEdgeFragment.child_prefix
#print axioms SourceEdgeFragment.access_eq_at
#print axioms SourceEdgeSelection.original_access_evaluation
#print axioms PathSite.relative_development_shared_syntax_evaluation
#print axioms current_whole_trail_and_original_accesses_share_the_evaluator
#print axioms original_root_evaluation_is_the_whole_actual_access
end Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
namespace Lamping.Checks.DegreeFamily.P06SharedRouteEvaluation
open Lamping Lambda Lambda.Labelled AG Graph
private def innerBound : LTerm := .lam (Labelled.Label.atom 1) (.var (Labelled.Label.atom 2) 0)
private def externalVar : LTerm := .lam (Labelled.Label.atom 1) (.var (Labelled.Label.atom 2) 2)
/-- The bound0 under the retained lambda stays bound0. It is outside the
contracted binder despite lying BELOW its depth; no free-index shortcut. -/
theorem kept_inner_bound_variable_preserves_the_literal_body_trail :
    (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) innerBound argument).subterm [.body]=
      some (.var (Labelled.Label.atom 2) 0) ∧
    (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) innerBound argument).sourceTrail
      atomWord [90] [91] [.body]=some [20,90,1,2] := by
  refine ⟨rfl,?_⟩
  have exactWord := LTerm.sourceTrail_contract_retained_variable atomWord [90] [91]
    (Labelled.Label.atom 20) (Labelled.Label.atom 10) (body:=innerBound) (p:=[.body])
    (k:=0) rfl (by decide) argument
  exact exactWord.trans rfl
/-- An external index is decremented by beta, but the SAME original label
path is retained. The evaluator is about edge identity, not current indices. -/
theorem kept_external_variable_changes_index_but_preserves_the_word :
    (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) externalVar argument).subterm [.body]=
      some (.var (Labelled.Label.atom 2) 1) ∧
    (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) externalVar argument).sourceTrail
      atomWord [90] [91] [.body]=some [20,90,1,2] := by
  refine ⟨rfl,?_⟩
  have exactWord := LTerm.sourceTrail_contract_retained_variable atomWord [90] [91]
    (Labelled.Label.atom 20) (Labelled.Label.atom 10) (body:=externalVar) (p:=[.body])
    (k:=2) rfl (by decide) argument
  exact exactWord.trans rfl
/-- The selected binder variable really inserts the backward route and
argument: dropping the disequality would make the retained formula false. -/
theorem copied_variable_does_not_satisfy_the_retained_formula :
    (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) body argument).sourceTrail
      atomWord [90] [91] [.body]≠some [20,90,1,2] := by decide
#print axioms LTerm.sourceTrail_subst_outside
#print axioms LTerm.sourceTrail_contract_retained_variable
#print axioms kept_inner_bound_variable_preserves_the_literal_body_trail
#print axioms kept_external_variable_changes_index_but_preserves_the_word
#print axioms copied_variable_does_not_satisfy_the_retained_formula
end Lamping.Checks.DegreeFamily.P06SharedRouteEvaluation
namespace Lamping.Checks.DegreeFamily.P06BetaBoundVariableOrigins
open Lamping Lambda
private def identity : Term := .lam (.var 0)
private def retainedBefore : Term := .lam (.app (.lam (.var 2)) identity)
private def retainedAfter : Term := .lam (.var 1)
private theorem retainedEvent : BetaAt retainedBefore [.body] retainedAfter := ⟨.var 2,identity,rfl,rfl⟩
private theorem var2_has_no_argument_copy (p : Path) : ¬ArgumentOccurrence (.var 2) p := by
  cases p with
  | nil => change ¬(some (Term.var 2)=some (.var 0)); decide
  | cons step rest => cases step <;> simp [ArgumentOccurrence,subtermAt]
/-- The retained outer-bound var1 recovers old var2 at the FULL old body
position. This excludes the argument-copy branch using actual syntax. -/
theorem retained_outer_leaf_recovers_its_original_full_position :
    subtermAt retainedBefore [.body,.fn,.body]=some (.var 2) := by
  have source := retainedEvent.outer_bound_variable_source_coordinates (p:=[]) rfl rfl
  rcases source with retained | ⟨q,r,_,occurs,_,_⟩
  · exact retained
  · exact False.elim (var2_has_no_argument_copy q occurs)
private def copiedBefore : Term := .lam (.app (.lam (.lam (.var 1))) (.var 1))
private def copiedAfter : Term := .lam (.lam (.var 2))
private theorem copiedEvent : BetaAt copiedBefore [.body] copiedAfter := ⟨.lam (.var 1),.var 1,rfl,rfl⟩
/-- The copied leaf crosses one retained lambda AND one copy lambda. The
unique q/r decomposition recovers the OLD argument var1, not a body var3. -/
theorem copied_outer_leaf_recovers_the_original_argument_position :
    subtermAt copiedBefore [.body,.arg]=some (.var 1) := by
  have source := copiedEvent.outer_bound_variable_source_coordinates (p:=[.body]) rfl rfl
  rcases source with retained | ⟨q,r,split,occurs,_,atArgument⟩
  · cases retained
  · have unique := contract_argument_origin_unique
      (show ArgumentOccurrence (.lam (.var 1)) [.body] from rfl) occurs
      (show [.body]++[]=q++r by simpa only [List.append_nil] using split)
    have qEq := unique.1
    have rEq := unique.2
    subst q; subst r
    exact atArgument
/-- Both diagrams live under a real retained outer lambda in closed syntax. -/
theorem retained_outer_examples_are_closed : Closed (.lam retainedBefore) ∧ Closed (.lam copiedBefore) := by
  exact ⟨by change (2<3) ∧ 0<3; decide,by change (1<4) ∧ 1<2; decide⟩

private def copiedBody : Term := .lam (.var 1)
private def lambdaBody : Term := .app (.var 1) (.app (.var 0) (.var 2))
private def originalArgument : Term := .lam (.lam lambdaBody)
private def lambdaBefore : Term := .lam (.app (.lam copiedBody) originalArgument)
private def lambdaAfter : Term := .lam (.lam (.lam (.lam (.app (.var 1) (.app (.var 0) (.var 3))))))
private theorem lambdaEvent : BetaAt lambdaBefore [.body] lambdaAfter := ⟨copiedBody,originalArgument,rfl,rfl⟩
/-- q=r=[body] select a genuine copied INNER argument lambda. Its bound0
is reflected at the original lambda, not at the outer argument binder. -/
theorem copied_lambda_bound_leaf_has_the_same_original_occurrence :
    subtermAt lambdaAfter [.body,.body,.body,.body,.arg,.fn]=some (.var 0) ∧
    subtermAt lambdaBefore [.body,.arg,.body,.body,.arg,.fn]=some (.var 0) := by
  have reflected := lambdaEvent.copied_lambda_bound_variable_iff rfl
    (show ArgumentOccurrence copiedBody [.body] from rfl)
    (show subtermAt originalArgument [.body]=some (.lam lambdaBody) from rfl) [.arg,.fn]
  exact ⟨reflected.mpr rfl,reflected.mp rfl⟩
/-- The neighboring var1 belongs to the OUTER argument lambda. It is not
bound by the copied inner lambda, while the external var2 really shifts to3. -/
theorem copied_lambda_does_not_capture_the_other_two_binders :
    ¬subtermAt lambdaAfter [.body,.body,.body,.body,.fn]=some (.var 0) ∧
    subtermAt lambdaAfter [.body,.body,.body,.body,.arg,.arg]=some (.var 3) ∧
    subtermAt originalArgument [.body,.body,.arg,.arg]=some (.var 2) := by
  exact ⟨by decide,rfl,rfl⟩
theorem copied_lambda_example_is_closed : Closed lambdaBefore := by
  change (1<3) ∧ (1<3 ∧ (0<3 ∧ 2<3))
  decide
/-- Arbitrary renaming can identify FREE variables. The internal-depth
premise in the reflection kernel cannot be deleted. -/
theorem free_renaming_is_not_bound_variable_reflection :
    subtermAt (rename (fun _ => 0) (.var 1)) []=some (.var 0) ∧
    ¬subtermAt (.var 1) []=some (.var 0) := ⟨rfl,by decide⟩
#print axioms occurrenceRenaming_bound
#print axioms renamed_bound_variable_iff
#print axioms liftSingle_outer_variable_iff
#print axioms BetaAt.outer_bound_variable_source_coordinates
#print axioms BetaAt.copied_lambda_bound_variable_iff
#print axioms retained_outer_leaf_recovers_its_original_full_position
#print axioms copied_outer_leaf_recovers_the_original_argument_position
#print axioms copied_lambda_bound_leaf_has_the_same_original_occurrence
#print axioms copied_lambda_does_not_capture_the_other_two_binders
#print axioms free_renaming_is_not_bound_variable_reflection
end Lamping.Checks.DegreeFamily.P06BetaBoundVariableOrigins
namespace Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
open Lamping Lambda Lambda.Labelled AG Graph
/-- The public builder uses the SAME selected atom words below a real
argument port. It does not restart that fragment at the root boundary. -/
theorem shared_local_argument_trail_keeps_its_actual_departure :
    ∃ beta : BetaEdge actualBetaSite.net,
    ∃ selection : SourceEdgeSelection original actualBetaSite.net (.inl ()),
    ∃ finish,∃ trail : PhysicalSyntaxTrail original (.inl ()) beta [] (.appArg (Labelled.Label.atom 0))
      (.lam (Labelled.Label.atom 3) (.var (Labelled.Label.atom 4) 0)) [.body] (.var (Labelled.Label.atom 4) 0) finish,
      (.lam (Labelled.Label.atom 3) (.var (Labelled.Label.atom 4) 0) : LTerm).sourceTrail
        selection.atomWord beta.principal beta.reverseRoute [.body]=some trail.edges ∧
      SourcePortRealizes original actualBetaSite.net (.inl ()) (.appArg (Labelled.Label.atom 0)) trail.fromEndpoint := by
  obtain ⟨beta,_,_,selection,walks⟩ := actualBetaSite.shared_source_route_evaluation
    (init_is_INIT identityApp) (by change (0<1) ∧ 0<1; decide) matching
  have routes := relative_development_selected_routes (init_is_INIT identityApp)
    (Marked.RelativeHistory.nil (Marked.mark (actualBetaSite.betaSyntaxFiber (.inl ()) original.erase) original.erase))
    (History.nil original)
  cases routes with
  | app rootRoute functionRoutes argumentRoutes =>
    obtain ⟨edge,edgeMember,atomic,_,toEq⟩ := rootRoute.forget.initial_atom_edge (init_is_INIT identityApp)
    have same := sourceEdges_unique (init_is_INIT identityApp) edgeMember
      (show (⟨Labelled.Label.atom 0,.external,.appContext (Labelled.Label.atom 0)⟩ : SourceEdge)
        ∈sourceEdges [] .external original from by decide) atomic
    have originEq := SourcePort.appContext.inj (toEq.symm.trans (congrArg SourceEdge.toPort same))
    rw [originEq] at argumentRoutes
    obtain ⟨finish,trail,word⟩ := selection.syntax_evaluation (init_is_INIT identityApp) matching walks
      argumentRoutes (p:=[.body]) (sub:=.var (Labelled.Label.atom 4) 0) rfl
    exact ⟨beta,selection,finish,trail,word,trail.fromRealizes⟩
#print axioms SourceEdgeSelection.syntax_evaluation
#print axioms shared_local_argument_trail_keeps_its_actual_departure
end Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
namespace Lamping.Checks.DegreeFamily.P06CopiedLambdaBodies
open Lamping Lambda Lambda.Labelled AG Graph
private def atomWord (n : Nat) : List Nat := [n]
private def oldInner : LTerm := .app (Labelled.Label.atom 5) (.var (Labelled.Label.atom 6) 1)
  (.app (Labelled.Label.atom 7) (.var (Labelled.Label.atom 8) 0) (.var (Labelled.Label.atom 9) 2))
private def newInner : LTerm := .app (Labelled.Label.atom 5) (.var (Labelled.Label.atom 6) 1)
  (.app (Labelled.Label.atom 7) (.var (Labelled.Label.atom 8) 0) (.var (Labelled.Label.atom 9) 3))
private def argument : LTerm := .lam (Labelled.Label.atom 3) (.lam (Labelled.Label.atom 4) oldInner)
private def body : LTerm := .lam (Labelled.Label.atom 1) (.var (Labelled.Label.atom 2) 1)
private def reduced : LTerm := LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) body argument
/-- The copied INNER lambda keeps its complete body edge-word evaluator
at EVERY position, while its external var2 truly becomes var3. -/
theorem copied_inner_lambda_body_uses_the_same_old_literal_words (p : Path) :
    newInner.sourceTrail atomWord [90] [91] p=oldInner.sourceTrail atomWord [90] [91] p := by
  obtain ⟨rho,equal⟩ := LTerm.contract_copied_lambda_body_rename
    (beta:=Labelled.Label.atom 20) (alpha:=Labelled.Label.atom 10)
    (show ArgumentOccurrence body.erase [.body] from rfl)
    (show argument.subterm [.body]=some (.lam (Labelled.Label.atom 4) oldInner) from rfl)
    (show reduced.subterm ([.body]++[.body])=some (.lam (Labelled.Label.atom 4) newInner) from rfl)
  rw [equal,LTerm.sourceTrail_rename]
/-- r=[] selects the copied ROOT lambda. Its incoming label does change;
the body still has the same literal words, including the nested lambda. -/
theorem copied_root_lambda_body_uses_the_same_old_literal_words (p : Path) :
    (.lam (Labelled.Label.atom 4) newInner : LTerm).sourceTrail atomWord [90] [91] p=
      (.lam (Labelled.Label.atom 4) oldInner : LTerm).sourceTrail atomWord [90] [91] p := by
  obtain ⟨rho,equal⟩ := LTerm.contract_copied_lambda_body_rename
    (beta:=Labelled.Label.atom 20) (alpha:=Labelled.Label.atom 10)
    (show ArgumentOccurrence body.erase [.body] from rfl)
    (show argument.subterm []=some (.lam (Labelled.Label.atom 3) (.lam (Labelled.Label.atom 4) oldInner)) from rfl)
    (show reduced.subterm ([.body]++[])=some (.lam
      (((Labelled.Label.atom 2).concat (Labelled.Label.atom 10).under).concat (Labelled.Label.atom 3))
      (.lam (Labelled.Label.atom 4) newInner)) from rfl)
  rw [equal,LTerm.sourceTrail_rename]
/-- The body-variable at the beta root acquires BOTH incoming prefixes.
Even this empty q/r case preserves the lambda BODY rather than its label. -/
theorem whole_root_copy_lambda_body_still_is_original :
    ∃ rho,(.lam (Labelled.Label.atom 4) oldInner : LTerm)=
      (.lam (Labelled.Label.atom 4) oldInner : LTerm).rename rho := by
  exact LTerm.contract_copied_lambda_body_rename
    (beta:=Labelled.Label.atom 20) (alpha:=Labelled.Label.atom 10)
    (show ArgumentOccurrence (.var (Labelled.Label.atom 2) 0 : LTerm).erase [] from rfl)
    (show argument.subterm []=some (.lam (Labelled.Label.atom 3) (.lam (Labelled.Label.atom 4) oldInner)) from rfl)
    (show (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10)
      (.var (Labelled.Label.atom 2) 0) argument).subterm ([]++[])=some (.lam
      (((Labelled.Label.atom 20).concat (Labelled.Label.atom 10).over).concat
        (((Labelled.Label.atom 2).concat (Labelled.Label.atom 10).under).concat (Labelled.Label.atom 3)))
      (.lam (Labelled.Label.atom 4) oldInner)) from rfl)
theorem copied_lambda_incoming_label_is_not_preserved :
    (reduced.subterm [.body]).map LTerm.label≠some (Labelled.Label.atom 3) := by decide
theorem actual_closed_labelled_copy_event :
    Closed (.lam (Labelled.Label.atom 50) (.app (Labelled.Label.atom 20)
      (.lam (Labelled.Label.atom 10) body) argument) : LTerm).erase ∧
    StepAt [.body] (.lam (Labelled.Label.atom 50) (.app (Labelled.Label.atom 20)
      (.lam (Labelled.Label.atom 10) body) argument)) (.lam (Labelled.Label.atom 50) reduced) := by
  exact ⟨by change (1<3) ∧ (1<3 ∧ (0<3 ∧ 2<3)); decide,.body (.root _ _ _ _)⟩
#print axioms LTerm.CopyInterior.lambda_body_rename
#print axioms LTerm.contract_copied_lambda_body_rename
#print axioms copied_inner_lambda_body_uses_the_same_old_literal_words
#print axioms copied_root_lambda_body_uses_the_same_old_literal_words
#print axioms whole_root_copy_lambda_body_still_is_original
#print axioms copied_lambda_incoming_label_is_not_preserved
#print axioms actual_closed_labelled_copy_event
end Lamping.Checks.DegreeFamily.P06CopiedLambdaBodies
namespace Lamping.Checks.DegreeFamily.P06BetaBoundVariableOrigins
open Lamping Lambda
private def apartBefore : Term := .app (.var 0) (.app (.lam (.var 0)) identity)
private def apartAfter : Term := .app (.var 0) identity
private theorem apartEvent : BetaAt apartBefore [.arg] apartAfter := ⟨.var 0,identity,rfl,rfl⟩
/-- A bound leaf outside the actual beta is genuinely disjoint and has the
same old full position/index. No caller disjointness premise is supplied. -/
theorem outside_bound_leaf_is_classified_from_the_actual_event :
    DisjointPositions [.arg] [.fn] ∧ subtermAt apartBefore [.fn]=some (.var 0) := by
  have all := apartEvent.all_outer_bound_variable_sources (leaf:=[.fn]) rfl rfl
  rcases all with outside | ⟨p,split,_⟩
  · exact outside
  · cases split
/-- The outer retained lambda makes the independent argument contraction
closed; the outside leaf is not a dummy free graph access assumption. -/
theorem disjoint_bound_leaf_example_is_closed : Closed (.lam apartBefore) := by
  change (0<1) ∧ (0<2 ∧ 0<2)
  decide
#print axioms BetaAt.bound_variable_outside_or_below
#print axioms BetaAt.all_outer_bound_variable_sources
#print axioms outside_bound_leaf_is_classified_from_the_actual_event
#print axioms disjoint_bound_leaf_example_is_closed
end Lamping.Checks.DegreeFamily.P06BetaBoundVariableOrigins
namespace Lamping.Checks.DegreeFamily.P06RetainedLambdaEvaluation
open Lamping Lambda Lambda.Labelled AG Graph
private def atoms (n : Nat) : List Nat := [n]
private def oldBody : LTerm := .lam (Labelled.Label.atom 2) (.app (Labelled.Label.atom 3)
  (.var (Labelled.Label.atom 4) 1) (.var (Labelled.Label.atom 5) 2))
private def argument : LTerm := .lam (Labelled.Label.atom 6) (.var (Labelled.Label.atom 7) 0)
private def newBody : LTerm := .lam (Labelled.Label.atom 2) (.app (Labelled.Label.atom 3)
  (.var (Labelled.Label.atom 4) 1) (.lam
    (((Labelled.Label.atom 5).concat (Labelled.Label.atom 10).under).concat (Labelled.Label.atom 6))
    (.var (Labelled.Label.atom 7) 0)))
private def body : LTerm := .lam (Labelled.Label.atom 1) oldBody
/-- The current bound leaf crosses another retained lambda. Protected slot
0 becomes slot1, and old var1 is recovered at EXACTLY body/fn. -/
theorem retained_root_lambda_recovers_old_bound_leaf_and_literal_word :
    ArgumentOccurrence oldBody.erase [.body,.fn] ∧
    newBody.sourceTrail atoms [90] [91] [.body,.fn]=some [2,3,4] := by
  have result := LTerm.contract_retained_lambda_bound_path atoms [90] [91]
    (beta:=Labelled.Label.atom 20) (alpha:=Labelled.Label.atom 10)
    (body:=body) (argument:=argument)
    (show body.subterm []=some (.lam (Labelled.Label.atom 1) oldBody) from rfl)
    (show (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) body argument).subterm []=
      some (.lam (((Labelled.Label.atom 20).concat (Labelled.Label.atom 10).over).concat (Labelled.Label.atom 1)) newBody) from rfl)
    (show ArgumentOccurrence newBody.erase [.body,.fn] from rfl)
  exact ⟨result.1,result.2.trans rfl⟩
/-- The same protection holds at a NONROOT retained body lambda; the outer
beta also substitutes in another body branch. No reduct INIT is required. -/
theorem retained_nonroot_lambda_uses_the_same_body_loop_word :
    ArgumentOccurrence oldBody.erase [.body,.fn] ∧
    newBody.sourceTrail atoms [90] [91] [.body,.fn]=oldBody.sourceTrail atoms [90] [91] [.body,.fn] := by
  exact LTerm.contract_retained_lambda_bound_path atoms [90] [91]
    (beta:=Labelled.Label.atom 20) (alpha:=Labelled.Label.atom 10)
    (body:=.app (Labelled.Label.atom 8) body (.var (Labelled.Label.atom 9) 0)) (argument:=argument)
    (p:=[.fn]) rfl rfl (show ArgumentOccurrence newBody.erase [.body,.fn] from rfl)
/-- The inserted argument has a bound0 of its OWN. It cannot supply the
retained outer lambda's expected var2 at this deeper path. -/
theorem inserted_argument_binder_cannot_be_captured_by_retained_lambda :
    ¬ArgumentOccurrence newBody.erase [.body,.arg,.body] := by
  change ¬(some (Term.var 0)=some (.var 2))
  decide
/-- Only protected bound-leaf trails are unchanged. The substituted outer
variable really adds argument syntax and a backward-route word elsewhere. -/
theorem arbitrary_body_trails_need_not_be_preserved :
    newBody.sourceTrail atoms [90] [91] [.body,.arg,.body]≠
      oldBody.sourceTrail atoms [90] [91] [.body,.arg,.body] := by decide
theorem actual_closed_retained_lambda_event :
    Closed (.app (Labelled.Label.atom 20) (.lam (Labelled.Label.atom 10) body) argument : LTerm).erase ∧
    StepAt [] (.app (Labelled.Label.atom 20) (.lam (Labelled.Label.atom 10) body) argument)
      (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) body argument) := by
  exact ⟨by change ((1<3) ∧ 2<3) ∧ 0<1; decide,.root _ _ _ _⟩
#print axioms LTerm.contract_retained_lambda_body
#print axioms LTerm.sourceTrail_subst_protected
#print axioms LTerm.contract_retained_lambda_bound_path
#print axioms retained_root_lambda_recovers_old_bound_leaf_and_literal_word
#print axioms retained_nonroot_lambda_uses_the_same_body_loop_word
#print axioms inserted_argument_binder_cannot_be_captured_by_retained_lambda
#print axioms arbitrary_body_trails_need_not_be_preserved
#print axioms actual_closed_retained_lambda_event
end Lamping.Checks.DegreeFamily.P06RetainedLambdaEvaluation

namespace Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
open Lamping Lambda Lambda.Labelled AG Graph
/-- Joint induction chooses the physical beta ONCE from its actual ports,
then evaluates the compound selected route with that SAME record. -/
theorem selected_route_builder_uses_the_preselected_physical_beta :
    ∃ beta : BetaEdge actualBetaSite.net,
    ∃ selection : SourceEdgeSelection original actualBetaSite.net (.inl ()),
    ∃ walk : PhysicalSourceWalk original (.inl ()) beta .external fullLabel (.lamContext (Labelled.Label.atom 3)),
      walk.edges=selection.evalLabel beta fullLabel ∧ ExpandedForward actualBetaSite.net walk.edges := by
  obtain ⟨beta,_,_,ports⟩ := actualBetaSite.selected_beta_source_ports (init_is_INIT identityApp) matching
  let selection := matching.source_edge_selection (show Closed original.erase from by change (0<1) ∧ 0<1; decide)
  obtain ⟨walk,word⟩ := selection.selected_route_walk (init_is_INIT identityApp) matching ports fullRoute
  exact ⟨beta,selection,walk,word,walk.forward⟩
/-- All four children retain their selected guards at the actual redex,
including the original body binder environment, rather than bare routes. -/
theorem actual_selected_redex_exposes_its_body_and_argument_routes :
    ∃ env ctx appId lamId,
      SelectedSourceRoute (sourceEdges [] .external original) allowed ctx (Labelled.Label.atom 0) (.appContext appId) ∧
      SelectedSourceRoute (sourceEdges [] .external original) allowed (.appFn appId) (Labelled.Label.atom 1) (.lamContext lamId) ∧
      SelectedTermRoutes (sourceEdges [] .external original) allowed (lamId::env) (.lamBody lamId) (.var (Labelled.Label.atom 2) 0) ∧
      SelectedTermRoutes (sourceEdges [] .external original) allowed env (.appArg appId)
        (.lam (Labelled.Label.atom 3) (.var (Labelled.Label.atom 4) 0)) := by
  have routes := relative_development_selected_routes (init_is_INIT identityApp)
    (Marked.RelativeHistory.nil (Marked.mark (actualBetaSite.betaSyntaxFiber (.inl ()) original.erase) original.erase))
    (History.nil original)
  exact routes.redex_children (site:=[]) rfl
#print axioms SourceEdgeSelection.selected_route_walk
#print axioms SelectedTermRoutes.redex_children
#print axioms selected_route_builder_uses_the_preselected_physical_beta
#print axioms actual_selected_redex_exposes_its_body_and_argument_routes
end Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
namespace Lamping.Checks.DegreeFamily.P06RetainedLambdaEvaluation
open Lamping Lambda Lambda.Labelled AG Graph
private def contextualSource : LTerm := .lam (Labelled.Label.atom 50)
  (.app (Labelled.Label.atom 20) (.lam (Labelled.Label.atom 10) body) argument)
private def contextualTarget : LTerm := .lam (Labelled.Label.atom 50)
  (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) body argument)
private theorem contextualEvent : StepAt [.body] contextualSource contextualTarget := .body (.root _ _ _ _)
/-- Strict-ancestor positions retain their old WORD, despite the subterm's
body changing. The classifier supplies actual old lookup existence itself. -/
theorem ancestor_target_position_has_a_real_old_evaluation :
    ∃ p old,contextualSource.subterm p=some old ∧
      contextualTarget.sourceTrail atoms [10] [91] []=contextualSource.sourceTrail atoms [10] [91] p := by
  have origins := contextualEvent.sourceTrail_position_origins atoms [10] [91] rfl rfl
    (show contextualTarget.subterm []=some contextualTarget from rfl)
  rcases origins with retained | ⟨q,r,old,path,_,_⟩
  · exact retained
  · cases path
/-- The retained BODY lambda is sent to a real old function/body position,
not mistaken for an argument copy at the root of the local contractum. -/
theorem retained_lambda_target_position_has_a_real_old_evaluation :
    ∃ p old,contextualSource.subterm p=some old ∧
      contextualTarget.sourceTrail atoms [10] [91] [.body]=contextualSource.sourceTrail atoms [10] [91] p := by
  have origins := contextualEvent.sourceTrail_position_origins atoms [10] [91] rfl rfl
    (show contextualTarget.subterm [.body]=some (.lam
      (((Labelled.Label.atom 20).concat (Labelled.Label.atom 10).over).concat (Labelled.Label.atom 1)) newBody) from rfl)
  rcases origins with retained | ⟨q,r,old,path,occurs,_⟩
  · exact retained
  · have tail : ([] : Path)=q++r := (List.cons.inj path).2
    have empty := (List.append_eq_nil_iff.mp tail.symm).1
    subst q
    cases occurs
/-- The other retained branch is a kept variable below two lambdas. Its
old index differs from the contracted binder's slot, excluding any copy. -/
theorem retained_variable_target_position_has_a_real_old_evaluation :
    ∃ p old,contextualSource.subterm p=some old ∧
      contextualTarget.sourceTrail atoms [10] [91] [.body,.body,.body,.fn]=
        contextualSource.sourceTrail atoms [10] [91] p := by
  have origins := contextualEvent.sourceTrail_position_origins atoms [10] [91] rfl rfl
    (show contextualTarget.subterm [.body,.body,.body,.fn]=some (.var (Labelled.Label.atom 4) 1) from rfl)
  rcases origins with retained | ⟨q,r,old,path,occurs,_⟩
  · exact retained
  · have localPath : ([.body,.body,.fn] : Path)=q++r := (List.cons.inj path).2
    exact False.elim (retained_variable_not_argument_origin
      (show subtermAt body.erase [.body,.body,.fn]=some (.var 1) from rfl)
      (by decide) occurs localPath)
/-- The ancestor subterm itself really changed; equality of evaluation was
not obtained by an incorrect unchanged-subterm assertion. -/
theorem ancestor_subterm_really_changes : contextualSource≠contextualTarget := by decide
#print axioms StepAt.sourceTrail_position_origins
#print axioms ancestor_target_position_has_a_real_old_evaluation
#print axioms retained_lambda_target_position_has_a_real_old_evaluation
#print axioms retained_variable_target_position_has_a_real_old_evaluation
#print axioms ancestor_subterm_really_changes
end Lamping.Checks.DegreeFamily.P06RetainedLambdaEvaluation

namespace Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
open Lamping Lambda Lambda.Labelled AG Graph
private def atoms (n : Nat) : List Nat := [n]
private theorem original_cannot_have_the_inserted_reverse_word (p : Path)
    (lookup : original.subterm p=some old) :
    original.sourceTrail atoms [1] [91] p≠some [0,1,2,91,3] := by
  cases p with
  | nil => decide
  | cons step rest =>
    cases step with
    | body => cases lookup
    | fn =>
      cases rest with
      | nil => decide
      | cons child tail => cases child with
        | fn | arg => cases lookup
        | body => cases tail with
          | nil => decide
          | cons child suffix => cases child <;> cases lookup
    | arg =>
      cases rest with
      | nil => decide
      | cons child tail => cases child with
        | fn | arg => cases lookup
        | body => cases tail with
          | nil => decide
          | cons child suffix => cases child <;> cases lookup
/-- The newly inserted reverse word cannot be any old ordinary trail, so
the actual total position classifier must return a genuine argument copy. -/
theorem created_compound_target_position_is_classified_as_argument_copy :
    ∃ q r argSub,([] : Path)=[]++(q++r) ∧ ArgumentOccurrence (.var (Labelled.Label.atom 2) 0 : LTerm).erase q ∧
      (.lam (Labelled.Label.atom 3) (.var (Labelled.Label.atom 4) 0) : LTerm).subterm r=some argSub := by
  have origins := (show StepAt [] original developed from .root _ _ _ _).sourceTrail_position_origins
    atoms [1] [91] rfl rfl (show developed.subterm []=some developed from rfl)
  rcases origins with ⟨p,old,lookup,word⟩ | copied
  · have impossible := original_cannot_have_the_inserted_reverse_word p lookup
    exact False.elim (impossible word.symm)
  · exact copied
#print axioms created_compound_target_position_is_classified_as_argument_copy
end Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
namespace Lamping.Checks.DegreeFamily.P06CopiedLambdaBodies
open Lamping Lambda Lambda.Labelled AG Graph
/-- The ORIGINAL lambda and its body are recovered from the copied target
alone. No old-lambda shape is supplied to the reverse interface. -/
theorem copied_inner_lambda_automatically_recovers_its_original_body (p : Path) :
    newInner.sourceTrail atomWord [90] [91] p=oldInner.sourceTrail atomWord [90] [91] p := by
  obtain ⟨stamp,oldBody,atOld,rho,equal⟩ := LTerm.contract_copied_lambda_origin
    (beta:=Labelled.Label.atom 20) (alpha:=Labelled.Label.atom 10)
    (show ArgumentOccurrence body.erase [.body] from rfl)
    (show reduced.subterm ([.body]++[.body])=some (.lam (Labelled.Label.atom 4) newInner) from rfl)
  have oldEq := LTerm.lam.inj (Option.some.inj atOld)
  have bodies : oldInner=oldBody := oldEq.2
  rw [←bodies] at equal
  rw [equal,LTerm.sourceTrail_rename]
/-- Both the argument copy and the copied lambda are at the root; the
inverse still reconstructs the exact old argument lambda before prefixes. -/
theorem whole_root_copy_automatically_recovers_the_original_lambda :
    ∃ stamp oldBody,argument.subterm []=some (.lam stamp oldBody) ∧
      ∃ rho,(.lam (Labelled.Label.atom 4) oldInner : LTerm)=oldBody.rename rho := by
  exact LTerm.contract_copied_lambda_origin
    (beta:=Labelled.Label.atom 20) (alpha:=Labelled.Label.atom 10)
    (show ArgumentOccurrence (.var (Labelled.Label.atom 2) 0 : LTerm).erase [] from rfl)
    (show (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10)
      (.var (Labelled.Label.atom 2) 0) argument).subterm ([]++[])=some (.lam
      (((Labelled.Label.atom 20).concat (Labelled.Label.atom 10).over).concat
        (((Labelled.Label.atom 2).concat (Labelled.Label.atom 10).under).concat (Labelled.Label.atom 3)))
      (.lam (Labelled.Label.atom 4) oldInner)) from rfl)
#print axioms LTerm.CopyInterior.lambda_origin
#print axioms LTerm.contract_copied_lambda_origin
#print axioms copied_inner_lambda_automatically_recovers_its_original_body
#print axioms whole_root_copy_automatically_recovers_the_original_lambda
end Lamping.Checks.DegreeFamily.P06CopiedLambdaBodies
namespace Lamping.Checks.DegreeFamily.P06RetainedLambdaEvaluation
open Lamping Lambda Lambda.Labelled AG Graph
/-- The total lambda-origin classifier derives the retained old lambda
shape before its protected-bound-loop theorem is applied. -/
theorem total_lambda_origin_recovers_retained_body_before_loop_reuse :
    newBody.sourceTrail atoms [90] [91] [.body,.fn]=oldBody.sourceTrail atoms [90] [91] [.body,.fn] := by
  have current := (show (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) body argument).subterm []=
    some (.lam (((Labelled.Label.atom 20).concat (Labelled.Label.atom 10).over).concat (Labelled.Label.atom 1)) newBody) from rfl)
  rcases LTerm.contract_lambda_position_origins current with retained | ⟨q,r,stamp,old,path,occurs,_,_⟩
  · obtain ⟨stamp,old,oldLambda,tau,equal⟩ := retained
    have parts := LTerm.lam.inj (Option.some.inj oldLambda)
    rw [←parts.2] at equal
    exact (LTerm.retained_lambda_bound_path atoms [90] [91] tau equal
      (show ArgumentOccurrence newBody.erase [.body,.fn] from rfl)).2
  · have empty := (List.append_eq_nil_iff.mp path.symm).1
    subst q
    cases occurs
#print axioms LTerm.contract_lambda_position_origins
#print axioms total_lambda_origin_recovers_retained_body_before_loop_reuse
end Lamping.Checks.DegreeFamily.P06RetainedLambdaEvaluation

namespace Lamping.Checks.DegreeFamily.P06CopiedLambdaBodies
open Lamping Lambda Lambda.Labelled AG Graph
/-- The target inner lambda cannot come from the old body at body/body:
that old position is below a VARIABLE. The total classifier must recover
an actual argument-copy lambda, with its exact original body. -/
theorem total_lambda_origin_forces_the_actual_argument_copy :
    ∃ q r stamp oldBody,([.body,.body] : Path)=q++r ∧ ArgumentOccurrence body.erase q ∧
      argument.subterm r=some (.lam stamp oldBody) ∧ ∃ rho,newInner=oldBody.rename rho := by
  have current := (show reduced.subterm [.body,.body]=some (.lam (Labelled.Label.atom 4) newInner) from rfl)
  rcases LTerm.contract_lambda_position_origins current with ⟨stamp,old,oldLambda,_⟩ | copied
  · cases oldLambda
  · exact copied
#print axioms total_lambda_origin_forces_the_actual_argument_copy
end Lamping.Checks.DegreeFamily.P06CopiedLambdaBodies
namespace Lamping.Checks.DegreeFamily.P06DisjointLabelledSubtree
open Lamping Lambda Lambda.Labelled AG Graph
private def compound : Labelled.Label := ((Labelled.Label.atom 7).concat (Labelled.Label.atom 7).under).concat (Labelled.Label.atom 7)
private def preserved : LTerm := .lam compound (.var (Labelled.Label.atom 7) 0)
private def identity : LTerm := .lam (Labelled.Label.atom 7) (.var (Labelled.Label.atom 7) 0)
private def source : LTerm := .app (Labelled.Label.atom 7) preserved
  (.app (Labelled.Label.atom 7) identity identity)
private def target : LTerm := .app (Labelled.Label.atom 7) preserved
  (LTerm.contract (Labelled.Label.atom 7) (Labelled.Label.atom 7) (.var (Labelled.Label.atom 7) 0) identity)
private theorem event : StepAt [.arg] source target := .arg (.root _ _ _ _)
/-- A real beta in the other branch preserves the WHOLE lambda subtree,
including a compound incoming label and repeatedly named body edge. -/
theorem complete_disjoint_lambda_subtree_is_preserved :
    target.subterm [.fn]=some preserved ∧ source.subterm [.fn]=some preserved := by
  have equal := event.disjoint_subterm (position:=[.fn]) (DisjointPositions.head_ne (by decide))
  exact ⟨by rw [equal]; rfl,rfl⟩
theorem example_is_closed_and_deliberately_not_INIT : Closed source.erase ∧ ¬INIT source := by
  refine ⟨?_,?_⟩
  · change (0<1) ∧ (0<1 ∧ 0<1)
    decide
  · intro initial
    have duplicate := initial.2
    simp [source,preserved,identity,LTerm.labels] at duplicate
#print axioms StepAt.disjoint_subterm
#print axioms complete_disjoint_lambda_subtree_is_preserved
#print axioms example_is_closed_and_deliberately_not_INIT
end Lamping.Checks.DegreeFamily.P06DisjointLabelledSubtree
namespace Lamping.Checks.DegreeFamily.P06OuterBoundEvaluationOrigins
open Lamping Lambda Lambda.Labelled AG Graph
private def atoms (n : Nat) : List Nat := [n]
private def identity : LTerm := .lam (Labelled.Label.atom 6) (.var (Labelled.Label.atom 7) 0)
private def retainedSource : LTerm := .lam (Labelled.Label.atom 1)
  (.app (Labelled.Label.atom 20) (.lam (Labelled.Label.atom 10) (.var (Labelled.Label.atom 2) 2)) identity)
private def retainedTarget : LTerm := .lam (Labelled.Label.atom 1)
  (LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10) (.var (Labelled.Label.atom 2) 2) identity)
private theorem retainedEvent : StepAt [.body] retainedSource retainedTarget := .body (.root _ _ _ _)
/-- The retained targetvar1 has an actual OLD outer-bound leaf at the
shifted fn/body coordinate, with exactly the same relative body word. -/
theorem actual_retained_outer_bound_leaf_inherits_an_old_word :
    ∃ p,ArgumentOccurrence retainedSource.erase p ∧
      retainedTarget.sourceTrail atoms [10] [91] [.body]=retainedSource.sourceTrail atoms [10] [91] p := by
  have origins := retainedEvent.outer_bound_variable_evaluation_origins atoms [10] [91] rfl rfl
    (show ArgumentOccurrence retainedTarget.erase [.body] from rfl)
  rcases origins with inherited | ⟨q,r,_,occurs,_⟩
  · exact inherited
  · cases q with
    | nil => cases occurs
    | cons step rest => cases step <;> cases occurs
private def copiedSource : LTerm := .app (Labelled.Label.atom 20)
  (.lam (Labelled.Label.atom 10) (.var (Labelled.Label.atom 2) 0)) (.var (Labelled.Label.atom 4) 0)
private def copiedTarget : LTerm := LTerm.contract (Labelled.Label.atom 20) (Labelled.Label.atom 10)
  (.var (Labelled.Label.atom 2) 0) (.var (Labelled.Label.atom 4) 0)
private theorem copiedEvent : StepAt [] copiedSource copiedTarget := .root _ _ _ _
/-- A copied outer-bound argument variable is a genuine second branch.
The only old outer-bound leaf is ARG; its shorter old word cannot equal
the expanded word containing the backward principal. -/
theorem actual_copied_outer_bound_leaf_is_classified_as_copy :
    ∃ q r,([] : Path)=[]++(q++r) ∧ ArgumentOccurrence (Term.var 0) q ∧
      subtermAt (Term.var 0) r=some (.var (binderDepth ([] : Path)+binderDepth r)) := by
  have origins := copiedEvent.outer_bound_variable_evaluation_origins atoms [10] [91] rfl rfl
    (show ArgumentOccurrence copiedTarget.erase [] from rfl)
  rcases origins with ⟨p,oldLeaf,word⟩ | copied
  · cases p with
    | nil => cases oldLeaf
    | cons step rest => cases step with
      | body => cases oldLeaf
      | arg => cases rest with
        | nil => cases word
        | cons child tail => cases child <;> cases oldLeaf
      | fn => cases rest with
        | nil => cases oldLeaf
        | cons child tail => cases child with
          | fn | arg => cases oldLeaf
          | body => cases tail with
            | nil => cases oldLeaf
            | cons child suffix => cases child <;> cases oldLeaf
  · exact copied
/-- These are real contractions in CLOSED bodies of an outside lambda. -/
theorem outer_bound_examples_are_actual_closed_lambda_bodies :
    Closed (.lam (Labelled.Label.atom 50) retainedSource : LTerm).erase ∧
    Closed (.lam (Labelled.Label.atom 50) copiedSource : LTerm).erase := by
  exact ⟨by change (2<3) ∧ 0<3; decide,by change (0<2) ∧ 0<1; decide⟩
#print axioms StepAt.outer_bound_variable_evaluation_origins
#print axioms actual_retained_outer_bound_leaf_inherits_an_old_word
#print axioms actual_copied_outer_bound_leaf_is_classified_as_copy
#print axioms outer_bound_examples_are_actual_closed_lambda_bodies
end Lamping.Checks.DegreeFamily.P06OuterBoundEvaluationOrigins

namespace Lamping.Checks.DegreeFamily.P06SpecifiedBindingShell
open AG Graph Lambda
private abbrev source : Term := .lam (.var 0)
private abbrev net := (encode 7 source).net
private def shell : Context := Context.empty.cons (.o .empty)
private def tail : Context := Context.empty.cons (.star .empty)
private def input : Context := shell.replace 7 tail
private def output : Context := shell.replace 7 (tail.cons .empty)
private def parentAccess : RootAccess net (.inl ()) :=
  ⟨[.inr (.inl (.inl ()))],⟨⟨⟨input,input,.single _ _⟩,.single _⟩,rfl,⟨.lam,rfl⟩⟩⟩
private def loop : List (Endpoint net) :=
  [.inl ⟨.inl (),lamBody⟩,.inr (.inr (.inr (.inl ()),true)),
   .inl ⟨.inr (),.inl ()⟩,.inr (.inr (.inr (.inr ⟨0,rfl⟩),false))]
private theorem wholeLabels : Labelling net (parentAccess.val++loop) input output :=
  (identityBindingLoop 7 shell tail).prefix_labelling (Sum.inl ()) HEq.rfl rfl (.single _ _)
private theorem wholeForward : Forward net (parentAccess.val++loop) :=
  .node (.inl ()) (Sum.inl ()) lamBody rfl rfl ⟨rfl,rfl⟩
    (identityBindingLoop 7 shell tail).forward
private def leaf : RootAccess net (.inl ()) :=
  ⟨parentAccess.val++loop,⟨⟨⟨input,output,wholeLabels⟩,wholeForward⟩,rfl,⟨.var,rfl⟩⟩⟩
/-- Consume the generic source theorem at a genuinely nonempty lower shell
and nonempty control tail. The two full contexts differ at the Cro slot. -/
theorem actual_nonempty_assignment_specified_shell :
    Context.SameShell 7 input output ∧ input.get 0=.o .empty ∧ input≠output := by
  have actual := (encode_closed_matches source (by change 0<1; decide) 7).specified_binding_shell
    (encode_closed_transparency source (by change 0<1; decide) 7) parentAccess leaf [] [] rfl rfl rfl
    (.inl ()) (Sum.inl ()) lamBody lamBind rfl HEq.rfl HEq.rfl HEq.rfl rfl
    wholeLabels (Labelling.single _ input)
  refine ⟨actual,rfl,?_⟩
  intro equal
  have atSeven := congrArg (fun c : Context => c.get 7) equal
  change Level.star .empty=Level.empty at atSeven
  cases atSeven
/-- The actual Cro tail changes, so omitting the SAME-input premise would
allow an unrelated parentAccess assignment with a different low shell. -/
theorem unrelated_prefix_assignment_has_wrong_shell :
    Labelling net parentAccess.val Context.empty Context.empty ∧
    ¬Context.SameShell 7 Context.empty output := by
  refine ⟨.single _ _,?_⟩
  intro bad
  have zero := bad 0 (by decide)
  change Level.empty=Level.o .empty at zero
  cases zero
#print axioms Matches.specified_binding_shell
#print axioms Matches.typed_syntax_binders
#print axioms actual_nonempty_assignment_specified_shell
#print axioms unrelated_prefix_assignment_has_wrong_shell
end Lamping.Checks.DegreeFamily.P06SpecifiedBindingShell




namespace Lamping.Checks.DegreeFamily.P06PairedAnchoredReset
open AG Graph Lambda SoundnessInitialInsertion
private theorem stream : BetaDetourBlocks (encode 0 identityApp).net
    (inserted 0) (input 0) (output 0) 1 := by
  have ordinary := (bodyLabels 0).ordinary_of_forward _ (bodyForward 0)
  have tailLabels : Labelling (encode 0 identityApp).net ((edge 0).argEnd::suffix 0) (output 0) (output 0) :=
    .cons (.transparent (argumentW 0) false (output 0)) (.single _ _)
  have finish : (pre 0++(edge 0).principal++loopEdges 0).getLast?=
      some ((encode 0 identityApp).net.wire (.inl ⟨(edge 0).lam,(edge 0).lamBind⟩)) := by
    simp only [List.getLast?_append,(actualLoop 0).finish,Option.some_or]
    rfl
  have actual := BetaDetourBlocks.append_backward (encode 0 identityApp).net (edge 0) ordinary
    finish rfl (tailLabels.detour_blocks _)
  simpa only [List.append_assoc,List.singleton_append] using actual
private def front : List (Endpoint (encode 0 identityApp).net) := pre 0++(edge 0).principal
private def cut : Endpoint (encode 0 identityApp).net := .inl ⟨(edge 0).lam,(edge 0).lamBody⟩
private def post : List (Endpoint (encode 0 identityApp).net) :=
  (loopEdges 0).tail++(edge 0).reverseRoute++((edge 0).argEnd::suffix 0)
private def replacement : Context := (Context.empty.cons (.o .empty)).cons (.star .empty)
private def target : Context := (output 0).replace 1 replacement
private theorem reference : ExpandedLabelling (encode 0 identityApp).net (front++[cut]) (input 0) (input 0) := by
  have ordinary : Labelling (encode 0 identityApp).net (front++[cut]) (input 0) (input 0) :=
    (.cons ((edge 0).app_fun_turn (input 0))
    (.cons (LabelledTurn.transparent (g:=(encode 0 identityApp).net) (.inr (.inl (.inl ()))) false (input 0))
      (.cons (.node (edge 0).lam (edge 0).lamCtx (edge 0).lamBody (.direct (.lamBody (input 0))))
        (.single _ _))))
  exact ordinary.expanded
/-- The cut is INSIDE the ordinary body before its Cro, while the SAME
whole eleven-segment stream also has a complete reversed beta block.
The final high tail is genuinely nonempty. -/
theorem actual_one_block_nonempty_anchored_reset :
    ∃ newInput newCut leftCount,
      BetaDetourBlocks (encode 0 identityApp).net (inserted 0) newInput target 1 ∧
      BetaDetourBlocks (encode 0 identityApp).net (front++[cut]) newInput newCut leftCount ∧
      Context.SameShell 0 (input 0) newCut ∧ target.get 1=.star .empty := by
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  have cutPositive : flowEndpoint (encode 0 identityApp).net flow.nodes initialBoundaryPolarity flow.vertices cut=true :=
    (AtProperRole.lamBody (root:=.inl ()) (edge 0).lam (edge 0).lamBody 0
      (edge 0).lamLabel (edge 0).lamBody_role).outgoing_flow trivial flow.nodes initialBoundaryPolarity flow.vertices rfl
  have cutDepth : endpointDepth (encode 0 identityApp).net balance.nodes (boundaryDepthAt 0) balance.vertices cut=(0 : Int) :=
    AtProperRole.outgoing_depth balance (.inl ()) rfl (e:=cut) (role:=.lamBody) (index:=0)
      (AtProperRole.lamBody (root:=.inl ()) (edge 0).lam (edge 0).lamBody 0
        (edge 0).lamLabel (edge 0).lamBody_role) trivial
  obtain ⟨newInput,newCut,leftCount,whole,before,shell⟩ := stream.relabel_anchored_indexed
    flow (root:=.inl ()) rfl balance rfl (m:=0) (i:=1) rfl
    (show inserted 0=front++cut::post from rfl) cutPositive cutDepth
    (by
      intro e last
      have actual : (inserted 0).getLast?=some ((encode 0 identityApp).net.wire
          (.inl ⟨.inr (.inr (.inl ())),(.inl ())⟩)) := rfl
      have same := Option.some.inj (last.symm.trans actual)
      rw [same,balance.wiring]
      exact (AtProperRole.lamCtx (g:=(encode 0 identityApp).net) (root:=.inl ())
        (.inr (.inr (.inl ()))) (.inl ()) 1 rfl HEq.rfl).incoming_depth balance (.inl ()) trivial)
    reference (Context.sameShell_replace (output 0) replacement 1)
  exact ⟨newInput,newCut,leftCount,whole,before,shell,rfl⟩
example : (inserted 0).length=11 ∧ replacement.get 0=.star .empty ∧ target.get 0=.empty := ⟨rfl,rfl,rfl⟩
#print axioms BetaDetourBlocks.relabel_anchored_indexed
#print axioms actual_one_block_nonempty_anchored_reset
end Lamping.Checks.DegreeFamily.P06PairedAnchoredReset




namespace Lamping.Checks.DegreeFamily.P06AnchoredDescending
open AG Graph Lambda
private abbrev net := DupNet 0
private def es : List (Endpoint net) := .inr (.inl (.inl ()))::dupRightEdges
private def cut : Endpoint net := .inl ⟨.inr (.inr (.inr ())),.inl ()⟩
private def front : List (Endpoint net) := [.inr (.inl (.inl ())),
  .inl ⟨.inl (),lamBody⟩,.inr (.inr (dupBodySeam,true)),
  .inl ⟨.inr (.inl (.inl ())),appArg⟩,.inr (.inr (dupArgumentSeam,true))]
private def post : List (Endpoint net) := [.inr (.inr (dupArgumentVariableSeam,false)),
  .inl ⟨dupBracket,.inl ()⟩,.inl ⟨dupFan,.inl ()⟩,.inr (.inr (dupBindingSeam,false))]
private def output : Context := Context.empty.cons (.star (.pair .empty .empty))
private def target : Context := output.replace 1 (Context.empty.cons (.o .empty))
private theorem wholeLabels : Labelling net es Context.empty output :=
  .cons (LabelledTurn.node (g:=net) (.inl ()) (Sum.inl ()) lamBody (.direct (.lamBody Context.empty))) dupRightBindingLoop.proper
private theorem reference : ExpandedLabelling net (front++[cut]) Context.empty Context.empty := by
  have cro : Traversal 1 (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
    exact .direct (by simpa only [Context.cons_empty,empty_replace_empty] using Passage.cro (i:=1) Context.empty Context.empty)
  have ordinary : Labelling net (front++[cut]) Context.empty Context.empty :=
    .cons (LabelledTurn.node (g:=net) (.inl ()) (Sum.inl ()) lamBody (.direct (.lamBody Context.empty)))
      (.cons (LabelledTurn.transparent (g:=net) dupBodySeam false Context.empty)
        (.cons (LabelledTurn.node (g:=net) (.inr (.inl (.inl ()))) appCtx appArg (.direct (.appArg Context.empty)))
          (.cons (LabelledTurn.transparent (g:=net) dupArgumentSeam false Context.empty)
            (.cons (LabelledTurn.node (g:=net) (.inr (.inr (.inr ()))) (.inr ()) (.inl ()) cro) (.single _ _)))))
  exact ordinary.expanded
 theorem actual_cut_above_final_height :
    ∃ newInput newCut leftCount,
      BetaDetourBlocks net es newInput target 0 ∧
      BetaDetourBlocks net (front++[cut]) newInput newCut leftCount ∧
      Context.SameShell 2 Context.empty newCut ∧ newCut≠target ∧ (1<2) := by
  obtain ⟨flow⟩ := encode_flowBalance duplicatedVariable 0
  obtain ⟨balance⟩ := encode_indexed_balance duplicatedVariable 0
  have positive := wholeLabels.positive_departures flow (by
    intro e head
    have same : e=(.inr (.inl (.inl ())) : Endpoint net) := Option.some.inj head.symm
    rw [same]
    rfl)
  have cutPositive : flowEndpoint net flow.nodes initialBoundaryPolarity flow.vertices cut=true :=
    positive cut (by simp [es,dupRightEdges,cut])
  have firstWire := balance.wiring (.inl ⟨.inr (.inl (.inl ())),appArg⟩)
  change balance.vertices dupArgumentSeam=1 at firstWire
  have secondWire := balance.wiring (.inr (.inr (dupArgumentSeam,true)))
  change balance.nodes (.inr (.inr (.inr ())))=balance.vertices dupArgumentSeam at secondWire
  have cutDepth : endpointDepth net balance.nodes (boundaryDepthAt 0) balance.vertices cut=(2 : Int) := by
    change balance.nodes (.inr (.inr (.inr ())))+1=2
    omega
  obtain ⟨newInput,newCut,leftCount,whole,before,shell⟩ := (wholeLabels.detour_blocks net).relabel_anchored_indexed
    flow (root:=.inl ()) rfl balance rfl (m:=2) (i:=1) rfl
    (show es=front++cut::post from rfl) cutPositive cutDepth
    (by
      intro e last
      have actual : es.getLast?=some (net.wire (.inl ⟨(.inl ()),lamBind⟩)) := rfl
      have same := Option.some.inj (last.symm.trans actual)
      rw [same,balance.wiring]
      exact (AtProperRole.lamBind (g:=net) (root:=.inl ()) (.inl ()) lamBind 0 rfl HEq.rfl).incoming_depth balance (.inl ()) trivial)
    reference (Context.sameShell_replace output (Context.empty.cons (.o .empty)) 1)
  refine ⟨newInput,newCut,leftCount,whole,before,shell,?_,by decide⟩
  intro equal
  have low := shell 0 (by decide)
  rw [equal] at low
  change Level.empty=Level.star (.pair .empty .empty) at low
  cases low
#print axioms actual_cut_above_final_height
end Lamping.Checks.DegreeFamily.P06AnchoredDescending


namespace Lamping.Checks.DegreeFamily.P06CorridorPresentation
open AG Graph Lambda
private abbrev term : Term := .lam (.app (.lam (.var 0)) (.var 0))
private abbrev net := (encode 0 term).net
private def app : (encode 0 term).N := .inr (.inl (.inl ()))
private def lam : (encode 0 term).N := .inr (.inr (.inl (.inl ())))
private def wire : (encode 0 term).W := .inl (.inr (.inr (.inl (.inl ()))))
private def corridor : TransparentCorridor net where
  first := ⟨app,.inl ()⟩
  last := ⟨lam,.inl ()⟩
  edges := [.inl ⟨app,.inl ()⟩,.inr (.inr (wire,true))]
  start := rfl
  finish := rfl
  transparent := by
    intro e f member
    have same := List.mem_singleton.mp member
    cases same
    exact ⟨wire,false,rfl,rfl⟩
 theorem actual_nonroot_exact_ports :
    ∃ presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()),
      presentation.sourceIso.ports ⟨app,.inl ()⟩=⟨.inr (.inl ()),.inl ()⟩ ∧
      presentation.sourceIso.ports ⟨lam,.inl ()⟩=⟨.inr (.inr ()),.inl ()⟩ ∧
      GraphStep (.beta 0) (ActualNet.ofNet net) (ActualNet.ofNet presentation.site.reduce) ∧
      ∃ keptNode, presentation.sourceIso.nodes (.inl ())=.inl keptNode := by
  obtain ⟨presentation⟩ := physical_corridor_presentation net (.beta 0) corridor app lam
    (by intro same; cases same) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
  have activeNode : presentation.sourceIso.nodes app=.inr (.inl ()) :=
    (presentation.sourceIso.port_node ⟨app,.inl ()⟩).symm.trans
      (congrArg Sigma.fst presentation.active_port)
  have passiveNode : presentation.sourceIso.nodes lam=.inr (.inr ()) :=
    (presentation.sourceIso.port_node ⟨lam,.inl ()⟩).symm.trans
      (congrArg Sigma.fst presentation.passive_port)
  refine ⟨presentation,presentation.active_port,presentation.passive_port,presentation.graph_step,?_⟩
  cases mapped : presentation.sourceIso.nodes (.inl ()) with
  | inl keptNode => exact ⟨keptNode,rfl⟩
  | inr selected =>
    cases selected with
    | inl tag =>
      cases tag
      have names := presentation.sourceIso.nodes.injective (mapped.trans activeNode.symm)
      cases names
    | inr tag =>
      cases tag
      have names := presentation.sourceIso.nodes.injective (mapped.trans passiveNode.symm)
      cases names
example : subtermAt term [.body]=some (.app (.lam (.var 0)) (.var 0)) ∧ Closed term :=
  ⟨rfl,by change (0<2) ∧ 0<1; decide⟩
#print axioms physical_corridor_presentation
#print axioms physical_corridor_graph_step
#print axioms actual_nonroot_exact_ports
end Lamping.Checks.DegreeFamily.P06CorridorPresentation


namespace Lamping.Checks.DegreeFamily.P06CorridorPresentation
open Lamping.AG Lamping.Graph Lamping.Lambda
private def rootPrefix : List (Endpoint net) := [.inr (.inl (.inl ())),
  .inl ⟨.inl (),lamBody⟩,.inr (.inr (.inr (.inl ()),true))]
private theorem parentLabels : Labelling net rootPrefix Context.empty Context.empty :=
  .cons (LabelledTurn.node (g:=net) (.inl ()) (Sum.inl ()) lamBody (.direct (.lamBody _)))
    (.cons (LabelledTurn.transparent (g:=net) (.inr (.inl ())) false _) (.single _ _))
private theorem parentForward : Forward net rootPrefix :=
  .node (.inl ()) (Sum.inl ()) lamBody rfl rfl ⟨rfl,rfl⟩
    (.transparent (.inr (.inl ())) false rfl rfl (.single _))
private def parentAccess : RootAccess net (.inl ()) :=
  ⟨rootPrefix,⟨⟨⟨_,_,parentLabels⟩,parentForward⟩,rfl,⟨.app,rfl⟩⟩⟩
private theorem principalLabels : Labelling net corridor.edges Context.empty Context.empty :=
  .cons (LabelledTurn.transparent (g:=net) wire false _) (.single _ _)
private theorem principalForward : Forward net corridor.edges :=
  .transparent wire false rfl rfl (.single _)
private theorem childLabels : Labelling net (rootPrefix++corridor.edges) Context.empty Context.empty :=
  .cons (LabelledTurn.node (g:=net) (.inl ()) (Sum.inl ()) lamBody (.direct (.lamBody _)))
    (.cons (LabelledTurn.transparent (g:=net) (.inr (.inl ())) false _)
      (.cons (LabelledTurn.node (g:=net) app appCtx (Sum.inl ()) (.direct (.appFun _))) principalLabels))
private theorem childForward : Forward net (rootPrefix++corridor.edges) :=
  .node (.inl ()) (Sum.inl ()) lamBody rfl rfl ⟨rfl,rfl⟩
    (.transparent (.inr (.inl ())) false rfl rfl
      (.node app appCtx (Sum.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩ principalForward))
private def childAccess : RootAccess net (.inl ()) :=
  ⟨rootPrefix++corridor.edges,⟨⟨⟨_,_,childLabels⟩,childForward⟩,rfl,⟨.lam,rfl⟩⟩⟩
private def redex : RedexOcc term := ⟨[.body],.app (.lam (.var 0)) (.var 0),rfl,True.intro⟩
private def rich : ActualRedexAccess net (.inl ()) redex where
  connection := {
    app := app, lam := lam, appPort := .inl (), lamPort := .inl (), appIndex := 0, lamIndex := 0,
    appLabel := rfl, lamLabel := rfl, appPrincipal := HEq.rfl, lamPrincipal := HEq.rfl,
    edges := corridor.edges, proper := ⟨⟨_,_,principalLabels⟩,principalForward⟩,
    start := rfl, finish := rfl, emptyWord := rfl }
  parent := parentAccess
  child := childAccess
  ctx := appCtx
  contextPrincipal := HEq.rfl
  parentWord := rfl
  childWord := rfl
  parentFinish := rfl
  split := rfl
private theorem originalFiber : physicalBetaFiberPaths net (.inl ()) term app lam=[[.body]] := by
  have member : AtPhysicalBeta net (.inl ()) term app lam [.body] := ⟨redex,rich,rfl,rfl,rfl⟩
  have selected := (physicalBetaTest_iff net (.inl ()) term app lam [.body]).mpr member
  change ([([.body] : Path)] : List Path).filter (physicalBetaTest net (.inl ()) term app lam)=_
  simp only [List.filter_cons,selected,List.filter_nil,ite_true]
/-- Exact source fiber and its actual one-event OLD schedule survive this
nonroot presentation. This example has ONE event; it makes no shared-fiber
multi-event or target-Matches claim. -/
theorem actual_nonroot_fiber_and_schedule_transport :
    ∃ presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()),
      presentation.site.betaSyntaxFiber (.inl ()) term=[[.body]] ∧
      Marked.RelativeHistory [[.body]] (Marked.mark (presentation.site.betaSyntaxFiber (.inl ()) term) term)
        (.lam (.var 0)) ∧
      Matches presentation.site.net (.inl ()) term := by
  obtain ⟨presentation⟩ := physical_corridor_presentation net (.beta 0) corridor app lam
    (by intro same; cases same) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
  have fiber := (presentation.betaSyntaxFiber_eq (.inl ()) term).trans originalFiber
  refine ⟨presentation,fiber,?_,?_⟩
  · rw [fiber]
    exact .cons (.lam (.root [[.body]] (.var 0) (.var 0))) (.nil _)
  · exact presentation.sourceIso.matches (encode_closed_matches term (by change (0<2) ∧ 0<1; decide) 0)
/-- Renaming preserves the complete rich source provenance, including the
literal parent and child words, rather than just matching endpoint kinds. -/
theorem actual_nonroot_rich_provenance_transport
    (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :
    accessWord presentation.site.net (presentation.sourceIso.actualRedexAccess rich).parent.val=[.body] ∧
    accessWord presentation.site.net (presentation.sourceIso.actualRedexAccess rich).child.val=[.body,.fn] ∧
    (presentation.sourceIso.actualRedexAccess rich).child.val=
      (presentation.sourceIso.actualRedexAccess rich).parent.val++
        (presentation.sourceIso.actualRedexAccess rich).connection.edges :=
  ⟨(presentation.sourceIso.actualRedexAccess rich).parentWord,
   (presentation.sourceIso.actualRedexAccess rich).childWord,
   (presentation.sourceIso.actualRedexAccess rich).split⟩
#print axioms NetIso.atPhysicalBeta_iff
#print axioms NetIso.physicalBetaFiberPaths_eq
#print axioms PhysicalCorridorPresentation.betaSyntaxFiber_eq
#print axioms actual_nonroot_fiber_and_schedule_transport
#print axioms actual_nonroot_rich_provenance_transport
end Lamping.Checks.DegreeFamily.P06CorridorPresentation



namespace Lamping.Checks.DegreeFamily.P06CorridorPresentation
open Lamping.AG Lamping.Graph Lamping.Lambda Lamping.Lambda.Labelled
/-- A genuine nonroot, one-event consumer of the full P/L/Q/R history top.
The selected original pair is retained through the SAME presentation iso;
all source semantic premises are transported from the actual closed encode. -/
theorem actual_nonroot_joint_consumer :
    ∃ (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()))
      (current : LTerm) (beta : BetaEdge presentation.site.net)
      (selection : SourceEdgeSelection (initLabels term) presentation.site.net (.inl ())),
      presentation.site.betaSyntaxFiber (.inl ()) term=[[.body]] ∧
      History [[.body]] (initLabels term) current ∧current.erase=.lam (.var 0) ∧
      beta.app=.inr (.inl ()) ∧beta.lam=.inr (.inr ()) ∧
      GeneratedSyntaxPaths selection beta current ∧SupportedSyntaxBinders selection beta current ∧
      TypedSyntaxPaths selection beta current ∧TypedSyntaxBinders selection beta current := by
  obtain ⟨presentation⟩ := physical_corridor_presentation net (.beta 0) corridor app lam
    (by intro same; cases same) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
  have closed : Closed term := by change (0<2) ∧ 0<1; decide
  have fiber := (presentation.betaSyntaxFiber_eq (.inl ()) term).trans originalFiber
  have actualRelative : Marked.RelativeHistory [[.body]]
      (Marked.mark (presentation.site.betaSyntaxFiber (.inl ()) term) term) (.lam (.var 0)) := by
    rw [fiber]
    exact .cons (.lam (.root [[.body]] (.var 0) (.var 0))) (.nil _)
  obtain ⟨current,labels,erased⟩ := lift_history actualRelative.general.betaHistory (initLabels term) (by simp only [erase_initLabels,Marked.erase_mark])
  have matching := presentation.sourceIso.matches (encode_closed_matches term closed 0)
  have inputs := presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance term 0
  let flow := presentation.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance term 0
  let balance := presentation.sourceIso.indexed_balance originalBalance
  have transparency := presentation.sourceIso.transparency (encode_closed_transparency term closed 0)
  obtain ⟨beta,atApp,atLam,selection,joint⟩ := presentation.site.relative_history_typed
    (init_is_INIT term) closed matching inputs flow rfl balance rfl transparency
  exact ⟨presentation,current,beta,selection,fiber,labels,erased,atApp,atLam,joint actualRelative labels⟩
#print axioms actual_nonroot_joint_consumer
end Lamping.Checks.DegreeFamily.P06CorridorPresentation



namespace Lamping.Checks.DegreeFamily.P06CorridorPresentation
open Lamping.AG Lamping.Graph Lamping.Lambda Lamping.Lambda.Labelled
/-- The public wrapper takes the original graph's actual fiber and source
premises directly. The schedule is never changed to a newly selected fiber. -/
theorem actual_nonroot_public_wrapper_consumer :
    ∃ (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()))
      (current : LTerm) (beta : BetaEdge presentation.site.net)
      (selection : SourceEdgeSelection (initLabels term) presentation.site.net (.inl ())),
      History [[.body]] (initLabels term) current ∧current.erase=.lam (.var 0) ∧
      beta.app=.inr (.inl ()) ∧beta.lam=.inr (.inr ()) ∧
      GeneratedSyntaxPaths selection beta current ∧SupportedSyntaxBinders selection beta current ∧
      TypedSyntaxPaths selection beta current ∧TypedSyntaxBinders selection beta current := by
  obtain ⟨presentation⟩ := physical_corridor_presentation net (.beta 0) corridor app lam
    (by intro same; cases same) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
  have actualRelative : Marked.RelativeHistory [[.body]]
      (Marked.mark (physicalBetaFiberPaths net (.inl ()) term app lam) term) (.lam (.var 0)) := by
    rw [originalFiber]
    exact .cons (.lam (.root [[.body]] (.var 0) (.var 0))) (.nil _)
  obtain ⟨current,labels,erased⟩ := lift_history actualRelative.general.betaHistory (initLabels term)
    (by simp only [erase_initLabels,Marked.erase_mark])
  have closed : Closed term := by change (0<2) ∧ 0<1; decide
  obtain ⟨flow⟩ := encode_flowBalance term 0
  obtain ⟨balance⟩ := encode_indexed_balance term 0
  obtain ⟨beta,atApp,atLam,selection,joint⟩ := presentation.relative_history_typed
    (init_is_INIT term) closed (encode_closed_matches term closed 0)
    (encode_closed_independence term closed 0).rootInputs flow rfl balance rfl
    (encode_closed_transparency term closed 0)
  exact ⟨presentation,current,beta,selection,labels,erased,atApp,atLam,joint actualRelative labels⟩
#print axioms PhysicalCorridorPresentation.relative_history_typed
#print axioms actual_nonroot_public_wrapper_consumer
end Lamping.Checks.DegreeFamily.P06CorridorPresentation


namespace Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical
open Lamping Lambda Lambda.Labelled AG Graph
/-- A real source lambda access recovers its actual original function edge
and physical-fiber degree, with no INIT premise on the source API. -/
theorem actual_source_lambda_provenance :
    (⟨Labelled.Label.atom 1,.appFn (Labelled.Label.atom 0),.lamContext (Labelled.Label.atom 1)⟩ : SourceEdge)
      ∈sourceEdges [] .external original ∧
    SelectedDegree original (actualBetaSite.betaSyntaxFiber (.inl ()) original.erase) (Labelled.Label.atom 1) := by
  obtain ⟨position,appStamp,argument,positionEq,headLookup,functionEdge,selected⟩ :=
    actualBetaSite.source_lambda_selected_origin matching SoundnessBetaAncestor.actualFlow rfl
      (oldPosition:= [.fn]) (origin:=Labelled.Label.atom 1) (oldBody:=.var (.atom 2) 0) rfl child rfl rfl
  have lengths := congrArg List.length positionEq
  have empty : position=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons,List.length_nil,List.length_append] at lengths; omega)
  subst position
  have headEq : original=.app appStamp (.lam (.atom 1) (.var (.atom 2) 0)) argument :=
    Option.some.inj headLookup
  have stampEq : (.atom 0 : Labelled.Label)=appStamp := congrArg LTerm.label headEq
  subst appStamp
  exact ⟨functionEdge,selected⟩
private theorem completeNormal : Marked.Normal (.lam (.var 0)) := True.intro
private def selectedLambdaRealizes : SourcePortRealizes original actualBetaSite.net (.inl ())
    (.lamContext (.atom 1)) (.inl ⟨.inr (.inr ()),.inl ()⟩) :=
  .lamContext (p:=[.fn]) (body:=.var (.atom 2) 0) rfl child rfl rfl HEq.rfl rfl
/-- The actually surviving lambda has a compound label; excluding the old
selected lambda origin is not merely an atomic-current-label result. -/
theorem actual_compound_lambda_excludes_selected_origin :
    fullLabel.lastAtom≠(Labelled.Label.atom 1).lastAtom := by
  intro same
  exact actualBetaSite.complete_no_realized_lambda_origin (init_is_INIT identityApp) matching
    SoundnessBetaAncestor.actualFlow rfl actualRelative completeNormal labelHistory
    selectedLambdaRealizes (p:=[]) (stamp:=fullLabel) (body:=.var (.atom 4) 0) rfl same
 theorem actual_current_lambda_label_is_compound : fullLabel.lastAtom=some 3 ∧ ¬IsAtomic fullLabel := by
  refine ⟨rfl,?_⟩
  rintro ⟨n,atomic⟩
  cases atomic
/-- The actual whole trail is built from the same relative/label histories.
Its own terminal realization excludes selected lambda ctx after completion. -/
theorem actual_completed_lambda_trail_avoids_selected_context :
    ∃ (beta : BetaEdge actualBetaSite.net) (finish : SourcePort)
      (trail : PhysicalSyntaxTrail original (.inl ()) beta [] .external developed []
        (.lam fullLabel (.var (.atom 4) 0)) finish),
      trail.toEndpoint≠(.inl ⟨.inr (.inr ()),.inl ()⟩ : Endpoint actualBetaSite.net) := by
  obtain ⟨beta,_app,_lam,_selection,allPositions⟩ := actualBetaSite.relative_development_shared_syntax_evaluation
    (init_is_INIT identityApp) (by change (0<1) ∧ 0<1; decide) matching actualRelative labelHistory
  obtain ⟨finish,trail,_evaluation⟩ := allPositions (p:=[]) (sub:=.lam fullLabel (.var (.atom 4) 0)) rfl
  refine ⟨beta,finish,trail,?_⟩
  intro atSelected
  exact actualBetaSite.complete_lambda_trail_exclusion (init_is_INIT identityApp) matching
    SoundnessBetaAncestor.actualFlow rfl actualRelative completeNormal labelHistory trail atSelected
#print axioms PathSite.source_lambda_selected_origin
#print axioms PathSite.complete_no_source_lambda_origin
#print axioms PathSite.complete_no_realized_lambda_origin
#print axioms PathSite.complete_lambda_trail_exclusion
#print axioms actual_source_lambda_provenance
#print axioms actual_compound_lambda_excludes_selected_origin
#print axioms actual_current_lambda_label_is_compound
#print axioms actual_completed_lambda_trail_avoids_selected_context
end Lamping.Checks.DegreeFamily.P06SelectedDegreePhysical




namespace Lamping.Checks.DegreeFamily.P06ForwardCoverageMatching
open Lamping AG Graph Lambda
/-- The generic assembly consumes real ordinary accesses and a raw suffix
at the variable. Neither an observation nor its uniqueness is supplied. -/
theorem actual_identity_kind_and_raw_binding_coverage :
    Matches Soundness.identityNet (.inl ()) (.lam (.var 0)) := by
  have closed : Closed (.lam (.var 0)) := by exact Nat.zero_lt_succ 0
  have inputs := (encode_closed_independence (.lam (.var 0)) closed 0).rootInputs
  obtain ⟨balance⟩ := encode_indexed_balance (.lam (.var 0)) 0
  apply inputs.matches_of_kind_binding_coverage (balance.nesting (.inl ()) rfl)
    (encode_closed_transparency (.lam (.var 0)) closed 0)
  rintro ⟨p,valid⟩
  cases p with
  | nil => exact ⟨Soundness.identityRootAccess,.lam (.var 0),rfl,rfl,rfl,True.intro⟩
  | cons step rest =>
    cases step with
    | fn | arg => cases valid
    | body =>
      cases rest with
      | nil => exact ⟨Soundness.identityVariableAccess,.var 0,rfl,rfl,rfl,Soundness.identity_binding⟩
      | cons step rest => cases step <;> cases valid
/-- Same kind is insufficient to choose a de Bruijn index. The same actual
variable access cannot supply the raw suffix for the wrong index. -/
theorem actual_same_kind_wrong_index_has_no_binding_suffix :
    accessKind Soundness.identityNet Soundness.identityVariableEdges=some .var ∧
    ¬BindingSuffix Soundness.identityNet Soundness.identityVariableEdges 1 := by
  refine ⟨rfl,fun suffix => ?_⟩
  have impossible := Soundness.identity_binding_index 1 suffix
  cases impossible
#print axioms RootInputs.matches_of_kind_binding_coverage
#print axioms PathSite.beta_matches_of_kind_binding_coverage
#print axioms actual_identity_kind_and_raw_binding_coverage
#print axioms actual_same_kind_wrong_index_has_no_binding_suffix
end Lamping.Checks.DegreeFamily.P06ForwardCoverageMatching

namespace Lamping.Checks.DegreeFamily.P06ForwardCoverageMatching
open Lamping AG Graph Lambda
/-- The public beta assembly is exercised on the genuine one-W I I site.
Its forward geometry remains the explicit hypothesis; this test does not
claim to have constructed those target accesses for arbitrary t. -/
theorem actual_beta_site_assembly (t : Term)
    (coverage : ∀ position : Position t, ∃ (access : RootAccess actualBetaSite.reduce (.inl ())) (u : Term),
      subtermAt t position.val=some u ∧ accessWord actualBetaSite.reduce access.val=position.val ∧
      accessKind actualBetaSite.reduce access.val=some (syntaxShape u).kind ∧
      (match u with | .var k => BindingSuffix actualBetaSite.reduce access.val k | _ => True)) :
    Matches actualBetaSite.reduce (.inl ()) t := by
  have closed : Closed identityApp := by exact ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have inputs := betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨originalBalance⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance originalBalance
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  exact actualBetaSite.beta_matches_of_kind_binding_coverage SoundnessBetaAncestor.actualFlow (.inl ())
    rfl balance rfl inputs transparency t coverage
#print axioms actual_beta_site_assembly
end Lamping.Checks.DegreeFamily.P06ForwardCoverageMatching


namespace Lamping.Checks.DegreeFamily.P06ClosedVariableBinders
open Lamping Lambda Lambda.Labelled
private abbrev same : Labelled.Label := .atom 7
private def repeated : LTerm := .lam same (.lam same (.app same (.var same 1) (.var same 0)))
private theorem closedRepeated : Closed repeated.erase := by change (1<2) ∧0<2; decide
/-- Identical lambda labels do not choose the lexical binder. The actual
index and literal path select the outer occurrence. -/
theorem repeated_labels_outer_occurrence :
    ∃ parent tail origin body,parent=[] ∧tail=[.body,.fn] ∧
      repeated.subterm parent=some (.lam origin body) ∧
      subtermAt body.erase tail=some (.var (binderDepth tail)) := by
  obtain ⟨parent,tail,origin,body,split,atParent,_leaf,bound,depth⟩ :=
    repeated.closed_variable_binder closedRepeated (show repeated.subterm [.body,.body,.fn]=some (.var same 1) from rfl)
  have unique := binding_prefix_depth_unique
    (show parent++(.body::tail)=[]++(.body::[.body,.fn]) from split.symm) (show binderDepth tail=binderDepth [.body,.fn] from depth.symm)
  exact ⟨parent,tail,origin,body,unique.1,unique.2,atParent,bound⟩
/-- The adjacent index-zero leaf instead selects the inner occurrence,
although its label is equal to the outer one's label. -/
theorem repeated_labels_inner_occurrence :
    ∃ parent tail origin body,parent=[.body] ∧tail=[.arg] ∧
      repeated.subterm parent=some (.lam origin body) ∧
      subtermAt body.erase tail=some (.var (binderDepth tail)) := by
  obtain ⟨parent,tail,origin,body,split,atParent,_leaf,bound,depth⟩ :=
    repeated.closed_variable_binder closedRepeated (show repeated.subterm [.body,.body,.arg]=some (.var same 0) from rfl)
  have unique := binding_prefix_depth_unique
    (show parent++(.body::tail)=[.body]++(.body::[.arg]) from split.symm) (show binderDepth tail=binderDepth [.arg] from depth.symm)
  exact ⟨parent,tail,origin,body,unique.1,unique.2,atParent,bound⟩
private def captureSource : LTerm := .lam same
  (.app same (.lam same (.lam same (.var same 1))) (.var same 0))
private def captureTarget : LTerm := .lam same (LTerm.contract same same (.lam same (.var same 1)) (.var same 0))
private def copied : Labelled.Label := (same.concat same.under).concat same
private theorem captureHistory : History [[.body]] captureSource captureTarget :=
  .cons (.body (.root _ _ _ _)) (.nil _)
/-- An actual non-INIT labelled capture-avoiding step shifts var0 to var1.
History.closed supplies the reduct's scope; the generic wrapper then finds
its true outer binder without a freshly assigned labelling. -/
theorem actual_capture_history_recovers_outer_lambda :
    Closed captureTarget.erase ∧∃ parent tail origin body,parent=[] ∧tail=[.body] ∧
      captureTarget.subterm parent=some (.lam origin body) ∧
      body.subterm tail=some (.var copied 1) := by
  have sourceClosed : Closed captureSource.erase := by change (1<3) ∧0<1; decide
  have targetClosed := captureHistory.closed sourceClosed
  refine ⟨targetClosed,?_⟩
  obtain ⟨parent,tail,origin,body,split,atParent,leaf,_bound,depth⟩ :=
    captureTarget.closed_variable_binder targetClosed
      (show captureTarget.subterm [.body,.body]=some (.var copied 1) from rfl)
  have unique := binding_prefix_depth_unique
    (show parent++(.body::tail)=[]++(.body::[.body]) from split.symm) (show binderDepth tail=binderDepth [.body] from depth.symm)
  exact ⟨parent,tail,origin,body,unique.1,unique.2,atParent,leaf⟩
theorem current_closed_is_necessary :
    ¬∃ parent tail origin body,([] : Path)=parent++(.body::tail) ∧
      (.var same 0 : LTerm).subterm parent=some (.lam origin body) := by
  rintro ⟨parent,tail,origin,body,split,_⟩
  have lengths := congrArg List.length split
  simp only [List.length_nil,List.length_append,List.length_cons] at lengths
  omega
#print axioms LTerm.closed_variable_binder
#print axioms History.closed
#print axioms repeated_labels_outer_occurrence
#print axioms repeated_labels_inner_occurrence
#print axioms actual_capture_history_recovers_outer_lambda
#print axioms current_closed_is_necessary
end Lamping.Checks.DegreeFamily.P06ClosedVariableBinders


namespace Lamping.Checks.DegreeFamily.P06ProperSourceReaderExpressions
open Lamping AG Graph Lambda AG.Marker
inductive GarbageNode where
  | lam | writer | reader | rootDead | lambdaDead
  deriving DecidableEq
instance : FiniteNames GarbageNode := ⟨[.lam,.writer,.reader,.rootDead,.lambdaDead],by intro n;cases n <;> simp⟩
private def garbageLabels : GarbageNode → Label signature
  | .lam => label .lam 1
  | .writer | .reader => label .cro 0
  | .rootDead | .lambdaDead => garbage
/-- The lambda/Cro component is physically disconnected from the root. -/
private def garbageNet : Net signature GarbageNode Unit Empty where
  label := garbageLabels
  wire := {
    mate := fun e => match e with
      | .inl ⟨.lam,.inl ()⟩ => .inl ⟨.lambdaDead,()⟩
      | .inl ⟨.lam,.inr false⟩ => .inl ⟨.reader,.inr ()⟩
      | .inl ⟨.lam,.inr true⟩ => .inl ⟨.writer,.inr ()⟩
      | .inl ⟨.writer,.inl ()⟩ => .inl ⟨.reader,.inl ()⟩
      | .inl ⟨.writer,.inr ()⟩ => .inl ⟨.lam,.inr true⟩
      | .inl ⟨.reader,.inl ()⟩ => .inl ⟨.writer,.inl ()⟩
      | .inl ⟨.reader,.inr ()⟩ => .inl ⟨.lam,.inr false⟩
      | .inl ⟨.rootDead,()⟩ => .inr (.inl ())
      | .inl ⟨.lambdaDead,()⟩ => .inl ⟨.lam,.inl ()⟩
      | .inr (.inl ()) => .inl ⟨.rootDead,()⟩
      | .inr (.inr ⟨e,_⟩) => nomatch e
    involutive := by
      rintro (⟨n,p⟩ | (u | ⟨e,d⟩))
      · cases n <;> cases p <;> first | rfl | rename_i d; cases d <;> rfl
      · cases u; rfl
      · exact nomatch e
    fixedPointFree := by
      rintro (⟨n,p⟩ | (u | ⟨e,d⟩))
      · cases n <;> cases p <;> first | (intro h;cases h) | rename_i d;cases d <;> (intro h;cases h)
      · intro h;cases h
      · exact nomatch e }
private def garbagePath : List (Endpoint garbageNet) :=
  [.inl ⟨.lam,lamBody⟩,.inl ⟨.writer,.inl ()⟩,.inl ⟨.reader,.inr ()⟩]
private theorem garbageLabelsTotal (a : Context) : Labelling garbageNet garbagePath a a := by
  have direct : Traversal 0 (.op .cro) (.inr ()) (.inl ()) a (a.cons .empty) := by
    simpa only [Context.replace_zero] using Traversal.direct (Passage.cro (i:=0) Context.empty a)
  exact .cons (LabelledTurn.node (g:=garbageNet) .writer (.inr ()) (.inl ()) direct)
    (.cons (LabelledTurn.node (g:=garbageNet) .reader (.inl ()) (.inr ()) direct.reverse) (.single _ _))
theorem garbage_component_has_no_root_access : ¬Nonempty (RootAccess garbageNet ()) := by
  rintro ⟨⟨es,⟨⟨⟨a,b,labels⟩,_⟩,head,terminal⟩⟩⟩
  cases labels with
  | single e a =>
    have same : e=.inr (.inl ()) := Option.some.inj head
    subst e
    obtain ⟨kind,impossible⟩ := terminal
    cases impossible
  | cons turn after =>
    have same := Option.some.inj head
    subst same
    change LabelledTurn garbageNet (.inl ⟨GarbageNode.rootDead,()⟩) _ _ _ at turn
    obtain ⟨q,_atQ,rule⟩ := turn.from_node GarbageNode.rootDead () rfl
    have samePort : (():Port (garbageNet.label GarbageNode.rootDead).sort)=q := by
      change (():Unit)=q
      cases q
      rfl
    exact rule.distinct samePort
/-- The constant-empty reader is reflected at its actual ordinal in an
unreachable proper-source component. Empty has no fictitious writer tag. -/
theorem garbage_reader_is_constant_empty :
    ∃ expressions : List ExprContext,∃ here,
      (∀ input,ContextTrace garbageNet garbagePath (expressions.map (fun c => c.eval input))) ∧
      expressions[1]?=some here ∧here.get 0=.empty := by
  obtain ⟨expressions,_first,traces⟩ := Marker.Labelling.expression_trace garbagePath ExprContext.initial (by
    intro input; exact ⟨input,by simpa only [ExprContext.eval_initial] using garbageLabelsTotal input⟩)
  have lengths := (traces Context.empty).length garbageNet
  rw [List.length_map] at lengths
  have valid : 1<expressions.length := by change 3=expressions.length at lengths;omega
  let here := expressions[1]
  have point : expressions[1]?=some here := List.getElem?_eq_getElem valid
  have shape := expression_reader_at_ordinal (g:=garbageNet) traces 1 GarbageNode.reader (.inl ()) (.inr ())
    (e:=.inl ⟨.writer,.inl ()⟩) rfl rfl rfl point
  exact ⟨expressions,here,traces,point,shape⟩
/-- A genuinely old full I theorem supplies the source-tail symbolic family
at a non-root lambda-body departure, rather than caller-given totality. -/
theorem actual_nonroot_source_I_expression_trace (a : Context) :
    ∃ expressions : List ExprContext,
      expressions.head?=some (ExprContext.sourceTail a 0) ∧
      ∀ input,ContextTrace Soundness.identityNet (Soundness.identityVariableEdges.tail)
        (expressions.map (fun c => c.eval input)) := by
  have loop := identityBindingLoop 0 Context.empty a
  have closed : Closed (.lam (.var 0)) := Nat.zero_lt_succ 0
  have independence := encode_closed_independence (.lam (.var 0)) closed 0
  have labels : Labelling Soundness.identityNet Soundness.identityVariableEdges.tail a (a.cons .empty) := by
    simpa only [Context.replace_zero] using loop.proper
  exact Marker.Independence.source_expression_trace independence rfl rfl
    (AtProperRole.lamBody (g:=Soundness.identityNet) (root:=.inl ()) (.inl ()) lamBody 0 rfl HEq.rfl) trivial
    (AtProperRole.lamBind (g:=Soundness.identityNet) (root:=.inl ()) (.inl ()) lamBind 0 rfl HEq.rfl) trivial loop.forward labels
#print axioms Independence.source_expression_trace
#print axioms expression_reader_at_ordinal
#print axioms source_expression_prefix
#print axioms garbage_component_has_no_root_access
#print axioms garbage_reader_is_constant_empty
#print axioms actual_nonroot_source_I_expression_trace
end Lamping.Checks.DegreeFamily.P06ProperSourceReaderExpressions





namespace Lamping.Checks.DegreeFamily.P06ProperSourceReaderExpressions
open Lamping AG Graph Lambda AG.Marker
/-- The original reference is a.tail m, with the actual replace-tail
identity; it is not silently identified with a whole root input. -/
theorem source_reference_is_exact (a : Context) (m : Nat) :
    (ExprContext.sourceTail a m).eval (a.tail m)=a := by
  rw [ExprContext.eval_sourceTail,Context.replace_tail]
theorem a_free_variable_is_not_a_constant_empty_reader :
    ¬ExprInputShape 0 (.op .cro) (.inl ()) (.inr ()) ExprContext.initial := by
  change (LevelExpr.var 0)≠LevelExpr.empty
  decide
/-- A primitive Cro0→inverseCro0 garbage path really tests empty after a
writer turn; the symbolic reader test is not obtained from Tagged origins. -/
theorem constant_empty_has_no_tagged_writer :
    TaggedLevel.empty.origins=[] ∧LevelExpr.literal Level.empty=LevelExpr.empty := ⟨rfl,rfl⟩
#print axioms source_reference_is_exact
#print axioms a_free_variable_is_not_a_constant_empty_reader
#print axioms constant_empty_has_no_tagged_writer
end Lamping.Checks.DegreeFamily.P06ProperSourceReaderExpressions

namespace Lamping.Checks.DegreeFamily.P06ProperNodeAncestry
open Lamping AG Graph
private def kept : Empty → Label signature := Empty.elim
/-- A complete literal rule LHS, with every auxiliary attached to its actual
boundary name. No root semantics or hypothesis about a desired parent. -/
private def directSite (s : Schema) : Site s kept (B:=s.Frontier) (W:=Empty) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl k,_⟩ => nomatch k
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inl ⟨.inr (.inr ()),.inl ()⟩
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inl ⟨.inr (.inl _),.inr q⟩ => .inr (.inl (.inl q))
      | .inl ⟨.inr (.inr _),.inr q⟩ => .inr (.inl (.inr q))
      | .inr (.inl (.inl q)) => .inl ⟨.inr (.inl ()),.inr q⟩
      | .inr (.inl (.inr q)) => .inl ⟨.inr (.inr ()),.inr q⟩
      | .inr (.inr ⟨.inl e,_⟩) => nomatch e
      | .inr (.inr ⟨.inr e,_⟩) => nomatch e
    involutive := by
      rintro (⟨k|(u|u),p⟩|((q|q)|⟨e|e,d⟩))
      · exact nomatch k
      · cases p <;> rfl
      · cases p <;> rfl
      · rfl
      · rfl
      · exact nomatch e
      · exact nomatch e
    fixedPointFree := by
      rintro (⟨k|(u|u),p⟩|((q|q)|⟨e|e,d⟩))
      · exact nomatch k
      · cases p <;> (intro h;cases h)
      · cases p <;> (intro h;cases h)
      · intro h;cases h
      · intro h;cases h
      · exact nomatch e
      · exact nomatch e }
  principal := rfl
private def pathSite (s : Schema) := (directSite s).pathSite
private abbrev fanSchema : Schema := .fanAction .lam 0 2 (by decide)
private abbrev croSchema : Schema := .croAction .app 0 2 (by decide)
private abbrev braSchema : Schema := .braAction .lam 0 2 (by decide)
/-- Actual two distinct fan copies have the SAME physical passive parent. -/
theorem actual_fan_both_branches (branch : Bool) :
    PhysicalNodeParent fanSchema (ActualNet.ofNet (pathSite fanSchema).net)
      (ActualNet.ofNet (pathSite fanSchema).reduce) (.inr (.inr ())) (.inr (.inl branch)) ∧
    (pathSite fanSchema).net.label (.inr (.inr ()))=label .lam 2 ∧
    (pathSite fanSchema).reduce.label (.inr (.inl branch))=label .lam 2 := by
  refine ⟨?_,rfl,rfl⟩
  exact .atSite kept (pathSite fanSchema) (.refl _) (.refl _)
    _ _ _ _ rfl rfl (.copied _ (.fan .lam 0 2 (by decide) branch))
theorem actual_fan_copies_are_distinct :
    (.inr (.inl false) : (ActualNet.ofNet (pathSite fanSchema).reduce).Node)≠.inr (.inl true) := by intro impossible;cases impossible
/-- The actual Cro copy changes j to j-1, rather than preserving a guessed
physical source level. -/
theorem actual_cro_passive_copy :
    PhysicalNodeParent croSchema (ActualNet.ofNet (pathSite croSchema).net)
      (ActualNet.ofNet (pathSite croSchema).reduce) (.inr (.inr ())) (.inr (.inl ())) ∧
    (pathSite croSchema).net.label (.inr (.inr ()))=label .app 2 ∧
    (pathSite croSchema).reduce.label (.inr (.inl ()))=label .app 1 := by
  refine ⟨?_,rfl,rfl⟩
  exact .atSite kept (pathSite croSchema) (.refl _) (.refl _)
    _ _ _ _ rfl rfl (.copied _ (.cro .app 0 2 (by decide)))
theorem actual_bra_passive_copy :
    PhysicalNodeParent braSchema (ActualNet.ofNet (pathSite braSchema).net)
      (ActualNet.ofNet (pathSite braSchema).reduce) (.inr (.inr ())) (.inr (.inl ())) ∧
    (pathSite braSchema).net.label (.inr (.inr ()))=label .lam 2 ∧
    (pathSite braSchema).reduce.label (.inr (.inl ()))=label .lam 3 := by
  refine ⟨?_,rfl,rfl⟩
  exact .atSite kept (pathSite braSchema) (.refl _) (.refl _)
    _ _ _ _ rfl rfl (.copied _ (.bra .lam 0 2 (by decide)))
/-- The constructor classifies the true rule step without a caller parent;
the trace theorem is consumed on the same one-event physical trace. -/
theorem actual_fan_graphstep_and_trace (branch : Bool) :
    (∃ parent,PhysicalNodeParent fanSchema (ActualNet.ofNet (pathSite fanSchema).net)
      (ActualNet.ofNet (pathSite fanSchema).reduce) parent (.inr (.inl branch)) ∧
      ((pathSite fanSchema).net.label parent).sort=.op .lam) ∧
    (∃ parent,ProperNodeAncestry (ActualNet.ofNet (pathSite fanSchema).net)
      (ActualNet.ofNet (pathSite fanSchema).reduce) [fanSchema] parent (.inr (.inl branch)) ∧
      ((pathSite fanSchema).net.label parent).sort=.op .lam) := by
  have step := GraphStep.site kept (pathSite fanSchema)
  exact ⟨step.proper_node_parent _ (Or.inr rfl) rfl,
    (GraphTrace.single step).proper_node_ancestry _ (Or.inr rfl) rfl⟩
#print axioms GraphStep.proper_node_parent
#print axioms GraphTrace.proper_node_ancestry
#print axioms actual_fan_both_branches
#print axioms actual_fan_copies_are_distinct
#print axioms actual_cro_passive_copy
#print axioms actual_bra_passive_copy
#print axioms actual_fan_graphstep_and_trace
end Lamping.Checks.DegreeFamily.P06ProperNodeAncestry


namespace Lamping.Checks.DegreeFamily.P06ProperNodeAncestry
open Lamping AG Graph
private abbrev fanTarget := (pathSite fanSchema).reduce
private def flipCopies : Bij (Empty⊕(Bool⊕Bool)) (Empty⊕(Bool⊕Bool)) where
  toFun := fun n => match n with | .inl e => nomatch e | .inr (.inl b) => .inr (.inl (!b)) | .inr (.inr q) => .inr (.inr q)
  invFun := fun n => match n with | .inl e => nomatch e | .inr (.inl b) => .inr (.inl (!b)) | .inr (.inr q) => .inr (.inr q)
  left_inv := by rintro (e|(b|q)); exact nomatch e;cases b <;> rfl;rfl
  right_inv := by rintro (e|(b|q)); exact nomatch e;cases b <;> rfl;rfl
private theorem flipCompatible (n : Empty⊕(Bool⊕Bool)) : fanTarget.label (flipCopies n)=fanTarget.label n := by
  rcases n with e | (b|q)
  · exact nomatch e
  · rfl
  · rfl
private noncomputable def renamed := fanTarget.reindex fanTarget.label flipCopies (Bij.refl _) flipCompatible
private noncomputable def after : NetIso fanTarget renamed :=
  (fanTarget.reindexIso fanTarget.label flipCopies (Bij.refl _) flipCompatible).symm
/-- A true schema event followed by a nontrivial boundary-fixed carrier
renaming exercises both finite-chain and zero-step-iso constructors. -/
theorem actual_copy_trace_with_carrier_renaming (branch : Bool) :
    ∃ parent,ProperNodeAncestry (ActualNet.ofNet (pathSite fanSchema).net)
      (ActualNet.ofNet renamed) [fanSchema] parent (after.nodes (.inr (.inl branch))) ∧
      ((pathSite fanSchema).net.label parent).sort=.op .lam := by
  have trace : GraphTrace (ActualNet.ofNet (pathSite fanSchema).net)
      (ActualNet.ofNet renamed) [fanSchema] :=
    .cons (GraphStep.site kept (pathSite fanSchema)) (.iso after)
  apply trace.proper_node_ancestry _ (Or.inr rfl)
  change (renamed.label (after.nodes (.inr (.inl branch)))).sort=.op .lam
  rw [after.labels]
  rfl
theorem actual_renaming_exchanges_the_two_copies :
    after.nodes (.inr (.inl false))=.inr (.inl true) ∧
    after.nodes (.inr (.inl true))=.inr (.inl false) := ⟨rfl,rfl⟩
/-- A fresh active control has no passive-copy ancestry, so the classifier
cannot accidentally use it as a proper child. -/
theorem fresh_fan_is_not_a_passive_copy (q : Bool) :
    ¬RightPassiveCopy fanSchema (.inr q) := by intro copy;cases copy
#print axioms actual_copy_trace_with_carrier_renaming
#print axioms actual_renaming_exchanges_the_two_copies
#print axioms fresh_fan_is_not_a_passive_copy
end Lamping.Checks.DegreeFamily.P06ProperNodeAncestry




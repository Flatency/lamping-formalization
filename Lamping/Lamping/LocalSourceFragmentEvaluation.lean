import Lamping.Lamping.FragmentRelabelling
import Lamping.Lambda.BetaPreimageErasure
import Lamping.Lambda.UniformAnnotatedOrigins
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original current : LTerm}

private theorem edge_atom (env ctx) (term : LTerm) : (sourceEdge env ctx term).atom=term.label := by
  cases term <;> rfl

/-- The actual local INIT cell locates its unique occurrence. Only then
are its literal physical segments aligned with a separately annotated
matched term at that SAME position. No global-label lookup is performed. -/
theorem SourceEdgeSelection.atomWord_occurrence_segments
    (selection : SourceEdgeSelection original g root) (initial : INIT original)
    (matching : Matches g root original.erase) (currentMatching : Matches g root current.erase)
    (occurrence : SourceSubterm [] .external original p env ctx sub)
    (atomic : sub.label=Labelled.Label.atom n)
    (fragment : OccurrenceFragment current g root p) :
    selection.atomWord n=fragment.fragment.segments := by
  have member : sourceEdge env ctx sub∈sourceEdges [] .external original :=
    occurrence.edges_subset _ (by cases sub <;> simp [sourceEdges,sourceEdge])
  let cell : {edge : SourceEdge // edge∈sourceEdges [] .external original} :=
    ⟨sourceEdge env ctx sub,member⟩
  have atomicCell : cell.val.atom=Labelled.Label.atom n := (edge_atom env ctx sub).trans atomic
  have wordEq := selection.atomWord_cell initial cell atomicCell
  cases chosenEq : selection.chosen cell with
  | mk q selected =>
    rw [chosenEq] at wordEq
    obtain ⟨actualEnv,actualCtx,actualSub,actualOccurrence,edgeEq⟩ := selected.occurrence
    have labels : actualSub.label=sub.label := by
      have atoms := congrArg SourceEdge.atom edgeEq
      exact (edge_atom actualEnv actualCtx actualSub).symm.trans (atoms.trans (edge_atom env ctx sub))
    have positionEq := LTerm.subterm_label_injective original initial.2 actualOccurrence.lookup occurrence.lookup labels
    subst q
    obtain ⟨rfl,rfl,rfl⟩ := actualOccurrence.same_occurrence occurrence
    let localFragment : OccurrenceFragment original g root p :=
      ⟨actualSub,actualEnv,actualCtx,actualOccurrence,selected⟩
    calc
      selection.atomWord n=selected.segments := wordEq
      _=localFragment.fragment.segments := rfl
      _=fragment.fragment.segments :=
        OccurrenceFragment.segments_unique_of_matches matching currentMatching localFragment fragment

/-- The local source annotation supplies its own atom; the chosen beta is
used only by the existing label evaluator. No degree or family history is
identified with this local annotation. -/
theorem SourceEdgeSelection.evalLabel_occurrence_segments
    (selection : SourceEdgeSelection original g root) (initial : INIT original)
    (matching : Matches g root original.erase) (currentMatching : Matches g root current.erase)
    (occurrence : SourceSubterm [] .external original p env ctx sub)
    (fragment : OccurrenceFragment current g root p) (beta : BetaEdge g) :
    selection.evalLabel beta sub.label=fragment.fragment.segments := by
  obtain ⟨n,atomic⟩ := initial.1 _ (LTerm.label_mem_of_subterm occurrence.lookup)
  have actual := selection.atomWord_occurrence_segments initial matching currentMatching occurrence atomic fragment
  simpa only [SourceEdgeSelection.evalLabel,atomic,Label.sourceWord,Labelled.Label.atom,Letter.sourceWord] using actual
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

theorem SourceEdgeSelection.uncreated_local_evaluation
    {source localTarget body argument node : LTerm} {site position oldPosition : Path} {beta alpha : Labelled.Label}
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (matching : Matches g root source.erase)
    (localStep : StepAt site (initLabels source.erase) localTarget)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site position oldPosition)
    (uncreated : ¬BetaCreatedIncoming body site position)
    (lookup : localTarget.subterm position=some node)
    (oldFragment : OccurrenceFragment source g root oldPosition) (physical : BetaEdge g) :
    selection.evalLabel physical node.label=oldFragment.fragment.segments := by
  obtain ⟨localBeta,localAlpha,localBody,localArgument,localRedex,_contractum⟩ := localStep.head_lookups
  have sameAt : subtermAt source.erase site=subtermAt (initLabels source.erase).erase site := by
    rw [erase_initLabels]
  simp only [←LTerm.erase_subterm,redex,localRedex,Option.map_some,LTerm.erase] at sameAt
  have sameHeads := Term.app.inj (Option.some.inj sameAt)
  have bodySame := Term.lam.inj sameHeads.1
  have localOrigin := origin.reannotate bodySame sameHeads.2
  have localUncreated := fun created=>(uncreated ((betaCreatedIncoming_of_same_erase bodySame).mpr created))
  obtain ⟨old,oldLookup,labelEq⟩ := localStep.beta_preimage_label localRedex localOrigin lookup localUncreated
  obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup (initLabels source.erase) oldLookup [] .external
  have localMatching : Matches g root (initLabels source.erase).erase := by
    simpa only [erase_initLabels] using matching
  have evaluation := selection.evalLabel_occurrence_segments (init_is_INIT source.erase)
    localMatching matching occurrence oldFragment physical
  rw [←labelEq]
  exact evaluation
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- The SAME whole OLD schedule preserves an old reading's local evaluator
at an actual global old coordinate. The global operational trace is returned
so another occurrence construction can identify that coordinate by trace
uniqueness. No intermediate source matches, INIT or freshness is required.
This identifies an evaluator block, not a target-selector path residual. -/
theorem SourceEdgeSelection.marker_free_local_evaluation
    {F ps : List Path} {m n : Marked} {d : Path →Option Labelled.Label}
    {source target localTarget current localCurrent : LTerm} {edge : Path} {degree : Labelled.Label}
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (matching : Matches g root source.erase)
    (old : Marked.RelativeOldHistory F ps m n) (aligned : DegreeAligned d m source)
    (labels : History ps source target)
    (localLabels : History ps (initLabels source.erase) localTarget)
    (selected : ∀ path∈F,d path=some degree)
    (lookup : target.subterm edge=some current) (localLookup : localTarget.subterm edge=some localCurrent)
    (safe : current.label.OuterBarsSafe (fun payload=>payload≠degree)) (physical : BetaEdge g) :
    ∃ oldPosition oldNode,source.subterm oldPosition=some oldNode ∧
      BetaNodeHistoryPreimage labels edge oldPosition ∧
      ∀ oldFragment : OccurrenceFragment source g root oldPosition,
        selection.evalLabel physical localCurrent.label=oldFragment.fragment.segments := by
  obtain ⟨oldPosition,oldNode,localOld,oldLookup,localOldLookup,_globalLabel,localLabel,trace⟩ :=
    old.marker_free_paired_origin aligned labels localLabels (erase_initLabels source.erase).symm
      selected lookup localLookup safe
  obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup (initLabels source.erase) localOldLookup [] .external
  have localMatching : Matches g root (initLabels source.erase).erase := by
    simpa only [erase_initLabels] using matching
  refine ⟨oldPosition,oldNode,oldLookup,trace,?_⟩
  intro oldFragment
  rw [←localLabel]
  exact selection.evalLabel_occurrence_segments (init_is_INIT source.erase) localMatching matching
    occurrence oldFragment physical
end
end Lamping.AG

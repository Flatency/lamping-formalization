import Lamping.Lamping.PathSiteBetaAncestor
import Lamping.Lambda.LabelPaths

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Fold a fixed directed-wire assignment over the literal physical list. -/
def physicalOriginalWord (weights : Endpoint g → EdgeWord)
    (es : List (Endpoint g)) : EdgeWord := es.flatMap weights

/-- Reversing a wire reverses order and orientation of its original atoms. -/
def OriginalWordReversal (weights : Endpoint g → EdgeWord) : Prop :=
  ∀ e, weights (g.wire e)=EdgeWord.reverse (weights e)

theorem physicalOriginalWord_reverse
    (weights : Endpoint g → EdgeWord) (reverseLaw : OriginalWordReversal weights)
    (es : List (Endpoint g)) :
    physicalOriginalWord weights (reverseEdges es)=
      EdgeWord.reverse (physicalOriginalWord weights es) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    calc
      physicalOriginalWord weights (reverseEdges (e::es))=
          physicalOriginalWord weights (reverseEdges es)++weights (g.wire e) := by
        simp only [reverseEdges,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
          physicalOriginalWord,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      _=EdgeWord.reverse (physicalOriginalWord weights es)++EdgeWord.reverse (weights e) := by
        rw [ih,reverseLaw]
      _=EdgeWord.reverse (physicalOriginalWord weights (e::es)) := by
        exact (EdgeWord.reverse_append (weights e) (physicalOriginalWord weights es)).symm
end

/-- Actual beta RHS: the APP frontiers carry the principal word and the
lambda frontiers its reverse. No label decoder is assumed. -/
def betaRhsOriginalWord (i : Nat) (principal : EdgeWord) :
    Endpoint (Schema.beta i).right.net → EdgeWord
  | .inl ⟨node,_⟩ => nomatch node
  | .inr (.inl (.inl _)) => principal
  | .inr (.inl (.inr _)) => EdgeWord.reverse principal
  | .inr (.inr (vertex,_)) => nomatch vertex

private theorem beta_rhs_reversal (i : Nat) (principal : EdgeWord) :
    OriginalWordReversal (g:=(Schema.beta i).right.net) (betaRhsOriginalWord i principal) := by
  rintro (⟨node,p⟩ | ((a|b) | ⟨vertex,d⟩))
  · exact nomatch node
  · cases a <;> rfl
  · cases b <;> exact (EdgeWord.reverse_reverse principal).symm
  · exact nomatch vertex

private abbrev betaWordRhs (i : Nat) := (Schema.beta i).right.net

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
local notation "rhs" => betaWordRhs i

/-- The assignment is constructed on the actual plugged target. Cut wires
retain their old values; only RHS reconnection wires receive the principal. -/
def PathSite.betaOriginalWordWeights (edge : BetaEdge site.net)
    (weights : Endpoint site.net → EdgeWord) : Endpoint site.reduce → EdgeWord :=
  fun e => Sum.elim (fun outside => weights (site.outsideEnd outside))
    (betaRhsOriginalWord i (physicalOriginalWord weights edge.principal))
    ((plugEnd (cut).label (rhs).label).invFun e)

theorem PathSite.beta_original_word_reversal
    (edge : BetaEdge site.net) (weights : Endpoint site.net → EdgeWord)
    (reverseLaw : OriginalWordReversal weights) :
    OriginalWordReversal (g:=site.reduce) (site.betaOriginalWordWeights edge weights) := by
  intro e
  have wiring : (plugEnd (cut).label (rhs).label).invFun (site.reduce.wire e)=
      ((cut).wire.sum (rhs).wire) ((plugEnd (cut).label (rhs).label).invFun e) := by
    change (plugEnd (cut).label (rhs).label).invFun
      ((plugEnd (cut).label (rhs).label)
        (((cut).wire.sum (rhs).wire) ((plugEnd (cut).label (rhs).label).invFun e)))=_
    exact (plugEnd (cut).label (rhs).label).left_inv _
  unfold PathSite.betaOriginalWordWeights
  rw [wiring]
  cases actual : (plugEnd (cut).label (rhs).label).invFun e with
  | inl outside =>
    change weights (site.outsideEnd ((cut).wire outside))=
      EdgeWord.reverse (weights (site.outsideEnd outside))
    rw [←site.outsideEnd_wire]
    exact reverseLaw _
  | inr inside =>
    exact beta_rhs_reversal i (physicalOriginalWord weights edge.principal) inside

/-- All four real residual constructors preserve the complete original
word. Their literal reconnection blocks determine both signs internally. -/
theorem BetaPathResidual.original_word_transport
    {edge : BetaEdge site.net} (weights : Endpoint site.net → EdgeWord)
    (reverseLaw : OriginalWordReversal weights) {raw old}
    (relation : BetaPathResidual site edge raw old) :
    raw.flatMap (Sum.elim (fun outside => weights (site.outsideEnd outside))
      (betaRhsOriginalWord i (physicalOriginalWord weights edge.principal)))=
      physicalOriginalWord weights old := by
  induction relation with
  | single outside => rfl
  | outside rest ih =>
    simp only [List.flatMap_cons,Sum.elim_inl,physicalOriginalWord] at ih ⊢
    rw [ih]
  | context arrival rest ih =>
    simp only [List.flatMap_cons,Sum.elim_inl,Sum.elim_inr,betaRhsOriginalWord,
      physicalOriginalWord,List.flatMap_append] at ih ⊢
    rw [ih]
  | binding arrival rest ih =>
    have reversePrincipal := physicalOriginalWord_reverse weights reverseLaw edge.principal
    change physicalOriginalWord weights edge.reverseRoute=
      EdgeWord.reverse (physicalOriginalWord weights edge.principal) at reversePrincipal
    simp only [List.flatMap_cons,Sum.elim_inl,Sum.elim_inr,betaRhsOriginalWord] at ih ⊢
    rw [ih]
    simpa only [physicalOriginalWord,List.flatMap_cons,List.flatMap_append] using
      congrArg (fun middle => _++(middle++_)) reversePrincipal.symm

/-- Reindex the raw result to the full actual target list, retaining all
plugged frontier endpoints and their literal order. -/
theorem BetaPathResidual.original_word_transport_actual
    {edge : BetaEdge site.net} (weights : Endpoint site.net → EdgeWord)
    (reverseLaw : OriginalWordReversal weights) {es : List (Endpoint site.reduce)} {old}
    (relation : BetaPathResidual site edge
      (es.map (plugEnd (cut).label (rhs).label).invFun) old) :
    physicalOriginalWord (site.betaOriginalWordWeights edge weights) es=
      physicalOriginalWord weights old := by
  have transported := relation.original_word_transport site weights reverseLaw
  simpa only [physicalOriginalWord,List.flatMap_map,PathSite.betaOriginalWordWeights,
    Function.comp_def] using transported
end

#print axioms physicalOriginalWord_reverse
#print axioms PathSite.beta_original_word_reversal
#print axioms BetaPathResidual.original_word_transport
#print axioms BetaPathResidual.original_word_transport_actual
end Lamping.AG

import Lamping.Lamping.BetaOriginalWordTransport
import Lamping.Lamping.CancellationFrontGeometry
import Lamping.Lamping.CancellationFragmentTransport

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- Cancellation preserves the branch and exchanges the side. -/
def cancellationRhsOriginalWord (s : Schema) (principal : EdgeWord) :
    Endpoint s.right.net → EdgeWord :=
  match s with
  | .fanCancel _ => fun
    | .inl ⟨n,_⟩ => nomatch n
    | .inr (.inl (.inl _)) => principal
    | .inr (.inl (.inr _)) => EdgeWord.reverse principal
    | .inr (.inr (v,_)) => nomatch v
  | .croCancel _ => fun
    | .inl ⟨n,_⟩ => nomatch n
    | .inr (.inl (.inl _)) => principal
    | .inr (.inl (.inr _)) => EdgeWord.reverse principal
    | .inr (.inr (v,_)) => nomatch v
  | .braCancel _ => fun
    | .inl ⟨n,_⟩ => nomatch n
    | .inr (.inl (.inl _)) => principal
    | .inr (.inl (.inr _)) => EdgeWord.reverse principal
    | .inr (.inr (v,_)) => nomatch v
  | _ => fun _ => []

theorem cancellation_rhs_original_word_reversal {s : Schema}
    (cancel : IsCancellation s) (principal : EdgeWord) :
    OriginalWordReversal (g:=s.right.net) (cancellationRhsOriginalWord s principal) := by
  cases cancel
  all_goals
    rintro (⟨n,p⟩ | ((a|b) | ⟨v,d⟩))
    · exact nomatch n
    · rfl
    · exact (EdgeWord.reverse_reverse principal).symm
    · exact nomatch v

section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

def PathSite.cancellationOriginalWordWeights (principal : SiteActionPrincipal site)
    (weights : Endpoint site.net → EdgeWord) : Endpoint site.reduce → EdgeWord :=
  fun e => Sum.elim (fun outside => weights (site.outsideEnd outside))
    (cancellationRhsOriginalWord s (physicalOriginalWord weights principal.edges))
    ((plugEnd (cut).label s.right.net.label).invFun e)

theorem PathSite.cancellation_original_word_reversal (cancel : IsCancellation s)
    (principal : SiteActionPrincipal site) (weights : Endpoint site.net → EdgeWord)
    (reverseLaw : OriginalWordReversal weights) :
    OriginalWordReversal (g:=site.reduce) (site.cancellationOriginalWordWeights principal weights) := by
  intro e
  have wiring : (plugEnd (cut).label s.right.net.label).invFun (site.reduce.wire e)=
      ((cut).wire.sum s.right.net.wire) ((plugEnd (cut).label s.right.net.label).invFun e) := by
    change (plugEnd (cut).label s.right.net.label).invFun
      ((plugEnd (cut).label s.right.net.label)
        (((cut).wire.sum s.right.net.wire) ((plugEnd (cut).label s.right.net.label).invFun e)))=_
    exact (plugEnd (cut).label s.right.net.label).left_inv _
  unfold PathSite.cancellationOriginalWordWeights
  rw [wiring]
  cases actual : (plugEnd (cut).label s.right.net.label).invFun e with
  | inl outside =>
    change weights (site.outsideEnd ((cut).wire outside))=
      EdgeWord.reverse (weights (site.outsideEnd outside))
    rw [←site.outsideEnd_wire]
    exact reverseLaw _
  | inr inside => exact cancellation_rhs_original_word_reversal cancel _ inside

/-- The actual canonical list retains its inherited entry and its SAME principal. -/
theorem cancellation_front_original_word (cancel : IsCancellation s)
    (principal : SiteActionPrincipal site) (weights : Endpoint site.net → EdgeWord)
    (reverseLaw : OriginalWordReversal weights) (f : s.Frontier) :
    physicalOriginalWord weights (site.cancellation_canonical_fronts principal.edges f)=
      weights (site.outsideEnd ((cut).wire (.inr (.inl (.inr f))))) ++
        cancellationRhsOriginalWord s (physicalOriginalWord weights principal.edges) (.inr (.inl f)) := by
  rw [cancellation_fronts_literal]
  have reversed := physicalOriginalWord_reverse weights reverseLaw principal.edges
  cases cancel <;> cases f <;>
    simp only [physicalOriginalWord,List.flatMap_cons,cancellationFrontRoute,
      cancellationRhsOriginalWord] at reversed ⊢
  all_goals first | rfl | exact congrArg (List.append _) reversed

/-- Reduce the three actual empty RHS schemas before the raw residual induction. -/
theorem CanonicalCancellationResidual.original_word_transport
    (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights)
    {es : List (Endpoint site.reduce)} {old : List (Endpoint site.net)}
    (relation : CanonicalCancellationResidual site
      (site.cancellation_canonical_fronts principal.edges) es old) :
    (es.map (plugEnd (cut).label s.right.net.label).invFun).flatMap
      (Sum.elim (fun outside => weights (site.outsideEnd outside))
        (cancellationRhsOriginalWord s (physicalOriginalWord weights principal.edges)))=
      physicalOriginalWord weights old := by
  cases cancel
  all_goals
    change CanonicalWireResidual _ _ _ _ _ _ _ at relation
    generalize mapped : es.map (plugEnd _ _).invFun=raw at relation ⊢
    clear mapped
    induction relation with
    | single e => rfl
    | outside rest ih =>
      simp only [List.flatMap_cons,Sum.elim_inl,physicalOriginalWord] at ih ⊢
      rw [ih]
    | @through e f tail old start rest ih =>
      have front := cancellation_front_original_word site (by constructor) principal weights reverseLaw f
      have literal := cancellation_fronts_literal site principal f
      rw [literal,List.cons_append,List.head?_cons] at start
      have entry := Option.some.inj start
      simp only [List.flatMap_cons,Sum.elim_inl,Sum.elim_inr,
        physicalOriginalWord,List.flatMap_append] at ih ⊢
      rw [ih]
      rw [entry] at front
      change _=physicalOriginalWord weights
        (site.cancellation_canonical_fronts principal.edges f)++physicalOriginalWord weights old
      rw [front,List.append_assoc]
      rfl

theorem CanonicalCancellationResidual.original_word_transport_actual
    (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights)
    {es : List (Endpoint site.reduce)} {old : List (Endpoint site.net)}
    (relation : CanonicalCancellationResidual site
      (site.cancellation_canonical_fronts principal.edges) es old) :
    physicalOriginalWord (site.cancellationOriginalWordWeights principal weights) es=
      physicalOriginalWord weights old := by
  have transported := relation.original_word_transport site cancel principal weights reverseLaw
  simpa only [physicalOriginalWord,List.flatMap_map,PathSite.cancellationOriginalWordWeights,
    Function.comp_def] using transported
end

#print axioms cancellation_rhs_original_word_reversal
#print axioms PathSite.cancellation_original_word_reversal
#print axioms cancellation_front_original_word
#print axioms CanonicalCancellationResidual.original_word_transport
#print axioms CanonicalCancellationResidual.original_word_transport_actual
end Lamping.AG

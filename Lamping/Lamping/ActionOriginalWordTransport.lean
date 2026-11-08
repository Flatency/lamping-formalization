import Lamping.Lamping.BetaOriginalWordTransport
import Lamping.Lamping.ActionCanonicalAssembly
import Lamping.Lamping.ActionLambdaCanonicalAccess
import Lamping.Lamping.FanAppCopiedFunctionCuts

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

def fanRhsOriginalWord {f : Op} {i j : Nat} (principal : EdgeWord) :
    Endpoint (fanRight f i j) → EdgeWord
  | .inl ⟨.inl _,.inl _⟩ => EdgeWord.reverse principal
  | .inr (.inl (.inl _)) => principal
  | _ => []

def unaryRhsOriginalWord {c f : Op} {single : Bij Unit (Aux c)} {i k : Nat}
    (principal : EdgeWord) : Endpoint (unaryRightCore c f single i k) → EdgeWord
  | .inl ⟨.inl _,.inl _⟩ => EdgeWord.reverse principal
  | .inr (.inl (.inl _)) => principal
  | _ => []

private theorem fan_rhs_reversal {f : Op} {i j : Nat} (principal : EdgeWord) :
    OriginalWordReversal (g:=fanRight f i j) (fanRhsOriginalWord principal) := by
  rintro (⟨b|q,p⟩ | ((b|q)|⟨v,d⟩))
  · cases p with
    | inl u => cases u; exact (EdgeWord.reverse_reverse principal).symm
    | inr a => rfl
  · cases p <;> rfl
  · rfl
  · rfl
  · exact nomatch v

private theorem unary_rhs_reversal {c f : Op} {single : Bij Unit (Aux c)} {i k : Nat}
    (principal : EdgeWord) : OriginalWordReversal
      (g:=unaryRightCore c f single i k) (unaryRhsOriginalWord principal) := by
  rintro (⟨u|q,p⟩ | ((u|q)|⟨v,d⟩))
  · cases p with
    | inl a => cases a; exact (EdgeWord.reverse_reverse principal).symm
    | inr a => rfl
  · cases p <;> rfl
  · rfl
  · rfl
  · exact nomatch v

def actionRhsOriginalWord {s : Schema} (_action : IsAction s) (principal : EdgeWord) :
    Endpoint s.right.net → EdgeWord :=
  match s with
  | .fanAction _ _ _ _ => fanRhsOriginalWord principal
  | .croAction _ _ _ _ => unaryRhsOriginalWord principal
  | .braAction _ _ _ _ => unaryRhsOriginalWord principal
  | _ => fun _ => []

private theorem action_rhs_reversal {s : Schema} (action : IsAction s) (principal : EdgeWord) :
    OriginalWordReversal (g:=s.right.net) (actionRhsOriginalWord action principal) := by
  cases action with
  | fan => exact fan_rhs_reversal principal
  | cro => exact unary_rhs_reversal principal
  | bra => exact unary_rhs_reversal principal

section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

def PathSite.actionOriginalWordWeights (action : IsAction s)
    (principal : SiteActionPrincipal site) (weights : Endpoint site.net → EdgeWord) :
    Endpoint site.reduce → EdgeWord :=
  fun e => Sum.elim (fun outside => weights (site.outsideEnd outside))
    (actionRhsOriginalWord action (physicalOriginalWord weights principal.edges))
    ((plugEnd (cut).label s.right.net.label).invFun e)

theorem PathSite.action_original_word_reversal (action : IsAction s)
    (principal : SiteActionPrincipal site) (weights : Endpoint site.net → EdgeWord)
    (reverseLaw : OriginalWordReversal weights) :
    OriginalWordReversal (g:=site.reduce) (site.actionOriginalWordWeights action principal weights) := by
  intro e
  have wiring : (plugEnd (cut).label s.right.net.label).invFun (site.reduce.wire e)=
      ((cut).wire.sum s.right.net.wire) ((plugEnd (cut).label s.right.net.label).invFun e) := by
    change (plugEnd (cut).label s.right.net.label).invFun
      ((plugEnd (cut).label s.right.net.label)
        (((cut).wire.sum s.right.net.wire) ((plugEnd (cut).label s.right.net.label).invFun e)))=_
    exact (plugEnd (cut).label s.right.net.label).left_inv _
  unfold PathSite.actionOriginalWordWeights
  rw [wiring]
  cases actual : (plugEnd (cut).label s.right.net.label).invFun e with
  | inl outside =>
    change weights (site.outsideEnd ((cut).wire outside))=
      EdgeWord.reverse (weights (site.outsideEnd outside))
    rw [←site.outsideEnd_wire]
    exact reverseLaw _
  | inr inside => exact action_rhs_reversal action _ inside
end

section Fan
variable {f : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction f i j lt) V) site.closed

theorem FanCanonicalLocal.original_word_seam {principal : SiteActionPrincipal site}
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights)
    {inside old} (relation : FanCanonicalLocal site principal inside old)
    (first last : Endpoint cut)
    (head : old.head?=some (site.outsideEnd first))
    (finish : old.getLast?=some (site.outsideEnd last)) :
    weights (site.outsideEnd first) ++
      physicalOriginalWord (fanRhsOriginalWord (physicalOriginalWord weights principal.edges)) inside ++
      weights (site.outsideEnd last) = physicalOriginalWord weights old := by
  simp only [OriginalWordReversal] at reverseLaw
  cases relation with
  | cross branch q =>
    simp only [SiteActionPrincipal.crossing,List.head?_cons] at head
    simp only [SiteActionPrincipal.crossing,List.getLast?_cons,List.getLast?_append,
      List.getLast?_cons,List.getLast?_nil,Option.some_or] at finish
    rw [←Option.some.inj head,←Option.some.inj finish]
    simp [physicalOriginalWord,fanCrossEdges,fanRhsOriginalWord,SiteActionPrincipal.crossing,
      List.append_assoc]
  | backward branch q =>
    simp only [reverseEdges,List.head?_map,List.head?_reverse,SiteActionPrincipal.crossing,
      List.getLast?_cons,List.getLast?_append,List.getLast?_nil,Option.some_or,
      Option.map_some] at head
    simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,
      SiteActionPrincipal.crossing,List.head?_cons,Option.map_some,Pairing.involutive] at finish
    rw [←Option.some.inj head,←Option.some.inj finish]
    rw [physicalOriginalWord_reverse _ (fan_rhs_reversal _) _,
      physicalOriginalWord_reverse _ reverseLaw _]
    simp [physicalOriginalWord,fanCrossEdges,fanRhsOriginalWord,SiteActionPrincipal.crossing,
      EdgeWord.reverse_append,reverseLaw,List.append_assoc]
  | passive branch p q =>
    simp only [PathSite.passiveCanonical,List.head?_cons] at head
    simp only [PathSite.passiveCanonical,List.getLast?_cons_cons,List.getLast?_singleton] at finish
    rw [←Option.some.inj head,←Option.some.inj finish]
    simp [physicalOriginalWord,fanPassiveEdges,fanRhsOriginalWord,PathSite.passiveCanonical]
end Fan

section Unary
variable {s : Schema} {k : Nat}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V)) (single : Bij Unit (Aux s.active))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

theorem UnaryCanonicalLocal.original_word_seam {principal : SiteActionPrincipal site}
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights)
    {inside old} (relation : UnaryCanonicalLocal (k:=k) site single principal inside old)
    (first last : Endpoint cut)
    (head : old.head?=some (site.outsideEnd first))
    (finish : old.getLast?=some (site.outsideEnd last)) :
    weights (site.outsideEnd first) ++
      physicalOriginalWord (unaryRhsOriginalWord (physicalOriginalWord weights principal.edges)) inside ++
      weights (site.outsideEnd last) = physicalOriginalWord weights old := by
  simp only [OriginalWordReversal] at reverseLaw
  cases relation with
  | cross q =>
    simp only [SiteActionPrincipal.crossing,List.head?_cons] at head
    simp only [SiteActionPrincipal.crossing,List.getLast?_cons,List.getLast?_append,
      List.getLast?_cons,List.getLast?_nil,Option.some_or] at finish
    rw [←Option.some.inj head,←Option.some.inj finish]
    simp [physicalOriginalWord,unaryCrossEdges,unaryRhsOriginalWord,SiteActionPrincipal.crossing,
      List.append_assoc]
  | backward q =>
    simp only [reverseEdges,List.head?_map,List.head?_reverse,SiteActionPrincipal.crossing,
      List.getLast?_cons,List.getLast?_append,List.getLast?_nil,Option.some_or,
      Option.map_some] at head
    simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,
      SiteActionPrincipal.crossing,List.head?_cons,Option.map_some,Pairing.involutive] at finish
    rw [←Option.some.inj head,←Option.some.inj finish]
    rw [physicalOriginalWord_reverse _ (unary_rhs_reversal _) _,
      physicalOriginalWord_reverse _ reverseLaw _]
    simp [physicalOriginalWord,unaryCrossEdges,unaryRhsOriginalWord,SiteActionPrincipal.crossing,
      EdgeWord.reverse_append,reverseLaw,List.append_assoc]
  | passive p q =>
    simp only [PathSite.passiveCanonical,List.head?_cons] at head
    simp only [PathSite.passiveCanonical,List.getLast?_cons_cons,List.getLast?_singleton] at finish
    rw [←Option.some.inj head,←Option.some.inj finish]
    simp [physicalOriginalWord,unaryPassiveEdges,unaryRhsOriginalWord,PathSite.passiveCanonical]
end Unary

section Blocks
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem action_word_seam (action : IsAction s) {principal : SiteActionPrincipal site}
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights)
    {inside old} (relation : ActionCanonicalLocal site principal inside old)
    (first last : Endpoint cut) (head : old.head?=some (site.outsideEnd first))
    (finish : old.getLast?=some (site.outsideEnd last)) :
    weights (site.outsideEnd first) ++
      physicalOriginalWord (actionRhsOriginalWord action (physicalOriginalWord weights principal.edges)) inside ++
      weights (site.outsideEnd last) = physicalOriginalWord weights old := by
  cases relation with
  | fan rel => cases action; exact rel.original_word_seam _ weights reverseLaw first last head finish
  | cro rel => cases action; exact rel.original_word_seam _ (Bij.refl _) weights reverseLaw first last head finish
  | bra rel => cases action; exact rel.original_word_seam _ (Bij.refl _) weights reverseLaw first last head finish

theorem ActionCanonicalBlocks.original_word_transport (action : IsAction s)
    {principal : SiteActionPrincipal site} (weights : Endpoint site.net → EdgeWord)
    (reverseLaw : OriginalWordReversal weights) {raw old}
    (relation : ActionCanonicalBlocks site principal raw old) :
    raw.flatMap (Sum.elim (fun outside => weights (site.outsideEnd outside))
      (actionRhsOriginalWord action (physicalOriginalWord weights principal.edges))) =
      physicalOriginalWord weights old := by
  induction relation with
  | single e => rfl
  | outside rest ih =>
    simp only [List.flatMap_cons,Sum.elim_inl,physicalOriginalWord] at ih ⊢
    rw [ih]
  | @through e exit tail old inside front route start rest ih =>
    have seam := action_word_seam site action weights reverseLaw route e
      (.inr (.inl (.inr exit))) start (by simp)
    simp only [physicalOriginalWord,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil] at seam
    have frontEq := List.append_cancel_right seam
    simp only [List.flatMap_cons,List.flatMap_append,List.flatMap_map,Sum.elim_inl,
      Sum.elim_inr,physicalOriginalWord] at ih ⊢
    rw [ih,←List.append_assoc,frontEq]

theorem ActionCanonicalBlocks.original_word_transport_actual (action : IsAction s)
    {principal : SiteActionPrincipal site} (weights : Endpoint site.net → EdgeWord)
    (reverseLaw : OriginalWordReversal weights) {es : List (Endpoint site.reduce)} {old}
    (relation : ActionCanonicalBlocks site principal
      (es.map (plugEnd (cut).label s.right.net.label).invFun) old) :
    physicalOriginalWord (site.actionOriginalWordWeights action principal weights) es =
      physicalOriginalWord weights old := by
  have transported := relation.original_word_transport site action weights reverseLaw
  simpa only [physicalOriginalWord,List.flatMap_map,PathSite.actionOriginalWordWeights,
    Function.comp_def] using transported
end Blocks

section PartialLambda
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- The real copied-lambda BODY completion inherits its old BODY tail.
The two fresh padding weights are zero; only the SAME inherited tail is cancelled. -/
theorem PathSite.cro_lambda_original_word_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b)
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights) :
    physicalOriginalWord (site.actionOriginalWordWeights (.cro .lam i j lt) principal weights) target.val =
      physicalOriginalWord weights source.val := by
  have relation := site.cro_lambda_canonical_access flow root positive matching principal source target word finish labels
  have folded := relation.original_word_transport site (.cro .lam i j lt) weights reverseLaw
  have same :
      physicalOriginalWord (site.actionOriginalWordWeights (.cro .lam i j lt) principal weights) target.val ++
        weights (.inl ⟨.inr (.inr ()),.inr true⟩) =
      physicalOriginalWord weights source.val ++ weights (.inl ⟨.inr (.inr ()),.inr true⟩) := by
    simpa only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.flatMap_map,
      Sum.elim_inr,Sum.elim_inl,physicalOriginalWord,PathSite.actionOriginalWordWeights,
      actionRhsOriginalWord,unaryRhsOriginalWord,List.nil_append,List.append_nil,Function.comp_def]
      using folded
  exact List.append_cancel_right same
end PartialLambda

section PartialApp
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))

/-- APP.FN completion retains reverse P and the inherited active auxiliary.
Neither is assumed empty when cancelling the common completion. -/
theorem PathSite.fan_app_function_original_word_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (branch : Bool)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b)
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights) :
    physicalOriginalWord (site.actionOriginalWordWeights (.fan .app i j lt) principal weights) target.val =
      physicalOriginalWord weights source.val := by
  have relation := site.fan_app_function_padding_access flow root positive matching principal source target word branch finish labels
  have folded := relation.original_word_transport site (.fan .app i j lt) weights reverseLaw
  have backwards := physicalOriginalWord_reverse weights reverseLaw principal.edges
  have same :
      physicalOriginalWord (site.actionOriginalWordWeights (.fan .app i j lt) principal weights) target.val ++
        (EdgeWord.reverse (physicalOriginalWord weights principal.edges) ++
          weights (.inl ⟨.inr (.inl ()),.inr branch⟩)) =
      physicalOriginalWord weights source.val ++
        (EdgeWord.reverse (physicalOriginalWord weights principal.edges) ++
          weights (.inl ⟨.inr (.inl ()),.inr branch⟩)) := by
    simp only [physicalOriginalWord,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.flatMap_map,Sum.elim_inr,Sum.elim_inl,actionRhsOriginalWord,fanRhsOriginalWord,
      List.append_nil] at folded
    change _ = (physicalOriginalWord weights source.val ++
      physicalOriginalWord weights (reverseEdges principal.edges)) ++ _ at folded
    rw [backwards,List.append_assoc] at folded
    simpa only [physicalOriginalWord,PathSite.actionOriginalWordWeights,Function.comp_def] using folded
  exact List.append_cancel_right same
end PartialApp

#print axioms PathSite.action_original_word_reversal
#print axioms FanCanonicalLocal.original_word_seam
#print axioms UnaryCanonicalLocal.original_word_seam
#print axioms ActionCanonicalBlocks.original_word_transport
#print axioms ActionCanonicalBlocks.original_word_transport_actual
#print axioms PathSite.cro_lambda_original_word_access
#print axioms PathSite.fan_app_function_original_word_access
end Lamping.AG

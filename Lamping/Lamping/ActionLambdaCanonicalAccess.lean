import Lamping.Lamping.ActionPendingLambdaPadding
import Lamping.Lamping.ActionPendingLambdaBranches
import Lamping.Lamping.BackwardPathDeterminism
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.lam i j lt) V) site.closed
private abbrev lambdaRight (i j : Nat) (lt : i<j) := (Schema.croAction .lam i j lt).right.net
local notation "rhs" => lambdaRight i j lt

/-- Identify the canonical old padding with THIS supplied source access.
The padding labels are constructed from the real writer and lambda-body turn. -/
theorem PathSite.cro_lambda_canonical_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ActionCanonicalBlocks site principal
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))])
      (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩]) := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut rhs first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node cut rhs first actualHead
    (.inl ()) (.inl ()) finish
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  obtain ⟨entry,shape,contexts⟩ := unaryRight_lam_context_prefix .cro (Bij.refl Unit) i (j-1)
    pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead insideFinish
  have rule : Traversal i (.op .cro) (.inr ()) (.inl ()) pending.middle (InitialOffsets.croAt i b) := by
    rw [contexts];exact .direct (InitialOffsets.Event.apply_rel (.cro i) b)
  obtain ⟨pre,oldLabels,oldHead,_preLast,oldLast,words⟩ := pending.fixed_principal_ancestor site
    (.cro .lam i j lt) principal first rawHead () (by rw [entry];rfl)
    (by rw [shape];rfl) rule
  rw [plug_decomposition_flatten] at words
  have rooted : (pre++principal.edges).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,oldHead,Option.some_or];rfl
  have typed : accessKind site.net (pre++principal.edges)=some AccessKind.lam := by
    simp only [accessKind,oldLast,Option.bind_some,Pairing.involutive]
    rfl
  have oldForward := oldLabels.root_forward_of_flow flow root rooted positive
  let oldAccess : RootAccess site.net root :=
    ⟨pre++principal.edges,⟨⟨⟨a,InitialOffsets.croAt i b,oldLabels⟩,oldForward⟩,rooted,⟨_,typed⟩⟩⟩
  have sameAccess : oldAccess=source := matching.accessWord_injective (words.symm.trans word.symm)
  have literal : pre++principal.edges=source.val := congrArg Subtype.val sameAccess
  rw [literal] at oldLabels oldLast
  have padLabels : Labelling site.net (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩]) a
      (InitialOffsets.croAt i b) :=
    oldLabels.append_seam (.single _ _) (by
      intro e f atLast atHead
      have eEq := Option.some.inj (atLast.symm.trans oldLast)
      have fEq := Option.some.inj atHead
      subst e;subst f
      rw [Pairing.involutive]
      exact LabelledTurn.node (g:=site.net) (.inr (.inr ())) _ _ (.direct (.lamBody _)))
  obtain ⟨old,relation,canonLabels,canonHead,canonLast,_whole⟩ :=
    pending.cro_lambda_canonical_completion site principal first rawHead insideFinish
  have padHead : (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩] : List (Endpoint site.net)).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,source.property.2.1,Option.some_or]
  have canonRoot : old.head?=some (.inr (.inl root)) := canonHead
  have padLast : (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩] : List (Endpoint site.net)).getLast?=
      some (.inl ⟨.inr (.inr ()),.inr true⟩) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have canonEnd : old.getLast?=some (.inl ⟨.inr (.inr ()),.inr true⟩) := canonLast
  have canonicalForward := canonLabels.root_forward_of_flow flow root canonRoot positive
  have padForward := padLabels.root_forward_of_flow flow root padHead positive
  have same := canonLabels.rooted_terminal_unique site.net canonicalForward canonRoot padLabels padForward padHead
    (canonEnd.trans padLast.symm)
  rw [same.1] at relation
  exact relation
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.lam i j lt) V) site.closed
private abbrev braLambdaRight (i j : Nat) (lt : i<j) := (Schema.braAction .lam i j lt).right.net
local notation "rhs" => braLambdaRight i j lt

/-- The corresponding bra-action exact source-padding reflection. -/
theorem PathSite.bra_lambda_canonical_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ActionCanonicalBlocks site principal
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))])
      (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩]) := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut rhs first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node cut rhs first actualHead
    (.inl ()) (.inl ()) finish
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  obtain ⟨entry,shape,contexts⟩ := unaryRight_lam_context_prefix .bra (Bij.refl Unit) i (j+1)
    pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead insideFinish
  have rule : Traversal i (.op .bra) (.inr ()) (.inl ()) pending.middle (InitialOffsets.braAt i b) := by
    rw [contexts];exact .direct (InitialOffsets.Event.apply_rel (.bra i) b)
  obtain ⟨pre,oldLabels,oldHead,_preLast,oldLast,words⟩ := pending.fixed_principal_ancestor site
    (.bra .lam i j lt) principal first rawHead () (by rw [entry];rfl)
    (by rw [shape];rfl) rule
  rw [plug_decomposition_flatten] at words
  have rooted : (pre++principal.edges).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,oldHead,Option.some_or];rfl
  have typed : accessKind site.net (pre++principal.edges)=some AccessKind.lam := by
    simp only [accessKind,oldLast,Option.bind_some,Pairing.involutive]
    rfl
  have oldForward := oldLabels.root_forward_of_flow flow root rooted positive
  let oldAccess : RootAccess site.net root :=
    ⟨pre++principal.edges,⟨⟨⟨a,InitialOffsets.braAt i b,oldLabels⟩,oldForward⟩,rooted,⟨_,typed⟩⟩⟩
  have sameAccess : oldAccess=source := matching.accessWord_injective (words.symm.trans word.symm)
  have literal : pre++principal.edges=source.val := congrArg Subtype.val sameAccess
  rw [literal] at oldLabels oldLast
  have padLabels : Labelling site.net (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩]) a
      (InitialOffsets.braAt i b) :=
    oldLabels.append_seam (.single _ _) (by
      intro e f atLast atHead
      have eEq := Option.some.inj (atLast.symm.trans oldLast)
      have fEq := Option.some.inj atHead
      subst e;subst f
      rw [Pairing.involutive]
      exact LabelledTurn.node (g:=site.net) (.inr (.inr ())) _ _ (.direct (.lamBody _)))
  obtain ⟨old,relation,canonLabels,canonHead,canonLast,_whole⟩ :=
    pending.bra_lambda_canonical_completion site principal first rawHead insideFinish
  have padHead : (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩] : List (Endpoint site.net)).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,source.property.2.1,Option.some_or]
  have canonRoot : old.head?=some (.inr (.inl root)) := canonHead
  have padLast : (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩] : List (Endpoint site.net)).getLast?=
      some (.inl ⟨.inr (.inr ()),.inr true⟩) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have canonEnd : old.getLast?=some (.inl ⟨.inr (.inr ()),.inr true⟩) := canonLast
  have canonicalForward := canonLabels.root_forward_of_flow flow root canonRoot positive
  have padForward := padLabels.root_forward_of_flow flow root padHead positive
  have same := canonLabels.rooted_terminal_unique site.net canonicalForward canonRoot padLabels padForward padHead
    (canonEnd.trans padLast.symm)
  rw [same.1] at relation
  exact relation
end
end Lamping.AG

import Lamping.Lamping.ActionPendingCanonicalTrim
import Lamping.Lamping.ActionPendingAccess
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {f : Op} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction f i j lt) V) site.closed
private abbrev actionRight (f : Op) (i j : Nat) (lt : i<j) := (Schema.croAction f i j lt).right.net
local notation "right" => actionRight f i j lt

/-- An actual copied auxiliary access fixes its canonical old prefix to the
supplied SAME-word source access. No fragment cut is presumed. -/
theorem PathSite.cro_aux_canonical_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (q : Aux f) (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inr q⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ∃ pending : PendingRhsBlock cut right
        (target.val.map (plugEnd (cut).label (right).label).invFun) a b,
      ActionCanonicalBlocks site principal pending.pre source.val ∧
      Labelling site.net source.val a pending.middle ∧
      source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧
      target.val.map (plugEnd (cut).label (right).label).invFun=pending.pre++
        [.inr (.inr (.inl (.inr q))),.inr (.inl ⟨.inr q,.inr ()⟩)] := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut right first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node cut right first actualHead
    (.inl ()) (.inr q) finish
  have rawHead : (target.val.map (plugEnd (cut).label (right).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (right).label).left_inv (.inl first))
  obtain ⟨old,relation,oldLabels,oldHead,oldLast,shape,_rule,words⟩ :=
    pending.cro_aux_canonical_trim site principal first rawHead q insideFinish
  rw [plug_decomposition_flatten] at words
  have sourceHead : old.head?=some (.inr (.inl root)) := oldHead
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ observation,accessKind site.net old=some observation := by
    rw [kind]; exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root sourceHead positive
  let oldAccess : RootAccess site.net root :=
    ⟨old,⟨⟨⟨a,pending.middle,oldLabels⟩,forward⟩,sourceHead,typed⟩⟩
  have same : oldAccess=source := matching.accessWord_injective (words.symm.trans word.symm)
  have literal : old=source.val := congrArg Subtype.val same
  rw [literal] at relation oldLabels oldLast
  exact ⟨pending,relation,oldLabels,oldLast,shape⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {f : Op} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction f i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction f i j lt) V) site.closed
private abbrev braActionRight (f : Op) (i j : Nat) (lt : i<j) := (Schema.braAction f i j lt).right.net
local notation "right" => braActionRight f i j lt

/-- The corresponding actual bra-action access reflection, on SAME principal. -/
theorem PathSite.bra_aux_canonical_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (q : Aux f) (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inr q⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ∃ pending : PendingRhsBlock cut right
        (target.val.map (plugEnd (cut).label (right).label).invFun) a b,
      ActionCanonicalBlocks site principal pending.pre source.val ∧
      Labelling site.net source.val a pending.middle ∧
      source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧
      target.val.map (plugEnd (cut).label (right).label).invFun=pending.pre++
        [.inr (.inr (.inl (.inr q))),.inr (.inl ⟨.inr q,.inr ()⟩)] := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut right first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node cut right first actualHead
    (.inl ()) (.inr q) finish
  have rawHead : (target.val.map (plugEnd (cut).label (right).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (right).label).left_inv (.inl first))
  obtain ⟨old,relation,oldLabels,oldHead,oldLast,shape,_rule,words⟩ :=
    pending.bra_aux_canonical_trim site principal first rawHead q insideFinish
  rw [plug_decomposition_flatten] at words
  have sourceHead : old.head?=some (.inr (.inl root)) := oldHead
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ observation,accessKind site.net old=some observation := by
    rw [kind]; exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root sourceHead positive
  let oldAccess : RootAccess site.net root :=
    ⟨old,⟨⟨⟨a,pending.middle,oldLabels⟩,forward⟩,sourceHead,typed⟩⟩
  have same : oldAccess=source := matching.accessWord_injective (words.symm.trans word.symm)
  have literal : old=source.val := congrArg Subtype.val same
  rw [literal] at relation oldLabels oldLast
  exact ⟨pending,relation,oldLabels,oldLast,shape⟩
end
end Lamping.AG

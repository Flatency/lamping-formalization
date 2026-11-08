import Lamping.Lamping.ActionOriginalWordTransport
import Lamping.Lamping.CancellationOriginalWordTransport
import Lamping.Lamping.FanCopiedLambdaContextCuts
import Lamping.Lamping.ActionKeptFragmentComparison
import Lamping.Lamping.ActionPendingCanonicalAccess
import Lamping.Lamping.MatchedControlInputs

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem action_fold_raw (action : IsAction s)
    (principal : SiteActionPrincipal site) (weights : Endpoint site.net → EdgeWord)
    (es : List (Endpoint site.reduce)) :
    physicalOriginalWord (site.actionOriginalWordWeights action principal weights) es =
      (es.map (plugEnd (cut).label s.right.net.label).invFun).flatMap
        (Sum.elim (fun outside => weights (site.outsideEnd outside))
          (actionRhsOriginalWord action (physicalOriginalWord weights principal.edges))) := by
  unfold physicalOriginalWord PathSite.actionOriginalWordWeights
  rw [List.flatMap_map]
  rfl
end

section Fan
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- The copied lambda context retains the complete SAME principal word. -/
theorem PathSite.fan_lambda_context_original_word_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (branch : Bool)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    {a b : Context} (whole : Labelling site.reduce target.val a b)
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights) :
    physicalOriginalWord (site.actionOriginalWordWeights (.fan .lam i j lt) principal weights) target.val =
      physicalOriginalWord weights source.val := by
  obtain ⟨pending,oldPre,_middle,relation,_labels,sourceSplit,_last,raw⟩ :=
    site.fan_lambda_context_canonical_trim flow root positive matching principal source target word branch finish whole
  have folded := relation.original_word_transport site (.fan .lam i j lt) weights reverseLaw
  simp only [actionRhsOriginalWord] at folded
  rw [action_fold_raw,raw,List.flatMap_append]
  simp only [List.flatMap_cons,List.flatMap_nil,Sum.elim_inr,actionRhsOriginalWord,fanRhsOriginalWord,List.append_nil]
  rw [folded,sourceSplit]
  simp only [physicalOriginalWord,List.flatMap_append]
end Fan

section Bra
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Both real completions carry the identical OLD body tail before cancellation. -/
theorem PathSite.bra_lambda_original_word_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    {a b : Context} (whole : Labelling site.reduce target.val a b)
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights) :
    physicalOriginalWord (site.actionOriginalWordWeights (.bra .lam i j lt) principal weights) target.val =
      physicalOriginalWord weights source.val := by
  have relation := site.bra_lambda_canonical_access flow root positive matching principal source target word finish whole
  have folded := relation.original_word_transport site (.bra .lam i j lt) weights reverseLaw
  have same :
      physicalOriginalWord (site.actionOriginalWordWeights (.bra .lam i j lt) principal weights) target.val ++
        weights (.inl ⟨.inr (.inr ()),.inr true⟩) =
      physicalOriginalWord weights source.val ++ weights (.inl ⟨.inr (.inr ()),.inr true⟩) := by
    simpa only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.flatMap_map,
      Sum.elim_inr,Sum.elim_inl,physicalOriginalWord,PathSite.actionOriginalWordWeights,
      actionRhsOriginalWord,unaryRhsOriginalWord,List.nil_append,List.append_nil,Function.comp_def]
      using folded
  exact List.append_cancel_right same
end Bra

section Aux
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {f : Op} {i j : Nat} {lt : i<j}

private theorem fan_aux_fold
    (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (branch : Bool) (q : Aux f)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inr q⟩)))
    {a b : Context} (whole : Labelling site.reduce target.val a b)
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights) :
    physicalOriginalWord (site.actionOriginalWordWeights (.fan f i j lt) principal weights) target.val =
      physicalOriginalWord weights source.val := by
  obtain ⟨pending,relation,_labels,_last,raw⟩ :=
    site.fan_aux_canonical_access flow root positive matching principal source target word branch q finish whole
  have folded := relation.original_word_transport site (.fan f i j lt) weights reverseLaw
  rw [action_fold_raw,raw,List.flatMap_append]
  simpa only [List.flatMap_cons,List.flatMap_nil,Sum.elim_inr,actionRhsOriginalWord,
    fanRhsOriginalWord,List.nil_append,List.append_nil] using folded

private theorem cro_aux_fold
    (site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (q : Aux f)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inr q⟩)))
    {a b : Context} (whole : Labelling site.reduce target.val a b)
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights) :
    physicalOriginalWord (site.actionOriginalWordWeights (.cro f i j lt) principal weights) target.val =
      physicalOriginalWord weights source.val := by
  obtain ⟨pending,relation,_labels,_last,raw⟩ :=
    site.cro_aux_canonical_access flow root positive matching principal source target word q finish whole
  have folded := relation.original_word_transport site (.cro f i j lt) weights reverseLaw
  rw [action_fold_raw,raw,List.flatMap_append]
  simpa only [List.flatMap_cons,List.flatMap_nil,Sum.elim_inr,actionRhsOriginalWord,
    unaryRhsOriginalWord,List.nil_append,List.append_nil] using folded

private theorem bra_aux_fold
    (site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (q : Aux f)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inr q⟩)))
    {a b : Context} (whole : Labelling site.reduce target.val a b)
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights) :
    physicalOriginalWord (site.actionOriginalWordWeights (.bra f i j lt) principal weights) target.val =
      physicalOriginalWord weights source.val := by
  obtain ⟨pending,relation,_labels,_last,raw⟩ :=
    site.bra_aux_canonical_access flow root positive matching principal source target word q finish whole
  have folded := relation.original_word_transport site (.bra f i j lt) weights reverseLaw
  rw [action_fold_raw,raw,List.flatMap_append]
  simpa only [List.flatMap_cons,List.flatMap_nil,Sum.elim_inr,actionRhsOriginalWord,
    unaryRhsOriginalWord,List.nil_append,List.append_nil] using folded
end Aux

section General
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Exhaust every actual proper endpoint; target Matches is not assumed. -/
theorem PathSite.action_original_word_root_access (action : IsAction s)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    {a b : Context} (whole : Labelling site.reduce target.val a b)
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights) :
    physicalOriginalWord (site.actionOriginalWordWeights action principal weights) target.val =
      physicalOriginalWord weights source.val := by
  obtain ⟨terminal,role,level,finish,atTerminal,incoming⟩ := target.incoming_endpoint
  cases atTerminal with
  | root => exact False.elim incoming
  | appFun => exact False.elim incoming
  | appArg => exact False.elim incoming
  | lamBody => exact False.elim incoming
  | appCtx node p level lab port =>
    cases node with
    | inl node =>
      exact (site.action_kept_canonical_access action flow root positive matching principal
        source target word node p finish whole).1.original_word_transport_actual site action weights reverseLaw
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl branch =>
          have same : f=.app := Kind.op.inj (congrArg Graph.Label.sort lab)
          subst f
          have ports : p=appCtx := eq_of_heq port
          subst p
          exact site.fan_app_function_original_word_access flow root positive matching principal source target word branch finish whole weights reverseLaw
        | inr q =>
          have impossible : Op.fan=.app := Kind.op.inj (congrArg Graph.Label.sort lab)
          cases impossible
      | cro f i j lt =>
        cases node with
        | inl value =>
          cases value
          have same : f=.app := Kind.op.inj (congrArg Graph.Label.sort lab)
          subst f
          have ports : p=appCtx := eq_of_heq port
          subst p
          exact cro_aux_fold site flow root positive matching principal source target word false finish whole weights reverseLaw
        | inr q =>
          have impossible : Op.cro=.app := Kind.op.inj (congrArg Graph.Label.sort lab)
          cases impossible
      | bra f i j lt =>
        cases node with
        | inl value =>
          cases value
          have same : f=.app := Kind.op.inj (congrArg Graph.Label.sort lab)
          subst f
          have ports : p=appCtx := eq_of_heq port
          subst p
          exact bra_aux_fold site flow root positive matching principal source target word false finish whole weights reverseLaw
        | inr q =>
          have impossible : Op.bra=.app := Kind.op.inj (congrArg Graph.Label.sort lab)
          cases impossible
  | lamCtx node p level lab port =>
    cases node with
    | inl node =>
      exact (site.action_kept_canonical_access action flow root positive matching principal
        source target word node p finish whole).1.original_word_transport_actual site action weights reverseLaw
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl branch =>
          have same : f=.lam := Kind.op.inj (congrArg Graph.Label.sort lab)
          subst f
          have ports : p=(Sum.inl () : Port (.op .lam)) := eq_of_heq port
          subst p
          exact site.fan_lambda_context_original_word_access flow root positive matching principal source target word branch finish whole weights reverseLaw
        | inr q =>
          have impossible : Op.fan=.lam := Kind.op.inj (congrArg Graph.Label.sort lab)
          cases impossible
      | cro f i j lt =>
        cases node with
        | inl value =>
          cases value
          have same : f=.lam := Kind.op.inj (congrArg Graph.Label.sort lab)
          subst f
          have ports : p=(Sum.inl () : Port (.op .lam)) := eq_of_heq port
          subst p
          exact site.cro_lambda_original_word_access flow root positive matching principal source target word finish whole weights reverseLaw
        | inr q =>
          have impossible : Op.cro=.lam := Kind.op.inj (congrArg Graph.Label.sort lab)
          cases impossible
      | bra f i j lt =>
        cases node with
        | inl value =>
          cases value
          have same : f=.lam := Kind.op.inj (congrArg Graph.Label.sort lab)
          subst f
          have ports : p=(Sum.inl () : Port (.op .lam)) := eq_of_heq port
          subst p
          exact site.bra_lambda_original_word_access flow root positive matching principal source target word finish whole weights reverseLaw
        | inr q =>
          have impossible : Op.bra=.lam := Kind.op.inj (congrArg Graph.Label.sort lab)
          cases impossible
  | lamBind node p level lab port =>
    cases node with
    | inl node =>
      exact (site.action_kept_canonical_access action flow root positive matching principal
        source target word node p finish whole).1.original_word_transport_actual site action weights reverseLaw
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl branch =>
          have same : f=.lam := Kind.op.inj (congrArg Graph.Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact fan_aux_fold site flow root positive matching principal source target word branch false finish whole weights reverseLaw
        | inr q =>
          have impossible : Op.fan=.lam := Kind.op.inj (congrArg Graph.Label.sort lab)
          cases impossible
      | cro f i j lt =>
        cases node with
        | inl value =>
          cases value
          have same : f=.lam := Kind.op.inj (congrArg Graph.Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact cro_aux_fold site flow root positive matching principal source target word false finish whole weights reverseLaw
        | inr q =>
          have impossible : Op.cro=.lam := Kind.op.inj (congrArg Graph.Label.sort lab)
          cases impossible
      | bra f i j lt =>
        cases node with
        | inl value =>
          cases value
          have same : f=.lam := Kind.op.inj (congrArg Graph.Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact bra_aux_fold site flow root positive matching principal source target word false finish whole weights reverseLaw
        | inr q =>
          have impossible : Op.bra=.lam := Kind.op.inj (congrArg Graph.Label.sort lab)
          cases impossible

/-- The common principal is chosen once before quantifying over all accesses. -/
theorem PathSite.cancellation_original_word_root_access (cancel : IsCancellation s)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (targetMatches : Matches site.reduce root term)
    (weights : Endpoint site.net → EdgeWord) (reverseLaw : OriginalWordReversal weights) :
    ∃ principal : SiteActionPrincipal site,
      ∀ (source : RootAccess site.net root) (target : RootAccess site.reduce root),
        accessWord site.net source.val=accessWord site.reduce target.val →
        physicalOriginalWord (site.cancellationOriginalWordWeights principal weights) target.val =
          physicalOriginalWord weights source.val := by
  obtain ⟨principal,all⟩ := site.cancellation_canonical_root_accesses cancel flow root positive
  refine ⟨principal,?_⟩
  intro source target word
  obtain ⟨canonical,canonicalWord,_kind,residual⟩ := all source
  have same : canonical=target := targetMatches.accessWord_injective (canonicalWord.trans word)
  subst canonical
  exact residual.original_word_transport_actual site cancel principal weights reverseLaw
end General

#print axioms PathSite.fan_lambda_context_original_word_access
#print axioms PathSite.bra_lambda_original_word_access
#print axioms PathSite.action_original_word_root_access
#print axioms PathSite.cancellation_original_word_root_access
end Lamping.AG

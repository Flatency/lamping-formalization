import Lamping.Lamping.RootActionPendingReplay
import Lamping.Lamping.ReachableNesting
import Lamping.Lamping.ActionResidualReplay
import Lamping.Lamping.ActionPendingReplay
import Lamping.Lamping.ReducedOutsideRoles
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- The actual reduced proper endpoint is retained. Its old proper role is
recovered by the physical cut/plug interface, not supplied as an oracle. -/
theorem PathSite.action_kept_typed_root_inputs_weak (action : IsAction s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) {t : Term}
    (matching : Matches site.net root t) (rootInputs : RootInputs site.net root)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output)
    (rooted : es.head?=some (.inr (.inl root)))
    (node : K) (p : Port (kept node).sort) (role : ProperRole) (level : Nat)
    (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inl node,p⟩)))
    (atTerminal : AtProperRole site.reduce root (.inl ⟨.inl node,p⟩) role level)
    (incoming : role.incoming) :
    ∀ requested : Context,∃ result,Labelling site.reduce es requested result := by
  let c := cutFragment site.net (pathPartition s V) site.closed
  let r := s.right.net
  let last : Endpoint c := c.wire (.inl ⟨node,p⟩)
  have represented : site.reduce.wire (.inl ⟨.inl node,p⟩)=AG.plugLeft c r last :=
    plugLeft_wire c r (.inl ⟨node,p⟩)
  have actualRole : AtProperRole site.reduce root (site.reduce.wire (AG.plugLeft c r last)) role level := by
    rw [←represented,Pairing.involutive]
    exact atTerminal
  have oldRole := site.reduced_outside_incoming root last role level actualRole incoming
  have lastFinish : es.getLast?=some (AG.plugLeft c r last) := finish.trans (congrArg some represented)
  obtain ⟨principal,old,_,oldLabels,oldHead,oldLast,replay⟩ :=
    site.action_root_relabelling_ancestor_root action matching rootInputs flow positive labels rooted last lastFinish
  have oldForward := oldLabels.root_forward_of_flow flow root oldHead positive
  have oldFinish : old.getLast?=some (site.net.wire (site.net.wire (site.outsideEnd last))) := by
    simpa only [Pairing.involutive] using oldLast
  have allInputs := rootInputs old input output (site.net.wire (site.outsideEnd last)) role level
    oldLabels oldForward oldHead oldFinish oldRole incoming
  intro requested
  obtain ⟨result,changed⟩ := allInputs requested
  exact ⟨result,replay requested result changed⟩

/-- All actual proper incoming endpoints are covered: kept nodes and each
new app/lambda copy. This proves only root-input existence, not full I. -/
theorem PathSite.action_typed_root_inputs_weak (action : IsAction s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) {t : Term}
    (matching : Matches site.net root t) (rootInputs : RootInputs site.net root)
    (nesting : Nesting site.net root) (transparency : Transparency site.net root)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output)
    (rooted : es.head?=some (.inr (.inl root)))
    (terminal : Endpoint site.reduce) (role : ProperRole) (level : Nat)
    (finish : es.getLast?=some (site.reduce.wire terminal))
    (atTerminal : AtProperRole site.reduce root terminal role level) (incoming : role.incoming) :
    ∀ requested : Context,∃ result,Labelling site.reduce es requested result := by
  cases atTerminal with
  | root => exact False.elim incoming
  | appFun => exact False.elim incoming
  | appArg => exact False.elim incoming
  | lamBody => exact False.elim incoming
  | appCtx node p level lab port =>
    cases node with
    | inl node =>
      exact site.action_kept_typed_root_inputs_weak action flow root positive matching rootInputs
        labels rooted node p .appCtx level finish (AtProperRole.appCtx (g:=site.reduce) (root:=root) (.inl node) p level lab port) incoming
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl branch =>
          have same : f=.app := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=appCtx := eq_of_heq port
          subst p
          exact site.fan_new_app_root_inputs_weak matching rootInputs flow positive labels rooted branch finish
        | inr q =>
          have impossible : Op.fan=.app := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
      | cro f i j lt =>
        cases node with
        | inl u =>
          cases u
          have same : f=.app := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=appCtx := eq_of_heq port
          subst p
          exact site.cro_new_app_root_inputs_weak matching rootInputs flow positive labels rooted finish
        | inr q =>
          have impossible : Op.cro=.app := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
      | bra f i j lt =>
        cases node with
        | inl u =>
          cases u
          have same : f=.app := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=appCtx := eq_of_heq port
          subst p
          exact site.bra_new_app_root_inputs_weak matching rootInputs flow positive labels rooted finish
        | inr q =>
          have impossible : Op.bra=.app := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
  | lamCtx node p level lab port =>
    cases node with
    | inl node =>
      exact site.action_kept_typed_root_inputs_weak action flow root positive matching rootInputs
        labels rooted node p .lamCtx level finish (AtProperRole.lamCtx (g:=site.reduce) (root:=root) (.inl node) p level lab port) incoming
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl branch =>
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=(Sum.inl ()) := eq_of_heq port
          subst p
          exact site.fan_new_lam_ctx_root_inputs_weak matching rootInputs flow positive labels rooted branch finish
        | inr q =>
          have impossible : Op.fan=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
      | cro f i j lt =>
        cases node with
        | inl u =>
          cases u
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=(Sum.inl ()) := eq_of_heq port
          subst p
          exact site.cro_new_lam_ctx_root_inputs_weak matching rootInputs flow positive labels rooted finish
        | inr q =>
          have impossible : Op.cro=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
      | bra f i j lt =>
        cases node with
        | inl u =>
          cases u
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=(Sum.inl ()) := eq_of_heq port
          subst p
          exact site.bra_new_lam_ctx_root_inputs_weak matching rootInputs flow positive labels rooted finish
        | inr q =>
          have impossible : Op.bra=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
  | lamBind node p level lab port =>
    cases node with
    | inl node =>
      exact site.action_kept_typed_root_inputs_weak action flow root positive matching rootInputs
        labels rooted node p .lamBind level finish (AtProperRole.lamBind (g:=site.reduce) (root:=root) (.inl node) p level lab port) incoming
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl branch =>
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact site.fan_new_lam_bind_root_inputs_weak matching rootInputs nesting transparency flow positive labels rooted branch finish
        | inr q =>
          have impossible : Op.fan=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
      | cro f i j lt =>
        cases node with
        | inl u =>
          cases u
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact site.cro_new_lam_bind_root_inputs_weak matching rootInputs nesting transparency flow positive labels rooted finish
        | inr q =>
          have impossible : Op.cro=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
      | bra f i j lt =>
        cases node with
        | inl u =>
          cases u
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact site.bra_new_lam_bind_root_inputs_weak matching rootInputs nesting transparency flow positive labels rooted finish
        | inr q =>
          have impossible : Op.bra=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible

/-- All three actual actions preserve typed root-input existence. The true
function-child access comes from source Matches; typed totality comes from
source RootInputs. Structural indexed balance supplies Nesting where the
copied lambda-binding branch needs it. No full proper-source I is assumed. -/
theorem PathSite.action_rootInputs (action : IsAction s)
    {boundary : B → Bool} {heights : B → Int} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true)
    (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    {t : Term} (matching : Matches site.net root t)
    (inputs : RootInputs site.net root) (transparency : Transparency site.net root) :
    RootInputs site.reduce root := by
  intro es input output terminal role level labels _forward rooted finish atTerminal incoming requested
  exact site.action_typed_root_inputs_weak action flow root positive matching inputs
    (balance.nesting root rootDepth) transparency labels rooted terminal role level finish atTerminal incoming requested
end
end Lamping.AG

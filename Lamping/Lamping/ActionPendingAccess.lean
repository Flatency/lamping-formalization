import Lamping.Lamping.ActionPendingLambdaWords
import Lamping.Lamping.PlugPendingEndpoints
import Lamping.Lamping.ActionKeptAccess
import Lamping.Lamping.MatchedControlInputs
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {f : Op} {i j : Nat} {lt : i<j}

/-- A supplied actual access to a new copy has a real source access with
the same word and observation kind. Variable indices are a separate obligation. -/
theorem PathSite.fan_new_aux_access_backward
    (site : PathSite (Schema.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (target : RootAccess site.reduce root) (branch : Bool) (q : Aux f)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inr q⟩))) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val := by
  let c := cutFragment site.net (pathPartition (Schema.fanAction f i j lt) V) site.closed
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨a,b,labels⟩ := target.property.1.1
  have actualHead : target.val.head?=some (AG.plugLeft c (Schema.fanAction f i j lt).right.net first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node c (Schema.fanAction f i j lt).right.net first actualHead
    (.inl branch) (.inr q) finish
  have rawHead : (target.val.map (plugEnd c.label (Schema.fanAction f i j lt).right.net.label).invFun).head?=
      some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd c.label (Schema.fanAction f i j lt).right.net.label).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,words,_tails⟩ := site.fan_pending_aux_ancestor_word pending first rawHead branch q insideFinish
  rw [plug_decomposition_flatten] at words
  have sourceHead : old.head?=some (.inr (.inl root)) := oldHead
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ observation,accessKind site.net old=some observation := by
    rw [kind]; exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root sourceHead positive
  exact ⟨⟨old,⟨⟨⟨_,_,oldLabels⟩,forward⟩,sourceHead,typed⟩⟩,words.symm,kind⟩

/-- A supplied actual access to a new copy has a real source access with
the same word and observation kind. Variable indices are a separate obligation. -/
theorem PathSite.fan_new_lam_access_backward
    (site : PathSite (Schema.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (target : RootAccess site.reduce root) (branch : Bool)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩))) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val := by
  let c := cutFragment site.net (pathPartition (Schema.fanAction .lam i j lt) V) site.closed
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨a,b,labels⟩ := target.property.1.1
  have actualHead : target.val.head?=some (AG.plugLeft c (Schema.fanAction .lam i j lt).right.net first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node c (Schema.fanAction .lam i j lt).right.net first actualHead
    (.inl branch) (.inl ()) finish
  have rawHead : (target.val.map (plugEnd c.label (Schema.fanAction .lam i j lt).right.net.label).invFun).head?=
      some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd c.label (Schema.fanAction .lam i j lt).right.net.label).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,words⟩ := site.fan_pending_lam_ancestor_word pending first rawHead branch insideFinish
  rw [plug_decomposition_flatten] at words
  have sourceHead : old.head?=some (.inr (.inl root)) := oldHead
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ observation,accessKind site.net old=some observation := by
    rw [kind]; exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root sourceHead positive
  exact ⟨⟨old,⟨⟨⟨_,_,oldLabels⟩,forward⟩,sourceHead,typed⟩⟩,words.symm,kind⟩

/-- A supplied actual access to a new copy has a real source access with
the same word and observation kind. Variable indices are a separate obligation. -/
theorem PathSite.cro_new_aux_access_backward
    (site : PathSite (Schema.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (target : RootAccess site.reduce root) (q : Aux f)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inr q⟩))) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val := by
  let c := cutFragment site.net (pathPartition (Schema.croAction f i j lt) V) site.closed
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨a,b,labels⟩ := target.property.1.1
  have actualHead : target.val.head?=some (AG.plugLeft c (Schema.croAction f i j lt).right.net first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node c (Schema.croAction f i j lt).right.net first actualHead
    (.inl ()) (.inr q) finish
  have rawHead : (target.val.map (plugEnd c.label (Schema.croAction f i j lt).right.net.label).invFun).head?=
      some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd c.label (Schema.croAction f i j lt).right.net.label).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,words,_tails⟩ := site.cro_pending_aux_ancestor_word pending first rawHead q insideFinish
  rw [plug_decomposition_flatten] at words
  have sourceHead : old.head?=some (.inr (.inl root)) := oldHead
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ observation,accessKind site.net old=some observation := by
    rw [kind]; exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root sourceHead positive
  exact ⟨⟨old,⟨⟨⟨_,_,oldLabels⟩,forward⟩,sourceHead,typed⟩⟩,words.symm,kind⟩

/-- A supplied actual access to a new copy has a real source access with
the same word and observation kind. Variable indices are a separate obligation. -/
theorem PathSite.cro_new_lam_access_backward
    (site : PathSite (Schema.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (target : RootAccess site.reduce root)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val := by
  let c := cutFragment site.net (pathPartition (Schema.croAction .lam i j lt) V) site.closed
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨a,b,labels⟩ := target.property.1.1
  have actualHead : target.val.head?=some (AG.plugLeft c (Schema.croAction .lam i j lt).right.net first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node c (Schema.croAction .lam i j lt).right.net first actualHead
    (.inl ()) (.inl ()) finish
  have rawHead : (target.val.map (plugEnd c.label (Schema.croAction .lam i j lt).right.net.label).invFun).head?=
      some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd c.label (Schema.croAction .lam i j lt).right.net.label).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,words⟩ := site.cro_pending_lam_ancestor_word pending first rawHead insideFinish
  rw [plug_decomposition_flatten] at words
  have sourceHead : old.head?=some (.inr (.inl root)) := oldHead
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ observation,accessKind site.net old=some observation := by
    rw [kind]; exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root sourceHead positive
  exact ⟨⟨old,⟨⟨⟨_,_,oldLabels⟩,forward⟩,sourceHead,typed⟩⟩,words.symm,kind⟩

/-- A supplied actual access to a new copy has a real source access with
the same word and observation kind. Variable indices are a separate obligation. -/
theorem PathSite.bra_new_aux_access_backward
    (site : PathSite (Schema.braAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (target : RootAccess site.reduce root) (q : Aux f)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inr q⟩))) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val := by
  let c := cutFragment site.net (pathPartition (Schema.braAction f i j lt) V) site.closed
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨a,b,labels⟩ := target.property.1.1
  have actualHead : target.val.head?=some (AG.plugLeft c (Schema.braAction f i j lt).right.net first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node c (Schema.braAction f i j lt).right.net first actualHead
    (.inl ()) (.inr q) finish
  have rawHead : (target.val.map (plugEnd c.label (Schema.braAction f i j lt).right.net.label).invFun).head?=
      some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd c.label (Schema.braAction f i j lt).right.net.label).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,words,_tails⟩ := site.bra_pending_aux_ancestor_word pending first rawHead q insideFinish
  rw [plug_decomposition_flatten] at words
  have sourceHead : old.head?=some (.inr (.inl root)) := oldHead
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ observation,accessKind site.net old=some observation := by
    rw [kind]; exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root sourceHead positive
  exact ⟨⟨old,⟨⟨⟨_,_,oldLabels⟩,forward⟩,sourceHead,typed⟩⟩,words.symm,kind⟩

/-- A supplied actual access to a new copy has a real source access with
the same word and observation kind. Variable indices are a separate obligation. -/
theorem PathSite.bra_new_lam_access_backward
    (site : PathSite (Schema.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (target : RootAccess site.reduce root)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val := by
  let c := cutFragment site.net (pathPartition (Schema.braAction .lam i j lt) V) site.closed
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨a,b,labels⟩ := target.property.1.1
  have actualHead : target.val.head?=some (AG.plugLeft c (Schema.braAction .lam i j lt).right.net first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node c (Schema.braAction .lam i j lt).right.net first actualHead
    (.inl ()) (.inl ()) finish
  have rawHead : (target.val.map (plugEnd c.label (Schema.braAction .lam i j lt).right.net.label).invFun).head?=
      some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd c.label (Schema.braAction .lam i j lt).right.net.label).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,words⟩ := site.bra_pending_lam_ancestor_word pending first rawHead insideFinish
  rw [plug_decomposition_flatten] at words
  have sourceHead : old.head?=some (.inr (.inl root)) := oldHead
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ observation,accessKind site.net old=some observation := by
    rw [kind]; exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root sourceHead positive
  exact ⟨⟨old,⟨⟨⟨_,_,oldLabels⟩,forward⟩,sourceHead,typed⟩⟩,words.symm,kind⟩

/-- Every actual target root access of an action reflects to a real source
root access with the same syntax word and endpoint kind. This covers kept
nodes and all copied proper endpoints. BindingSuffix indices are not claimed. -/
theorem PathSite.action_root_access_backward {s : Schema}
    (site : PathSite s kept (B:=B) (W:=W) (V:=V)) (action : IsAction s)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (target : RootAccess site.reduce root) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val := by
  obtain ⟨terminal,role,level,finish,atTerminal,incoming⟩ := target.incoming_endpoint
  cases atTerminal with
  | root => exact False.elim incoming
  | appFun => exact False.elim incoming
  | appArg => exact False.elim incoming
  | lamBody => exact False.elim incoming
  | appCtx node p level lab port =>
    cases node with
    | inl node =>
      exact site.action_kept_access_backward action flow root positive target node p finish
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl branch =>
          have same : f=.app := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=appCtx := eq_of_heq port
          subst p
          exact site.fan_new_aux_access_backward flow root positive target branch false finish
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
          exact site.cro_new_aux_access_backward flow root positive target false finish
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
          exact site.bra_new_aux_access_backward flow root positive target false finish
        | inr q =>
          have impossible : Op.bra=.app := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
  | lamCtx node p level lab port =>
    cases node with
    | inl node =>
      exact site.action_kept_access_backward action flow root positive target node p finish
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl branch =>
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=(Sum.inl ()) := eq_of_heq port
          subst p
          exact site.fan_new_lam_access_backward flow root positive target branch finish
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
          exact site.cro_new_lam_access_backward flow root positive target finish
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
          exact site.bra_new_lam_access_backward flow root positive target finish
        | inr q =>
          have impossible : Op.bra=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
  | lamBind node p level lab port =>
    cases node with
    | inl node =>
      exact site.action_kept_access_backward action flow root positive target node p finish
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl branch =>
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact site.fan_new_aux_access_backward flow root positive target branch false finish
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
          exact site.cro_new_aux_access_backward flow root positive target false finish
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
          exact site.bra_new_aux_access_backward flow root positive target false finish
        | inr q =>
          have impossible : Op.bra=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
end
end Lamping.AG

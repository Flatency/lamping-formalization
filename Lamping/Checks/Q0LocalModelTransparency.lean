import Lamping.Checks.Q0LocalModelFixture
import Lamping.Lamping.FlowBalance
import Lamping.Lamping.InitialTransparency
import Lamping.Lamping.PathLabelDeterminism

namespace Lamping.Checks.Q0LocalModelTransparency
open AG Graph Lambda Q0LocalModelFixture

def nodeBase : Node → Int
  | .F => 1
  | .C1 => 1
  | .CJ => 2
  | .CK => 2
  | _ => 0

def actual_indexed_balance : IndexedLevelBalance net (fun _ : Unit => (0 : Int)) where
  nodes := nodeBase
  vertices := Empty.elim
  wiring := by
    rintro (⟨n,p⟩ | (u | ⟨e,d⟩))
    · cases n <;> cases p <;> rename_i x <;> cases x <;> rfl
    · cases u; rfl
    · exact nomatch e
  bounded := by intro n; cases n <;> simp [ControlIndexBound,nodeBase,net,nodeLabel,AG.label]

def actual_flow_balance : FlowBalance net (fun _ : Unit => true) where
  nodes := fun _ => true
  vertices := Empty.elim
  wiring := by
    rintro (⟨n,p⟩ | (u | ⟨e,d⟩))
    · cases n <;> cases p <;> rename_i x <;> cases x <;> rfl
    · cases u; rfl
    · exact nomatch e

private theorem actual_loop_same_assignment
    (code : LambdaCode) (pre : List (Endpoint net))
    (ctx : Port (net.label (lambdaNode code)).sort)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    {a b : Context}
    (last : pre.getLast? = some (net.wire (.inl ⟨lambdaNode code,ctx⟩)))
    (labels : Labelling net (pre ++ loopEdges code) a b) :
    ∃ (middle : Context) (binding : BindingLoop net (loopEdges code) middle b),
      binding.binder = lambdaNode code ∧ Labelling net pre a middle := by
  cases code with
  | L =>
    have sameCtx : ctx = (.inl () : Port (.op .lam)) := eq_of_heq ctxRole
    subst ctx
    obtain ⟨middle,after,first,suffix,seam⟩ := labels.split_seam pre (loopEdges .L)
      (net.wire (.inl ⟨Node.L,.inl ()⟩)) (.inl ⟨Node.L,lamBody⟩) last rfl
    rw [Pairing.involutive] at seam
    have same : middle=after := by
      cases seam with
      | node node p q rule => exact rule.proper_context
    subst after
    have final : b = InitialOffsets.croAt (lambdaIndex .L) middle :=
      suffix.output_unique (actual_loop .L middle).proper
    cases final
    exact ⟨middle,actual_loop .L middle,rfl,first⟩
  | J =>
    have sameCtx : ctx = (.inl () : Port (.op .lam)) := eq_of_heq ctxRole
    subst ctx
    obtain ⟨middle,after,first,suffix,seam⟩ := labels.split_seam pre (loopEdges .J)
      (net.wire (.inl ⟨Node.J,.inl ()⟩)) (.inl ⟨Node.J,lamBody⟩) last rfl
    rw [Pairing.involutive] at seam
    have same : middle=after := by
      cases seam with
      | node node p q rule => exact rule.proper_context
    subst after
    have final : b = InitialOffsets.croAt (lambdaIndex .J) middle :=
      suffix.output_unique (actual_loop .J middle).proper
    cases final
    exact ⟨middle,actual_loop .J middle,rfl,first⟩
  | K =>
    have sameCtx : ctx = (.inl () : Port (.op .lam)) := eq_of_heq ctxRole
    subst ctx
    obtain ⟨middle,after,first,suffix,seam⟩ := labels.split_seam pre (loopEdges .K)
      (net.wire (.inl ⟨Node.K,.inl ()⟩)) (.inl ⟨Node.K,lamBody⟩) last rfl
    rw [Pairing.involutive] at seam
    have same : middle=after := by
      cases seam with
      | node node p q rule => exact rule.proper_context
    subst after
    have final : b = InitialOffsets.croAt (lambdaIndex .K) middle :=
      suffix.output_unique (actual_loop .K middle).proper
    cases final
    exact ⟨middle,actual_loop .K middle,rfl,first⟩

private theorem binding_kind (kind : Kind) (p : Port kind) (isLam : kind=.op .lam)
    (role : HEq p lamBind) : portKind kind p=some .var := by
  subst kind
  have same : p=lamBind := eq_of_heq role
  subst p
  rfl

theorem actual_transparency : Transparency net () := by
  intro es a b n ctx _body bind isLam ctxRole _bodyRole bindRole rooted finish forward labels
  have kind : accessKind net es=some .var := by
    unfold accessKind
    rw [finish]
    simp only [Option.bind_some,Pairing.involutive]
    exact binding_kind _ bind isLam bindRole
  let actual : RootAccess net () := ⟨es,⟨⟨⟨a,b,labels⟩,forward⟩,rooted,.var,kind⟩⟩
  obtain ⟨code,same,_word⟩ := actual_root_access_classification actual
  change es=edges code at same
  subst es
  cases code with
  | root => simp [accessKind,edges,net,mate,nodeLabel,portKind,AG.label] at kind
  | leftA => simp [accessKind,edges,net,mate,nodeLabel,portKind,AG.label] at kind
  | leftB => simp [accessKind,edges,net,mate,nodeLabel,portKind,AG.label] at kind
  | leftL => simp [accessKind,edges,net,mate,nodeLabel,portKind,AG.label] at kind
  | leftV =>
    cases n <;> try {cases isLam}
    all_goals
      have sameBind : bind = lamBind := eq_of_heq bindRole
      have sameCtx : ctx = (.inl () : Port (.op .lam)) := eq_of_heq ctxRole
      subst bind; subst ctx
      simp [edges,net,mate,lamBind] at finish
    obtain ⟨middle,binding,binder,preLabels⟩ :=
      actual_loop_same_assignment .L (edges .leftL) (.inl ()) HEq.rfl (by rfl) labels
    exact ⟨edges .leftL,loopEdges .L,middle,binding,rfl,binder,rfl,preLabels⟩
  | leftJ => simp [accessKind,edges,net,mate,nodeLabel,portKind,AG.label] at kind
  | leftJV =>
    cases n <;> try {cases isLam}
    all_goals
      have sameBind : bind = lamBind := eq_of_heq bindRole
      have sameCtx : ctx = (.inl () : Port (.op .lam)) := eq_of_heq ctxRole
      subst bind; subst ctx
      simp [edges,net,mate,lamBind] at finish
    obtain ⟨middle,binding,binder,preLabels⟩ :=
      actual_loop_same_assignment .J (edges .leftJ) (.inl ()) HEq.rfl (by rfl) labels
    exact ⟨edges .leftJ,loopEdges .J,middle,binding,rfl,binder,rfl,preLabels⟩
  | leftK => simp [accessKind,edges,net,mate,nodeLabel,portKind,AG.label] at kind
  | leftKV =>
    cases n <;> try {cases isLam}
    all_goals
      have sameBind : bind = lamBind := eq_of_heq bindRole
      have sameCtx : ctx = (.inl () : Port (.op .lam)) := eq_of_heq ctxRole
      subst bind; subst ctx
      simp [edges,net,mate,lamBind] at finish
    obtain ⟨middle,binding,binder,preLabels⟩ :=
      actual_loop_same_assignment .K (edges .leftK) (.inl ()) HEq.rfl (by rfl) labels
    exact ⟨edges .leftK,loopEdges .K,middle,binding,rfl,binder,rfl,preLabels⟩
  | rightA => simp [accessKind,edges,net,mate,nodeLabel,portKind,AG.label] at kind
  | rightB => simp [accessKind,edges,net,mate,nodeLabel,portKind,AG.label] at kind
  | rightL => simp [accessKind,edges,net,mate,nodeLabel,portKind,AG.label] at kind
  | rightV =>
    cases n <;> try {cases isLam}
    all_goals
      have sameBind : bind = lamBind := eq_of_heq bindRole
      have sameCtx : ctx = (.inl () : Port (.op .lam)) := eq_of_heq ctxRole
      subst bind; subst ctx
      simp [edges,net,mate,lamBind] at finish
    obtain ⟨middle,binding,binder,preLabels⟩ :=
      actual_loop_same_assignment .L (edges .rightL) (.inl ()) HEq.rfl (by rfl) labels
    exact ⟨edges .rightL,loopEdges .L,middle,binding,rfl,binder,rfl,preLabels⟩
  | rightJ => simp [accessKind,edges,net,mate,nodeLabel,portKind,AG.label] at kind
  | rightJV =>
    cases n <;> try {cases isLam}
    all_goals
      have sameBind : bind = lamBind := eq_of_heq bindRole
      have sameCtx : ctx = (.inl () : Port (.op .lam)) := eq_of_heq ctxRole
      subst bind; subst ctx
      simp [edges,net,mate,lamBind] at finish
    obtain ⟨middle,binding,binder,preLabels⟩ :=
      actual_loop_same_assignment .J (edges .rightJ) (.inl ()) HEq.rfl (by rfl) labels
    exact ⟨edges .rightJ,loopEdges .J,middle,binding,rfl,binder,rfl,preLabels⟩
  | rightK => simp [accessKind,edges,net,mate,nodeLabel,portKind,AG.label] at kind
  | rightKV =>
    cases n <;> try {cases isLam}
    all_goals
      have sameBind : bind = lamBind := eq_of_heq bindRole
      have sameCtx : ctx = (.inl () : Port (.op .lam)) := eq_of_heq ctxRole
      subst bind; subst ctx
      simp [edges,net,mate,lamBind] at finish
    obtain ⟨middle,binding,binder,preLabels⟩ :=
      actual_loop_same_assignment .K (edges .rightK) (.inl ()) HEq.rfl (by rfl) labels
    exact ⟨edges .rightK,loopEdges .K,middle,binding,rfl,binder,rfl,preLabels⟩

#print axioms actual_indexed_balance
#print axioms actual_flow_balance
#print axioms actual_transparency

end Lamping.Checks.Q0LocalModelTransparency

import Lamping.Lamping.PairedCurrentChainSourceLabels
import Lamping.Lamping.TerminalHeadSuppliers
import Lamping.Lamping.MarkedOldSourceEndpointIso
import Lamping.Lamping.FamilyRepresentation
import Lamping.Lambda.UniformOldCreatedIncomingLabels
import Lamping.Lambda.AuxiliaryNodeHistoryOrigins
import Lamping.Lambda.TargetHistoryPreimages
import Lamping.Lambda.SafeIncomingHistory

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem empty_prefix_at_proper
    (proper : SyntaxIncidence.ProperAt current start)
    (segment : PrerequisitePrefix current start edges finish) (empty : edges=[]) : finish=start := by
  cases segment with
  | refl => rfl
  | app => cases empty
  | lam => cases empty
  | var lookup =>
    rcases proper with ⟨a,fn,arg,atNode⟩ |⟨a,body,atNode⟩ <;>
      rw [lookup] at atNode <;> cases atNode

theorem same_kind_old_endpoint_iso
    {original source current : LTerm}
    {prior ps F : List Path} {degree : Lambda.Labelled.Label} {marked : Marked}
    (initial : INIT original)
    (prefixHistory : History prior original source)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (labels : History ps source current)
    (selected : ∀ name ∈ F, source.degreeAt name = some degree)
    (sourceSafe : source.OuterBarsSafe (fun payload => payload ≠ degree))
    (sourceClosed : Closed source.erase)
    (currentClosed : Closed current.erase)
    (left right : SyntaxIncidence.ProperPosition current)
    (oldLeft oldRight : SyntaxIncidence.ProperPosition source)
    (leftTrace : BetaVertexHistoryPreimage labels (some left) (some oldLeft))
    (rightTrace : BetaVertexHistoryPreimage labels (some right) (some oldRight))
    {leftEdges rightEdges : List Path}
    (leftChain : EndpointChain current (some left) leftEdges)
    (rightChain : EndpointChain current (some right) rightEdges)
    (currentIso : ChainIncidenceIsomorphic
      (chainSyntaxIncidence current currentClosed leftEdges)
      (chainSyntaxIncidence current currentClosed rightEdges))
    (sameKind : ∃ kind : Bool,
      ProperKind current left kind ∧ ProperKind current right kind) :
    SuccessfulEndpointIso source sourceClosed (some oldLeft) (some oldRight) := by
  cases leftTrace with
  | proper leftTrace =>
    cases rightTrace with
    | proper rightTrace =>
      obtain ⟨iso⟩ := currentIso
      rcases paired_current_chain_source_labels initial prefixHistory old labels selected sourceSafe
        sourceClosed currentClosed leftChain rightChain iso leftTrace rightTrace with safe | same | opposite
      · obtain ⟨_,es,fs,lc,rc,_eq,oldIso⟩ := safe
        exact ⟨es,fs,lc,rc,oldIso⟩
      · obtain ⟨_l,_r,_direction,_before,_head,es,fs,lc,rc,_eq,oldIso⟩ := same
        exact ⟨es,fs,lc,rc,oldIso⟩
      · obtain ⟨l,r,_la,_ra,different,_before,_head⟩ := opposite
        obtain ⟨_one,_other,le,re,_lt,_rt⟩ := actual_parent_opposite_cut_singleton
          initial (prefixHistory.append labels) currentClosed l r iso different
        have lr : l.reader=left.val := empty_prefix_at_proper left.property l.segment le
        have rr : r.reader=right.val := empty_prefix_at_proper right.property r.segment re
        have leftRead : PrerequisiteReadsDirected current left.val l.edge l.forward :=
          Eq.mp (congrArg (fun p=>PrerequisiteReadsDirected current p l.edge l.forward) lr) l.reading
        have rightRead : PrerequisiteReadsDirected current right.val r.edge r.forward :=
          Eq.mp (congrArg (fun p=>PrerequisiteReadsDirected current p r.edge r.forward) rr) r.reading
        obtain ⟨kind,lk,rk⟩ := sameKind
        exact False.elim (different ((leftRead.proper_kind.unique lk).trans
          (rightRead.proper_kind.unique rk).symm))

private theorem endpoint_is_proper
    {vertex : SyntaxIncidence.Vertex current}
    (available : ∃ es,EndpointChain current vertex es) :
    ∃ proper : SyntaxIncidence.ProperPosition current,vertex=some proper := by
  cases vertex with
  | none => obtain ⟨_es,impossible⟩ := available; exact False.elim impossible
  | some proper => exact ⟨proper,rfl⟩

private theorem reflect_proper_pair
    {original source current : LTerm} {prior ps F : List Path}
    {degree : Lambda.Labelled.Label} {marked : Marked}
    (initial : INIT original) (prefixHistory : History prior original source)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (labels : History ps source current)
    (selected : ∀ name ∈ F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (sourceClosed : Closed source.erase)
    (left right : SyntaxIncidence.ProperPosition current)
    {oldLeft oldRight : SyntaxIncidence.Vertex source}
    (leftTrace : BetaVertexHistoryPreimage labels (some left) oldLeft)
    (rightTrace : BetaVertexHistoryPreimage labels (some right) oldRight)
    (currentIso : SuccessfulEndpointIso current (labels.closed sourceClosed) (some left) (some right))
    (sameKind : ∃ kind,ProperKind current left kind ∧ProperKind current right kind) :
    SuccessfulEndpointIso source sourceClosed oldLeft oldRight := by
  cases leftTrace with
  | proper leftTrace =>
    cases rightTrace with
    | proper rightTrace =>
      obtain ⟨es,fs,lc,rc,iso⟩ := currentIso
      exact same_kind_old_endpoint_iso initial prefixHistory old labels selected sourceSafe
        sourceClosed (labels.closed sourceClosed) left right _ _ (.proper leftTrace) (.proper rightTrace)
        lc rc iso sameKind

theorem uniform_old_equal_auxiliary_endpoint_isos
    {original source current : LTerm}
    {prior ps F : List Path} {degree : Lambda.Labelled.Label} {marked : Marked}
    (initial : INIT original)
    (prefixHistory : History prior original source)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (labels : History ps source current)
    (selected : ∀ name ∈ F, source.degreeAt name = some degree)
    (sourceSafe : source.OuterBarsSafe (fun payload => payload ≠ degree))
    (sourceClosed : Closed source.erase)
    (left right : SyntaxIncidence.Edge current)
    (leftAux : AuxiliaryAt current left.val)
    (rightAux : AuxiliaryAt current right.val)
    (sameLabel : SyntaxIncidence.label current left = SyntaxIncidence.label current right)
    (sourceIso : SuccessfulEndpointIso current (labels.closed sourceClosed)
      (SyntaxIncidence.source current left) (SyntaxIncidence.source current right))
    (targetIso : SuccessfulEndpointIso current (labels.closed sourceClosed)
      (SyntaxIncidence.target current (labels.closed sourceClosed) left)
      (SyntaxIncidence.target current (labels.closed sourceClosed) right)) :
    ∃ (oldLeft oldRight : SyntaxIncidence.Edge source) (leftNode rightNode : LTerm),
      source.subterm oldLeft.val = some leftNode ∧
      source.subterm oldRight.val = some rightNode ∧
      BetaNodeHistoryPreimage labels left.val oldLeft.val ∧
      BetaNodeHistoryPreimage labels right.val oldRight.val ∧
      AuxiliaryAt source oldLeft.val ∧
      AuxiliaryAt source oldRight.val ∧
      leftNode.label = rightNode.label ∧
      SyntaxIncidence.label source oldLeft = SyntaxIncidence.label source oldRight ∧
      SuccessfulEndpointIso source sourceClosed
        (SyntaxIncidence.source source oldLeft) (SyntaxIncidence.source source oldRight) ∧
      SuccessfulEndpointIso source sourceClosed
        (SyntaxIncidence.target source sourceClosed oldLeft)
        (SyntaxIncidence.target source sourceClosed oldRight) := by
  obtain ⟨ln,ll⟩ := SyntaxIncidence.edge_lookup current left
  obtain ⟨rn,rl⟩ := SyntaxIncidence.edge_lookup current right
  have labelEq : ln.label=rn.label := by
    rw [SyntaxIncidence.label_of_lookup current left ll,
      SyntaxIncidence.label_of_lookup current right rl] at sameLabel
    exact sameLabel
  obtain ⟨lp,lo,lold,lt⟩ := labels.node_preimage_from_lookup ll
  obtain ⟨rp,ro,rold,rt⟩ := labels.node_preimage_from_lookup rl
  let le : SyntaxIncidence.Edge source := ⟨lp,by rw [←LTerm.erase_subterm,lold];rfl⟩
  let re : SyntaxIncidence.Edge source := ⟨rp,by rw [←LTerm.erase_subterm,rold];rfl⟩
  obtain ⟨ls,lsEq⟩ := endpoint_is_proper sourceIso.left_available
  obtain ⟨rs,rsEq⟩ := endpoint_is_proper sourceIso.right_available
  obtain ⟨ld,ldEq⟩ := endpoint_is_proper targetIso.left_available
  obtain ⟨rd,rdEq⟩ := endpoint_is_proper targetIso.right_available
  have lsSpec := SyntaxIncidence.source_spec current left
  have rsSpec := SyntaxIncidence.source_spec current right
  have ldSpec := SyntaxIncidence.target_spec current (labels.closed sourceClosed) left
  have rdSpec := SyntaxIncidence.target_spec current (labels.closed sourceClosed) right
  rw [lsEq] at lsSpec
  rw [rsEq] at rsSpec
  rw [ldEq] at ldSpec
  rw [rdEq] at rdSpec
  rw [lsEq,rsEq] at sourceIso
  rw [ldEq,rdEq] at targetIso
  obtain ⟨sk,tk,lsk,rsk,ltk,rtk⟩ := (prefixHistory.append labels).equal_label_endpoint_kinds
    initial ll rl labelEq lsSpec rsSpec ldSpec rdSpec
  obtain ⟨oldLD,oldLDSpec,ldTrace⟩ := lt.target_history ldSpec
  obtain ⟨oldRD,oldRDSpec,rdTrace⟩ := rt.target_history rdSpec
  have oldTargetIso := reflect_proper_pair initial prefixHistory old labels selected sourceSafe
    sourceClosed ld rd ldTrace rdTrace targetIso ⟨tk,ltk,rtk⟩
  have oldTarget : SuccessfulEndpointIso source sourceClosed
      (SyntaxIncidence.target source sourceClosed le) (SyntaxIncidence.target source sourceClosed re) := by
    rw [SyntaxIncidence.target_eq_of_spec source sourceClosed le oldLDSpec,
      SyntaxIncidence.target_eq_of_spec source sourceClosed re oldRDSpec]
    exact oldTargetIso
  obtain ⟨_leftOld,_leftAt,leftOldAux⟩ := lt.auxiliary_source ll leftAux
  obtain ⟨_rightOld,_rightAt,rightOldAux⟩ := rt.auxiliary_source rl rightAux
  have nodeEq : lo.label=ro.label := by
    by_cases safe : ln.label.OuterBarsSafe (fun x=>x≠degree)
    · have rightSafe : rn.label.OuterBarsSafe (fun x=>x≠degree) := labelEq ▸ safe
      have lu := old.safe_incoming_uncreated (DegreeAligned.initial source F) selected lt ll safe
      have ru := old.safe_incoming_uncreated (DegreeAligned.initial source F) selected rt rl rightSafe
      obtain ⟨a,atA,al⟩ := lu.source_label ll
      obtain ⟨b,atB,bl⟩ := ru.source_label rl
      have ae := Option.some.inj (atA.symm.trans lold)
      have be := Option.some.inj (atB.symm.trans rold)
      subst a;subst b
      exact al.trans (labelEq.trans bl.symm)
    · obtain ⟨a,b,atA,atB,same⟩ := old.equal_marked_node_origin_labels
        (DegreeAligned.initial source F) labels selected lt rt ll rl sourceSafe safe labelEq
      have ae := Option.some.inj (atA.symm.trans lold)
      have be := Option.some.inj (atB.symm.trans rold)
      subst a;subst b
      exact same
  have oldLabel : SyntaxIncidence.label source le=SyntaxIncidence.label source re := by
    rw [SyntaxIncidence.label_of_lookup source le lold,
      SyntaxIncidence.label_of_lookup source re rold]
    exact nodeEq
  have oldSource : SuccessfulEndpointIso source sourceClosed
      (SyntaxIncidence.source source le) (SyntaxIncidence.source source re) := by
    by_cases safe : ln.label.OuterBarsSafe (fun x=>x≠degree)
    · have rightSafe : rn.label.OuterBarsSafe (fun x=>x≠degree) := labelEq ▸ safe
      obtain ⟨_a,oldLS,_atA,_al,oldLSSpec,lsTrace⟩ :=
        old.safe_incoming_source_history selected lt ll safe lsSpec
      obtain ⟨_b,oldRS,_atB,_bl,oldRSSpec,rsTrace⟩ :=
        old.safe_incoming_source_history selected rt rl rightSafe rsSpec
      rw [SyntaxIncidence.source_eq_of_spec source le oldLSSpec,
        SyntaxIncidence.source_eq_of_spec source re oldRSSpec]
      exact reflect_proper_pair initial prefixHistory old labels selected sourceSafe sourceClosed
        ls rs lsTrace rsTrace sourceIso ⟨sk,lsk,rsk⟩
    · have rightMarked : ¬rn.label.OuterBarsSafe (fun x=>x≠degree) := by rw [←labelEq];exact safe
      exact marked_old_source_endpoint_iso sourceClosed old selected lt rt ll rl sourceSafe safe rightMarked
        (SyntaxIncidence.source_spec source le) (SyntaxIncidence.source_spec source re)
  exact ⟨le,re,lo,ro,lold,rold,lt,rt,leftOldAux,rightOldAux,nodeEq,oldLabel,oldSource,oldTarget⟩

theorem uniform_old_equal_auxiliary_source_pieces
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    {original source current : LTerm}
    {prior ps F : List Path} {degree : Lambda.Labelled.Label} {marked : Marked}
    (initial : INIT original)
    (prefixHistory : History prior original source)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (labels : History ps source current)
    (selected : ∀ name ∈ F, source.degreeAt name = some degree)
    (sourceSafe : source.OuterBarsSafe (fun payload => payload ≠ degree))
    (sourceClosed : Closed source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceJoint : JointRepresentation sourceClosed sourceSelection)
    (left right : SyntaxIncidence.Edge current)
    (leftAux : AuxiliaryAt current left.val)
    (rightAux : AuxiliaryAt current right.val)
    (sameLabel : SyntaxIncidence.label current left = SyntaxIncidence.label current right)
    (sourceIso : SuccessfulEndpointIso current (labels.closed sourceClosed)
      (SyntaxIncidence.source current left) (SyntaxIncidence.source current right))
    (targetIso : SuccessfulEndpointIso current (labels.closed sourceClosed)
      (SyntaxIncidence.target current (labels.closed sourceClosed) left)
      (SyntaxIncidence.target current (labels.closed sourceClosed) right)) :
    ∃ (oldLeft oldRight : SyntaxIncidence.Edge source) (leftNode rightNode : LTerm),
      source.subterm oldLeft.val = some leftNode ∧
      source.subterm oldRight.val = some rightNode ∧
      BetaNodeHistoryPreimage labels left.val oldLeft.val ∧
      BetaNodeHistoryPreimage labels right.val oldRight.val ∧
      AuxiliaryAt source oldLeft.val ∧
      AuxiliaryAt source oldRight.val ∧
      leftNode.label = rightNode.label ∧
      SyntaxIncidence.label source oldLeft = SyntaxIncidence.label source oldRight ∧
      SuccessfulEndpointIso source sourceClosed
        (SyntaxIncidence.source source oldLeft) (SyntaxIncidence.source source oldRight) ∧
      SuccessfulEndpointIso source sourceClosed
        (SyntaxIncidence.target source sourceClosed oldLeft)
        (SyntaxIncidence.target source sourceClosed oldRight) ∧
      (sourceSelection oldLeft).fragment.segments = (sourceSelection oldRight).fragment.segments := by
  obtain ⟨le,re,ln,rn,ll,rl,lt,rt,la,ra,nodeEq,labelEq,sourceIso,targetIso⟩ :=
    uniform_old_equal_auxiliary_endpoint_isos initial prefixHistory old labels selected sourceSafe
      sourceClosed left right leftAux rightAux sameLabel sourceIso targetIso
  have pieces : (sourceSelection le).fragment.segments=(sourceSelection re).fragment.segments := by
    exact Classical.byContradiction (fun different=>
      sourceJoint.2 le re la ra labelEq different ⟨sourceIso,targetIso⟩)
  exact ⟨le,re,ln,rn,ll,rl,lt,rt,la,ra,nodeEq,labelEq,sourceIso,targetIso,pieces⟩

end Lamping.AG
#print axioms Lamping.AG.same_kind_old_endpoint_iso
#print axioms Lamping.AG.uniform_old_equal_auxiliary_endpoint_isos
#print axioms Lamping.AG.uniform_old_equal_auxiliary_source_pieces

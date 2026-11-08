import Lamping.Lamping.ActionLambdaPrefix
import Lamping.Lamping.ExpandedTransparencySurgery
import Lamping.Lamping.SourceContextPrefixes
namespace Lamping.AG
open Graph
section Suffix
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Actual ordinary whole-path labels and a same-assignment shell construct
the ordinary binding suffix at the selected lambda occurrence. -/
theorem ordinary_binding_suffix (node : N) (ctx body bind : Port (g.label node).sort)
    (sort : (g.label node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody) (bindRole : HEq bind lamBind)
    (pre tail : List (Endpoint g)) (a middle b : Context)
    (labels : Labelling g (pre++(.inl ⟨node,body⟩)::tail) a b)
    (forward : Forward g (pre++(.inl ⟨node,body⟩)::tail))
    (prefixLabels : Labelling g pre a middle)
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (finish : (pre++(.inl ⟨node,body⟩)::tail).getLast?=some (g.wire (.inl ⟨node,bind⟩)))
    (shell : Context.SameShell (g.label node).index middle b) :
    ∃ binding : BindingLoop g ((.inl ⟨node,body⟩)::tail) middle b,binding.binder=node := by
  obtain ⟨expanded,binderEq⟩ := expanded_binding_suffix node ctx body bind sort ctxRole bodyRole bindRole
    pre tail a middle b labels.expanded forward.expanded prefixLabels.expanded prefixEnd finish shell
  have suffixLabels := Labelling.after_lambda_context node ctx body sort ctxRole bodyRole pre tail a middle b
    prefixLabels prefixEnd labels
  have atBody : (pre++(.inl ⟨node,body⟩)::tail)[pre.length]?=some (.inl ⟨node,body⟩) := by
    rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
    rfl
  have suffixForward := forward.suffix_at pre.length _ atBody
  simp only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at suffixForward
  exact ⟨⟨expanded.binder,expanded.isLam,expanded.body,expanded.bind,expanded.body_role,expanded.bind_role,
    expanded.start,expanded.finish,suffixLabels,suffixForward,expanded.shell⟩,binderEq⟩
end Suffix

private theorem primary_heq {f : Op} (lam : f=.lam) :
    HEq (Sum.inl () : Port (.op f)) (Sum.inl () : Port (.op .lam)) := by subst f; rfl

private theorem same_prefix {T : Type} (left right : List T) (e : T) (after tail : List T)
    (same : left++e::after=right++e::tail) (length : left.length=right.length) : left=right := by
  induction left generalizing right with
  | nil => cases right with
    | nil => rfl
    | cons h right => simp at length
  | cons h left ih => cases right with
    | nil => simp at length
    | cons k right =>
      obtain ⟨heads,rest⟩ := List.cons.inj same
      have lengths : left.length=right.length := by simpa only [List.length_cons,Nat.succ.injEq] using length
      have result := ih right rest lengths
      subst k
      exact congrArg (h::·) result

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
local notation "rhs" => s.right.net

private theorem outside_aux_end (e : Endpoint cut) (entry : s.Frontier)
    (arrival : (cut).wire e=.inr (.inl (.inr entry))) :
    site.outsideEnd e=site.net.wire (site.outsideEnd (.inr (.inl (.inr entry)))) := by
  have wired : site.net.wire (site.outsideEnd e)=site.outsideEnd (.inr (.inl (.inr entry))) := by
    rw [site.outsideEnd_wire,arrival]
  have same := congrArg site.net.wire.mate wired
  simpa only [Pairing.involutive] using same

/-- Same-assignment transparency at a copied lambda binding endpoint. The
pending block is an actual finite suffix; its entry/inverse/copy metadata are
subsequently filled by the real schema prefix classifiers. The old binder
prefix is selected by ordinary T, then its positive ordinal is reflected
through actual complete canonical blocks to the corresponding new prefix. -/
theorem PathSite.pending_copied_lambda_transparency (action : IsAction s) (lam : s.passive=.lam)
    {root : B} {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root)
    (bodyAux bindAux : Aux s.passive)
    (bodyRole : HEq (Sum.inr bodyAux : Port (.op s.passive)) lamBody)
    (bindRole : HEq (Sum.inr bindAux : Port (.op s.passive)) lamBind)
    {raw : List (PlugSegment cut rhs)} {input output : Context}
    (pending : PendingRhsBlock cut rhs raw input output)
    (rooted : raw.head?=some (.inl (.inr (.inl (.inl root)))))
    (entry : pending.enter=.inr bindAux)
    (lastBranch : Aux s.active) (copied : s.right.N)
    (lastCopy : ActionLambdaCopy site lastBranch copied)
    (targetBind : Port ((rhs).label copied).sort) (targetBindRole : HEq targetBind lamBind)
    (inverse : Traversal s.low (.op s.active) (.inl ()) (.inr lastBranch) pending.middle output)
    (finish : (raw.map (plugEnd (cut).label (rhs).label)).getLast?=
      some (site.reduce.wire (.inl ⟨.inr copied,targetBind⟩))) :
    ∃ (pre loop : List (Endpoint site.reduce)) (middle : Context) (binding : BindingLoop site.reduce loop middle output),
      raw.map (plugEnd (cut).label (rhs).label)=pre++loop ∧binding.binder=.inr copied ∧
      ∃ ctx : Port ((rhs).label copied).sort,HEq ctx (Sum.inl () : Port (.op .lam)) ∧
        pre.getLast?=some (site.reduce.wire (.inl ⟨.inr copied,ctx⟩)) ∧Labelling site.reduce pre input middle := by
  have preRoot : pending.pre.head?=some (.inl (.inr (.inl (.inl root)))) := pending.prefixHead.trans rooted
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨old,relation,oldLabels,oldRoot,oldLast⟩ := pending.prefixPath.action_canonical_lift site action principal
    (.inr (.inl (.inl root))) pending.last preRoot pending.prefixLast
  have endpoint := outside_aux_end site pending.last pending.enter pending.arrival
  rw [entry] at endpoint
  have oldFinish : old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr bindAux⟩)) := by
    rw [endpoint] at oldLast
    exact oldLast
  have oldForward := oldLabels.root_forward_of_flow flow root oldRoot positive
  obtain ⟨oldPre,oldLoop,oldMiddle,binding,oldSplit,binderEq,oldPreEnd,oldPrefix⟩ := oldT
    old input pending.middle (.inr (.inr ())) (.inl ()) (.inr bodyAux) (.inr bindAux)
    (congrArg Kind.op lam) (primary_heq lam) bodyRole bindRole oldRoot oldFinish oldForward oldLabels
  have oldBodyStart : oldLoop.head?=some (.inl ⟨.inr (.inr ()),.inr bodyAux⟩) := by
    rcases binding with ⟨binder,isLam,body,bind,hbody,hbind,start,ending,labels,fw,shell⟩
    dsimp at binderEq
    subst binder
    have same : body=.inr bodyAux := eq_of_heq (hbody.trans bodyRole.symm)
    rw [same] at start
    exact start
  obtain ⟨oldTail,loopSplit⟩ := List.head?_eq_some_iff.mp oldBodyStart
  have sourceSplit : old=oldPre++(.inl ⟨.inr (.inr ()),.inr bodyAux⟩)::oldTail := by rw [oldSplit,loopSplit]
  have preNonempty : oldPre≠[] := by intro empty; rw [empty] at oldPreEnd; cases oldPreEnd
  have atBody : old[oldPre.length]?=some (.inl ⟨.inr (.inr ()),.inr bodyAux⟩) := by
    rw [sourceSplit,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
    rfl
  obtain ⟨cutAt⟩ := relation.split_lambda_occurrence site lam pending.prefixPath bodyAux oldPre.length
    (List.length_pos_iff.mpr preNonempty) atBody
  have beforeEq : oldPre=cutAt.oldBefore++cutAt.front := by
    have length : (cutAt.oldBefore++cutAt.front).length=oldPre.length := by
      rw [List.length_append]; exact cutAt.position
    exact same_prefix oldPre (cutAt.oldBefore++cutAt.front) _ oldTail cutAt.oldAfter
      (sourceSplit.symm.trans cutAt.old_eq) length.symm
  obtain ⟨branch,node,ctx,body,targetPre,targetTail,newMiddle,copy,isLam,ctxRole,newBodyRole,targetPrefixSplit,targetCtxEnd,targetPrefix,writer⟩ :=
    cutAt.prefix_writer site lam bodyRole pending.prefixPath (by rw [←beforeEq]; exact oldPrefix)
  have shell : Context.SameShell s.high oldMiddle pending.middle := by
    have actual := binding.shell
    rw [binderEq] at actual
    exact actual
  obtain ⟨sameCopy,newShell⟩ := copy.binding_shell site lastCopy writer inverse shell
  subst copied
  have labels := (pending.labelling cut rhs).actual cut rhs
  have fullSplit : raw.map (plugEnd (cut).label (rhs).label)=targetPre++
      (.inl ⟨.inr node,body⟩)::(targetTail++(pending.inside.map Sum.inr).map (plugEnd (cut).label (rhs).label)) := by
    have mapped := congrArg (List.map (plugEnd (cut).label (rhs).label)) pending.equation
    have mapped' := mapped.trans List.map_append
    exact mapped'.trans (by rw [targetPrefixSplit]; simp only [List.append_assoc,List.cons_append])
  have physicalRoot : (raw.map (plugEnd (cut).label (rhs).label)).head?=some (.inr (.inl root)) := by
    rw [List.head?_map,rooted]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := labels.root_forward_of_flow newFlow root physicalRoot positive
  obtain ⟨newBinding,newBinder⟩ := ordinary_binding_suffix (g:=site.reduce) (.inr node) ctx body targetBind isLam
    ctxRole newBodyRole targetBindRole targetPre _ input newMiddle output
    (by rw [←fullSplit]; exact labels) (by rw [←fullSplit]; exact forward)
    targetPrefix targetCtxEnd (by rw [←fullSplit]; exact finish) newShell
  exact ⟨targetPre,_,newMiddle,newBinding,fullSplit,newBinder,ctx,ctxRole,targetCtxEnd,targetPrefix⟩
end
end Lamping.AG

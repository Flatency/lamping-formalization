import Lamping.Lamping.ActionLambdaPrefixWords
import Lamping.Lamping.ActionPendingWords
import Lamping.Lamping.CopiedLambdaTransparency
namespace Lamping.AG
open Graph Lambda
private theorem suffix_of_binder_eq
    {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    {g : Net signature N D U} {es pre loop : List (Endpoint g)} {a middle b : Context}
    (binding : BindingLoop g loop middle b) (node : N) (binderEq : binding.binder=node)
    (ctx : Port (g.label node).sort) (role : HEq ctx (Sum.inl () : Port (.op .lam)))
    (split : es=pre++loop) (last : pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (labels : Labelling g pre a middle) : BindingSuffix g es (binderDepth (accessWord g loop)) := by
  rcases binding with ⟨binder,isLam,body,bind,bodyRole,bindRole,start,finish,proper,forward,shell⟩
  dsimp at binderEq
  subst binder
  exact ⟨pre,loop,a,middle,b,
    ⟨node,isLam,body,bind,bodyRole,bindRole,start,finish,proper,forward,shell⟩,
    ctx,split,role,last,labels,rfl⟩

private theorem body_word_split
    {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    (g : Net signature N D U) (pre : List (Endpoint g)) (node : N)
    (body : Port (g.label node).sort) (tail : List (Endpoint g))
    (sort : (g.label node).sort=.op .lam) (role : HEq body lamBody) (nonempty : pre≠[]) :
    accessWord g (pre++(.inl ⟨node,body⟩)::tail)=
      accessWord g pre++(.body::accessWord g ((.inl ⟨node,body⟩)::tail)) := by
  have token : arrivalWord g (.inl ⟨node,body⟩)=[.body] := by
    have generic : ∀ (kind : Kind) (p : Port kind),kind=.op .lam → HEq p lamBody →
        (match kind,p with
        | .op .app,.inl () => [Step.fn]
        | .op .app,.inr true => [Step.arg]
        | .op .lam,.inr true => [Step.body]
        | _,_ => [])=[Step.body] := by
      intro kind p same port
      subst kind
      have eqs : p=lamBody := eq_of_heq port
      subst p
      rfl
    exact generic _ _ sort role
  rw [accessWord_append g _ _ nonempty]
  simp only [List.flatMap_cons,token,List.singleton_append,accessWord]

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
theorem PathSite.pending_copied_lambda_binding_words (action : IsAction s) (lam : s.passive=.lam)
    {root : B} {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root)
    (bodyAux bindAux : Aux s.passive)
    (bodyRole : HEq (Sum.inr bodyAux : Port (.op s.passive)) lamBody)
    (bindRole : HEq (Sum.inr bindAux : Port (.op s.passive)) lamBind)
    {raw : List (PlugSegment cut rhs)} {input output : Context}
    (pending : PendingRhsBlock cut rhs raw input output)
    (rooted : raw.head?=some (.inl (.inr (.inl (.inl root)))))
    (insideTokens : accessTokens rhs pending.inside=[])
    (entry : pending.enter=.inr bindAux)
    (lastBranch : Aux s.active) (copied : s.right.N)
    (lastCopy : ActionLambdaCopy site lastBranch copied)
    (targetBind : Port ((rhs).label copied).sort) (targetBindRole : HEq targetBind lamBind)
    (inverse : Traversal s.low (.op s.active) (.inl ()) (.inr lastBranch) pending.middle output)
    (finish : (raw.map (plugEnd (cut).label (rhs).label)).getLast?=
      some (site.reduce.wire (.inl ⟨.inr copied,targetBind⟩))) :
    ∃ old,Labelling site.net old input pending.middle ∧
      old.head?=some (.inr (.inl root)) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr bindAux⟩)) ∧
      accessWord site.reduce (raw.map (plugEnd (cut).label (rhs).label))=accessWord site.net old ∧
      ∃ index,BindingSuffix site.net old index ∧
        BindingSuffix site.reduce (raw.map (plugEnd (cut).label (rhs).label)) index := by
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
  obtain ⟨branch,node,ctx,body,targetPre,targetTail,newMiddle,copy,isLam,ctxRole,newBodyRole,targetPrefixSplit,targetCtxEnd,targetPrefix,writer,prefixWord⟩ :=
    cutAt.prefix_writer_word site lam bodyRole pending.prefixPath (by rw [←beforeEq]; exact oldPrefix)
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
  have prefixWords := relation.word site pending.prefixPath
  have preNonemptyRaw : pending.pre≠[] := by intro empty; rw [empty] at preRoot; cases preRoot
  have mapNonempty : pending.pre.map (plugEnd (cut).label (rhs).label)≠[] := by
    cases eqs : pending.pre with
    | nil => exact False.elim (preNonemptyRaw eqs)
    | cons e es => simp
  have wholeWord := congrArg
    (fun es => accessWord site.reduce (es.map (plugEnd (cut).label (rhs).label))) pending.equation
  simp only [List.map_append] at wholeWord
  rw [accessWord_append site.reduce _ _ mapNonempty,prefixWords] at wholeWord
  have rhsTokens : accessTokens site.reduce
      ((pending.inside.map Sum.inr).map (plugEnd (cut).label (rhs).label))=[] := by
    rw [List.map_map]
    exact (accessTokens_plugRight cut rhs pending.inside).trans insideTokens
  change accessWord site.reduce (raw.map (plugEnd (cut).label (rhs).label))=
    accessWord site.net old++accessTokens site.reduce
      ((pending.inside.map Sum.inr).map (plugEnd (cut).label (rhs).label)) at wholeWord
  rw [rhsTokens,List.append_nil] at wholeWord
  have sourceParts : accessWord site.net old=
      accessWord site.net oldPre++(.body::accessWord site.net oldLoop) := by
    have eqs := congrArg (accessWord site.net) sourceSplit
    have tokens := body_word_split site.net oldPre (.inr (.inr ())) (.inr bodyAux) oldTail
      (congrArg Kind.op lam) bodyRole preNonempty
    simpa only [←loopSplit] using eqs.trans tokens
  have targetPreNonempty : targetPre≠[] := by intro empty; rw [empty] at targetCtxEnd; cases targetCtxEnd
  have targetParts : accessWord site.reduce (raw.map (plugEnd (cut).label (rhs).label))=
      accessWord site.reduce targetPre++(.body::accessWord site.reduce
        ((.inl ⟨.inr node,body⟩)::(targetTail++(pending.inside.map Sum.inr).map (plugEnd (cut).label (rhs).label)))) := by
    exact (congrArg (accessWord site.reduce) fullSplit).trans
      (body_word_split site.reduce targetPre (.inr node) body _ isLam newBodyRole targetPreNonempty)
  rw [←beforeEq] at prefixWord
  rw [prefixWord] at targetParts
  have equal := List.append_cancel_left (targetParts.symm.trans (wholeWord.trans sourceParts))
  have loopWord := (List.cons.inj equal).2
  have oldSuffix := suffix_of_binder_eq binding (.inr (.inr ())) binderEq (.inl ())
    (primary_heq lam) oldSplit oldPreEnd oldPrefix
  have newSuffix := suffix_of_binder_eq newBinding (.inr node) newBinder ctx ctxRole fullSplit targetCtxEnd targetPrefix
  refine ⟨old,oldLabels,oldRoot,oldFinish,wholeWord,binderDepth (accessWord site.net oldLoop),oldSuffix,?_⟩
  simpa only [loopWord] using newSuffix
end
end Lamping.AG

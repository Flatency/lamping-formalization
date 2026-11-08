import Lamping.Lamping.ExpandedTransparencySurgery
import Lamping.Lamping.BetaDetourCoherence
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

private theorem lambda_label (node : N) (sort : (g.label node).sort=.op .lam) :
    g.label node=label .lam (g.label node).index := by
  cases h : g.label node with
  | mk kind index =>
    have same : kind=.op .lam := by simpa only [h] using sort
    subst kind
    rfl

private theorem same_lambda_port (left right : N) (same : left=right)
    (p : Port (g.label left).sort) (q : Port (g.label right).sort)
    (canonical : Port (.op .lam)) (hp : HEq p canonical) (hq : HEq q canonical) :
    (.inl ⟨left,p⟩ : Endpoint g)=.inl ⟨right,q⟩ := by
  subst right
  have equal : p=q := eq_of_heq (hp.trans hq.symm)
  subst q
  rfl

private theorem lambda_app_ends_differ (edge : BetaEdge g) (node : N)
    (ctx : Port (g.label node).sort) (sort : (g.label node).sort=.op .lam) :
    g.wire (.inl ⟨node,ctx⟩)≠g.wire (.inl ⟨edge.app,edge.appCtx⟩) := by
  intro same
  have ports := congrArg g.wire same
  simp only [Pairing.involutive] at ports
  have nodes : node=edge.app := congrArg Sigma.fst (Sum.inl.inj ports)
  have kinds := congrArg (fun n => (g.label n).sort) nodes
  change (g.label node).sort=(g.label edge.app).sort at kinds
  rw [sort,edge.appLabel] at kinds
  cases kinds

private theorem last_append_nonempty {T : Type} (pre tail : List T) (nonempty : tail≠[]) :
    (pre++tail).getLast?=tail.getLast? := by
  cases point : tail.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp point))
  | some e => simp only [List.getLast?_append,point,Option.some_or]

/-- The first-backward induction step for transparency. Its smaller argument
decomposition is consumed in its own assignment. If its binder precedes the
ordinary app prefix, ordinary shell reflection changes that seam; otherwise
the literal suffix loop is retained and the new prefix is actually spliced.
This lemma does not assert the smaller argument's transparency. -/
theorem BetaEdge.transparency_splice (edge : BetaEdge g) (independence : Independence g root)
    (pre loop suffix : List (Endpoint g)) (a argumentInput seam bodyEnd b : Context)
    (appLabels : Labelling g pre a seam) (argumentPrefix : Labelling g pre argumentInput bodyEnd)
    (appForward : Forward g pre)
    (appEnd : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (shell : Context.SameShell edge.index seam bodyEnd)
    (bodyLabels : Labelling g (pre++edge.principal++loop) a bodyEnd)
    (loopEnd : loop.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)))
    (node : N) (ctx body bind : Port (g.label node).sort)
    (sort : (g.label node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body AG.lamBody) (bindRole : HEq bind AG.lamBind)
    (fullLabels : ExpandedLabelling g
      (pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix) a b)
    (fullForward : ExpandedForward g
      (pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix))
    (finish : (pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix).getLast?=
      some (g.wire (.inl ⟨node,bind⟩)))
    (candidate tail : List (Endpoint g)) (middle : Context)
    (binding : ExpandedBindingLoop g tail middle b) (sameBinder : binding.binder=node)
    (argumentSplit : pre++edge.argEnd::suffix=candidate++tail)
    (candidateLabels : ExpandedLabelling g candidate argumentInput middle)
    (candidateEnd : candidate.getLast?=some (g.wire (.inl ⟨node,ctx⟩))) :
    ∃ (newPre newLoop : List (Endpoint g)) (newMiddle : Context)
      (newBinding : ExpandedBindingLoop g newLoop newMiddle b),
      pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix=newPre++newLoop ∧
      newBinding.binder=node ∧ newPre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)) ∧
      ExpandedLabelling g newPre a newMiddle := by
  have candidateNonempty : candidate≠[] := by intro empty; rw [empty] at candidateEnd; cases candidateEnd
  have tailStart : tail.head?=some (.inl ⟨node,body⟩) :=
    binding.start.trans (congrArg some (same_lambda_port binding.binder node sameBinder
      binding.body body AG.lamBody binding.body_role bodyRole))
  have candidateShell : Context.SameShell (g.label node).index middle b := by
    rw [←sameBinder]
    exact binding.shell
  rcases compare_path_prefixes candidate pre tail (edge.argEnd::suffix) argumentSplit.symm with
    ⟨between,preSplit,tailSplit⟩ |⟨between,candidateSplit,argumentTailSplit⟩
  · cases between with
    | nil =>
      have same : pre=candidate := by simpa only [List.append_nil] using preSplit
      have endEq : candidate.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)) := by
        rw [←same]; exact appEnd
      have ends := candidateEnd.symm.trans endEq
      exact False.elim (lambda_app_ends_differ edge node ctx sort (Option.some.inj ends))
    | cons first between =>
      have firstEq : first=(.inl ⟨node,body⟩ : Endpoint g) := by
        rw [tailSplit] at tailStart
        exact Option.some.inj tailStart
      subst first
      have ordinaryLabels : Labelling g (candidate++(.inl ⟨node,body⟩)::between) a seam := by
        rw [←preSplit]; exact appLabels
      have ordinaryForward : Forward g (candidate++(.inl ⟨node,body⟩)::between) := by
        rw [←preSplit]; exact appForward
      obtain ⟨actualMiddle,actualPrefix⟩ := ordinaryLabels.prefix candidateNonempty
      have prefixForward := ordinaryForward.prefix_of_append candidateNonempty
      have changedPrefix := candidateLabels.ordinary_of_forward g prefixForward
      have reflected := independence.reflect_lambda_prefix edge node ctx body (g.label node).index
        (lambda_label node sort) ctxRole bodyRole candidate between a actualMiddle seam
        argumentInput middle bodyEnd actualPrefix changedPrefix candidateEnd ordinaryLabels
        (by rw [←preSplit]; exact argumentPrefix) ordinaryForward
        (by rw [←preSplit]; exact appEnd) shell
      have actualShell : Context.SameShell (g.label node).index actualMiddle b := by
        intro k low
        exact (reflected k low).trans (candidateShell k low)
      let rest := between++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix
      have fullEq : pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix=
          candidate++(.inl ⟨node,body⟩)::rest := by
        simp only [preSplit,rest,List.append_assoc,List.cons_append]
      have labels : ExpandedLabelling g (candidate++(.inl ⟨node,body⟩)::rest) a b := by
        rw [←fullEq]; exact fullLabels
      obtain ⟨newBinding,binderEq⟩ := expanded_binding_suffix node ctx body bind sort ctxRole bodyRole bindRole
        candidate rest a actualMiddle b labels (by rw [←fullEq]; exact fullForward)
        actualPrefix.expanded candidateEnd (by rw [←fullEq]; exact finish) actualShell
      exact ⟨candidate,_,actualMiddle,newBinding,fullEq,binderEq,candidateEnd,actualPrefix.expanded⟩
  · cases between with
    | nil =>
      have same : candidate=pre := by simpa only [List.append_nil] using candidateSplit
      have endEq : candidate.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)) := by
        rw [same]; exact appEnd
      have ends := candidateEnd.symm.trans endEq
      exact False.elim (lambda_app_ends_differ edge node ctx sort (Option.some.inj ends))
    | cons first between =>
      have firstEq : first=edge.argEnd := (List.cons.inj argumentTailSplit).1.symm
      subst first
      have splitRest : suffix=between++tail := (List.cons.inj argumentTailSplit).2
      have labels : ExpandedLabelling g (pre++edge.argEnd::between) argumentInput middle := by
        rw [←candidateSplit]; exact candidateLabels
      have after := edge.argument_tail_labeling pre between argumentPrefix.expanded appEnd labels
      have newLabels := edge.insert_labeling pre loop between bodyLabels.expanded loopEnd after
      let newPre := pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++between
      have fullEq : pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix=newPre++tail := by
        simp only [newPre,splitRest,List.append_assoc]
      have newEnd : newPre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)) := by
        have candidateLast : (edge.argEnd::between).getLast?=some (g.wire (.inl ⟨node,ctx⟩)) := by
          rw [candidateSplit,last_append_nonempty pre _ (by simp)] at candidateEnd
          exact candidateEnd
        have unchanged := last_append_nonempty (pre++edge.principal++loop++edge.reverseRoute)
          (edge.argEnd::between) (by simp)
        have result := unchanged.trans candidateLast
        simpa only [newPre,List.append_assoc,List.singleton_append] using result
      exact ⟨newPre,tail,middle,binding,fullEq,sameBinder,newEnd,newLabels⟩
end
end Lamping.AG

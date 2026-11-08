import Lamping.Lamping.ForwardCanonicalOriginalFragments

namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
variable {source current : LTerm}

private theorem head_nonterminal (chain : PrerequisiteChain t start (edge::after))
    (more : after≠[]) : ¬PrerequisiteRedexEdge t edge := by
  obtain ⟨before,last,split,_redex,earlier⟩ := chain.redex_only_last
  cases before with
  | nil =>
      simp only [List.nil_append,List.cons.injEq] at split
      exact False.elim (more split.2)
  | cons head tail =>
      have same : edge=head := (List.cons.inj split).1
      exact earlier edge (by rw [same];exact List.mem_cons_self)

private theorem first_bad_split_unique {A : Type} (P : A→Prop)
    {bs cs : List A} {e f : A} {as ds : List A}
    (same : bs++e::as=cs++f::ds)
    (leftSafe : ∀x∈bs,P x) (rightSafe : ∀x∈cs,P x)
    (leftBad : ¬P e) (rightBad : ¬P f) : bs=cs ∧e=f ∧as=ds := by
  induction bs generalizing cs with
  | nil =>
      cases cs with
      | nil => exact ⟨rfl,(List.cons.inj same).1,(List.cons.inj same).2⟩
      | cons head tail =>
          have eq : e=head := (List.cons.inj same).1
          exact False.elim (leftBad (eq ▸ rightSafe head List.mem_cons_self))
  | cons head tail ih =>
      cases cs with
      | nil =>
          have eq : head=f := (List.cons.inj same).1
          exact False.elim (rightBad (eq ▸ leftSafe head List.mem_cons_self))
      | cons other rest =>
          have parts := List.cons.inj same
          have answer := ih parts.2 (fun x inside=>leftSafe x (List.mem_cons_of_mem _ inside))
            (fun x inside=>rightSafe x (List.mem_cons_of_mem _ inside))
          exact ⟨by rw [parts.1,answer.1],answer.2⟩

private theorem cut_bad (cut : ActualUnsafeMarkerCut F ps source current degree start edges) :
    ¬degreeReadSafe degree (current.labelAt cut.edge) := by
  intro safe
  exact cut.marked (safe cut.node.label (by simp only [LTerm.labelAt,cut.lookup,Option.map_some]))

private theorem cut_ext
    (left right : ActualUnsafeMarkerCut F ps source current degree start edges)
    (before : left.before=right.before) (edge : left.edge=right.edge)
    (after : left.after=right.after) (reader : left.reader=right.reader)
    (node : left.node=right.node) (direction : left.forward=right.forward) : left=right := by
  cases left
  cases right
  cases before
  cases edge
  cases after
  cases reader
  cases node
  cases direction
  rfl

/-- SAME actual start/list fixes its nonterminal first unsafe cut, including
TRUE function-parent cancellation and FALSE literal reader equality. -/
theorem ActualUnsafeMarkerCut.nonterminal_unique
    (left right : ActualUnsafeMarkerCut F ps source current degree start edges)
    (more : left.after≠[]) : left=right := by
  obtain ⟨before,edge,after⟩ := first_bad_split_unique
    (fun p=>degreeReadSafe degree (current.labelAt p))
    (left.split.symm.trans right.split) left.safeBefore right.safeBefore (cut_bad left) (cut_bad right)
  have rightMore : right.after≠[] := fun empty=>more (after.trans empty)
  have direction := left.reading.nonredex_direction_eq right.reading
    (head_nonterminal left.remaining more) (head_nonterminal right.remaining rightMore)
    (congrArg List.getLast? edge)
  have reader : left.reader=right.reader := by
    cases sign : left.forward with
    | false =>
        have ld : left.edge=left.reader := by simpa only [sign] using left.reading.2
        have rd : right.edge=right.reader := by simpa only [←direction,sign] using right.reading.2
        exact ld.symm.trans (edge.trans rd)
    | true =>
        have ld : left.edge=left.reader++[.fn] := by simpa only [sign] using left.reading.2
        have rd : right.edge=right.reader++[.fn] := by simpa only [←direction,sign] using right.reading.2
        exact List.append_cancel_right (ld.symm.trans (edge.trans rd))
  have node : left.node=right.node := Option.some.inj (left.lookup.symm.trans (edge ▸ right.lookup))
  exact cut_ext left right before edge after reader node direction

/-- Exact incidence and SAME operational ancestry determine the SOURCE
proper vertex and its complete literal chain. No equal-label coordinate rule. -/
theorem CanonicalAfterFarOutput.source_data_unique
    {labels : History ps source current}
    {cut : ActualUnsafeMarkerCut F ps source current degree start edges}
    {snapshot : IncomingIncidenceSnapshot current cut.edge}
    (left right : CanonicalAfterFarOutput labels cut snapshot) :
    left.currentProper=right.currentProper ∧left.sourceProper=right.sourceProper ∧
      left.sourceEdges=right.sourceEdges := by
  have currentEq : left.currentProper=right.currentProper :=
    Option.some.inj (left.farEq.symm.trans right.farEq)
  have leftTrace : BetaNodeHistoryPreimage labels right.currentProper.val left.sourceProper.val := by
    rw [←currentEq];exact left.nodeTrace
  have sourcePath := leftTrace.unique right.nodeTrace
  have sourceEq : left.sourceProper=right.sourceProper := Subtype.ext sourcePath
  have leftChain : PrerequisiteChain source right.sourceProper.val left.sourceEdges := by
    rw [←sourceEq];exact left.sourceChain
  exact ⟨currentEq,sourceEq,leftChain.unique right.sourceChain⟩

/-- Reuse existing B2 good on these EXACT given cut/snapshot/canonical
outputs. The parent chains are internally supplied by the genuine prefixes. -/
theorem actual_given_parent_canonical_far_comparison
    {initialSource source current : LTerm} {prior ps F : List Path} {degree : Label} {n : Marked}
    (initial : INIT initialSource) (prefixHistory : History prior initialSource source)
    (sourceClosed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftCut : ActualUnsafeMarkerCut F ps source current degree leftStart leftEdges)
    (rightCut : ActualUnsafeMarkerCut F ps source current degree rightStart rightEdges)
    (leftMore : leftCut.after≠[]) (rightMore : rightCut.after≠[])
    (leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge)
    (rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge)
    (left : CanonicalAfterFarOutput labels leftCut leftSnapshot)
    (right : CanonicalAfterFarOutput labels rightCut rightSnapshot)
    (wholeIso : ChainIncidenceIso
      (chainSyntaxIncidence current (labels.closed sourceClosed) leftEdges)
      (chainSyntaxIncidence current (labels.closed sourceClosed) rightEdges)) :
    CanonicalFarFullComparison sourceClosed left right := by
  have leftChain : PrerequisiteChain current leftStart leftEdges := by
    rw [leftCut.split];exact leftCut.segment.close leftCut.remaining
  have rightChain : PrerequisiteChain current rightStart rightEdges := by
    rw [rightCut.split];exact rightCut.segment.close rightCut.remaining
  rcases actual_parent_cuts_canonical_far_comparison initial prefixHistory sourceClosed old labels
      selected sourceSafe leftChain rightChain wholeIso with safe | cuts
  · apply False.elim
    apply cut_bad leftCut
    apply safe.1 leftCut.edge
    exact Eq.mpr (congrArg (fun xs : List Path=>leftCut.edge∈xs) leftCut.split)
      (List.mem_append_right _ List.mem_cons_self)
  · obtain ⟨lc,rc,_length,_before,_head,_after,result⟩ := cuts
    have le := leftCut.nonterminal_unique lc leftMore
    have re := rightCut.nonterminal_unique rc rightMore
    cases le
    cases re
    rcases result with empty | more
    · exact False.elim (leftMore empty.1)
    · obtain ⟨_lm,_rm,ls,rs,l,r,good⟩ := more
      have lshot := ls.unique leftSnapshot
      have rshot := rs.unique rightSnapshot
      cases lshot
      cases rshot
      obtain ⟨_lc,_ls,leftEdgesEq⟩ := l.source_data_unique left
      obtain ⟨_rc,_rs,rightEdgesEq⟩ := r.source_data_unique right
      simpa only [CanonicalFarFullComparison,leftEdgesEq,rightEdgesEq] using good

end Lamping.AG

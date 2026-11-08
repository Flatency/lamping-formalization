import Lamping.Lamping.PairedCurrentChainSourceLabels
import Lamping.Lamping.BoundedAfterPhysicalComparison
import Lamping.Lamping.ActualPrerequisiteSignedSlots

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
variable {source current : LTerm}

private theorem cut_bad (cut : ActualUnsafeMarkerCut F ps source current degree start es) :
    ¬degreeReadSafe degree (current.labelAt cut.edge) := by
  intro safe
  exact cut.marked (safe cut.node.label (by simp only [LTerm.labelAt,cut.lookup,Option.map_some]))

private theorem first_bad_split {A : Type} (P : A→Prop)
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

private theorem cut_labels_align
    (left : ActualUnsafeMarkerCut F ps source current degree ls les)
    (right : ActualUnsafeMarkerCut F ps source current degree rs res)
    (same : les.map current.labelAt=res.map current.labelAt) :
    left.before.map current.labelAt=right.before.map current.labelAt ∧
      current.labelAt left.edge=current.labelAt right.edge ∧
      left.after.map current.labelAt=right.after.map current.labelAt := by
  have l := congrArg (List.map current.labelAt) left.split
  have r := congrArg (List.map current.labelAt) right.split
  have aligned : left.before.map current.labelAt++current.labelAt left.edge::left.after.map current.labelAt=
      right.before.map current.labelAt++current.labelAt right.edge::right.after.map current.labelAt := by
    simpa only [List.map_append,List.map_cons] using l.symm.trans (same.trans r)
  apply first_bad_split (degreeReadSafe degree) aligned
  · intro label member
    obtain ⟨edge,inside,rfl⟩ := List.mem_map.mp member
    exact left.safeBefore edge inside
  · intro label member
    obtain ⟨edge,inside,rfl⟩ := List.mem_map.mp member
    exact right.safeBefore edge inside
  · exact cut_bad left
  · exact cut_bad right

/-- A terminal remainder is a genuine singleton chain at its actual reader.
Whole-parent iso supplies its singleton iso, without a sign or kind premise. -/
theorem actual_terminal_cut_singletons
    {initialSource oldSource current : LTerm} {historySites F ps : List Path} {degree : Label}
    (initial : INIT initialSource) (fullHistory : History historySites initialSource current)
    (closed : Closed current.erase)
    (left : ActualUnsafeMarkerCut F ps oldSource current degree ls les)
    (right : ActualUnsafeMarkerCut F ps oldSource current degree rs res)
    (leftTerminal : left.after=[]) (rightTerminal : right.after=[])
    (wholeIso : ChainIncidenceIso (chainSyntaxIncidence current closed les)
      (chainSyntaxIncidence current closed res)) :
    ∃_lc : PrerequisiteChain current left.reader [left.edge],
    ∃_rc : PrerequisiteChain current right.reader [right.edge],
      current.labelAt left.edge=current.labelAt right.edge ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence current closed [left.edge])
        (chainSyntaxIncidence current closed [right.edge]) := by
  have lp : PrerequisiteChain current ls les := by rw [left.split];exact left.segment.close left.remaining
  have rp : PrerequisiteChain current rs res := by rw [right.split];exact right.segment.close right.remaining
  have labels := actual_chain_labels_forward fullHistory initial closed lp rp wholeIso
  have same := (cut_labels_align left right labels).2.1
  have lc : PrerequisiteChain current left.reader [left.edge] := by simpa only [leftTerminal] using left.remaining
  have rc : PrerequisiteChain current right.reader [right.edge] := by simpa only [rightTerminal] using right.remaining
  refine ⟨lc,rc,same,?_⟩
  apply actual_chain_iso_of_labels fullHistory initial closed lc rc
  simp only [List.map_cons,List.map_nil,same]

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- This is a strictly shorter CURRENT-chain call. At whole length one its
strict bound is false, and no terminal base conclusion is asserted. -/
theorem actual_terminal_cut_physical_below
    {initialSource oldSource current : LTerm} {historySites F ps : List Path} {degree : Label}
    (initial : INIT initialSource) (fullHistory : History historySites initialSource current)
    (closed : Closed current.erase) (selection : OccurrenceFragmentSelection current g root)
    (left : ActualUnsafeMarkerCut F ps oldSource current degree ls les)
    (right : ActualUnsafeMarkerCut F ps oldSource current degree rs res)
    (leftTerminal : left.after=[]) (rightTerminal : right.after=[])
    (wholeIso : ChainIncidenceIso (chainSyntaxIncidence current closed les)
      (chainSyntaxIncidence current closed res))
    (multi : 1<max les.length res.length)
    (ih : ChainForwardBelow closed selection (max les.length res.length)) :
    ∃lc : PrerequisiteChain current left.reader [left.edge],
    ∃rc : PrerequisiteChain current right.reader [right.edge],
      SameChainRepresentation selection lc rc := by
  obtain ⟨lc,rc,_same,iso⟩ := actual_terminal_cut_singletons initial fullHistory closed
    left right leftTerminal rightTerminal wholeIso
  exact ⟨lc,rc,ih lc rc (by simpa only [List.length_singleton,Nat.max_self] using multi) iso⟩
end

/-- Opposite reads in actual isomorphic parents can only occur in the whole
singleton base. The walk anchors and actual first-bad ordinal are internal. -/
theorem actual_parent_opposite_cut_singleton
    {initialSource oldSource current : LTerm} {historySites F ps : List Path} {degree : Label}
    (initial : INIT initialSource) (fullHistory : History historySites initialSource current)
    (closed : Closed current.erase)
    (left : ActualUnsafeMarkerCut F ps oldSource current degree ls les)
    (right : ActualUnsafeMarkerCut F ps oldSource current degree rs res)
    (wholeIso : ChainIncidenceIso (chainSyntaxIncidence current closed les)
      (chainSyntaxIncidence current closed res)) (opposite : left.forward≠right.forward) :
    les.length=1 ∧res.length=1 ∧left.before=[] ∧right.before=[] ∧left.after=[] ∧right.after=[] := by
  have lp : PrerequisiteChain current ls les := by rw [left.split];exact left.segment.close left.remaining
  have rp : PrerequisiteChain current rs res := by rw [right.split];exact right.segment.close right.remaining
  have labels := actual_chain_labels_forward fullHistory initial closed lp rp wholeIso
  have lengths : les.length=res.length := by simpa only [List.length_map] using congrArg List.length labels
  have before := (cut_labels_align left right labels).1
  have ordinal : left.before.length=right.before.length := by simpa only [List.length_map] using congrArg List.length before
  have notMulti : ¬1<les.length := by
    intro multi
    obtain ⟨lf,ss,vs,lt,lwalk⟩ := lp.signed_path
    obtain ⟨rf,ts,ws,rt,rwalk⟩ := rp.signed_path
    have signs := SignedProperWalk.signs_eq_of_multiedge fullHistory initial lp rp lwalk rwalk labels multi
    obtain ⟨_a,_ap,_av,lsign⟩ := left.signed_slot lwalk lt
    obtain ⟨_b,_bp,_bv,rsign⟩ := right.signed_slot rwalk rt
    apply opposite
    rw [signs,ordinal] at lsign
    exact Option.some.inj (lsign.symm.trans rsign)
  have positive : 0<les.length := by
    by_cases positive : 0<les.length
    · exact positive
    · exact False.elim (lp.nonempty (List.length_eq_zero_iff.mp (by omega)))
  have one : les.length=1 := by omega
  have other : res.length=1 := lengths ▸ one
  have ll := congrArg List.length left.split
  have rl := congrArg List.length right.split
  simp only [List.length_append,List.length_cons] at ll rl
  exact ⟨one,other,List.length_eq_zero_iff.mp (by omega),List.length_eq_zero_iff.mp (by omega),
    List.length_eq_zero_iff.mp (by omega),List.length_eq_zero_iff.mp (by omega)⟩

private theorem zero_prefix_finish (segment : PrerequisitePrefix t start es finish)
    (empty : es=[]) (proper : ∀stamp index,t.subterm start≠some (.var stamp index)) : finish=start := by
  cases segment with
  | refl => rfl
  | app => cases empty
  | lam => cases empty
  | var lookup => exact False.elim (proper _ _ lookup)

private theorem lambda_singleton_false
    (cut : ActualUnsafeMarkerCut F ps source current degree edge [edge])
    (lookup : current.subterm edge=some (.lam stamp body)) : cut.forward=false := by
  have size := congrArg List.length cut.split
  simp only [List.length_append,List.length_cons,List.length_nil] at size
  have empty : cut.before=[] := List.length_eq_zero_iff.mp (by omega)
  have reader : cut.reader=edge := zero_prefix_finish cut.segment empty (by
    intro a i atVar
    rw [lookup] at atVar
    cases atVar)
  have head : cut.edge=edge := by
    have split := cut.split
    rw [empty,List.nil_append] at split
    exact (List.cons.inj split).1.symm
  cases direction : cut.forward with
  | false => rfl
  | true =>
      have eq := cut.reading.2
      rw [direction] at eq
      change cut.edge=cut.reader++[.fn] at eq
      have length := congrArg List.length eq
      simp only [head,reader,List.length_append,List.length_singleton] at length
      omega

/-- Uniform FALSE companions at the actual redex lambdas compare ONLY their
OWN original node chains. Original APP/lam parent-start iso is not asserted. -/
theorem actual_redex_lambda_origin_chain_comparison
    {initialSource source current : LTerm} {prior ps F : List Path} {degree : Label} {marked : Marked}
    {lp rp oldLeft oldRight : Path} {la ll ra rl : Label} {lb larg rb rarg : LTerm}
    (initial : INIT initialSource) (prefixHistory : History prior initialSource source)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree)) (closed : Closed source.erase)
    (leftRedex : current.subterm lp=some (.app la (.lam ll lb) larg))
    (rightRedex : current.subterm rp=some (.app ra (.lam rl rb) rarg))
    (sameCurrent : ll=rl)
    (leftTrace : BetaNodeHistoryPreimage labels (lp++[.fn]) oldLeft)
    (rightTrace : BetaNodeHistoryPreimage labels (rp++[.fn]) oldRight) :
    ∃es fs,PrerequisiteChain source oldLeft es ∧PrerequisiteChain source oldRight fs ∧
      es.map source.labelAt=fs.map source.labelAt ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence source closed es) (chainSyntaxIncidence source closed fs) := by
  have lnode : current.subterm (lp++[.fn])=some (.lam ll lb) := by rw [LTerm.subterm_append,leftRedex];rfl
  have rnode : current.subterm (rp++[.fn])=some (.lam rl rb) := by rw [LTerm.subterm_append,rightRedex];rfl
  let lc : PrerequisiteChain current (lp++[.fn]) [lp++[.fn]] := .redex_lam leftRedex
  let rc : PrerequisiteChain current (rp++[.fn]) [rp++[.fn]] := .redex_lam rightRedex
  have vector : [lp++[.fn]].map current.labelAt=[rp++[.fn]].map current.labelAt := by
    simp only [List.map_cons,List.map_nil,LTerm.labelAt,lnode,rnode,Option.map_some,LTerm.label,sameCurrent]
  obtain ⟨iso⟩ := actual_chain_iso_of_labels (prefixHistory.append labels) initial (labels.closed closed) lc rc vector
  rcases paired_current_chain_source_labels initial prefixHistory old labels selected sourceSafe closed
      (labels.closed closed) lc rc iso leftTrace rightTrace with safe | same | opposite
  · exact safe.2
  · obtain ⟨_l,_r,_direction,_front,_head,answer⟩ := same
    exact answer
  · obtain ⟨left,right,_lt,_rt,different,_front,_head⟩ := opposite
    exact False.elim (different ((lambda_singleton_false left lnode).trans (lambda_singleton_false right rnode).symm))

end Lamping.AG

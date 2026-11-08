import Lamping.Lamping.SynchronizedUnsafeCuts
import Lamping.Checks.DegreeReadSafetyProfiles
namespace Lamping.Checks.SynchronizedUnsafeCutsChecks
open Graph Lambda Lambda.Labelled AG FanSuccessfulChains BetaChainEvaluatedResidualsChecks

private theorem old : Marked.RelativeOldHistory [[.fn]] [[.fn]]
    (Marked.mark [[.fn]] original.erase) FanSuccessfulReachable.endpoint :=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.nil _)
private theorem selected (name : Path) (inside : name∈([[.fn]] : List Path)) :
    original.degreeAt name=some (.atom 2) := by
  have eq := List.mem_singleton.mp inside;subst name;rfl
private theorem rightBad : ¬degreeReadSafe (.atom 2) (current.labelAt right) := by
  change ¬degreeReadSafe (.atom 2) (some rightLabel)
  simp [degreeReadSafe,rightLabel,Label.outerBarsSafe_concat,Label.atom,Label.under,Label.OuterBarsSafe]
private theorem firstSafe : degreeReadSafe (.atom 2) (current.labelAt rightVar) := by
  change degreeReadSafe (.atom 2) (some (.atom 11))
  simp [degreeReadSafe,Label.atom,Label.OuterBarsSafe]
private theorem fiveVector :
    rightBodyEdges.map (fun path=>degreeReadSafe (.atom 2) (current.labelAt path))=
      [True,False,True,True,False] := by
  change degreeReadSafe (.atom 2) (some (.atom 11))::
    rightEdges.map (fun path=>degreeReadSafe (.atom 2) (current.labelAt path))=_
  rw [DegreeReadSafetyProfilesChecks.actual_four_safety_values]
  simp [degreeReadSafe,Label.atom,Label.OuterBarsSafe]

private theorem cut_bad (cut : ActualUnsafeMarkerCut F ps source target degree start edges) :
    ¬degreeReadSafe degree (target.labelAt cut.edge) := by
  intro good
  exact cut.marked (good cut.node.label (by simp only [LTerm.labelAt,cut.lookup,Option.map_some]))

private theorem cut_zero (cut : ActualUnsafeMarkerCut F ps source target degree start edges)
    (shape : edges=head::tail) (bad : ¬degreeReadSafe degree (target.labelAt head)) :
    cut.before=[] ∧cut.edge=head ∧cut.after=tail := by
  cases front : cut.before with
  | nil =>
    have eq : head::tail=cut.edge::cut.after := by simpa only [front,List.nil_append] using shape.symm.trans cut.split
    exact ⟨rfl,(List.cons.inj eq).1.symm,(List.cons.inj eq).2.symm⟩
  | cons p ps =>
    have eq : head::tail=p::(ps++cut.edge::cut.after) := by simpa only [front,List.cons_append] using shape.symm.trans cut.split
    have good := cut.safeBefore p (by rw [front];exact List.mem_cons_self)
    exact False.elim (bad ((List.cons.inj eq).1.symm ▸ good))

private theorem cut_one (cut : ActualUnsafeMarkerCut F ps source target degree start edges)
    (shape : edges=first::second::tail)
    (safe : degreeReadSafe degree (target.labelAt first))
    (bad : ¬degreeReadSafe degree (target.labelAt second)) :
    cut.before=[first] ∧cut.edge=second ∧cut.after=tail := by
  cases front : cut.before with
  | nil =>
    have eq : first::second::tail=cut.edge::cut.after := by simpa only [front,List.nil_append] using shape.symm.trans cut.split
    exact False.elim (cut_bad cut ((List.cons.inj eq).1 ▸ safe))
  | cons p ps =>
    have eq : first::second::tail=p::(ps++cut.edge::cut.after) := by simpa only [front,List.cons_append] using shape.symm.trans cut.split
    have hp := (List.cons.inj eq).1
    have tails := (List.cons.inj eq).2
    cases rest : ps with
    | nil =>
      have pair : second=cut.edge ∧tail=cut.after := by simpa only [rest,List.nil_append,List.cons.injEq] using tails
      exact ⟨by simp [hp],pair.1.symm,pair.2.symm⟩
    | cons q qs =>
      have hq : second=q := (List.cons.inj (by simpa only [rest,List.cons_append] using tails)).1
      have member : q∈cut.before := by rw [front,rest];simp
      exact False.elim (bad (hq.symm ▸ cut.safeBefore q member))

private theorem producer
    (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ())) :
    ∃localTarget,∃_localHistory : History [[.fn]] (initLabels original.erase) localTarget,
      ∃edge : BetaEdge site.net,
      ∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
      SiteBetaGeometry site edge ∧
      ∀{p es}(chain : PrerequisiteChain current p es),
        Nonempty (EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain) := by
  have matching := FanSuccessfulReachable.concrete.sourceIso.matches
    (encode_closed_matches FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  have inputs := FanSuccessfulReachable.concrete.sourceIso.rootInputs
    (encode_closed_independence FanSuccessfulReachable.term FanSuccessfulReachable.closed 0).rootInputs
  obtain ⟨baseFlow⟩ := encode_flowBalance FanSuccessfulReachable.term 0
  have flow := FanSuccessfulReachable.concrete.sourceIso.flowBalance baseFlow
  obtain ⟨baseBalance⟩ := encode_indexed_balance FanSuccessfulReachable.term 0
  have balance := FanSuccessfulReachable.concrete.sourceIso.indexed_balance baseBalance
  have transparent := FanSuccessfulReachable.concrete.sourceIso.transparency
    (encode_closed_transparency FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  obtain ⟨localTarget,history,_erase,_matches,edge,selection,geometry,all⟩ :=
    site.beta_evaluated_chain_residuals sourceClosed matching inputs flow rfl balance rfl transparent
      FanSuccessfulReachable.relative (by simp [FanSuccessfulReachable.endpoint,Marked.Normal]) actualHistory targetSelection
  exact ⟨localTarget,history,edge,selection,geometry,all⟩

/-- Real different starts, the SAME four READ edges, and first unsafe zero. -/
theorem actual_first_unsafe_zero :
    right≠rightVar ∧rightEdges.length=4 ∧
    ∃lc : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) right rightEdges,
    ∃rc : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) rightVar rightEdges,
      lc.before=[] ∧rc.before=[] ∧lc.edge=right ∧rc.edge=right ∧
      lc.after=rightEdges.tail ∧rc.after=rightEdges.tail := by
  obtain ⟨targetSelection⟩ := FanSuccessfulReachable.beta_matches.occurrence_fragment_selection targetClosed
  obtain ⟨localTarget,history,edge,selection,geometry,all⟩ := producer targetSelection
  obtain ⟨left⟩ := all right_lambda_chain
  obtain ⟨rightOut⟩ := all right_variable_chain
  have matching := FanSuccessfulReachable.concrete.sourceIso.matches
    (encode_closed_matches FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  obtain ⟨baseFlow⟩ := encode_flowBalance FanSuccessfulReachable.term 0
  have flow := FanSuccessfulReachable.concrete.sourceIso.flowBalance baseFlow
  rcases left.synchronized_unsafe_cuts_of_target_images site matching flow rfl
      FanSuccessfulReachable.relative (by simp [FanSuccessfulReachable.endpoint,Marked.Normal])
      old actualHistory selected (initial.outerBarsSafe _) history geometry rightOut (by rfl) with safe | cuts
  · exact False.elim (rightBad (safe.1 right (by simp [rightEdges])))
  · obtain ⟨_ordinal,lc,rc,_ll,_rl,_lt,_rt,_lh,_rh,_ld,_rd,_lb,_rb,_lm,_rm⟩ := cuts
    obtain ⟨lb,le,la⟩ := cut_zero lc (by rfl) rightBad
    obtain ⟨rb,re,ra⟩ := cut_zero rc (by rfl) rightBad
    exact ⟨by decide,rfl,lc,rc,lb,rb,le,re,la,ra⟩

/-- Real five READ body chain selfpair, with nonempty before and after3. -/
theorem actual_first_unsafe_one :
    rightBodyEdges.map (fun p=>degreeReadSafe (.atom 2) (current.labelAt p))=[True,False,True,True,False] ∧
    ∃lc : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) rightBody rightBodyEdges,
    ∃rc : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) rightBody rightBodyEdges,
      lc.before=[rightVar] ∧rc.before=[rightVar] ∧lc.edge=right ∧rc.edge=right ∧
      lc.after=[[.fn,.body,.fn],xVar,[.fn]] ∧rc.after=[[.fn,.body,.fn],xVar,[.fn]] ∧
      lc.before.length=1 ∧rc.before.length=1 ∧lc.after.length=3 ∧rc.after.length=3 := by
  obtain ⟨targetSelection⟩ := FanSuccessfulReachable.beta_matches.occurrence_fragment_selection targetClosed
  obtain ⟨localTarget,history,edge,selection,geometry,all⟩ := producer targetSelection
  obtain ⟨out⟩ := all right_body_chain
  have matching := FanSuccessfulReachable.concrete.sourceIso.matches
    (encode_closed_matches FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  obtain ⟨baseFlow⟩ := encode_flowBalance FanSuccessfulReachable.term 0
  have flow := FanSuccessfulReachable.concrete.sourceIso.flowBalance baseFlow
  rcases out.synchronized_unsafe_cuts_of_target_images site matching flow rfl
      FanSuccessfulReachable.relative (by simp [FanSuccessfulReachable.endpoint,Marked.Normal])
      old actualHistory selected (initial.outerBarsSafe _) history geometry out (by rfl) with safe | cuts
  · exact False.elim (rightBad (safe.1 right (by simp [rightBodyEdges,rightEdges])))
  · obtain ⟨_ordinal,lc,rc,_ll,_rl,_lt,_rt,_lh,_rh,_ld,_rd,_lb,_rb,_lm,_rm⟩ := cuts
    obtain ⟨lb,le,la⟩ := cut_one lc (by rfl) firstSafe rightBad
    obtain ⟨rb,re,ra⟩ := cut_one rc (by rfl) firstSafe rightBad
    exact ⟨fiveVector,lc,rc,lb,rb,le,re,la,ra,by rw [lb];rfl,by rw [rb];rfl,by rw [la];rfl,by rw [ra];rfl⟩

#print axioms actual_first_unsafe_zero
#print axioms actual_first_unsafe_one
end Lamping.Checks.SynchronizedUnsafeCutsChecks


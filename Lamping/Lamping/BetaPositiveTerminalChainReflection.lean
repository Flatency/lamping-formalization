import Lamping.Lamping.BetaSynchronizedBeforeImages
import Lamping.Lamping.TerminalPredecessorDirection
import Lamping.Lamping.BetaChainEvaluatedResiduals
import Lamping.Lambda.PrerequisitePrefixCancellation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem canonical_drop_append
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {t : LTerm} {g : Net signature N B W} {root : B}
    (selection : OccurrenceFragmentSelection t g root)
    (parent : PrerequisiteChain t start edges)
    (tail : PrerequisiteChain t next after)
    (split : edges=before++after) :
    (canonicalChainImage selection parent).drop before.length=canonicalChainImage selection tail := by
  subst edges
  simp only [canonicalChainImage,List.attach_append,List.map_append,List.map_map,Function.comp_def]
  rw [List.drop_append]
  simp only [List.length_map,List.length_attach,Nat.sub_self,List.drop_zero]
  rw [List.drop_eq_nil_of_le (by simp only [List.length_map,List.length_attach];omega),List.nil_append]
  rfl

private theorem splice_equal {A : Type} {xs ys : List A} {n : Nat}
    (front : xs.take n=ys.take n) (tail : xs.drop n=ys.drop n) : xs=ys := by
  calc
    xs=xs.take n++xs.drop n := (List.take_append_drop n xs).symm
    _=ys.take n++ys.drop n := by rw [front,tail]
    _=ys := List.take_append_drop n ys

variable {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

-- Suggested name; exact mathematics, not implementation authorization.
theorem PathSite.beta_positive_terminal_chain_reflection
    {root : B} {source target original : LTerm}
    {ps prior F : List Path} {marked oldMarked : Marked} {degree : Labelled.Label}
    {leftStart rightStart : Path} {les res : List Path}
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) oldMarked)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (prefixHistory : History prior original source) (initial : INIT original)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (sourceRepresentation : ChainRepresentationInvariant closed sourceSelection)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (leftParent : PrerequisiteChain target leftStart les)
    (rightParent : PrerequisiteChain target rightStart res)
    (parentSame : SameChainRepresentation targetSelection leftParent rightParent)
    (left : ActualUnsafeMarkerCut F ps source target degree leftStart les)
    (right : ActualUnsafeMarkerCut F ps source target degree rightStart res)
    (leftTerminal : left.after=[]) (rightTerminal : right.after=[])
    (beforePositive : 0<left.before.length)
    (remainingIso : ChainIncidenceIsomorphic
      (chainSyntaxIncidence target (history.closed closed) [left.edge])
      (chainSyntaxIncidence target (history.closed closed) [right.edge])) :
    1<max les.length res.length ∧
      left.before.map target.labelAt=right.before.map target.labelAt ∧
      ChainIncidenceIsomorphic
        (chainSyntaxIncidence target (history.closed closed) les)
        (chainSyntaxIncidence target (history.closed closed) res) := by
  have lengths := congrArg List.length parentSame
  change (canonicalChainImage targetSelection leftParent).length=
    (canonicalChainImage targetSelection rightParent).length at lengths
  rw [canonicalChainImage_length,canonicalChainImage_length] at lengths
  have llen := congrArg List.length left.split
  have rlen := congrArg List.length right.split
  simp only [leftTerminal,rightTerminal,List.length_append,List.length_cons,List.length_nil] at llen rlen
  have ordinal : left.before.length=right.before.length := by omega
  have smaller : 1<max les.length res.length := by omega
  obtain ⟨_localTarget,_localHistory,_erase,targetMatches,_physicalEdge,_selection,_geometry,_all⟩ :=
    site.beta_evaluated_chain_residuals closed matching inputs flow positive balance rootDepth transparency
      relative normal history targetSelection
  have direction := actual_terminal_predecessor_direction_eq targetMatches targetSelection
    leftParent rightParent parentSame left right ordinal beforePositive leftTerminal rightTerminal
  have lc : PrerequisiteChain target left.reader [left.edge] := by simpa only [leftTerminal] using left.remaining
  have rc : PrerequisiteChain target right.reader [right.edge] := by simpa only [rightTerminal] using right.remaining
  obtain ⟨singletonIso⟩ := remainingIso
  have singletonLabels := actual_chain_labels_forward (prefixHistory.append history) initial
    (history.closed closed) lc rc singletonIso
  have sameHead : left.node.label=right.node.label := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true,LTerm.labelAt,
      left.lookup,right.lookup,Option.map_some,Option.some.injEq] using singletonLabels
  have sameWord : left.node.label.readLetters left.forward=right.node.label.readLetters left.forward :=
    congrArg (fun label : Labelled.Label=>label.readLetters left.forward) sameHead
  obtain ⟨edge,geometry,allChildren⟩ := site.beta_uncreated_child_residuals closed matching inputs flow positive
    balance rootDepth transparency relative normal history old (DegreeAligned.initial source F) selected
  have leftBeforeSafe : ∀p∈left.before,∀node,target.subterm p=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree) := by
    intro p member node atNode
    exact left.safeBefore p member node.label (by simp only [LTerm.labelAt,atNode,Option.map_some])
  have rightBeforeSafe : ∀p∈right.before,∀node,target.subterm p=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree) := by
    intro p member node atNode
    exact right.safeBefore p member node.label (by simp only [LTerm.labelAt,atNode,Option.map_some])
  have rightReading : PrerequisiteReadsDirected target right.reader right.edge left.forward := by
    rw [direction];exact right.reading
  obtain ⟨ls,lbs,lr,lf,lname,ln,lmarker,lrest,lchosen,lat,lsafe,lchain,lprefix,lread,lbefore,lmarks,lword,
      _lstart,_lorigins,lresiduals⟩ := site.beta_before_block_images_at_read history old selected sourceSafe
    sourceSelection targetSelection edge allChildren leftParent left.split left.segment left.reading
      left.lookup left.marked leftBeforeSafe
  obtain ⟨rs,rbs,rr,rf,rname,rn,rmarker,rrest,rchosen,rat,rsafe,rchain,rprefix,rread,rbefore,rmarks,rword,
      _rstart,_rorigins,rresiduals⟩ := site.beta_before_block_images_at_read history old selected sourceSafe
    sourceSelection targetSelection edge allChildren rightParent right.split right.segment rightReading
      right.lookup right.marked rightBeforeSafe
  let lsource : MarkerSourceChain F source degree left.forward (left.before.map target.labelAt)
      (left.node.label.readLetters left.forward) :=
    ⟨ls,lbs,lr,lf,lname,ln,lmarker,lrest,lchosen,lat,lsafe,lprefix,lread,lchain,lbefore,lmarks,lword⟩
  let rsource : MarkerSourceChain F source degree left.forward (right.before.map target.labelAt)
      (right.node.label.readLetters left.forward) :=
    ⟨rs,rbs,rr,rf,rname,rn,rmarker,rrest,rchosen,rat,rsafe,rprefix,rread,rchain,rbefore,rmarks,rword⟩
  have firstLabels : ln.label=rn.label := (lsource.compare_first rsource sameWord).1
  have sourceFrontLength : lbs.length=left.before.length := by
    simpa only [List.length_map] using (congrArg List.length lbefore).symm
  have otherFrontLength : rbs.length=right.before.length := by
    simpa only [List.length_map] using (congrArg List.length rbefore).symm
  have targetTakes := congrArg (fun xs : List (List (Endpoint site.reduce))=>xs.take left.before.length) parentSame
  have sourceTakes : (canonicalChainImage sourceSelection lchain).take left.before.length=
      (canonicalChainImage sourceSelection rchain).take left.before.length := by
    rw [←ordinal] at rresiduals
    exact (lresiduals.equality_iff site geometry rresiduals).mp targetTakes
  have ltail : PrerequisiteChain source lr [lf,lname++[.fn]] := lprefix.cancel_successful_chain lchain
  have rtail : PrerequisiteChain source rr [rf,rname++[.fn]] := rprefix.cancel_successful_chain rchain
  obtain ⟨la,lbody,larg,latRedex⟩ := LTerm.degreeAt_redex (selected _ lchosen)
  obtain ⟨ra,rbody,rarg,ratRedex⟩ := LTerm.degreeAt_redex (selected _ rchosen)
  have lfn : source.subterm (lname++[.fn])=some (.lam degree lbody) := by
    rw [LTerm.subterm_append,latRedex];rfl
  have rfn : source.subterm (rname++[.fn])=some (.lam degree rbody) := by
    rw [LTerm.subterm_append,ratRedex];rfl
  have tailLabels : [lf,lname++[.fn]].map source.labelAt=[rf,rname++[.fn]].map source.labelAt := by
    have lfirst : source.labelAt lf=some ln.label := by simp only [LTerm.labelAt,lat,Option.map_some]
    have rfirst : source.labelAt rf=some rn.label := by simp only [LTerm.labelAt,rat,Option.map_some]
    have lfunction : source.labelAt (lname++[.fn])=some degree := by
      simp only [LTerm.labelAt,lfn,Option.map_some,LTerm.label]
    have rfunction : source.labelAt (rname++[.fn])=some degree := by
      simp only [LTerm.labelAt,rfn,Option.map_some,LTerm.label]
    simp only [List.map_cons,List.map_nil,lfirst,rfirst,lfunction,rfunction,firstLabels]
  have tailIso := actual_chain_iso_of_labels prefixHistory initial closed ltail rtail tailLabels
  have tailImages := (sourceRepresentation ltail rtail).mpr tailIso
  have ldropped := canonical_drop_append sourceSelection lchain ltail rfl
  have rdropped := canonical_drop_append sourceSelection rchain rtail rfl
  have sourceDrops : (canonicalChainImage sourceSelection lchain).drop left.before.length=
      (canonicalChainImage sourceSelection rchain).drop left.before.length := by
    rw [sourceFrontLength] at ldropped
    rw [otherFrontLength,←ordinal] at rdropped
    exact ldropped.trans (tailImages.trans rdropped.symm)
  have sourceWhole : SameChainRepresentation sourceSelection lchain rchain := splice_equal sourceTakes sourceDrops
  obtain ⟨sourceIso⟩ := (sourceRepresentation lchain rchain).mp sourceWhole
  have sourceLabels := actual_chain_labels_forward prefixHistory initial closed lchain rchain sourceIso
  have beforeLabels := congrArg (fun xs : List (Option Labelled.Label)=>xs.take left.before.length) sourceLabels
  have sourceBefore : lbs.map source.labelAt=rbs.map source.labelAt := by
    have ltake : ((lbs++[lf,lname++[.fn]]).map source.labelAt).take left.before.length=lbs.map source.labelAt := by
      have length : (lbs.map source.labelAt).length=lbs.length := by simp only [List.length_map]
      rw [List.map_append,←sourceFrontLength,←length,List.take_left]
    have rtake : ((rbs++[rf,rname++[.fn]]).map source.labelAt).take left.before.length=rbs.map source.labelAt := by
      have length : (rbs.map source.labelAt).length=rbs.length := by simp only [List.length_map]
      rw [ordinal,List.map_append,←otherFrontLength,←length,List.take_left]
    exact ltake.symm.trans (beforeLabels.trans rtake)
  have targetBefore : left.before.map target.labelAt=right.before.map target.labelAt :=
    lbefore.trans (sourceBefore.trans rbefore.symm)
  have targetLabels : les.map target.labelAt=res.map target.labelAt := by
    rw [left.split,right.split,leftTerminal,rightTerminal]
    simp only [List.map_append,List.map_cons,List.map_nil,targetBefore,LTerm.labelAt,
      left.lookup,right.lookup,Option.map_some,sameHead]
  exact ⟨smaller,targetBefore,actual_chain_iso_of_labels (prefixHistory.append history) initial
    (history.closed closed) leftParent rightParent targetLabels⟩

#print axioms PathSite.beta_positive_terminal_chain_reflection
end Lamping.AG

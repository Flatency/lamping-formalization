import Lamping.Lamping.NonterminalSpineHeadComparison
import Lamping.Lamping.BetaSynchronizedBeforeImages
import Lamping.Lamping.TerminalHeadSuppliers

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem canonical_tail
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {target : LTerm} {g : Net signature N B W} {root : B}
    (selection : OccurrenceFragmentSelection target g root)
    (parent : PrerequisiteChain target start es)
    (tail : PrerequisiteChain target tailStart after)
    (split : es=before++edge::after) :
    (canonicalChainImage selection parent).drop (before.length+1)=
      canonicalChainImage selection tail := by
  subst es
  simp only [canonicalChainImage,List.attach_append,List.attach_cons,List.map_append,
    List.map_cons,List.map_map,Function.comp_def]
  rw [List.drop_append]
  simp only [List.length_map,List.length_attach]
  simp only [Nat.add_sub_cancel_left,List.drop_succ_cons,List.drop_zero]
  rw [List.drop_eq_nil_of_le (by simp only [List.length_map,List.length_attach];omega),List.nil_append]
  rfl

private theorem list_cut_eq {A : Type} {xs ys : List A} {n : Nat}
    (before : xs.take n=ys.take n) (head : xs[n]?=ys[n]?)
    (after : xs.drop (n+1)=ys.drop (n+1)) : xs=ys := by
  induction n generalizing xs ys with
  | zero => cases xs <;> cases ys <;> simp_all
  | succ n ih =>
    cases xs with
    | nil => cases ys <;> simp_all
    | cons x xs =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
        simp only [List.take_succ_cons] at before
        have pair:=List.cons.inj before
        simp only [List.getElem?_cons_succ] at head
        simp only [List.drop_succ_cons] at after
        have rest:=ih pair.2 head after
        rw [pair.1,rest]

private theorem member_of_split {A : Type} {es before after : List A} {edge : A}
    (split : es=before++edge::after) : edge∈es := by
  rw [split]
  exact List.mem_append_right _ List.mem_cons_self

private theorem slot_of_split {A : Type} {es before after : List A} {edge : A}
    (split : es=before++edge::after) : es[before.length]?=some edge := by
  rw [split,List.getElem?_append_right (by omega)]
  simp

private def cutMember {F ps : List Path} {source target : LTerm} {degree : Label}
    {start : Path} {es : List Path}
    (cut : ActualUnsafeMarkerCut F ps source target degree start es) : {p : Path // p∈es} :=
  ⟨cut.edge,member_of_split cut.split⟩

private theorem cutSlot {F ps : List Path} {source target : LTerm} {degree : Label}
    {start : Path} {es : List Path}
    (cut : ActualUnsafeMarkerCut F ps source target degree start es) :
    es[cut.before.length]?=some (cutMember cut).val := by
  exact slot_of_split cut.split

private theorem canonical_terminal_drop
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {target : LTerm} {g : Net signature N B W} {root : B}
    (selection : OccurrenceFragmentSelection target g root)
    (parent : PrerequisiteChain target start es)
    (split : es=before++[edge]) :
    (canonicalChainImage selection parent).drop (before.length+1)=[] := by
  apply List.drop_eq_nil_of_le
  rw [canonicalChainImage_length,split]
  simp

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- The genuine CURRENT shorter-chain induction step for whole parents of
length greater than one. The marked singleton base is intentionally separate. -/
theorem PathSite.beta_multiedge_chain_forward
    {root : B} {source target original : LTerm} {ps F prior : List Path} {marked oldMarked : Marked}
    {ls rs : Path} {les res : List Path} {degree : Labelled.Label}
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (initial : INIT original) (prefixHistory : History prior original source)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) oldMarked)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (first : PrerequisiteChain target ls les) (second : PrerequisiteChain target rs res)
    (iso : ChainIncidenceIso (chainSyntaxIncidence target (history.closed closed) les)
      (chainSyntaxIncidence target (history.closed closed) res))
    (multi : 1<max les.length res.length)
    (ih : ChainForwardBelow (history.closed closed) targetSelection (max les.length res.length)) :
    SameChainRepresentation targetSelection first second := by
  rcases actual_first_unsafe_current_after initial prefixHistory old history selected sourceSafe
      (history.closed closed) first second iso with safe|cuts
  · apply (site.beta_marker_free_rep closed matching inputs flow positive balance rootDepth transparency
      relative normal history old (DegreeAligned.initial source F) selected sourceSelection targetSelection
      sourceJoint.1 first second ?_ ?_).mpr ⟨iso⟩
    · intro e inside node lookup
      exact safe.1 e inside node.label (by simp only [LTerm.labelAt,lookup,Option.map_some])
    · intro e inside node lookup
      exact safe.2 e inside node.label (by simp only [LTerm.labelAt,lookup,Option.map_some])
  · obtain ⟨left,right,lengths,beforeLabels,headLabels,_afterLabels,leftShort,rightShort,afterCase⟩:=cuts
    have direction : left.forward=right.forward := by
      by_cases same : left.forward=right.forward
      · exact same
      · obtain ⟨lone,rone,_⟩:=actual_parent_opposite_cut_singleton initial (prefixHistory.append history)
          (history.closed closed) left right iso same
        rw [lone,rone] at multi
        exact False.elim (by omega)
    have before:=site.beta_synchronized_before_images closed matching inputs flow positive balance rootDepth
      transparency relative normal history old selected sourceSafe prefixHistory initial sourceSelection
      targetSelection sourceJoint.1 first second left right beforeLabels headLabels direction
    let lm:=cutMember left
    let rm:=cutMember right
    have leftSlot : les[left.before.length]?=some (actualChainPosition first lm).val := cutSlot left
    have rightSlot : res[left.before.length]?=some (actualChainPosition second rm).val := by
      simpa only [lengths] using cutSlot right
    have parts :
        (targetSelection (actualChainPosition first lm)).fragment.segments=
          (targetSelection (actualChainPosition second rm)).fragment.segments ∧
        (canonicalChainImage targetSelection first).drop (left.before.length+1)=
          (canonicalChainImage targetSelection second).drop (right.before.length+1) := by
      rcases afterCase with terminal|more
      · obtain ⟨lc,rc,physical⟩:=actual_terminal_cut_physical_below initial (prefixHistory.append history)
          (history.closed closed) targetSelection left right terminal.1 terminal.2 iso multi ih
        have heads:=same_chain_representation_slot targetSelection lc rc physical
          (actualChainPosition first lm) (actualChainPosition second rm) (n:=0) rfl rfl
        refine ⟨heads,?_⟩
        have lsplit : les=left.before++[left.edge] := by simpa only [terminal.1] using left.split
        have rsplit : res=right.before++[right.edge] := by simpa only [terminal.2] using right.split
        rw [canonical_terminal_drop targetSelection first lsplit,
          canonical_terminal_drop targetSelection second rsplit]
      · obtain ⟨leftMore,rightMore,_same,ln,rn,_lg,_rg,lc,rc,tailIso⟩:=more
        have physical:=ih lc rc (by omega) tailIso
        obtain ⟨localTarget,localHistory,_erase,_targetMatches,edge,selection,geometry,allChains⟩:=
          site.beta_evaluated_chain_residuals closed matching inputs flow positive balance rootDepth
            transparency relative normal history targetSelection
        obtain ⟨leval⟩:=allChains first
        obtain ⟨reval⟩:=allChains second
        obtain ⟨lleaf,lsnap,⟨lgeom⟩⟩:=left.spine.incidence_leaf_output closed left.lookup
        obtain ⟨rleaf,rsnap,⟨rgeom⟩⟩:=right.spine.incidence_leaf_output closed right.lookup
        obtain ⟨lcanon⟩:=left.canonical_far_output history closed leftMore lsnap
        obtain ⟨rcanon⟩:=right.canonical_far_output history closed rightMore rsnap
        obtain ⟨lpair⟩:=lgeom.paired_reannotation localHistory (erase_initLabels source.erase).symm
        obtain ⟨rpair⟩:=rgeom.paired_reannotation localHistory (erase_initLabels source.erase).symm
        obtain ⟨lnear⟩:=Lamping.AG.PairedSpineReannotation.near_first_atom lpair selected
        obtain ⟨rnear⟩:=Lamping.AG.PairedSpineReannotation.near_first_atom rpair selected
        have heads:=EvaluatedChainResiduals.given_nonterminal_spine_head_pieces site initial prefixHistory closed
          old selected sourceSafe leftMore rightMore iso lcanon rcanon lpair rpair lnear rnear matching
          sourceSelection sourceJoint geometry leval reval lm rm rfl rfl
        refine ⟨heads,?_⟩
        rw [canonical_tail targetSelection first lc left.split,canonical_tail targetSelection second rc right.split]
        exact physical
    apply list_cut_eq (n:=left.before.length)
    · simpa only [lengths] using before
    · rw [canonical_chain_slot targetSelection first (actualChainPosition first lm) leftSlot,
        canonical_chain_slot targetSelection second (actualChainPosition second rm) rightSlot]
      exact congrArg some parts.1
    · simpa only [lengths] using parts.2
end

#print axioms PathSite.beta_multiedge_chain_forward

end Lamping.AG

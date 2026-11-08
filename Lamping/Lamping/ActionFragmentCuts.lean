import Lamping.Lamping.ActionPendingLambdaPadding
import Lamping.Lamping.OccurrencePhysicalNodes
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
private theorem child_context_unique {kind : Kind} {ctx child ctx' child' : Port kind} {step step'}
    (left : SyntaxChildPorts kind ctx child step)
    (right : SyntaxChildPorts kind ctx' child' step') : ctx=ctx' := by
  cases left <;> cases right <;> rfl
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}

/-- Equal actual child pieces identify their physical parent context seam.
No different-position node injectivity is asserted. -/
theorem SourceEdgeFragment.equal_piece_parent_seams
    (matching : Matches g root current.erase)
    {leftEdge rightEdge : SourceEdge} {p q : Path}
    (left : SourceEdgeFragment current g root leftEdge p)
    (right : SourceEdgeFragment current g root rightEdge q)
    {leftTerm rightTerm : LTerm} {leftStep rightStep : Step}
    (leftRole : SourceDeparture leftTerm leftStep leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm rightStep rightEdge.fromPort)
    (leftParent rightParent : RootAccess g root)
    (leftWord : p=accessWord g leftParent.val++[leftStep])
    (rightWord : q=accessWord g rightParent.val++[rightStep])
    (same : left.segments=right.segments) :
    leftParent.val.getLast?=rightParent.val.getLast? := by
  obtain ⟨ln,lc,ld,ltail,lroles,lfinish,lsplit,_lf,_la⟩ := matching.syntax_child_fragment
    leftParent left.access leftStep (left.word.trans leftWord)
  obtain ⟨rn,rc,rd,rtail,rroles,rfinish,rsplit,_rf,_ra⟩ := matching.syntax_child_fragment
    rightParent right.access rightStep (right.word.trans rightWord)
  have lcut := left.child_prefix matching leftRole leftParent leftWord
  have rcut := right.child_prefix matching rightRole rightParent rightWord
  have lp : left.segments=(.inl ⟨ln,ld⟩)::ltail :=
    List.append_cancel_left (lcut.2.symm.trans lsplit)
  have rp : right.segments=(.inl ⟨rn,rd⟩)::rtail :=
    List.append_cancel_left (rcut.2.symm.trans rsplit)
  rw [lp,rp] at same
  have endpoints : (⟨ln,ld⟩ : Σ n : N, Port (g.label n).sort)=⟨rn,rd⟩ := Sum.inl.inj (List.cons.inj same).1
  have nodes : ln=rn := congrArg Sigma.fst endpoints
  subst rn
  have contexts := child_context_unique lroles rroles
  rw [contexts] at lfinish
  exact lfinish.trans rfinish.symm
end
end Lamping.AG
namespace Lamping.AG
open Graph
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

theorem PlugLabelling.split_overlap {before after : List (PlugSegment c r)} {pivot : PlugSegment c r}
    {a b : Context} (labels : PlugLabelling c r (before++pivot::after) a b) :
    ∃ seam,PlugLabelling c r (before++[pivot]) a seam ∧
      PlugLabelling c r (pivot::after) seam b := by
  induction before generalizing a with
  | nil => exact ⟨a,.single _ _,labels⟩
  | cons e before ih =>
    cases before with
    | nil =>
      cases labels with
      | cons turn rest => exact ⟨_,.cons turn (.single _ _),rest⟩
    | cons f before =>
      cases labels with
      | cons turn rest =>
        obtain ⟨seam,left,right⟩ := ih rest
        exact ⟨seam,.cons turn left,right⟩
end
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

theorem ActionCanonicalBlocks.split_outside_assignments {principal : SiteActionPrincipal site}
    {raw old} (relation : ActionCanonicalBlocks site principal raw old)
    {a b : Context} (labels : PlugLabelling cut s.right.net raw a b)
    (pivot : Endpoint cut) {before after}
    (split : old=before++site.outsideEnd pivot::after) :
    ∃ rawBefore rawAfter seam,raw=rawBefore++Sum.inl pivot::rawAfter ∧
      ActionCanonicalBlocks site principal (rawBefore++[Sum.inl pivot]) (before++[site.outsideEnd pivot]) ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::rawAfter) (site.outsideEnd pivot::after) ∧
      PlugLabelling cut s.right.net (rawBefore++[Sum.inl pivot]) a seam ∧
      PlugLabelling cut s.right.net (Sum.inl pivot::rawAfter) seam b := by
  obtain ⟨rawBefore,rawAfter,rawSplit,left,right⟩ := relation.split_at_outside site pivot split
  have actual : PlugLabelling cut s.right.net (rawBefore++Sum.inl pivot::rawAfter) a b := by
    rw [←rawSplit];exact labels
  obtain ⟨seam,leftLabels,rightLabels⟩ := actual.split_overlap cut s.right.net
  exact ⟨rawBefore,rawAfter,seam,rawSplit,left,right,leftLabels,rightLabels⟩

theorem ActionCanonicalBlocks.unary_same_outside_suffix
    (unary : s.active≠.fan) {principal : SiteActionPrincipal site}
    {raw otherRaw old otherOld : List _}
    (left : ActionCanonicalBlocks site principal raw old)
    (right : ActionCanonicalBlocks site principal otherRaw otherOld)
    {a b c d : Context}
    (labels : PlugLabelling cut s.right.net raw a b)
    (otherLabels : PlugLabelling cut s.right.net otherRaw c d)
    (pivot : Endpoint cut) {before otherBefore after : List (Endpoint site.net)}
    (leftSplit : old=before++site.outsideEnd pivot::after)
    (rightSplit : otherOld=otherBefore++site.outsideEnd pivot::after) :
    ∃ leftRaw rightRaw tail,
      raw=leftRaw++Sum.inl pivot::tail ∧otherRaw=rightRaw++Sum.inl pivot::tail := by
  obtain ⟨leftRaw,leftTail,leftSeam,rawSplit,_leftPrefix,leftSuffix,_leftLabels,leftSuffixLabels⟩ :=
    left.split_outside_assignments site labels pivot leftSplit
  obtain ⟨rightRaw,rightTail,rightSeam,otherSplit,_rightPrefix,rightSuffix,_rightLabels,rightSuffixLabels⟩ :=
    right.split_outside_assignments site otherLabels pivot rightSplit
  have suffixEq := leftSuffix.unary_target_unique_of_labels site unary rightSuffix
    leftSuffixLabels rightSuffixLabels rfl
  have tails := (List.cons.inj suffixEq).2
  exact ⟨leftRaw,rightRaw,leftTail,rawSplit,by rw [tails];exact otherSplit⟩
/-- The real parent prefix fixes the cut ordinal, even at a repeated outside
endpoint. Both literal prefix equations are actual input decompositions. -/
theorem ActionCanonicalBlocks.unary_cut_at_actual_prefix
    (unary : s.active≠.fan) {principal : SiteActionPrincipal site}
    {raw old parentRaw parentOld newPiece oldPiece : List _}
    (whole : ActionCanonicalBlocks site principal raw old)
    (parent : ActionCanonicalBlocks site principal parentRaw parentOld)
    {a b c d : Context} (labels : PlugLabelling cut s.right.net raw a b)
    (parentLabels : PlugLabelling cut s.right.net parentRaw c d)
    (oldSplit : old=parentOld++oldPiece) (rawSplit : raw=parentRaw++newPiece)
    (pivot : Endpoint cut) (parentLast : parentOld.getLast?=some (site.outsideEnd pivot)) :
    ∃ seam,ActionCanonicalBlocks site principal (Sum.inl pivot::newPiece)
        (site.outsideEnd pivot::oldPiece) ∧
      PlugLabelling cut s.right.net (Sum.inl pivot::newPiece) seam b := by
  obtain ⟨before,parentSplit⟩ := List.getLast?_eq_some_iff.mp parentLast
  have oldCut : old=before++site.outsideEnd pivot::oldPiece := by
    rw [oldSplit,parentSplit,List.append_assoc];rfl
  obtain ⟨rawBefore,rawAfter,seam,split,left,right,leftLabels,rightLabels⟩ :=
    whole.split_outside_assignments site labels pivot oldCut
  have prefixSame : before++[site.outsideEnd pivot]=parentOld := parentSplit.symm
  have prefixEq := left.unary_target_unique_of_labels site unary parent leftLabels parentLabels prefixSame
  have reassembled : raw=parentRaw++rawAfter := by
    rw [split,←prefixEq,List.append_assoc];rfl
  have tailEq : newPiece=rawAfter := List.append_cancel_left (rawSplit.symm.trans reassembled)
  rw [←tailEq] at right rightLabels
  exact ⟨seam,right,rightLabels⟩end
end Lamping.AG
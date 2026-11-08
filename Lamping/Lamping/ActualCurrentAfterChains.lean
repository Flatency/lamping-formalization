import Lamping.Lamping.ActualUnsafeMarkerLeaves
import Lamping.Lamping.ActualChainLabelConverse
namespace Lamping.Lambda.Labelled

/-- The next start is an actual FUNCTION occurrence or the actual parent
of the lambda read. This is derived geometry, not a completion premise. -/
def ActualAfterStart (t : LTerm) (reader edge next : Path) : Prop :=
  (∃ stamp fn arg,t.subterm reader=some (.app stamp fn arg) ∧edge=reader++[.fn] ∧next=edge) ∨
  (∃ parent child stamp body,reader=parent++[child] ∧child≠.fn ∧
    t.subterm reader=some (.lam stamp body) ∧edge=reader ∧next=parent)

/-- A nonempty literal AFTER of a real next read has a real successful
chain. Variable-to-binder jumps remain inside that actual chain. -/
theorem PrerequisiteChain.after_of_read
    (chain : PrerequisiteChain t reader (edge::after))
    (read : PrerequisiteReads t reader edge) (nonempty : after≠[]) :
    ∃next,ActualAfterStart t reader edge next ∧PrerequisiteChain t next after := by
  rcases read with ⟨stamp,fn,arg,lookup,edgeEq⟩ | ⟨stamp,body,lookup,edgeEq⟩
  · rcases chain.app_cases lookup with ⟨l,b,shape,split⟩ | ⟨notLambda,tail,split,actual⟩
    · have length:=congrArg List.length split
      simp only [List.length_cons,List.length_nil] at length
      exact False.elim (nonempty (List.length_eq_zero_iff.mp (by omega)))
    · have parts:=List.cons.inj split
      refine ⟨edge,Or.inl ⟨stamp,fn,arg,lookup,edgeEq,rfl⟩,?_⟩
      rw [parts.1,parts.2];exact actual
  · rcases chain.lambda_cases lookup with ⟨parent,a,arg,atFunction,atApp,split⟩ |
      ⟨parent,child,tail,readerEq,notFunction,split,actual⟩
    · have length:=congrArg List.length split
      simp only [List.length_cons,List.length_nil] at length
      exact False.elim (nonempty (List.length_eq_zero_iff.mp (by omega)))
    · have parts:=List.cons.inj split
      exact ⟨parent,Or.inr ⟨parent,child,stamp,body,readerEq,notFunction,lookup,edgeEq,rfl⟩,parts.2 ▸ actual⟩
end Lamping.Lambda.Labelled
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

theorem ActualUnsafeMarkerCut.after_length_lt
    (cut : ActualUnsafeMarkerCut F ps oldSource current degree start edges) :
    cut.after.length<edges.length := by
  have length:=congrArg List.length cut.split
  simp only [List.length_append,List.length_cons] at length
  omega

theorem ActualUnsafeMarkerCut.current_after_chain
    (cut : ActualUnsafeMarkerCut F ps oldSource current degree start edges) (nonempty : cut.after≠[]) :
    ∃next,ActualAfterStart current cut.reader cut.edge next ∧
      PrerequisiteChain current next cut.after ∧cut.after.length<edges.length := by
  obtain ⟨next,geometry,actual⟩:=cut.remaining.after_of_read cut.reading.1 nonempty
  exact ⟨next,geometry,actual,cut.after_length_lt⟩

/-- Equal CURRENT AFTER labels of the two actual cuts supply the actual
AFTER iso internally. No original-source otherLast chain is inferred. -/
theorem actual_cut_after_iso
    {initialSource oldSource current : LTerm} {history ps F : List Path}
    {degree : Label} {leftStart rightStart : Path} {es fs : List Path}
    (labels : History history initialSource current) (initial : INIT initialSource) (closed : Closed current.erase)
    (left : ActualUnsafeMarkerCut F ps oldSource current degree leftStart es)
    (right : ActualUnsafeMarkerCut F ps oldSource current degree rightStart fs)
    (same : left.after.map current.labelAt=right.after.map current.labelAt)
    (nonempty : left.after≠[]) :
    ∃leftNext rightNext,ActualAfterStart current left.reader left.edge leftNext ∧
      ActualAfterStart current right.reader right.edge rightNext ∧
      PrerequisiteChain current leftNext left.after ∧PrerequisiteChain current rightNext right.after ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence current closed left.after) (chainSyntaxIncidence current closed right.after) ∧
      left.after.length<es.length ∧right.after.length<fs.length := by
  have rightMore : right.after≠[] := by
    intro empty
    have length:=congrArg List.length same
    simp only [List.length_map,empty,List.length_nil] at length
    exact nonempty (List.length_eq_zero_iff.mp length)
  obtain ⟨leftNext,lg,lc,ll⟩:=left.current_after_chain nonempty
  obtain ⟨rightNext,rg,rc,rl⟩:=right.current_after_chain rightMore
  exact ⟨leftNext,rightNext,lg,rg,lc,rc,actual_chain_iso_of_labels labels initial closed lc rc same,ll,rl⟩

/-- A direct assembly from the actual OLD producer. All-safe, terminal
empty AFTER, and genuine shorter nonempty AFTER are separate outputs. -/
theorem actual_first_unsafe_current_after
    {initialSource oldSource current : LTerm} {prior ps F : List Path} {degree : Label} {n : Marked}
    (initial : INIT initialSource) (prefixHistory : History prior initialSource oldSource)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F oldSource.erase) n)
    (labels : History ps oldSource current)
    (selected : ∀name∈F,oldSource.degreeAt name=some degree)
    (sourceSafe : oldSource.OuterBarsSafe (fun x=>x≠degree)) (closed : Closed current.erase)
    (leftChain : PrerequisiteChain current leftStart es) (rightChain : PrerequisiteChain current rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence current closed es) (chainSyntaxIncidence current closed fs)) :
    ((∀e∈es,degreeReadSafe degree (current.labelAt e)) ∧(∀e∈fs,degreeReadSafe degree (current.labelAt e))) ∨
    ∃left : ActualUnsafeMarkerCut F ps oldSource current degree leftStart es,
      ∃right : ActualUnsafeMarkerCut F ps oldSource current degree rightStart fs,
      left.before.length=right.before.length ∧
      left.before.map current.labelAt=right.before.map current.labelAt ∧
      current.labelAt left.edge=current.labelAt right.edge ∧
      left.after.map current.labelAt=right.after.map current.labelAt ∧
      left.after.length<es.length ∧right.after.length<fs.length ∧
      ((left.after=[] ∧right.after=[]) ∨
       (left.after≠[] ∧right.after≠[] ∧left.forward=right.forward ∧
        ∃leftNext rightNext,ActualAfterStart current left.reader left.edge leftNext ∧
          ActualAfterStart current right.reader right.edge rightNext ∧
          PrerequisiteChain current leftNext left.after ∧PrerequisiteChain current rightNext right.after ∧
          ChainIncidenceIsomorphic (chainSyntaxIncidence current closed left.after) (chainSyntaxIncidence current closed right.after))) := by
  rcases actual_first_unsafe_marker_leaves initial prefixHistory old labels selected sourceSafe closed leftChain rightChain iso with all | cuts
  · exact Or.inl all
  · obtain ⟨left,right,len,lt,rt,ld,rd,front,head,back,tails,signs⟩:=cuts
    refine Or.inr ⟨left,right,len,front,head,back,left.after_length_lt,right.after_length_lt,?_⟩
    by_cases empty : left.after=[]
    · exact Or.inl ⟨empty,tails.mp empty⟩
    · have rightMore : right.after≠[] := fun eq=>empty (tails.mpr eq)
      obtain ⟨ln,rn,lg,rg,lc,rc,comparison,ll,rl⟩:=actual_cut_after_iso (prefixHistory.append labels) initial closed left right back empty
      exact Or.inr ⟨empty,rightMore,signs.resolve_left empty,ln,rn,lg,rg,lc,rc,comparison⟩
end Lamping.AG

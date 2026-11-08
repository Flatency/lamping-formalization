import Lamping.Lamping.ActualFirstUnsafeCuts
import Lamping.Lambda.DirectedMarkerLeafWords
import Lamping.Lambda.NonterminalReadingDirections
namespace Lamping.AG
open Lambda Lambda.Labelled

/-- OUTPUT at one internally chosen actual unsafe READ. It retains the
relative OLD source, not the initial source used only for edge ordering. -/
structure ActualUnsafeMarkerCut (F ps : List Path) (oldSource current : LTerm)
    (degree : Label) (start : Path) (edges : List Path) where
  before : List Path
  edge : Path
  after : List Path
  reader : Path
  node : LTerm
  forward : Bool
  split : edges=before++edge::after
  segment : PrerequisitePrefix current start before reader
  remaining : PrerequisiteChain current reader (edge::after)
  reading : PrerequisiteReadsDirected current reader edge forward
  lookup : current.subterm edge=some node
  safeBefore : ∀ e∈before,degreeReadSafe degree (current.labelAt e)
  marked : ¬node.label.OuterBarsSafe (fun x=>x≠degree)
  spine : DirectedMarkerSpine F oldSource degree forward ps current (before.map current.labelAt) edge
  leaf : Nonempty (DirectedMarkerLeafOutput F oldSource degree forward ps (node.label.readLetters forward))

private theorem make_marker_cut
    {F ps : List Path} {oldSource current : LTerm} {degree : Label} {n : Marked}
    (old : Marked.RelativeOldHistory F ps (Marked.mark F oldSource.erase) n)
    (labels : History ps oldSource current)
    (selected : ∀ name∈F,oldSource.degreeAt name=some degree)
    (sourceSafe : oldSource.OuterBarsSafe (fun x=>x≠degree))
    (segment : PrerequisitePrefix current start before reader)
    (remaining : PrerequisiteChain current reader (edge::after))
    (read : PrerequisiteReads current reader edge)
    (safeBefore : ∀ e∈before,degreeReadSafe degree (current.labelAt e))
    (notSafe : ¬degreeReadSafe degree (current.labelAt edge)) :
    ∃ node forward,current.subterm edge=some node ∧
      PrerequisiteReadsDirected current reader edge forward ∧
      ¬node.label.OuterBarsSafe (fun x=>x≠degree) ∧
      DirectedMarkerSpine F oldSource degree forward ps current (before.map current.labelAt) edge ∧
      Nonempty (DirectedMarkerLeafOutput F oldSource degree forward ps (node.label.readLetters forward)) := by
  have atNode : ∃ node,current.subterm edge=some node := by
    rcases remaining.eligible (List.mem_cons_self) with ⟨p,a,fn,arg,eq,atApp⟩ | ⟨a,body,atLambda⟩
    · refine ⟨fn,?_⟩;rw [eq,LTerm.subterm_append,atApp];cases fn <;> rfl
    · exact ⟨_,atLambda⟩
  obtain ⟨node,lookup⟩:=atNode
  have marked : ¬node.label.OuterBarsSafe (fun x=>x≠degree) := by
    intro good;apply notSafe
    intro other same
    have eq : other=node.label := by simpa only [LTerm.labelAt,lookup,Option.map_some,Option.some.injEq] using same.symm
    exact eq ▸ good
  have beforeSafe : ∀ e∈before,∀ node,current.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree) := by
    intro e member node lookup
    exact safeBefore e member node.label (by simp only [LTerm.labelAt,lookup,Option.map_some])
  have directed : ∃ forward,PrerequisiteReadsDirected current reader edge forward := by
    rcases read with app | lam
    · obtain ⟨stamp,fn,arg,lookup,eq⟩:=app
      exact ⟨true,Or.inl ⟨stamp,fn,arg,lookup,eq⟩,eq⟩
    · obtain ⟨stamp,body,lookup,eq⟩:=lam
      exact ⟨false,Or.inr ⟨stamp,body,lookup,eq⟩,eq⟩
  obtain ⟨forward,reading⟩:=directed
  have spine:=old.directed_marker_spine labels selected sourceSafe segment reading lookup marked beforeSafe
  exact ⟨node,forward,lookup,reading,marked,spine,spine.leaf_output lookup⟩

private theorem nonterminal_not_redex (chain : PrerequisiteChain t start (edge::after))
    (nonempty : after≠[]) : ¬PrerequisiteRedexEdge t edge := by
  obtain ⟨bs,last,split,redex,earlier⟩:=chain.redex_only_last
  cases bs with
  | nil => simp only [List.nil_append,List.cons.injEq] at split;exact False.elim (nonempty split.2)
  | cons head tail =>
    have eq : edge=head := (List.cons.inj split).1
    exact earlier edge (by rw [eq];exact List.mem_cons_self)

/-- Both first degree-unsafe cuts and their actual OLD spines/leaves are
outputs. Only the composed history is used for order and incoming roles. -/
theorem actual_first_unsafe_marker_leaves
    {initialSource oldSource current : LTerm} {prior ps F : List Path} {degree : Label} {n : Marked}
    (initial : INIT initialSource) (prefixHistory : History prior initialSource oldSource)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F oldSource.erase) n)
    (labels : History ps oldSource current)
    (selected : ∀ name∈F,oldSource.degreeAt name=some degree)
    (sourceSafe : oldSource.OuterBarsSafe (fun x=>x≠degree))
    (closed : Closed current.erase)
    (leftChain : PrerequisiteChain current leftStart es) (rightChain : PrerequisiteChain current rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence current closed es) (chainSyntaxIncidence current closed fs)) :
    ((∀ e∈es,degreeReadSafe degree (current.labelAt e)) ∧(∀ e∈fs,degreeReadSafe degree (current.labelAt e))) ∨
    ∃ left : ActualUnsafeMarkerCut F ps oldSource current degree leftStart es,
      ∃ right : ActualUnsafeMarkerCut F ps oldSource current degree rightStart fs,
      left.before.length=right.before.length ∧
      es.take left.before.length=left.before ∧fs.take left.before.length=right.before ∧
      es.drop (left.before.length+1)=left.after ∧fs.drop (left.before.length+1)=right.after ∧
      left.before.map current.labelAt=right.before.map current.labelAt ∧
      current.labelAt left.edge=current.labelAt right.edge ∧
      left.after.map current.labelAt=right.after.map current.labelAt ∧
      (left.after=[] ↔right.after=[]) ∧(left.after=[] ∨left.forward=right.forward) := by
  have full:=prefixHistory.append labels
  rcases actual_first_unsafe_cuts full initial closed leftChain rightChain iso (degreeReadSafe degree) with all | cut
  · exact Or.inl all
  · obtain ⟨k,bs,e,as,cs,f,ds,l,r,ls,rs,bl,cl,lt,rt,ld,rd,front,head,back,good,goodRight,bad,badRight,lp,lr,lc,rp,rr,rc⟩:=cut
    obtain ⟨ln,lf,ll,lrD,lbad,lsp,lleaf⟩:=make_marker_cut old labels selected sourceSafe lp lc lr good bad
    obtain ⟨rn,rf,rl,rrD,rbad,rsp,rleaf⟩:=make_marker_cut old labels selected sourceSafe rp rc rr goodRight badRight
    have tails : as=[] ↔ds=[] := by
      have len:=congrArg List.length back
      simp only [List.length_map] at len
      constructor <;> intro eq
      · apply List.length_eq_zero_iff.mp;rw [←len,eq];rfl
      · apply List.length_eq_zero_iff.mp;rw [len,eq];rfl
    have signs : as=[] ∨lf=rf := by
      by_cases empty : as=[]
      · exact Or.inl empty
      · right
        have rightNonempty : ds≠[] := fun eq=>empty (tails.mpr eq)
        have sameLabel : ln.label=rn.label := by simpa only [LTerm.labelAt,ll,rl,Option.map_some,Option.some.injEq] using head
        exact full.equal_label_nonredex_read_direction initial ll rl sameLabel lrD rrD
          (nonterminal_not_redex lc empty) (nonterminal_not_redex rc rightNonempty)
    let left : ActualUnsafeMarkerCut F ps oldSource current degree leftStart es :=
      ⟨bs,e,as,l,ln,lf,ls,lp,lc,lrD,ll,good,lbad,lsp,lleaf⟩
    let right : ActualUnsafeMarkerCut F ps oldSource current degree rightStart fs :=
      ⟨cs,f,ds,r,rn,rf,rs,rp,rc,rrD,rl,goodRight,rbad,rsp,rleaf⟩
    refine Or.inr ⟨left,right,bl.trans cl.symm,?_,?_,?_,?_,front,head,back,tails,signs⟩
    · exact bl ▸ lt
    · exact bl ▸ rt
    · exact bl ▸ ld
    · exact bl ▸ rd
end Lamping.AG

import Lamping.Lambda.ActualIncomingLabelRoles
import Lamping.Lambda.ActualNodeLabelAncestry
import Lamping.Lambda.LabelRegions

namespace Lamping.Lambda.Labelled

/-- Only the final outer atom of a genuine source route can be an original
lambda edge: earlier route segments terminate at APP context or binder ports. -/
theorem SourceRoute.outer_lambda_atom_finish
    {source oldBody : LTerm} {oldPosition : Path} {n : Nat}
    {start finish : SourcePort} {label : Label}
    (initial : INIT source)
    (oldLambda : source.subterm oldPosition=some (.lam (Label.atom n) oldBody))
    (route : SourceRoute (sourceEdges [] .external source) start label finish)
    (outer : Letter.atom n∈label.letters) :
    finish=SourcePort.lamContext (Label.atom n) := by
  obtain ⟨env,ctx,located⟩:=SourceSubterm.of_lookup source oldLambda [] .external
  let original : SourceEdge:=sourceEdge env ctx (.lam (Label.atom n) oldBody)
  have originalMember : original∈sourceEdges [] .external source :=
    located.edges_subset original (List.mem_cons_self)
  induction route with
  | atom member atomic =>
    simp only [Label.atom,Label.letters,List.mem_singleton] at outer
    have same:=sourceEdges_unique initial member originalMember
      (atomic.trans (congrArg Label.single outer).symm)
    exact congrArg SourceEdge.toPort same
  | over left degree right ihLeft _ ihRight =>
    simp only [Label.letters_concat,Label.over,Label.letters,List.mem_append,List.mem_singleton] at outer
    rcases outer with (inside |impossible) |inside
    · have impossible:=ihLeft inside
      cases impossible
    · cases impossible
    · exact ihRight inside
  | under left degree right ihLeft _ ihRight =>
    simp only [Label.letters_concat,Label.under,Label.letters,List.mem_append,List.mem_singleton] at outer
    rcases outer with (inside |impossible) |inside
    · have impossible:=ihLeft inside
      cases impossible
    · cases impossible
    · exact ihRight inside

/-- Literal outer membership of an original INIT lambda atom internally
supplies the current constructor, its last atom, and THIS original ancestry.
Copies may share the original position; no current-coordinate injection occurs. -/
theorem History.original_lambda_outer_atom_origin
    {ps : List Path} {source target oldBody node : LTerm}
    {oldPosition position : Path} {n : Nat}
    (labels : History ps source target) (initial : INIT source)
    (oldLambda : source.subterm oldPosition=some (.lam (Label.atom n) oldBody))
    (lookup : target.subterm position=some node)
    (outer : Letter.atom n∈node.label.letters) :
    ∃ currentLabel currentBody,node=.lam currentLabel currentBody ∧
      currentLabel.lastAtom=some n ∧BetaNodeHistoryPreimage labels position oldPosition := by
  obtain ⟨ctx,finish,route,_⟩:=labels.node_incoming_route initial lookup
  have endAt:=route.outer_lambda_atom_finish initial oldLambda outer
  rw [endAt] at route
  obtain ⟨m,last,atomic⟩:=route.lam_last_atom
  have numbers : n=m := by
    have equal:=congrArg Label.lastAtom atomic
    simpa only [Label.lastAtom,Label.atom,Option.some.injEq] using equal
  have actualLast : node.label.lastAtom=some n := numbers.symm ▸last
  obtain ⟨oldPoint,old,atOld,trace⟩:=labels.node_preimage_from_lookup lookup
  obtain ⟨ancestor,atAncestor,sameLast,sameKind⟩:=trace.lastAtom_constructor lookup
  obtain ⟨k,atom⟩:=initial.1 ancestor.label (LTerm.label_mem_of_subterm atAncestor)
  have oldNumber : n=k := by
    have equal:=actualLast.symm.trans sameLast
    simpa only [atom,Label.atom,Label.lastAtom,Option.some.injEq] using equal
  have sameLabel : ancestor.label=(LTerm.lam (Label.atom n) oldBody).label :=
    atom.trans (congrArg Label.atom oldNumber.symm)
  have coordinate:=LTerm.subterm_label_injective source initial.2 atAncestor oldLambda sameLabel
  have atOriginal : source.subterm oldPosition=some ancestor := coordinate ▸atAncestor
  have original:=Option.some.inj (atOriginal.symm.trans oldLambda)
  subst ancestor
  cases node with
  | var label index => cases sameKind
  | app label fn arg => cases sameKind
  | lam label body => exact ⟨label,body,rfl,actualLast,coordinate ▸trace⟩

#print axioms SourceRoute.outer_lambda_atom_finish
#print axioms History.original_lambda_outer_atom_origin
end Lamping.Lambda.Labelled

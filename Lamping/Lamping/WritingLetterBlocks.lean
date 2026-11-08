import Lamping.Lamping.BetaChainEvaluatedResiduals
import Lamping.Lamping.ProperControlBlockParsing
import Lamping.Lamping.ControlPrincipalPrefixes
import Lamping.Lamping.DirectedPhysicalLabelEvaluation
import Lamping.Lambda.ActualIncomingLabelRoles
import Lamping.Lambda.LabelCopyComponents

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem outer_atom_member
    (route : SourceRoute edges start stamp finish)
    (outer : Letter.atom n∈stamp.letters) :
    ∃ cell∈edges,cell.atom=Label.atom n := by
  induction route with
  | atom member atomic =>
    simp only [Label.atom,Label.letters,List.mem_singleton] at outer
    exact ⟨_,member,atomic.trans (congrArg Label.single outer.symm)⟩
  | over left degree right ihLeft _ ihRight =>
    simp only [Label.letters_concat,Label.over,Label.letters,List.mem_append,List.mem_singleton] at outer
    rcases outer with (inside |impossible) |inside
    · exact ihLeft inside
    · cases impossible
    · exact ihRight inside
  | under left degree right ihLeft _ ihRight =>
    simp only [Label.letters_concat,Label.under,Label.letters,List.mem_append,List.mem_singleton] at outer
    rcases outer with (inside |impossible) |inside
    · exact ihLeft inside
    · cases impossible
    · exact ihRight inside

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private abbrev Regular (block : List (Endpoint g)) : Prop := block≠[] ∧
  (∀ e f,(e,f)∈block.zip block.tail →ControlOnlyTurn (g:=g) e f) ∧
  ∃ (node : N) (port : Port (g.label node).sort),
    ((g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) ∧
      block.getLast?=some (g.wire (.inl ⟨node,port⟩))

private theorem child_proper {kind : Kind} {ctx departure : Port kind}
    (roles : SyntaxChildPorts kind ctx departure step) : kind=.op .app ∨kind=.op .lam := by
  cases roles
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem proper_realizes
    (realizes : SourcePortRealizes original g root sourcePort endpoint)
    (nonexternal : sourcePort≠.external) :
    ∃ (node : N) (port : Port (g.label node).sort),endpoint=.inl ⟨node,port⟩ ∧
      ((g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) := by
  cases realizes with
  | external => exact False.elim (nonexternal rfl)
  | departure lookup sourceRole parent word roles finish =>
    exact ⟨_,_,rfl,child_proper roles⟩
  | appContext lookup access word shape role finish => exact ⟨_,_,rfl,Or.inl shape⟩
  | lamContext lookup access word shape role finish => exact ⟨_,_,rfl,Or.inr shape⟩
  | binding lookup parent word shape contextRole bindingRole finish => exact ⟨_,_,rfl,Or.inr shape⟩

private theorem chosen_regular
    (cell : {e : SourceEdge // e∈sourceEdges [] .external original})
    (fragment : SourceEdgeFragment original g root cell.val p) : Regular fragment.segments := by
  have nonexternal : cell.val.toPort≠.external := by
    intro external
    rcases sourceEdges_to_port original cell.property with inside | ⟨l,member,binding⟩ | ⟨i,free⟩
    · obtain ⟨l,member,node⟩:=inside
      rw [external] at node
      cases node
    · rw [external] at binding
      cases binding
    · rw [external] at free
      cases free
  obtain ⟨node,port,actual,proper⟩:=proper_realizes fragment.toRealizes nonexternal
  refine ⟨?_,fragment.forward.empty_word_control_only fragment.emptyWord,node,port,proper,?_⟩
  · intro empty
    have head:=fragment.start
    rw [empty] at head
    cases head
  · simpa only [actual] using fragment.finish

private theorem principal_regular (beta : BetaEdge g) : Regular beta.principal := by
  exact ⟨beta.principal_nonempty,(fun e f member=>Or.inl (beta.transparent e f member)),
    beta.lam,beta.lamCtx,Or.inr (congrArg Graph.Label.sort beta.lamLabel),beta.principalEnd⟩

private theorem reverse_regular (beta : BetaEdge g) : Regular beta.reverseRoute := by
  refine ⟨?_,?_,beta.app,beta.appFun,Or.inl (congrArg Graph.Label.sort beta.appLabel),beta.reverse_finish⟩
  · intro empty
    have finish:=beta.reverse_finish
    rw [empty] at finish
    cases finish
  · intro e f member
    exact Or.inl (transparent_reverse_turns beta.principal beta.transparent e f member)
end

theorem EvaluatedChainResiduals.writing_letter_blocks_regular
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original target localTarget : LTerm} {ps : List Path}
    {edge : BetaEdge site.net}
    {selection : SourceEdgeSelection original site.net root}
    {targetSelection : OccurrenceFragmentSelection target site.reduce root}
    {start : Path} {es : List Path}
    {chain : PrerequisiteChain target start es}
    (initial : INIT original)
    (localHistory : History ps original localTarget)
    (out : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain)
    (member : {p : Path // p∈es}) :
    (∀ n,Letter.atom n∈(out.node member).label.letters →
      ∃ cell : {e : SourceEdge // e∈sourceEdges [] .external original},
        cell.val.atom=Label.atom n ∧
        selection.atomWord n=(selection.chosen cell).2.segments) ∧
    (let blocks : List (List (Endpoint site.net)) :=
      (out.node member).label.letters.map
        (fun letter=>letter.sourceWord selection.atomWord edge.principal edge.reverseRoute)
     blocks.flatten=selection.evalLabel edge (out.node member).label ∧
       ∀ block∈blocks,block≠[] ∧
         (∀ e f,(e,f)∈block.zip block.tail →ControlOnlyTurn (g:=site.net) e f) ∧
         ∃ (node : K⊕(Unit⊕Unit)) (port : Port (site.net.label node).sort),
           ((site.net.label node).sort=.op .app ∨(site.net.label node).sort=.op .lam) ∧
             block.getLast?=some (site.net.wire (.inl ⟨node,port⟩))) := by
  obtain ⟨ctx,finish,route,_role⟩:=localHistory.node_incoming_route initial (out.lookup member)
  have atoms (n : Nat) (outer : Letter.atom n∈(out.node member).label.letters) :
      ∃ cell : {e : SourceEdge // e∈sourceEdges [] .external original},
        cell.val.atom=Label.atom n ∧selection.atomWord n=(selection.chosen cell).2.segments := by
    obtain ⟨sourceEdge,inside,atomic⟩:=outer_atom_member route outer
    let cell : {e : SourceEdge // e∈sourceEdges [] .external original}:=⟨sourceEdge,inside⟩
    exact ⟨cell,atomic,selection.atomWord_cell initial cell atomic⟩
  refine ⟨atoms,?_,?_⟩
  · have assembly:=selection.interpret_read_label edge true (out.node member).label
    simpa only [List.flatMap,interpretReadLetters,Label.readLetters,orientPhysical,if_true] using assembly
  · intro block inside
    obtain ⟨letter,letterMember,rfl⟩:=List.mem_map.mp inside
    cases letter with
    | atom n =>
      obtain ⟨cell,atomic,same⟩:=atoms n letterMember
      change Regular (selection.atomWord n)
      rw [same]
      exact chosen_regular cell (selection.chosen cell).2
    | over degree => exact principal_regular edge
    | under degree => exact reverse_regular edge

end Lamping.AG
#print axioms Lamping.AG.EvaluatedChainResiduals.writing_letter_blocks_regular

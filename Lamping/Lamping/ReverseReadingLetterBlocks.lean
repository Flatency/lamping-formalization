import Lamping.Lamping.WritingLetterBlocks
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem outer_external_start
    {source : LTerm} {a b : SourcePort} {stamp : Label} {cell : SourceEdge} {n : Nat}
    (initial : INIT source)
    (route : SourceRoute (sourceEdges [] .external source) a stamp b)
    (member : cell∈sourceEdges [] .external source)
    (atomic : cell.atom=Label.atom n) (external : cell.fromPort=.external)
    (outer : Letter.atom n∈stamp.letters) : a=.external := by
  induction route with
  | atom inside atomEq =>
    simp only [Label.atom,Label.letters,List.mem_singleton] at outer
    have same := sourceEdges_unique initial inside member
      ((atomEq.trans (congrArg Label.single outer.symm)).trans atomic.symm)
    exact (congrArg SourceEdge.fromPort same).trans external
  | over left degree right ihLeft _ ihRight =>
    simp only [Label.letters_concat,Label.over,Label.letters,List.mem_append,List.mem_singleton] at outer
    rcases outer with (inside |impossible) |inside
    · exact ihLeft inside
    · cases impossible
    · have bad := ihRight inside
      cases bad
  | under left degree right ihLeft _ ihRight =>
    simp only [Label.letters_concat,Label.under,Label.letters,List.mem_append,List.mem_singleton] at outer
    rcases outer with (inside |impossible) |inside
    · exact ihLeft inside
    · cases impossible
    · have bad := ihRight inside
      cases bad

private theorem nonroot_cell_nonexternal
    {original current node : LTerm} {ps : List Path} {p : Path} {cell : SourceEdge} {n : Nat}
    (initial : INIT original) (history : History ps original current)
    (lookup : current.subterm p=some node) (nonroot : p≠[])
    (member : cell∈sourceEdges [] .external original) (atomic : cell.atom=Label.atom n)
    (outer : Letter.atom n∈node.label.letters) : cell.fromPort≠.external := by
  intro external
  obtain ⟨ctx,finish,route,role⟩ := history.node_incoming_route initial lookup
  have same := outer_external_start initial route member atomic external outer
  have empty : p.getLast?=none := by rw [←role,same];rfl
  exact nonroot (List.getLast?_eq_none_iff.mp empty)

private theorem adjacent_snoc {A : Type} {R : A → A → Prop}
    {es : List A} {e f : A}
    (turns : ∀ x y,(x,y)∈es.zip es.tail →R x y)
    (last : es.getLast?=some e) (next : R e f) :
    ∀ x y,(x,y)∈(es++[f]).zip (es++[f]).tail →R x y := by
  induction es with
  | nil => cases last
  | cons x es ih =>
    cases es with
    | nil =>
      have same : x=e := Option.some.inj last
      subst x
      simpa using next
    | cons y es =>
      intro a b member
      simp only [List.cons_append,List.tail_cons,List.zip_cons_cons,List.mem_cons] at member
      rcases member with same |member
      · cases same
        exact turns x y (by simp)
      · exact ih (by intro a b h;exact turns a b (by
          simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons];exact Or.inr h))
          (by simpa only [List.getLast?_cons_cons] using last) a b member

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
private theorem reverse_control_turn {e f : Endpoint g}
    (turn : ControlOnlyTurn (g:=g) e f) :
    ControlOnlyTurn (g:=g) (g.wire f) (g.wire e) := by
  rcases turn with ⟨w,d,arrives,leaves⟩ |⟨node,p,q,op,shape,control,arrives,leaves⟩
  · refine Or.inl ⟨w,!d,?_,?_⟩
    · simpa only [Pairing.involutive] using leaves
    · simpa only [Bool.not_not] using arrives
  · exact Or.inr ⟨node,q,p,op,shape,control,by simpa only [Pairing.involutive] using leaves,arrives⟩

private theorem reverse_control_turns (es : List (Endpoint g))
    (turns : ∀ e f,(e,f)∈es.zip es.tail →ControlOnlyTurn (g:=g) e f) :
    ∀ e f,(e,f)∈(reverseEdges es).zip (reverseEdges es).tail →ControlOnlyTurn (g:=g) e f := by
  induction es with
  | nil => simp [reverseEdges]
  | cons e es ih =>
    cases es with
    | nil => simp [reverseEdges]
    | cons f es =>
      have tail := ih (by intro x y h;exact turns x y (by
        simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons];exact Or.inr h))
      rw [show reverseEdges (e::f::es)=reverseEdges (f::es)++[g.wire e] from by simp [reverseEdges]]
      apply adjacent_snoc tail (e:=g.wire f)
      · simp [reverseEdges]
      · exact reverse_control_turn (turns e f (by simp))

private abbrev Regular (block : List (Endpoint g)) : Prop := block≠[] ∧
  (∀ e f,(e,f)∈block.zip block.tail →ControlOnlyTurn (g:=g) e f) ∧
  ∃(node : N) (port : Port (g.label node).sort),
    ((g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) ∧
      block.getLast?=some (g.wire (.inl ⟨node,port⟩))

private theorem child_proper {kind : Kind} {ctx dep : Port kind}
    (roles : SyntaxChildPorts kind ctx dep step) : kind=.op .app ∨kind=.op .lam := by
  cases roles
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
private theorem proper_realizes
    (realizes : SourcePortRealizes original g root sourcePort endpoint)
    (nonexternal : sourcePort≠.external) :
    ∃(node : N) (port : Port (g.label node).sort),endpoint=.inl ⟨node,port⟩ ∧
      ((g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) := by
  cases realizes with
  | external => exact False.elim (nonexternal rfl)
  | departure lookup role parent word roles finish => exact ⟨_,_,rfl,child_proper roles⟩
  | appContext lookup access word shape role finish => exact ⟨_,_,rfl,Or.inl shape⟩
  | lamContext lookup access word shape role finish => exact ⟨_,_,rfl,Or.inr shape⟩
  | binding lookup parent word shape contextRole role finish => exact ⟨_,_,rfl,Or.inr shape⟩

private theorem chosen_reverse_regular
    (cell : {e : SourceEdge //e∈sourceEdges [] .external original})
    (fragment : SourceEdgeFragment original g root cell.val p)
    (nonexternal : cell.val.fromPort≠.external) : Regular (reverseEdges fragment.segments) := by
  obtain ⟨node,port,endpoint,proper⟩ := proper_realizes fragment.fromRealizes nonexternal
  have finish : (reverseEdges fragment.segments).getLast?=some (g.wire fragment.fromEndpoint) := by
    simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,fragment.start,Option.map_some]
  refine ⟨?_,reverse_control_turns _ (fragment.forward.empty_word_control_only fragment.emptyWord),
    node,port,proper,?_⟩
  · intro empty
    rw [empty] at finish
    cases finish
  · simpa only [endpoint] using finish

private theorem principal_regular (edge : BetaEdge g) : Regular edge.principal :=
  ⟨edge.principal_nonempty,(fun e f h=>Or.inl (edge.transparent e f h)),
    edge.lam,edge.lamCtx,Or.inr (congrArg Graph.Label.sort edge.lamLabel),edge.principalEnd⟩
private theorem reverse_regular (edge : BetaEdge g) : Regular edge.reverseRoute := by
  refine ⟨?_,?_,edge.app,edge.appFun,Or.inl (congrArg Graph.Label.sort edge.appLabel),edge.reverse_finish⟩
  · intro empty
    have finish := edge.reverse_finish
    rw [empty] at finish
    cases finish
  · intro e f h
    exact Or.inl (transparent_reverse_turns edge.principal edge.transparent e f h)
end

theorem EvaluatedChainResiduals.reverse_reading_letter_blocks_regular
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
    (let blocks : List (List (Endpoint site.net)) :=
      (out.node member).label.readLetters false |>.map
        (fun letter=>orientPhysical false
          (letter.sourceWord selection.atomWord edge.principal edge.reverseRoute))
     blocks.flatten=reverseEdges (selection.evalLabel edge (out.node member).label) ∧
       ∀ block∈blocks,block≠[] ∧
         (∀ e f,(e,f)∈block.zip block.tail →ControlOnlyTurn (g:=site.net) e f) ∧
         ∃ (node : K⊕(Unit⊕Unit)) (port : Port (site.net.label node).sort),
           ((site.net.label node).sort=.op .app ∨(site.net.label node).sort=.op .lam) ∧
             block.getLast?=some (site.net.wire (.inl ⟨node,port⟩))) := by
  obtain ⟨atoms,_writing⟩ := EvaluatedChainResiduals.writing_letter_blocks_regular site initial localHistory out member
  refine ⟨?_,?_⟩
  · have assembly := selection.interpret_read_label edge false (out.node member).label
    simpa only [List.flatMap,interpretReadLetters,orientPhysical,if_false] using assembly
  · intro block inside
    obtain ⟨letter,letterMember,rfl⟩ := List.mem_map.mp inside
    have memberWriting : letter∈(out.node member).label.letters := by
      simpa [Label.readLetters] using letterMember
    cases letter with
    | atom n =>
      obtain ⟨cell,atomic,same⟩ := atoms n memberWriting
      have nonexternal := nonroot_cell_nonexternal initial localHistory (out.lookup member)
        (chain.reading_ne_nil member.property) cell.property atomic memberWriting
      change Regular (reverseEdges (selection.atomWord n))
      rw [same]
      exact chosen_reverse_regular cell (selection.chosen cell).2 nonexternal
    | over degree =>
      have same : reverseEdges edge.principal=edge.reverseRoute := rfl
      change Regular (reverseEdges edge.principal)
      rw [same]
      exact reverse_regular edge
    | under degree =>
      have same : reverseEdges edge.reverseRoute=edge.principal := by
        change reverseEdges (reverseEdges edge.principal)=edge.principal
        exact reverseEdges_involutive _
      change Regular (reverseEdges edge.reverseRoute)
      rw [same]
      exact principal_regular edge

#print axioms EvaluatedChainResiduals.reverse_reading_letter_blocks_regular
end Lamping.AG

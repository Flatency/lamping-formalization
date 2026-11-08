import Lamping.Lambda.LabelHeadFreeWalks
namespace Lamping.Lambda.Labelled

/-- Head ports and ports without a syntax node cannot support a permitted
head-free turn. Free/binding ports retain their actual distinction. -/
def SourcePort.DeadAtHead (app lam : Label) (port : SourcePort) : Prop :=
  port.AtHead app lam ∨ port.node=none

theorem HeadFreeTurn.live_ports (turn : HeadFreeTurn app lam a b) :
    ¬a.DeadAtHead app lam ∧ ¬b.DeadAtHead app lam := by
  obtain ⟨node,left,right⟩ := turn.source_turn.same_node
  constructor
  · intro dead
    rcases dead with blocked | empty
    · exact turn.avoids_head.1 blocked
    · rw [left] at empty; cases empty
  · intro dead
    rcases dead with blocked | empty
    · exact turn.avoids_head.2 blocked
    · rw [right] at empty; cases empty

/-- An actual isolated edge cannot occur anywhere in a restricted walk
starting at a live port. At joins each next component again starts live. -/
theorem HeadFreeWalk.excludes_isolated
    (walk : HeadFreeWalk edges app lam a word b) (live : ¬a.DeadAtHead app lam)
    (isolated : ∀ {s e r},SourceTraverse edges s e r → e.atom=n →
      s.DeadAtHead app lam ∧ r.DeadAtHead app lam) :
    ∀ e∈word,e.atom≠n := by
  induction walk with
  | edge actual =>
    intro e member same
    have equal := List.mem_singleton.mp member
    cases equal
    exact live (isolated actual same).1
  | @join start first middle next rest finish left turn right hl hr =>
    intro e member
    rcases List.mem_append.mp member with before | after
    · exact hl live e before
    · exact hr turn.live_ports.2 e after

/-- Unlike the earlier nonroot-edge API, the incoming edge is retained.
Its only extra possible endpoint is the actual head boundary context. -/
theorem SourceTraverse.head_subtree_ports
    (actual : SourceTraverse (sourceEdges env ctx t) a e b)
    (boundary : ctx.AtHead app lam) :
    (SubtreePort env t.labels a ∨ a.AtHead app lam) ∧
    (SubtreePort env t.labels b ∨ b.AtHead app lam) := by
  have startClass : ∀ edge∈sourceEdges env ctx t,
      SubtreePort env t.labels edge.fromPort ∨ edge.fromPort.AtHead app lam := by
    intro edge member
    rcases sourceEdges_from_port t member with same | inside
    · exact .inr (same ▸ boundary)
    · exact .inl (.inl inside)
  cases actual with
  | forward member _ => exact ⟨startClass _ member,.inl (sourceEdges_to_port t member)⟩
  | backward member _ => exact ⟨.inl (sourceEdges_to_port t member),startClass _ member⟩

theorem HeadFreeWalk.subtree_ports
    (walk : HeadFreeWalk (sourceEdges env ctx t) app lam a word b)
    (boundary : ctx.AtHead app lam) :
    (SubtreePort env t.labels a ∨ a.AtHead app lam) ∧
    (SubtreePort env t.labels b ∨ b.AtHead app lam) := by
  induction walk with
  | edge actual => exact actual.head_subtree_ports boundary
  | join _ _ _ left right => exact ⟨left.1,right.2⟩

/-- Head-free walks cannot mix actual disjoint syntax components even when
their incoming edges remain present. The boundary restriction is established
on each actual component context; cover still concerns individual real edges. -/
theorem HeadFreeWalk.one_component {Index : Type} {sites : Index → Path}
    {environments : Index → List Label} {contexts : Index → SourcePort} {subtrees : Index → LTerm}
    (components : ∀ i,SourceSubterm [] .external t (sites i) (environments i) (contexts i) (subtrees i))
    (initial : INIT t) (separate : ∀ i j,i≠j → DisjointPositions (sites i) (sites j))
    (boundaries : ∀ i,(contexts i).AtHead app lam)
    (walk : HeadFreeWalk (sourceEdges [] .external t) app lam a word b)
    (cover : ∀ {s e r},e∈word → SourceTraverse (sourceEdges [] .external t) s e r →
      ∃ i,SourceTraverse (sourceEdges (environments i) (contexts i) (subtrees i)) s e r) :
    ∃ i,HeadFreeWalk (sourceEdges (environments i) (contexts i) (subtrees i)) app lam a word b := by
  induction walk with
  | edge actual =>
    obtain ⟨i,localEdge⟩ := cover List.mem_cons_self actual
    exact ⟨i,.edge localEdge⟩
  | @join start first middle next rest finish left turn right hl hr =>
    obtain ⟨i,leftWalk⟩ := hl (fun member actual => cover (List.mem_append_left _ member) actual)
    obtain ⟨j,rightWalk⟩ := hr (fun member actual => cover (List.mem_append_right _ member) actual)
    have leftPort : SubtreePort (environments i) (subtrees i).labels middle := by
      rcases (leftWalk.subtree_ports (boundaries i)).2 with inside | blocked
      · exact inside
      · exact False.elim (turn.avoids_head.1 blocked)
    have rightPort : SubtreePort (environments j) (subtrees j).labels next := by
      rcases (rightWalk.subtree_ports (boundaries j)).1 with inside | blocked
      · exact inside
      · exact False.elim (turn.avoids_head.2 blocked)
    have same : i=j := by
      classical
      by_cases equal : i=j
      · exact equal
      · exact False.elim (SourceTurn.not_between_disjoint_subtrees (components i) (components j)
          initial (separate i j equal) leftPort rightPort turn.source_turn)
    cases same
    exact ⟨i,.join leftWalk turn rightWalk⟩

/-- The two original head edges are genuinely isolated after their app and
lambda turns are removed. INIT supplies actual edge identity, not arbitrary
label-word injectivity. Both signed orientations are covered. -/
theorem SourceTraverse.root_head_isolated {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (actual : SourceTraverse (sourceEdges [] .external (.app beta (.lam alpha body) argument)) a e b)
    (headAtom : Label.atom e.atom=beta ∨ Label.atom e.atom=alpha) :
    a.DeadAtHead beta alpha ∧ b.DeadAtHead beta alpha := by
  have classify : ∀ edge∈sourceEdges [] .external (.app beta (.lam alpha body) argument),
      (edge.atom=beta ∨ edge.atom=alpha) →
      edge.fromPort.DeadAtHead beta alpha ∧ edge.toPort.DeadAtHead beta alpha := by
    intro edge member same
    rcases same with betaEq | alphaEq
    · have equal : edge=⟨beta,.external,.appContext beta⟩ :=
        sourceEdges_unique initial member List.mem_cons_self betaEq
      cases equal
      exact ⟨.inr rfl,.inl rfl⟩
    · have selected : (⟨alpha,.appFn beta,.lamContext alpha⟩ : SourceEdge)∈
          sourceEdges [] .external (.app beta (.lam alpha body) argument) :=
        List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self)
      have equal := sourceEdges_unique initial member selected alphaEq
      cases equal
      exact ⟨.inl rfl,.inl rfl⟩
  cases actual with
  | forward member atomic => exact classify _ member (headAtom.imp (atomic.trans ·) (atomic.trans ·))
  | backward member atomic =>
    have ends := classify _ member (headAtom.imp (atomic.trans ·) (atomic.trans ·))
    exact ⟨ends.2,ends.1⟩

/-- Every occurrence of either head atom is excluded throughout the walk,
including buried reversed payloads; the start is a different actual app. -/
theorem HeadFreeWalk.root_head_atoms_absent {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (walk : HeadFreeWalk (sourceEdges [] .external (.app beta (.lam alpha body) argument)) beta alpha
      (.appFn appId) word finish) (different : appId≠beta) :
    ∀ e∈word,Label.atom e.atom≠beta ∧ Label.atom e.atom≠alpha := by
  have live : ¬(SourcePort.appFn appId).DeadAtHead beta alpha := by
    simp [SourcePort.DeadAtHead,SourcePort.AtHead,SourcePort.node,different]
  intro e member
  constructor
  · intro same
    have absent := walk.excludes_isolated live (n := e.atom) (fun actual equal =>
      actual.root_head_isolated initial (.inl (by simpa only [equal] using same)))
    exact absent e member rfl
  · intro same
    have absent := walk.excludes_isolated live (n := e.atom) (fun actual equal =>
      actual.root_head_isolated initial (.inr (by simpa only [equal] using same)))
    exact absent e member rfl

/-- Once the two head edges are absent, each actual source traversal is an
actual body edge or argument edge. Their incoming edges remain present. -/
theorem SourceTraverse.root_head_cover {body argument : LTerm}
    (actual : SourceTraverse (sourceEdges [] .external (.app beta (.lam alpha body) argument)) a e b)
    (notApp : Label.atom e.atom≠beta) (notLam : Label.atom e.atom≠alpha) :
    SourceTraverse (sourceEdges [alpha] (.lamBody alpha) body) a e b ∨
      SourceTraverse (sourceEdges [] (.appArg beta) argument) a e b := by
  have classify : ∀ edge∈sourceEdges [] .external (.app beta (.lam alpha body) argument),
      edge.atom=Label.atom e.atom →
      edge∈sourceEdges [alpha] (.lamBody alpha) body ∨ edge∈sourceEdges [] (.appArg beta) argument := by
    intro edge member atomic
    rcases List.mem_cons.mp member with same | member
    · cases same; exact False.elim (notApp atomic.symm)
    · rcases List.mem_append.mp member with function | arg
      · rcases List.mem_cons.mp function with same | inner
        · cases same; exact False.elim (notLam atomic.symm)
        · exact .inl inner
      · exact .inr arg
  cases actual with
  | forward member atomic =>
    rcases classify _ member atomic with body | arg
    · exact .inl (.forward body atomic)
    · exact .inr (.forward arg atomic)
  | backward member atomic =>
    rcases classify _ member atomic with body | arg
    · exact .inl (.backward body atomic)
    · exact .inr (.backward arg atomic)

/-- A generated root-head-free degree walk lies wholly in the actual body
or wholly in the original argument. No copy occurrence or component is an
input; the component is selected from the actual nonempty path. -/
theorem HeadFreeWalk.root_head_one_component {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (walk : HeadFreeWalk (sourceEdges [] .external (.app beta (.lam alpha body) argument)) beta alpha
      (.appFn appId) word finish) (different : appId≠beta) :
    HeadFreeWalk (sourceEdges [alpha] (.lamBody alpha) body) beta alpha (.appFn appId) word finish ∨
      HeadFreeWalk (sourceEdges [] (.appArg beta) argument) beta alpha (.appFn appId) word finish := by
  let sites : Bool → Path := fun i => if i then [.arg] else [.fn,.body]
  let envs : Bool → List Label := fun i => if i then [] else [alpha]
  let ports : Bool → SourcePort := fun i => if i then .appArg beta else .lamBody alpha
  let trees : Bool → LTerm := fun i => if i then argument else body
  have components : ∀ i,SourceSubterm [] .external (.app beta (.lam alpha body) argument)
      (sites i) (envs i) (ports i) (trees i) := by
    intro i; cases i
    · exact .fn (.body .nil)
    · exact .arg .nil
  have separate : ∀ i j,i≠j → DisjointPositions (sites i) (sites j) := by
    intro i j different
    cases i <;> cases j <;> simp_all [sites,DisjointPositions]
  have boundaries : ∀ i,(ports i).AtHead beta alpha := by
    intro i; cases i <;> rfl
  have absent := walk.root_head_atoms_absent initial different
  obtain ⟨i,localWalk⟩ := walk.one_component components initial separate boundaries (by
    intro s e r member actual
    rcases actual.root_head_cover (absent e member).1 (absent e member).2 with bodyEdge | argumentEdge
    · exact ⟨false,bodyEdge⟩
    · exact ⟨true,argumentEdge⟩)
  cases i
  · exact .inl localWalk
  · exact .inr localWalk

/-- Root-head static support cut for an actual transported degree. The
original head degree is outside the supplied support; the selected body or
argument region is proved from the generated walk, not assumed as a cover. -/
theorem History.root_head_degree_region {body argument : LTerm}
    (history : History ps (.app beta (.lam alpha body) argument) u)
    (initial : INIT (.app beta (.lam alpha body) argument))
    (outside : ¬alpha.Supported region) (degree : u.degreeAt p=some l)
    (support : l.Supported region) :
    l.Supported (SourceRegion body) ∨ l.Supported (SourceRegion argument) := by
  obtain ⟨appId,lamId,appDifferent,_,route⟩ :=
    history.generated_head_free_degree initial SourceSubterm.nil outside degree support
  rcases route.head_free_walk.root_head_one_component initial appDifferent with inBody | inArgument
  · exact .inl ((Label.supported_iff_within _ _).mpr inBody.walk.within_source)
  · exact .inr ((Label.supported_iff_within _ _).mpr inArgument.walk.within_source)
end Lamping.Lambda.Labelled





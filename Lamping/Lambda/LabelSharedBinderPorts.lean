import Lamping.Lambda.LabelArgumentBinderScope
namespace Lamping.Lambda.Labelled

/-- Sharing a binding endpoint across actual disjoint subtrees forces that
binder to be on their external syntax ancestry, never inside either subtree. -/
theorem SourceSubterm.shared_binding_above
    (left : SourceSubterm [] .external t p envA ctxA a)
    (right : SourceSubterm [] .external t q envB ctxB b) (initial : INIT t)
    (apart : DisjointPositions p q)
    (leftEdge : e∈sourceEdges envA ctxA a) (rightEdge : f∈sourceEdges envB ctxB b)
    (leftPort : e.toPort=.lamBind l) (rightPort : f.toPort=.lamBind l) :
    BinderAbove t p l ∧ BinderAbove t q l := by
  have aboveOne : ∀ {p q envA ctxA a envB ctxB b e f},
      SourceSubterm [] .external t p envA ctxA a → SourceSubterm [] .external t q envB ctxB b →
      DisjointPositions p q → e∈sourceEdges envA ctxA a → f∈sourceEdges envB ctxB b →
      e.toPort=.lamBind l → f.toPort=.lamBind l → BinderAbove t p l := by
    intro p q envA ctxA a envB ctxB b e f first second separate em fm ep fp
    rcases sourceEdges_to_port a em with ⟨node,member,nodeEq⟩ | ⟨node,outer,nodeEq⟩ | ⟨i,freeEq⟩
    · have same : node=l := by simpa only [ep,SourcePort.node,Option.some.injEq] using nodeEq.symm
      exact False.elim (second.edge_not_bind_disjoint initial first.lookup separate.symm fm (same ▸ member) fp)
    · have same : node=l := SourcePort.lamBind.inj (nodeEq.symm.trans ep)
      rcases first.binders_above l (same ▸ outer) with impossible | above
      · cases impossible
      · exact above
    · rw [ep] at freeEq
      cases freeEq
  exact ⟨aboveOne left right apart leftEdge rightEdge leftPort rightPort,
    aboveOne right left apart.symm rightEdge leftEdge rightPort leftPort⟩

private theorem edge_in_ancestor_subterm
    (initial : INIT t) (member : e∈sourceEdges [] .external t)
    (atNode : t.subterm p=some node) (atomic : node.label=e.atom)
    (paths : p=site++suffix) :
    ∃ env ctx copy,SourceSubterm [] .external t site env ctx copy ∧ e∈sourceEdges env ctx copy := by
  rw [paths,LTerm.subterm_append] at atNode
  obtain ⟨copy,copyLookup,inside⟩ := Option.bind_eq_some_iff.mp atNode
  obtain ⟨env,ctx,located⟩ := SourceSubterm.of_lookup t copyLookup [] .external
  have labelMember : e.atom∈copy.labels := atomic ▸ LTerm.label_mem_of_subterm inside
  obtain ⟨edge,edgeMember,equalAtom⟩ := sourceEdges_has_label (env := env) (atPort := ctx) labelMember
  have same := sourceEdges_unique initial (located.edges_subset edge edgeMember) member equalAtom
  exact ⟨env,ctx,copy,located,same ▸ edgeMember⟩

private theorem nonroot_label_ne (initial : INIT t)
    (lookup : t.subterm p=some node) (nonempty : p≠[]) : node.label≠t.label := by
  cases p with
  | nil => exact False.elim (nonempty rfl)
  | cons edge rest =>
    cases t with
    | var => cases edge <;> simp [LTerm.subterm] at lookup
    | lam l b =>
      cases edge with
      | fn => simp [LTerm.subterm] at lookup
      | arg => simp [LTerm.subterm] at lookup
      | body =>
        intro equal
        change node.label=l at equal
        exact (List.nodup_cons.mp initial.2).1 (equal ▸ LTerm.label_mem_of_subterm lookup)
    | app l fn arg =>
      cases edge with
      | body => simp [LTerm.subterm] at lookup
      | fn =>
        intro equal
        change node.label=l at equal
        exact (List.nodup_cons.mp initial.2).1 (List.mem_append_left _ (equal ▸ LTerm.label_mem_of_subterm lookup))
      | arg =>
        intro equal
        change node.label=l at equal
        exact (List.nodup_cons.mp initial.2).1 (List.mem_append_right _ (equal ▸ LTerm.label_mem_of_subterm lookup))

/-- Every genuine single-beta edge-image collision is in two actual
argument copies. Their source environments and physical edges are returned. -/
theorem StepAt.edge_image_collision_strict_copies {body argument : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (left : e∈sourceEdges [] .external (initLabels u.erase))
    (right : f∈sourceEdges [] .external (initLabels u.erase))
    (same : e.atom.relabel (initialRelabelling u 0)=f.atom.relabel (initialRelabelling u 0))
    (different : e≠f) :
    ∃ m p q envA ctxA a envB ctxB b,
      e.atom.relabel (initialRelabelling u 0)=Label.atom m ∧ Label.atom m∈argument.labels ∧
      ArgumentOccurrence body.erase p ∧ ArgumentOccurrence body.erase q ∧ p≠q ∧
      SourceSubterm [] .external (initLabels u.erase) (head++p) envA ctxA a ∧
      SourceSubterm [] .external (initLabels u.erase) (head++q) envB ctxB b ∧
      e∈sourceEdges envA ctxA a ∧ f∈sourceEdges envB ctxB b ∧ e.atom≠a.label ∧ f.atom≠b.label := by
  let basis := initLabels u.erase
  have labelMember : ∀ edge∈sourceEdges [] .external basis,edge.atom∈basis.labels := by
    intro edge member
    rw [←sourceEdges_atoms basis [] .external]
    exact List.mem_map.mpr ⟨edge,member,rfl⟩
  obtain ⟨p,node,atNode,nodeLabel⟩ := LTerm.label_mem_located basis (labelMember e left)
  obtain ⟨q,other,atOther,otherLabel⟩ := LTerm.label_mem_located basis (labelMember f right)
  have differentPaths : p≠q := by
    intro equal
    subst q
    have nodes := Option.some.inj (atNode.symm.trans atOther)
    exact different (sourceEdges_unique (init_is_INIT _) left right (nodeLabel.symm.trans ((congrArg LTerm.label nodes).trans otherLabel)))
  have equalLabels : (node.relabel (initialRelabelling u 0)).label=(other.relabel (initialRelabelling u 0)).label := by
    simpa only [LTerm.label_relabel,nodeLabel,otherLabel] using same
  obtain ⟨_,copyP,copyQ,currentCopy,_,suffixP,suffixQ,occP,occQ,diff,copyLookup,_,pathP,pathQ,strictP,strictQ⟩ :=
    step.label_collision_distinct_copies initial source (LTerm.basis_node_transport u atNode)
      (LTerm.basis_node_transport u atOther) equalLabels differentPaths
  obtain ⟨envA,ctxA,a,copyA,edgeA⟩ := edge_in_ancestor_subterm (init_is_INIT _) left atNode nodeLabel pathP
  obtain ⟨envB,ctxB,b,copyB,edgeB⟩ := edge_in_ancestor_subterm (init_is_INIT _) right atOther otherLabel pathQ
  have atContract : (LTerm.contract beta alpha body argument).subterm copyP=some currentCopy := by
    rw [LTerm.subterm_append,step.contract_lookup source] at copyLookup
    exact copyLookup
  have atCurrentNode := LTerm.basis_node_transport u atNode
  rw [pathP,LTerm.subterm_append,copyLookup] at atCurrentNode
  have copied := LTerm.contract_argument_copy_interior occP atContract
  obtain ⟨old,oldLookup,equalLabel⟩ := copied.nonroot_node atCurrentNode strictP
  have oldMember := LTerm.label_mem_of_subterm oldLookup
  obtain ⟨m,atomic⟩ := (initial.subterm (p := head++[.arg]) (by simp [LTerm.subterm_append,source,LTerm.subterm])).1 old.label oldMember
  have imageAtomic : e.atom.relabel (initialRelabelling u 0)=Label.atom m := by
    rw [LTerm.label_relabel,nodeLabel] at equalLabel
    exact equalLabel.symm.trans atomic
  refine ⟨m,copyP,copyQ,envA,ctxA,a,envB,ctxB,b,imageAtomic,atomic ▸ oldMember,occP,occQ,diff,copyA,copyB,edgeA,edgeB,?_,?_⟩
  · have inner : a.subterm suffixP=some node := by
      rw [pathP,LTerm.subterm_append,copyA.lookup] at atNode
      exact atNode
    exact nodeLabel ▸ nonroot_label_ne ((init_is_INIT _).subterm copyA.lookup) inner strictP
  · have inner : b.subterm suffixQ=some other := by
      rw [pathQ,LTerm.subterm_append,copyB.lookup] at atOther
      exact atOther
    exact otherLabel ▸ nonroot_label_ne ((init_is_INIT _).subterm copyB.lookup) inner strictQ

/-- Every genuine single-beta edge-image collision is in two actual
argument copies. Their source environments and physical edges are returned. -/
theorem StepAt.edge_image_collision_copies {body argument : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (left : e∈sourceEdges [] .external (initLabels u.erase))
    (right : f∈sourceEdges [] .external (initLabels u.erase))
    (same : e.atom.relabel (initialRelabelling u 0)=f.atom.relabel (initialRelabelling u 0))
    (different : e≠f) :
    ∃ m p q envA ctxA a envB ctxB b,
      e.atom.relabel (initialRelabelling u 0)=Label.atom m ∧ Label.atom m∈argument.labels ∧
      ArgumentOccurrence body.erase p ∧ ArgumentOccurrence body.erase q ∧ p≠q ∧
      SourceSubterm [] .external (initLabels u.erase) (head++p) envA ctxA a ∧
      SourceSubterm [] .external (initLabels u.erase) (head++q) envB ctxB b ∧
      e∈sourceEdges envA ctxA a ∧ f∈sourceEdges envB ctxB b := by
  obtain ⟨m,p,q,envA,ctxA,a,envB,ctxB,b,image,old,occP,occQ,diff,copyA,copyB,edgeA,edgeB,_,_⟩ :=
    step.edge_image_collision_strict_copies initial source left right same different
  exact ⟨m,p,q,envA,ctxA,a,envB,ctxB,b,image,old,occP,occQ,diff,copyA,copyB,edgeA,edgeB⟩
/-- A real same-image collision at a shared binding port necessarily uses
an old lambda strictly above the contracted head. All copy and binder
occurrences are constructed from the two physical edges. -/
theorem StepAt.shared_binding_collision_ancestor {body argument : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (left : e∈sourceEdges [] .external (initLabels u.erase))
    (right : f∈sourceEdges [] .external (initLabels u.erase))
    (same : e.atom.relabel (initialRelabelling u 0)=f.atom.relabel (initialRelabelling u 0))
    (different : e≠f) (leftPort : e.toPort=.lamBind (Label.atom j))
    (rightPort : f.toPort=.lamBind (Label.atom j)) :
    ∃ n binderSite tail oldBody,head=binderSite++(.body::tail) ∧
      initialRelabelling u 0 j=Label.atom n ∧
      t.subterm binderSite=some (.lam (Label.atom n) oldBody) := by
  obtain ⟨m,p,q,envA,ctxA,a,envB,ctxB,b,image,argumentAtom,occP,occQ,diff,copyA,copyB,edgeA,edgeB⟩ :=
    step.edge_image_collision_copies initial source left right same different
  have above := (copyA.shared_binding_above copyB (init_is_INIT _)
    ((occP.disjoint_of_ne occQ diff).prefix head) edgeA edgeB leftPort rightPort).1
  obtain ⟨site,after,current,copyPath,binderLookup⟩ := above
  have strict : head++p=site++(.body::after) := by simpa only [List.append_assoc,List.singleton_append] using copyPath
  obtain ⟨n,tail,oldBody,headPath,atomic,old⟩ := step.argument_copy_external_binder
    initial source occP strict binderLookup left leftPort image argumentAtom
  exact ⟨n,site,tail,oldBody,headPath,atomic,old⟩

/-- In the actual whole Standard run, every shared-binding collision's
binder atom is absent recursively from the final degree. -/
theorem History.standard_shared_binding_collision_avoid {body argument : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (left : e∈sourceEdges [] .external (initLabels u.erase))
    (right : f∈sourceEdges [] .external (initLabels u.erase))
    (same : e.atom.relabel (initialRelabelling u 0)=f.atom.relabel (initialRelabelling u 0))
    (different : e≠f) (leftPort : e.toPort=.lamBind (Label.atom j))
    (rightPort : f.toPort=.lamBind (Label.atom j))
    (history : History ps t v) (last : StepAt q v z)
    (tail : ParallelHistory u.erase z.erase) (ordinary : Atomic tail)
    (standard : Standard (.cons (singleContraction step.betaAt) tail))
    (paths : (ParallelHistory.cons (singleContraction step.betaAt) tail).derivation.paths=ps++[q])
    (degree : v.degreeAt q=some l) :
    ∃ n,initialRelabelling u 0 j=Label.atom n ∧ l.Supported (fun k => k≠n) := by
  obtain ⟨n,site,headSuffix,oldBody,headPath,atomic,old⟩ :=
    step.shared_binding_collision_ancestor initial source left right same different leftPort rightPort
  exact ⟨n,atomic,history.standard_ancestor_degree_avoid last initial old step.betaAt
    tail ordinary standard paths headPath degree⟩

end Lamping.Lambda.Labelled







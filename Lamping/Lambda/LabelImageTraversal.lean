import Lamping.Lambda.LabelSharedBinderPorts
namespace Lamping.Lambda.Labelled

/-- At a common actual node of disjoint subtree edge interiors, only their
external binding port can coincide. Port equality, not just node equality,
is retained. -/
theorem SourcePort.shared_subtree_node
    (left : SourceSubterm [] .external t p envA ctxA a)
    (right : SourceSubterm [] .external t q envB ctxB b) (initial : INIT t)
    (apart : DisjointPositions p q)
    (leftClass : SubtreePort envA a.labels port) (rightClass : SubtreePort envB b.labels port)
    (node : port.node=some l) : port=.lamBind l := by
  rcases leftClass.node_cases node with inLeft | ⟨outerLeft,leftPort⟩
  · rcases rightClass.node_cases node with inRight | ⟨outerRight,rightPort⟩
    · exact False.elim (LTerm.disjoint_subterm_labels initial left.lookup right.lookup apart l inLeft inRight)
    · exact False.elim (right.binder_not_in_disjoint initial left.lookup apart.symm outerRight inLeft)
  · rcases rightClass.node_cases node with inRight | ⟨_,_⟩
    · exact False.elim (left.binder_not_in_disjoint initial right.lookup apart outerLeft inRight)
    · exact leftPort

/-- Genuine outgoing syntax edges never start at a binding or principal
lambda port. This uses the actual root boundary, retained as an alternative. -/
theorem sourceEdges_from_lambda_port (t : LTerm) (member : e∈sourceEdges env ctx t) :
    (e.fromPort=.lamBind l → ctx=.lamBind l) ∧
    (e.fromPort=.lamContext l → ctx=.lamContext l) := by
  induction t generalizing env ctx with
  | var =>
    have equal := List.mem_singleton.mp member
    cases equal
    exact ⟨id,id⟩
  | lam l b ih =>
    rcases List.mem_cons.mp member with equal | inside
    · cases equal; exact ⟨id,id⟩
    · obtain ⟨binding,context⟩ := ih inside
      exact ⟨(fun eq => by cases binding eq),(fun eq => by cases context eq)⟩
  | app l f a hf ha =>
    rcases List.mem_cons.mp member with equal | inside
    · cases equal; exact ⟨id,id⟩
    · rcases List.mem_append.mp inside with inside | inside
      · obtain ⟨binding,context⟩ := hf inside
        exact ⟨(fun eq => by cases binding eq),(fun eq => by cases context eq)⟩
      · obtain ⟨binding,context⟩ := ha inside
        exact ⟨(fun eq => by cases binding eq),(fun eq => by cases context eq)⟩

/-- An actual signed traversal reaching a lambda principal port is its
forward incoming edge, including the exact original atomic identity. -/
theorem SourceTraverse.finish_lambda_context
    (walk : SourceTraverse (sourceEdges [] .external t) start edge finish)
    (endpoint : finish=.lamContext l) :
    Label.atom edge.atom=l ∧ edge.backwards=false := by
  cases walk with
  | forward member atomic => exact ⟨atomic.symm.trans (sourceEdges_to_lam t member endpoint),rfl⟩
  | backward member atomic =>
    have impossible := (sourceEdges_from_lambda_port t member).2 endpoint
    cases impossible




/-- Actual different single-beta edges with the same image can share a
node port only at an external binding port of their distinct argument copies. -/
theorem StepAt.edge_image_collision_common_port {body argument : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (left : e∈sourceEdges [] .external (initLabels u.erase))
    (right : f∈sourceEdges [] .external (initLabels u.erase))
    (same : e.atom.relabel (initialRelabelling u 0)=f.atom.relabel (initialRelabelling u 0))
    (different : e≠f) (node : port.node=some l)
    (leftPort : e.fromPort=port ∨ e.toPort=port)
    (rightPort : f.fromPort=port ∨ f.toPort=port) :
    ∃ j,port=.lamBind (Label.atom j) ∧ e.toPort=port ∧ f.toPort=port := by
  obtain ⟨_,p,q,envA,ctxA,a,envB,ctxB,b,_,_,occP,occQ,diff,copyA,copyB,edgeA,edgeB,nonrootA,nonrootB⟩ :=
    step.edge_image_collision_strict_copies initial source left right same different
  have classA : SubtreePort envA a.labels port := by
    rcases leftPort with fromEq | toEq
    · exact fromEq ▸ (.inl (sourceEdges_nonroot_from a edgeA nonrootA))
    · exact toEq ▸ sourceEdges_to_port a edgeA
  have classB : SubtreePort envB b.labels port := by
    rcases rightPort with fromEq | toEq
    · exact fromEq ▸ (.inl (sourceEdges_nonroot_from b edgeB nonrootB))
    · exact toEq ▸ sourceEdges_to_port b edgeB
  have binding := SourcePort.shared_subtree_node copyA copyB (init_is_INIT _)
    ((occP.disjoint_of_ne occQ diff).prefix head) classA classB node
  have toA : e.toPort=port := by
    rcases leftPort with fromEq | toEq
    · have impossible := (sourceEdges_from_lambda_port (initLabels u.erase) left).1 (fromEq.trans binding)
      cases impossible
    · exact toEq
  have toB : f.toPort=port := by
    rcases rightPort with fromEq | toEq
    · have impossible := (sourceEdges_from_lambda_port (initLabels u.erase) right).1 (fromEq.trans binding)
      cases impossible
    · exact toEq
  have above := (copyA.shared_binding_above copyB (init_is_INIT _)
    ((occP.disjoint_of_ne occQ diff).prefix head) edgeA edgeB (toA.trans binding) (toB.trans binding)).1
  obtain ⟨before,after,body,_,lookup⟩ := above
  obtain ⟨j,atomic⟩ := (init_is_INIT u.erase).1 l (LTerm.label_mem_of_subterm lookup)
  exact ⟨j,by simpa only [atomic] using binding,toA,toB⟩

/-- The eight real CodeTurns show exactly which preceding endpoint leads
into the shared binding branch. -/
theorem CodeTurn.into_binding (turn : CodeTurn before token after) (binding : after=.lamBind l) :
    before=.lamContext l ∧ token=.closeTok true true := by
  cases turn <;> cases binding <;> exact ⟨rfl,rfl⟩


/-- In an actual whole Standard run, the next physical edge is forced by
its full image once the previous traversal and turn are fixed. Membership of
the previous edge in the same local degree supplies the recursive support
needed to exclude the shared-binding alternative. -/
theorem History.standard_next_edge_image_injective {body argument : LTerm} {localDegree : Label}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (previous : SourceTraverse (sourceEdges [] .external (initLabels u.erase)) before previousEdge middle)
    (turn : CodeTurn middle token port)
    (left : e∈sourceEdges [] .external (initLabels u.erase))
    (right : f∈sourceEdges [] .external (initLabels u.erase))
    (same : e.atom.relabel (initialRelabelling u 0)=f.atom.relabel (initialRelabelling u 0))
    (leftPort : e.fromPort=port ∨ e.toPort=port)
    (rightPort : f.fromPort=port ∨ f.toPort=port)
    (history : History ps t v) (last : StepAt q v z)
    (tail : ParallelHistory u.erase z.erase) (ordinary : Atomic tail)
    (standard : Standard (.cons (singleContraction step.betaAt) tail))
    (paths : (ParallelHistory.cons (singleContraction step.betaAt) tail).derivation.paths=ps++[q])
    (degree : v.degreeAt q=some l) (localImage : localDegree.relabel (initialRelabelling u 0)=l)
    (previousMember : previousEdge∈localDegree.edgeWord) : e=f := by
  classical
  apply Classical.byContradiction
  intro different
  have node : ∃ id,port.node=some id := by cases turn <;> exact ⟨_,rfl⟩
  obtain ⟨id,nodeEq⟩ := node
  obtain ⟨j,binding,toA,toB⟩ := step.edge_image_collision_common_port initial source left right same different nodeEq leftPort rightPort
  have previousEnd := (turn.into_binding binding).1
  have previousAtom := (previous.finish_lambda_context previousEnd).1
  have atomIdentity : previousEdge.atom=j := by simpa only [Label.atom,Label.single.injEq,Letter.atom.injEq] using previousAtom
  obtain ⟨n,binderImage,avoid⟩ := history.standard_shared_binding_collision_avoid step initial source left right same different
    (toA.trans binding) (toB.trans binding) last tail ordinary standard paths degree
  have localSupport := (Label.supported_relabel _ _ localDegree).mp (localImage.symm ▸ avoid)
  have edgeSupport := (Label.supported_iff_within _ localDegree).mp localSupport previousEdge previousMember
  change (initialRelabelling u 0 previousEdge.atom).Supported (fun k => k≠n) at edgeSupport
  rw [atomIdentity,binderImage] at edgeSupport
  exact edgeSupport rfl

end Lamping.Lambda.Labelled





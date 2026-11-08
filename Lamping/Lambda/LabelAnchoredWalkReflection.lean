import Lamping.Lambda.LabelImageTraversal
import Lamping.Lambda.LabelExpandedCodeAlignment
namespace Lamping.Lambda.Labelled

/-- The actual predecessor may be reversed during leftward propagation.
Only its atomic membership is used, obtained from the same local degree. -/
theorem History.standard_next_edge_image_injective_atom {body argument : LTerm} {localDegree : Label}
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
    (previousMember : ∃ e∈localDegree.edgeWord,e.atom=previousEdge.atom) : e=f := by
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
  obtain ⟨member,inWord,sameAtom⟩ := previousMember
  have localSupport := (Label.supported_relabel _ _ localDegree).mp (localImage.symm ▸ avoid)
  have edgeSupport := (Label.supported_iff_within _ localDegree).mp localSupport member inWord
  change (initialRelabelling u 0 member.atom).Supported (fun k => k≠n) at edgeSupport
  rw [sameAtom,atomIdentity,binderImage] at edgeSupport
  exact edgeSupport rfl

/-- Exact signed next traversals agree after the same actual predecessor
and turn, under the genuine whole Standard degree support. -/
theorem History.standard_next_traversal_image_injective {body argument : LTerm} {localDegree : Label}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (previous : SourceTraverse (sourceEdges [] .external (initLabels u.erase)) before previousEdge middle)
    (turn : CodeTurn middle token port)
    (left : SourceTraverse (sourceEdges [] .external (initLabels u.erase)) port edgeA finishA)
    (right : SourceTraverse (sourceEdges [] .external (initLabels u.erase)) portB edgeB finishB)
    (sameStart : portB=port)
    (same : initialRelabelling u 0 edgeA.atom=initialRelabelling u 0 edgeB.atom)
    (direction : edgeA.backwards=edgeB.backwards)
    (history : History ps t v) (last : StepAt q v z)
    (tail : ParallelHistory u.erase z.erase) (ordinary : Atomic tail)
    (standard : Standard (.cons (singleContraction step.betaAt) tail))
    (paths : (ParallelHistory.cons (singleContraction step.betaAt) tail).derivation.paths=ps++[q])
    (degree : v.degreeAt q=some l) (localImage : localDegree.relabel (initialRelabelling u 0)=l)
    (previousMember : ∃ e∈localDegree.edgeWord,e.atom=previousEdge.atom) : edgeA=edgeB := by
  cases left with
  | @forward a n leftMember leftAtom =>
    cases right with
    | @forward b m rightMember rightAtom =>
      have equal := history.standard_next_edge_image_injective_atom step initial source previous turn leftMember rightMember
        (by simpa only [leftAtom,rightAtom,Label.relabel_atom] using same) (.inl rfl) (.inl sameStart)
        last tail ordinary standard paths degree localImage previousMember
      have atoms : n=m := by simpa only [Label.atom,Label.single.injEq,Letter.atom.injEq] using leftAtom.symm.trans ((congrArg SourceEdge.atom equal).trans rightAtom)
      cases atoms; rfl
    | backward => cases direction
  | @backward a n leftMember leftAtom =>
    cases right with
    | forward => cases direction
    | @backward b m rightMember rightAtom =>
      have equal := history.standard_next_edge_image_injective_atom step initial source previous turn leftMember rightMember
        (by simpa only [leftAtom,rightAtom,Label.relabel_atom] using same) (.inr rfl) (.inr sameStart)
        last tail ordinary standard paths degree localImage previousMember
      have atoms : n=m := by simpa only [Label.atom,Label.single.injEq,Letter.atom.injEq] using leftAtom.symm.trans ((congrArg SourceEdge.atom equal).trans rightAtom)
      cases atoms; rfl


private theorem CodeTurn.imageToken (turn : CodeTurn a token b) (s) :
    token.imageToken s=.inr token := by cases turn <;> rfl
private theorem CodeTurn.end_unique (left : CodeTurn a token b) (right : CodeTurn a token c) : b=c := by
  cases left <;> cases right <;> rfl
private theorem CodeTurn.start_unique (left : CodeTurn a token b) (right : CodeTurn c token b) : a=c := by
  have equal := left.flip.end_unique right.flip
  exact equal

private def ContinuationUnique (edges : List SourceEdge) (s : Nat → Label) (allowed : Nat → Prop) : Prop :=
  ∀ {a previous middle token port portB e f b c},
    SourceTraverse edges a previous middle → CodeTurn middle token port →
    SourceTraverse edges port e b → SourceTraverse edges portB f c → portB=port →
    s e.atom=s f.atom → e.backwards=f.backwards → allowed previous.atom → e=f

private theorem continue_unique (initial : INIT base) (s : Nat → Label) (allowed : Nat → Prop)
    (forced : ContinuationUnique (sourceEdges [] .external base) s allowed)
    (walk : CodedWalk (sourceEdges [] .external base) a code b) :
    ∀ {a' code' b' before previous middle token},
      (∀ e∈codeEdges code,allowed e.atom) →
      CodedWalk (sourceEdges [] .external base) a' code' b' →
      code.map (PathCodeToken.imageToken s)=code'.map (PathCodeToken.imageToken s) →
      SourceTraverse (sourceEdges [] .external base) before previous middle →
      CodeTurn middle token a → a'=a → allowed previous.atom → b=b' ∧ code=code' := by
  induction walk with
  | last edge =>
    intro a' code' b' before previous middle token valid other same prior turn starts priorAllowed
    cases other with
    | last otherEdge =>
      have first := List.cons.inj same |>.1
      have pair := Sum.inl.inj first
      have fields := Prod.mk.inj pair
      have equal := forced prior turn edge otherEdge starts fields.1 fields.2 priorAllowed
      cases equal
      exact ⟨(edge.endpoints initial otherEdge).2,rfl⟩
    | cons otherEdge otherTurn otherTail =>
      have impossible := List.cons.inj same |>.2
      cases impossible
  | @cons a e middle token next rest b edge turn tail ih =>
    intro a' code' b' before previous priorMiddle priorToken valid other same prior priorTurn starts priorAllowed
    cases other with
    | last otherEdge =>
      have impossible := List.cons.inj same |>.2
      cases impossible
    | @cons a' f middle' token' next' rest' b' otherEdge otherTurn otherTail =>
      have heads := List.cons.inj same
      have fields := Prod.mk.inj (Sum.inl.inj heads.1)
      have equal := forced prior priorTurn edge otherEdge starts fields.1 fields.2 priorAllowed
      cases equal
      have middleEqual := (edge.endpoints initial otherEdge).2
      cases middleEqual
      have turns := List.cons.inj heads.2
      have tokenEqual : token=token' := by
        have eq := turns.1
        rw [turn.imageToken,otherTurn.imageToken] at eq
        exact Sum.inr.inj eq
      cases tokenEqual
      have nextEqual := turn.end_unique otherTurn
      have currentAllowed := valid e List.mem_cons_self
      have tailAllowed : ∀ e∈codeEdges rest,allowed e.atom := by
        intro e member
        exact valid e (List.mem_cons_of_mem _ (by simpa only [turn.codeEdges] using member))
      obtain ⟨finish,codeEqual⟩ := ih tailAllowed otherTail turns.2 edge turn nextEqual.symm currentAllowed
      exact ⟨finish,by cases codeEqual; rfl⟩


private theorem CodedWalk.first_traverse (walk : CodedWalk edges a code b) :
    ∃ e finish,SourceTraverse edges a e finish ∧ e∈codeEdges code := by
  cases walk with
  | last edge => exact ⟨_,_,edge,List.mem_cons_self⟩
  | cons edge turn tail => exact ⟨_,_,edge,List.mem_cons_self⟩

private def AnchorUnique (edges : List SourceEdge) (s : Nat → Label) (outside : Label → Prop) : Prop :=
  ∀ {a e b c f d},SourceTraverse edges a e b → SourceTraverse edges c f d →
    s e.atom=s f.atom → e.backwards=f.backwards → outside (s e.atom) → e=f

private theorem anchored_unique (initial : INIT base) (s : Nat → Label) (allowed : Nat → Prop)
    (outside : Label → Prop) (forced : ContinuationUnique (sourceEdges [] .external base) s allowed)
    (anchorUnique : AnchorUnique (sourceEdges [] .external base) s outside)
    (walk : CodedWalk (sourceEdges [] .external base) a code b) :
    ∀ {a' code' b'},(∀ e∈codeEdges code,allowed e.atom) →
      (∃ e∈codeEdges code,outside (s e.atom)) →
      CodedWalk (sourceEdges [] .external base) a' code' b' →
      code.map (PathCodeToken.imageToken s)=code'.map (PathCodeToken.imageToken s) →
      a=a' ∧ b=b' ∧ code=code' := by
  induction walk with
  | last edge =>
    intro a' code' b' valid anchor other same
    cases other with
    | last otherEdge =>
      have fields := Prod.mk.inj (Sum.inl.inj (List.cons.inj same).1)
      obtain ⟨r,member,out⟩ := anchor
      have equalR := List.mem_singleton.mp member
      cases equalR
      have equal := anchorUnique edge otherEdge fields.1 fields.2 out
      cases equal
      obtain ⟨start,finish⟩ := edge.endpoints initial otherEdge
      exact ⟨start,finish,rfl⟩
    | cons otherEdge otherTurn otherTail => cases (List.cons.inj same).2
  | @cons a e middle token next rest b edge turn tail ih =>
    intro a' code' b' valid anchor other same
    cases other with
    | last otherEdge => cases (List.cons.inj same).2
    | @cons a' f middle' token' next' rest' b' otherEdge otherTurn otherTail =>
      have heads := List.cons.inj same
      have fields := Prod.mk.inj (Sum.inl.inj heads.1)
      have turns := List.cons.inj heads.2
      have tokenEqual : token=token' := by
        have eq := turns.1
        rw [turn.imageToken,otherTurn.imageToken] at eq
        exact Sum.inr.inj eq
      cases tokenEqual
      have currentAllowed := valid e List.mem_cons_self
      have tailAllowed : ∀ e∈codeEdges rest,allowed e.atom := by
        intro e member
        exact valid e (List.mem_cons_of_mem _ (by simpa only [turn.codeEdges] using member))
      obtain ⟨anchorEdge,anchorMember,anchorOutside⟩ := anchor
      have split : anchorEdge=e ∨ anchorEdge∈codeEdges rest := by
        simpa only [codeEdges,turn.codeEdges,List.mem_cons] using anchorMember
      rcases split with first | inTail
      · cases first
        have equal := anchorUnique edge otherEdge fields.1 fields.2 anchorOutside
        cases equal
        obtain ⟨start,middleEqual⟩ := edge.endpoints initial otherEdge
        cases middleEqual
        have nextEqual := turn.end_unique otherTurn
        obtain ⟨finish,tailEqual⟩ := continue_unique initial s allowed forced tail tailAllowed otherTail
          turns.2 edge turn nextEqual.symm currentAllowed
        exact ⟨start,finish,by cases tailEqual; rfl⟩
      · obtain ⟨nextEqual,finish,tailEqual⟩ := ih tailAllowed ⟨anchorEdge,inTail,anchorOutside⟩ otherTail turns.2
        cases nextEqual
        have middleEqual := turn.start_unique otherTurn
        obtain ⟨firstEdge,firstFinish,firstTraverse,firstMember⟩ := tail.first_traverse
        have firstAllowed : allowed firstEdge.flip.atom := tailAllowed firstEdge firstMember
        have equalFlip := forced firstTraverse.flip turn.flip edge.flip otherEdge.flip middleEqual.symm
          fields.1 (congrArg Bool.not fields.2) firstAllowed
        have equal : e=f := by
          have flipped := congrArg OrientedAtom.flip equalFlip
          simpa only [OrientedAtom.flip_flip] using flipped
        cases equal
        have start := (edge.endpoints initial otherEdge).1
        exact ⟨start,finish,by cases tailEqual; rfl⟩


/-- Whole finite walk reflection from a genuine non-argument anchor. The
left walk is the actual local-degree code; its recursive membership, the
whole Standard schedule, and the exact global relabelling discharge both
forward and backward continuation. No arbitrary anchored-walk injection is
asserted. -/
theorem History.standard_anchored_degree_code_reflection {body argument : LTerm} {localDegree : Label}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (history : History ps t v) (last : StepAt q v z)
    (tail : ParallelHistory u.erase z.erase) (ordinary : Atomic tail)
    (standard : Standard (.cons (singleContraction step.betaAt) tail))
    (paths : (ParallelHistory.cons (singleContraction step.betaAt) tail).derivation.paths=ps++[q])
    (degree : v.degreeAt q=some l) (localImage : localDegree.relabel (initialRelabelling u 0)=l)
    (walk : CodedWalk (sourceEdges [] .external (initLabels u.erase)) a (localDegree.pathCode false) b)
    (other : CodedWalk (sourceEdges [] .external (initLabels u.erase)) a' code' b')
    (same : localDegree.imageCode (initialRelabelling u 0) false=code'.map (PathCodeToken.imageToken (initialRelabelling u 0)))
    (anchor : ∃ e∈localDegree.edgeWord,¬(initialRelabelling u 0 e.atom).Supported (SourceRegion argument)) :
    a=a' ∧ b=b' ∧ localDegree.pathCode false=code' := by
  let s := initialRelabelling u 0
  let allowed : Nat → Prop := fun n => ∃ e∈localDegree.edgeWord,e.atom=n
  let outside : Label → Prop := fun image => ¬image.Supported (SourceRegion argument)
  have forced : ContinuationUnique (sourceEdges [] .external (initLabels u.erase)) s allowed := by
    intro before previous middle token port portB e f b c prior turn left right starts images directions member
    exact history.standard_next_traversal_image_injective step initial source prior turn left right starts images directions
      last tail ordinary standard paths degree localImage member
  have anchorUnique : AnchorUnique (sourceEdges [] .external (initLabels u.erase)) s outside := by
    intro start e finish start' f finish' left right images directions out
    cases left with
    | @forward edge n member atomic =>
      cases right with
      | @forward edge' m member' atomic' =>
        have equal := step.outside_argument_edge_injective initial source member member'
          (by simpa only [atomic,atomic',Label.relabel_atom] using images)
          (by simpa only [atomic,Label.relabel_atom] using out)
        have atoms : n=m := by simpa only [Label.atom,Label.single.injEq,Letter.atom.injEq] using atomic.symm.trans ((congrArg SourceEdge.atom equal).trans atomic')
        cases atoms; rfl
      | backward => cases directions
    | @backward edge n member atomic =>
      cases right with
      | forward => cases directions
      | @backward edge' m member' atomic' =>
        have equal := step.outside_argument_edge_injective initial source member member'
          (by simpa only [atomic,atomic',Label.relabel_atom] using images)
          (by simpa only [atomic,Label.relabel_atom] using out)
        have atoms : n=m := by simpa only [Label.atom,Label.single.injEq,Letter.atom.injEq] using atomic.symm.trans ((congrArg SourceEdge.atom equal).trans atomic')
        cases atoms; rfl
  have valid : ∀ e∈codeEdges (localDegree.pathCode false),allowed e.atom := by
    intro e member
    exact ⟨e,by simpa only [Label.codeEdges_pathCode,Bool.false_eq_true,ite_false] using member,rfl⟩
  have hasAnchor : ∃ e∈codeEdges (localDegree.pathCode false),outside (s e.atom) := by
    simpa only [Label.codeEdges_pathCode,Bool.false_eq_true,ite_false] using anchor
  exact anchored_unique (init_is_INIT _) s allowed outside forced anchorUnique walk valid hasAnchor other same

end Lamping.Lambda.Labelled





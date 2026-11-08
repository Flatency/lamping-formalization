import Lamping.Lambda.UncreatedPrerequisiteReadings
import Lamping.Lambda.SyntaxIncidence
import Lamping.Lambda.BetaPreimageLabels
namespace Lamping.Lambda.Labelled
open SyntaxIncidence

/-- Zero-edge lexical jumps preserve the actual incoming target vertex. -/
theorem PrerequisitePrefix.target_of_no_edges
    (segment : PrerequisitePrefix t start edges finish) (empty : edges=[])
    (atFinish : Target t finish vertex) : Target t start vertex := by
  induction segment generalizing vertex with
  | refl => exact atFinish
  | app _ _ _ _ => cases empty
  | lam _ _ _ _ => cases empty
  | @var leaf stamp index parent origin body rest es finish lookup binder split depth tail ih =>
    let actual : ProperPosition t := ⟨parent,Or.inr ⟨origin,body,binder⟩⟩
    have same : vertex=some actual := Target.unique (ih empty atFinish) (Or.inl rfl)
    subst vertex
    exact Or.inr ⟨stamp,index,origin,body,rest,lookup,binder,split,depth⟩

/-- Pointwise proper occurrence preimages and the external boundary.
This relation asserts neither injectivity nor an incidence isomorphism. -/
inductive BetaVertexPreimage (body argument : LTerm) (site : Path) (source target : LTerm) :
    Vertex target →Vertex source →Prop where
  | boundary : BetaVertexPreimage body argument site source target none none
  | proper {current : ProperPosition target} {old : ProperPosition source} :
      BetaNodePreimage body argument site current.val old.val →
      BetaVertexPreimage body argument site source target (some current) (some old)

/-- The old endpoint coordinate is fixed by the supplied current vertex.
This is forward uniqueness, not injectivity between different copies. -/
theorem BetaVertexPreimage.unique
    {body argument source target : LTerm} {site : Path}
    {current : Vertex target} {first second : Vertex source}
    (left : BetaVertexPreimage body argument site source target current first)
    (right : BetaVertexPreimage body argument site source target current second) : first=second := by
  cases left with
  | boundary => cases right; rfl
  | proper origin =>
    cases right with
    | proper other => exact congrArg some (Subtype.ext (origin.unique other))

/-- The target endpoint of a supplied occurrence preimage has a genuine
old target preimage, including lexical binders outside the contracted head.
The incoming edge may be created: this theorem does not preserve labels. -/
theorem StepAt.beta_incidence_target_preimage
    {source target body argument : LTerm} {site edge oldEdge : Path} {beta alpha : Label}
    {vertex : Vertex target}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site edge oldEdge)
    (endpoint : Target target edge vertex) :
    ∃ oldVertex,Target source oldEdge oldVertex ∧
      BetaVertexPreimage body argument site source target vertex oldVertex := by
  cases vertex with
  | none => cases endpoint
  | some position =>
    rcases endpoint with equal | ⟨stamp,index,binderStamp,binderBody,rest,lookup,binder,split,depth⟩
    · rw [equal] at origin
      rcases position.property with ⟨stamp,fn,arg,lookup⟩ | ⟨stamp,inner,lookup⟩
      · obtain ⟨old,oldLookup,same⟩ := step.preimage_node_constructor redex origin lookup
        cases old with
        | var => cases same
        | lam => cases same
        | app oldStamp oldFn oldArg =>
          let oldPosition : ProperPosition source := ⟨oldEdge,Or.inl ⟨oldStamp,oldFn,oldArg,oldLookup⟩⟩
          exact ⟨some oldPosition,Or.inl rfl,.proper origin⟩
      · obtain ⟨old,oldLookup,same⟩ := step.preimage_node_constructor redex origin lookup
        cases old with
        | var => cases same
        | app => cases same
        | lam oldStamp oldBody =>
          let oldPosition : ProperPosition source := ⟨oldEdge,Or.inr ⟨oldStamp,oldBody,oldLookup⟩⟩
          exact ⟨some oldPosition,Or.inl rfl,.proper origin⟩
    · obtain ⟨oldParent,oldStamp,oldBody,oldBinder,oldJump,parentOrigin⟩ :=
        step.beta_variable_preimage_prefix redex origin binder (by simpa only [depth] using lookup) split
      let oldPosition : ProperPosition source := ⟨oldParent,Or.inr ⟨oldStamp,oldBody,oldBinder⟩⟩
      exact ⟨some oldPosition,oldJump.target_of_no_edges rfl (Or.inl rfl),.proper parentOrigin⟩
private theorem parent_before_last {parent site relative : Path} {child : Step}
    (equal : parent++[child]=site++relative) (nonroot : relative≠[]) :
    ∃ inside,parent=site++inside ∧relative=inside++[child] := by
  induction site generalizing parent with
  | nil => exact ⟨parent,rfl,equal.symm⟩
  | cons head rest ih =>
    cases parent with
    | nil =>
      have positive := List.length_pos_iff.mpr nonroot
      have sizes := congrArg List.length equal
      simp only [List.length_append,List.length_cons,List.length_nil] at sizes
      omega
    | cons first tail =>
      have parts := List.cons.inj equal
      cases parts.1
      obtain ⟨inside,parentEq,relativeEq⟩ := ih parts.2
      exact ⟨inside,congrArg (head::·) parentEq,relativeEq⟩

private theorem last_parent_eq {left right : Path} {first second : Step}
    (equal : left++[first]=right++[second]) : left=right := by
  have lengths : left.length=right.length := by
    have sizes := congrArg List.length equal
    simp only [List.length_append,List.length_singleton] at sizes
    omega
  exact List.append_inj_left equal lengths

/-- For an uncreated incoming edge, its literal parent/boundary endpoint
also has the actual old source preimage. Copy and retained roots are excluded
by uncreatedness, rather than by a hypothesized parent map or isomorphism. -/
theorem StepAt.beta_incidence_source_preimage
    {source target body argument current : LTerm} {site edge oldEdge : Path} {beta alpha : Label}
    {vertex : Vertex target}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site edge oldEdge)
    (lookup : target.subterm edge=some current)
    (notCreated : ¬BetaCreatedIncoming body site edge)
    (endpoint : Source target edge vertex) :
    ∃ oldVertex,Source source oldEdge oldVertex ∧
      BetaVertexPreimage body argument site source target vertex oldVertex := by
  obtain ⟨oldNode,atOldNode,_⟩ := step.beta_preimage_label redex origin lookup notCreated
  let oldPosition : Edge source := ⟨oldEdge,by rw [←LTerm.erase_subterm,atOldNode];rfl⟩
  obtain ⟨oldVertex,oldEndpoint⟩ := source_total source oldPosition
  refine ⟨oldVertex,oldEndpoint,?_⟩
  cases vertex with
  | none =>
    have outside : ¬∃ relative,edge=site++relative := by
      rintro ⟨relative,equal⟩
      have zero : site.length=0 := by
        have sizes := congrArg List.length (equal.symm.trans endpoint)
        simp only [List.length_append,List.length_nil] at sizes
        omega
      have empty : site=[] := List.length_eq_zero_iff.mp zero
      exact notCreated (Or.inl (endpoint.trans empty.symm))
    have same := origin.unique (.context outside)
    have vertexEq : oldVertex=none := Source.unique oldEndpoint (same.trans endpoint)
    subst oldVertex
    exact .boundary
  | some position =>
    obtain ⟨child,nowTerm,port,edgeEq,atParent,departure⟩ := endpoint
    cases oldVertex with
    | none =>
      have nonempty : oldEdge≠[] := by
        intro empty
        rcases origin.coordinates with ⟨same,_⟩ |
          ⟨relative,old,_,atOld,_,_⟩ | ⟨q,relative,old,_,_,atOld,_⟩
        · have sizes := congrArg List.length (edgeEq.symm.trans (same.trans empty))
          simp only [List.length_append,List.length_singleton,List.length_nil] at sizes
          omega
        · have sizes := congrArg List.length (atOld.symm.trans empty)
          simp only [List.length_append,List.length_cons,List.length_nil] at sizes
          omega
        · have sizes := congrArg List.length (atOld.symm.trans empty)
          simp only [List.length_append,List.length_cons,List.length_nil] at sizes
          omega
      exact False.elim (nonempty oldEndpoint)
    | some oldPosition =>
      obtain ⟨oldChild,oldTerm,oldPort,oldEdgeEq,oldAtParent,oldDeparture⟩ := oldEndpoint
      apply BetaVertexPreimage.proper
      rcases origin.coordinates with ⟨same,outside⟩ |
        ⟨relative,old,atCurrent,atOld,_,_⟩ | ⟨q,relative,old,occurs,atCurrent,atOld,_⟩
      · have parentEq := last_parent_eq (edgeEq.symm.trans (same.trans oldEdgeEq))
        have parentOutside : ¬∃ inside,position.val=site++inside := by
          rintro ⟨inside,equal⟩
          apply outside
          exact ⟨inside++[child],by rw [edgeEq,equal,List.append_assoc]⟩
        rw [←parentEq]
        exact .context parentOutside
      · have nonroot : relative≠[] := by
          intro empty
          exact notCreated (Or.inl (by simpa only [empty,List.append_nil] using atCurrent))
        obtain ⟨inside,parentEq,relativeEq⟩ := parent_before_last (edgeEq.symm.trans atCurrent) nonroot
        have oldSplit : oldEdge=((site++[.fn,.body])++inside)++[child] := by
          rw [atOld,relativeEq]
          simp only [List.append_assoc]
        have oldParentEq := last_parent_eq (oldEdgeEq.symm.trans oldSplit)
        have localLookup : body.subterm inside=some oldTerm := by
          have actual := oldAtParent
          rw [oldParentEq] at actual
          simpa only [LTerm.subterm_append,redex,Option.bind_some,LTerm.subterm] using actual
        have nonselected : ∀ stamp,oldTerm≠.var stamp (binderDepth inside) := by
          cases oldDeparture <;> intro stamp impossible <;> cases impossible
        rw [parentEq,oldParentEq]
        exact .retained localLookup nonselected
      · have nonroot : relative≠[] := by
          intro empty
          apply notCreated
          exact betaCreatedIncoming_iff.mpr (Or.inr ⟨q,occurs,by simpa only [empty,List.append_nil] using atCurrent⟩)
        obtain ⟨inside,parentEq,relativeEq⟩ := parent_before_last (edgeEq.symm.trans atCurrent) nonroot
        have oldSplit : oldEdge=((site++[.arg])++inside)++[child] := by
          rw [atOld,relativeEq]
          simp only [List.append_assoc]
        have oldParentEq := last_parent_eq (oldEdgeEq.symm.trans oldSplit)
        have localLookup : argument.subterm inside=some oldTerm := by
          have actual := oldAtParent
          rw [oldParentEq] at actual
          simpa only [LTerm.subterm_append,redex,Option.bind_some,LTerm.subterm] using actual
        rw [parentEq,oldParentEq]
        exact .copied occurs localLookup
end Lamping.Lambda.Labelled

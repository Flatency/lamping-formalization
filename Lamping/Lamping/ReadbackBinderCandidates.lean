import Lamping.Lamping.ReadbackMachine
import Lamping.Lamping.ReadbackCorrectness
import Lamping.Lamping.CopiedLambdaTransparency

namespace Lamping.AG.Readback
open Graph Lambda

theorem portNumber_injective (kind : Kind) : Function.Injective (portNumber kind) := by
  cases kind with
  | garbage => intro p q same; cases p; cases q; rfl
  | op op =>
    cases op <;> intro p q same <;> cases p with
    | inl p => cases p; cases q with
      | inl q => cases q; rfl
      | inr q => cases q <;> cases same
    | inr p => cases q with
      | inl q => cases q; cases p <;> cases same
      | inr q => cases p <;> cases q <;> first | rfl | cases same

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]
variable {g : Net signature N B W}

theorem endpointSame_iff (left right : Endpoint g) :
    endpointSame g left right=true ↔left=right := by
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      obtain ⟨n,p⟩ := left
      obtain ⟨m,q⟩ := right
      simp only [endpointSame,Bool.and_eq_true,decide_eq_true_eq]
      constructor
      · rintro ⟨rfl,same⟩
        have ports := portNumber_injective (g.label n).sort same
        subst q
        rfl
      · intro same
        cases same
        exact ⟨rfl,rfl⟩
    | inr right => cases right <;> simp [endpointSame]
  | inr left =>
    cases right with
    | inl right => cases left <;> simp [endpointSame]
    | inr right => cases left <;> cases right <;> simp [endpointSame,Prod.ext_iff]

private instance runtimeEndpointLawful : LawfulBEq (Endpoint g) where
  eq_of_beq := by intro left right same; exact (endpointSame_iff left right).mp same
  rfl := by intro endpoint; exact (endpointSame_iff endpoint endpoint).mpr rfl

theorem shellEqual_iff (width : Nat) (left right : ContextData) :
    shellEqual width left right=true ↔
      Context.SameShell width (Context.ofList left) (Context.ofList right) := by
  simp only [shellEqual,List.all_eq_true,decide_eq_true_eq,List.mem_range,
    Context.SameShell,ContextData.denote_get]

/-- The executable prefix test is equality of the literal endpoint lists,
including transparent occurrences; no endpoint-only path equivalence is used. -/
theorem runtime_prefix_iff (pre path : List (Endpoint g)) :
    pre.isPrefixOf path=true ↔∃ tail,path=pre++tail := by
  rw [List.isPrefixOf_iff_prefix]
  constructor
  · rintro ⟨tail,same⟩
    exact ⟨tail,same.symm⟩
  · rintro ⟨tail,same⟩
    exact ⟨tail,same.symm⟩

theorem mem_binderCandidates (frames : List (BinderFrame g)) (node : N)
    (path : List (Endpoint g)) (output : ContextData) (k : Nat) :
    k∈binderCandidates g frames node path output ↔
      ∃ frame,(frame,k)∈frames.zipIdx ∧frame.node=node ∧
        Context.SameShell frame.index (Context.ofList frame.seam) (Context.ofList output) ∧
        ∃ tail,path=frame.stem++frame.bodyDeparture::tail := by
  simp only [binderCandidates,List.mem_filterMap]
  constructor
  · rintro ⟨⟨frame,j⟩,member,result⟩
    split at result
    · rename_i accepted
      cases Option.some.inj result
      have facts : frame.node=node ∧shellEqual frame.index frame.seam output=true ∧
          (frame.stem++[frame.bodyDeparture]).isPrefixOf path=true := by
        simpa only [Bool.and_eq_true,decide_eq_true_eq,and_assoc] using accepted
      have shell := (shellEqual_iff _ _ _).mp facts.2.1
      obtain ⟨tail,split⟩ := (runtime_prefix_iff _ _).mp facts.2.2
      exact ⟨frame,member,facts.1,shell,tail,by simpa only [List.append_assoc,List.singleton_append] using split⟩
    · contradiction
  · rintro ⟨frame,member,sameNode,shell,tail,split⟩
    refine ⟨(frame,k),member,?_⟩
    have pre : (frame.stem++[frame.bodyDeparture]).isPrefixOf path=true :=
      (runtime_prefix_iff _ _).mpr ⟨tail,by simpa only [List.append_assoc,List.singleton_append] using split⟩
    have low := (shellEqual_iff _ _ _).mpr shell
    simp [sameNode,low,pre]

private theorem last_append_nonempty {T : Type} (pre tail : List T) (nonempty : tail≠[]) :
    (pre++tail).getLast?=tail.getLast? := by
  rw [List.getLast?_append]
  cases last : tail.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp last))
  | some value => rfl

/-- At one actual recorded lambda occurrence, the runtime shell and literal
prefix checks cut a genuine binding loop from the same whole labelling.
Physical metadata and prefix labels are execution invariants still to be
maintained by the whole machine; no BindingSuffix is an input to this lemma. -/
theorem frame_binding_suffix (frame : BinderFrame g) (path : List (Endpoint g))
    (input output : ContextData) (ctx body bind : Port (g.label frame.node).sort)
    (sort : (g.label frame.node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (bodyRole : HEq body lamBody) (bindRole : HEq bind lamBind)
    (indexEq : frame.index=(g.label frame.node).index)
    (bodyEq : frame.bodyDeparture=.inl ⟨frame.node,body⟩)
    (prefixEnd : frame.stem.getLast?=some (g.wire (.inl ⟨frame.node,ctx⟩)))
    (labels : Labelling g path (Context.ofList input) (Context.ofList output))
    (forward : Forward g path)
    (prefixLabels : Labelling g frame.stem (Context.ofList input) (Context.ofList frame.seam))
    (finish : path.getLast?=some (g.wire (.inl ⟨frame.node,bind⟩)))
    (shell : shellEqual frame.index frame.seam output=true)
    (prefixTest : (frame.stem++[frame.bodyDeparture]).isPrefixOf path=true) :
    ∃ tail,path=frame.stem++frame.bodyDeparture::tail ∧
      BindingSuffix g path (binderDepth (accessWord g (frame.bodyDeparture::tail))) := by
  obtain ⟨tail,split⟩ := (runtime_prefix_iff _ _).mp prefixTest
  have split' : path=frame.stem++frame.bodyDeparture::tail := by
    simpa only [List.append_assoc,List.singleton_append] using split
  have shell' := (shellEqual_iff _ _ _).mp shell
  rw [indexEq] at shell'
  have labelled : Labelling g (frame.stem++(.inl ⟨frame.node,body⟩)::tail)
      (Context.ofList input) (Context.ofList output) := by
    simpa only [split',bodyEq] using labels
  have directed : Forward g (frame.stem++(.inl ⟨frame.node,body⟩)::tail) := by
    simpa only [split',bodyEq] using forward
  have finished : (frame.stem++(.inl ⟨frame.node,body⟩)::tail).getLast?=
      some (g.wire (.inl ⟨frame.node,bind⟩)) := by
    simpa only [split',bodyEq] using finish
  obtain ⟨loop,_binderEq⟩ := ordinary_binding_suffix frame.node ctx body bind sort
    ctxRole bodyRole bindRole frame.stem tail (Context.ofList input)
      (Context.ofList frame.seam) (Context.ofList output)
        labelled directed prefixLabels prefixEnd finished shell'
  let fixedLoop : BindingLoop g ((.inl ⟨frame.node,body⟩)::tail)
      (Context.ofList frame.seam) (Context.ofList output) := {
    binder:=frame.node,isLam:=sort,body:=body,bind:=bind,
    body_role:=bodyRole,bind_role:=bindRole,start:=rfl,
    finish:=(last_append_nonempty frame.stem
      ((.inl ⟨frame.node,body⟩ : Endpoint g)::tail) (by simp)).symm.trans finished,
    proper:=loop.proper,forward:=loop.forward,shell:=shell' }
  refine ⟨tail,split',?_⟩
  rw [bodyEq]
  exact ⟨frame.stem,(.inl ⟨frame.node,body⟩)::tail,Context.ofList input,
    Context.ofList frame.seam,Context.ofList output,fixedLoop,ctx,
    by simpa only [bodyEq] using split',ctxRole,prefixEnd,prefixLabels,rfl⟩

end
end Lamping.AG.Readback

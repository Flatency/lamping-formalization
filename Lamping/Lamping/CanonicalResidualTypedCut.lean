import Lamping.Lamping.CancellationCanonicalResidual

namespace Lamping.AG
open Graph
section
variable {K B F W N D V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames F]
  [FiniteNames W] [FiniteNames N] [FiniteNames D] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature Empty F Empty)
variable (g : Net signature N D V) (embed : Endpoint c → Endpoint g)
variable (fronts : F → List (Endpoint g))

private theorem typed_nonempty {xs : List (Endpoint g)}
    (typed : ∃ k,accessKind g xs=some k) : xs≠[] := by
  intro empty
  obtain ⟨k,kind⟩ := typed
  rw [empty] at kind
  cases kind

/-- A proper terminal cut cannot lie in a frontier whose every segment is
untyped. The actual remainder of the prefix is constructed by list recursion. -/
private theorem cut_untyped_front {front rest pre post : List (Endpoint g)}
    (untyped : ∀ e∈front,accessKind g [e]=none)
    (split : front++rest=pre++post) (typed : ∃ k,accessKind g pre=some k) :
    ∃ middle,pre=front++middle ∧rest=middle++post ∧∃ k,accessKind g middle=some k := by
  induction front generalizing pre with
  | nil => exact ⟨pre,rfl,split,typed⟩
  | cons e front ih =>
    cases pre with
    | nil => exact False.elim (typed_nonempty g typed rfl)
    | cons x pre =>
      obtain ⟨headEqual,tailEqual⟩ := List.cons.inj split
      subst x
      cases pre with
      | nil =>
        obtain ⟨k,kind⟩ := typed
        rw [untyped e (by simp)] at kind
        cases kind
      | cons next pre =>
        have tailTyped : ∃ k,accessKind g (next::pre)=some k := by
          simpa only [accessKind,List.getLast?_cons_cons] using typed
        obtain ⟨middle,first,second,kind⟩ := ih
          (fun x member=>untyped x (List.mem_cons_of_mem _ member)) tailEqual tailTyped
        exact ⟨middle,congrArg (e::·) first,second,kind⟩

private theorem CanonicalWireResidual.raw_nonempty
    (relation : CanonicalWireResidual c r g embed fronts raw old) : raw≠[] := by
  cases relation <;> simp

private theorem CanonicalWireResidual.prefix_shape
    (relation : CanonicalWireResidual c r g embed fronts pre old)
    (split : Sum.inl e::tail=pre++post) : ∃ rest,pre=Sum.inl e::rest := by
  have nonempty := relation.raw_nonempty c r g embed fronts
  have same := congrArg List.head? split
  rw [List.head?_append] at same
  cases head : pre.head? with
  | none => exact False.elim (nonempty (List.head?_eq_none_iff.mp head))
  | some first =>
    have equal : Sum.inl e=first := by
      simp only [List.head?_cons,head,Option.some_or] at same
      exact Option.some.inj same
    subst first
    exact List.head?_eq_some_iff.mp head

/-- Split at a real typed old prefix. The split is literal and has no
shared endpoint; both canonical sub-relations are conclusions. -/
theorem CanonicalWireResidual.split_at_typed_prefix
    (frontUntyped : ∀ f e,e∈fronts f →accessKind g [e]=none)
    (relation : CanonicalWireResidual c r g embed fronts raw old)
    {pre post : List (Endpoint g)} (split : old=pre++post)
    (typed : ∃ k,accessKind g pre=some k) (postNonempty : post≠[]) :
    ∃ rawPre rawPost,raw=rawPre++rawPost ∧
      CanonicalWireResidual c r g embed fronts rawPre pre ∧
      CanonicalWireResidual c r g embed fronts rawPost post := by
  induction relation generalizing pre post with
  | single e =>
    have preNonempty := typed_nonempty g typed
    have size := congrArg List.length split
    have before := List.length_pos_iff.mpr preNonempty
    have after := List.length_pos_iff.mpr postNonempty
    simp only [List.length_singleton,List.length_append] at size
    omega
  | @outside e f tail old rest ih =>
    cases pre with
    | nil => exact False.elim (typed_nonempty g typed rfl)
    | cons x pre =>
      obtain ⟨headEqual,tailEqual⟩ := List.cons.inj split
      subst x
      cases pre with
      | nil =>
        have equal : old=post := by simpa only [List.nil_append] using tailEqual
        refine ⟨[.inl e],.inl f::tail,rfl,.single e,?_⟩
        rw [←equal]
        exact rest
      | cons next pre =>
        have tailTyped : ∃ k,accessKind g (next::pre)=some k := by
          simpa only [accessKind,List.getLast?_cons_cons] using typed
        obtain ⟨rawPre,rawPost,rawSplit,first,second⟩ := ih tailEqual tailTyped postNonempty
        obtain ⟨rawTail,shape⟩ := first.prefix_shape c r g embed fronts rawSplit
        rw [shape] at rawSplit first
        exact ⟨.inl e::.inl f::rawTail,rawPost,by simpa only [List.cons_append] using congrArg (Sum.inl e::·) rawSplit,
          .outside first,second⟩
  | @through e f tail old start rest ih =>
    obtain ⟨middle,preSplit,oldSplit,middleTyped⟩ := cut_untyped_front g (frontUntyped f) split typed
    obtain ⟨rawPre,rawPost,rawSplit,first,second⟩ := ih oldSplit middleTyped postNonempty
    obtain ⟨rawTail,shape⟩ := first.prefix_shape c r g embed fronts rawSplit
    rw [shape] at rawSplit first
    refine ⟨.inl e::.inr (.inr (.inl f))::.inl (.inr (.inl (.inr (wireBoundaryMate r f))))::rawTail,
      rawPost,?_,?_,second⟩
    · simpa only [List.cons_append] using congrArg (fun suffix=>Sum.inl e::Sum.inr (.inr (.inl f))::suffix) rawSplit
    · rw [preSplit]
      exact .through start first
end
end Lamping.AG

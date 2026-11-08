import Lamping.Lamping.PlugPathDecomposition
namespace Lamping.AG
open Graph
section
variable {K B F W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames F] [FiniteNames W]
variable (c : Net signature K (B⊕F) W) (r : Net signature Empty F Empty)

def wireBoundaryMate (f : F) : F :=
  match r.wire (.inr (.inl f)) with
  | .inl ⟨node,_⟩ => nomatch node
  | .inr (.inl mate) => mate
  | .inr (.inr (w,_)) => nomatch w

theorem wireBoundaryMate_spec (f : F) : r.wire (.inr (.inl f))=.inr (.inl (wireBoundaryMate r f)) := by
  unfold wireBoundaryMate
  cases result : r.wire (.inr (.inl f)) with
  | inl node => exact nomatch node.1
  | inr endpoint =>
    cases endpoint with
    | inl mate => rfl
    | inr vertex => exact nomatch vertex.1

private theorem no_wire_turn {x y : Endpoint r} (turn : LabelledTurn r x y a b) : False := by
  cases turn with
  | node node => exact nomatch node
  | transparent vertex => exact nomatch vertex

private theorem from_left {x : Endpoint c} {y : PlugSegment c r}
    (turn : PlugTurn c r (.inl x) y a b) :
    (∃ z,y=.inl z ∧LabelledTurn c x z a b) ∨
      (∃ f,x=.inr (.inl (.inr f)) ∧y=.inr (.inr (.inl f)) ∧a=b) := by
  cases turn with
  | left turn => exact Or.inl ⟨_,rfl,turn⟩
  | enter f a => exact Or.inr ⟨f,rfl,rfl,rfl⟩

private theorem from_right {x : Endpoint r} {y : PlugSegment c r}
    (turn : PlugTurn c r (.inr x) y a b) :
    ∃ f,x=.inr (.inl f) ∧y=.inl (.inr (.inl (.inr f))) ∧a=b := by
  cases turn with
  | right turn => exact False.elim (no_wire_turn r turn)
  | leave f a => exact ⟨f,rfl,rfl,rfl⟩

/-- Complete left-ended paths in a wire-only RHS plug consist exactly of
ordinary outside turns and two-turn excursions. Each constructor retains
every original raw directed segment, including both glue-frontier sides. -/
inductive WireExcursions : List (PlugSegment c r) → Context → Context → Prop where
  | single (e : Endpoint c) (a : Context) : WireExcursions [.inl e] a a
  | outside {e f : Endpoint c} {tail : List (PlugSegment c r)} {a b d : Context}
      (turn : LabelledTurn c (c.wire e) f a b) (rest : WireExcursions (.inl f::tail) b d) :
      WireExcursions (.inl e::.inl f::tail) a d
  | through {e : Endpoint c} {f : F} {tail : List (PlugSegment c r)} {a b : Context}
      (arrival : c.wire e=.inr (.inl (.inr f)))
      (rest : WireExcursions (.inl (.inr (.inl (.inr (wireBoundaryMate r f))))::tail) a b) :
      WireExcursions (.inl e::.inr (.inr (.inl f))::.inl (.inr (.inl (.inr (wireBoundaryMate r f))))::tail) a b

theorem WireExcursions.labelling {es : List (PlugSegment c r)} (path : WireExcursions c r es a b) :
    PlugLabelling c r es a b := by
  induction path with
  | single e a => exact .single _ _
  | outside turn rest ih => exact .cons (.left turn) ih
  | @through e f tail a b arrival rest ih =>
    apply PlugLabelling.cons
    · change PlugTurn c r (.inl (c.wire e)) (.inr (.inr (.inl f))) a a
      rw [arrival]
      exact .enter f a
    · apply PlugLabelling.cons
      · change PlugTurn c r (.inr (r.wire (.inr (.inl f)))) (.inl (.inr (.inl (.inr (wireBoundaryMate r f))))) a a
        rw [wireBoundaryMate_spec]
        exact .leave _ a
      · exact ih

private theorem complete {es : List (PlugSegment c r)} (labels : PlugLabelling c r es a b)
    (first last : Endpoint c) (head : es.head?=some (.inl first)) (finish : es.getLast?=some (.inl last)) :
    WireExcursions c r es a b := by
  cases labels with
  | single e a =>
    have same : e=.inl first := Option.some.inj head
    subst e
    exact .single _ _
  | @cons e next tail a middle b turn after =>
    have same : e=.inl first := Option.some.inj head
    subst e
    rcases from_left c r turn with ⟨nextLeft,same,localTurn⟩ | ⟨f,arrival,nextEq,contexts⟩
    · subst next
      apply WireExcursions.outside localTurn
      exact complete after nextLeft last rfl (by simpa only [List.getLast?_cons_cons] using finish)
    · subst next
      subst contexts
      cases after with
      | single => cases finish
      | @cons next second tail a middle b turn after =>
        change PlugTurn c r (.inr (r.wire (.inr (.inl f)))) second _ _ at turn
        obtain ⟨mate,same,nextEq,contexts⟩ := from_right c r turn
        have mateEq : mate=wireBoundaryMate r f := by
          rw [wireBoundaryMate_spec] at same
          exact (Sum.inl.inj (Sum.inr.inj same)).symm
        subst mate
        subst second
        subst contexts
        apply WireExcursions.through arrival
        exact complete after _ last rfl (by simpa only [List.getLast?_cons_cons] using finish)
termination_by es.length
decreasing_by all_goals simp_wf; simp_all only [List.length_cons]; omega

theorem PlugLabelling.wire_excursions {es : List (PlugSegment c r)} (labels : PlugLabelling c r es a b)
    (first last : Endpoint c) (head : es.head?=some (.inl first)) (finish : es.getLast?=some (.inl last)) :
    WireExcursions c r es a b := complete c r labels first last head finish

/-- Direct whole physical-path interface. Both supplied ends are actual
outside segment occurrences; no maximality or distinctness is required. -/
theorem Labelling.wire_excursions {es : List (Endpoint (plug c r))}
    (labels : Labelling (plug c r) es a b) (first last : Endpoint c)
    (head : es.head?=some (AG.plugLeft c r first)) (finish : es.getLast?=some (AG.plugLeft c r last)) :
    WireExcursions c r (es.map (plugEnd c.label r.label).invFun) a b := by
  apply (labels.plug_decomposition c r).wire_excursions c r first last
  · rw [List.head?_map,head]
    exact congrArg some ((plugEnd c.label r.label).left_inv (.inl first))
  · rw [List.getLast?_map,finish]
    exact congrArg some ((plugEnd c.label r.label).left_inv (.inl last))

end
end Lamping.AG

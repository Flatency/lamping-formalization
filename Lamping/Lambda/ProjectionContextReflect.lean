import Lamping.Lambda.ExtractionContextLift
import Lamping.Lambda.StepProjectionHead
namespace Lamping.Lambda
namespace SyntaxContext

theorem plug_injective (C : SyntaxContext) : Function.Injective C.plug := by
  induction C with
  | hole => exact fun _ _ eq => eq
  | frame outer inner ih => exact fun _ _ eq => ih (outer.plug_injective eq)

theorem selection_injective (C : SyntaxContext) : Function.Injective C.selection := by
  intro F G equal
  have projected := congrArg (List.map (List.drop C.path.length)) equal
  simpa only [C.selection_eq_map,List.map_map,Function.comp_def,List.drop_left,List.map_id_fun'] using projected

theorem liftStep_residualSet (C : SyntaxContext) (h : ParallelStep F t u) (names : List Path) :
    (C.liftStep h).residualSet (C.selection names)=C.selection (h.residualSet names) := by
  rw [C.selection_eq_map names,C.selection_eq_map (h.residualSet names)]
  exact h.residualSet_prefix_eq (C.liftStep h) (C.lookup t) (C.liftStep_paths h) names

theorem liftHistory_cons (C : SyntaxContext) (h : ParallelStep F t u) (tail : ParallelHistory u v) :
    C.liftHistory (.cons h tail)=.cons (C.liftStep h) (C.liftHistory tail) := by
  induction C with
  | hole => rfl
  | frame outer inner ih => simp only [liftHistory,liftStep,ih,SyntaxFrame.liftHistory]

theorem liftHistory_nil (C : SyntaxContext) (t : Term) :
    C.liftHistory (.nil t)=.nil (C.plug t) := by
  induction C with
  | hole => rfl
  | frame outer inner ih => simp only [liftHistory,plug,ih,SyntaxFrame.liftHistory]

private theorem step_heq_paths (H : ParallelStep F t u) (K : ParallelStep F t v)
    (paths : H.paths=K.paths) : u=v ∧ HEq H K := by
  have valid := K.derivation.valid
  change BetaHistory K.paths t v at valid
  rw [←paths] at valid
  have endpoint := H.derivation.valid.deterministic valid
  cases endpoint
  have equal : H=K := H.ext_data K paths (Marked.complete_unique
    ⟨((Marked.completeOld_iff _ _).mp H.complete).1.steps,
      ((Marked.completeOld_iff _ _).mp H.complete).2⟩
    ⟨((Marked.completeOld_iff _ _).mp K.complete).1.steps,
      ((Marked.completeOld_iff _ _).mp K.complete).2⟩)
  exact ⟨rfl,heq_of_eq equal⟩

/-- Reflect a complete development with context-prefixed selection names.
The full outside context and chosen marked development are recovered. -/
theorem reflectStep (C : SyntaxContext)
    (H : ParallelStep (C.selection F) (C.plug a) U) :
    ∃ b, ∃ h : ParallelStep F a b,
      U=C.plug b ∧ HEq H (C.liftStep h) ∧
      H.paths=h.paths.map (fun q => C.path++q) := by
  let narrowed := H.reindex (F.map (fun q => C.path++q))
    (fun q => by rw [C.selection_eq_map])
  obtain ⟨b,h,_,paths⟩ := narrowed.prefix_scope (C.lookup a)
  have actualPaths : H.paths=h.paths.map (fun q => C.path++q) := paths
  obtain ⟨endpoint,equal⟩ := step_heq_paths H (C.liftStep h)
    (actualPaths.trans (C.liftStep_paths h).symm)
  exact ⟨b,h,endpoint,equal,actualPaths⟩

theorem reflectStep_fixed (C : SyntaxContext)
    (H : ParallelStep (C.selection F) (C.plug a) (C.plug b)) :
    ∃ h : ParallelStep F a b, H=C.liftStep h := by
  obtain ⟨c,h,endpoint,equal,_⟩ := C.reflectStep H
  have same : b=c := C.plug_injective endpoint
  cases same
  exact ⟨h,eq_of_heq equal⟩

/-- An actual ordinary schedule confined to the hole is exactly a lifted
ordinary history; endpoint equality follows from its real beta schedule. -/
theorem reflectHistory (C : SyntaxContext) (H : ParallelHistory (C.plug a) U)
    (ordinary : Atomic H) (inside : Internal C.path H) :
    ∃ b, ∃ h : ParallelHistory a b, Atomic h ∧ U=C.plug b ∧
      HEq H (C.liftHistory h) ∧
      H.derivation.paths=h.derivation.paths.map (fun q => C.path++q) := by
  obtain ⟨ps,b,paths,program,_⟩ := inside.extract (C.lookup a)
  obtain ⟨h,atomic,localPaths⟩ := program.atomic
  have actualPaths : H.derivation.paths=h.derivation.paths.map (fun q => C.path++q) := by
    rw [localPaths]
    exact paths
  have liftedPaths : H.derivation.paths=(C.liftHistory h).derivation.paths :=
    actualPaths.trans (C.liftHistory_paths h).symm
  have valid := (C.liftHistory h).derivation.valid
  rw [←liftedPaths] at valid
  have endpoint := H.derivation.valid.deterministic valid
  cases endpoint
  have equal : H=C.liftHistory h := ordinary.paths_injective (C.liftAtomic atomic) liftedPaths
  exact ⟨b,h,atomic,rfl,heq_of_eq equal,actualPaths⟩

theorem reflectHistory_fixed (C : SyntaxContext) (H : ParallelHistory (C.plug a) (C.plug b))
    (ordinary : Atomic H) (inside : Internal C.path H) :
    ∃ h : ParallelHistory a b, Atomic h ∧ H=C.liftHistory h := by
  obtain ⟨c,h,atomic,endpoint,equal,_⟩ := C.reflectHistory H ordinary inside
  have same : b=c := C.plug_injective endpoint
  cases same
  exact ⟨h,atomic,eq_of_heq equal⟩

private theorem nil_row_data {h : ParallelStep F t u} {k : ParallelStep G t u}
    (row : StepProjection h (.nil t) (.nil u) k) : F=G ∧ HEq h k := by
  cases row
  exact ⟨rfl,HEq.rfl⟩

private theorem head_selection {first : ParallelStep F t u} {top : ParallelStep H t v}
    {bottom : ParallelStep K u w} {rest : ParallelHistory v x} {rest' : ParallelHistory w y}
    {last : ParallelStep L x y}
    (row : StepProjection first (.cons top rest) (.cons bottom rest') last) :
    first.residualSet H=K := by
  cases row
  rfl

private theorem reindex_heq (h : ParallelStep F t u) (eq : F=G)
    (members : ∀ p,p∈F ↔ p∈G) : HEq h (h.reindex G members) := by
  cases eq
  rfl

private theorem replace_first {h : ParallelStep F t u} {k : ParallelStep G t u}
    (eq : F=G) (he : HEq h k) (row : StepProjection h σ τ last) : StepProjection k σ τ last := by
  cases eq
  cases eq_of_heq he
  exact row

private theorem cons_heq {h : ParallelStep F t u} {k : ParallelStep G t u}
    (eq : F=G) (he : HEq h k) (tail : ParallelHistory u v) :
    ParallelHistory.cons h tail=ParallelHistory.cons k tail := by
  cases eq
  cases eq_of_heq he
  rfl

/-- Reflect an actual row whose two horizontal ordinary histories and
vertical complete developments are the specified context lifts. -/
theorem reflectProjection (C : SyntaxContext) {h : ParallelStep F t u}
    {σ : ParallelHistory t v} {τ : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection (C.liftStep h) (C.liftHistory σ) (C.liftHistory τ) (C.liftStep last))
    (ordinary : Atomic σ) (projectedOrdinary : Atomic τ) : StepProjection h σ τ last := by
  induction ordinary generalizing F u w G with
  | nil t =>
    cases projectedOrdinary with
    | cons B rest =>
      have lengths := row.length
      rw [C.liftHistory_length,C.liftHistory_length] at lengths
      change 1+_=0 at lengths
      omega
    | nil =>
      rw [C.liftHistory_nil,C.liftHistory_nil] at row
      have data := nil_row_data row
      have same : F=G := C.selection_injective data.1
      cases same
      have mapped := congrArg ParallelStep.paths (eq_of_heq data.2)
      rw [C.liftStep_paths,C.liftStep_paths] at mapped
      have paths : h.paths=last.paths := by
        have dropped := congrArg (List.map (List.drop C.path.length)) mapped
        simpa only [List.map_map,Function.comp_def,List.drop_left,List.map_id_fun'] using dropped
      have equal : h=last := eq_of_heq (step_heq_paths h last paths).2
      cases equal
      exact .nil h
  | @cons t p a v tail S tailAtomic ih =>
    cases projectedOrdinary with
    | nil =>
      have lengths := row.length
      rw [C.liftHistory_length,C.liftHistory_length] at lengths
      change 0=1+_ at lengths
      omega
    | @cons u q b w bottom B bottomAtomic =>
      rw [C.liftHistory_cons,C.liftHistory_cons] at row
      have selection := head_selection row
      have localSelection : h.residualSet [p]=[q] := by
        apply C.selection_injective
        rw [←C.liftStep_residualSet h [p]]
        exact selection
      obtain ⟨sq,first,top,_,_,remaining⟩ := row.head_square
      cases sq with
      | mk firstStep topStep side vertical =>
        cases first
        cases top
        have verticalNames := C.liftStep_residualSet (singleContraction S) F
        let indexed := vertical.reindex (C.selection ((singleContraction S).residualSet F))
          (fun r => by rw [verticalNames])
        obtain ⟨localVertical,equal⟩ := C.reflectStep_fixed indexed
        have verticalHeq : HEq vertical (C.liftStep localVertical) := by
          have same := reindex_heq vertical verticalNames (fun r => by rw [verticalNames])
          change HEq vertical indexed at same
          rw [equal] at same
          exact same
        have tailGlobal := replace_first verticalNames verticalHeq remaining
        have tailLocal := ih tailGlobal bottomAtomic
        let localSide := (singleContraction B).reindex (h.residualSet [p])
          (fun r => by rw [localSelection])
        have localRow : StepProjection h (.cons (singleContraction S) tail)
            (.cons localSide bottom) last :=
          .cons ⟨h,singleContraction S,localSide,localVertical⟩ tailLocal
        have same := (reindex_heq (singleContraction B) localSelection.symm
          (fun r => by rw [localSelection])).symm
        rw [cons_heq localSelection same] at localRow
        exact localRow

/-- Recover all four local sides from an actual global row confined to the
hole. Neither a local row nor an outside-context identity is an input. -/
theorem reflectScopedProjection (C : SyntaxContext)
    {H : ParallelStep (C.selection F) (C.plug t) U}
    {top : ParallelHistory (C.plug t) V} {bottom : ParallelHistory U W}
    {L : ParallelStep (C.selection G) V W}
    (row : StepProjection H top bottom L) (ha : Atomic top) (hb : Atomic bottom)
    (hi : Internal C.path top) (hj : Internal C.path bottom) :
    ∃ u v w, ∃ h : ParallelStep F t u, ∃ σ : ParallelHistory t v,
      ∃ τ : ParallelHistory u w, ∃ last : ParallelStep G v w,
      Atomic σ ∧ Atomic τ ∧ StepProjection h σ τ last ∧
      U=C.plug u ∧ V=C.plug v ∧ W=C.plug w ∧
      HEq H (C.liftStep h) ∧ HEq top (C.liftHistory σ) ∧
      HEq bottom (C.liftHistory τ) ∧ HEq L (C.liftStep last) := by
  obtain ⟨u,h,ueq,heq,_⟩ := C.reflectStep H
  cases ueq
  obtain ⟨v,σ,atomicTop,veq,topEq,_⟩ := C.reflectHistory top ha hi
  cases veq
  obtain ⟨w,τ,atomicBottom,weq,bottomEq,_⟩ := C.reflectHistory bottom hb hj
  cases weq
  obtain ⟨last,lastEq⟩ := C.reflectStep_fixed L
  have global := row
  rw [eq_of_heq heq,eq_of_heq topEq,eq_of_heq bottomEq,lastEq] at global
  exact ⟨u,v,w,h,σ,τ,last,atomicTop,atomicBottom,
    C.reflectProjection global atomicTop atomicBottom,rfl,rfl,rfl,heq,topEq,bottomEq,
    heq_of_eq lastEq⟩

end SyntaxContext
end Lamping.Lambda

import Lamping.Lambda.ParallelPrefixResidualSet
import Lamping.Lambda.DerivationProjection
import Lamping.Lambda.AtomicProjection
namespace Lamping.Lambda
namespace SyntaxFrame

noncomputable def liftStep (C : SyntaxFrame) (h : ParallelStep F t u) :
    ParallelStep (F.map (C.edge::·)) (C.plug t) (C.plug u) :=
  Classical.choose (C.parallel_lift h)

theorem liftStep_paths (C : SyntaxFrame) (h : ParallelStep F t u) :
    (C.liftStep h).paths=h.paths.map (C.edge::·) :=
  Classical.choose_spec (C.parallel_lift h)

theorem liftStep_residualSet (C : SyntaxFrame) (h : ParallelStep F t u) (names : List Path) :
    (C.liftStep h).residualSet (names.map (C.edge::·))=
      (h.residualSet names).map (C.edge::·) := by
  simpa only [List.singleton_append] using h.residualSet_prefix_eq (C.liftStep h)
    (C.lookup t) (by simpa only [List.singleton_append] using C.liftStep_paths h) names

noncomputable def liftHistory (C : SyntaxFrame) : ParallelHistory t u →
    ParallelHistory (C.plug t) (C.plug u)
  | .nil _ => .nil _
  | .cons h tail => .cons (C.liftStep h) (C.liftHistory tail)

theorem liftHistory_paths (C : SyntaxFrame) (h : ParallelHistory t u) :
    (C.liftHistory h).derivation.paths=h.derivation.paths.map (C.edge::·) := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    change (C.liftStep head).paths++_=(head.paths++_).map (C.edge::·)
    rw [C.liftStep_paths,ih,List.map_append]

noncomputable def liftSquare (C : SyntaxFrame) (sq : ParallelMovesSquare F G t u v w) :
    ParallelMovesSquare (F.map (C.edge::·)) (G.map (C.edge::·))
      (C.plug t) (C.plug u) (C.plug v) (C.plug w) where
  first := C.liftStep sq.first
  second := C.liftStep sq.second
  afterFirst := by
    rw [C.liftStep_residualSet]
    exact C.liftStep sq.afterFirst
  afterSecond := by
    rw [C.liftStep_residualSet]
    exact C.liftStep sq.afterSecond

private theorem liftSquare_afterFirst_heq (C : SyntaxFrame)
    (sq : ParallelMovesSquare F G t u v w) :
    HEq (C.liftSquare sq).afterFirst (C.liftStep sq.afterFirst) := by
  unfold liftSquare
  simp

private theorem liftSquare_afterSecond_heq (C : SyntaxFrame)
    (sq : ParallelMovesSquare F G t u v w) :
    HEq (C.liftSquare sq).afterSecond (C.liftStep sq.afterSecond) := by
  unfold liftSquare
  simp

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

theorem liftProjection (C : SyntaxFrame) (row : StepProjection h σ τ last) :
    StepProjection (C.liftStep h) (C.liftHistory σ) (C.liftHistory τ) (C.liftStep last) := by
  induction row with
  | nil h => exact .nil _
  | cons sq tail ih =>
    have ih' := replace_first (C.liftStep_residualSet sq.second _).symm
      (C.liftSquare_afterSecond_heq sq).symm ih
    have result := StepProjection.cons (C.liftSquare sq) ih'
    rw [cons_heq (C.liftStep_residualSet sq.first _)
      (C.liftSquare_afterFirst_heq sq)] at result
    exact result

theorem liftAtomic (C : SyntaxFrame) (ordinary : Atomic σ) : Atomic (C.liftHistory σ) := by
  induction ordinary with
  | nil => exact .nil _
  | cons head rest ih =>
    obtain ⟨global,he⟩ := (C.liftStep (singleContraction head)).eq_single_contraction
      (C.redex_lift ⟨_,head.redex⟩) rfl
    change Atomic (.cons (C.liftStep (singleContraction head)) _)
    rw [he]
    exact .cons global ih

end SyntaxFrame

/-- A concrete syntax context retains every sibling term and binder. -/
inductive SyntaxContext where
  | hole
  | frame (outer : SyntaxFrame) (inner : SyntaxContext)

namespace SyntaxContext
def path : SyntaxContext → Path
  | .hole => []
  | .frame C D => C.edge::D.path
def plug : SyntaxContext → Term → Term
  | .hole,t => t
  | .frame C D,t => C.plug (D.plug t)
def selection : SyntaxContext → List Path → List Path
  | .hole,F => F
  | .frame C D,F => (D.selection F).map (C.edge::·)

theorem selection_eq_map (C : SyntaxContext) (F : List Path) :
    C.selection F=F.map (fun q => C.path++q) := by
  induction C with
  | hole => simp [selection,path]
  | frame outer inner ih => simp only [selection,path,ih,List.map_map,Function.comp_def,List.cons_append]

theorem lookup (C : SyntaxContext) (t : Term) : subtermAt (C.plug t) C.path=some t := by
  induction C with
  | hole => cases t <;> rfl
  | frame outer inner ih =>
    change subtermAt (outer.plug (inner.plug t)) ([outer.edge]++inner.path)=some t
    rw [subtermAt_append,outer.lookup,Option.bind_some,ih]

theorem of_lookup (hp : subtermAt t pre=some a) :
    ∃ C : SyntaxContext, C.path=pre ∧ C.plug a=t := by
  induction pre generalizing t with
  | nil => simp only [subtermAt,Option.some.injEq] at hp; exact ⟨.hole,rfl,hp.symm⟩
  | cons e pre ih =>
    have frame (C : SyntaxFrame) (b : Term)
        (hp : subtermAt (C.plug b) (C.edge::pre)=some a) :
        ∃ D : SyntaxContext, D.path=C.edge::pre ∧ D.plug a=C.plug b := by
      have localLookup : subtermAt b pre=some a := by
        change subtermAt (C.plug b) ([C.edge]++pre)=some a at hp
        simpa only [subtermAt_append,C.lookup,Option.bind_some] using hp
      obtain ⟨D,dp,dt⟩ := ih localLookup
      exact ⟨.frame C D,by simp only [path,dp],by simp only [plug,dt]⟩
    cases t with
    | var i => cases e <;> simp [subtermAt] at hp
    | lam b => cases e with
      | body => exact frame .body b hp
      | fn => simp [subtermAt] at hp
      | arg => simp [subtermAt] at hp
    | app f b => cases e with
      | fn => exact frame (.fn b) f hp
      | arg => exact frame (.arg f) b hp
      | body => simp [subtermAt] at hp

noncomputable def liftStep : (C : SyntaxContext) → ParallelStep F t u →
    ParallelStep (C.selection F) (C.plug t) (C.plug u)
  | .hole,h => h
  | .frame C D,h => C.liftStep (D.liftStep h)
noncomputable def liftHistory : (C : SyntaxContext) → ParallelHistory t u →
    ParallelHistory (C.plug t) (C.plug u)
  | .hole,h => h
  | .frame C D,h => C.liftHistory (D.liftHistory h)

theorem liftStep_paths (C : SyntaxContext) (h : ParallelStep F t u) :
    (C.liftStep h).paths=h.paths.map (fun q => C.path++q) := by
  induction C with
  | hole => simp [liftStep,path]
  | frame outer inner ih =>
    simp only [liftStep,outer.liftStep_paths,ih,path,List.map_map,Function.comp_def,List.cons_append]

theorem liftHistory_paths (C : SyntaxContext) (h : ParallelHistory t u) :
    (C.liftHistory h).derivation.paths=h.derivation.paths.map (fun q => C.path++q) := by
  induction C with
  | hole => simp [liftHistory,path]
  | frame outer inner ih =>
    simp only [liftHistory,outer.liftHistory_paths,ih,path,List.map_map,Function.comp_def,List.cons_append]

theorem liftProjection (C : SyntaxContext) (row : StepProjection h σ τ last) :
    StepProjection (C.liftStep h) (C.liftHistory σ) (C.liftHistory τ) (C.liftStep last) := by
  induction C with
  | hole => exact row
  | frame outer inner ih => exact outer.liftProjection ih

theorem liftAtomic (C : SyntaxContext) (ordinary : Atomic σ) : Atomic (C.liftHistory σ) := by
  induction C with
  | hole => exact ordinary
  | frame outer inner ih => exact outer.liftAtomic ih

end SyntaxContext

/-- Lift all four chosen sides of an actual tile row through one fixed
context. The construction retains the entire outside term, not only a lookup. -/
theorem StepProjection.prefix_lift {h : ParallelStep F t u}
    {σ : ParallelHistory t v} {τ : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection h σ τ last) (hp : subtermAt T pre=some t) :
    ∃ U V W, ∃ H : ParallelStep (F.map (fun q => pre++q)) T U,
      ∃ globalTop : ParallelHistory T V, ∃ globalBottom : ParallelHistory U W,
      ∃ L : ParallelStep (G.map (fun q => pre++q)) V W,
      StepProjection H globalTop globalBottom L ∧
      subtermAt U pre=some u ∧ subtermAt V pre=some v ∧ subtermAt W pre=some w ∧
      H.paths=h.paths.map (fun q => pre++q) ∧
      globalTop.derivation.paths=σ.derivation.paths.map (fun q => pre++q) ∧
      globalBottom.derivation.paths=τ.derivation.paths.map (fun q => pre++q) ∧
      L.paths=last.paths.map (fun q => pre++q) ∧
      (Atomic σ → Atomic globalTop) ∧ (Atomic τ → Atomic globalBottom) := by
  obtain ⟨C,cp,ct⟩ := SyntaxContext.of_lookup hp
  have package : ∃ U V W, ∃ H : ParallelStep (C.selection F) (C.plug t) U,
      ∃ globalTop : ParallelHistory (C.plug t) V, ∃ globalBottom : ParallelHistory U W,
      ∃ L : ParallelStep (C.selection G) V W,
      StepProjection H globalTop globalBottom L ∧
      subtermAt U C.path=some u ∧ subtermAt V C.path=some v ∧ subtermAt W C.path=some w ∧
      H.paths=h.paths.map (fun q => C.path++q) ∧
      globalTop.derivation.paths=σ.derivation.paths.map (fun q => C.path++q) ∧
      globalBottom.derivation.paths=τ.derivation.paths.map (fun q => C.path++q) ∧
      L.paths=last.paths.map (fun q => C.path++q) ∧
      (Atomic σ → Atomic globalTop) ∧ (Atomic τ → Atomic globalBottom) :=
    ⟨C.plug u,C.plug v,C.plug w,C.liftStep h,C.liftHistory σ,C.liftHistory τ,C.liftStep last,
      C.liftProjection row,C.lookup u,C.lookup v,C.lookup w,C.liftStep_paths h,
      C.liftHistory_paths σ,C.liftHistory_paths τ,C.liftStep_paths last,
      C.liftAtomic,C.liftAtomic⟩
  rw [←ct,←cp,←C.selection_eq_map F,←C.selection_eq_map G]
  exact package

end Lamping.Lambda

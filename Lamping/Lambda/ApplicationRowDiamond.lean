import Lamping.Lambda.ApplicationDiamond
import Lamping.Lambda.TagProjection
import Lamping.Lambda.DerivationProjection
namespace Lamping.Lambda.Marked

/-- Set activity by current physical positions while preserving arbitrary
application identities. Unlike old-name reselection this also handles names
unrelated to current positions. -/
def selectPositionsAt (F : List Path) : Marked → Path → Marked
  | .var i,_ => .var i
  | .lam b,p => .lam (selectPositionsAt F b (p++[.body]))
  | .app l (.lam b) a,p | .red l b a,p =>
      if p∈F then .red l (selectPositionsAt F b ((p++[.fn])++[.body])) (selectPositionsAt F a (p++[.arg]))
      else .app l (.lam (selectPositionsAt F b ((p++[.fn])++[.body]))) (selectPositionsAt F a (p++[.arg]))
  | .app l f a,p => .app l (selectPositionsAt F f (p++[.fn])) (selectPositionsAt F a (p++[.arg]))

theorem selectPositionsAt_skeleton (F : List Path) (t : Marked) (p : Path) :
    (selectPositionsAt F t p).skeleton=(markAt F t.erase p).skeleton := by
  induction t generalizing p with
  | var => rfl
  | lam b ih => simp only [selectPositionsAt,markAt,erase,skeleton,ih]
  | red l b a hb ha =>
    simp only [selectPositionsAt,erase,markAt]
    split <;> simp only [skeleton,hb,ha]
  | app l f a hf ha =>
    cases f with
    | var => simp only [selectPositionsAt,erase,markAt,skeleton,ha]
    | app => simp only [selectPositionsAt,erase,markAt,skeleton,hf,ha]
    | red k b x =>
      change Marked.app [] (selectPositionsAt F (.red k b x) (p++[.fn])).skeleton (selectPositionsAt F a (p++[.arg])).skeleton =
        Marked.app [] (markAt F (Marked.red k b x).erase (p++[.fn])).skeleton (markAt F a.erase (p++[.arg])).skeleton
      rw [hf,ha]
    | lam b =>
      have hb := hf (p++[.fn])
      simp only [selectPositionsAt,erase,markAt,skeleton,Marked.lam.injEq] at hb
      simp only [selectPositionsAt,erase,markAt]
      split <;> simp only [skeleton,hb,ha]

theorem selectPositionsAt_passive (F : List Path) (t : Marked) (p : Path) :
    (selectPositionsAt F t p).passive=t.passive := by
  induction t generalizing p with
  | var => rfl
  | lam b ih => simp only [selectPositionsAt,passive,ih]
  | red l b a hb ha => simp only [selectPositionsAt]; split <;> simp only [passive,hb,ha]
  | app l f a hf ha =>
    cases f with
    | var => simp only [selectPositionsAt,passive,ha]
    | app => simp only [selectPositionsAt,passive,hf,ha]
    | red k b x =>
      change Marked.app l (selectPositionsAt F (.red k b x) (p++[.fn])).passive (selectPositionsAt F a (p++[.arg])).passive =
        Marked.app l (Marked.red k b x).passive a.passive
      rw [hf,ha]
    | lam b =>
      have hb := hf (p++[.fn])
      simp only [selectPositionsAt,passive,Marked.lam.injEq] at hb
      simp only [selectPositionsAt]; split <;> simp only [passive,hb,ha]

end Lamping.Lambda.Marked
namespace Lamping.Lambda

/-- A genuine tile commutes arbitrary passive application identities,
without a Valid assumption and without aligning identities with positions. -/
theorem ParallelMovesSquare.passive_tracking_diamond (sq : ParallelMovesSquare F G t u v w)
    (annotations : Marked) (source : annotations.erase=t) :
    ∃ target : Marked,
      Marked.History (sq.first.derivation.append sq.afterFirst.derivation).paths annotations.passive target ∧
      Marked.History (sq.second.derivation.append sq.afterSecond.derivation).paths annotations.passive target := by
  let selected := Marked.selectPositionsAt (F++G) annotations []
  have shape : (Marked.mark (F++G) t).skeleton=selected.skeleton := by
    rw [Marked.selectPositionsAt_skeleton]
    exact congrArg (fun t => (Marked.mark (F++G) t).skeleton) source.symm
  obtain ⟨target,left,right⟩ := sq.tracking_diamond selected shape
  exact ⟨target.passive,by simpa only [selected,Marked.selectPositionsAt_passive] using left.passive,
    by simpa only [selected,Marked.selectPositionsAt_passive] using right.passive⟩

private theorem tracking_split (history : Marked.History (ps++qs) a c) :
    ∃ b,Marked.History ps a b ∧ Marked.History qs b c := by
  induction ps generalizing a with
  | nil => exact ⟨a,.nil _,history⟩
  | cons p ps ih =>
    cases history with
    | cons first rest =>
      obtain ⟨b,left,right⟩ := ih rest
      exact ⟨b,.cons first left,right⟩

private theorem tracking_passive_target {a b : Marked} (history : Marked.History ps a.passive b) : b.passive=b := by
  have other := history.passive
  rw [Marked.passive_idempotent] at other
  exact other.deterministic history

/-- An entire actual residual row commutes arbitrary passive application
identities. Names may also occur at nonredex applications or repeat. -/
theorem StepProjection.passive_tracking_diamond
    {vertical : ParallelStep F t u} {σ : ParallelHistory t v} {τ : ParallelHistory u w}
    {last : ParallelStep G v w} (row : StepProjection vertical σ τ last)
    (annotations : Marked) (source : annotations.erase=t) :
    ∃ target : Marked,
      Marked.History (vertical.derivation.append τ.derivation).paths annotations.passive target ∧
      Marked.History (σ.derivation.append last.derivation).paths annotations.passive target := by
  induction row generalizing annotations with
  | nil vertical =>
    obtain ⟨target,history,_⟩ := Marked.lift_betaHistory vertical.derivation.valid annotations.passive
      ((Marked.passive_erase _).trans source)
    exact ⟨target,by simpa only [ParallelHistory.derivation,Derivation.append,Derivation.nil,List.append_nil] using history,
      by simpa only [ParallelHistory.derivation,Derivation.append,Derivation.nil,List.nil_append] using history⟩
  | @cons F H t u v x y σ w τ G last square rest ih =>
    obtain ⟨corner,left,right⟩ := square.passive_tracking_diamond annotations source
    obtain ⟨middle,firstTop,nextVertical⟩ := tracking_split right
    have middleSource : middle.erase=v := square.second.derivation.tracking_erase firstTop
      ((Marked.passive_erase _).trans source)
    obtain ⟨target,tailLeft,tailRight⟩ := ih middle middleSource
    have passiveMiddle := tracking_passive_target firstTop
    rw [passiveMiddle] at tailLeft tailRight
    obtain ⟨other,otherVertical,bottomTail⟩ := tracking_split tailLeft
    have same := nextVertical.deterministic otherVertical
    subst other
    refine ⟨target,?_,?__⟩
    · simpa only [ParallelHistory.derivation,Derivation.append,List.append_assoc] using left.append bottomTail
    · simpa only [ParallelHistory.derivation,Derivation.append,List.append_assoc] using firstTop.append tailRight

end Lamping.Lambda



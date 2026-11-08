import Lamping.Lambda.LabelFunctionPullback
namespace Lamping.Lambda.Labelled

/-- A real source turn which does not pass through either node of the
specified original beta head. App and lambda ports retain distinct roles. -/
inductive HeadFreeTurn (blockedApp blockedLam : Label) : SourcePort → SourcePort → Prop where
  | appOver (different : l≠blockedApp) : HeadFreeTurn blockedApp blockedLam (.appContext l) (.appFn l)
  | appUnder (different : l≠blockedApp) : HeadFreeTurn blockedApp blockedLam (.appFn l) (.appArg l)
  | lamOver (different : l≠blockedLam) : HeadFreeTurn blockedApp blockedLam (.lamContext l) (.lamBody l)
  | lamUnder (different : l≠blockedLam) : HeadFreeTurn blockedApp blockedLam (.lamBind l) (.lamContext l)
  | symm : HeadFreeTurn blockedApp blockedLam a b → HeadFreeTurn blockedApp blockedLam b a

def SourcePort.AtHead (blockedApp blockedLam : Label) : SourcePort → Prop
  | .appContext l | .appFn l | .appArg l => l=blockedApp
  | .lamContext l | .lamBody l | .lamBind l => l=blockedLam
  | .external | .free _ => False

theorem HeadFreeTurn.source_turn (turn : HeadFreeTurn blockedApp blockedLam a b) : SourceTurn a b := by
  induction turn with
  | appOver => exact .appOver _
  | appUnder => exact .appUnder _
  | lamOver => exact .lamOver _
  | lamUnder => exact .lamUnder _
  | symm _ ih => exact .symm ih

/-- No permitted turn can enter or leave a head port. Merely sharing a head
node therefore never supplies an implicit crossing between two edges. -/
theorem HeadFreeTurn.avoids_head (turn : HeadFreeTurn blockedApp blockedLam a b) :
    ¬a.AtHead blockedApp blockedLam ∧ ¬b.AtHead blockedApp blockedLam := by
  induction turn with
  | appOver different => exact ⟨different,different⟩
  | appUnder different => exact ⟨different,different⟩
  | lamOver different => exact ⟨different,different⟩
  | lamUnder different => exact ⟨different,different⟩
  | symm _ ih => exact ⟨ih.2,ih.1⟩

/-- A nonempty oriented source walk retaining the head restriction on every
actual intervening turn, including those inside reversed under payloads. -/
inductive HeadFreeWalk (edges : List SourceEdge) (blockedApp blockedLam : Label) :
    SourcePort → EdgeWord → SourcePort → Prop where
  | edge : SourceTraverse edges a e b → HeadFreeWalk edges blockedApp blockedLam a [e] b
  | join : HeadFreeWalk edges blockedApp blockedLam a p b → HeadFreeTurn blockedApp blockedLam b c →
      HeadFreeWalk edges blockedApp blockedLam c q d → HeadFreeWalk edges blockedApp blockedLam a (p++q) d

theorem HeadFreeWalk.walk (walk : HeadFreeWalk edges blockedApp blockedLam a word b) :
    SourceWalk edges a word b := by
  induction walk with
  | edge actual => exact .edge actual
  | join _ turn _ left right => exact .join left turn.source_turn right

theorem HeadFreeWalk.reverse (walk : HeadFreeWalk edges blockedApp blockedLam a word b) :
    HeadFreeWalk edges blockedApp blockedLam b (EdgeWord.reverse word) a := by
  induction walk with
  | edge actual => exact .edge actual.flip
  | join _ turn _ left right =>
    rw [EdgeWord.reverse_append]
    exact .join right (.symm turn) left

/-- Generated head-free label routes supply the actual restricted walk;
under labels reverse both edge order and each edge orientation. -/
theorem HeadFreeRoute.head_free_walk (route : HeadFreeRoute edges blockedApp blockedLam a l b) :
    HeadFreeWalk edges blockedApp blockedLam a l.edgeWord b := by
  induction route with
  | atom member atomic => exact .edge (.forward member atomic)
  | over appDifferent lamDifferent _ _ _ left middle right =>
    simp only [Label.edgeWord_concat,Label.edgeWord_over]
    exact .join (.join left (.appOver appDifferent) middle) (.lamOver lamDifferent) right
  | under appDifferent lamDifferent _ _ _ left middle right =>
    simp only [Label.edgeWord_concat,Label.edgeWord_under]
    exact .join (.join left (.lamUnder lamDifferent) middle.reverse) (.appUnder appDifferent) right
end Lamping.Lambda.Labelled

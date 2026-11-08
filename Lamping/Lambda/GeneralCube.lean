import Lamping.Lambda.ResidualSetComposition
import Lamping.Lambda.FiniteSelections
namespace Lamping.Lambda

/-- Three actual developments and all three front squares. These are
concrete complete edges, with their chosen schedules and old-name sets. -/
structure GeneralCubeFront (F G H : List Path) (t A B C AB AC BC : Term) where
  f : ParallelStep F t A
  g : ParallelStep G t B
  h : ParallelStep H t C
  fg : ParallelStep (f.residualSet G) A AB
  gf : ParallelStep (g.residualSet F) B AB
  fh : ParallelStep (f.residualSet H) A AC
  hf : ParallelStep (h.residualSet F) C AC
  gh : ParallelStep (g.residualSet H) B BC
  hg : ParallelStep (h.residualSet G) C BC

namespace GeneralCubeFront
def faceFG (front : GeneralCubeFront F G H t A B C AB AC BC) :
    ParallelMovesSquare F G t A B AB := ⟨front.f,front.g,front.fg,front.gf⟩
def faceFH (front : GeneralCubeFront F G H t A B C AB AC BC) :
    ParallelMovesSquare F H t A C AC := ⟨front.f,front.h,front.fh,front.hf⟩
def faceGH (front : GeneralCubeFront F G H t A B C AB AC BC) :
    ParallelMovesSquare G H t B C BC := ⟨front.g,front.h,front.gh,front.hg⟩

/-- Projecting either side of a front square across the third development
gives genuinely permutation-equivalent bottom paths. The opposite complete
edges are given actual developments; their endpoint agreement and the
permutation are proved, not supplied as a cube certificate. -/
theorem bottom_coherence (front : GeneralCubeFront F G H t A B C AB AC BC)
    (left : ParallelStep (front.fh.residualSet (front.f.residualSet G)) AC Z)
    (right : ParallelStep (front.gh.residualSet (front.g.residualSet F)) BC Z') :
    ∃ eq : Z=Z', PermEq
      (eq ▸ ((ParallelHistory.single front.hf).append (.single left)))
      ((ParallelHistory.single front.hg).append (.single right)) := by
  obtain ⟨W,afterF,afterG,_⟩ := parallel_moves front.hf front.hg
  have leftNames : ∀ p,p∈front.fh.residualSet (front.f.residualSet G) ↔
      p∈front.hf.residualSet (front.h.residualSet G) :=
    front.faceFH.composite_residualSet_members G
  have rightNames : ∀ p,p∈front.gh.residualSet (front.g.residualSet F) ↔
      p∈front.hg.residualSet (front.h.residualSet F) :=
    front.faceGH.composite_residualSet_members F
  have leftEndpoint := left.endpoint_selection afterF leftNames
  have rightEndpoint := right.endpoint_selection afterG rightNames
  cases leftEndpoint
  cases rightEndpoint
  have leftPerm := PermEq.selection left afterF leftNames
  have rightPerm := PermEq.selection right afterG rightNames
  let square : ParallelMovesSquare (front.h.residualSet F) (front.h.residualSet G)
      C AC BC Z := ⟨front.hf,front.hg,afterF,afterG⟩
  exact ⟨rfl,.trans (PermEq.prepend (.single front.hf) leftPerm)
    (.trans (.moves square) (.symm (PermEq.prepend (.single front.hg) rightPerm)))⟩

end GeneralCubeFront
end Lamping.Lambda

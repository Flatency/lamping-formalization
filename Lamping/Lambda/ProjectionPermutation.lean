import Lamping.Lambda.GeneralCube
import Lamping.Lambda.DerivationProjection
import Lamping.Lambda.ProjectionSelections
import Lamping.Lambda.ProjectionSplits
namespace Lamping.Lambda

private theorem nil_row (h : ParallelStep F t u) {bottom : ParallelHistory u v}
    {last : ParallelStep G t v} (row : StepProjection h (.nil t) bottom last) :
    v=u ∧ HEq bottom (ParallelHistory.nil u) := by
  cases row
  exact ⟨rfl,HEq.rfl⟩

private theorem one_tile (h : ParallelStep H t U) (f : ParallelStep F t A)
    {bottom : ParallelHistory U V} {last : ParallelStep K A V}
    (row : StepProjection h (.single f) bottom last) :
    ∃ square : ParallelMovesSquare H F t U A V,
      square.first=h ∧ square.second=f ∧ bottom=.single square.afterFirst := by
  cases row with
  | cons square tail =>
    obtain ⟨eq,bottomEq⟩ := nil_row square.afterSecond tail
    cases eq
    have equal := eq_of_heq bottomEq
    rw [equal]
    exact ⟨square,rfl,rfl,rfl⟩

private theorem two_tiles (h : ParallelStep H t U) (f : ParallelStep F t A)
    (g : ParallelStep G A C) {bottom : ParallelHistory U V} {last : ParallelStep K C V}
    (row : StepProjection h (.cons f (.single g)) bottom last) :
    ∃ M, ∃ first : ParallelMovesSquare H F t U A M,
      first.first=h ∧ first.second=f ∧
      ∃ second : ParallelMovesSquare (first.second.residualSet H) G A M C V,
        second.first=first.afterSecond ∧ second.second=g ∧
        bottom=.cons first.afterFirst (.single second.afterFirst) := by
  cases row with
  | cons first tail =>
    obtain ⟨second,vertical,top,bottomEq⟩ := one_tile first.afterSecond g tail
    rw [bottomEq]
    exact ⟨_,first,rfl,rfl,second,vertical,top,rfl⟩

/-- Actual two-tile projections of the two paths of a genuine square are
permutation equivalent. Their common endpoint is constructed by the cube. -/
theorem StepProjection.moves_coherence
    (square : ParallelMovesSquare F G t A B C) (h : ParallelStep H t U)
    {left : ParallelHistory U V} {right : ParallelHistory U W}
    {lastLeft : ParallelStep K C V} {lastRight : ParallelStep L C W}
    (rowLeft : StepProjection h
      ((ParallelHistory.single square.first).append (.single square.afterFirst)) left lastLeft)
    (rowRight : StepProjection h
      ((ParallelHistory.single square.second).append (.single square.afterSecond)) right lastRight) :
    ∃ eq : V=W, PermEq (eq ▸ left) right := by
  obtain ⟨M,leftFirst,firstH,firstF,leftSecond,secondH,secondG,leftEq⟩ :=
    two_tiles h square.first square.afterFirst rowLeft
  obtain ⟨N,rightFirst,rightH,rightG,rightSecond,rightSecondH,rightSecondF,rightEq⟩ :=
    two_tiles h square.second square.afterSecond rowRight
  cases leftFirst with
  | mk start first leftF leftH =>
    cases firstH
    cases firstF
    cases leftSecond with
    | mk incoming top leftBottom leftLast =>
      cases secondH
      cases secondG
      cases rightFirst with
      | mk start' first' rightG' rightH' =>
        cases rightH
        cases rightG
        cases rightSecond with
        | mk incoming' top' rightBottom rightLast =>
          cases rightSecondH
          cases rightSecondF
          rw [leftEq,rightEq]
          let front : GeneralCubeFront F G H t A B U C _ _ := {
            f := square.first
            g := square.second
            h := start
            fg := square.afterFirst
            gf := square.afterSecond
            fh := leftH
            hf := leftF
            gh := rightH'
            hg := rightG' }
          exact front.bottom_coherence leftBottom rightBottom

private theorem uncons (h : ParallelStep H t U) (head : ParallelStep F t A)
    (tail : ParallelHistory A B) {bottom : ParallelHistory U V} {last : ParallelStep K B V}
    (row : StepProjection h (.cons head tail) bottom last) :
    ∃ M, ∃ first : ParallelStep (h.residualSet F) U M,
      ∃ vertical : ParallelStep (head.residualSet H) A M,
      ∃ rest : ParallelHistory M V, StepProjection vertical tail rest last ∧ bottom=.cons first rest := by
  cases row with
  | cons square remaining => exact ⟨_,square.afterFirst,square.afterSecond,_,remaining,rfl⟩

private theorem residualSet_selection (h : ParallelStep F t u) (k : ParallelStep G t u)
    (same : ∀ p,p∈F ↔ p∈G) (names : List Path) : h.residualSet names=k.residualSet names := by
  exact h.residualSet_independent (k.reindex F (fun p => (same p).symm)) names

private theorem residualSet_members_congr (h : ParallelStep F t u)
    (same : ∀ p,p∈G ↔ p∈H) (p : Path) : p∈h.residualSet G ↔ p∈h.residualSet H := by
  change p∈Marked.setResidualPositions G h.markedTarget ↔ p∈Marked.setResidualPositions H h.markedTarget
  rw [Marked.mem_setResidualPositions,Marked.mem_setResidualPositions]
  exact ⟨fun ⟨r,hr,hp⟩ => ⟨r,(same r).mp hr,hp⟩,
    fun ⟨r,hr,hp⟩ => ⟨r,(same r).mpr hr,hp⟩⟩

/-- A fixed top history has the same projected permutation class for all
chosen developments of extensionally the same initial finite set. -/
theorem StepProjection.same_top_coherence (σ : ParallelHistory t v)
    (h : ParallelStep F t U) (k : ParallelStep G t U) (same : ∀ p,p∈F ↔ p∈G)
    {left : ParallelHistory U V} {right : ParallelHistory U W}
    {lastLeft : ParallelStep K v V} {lastRight : ParallelStep L v W}
    (rowLeft : StepProjection h σ left lastLeft) (rowRight : StepProjection k σ right lastRight) :
    ∃ eq : V=W, PermEq (eq ▸ left) right := by
  induction σ generalizing F G U V W K L with
  | nil t =>
    obtain ⟨leftEnd,leftEq⟩ := nil_row h rowLeft
    obtain ⟨rightEnd,rightEq⟩ := nil_row k rowRight
    cases leftEnd
    cases rightEnd
    have a := eq_of_heq leftEq
    have b := eq_of_heq rightEq
    rw [a,b]
    exact ⟨rfl,.refl _⟩
  | @cons t A v namesTop head tail ih =>
    obtain ⟨M,firstL,verticalL,restL,remainingL,leftEq⟩ := uncons h head tail rowLeft
    obtain ⟨N,firstR,verticalR,restR,remainingR,rightEq⟩ := uncons k head tail rowRight
    have names := residualSet_selection h k same namesTop
    have firstNames : ∀ p,p∈h.residualSet namesTop ↔ p∈k.residualSet namesTop := fun p => by rw [names]
    have middle := firstL.endpoint_selection firstR firstNames
    cases middle
    have firstPerm := PermEq.selection firstL firstR firstNames
    have verticalNames := residualSet_members_congr head same
    obtain ⟨endpoint,restPerm⟩ := ih verticalL verticalR verticalNames remainingL remainingR
    cases endpoint
    rw [leftEq,rightEq]
    exact ⟨rfl,PermEq.comp firstPerm restPerm⟩

/-- The last selections of rows over genuinely permutation-equivalent top
programs agree extensionally. Validity concerns only the initial names. -/
theorem StepProjection.permuted_final_selection {a b : ParallelHistory t v}
    (perm : PermEq a b) (h : ParallelStep F t U) (k : ParallelStep G t U)
    (same : ∀p,p∈F ↔ p∈G)
    (valid : ∀p∈F,∃z,subtermAt t p=some z ∧ IsRedex z)
    {left : ParallelHistory U V} {right : ParallelHistory U W}
    {lastLeft : ParallelStep K v V} {lastRight : ParallelStep L v W}
    (rowLeft : StepProjection h a left lastLeft) (rowRight : StepProjection k b right lastRight)
    (p : Path) : p∈K ↔ p∈L := by
  have validG : ∀p∈G,∃z,subtermAt t p=some z ∧ IsRedex z := fun p hp => valid p ((same p).mpr hp)
  constructor
  · intro hp
    let s : RedexOcc v := ⟨p,rowLeft.final_selection_valid valid p hp⟩
    obtain ⟨r,hr,residual⟩ := (rowLeft.final_selection valid s).mp hp
    exact (rowRight.final_selection validG s).mpr ⟨r,(same r.val).mp hr,(perm.residual r s).mp residual⟩
  · intro hp
    let s : RedexOcc v := ⟨p,rowRight.final_selection_valid validG p hp⟩
    obtain ⟨r,hr,residual⟩ := (rowRight.final_selection validG s).mp hp
    exact (rowLeft.final_selection valid s).mpr ⟨r,(same r.val).mpr hr,(perm.residual r s).mpr residual⟩

/-- Projection through every generated permutation respects its actual
permutation class. The chosen developments and schedules are arbitrary;
initial selected names must be actual redex positions. -/
theorem PermEq.projection_coherence {a b : ParallelHistory t v} (perm : PermEq a b)
    (h : ParallelStep F t U) (k : ParallelStep G t U) (same : ∀p,p∈F ↔ p∈G)
    (valid : ∀p∈F,∃z,subtermAt t p=some z ∧ IsRedex z)
    {left : ParallelHistory U V} {right : ParallelHistory U W}
    {lastLeft : ParallelStep K v V} {lastRight : ParallelStep L v W}
    (rowLeft : StepProjection h a left lastLeft) (rowRight : StepProjection k b right lastRight) :
    ∃eq : V=W,PermEq (eq ▸ left) right := by
  induction perm generalizing F G U V W K L with
  | refl a => exact StepProjection.same_top_coherence a h k same rowLeft rowRight
  | symm perm ih =>
    obtain ⟨eq,back⟩ := ih k h (fun p => (same p).symm)
      (fun p hp => valid p ((same p).mpr hp)) rowRight rowLeft
    cases eq
    exact ⟨rfl,back.symm⟩
  | @trans t v a b c ab bc ihab ihbc =>
    obtain ⟨M,N,middle,lastMiddle,rowMiddle⟩ := StepProjection.exists_projection h b
    obtain ⟨first,firstPerm⟩ := ihab h h (fun _ => Iff.rfl) valid rowLeft rowMiddle
    cases first
    obtain ⟨last,lastPerm⟩ := ihbc h k same valid rowMiddle rowRight
    cases last
    exact ⟨rfl,firstPerm.trans lastPerm⟩
  | @comp t v z a b c d ab cd ihab ihcd =>
    obtain ⟨M,H,firstLeft,tailLeft,verticalLeft,rowFirstLeft,rowTailLeft,leftEq⟩ := rowLeft.split_append a c
    obtain ⟨N,J,firstRight,tailRight,verticalRight,rowFirstRight,rowTailRight,rightEq⟩ := rowRight.split_append b d
    obtain ⟨middle,firstPerm⟩ := ihab h k same valid rowFirstLeft rowFirstRight
    cases middle
    have middleNames := StepProjection.permuted_final_selection ab h k same valid rowFirstLeft rowFirstRight
    have middleValid := rowFirstLeft.final_selection_valid valid
    obtain ⟨last,lastPerm⟩ := ihcd verticalLeft verticalRight middleNames middleValid rowTailLeft rowTailRight
    cases last
    rw [leftEq,rightEq]
    exact ⟨rfl,.comp firstPerm lastPerm⟩
  | @development names t0 v0 first second =>
    obtain ⟨squareLeft,headLeft,topLeft,leftEq⟩ := one_tile h first rowLeft
    obtain ⟨squareRight,headRight,topRight,rightEq⟩ := one_tile k second rowRight
    cases squareLeft with
    | mk start top afterFirst afterSecond =>
      cases headLeft
      cases topLeft
      cases squareRight with
      | mk start' top' afterFirst' afterSecond' =>
        cases headRight
        cases topRight
        have sameResidual := residualSet_selection start start' same names
        have equivalent : ∀p,p∈start.residualSet names ↔ p∈start'.residualSet names := by
          intro p; rw [sameResidual]
        have endpoint := afterFirst.endpoint_selection afterFirst' equivalent
        cases endpoint
        rw [leftEq,rightEq]
        exact ⟨rfl,.selection afterFirst afterFirst' equivalent⟩
  | moves square =>
    obtain ⟨M,N,middle,lastMiddle,rowMiddle⟩ := StepProjection.exists_projection h
      ((ParallelHistory.single square.second).append (.single square.afterSecond))
    obtain ⟨first,firstPerm⟩ := StepProjection.moves_coherence square h rowLeft rowMiddle
    cases first
    obtain ⟨last,lastPerm⟩ := StepProjection.same_top_coherence _ h k same rowMiddle rowRight
    cases last
    exact ⟨rfl,firstPerm.trans lastPerm⟩
  | empty step =>
    obtain ⟨rightEnd,rightEmpty⟩ := nil_row k rowRight
    cases rightEnd
    rw [eq_of_heq rightEmpty]
    obtain ⟨square,head,top,leftEq⟩ := one_tile h step rowLeft
    cases square with
    | mk start top' afterFirst afterSecond =>
      cases head
      cases top
      have emptyNames : start.residualSet []=[] := rfl
      have endpoint := afterFirst.endpoint_selection (ParallelStep.empty U) (by intro p; rw [emptyNames])
      cases endpoint
      rw [leftEq]
      exact ⟨rfl,PermEq.empty_of_selection afterFirst emptyNames⟩

end Lamping.Lambda



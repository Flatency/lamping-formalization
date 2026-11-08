import Lamping.Lambda.SquareSingletonResiduals
import Lamping.Lambda.SingleContraction
namespace Lamping.Lambda

private theorem residualSet_cast {F G : List Path} (eq : F = G) (h : ParallelStep F t u) (names : List Path) :
    (eq ▸ h).residualSet names = h.residualSet names := by
  cases eq
  rfl

/-- Reconstruct the back face of a singleton cube from two genuine old-image
 squares and their projected opposite contractions. The missing selections
 are proved by residual composition around those squares. -/
def singleton_cube_back
    (R : BetaAt t r u) (S : BetaAt t s v) (A : BetaAt t a z)
    (S_R : RedexOcc u) (R_S : RedexOcc v)
    (A_R : BetaAt u ar x) (R_A : BetaAt z ra x)
    (A_S : BetaAt v as' y) (S_A : BetaAt z sa y)
    (S_RA : BetaAt x sra q) (R_SA : BetaAt y rsa q)
    (rs : (singleContraction R).residualSet [s] = [S_R.val])
    (sr : (singleContraction S).residualSet [r] = [R_S.val])
    (ra' : (singleContraction R).residualSet [a] = [ar])
    (ar' : (singleContraction A).residualSet [r] = [ra])
    (sa' : (singleContraction S).residualSet [a] = [as'])
    (as'Image : (singleContraction A).residualSet [s] = [sa])
    (lastR : (singleContraction A_R).residualSet [S_R.val] = [sra])
    (lastS : (singleContraction A_S).residualSet [R_S.val] = [rsa]) :
    ParallelMovesSquare [ra] [sa] z x y q := by
  let squareR : ParallelMovesSquare [r] [a] t u z x :=
    ⟨singleContraction R,singleContraction A,
      ra'.symm ▸ singleContraction A_R, ar'.symm ▸ singleContraction R_A⟩
  let squareS : ParallelMovesSquare [s] [a] t v z y :=
    ⟨singleContraction S,singleContraction A,
      sa'.symm ▸ singleContraction A_S, as'Image.symm ▸ singleContraction S_A⟩
  have transferS := squareR.singleton_residualSet ⟨s,S.redex⟩ S_R ⟨sa,S_A.redex⟩ rs as'Image
  have transferR := squareS.singleton_residualSet ⟨r,R.redex⟩ R_S ⟨ra,R_A.redex⟩ sr ar'
  simp only [squareR, residualSet_cast] at transferS
  simp only [squareS, residualSet_cast] at transferR
  have afterR : (singleContraction R_A).residualSet [sa] = [sra] := transferS.symm.trans lastR
  have afterS : (singleContraction S_A).residualSet [ra] = [rsa] := transferR.symm.trans lastS
  exact ⟨singleContraction R_A,singleContraction S_A,
    afterR.symm ▸ singleContraction S_RA,afterS.symm ▸ singleContraction R_SA⟩

end Lamping.Lambda

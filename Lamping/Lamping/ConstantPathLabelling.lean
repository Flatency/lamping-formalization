import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Every segment occurrence carries the same supplied context. -/
inductive ConstantLabelling (a : Context) : List (Endpoint g) → Prop
  | single (e) : ConstantLabelling a [e]
  | cons {e f es} : LabelledTurn g (g.wire e) f a a → ConstantLabelling a (f::es) →
      ConstantLabelling a (e::f::es)
 theorem ConstantLabelling.label {a es} (h : ConstantLabelling (g:=g) a es) : Labelling g es a a := by
  induction h with
  | single => exact .single _ _
  | cons turn tail ih => exact .cons turn ih
 theorem ConstantLabelling.append_one {a es e f} (h : ConstantLabelling (g:=g) a es)
     (last : es.getLast?=some e) (step : LabelledTurn g (g.wire e) f a a) :
     ConstantLabelling (g:=g) a (es++[f]) := by
  induction h with
  | single x =>
    have same : x=e := Option.some.inj last
    subst e
    exact .cons step (.single f)
  | cons turn tail ih => exact .cons turn (ih (by simpa only [List.getLast?_cons_cons] using last))
 theorem ConstantLabelling.reverse {a es} (h : ConstantLabelling (g:=g) a es) :
     ConstantLabelling (g:=g) a (reverseEdges es) := by
  induction h with
  | single e => exact .single _
  | @cons e f es turn tail ih =>
    rw [show reverseEdges (e::f::es)=reverseEdges (f::es)++[g.wire e] by simp [reverseEdges]]
    apply ih.append_one (e:=g.wire f)
    · simp [reverseEdges]
    · simpa only [Pairing.involutive] using turn.reverse
 theorem ConstantLabelling.prefix {a pre tail} (h : ConstantLabelling (g:=g) a (pre++tail))
     (nonempty : pre≠[]) : ConstantLabelling (g:=g) a pre := by
  induction pre with
  | nil => exact False.elim (nonempty rfl)
  | cons x pre ih =>
    cases pre with
    | nil => exact .single x
    | cons y pre => cases h with
      | cons turn rest => exact .cons turn (ih rest (by simp))

 theorem transparent_constant_labelling (es : List (Endpoint g)) (nonempty : es≠[])
     (transparent : ∀ e f,(e,f)∈es.zip es.tail →
       ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) (a : Context) :
     ConstantLabelling (g:=g) a es := by
  induction es with
  | nil => exact False.elim (nonempty rfl)
  | cons e es ih =>
    cases es with
    | nil => exact .single e
    | cons f es =>
      obtain ⟨w,d,arrives,leaves⟩ := transparent e f (by simp)
      refine .cons ?_ (ih (by simp) ?_)
      · rw [arrives,leaves]
        exact .transparent w d a
      · intro x y pair
        exact transparent x y (by simp only [List.zip_cons_cons,List.tail_cons,List.mem_cons]; exact Or.inr pair)

 theorem BetaEdge.reverse_constant_labelling (r : BetaEdge g) (a : Context) :
     ConstantLabelling (g:=g) a r.reverseRoute :=
   (transparent_constant_labelling r.principal r.principal_nonempty r.transparent a).reverse
end
end Lamping.AG


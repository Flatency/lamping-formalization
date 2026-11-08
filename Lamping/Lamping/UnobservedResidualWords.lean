import Lamping.Lamping.UnobservedWireSourceResidual
import Lamping.Lamping.TraceSeams
namespace Lamping.AG
open Graph Lambda
section
variable {K B F W N D V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames F]
  [FiniteNames W] [FiniteNames N] [FiniteNames D] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature Empty F Empty)
variable (g : Net signature N D V) (embed : Endpoint c → Endpoint g)

def outsideEmission : PlugSegment c r → Path
  | .inl e => arrivalWord g (embed e)
  | .inr _ => []

def outsideAccessWord : List (PlugSegment c r) → Path
  | [] => []
  | _::tail => tail.flatMap (outsideEmission c r g embed)

private theorem overlap_word (front : List (Endpoint g)) (nonempty : front≠[])
    (last : Endpoint g) (post : List (Endpoint g)) :
    accessWord g (front++last::post)=
      accessWord g (front++[last])++accessWord g (last::post) := by
  cases front with
  | nil => exact False.elim (nonempty rfl)
  | cons e front =>
    simp only [List.cons_append,accessWord,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc]

/-- The explicitly recorded unobserved fronts preserve syntax words on
actual forward source paths. The raw first outside segment is kept; its
departure token is not silently erased. Frontier departure tokens are an
explicit local control-only fact to instantiate at cancellation sites. -/
theorem UnobservedWireResidual.access_word
    (frontierWord : ∀ f,arrivalWord g (embed (.inr (.inl (.inr f))))=[])
    {raw old} (relation : UnobservedWireResidual c r g embed raw old)
    (forward : Forward g old) : outsideAccessWord c r g embed raw=accessWord g old := by
  induction relation with
  | single e => rfl
  | @outside e f tail old rest ih =>
    have oldHead := rest.head c r g embed rfl
    obtain ⟨post,oldSplit⟩ := List.head?_eq_some_iff.mp oldHead
    rw [oldSplit] at forward ⊢
    have tailForward : Forward g (embed f::post) := by cases forward <;> assumption
    have after := ih (by simpa only [oldSplit] using tailForward)
    change (arrivalWord g (embed f)++tail.flatMap (outsideEmission c r g embed))=
      arrivalWord g (embed f)++post.flatMap (arrivalWord g)
    change tail.flatMap (outsideEmission c r g embed)=accessWord g old at after
    rw [oldSplit] at after
    rw [after]
    rfl
  | @through e f tail old front start nonempty unobserved rest ih =>
    let paired : Endpoint c := .inr (.inl (.inr (wireBoundaryMate r f)))
    have oldHead := rest.head c r g embed rfl
    obtain ⟨post,oldSplit⟩ := List.head?_eq_some_iff.mp oldHead
    have fullForward : Forward g ((front++[embed paired])++post) := by
      simpa only [oldSplit,List.append_assoc,List.singleton_append] using forward
    have blockForward := fullForward.prefix_of_append (by simp)
    have blockWord : accessWord g (front++[embed paired])=[] :=
      blockForward.unobserved_access_word (by simpa only [List.dropLast_concat] using unobserved)
    have tailAt : (front++old)[front.length]?=some (embed paired) := by
      rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,oldSplit]
      rfl
    have suffixForward := forward.suffix_at front.length _ tailAt
    simp only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at suffixForward
    have after := ih suffixForward
    have sourceWord : accessWord g (front++old)=accessWord g old := by
      rw [oldSplit,overlap_word g front nonempty (embed paired) post,blockWord,List.nil_append]
    rw [sourceWord]
    change ([]++arrivalWord g (embed paired)++tail.flatMap (outsideEmission c r g embed))=accessWord g old
    rw [frontierWord]
    exact after
end
end Lamping.AG

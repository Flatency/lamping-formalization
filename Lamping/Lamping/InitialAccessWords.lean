import Lamping.Lamping.MatchingDefinitions
import Lamping.Lamping.InitialOccurrencePaths
namespace Lamping.AG
open Graph Lambda
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

theorem arrivalWord_plugLeft (e : Endpoint c) :
    arrivalWord (plug c r) (plugLeft c r e)=arrivalWord c e := by
  rcases e with ⟨n,p⟩ | ((b|f) | ⟨w,d⟩) <;> rfl

theorem arrivalWord_plugRight (e : Endpoint r) :
    arrivalWord (plug c r) (plugRight c r e)=arrivalWord r e := by
  rcases e with ⟨n,p⟩ | (f | ⟨w,d⟩) <;> rfl

theorem accessWord_plugLeft (es : List (Endpoint c)) :
    accessWord (plug c r) (es.map (plugLeft c r))=accessWord c es := by
  cases es with
  | nil => rfl
  | cons e es =>
    change (es.map (plugLeft c r)).flatMap (arrivalWord (plug c r))=es.flatMap (arrivalWord c)
    rw [List.flatMap_map]
    exact congrArg (fun f => es.flatMap f) (funext (arrivalWord_plugLeft c r))

theorem accessWord_plugRight (es : List (Endpoint r)) :
    accessWord (plug c r) (es.map (plugRight c r))=accessWord r es := by
  cases es with
  | nil => rfl
  | cons e es =>
    change (es.map (plugRight c r)).flatMap (arrivalWord (plug c r))=es.flatMap (arrivalWord r)
    rw [List.flatMap_map]
    exact congrArg (fun f => es.flatMap f) (funext (arrivalWord_plugRight c r))
end

section
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)

theorem arrivalWord_unionL (e : Endpoint g) :
    arrivalWord (unionNet g h) (InitialOffsets.unionL g h e)=arrivalWord g e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl

theorem arrivalWord_unionR (e : Endpoint h) :
    arrivalWord (unionNet g h) (InitialOffsets.unionR g h e)=arrivalWord h e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl

theorem accessWord_unionL (es : List (Endpoint g)) :
    accessWord (unionNet g h) (es.map (InitialOffsets.unionL g h))=accessWord g es := by
  cases es with
  | nil => rfl
  | cons e es =>
    change (es.map (InitialOffsets.unionL g h)).flatMap (arrivalWord (unionNet g h))=es.flatMap (arrivalWord g)
    rw [List.flatMap_map]
    exact congrArg (fun f => es.flatMap f) (funext (arrivalWord_unionL g h))

theorem accessWord_unionR (es : List (Endpoint h)) :
    accessWord (unionNet g h) (es.map (InitialOffsets.unionR g h))=accessWord h es := by
  cases es with
  | nil => rfl
  | cons e es =>
    change (es.map (InitialOffsets.unionR g h)).flatMap (arrivalWord (unionNet g h))=es.flatMap (arrivalWord h)
    rw [List.flatMap_map]
    exact congrArg (fun f => es.flatMap f) (funext (arrivalWord_unionR g h))
end

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

theorem accessWord_append (pre tail : List (Endpoint g)) (nonempty : pre≠[]) :
    accessWord g (pre++tail)=accessWord g pre++tail.flatMap (arrivalWord g) := by
  cases pre with
  | nil => exact False.elim (nonempty rfl)
  | cons e es => exact List.flatMap_append

theorem accessWord_boundary (b : B) (tail : List (Endpoint g)) :
    accessWord g (.inr (.inl b)::tail)=tail.flatMap (arrivalWord g) := rfl
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
/-- All emitted syntax tokens, including a fragment's first departure.
For a rooted whole path that departure is a boundary and emits nothing. -/
def accessTokens (es : List (Endpoint g)) : Path := es.flatMap (arrivalWord g)
theorem accessTokens_append (xs ys : List (Endpoint g)) :
    accessTokens g (xs++ys)=accessTokens g xs++accessTokens g ys := List.flatMap_append

theorem accessTokens_eq_accessWord {es : List (Endpoint g)} (root : B)
    (head : es.head?=some (.inr (.inl root))) : accessTokens g es=accessWord g es := by
  cases es with
  | nil => cases head
  | cons e es =>
    have same : e=.inr (.inl root) := Option.some.inj head
    cases same
    rfl
end
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
theorem accessTokens_plugLeft (es : List (Endpoint c)) :
    accessTokens (plug c r) (es.map (plugLeft c r))=accessTokens c es := by
  unfold accessTokens
  rw [List.flatMap_map]
  exact congrArg (fun f => es.flatMap f) (funext (arrivalWord_plugLeft c r))
theorem accessTokens_plugRight (es : List (Endpoint r)) :
    accessTokens (plug c r) (es.map (plugRight c r))=accessTokens r es := by
  unfold accessTokens
  rw [List.flatMap_map]
  exact congrArg (fun f => es.flatMap f) (funext (arrivalWord_plugRight c r))
theorem accessTokens_three_pieces (xs : List (Endpoint c)) (ys : List (Endpoint r)) (zs : List (Endpoint c)) :
    accessTokens (plug c r) (xs.map (plugLeft c r)++ys.map (plugRight c r)++zs.map (plugLeft c r))=
      accessTokens c xs++accessTokens r ys++accessTokens c zs := by
  rw [accessTokens_append,accessTokens_append,accessTokens_plugLeft,
    accessTokens_plugRight,accessTokens_plugLeft]
end
section
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
theorem accessTokens_unionL (es : List (Endpoint g)) :
    accessTokens (unionNet g h) (es.map (InitialOffsets.unionL g h))=accessTokens g es := by
  unfold accessTokens
  rw [List.flatMap_map]
  exact congrArg (fun f => es.flatMap f) (funext (arrivalWord_unionL g h))
theorem accessTokens_unionR (es : List (Endpoint h)) :
    accessTokens (unionNet g h) (es.map (InitialOffsets.unionR g h))=accessTokens h es := by
  unfold accessTokens
  rw [List.flatMap_map]
  exact congrArg (fun f => es.flatMap f) (funext (arrivalWord_unionR g h))
end
end Lamping.AG

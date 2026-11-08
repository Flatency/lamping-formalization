import Lamping.Lamping.InitialAccessLookup
import Lamping.Lamping.InitialBindingSuffix
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
/-- Actual binder-suffix incidence/labels without a shell or direction input.
Only the actual initial encoding theorem later supplies those properties. -/
def RawBindingSuffix (es : List (Endpoint g)) (index : Nat) : Prop :=
  ∃ (pre loop : List (Endpoint g)) (a b c : Context)
    (binding : InitialOffsets.RawLoop g loop b c) (ctx : Port (g.label binding.binder).sort),
    es=pre++loop ∧HEq ctx (Sum.inl () : Port (.op .lam)) ∧
    pre.getLast?=some (g.wire (.inl ⟨binding.binder,ctx⟩)) ∧Labelling g pre a b ∧
    index=binderDepth (accessWord g loop)
end

theorem RawBindingSuffix.binding (t : Term) (n : Nat)
    {es : List (Endpoint (encode n t).net)} (raw : RawBindingSuffix (encode n t).net es k) :
    BindingSuffix (encode n t).net es k := by
  obtain ⟨pre,loop,a,b,c,binding,ctx,same,role,last,labels,index⟩ := raw
  exact ⟨pre,loop,a,b,c,InitialOffsets.encode_rawLoop_binding t n loop b c binding,
    ctx,same,role,last,labels,index⟩

section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
def InitialOffsets.RawLoop.plugRight {es : List (Endpoint r)} (loop : InitialOffsets.RawLoop r es a b) :
    InitialOffsets.RawLoop (plug c r) (es.map (AG.plugRight c r)) a b where
  binder := .inr loop.binder
  isLam := loop.isLam
  body := loop.body
  bind := loop.bind
  body_role := loop.body_role
  bind_role := loop.bind_role
  start := by rw [List.head?_map,loop.start]; rfl
  finish := by rw [List.getLast?_map,loop.finish]; exact congrArg some (plugRight_wire c r _).symm
  proper := loop.proper.plugRight c

theorem RawBindingSuffix.plugRight {es : List (Endpoint r)} (raw : RawBindingSuffix r es k) :
    RawBindingSuffix (plug c r) (es.map (AG.plugRight c r)) k := by
  obtain ⟨pre,loop,a,b,c',binding,ctx,same,role,last,labels,index⟩ := raw
  refine ⟨pre.map (AG.plugRight c r),loop.map (AG.plugRight c r),a,b,c',binding.plugRight c r,
    ctx,?_,role,?_,labels.plugRight c,?_⟩
  · rw [same,List.map_append]
  · rw [List.getLast?_map,last]; exact congrArg some (plugRight_wire c r _).symm
  · rw [accessWord_plugRight]; exact index
end
section
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
def InitialOffsets.RawLoop.unionLeft {es : List (Endpoint g)} (loop : InitialOffsets.RawLoop g es a b) :
    InitialOffsets.RawLoop (unionNet g h) (es.map (InitialOffsets.unionL g h)) a b where
  binder := .inl loop.binder
  isLam := loop.isLam
  body := loop.body
  bind := loop.bind
  body_role := loop.body_role
  bind_role := loop.bind_role
  start := by rw [List.head?_map,loop.start]; rfl
  finish := by rw [List.getLast?_map,loop.finish]; exact congrArg some (union_left g h _).symm
  proper := loop.proper.unionLeft g h

def InitialOffsets.RawLoop.unionRight {es : List (Endpoint h)} (loop : InitialOffsets.RawLoop h es a b) :
    InitialOffsets.RawLoop (unionNet g h) (es.map (InitialOffsets.unionR g h)) a b where
  binder := .inr loop.binder
  isLam := loop.isLam
  body := loop.body
  bind := loop.bind
  body_role := loop.body_role
  bind_role := loop.bind_role
  start := by rw [List.head?_map,loop.start]; rfl
  finish := by rw [List.getLast?_map,loop.finish]; exact congrArg some (union_right g h _).symm
  proper := loop.proper.unionRight g h

theorem RawBindingSuffix.unionLeft {es : List (Endpoint g)} (raw : RawBindingSuffix g es k) :
    RawBindingSuffix (unionNet g h) (es.map (InitialOffsets.unionL g h)) k := by
  obtain ⟨pre,loop,a,b,c,binding,ctx,same,role,last,labels,index⟩ := raw
  refine ⟨pre.map (InitialOffsets.unionL g h),loop.map (InitialOffsets.unionL g h),a,b,c,
    binding.unionLeft g h,ctx,?_,role,?_,labels.unionLeft g h,?_⟩
  · rw [same,List.map_append]
  · rw [List.getLast?_map,last]; exact congrArg some (union_left g h _).symm
  · rw [accessWord_unionL]; exact index

theorem RawBindingSuffix.unionRight {es : List (Endpoint h)} (raw : RawBindingSuffix h es k) :
    RawBindingSuffix (unionNet g h) (es.map (InitialOffsets.unionR g h)) k := by
  obtain ⟨pre,loop,a,b,c,binding,ctx,same,role,last,labels,index⟩ := raw
  refine ⟨pre.map (InitialOffsets.unionR g h),loop.map (InitialOffsets.unionR g h),a,b,c,
    binding.unionRight g h,ctx,?_,role,?_,labels.unionRight g h,?_⟩
  · rw [same,List.map_append]
  · rw [List.getLast?_map,last]; exact congrArg some (union_right g h _).symm
  · rw [accessWord_unionR]; exact index
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
/-- Prefix an embedded child's binder witness by a real, context-preserving
patch route. The quantified route is physical input data, not a global invariant. -/
theorem RawBindingSuffix.enter_child {es : List (Endpoint r)} {root : B} {entry : F}
    (raw : RawBindingSuffix r es k) (head : es.head?=some (.inr (.inl entry)))
    (kind : accessKind r es=some .var)
    (first : ∀ input,LocalPath c (.inl root) (.inr entry) input input)
    (token : Path) (firstWord : ∀ input,accessTokens c (first input).edges=token) :
    ∃ joined : List (Endpoint (plug c r)),RawBindingSuffix (plug c r) joined k ∧
      joined.head?=some (.inr (.inl root)) ∧
      accessTokens (plug c r) joined=token++accessTokens r es ∧
      accessKind (plug c r) joined=some .var := by
  obtain ⟨pre,loop,a,b,d,binding,ctx,same,role,last,labels,index⟩ := raw
  have preHead : pre.head?=some (.inr (.inl entry)) := by
    rw [same] at head
    cases pre with
    | nil => cases labels
    | cons e tail => exact head
  let xs := (first a).edges.map (AG.plugLeft c r)
  let joined := xs++es.map (AG.plugRight c r)
  have preLabels : Labelling (plug c r) (xs++pre.map (AG.plugRight c r)) a b := by
    apply ((first a).labeling.plugLeft c r).append_seam (labels.plugRight c)
    intro left right leftLast rightHead
    have leftEq : left=AG.plugLeft c r (c.wire (.inr (.inl (.inr entry)))) := by
      have original : xs.getLast?=some (AG.plugLeft c r (c.wire (.inr (.inl (.inr entry))))) := by
        rw [List.getLast?_map,(first a).finish]; rfl
      exact Option.some.inj (leftLast.symm.trans original)
    have rightEq : right=AG.plugRight c r (.inr (.inl entry)) := by
      have original : (pre.map (AG.plugRight c r)).head?=some (AG.plugRight c r (.inr (.inl entry))) := by
        rw [List.head?_map,preHead]; rfl
      exact Option.some.inj (rightHead.symm.trans original)
    rw [leftEq,rightEq,←plugLeft_wire,Pairing.involutive]
    exact .transparent (Sum.inr entry) false a
  have esMappedNonempty : es.map (AG.plugRight c r)≠[] := by
    intro empty
    have heads := congrArg List.head? empty
    rw [List.head?_map,head] at heads
    cases heads
  refine ⟨joined,?_,?_,?_,?_⟩
  · refine ⟨xs++pre.map (AG.plugRight c r),loop.map (AG.plugRight c r),a,b,d,
      binding.plugRight c r,ctx,?_,role,?_,preLabels,?_⟩
    · dsimp only [joined]
      rw [same,List.map_append,List.append_assoc]
    · rw [List.getLast?_append]
      have lastMapped : (pre.map (AG.plugRight c r)).getLast?=
          some ((plug c r).wire (.inl ⟨.inr binding.binder,ctx⟩)) := by
        rw [List.getLast?_map,last]
        exact congrArg some (plugRight_wire c r _).symm
      rw [lastMapped]; rfl
    · rw [accessWord_plugRight]; exact index
  · dsimp only [joined,xs]
    rw [List.head?_append,List.head?_map,(first a).start]; rfl
  · dsimp only [joined,xs]
    rw [accessTokens_append,accessTokens_plugLeft,accessTokens_plugRight,firstWord]
  · dsimp only [joined]
    rw [accessKind_append _ _ _ esMappedNonempty,accessKind_plugRight]
    exact kind
end
end Lamping.AG


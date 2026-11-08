import Lamping.Lamping.InitialFreeConstruction
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
private theorem last_append_nonempty {T : Type} (xs ys : List T) (nonempty : ys≠[]) :
    (xs++ys).getLast?=ys.getLast? := by
  rw [List.getLast?_append]
  cases h : ys.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp h))
  | some => rfl

theorem accessKind_append (xs ys : List (Endpoint g)) (nonempty : ys≠[]) :
    accessKind g (xs++ys)=accessKind g ys := by
  unfold accessKind
  rw [last_append_nonempty xs ys nonempty]
end
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

theorem accessKind_plugRight (es : List (Endpoint r)) :
    accessKind (plug c r) (es.map (AG.plugRight c r))=accessKind r es := by
  unfold accessKind
  rw [List.getLast?_map]
  cases last : es.getLast? with
  | none => rfl
  | some e =>
    simp only [Option.map_some,Option.bind_some,plugRight_wire]
    rcases r.wire e with ⟨n,p⟩ | (f | ⟨w,d⟩) <;> rfl

/-- Enter an encoded child through an actual patch path. The child may stop
at an internal proper node; it need not return to a frontier boundary. -/
theorem Labelling.enter_child {x : B} {entry : F}
    (first : LocalPath c (.inl x) (.inr entry) a b)
    {es : List (Endpoint r)} (middle : Labelling r es b d)
    (head : es.head?=some (.inr (.inl entry))) :
    ∃ joined : List (Endpoint (plug c r)),
      Labelling (plug c r) joined a d ∧
      joined.head?=some (.inr (.inl x)) ∧
      accessTokens (plug c r) joined=accessTokens c first.edges++accessTokens r es ∧
      accessKind (plug c r) joined=accessKind r es := by
  let joined := first.edges.map (AG.plugLeft c r)++es.map (AG.plugRight c r)
  have headFirst : (first.edges.map (AG.plugLeft c r)).head?=some (.inr (.inl x)) := by
    rw [List.head?_map,first.start]
    rfl
  have nonempty : es.map (AG.plugRight c r)≠[] := by
    intro empty
    have heads := congrArg List.head? empty
    rw [List.head?_map,head] at heads
    cases heads
  refine ⟨joined,?_,?_,?_,?_⟩
  · apply (first.labeling.plugLeft c r).append_seam (middle.plugRight c)
    intro left right leftEnd rightStart
    have leftEq : left=AG.plugLeft c r (c.wire (.inr (.inl (.inr entry)))) := by
      have original : (first.edges.map (AG.plugLeft c r)).getLast?=
          some (AG.plugLeft c r (c.wire (.inr (.inl (.inr entry))))) := by
        rw [List.getLast?_map,first.finish]; rfl
      exact Option.some.inj (leftEnd.symm.trans original)
    have rightEq : right=AG.plugRight c r (.inr (.inl entry)) := by
      have original : (es.map (AG.plugRight c r)).head?=some (AG.plugRight c r (.inr (.inl entry))) := by
        rw [List.head?_map,head]; rfl
      exact Option.some.inj (rightStart.symm.trans original)
    rw [leftEq,rightEq,←plugLeft_wire,Pairing.involutive]
    exact .transparent (Sum.inr entry) false b
  · simp only [joined,List.head?_append,headFirst,Option.some_or]
  · exact (accessTokens_append _ _ _).trans (by rw [accessTokens_plugLeft,accessTokens_plugRight])
  · rw [accessKind_append _ _ _ nonempty,accessKind_plugRight]
end
section
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)

theorem accessKind_unionL (es : List (Endpoint g)) :
    accessKind (unionNet g h) (es.map (InitialOffsets.unionL g h))=accessKind g es := by
  unfold accessKind
  rw [List.getLast?_map]
  cases last : es.getLast? with
  | none => rfl
  | some e =>
    simp only [Option.map_some,Option.bind_some,InitialOffsets.unionL,union_left]
    rcases g.wire e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl

theorem accessKind_unionR (es : List (Endpoint h)) :
    accessKind (unionNet g h) (es.map (InitialOffsets.unionR g h))=accessKind h es := by
  unfold accessKind
  rw [List.getLast?_map]
  cases last : es.getLast? with
  | none => rfl
  | some e =>
    simp only [Option.map_some,Option.bind_some,InitialOffsets.unionR,union_right]
    rcases h.wire e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
/-- An actual child route can return through its exit seam and stop immediately
at the adjoining patch port. No exterior boundary endpoint is required. -/
theorem LocalPath.enter_return {x : B} {entry exit : F}
    (first : LocalPath c (.inl x) (.inr entry) a b)
    (middle : LocalPath r entry exit b d) :
    ∃ es : List (Endpoint (plug c r)), Labelling (plug c r) es a d ∧
      es.head?=some (.inr (.inl x)) ∧
      accessTokens (plug c r) es=accessTokens c first.edges++accessTokens r middle.edges ∧
      es.getLast?=some (AG.plugLeft c r (.inr (.inl (.inr exit)))) := by
  let front := first.edges.map (AG.plugLeft c r)++middle.edges.map (AG.plugRight c r)
  have labelsFront : Labelling (plug c r) front a d := by
    apply (first.labeling.plugLeft c r).append_seam (middle.labeling.plugRight c)
    intro left right last start
    have leftEq : left=AG.plugLeft c r (c.wire (.inr (.inl (.inr entry)))) := by
      have original : (first.edges.map (AG.plugLeft c r)).getLast?=
          some (AG.plugLeft c r (c.wire (.inr (.inl (.inr entry))))) := by
        rw [List.getLast?_map,first.finish]; rfl
      exact Option.some.inj (last.symm.trans original)
    have rightEq : right=AG.plugRight c r (.inr (.inl entry)) := by
      have original : (middle.edges.map (AG.plugRight c r)).head?=
          some (AG.plugRight c r (.inr (.inl entry))) := by
        rw [List.head?_map,middle.start]; rfl
      exact Option.some.inj (start.symm.trans original)
    rw [leftEq,rightEq,←plugLeft_wire,Pairing.involutive]
    exact .transparent (Sum.inr entry) false b
  have middleNonempty : middle.edges.map (AG.plugRight c r)≠[] := by
    intro empty
    have heads := congrArg List.head? empty
    rw [List.head?_map,middle.start] at heads
    cases heads
  have lastFront : front.getLast?=some (AG.plugRight c r (r.wire (.inr (.inl exit)))) := by
    dsimp only [front]
    rw [last_append_nonempty _ _ middleNonempty,List.getLast?_map,middle.finish]; rfl
  let seam := AG.plugLeft c r (.inr (.inl (.inr exit)))
  refine ⟨front++[seam],?_,?_,?_,?_⟩
  · apply labelsFront.append_seam (.single seam d)
    intro left right last start
    have leftEq := Option.some.inj (last.symm.trans lastFront)
    have rightEq : right=seam := (Option.some.inj start).symm
    rw [leftEq,rightEq,←plugRight_wire,Pairing.involutive]
    exact .transparent (Sum.inr exit) true d
  · simp only [front,List.head?_append,List.head?_map,first.start,Option.map_some,Option.some_or]
    rfl
  · rw [accessTokens_append,accessTokens_append,accessTokens_plugLeft,accessTokens_plugRight]
    change (_++_)++[]= _
    exact List.append_nil _
  · rw [last_append_nonempty front [seam] (by simp)]
    rfl
end
end Lamping.AG


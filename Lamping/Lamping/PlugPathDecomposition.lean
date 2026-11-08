import Lamping.Lamping.InitialPathControls
namespace Lamping.AG
open Graph
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

abbrev PlugSegment := Endpoint c ⊕Endpoint r
def plugSegmentWire : PlugSegment c r → PlugSegment c r :=
  Sum.elim (Sum.inl ∘c.wire.mate) (Sum.inr ∘r.wire.mate)

/-- Exact inversion of a glued turn. Frontier crossings retain their actual
name and direction; left/right turns retain the actual local node relation. -/
inductive PlugTurn : PlugSegment c r → PlugSegment c r → Context → Context → Prop where
  | left {x y a b} (turn : LabelledTurn c x y a b) : PlugTurn (.inl x) (.inl y) a b
  | right {x y a b} (turn : LabelledTurn r x y a b) : PlugTurn (.inr x) (.inr y) a b
  | enter (f : F) (a : Context) : PlugTurn (.inl (.inr (.inl (.inr f)))) (.inr (.inr (.inl f))) a a
  | leave (f : F) (a : Context) : PlugTurn (.inr (.inr (.inl f))) (.inl (.inr (.inl (.inr f)))) a a

theorem PlugTurn.of_actual {x y : Endpoint (plug c r)} (turn : LabelledTurn (plug c r) x y a b) :
    PlugTurn c r ((plugEnd c.label r.label).invFun x) ((plugEnd c.label r.label).invFun y) a b := by
  cases turn with
  | node node p q rule =>
    cases node with
    | inl k => exact .left (.node k p q rule)
    | inr n => exact .right (.node n p q rule)
  | transparent vertex d a =>
    rcases vertex with (w|v)|f
    · exact .left (.transparent w d a)
    · exact .right (.transparent v d a)
    · cases d
      · exact .enter f a
      · exact .leave f a

theorem PlugTurn.actual {x y : PlugSegment c r} (turn : PlugTurn c r x y a b) :
    LabelledTurn (plug c r) ((plugEnd c.label r.label) x) ((plugEnd c.label r.label) y) a b := by
  cases turn with
  | left turn => exact turn.plugLeft c r
  | right turn => exact turn.plugRight c
  | enter f a => exact LabelledTurn.transparent (g:=plug c r) (.inr f) false a
  | leave f a => exact LabelledTurn.transparent (g:=plug c r) (.inr f) true a

theorem plugSegmentWire_inverse (e : Endpoint (plug c r)) :
    (plugEnd c.label r.label).invFun ((plug c r).wire e)=
      plugSegmentWire c r ((plugEnd c.label r.label).invFun e) := by
  change (plugEnd c.label r.label).invFun ((plugEnd c.label r.label)
    (plugSegmentWire c r ((plugEnd c.label r.label).invFun e)))=_
  exact (plugEnd c.label r.label).left_inv _

/-- A finite ordered trace of raw segment occurrences. Singleton and
frontier-truncated paths are included; there is no direction/generation or
soundness hypothesis hidden in this decomposition. -/
inductive PlugLabelling : List (PlugSegment c r) → Context → Context → Prop where
  | single (e a) : PlugLabelling [e] a a
  | cons {e f es a b d} (turn : PlugTurn c r (plugSegmentWire c r e) f a b)
      (tail : PlugLabelling (f::es) b d) : PlugLabelling (e::f::es) a d

theorem Labelling.plug_decomposition {es : List (Endpoint (plug c r))}
    (labels : Labelling (plug c r) es a b) :
    PlugLabelling c r (es.map (plugEnd c.label r.label).invFun) a b := by
  induction labels with
  | single e a => exact .single _ _
  | cons turn tail ih =>
    apply PlugLabelling.cons
    · have localTurn := PlugTurn.of_actual c r turn
      rw [plugSegmentWire_inverse] at localTurn
      exact localTurn
    · exact ih

theorem PlugLabelling.actual {es : List (PlugSegment c r)} (labels : PlugLabelling c r es a b) :
    Labelling (plug c r) (es.map (plugEnd c.label r.label)) a b := by
  induction labels with
  | single e a => exact .single _ _
  | @cons e f es a b d turn tail ih =>
    apply Labelling.cons
    · have actual := turn.actual c r
      have wired : (plug c r).wire ((plugEnd c.label r.label) e)=
          (plugEnd c.label r.label) (plugSegmentWire c r e) :=
        Pairing.rename_apply (c.wire.sum r.wire) (plugEnd c.label r.label) e
      rw [wired]
      exact actual
    · exact ih

theorem plug_decomposition_flatten (es : List (Endpoint (plug c r))) :
    (es.map (plugEnd c.label r.label).invFun).map (plugEnd c.label r.label)=es := by
  rw [List.map_map]
  have inverse : (fun e : Endpoint (plug c r) => (plugEnd c.label r.label) ((plugEnd c.label r.label).invFun e))=id :=
    funext (plugEnd c.label r.label).right_inv
  change List.map (fun e : Endpoint (plug c r) => (plugEnd c.label r.label) ((plugEnd c.label r.label).invFun e)) es=es
  rw [inverse,List.map_id]
end
end Lamping.AG

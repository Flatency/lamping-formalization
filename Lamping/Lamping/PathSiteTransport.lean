import Lamping.Lamping.LocalTransport
import Lamping.Lamping.PathSplicing
namespace Lamping.AG
open Graph
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R]
  [FiniteNames B] [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B ⊕ F) W) (r : Net signature R F V)

/-- Natural embedding of every real RHS endpoint into the actual plug output. -/
def plugRight (e : Endpoint r) : Endpoint (plug c r) := plugEnd c.label r.label (.inr e)

theorem plugRight_wire (e : Endpoint r) :
    (plug c r).wire (plugRight c r e) = plugRight c r (r.wire e) :=
  Pairing.rename_apply _ _ _

theorem LabelledTurn.plugRight {x y : Endpoint r} {a b : Context}
    (h : LabelledTurn r x y a b) :
    LabelledTurn (plug c r) (AG.plugRight c r x) (AG.plugRight c r y) a b := by
  cases h with
  | node n p q ht => exact LabelledTurn.node (g := plug c r) (.inr n) p q ht
  | transparent v d a => exact LabelledTurn.transparent (g := plug c r) (.inl (.inr v)) d a

theorem Labelling.plugRight {es : List (Endpoint r)} {a b : Context}
    (h : Labelling r es a b) : Labelling (plug c r) (es.map (AG.plugRight c r)) a b := by
  induction h with
  | single e a => exact .single _ a
  | cons ht _ ih =>
    have ht' := ht.plugRight c
    rw [← plugRight_wire] at ht'
    exact .cons ht' ih

def LocalPath.plugEdges {x y : F} {a b : Context} (p : LocalPath r x y a b) :
    List (Endpoint (plug c r)) := p.edges.map (AG.plugRight c r)

theorem LocalPath.plug_labeling {x y : F} {a b : Context} (p : LocalPath r x y a b) :
    Labelling (plug c r) (p.plugEdges c) a b := p.labeling.plugRight c

theorem LocalPath.plug_start {x y : F} {a b : Context} (p : LocalPath r x y a b) :
    (p.plugEdges c).head? = some (.inr (.inr (.inr x,true))) := by
  simp only [plugEdges,List.head?_map,p.start,Option.map_some]
  rfl

theorem LocalPath.plug_finish {x y : F} {a b : Context} (p : LocalPath r x y a b) :
    (p.plugEdges c).getLast? = some ((plug c r).wire (.inr (.inr (.inr y,true)))) := by
  simp only [plugEdges,List.getLast?_map,p.finish,Option.map_some]
  congr 1
end

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B := B) (W := W) (V := V))

/-- The RHS piece is embedded into the actual cutFragment→plug result,
not a separate net chosen to satisfy the transport conclusion. -/
def PathSite.rhsEdges {x y : s.Frontier} {a b : Context}
    (p : LocalPath s.right.net x y a b) : List (Endpoint site.reduce) :=
  p.plugEdges (cutFragment site.net (pathPartition s V) site.closed)

theorem PathSite.rhs_labeling {x y : s.Frontier} {a b : Context}
    (p : LocalPath s.right.net x y a b) : Labelling site.reduce (site.rhsEdges p) a b :=
  p.plug_labeling _

theorem PathSite.rhs_start {x y : s.Frontier} {a b : Context}
    (p : LocalPath s.right.net x y a b) :
    (site.rhsEdges p).head? = some (.inr (.inr (.inr x,true))) := p.plug_start _

theorem PathSite.rhs_finish {x y : s.Frontier} {a b : Context}
    (p : LocalPath s.right.net x y a b) :
    (site.rhsEdges p).getLast? = some (site.reduce.wire (.inr (.inr (.inr y,true)))) :=
  p.plug_finish _
end
end Lamping.AG

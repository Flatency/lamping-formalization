import Lamping.Lamping.ExposureControlWords
import Lamping.Lamping.ActionCanonicalAssembly

namespace Lamping.AG
open Graph
namespace ExposureScheduling

/-- The contribution of an actual departure, before dropping a path's head. -/
def endpointControlWord {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) : Endpoint g → List Bool
  | .inl ⟨node,port⟩ => controlPortWord (g.label node).sort port
  | .inr _ => []

section Plug
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

def rawControlWord (raw : List (PlugSegment c r)) : List Bool :=
  raw.tail.flatMap (Sum.elim (endpointControlWord c) (endpointControlWord r))

/-- Literal plug endpoint transport, including the common frontier. -/
theorem controlWord_plug_map (raw : List (PlugSegment c r)) :
    controlWord (plug c r) (raw.map (plugEnd c.label r.label))=rawControlWord c r raw := by
  cases raw with
  | nil => rfl
  | cons e tail =>
    change (tail.map (plugEnd c.label r.label)).flatMap (endpointControlWord (plug c r))=
      tail.flatMap (Sum.elim (endpointControlWord c) (endpointControlWord r))
    rw [List.flatMap_map]
    apply congrArg (fun f => tail.flatMap f)
    funext piece
    rcases piece with (⟨node,p⟩|((boundary|frontier)|⟨vertex,direction⟩))|
      (⟨node,p⟩|(frontier|⟨vertex,direction⟩)) <;> rfl

/-- The actual next turn for an outside/outside raw step. -/
theorem outside_cons_view {e f : Endpoint c} {tail} {a b : Context}
    (labels : PlugLabelling c r (Sum.inl e::Sum.inl f::tail) a b) :
    ∃ middle,LabelledTurn c (c.wire e) f a middle ∧
      PlugLabelling c r (Sum.inl f::tail) middle b := by
  cases labels with
  | cons turn rest =>
    change PlugTurn c r (Sum.inl (c.wire e)) (Sum.inl f) a _ at turn
    generalize arrivalEq : c.wire e=arrival at turn
    cases turn with
    | left localTurn => exact ⟨_,by simpa only [arrivalEq] using localTurn,rest⟩
end Plug

/-- Transparent vertices have no control token, at every literal visit. -/
theorem transparent_control_word {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (es : List (Endpoint g))
    (transparent : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,g.wire e=Sum.inr (Sum.inr (w,d)) ∧f=Sum.inr (Sum.inr (w,!d))) :
    controlWord g es=[] := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases es with
    | nil => rfl
    | cons f tail =>
      obtain ⟨w,d,_arrives,leaves⟩ := transparent e f (by simp)
      have rest := ih (by intro x y pair;exact transparent x y (List.mem_cons_of_mem _ pair))
      change endpointControlWord g f++controlWord g (f::tail)=[]
      rw [rest,leaves]
      rfl
end ExposureScheduling

section Outside
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

/-- Actual outside turns retain the departure token, without an inverse label map. -/
theorem PathSite.outside_control_port_word {e f : Endpoint cut} {a b : Context}
    (turn : LabelledTurn cut ((cut).wire e) f a b) :
    ExposureScheduling.endpointControlWord site.net (site.outsideEnd f)=
      ExposureScheduling.endpointControlWord cut f := by
  generalize arrivalEq : (cut).wire e=arrival at turn
  cases turn <;> rfl
end Outside
end Lamping.AG

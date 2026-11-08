import Lamping.Lamping.IndexedSchemaBalance
import Lamping.Lamping.GraphBalancePreservation
namespace Lamping.Graph
open Lamping.AG
section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M]
  [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V} (iso : NetIso g h)

def NetIso.indexed_balance {boundary : B → Int} (old : IndexedLevelBalance g boundary) :
    IndexedLevelBalance h boundary where
  toLevelBalance := iso.balance old.toLevelBalance
  bounded m := by
    have same := iso.labels (iso.nodes.invFun m)
    rw [iso.nodes.right_inv] at same
    change ControlIndexBound (h.label m) (old.nodes (iso.nodes.invFun m))
    rw [same]
    exact old.bounded _
end
end Lamping.Graph

namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V)) {boundary : B → Int}

def PathSite.cut_indexed_balance (old : IndexedLevelBalance site.net boundary) :
    IndexedLevelBalance (cutFragment site.net (pathPartition s V) site.closed)
      (Sum.elim boundary (site.frontierDepth old.toLevelBalance)) where
  toLevelBalance := site.cut_balance old.toLevelBalance
  bounded k := old.bounded (.inl k)

def PathSite.left_indexed_balance (old : IndexedLevelBalance site.net boundary) :
    IndexedLevelBalance s.left (site.frontierDepth old.toLevelBalance) where
  toLevelBalance := site.left_balance old.toLevelBalance
  bounded n := old.bounded (.inr n)

theorem PathSite.reduce_indexed_balance (old : IndexedLevelBalance site.net boundary) :
    Nonempty (IndexedLevelBalance site.reduce boundary) := by
  obtain ⟨rhs⟩ := s.indexed_balance_preservation _ (site.left_indexed_balance old)
  exact ⟨IndexedLevelBalance.plug _ _ _ _ (site.cut_indexed_balance old) rhs⟩
end
section
variable {B : Type} [FiniteNames B] {boundary : B → Int}

theorem GraphStep.indexed_balance {s : Schema} {g h : ActualNet B} (step : GraphStep s g h)
    (old : IndexedLevelBalance g.net boundary) : Nonempty (IndexedLevelBalance h.net boundary) := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    obtain ⟨changed⟩ := site.reduce_indexed_balance (sourceIso.indexed_balance old)
    exact ⟨targetIso.indexed_balance changed⟩

theorem GraphTrace.indexed_balance {g h : ActualNet B} {schemas : List Schema}
    (trace : GraphTrace g h schemas) (old : IndexedLevelBalance g.net boundary) :
    Nonempty (IndexedLevelBalance h.net boundary) := by
  induction trace with
  | iso same => exact ⟨same.indexed_balance old⟩
  | cons step tail ih =>
    obtain ⟨changed⟩ := step.indexed_balance old
    exact ih changed
end

/-- Actual arbitrary finite rewrites retain strict Fan/Bra and weak Cro bounds.
This statement contains no ordinary or expanded path invariant hypothesis. -/
theorem initial_trace_indexed_balance (t : Term) (target : ActualNet (Boundary t))
    (schemas : List Schema) (trace : GraphTrace (ActualNet.initial t) target schemas) :
    Nonempty (IndexedLevelBalance target.net (boundaryDepthAt 0)) := by
  obtain ⟨initial⟩ := encode_indexed_balance t 0
  exact trace.indexed_balance initial
end Lamping.AG

import Lamping.Lamping.CompositionalBalance
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V)) {boundary : B → Int}

def PathSite.frontierDepth (old : LevelBalance site.net boundary) : s.Frontier → Int :=
  Sum.elim
    (fun a => portDepth s.low (.op s.active) (old.nodes (.inr (.inl ()))) (.inr a))
    (fun a => portDepth s.high (.op s.passive) (old.nodes (.inr (.inr ()))) (.inr a))

private theorem cut_depth (old : LevelBalance site.net boundary)
    (e : Endpoint (cutFragment site.net (pathPartition s V) site.closed)) :
    endpointDepth site.net old.nodes boundary old.vertices
      ((fragmentEnd site.net.label (pathPartition s V)).invFun (.inl e))=
    endpointDepth (cutFragment site.net (pathPartition s V) site.closed)
      (fun k => old.nodes (.inl k)) (Sum.elim boundary (site.frontierDepth old))
      (fun w => old.vertices (.inl w)) e := by
  rcases e with ⟨k,p⟩ | ((b | (a|a)) | ⟨w,d⟩) <;> rfl

/-- Retain the actual outside pairing and all its boundary values. No
assumption about distinct frontier wires or absence of aliases is used. -/
def PathSite.cut_balance (old : LevelBalance site.net boundary) :
    LevelBalance (cutFragment site.net (pathPartition s V) site.closed)
      (Sum.elim boundary (site.frontierDepth old)) where
  nodes := fun k => old.nodes (.inl k)
  vertices := fun w => old.vertices (.inl w)
  wiring e := by
    let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
    have restricted := restrict_mate (site.net.wire.rename split) site.closed e
    have pulled := congrArg split.invFun restricted
    simp only [Pairing.rename,split.left_inv] at pulled
    change site.net.wire (split.invFun (.inl e))=
      split.invFun (.inl ((cutFragment site.net (pathPartition s V) site.closed).wire e)) at pulled
    have same := old.wiring (split.invFun (.inl e))
    rw [pulled] at same
    exact (cut_depth site old _).symm.trans (same.trans (cut_depth site old e))

def PathSite.internalDepth (old : LevelBalance site.net boundary) (i : Bool⊕(V×Bool)) : Int :=
  endpointDepth site.net old.nodes boundary old.vertices
    ((fragmentEnd site.net.label (pathPartition s V)).invFun (.inr i))

theorem PathSite.internal_segment_depth (old : LevelBalance site.net boundary) (i : Bool⊕(V×Bool)) :
    site.internalDepth old (site.internal i)=site.internalDepth old i := by
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have paired := congrArg split.invFun (site.wiring i)
  change split.invFun ((site.net.wire.rename split) (.inr i))=_ at paired
  simp only [Pairing.rename,split.left_inv] at paired
  change site.net.wire (split.invFun (.inr i))=split.invFun (.inr (site.internal i)) at paired
  have same := old.wiring (split.invFun (.inr i))
  rw [paired] at same
  exact same

theorem PathSite.internal_reach_depth (old : LevelBalance site.net boundary)
    {x y : Bool⊕(V×Bool)} (reach : InternalReach site.internal x y) :
    site.internalDepth old x=site.internalDepth old y := by
  induction reach with
  | refl => rfl
  | segment i => exact (site.internal_segment_depth old i).symm
  | vertex v d => rfl
  | trans _ _ first second => exact first.trans second

theorem PathSite.principal_depth (old : LevelBalance site.net boundary) :
    portDepth s.high (.op s.passive) (old.nodes (.inr (.inr ()))) (.inl ())=
      portDepth s.low (.op s.active) (old.nodes (.inr (.inl ()))) (.inl ()) :=
  (site.internal_reach_depth old (site.connected (.inl true))).symm

/-- Collapse only the subdivided principal wire for the local numeric
schema argument. Its principal equality comes from the actual connected
internal component, including every deleted transparent vertex. -/
def PathSite.left_balance (old : LevelBalance site.net boundary) :
    LevelBalance s.left (site.frontierDepth old) where
  nodes := fun n => old.nodes (.inr n)
  vertices := Empty.elim
  wiring := by
    rintro (⟨u|u,p⟩ | ((a|a) | ⟨w,d⟩))
    · cases u
      cases p with
      | inl u => cases u; exact site.principal_depth old
      | inr a => rfl
    · cases u
      cases p with
      | inl u => cases u; exact (site.principal_depth old).symm
      | inr a => rfl
    · rfl
    · rfl
    · exact nomatch w
end
end Lamping.AG

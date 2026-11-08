import Lamping.Lamping.SelectedPrincipalSite
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

/-- Actual principal ports joined by one segment belong to different nodes:
if the names coincided, compatible labels identify both principal ports and
fixed-point-freedom of the actual pairing gives a contradiction. -/
theorem principal_connection_distinct (g : Net signature N B W) (schema : Schema)
    (active passive : N)
    (activeLabel : g.label active=label schema.active schema.low)
    (passiveLabel : g.label passive=label schema.passive schema.high)
    (p : Port (g.label active).sort) (q : Port (g.label passive).sort)
    (activePrincipal : HEq p (Sum.inl () : Port (.op schema.active)))
    (passivePrincipal : HEq q (Sum.inl () : Port (.op schema.passive)))
    (connection : g.wire (.inl ⟨active,p⟩)=.inl ⟨passive,q⟩) : active≠passive := by
  intro same
  subst passive
  have kinds := congrArg Label.sort (activeLabel.symm.trans passiveLabel)
  have ops : schema.active=schema.passive := Kind.op.inj kinds
  rw [←ops] at passivePrincipal
  have ports : p=q := eq_of_heq (activePrincipal.trans passivePrincipal.symm)
  subst q
  exact g.wire.fixedPointFree _ connection

/-- The actual direct connection suffices: distinctness is derived from it,
then real carrier selection and rewiring construct the GraphStep. -/
theorem actual_principal_graph_step (g : Net signature N B W) (schema : Schema)
    (active passive : N)
    (activeLabel : g.label active=label schema.active schema.low)
    (passiveLabel : g.label passive=label schema.passive schema.high)
    (p : Port (g.label active).sort) (q : Port (g.label passive).sort)
    (activePrincipal : HEq p (Sum.inl () : Port (.op schema.active)))
    (passivePrincipal : HEq q (Sum.inl () : Port (.op schema.passive)))
    (connection : g.wire (.inl ⟨active,p⟩)=.inl ⟨passive,q⟩) :
    ∃ target : ActualNet B,GraphStep schema (ActualNet.ofNet g) target :=
  selected_principal_graph_step g schema active passive
    (principal_connection_distinct g schema active passive activeLabel passiveLabel
      p q activePrincipal passivePrincipal connection)
    activeLabel passiveLabel p q activePrincipal passivePrincipal connection
end
end Lamping.AG

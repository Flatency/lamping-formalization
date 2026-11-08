import Lamping.Lamping.PathSiteBetaAncestor
import Lamping.Lamping.GlobalPathInvariants
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
theorem PathSite.reduced_outside_incoming (root : B)
    (last : Endpoint (cutFragment site.net (pathPartition s V) site.closed))
    (role : ProperRole) (level : Nat)
    (atTerminal : AtProperRole site.reduce root
      (site.reduce.wire (AG.plugLeft _ _ last)) role level) (incoming : role.incoming) :
    AtProperRole site.net root (site.net.wire (site.outsideEnd last)) role level := by
  have wire := plugLeft_wire (cutFragment site.net (pathPartition s V) site.closed)
    s.right.net last
  change site.reduce.wire (AG.plugLeft _ _ last)=AG.plugLeft _ _
    ((cutFragment site.net (pathPartition s V) site.closed).wire last) at wire
  rw [wire] at atTerminal
  rw [site.outsideEnd_wire]
  generalize (cutFragment site.net (pathPartition s V) site.closed).wire last = endpoint at atTerminal ⊢
  rcases endpoint with ⟨node,p⟩ | ((boundary | frontier) | ⟨vertex,direction⟩)
  · cases atTerminal with
    | appCtx node p level lab port => exact AtProperRole.appCtx (g:=site.net) (root:=root) (.inl node) p level lab port
    | appFun node p level lab port => exact AtProperRole.appFun (g:=site.net) (root:=root) (.inl node) p level lab port
    | appArg node p level lab port => exact AtProperRole.appArg (g:=site.net) (root:=root) (.inl node) p level lab port
    | lamCtx node p level lab port => exact AtProperRole.lamCtx (g:=site.net) (root:=root) (.inl node) p level lab port
    | lamBody node p level lab port => exact AtProperRole.lamBody (g:=site.net) (root:=root) (.inl node) p level lab port
    | lamBind node p level lab port => exact AtProperRole.lamBind (g:=site.net) (root:=root) (.inl node) p level lab port
  · cases atTerminal
    exact False.elim incoming
  · cases atTerminal
  · cases atTerminal

theorem PathSite.reduced_incoming_kept (empty : s.right.N → False) {root : B} {terminal : Endpoint site.reduce} {role : ProperRole} {level : Nat}
    (atTerminal : AtProperRole site.reduce root terminal role level) (incoming : role.incoming) :
    ∃ (node : K) (p : Port (kept node).sort),terminal=.inl ⟨.inl node,p⟩ := by
  cases atTerminal with
  | root => exact False.elim incoming
  | appCtx node p level lab port => cases node with
    | inl node => exact ⟨node,p,rfl⟩
    | inr node => exact False.elim (empty node)
  | appFun node p level lab port => exact False.elim incoming
  | appArg node p level lab port => exact False.elim incoming
  | lamCtx node p level lab port => cases node with
    | inl node => exact ⟨node,p,rfl⟩
    | inr node => exact False.elim (empty node)
  | lamBody node p level lab port => exact False.elim incoming
  | lamBind node p level lab port => cases node with
    | inl node => exact ⟨node,p,rfl⟩
    | inr node => exact False.elim (empty node)


end
end Lamping.AG



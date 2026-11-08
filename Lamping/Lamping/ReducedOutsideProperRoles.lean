import Lamping.Lamping.ReducedOutsideRoles
import Lamping.Lamping.FlowRootPaths
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Reflect any actual retained proper endpoint, including the boundary root.
No incoming-only restriction or rooted-path reachability is needed. -/
theorem PathSite.reduced_outside_proper_role (root : B)
    (endpoint : Endpoint (cutFragment site.net (pathPartition s V) site.closed))
    (role : ProperRole) (level : Nat)
    (atTerminal : AtProperRole site.reduce root
      (AG.plugLeft _ _ endpoint) role level) :
    AtProperRole site.net root (site.outsideEnd endpoint) role level := by
  rcases endpoint with ⟨node,p⟩ | ((boundary | frontier) | ⟨vertex,direction⟩)
  · cases atTerminal with
    | appCtx node p level lab port => exact AtProperRole.appCtx (g:=site.net) (root:=root) (.inl node) p level lab port
    | appFun node p level lab port => exact AtProperRole.appFun (g:=site.net) (root:=root) (.inl node) p level lab port
    | appArg node p level lab port => exact AtProperRole.appArg (g:=site.net) (root:=root) (.inl node) p level lab port
    | lamCtx node p level lab port => exact AtProperRole.lamCtx (g:=site.net) (root:=root) (.inl node) p level lab port
    | lamBody node p level lab port => exact AtProperRole.lamBody (g:=site.net) (root:=root) (.inl node) p level lab port
    | lamBind node p level lab port => exact AtProperRole.lamBind (g:=site.net) (root:=root) (.inl node) p level lab port
  · cases atTerminal
    exact .root
  · cases atTerminal
  · cases atTerminal

end
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- With a node-free RHS every proper endpoint has an actual left-fragment
representative, including the designated boundary root. -/
theorem PathSite.reduced_proper_outside (empty : s.right.N → False)
    {root : B} {e : Endpoint site.reduce} {role : ProperRole} {level : Nat}
    (atPort : AtProperRole site.reduce root e role level) :
    ∃ first : Endpoint (cutFragment site.net (pathPartition s V) site.closed),
      e=AG.plugLeft _ s.right.net first := by
  cases atPort with
  | root => exact ⟨.inr (.inl (.inl root)),rfl⟩
  | appCtx node p level lab port
  | appFun node p level lab port
  | appArg node p level lab port
  | lamCtx node p level lab port
  | lamBody node p level lab port
  | lamBind node p level lab port =>
    cases node with
    | inl node => exact ⟨.inl ⟨node,p⟩,rfl⟩
    | inr node => exact False.elim (empty node)
end

private theorem label_port_flow (l : Label signature) (op : Op) (index : Nat)
    (p : Port l.sort) (q : Port (.op op)) (lab : l=label op index) (port : HEq p q) (base : Bool) :
    flowPort l.sort base p=flowPort (.op op) base q := by
  subst l
  exact congrArg (flowPort (.op op) base) (eq_of_heq port)

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Outgoing proper roles have positive incidence polarity independently
of the arbitrary control-node base polarities. -/
theorem AtProperRole.outgoing_flow {e : Endpoint g} {role : ProperRole} {level : Nat}
    (atPort : AtProperRole g root e role level) (outgoing : role.outgoing)
    (nodes : N → Bool) (boundary : B → Bool) (vertices : W → Bool)
    (positive : boundary root=true) : flowEndpoint g nodes boundary vertices e=true := by
  cases atPort with
  | root => exact positive
  | appCtx => exact False.elim outgoing
  | lamCtx => exact False.elim outgoing
  | lamBind => exact False.elim outgoing
  | appFun node p level lab port => exact label_port_flow (g.label node) .app level p (.inl ()) lab port (nodes node)
  | appArg node p level lab port => exact label_port_flow (g.label node) .app level p AG.appArg lab port (nodes node)
  | lamBody node p level lab port => exact label_port_flow (g.label node) .lam level p AG.lamBody lab port (nodes node)
end
end Lamping.AG

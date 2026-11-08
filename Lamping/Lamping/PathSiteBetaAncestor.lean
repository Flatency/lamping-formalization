import Lamping.Lamping.FlowRootPaths
import Lamping.Lamping.PathSiteBeta
import Lamping.Lamping.ExpandedInsertionGeometry
import Lamping.Lamping.WireRhsExcursions
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Literal old endpoint represented by one outside-cut endpoint, including
the active auxiliary frontier ports. -/
def PathSite.outsideEnd (e : Endpoint (cutFragment site.net (pathPartition s V) site.closed)) :
    Endpoint site.net := (fragmentEnd site.net.label (pathPartition s V)).invFun (.inl e)

theorem PathSite.outsideEnd_wire (e : Endpoint (cutFragment site.net (pathPartition s V) site.closed)) :
    site.net.wire (site.outsideEnd e) =
      site.outsideEnd ((cutFragment site.net (pathPartition s V) site.closed).wire e) := by
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have paired := congrArg split.invFun (restrict_mate (site.net.wire.rename split) site.closed e)
  simp only [Pairing.rename,split.left_inv] at paired
  exact paired

theorem LabelledTurn.outsideEnd {e f : Endpoint (cutFragment site.net (pathPartition s V) site.closed)}
    {a b : Context} (turn : LabelledTurn (cutFragment site.net (pathPartition s V) site.closed) e f a b) :
    LabelledTurn site.net (site.outsideEnd e) (site.outsideEnd f) a b := by
  cases turn with
  | node n p q rule => exact LabelledTurn.node (g:=site.net) (.inl n) p q rule
  | transparent w d a => exact LabelledTurn.transparent (g:=site.net) (.inl w) d a

theorem Labelling.outsideEnd {es : List (Endpoint (cutFragment site.net (pathPartition s V) site.closed))}
    {a b : Context} (labels : Labelling (cutFragment site.net (pathPartition s V) site.closed) es a b) :
    Labelling site.net (es.map site.outsideEnd) a b := by
  induction labels with
  | single e a => exact .single _ _
  | cons turn tail ih =>
    have actual := turn.outsideEnd site
    rw [←site.outsideEnd_wire] at actual
    exact .cons actual ih
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- A principal-route witness with the two active physical identifiers retained.
The complete finite route is derived from actual internal connectivity. -/
theorem PathSite.betaEdge_identified :
    ∃ edge : BetaEdge site.net,
      edge.app = .inr (.inl ()) ∧ edge.lam = .inr (.inr ()) ∧
      edge.funEnd = .inl ⟨.inr (.inl ()),.inl ()⟩ ∧
      edge.ctxEnd = .inl ⟨.inr (.inr ()),.inl ()⟩ ∧
      edge.argEnd = .inl ⟨.inr (.inl ()),.inr true⟩ ∧
      (.inl ⟨edge.lam,edge.lamBind⟩ : Endpoint site.net) = .inl ⟨.inr (.inr ()),.inr false⟩ ∧
      (.inl ⟨edge.lam,edge.lamBody⟩ : Endpoint site.net) = .inl ⟨.inr (.inr ()),.inr true⟩ ∧
      (.inl ⟨edge.app,edge.appCtx⟩ : Endpoint site.net) = .inl ⟨.inr (.inl ()),.inr false⟩ := by
  obtain ⟨es,start,finish,turns⟩ := (site.connected (.inl true)).principal_route.realize
  let edge : BetaEdge site.net := {
    app := .inr (.inl ()), lam := .inr (.inr ()), index := i
    appLabel := rfl, lamLabel := rfl
    appFun := .inl (), appCtx := .inr false, appArg := .inr true
    lamCtx := .inl (), lamBody := .inr true, lamBind := .inr false
    appFun_role := HEq.rfl, appCtx_role := HEq.rfl, appArg_role := HEq.rfl
    lamCtx_role := HEq.rfl, lamBody_role := HEq.rfl, lamBind_role := HEq.rfl
    principal := es.map site.internalEnd
    principalStart := by rw [List.head?_map,start]; rfl
    principalEnd := by
      rw [List.getLast?_map,finish]
      change some (site.internalEnd (site.internal (.inl true))) = some (site.net.wire (site.internalEnd (.inl true)))
      rw [site.internalEnd_wire]
    transparent := by
      intro e f mem
      rw [←List.map_tail,List.zip_map] at mem
      obtain ⟨⟨x,y⟩,hxy,eq⟩ := List.mem_map.mp mem
      cases eq
      obtain ⟨v,d,hx,hy⟩ := turns x y hxy
      refine ⟨.inr v,d,?_,?_⟩
      · rw [site.internalEnd_wire,hx]; rfl
      · rw [hy]; rfl }
  exact ⟨edge,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Literal ordered residual relation for beta blocks. Outside segments are
retained, context-to-body expands by the forward principal route, and
binding-to-argument expands by its physical reverse. It asserts no labels,
generation, path invariant, or semantic correctness. -/
inductive BetaPathResidual (edge : BetaEdge site.net) :
    List (PlugSegment (cutFragment site.net (pathPartition (.beta i) V) site.closed) (Schema.beta i).right.net) →
    List (Endpoint site.net) → Prop where
  | single (e) : BetaPathResidual edge [.inl e] [site.outsideEnd e]
  | outside {e f tail oldTail}
      (rest : BetaPathResidual edge (.inl f::tail) oldTail) :
      BetaPathResidual edge (.inl e::.inl f::tail) (site.outsideEnd e::oldTail)
  | context {e tail oldTail}
      (arrival : (cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e =
        .inr (.inl (.inr (.inl false))))
      (rest : BetaPathResidual edge (.inl (.inr (.inl (.inr (.inr true))))::tail) oldTail) :
      BetaPathResidual edge
        (.inl e::.inr (.inr (.inl (.inl false)))::.inl (.inr (.inl (.inr (.inr true))))::tail)
        (site.outsideEnd e::(edge.principal++oldTail))
  | binding {e tail oldTail}
      (arrival : (cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e =
        .inr (.inl (.inr (.inr false))))
      (rest : BetaPathResidual edge (.inl (.inr (.inl (.inr (.inl true))))::tail) oldTail) :
      BetaPathResidual edge
        (.inl e::.inr (.inr (.inl (.inr false)))::.inl (.inr (.inl (.inr (.inl true))))::tail)
        (site.outsideEnd e::(edge.reverseRoute++oldTail))

theorem BetaPathResidual.head {edge : BetaEdge site.net} {raw old first}
    (relation : BetaPathResidual site edge raw old) (start : raw.head?=some (.inl first)) :
    old.head?=some (site.outsideEnd first) := by
  cases relation <;>
    simp only [List.head?_cons,Option.some.injEq,Sum.inl.injEq] at start ⊢ <;> subst first <;> rfl

theorem BetaPathResidual.nonempty {edge : BetaEdge site.net} {raw old}
    (relation : BetaPathResidual site edge raw old) : old ≠ [] := by
  cases relation <;> simp

theorem BetaPathResidual.finish {edge : BetaEdge site.net} {raw old last}
    (relation : BetaPathResidual site edge raw old) (endAt : raw.getLast?=some (.inl last)) :
    old.getLast?=some (site.outsideEnd last) := by
  induction relation with
  | single e =>
    have same : e=last := Sum.inl.inj (Option.some.inj endAt)
    subst last
    rfl
  | outside rest ih =>
    have got := ih (by simpa only [List.getLast?_cons_cons] using endAt)
    simp only [List.getLast?_cons,got,Option.getD_some]
  | context arrival rest ih =>
    have got := ih (by simpa only [List.getLast?_cons_cons] using endAt)
    simp only [List.getLast?_cons,List.getLast?_append,got,Option.some_or,Option.getD_some]
  | binding arrival rest ih =>
    have got := ih (by simpa only [List.getLast?_cons_cons] using endAt)
    simp only [List.getLast?_cons,List.getLast?_append,got,Option.some_or,Option.getD_some]

theorem BetaPathResidual.reverse_occurs {edge : BetaEdge site.net} {raw old}
    (relation : BetaPathResidual site edge raw old)
    (entry : (.inr (.inr (.inl (.inr false)))) ∈ raw) : edge.ctxEnd ∈ old := by
  induction relation with
  | single e => simp at entry
  | outside rest ih =>
    have mem := ih (by simpa using entry)
    exact List.mem_cons_of_mem _ mem
  | context arrival rest ih =>
    have mem := ih (by simpa using entry)
    exact List.mem_cons_of_mem _ (List.mem_append_right _ mem)
  | binding arrival rest ih =>
    obtain ⟨tail,same⟩ := List.head?_eq_some_iff.mp edge.reverse_start
    simp [same]
/-- An occurrence-level direction predicate, proved below from actual source
flow. It says only which of the four RHS boundary entrances occur. -/
def BetaEntriesForward
    (raw : List (PlugSegment (cutFragment site.net (pathPartition (.beta i) V) site.closed) (Schema.beta i).right.net)) : Prop :=
  ∀ f, (.inr (.inr (.inl f))) ∈ raw → f=.inl false ∨ f=.inr false

theorem WireExcursions.beta_residual {raw a b}
    (path : WireExcursions (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net raw a b) (edge : BetaEdge site.net)
    (directions : BetaEntriesForward site raw) :
    ∃ old, BetaPathResidual site edge raw old := by
  induction path with
  | single e a => exact ⟨_,.single e⟩
  | @outside e f tail a b d turn rest ih =>
    obtain ⟨old,relation⟩ := ih (by
      intro x mem
      exact directions x (List.mem_cons_of_mem _ mem))
    exact ⟨_,.outside relation⟩
  | @through e f tail a b arrival rest ih =>
    have entry := directions f (by simp)
    have tailDirection : BetaEntriesForward site
        (.inl (.inr (.inl (.inr (wireBoundaryMate (Schema.beta i).right.net f))))::tail) := by
      intro x mem
      exact directions x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem))
    obtain ⟨old,relation⟩ := ih tailDirection
    rcases entry with entry | entry
    · subst f
      exact ⟨_,.context arrival relation⟩
    · subst f
      exact ⟨_,.binding arrival relation⟩

/-- Direction is derived from actual labelled occurrences, rather than assumed
of the path being reflected. The source flow constructs the new glue values. -/
theorem WireExcursions.beta_entries_forward {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPolarity : boundary root=true)
    {raw a b} (path : WireExcursions (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net raw a b)
    (rooted : (raw.map (plugEnd _ _)).head?=some (.inr (.inl root))) :
    BetaEntriesForward site raw := by
  have labels := (path.labelling _ _).actual _ _
  intro f mem
  have actualMem : (plugEnd _ _) (.inr (.inr (.inl f))) ∈ raw.map (plugEnd _ _) :=
    List.mem_map_of_mem mem
  rcases f with b | b <;> cases b
  · exact Or.inl rfl
  · exact False.elim (site.beta_no_argument_entry flow root labels rooted rootPolarity actualMem)
  · exact Or.inr rfl
  · exact False.elim (site.beta_no_body_entry flow root labels rooted rootPolarity actualMem)
end
end Lamping.AG

import Lamping.Lamping.BetaDetourBlocks
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

private theorem outside_turn {x y : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)}
    {a b : Context} (turn : PlugTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed) (Schema.beta i).right.net
      (.inl x) (.inl y) a b) :
    LabelledTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed) x y a b := by
  cases turn with
  | left localTurn => exact localTurn

private theorem enter_context {x : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)}
    {y : Endpoint (Schema.beta i).right.net} {a b : Context}
    (turn : PlugTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed) (Schema.beta i).right.net (.inl x) (.inr y) a b) : a=b := by
  cases turn
  rfl

private theorem leave_context {x : Endpoint (Schema.beta i).right.net}
    {y : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)} {a b : Context}
    (turn : PlugTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed) (Schema.beta i).right.net (.inr x) (.inl y) a b) : a=b := by
  cases turn
  rfl

private theorem context_stream {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {e : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)} {oldTail : List (Endpoint site.net)}
    {a b : Context} {count : Nat}
    (arrival : (cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e = .inr (.inl (.inr (.inl false))))
    (head : oldTail.head?=some (site.outsideEnd (.inr (.inl (.inr (.inr true))))))
    (rest : BetaDetourBlocks site.net oldTail a b count) :
    BetaDetourBlocks site.net (site.outsideEnd e::(edge.principal++oldTail)) a b count := by
  have arrives : site.net.wire (site.outsideEnd e)=.inl ⟨edge.app,edge.appCtx⟩ := by
    rw [site.outsideEnd_wire,arrival,geometry.appCtx]
    rfl
  have principal : Labelling site.net (site.outsideEnd e::edge.principal) a a := by
    obtain ⟨tail,same⟩ := List.head?_eq_some_iff.mp edge.principalStart
    have labels := edge.principal_labeling a
    rw [same] at labels ⊢
    apply Labelling.cons _ labels
    rw [arrives]
    exact edge.app_fun_turn a
  have finish : (site.outsideEnd e::edge.principal).getLast?=some (site.net.wire edge.ctxEnd) := by
    simp only [List.getLast?_cons,edge.principalEnd,Option.getD_some,BetaEdge.ctxEnd]
  have starts : oldTail.head?=some (.inl ⟨edge.lam,edge.lamBody⟩) := by rw [geometry.body]; exact head
  exact rest.splice_ordinary site.net principal finish starts (by
    simpa only [Pairing.involutive] using edge.lam_body_turn a)

/-- The same actual semantic ancestor admits a genuine finite paired-block
stream. Context shortcuts contribute only ordinary turns; each binding
shortcut contributes exactly one counted backward block. -/
theorem BetaPathResidual.detour_blocks {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {raw old} (relation : BetaPathResidual site edge raw old) {a b : Context}
    (labels : PlugLabelling (cutFragment site.net (pathPartition (.beta i) V) site.closed) (Schema.beta i).right.net raw a b) :
    ∃ count, BetaDetourBlocks site.net old a b count := by
  induction relation generalizing a b with
  | single e => cases labels; exact ⟨0,.single _ _⟩
  | @outside e f tail oldTail relation ih =>
    cases labels with
    | cons turn after =>
      obtain ⟨count,rest⟩ := ih after
      have localTurn := (outside_turn site turn).outsideEnd site
      rw [←site.outsideEnd_wire] at localTurn
      obtain ⟨xs,same⟩ := List.head?_eq_some_iff.mp (relation.head site rfl)
      rw [same] at rest ⊢
      exact ⟨count,.ordinary localTurn rest⟩
  | context arrival relation ih =>
    cases labels with
    | cons turn after =>
      cases enter_context site turn
      cases after with
      | cons turn after =>
        cases leave_context site turn
        obtain ⟨count,rest⟩ := ih after
        exact ⟨count,context_stream site geometry arrival (relation.head site rfl) rest⟩
  | @binding e tail oldTail arrival relation ih =>
    cases labels with
    | cons turn after =>
      cases enter_context site turn
      cases after with
      | cons turn after =>
        cases leave_context site turn
        obtain ⟨count,rest⟩ := ih after
        refine ⟨count+1,.backward edge (site.outsideEnd e) ?_ ?_ rest⟩
        · rw [site.outsideEnd_wire,arrival,geometry.binding]
          rfl
        · rw [geometry.argument]
          exact relation.head site rfl
end
end Lamping.AG

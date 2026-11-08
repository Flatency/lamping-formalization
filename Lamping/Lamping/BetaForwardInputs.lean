import Lamping.Lamping.InitialPathConstruction
import Lamping.Lamping.BetaProperAncestors
import Lamping.Lamping.BetaResidualContraction
import Lamping.Lamping.BetaDetourReflection
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

private theorem left_turn {x y : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)}
    {a b : Context} (turn : PlugTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net (.inl x) (.inl y) a b) :
    LabelledTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed) x y a b := by
  cases turn with | left actual => exact actual

private theorem entry_equal {x : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)}
    {y : Endpoint (Schema.beta i).right.net} {a b : Context}
    (turn : PlugTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net (.inl x) (.inr y) a b) : a=b := by cases turn; rfl
private theorem exit_equal {x : Endpoint (Schema.beta i).right.net}
    {y : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)} {a b : Context}
    (turn : PlugTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net (.inr x) (.inl y) a b) : a=b := by cases turn; rfl

private theorem context_ordinary {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {e : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)} {oldTail}
    {a b : Context}
    (arrival : (cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e = .inr (.inl (.inr (.inl false))))
    (head : oldTail.head?=some (site.outsideEnd (.inr (.inl (.inr (.inr true))))))
    (rest : Labelling site.net oldTail a b) :
    Labelling site.net (site.outsideEnd e::(edge.principal++oldTail)) a b := by
  have arrives : site.net.wire (site.outsideEnd e)=.inl ⟨edge.app,edge.appCtx⟩ := by
    rw [site.outsideEnd_wire,arrival,geometry.appCtx]; rfl
  have principal : Labelling site.net (site.outsideEnd e::edge.principal) a a := by
    obtain ⟨tail,same⟩ := List.head?_eq_some_iff.mp edge.principalStart
    have labels := edge.principal_labeling a
    rw [same] at labels ⊢
    apply Labelling.cons _ labels
    rw [arrives]
    exact edge.app_fun_turn a
  have finish : (site.outsideEnd e::edge.principal).getLast?=some (site.net.wire edge.ctxEnd) := by
    simp only [List.getLast?_cons,edge.principalEnd,Option.getD_some,BetaEdge.ctxEnd]
  apply principal.append_seam rest
  intro x y atX atY
  have hx : x=site.net.wire edge.ctxEnd := Option.some.inj (atX.symm.trans finish)
  have hy : y=.inl ⟨edge.lam,edge.lamBody⟩ := by
    rw [geometry.body]
    exact Option.some.inj (atY.symm.trans head)
  rw [hx,hy,Pairing.involutive]
  exact edge.lam_body_turn a

/-- No binding-side entrance is a physical restriction on the original raw
path. Under it every expanded ancestor block is actually ordinary. -/
theorem BetaPathResidual.ordinary_without_binding {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) {raw old} (relation : BetaPathResidual site edge raw old)
    {a b : Context}
    (labels : PlugLabelling (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net raw a b)
    (noBinding : (.inr (.inr (.inl (.inr false)))) ∉ raw) : Labelling site.net old a b := by
  induction relation generalizing a b with
  | single e => cases labels; exact .single _ _
  | @outside e f tail oldTail relation ih =>
    cases labels with
    | cons turn after =>
      have rest := ih after (by intro mem; exact noBinding (List.mem_cons_of_mem _ mem))
      have actual := (left_turn site turn).outsideEnd site
      rw [←site.outsideEnd_wire] at actual
      obtain ⟨xs,same⟩ := List.head?_eq_some_iff.mp (relation.head site rfl)
      rw [same] at rest ⊢
      exact .cons actual rest
  | context arrival relation ih =>
    cases labels with
    | cons enter after =>
      cases entry_equal site enter
      cases after with
      | cons leave after =>
        cases exit_equal site leave
        exact context_ordinary site geometry arrival (relation.head site rfl)
          (ih after (by intro mem; exact noBinding (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem))))
  | binding arrival relation ih => exact False.elim (noBinding (by simp))

/-- General proper-source arbitrary-input existence for the beta paths having
no physical binding shortcut. Source and target may both be non-root ports;
context shortcuts may occur any finite number of times. -/
theorem PathSite.beta_no_binding_proper_inputs {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPositive : boundary root=true)
    (independence : Independence site.net root)
    {es : List (Endpoint site.reduce)} {a b : Context} {first last sr tr m n}
    (labels : Labelling site.reduce es a b)
    (head : es.head?=some first) (finish : es.getLast?=some (site.reduce.wire last))
    (source : AtProperRole site.reduce root first sr m) (outgoing : sr.outgoing)
    (target : AtProperRole site.reduce root last tr n) (incoming : tr.incoming)
    (noBinding : (.inr (.inr (.inl (.inr false)))) ∉ es.map (plugEnd _ _).invFun) :
    ∀ replacement, ∃ output, Labelling site.reduce es (a.replace m replacement) output := by
  obtain ⟨edge,old,oldFirst,oldLast,geometry,relation,_,_,oldHead,oldFinish,oldSource,oldTarget⟩ :=
    site.beta_proper_ancestor flow root rootPositive labels head finish source outgoing target
  have ordinary := relation.ordinary_without_binding site geometry (labels.plug_decomposition _ _) noBinding
  have forward := ordinary.forward_of_flow flow (by
    intro e atHead
    rw [oldHead] at atHead
    cases Option.some.inj atHead
    exact oldSource.outgoing_flow outgoing flow.nodes boundary flow.vertices rootPositive)
  have total := (independence old oldFirst oldLast sr tr m n a b oldHead oldFinish oldSource outgoing
    oldTarget incoming forward ordinary).1
  intro replacement
  obtain ⟨output,changed⟩ := total replacement
  exact ⟨output,relation.contract_actual site geometry labels changed.expanded⟩
end
end Lamping.AG



import Lamping.Lamping.InteriorSourceBlockEndpoints
import Lamping.Lamping.BetaCanonicalComparison
import Lamping.Lamping.FixedBetaDetourBlocks
import Lamping.Lamping.BetaChainEvaluatedResiduals
import Lamping.Lamping.DirectedPhysicalLabelEvaluation
import Lamping.Lamping.ExpandedIndependence

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem window_role_endpoint {N B W : Type}
    [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {T : Type} {canonical : T} {n m : N}
    {p : Port (g.label n).sort} {q : Port (g.label m).sort}
    (nodes : n=m) (left : HEq p canonical) (right : HEq q canonical) :
    (.inl ⟨n,p⟩ : Endpoint g)=.inl ⟨m,q⟩ := by
  subst m
  cases eq_of_heq (left.trans right.symm)
  rfl

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B]
variable [FiniteNames W] [FiniteNames V] {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- The actual source atom after a selected bar starts at this fixed site's
ARG/BODY departure. Only port witnesses are transferred; the supplied beta
edge and its complete principal route stay fixed. -/
theorem actual_window_atom_departure {source : LTerm} {root : B}
    (matching : Matches site.net root source.erase)
    (edge : BetaEdge site.net) (geometry : SiteBetaGeometry site edge)
    (selection : SourceEdgeSelection (initLabels source.erase) site.net root)
    {n : Nat} {lk rk : Bool}
    (windowGeometry : InteriorSourceBlock.WindowGeometry (initLabels source.erase)
      (site.betaSyntaxFiber root source.erase) n lk rk) :
    ∃ atomTail, selection.atomWord n=
      site.outsideEnd (.inr (.inl (.inr
        (if lk then Sum.inr true else Sum.inl true))))::atomTail := by
  let basis := initLabels source.erase
  have initial : INIT basis := init_is_INIT _
  have localMatching : Matches site.net root basis.erase := by
    simpa only [basis,erase_initLabels] using matching
  let redex := windowGeometry.left
  have selected : SelectedDegree basis (site.betaSyntaxFiber root basis.erase) redex.degree := by
    refine ⟨redex.position,?_,?_⟩
    · simpa only [basis,erase_initLabels] using redex.member
    · change ((initLabels source.erase).subterm redex.position).bind LTerm.degree=some redex.degree
      rw [redex.lookup]
      rfl
  obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup basis redex.lookup [] .external
  have canonicalMember : (⟨redex.degree,.appFn redex.beta,.lamContext redex.degree⟩ : SourceEdge)
      ∈sourceEdges [] .external basis :=
    occurrence.edges_subset _ (by simp [sourceEdges])
  have route : SourceRoute (sourceEdges [] .external basis)
      (.appFn redex.beta) redex.degree (.lamContext redex.degree) := by
    obtain ⟨a,atomic⟩ := selected.atomic initial
    simpa only [atomic] using (SourceRoute.atom canonicalMember atomic)
  obtain ⟨beta,app,lam,allPorts⟩ := site.selected_beta_source_ports initial localMatching
  obtain ⟨_,ports⟩ := allPorts selected route
  have edgeApp : edge.app=.inr (.inl ()) :=
    congrArg Sigma.fst (Sum.inl.inj geometry.argument)
  have edgeLam : edge.lam=.inr (.inr ()) :=
    congrArg Sigma.fst (Sum.inl.inj geometry.body)
  let cell : {e : SourceEdge //e∈sourceEdges [] .external basis} :=
    ⟨windowGeometry.edge,windowGeometry.member⟩
  let fragment := (selection.chosen cell).2
  have word := selection.atomWord_cell initial cell windowGeometry.atomic
  have realizes := fragment.fromRealizes
  rw [windowGeometry.departure] at realizes
  have first : fragment.fromEndpoint=site.outsideEnd (.inr (.inl (.inr
      (if lk then Sum.inr true else Sum.inl true)))) := by
    cases lk with
    | false =>
      have roles := window_role_endpoint (g:=site.net) (app.trans edgeApp.symm)
        beta.appArg_role edge.appArg_role
      have actual := ports.appArgument
      change SourcePortRealizes basis site.net root (.appArg redex.beta)
        (.inl ⟨beta.app,beta.appArg⟩) at actual
      rw [roles] at actual
      have eq := realizes.unique initial localMatching actual
      exact eq.trans (by change edge.argEnd=_; rw [geometry.argument]; rfl)
    | true =>
      have roles := window_role_endpoint (g:=site.net) (lam.trans edgeLam.symm)
        beta.lamBody_role edge.lamBody_role
      have actual := ports.lamBody
      rw [roles] at actual
      have eq := realizes.unique initial localMatching actual
      exact eq.trans (by rw [geometry.body]; rfl)
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp fragment.start
  exact ⟨tail,word.trans (split.trans (congrArg (fun e=>e::tail) first))⟩

local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed

/-- A real literal window gives an occurrence cut inside the SAME supplied
evaluated residual, at its complete old physical prefix length. Every
assignment split retains the caller's original input and output contexts. -/
theorem EvaluatedChainResiduals.interior_window_raw_cut
    {source target localTarget : LTerm} {root : B}
    (matching : Matches site.net root source.erase)
    (edge : BetaEdge site.net) (geometry : SiteBetaGeometry site edge)
    (selection : SourceEdgeSelection (initLabels source.erase) site.net root)
    {ps : List Path} {marked : Marked}
    (old : Marked.RelativeOldHistory (site.betaSyntaxFiber root source.erase) ps
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    {start : Path} {es : List Path} (chain : PrerequisiteChain target start es)
    (out : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain)
    (member : {p : Path //p∈es}) {n : Nat} {lk rk : Bool}
    {pre post : List Letter} {dl dr : Labelled.Label}
    (window : (out.node member).label.letters=
      pre++[InteriorSourceBlock.bar lk dl,.atom n,InteriorSourceBlock.bar rk dr]++post) :
    let evalLetters := fun xs : List Letter => xs.flatMap
      (Letter.sourceWord selection.atomWord edge.principal edge.reverseRoute)
    let oldPre := evalLetters (pre++[InteriorSourceBlock.bar lk dl])
    let oldPost := evalLetters (InteriorSourceBlock.bar rk dr::post)
    let endpoint : Endpoint cut := .inr (.inl (.inr
      (if lk then Sum.inr true else Sum.inl true)))
    let raw := (targetSelection (actualChainPosition chain member)).fragment.segments.map
      (plugEnd (cut).label ((Schema.beta i).right.net).label).invFun
    let wholeOld := selection.evalLabel edge (out.node member).label
    ∃ atomTail, selection.atomWord n=site.outsideEnd endpoint::atomTail ∧
      ∃ cutAt : BetaResidualOccurrence site edge raw wholeOld endpoint oldPre.length,
        cutAt.oldBefore=oldPre ∧cutAt.oldAfter=atomTail++oldPost ∧
        ∀ {a b : Context}, PlugLabelling cut (Schema.beta i).right.net raw a b →
          ∃ seam leftCount rightCount,
            FixedBetaDetourBlocks edge (cutAt.oldBefore++[site.outsideEnd endpoint]) a seam leftCount ∧
            FixedBetaDetourBlocks edge (site.outsideEnd endpoint::cutAt.oldAfter) seam b rightCount := by
  dsimp only
  obtain ⟨ctx,finish,route⟩ := InteriorSourceBlock.actual_old_node_route old localHistory (out.lookup member)
  obtain ⟨windowGeometry⟩ := InteriorSourceBlock.route_window_geometry (init_is_INIT _) route window
  obtain ⟨atomTail,atomEq⟩ := actual_window_atom_departure site matching edge geometry selection windowGeometry
  have assembly := selection.interpret_read_label edge true (out.node member).label
  simp only [interpretReadLetters,Label.readLetters,orientPhysical,if_true] at assembly
  have split : selection.evalLabel edge (out.node member).label=
      (pre++[InteriorSourceBlock.bar lk dl]).flatMap
        (Letter.sourceWord selection.atomWord edge.principal edge.reverseRoute) ++
      site.outsideEnd (.inr (.inl (.inr (if lk then Sum.inr true else Sum.inl true))))::
        (atomTail++(InteriorSourceBlock.bar rk dr::post).flatMap
          (Letter.sourceWord selection.atomWord edge.principal edge.reverseRoute)) := by
    rw [←assembly,window]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,Letter.sourceWord,
      atomEq,List.append_nil,List.nil_append,List.append_assoc,List.cons_append]
    rfl
  obtain ⟨cutAt,beforeEq,afterEq⟩ := (out.residual member).split_outside site geometry _ _ _ split
  refine ⟨atomTail,atomEq,cutAt,beforeEq,afterEq,?_⟩
  intro a b labels
  have actual := labels.actual cut (Schema.beta i).right.net
  rw [cutAt.raw_eq,List.map_append,List.map_cons] at actual
  obtain ⟨seam,left,right⟩ := actual.split_segment
  have leftRaw := left.plug_decomposition cut (Schema.beta i).right.net
  have rightRaw := right.plug_decomposition cut (Schema.beta i).right.net
  have inverse : ∀ e : PlugSegment cut (Schema.beta i).right.net,
      (plugEnd (cut).label ((Schema.beta i).right.net).label).invFun
        ((plugEnd (cut).label ((Schema.beta i).right.net).label) e)=e :=
    (plugEnd (cut).label ((Schema.beta i).right.net).label).left_inv
  simp only [List.map_append,List.map_cons,List.map_nil,List.map_map,
    Function.comp_def,inverse,List.map_id_fun'] at leftRaw rightRaw
  obtain ⟨leftCount,leftStream⟩ := cutAt.prefixResidual.fixed_detour_blocks site geometry leftRaw
  obtain ⟨rightCount,rightStream⟩ := cutAt.suffixResidual.fixed_detour_blocks site geometry rightRaw
  exact ⟨seam,leftCount,rightCount,leftStream,rightStream⟩
end
end Lamping.AG

#print axioms Lamping.AG.actual_window_atom_departure
#print axioms Lamping.AG.EvaluatedChainResiduals.interior_window_raw_cut

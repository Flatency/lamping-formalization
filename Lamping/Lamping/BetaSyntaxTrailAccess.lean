import Lamping.Lamping.BetaSyntaxTrailContraction
import Lamping.Lamping.FlowRootPaths

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm} {edge : BetaEdge g}

/-- The last header is taken from the actual finite image, not reconstructed
from its endpoint. -/
theorem SyntaxTrailImage.terminal_route
    (image : SyntaxTrailImage original root edge env start current p sub finish es) :
    ∃ localStart localEdges,SourceRouteImage original root edge localStart sub.label finish localEdges := by
  induction image with
  | var route | lam route | app route => exact ⟨_,_,route⟩
  | fn _ _ ih | arg _ _ ih | body _ _ ih => exact ih

private theorem app_ports
    (actual : SourcePortRealizes original g root (.appContext origin) endpoint) :
    ∃ (node : N) (port : Port (g.label node).sort),endpoint=.inl ⟨node,port⟩ ∧
      (g.label node).sort=.op .app ∧HEq port appCtx := by
  cases actual with
  | appContext _ _ _ sort role _ => exact ⟨_,_,rfl,sort,role⟩
  | departure _ role => cases role
private theorem lam_ports
    (actual : SourcePortRealizes original g root (.lamContext origin) endpoint) :
    ∃ (node : N) (port : Port (g.label node).sort),endpoint=.inl ⟨node,port⟩ ∧
      (g.label node).sort=.op .lam ∧HEq port (Sum.inl () : Port (.op .lam)) := by
  cases actual with
  | lamContext _ _ _ sort role _ => exact ⟨_,_,rfl,sort,role⟩
  | departure _ role => cases role
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
variable {root : B} {original target : LTerm} {ps : List Path} {marked : Marked}

theorem PhysicalSyntaxTrail.complete_app_terminal
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (history : History ps original target)
    {edge : BetaEdge site.net} {p stamp fn arg finish}
    (trail : PhysicalSyntaxTrail original root edge [] .external target p (.app stamp fn arg) finish) :
    ∃ (node : K) (ctx : Port (kept node).sort),trail.toEndpoint=.inl ⟨.inl node,ctx⟩ ∧
      (kept node).sort=.op .app ∧HEq ctx appCtx := by
  obtain ⟨n,_last,finishEq⟩ := trail.image.app_finish
  let endpoint : Endpoint site.net := trail.toEndpoint
  have actual : SourcePortRealizes original site.net root finish endpoint := trail.toRealizes
  rw [finishEq] at actual
  obtain ⟨node,ctx,endEq,sort,role⟩ := app_ports actual
  obtain ⟨start,edges,route⟩ := trail.image.terminal_route
  rw [finishEq] at route
  have actual' : SourcePortRealizes original site.net root (.appContext (.atom n)) (.inl ⟨node,ctx⟩) := by
    rw [←endEq]; exact actual
  obtain ⟨node,rfl⟩ := site.complete_app_context_kept initial matching flow positive relative normal history
    route trail.lookup actual'
  exact ⟨node,ctx,endEq,sort,role⟩

theorem PhysicalSyntaxTrail.complete_lambda_terminal
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (history : History ps original target)
    {edge : BetaEdge site.net} {p stamp body finish}
    (trail : PhysicalSyntaxTrail original root edge [] .external target p (.lam stamp body) finish) :
    ∃ (node : K) (ctx : Port (kept node).sort),trail.toEndpoint=.inl ⟨.inl node,ctx⟩ ∧
      (kept node).sort=.op .lam ∧HEq ctx (Sum.inl () : Port (.op .lam)) := by
  obtain ⟨n,_last,finishEq⟩ := trail.image.lam_finish
  let endpoint : Endpoint site.net := trail.toEndpoint
  have actual : SourcePortRealizes original site.net root finish endpoint := trail.toRealizes
  rw [finishEq] at actual
  obtain ⟨node,ctx,endEq,sort,role⟩ := lam_ports actual
  obtain ⟨start,edges,route⟩ := trail.image.terminal_route
  rw [finishEq] at route
  have actual' : SourcePortRealizes original site.net root (.lamContext (.atom n)) (.inl ⟨node,ctx⟩) := by
    rw [←endEq]; exact actual
  obtain ⟨node,rfl⟩ := site.complete_lambda_context_kept initial matching flow positive relative normal history
    route trail.lookup actual'
  exact ⟨node,ctx,endEq,sort,role⟩

private theorem raw_head {edge : BetaEdge site.net} {raw old}
    (relation : BetaPathResidual site edge raw old) : ∃ first : Endpoint cut,raw.head?=some (.inl first) := by
  cases relation <;> exact ⟨_,rfl⟩

/-- The actual contraction becomes a genuine root access once its retained
proper terminal is identified. Labels construct the new forward path;
neither a target access nor a target path shape is supplied. -/
theorem PhysicalSyntaxTrail.beta_contract_access
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (history : History ps original target)
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {p sub finish} (trail : PhysicalSyntaxTrail original root edge [] .external target p sub finish)
    {a b : Context} (labels : ExpandedLabelling site.net trail.edges a b)
    (node : K) (port : Port (kept node).sort) (kind : AccessKind)
    (terminal : trail.toEndpoint=.inl ⟨.inl node,port⟩) (proper : portKind (kept node).sort port=some kind) :
    ∃ access : RootAccess site.reduce root,
      BetaPathResidual site edge (access.val.map (plugEnd _ _).invFun) trail.edges ∧
      Labelling site.reduce access.val a b ∧accessWord site.reduce access.val=p ∧
      accessKind site.reduce access.val=some kind ∧
      access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩)) := by
  obtain ⟨raw,residual,actual,word⟩ := trail.image.beta_contract_word site initial matching flow positive
    relative normal history geometry [] (by simp [LTerm.subterm]) labels (.inr (.inl (.inl root))) trail.rooted
  obtain ⟨first,rawHead⟩ := raw_head site residual
  have firstEq : first=(.inr (.inl (.inl root)) : Endpoint cut) :=
    site.outsideEnd_injective (Option.some.inj ((residual.head site rawHead).symm.trans trail.rooted))
  rw [firstEq] at rawHead
  let es := raw.map (plugEnd (cut).label (Schema.beta i).right.net.label)
  have rooted : es.head?=some (.inr (.inl root)) := by rw [List.head?_map,rawHead]; rfl
  have oldFinish : trail.edges.getLast?=some (site.outsideEnd ((cut).wire (.inl ⟨node,port⟩))) := by
    rw [←site.outsideEnd_wire (.inl ⟨node,port⟩)]
    change trail.edges.getLast?=some (site.net.wire (.inl ⟨.inl node,port⟩))
    rw [←terminal]
    exact trail.last
  have rawFinish := residual.reflect_finish site _ oldFinish
  have finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩)) := by
    rw [List.getLast?_map,rawFinish]
    exact congrArg some (plugLeft_wire _ _ _).symm
  have kindEq : accessKind site.reduce es=some kind := by
    rw [accessKind,finish,Option.bind_some,Pairing.involutive]
    exact proper
  have ordinary : Labelling site.reduce es a b := actual.actual _ _
  obtain ⟨changed⟩ := site.reduce_flowBalance flow
  have forward := ordinary.root_forward_of_flow changed root rooted positive
  let access : RootAccess site.reduce root := ⟨es,⟨⟨⟨a,b,ordinary⟩,forward⟩,rooted,⟨kind,kindEq⟩⟩⟩
  have inverseMap : es.map (plugEnd (cut).label (Schema.beta i).right.net.label).invFun=raw := by
    simp only [es,List.map_map,Function.comp_def,(plugEnd _ _).left_inv]
    exact congrFun List.map_id_fun raw
  exact ⟨access,by change BetaPathResidual site edge (es.map _) _; rw [inverseMap]; exact residual,
    ordinary,word,kindEq,finish⟩
end
end Lamping.AG

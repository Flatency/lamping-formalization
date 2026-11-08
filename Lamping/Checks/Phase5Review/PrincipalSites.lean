import Lamping.Lamping.PrincipalConnectionDistinct
import Lamping.Lamping.LabelledControlCorridors
import Lamping.Lamping.ControlInitialObstruction
import Lamping.Lamping.PrincipalCorridorExtraction
import Lamping.Lamping.InitialFullIndependence
import Lamping.Lamping.RootBindingSuffixUniqueness
import Lamping.Lamping.RootNormalFormReflection
import Lamping.Lamping.ConditionalNormalFormReflection
import Lamping.Lamping.InternalControlCorridorStep
import Lamping.Lamping.CorridorOccurrenceSeams
import Lamping.Lamping.MatchingRedexConnection
import Lamping.Lamping.InitialMatching
import Lamping.Lamping.BetaEncodingIso
import Lamping.Lamping.GraphFlowPreservation
import Lamping.Checks.Paths
namespace Lamping.Checks.Phase5Review.PrincipalSites
open AG Graph
abbrev graph := leftNet .fan .fan 2 2

def swap : Bij (Unit⊕Unit) (Unit⊕Unit) where
  toFun := fun x => match x with | .inl _ => .inr () | .inr _ => .inl ()
  invFun := fun x => match x with | .inl _ => .inr () | .inr _ => .inl ()
  left_inv := by rintro (u|u) <;> cases u <;> rfl
  right_inv := by rintro (u|u) <;> cases u <;> rfl

private theorem compatible : ∀ n,graph.label (swap n)=graph.label n := by
  rintro (u|u) <;> cases u <;> rfl

noncomputable def renamed := graph.reindex graph.label swap (Bij.refl Empty) compatible
noncomputable def actualIso := graph.reindexIso graph.label swap (Bij.refl Empty) compatible

theorem actual_node_swap : actualIso.nodes (Sum.inl ())=Sum.inr () := rfl

theorem actual_boundary_wire_conjugation :
    renamed.wire (.inr (.inl (.inl false)))=.inl ⟨Sum.inr (),fanO⟩ := by
  apply actualIso.ends.injective
  change actualIso.ends ((graph.reindex graph.label swap (Bij.refl Empty) compatible).wire (.inr (.inl (.inl false)))) = _
  rw [actualIso.wiring]
  rfl

theorem actual_direct_cancellation :
    ∃ target : ActualNet (Bool⊕Bool),GraphStep (.fanCancel 2) (ActualNet.ofNet graph) target :=
  actual_principal_graph_step graph (.fanCancel 2) (Sum.inl ()) (Sum.inr ()) rfl rfl
    (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl

theorem actual_direct_not_normal : ¬GraphNormal (ActualNet.ofNet graph) := by
  obtain ⟨target,step⟩ := actual_direct_cancellation
  exact fun normal => normal _ target step

theorem wrong_beta_index_is_not_a_match :
    (leftNet .app .lam 0 1).label (Sum.inr ())≠label .lam 0 := by
  intro equal
  have wrong := congrArg Label.index equal
  cases wrong

theorem same_principal_cannot_connect {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (node : N) (p : Port (g.label node).sort) :
    g.wire (.inl ⟨node,p⟩)≠.inl ⟨node,p⟩ := g.wire.fixedPointFree _

#print axioms actual_boundary_wire_conjugation
#print axioms actual_direct_cancellation
#print axioms actual_direct_not_normal
#print axioms wrong_beta_index_is_not_a_match
#print axioms same_principal_cannot_connect

/-- The original encoded beta occurrence really contains a W; this calls the
arbitrary-carrier construction, rather than the old direct-wire Site bridge. -/
def actualOneWCorridor : TransparentCorridor actualBetaSite.net where
  first := ⟨Checks.Paths.encodedBetaOccurrence.app,Checks.Paths.encodedBetaOccurrence.appFun⟩
  last := ⟨Checks.Paths.encodedBetaOccurrence.lam,Checks.Paths.encodedBetaOccurrence.lamCtx⟩
  edges := Checks.Paths.encodedBetaOccurrence.principal
  start := Checks.Paths.encodedBetaOccurrence.principalStart
  finish := Checks.Paths.encodedBetaOccurrence.principalEnd
  transparent := Checks.Paths.encodedBetaOccurrence.transparent

theorem actual_one_w_is_selected : actualOneWCorridor.vertex (Sum.inr ()) := by
  exact ⟨true,by simp [actualOneWCorridor,Checks.Paths.encodedBetaOccurrence]⟩

theorem actual_unrelated_w_is_not_selected : ¬actualOneWCorridor.vertex (Sum.inl (Sum.inr ())) := by
  rintro ⟨d,member⟩
  change (Sum.inr (Sum.inr (Sum.inl (Sum.inr ()),d)) : Endpoint actualBetaSite.net)∈
    [Sum.inl ⟨Sum.inr (Sum.inl ()),Sum.inl ()⟩,Sum.inr (Sum.inr (Sum.inr (),true))] at member
  simp at member

theorem actual_one_w_beta_step :
    ∃ target : ActualNet (Boundary identityApp),GraphStep (.beta 0) (ActualNet.ofNet actualBetaSite.net) target := by
  exact physical_corridor_graph_step actualBetaSite.net (.beta 0) actualOneWCorridor
    (.inr (.inl ())) (.inr (.inr ())) (by intro h; cases h) rfl rfl
    (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl

#print axioms actual_one_w_is_selected
#print axioms actual_unrelated_w_is_not_selected
#print axioms actual_one_w_beta_step

/-- Initial structural flow supplies distinctness automatically even on the
subdivided principal corridor, with no caller distinct-node certificate. -/
theorem actual_one_w_beta_step_from_initial_flow :
    ∃ target : ActualNet (Boundary identityApp),GraphStep (.beta 0) (ActualNet.ofNet actualBetaSite.net) target := by
  obtain ⟨initial⟩ := encode_flowBalance identityApp 0
  have physicalFlow := betaEncodingIso.flowBalance initial
  exact physical_corridor_graph_step_of_flow actualBetaSite.net (.beta 0) physicalFlow actualOneWCorridor
    (.inr (.inl ())) (.inr (.inr ())) rfl rfl
    (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl

#print axioms actual_one_w_beta_step_from_initial_flow

abbrev reversedGraph := leftNet .cro .cro 3 1

def reversedFlow : FlowBalance reversedGraph (fun | .inl _ => true | .inr _ => false) where
  nodes := fun | .inl _ => true | .inr _ => false
  vertices := Empty.elim
  wiring := by
    rintro (⟨(u|u),p⟩ | ((u|u) | ⟨w,d⟩))
    · cases u; cases p with | inl u => cases u; rfl | inr u => cases u; rfl
    · cases u; cases p with | inl u => cases u; rfl | inr u => cases u; rfl
    · cases u; rfl
    · cases u; rfl
    · exact nomatch w

def reversedCorridor : TransparentCorridor reversedGraph where
  first := ⟨.inl (),.inl ()⟩
  last := ⟨.inr (),.inl ()⟩
  edges := [.inl ⟨.inl (),.inl ()⟩]
  start := rfl
  finish := rfl
  transparent := by intro e f member; cases member

/-- The lower active control is physically second; the real corridor is
reversed by the public constructor, rather than changing the graph labels. -/
theorem reversed_actual_control_action :
    ∃ target,GraphStep (.croAction .cro 1 3 (by decide)) (ActualNet.ofNet reversedGraph) target := by
  have fit : (Schema.croAction .cro 1 3 (by decide)).FitsControlPair .cro .cro 3 1 :=
    Or.inr ⟨rfl,rfl,rfl,rfl⟩
  exact fit.graph_step reversedFlow reversedCorridor (.inl ()) (.inr ()) rfl rfl
    (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl

theorem cro_empty_writer (i : Nat) :
    Traversal i (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty :=
  .direct (by simpa only [Context.cons_empty,empty_replace_empty] using
    Passage.cro (i:=i) Context.empty Context.empty)

theorem actual_control_marker_to_graph_step :
    ∃ schema target,GraphStep schema (ActualNet.ofNet reversedGraph) target :=
  control_corridor_graph_step (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
    (cro_empty_writer 3) (cro_empty_writer 1).reverse reversedFlow reversedCorridor
    (.inl ()) (.inr ()) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl

/-- Printed mixed equal-index controls cannot supply the actual seam
traversals required by the graph interaction constructor. -/
theorem mixed_same_index_seam_impossible (i : Nat) (p : Port (.op .fan)) (q : Port (.op .cro))
    (a b c : Context) (left : Traversal i (.op .fan) p (.inl ()) a b)
    (right : Traversal i (.op .cro) (.inl ()) q b c) : False := by
  have same := left.equal_index_control_principals (Or.inl rfl) (Or.inr (Or.inl rfl)) right
  cases same

#print axioms reversed_actual_control_action
#print axioms actual_control_marker_to_graph_step
#print axioms mixed_same_index_seam_impossible

/-- A concrete syntax redex produces its physical connection from real
closed initial Matches, with no supplied path or path-extension premise. -/
theorem actual_matched_redex_has_connection : Nonempty (RedexConnection actualBetaSite.net) := by
  have closed : Lambda.Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have matching := betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  exact matching.redex_connection ⟨[],identityApp,rfl,True.intro⟩

#print axioms actual_matched_redex_has_connection

namespace HighReader
private def labels : Bool → Label signature | false => label .lam 1 | true => label .cro 1
/-- The direct high-reader countercheck with an actual W subdivision. -/
def graph : Net signature Bool Unit Unit where
  label := labels
  wire := {
    mate := fun e => match e with
      | .inl ⟨false,.inl ()⟩ => .inr (.inl ())
      | .inl ⟨false,.inr false⟩ => .inl ⟨true,.inr ()⟩
      | .inl ⟨false,.inr true⟩ => .inr (.inr ((),false))
      | .inl ⟨true,.inl ()⟩ => .inr (.inr ((),true))
      | .inl ⟨true,.inr ()⟩ => .inl ⟨false,.inr false⟩
      | .inr (.inl ()) => .inl ⟨false,.inl ()⟩
      | .inr (.inr (_,false)) => .inl ⟨false,.inr true⟩
      | .inr (.inr (_,true)) => .inl ⟨true,.inl ()⟩
    involutive := by
      rintro (⟨node,port⟩ | (boundary | ⟨w,d⟩))
      · cases node <;> cases port <;> first | rfl | rename_i bit; cases bit <;> rfl
      · cases boundary; rfl
      · cases w; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨node,port⟩ | (boundary | ⟨w,d⟩)) same
      · cases node <;> cases port <;> first | cases same | rename_i bit; cases bit <;> cases same
      · cases same
      · cases d <;> cases same }

abbrev body : Endpoint graph := .inl ⟨false,lamBody⟩
abbrev bind : Endpoint graph := .inl ⟨false,lamBind⟩
abbrev middle : Endpoint graph := .inr (.inr ((),true))
abbrev aux : Endpoint graph := .inl ⟨true,.inr ()⟩

theorem path_labels : Labelling graph [body,middle,aux] Context.empty Context.empty :=
  .cons (LabelledTurn.transparent (g:=graph) () false _) (.cons
    (LabelledTurn.node (g:=graph) true (.inl ()) (.inr ()) (cro_empty_writer 1).reverse) (.single _ _))

theorem prefix_transparent : ∀ x y,(x,y)∈([body,middle] : List (Endpoint graph)).zip [middle] →
    ∃ w d,graph.wire x=.inr (.inr (w,d)) ∧y=.inr (.inr (w,!d)) := by
  intro x y member
  have same := List.mem_singleton.mp member
  cases same
  exact ⟨(),false,rfl,rfl⟩

theorem path_forward : Forward graph [body,middle,aux] :=
  .transparent () false rfl rfl (.node true (.inl ()) (.inr ()) rfl rfl True.intro (.single _))

theorem no_independence : ¬Independence graph () := by
  intro indep
  exact indep.no_high_control_initial [body] middle aux [] body bind .lamBody .lamBind 1 1
    Context.empty Context.empty rfl rfl
    (AtProperRole.lamBody (g:=graph) (root:=()) false AG.lamBody 1 rfl HEq.rfl) True.intro (AtProperRole.lamBind (g:=graph) (root:=()) false AG.lamBind 1 rfl HEq.rfl) True.intro
    path_forward path_labels prefix_transparent true (.inl ()) (.inr ()) .cro 1 rfl
    (Or.inr (Or.inl rfl)) HEq.rfl rfl rfl (Nat.le_refl 1)
end HighReader

#print axioms HighReader.path_labels
#print axioms HighReader.no_independence

namespace ControlChain
private def labels : Bool⊕Bool → Label signature
  | .inl false => label .app 0
  | .inl true => label .cro 0
  | .inr false => label .cro 0
  | .inr true => label .lam 0

def graph : Net signature (Bool⊕Bool) Bool Empty where
  label := labels
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl false,.inl ()⟩ => .inl ⟨.inl true,.inr ()⟩
      | .inl ⟨.inl false,.inr b⟩ => .inr (.inl b)
      | .inl ⟨.inl true,.inl ()⟩ => .inl ⟨.inr false,.inl ()⟩
      | .inl ⟨.inl true,.inr ()⟩ => .inl ⟨.inl false,.inl ()⟩
      | .inl ⟨.inr false,.inl ()⟩ => .inl ⟨.inl true,.inl ()⟩
      | .inl ⟨.inr false,.inr ()⟩ => .inl ⟨.inr true,.inl ()⟩
      | .inl ⟨.inr true,.inl ()⟩ => .inl ⟨.inr false,.inr ()⟩
      | .inl ⟨.inr true,.inr b⟩ => .inl ⟨.inr true,.inr (!b)⟩
      | .inr (.inl b) => .inl ⟨.inl false,.inr b⟩
      | .inr (.inr (w,_)) => nomatch w
    involutive := by
      rintro (⟨(b|b),port⟩ | (boundary | ⟨w,d⟩))
      · cases b <;> cases port <;> first | rfl | rename_i bit; cases bit <;> rfl
      · cases b <;> cases port <;> first | rfl | rename_i bit; cases bit <;> rfl
      · rfl
      · exact nomatch w
    fixedPointFree := by
      rintro (⟨(b|b),port⟩ | (boundary | ⟨w,d⟩)) same
      · cases b <;> cases port <;> first | cases same | rename_i bit; cases bit <;> cases same
      · cases b <;> cases port <;> first | cases same | rename_i bit; cases bit <;> cases same
      · cases same
      · exact nomatch w }

abbrev path : List (Endpoint graph) :=
  [.inl ⟨.inl false,.inl ()⟩,.inl ⟨.inl true,.inl ()⟩,.inl ⟨.inr false,.inr ()⟩]

theorem path_labels : Labelling graph path Context.empty Context.empty :=
  .cons (LabelledTurn.node (g:=graph) (.inl true) (.inr ()) (.inl ()) (cro_empty_writer 0))
    (.cons (LabelledTurn.node (g:=graph) (.inr false) (.inl ()) (.inr ()) (cro_empty_writer 0).reverse) (.single _ _))

theorem path_forward : Forward graph path :=
  .node (.inl true) (.inr ()) (.inl ()) rfl rfl True.intro
    (.node (.inr false) (.inl ()) (.inr ()) rfl rfl True.intro (.single _))

/-- The first control is crossed aux→principal, forcing the extractor to
recurse before it finds the actual principal-to-principal middle corridor. -/
theorem actual_multicontrol_corridor :
    ∃ route : TransparentCorridor graph,IsPrincipal (g:=graph) route.first ∧
      IsPrincipal (g:=graph) route.last ∧ ∃ before after,path=before++route.edges++after := by
  exact path_labels.principal_corridor (path_forward.empty_word_control_only rfl)
    ⟨.inl false,.inl ()⟩ ⟨.inr true,.inl ()⟩
    ⟨.app,rfl,HEq.rfl⟩ ⟨.lam,rfl,HEq.rfl⟩ rfl rfl
end ControlChain

theorem actual_matched_one_w_corridor :
    ∃ connection : RedexConnection actualBetaSite.net,∃ route : TransparentCorridor actualBetaSite.net,
      IsPrincipal (g:=actualBetaSite.net) route.first ∧ IsPrincipal (g:=actualBetaSite.net) route.last ∧
      ∃ before after,connection.edges=before++route.edges++after := by
  obtain ⟨connection⟩ := actual_matched_redex_has_connection
  obtain ⟨route,left,right,before,after,split⟩ := connection.principal_corridor
  exact ⟨connection,route,left,right,before,after,split⟩

#print axioms ControlChain.actual_multicontrol_corridor
#print axioms actual_matched_one_w_corridor

/-- The schema choice reads the seam from one actual whole labelling,
rather than receiving two independently chosen control rules. -/
theorem actual_whole_control_corridor_step :
    ∃ schema target,GraphStep schema (ActualNet.ofNet reversedGraph) target := by
  have whole : Labelling reversedGraph
      [.inr (.inl (.inl ())),.inl ⟨.inl (),.inl ()⟩,.inl ⟨.inr (),.inr ()⟩]
      Context.empty Context.empty :=
    .cons (LabelledTurn.node (g:=reversedGraph) (.inl ()) (.inr ()) (.inl ()) (cro_empty_writer 3))
      (.cons (LabelledTurn.node (g:=reversedGraph) (.inr ()) (.inl ()) (.inr ()) (cro_empty_writer 1).reverse) (.single _ _))
  exact labelled_control_corridor_graph_step (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
    reversedFlow reversedCorridor (.inl ()) (.inr ()) rfl rfl
    (.inl ()) (.inr ()) (.inl ()) (.inr ()) HEq.rfl HEq.rfl rfl rfl
    (.inr (.inl (.inl ()))) (.inl ⟨.inr (),.inr ()⟩) rfl rfl whole

#print axioms actual_whole_control_corridor_step

namespace ControlChain

def middleCorridor : TransparentCorridor graph where
  first := ⟨.inl true,.inl ()⟩
  last := ⟨.inr false,.inl ()⟩
  edges := [.inl ⟨.inl true,.inl ()⟩]
  start := rfl
  finish := rfl
  transparent := by intro x y member; cases member

theorem path_labels_context (a : Context) : Labelling graph path a a := by
  have write : Traversal 0 (.op .cro) (.inr ()) (.inl ()) a (a.cons .empty) :=
    .direct (by simpa only [Context.replace_zero] using Passage.cro (i:=0) Context.empty a)
  exact .cons (LabelledTurn.node (g:=graph) (.inl true) (.inr ()) (.inl ()) write)
    (.cons (LabelledTurn.node (g:=graph) (.inr false) (.inl ()) (.inr ()) write.reverse) (.single _ _))

/-- Both surrounding lists are nonempty and the actual middle context is
changed; the two returned seams come from the same whole assignment. -/
theorem actual_nonempty_seams (a : Context) :
    Labelling graph [.inl ⟨.inl false,.inl ()⟩,.inl ⟨.inl true,.inl ()⟩] a (a.cons .empty) ∧
    Labelling graph [.inl ⟨.inl true,.inl ()⟩,.inl ⟨.inr false,.inr ()⟩] (a.cons .empty) a := by
  obtain ⟨middle,beforeLabels,afterLabels⟩ := (path_labels_context a).corridor_seams middleCorridor
    [.inl ⟨.inl false,.inl ()⟩] [.inl ⟨.inr false,.inr ()⟩]
  have write : Traversal 0 (.op .cro) (.inr ()) (.inl ()) a (a.cons .empty) :=
    .direct (by simpa only [Context.replace_zero] using Passage.cro (i:=0) Context.empty a)
  have actualPrefix : Labelling graph [.inl ⟨.inl false,.inl ()⟩,.inl ⟨.inl true,.inl ()⟩] a (a.cons .empty) :=
    .cons (LabelledTurn.node (g:=graph) (.inl true) (.inr ()) (.inl ()) write) (.single _ _)
  have same : middle=a.cons .empty := beforeLabels.output_unique actualPrefix
  subst middle
  exact ⟨beforeLabels,afterLabels⟩

theorem seam_really_changes :
    (Context.empty.cons (.star .empty)).cons .empty≠Context.empty.cons (.star .empty) := by
  intro same
  have head := congrArg (fun c : Context => c.get 0) same
  cases head
end ControlChain

#print axioms ControlChain.actual_nonempty_seams
#print axioms ControlChain.seam_really_changes
namespace ControlChain

def actualFlow : FlowBalance graph (fun b => !b) where
  nodes := fun n => match n with | .inl true => true | _ => false
  vertices := Empty.elim
  wiring := by
    rintro (⟨(b|b),port⟩ | (boundary | ⟨w,d⟩))
    · cases b <;> cases port <;> first | rfl | rename_i bit; cases bit <;> rfl
    · cases b <;> cases port <;> first | rfl | rename_i bit; cases bit <;> rfl
    · cases boundary <;> rfl
    · exact nomatch w

theorem actual_internal_step (a : Context) :
    ∃ schema target, GraphStep schema (ActualNet.ofNet graph) target := by
  exact (path_labels_context a).internal_control_corridor_step
    (path_forward.empty_word_control_only rfl) actualFlow middleCorridor
    ⟨.cro,rfl,HEq.rfl⟩ ⟨.cro,rfl,HEq.rfl⟩
    [.inl ⟨.inl false,.inl ()⟩] [.inl ⟨.inr false,.inr ()⟩] rfl (by simp) (by simp)
end ControlChain
#print axioms ControlChain.actual_internal_step
/-- The total conditional interface receives all source hypotheses from the
actual initial encoding; no target invariant or chosen corridor is supplied. -/
theorem initial_matched_redex_has_actual_step :
    ∃ schema target, GraphStep schema (ActualNet.ofNet (encode 0 identityApp).net) target := by
  have closed : Lambda.Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  let redex : Lambda.RedexOcc identityApp := ⟨[],by exact ⟨_,rfl,True.intro⟩⟩
  exact (encode_closed_matches identityApp closed 0).syntax_redex_graph_step
    (encode_closed_independence identityApp closed 0) balance rfl flow redex
#print axioms initial_matched_redex_has_actual_step
/-- The root-only interface is exercised independently of the earlier full-I
wrapper: only its rootInputs consequence is supplied to the new theorem. -/
theorem initial_matched_redex_step_from_root_inputs :
    ∃ schema target, GraphStep schema (ActualNet.ofNet (encode 0 identityApp).net) target := by
  have closed : Lambda.Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  let redex : Lambda.RedexOcc identityApp := ⟨[],by exact ⟨_,rfl,True.intro⟩⟩
  exact (encode_closed_matches identityApp closed 0).syntax_redex_graph_step_of_root_inputs
    (encode_closed_independence identityApp closed 0).rootInputs balance rfl flow redex
#print axioms initial_matched_redex_step_from_root_inputs
namespace WeakSuffix
open Lambda
private def nested : Term := .lam (.lam (.var 1))

theorem actual_nested_suffix_unique :
    ∃ access : RootAccess (encode 7 nested).net (.inl ()),
      accessWord (encode 7 nested).net access.val=[.body,.body] ∧
      BindingSuffix (encode 7 nested).net access.val 1 ∧
      ∀ k,BindingSuffix (encode 7 nested).net access.val k → k=1 := by
  have closed : Closed nested := by change 1<2; decide
  obtain ⟨access,word⟩ := encode_closed_access_coverage nested closed 7
    ⟨[.body,.body],by decide⟩ Context.empty
  have lookup : subtermAt nested (accessWord (encode 7 nested).net access.val)=some (.var 1) := by
    rw [word]; rfl
  have original := (encode_closed_var_observes nested closed 7 access 1 lookup).2.1
  have invariants := encode_closed_ordinary_invariants nested closed 7
  refine ⟨access,word,original,?_⟩
  intro k other
  exact invariants.independence.rootInputs.binding_suffix_unique
    invariants.nesting invariants.transparency access other original
end WeakSuffix
#print axioms WeakSuffix.actual_nested_suffix_unique
end Lamping.Checks.Phase5Review.PrincipalSites





















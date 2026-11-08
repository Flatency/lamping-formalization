import Lamping.Lamping.ActionFunctionPadding
import Lamping.Lamping.CanonicalChildDeparture
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
private theorem syntax_argument_role {kind : Kind} {ctx dep : Port kind}
    (roles : SyntaxChildPorts kind ctx dep .arg) : HEq dep (appArg : Port (.op .app)) := by
  cases roles;exact HEq.rfl
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
theorem actual_argument_child_head (matching : Matches g root current.erase)
    (fragment : SourceEdgeFragment current g root edge position)
    (role : SourceDeparture parentTerm .arg edge.fromPort)
    (parent : RootAccess g root) (word : position=accessWord g parent.val++[.arg])
    (node : N) (context argument : Port (g.label node).sort)
    (argumentRole : HEq argument (appArg : Port (.op .app)))
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,context⟩))) :
    fragment.fromEndpoint=.inl ⟨node,argument⟩ := by
  obtain ⟨n,ctx,dep,tail,roles,parentFinish,split,_,_⟩ := matching.syntax_child_fragment
    parent fragment.access .arg (fragment.word.trans word)
  have endpoints : (⟨n,ctx⟩ : NodePort signature N g.label)=⟨node,context⟩ := by
    have same := Option.some.inj (parentFinish.symm.trans finish)
    have wired := congrArg g.wire same
    simp only [Pairing.involutive] at wired
    exact Sum.inl.inj wired
  have nodeEq : n=node := congrArg Sigma.fst endpoints
  subst n
  have depEq : dep=argument := eq_of_heq ((syntax_argument_role roles).trans argumentRole.symm)
  have cut := fragment.child_prefix matching role parent word
  have piece : fragment.segments=.inl ⟨node,dep⟩::tail := List.append_cancel_left (cut.2.symm.trans split)
  have first := fragment.start
  rw [piece,depEq] at first
  exact (Option.some.inj first).symm
end
section
variable {K B W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W]
variable (c : Net signature K (B⊕(Unit⊕Bool)) W) (op : Op) (single : Bij Unit (Aux op)) (i j : Nat)
local notation "rhs" => unaryRightCore op Op.app single i j
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) appArg)) : PlugSegment c rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment c rhs)
local notation "exitSegment" => (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inr true)))) : PlugSegment c rhs)
/-- The ARG writer is a real indexed control turn. Its output is retained,
not silently identified with the copied application's input assignment. -/
theorem unary_typed_argument_prefix (control : op=.fan ∨op=.cro ∨op=.bra)
    {es : List (PlugSegment c rhs)} {a b : Context}
    (labels : PlugLabelling c rhs es a b) (head : es.head?=some argumentSegment)
    (typed : ∃k,accessKind (plug c rhs) (es.map (plugEnd c.label (rhs).label))=some k) :
    ∃tail middle,es=argumentSegment::writerSegment::exitSegment::tail ∧
      Traversal i (.op op) (.inr (single ())) (.inl ()) a middle ∧
      PlugLabelling c rhs (exitSegment::tail) middle b := by
  cases es with
  | nil => cases head
  | cons e es =>
    have same := Option.some.inj head
    subst e
    cases labels with
    | single =>
      obtain ⟨kind,typed⟩ := typed
      rcases control with rfl|rfl|rfl <;> cases typed
    | @cons e f es a middle b turn rest =>
      change PlugTurn c rhs (.inr (.inl ⟨.inr true,.inr (single ())⟩)) f a middle at turn
      cases turn with
      | right step =>
        obtain ⟨port,out,rule⟩ := step.from_node (.inr true) (.inr (single ())) rfl
        have principal : port=.inl () := by
          rcases control with rfl|rfl|rfl <;> exact rule.control_aux
        subst port
        cases out
        cases es with
        | nil =>
          obtain ⟨kind,typed⟩ := typed
          change none=some kind at typed
          cases typed
        | cons f es =>
          cases rest with
          | cons next suffix =>
            change PlugTurn c rhs (.inr (.inr (.inl (.inr true)))) f middle _ at next
            cases next with
            | leave => exact ⟨es,middle,rfl,rule,suffix⟩
            | right impossible => cases impossible

theorem unary_copied_argument_fragment (control : op=.fan ∨op=.cro ∨op=.bra)
    {current : LTerm} {root : B}
    (matching : Matches (plug c rhs) root current.erase)
    (fragment : SourceEdgeFragment current (plug c rhs) root edge position)
    (role : SourceDeparture parentTerm .arg edge.fromPort)
    (parent : RootAccess (plug c rhs) root)
    (word : position=accessWord (plug c rhs) parent.val++[.arg])
    (finish : parent.val.getLast?=some ((plug c rhs).wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    {a b : Context} (labels : Labelling (plug c rhs) fragment.segments a b) :
    ∃tail middle,fragment.segments.map (plugEnd c.label (rhs).label).invFun=
      argumentSegment::writerSegment::exitSegment::tail ∧
      Traversal i (.op op) (.inr (single ())) (.inl ()) a middle ∧
      PlugLabelling c rhs (exitSegment::tail) middle b := by
  have actualStart := actual_argument_child_head matching fragment role parent word
    (.inr (.inl ())) appCtx appArg HEq.rfl finish
  have head := fragment.start
  rw [actualStart] at head
  have rawHead : (fragment.segments.map (plugEnd c.label (rhs).label).invFun).head?=some argumentSegment := by
    rw [List.head?_map,head];rfl
  apply unary_typed_argument_prefix c op single i j control (labels.plug_decomposition c rhs) rawHead
  simpa only [plug_decomposition_flatten] using fragment.fragment_typed
end

#print axioms Lamping.AG.actual_argument_child_head
#print axioms Lamping.AG.unary_typed_argument_prefix
#print axioms Lamping.AG.unary_copied_argument_fragment
section
variable {K B W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W]
variable (c : Net signature K (B⊕(Unit⊕Bool)) W) (op : Op) (single : Bij Unit (Aux op))
    (i k : Nat)
local notation "rhs" => unaryRightCore op Op.app single i k
/-- The ARG extension writes back the exact pending input by reversing its
actual context-reader rule. The final context is pending.middle, not b. -/
theorem PendingRhsBlock.unary_argument_padding (control : op=.fan ∨op=.cro ∨op=.bra)
    {raw : List (PlugSegment c rhs)} {a b : Context}
    (pending : PendingRhsBlock c rhs raw a b)
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),appCtx⟩))) :
    ∃ path : LocalPath rhs (.inr false) (.inr true) pending.middle pending.middle,
      pending.enter=.inr false ∧
      path.edges=pending.inside++[.inl ⟨.inl (),appArg⟩,.inl ⟨.inr true,.inl ()⟩] ∧
      PlugExcursions c rhs
        (.inl pending.last::(path.edges.map Sum.inr++[.inl (.inr (.inl (.inr (.inr true))))]))
        pending.middle pending.middle ∧
      raw++[.inr (.inl ⟨.inl (),appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
        .inl (.inr (.inl (.inr (.inr true))))]=
        pending.pre++((.inl pending.last::(path.edges.map (Sum.inr : Endpoint rhs → PlugSegment c rhs)++
          [.inl (.inr (.inl (.inr (.inr true))))])) : List (PlugSegment c rhs)).tail := by
  obtain ⟨entry,shape,rule⟩ := unaryRight_app_context_prefix op single control i k
    pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead finish
  let path : LocalPath rhs (.inr false) (.inr true) pending.middle pending.middle := {
    edges := [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr (single ())⟩,
      .inl ⟨.inl (),appArg⟩,.inl ⟨.inr true,.inl ()⟩]
    start := rfl
    finish := rfl
    labeling := .cons (LabelledTurn.node (g:=rhs) (.inr false) _ _ rule)
      (.cons (LabelledTurn.node (g:=rhs) (.inl ()) _ _ (.direct (.appArg b)))
        (.cons (LabelledTurn.node (g:=rhs) (.inr true) _ _ rule.reverse) (.single _ _))) }
  have arrival : c.wire pending.last=.inr (.inl (.inr (.inr false))) := by
    rw [pending.arrival,entry]
  refine ⟨path,entry,?_,?_,?_⟩
  · rw [shape];rfl
  · exact .through path arrival (.single _ _)
  · have eqs := pending.equation
    rw [shape] at eqs
    exact (congrArg (fun xs=>xs++[.inr (.inl ⟨.inl (),appArg⟩),
      .inr (.inl ⟨.inr true,.inl ()⟩),.inl (.inr (.inl (.inr (.inr true))))]) eqs).trans
      (by simp only [List.append_assoc];rfl)
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.app i j lt) V) site.closed
local notation "rhs" => unaryRightCore Op.cro Op.app (Bij.refl _) i (j-1)
/-- Real ARG padding normalizes to the supplied source parent followed by
its old APP ARG departure. No reverse principal route occurs here. -/
theorem PathSite.cro_argument_padding_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ActionCanonicalBlocks site principal
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))])
      (source.val++[.inl ⟨.inr (.inr ()),appArg⟩]) := by
  obtain ⟨pending,_preRelation,oldLabels,oldFinish,_shape⟩ :=
    site.cro_aux_canonical_access flow root positive matching principal source target word false finish labels
  change PendingRhsBlock cut rhs (target.val.map (plugEnd (cut).label (rhs).label).invFun) a b at pending
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut rhs first) := target.property.2.1
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  have insideFinish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),appCtx⟩)) := by
    apply pending.inside_finish cut rhs ((rhs).wire (.inl ⟨.inl (),appCtx⟩))
    rw [List.getLast?_map,finish]
    change some ((plugEnd (cut).label (rhs).label).invFun
      ((plug cut rhs).wire (.inl ⟨.inr (.inl ()),appCtx⟩)))=_
    rw [plugSegmentWire_inverse];rfl
  obtain ⟨path,_entry,_pathEq,rightPath,paddedEq⟩ := pending.unary_argument_padding
    cut .cro (Bij.refl _) i (j-1) (Or.inr (Or.inl rfl)) insideFinish
  obtain ⟨before,preEq⟩ := List.getLast?_eq_some_iff.mp pending.prefixLast
  have joined := pending.prefixPath.overlap_join cut rhs preEq rightPath
  have whole : PlugExcursions cut rhs
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]) a pending.middle := by
    rw [paddedEq]
    simpa only [preEq,List.append_assoc,List.cons_append,List.tail_cons] using joined
  have starts : (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))] : List (PlugSegment cut rhs)).head?=some (.inl first) := by
    rw [List.head?_append,rawHead,Option.some_or]
  have ends : (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))] : List (PlugSegment cut rhs)).getLast?=
        some (.inl (.inr (.inl (.inr (.inr true))))) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨old,relation,canonLabels,canonHead,canonLast⟩ := whole.action_canonical_lift site
    (.cro .app i j lt) principal first (.inr (.inl (.inr (.inr true)))) starts ends
  let oldArg : Endpoint site.net := .inl ⟨.inr (.inr ()),appArg⟩
  have padLabels : Labelling site.net (source.val++[oldArg]) a pending.middle := by
    exact oldLabels.append_seam (.single oldArg pending.middle) (by
      intro e f last head
      have eEq:=Option.some.inj (last.symm.trans oldFinish)
      have fEq:=Option.some.inj head
      subst e;subst f
      rw [Pairing.involutive]
      exact LabelledTurn.node (g:=site.net) (.inr (.inr ())) appCtx appArg
        (.direct (.appArg pending.middle)))
  have padHead : (source.val++[oldArg]).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,source.property.2.1,Option.some_or]
  have padLast : (source.val++[oldArg]).getLast?=some oldArg := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have canonRoot : old.head?=some (.inr (.inl root)) := canonHead
  have canonEnd : old.getLast?=some oldArg := canonLast
  have same := canonLabels.rooted_terminal_unique site.net
    (canonLabels.root_forward_of_flow flow root canonRoot positive) canonRoot padLabels
    (padLabels.root_forward_of_flow flow root padHead positive) padHead (canonEnd.trans padLast.symm)
  rw [same.1] at relation
  exact relation
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.app i j lt) V) site.closed
local notation "rhs" => unaryRightCore Op.bra Op.app (Bij.refl _) i (j+1)
/-- Real ARG padding normalizes to the supplied source parent followed by
its old APP ARG departure. No reverse principal route occurs here. -/
theorem PathSite.bra_argument_padding_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ActionCanonicalBlocks site principal
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))])
      (source.val++[.inl ⟨.inr (.inr ()),appArg⟩]) := by
  obtain ⟨pending,_preRelation,oldLabels,oldFinish,_shape⟩ :=
    site.bra_aux_canonical_access flow root positive matching principal source target word false finish labels
  change PendingRhsBlock cut rhs (target.val.map (plugEnd (cut).label (rhs).label).invFun) a b at pending
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut rhs first) := target.property.2.1
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  have insideFinish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),appCtx⟩)) := by
    apply pending.inside_finish cut rhs ((rhs).wire (.inl ⟨.inl (),appCtx⟩))
    rw [List.getLast?_map,finish]
    change some ((plugEnd (cut).label (rhs).label).invFun
      ((plug cut rhs).wire (.inl ⟨.inr (.inl ()),appCtx⟩)))=_
    rw [plugSegmentWire_inverse];rfl
  obtain ⟨path,_entry,_pathEq,rightPath,paddedEq⟩ := pending.unary_argument_padding
    cut .bra (Bij.refl _) i (j+1) (Or.inr (Or.inr rfl)) insideFinish
  obtain ⟨before,preEq⟩ := List.getLast?_eq_some_iff.mp pending.prefixLast
  have joined := pending.prefixPath.overlap_join cut rhs preEq rightPath
  have whole : PlugExcursions cut rhs
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]) a pending.middle := by
    rw [paddedEq]
    simpa only [preEq,List.append_assoc,List.cons_append,List.tail_cons] using joined
  have starts : (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))] : List (PlugSegment cut rhs)).head?=some (.inl first) := by
    rw [List.head?_append,rawHead,Option.some_or]
  have ends : (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))] : List (PlugSegment cut rhs)).getLast?=
        some (.inl (.inr (.inl (.inr (.inr true))))) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨old,relation,canonLabels,canonHead,canonLast⟩ := whole.action_canonical_lift site
    (.bra .app i j lt) principal first (.inr (.inl (.inr (.inr true)))) starts ends
  let oldArg : Endpoint site.net := .inl ⟨.inr (.inr ()),appArg⟩
  have padLabels : Labelling site.net (source.val++[oldArg]) a pending.middle := by
    exact oldLabels.append_seam (.single oldArg pending.middle) (by
      intro e f last head
      have eEq:=Option.some.inj (last.symm.trans oldFinish)
      have fEq:=Option.some.inj head
      subst e;subst f
      rw [Pairing.involutive]
      exact LabelledTurn.node (g:=site.net) (.inr (.inr ())) appCtx appArg
        (.direct (.appArg pending.middle)))
  have padHead : (source.val++[oldArg]).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,source.property.2.1,Option.some_or]
  have padLast : (source.val++[oldArg]).getLast?=some oldArg := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have canonRoot : old.head?=some (.inr (.inl root)) := canonHead
  have canonEnd : old.getLast?=some oldArg := canonLast
  have same := canonLabels.rooted_terminal_unique site.net
    (canonLabels.root_forward_of_flow flow root canonRoot positive) canonRoot padLabels
    (padLabels.root_forward_of_flow flow root padHead positive) padHead (canonEnd.trans padLast.symm)
  rw [same.1] at relation
  exact relation
end
end Lamping.AG
#print axioms Lamping.AG.PendingRhsBlock.unary_argument_padding
#print axioms Lamping.AG.PathSite.cro_argument_padding_access
#print axioms Lamping.AG.PathSite.bra_argument_padding_access

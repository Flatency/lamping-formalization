/-
Finite copied-lambda body prefixes for the two unary action diagrams.
Actual terminal typedness excludes the two truncated prefixes; no path
completion, remaining-tail totality or representation premise is assumed.
The occurrence wrapper derives its physical departure from an actual parent
RootAccess on the SAME matching graph.
-/
import Lamping.Lamping.CancellationFragmentTransport
import Lamping.Lamping.ActionKeptFragmentComparison
namespace Lamping.AG
open Graph
section
variable {K B W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W]
variable (c : Net signature K (B⊕(Unit⊕Bool)) W) (op : Op)
  (single : Bij Unit (Aux op)) (control : op=Op.cro ∨op=Op.bra) (i j : Nat)
local notation "rhs" => unaryRightCore op Op.lam single i j
local notation "bodySegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inr true))) : PlugSegment c rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment c rhs)
local notation "exitSegment" => (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inr true)))) : PlugSegment c rhs)
include control in
theorem unary_body_prefix {es : List (PlugSegment c rhs)} {a b : Context}
    (labels : PlugLabelling c rhs es a b)
    (head : es.head?=some bodySegment)
    (notOne : es≠[bodySegment]) (notTwo : es≠[bodySegment,writerSegment]) :
    ∃tail middle,es=bodySegment::writerSegment::exitSegment::tail ∧
      Traversal i (.op op) (.inr (single ())) (.inl ()) a middle ∧
      PlugLabelling c rhs (exitSegment::tail) middle b := by
  cases es with
  | nil => cases head
  | cons e es =>
    have same := Option.some.inj head
    subst e
    cases labels with
    | single => exact False.elim (notOne rfl)
    | @cons e f es a middle b turn rest =>
      change PlugTurn c rhs (.inr (.inl ⟨.inr true,.inr (single ())⟩)) f a middle at turn
      cases turn with
      | right nodeTurn =>
        cases nodeTurn with
        | node n p q rule =>
          have qEq : q=.inl () := by
            rcases control with rfl|rfl <;> exact rule.control_aux
          subst q
          cases rest with
          | single => exact False.elim (notTwo rfl)
          | @cons _ f es _ after _ turn rest =>
            change PlugTurn c rhs (.inr (.inr (.inl (.inr true)))) f middle after at turn
            cases turn with
            | leave => exact ⟨es,middle,rfl,rule,rest⟩
            | right impossible => cases impossible
include control in
theorem unary_typed_body_prefix {es : List (PlugSegment c rhs)} {a b : Context}
    (labels : PlugLabelling c rhs es a b) (head : es.head?=some bodySegment)
    (typed : ∃k,accessKind (plug c rhs) (es.map (plugEnd c.label (rhs).label))=some k) :
    ∃tail middle,es=bodySegment::writerSegment::exitSegment::tail ∧
      Traversal i (.op op) (.inr (single ())) (.inl ()) a middle ∧
      PlugLabelling c rhs (exitSegment::tail) middle b := by
  apply unary_body_prefix c op single control i j labels head
  · intro single
    rw [single] at typed
    obtain ⟨kind,typed⟩ := typed
    rcases control with rfl|rfl <;> change none=some kind at typed <;> cases typed
  · intro pair
    rw [pair] at typed
    obtain ⟨kind,typed⟩ := typed
    rcases control with rfl|rfl <;> change none=some kind at typed <;> cases typed
end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
private theorem syntax_body_role {kind : Kind} {ctx dep : Port kind}
    (roles : SyntaxChildPorts kind ctx dep .body) : HEq dep lamBody := by
  cases roles;exact HEq.rfl
theorem actual_lambda_child_head (matching : Matches g root current.erase)
    (fragment : SourceEdgeFragment current g root edge position)
    (role : SourceDeparture parentTerm .body edge.fromPort)
    (parent : RootAccess g root) (word : position=accessWord g parent.val++[.body])
    (node : N) (context body : Port (g.label node).sort)
    (bodyRole : HEq body lamBody)
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,context⟩))) :
    fragment.fromEndpoint=.inl ⟨node,body⟩ := by
  obtain ⟨n,ctx,dep,tail,roles,parentFinish,split,_,_⟩ := matching.syntax_child_fragment
    parent fragment.access .body (fragment.word.trans word)
  have endpoints : (⟨n,ctx⟩ : NodePort signature N g.label)=⟨node,context⟩ := by
    have same := Option.some.inj (parentFinish.symm.trans finish)
    have wired := congrArg g.wire same
    simp only [Pairing.involutive] at wired
    exact Sum.inl.inj wired
  have nodeEq : n=node := congrArg Sigma.fst endpoints
  subst n
  have depRole : HEq dep lamBody := syntax_body_role roles
  have depEq : dep=body := eq_of_heq (depRole.trans bodyRole.symm)
  have cut := fragment.child_prefix matching role parent word
  have piece : fragment.segments=.inl ⟨node,dep⟩::tail := List.append_cancel_left (cut.2.symm.trans split)
  have first := fragment.start
  rw [piece,depEq] at first
  exact (Option.some.inj first).symm
end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W]
variable (c : Net signature K (B⊕(Unit⊕Bool)) W) (op : Op)
  (single : Bij Unit (Aux op)) (control : op=Op.cro ∨op=Op.bra) (i j : Nat)
local notation "rhs" => unaryRightCore op Op.lam single i j
local notation "bodySegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inr true))) : PlugSegment c rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment c rhs)
local notation "exitSegment" => (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inr true)))) : PlugSegment c rhs)
include control in
 theorem unary_copied_lambda_body_fragment {current : LTerm} {root : B}
    (matching : Matches (plug c rhs) root current.erase)
    (fragment : SourceEdgeFragment current (plug c rhs) root edge position)
    (role : SourceDeparture parentTerm .body edge.fromPort)
    (parent : RootAccess (plug c rhs) root)
    (word : position=accessWord (plug c rhs) parent.val++[.body])
    (finish : parent.val.getLast?=some ((plug c rhs).wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    {a b : Context} (labels : Labelling (plug c rhs) fragment.segments a b) :
    ∃tail middle,fragment.segments.map (plugEnd c.label (rhs).label).invFun=
      bodySegment::writerSegment::exitSegment::tail ∧
      Traversal i (.op op) (.inr (single ())) (.inl ()) a middle ∧
      PlugLabelling c rhs (exitSegment::tail) middle b := by
  have actualStart := actual_lambda_child_head matching fragment role parent word
    (.inr (.inl ())) (.inl ()) (.inr true) HEq.rfl finish
  have head := fragment.start
  rw [actualStart] at head
  have rawHead : (fragment.segments.map (plugEnd c.label (rhs).label).invFun).head?=some bodySegment := by
    rw [List.head?_map,head]
    rfl
  apply unary_typed_body_prefix c op single control i j (labels.plug_decomposition c rhs) rawHead
  have typed := fragment.fragment_typed
  simpa only [plug_decomposition_flatten] using typed
end
end Lamping.AG
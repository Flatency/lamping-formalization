import Lamping.Lamping.ActionCopiedBindingComparison
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
private theorem syntax_function_role {kind : Kind} {ctx dep : Port kind}
    (roles : SyntaxChildPorts kind ctx dep .fn) : HEq dep (Sum.inl () : Port (.op .app)) := by
  cases roles;exact HEq.rfl
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
 theorem actual_function_child_head (matching : Matches g root current.erase)
    (fragment : SourceEdgeFragment current g root edge position)
    (role : SourceDeparture parentTerm .fn edge.fromPort)
    (parent : RootAccess g root) (word : position=accessWord g parent.val++[.fn])
    (node : N) (context function : Port (g.label node).sort)
    (functionRole : HEq function (Sum.inl () : Port (.op .app)))
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,context⟩))) :
    fragment.fromEndpoint=.inl ⟨node,function⟩ := by
  obtain ⟨n,ctx,dep,tail,roles,parentFinish,split,_,_⟩ := matching.syntax_child_fragment
    parent fragment.access .fn (fragment.word.trans word)
  have endpoints : (⟨n,ctx⟩ : NodePort signature N g.label)=⟨node,context⟩ := by
    have same := Option.some.inj (parentFinish.symm.trans finish)
    have wired := congrArg g.wire same
    simp only [Pairing.involutive] at wired
    exact Sum.inl.inj wired
  have nodeEq : n=node := congrArg Sigma.fst endpoints
  subst n
  have depEq : dep=function := eq_of_heq ((syntax_function_role roles).trans functionRole.symm)
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
local notation "functionSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment c rhs)
local notation "exitSegment" => (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inl ())))) : PlugSegment c rhs)
 theorem unary_typed_function_prefix {es : List (PlugSegment c rhs)} {a b : Context}
    (labels : PlugLabelling c rhs es a b) (head : es.head?=some functionSegment)
    (typed : ∃k,accessKind (plug c rhs) (es.map (plugEnd c.label (rhs).label))=some k) :
    ∃tail,es=functionSegment::exitSegment::tail ∧PlugLabelling c rhs (exitSegment::tail) a b := by
  cases es with
  | nil => cases head
  | cons e es =>
    have same := Option.some.inj head
    subst e
    cases labels with
    | single =>
      obtain ⟨kind,typed⟩ := typed
      change none=some kind at typed
      cases typed
    | @cons e f es a middle b turn rest =>
      change PlugTurn c rhs (.inr (.inr (.inl (.inl ())))) f a middle at turn
      cases turn with
      | leave => exact ⟨es,rfl,rest⟩
      | right impossible => cases impossible
 theorem unary_copied_function_fragment {current : LTerm} {root : B}
    (matching : Matches (plug c rhs) root current.erase)
    (fragment : SourceEdgeFragment current (plug c rhs) root edge position)
    (role : SourceDeparture parentTerm .fn edge.fromPort)
    (parent : RootAccess (plug c rhs) root)
    (word : position=accessWord (plug c rhs) parent.val++[.fn])
    (finish : parent.val.getLast?=some ((plug c rhs).wire (.inl ⟨.inr (.inl ()),.inr false⟩)))
    {a b : Context} (labels : Labelling (plug c rhs) fragment.segments a b) :
    ∃tail,fragment.segments.map (plugEnd c.label (rhs).label).invFun=
      functionSegment::exitSegment::tail ∧PlugLabelling c rhs (exitSegment::tail) a b := by
  have actualStart := actual_function_child_head matching fragment role parent word
    (.inr (.inl ())) (.inr false) (.inl ()) HEq.rfl finish
  have head := fragment.start
  rw [actualStart] at head
  have rawHead : (fragment.segments.map (plugEnd c.label (rhs).label).invFun).head?=some functionSegment := by
    rw [List.head?_map,head]
    rfl
  apply unary_typed_function_prefix c op single i j (labels.plug_decomposition c rhs) rawHead
  simpa only [plug_decomposition_flatten] using fragment.fragment_typed
end
end Lamping.AG
import Lamping.Lamping.PathDefinitions
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
/-- A beta edge is an actual directed segment, not merely two equal node labels.
The principal segment list retains transparent subdivision vertices. -/
structure BetaEdge where
  app : N
  lam : N
  index : Nat
  appLabel : g.label app = label .app index
  lamLabel : g.label lam = label .lam index
  appFun : Port (g.label app).sort
  appCtx : Port (g.label app).sort
  appArg : Port (g.label app).sort
  lamCtx : Port (g.label lam).sort
  lamBody : Port (g.label lam).sort
  lamBind : Port (g.label lam).sort
  appFun_role : HEq appFun (Sum.inl () : Port (.op .app))
  appCtx_role : HEq appCtx AG.appCtx
  appArg_role : HEq appArg AG.appArg
  lamCtx_role : HEq lamCtx (Sum.inl () : Port (.op .lam))
  lamBody_role : HEq lamBody AG.lamBody
  lamBind_role : HEq lamBind AG.lamBind
  principal : List (Endpoint g)
  principalStart : principal.head?=some (.inl ⟨app,appFun⟩)
  principalEnd : principal.getLast?=some (g.wire (.inl ⟨lam,lamCtx⟩))
  transparent : ∀ e f, (e,f) ∈ principal.zip principal.tail →
    ∃ w d, g.wire e=.inr (.inr (w,d)) ∧ f=.inr (.inr (w,!d))
namespace BetaEdge
def funEnd (r : BetaEdge g) : Endpoint g := .inl ⟨r.app,r.appFun⟩
def ctxEnd (r : BetaEdge g) : Endpoint g := .inl ⟨r.lam,r.lamCtx⟩
def argEnd (r : BetaEdge g) : Endpoint g := .inl ⟨r.app,r.appArg⟩
/-- Reversal retains every physical segment occurrence, including transparent W. -/
def reverseRoute (r : BetaEdge g) : List (Endpoint g) := r.principal.reverse.map g.wire.mate
end BetaEdge
/-- Proper labeling extended only by the two turns surrounding a reversed beta edge.
The equality at binding→context is precisely AG98 PDF74. -/
inductive ExpandedTurn : Endpoint g → Endpoint g → Context → Context → Prop
  | ordinary {x y a b} : LabelledTurn g x y a b → ExpandedTurn x y a b
  | bindToCtx (r : BetaEdge g) (a) : ExpandedTurn
      (.inl ⟨r.lam,r.lamBind⟩) r.ctxEnd a a
  | funToArg (r : BetaEdge g) (a) : ExpandedTurn r.funEnd r.argEnd a a
/-- Forward directions for ordinary turns; reversed beta turns are explicit. -/
inductive ExpandedDirection : Endpoint g → Endpoint g → Prop
  | node (n : N) (p q : Port (g.label n).sort)
      (direction : ForwardPorts (g.label n).sort p q) :
      ExpandedDirection (.inl ⟨n,p⟩) (.inl ⟨n,q⟩)
  | transparent (w : W) (d : Bool) : ExpandedDirection
      (.inr (.inr (w,d))) (.inr (.inr (w,!d)))
  | bindToCtx (r : BetaEdge g) : ExpandedDirection
      (.inl ⟨r.lam,r.lamBind⟩) r.ctxEnd
  | funToArg (r : BetaEdge g) : ExpandedDirection r.funEnd r.argEnd
inductive ExpandedForward : List (Endpoint g) → Prop
  | single (e) : ExpandedForward [e]
  | cons {e f es} : ExpandedDirection g (g.wire e) f →
      ExpandedForward (f::es) → ExpandedForward (e::f::es)
inductive ExpandedLabelling : List (Endpoint g) → Context → Context → Prop
  | single (e a) : ExpandedLabelling [e] a a
  | cons {e f es a b c} : ExpandedTurn g (g.wire e) f a b →
      ExpandedLabelling (f::es) b c → ExpandedLabelling (e::f::es) a c
/-- The loop may itself cross reversed beta edges (AG98 PDF73–74). -/
structure ExpandedBindingLoop (es : List (Endpoint g)) (a b : Context) where
  binder : N
  isLam : (g.label binder).sort=.op .lam
  body : Port (g.label binder).sort
  bind : Port (g.label binder).sort
  body_role : HEq body lamBody
  bind_role : HEq bind lamBind
  start : es.head?=some (.inl ⟨binder,body⟩)
  finish : es.getLast?=some (g.wire (.inl ⟨binder,bind⟩))
  proper : ExpandedLabelling g es a b
  forward : ExpandedForward g es
  shell : Context.SameShell (g.label binder).index a b
/-- Definition 3.5.16 as the least root-based closure. Lists include the segment at
 each seam once. The two premises are the old argument path and old body-loop path.
 No arbitrary labelable expanded walk constructor exists. -/
inductive ExpandedProperPath (root : B) : List (Endpoint g) → Prop
  | base {es} (path : ForwardProperPath g es)
      (rooted : es.head?=some (.inr (.inl root))) : ExpandedProperPath root es
  | insert (r : BetaEdge g) (pre loop suffix : List (Endpoint g))
      (argument : ExpandedProperPath root (pre ++ r.argEnd::suffix))
      (body : ExpandedProperPath root (pre ++ r.principal ++ loop))
      (preEnd : pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩)))
      (loopStart : loop.head?=some (.inl ⟨r.lam,r.lamBody⟩))
      (loopEnd : loop.getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩)))
      (a b : Context) (binding : BindingLoop g loop a b)
      (sameBinder : binding.binder=r.lam) :
      ExpandedProperPath root (pre ++ r.principal ++ loop ++ r.reverseRoute ++ [r.argEnd] ++ suffix)
/-- Generation is rooted even after insertion; root is never a freely supplied label. -/
theorem expanded_rooted {root es} (h : ExpandedProperPath g root es) :
    es.head?=some (.inr (.inl root)) := by
  induction h with
  | base _ rooted => exact rooted
  | insert r pre loop suffix _ _ preEnd _ _ _ _ _ _ ih _ =>
    cases pre with
    | nil => simp at preEnd
    | cons e rest => simpa using ih
end
end Lamping.AG




namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
/-- Ordinary forward paths embed into the expanded direction grammar. -/
theorem Forward.expanded {es : List (Endpoint g)} (h : Forward g es) : ExpandedForward g es := by
  induction h with
  | single e => exact .single e
  | node n p q ha hl hd hs ih =>
    apply ExpandedForward.cons
    · rw [ha,hl]; exact .node n p q hd
    · exact ih
  | transparent w d ha hl hs ih =>
    apply ExpandedForward.cons
    · rw [ha,hl]; exact .transparent w d
    · exact ih
/-- Expanded labels retain ordinary proper labels at each unchanged segment. -/
theorem Labelling.expanded {es : List (Endpoint g)} (h : Labelling g es a b) :
    ExpandedLabelling g es a b := by
  induction h with
  | single e a => exact .single e a
  | cons ht hs ih => exact .cons (.ordinary ht) ih
/-- The original binding-loop notion embeds into the expanded loop notion.
The converse is not claimed (Ex3.5.20 concerns generation equivalence). -/
def BindingLoop.expanded {es : List (Endpoint g)} {a b : Context} (h : BindingLoop g es a b) :
    ExpandedBindingLoop g es a b where
  binder := h.binder
  isLam := h.isLam
  body := h.body
  bind := h.bind
  body_role := h.body_role
  bind_role := h.bind_role
  start := h.start
  finish := h.finish
  proper := h.proper.expanded
  forward := h.forward.expanded
  shell := h.shell
end
end Lamping.AG

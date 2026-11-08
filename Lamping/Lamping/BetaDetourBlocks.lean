import Lamping.Lamping.PathSiteBetaDirection
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

/-- A finite ordered stream of ordinary true turns and complete paired beta
backward blocks. The index counts blocks, not physical segments. Ordinary
turns may use active proper nodes; no generation or semantic invariant is a
constructor field. Labels are supplied only for actual local ordinary rules. -/
inductive BetaDetourBlocks : List (Endpoint g) → Context → Context → Nat → Prop where
  | single (e a) : BetaDetourBlocks [e] a a 0
  | ordinary {e f tail a middle b count}
      (turn : LabelledTurn g (g.wire e) f a middle)
      (rest : BetaDetourBlocks (f::tail) middle b count) :
      BetaDetourBlocks (e::f::tail) a b count
  | backward (edge : BetaEdge g) (e : Endpoint g) {tail a b count}
      (arrival : g.wire e=.inl ⟨edge.lam,edge.lamBind⟩)
      (head : tail.head?=some edge.argEnd) (rest : BetaDetourBlocks tail a b count) :
      BetaDetourBlocks (e::(edge.reverseRoute++tail)) a b (count+1)

theorem BetaDetourBlocks.nonempty {es a b count} (path : BetaDetourBlocks g es a b count) : es≠[] := by
  cases path <;> simp

theorem Labelling.detour_blocks {es a b} (labels : Labelling g es a b) : BetaDetourBlocks g es a b 0 := by
  induction labels with
  | single e a => exact .single _ _
  | cons turn rest ih => exact .ordinary turn ih

/-- Appending one complete backward block to an ordinary assigned prefix
increments the block count exactly once, retaining that prefix's final segment. -/
theorem BetaDetourBlocks.append_backward (edge : BetaEdge g) {pre tail : List (Endpoint g)}
    {input seam output : Context} {count : Nat} (prefixLabels : Labelling g pre input seam)
    (finish : pre.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)))
    (head : tail.head?=some edge.argEnd) (rest : BetaDetourBlocks g tail seam output count) :
    BetaDetourBlocks g (pre++edge.reverseRoute++tail) input output (count+1) := by
  induction prefixLabels with
  | single e a =>
    have arrival : g.wire e=.inl ⟨edge.lam,edge.lamBind⟩ := by
      have same : e=g.wire (.inl ⟨edge.lam,edge.lamBind⟩) := Option.some.inj finish
      rw [same,Pairing.involutive]
    exact .backward edge e arrival head rest
  | cons turn after ih =>
    exact .ordinary turn (ih (by simpa only [List.getLast?_cons_cons] using finish) rest)

theorem BetaDetourBlocks.labelling {es a b count} (path : BetaDetourBlocks g es a b count) :
    ExpandedLabelling g es a b := by
  induction path with
  | single e a => exact .single _ _
  | ordinary turn rest ih => exact .cons (.ordinary turn) ih
  | @backward edge e tail a b count arrival head rest ih =>
    have reverse := (ExpandedLabelling.single (g:=g) e a).splice rfl
      (edge.reverse_labeling a).expanded edge.reverse_start (by
        change ExpandedTurn g (g.wire e) edge.ctxEnd a a
        rw [arrival]
        exact .bindToCtx edge a)
    have finish : ([e]++edge.reverseRoute).getLast?=some (g.wire edge.funEnd) := by
      simp only [List.getLast?_append,edge.reverse_finish,Option.some_or]
    exact reverse.splice finish ih head (by
      simpa only [Pairing.involutive] using ExpandedTurn.funToArg (g:=g) edge a)

theorem BetaDetourBlocks.zero_ordinary {es a b} (path : BetaDetourBlocks g es a b 0) : Labelling g es a b := by
  generalize countEq : 0=count at path
  induction path with
  | single e a => exact .single _ _
  | ordinary turn rest ih => exact .cons turn (ih countEq)
  | backward edge e arrival head rest ih => omega

/-- Prepending a finite ordinary piece retains exactly the remaining backward
block count. The actual seam turn is kept, with no endpoint or context reset. -/
theorem BetaDetourBlocks.splice_ordinary {pre tail : List (Endpoint g)} {a middle next b : Context} {count}
    (labels : Labelling g pre a middle) {e f : Endpoint g} (finish : pre.getLast?=some e)
    (rest : BetaDetourBlocks g tail next b count) (head : tail.head?=some f)
    (turn : LabelledTurn g (g.wire e) f middle next) :
    BetaDetourBlocks g (pre++tail) a b count := by
  induction labels with
  | single x a =>
    have same : x=e := Option.some.inj finish
    subst e
    obtain ⟨xs,same⟩ := List.head?_eq_some_iff.mp head
    rw [same] at rest ⊢
    exact .ordinary turn rest
  | cons localTurn after ih =>
    exact .ordinary localTurn (ih (by simpa using finish) turn)

/-- The first backward block has a genuinely ordinary labelled prefix ending
at that block's physical binder. Deleting it leaves one fewer block, retaining
the complete ordered suffix and its actual input/output contexts. -/
theorem BetaDetourBlocks.first_backward {es a b count}
    (path : BetaDetourBlocks g es a b count) (positive : 0<count) :
    ∃ (edge : BetaEdge g) (pre tail : List (Endpoint g)) (seam : Context) (remaining : Nat),
      count=remaining+1 ∧ es=pre++edge.reverseRoute++tail ∧
      Labelling g pre a seam ∧ pre.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) ∧
      tail.head?=some edge.argEnd ∧ BetaDetourBlocks g tail seam b remaining := by
  induction path with
  | single e a => omega
  | @ordinary e f tail a middle b count turn rest ih =>
    obtain ⟨edge,pre,suffix,seam,remaining,countEq,decomp,labels,finish,head,path⟩ := ih positive
    have preHead : pre.head?=some f := by
      have nonempty := labels.nonempty
      cases pre with
      | nil => exact False.elim (nonempty rfl)
      | cons x xs => exact congrArg (fun xs => xs.head?) decomp.symm
    obtain ⟨xs,same⟩ := List.head?_eq_some_iff.mp preHead
    refine ⟨edge,e::pre,suffix,seam,remaining,countEq,?_,?_,?_,head,path⟩
    · simpa only [List.cons_append] using congrArg (List.cons e) decomp
    · rw [same] at labels ⊢
      exact .cons turn labels
    · simp only [List.getLast?_cons,finish,Option.getD_some]
  | @backward edge e tail a b count arrival head rest ih =>
    refine ⟨edge,[e],tail,a,count,rfl,rfl,.single _ _,?_,head,rest⟩
    have same := congrArg g.wire.mate arrival
    simpa only [Pairing.involutive] using congrArg some same

private theorem lambda_context_negative {kind : Kind} (p : Port kind) (base : Bool)
    (sort : kind=.op .lam) (role : HEq p (Sum.inl () : Port (.op .lam))) :
    flowPort kind base p=false := by
  subst kind
  have same : p=.inl () := eq_of_heq role
  subst p
  rfl

theorem BetaEdge.ctx_polarity (edge : BetaEdge g) (nodes : N → Bool) (boundary : B → Bool) (vertices : W → Bool) :
    flowEndpoint g nodes boundary vertices edge.ctxEnd=false :=
  lambda_context_negative edge.lamCtx (nodes edge.lam) (congrArg Label.sort edge.lamLabel) edge.lamCtx_role

/-- A retained reversed principal departure in a genuine rooted stream cannot
be hidden in its ordinary/zero-block case. This checks the physical endpoint,
not a presumed syntactic tag on the stream. -/
theorem BetaDetourBlocks.positive_count {es a b count} (path : BetaDetourBlocks g es a b count)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (root : B) (rootPolarity : boundary root=true)
    (rooted : es.head?=some (.inr (.inl root))) (edge : BetaEdge g) (occurs : edge.ctxEnd ∈ es) :
    0<count := by
  by_cases zero : count=0
  · subst count
    have positive := (path.zero_ordinary g).root_positive_departures flow root rooted rootPolarity _ occurs
    rw [edge.ctx_polarity] at positive
    cases positive
  · omega
end
end Lamping.AG

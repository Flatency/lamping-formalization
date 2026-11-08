import Lamping.Lamping.BetaDetourReflection
import Lamping.Lamping.BetaBindingProvenance
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Finite paired streams for ONE physical rewrite. All reversed blocks use
the same supplied edge. This records provenance that generic blocks erase. -/
inductive FixedBetaDetourBlocks (edge : BetaEdge g) :
    List (Endpoint g) → Context → Context → Nat → Prop where
  | single (e a) : FixedBetaDetourBlocks edge [e] a a 0
  | ordinary {e f tail a middle b count}
      (turn : LabelledTurn g (g.wire e) f a middle)
      (rest : FixedBetaDetourBlocks edge (f::tail) middle b count) :
      FixedBetaDetourBlocks edge (e::f::tail) a b count
  | backward (e : Endpoint g) {tail a b count}
      (arrival : g.wire e=.inl ⟨edge.lam,edge.lamBind⟩)
      (head : tail.head?=some edge.argEnd)
      (rest : FixedBetaDetourBlocks edge tail a b count) :
      FixedBetaDetourBlocks edge (e::(edge.reverseRoute++tail)) a b (count+1)

theorem FixedBetaDetourBlocks.erase {edge : BetaEdge g} {es a b count}
    (path : FixedBetaDetourBlocks edge es a b count) : BetaDetourBlocks g es a b count := by
  induction path with
  | single e a => exact .single _ _
  | ordinary turn rest ih => exact .ordinary turn ih
  | backward e arrival head rest ih => exact .backward edge e arrival head ih

theorem FixedBetaDetourBlocks.splice_ordinary {edge : BetaEdge g}
    {pre tail : List (Endpoint g)} {a middle next b : Context} {count}
    (labels : Labelling g pre a middle) {e f : Endpoint g}
    (finish : pre.getLast?=some e)
    (rest : FixedBetaDetourBlocks edge tail next b count) (head : tail.head?=some f)
    (turn : LabelledTurn g (g.wire e) f middle next) :
    FixedBetaDetourBlocks edge (pre++tail) a b count := by
  induction labels with
  | single x a =>
    have same : x=e := Option.some.inj finish
    subst e
    obtain ⟨xs,same⟩ := List.head?_eq_some_iff.mp head
    rw [same] at rest ⊢
    exact .ordinary turn rest
  | cons localTurn after ih =>
    exact .ordinary localTurn (ih (by simpa using finish) turn)

/-- The first reversed block belongs to the fixed rewrite, rather than an
existentially reselected beta edge of the same source graph. -/
theorem FixedBetaDetourBlocks.first_backward {edge : BetaEdge g} {es a b count}
    (path : FixedBetaDetourBlocks edge es a b count) (positive : 0<count) :
    ∃ (pre tail : List (Endpoint g)) (seam : Context) (remaining : Nat),
      count=remaining+1 ∧ es=pre++edge.reverseRoute++tail ∧
      Labelling g pre a seam ∧
      pre.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) ∧
      tail.head?=some edge.argEnd ∧ FixedBetaDetourBlocks edge tail seam b remaining := by
  induction path with
  | single e a => omega
  | @ordinary e f tail a middle b count turn rest ih =>
    obtain ⟨pre,suffix,seam,remaining,countEq,decomp,labels,finish,head,path⟩ := ih positive
    have preHead : pre.head?=some f := by
      cases pre with
      | nil => exact False.elim (labels.nonempty rfl)
      | cons x xs => exact congrArg (fun xs => xs.head?) decomp.symm
    obtain ⟨xs,same⟩ := List.head?_eq_some_iff.mp preHead
    refine ⟨e::pre,suffix,seam,remaining,countEq,?_,?_,?_,head,path⟩
    · simpa only [List.cons_append] using congrArg (List.cons e) decomp
    · rw [same] at labels ⊢
      exact .cons turn labels
    · simp only [List.getLast?_cons,finish,Option.getD_some]
  | @backward e tail a b count arrival head rest ih =>
    refine ⟨[e],tail,a,count,rfl,rfl,.single _ _,?_,head,rest⟩
    have same := congrArg g.wire.mate arrival
    simpa only [Pairing.involutive] using congrArg some same

private theorem binding_kind (actual : Label signature) (p : Port actual.sort) (index : Nat)
    (labelEq : actual=label .lam index) (role : HEq p lamBind) :
    portKind actual.sort p=some .var := by
  subst actual
  have same : p=lamBind := eq_of_heq role
  subst p
  rfl

/-- The first reversed block in a rooted fixed stream has a genuinely
ordinary RootAccess at THIS edge's binding port, with its actual assignment.
This does not assert totality or root reachability of any argument suffix. -/
theorem FixedBetaDetourBlocks.first_backward_root {edge : BetaEdge g} {es a b count}
    (path : FixedBetaDetourBlocks edge es a b count) (positive : 0<count)
    {directions : B → Bool} (flow : FlowBalance g directions)
    (root : B) (rootPositive : directions root=true)
    (rooted : es.head?=some (.inr (.inl root))) :
    ∃ (pre : RootAccess g root) (tail : List (Endpoint g)) (seam : Context) (remaining : Nat),
      count=remaining+1 ∧ es=pre.val++edge.reverseRoute++tail ∧
      Labelling g pre.val a seam ∧
      pre.val.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) ∧
      tail.head?=some edge.argEnd ∧ FixedBetaDetourBlocks edge tail seam b remaining := by
  obtain ⟨pre,tail,seam,remaining,countEq,split,labels,finish,head,rest⟩ := path.first_backward positive
  have preRoot : pre.head?=some (.inr (.inl root)) := by
    cases pre with
    | nil => exact False.elim (labels.nonempty rfl)
    | cons e xs => simpa only [split,List.cons_append,List.head?_cons] using rooted
  have kind : accessKind g pre=some .var := by
    simp only [accessKind,finish,Option.bind_some,Pairing.involutive]
    exact binding_kind _ _ _ edge.lamLabel edge.lamBind_role
  let access : RootAccess g root :=
    ⟨pre,⟨⟨⟨a,seam,labels⟩,labels.root_forward_of_flow flow root preRoot rootPositive⟩,
      preRoot,⟨.var,kind⟩⟩⟩
  exact ⟨access,tail,seam,remaining,countEq,split,labels,finish,head,rest⟩
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

private theorem outside_turn {x y : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)}
    {a b : Context} (turn : PlugTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net (.inl x) (.inl y) a b) :
    LabelledTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed) x y a b := by
  cases turn with
  | left localTurn => exact localTurn

private theorem enter_context {x : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)}
    {y : Endpoint (Schema.beta i).right.net} {a b : Context}
    (turn : PlugTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net (.inl x) (.inr y) a b) : a=b := by
  cases turn
  rfl

private theorem leave_context {x : Endpoint (Schema.beta i).right.net}
    {y : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)} {a b : Context}
    (turn : PlugTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net (.inr x) (.inl y) a b) : a=b := by
  cases turn
  rfl

private theorem context_stream {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {e : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)}
    {oldTail : List (Endpoint site.net)} {a b : Context} {count : Nat}
    (arrival : (cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e=
      .inr (.inl (.inr (.inl false))))
    (head : oldTail.head?=some (site.outsideEnd (.inr (.inl (.inr (.inr true))))))
    (rest : FixedBetaDetourBlocks edge oldTail a b count) :
    FixedBetaDetourBlocks edge (site.outsideEnd e::(edge.principal++oldTail)) a b count := by
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
  have starts : oldTail.head?=some (.inl ⟨edge.lam,edge.lamBody⟩) := by
    rw [geometry.body]
    exact head
  exact rest.splice_ordinary principal finish starts (by
    simpa only [Pairing.involutive] using edge.lam_body_turn a)

/-- The actual same-site residual supplies fixed-edge provenance for every
backward block, together with the original input and output assignments. -/
theorem BetaPathResidual.fixed_detour_blocks {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) {raw old}
    (relation : BetaPathResidual site edge raw old) {a b : Context}
    (labels : PlugLabelling (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net raw a b) :
    ∃ count,FixedBetaDetourBlocks edge old a b count := by
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
        refine ⟨count+1,.backward (site.outsideEnd e) ?_ ?_ rest⟩
        · rw [site.outsideEnd_wire,arrival,geometry.binding]
          rfl
        · rw [geometry.argument]
          exact relation.head site rfl

/-- A positive rooted ancestor stream actually encounters the old syntax
fiber of THIS rewrite. Its first reversed entrance has a real source bound
variable below that redex, and the literal remaining stream has fewer blocks. -/
theorem PathSite.fixed_stream_old_fiber
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    (principal : SiteActionPrincipal site)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (rootPositive : directions root=true)
    {t : Lambda.Term} (matching : Matches site.net root t)
    (transparent : Transparency site.net root)
    {es : List (Endpoint site.net)} {a b : Context} {count : Nat}
    (path : FixedBetaDetourBlocks edge es a b count) (positive : 0<count)
    (rooted : es.head?=some (.inr (.inl root))) :
    ∃ (pre : RootAccess site.net root) (tail : List (Endpoint site.net))
      (seam : Context) (remaining : Nat) (redex : Lambda.RedexOcc t) (q : Lambda.Path),
      count=remaining+1 ∧ es=pre.val++edge.reverseRoute++tail ∧
      Labelling site.net pre.val a seam ∧
      tail.head?=some edge.argEnd ∧ FixedBetaDetourBlocks edge tail seam b remaining ∧
      redex.val∈site.betaSyntaxFiber root t ∧
      accessWord site.net pre.val=redex.val++[.fn,.body]++q ∧
      Lambda.subtermAt t (accessWord site.net pre.val)=some (.var (Lambda.binderDepth q)) := by
  obtain ⟨pre,tail,seam,remaining,countEq,split,labels,finish,head,rest⟩ :=
    path.first_backward_root positive flow root rootPositive rooted
  have actualFinish : pre.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),lamBind⟩)) := by
    rw [geometry.binding] at finish
    exact finish
  obtain ⟨redex,_parent,_binder,loop,_input,_middle,_output,_binding,member,_word,
      _principalSplit,_bindingSplit,_binderEq,_before,words,lookup⟩ :=
    site.beta_binding_access_provenance principal flow root rootPositive matching transparent pre actualFinish
  exact ⟨pre,tail,seam,remaining,redex,accessWord site.net loop,
    countEq,split,labels,head,rest,member,words,lookup⟩
end
end Lamping.AG

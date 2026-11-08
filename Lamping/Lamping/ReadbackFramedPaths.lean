import Lamping.Lamping.ReadbackBinderCandidates
import Lamping.Lamping.ReadbackScanSimulation

namespace Lamping.AG.Readback
open Graph Lambda

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

/-- A finite read-task trace keeps the literal root path. Lambda-body steps
push their actual occurrence; application and control steps retain the stack.
This is an internal execution invariant, not an input to readback. -/
inductive FramedPath (root : B) (input : ContextData) :
    List (Endpoint g) → ContextData → List (BinderFrame g) → Prop where
  | initial : FramedPath root input [.inr (.inl root)] input []
  | scan {path before frames e f after}
      (prior : FramedPath root input path before frames)
      (last : path.getLast?=some e)
      (step : scanOne g e before=.next f after) :
      FramedPath root input (path++[f]) after frames
  | application {path context frames e}
      (prior : FramedPath root input path context frames)
      (last : path.getLast?=some e)
      (node : N) (ctx child : Port (g.label node).sort)
      (sort : (g.label node).sort=.op .app)
      (ctxRole : HEq ctx appCtx)
      (childRole : HEq child (Sum.inl () : Port (.op .app)) ∨HEq child appArg)
      (arrives : g.wire e=.inl ⟨node,ctx⟩) :
      FramedPath root input (path++[.inl ⟨node,child⟩]) context frames
  | body {path context frames e}
      (prior : FramedPath root input path context frames)
      (last : path.getLast?=some e)
      (node : N) (ctx body : Port (g.label node).sort)
      (sort : (g.label node).sort=.op .lam)
      (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
      (bodyRole : HEq body lamBody)
      (arrives : g.wire e=.inl ⟨node,ctx⟩) :
      FramedPath root input (path++[.inl ⟨node,body⟩]) context
        (⟨node,(g.label node).index,path,.inl ⟨node,body⟩,context⟩::frames)

private theorem app_turn {kind : Kind} {index : Nat} (ctx child : Port kind)
    (sort : kind=.op .app) (ctxRole : HEq ctx appCtx)
    (childRole : HEq child (Sum.inl () : Port (.op .app)) ∨HEq child appArg)
    (a : Context) : Traversal index kind ctx child a a ∧ForwardPorts kind ctx child := by
  subst kind
  cases eq_of_heq ctxRole
  rcases childRole with first|second
  · cases eq_of_heq first
    exact ⟨.direct (.appFun a),rfl,Or.inl rfl⟩
  · cases eq_of_heq second
    exact ⟨.direct (.appArg a),rfl,Or.inr rfl⟩

private theorem body_turn {kind : Kind} {index : Nat} (ctx body : Port kind)
    (sort : kind=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (bodyRole : HEq body lamBody) (a : Context) :
    Traversal index kind ctx body a a ∧ForwardPorts kind ctx body := by
  subst kind
  cases eq_of_heq ctxRole
  cases eq_of_heq bodyRole
  exact ⟨.direct (.lamBody a),rfl,rfl⟩

private theorem forward_append {es : List (Endpoint g)} {e f : Endpoint g}
    (forward : Forward g es) (last : es.getLast?=some e)
    (step : Forward g [e,f]) : Forward g (es++[f]) := by
  induction forward with
  | single x =>
    have same : x=e := by simpa using last
    subst x
    exact step
  | node node p q arrives leaves direction after ih =>
    exact .node node p q arrives leaves direction (ih (by simpa using last))
  | transparent vertex direction arrives leaves after ih =>
    exact .transparent vertex direction arrives leaves (ih (by simpa using last))

private theorem executeControl_kind {i kind p a q b}
    (success : executeControl i kind p a=some (q,b)) :
    kind=.op .fan ∨kind=.op .cro ∨kind=.op .bra := by
  cases kind with
  | garbage => simp [executeControl] at success
  | op op => cases op with
    | app => simp [executeControl] at success
    | lam => simp [executeControl] at success
    | fan => exact Or.inl rfl
    | cro => exact Or.inr (Or.inl rfl)
    | bra => exact Or.inr (Or.inr rfl)

private theorem controls_forward (kind : Kind) (p q : Port kind)
    (control : kind=.op .fan ∨kind=.op .cro ∨kind=.op .bra) : ForwardPorts kind p q := by
  rcases control with rfl|rfl|rfl <;> trivial

theorem scanOne_next_forward {e f : Endpoint g} {a b : ContextData}
    (step : scanOne g e a=.next f b) : Forward g [e,f] := by
  cases wireEq : g.wire e with
  | inl actual =>
    obtain ⟨node,port⟩ := actual
    cases role : portKind (g.label node).sort port with
    | some kind => simp [scanOne,wireEq,role] at step
    | none =>
      cases success : executeControl (g.label node).index (g.label node).sort port a with
      | none => simp [scanOne,wireEq,role,success] at step
      | some result =>
        obtain ⟨out,after⟩ := result
        simp only [scanOne,wireEq,role,success,ScanResult.next.injEq] at step
        obtain ⟨rfl,rfl⟩ := step
        exact .node node port out wireEq rfl
          (controls_forward _ _ _ (executeControl_kind success)) (.single _)
  | inr target => cases target with
    | inl boundary => simp [scanOne,wireEq] at step
    | inr wire =>
      obtain ⟨vertex,direction⟩ := wire
      simp only [scanOne,wireEq,ScanResult.next.injEq] at step
      obtain ⟨rfl,rfl⟩ := step
      exact .transparent vertex direction wireEq rfl (.single _)

namespace FramedPath

theorem labels {root input path context frames}
    (trace : FramedPath g root input path context frames) :
    Labelling g path (Context.ofList input) (Context.ofList context) := by
  induction trace with
  | initial => exact .single _ _
  | scan prior last step ih => exact ih.append_turn last (scanOne_next_sound _ _ _ _ _ step)
  | application prior last node ctx child sort ctxRole childRole arrives ih =>
    apply ih.append_turn last
    rw [arrives]
    exact .node node ctx child
      ((app_turn (index:=(g.label node).index) ctx child sort ctxRole childRole _).1)
  | body prior last node ctx body sort ctxRole bodyRole arrives ih =>
    apply ih.append_turn last
    rw [arrives]
    exact .node node ctx body
      ((body_turn (index:=(g.label node).index) ctx body sort ctxRole bodyRole _).1)

theorem forward {root input path context frames}
    (trace : FramedPath g root input path context frames) : Forward g path := by
  induction trace with
  | initial => exact .single _
  | scan prior last step ih => exact forward_append g ih last (scanOne_next_forward g step)
  | application prior last node ctx child sort ctxRole childRole arrives ih =>
    exact forward_append g ih last (.node node ctx child arrives rfl
      (app_turn (index:=0) ctx child sort ctxRole childRole Context.empty).2 (.single _))
  | body prior last node ctx body sort ctxRole bodyRole arrives ih =>
    exact forward_append g ih last (.node node ctx body arrives rfl
      (body_turn (index:=0) ctx body sort ctxRole bodyRole Context.empty).2 (.single _))

theorem nonempty {root input path context frames}
    (trace : FramedPath g root input path context frames) : path≠[] := by
  intro empty
  have labels := trace.labels
  rw [empty] at labels
  cases labels

theorem rooted {root input path context frames}
    (trace : FramedPath g root input path context frames) :
    path.head?=some (.inr (.inl root)) := by
  induction trace with
  | initial => rfl
  | scan prior last step ih => simp only [List.head?_append,ih,Option.some_or]
  | application prior last node ctx child sort ctxRole childRole arrives ih =>
    simp only [List.head?_append,ih,Option.some_or]
  | body prior last node ctx body sort ctxRole bodyRole arrives ih =>
    simp only [List.head?_append,ih,Option.some_or]

/-- Concrete metadata recorded when this exact frame was pushed. The seam
label is inherited from the actual root-input labelling of its literal prefix. -/
def FrameOrigin (input : ContextData) (frame : BinderFrame g) : Prop :=
  frame.index=(g.label frame.node).index ∧(g.label frame.node).sort=.op .lam ∧
  ∃ ctx body : Port (g.label frame.node).sort,
    HEq ctx (Sum.inl () : Port (.op .lam)) ∧HEq body lamBody ∧
    frame.bodyDeparture=.inl ⟨frame.node,body⟩ ∧
    frame.stem.getLast?=some (g.wire (.inl ⟨frame.node,ctx⟩)) ∧
    Labelling g frame.stem (Context.ofList input) (Context.ofList frame.seam)

theorem frame_origin {root input path context frames}
    (trace : FramedPath g root input path context frames)
    (frame : BinderFrame g) (member : frame∈frames) : FrameOrigin g input frame := by
  induction trace with
  | initial => cases member
  | scan prior last step ih => exact ih member
  | application prior last node ctx child sort ctxRole childRole arrives ih => exact ih member
  | body prior last node ctx body sort ctxRole bodyRole arrives ih =>
    rcases List.mem_cons.mp member with same|member
    · subst frame
      have endpoint := congrArg g.wire.mate arrives
      have eEq := (g.pairing _).symm.trans endpoint
      exact ⟨rfl,sort,ctx,body,ctxRole,bodyRole,rfl,
        last.trans (congrArg some eEq),prior.labels⟩
    · exact ih member

/-- Stack distance counts later literal lambda-body turns on this same path. -/
def FrameCut (path : List (Endpoint g)) (frame : BinderFrame g) (distance : Nat) : Prop :=
  ∃ tail,path=frame.stem++frame.bodyDeparture::tail ∧
    binderDepth (accessWord g (frame.bodyDeparture::tail))=distance

private theorem frameCut_append {path : List (Endpoint g)} {frame : BinderFrame g} {distance : Nat}
    (cut : FrameCut g path frame distance) (next : Endpoint g) :
    FrameCut g (path++[next]) frame (distance+binderDepth (arrivalWord g next)) := by
  obtain ⟨tail,split,count⟩ := cut
  refine ⟨tail++[next],by simp only [split,List.append_assoc,List.cons_append],?_⟩
  have nonempty : (frame.bodyDeparture::tail : List (Endpoint g))≠[] := by simp
  have word := accessWord_append g (frame.bodyDeparture::tail) [next] nonempty
  simp only [List.flatMap_singleton] at word
  change binderDepth (accessWord g ((frame.bodyDeparture::tail)++[next]))=_
  rw [word,binderDepth_append,count]

private theorem scanOne_next_empty_word {e f : Endpoint g} {a b : ContextData}
    (step : scanOne g e a=.next f b) : arrivalWord g f=[] := by
  cases wireEq : g.wire e with
  | inl actual =>
    obtain ⟨node,port⟩ := actual
    cases role : portKind (g.label node).sort port with
    | some kind => simp [scanOne,wireEq,role] at step
    | none =>
      cases success : executeControl (g.label node).index (g.label node).sort port a with
      | none => simp [scanOne,wireEq,role,success] at step
      | some result =>
        obtain ⟨out,after⟩ := result
        simp only [scanOne,wireEq,role,success,ScanResult.next.injEq] at step
        obtain ⟨rfl,rfl⟩ := step
        have controls := executeControl_kind success
        have empty (kind : Kind) (q : Port kind)
            (control : kind=.op .fan ∨kind=.op .cro ∨kind=.op .bra) :
            (match kind,q with
            | .op .app,.inl () => [Step.fn]
            | .op .app,.inr true => [Step.arg]
            | .op .lam,.inr true => [Step.body]
            | _,_ => [])=[] := by
          rcases control with rfl|rfl|rfl <;> rfl
        exact empty _ out controls
  | inr target => cases target with
    | inl boundary => simp [scanOne,wireEq] at step
    | inr wire =>
      obtain ⟨vertex,direction⟩ := wire
      simp only [scanOne,wireEq,ScanResult.next.injEq] at step
      obtain ⟨rfl,rfl⟩ := step
      rfl

private def departureToken (kind : Kind) (port : Port kind) : Path :=
  match kind,port with
      | .op .app,.inl () => [Step.fn]
      | .op .app,.inr true => [Step.arg]
      | .op .lam,.inr true => [Step.body]
      | _,_ => []

private theorem app_child_depth {kind : Kind} (child : Port kind)
    (sort : kind=.op .app)
    (role : HEq child (Sum.inl () : Port (.op .app)) ∨HEq child appArg) :
    binderDepth (departureToken kind child)=0 := by
  subst kind
  rcases role with first|second
  · cases eq_of_heq first; rfl
  · cases eq_of_heq second; rfl

private theorem body_depth {kind : Kind} (body : Port kind)
    (sort : kind=.op .lam) (role : HEq body lamBody) :
    binderDepth (departureToken kind body)=1 := by
  subst kind
  cases eq_of_heq role
  rfl

theorem frame_cut {root input path context frames}
    (trace : FramedPath g root input path context frames)
    (frame : BinderFrame g) (distance : Nat) (atFrame : frames[distance]?=some frame) :
    FrameCut g path frame distance := by
  induction trace generalizing distance with
  | initial => simp at atFrame
  | @scan path before frames e f after prior last step ih =>
    have cut := frameCut_append g (ih distance atFrame) f
    simpa only [scanOne_next_empty_word g step,binderDepth,Nat.add_zero] using cut
  | application prior last node ctx child sort ctxRole childRole arrives ih =>
    have cut := frameCut_append g (ih distance atFrame) (.inl ⟨node,child⟩)
    have zero : binderDepth (arrivalWord g (.inl ⟨node,child⟩))=0 :=
      app_child_depth child sort childRole
    simpa only [zero,Nat.add_zero] using cut
  | body prior last node ctx body sort ctxRole bodyRole arrives ih =>
    cases distance with
    | zero =>
      have same := Option.some.inj atFrame
      cases same
      exact ⟨[],rfl,rfl⟩
    | succ distance =>
      have cut := frameCut_append g (ih distance atFrame) (.inl ⟨node,body⟩)
      have one : binderDepth (arrivalWord g (.inl ⟨node,body⟩))=1 := body_depth body sort bodyRole
      simpa only [one] using cut

private theorem split_snoc {T : Type} (path : List T) (next : T)
    (pre : List T) (body : T) (tail : List T) (split : path++[next]=pre++body::tail) :
    (pre=path ∧body=next ∧tail=[]) ∨
      ∃ oldTail,path=pre++body::oldTail ∧tail=oldTail++[next] := by
  induction path generalizing pre with
  | nil =>
    cases pre with
    | nil =>
      obtain ⟨heads,rest⟩ := List.cons.inj split
      exact Or.inl ⟨rfl,heads.symm,rest.symm⟩
    | cons first rest =>
      have restEq := (List.cons.inj split).2
      have lengthEq := congrArg List.length restEq
      simp at lengthEq
      omega
  | cons first rest ih =>
    cases pre with
    | nil =>
      obtain ⟨heads,restEq⟩ := List.cons.inj split
      subst body
      exact Or.inr ⟨rest,rfl,restEq.symm⟩
    | cons head pre =>
      obtain ⟨heads,restEq⟩ := List.cons.inj split
      subst head
      rcases ih pre restEq with ⟨rfl,same,empty⟩ | ⟨oldTail,oldSplit,tailEq⟩
      · exact Or.inl ⟨rfl,same,empty⟩
      · exact Or.inr ⟨oldTail,by rw [oldSplit]; rfl,tailEq⟩

private theorem body_token {kind : Kind} (body : Port kind)
    (sort : kind=.op .lam) (role : HEq body lamBody) :
    departureToken kind body=[.body] := by
  subst kind
  cases eq_of_heq role
  rfl

/-- Every literal lambda-body departure in this finite execution path was
actually pushed. This includes repeated visits to the same physical lambda. -/
theorem body_frame_exists {root input path context frames}
    (trace : FramedPath g root input path context frames)
    (pre : List (Endpoint g)) (body : Endpoint g) (tail : List (Endpoint g))
    (split : path=pre++body::tail) (token : arrivalWord g body=[.body]) :
    ∃ (frame : BinderFrame g) (distance : Nat),frames[distance]?=some frame ∧
      frame.stem=pre ∧frame.bodyDeparture=body := by
  induction trace generalizing pre tail with
  | initial =>
    cases pre with
    | nil =>
      have headEq := (List.cons.inj split).1
      subst body
      cases token
    | cons first pre =>
      have lengthEq := congrArg List.length split
      simp at lengthEq
  | @scan path before frames e next after prior last step ih =>
    rcases split_snoc path next pre body tail split with
      ⟨rfl,rfl,empty⟩ | ⟨oldTail,oldSplit,tailEq⟩
    · have noToken := scanOne_next_empty_word g step
      rw [noToken] at token
      cases token
    · exact ih pre oldTail oldSplit
  | @application path context frames e prior last node ctx child sort ctxRole childRole arrives ih =>
    rcases split_snoc path (.inl ⟨node,child⟩) pre body tail split with
      ⟨rfl,rfl,empty⟩ | ⟨oldTail,oldSplit,tailEq⟩
    · have zero : binderDepth (arrivalWord g (.inl ⟨node,child⟩))=0 :=
        app_child_depth child sort childRole
      rw [token] at zero
      cases zero
    · exact ih pre oldTail oldSplit
  | @body path context frames e prior last node ctx actualBody sort ctxRole bodyRole arrives ih =>
    rcases split_snoc path (.inl ⟨node,actualBody⟩) pre body tail split with
      ⟨rfl,rfl,empty⟩ | ⟨oldTail,oldSplit,tailEq⟩
    · exact ⟨_,0,rfl,rfl,rfl⟩
    · obtain ⟨frame,distance,indexed,stemEq,bodyEq⟩ := ih pre oldTail oldSplit
      exact ⟨frame,distance+1,indexed,stemEq,bodyEq⟩

private theorem variable_port (kind : Kind) (port : Port kind)
    (terminal : portKind kind port=some .var) : HEq port lamBind := by
  cases kind with
  | garbage => cases terminal
  | op op =>
    cases op <;> cases port with
    | inl slot => cases slot; cases terminal
    | inr side => cases side <;> first | rfl | cases terminal

private theorem variable_sort (kind : Kind) (port : Port kind)
    (terminal : portKind kind port=some .var) : kind=.op .lam := by
  cases kind with
  | garbage => cases terminal
  | op op =>
    cases op <;> cases port with
    | inl slot => cases slot; cases terminal
    | inr side => cases side <;> first | rfl | cases terminal

private theorem lambda_ports (kind : Kind) (sort : kind=.op .lam) :
    ∃ ctx body : Port kind,HEq ctx (Sum.inl () : Port (.op .lam)) ∧HEq body lamBody := by
  subst kind
  exact ⟨.inl (),lamBody,HEq.rfl,HEq.rfl⟩

section
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]

/-- Every candidate accepted at a genuine variable arrival identifies a real
binding suffix of the same execution path, with exactly its stack distance.
The physical metadata and suffix count are derived from FramedPath itself. -/
theorem candidate_binding_suffix {root input path context frames}
    (trace : FramedPath g root input path context frames)
    (arrival : NodePort signature N g.label)
    (finish : path.getLast?=some (g.wire (.inl arrival)))
    (terminal : portKind (g.label arrival.1).sort arrival.2=some .var)
    (distance : Nat) (accepted : distance∈binderCandidates g frames arrival.1 path context) :
    BindingSuffix g path distance := by
  obtain ⟨frame,atFrame,nodeEq,shell,tail,pathSplit⟩ :=
    (mem_binderCandidates frames arrival.1 path context distance).mp accepted
  have indexed := List.mk_mem_zipIdx_iff_getElem?.mp atFrame
  have member := List.mem_of_getElem? indexed
  obtain ⟨indexEq,sort,ctx,body,ctxRole,bodyRole,bodyEq,prefixEnd,prefixLabels⟩ :=
    frame_origin g trace frame member
  obtain ⟨node,bind⟩ := arrival
  simp only at nodeEq
  subst node
  have bindRole := variable_port _ bind terminal
  have prefixTest : (frame.stem++[frame.bodyDeparture]).isPrefixOf path=true :=
    (runtime_prefix_iff _ _).mpr ⟨tail,by simpa only [List.append_assoc,List.singleton_append] using pathSplit⟩
  obtain ⟨actualTail,actualSplit,bound⟩ := frame_binding_suffix frame path input context
    ctx body bind sort ctxRole bodyRole bindRole indexEq bodyEq prefixEnd trace.labels
      trace.forward prefixLabels finish ((shellEqual_iff _ _ _).mpr shell) prefixTest
  obtain ⟨indexedTail,indexedSplit,count⟩ := frame_cut g trace frame distance indexed
  have tails : actualTail=indexedTail :=
    (List.cons.inj (List.append_cancel_left (actualSplit.symm.trans indexedSplit))).2
  rw [tails,count] at bound
  exact bound

/-- Matching is used only after the runtime candidate has been proved to be
an actual binding occurrence. Its observational uniqueness fixes the index. -/
theorem candidate_index_of_observes {root input path context frames}
    (trace : FramedPath g root input path context frames)
    (arrival : NodePort signature N g.label)
    (finish : path.getLast?=some (g.wire (.inl arrival)))
    (terminal : portKind (g.label arrival.1).sort arrival.2=some .var)
    (index : Nat) (observes : Observes g path (.var index))
    (distance : Nat) (accepted : distance∈binderCandidates g frames arrival.1 path context) :
    distance=index :=
  observes.2.2 distance (candidate_binding_suffix g trace arrival finish terminal distance accepted)

/-- Transparency supplies a shell-valid split for the very same assignment
as this execution trace. Its literal body occurrence must already be in the
stack. Observational uniqueness then identifies its lexical index. Neither
the original observation's chosen assignment nor a node-only search is used. -/
theorem observed_candidate_exists {root input path context frames}
    (trace : FramedPath g root input path context frames)
    (transparency : Transparency g root)
    (arrival : NodePort signature N g.label)
    (finish : path.getLast?=some (g.wire (.inl arrival)))
    (terminal : portKind (g.label arrival.1).sort arrival.2=some .var)
    (index : Nat) (observes : Observes g path (.var index)) :
    index∈binderCandidates g frames arrival.1 path context := by
  obtain ⟨node,bind⟩ := arrival
  have sort := variable_sort _ bind terminal
  have bindRole := variable_port _ bind terminal
  obtain ⟨ctx,body,ctxRole,bodyRole⟩ := lambda_ports _ sort
  obtain ⟨pre,loop,middle,binding,split,binderEq,preEnd,preLabels⟩ :=
    transparency path (Context.ofList input) (Context.ofList context) node ctx body bind
      sort ctxRole bodyRole bindRole trace.rooted finish trace.forward trace.labels
  rcases binding with ⟨binder,isLam,loopBody,loopBind,loopBodyRole,loopBindRole,
    start,last,loopLabels,loopForward,loopShell⟩
  dsimp only at binderEq
  subst binder
  have bodySame : loopBody=body := eq_of_heq (loopBodyRole.trans bodyRole.symm)
  subst loopBody
  obtain ⟨tail,loopEq⟩ := List.head?_eq_some_iff.mp start
  rw [loopEq] at split
  have token : arrivalWord g (.inl ⟨node,body⟩)=[.body] := body_token body sort bodyRole
  obtain ⟨frame,distance,atFrame,stemEq,bodyEq⟩ :=
    body_frame_exists g trace pre (.inl ⟨node,body⟩) tail split token
  obtain ⟨indexEq,frameSort,frameCtx,frameBody,frameCtxRole,frameBodyRole,
      frameDepEq,framePrefixEnd,framePrefixLabels⟩ :=
    frame_origin g trace frame (List.mem_of_getElem? atFrame)
  have nodeEq : frame.node=node :=
    congrArg Sigma.fst (Sum.inl.inj (frameDepEq.symm.trans bodyEq))
  rw [stemEq] at framePrefixLabels
  have seamEq : Context.ofList frame.seam=middle := framePrefixLabels.output_unique preLabels
  have shell : Context.SameShell frame.index (Context.ofList frame.seam) (Context.ofList context) := by
    rw [indexEq,nodeEq,seamEq]
    exact loopShell
  have accepted : distance∈binderCandidates g frames node path context := by
    apply (mem_binderCandidates frames node path context distance).mpr
    refine ⟨frame,List.mk_mem_zipIdx_iff_getElem?.mpr atFrame,nodeEq,shell,tail,?_⟩
    rw [stemEq,bodyEq]
    exact split
  have same := candidate_index_of_observes g trace ⟨node,bind⟩ finish terminal index observes distance accepted
  simpa only [same] using accepted

private theorem filterMap_projection_sublist {T : Type} (xs : List T)
    (test : T → Bool) (value : T → Nat) :
    List.Sublist (xs.filterMap (fun x => if test x then some (value x) else none)) (xs.map value) := by
  induction xs with
  | nil => exact .slnil
  | cons first rest ih =>
    by_cases accept : test first=true
    · simp only [List.filterMap_cons,if_pos accept,List.map_cons]
      exact .cons₂ _ ih
    · simp only [List.filterMap_cons,if_neg accept,List.map_cons]
      exact .cons _ ih

theorem binderCandidates_nodup (frames : List (BinderFrame g)) (node : N)
    (path : List (Endpoint g)) (context : ContextData) :
    (binderCandidates g frames node path context).Nodup := by
  have selected := filterMap_projection_sublist frames.zipIdx
    (fun (frame,_) => frame.node=node &&shellEqual frame.index frame.seam context &&
      (frame.stem++[frame.bodyDeparture]).isPrefixOf path) Prod.snd
  have unique : (frames.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  exact selected.nodup unique

/-- The finite search has exactly one candidate on a framed variable access.
This closes the missing/ambiguous runtime branches locally, not whole-machine
termination or preservation of FramedPath through task scheduling. -/
theorem observed_candidates_singleton {root input path context frames}
    (trace : FramedPath g root input path context frames)
    (transparency : Transparency g root)
    (arrival : NodePort signature N g.label)
    (finish : path.getLast?=some (g.wire (.inl arrival)))
    (terminal : portKind (g.label arrival.1).sort arrival.2=some .var)
    (index : Nat) (observes : Observes g path (.var index)) :
    binderCandidates g frames arrival.1 path context=[index] := by
  have present := observed_candidate_exists g trace transparency arrival finish terminal index observes
  have unique := candidate_index_of_observes g trace arrival finish terminal index observes
  have noDuplicates := binderCandidates_nodup g frames arrival.1 path context
  cases candidatesEq : binderCandidates g frames arrival.1 path context with
  | nil => simp [candidatesEq] at present
  | cons first rest =>
    have firstEq := unique first (by simp [candidatesEq])
    subst first
    have noRest : index∉rest := (List.nodup_cons.mp (by simpa only [candidatesEq] using noDuplicates)).1
    cases rest with
    | nil => rfl
    | cons second tail =>
      have secondEq := unique second (by simp [candidatesEq])
      subst second
      exact False.elim (noRest (by simp))

end

end FramedPath
end
end Lamping.AG.Readback

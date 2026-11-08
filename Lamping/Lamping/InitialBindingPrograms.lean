import Lamping.Lamping.InitialControlWords
namespace Lamping.AG
open Graph Lambda

private theorem lam_ports (actual : Label signature) (n : Nat) (lab : actual=label .lam n) :
    ∃ ctx body : Port actual.sort,HEq ctx (Sum.inl () : Port (.op .lam)) ∧HEq body lamBody := by
  subst actual
  exact ⟨.inl (),lamBody,HEq.rfl,HEq.rfl⟩

private theorem lam_event_none (index : Nat) (kind : Kind) (port : Port kind) (isLam : kind=.op .lam) :
    InitialOffsets.eventOfPort index kind port=none := by
  subst kind
  rfl

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
private theorem events_all_at_lam (es : List (Endpoint g)) (node : N) (port : Port (g.label node).sort)
    (isLam : (g.label node).sort=.op .lam) (last : es.getLast?=some (g.wire (.inl ⟨node,port⟩))) :
    InitialOffsets.eventsOfEdges g es=InitialOffsets.allEvents g es := by
  apply InitialOffsets.events_eq_allEvents
  intro e he
  have same : e=g.wire (.inl ⟨node,port⟩) := Option.some.inj (he.symm.trans last)
  unfold InitialOffsets.arrivalEvents
  rw [same,Pairing.involutive]
  change (InitialOffsets.eventOfPort _ _ _).toList=[]
  rw [lam_event_none _ _ _ isLam]
  rfl
end

/-- The physical control word of a closed initial proper-source path ending
at a binding port is one of the corrected descending programs. The shape is
extracted from an actual loop suffix; no context formula is assumed. -/
theorem encode_binding_program (t : Term) (closed : Closed t) (level : Nat)
    (es : List (Endpoint (encode level t).net)) (e f : Endpoint (encode level t).net)
    (sr : ProperRole) (m n : Nat)
    (source : AtProperRole (encode level t).net (.inl ()) e sr m) (outgoing : sr.outgoing)
    (target : AtProperRole (encode level t).net (.inl ()) f .lamBind n)
    (head : es.head?=some e) (last : es.getLast?=some ((encode level t).net.wire f))
    (labels : Labelling (encode level t).net es a b) :
    ∃ shape : InitialOffsets.Shape,InitialOffsets.eventsOfEdges (encode level t).net es=shape.events n := by
  cases target with
  | lamBind binder bind n lab bindRole =>
    obtain ⟨ctx,body,ctxRole,bodyRole⟩ := lam_ports _ n lab
    have isLam : ((encode level t).net.label binder).sort=.op .lam := congrArg Label.sort lab
    obtain ⟨pre,rooted,prefixLabels⟩ := encode_source_identity_prefix t level e sr m source outgoing
    cases es with
    | nil => cases head
    | cons first tail =>
      have same : first=e := Option.some.inj head
      subst first
      have whole := (prefixLabels a).join labels
      have wholeRoot : (pre++e::tail).head?=some (.inr (.inl (.inl ()))) := by
        cases pre <;> exact rooted
      have wholeLast : (pre++e::tail).getLast?=some ((encode level t).net.wire (.inl ⟨binder,bind⟩)) := by
        rw [List.getLast?_append,last]
        rfl
      obtain ⟨binderPre,loop,middle,binding,split,binderEq,binderLast,binderLabels⟩ :=
        encode_closed_transparency t closed level _ a b binder ctx body bind isLam ctxRole bodyRole bindRole
          wholeRoot wholeLast (encode_root_forward t level _ wholeRoot ⟨a,b,whole⟩) whole
      let raw : InitialOffsets.RawLoop (encode level t).net loop middle b := {
        binder := binding.binder, isLam := binding.isLam, body := binding.body, bind := binding.bind,
        body_role := binding.body_role,bind_role := binding.bind_role,start := binding.start,
        finish := binding.finish,proper := binding.proper }
      obtain ⟨shape,shapeWord⟩ := InitialOffsets.encode_rawLoop_shape t level loop middle b raw
      have index : ((encode level t).net.label raw.binder).index=n := by
        change ((encode level t).net.label binding.binder).index=n
        rw [binderEq,lab]
        rfl
      rw [index] at shapeWord
      obtain ⟨addr⟩ := encode_addressing t level
      have contextRole : AtProperRole (encode level t).net (.inl ()) (.inl ⟨binder,ctx⟩) .lamCtx n :=
        .lamCtx binder ctx n lab ctxRole
      obtain ⟨word,_,atPort,_⟩ := contextRole.context_address (Or.inr rfl) addr.nodes (boundaryAddressAt []) addr.vertices
      have atEnd : endpointAddress (encode level t).net addr.nodes (boundaryAddressAt []) addr.vertices
          ((encode level t).net.wire (.inl ⟨binder,ctx⟩))=some word :=
        (addr.wiring _).trans atPort
      have binderRoot : binderPre.head?=some (.inr (.inl (.inl ()))) := by
        cases binderPre with
        | nil => cases binderLast
        | cons x xs =>
          rw [split] at wholeRoot
          exact wholeRoot
      have noBinderEvents := addr.path_no_events _ (encode_root_initial t level _ binderRoot binderLabels)
        _ binderLast word atEnd
      have noBinderAll : InitialOffsets.allEvents (encode level t).net binderPre=[] :=
        (events_all_at_lam _ binderPre binder ctx isLam binderLast).symm.trans noBinderEvents
      have noSource := encode_source_prefix_no_events t level pre e sr m source outgoing rooted (prefixLabels a)
      have wholeWord : InitialOffsets.eventsOfEdges (encode level t).net (pre++e::tail)=shape.events n := by
        rw [events_all_at_lam _ _ binder bind isLam wholeLast,split]
        rw [InitialOffsets.allEvents,List.flatMap_append]
        change InitialOffsets.allEvents _ binderPre ++ InitialOffsets.allEvents _ loop=shape.events n
        rw [noBinderAll,List.nil_append,shapeWord]
      refine ⟨shape,?_⟩
      rw [InitialOffsets.events_join,noSource,List.nil_append] at wholeWord
      exact wholeWord
end Lamping.AG

import Lamping.Lamping.ReadbackMatchedAccess

namespace Lamping.AG.Readback
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Internal proof state at an actual proper observation. The machine still
stores only departure/stem/context/frames, and does not consume this relation. -/
structure ReadyAccess (input : ContextData) (access : RootAccess g root)
    (departure : Endpoint g) (stem : List (Endpoint g)) (context : ContextData)
    (frames : List (BinderFrame g)) : Prop where
  split : access.val=stem++[departure]
  framed : FramedPath g root input access.val context frames

namespace ReadyAccess

theorem terminal {input context : ContextData} {access : RootAccess g root} {departure : Endpoint g}
    {stem : List (Endpoint g)} {frames : List (BinderFrame g)}
    (ready : ReadyAccess input access departure stem context frames)
    (kind : AccessKind) (kindEq : accessKind g access.val=some kind) :
    ∃ arrival : NodePort signature N g.label,g.wire departure=.inl arrival ∧
      portKind (g.label arrival.1).sort arrival.2=some kind := by
  have last : access.val.getLast?=some departure := by rw [ready.split]; simp
  unfold accessKind at kindEq
  simp only [last,Option.bind_some] at kindEq
  cases wired : g.wire departure with
  | inl arrival => exact ⟨arrival,rfl,by simpa only [wired] using kindEq⟩
  | inr target => cases target <;> simp [wired] at kindEq

theorem finish {input context : ContextData} {access : RootAccess g root} {departure : Endpoint g}
    {stem : List (Endpoint g)} {frames : List (BinderFrame g)}
    (ready : ReadyAccess input access departure stem context frames)
    (arrival : NodePort signature N g.label) (wired : g.wire departure=.inl arrival) :
    access.val.getLast?=some (g.wire (.inl arrival)) := by
  rw [ready.split]
  simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have back := congrArg g.wire.mate wired
  exact congrArg some (by simpa only [Pairing.involutive] using back)

end ReadyAccess

theorem Matches.observes_lookup {term : Term} (matching : Matches g root term)
    (access : RootAccess g root) (subterm : Term)
    (lookup : subtermAt term (accessWord g access.val)=some subterm) :
    Observes g access.val (syntaxShape subterm) := by
  obtain ⟨bijection,corresponds,_prefixProof⟩ := matching
  obtain ⟨word,other,otherLookup,observes⟩ := corresponds access
  rw [←word] at otherLookup
  have same := Option.some.inj (lookup.symm.trans otherLookup)
  subst other
  exact observes

private theorem observed_sort (kind : Kind) (port : Port kind) (observation : AccessKind)
    (proper : observation=.app ∨observation=.lam)
    (terminal : portKind kind port=some observation) :
    kind=.op (if observation=.app then .app else .lam) := by
  rcases proper with rfl|rfl
  · cases kind with
    | garbage => cases terminal
    | op op => cases op <;> cases port with
      | inl slot => cases slot; cases terminal
      | inr branch => cases branch <;> first | rfl | cases terminal
  · cases kind with
    | garbage => cases terminal
    | op op => cases op <;> cases port with
      | inl slot => cases slot; first | rfl | cases terminal
      | inr branch => cases branch <;> cases terminal

private theorem app_context_role (kind : Kind) (port : Port kind)
    (terminal : portKind kind port=some .app) : HEq port appCtx := by
  cases kind with
  | garbage => cases terminal
  | op op => cases op <;> cases port with
    | inl slot => cases slot; cases terminal
    | inr branch => cases branch <;> first | rfl | cases terminal

private theorem lambda_context_role (kind : Kind) (port : Port kind)
    (terminal : portKind kind port=some .lam) :
    HEq port (Sum.inl () : Port (.op .lam)) := by
  cases kind with
  | garbage => cases terminal
  | op op => cases op <;> cases port with
    | inl slot => cases slot; first | rfl | cases terminal
    | inr branch => cases branch <;> cases terminal

private theorem port_cast_eq {kind target : Kind} (sort : kind=target)
    (p : Port kind) (q : Port target) (role : HEq p q) : p=sort.symm ▸q := by
  subst target
  exact eq_of_heq role

section
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]

theorem ReadyAccess.variable_step {input context : ContextData} {access : RootAccess g root} {departure : Endpoint g}
    {stem : List (Endpoint g)} {frames : List (BinderFrame g)}
    (ready : ReadyAccess input access departure stem context frames)
    (transparency : Transparency g root) (index : Nat)
    (observes : Observes g access.val (.var index))
    (rest : List (ReadbackTask g)) (values : List Term) :
    machineStep g ⟨.read departure context stem frames::rest,values⟩=
      .next ⟨rest,.var index::values⟩ := by
  obtain ⟨arrival,wired,terminal⟩ := ready.terminal .var observes.1
  have finish := ready.finish arrival wired
  have candidates := FramedPath.observed_candidates_singleton g ready.framed transparency
    arrival finish terminal index observes
  simp only [machineStep,scanOne,wired,terminal]
  rw [←ready.split,candidates]

/-- The physical application node supplies the two actual child departures;
their contexts and lexical stacks are inherited without relabelling. -/
theorem ReadyAccess.application_step {input context : ContextData} {access : RootAccess g root} {departure : Endpoint g}
    {stem : List (Endpoint g)} {frames : List (BinderFrame g)}
    (ready : ReadyAccess input access departure stem context frames)
    (observes : Observes g access.val .app)
    (rest : List (ReadbackTask g)) (values : List Term) :
    ∃ (node : N) (sort : (g.label node).sort=.op .app),
      access.val.getLast?=some (g.wire (.inl ⟨node,sort.symm ▸appCtx⟩)) ∧
      machineStep g ⟨.read departure context stem frames::rest,values⟩=
        .next ⟨.read (.inl ⟨node,sort.symm ▸ (Sum.inl () : Port (.op .app))⟩) context access.val frames::
          .read (.inl ⟨node,sort.symm ▸ appArg⟩) context access.val frames::.buildApp::rest,values⟩ := by
  obtain ⟨arrival,wired,terminal⟩ := ready.terminal .app observes.1
  have sort : (g.label arrival.1).sort=.op .app := observed_sort _ arrival.2 .app (Or.inl rfl) terminal
  have roleEq := port_cast_eq sort arrival.2 appCtx (app_context_role _ arrival.2 terminal)
  refine ⟨arrival.1,sort,?_,?_⟩
  · have prefixFinish := ready.finish arrival wired
    change access.val.getLast?=some (g.wire (.inl ⟨arrival.1,arrival.2⟩)) at prefixFinish
    rw [roleEq] at prefixFinish
    exact prefixFinish
  ·
    simp only [machineStep,scanOne,wired,terminal,dif_pos sort]
    rw [ready.split]
    rfl

/-- A lambda step records this exact literal occurrence and its actual seam.
The frame is pushed only for the body task, leaving the continuation intact. -/
theorem ReadyAccess.lambda_step {input context : ContextData} {access : RootAccess g root} {departure : Endpoint g}
    {stem : List (Endpoint g)} {frames : List (BinderFrame g)}
    (ready : ReadyAccess input access departure stem context frames)
    (observes : Observes g access.val .lam)
    (rest : List (ReadbackTask g)) (values : List Term) :
    ∃ (node : N) (sort : (g.label node).sort=.op .lam),
      access.val.getLast?=some (g.wire (.inl ⟨node,sort.symm ▸(Sum.inl () : Port (.op .lam))⟩)) ∧
      let body : Endpoint g := .inl ⟨node,sort.symm ▸ lamBody⟩
      let frame : BinderFrame g := ⟨node,(g.label node).index,access.val,body,context⟩
      machineStep g ⟨.read departure context stem frames::rest,values⟩=
        .next ⟨.read body context access.val (frame::frames)::.buildLam::rest,values⟩ := by
  obtain ⟨arrival,wired,terminal⟩ := ready.terminal .lam observes.1
  have sort : (g.label arrival.1).sort=.op .lam := observed_sort _ arrival.2 .lam (Or.inr rfl) terminal
  have roleEq := port_cast_eq sort arrival.2 (.inl ()) (lambda_context_role _ arrival.2 terminal)
  refine ⟨arrival.1,sort,?_,?_⟩
  · have prefixFinish := ready.finish arrival wired
    change access.val.getLast?=some (g.wire (.inl ⟨arrival.1,arrival.2⟩)) at prefixFinish
    rw [roleEq] at prefixFinish
    exact prefixFinish
  · simp only [machineStep,scanOne,wired,terminal,dif_pos sort]
    rw [ready.split]
    rfl

end
end
end Lamping.AG.Readback


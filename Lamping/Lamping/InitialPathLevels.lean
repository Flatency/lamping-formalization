import Lamping.Lamping.InitialSourcePaths
namespace Lamping.AG
open Graph Lambda
private theorem label_port_height (actual : Label signature) (op : Op) (n : Nat)
    (p : Port actual.sort) (q : Port (.op op)) (lab : actual=label op n) (role : HEq p q) :
    syntaxPortHeight actual.index actual.sort p=syntaxPortHeight n (.op op) q := by
  subst actual
  have same : p=q := eq_of_heq role
  subst p
  rfl
private theorem label_port_polarity (actual : Label signature) (op : Op) (n : Nat)
    (p : Port actual.sort) (q : Port (.op op)) (lab : actual=label op n) (role : HEq p q) :
    initialPortPolarity actual.sort p=initialPortPolarity (.op op) q := by
  subst actual
  have same : p=q := eq_of_heq role
  subst p
  rfl

def ProperRole.initialHeight : ProperRole → Nat → Option Nat
  | .appCtx,m | .appFun,m | .lamCtx,m | .lamBody,m => some m
  | .appArg,m => some (m+1)
  | _,_ => none
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem AtProperRole.height {root : B} {e : Endpoint g} {role : ProperRole} {m : Nat}
    (source : AtProperRole g root e role m) (notRoot : role≠.root)
    (bp : B → Option Nat) (vp : W → Option Nat) :
    endpointHeight g bp vp e=role.initialHeight m := by
  cases source with
  | root => exact False.elim (notRoot rfl)
  | appCtx node p m lab port => exact label_port_height _ .app m p AG.appCtx lab port
  | appFun node p m lab port => exact label_port_height _ .app m p (.inl ()) lab port
  | appArg node p m lab port => exact label_port_height _ .app m p AG.appArg lab port
  | lamCtx node p m lab port => exact label_port_height _ .lam m p (.inl ()) lab port
  | lamBody node p m lab port => exact label_port_height _ .lam m p AG.lamBody lab port
  | lamBind node p m lab port => exact label_port_height _ .lam m p AG.lamBind lab port

theorem AtProperRole.context_height {root : B} {e : Endpoint g} {role : ProperRole} {m : Nat}
    (target : AtProperRole g root e role m) (context : role=.appCtx ∨role=.lamCtx)
    (bp : B → Option Nat) (vp : W → Option Nat) : endpointHeight g bp vp e=some m := by
  rcases context with app | lam
  · subst role; exact target.height (by intro bad; cases bad) bp vp
  · subst role; exact target.height (by intro bad; cases bad) bp vp

theorem AtProperRole.outgoing_polarity {root : B} {e : Endpoint g} {role : ProperRole} {m : Nat}
    (source : AtProperRole g root e role m) (outgoing : role.outgoing)
    (bp : B → Bool) (vp : W → Bool) (atRoot : bp root=true) : endPolarity bp vp e=true := by
  cases source with
  | root => exact atRoot
  | appCtx => cases outgoing
  | lamCtx => cases outgoing
  | lamBind => cases outgoing
  | appFun node p m lab port => exact label_port_polarity _ .app m p (.inl ()) lab port
  | appArg node p m lab port => exact label_port_polarity _ .app m p AG.appArg lab port
  | lamBody node p m lab port => exact label_port_polarity _ .lam m p AG.lamBody lab port
end

theorem encode_source_height (t : Term) (level : Nat)
    (vertices : (encode level t).W → Option Nat) (e : Endpoint (encode level t).net) (role : ProperRole) (m : Nat)
    (source : AtProperRole (encode level t).net (.inl ()) e role m) (outgoing : role.outgoing) :
    ∃ height,endpointHeight (encode level t).net (boundaryHeightAt level) vertices e=some height ∧
      m≤height ∧(role=.appArg → m<height) := by
  cases source with
  | root => exact ⟨level,rfl,Nat.zero_le _,by intro bad; cases bad⟩
  | appCtx => cases outgoing
  | lamCtx => cases outgoing
  | lamBind => cases outgoing
  | appFun node p m lab port =>
    exact ⟨m,label_port_height _ .app m p (.inl ()) lab port,Nat.le_refl _,by intro bad; cases bad⟩
  | appArg node p m lab port =>
    exact ⟨m+1,label_port_height _ .app m p AG.appArg lab port,Nat.le_succ _,fun _ => Nat.lt_succ_self _⟩
  | lamBody node p m lab port =>
    exact ⟨m,label_port_height _ .lam m p AG.lamBody lab port,Nat.le_refl _,by intro bad; cases bad⟩

theorem encode_source_initial (t : Term) (level : Nat) (es : List (Endpoint (encode level t).net))
    (e : Endpoint (encode level t).net) (role : ProperRole) (m : Nat)
    (source : AtProperRole (encode level t).net (.inl ()) e role m) (outgoing : role.outgoing)
    (head : es.head?=some e) (labels : Labelling (encode level t).net es a b) :
    InitialLabelling (g:=(encode level t).net) es a b := by
  obtain ⟨vp,flow⟩ := encode_flow t level
  have polarity := source.outgoing_polarity outgoing initialBoundaryPolarity vp rfl
  apply labels.initial_of_flow flow
  intro first firstEq
  have same : e=first := Option.some.inj (head.symm.trans firstEq)
  exact same ▸ polarity

/-- The argument-source strict inequality is a consequence of the real
appArg level shift, not an extra side condition fed to the path theorem. -/
theorem encode_source_first_cro (t : Term) (level : Nat)
    (es : List (Endpoint (encode level t).net)) (e : Endpoint (encode level t).net) (role : ProperRole) (m leaf : Nat)
    (source : AtProperRole (encode level t).net (.inl ()) e role m) (outgoing : role.outgoing)
    (head : es.head?=some e) (labels : Labelling (encode level t).net es a b)
    (first : (InitialOffsets.eventsOfEdges (encode level t).net es).head?=some (.cro leaf)) :
    m≤leaf ∧(role=.appArg → m<leaf) := by
  obtain ⟨height⟩ := encode_heighting t level
  obtain ⟨start,atSource,lower,strict⟩ := encode_source_height t level height.vertices e role m source outgoing
  have bound := height.first_cro_lower _ (encode_source_initial t level es e role m source outgoing head labels)
    e head start leaf atSource first
  exact ⟨Nat.le_trans lower bound,fun arg => Nat.lt_of_lt_of_le (strict arg) bound⟩
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
theorem encode_source_context_levels (t : Term) (level : Nat)
    (es : List (Endpoint (encode level t).net)) (e f : Endpoint (encode level t).net)
    (sr tr : ProperRole) (m n : Nat)
    (source : AtProperRole (encode level t).net (.inl ()) e sr m) (outgoing : sr.outgoing)
    (target : AtProperRole (encode level t).net (.inl ()) f tr n) (context : tr=.appCtx ∨tr=.lamCtx)
    (head : es.head?=some e) (last : es.getLast?=some ((encode level t).net.wire f))
    (labels : Labelling (encode level t).net es a b) : m≤n ∧(sr=.appArg → m<n) := by
  obtain ⟨height⟩ := encode_heighting t level
  obtain ⟨sourceHeight,state,lower,strict⟩ := encode_source_height t level height.vertices e sr m source outgoing
  have terminal : endpointHeight (encode level t).net (boundaryHeightAt level) height.vertices
      ((encode level t).net.wire f)=some n :=
    (height.wiring f).trans (target.context_height context _ _)
  obtain ⟨start,atStart,bound⟩ := height.path_height _
    (encode_source_initial t level es e sr m source outgoing head labels) e _ head last n terminal
  have equal : sourceHeight=start := Option.some.inj (state.symm.trans atStart)
  subst start
  exact ⟨Nat.le_trans lower bound,fun arg => Nat.lt_of_lt_of_le (strict arg) bound⟩
end Lamping.AG


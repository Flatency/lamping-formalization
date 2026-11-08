import Lamping.Lamping.InitialIndependence
namespace Lamping.AG
open Graph Lambda
private theorem passage_address_no_event {i : Nat} {kind : Kind} {p q : Port kind}
    (rule : Passage i kind p q a b) (address result : Path)
    (output : syntaxPortAddress kind q address=some result) : InitialOffsets.eventOfPort i kind p=none := by
  cases rule <;> first | rfl | cases output
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
private theorem InitialTurn.address_no_events (nodes : N → Path) (boundary : B → Option Path)
    (vertices : W → Option Path) {x y : Endpoint g} (turn : InitialTurn (g:=g) x y a b)
    (word : Path) (atExit : endpointAddress g nodes boundary vertices y=some word) : endpointEvents g x=[] := by
  cases turn with
  | node n p q rule =>
    have noEvent := passage_address_no_event rule _ _ atExit
    change (InitialOffsets.eventOfPort _ _ _).toList=[]
    rw [noEvent]; rfl
  | transparent => rfl

theorem Addressing.path_no_events {boundary : B → Option Path} (addr : Addressing g boundary)
    {es : List (Endpoint g)} (labels : InitialLabelling (g:=g) es a b)
    (f : Endpoint g) (last : es.getLast?=some f) (word : Path)
    (atExit : endpointAddress g addr.nodes boundary addr.vertices f=some word) :
    InitialOffsets.eventsOfEdges g es=[] := by
  induction labels generalizing f word with
  | single e a => rfl
  | @cons e y tail a middle b turn after ih =>
    have final : (y::tail).getLast?=some f := by simpa only [List.getLast?_cons_cons] using last
    obtain ⟨before,state,_⟩ := addr.path_predecessor g after y f rfl final word atExit
    have noEvent := turn.address_no_events g addr.nodes boundary addr.vertices before state
    change endpointEvents g (g.wire e)++InitialOffsets.eventsOfEdges g (y::tail)=[]
    rw [noEvent,ih f final word atExit]
    rfl

theorem InitialOffsets.events_join (pre : List (Endpoint g)) (e : Endpoint g) (tail : List (Endpoint g)) :
    eventsOfEdges g (pre++e::tail)=eventsOfEdges g (pre++[e])++eventsOfEdges g (e::tail) := by
  induction pre with
  | nil => rfl
  | cons first pre ih =>
    cases pre with
    | nil =>
      change arrivalEvents g first ++ eventsOfEdges g (e::tail)=
        (arrivalEvents g first ++ []) ++ eventsOfEdges g (e::tail)
      rw [List.append_nil]
    | cons next pre =>
      change arrivalEvents g first++eventsOfEdges g ((next::pre)++e::tail)=
        (arrivalEvents g first++eventsOfEdges g ((next::pre)++[e]))++eventsOfEdges g (e::tail)
      rw [ih,List.append_assoc]
end

private theorem label_port_address (actual : Label signature) (op : Op) (level : Nat)
    (p : Port actual.sort) (q : Port (.op op)) (lab : actual=label op level) (port : HEq p q) (word : Path) :
    syntaxPortAddress actual.sort p word=syntaxPortAddress (.op op) q word := by
  subst actual
  have same : p=q := eq_of_heq port
  subst p
  rfl
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem AtProperRole.outgoing_address {root : B} {e : Endpoint g} {role : ProperRole} {m : Nat}
    (source : AtProperRole g root e role m) (outgoing : role.outgoing)
    (nodes : N → Path) (boundary : B → Option Path) (vertices : W → Option Path)
    (atRoot : boundary root=some []) :
    ∃ word,endpointAddress g nodes boundary vertices e=some word := by
  cases source with
  | root => exact ⟨[],atRoot⟩
  | appCtx => cases outgoing
  | lamCtx => cases outgoing
  | lamBind => cases outgoing
  | appFun node p m lab port =>
    refine ⟨nodes node++[Step.fn],?_⟩
    exact label_port_address _ .app m p (.inl ()) lab port (nodes node)
  | appArg node p m lab port =>
    refine ⟨nodes node++[Step.arg],?_⟩
    exact label_port_address _ .app m p AG.appArg lab port (nodes node)
  | lamBody node p m lab port =>
    refine ⟨nodes node++[Step.body],?_⟩
    exact label_port_address _ .lam m p AG.lamBody lab port (nodes node)
end

/-- An actual initial rooted source prefix has no control events before its
selected outgoing segment. Context equality alone is not used to infer this. -/
theorem encode_source_prefix_no_events (t : Term) (level : Nat)
    (pre : List (Endpoint (encode level t).net)) (e : Endpoint (encode level t).net)
    (role : ProperRole) (m : Nat) (source : AtProperRole (encode level t).net (.inl ()) e role m)
    (outgoing : role.outgoing) (rooted : (pre++[e]).head?=some (.inr (.inl (.inl ()))))
    (labels : Labelling (encode level t).net (pre++[e]) a b) :
    InitialOffsets.eventsOfEdges (encode level t).net (pre++[e])=[] := by
  obtain ⟨addr⟩ := encode_addressing t level
  obtain ⟨word,atExit⟩ := source.outgoing_address outgoing addr.nodes (boundaryAddressAt []) addr.vertices rfl
  have last : (pre++[e]).getLast?=some e := by
    rw [List.getLast?_append]; rfl
  exact addr.path_no_events _ (encode_root_initial t level _ rooted labels) e last word atExit
end Lamping.AG

import Std
namespace Lamping.Graph
/-- An explicit finite enumeration; boundary order uses the last-occurrence order. -/
class FiniteNames (α : Type) where
  all : List α
  complete : ∀ a, a ∈ all
instance : FiniteNames Empty := ⟨[], fun a => nomatch a⟩
instance : FiniteNames Unit := ⟨[()], by intro a; cases a; simp⟩
instance : FiniteNames Bool := ⟨[false, true], by intro a; cases a <;> simp⟩
instance (n : Nat) : FiniteNames (Fin n) := ⟨List.finRange n, by intro a; exact List.mem_ofFn.mpr ⟨a,rfl⟩⟩
instance [FiniteNames A] [FiniteNames B] : FiniteNames (A ⊕ B) :=
  ⟨FiniteNames.all.map Sum.inl ++ FiniteNames.all.map Sum.inr, by
    intro x; cases x <;> simp [FiniteNames.complete]⟩
instance [FiniteNames A] [FiniteNames B] : FiniteNames (A × B) :=
  ⟨FiniteNames.all.flatMap (fun a => FiniteNames.all.map (a, ·)), by
    intro ⟨a,b⟩; simp only [List.mem_flatMap, List.mem_map]
    exact ⟨a, FiniteNames.complete a, b, FiniteNames.complete b, rfl⟩⟩
instance {A : Type} {P : A → Type} [FiniteNames A] [∀ a, FiniteNames (P a)] :
    FiniteNames ((a : A) × P a) :=
  ⟨FiniteNames.all.flatMap (fun a => FiniteNames.all.map (Sigma.mk a)), by
    intro ⟨a,p⟩
    exact List.mem_flatMap.mpr ⟨a,FiniteNames.complete a,
      List.mem_map.mpr ⟨p,FiniteNames.complete p,rfl⟩⟩⟩
/-- Small explicit equivalences keep all graph operations executable without choice. -/
structure Bij (A B : Type) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
instance : CoeFun (Bij A B) (fun _ => A → B) := ⟨Bij.toFun⟩
def Bij.refl (A : Type) : Bij A A := ⟨id,id, fun _ => rfl, fun _ => rfl⟩
def Bij.symm (e : Bij A B) : Bij B A := ⟨e.invFun,e.toFun,e.right_inv,e.left_inv⟩
def Bij.trans (e : Bij A B) (f : Bij B C) : Bij A C :=
  ⟨fun a => f (e a), fun c => e.invFun (f.invFun c), by
    intro a; simp [f.left_inv,e.left_inv], by intro c; simp [e.right_inv,f.right_inv]⟩
theorem Bij.injective (e : Bij A B) : Function.Injective e := by
  intro a b h; have := congrArg e.invFun h; simpa [e.left_inv] using this
/-- A segment pairs distinct ends. Two ends on one node give an original self-loop. -/
structure Pairing (E : Type) where
  mate : E → E
  involutive : ∀ e, mate (mate e) = e
  fixedPointFree : ∀ e, mate e ≠ e
instance : CoeFun (Pairing E) (fun _ => E → E) := ⟨Pairing.mate⟩
def Pairing.rename (p : Pairing E) (e : Bij E F) : Pairing F where
  mate x := e (p (e.invFun x))
  involutive x := by simp [e.left_inv, p.involutive, e.right_inv]
  fixedPointFree x := by
    intro h
    have hh := congrArg e.invFun h
    have : p (e.invFun x) = e.invFun x := by simpa [e.left_inv] using hh
    exact p.fixedPointFree _ this
@[simp] theorem Pairing.rename_apply (p : Pairing E) (e : Bij E F) (x : E) :
    p.rename e (e x) = e (p x) := by simp [Pairing.rename,e.left_inv]
theorem Pairing.rename_trans (p : Pairing E) (e : Bij E F) (f : Bij F G) :
    (p.rename e).rename f = p.rename (e.trans f) := rfl
structure Signature where
  Kind : Type
  Port : Kind → Type
  finitePort : ∀ s, FiniteNames (Port s)
  principal : (s : Kind) → Option (Port s)
attribute [instance] Signature.finitePort
structure Label (S : Signature) where
  sort : S.Kind
  index : Nat
abbrev NodePort (S : Signature) (N : Type) (label : N → Label S) :=
  (n : N) × S.Port (label n).sort
/-- Wire vertices have exactly two ends. They are transparent subdivision points,
not Lamping operators, and retain closed wire-only components. -/
abbrev End (S : Signature) (N B W : Type) (label : N → Label S) :=
  NodePort S N label ⊕ (B ⊕ (W × Bool))
structure Net (S : Signature) (N B W : Type) [FiniteNames N] [FiniteNames B] [FiniteNames W] where
  label : N → Label S
  wire : Pairing (End S N B W label)
variable {S : Signature} {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
/-- Every port and boundary has exactly one partner, by construction. -/
theorem Net.pairing (g : Net S N B W) (e : End S N B W g.label) :
    g.wire (g.wire e) = e := g.wire.involutive e
/-- Remove repeated enumeration entries, preserving last-occurrence order. -/
def unique [DecidableEq A] : List A → List A
  | [] => []
  | a :: xs => if a ∈ unique xs then unique xs else a :: unique xs
@[simp] theorem mem_unique [DecidableEq A] (a : A) (xs : List A) :
    a ∈ unique xs ↔ a ∈ xs := by
  induction xs generalizing a with
  | nil => simp [unique]
  | cons x xs ih =>
    simp only [unique]; split
    · have hx := (ih x).mp (by assumption); simp_all
    · simp_all
 theorem unique_nodup [DecidableEq A] (xs : List A) : (unique xs).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih => simp only [unique]; split <;> simp_all
/-- The designated order is the duplicate-free enumeration, not arbitrary renaming. -/
def Net.boundaryOrder [DecidableEq B] (_ : Net S N B W) : List B :=
  unique FiniteNames.all
 theorem Net.boundaryOrder_nodup [DecidableEq B] (g : Net S N B W) :
    g.boundaryOrder.Nodup := unique_nodup _
 theorem Net.boundaryOrder_complete [DecidableEq B] (g : Net S N B W) (b : B) :
    b ∈ g.boundaryOrder := (mem_unique _ _).mpr (FiniteNames.complete b)
/-- Isomorphisms fix ordered boundary names and preserve sort, index, named
port roles and the two sides of each transparent wire vertex. -/
structure NetIso {N' W' : Type} [FiniteNames N'] [FiniteNames W']
    (g : Net S N B W) (h : Net S N' B W') where
  nodes : Bij N N'
  vertices : Bij W W'
  labels : ∀ n, h.label (nodes n) = g.label n
  ports : Bij (NodePort S N g.label) (NodePort S N' h.label)
  port_node : ∀ p, (ports p).1 = nodes p.1
  port_role : ∀ p, HEq (ports p).2 p.2
  ends : Bij (End S N B W g.label) (End S N' B W' h.label)
  node_end : ∀ p, ends (.inl p) = .inl (ports p)
  boundary_end : ∀ b, ends (.inr (.inl b)) = .inr (.inl b)
  vertex_end : ∀ w d, ends (.inr (.inr (w,d))) = .inr (.inr (vertices w,d))
  wiring : ∀ e, ends (g.wire e) = h.wire (ends e)
 theorem NetIso.boundary_order [DecidableEq B] {N' W' : Type}
    [FiniteNames N'] [FiniteNames W'] {g : Net S N B W} {h : Net S N' B W'}
    (_ : NetIso g h) : g.boundaryOrder = h.boundaryOrder := rfl
def NetIso.refl (g : Net S N B W) : NetIso g g where
  nodes := Bij.refl _
  vertices := Bij.refl _
  labels _ := rfl
  ports := Bij.refl _
  port_node _ := rfl
  port_role _ := HEq.rfl
  ends := Bij.refl _
  node_end _ := rfl
  boundary_end _ := rfl
  vertex_end _ _ := rfl
  wiring _ := rfl

def NetIso.trans {N' W' N'' W'' : Type}
    [FiniteNames N'] [FiniteNames W'] [FiniteNames N''] [FiniteNames W'']
    {g : Net S N B W} {h : Net S N' B W'} {k : Net S N'' B W''}
    (a : NetIso g h) (b : NetIso h k) : NetIso g k where
  nodes := a.nodes.trans b.nodes
  vertices := a.vertices.trans b.vertices
  labels n := (b.labels (a.nodes n)).trans (a.labels n)
  ports := a.ports.trans b.ports
  port_node p := by change (b.ports (a.ports p)).1 = b.nodes (a.nodes p.1); rw [b.port_node,a.port_node]
  port_role p := (b.port_role (a.ports p)).trans (a.port_role p)
  ends := a.ends.trans b.ends
  node_end p := by change b.ends (a.ends (.inl p)) = _; rw [a.node_end,b.node_end]; rfl
  boundary_end p := by change b.ends (a.ends (.inr (.inl p))) = _; rw [a.boundary_end,b.boundary_end]
  vertex_end w d := by change b.ends (a.ends (.inr (.inr (w,d)))) = _; rw [a.vertex_end,b.vertex_end]; rfl
  wiring e := by change b.ends (a.ends (g.wire e)) = _; rw [a.wiring,b.wiring]; rfl

theorem sigma_snd_heq {A : Type} {P : A → Type} {x y : (a : A) × P a}
    (h : x = y) : HEq x.2 y.2 := by cases h; rfl
def NetIso.symm {N' W' : Type} [FiniteNames N'] [FiniteNames W']
    {g : Net S N B W} {h : Net S N' B W'} (a : NetIso g h) : NetIso h g where
  nodes := a.nodes.symm
  vertices := a.vertices.symm
  labels n := by
    have hi := a.labels (a.nodes.invFun n)
    rw [a.nodes.right_inv] at hi
    exact hi.symm
  ports := a.ports.symm
  port_node p := by
    have hi := congrArg a.nodes.invFun (a.port_node (a.ports.invFun p))
    simpa only [a.ports.right_inv,a.nodes.left_inv] using hi.symm
  port_role p := by
    change HEq (a.ports.invFun p).2 p.2
    have hp : a.ports (a.ports.invFun p) = p := a.ports.right_inv p
    exact (a.port_role (a.ports.invFun p)).symm.trans (sigma_snd_heq hp)
  ends := a.ends.symm
  node_end p := by
    apply a.ends.injective
    change a.ends (a.ends.invFun (.inl p)) = a.ends (.inl (a.ports.invFun p))
    rw [a.ends.right_inv,a.node_end,a.ports.right_inv]
  boundary_end b := by
    apply a.ends.injective
    change a.ends (a.ends.invFun (.inr (.inl b))) = a.ends (.inr (.inl b))
    rw [a.ends.right_inv,a.boundary_end]
  vertex_end w d := by
    apply a.ends.injective
    change a.ends (a.ends.invFun (.inr (.inr (w,d)))) = a.ends (.inr (.inr (a.vertices.invFun w,d)))
    rw [a.ends.right_inv,a.vertex_end,a.vertices.right_inv]
  wiring e := by
    change a.ends.invFun (h.wire e) = g.wire (a.ends.invFun e)
    apply a.ends.injective
    rw [a.ends.right_inv,a.wiring,a.ends.right_inv]
end Lamping.Graph









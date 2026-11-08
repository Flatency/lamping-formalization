import Lamping.Lamping.ChainIncidenceIso
namespace Lamping.AG
open Graph

private theorem two_step_induction {P : Nat →Prop} (zero : P 0) (one : P 1)
    (more : ∀k,P k →P (k+1) →P (k+2)) : ∀k,P k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => exact zero
    | succ k =>
      cases k with
      | zero => exact one
      | succ k => exact more k (ih k (by omega)) (ih (k+1) (by omega))

/-- A finite simple path indexed by consecutive vertex slots admits no
turnback under an injective incidence map. No orientation is supplied. -/
theorem finite_unit_path_order_or_reverse (n : Nat) (f : Nat →Nat)
    (bounded : ∀k,k≤n →f k≤n)
    (injective : ∀i j,i≤n →j≤n →f i=f j →i=j)
    (adjacent : ∀k,k<n →f (k+1)=f k+1 ∨f k=f (k+1)+1) :
    (∀k,k≤n →f k=k) ∨(∀k,k≤n →f k=n-k) := by
  cases n with
  | zero =>
    exact Or.inl (by intro k bound;have value:=bounded k bound;omega)
  | succ n =>
    rcases adjacent 0 (by omega) with firstUp | firstDown
    · have ascending : ∀k,k≤n+1 →f k=f 0+k := by
        intro k
        induction k using two_step_induction with
        | zero => intro _;omega
        | one => intro _;simpa only [Nat.zero_add] using firstUp
        | more k ih ihNext =>
          intro bound
          have prev:=ih (by omega)
          have here:=ihNext (by omega)
          have next : f (k+2)=f (k+1)+1 ∨f (k+1)=f (k+2)+1 := by
            simpa only [Nat.add_assoc] using adjacent (k+1) (by omega)
          rcases next with up | down
          · omega
          · have same : f (k+2)=f k := by omega
            have impossible:=injective (k+2) k (by omega) (by omega) same
            omega
      have final:=ascending (n+1) (by omega)
      have bound:=bounded (n+1) (by omega)
      have initial : f 0=0 := by omega
      exact Or.inl (by intro k bound;have step:=ascending k bound;omega)
    · have descending : ∀k,k≤n+1 →f k+k=f 0 := by
        intro k
        induction k using two_step_induction with
        | zero => intro _;omega
        | one => intro _;simpa only [Nat.zero_add] using firstDown.symm
        | more k ih ihNext =>
          intro bound
          have prev:=ih (by omega)
          have here:=ihNext (by omega)
          have next : f (k+2)=f (k+1)+1 ∨f (k+1)=f (k+2)+1 := by
            simpa only [Nat.add_assoc] using adjacent (k+1) (by omega)
          rcases next with up | down
          · have same : f (k+2)=f k := by omega
            have impossible:=injective (k+2) k (by omega) (by omega) same
            omega
          · omega
      have final:=descending (n+1) (by omega)
      have bound:=bounded 0 (by omega)
      have initial : f 0=n+1 := by omega
      exact Or.inr (by intro k bound;have step:=descending k bound;omega)

/-- The directly finite-carrier version used after extracting actual
vertex slots. Bijection is stronger than the injectivity needed here. -/
theorem finite_path_slot_order_or_reverse (n : Nat) (f : Fin (n+1) →Fin (n+1))
    (injective : Function.Injective f)
    (adjacent : ∀k : Fin n,
      (f ⟨k.val+1,by omega⟩).val=(f ⟨k.val,by omega⟩).val+1 ∨
      (f ⟨k.val,by omega⟩).val=(f ⟨k.val+1,by omega⟩).val+1) :
    (∀k,(f k).val=k.val) ∨(∀k,(f k).val=n-k.val) := by
  let value (k : Nat) : Nat := if h:k<n+1 then (f ⟨k,h⟩).val else 0
  have bounded : ∀k,k≤n →value k≤n := by
    intro k bound
    simp only [value,dif_pos (by omega : k<n+1)]
    exact Nat.le_of_lt_succ (f ⟨k,by omega⟩).isLt
  have inj : ∀i j,i≤n →j≤n →value i=value j →i=j := by
    intro i j hi hj same
    simp only [value,dif_pos (by omega : i<n+1),dif_pos (by omega : j<n+1)] at same
    exact congrArg Fin.val (injective (Fin.ext same))
  have next : ∀k,k<n →value (k+1)=value k+1 ∨value k=value (k+1)+1 := by
    intro k bound
    simpa only [value,dif_pos (by omega : k+1<n+1),dif_pos (by omega : k<n+1)] using adjacent ⟨k,bound⟩
  rcases finite_unit_path_order_or_reverse n value bounded inj next with up | down
  · exact Or.inl (by intro k;simpa only [value,dif_pos k.isLt] using up k.val (by omega))
  · exact Or.inr (by intro k;simpa only [value,dif_pos k.isLt] using down k.val (by omega))

/-- A complete finite simple incidence path presentation. These are actual
vertex/edge enumerations and incidence equations, not fields of an iso. -/
structure IndexedSimpleIncidencePath (g : EdgeLabelledIncidence) (n : Nat) where
  vertices : Bij (Fin (n+1)) g.Vertex
  edges : Bij (Fin n) g.Edge
  incidence : ∀k : Fin n,
    (g.source (edges k)=vertices ⟨k.val,by omega⟩ ∧
      g.target (edges k)=vertices ⟨k.val+1,by omega⟩) ∨
    (g.target (edges k)=vertices ⟨k.val,by omega⟩ ∧
      g.source (edges k)=vertices ⟨k.val+1,by omega⟩)

namespace IndexedSimpleIncidencePath
def mappedSlot {left right : EdgeLabelledIncidence} {n : Nat}
    (first : IndexedSimpleIncidencePath left n) (second : IndexedSimpleIncidencePath right n)
    (iso : ChainIncidenceIso left right) (k : Fin (n+1)) : Fin (n+1) :=
  second.vertices.invFun (iso.vertices (first.vertices k))

theorem mapped_slot_adjacent {left right : EdgeLabelledIncidence} {n : Nat}
    (first : IndexedSimpleIncidencePath left n) (second : IndexedSimpleIncidencePath right n)
    (iso : ChainIncidenceIso left right) (k : Fin n) :
    (mappedSlot first second iso ⟨k.val+1,by omega⟩).val=
      (mappedSlot first second iso ⟨k.val,by omega⟩).val+1 ∨
    (mappedSlot first second iso ⟨k.val,by omega⟩).val=
      (mappedSlot first second iso ⟨k.val+1,by omega⟩).val+1 := by
  let j := second.edges.invFun (iso.edges (first.edges k))
  have edgeEq : second.edges j=iso.edges (first.edges k) := second.edges.right_inv _
  have identify (a b : Fin (n+1))
      (equal : iso.vertices (first.vertices a)=second.vertices b) :
      mappedSlot first second iso a=b := by
    have mapped:=congrArg second.vertices.invFun equal
    simpa only [mappedSlot,second.vertices.left_inv] using mapped
  have rightInc := second.incidence j
  rw [edgeEq] at rightInc
  rcases first.incidence k with ⟨ls,lt⟩ | ⟨lt,ls⟩
  · have source : iso.vertices (first.vertices ⟨k.val,by omega⟩)=right.source (iso.edges (first.edges k)) :=
      (congrArg iso.vertices ls).symm.trans (iso.source_eq _)
    have target : iso.vertices (first.vertices ⟨k.val+1,by omega⟩)=right.target (iso.edges (first.edges k)) :=
      (congrArg iso.vertices lt).symm.trans (iso.target_eq _)
    rcases rightInc with ⟨rs,rt⟩ | ⟨rt,rs⟩
    · have a:=identify _ _ (source.trans rs)
      have b:=identify _ _ (target.trans rt)
      exact Or.inl (by rw [a,b])
    · have a:=identify _ _ (source.trans rs)
      have b:=identify _ _ (target.trans rt)
      exact Or.inr (by rw [a,b])
  · have target : iso.vertices (first.vertices ⟨k.val,by omega⟩)=right.target (iso.edges (first.edges k)) :=
      (congrArg iso.vertices lt).symm.trans (iso.target_eq _)
    have source : iso.vertices (first.vertices ⟨k.val+1,by omega⟩)=right.source (iso.edges (first.edges k)) :=
      (congrArg iso.vertices ls).symm.trans (iso.source_eq _)
    rcases rightInc with ⟨rs,rt⟩ | ⟨rt,rs⟩
    · have a:=identify _ _ (target.trans rt)
      have b:=identify _ _ (source.trans rs)
      exact Or.inr (by rw [a,b])
    · have a:=identify _ _ (target.trans rt)
      have b:=identify _ _ (source.trans rs)
      exact Or.inl (by rw [a,b])

/-- Any actual bare incidence iso induces either the original vertex slot
order or its reversal on two complete simple path presentations. -/
theorem iso_order_or_reverse {left right : EdgeLabelledIncidence} {n : Nat}
    (first : IndexedSimpleIncidencePath left n) (second : IndexedSimpleIncidencePath right n)
    (iso : ChainIncidenceIso left right) :
    (∀k,(mappedSlot first second iso k).val=k.val) ∨
    (∀k,(mappedSlot first second iso k).val=n-k.val) := by
  apply finite_path_slot_order_or_reverse n (mappedSlot first second iso)
  · intro a b equal
    apply first.vertices.injective
    apply iso.vertices.injective
    have value := congrArg second.vertices equal
    simpa only [mappedSlot,second.vertices.right_inv] using value
  · exact mapped_slot_adjacent first second iso

/-- A genuine non-loop singleton has a complete two-vertex presentation
from either endpoint. This does not choose a syntax reading direction. -/
noncomputable def singleton {g : EdgeLabelledIncidence} (edge : g.Edge) (a b : g.Vertex)
    (different : a≠b)
    (endpoints : (g.source edge=a ∧g.target edge=b) ∨(g.target edge=a ∧g.source edge=b)) :
    IndexedSimpleIncidencePath (g.induced (fun e=>e=edge)) 1 := by
  classical
  let G := g.induced (fun e=>e=edge)
  have aIncident : g.Incident (fun e=>e=edge) a := by
    refine ⟨edge,rfl,?_⟩
    rcases endpoints with ⟨sa,tb⟩ | ⟨ta,sb⟩
    · exact Or.inl sa.symm
    · exact Or.inr ta.symm
  have bIncident : g.Incident (fun e=>e=edge) b := by
    refine ⟨edge,rfl,?_⟩
    rcases endpoints with ⟨sa,tb⟩ | ⟨ta,sb⟩
    · exact Or.inr tb.symm
    · exact Or.inl sb.symm
  have casesVertex (v : G.Vertex) : v.val=a ∨v.val=b := by
    obtain ⟨e,equal,incident⟩ := v.property
    subst e
    rcases endpoints with ⟨sa,tb⟩ | ⟨ta,sb⟩
    · simpa only [sa,tb] using incident
    · simpa only [ta,sb,or_comm] using incident
  let vertexTo (k : Fin 2) : G.Vertex := if k.val=0 then ⟨a,aIncident⟩ else ⟨b,bIncident⟩
  let vertexFrom (v : G.Vertex) : Fin 2 := if v.val=a then 0 else 1
  have casesIndex (k : Fin 2) : k=0 ∨k=1 := by
    by_cases zero:k.val=0
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr (Fin.ext (by have bound:=k.isLt;omega))
  refine {
    vertices := ⟨vertexTo,vertexFrom,?_,?_⟩
    edges := ⟨fun _=>⟨edge,rfl⟩,fun _=>0,?_,?_⟩
    incidence := ?_ }
  · intro k
    rcases casesIndex k with rfl | rfl <;> simp [vertexTo,vertexFrom,different.symm]
  · intro v
    apply Subtype.ext
    rcases casesVertex v with equal | equal
    · simp [vertexTo,vertexFrom,equal]
    · simp [vertexTo,vertexFrom,equal,different.symm]
  · intro k
    apply Fin.ext
    have bound:=k.isLt
    simp only [Fin.val_zero];omega
  · rintro ⟨e,equal⟩
    exact Subtype.ext equal.symm
  · intro k
    have equal : k.val=0 := by have bound:=k.isLt;omega
    rcases endpoints with ⟨sa,tb⟩ | ⟨ta,sb⟩
    · exact Or.inl ⟨Subtype.ext (by simpa [G,vertexTo,equal] using sa),
        Subtype.ext (by simpa [G,vertexTo,equal] using tb)⟩
    · exact Or.inr ⟨Subtype.ext (by simpa [G,vertexTo,equal] using ta),
        Subtype.ext (by simpa [G,vertexTo,equal] using sb)⟩
end IndexedSimpleIncidencePath
end Lamping.AG

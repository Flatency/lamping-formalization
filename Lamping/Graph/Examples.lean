import Lamping.Graph.Rewrite
namespace Lamping.Graph
inductive ThreePort | principal | left | right deriving DecidableEq, Repr
instance : FiniteNames ThreePort := ⟨[.principal,.left,.right], by intro p; cases p <;> simp⟩
def fixtureSignature : Signature := ⟨Unit, fun _ => ThreePort, fun _ => inferInstance, fun _ => some .principal⟩
def fixtureLabel (_ : Empty ⊕ Bool) : Label fixtureSignature := ⟨(),7⟩
abbrev FixtureEnd := End fixtureSignature (Empty ⊕ Bool) Empty (Empty ⊕ Unit) fixtureLabel
/-- Two trivalent nodes. Their principal edge has a transparent subdivision.
The two auxiliary edges are parallel and connect the same pair of nodes. -/
def fixtureMate : FixtureEnd → FixtureEnd
  | .inl ⟨.inl e,_⟩ => nomatch e
  | .inl ⟨.inr n,.principal⟩ => .inr (.inr (.inr (),n))
  | .inl ⟨.inr n,.left⟩ => .inl ⟨.inr (!n),.left⟩
  | .inl ⟨.inr n,.right⟩ => .inl ⟨.inr (!n),.right⟩
  | .inr (.inl e) => nomatch e
  | .inr (.inr (.inl e,_)) => nomatch e
  | .inr (.inr (.inr _,n)) => .inl ⟨.inr n,.principal⟩
def parallelOriginal : Net fixtureSignature (Empty ⊕ Bool) Empty (Empty ⊕ Unit) where
  label := fixtureLabel
  wire := {
    mate := fixtureMate
    involutive := by
      rintro (⟨e | n,p⟩ | (e | ⟨e | u,n⟩))
      · exact nomatch e
      · cases p <;> cases n <;> rfl
      · exact nomatch e
      · exact nomatch e
      · cases u; rfl
    fixedPointFree := by
      rintro (⟨e | n,p⟩ | (e | ⟨e | u,n⟩))
      · exact nomatch e
      · cases p <;> cases n <;> (intro h; cases h)
      · exact nomatch e
      · exact nomatch e
      · cases u; intro h; cases h }
/-- Four frontier ports; principals plus both ends of the internal wire are
removed. The old principal subdivision is therefore not retained as a ghost loop. -/
def fixturePartition : Bij
    (NodePort fixtureSignature Bool (fun n => fixtureLabel (.inr n)) ⊕ (Unit × Bool))
    ((Bool × Bool) ⊕ (Bool ⊕ Bool)) where
  toFun
    | .inl ⟨n,.principal⟩ => .inr (.inl n)
    | .inl ⟨n,.left⟩ => .inl (n,false)
    | .inl ⟨n,.right⟩ => .inl (n,true)
    | .inr (_,n) => .inr (.inr n)
  invFun
    | .inl (n,false) => .inl ⟨n,.left⟩
    | .inl (n,true) => .inl ⟨n,.right⟩
    | .inr (.inl n) => .inl ⟨n,.principal⟩
    | .inr (.inr n) => .inr ((),n)
  left_inv := by rintro (⟨n,p⟩ | ⟨u,n⟩); cases p <;> rfl; cases u; rfl
  right_inv := by rintro (⟨n,p⟩ | (n | n)); cases p <;> rfl; rfl; rfl
 theorem fixtureClosed : ∀ e i,
    parallelOriginal.wire.rename (fragmentEnd parallelOriginal.label fixturePartition) (.inl e) ≠ .inr i := by
  rintro (⟨e,p⟩ | ((e | ⟨n,d⟩) | ⟨e,d⟩)) i
  · exact nomatch e
  · exact nomatch e
  · cases n <;> cases d <;> cases i <;> (intro h; cases h)
  · exact nomatch e

def auxiliaryRhs : Net fixtureSignature Empty (Bool × Bool) Empty where
  label := Empty.elim
  wire := {
    mate := fun e => match e with
      | .inl ⟨e,_⟩ => nomatch e
      | .inr (.inl (n,d)) => .inr (.inl (!n,d))
      | .inr (.inr (e,_)) => nomatch e
    involutive := by rintro (⟨e,p⟩ | (⟨n,d⟩ | ⟨e,p⟩)); exact nomatch e; cases n <;> rfl; exact nomatch e
    fixedPointFree := by rintro (⟨e,p⟩ | (⟨n,d⟩ | ⟨e,p⟩)); exact nomatch e; cases n <;> (intro h; cases h); exact nomatch e }
/-- The result has no nodes and four transparent vertices. It has two closed
components (one for each auxiliary role), even though there are no boundaries. -/
def annihilated := replace parallelOriginal fixturePartition fixtureClosed auxiliaryRhs
 theorem annihilated_no_nodes (n : Empty ⊕ Empty) : False := by cases n <;> contradiction
 theorem annihilated_outer (n d : Bool) :
    annihilated.wire (.inr (.inr (.inr (n,d),false))) =
      .inr (.inr (.inr (!n,d),false)) := by cases n <;> cases d <;> rfl
 theorem annihilated_inner (n d : Bool) :
    annihilated.wire (.inr (.inr (.inr (n,d),true))) =
      .inr (.inr (.inr (!n,d),true)) := by cases n <;> cases d <;> rfl
/-- A separate original-node self-loop fixture. -/
def selfLoopMate : FixtureEnd → FixtureEnd
  | .inl ⟨.inr n,.left⟩ => .inl ⟨.inr n,.right⟩
  | .inl ⟨.inr n,.right⟩ => .inl ⟨.inr n,.left⟩
  | e => fixtureMate e
def selfLoopOriginal : Net fixtureSignature (Empty ⊕ Bool) Empty (Empty ⊕ Unit) where
  label := fixtureLabel
  wire := {
    mate := selfLoopMate
    involutive := by
      rintro (⟨e | n,p⟩ | (e | ⟨e | u,n⟩))
      · exact nomatch e
      · cases p <;> cases n <;> rfl
      · exact nomatch e
      · exact nomatch e
      · cases u; rfl
    fixedPointFree := by
      rintro (⟨e | n,p⟩ | (e | ⟨e | u,n⟩))
      · exact nomatch e
      · cases p <;> cases n <;> (intro h; cases h)
      · exact nomatch e
      · exact nomatch e
      · cases u; intro h; cases h }
 theorem selfLoopClosed : ∀ e i,
    selfLoopOriginal.wire.rename (fragmentEnd selfLoopOriginal.label fixturePartition) (.inl e) ≠ .inr i := by
  rintro (⟨e,p⟩ | ((e | ⟨n,d⟩) | ⟨e,d⟩)) i
  · exact nomatch e
  · exact nomatch e
  · cases n <;> cases d <;> cases i <;> (intro h; cases h)
  · exact nomatch e

def selfLoopAnnihilated := replace selfLoopOriginal fixturePartition selfLoopClosed auxiliaryRhs
 theorem selfLoopAnnihilated_outer (n d : Bool) :
    selfLoopAnnihilated.wire (.inr (.inr (.inr (n,d),false))) =
      .inr (.inr (.inr (n,!d),false)) := by cases n <;> cases d <;> rfl
/-- Closing an already connected boundary pair produces a one-vertex circle. -/
def boundaryWire : Net fixtureSignature Empty (Empty ⊕ (Unit × Bool)) Empty where
  label := Empty.elim
  wire := {
    mate := fun e => match e with
      | .inl ⟨e,_⟩ => nomatch e
      | .inr (.inl (.inl e)) => nomatch e
      | .inr (.inl (.inr (u,d))) => .inr (.inl (.inr (u,!d)))
      | .inr (.inr (e,_)) => nomatch e
    involutive := by rintro (⟨e,p⟩ | ((e | ⟨u,d⟩) | ⟨e,p⟩)); exact nomatch e; exact nomatch e; cases d <;> rfl; exact nomatch e
    fixedPointFree := by rintro (⟨e,p⟩ | ((e | ⟨u,d⟩) | ⟨e,p⟩)); exact nomatch e; exact nomatch e; cases d <;> (intro h; cases h); exact nomatch e }
def closedCircle := glue boundaryWire
 theorem closedCircle_mate (d : Bool) :
    closedCircle.wire (.inr (.inr (.inr (),d))) = .inr (.inr (.inr (),!d)) := rfl
end Lamping.Graph


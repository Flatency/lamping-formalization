import Lamping.Lamping.ReadbackActualRedexRecord
import Lamping.Lamping.ExecutableReadback

namespace Lamping.AG.Readback.OccurrenceData
open Graph Lambda

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]
variable {g : Net signature N B W} {root : B}

private theorem eq_some_get {A : Type} (value : Option A) (present : value.isSome) :
    value = some (value.get present) := by
  cases value with
  | none => cases present
  | some item => rfl

private theorem initial_accessible (domain : ReadbackDomain g root) :
    Acc (MachineNext g) (initial g root).erase := by
  obtain ⟨n, term, run⟩ := domain.successful
  exact accessible_of_fuel g (show machineFuel g n (initial g root).erase = .done term from run)

private theorem initial_output_isSome (domain : ReadbackDomain g root) :
    (runOnAccessible g ⟨initial g root, initial_accessible domain⟩).isSome := by
  obtain ⟨inputs, transparency, term, matching⟩ := domain
  obtain ⟨_, tree, run, _⟩ := initial_success matching inputs transparency
  rw [run]
  trivial

/-- Run the annotated machine itself and unwrap its proved-successful output. -/
def readbackTree (domain : ReadbackDomain g root) : Tree g :=
  (runOnAccessible g ⟨initial g root, initial_accessible domain⟩).get (initial_output_isSome domain)

theorem readbackTree_run (domain : ReadbackDomain g root) :
    runOnAccessible g ⟨initial g root, initial_accessible domain⟩ = some (readbackTree domain) :=
  eq_some_get _ _

/-- The same graph and domain give the same term under the annotated and P10
machines. The proof never selects a tree or a fuel value for the program. -/
theorem readbackTree_erase (domain : ReadbackDomain g root) :
    (readbackTree domain).erase = Lamping.AG.Readback.readback g root domain := by
  obtain ⟨n, run⟩ := Unbounded.run_success_has_fuel
    ⟨initial g root, initial_accessible domain⟩ (readbackTree_run domain)
  exact (Lamping.AG.Readback.readback_eq_of_fuel domain
    (fuel_done_original run)).symm

private def accessAtTree {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (run : runOnAccessible g ⟨initial g root, accessible⟩ = some tree)
    {term : Term} (same : tree.erase = term) (matching : Matches g root term)
    (redex : RedexOcc term) : ActualRedexAccess g root redex :=
  let onTree : RedexOcc tree.erase := ⟨redex.val, by rw [same]; exact redex.property⟩
  let queried := tree.redexCursors redex.val
  let pair := queried.get (by
    obtain ⟨app, lam, found⟩ := tree.redexCursors_complete redex.val onTree.property
    change (tree.redexCursors redex.val).isSome
    rw [found]
    trivial)
  let proofOfPair : tree.redexCursors onTree.val = some (pair.1, pair.2) := by
    change queried = some pair
    exact eq_some_get queried _
  let found := ActualRedexCursor.actualAccess accessible run
    (show Matches g root tree.erase from same.symm ▸ matching) onTree proofOfPair
  { connection := found.connection
    parent := found.parent
    child := found.child
    ctx := found.ctx
    contextPrincipal := found.contextPrincipal
    parentWord := found.parentWord
    childWord := found.childWord
    parentFinish := found.parentFinish
    split := found.split }

/-- Compute the physical access at this exact redex path, using the annotated
readback and its actual two-cursor query. All domain evidence is proof-only. -/
def actualAccessAt {term : Term} (domain : ReadbackDomain g root)
    (matching : Matches g root term) (redex : RedexOcc term) : ActualRedexAccess g root redex :=
  accessAtTree (initial_accessible domain) (readbackTree_run domain)
    ((readbackTree_erase domain).trans (Lamping.AG.Readback.readback_eq_of_matches domain matching))
    matching redex

end
end Lamping.AG.Readback.OccurrenceData

namespace Lamping.AG.Readback.ExecutableNet
open Graph Lambda

/-- The executable graph supplies its own equality operations and the answer
is indexed by the supplied occurrence, with its original literal path. -/
def actualAccessAt {B : Type} [FiniteNames B] [DecidableEq B]
    (source : ExecutableNet B) (root : B)
    (domain : ReadbackDomain source.graph.net root)
    {term : Term} (matching : Matches source.graph.net root term)
    (redex : RedexOcc term) : ActualRedexAccess source.graph.net root redex := by
  letI := source.nodeEquality
  letI := source.wireEquality
  exact OccurrenceData.actualAccessAt domain matching redex

#print axioms Lamping.AG.Readback.OccurrenceData.readbackTree
#print axioms Lamping.AG.Readback.OccurrenceData.readbackTree_run
#print axioms Lamping.AG.Readback.OccurrenceData.readbackTree_erase
#print axioms Lamping.AG.Readback.OccurrenceData.actualAccessAt
#print axioms Lamping.AG.Readback.ExecutableNet.actualAccessAt

end Lamping.AG.Readback.ExecutableNet

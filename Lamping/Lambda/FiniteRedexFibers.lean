import Lamping.Lambda.DevelopmentTheory
import Lamping.Graph.Core
namespace Lamping.Lambda

/-- A finite syntax-redex fiber of an explicit predicate. The graph-site
meaning of the predicate is a separate obligation; no matching or graph
accessibility assumption is hidden here. -/
def redexFiberPaths (t : Term) (test : Path → Bool) : List Path :=
  (redexPositions t).filter test

abbrev RedexFiber (t : Term) (test : Path → Bool) := {p : Path // p∈redexFiberPaths t test}

theorem mem_redexFiberPaths (t : Term) (test : Path → Bool) (p : Path) :
    p∈redexFiberPaths t test ↔ (∃ u,subtermAt t p=some u ∧ IsRedex u) ∧ test p=true := by
  simp only [redexFiberPaths,List.mem_filter,mem_redexPositions]

instance redexFiberFiniteNames (t : Term) (test : Path → Bool) : Graph.FiniteNames (RedexFiber t test) where
  all := (redexFiberPaths t test).attach
  complete p := List.mem_attach _ p

def RedexFiber.redex (p : RedexFiber t test) : RedexOcc t :=
  ⟨p.val,((mem_redexFiberPaths t test p.val).mp p.property).1⟩

theorem RedexFiber.selected (p : RedexFiber t test) : test p.val=true :=
  ((mem_redexFiberPaths t test p.val).mp p.property).2

/-- Every selected occurrence is a genuine old source redex. -/
theorem redexFiberPaths_valid (member : p∈redexFiberPaths t test) : p∈redexPositions t :=
  (List.mem_filter.mp member).1

/-- Actual complete old-name developments exist for the finite fiber,
including the empty fiber. This is P04's finite theorem, not completion of
arbitrary graph paths or arbitrary syntax reductions. -/
theorem redexFiber_complete_exists (t : Term) (test : Path → Bool) :
    ∃ ps marked,Marked.CompleteOldDevelopment (redexFiberPaths t test) t ps marked :=
  Marked.completeOld_exists _ _

/-- Every fiber development realizes its actual chosen beta schedule. -/
theorem redexFiber_complete_betaHistory
    (complete : Marked.CompleteOldDevelopment (redexFiberPaths t test) t ps marked) :
    BetaHistory ps t marked.erase := by
  have actual := ((Marked.completeOld_iff _ _).mp complete).1.general.betaHistory
  simpa only [Marked.erase_mark] using actual

/-- The actual marked endpoint, including passive old names, is independent
of the chosen complete schedule. -/
theorem redexFiber_complete_endpoint
    (complete : Marked.CompleteOldDevelopment (redexFiberPaths t test) t ps marked) :
    marked=Marked.dev (Marked.mark (redexFiberPaths t test) t) := by
  obtain ⟨history,normal⟩ := (Marked.completeOld_iff _ _).mp complete
  exact Marked.complete_endpoint ⟨history.steps,normal⟩

/-- In particular all old redex residuals agree across complete schedules,
including those whose source name was outside the selected fiber. -/
theorem redexFiber_complete_residuals
    (left : Marked.CompleteOldDevelopment (redexFiberPaths t test) t ps a)
    (right : Marked.CompleteOldDevelopment (redexFiberPaths t test) t qs b) (r : RedexOcc t) :
    a.erase=b.erase ∧ Marked.tracePositions r.val a=Marked.tracePositions r.val b :=
  Marked.completeOld_independent left right r

/-- Only emptiness of the valid source fiber makes a complete schedule empty.
Nonemptiness is not a claim that its endpoint differs from the source. -/
theorem redexFiber_complete_empty_iff
    (complete : Marked.CompleteOldDevelopment (redexFiberPaths t test) t ps marked) :
    ps=[] ↔ redexFiberPaths t test=[] := by
  constructor
  · intro empty
    subst ps
    obtain ⟨history,normal⟩ := (Marked.completeOld_iff _ _).mp complete
    have initialNormal : Marked.Normal (Marked.mark (redexFiberPaths t test) t) := by
      cases history
      exact normal
    have inactive := (Marked.normal_iff_active_empty _).mp initialNormal
    cases selected : redexFiberPaths t test with
    | nil => rfl
    | cons p rest =>
      have member : p∈redexFiberPaths t test := by rw [selected]; exact List.mem_cons_self
      have active := (Marked.active_mark _ _ p).mpr ⟨member,redexFiberPaths_valid member⟩
      rw [inactive] at active
      cases active
  · intro empty
    have history := complete.1
    rw [empty] at history
    cases history with
    | nil => rfl
    | cons step member rest => simp [Marked.setResidualPositions] at member

/-- Garbage/empty fibers use the reflexive syntax reduction exactly. -/
theorem redexFiber_complete_empty_endpoint
    (complete : Marked.CompleteOldDevelopment (redexFiberPaths t test) t ps marked)
    (empty : redexFiberPaths t test=[]) : ps=[] ∧ marked.erase=t := by
  have noSteps := (redexFiber_complete_empty_iff complete).mpr empty
  refine ⟨noSteps,?_⟩
  have history := redexFiber_complete_betaHistory complete
  rw [noSteps] at history
  cases history
  rfl

/-- A nonempty valid fiber forces a real first beta event and the remaining
finite actual beta history. The endpoint may nevertheless equal the source. -/
theorem redexFiber_complete_nonempty
    (complete : Marked.CompleteOldDevelopment (redexFiberPaths t test) t ps marked)
    (nonempty : redexFiberPaths t test≠[]) :
    ∃ p rest middle,ps=p::rest ∧ BetaAt t p middle ∧ BetaHistory rest middle marked.erase := by
  have positive : ps≠[] := fun empty => nonempty ((redexFiber_complete_empty_iff complete).mp empty)
  have history := redexFiber_complete_betaHistory complete
  cases history with
  | nil => exact False.elim (positive rfl)
  | cons head tail => exact ⟨_,_,_,rfl,head,tail⟩


/-- Finite fibers are bounded by the syntax's finite redex enumeration,
independently of graph size or possible root-path multiplicity. -/
theorem redexFiberPaths_length_le (t : Term) (test : Path → Bool) :
    (redexFiberPaths t test).length≤(redexPositions t).length :=
  List.length_filter_le _ _

/-- Every selected old name has no residual at the actual complete endpoint.
Newly created redexes are deliberately not reselected. -/
theorem redexFiber_complete_exhausted
    (complete : Marked.CompleteOldDevelopment (redexFiberPaths t test) t ps marked)
    (member : name∈redexFiberPaths t test) : Marked.tracePositions name marked=[] := by
  cases positions : Marked.tracePositions name marked with
  | nil => rfl
  | cons p rest =>
    have remaining : p∈Marked.setResidualPositions (redexFiberPaths t test) marked :=
      (Marked.mem_setResidualPositions _ _ _).mpr ⟨name,member,by rw [positions]; exact List.mem_cons_self⟩
    rw [complete.2] at remaining
    cases remaining

/-- The syntax endpoint is reached by actual beta multi-reduction. -/
theorem redexFiber_complete_betas
    (complete : Marked.CompleteOldDevelopment (redexFiberPaths t test) t ps marked) : Betas t marked.erase := by
  have actual := ((Marked.completeOld_iff _ _).mp complete).1.steps.erase
  simpa only [Marked.erase_mark] using actual

end Lamping.Lambda


import Lamping.Lambda.NeededAccessibility
import Lamping.Lambda.SingleContraction

namespace Lamping.Lambda

/-- Syntax-only endpoint computation; its domain proof is never inspected. -/
def loStepTarget (t : Term) : Option Term :=
  (loRedex t).map fun p => (Marked.dev (Marked.mark [p] t)).erase

theorem loStepTarget_none_iff (t : Term) : loStepTarget t=none ↔ BetaNF t := by
  rw [loStepTarget,Option.map_eq_none_iff,loRedex_none_iff]

private theorem computed_lo_contract {t : Term} {p : Path}
    (hit : loRedex t=some p) :
    BetaAt t p (Marked.dev (Marked.mark [p] t)).erase ∧
      NeededParallelNext (Marked.dev (Marked.mark [p] t)).erase t := by
  let r : RedexOcc t := ⟨p,loRedex_sound hit⟩
  obtain ⟨u,head⟩ := r.contract_exists
  have same : (Marked.dev (Marked.mark [p] t)).erase=u :=
    (Marked.singleton_complete head).2
  rw [same]
  refine ⟨head,[p],singleContraction head,r,?_,?_⟩
  · exact List.mem_singleton.mpr rfl
  · exact loRedex_needed hit

theorem loStepTarget_some_spec {t u : Term} (step : loStepTarget t=some u) :
    Beta t u ∧ NeededParallelNext u t := by
  unfold loStepTarget at step
  obtain ⟨p,hit,same⟩ := Option.map_eq_some_iff.mp step
  obtain ⟨head,next⟩ := computed_lo_contract hit
  cases same
  exact ⟨head.beta,next⟩

private theorem history_betas {ps : List Path} {t u : Term}
    (history : BetaHistory ps t u) : Betas t u := by
  induction history with
  | nil t => exact .refl t
  | cons head _tail ih => exact .cons head.beta ih

/-- Only a proposition is projected; the normalizing witness is not data. -/
theorem NeededParallelNext.hasNF {t u : Term} (normalizable : HasNF t)
    (next : NeededParallelNext u t) : HasNF u := by
  obtain ⟨n,rho,sourceLO,normal⟩ := normalizable.exists_lo
  obtain ⟨F,step,r,selected,needed⟩ := next
  obtain ⟨w,G,tau,last,row⟩ := StepProjection.exists_projection step rho
  obtain ⟨observed,_lo,targetNormal,_same,_perm,_shorter⟩ :=
    row.exists_shorter_lo_of_needed_selected sourceLO normal r selected needed
  exact ⟨w,history_betas observed.derivation.valid,targetNormal⟩

/-- The HasNF field restricts the domain and is erased by compilation. -/
def NormalizableTerm := {t : Term // HasNF t}

private instance : WellFoundedRelation NormalizableTerm where
  rel := InvImage NeededParallelNext Subtype.val
  wf := ⟨fun state => InvImage.accessible Subtype.val
    state.property.acc_neededParallelNext⟩

/-- Ordinary executable recursion. Selection and endpoint data are obtained
only from loRedex and marked development, never from an existential proof. -/
def loNormalizeCertified (state : NormalizableTerm) :
    {n : Term // BetaNF n ∧ Betas state.val n} :=
  match hit : loRedex state.val with
  | none => ⟨state.val,(loRedex_none_iff state.val).mp hit,.refl state.val⟩
  | some p =>
    let target := (Marked.dev (Marked.mark [p] state.val)).erase
    have next : NeededParallelNext target state.val := (computed_lo_contract hit).2
    let result := loNormalizeCertified ⟨target,NeededParallelNext.hasNF state.property next⟩
    ⟨result.val,result.property.1,.cons (computed_lo_contract hit).1.beta result.property.2⟩
termination_by state
decreasing_by exact next

def loNormalize (t : Term) (normalizable : HasNF t) : Term :=
  (loNormalizeCertified ⟨t,normalizable⟩).val

theorem loNormalize_betaNF (t : Term) (normalizable : HasNF t) :
    BetaNF (loNormalize t normalizable) :=
  (loNormalizeCertified ⟨t,normalizable⟩).property.1

theorem loNormalize_betas (t : Term) (normalizable : HasNF t) :
    Betas t (loNormalize t normalizable) :=
  (loNormalizeCertified ⟨t,normalizable⟩).property.2

#print axioms loStepTarget
#print axioms loStepTarget_none_iff
#print axioms loStepTarget_some_spec
#print axioms NeededParallelNext.hasNF
#print axioms NormalizableTerm
#print axioms loNormalizeCertified
#print axioms loNormalize
#print axioms loNormalize_betaNF
#print axioms loNormalize_betas

end Lamping.Lambda

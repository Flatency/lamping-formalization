import Lamping.Lambda.DerivationProjection
namespace Lamping.Lambda

/-- A genuine rectangular parallel-moves grid. The two output histories are
 residual derivations; their existence does not follow from common endpoints. -/
inductive HistoryProjection : ParallelHistory t u → ParallelHistory t v →
    ParallelHistory v w → ParallelHistory u w → Prop where
  | nil (σ : ParallelHistory t v) : HistoryProjection (.nil t) σ (.nil v) σ
  | cons (row : StepProjection h σ σ₁ h')
      (tail : HistoryProjection ρ σ₁ ρ' σ') :
      HistoryProjection (.cons h ρ) σ ((ParallelHistory.single h').append ρ') σ'

namespace HistoryProjection
 theorem exists_projection (ρ : ParallelHistory t u) (σ : ParallelHistory t v) :
     ∃ (w : Term) (ρ' : ParallelHistory v w) (σ' : ParallelHistory u w),
       HistoryProjection ρ σ ρ' σ' := by
   induction ρ generalizing v with
   | nil => exact ⟨_, .nil _, σ, .nil σ⟩
   | cons h hs ih =>
     obtain ⟨z, F, σ₁, h', hrow⟩ := StepProjection.exists_projection h σ
     obtain ⟨w, ρ', σ', htail⟩ := ih σ₁
     exact ⟨w, (ParallelHistory.single h').append ρ', σ', .cons hrow htail⟩

 theorem lengths (h : HistoryProjection ρ σ ρ' σ') :
     ρ'.length = ρ.length ∧ σ'.length = σ.length := by
   induction h with
   | nil => exact ⟨rfl, rfl⟩
   | cons row tail ih =>
     constructor
     · simp only [ParallelHistory.length_append, ParallelHistory.single,
         ParallelHistory.length, ih.1]
     · exact ih.2.trans row.length

 theorem permutation (h : HistoryProjection ρ σ ρ' σ') :
     PermEq (ρ.append σ') (σ.append ρ') := by
   induction h with
   | nil σ =>
     simp only [ParallelHistory.append, ParallelHistory.append_nil]
     exact .refl _
   | @cons t u v w F a h σ z σ₁ G h' ρ ρ' σ' row tail ih =>
     have hi := PermEq.prepend (ParallelHistory.single h) ih
     have hr := row.permutation.append ρ'
     simp only [ParallelHistory.append_assoc] at hi hr
     exact .trans hi hr
end HistoryProjection

/-- AG5.1.6 diamond property for all actual histories, constructed from the
 tile recursion. Empty residual steps are retained until PermEq deletes them. -/
 theorem history_diamond (ρ : ParallelHistory t u) (σ : ParallelHistory t v) :
     ∃ (w : Term) (ρ' : ParallelHistory v w) (σ' : ParallelHistory u w),
       PermEq (ρ.append σ') (σ.append ρ') := by
   obtain ⟨w, ρ', σ', hp⟩ := HistoryProjection.exists_projection ρ σ
   exact ⟨w, ρ', σ', hp.permutation⟩
end Lamping.Lambda




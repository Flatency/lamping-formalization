import Lamping.Lambda.DevelopmentTheory
namespace Lamping.Lambda

/-- A real, occurrence-indexed derivation. The path list is part of its identity. -/
structure Derivation (source target : Term) where
  paths : List Path
  valid : BetaHistory paths source target

namespace BetaHistory
 theorem append (h : BetaHistory ps t u) (k : BetaHistory qs u v) :
    BetaHistory (ps ++ qs) t v := by
  induction h with
  | nil => exact k
  | cons h hs ih => exact .cons h (ih k)
end BetaHistory

namespace Derivation
 def nil (t : Term) : Derivation t t := ⟨[], .nil t⟩
 def append (h : Derivation t u) (k : Derivation u v) : Derivation t v :=
   ⟨h.paths ++ k.paths, h.valid.append k.valid⟩
 theorem ext {h k : Derivation t u} (hp : h.paths = k.paths) : h = k := by
   cases h; cases k; cases hp; rfl
 @[simp] theorem nil_append (h : Derivation t u) : (nil t).append h = h := by
   apply ext; rfl
 @[simp] theorem append_nil (h : Derivation t u) : h.append (nil u) = h := by
   apply ext; exact List.append_nil _
 theorem append_assoc (h : Derivation t u) (k : Derivation u v) (l : Derivation v w) :
     (h.append k).append l = h.append (k.append l) := by
   apply ext; exact List.append_assoc _ _ _

 /-- Original redex names are initialized once, then transported through the
 actual beta history. No terminal re-enumeration occurs. -/
 def Residual (h : Derivation t u) (r : RedexOcc t) (s : RedexOcc u) : Prop :=
   ∃ v, Marked.History h.paths (Marked.mark [] t) v ∧
     v.erase = u ∧ s.val ∈ Marked.tracePositions r.val v

 theorem tracked (h : Derivation t u) :
     ∃ v, Marked.History h.paths (Marked.mark [] t) v ∧ v.erase = u :=
   Marked.lift_betaHistory h.valid _ (Marked.erase_mark [] t)

 theorem residual_nil (r s : RedexOcc t) : Residual (nil t) r s ↔ r = s := by
   constructor
   · rintro ⟨v, hv, _, hs⟩
     cases hv
     have hh := (Marked.initial_residual [] t r s.val).mp hs
     exact Subtype.ext hh.symm
   · intro hh; subst s
     exact ⟨_, .nil _, Marked.erase_mark [] t,
       (Marked.initial_residual [] t r r.val).mpr rfl⟩

 theorem residual_unique_tracking (h : Derivation t u)
     (a : Marked.History h.paths (Marked.mark [] t) v)
     (b : Marked.History h.paths (Marked.mark [] t) w) :
     Marked.tracePositions r v = Marked.tracePositions r w :=
   congrArg (Marked.tracePositions r) (a.deterministic b)
end Derivation

/-- AG5.1.2 parallel contraction: an actual complete development of F.
 Lists represent finite sets extensionally through membership. -/
structure ParallelStep (F : List Path) (source target : Term) where
  paths : List Path
  markedTarget : Marked
  complete : Marked.CompleteOldDevelopment F source paths markedTarget
  target_eq : markedTarget.erase = target

namespace ParallelStep
 def derivation (h : ParallelStep F t u) : Derivation t u := by
   have hh := ((Marked.completeOld_iff F t).mp h.complete).1.general.betaHistory
   rw [Marked.erase_mark, h.target_eq] at hh
   exact ⟨h.paths, hh⟩
 theorem exists_target (F : List Path) (t : Term) : ∃ u, Nonempty (ParallelStep F t u) := by
   obtain ⟨ps, v, hv⟩ := Marked.completeOld_exists F t
   exact ⟨v.erase, ⟨⟨ps, v, hv, rfl⟩⟩⟩
 theorem endpoint (h : ParallelStep F t u) (k : ParallelStep F t v) : u = v := by
   obtain ⟨ps, w, hw⟩ := Marked.completeOld_exists F t
   have hd := Marked.complete_unique
     ⟨((Marked.completeOld_iff F t).mp h.complete).1.steps,
       ((Marked.completeOld_iff F t).mp h.complete).2⟩
     ⟨((Marked.completeOld_iff F t).mp k.complete).1.steps,
       ((Marked.completeOld_iff F t).mp k.complete).2⟩
   exact h.target_eq.symm.trans ((congrArg Marked.erase hd).trans k.target_eq)
 theorem old_residual (h : ParallelStep F t u) (k : ParallelStep F t v) (r : RedexOcc t) :
     Marked.tracePositions r.val h.markedTarget =
       Marked.tracePositions r.val k.markedTarget :=
   (Marked.completeOld_independent h.complete k.complete r).2
 def residualSet (h : ParallelStep F t u) (G : List Path) : List Path :=
   Marked.setResidualPositions G h.markedTarget
 theorem residualSet_independent (h : ParallelStep F t u) (k : ParallelStep F t v)
     (G : List Path) : h.residualSet G = k.residualSet G := by
   apply congrArg (Marked.setResidualPositions G)
   exact Marked.complete_unique
     ⟨((Marked.completeOld_iff F t).mp h.complete).1.steps,
       ((Marked.completeOld_iff F t).mp h.complete).2⟩
     ⟨((Marked.completeOld_iff F t).mp k.complete).1.steps,
       ((Marked.completeOld_iff F t).mp k.complete).2⟩
end ParallelStep
end Lamping.Lambda

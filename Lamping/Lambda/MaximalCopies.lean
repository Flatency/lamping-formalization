import Lamping.Lambda.CompleteFamilies
namespace Lamping.Lambda

def SelectionValid (t : Term) (F : List Path) : Prop :=
  ∀ p ∈ F, ∃ z, subtermAt t p = some z ∧ IsRedex z

def SelectionSubset (F G : List Path) : Prop := ∀ p ∈ F, p ∈ G

/-- One common ancestor and one extension generate the entire residual set.
 This is the source's bare “Namely” existence condition; it is not maximality. -/
def CopySet (ρ : ParallelHistory m t) (F : List Path) : Prop :=
  SelectionValid t F ∧ ∃ (a : RedexWithHistory m) (τ : ParallelHistory a.target t),
    PermEq (a.history.append τ) ρ ∧ ∀ r : RedexOcc t,
      r.val ∈ F ↔ τ.derivation.Residual a.redex r

/-- Maximality ranges over all histories, common ancestors and extensions.
 Finite lists are compared by membership, including reordered/duplicate lists. -/
def MaxCopySet (ρ : ParallelHistory m t) (F : List Path) : Prop :=
  CopySet ρ F ∧ ∀ G, CopySet ρ G → SelectionSubset F G → SelectionSubset G F

 theorem CopySet.same_family {ρ : ParallelHistory m t} (h : CopySet ρ F)
     (r s : RedexOcc t) (hr : r.val ∈ F) (hs : s.val ∈ F) :
     FamilyEq ⟨t, ρ, r⟩ ⟨t, ρ, s⟩ := by
   obtain ⟨_, a, τ, hp, hm⟩ := h
   have hleft : Copy a ⟨t, ρ, r⟩ := ⟨τ, hp, (hm r).mp hr⟩
   have hright : Copy a ⟨t, ρ, s⟩ := ⟨τ, hp, (hm s).mp hs⟩
   exact .trans (.symm (.copy hleft)) (.copy hright)

/-- The maximality half once common-copy representability has separately been
 proved. It does not assert that every whole family has such a representative;
 the source canonical-history argument remains necessary for 5.4.8. -/
 theorem CompleteFamilyStep.maximal_copySet
     {ρ : ParallelHistory m t} {step : ParallelStep F t u}
     (h : CompleteFamilyStep ρ step) (hc : CopySet ρ F) : MaxCopySet ρ F := by
   refine ⟨hc, ?_⟩
   intro G hG hFG p hp
   obtain ⟨r, hr, hfamily⟩ := h.2
   have hrG := hFG r.val hr
   let s : RedexOcc t := ⟨p, hG.1 p hp⟩
   exact (hfamily s).mpr (hG.same_family r s hrG hp)
end Lamping.Lambda

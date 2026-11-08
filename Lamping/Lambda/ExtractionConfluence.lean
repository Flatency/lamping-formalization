import Lamping.Lambda.PointedRuns
namespace Lamping.Lambda

def ExtractionJoin (r s : ExtractionRun m) : Prop :=
  ∃ t, Extraction r t ∧ Extraction s t

def ExtractionLocallyConfluent (m : Term) : Prop :=
  ∀ {r s t : ExtractionRun m}, ExtractionStep r s → ExtractionStep r t → ExtractionJoin s t

def ExtractionConfluent (m : Term) : Prop :=
  ∀ {r s t : ExtractionRun m}, Extraction r s → Extraction r t → ExtractionJoin s t

 theorem Extraction.rank_le (h : Extraction r s) : s.rank ≤ r.rank := by
   induction h with
   | refl => exact Nat.le_refl _
   | cons h hs ih => have := h.rank_lt; omega

/-- A generic terminating-relation lemma specialized to the implemented rank.
 The actual hlocal critical-pair theorem is NOT established by this statement. -/
 theorem extraction_newman (hlocal : ExtractionLocallyConfluent m) : ExtractionConfluent m := by
   intro r s t hrs hrt
   have main : ∀ n, ∀ (r : ExtractionRun m), r.rank = n →
       ∀ {s t}, Extraction r s → Extraction r t → ExtractionJoin s t := by
     intro n
     induction n using Nat.strongRecOn with
     | ind n ih =>
       intro r hr s t hrs hrt
       cases hrs with
       | refl => exact ⟨t, hrt, .refl _⟩
       | @cons _ a _ ha has =>
         cases hrt with
         | refl => exact ⟨s, .refl _, .cons ha has⟩
         | @cons _ b _ hb hbt =>
           obtain ⟨u, hau, hbu⟩ := hlocal ha hb
           have haRank : a.rank < n := by have := ha.rank_lt; omega
           have hbRank : b.rank < n := by have := hb.rank_lt; omega
           obtain ⟨x, hsx, hux⟩ := ih a.rank haRank a rfl has hau
           obtain ⟨y, hty, huy⟩ := ih b.rank hbRank b rfl hbt hbu
           have huRank : u.rank < n := by have := hau.rank_le; omega
           obtain ⟨z, hxz, hyz⟩ := ih u.rank huRank u rfl hux huy
           exact ⟨z, hsx.trans hxz, hty.trans hyz⟩
   exact main r.rank r rfl hrs hrt

 theorem ExtractionNormal.target_eq (hn : ExtractionNormal r) (h : Extraction r s) : r = s := by
   cases h with
   | refl => rfl
   | cons h hs => exact False.elim (hn ⟨_, h⟩)

/-- Normal-form uniqueness remains conditional on the still-required actual
 hlocal-confluence theorem; it is not a canonical-family theorem. -/
 theorem extraction_normal_unique_of_local_confluence {r s t : ExtractionRun m}
     (hlocal : ExtractionLocallyConfluent m)
     (h : Extraction r s) (k : Extraction r t)
     (hs : ExtractionNormal s) (ht : ExtractionNormal t) : s = t := by
   obtain ⟨u, hsu, htu⟩ := extraction_newman hlocal h k
   exact (hs.target_eq hsu).trans (ht.target_eq htu).symm
end Lamping.Lambda



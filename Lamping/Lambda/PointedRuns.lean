import Lamping.Lambda.ExtractionClosure
import Lamping.Lambda.ContextualBeta
import Lamping.Lambda.PermutationResidual
namespace Lamping.Lambda
 theorem BetaHistory.deterministic (h : BetaHistory ps t u) (k : BetaHistory ps t v) : u = v := by
   induction h generalizing v with
   | nil => cases k; rfl
   | cons h hs ih =>
     cases k with
     | cons k ks =>
       cases h.unique k
       exact ih ks

 theorem Atomic.paths_injective {ρ σ : ParallelHistory t u} (ha : Atomic ρ) (hb : Atomic σ)
     (he : ρ.derivation.paths = σ.derivation.paths) : ρ = σ := by
   induction ha with
   | nil =>
     cases hb with
     | nil => rfl
     | cons h hs =>
       change [] = _ :: _ at he
       cases he
   | cons h hs ih =>
     cases hb with
     | nil =>
       change _ :: _ = [] at he
       cases he
     | cons k ks =>
       change _ :: _ = _ :: _ at he
       obtain ⟨hpath, htail⟩ := List.cons.inj he
       cases hpath
       cases h.unique k
       have hsame := ih ks htail
       cases hsame
       rfl

/-- The run includes the last contraction; the pointed history stops just
 before it. Atomic prevents empty-step and grouping artifacts. -/
def RunRepresents (r : ExtractionRun m) (a : RedexWithHistory m) : Prop :=
  ∃ hb : BetaAt a.target a.redex.val r.target,
    Atomic a.history ∧ r.history = a.history.append (.single (singleContraction hb))

 theorem ExtractionRun.represents_exists (r : ExtractionRun m) (hp : 0 < r.rank) :
     ∃ a, RunRepresents r a := by
   obtain ⟨t, p, pre, hb, hpre, he⟩ := r.atomic.last hp
   exact ⟨⟨t, pre, ⟨p, hb.redex⟩⟩, hb, hpre, he⟩
 theorem RunRepresents.unique (ha : RunRepresents r a) (hb : RunRepresents r b) : a = b := by
   rcases a with ⟨ta, pa, ra⟩
   rcases b with ⟨tb, pb, rb⟩
   obtain ⟨hba, haa, hea⟩ := ha
   obtain ⟨hbb, hab, heb⟩ := hb
   have hpaths := congrArg (fun h => h.derivation.paths) (hea.symm.trans heb)
   simp only [ParallelHistory.derivation_append, ParallelHistory.single_derivation] at hpaths
   change pa.derivation.paths ++ [ra.val] = pb.derivation.paths ++ [rb.val] at hpaths
   have hrev := congrArg List.reverse hpaths
   simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
     List.singleton_append] at hrev
   obtain ⟨hr, hpreRev⟩ := List.cons.inj hrev
   have hpre := congrArg List.reverse hpreRev
   simp only [List.reverse_reverse] at hpre
   have hpb := pb.derivation.valid
   rw [← hpre] at hpb
   have heterm := pa.derivation.valid.deterministic hpb
   cases heterm
   have hehistory := haa.paths_injective hab hpre
   cases hehistory
   have heredex : ra = rb := Subtype.ext hr
   cases heredex
   rfl
end Lamping.Lambda





import Lamping.Lambda.CanonicalUniqueness
import Lamping.Lambda.ExtractionNormalHead
import Lamping.Lambda.RootPointedPrefixOrder
import Lamping.Lambda.RootProjectedCopyReflection
namespace Lamping.Lambda

/-- AG5.4.4 for an actual ordinary standard target prefix. A canonical
 representative is a Copy ancestor precisely when its history is a prefix
 modulo generated permutation. -/
theorem canonical_copy_of_standard
    {c : ExtractionRun m} {a b : RedexWithHistory m}
    (canonical : CanonicalRun c) (represented : RunRepresents c a)
    (ordinary : Atomic b.history) (standard : Standard b.history)
    (family : FamilyEq a b) (order : HistoryPrefix a.history b.history) : Copy a b := by
  have main : ∀ (n : Nat) (m : Term) (b : RedexWithHistory m),
      Atomic b.history → Standard b.history → b.history.length=n →
      ∀ (c : ExtractionRun m) (a : RedexWithHistory m),
      CanonicalRun c → RunRepresents c a → FamilyEq a b →
      HistoryPrefix a.history b.history → Copy a b := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro m b atomic standard count c a canonical represented family order
      rcases b with ⟨bt,bh,br⟩
      change Atomic bh at atomic
      change Standard bh at standard
      change bh.length=n at count
      cases atomic with
      | nil =>
        obtain ⟨endB,lastB⟩ := br.contract_exists
        let runB : ExtractionRun m := .of (.single (singleContraction lastB)) (.single lastB)
        have repB : RunRepresents runB ⟨m,.nil m,br⟩ := ⟨lastB,.nil _,rfl⟩
        have extracted := family.symm.extract_canonical repB represented (.nil _) canonical
        have eq := (extraction_single_normal lastB).target_eq extracted
        cases eq
        have points := represented.unique repB
        cases points
        exact Copy.refl _
      | @cons m p u bt tail T ht =>
        have tailStandard : Standard tail := standard.suffix (ρ := .single (singleContraction T))
        let b0 : RedexWithHistory u := ⟨bt,tail,br⟩
        obtain ⟨endB,lastB⟩ := br.contract_exists
        let tailRun : ExtractionRun u := .of (tail.append (.single (singleContraction lastB)))
          (ht.append (.single lastB))
        have tailRep : RunRepresents tailRun b0 := ⟨lastB,ht,rfl⟩
        obtain ⟨normalTail,tailSteps,tailCanonical⟩ :=
          canonical_extraction_exists (r := tailRun) ⟨b0,tailRep,tailStandard⟩
        obtain ⟨a0,rep0⟩ := normalTail.represents_exists tailCanonical.1
        have family0 : FamilyEq a0 b0 := (tailSteps.family b0 a0 tailRep rep0).symm
        let fullRun := tailRun.prepend (.single (singleContraction T)) (.single T)
        have fullRep : RunRepresents fullRun ⟨bt,.cons (singleContraction T) tail,br⟩ :=
          tailRep.prepend (.single (singleContraction T)) (.single T)
        have fullSteps := family.symm.extract_canonical fullRep represented standard canonical
        have alternatives := extraction_normal_head_decomposition (R := T) tailSteps
          tailCanonical.2.2 fullSteps canonical.2.2
        have smaller : tail.length<n := by change 1+tail.length=n at count; omega
        rcases alternatives with keep | root
        · rw [keep] at represented
          have pointEq := represented.unique (rep0.prepend (.single (singleContraction T)) (.single T))
          rw [pointEq] at order ⊢
          change HistoryPrefix ((ParallelHistory.single (singleContraction T)).append a0.history)
            ((ParallelHistory.single (singleContraction T)).append tail) at order
          have recursive := ih tail.length smaller u b0 ht tailStandard rfl normalTail a0
            tailCanonical rep0 family0 (order.cancel_prefix (.single (singleContraction T)))
          exact recursive.prepend (.single (singleContraction T))
        · obtain ⟨z,F,program,last,q,row,first,toCommon,unique⟩ :=
            root.pointed_prefix_fiber a0 a rep0 represented
          have second := HistoryPrefix.projected_head_le (R := T) a b0 order program last row
          have recursive := ih tail.length smaller u b0 ht tailStandard rfl normalTail a0
            tailCanonical rep0 family0 (first.trans second)
          obtain ⟨q',toPoint,toTarget⟩ := first.copy_interpolation second a0.redex b0.redex recursive
          have same := unique q' toPoint
          cases same
          exact toCommon.trans (toTarget.prepend (.single (singleContraction T)))
  exact main b.history.length m b ordinary standard rfl c a canonical represented family order

/-- The full AG5.4.4 equivalence, for arbitrary parallel target histories.
 Ordinary standardization preserves their actual permutation class. -/
theorem canonical_copy_iff_history_prefix {c : ExtractionRun m} {a b : RedexWithHistory m}
    (canonical : CanonicalRun c) (represented : RunRepresents c a) (family : FamilyEq a b) :
    Copy a b ↔ HistoryPrefix a.history b.history := by
  constructor
  · exact Copy.history_prefix
  · intro order
    obtain ⟨ordinary,atomic,standard,permutation⟩ := atomic_standardization_exists b.history
    let standardized : RedexWithHistory m := ⟨b.target,ordinary,b.redex⟩
    have changedFamily : FamilyEq a standardized := .trans family (FamilyEq.of_permutation b ordinary permutation)
    obtain ⟨extension,prefixPerm⟩ := order
    have changedOrder : HistoryPrefix a.history standardized.history := ⟨extension,prefixPerm.trans permutation⟩
    have copied := canonical_copy_of_standard (b := standardized) canonical represented atomic standard changedFamily changedOrder
    exact Copy.history_right (b := standardized) b.history permutation.symm copied

end Lamping.Lambda

import Lamping.Lamping.MarkerTransport
namespace Lamping.AG.Marker
open Graph Lambda

 def originDelta (tag writer : Origin) : Nat := if tag=writer then 1 else 0
 def countLevel (tag : Origin) : TaggedLevel → Nat
  | .empty => 0
  | .o writer a | .star writer a => originDelta tag writer + countLevel tag a
  | .pair writer a b => originDelta tag writer + countLevel tag a + countLevel tag b

 theorem countLevel_zero_iff (tag : Origin) (a : TaggedLevel) :
    countLevel tag a=0 ↔ tag∉a.origins := by
  induction a with
  | empty => simp [countLevel,TaggedLevel.origins]
  | o writer a ih | star writer a ih =>
    simp [countLevel,TaggedLevel.origins,originDelta,ih]
  | pair writer a b ia ib =>
    simp [countLevel,TaggedLevel.origins,originDelta,ia,ib,and_assoc]

 def countPrefix (tag : Origin) (a : TaggedContext) : Nat → Nat
  | 0 => 0
  | n+1 => countPrefix tag a n + countLevel tag (a.get n)

 theorem countPrefix_mono (tag : Origin) (a : TaggedContext) {n m : Nat} (h : n≤m) :
    countPrefix tag a n≤countPrefix tag a m := by
  induction m with
  | zero =>
    have eq : n=0 := by omega
    subst n
    exact Nat.le_refl _
  | succ m ih =>
    by_cases lower : n≤m
    · have old := ih lower
      simp only [countPrefix]
      omega
    · have eq : n=m+1 := by omega
      subst n
      exact Nat.le_refl _

 theorem countPrefix_cons (tag : Origin) (a : TaggedContext) (x : TaggedLevel) (n : Nat) :
    countPrefix tag (a.cons x) (n+1)=countLevel tag x+countPrefix tag a n := by
  induction n with
  | zero => simp [countPrefix,TaggedContext.cons]
  | succ n ih =>
    simp only [countPrefix,TaggedContext.cons] at *
    omega

 theorem countPrefix_replace (tag : Origin) (a b : TaggedContext) (i n : Nat) :
    countPrefix tag (a.replace i b) n=
      countPrefix tag a (min n i)+countPrefix tag b (n-i) := by
  induction n with
  | zero => simp [countPrefix]
  | succ n ih =>
    rw [countPrefix,ih]
    by_cases low : n<i
    · have mn : min n i=n := by omega
      have ms : min (n+1) i=n+1 := by omega
      have dz : n-i=0 := by omega
      have ds : n+1-i=0 := by omega
      simp only [TaggedContext.replace,if_pos low,mn,ms,dz,ds,countPrefix]
      omega
    · have mn : min n i=i := by omega
      have ms : min (n+1) i=i := by omega
      have ds : n+1-i=(n-i)+1 := by omega
      simp only [TaggedContext.replace,if_neg low,mn,ms,ds,countPrefix]
      omega

 theorem countPrefix_zero_of_absent (tag : Origin) (a : TaggedContext)
    (absent : ¬TaggedContext.HasOrigin tag a) (n : Nat) : countPrefix tag a n=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have zero : countLevel tag (a.get n)=0 := (countLevel_zero_iff tag _).mpr
      (by intro present; exact absent ⟨n,present⟩)
    simp only [countPrefix,ih,zero,Nat.add_zero]

/-- At most one occurrence in the entire infinite context, expressed by all
finite prefixes. This avoids identifying finite-support contexts with padded lists. -/
def UniqueOrigins (a : TaggedContext) : Prop := ∀ tag n, countPrefix tag a n≤1

 theorem countPrefix_cons_bound (tag : Origin) (a : TaggedContext) (x : TaggedLevel) (n : Nat) :
    countPrefix tag (a.cons x) n≤countLevel tag x+countPrefix tag a n := by
  cases n with
  | zero => simp [countPrefix]
  | succ n =>
    rw [countPrefix_cons]
    have hm := countPrefix_mono tag a (Nat.le_succ n)
    simp only [Nat.succ_eq_add_one] at *
    omega

 theorem countPrefix_replace_bound (tag : Origin) (a b : TaggedContext) (i n : Nat) :
    countPrefix tag (a.replace i b) n≤countPrefix tag a i+countPrefix tag b n := by
  rw [countPrefix_replace]
  have hm := countPrefix_mono tag a (Nat.min_le_right n i)
  have hs := countPrefix_mono tag b (Nat.sub_le n i)
  omega

 theorem countPrefix_replace_wide (tag : Origin) (a b : TaggedContext) (i n : Nat) :
    countPrefix tag (a.replace i b) (n+i+2)=countPrefix tag a i+countPrefix tag b (n+2) := by
  rw [countPrefix_replace]
  have hm : min (n+i+2) i=i := by omega
  have hs : n+i+2-i=n+2 := by omega
  rw [hm,hs]

private theorem wrapping_count_bounds (tag writer : Origin) (s c : TaggedContext)
    (x z : TaggedLevel) (i n : Nat) (hz : countLevel tag z=originDelta tag writer+countLevel tag x) :
    countPrefix tag (s.replace i (c.cons x)) n≤countPrefix tag (s.replace i (c.cons z)) (n+i+2) ∧
    countPrefix tag (s.replace i (c.cons z)) n≤
      countPrefix tag (s.replace i (c.cons x)) (n+i+2)+originDelta tag writer := by
  have ha := countPrefix_replace_bound tag s (c.cons x) i n
  have hb := countPrefix_replace_bound tag s (c.cons z) i n
  have hx := countPrefix_cons_bound tag c x n
  have hz' := countPrefix_cons_bound tag c z n
  have wideA := countPrefix_replace_wide tag s (c.cons x) i n
  have wideB := countPrefix_replace_wide tag s (c.cons z) i n
  simp only [countPrefix_cons] at wideA wideB
  have hm := countPrefix_mono tag c (Nat.le_succ n)
  simp only [Nat.succ_eq_add_one] at *
  omega

/-- Each direct control has exactly the original resources plus at most its
one writer. Bounds use larger finite input prefixes, never an infinite sum. -/
theorem TaggedPassage.count_bounds {writer i kind p q a b}
    (h : TaggedPassage writer i kind p q a b) (tag : Origin) (n : Nat) :
    countPrefix tag a n≤countPrefix tag b (n+i+2) ∧
    countPrefix tag b n≤countPrefix tag a (n+i+2)+originDelta tag writer := by
  cases h with
  | fanO s c x => exact wrapping_count_bounds tag writer s c x (.o writer x) i n rfl
  | fanStar s c x => exact wrapping_count_bounds tag writer s c x (.star writer x) i n rfl
  | cro s c =>
    have ha := countPrefix_replace_bound tag s c i n
    have hb := countPrefix_replace_bound tag s (c.cons .empty) i n
    have hx := countPrefix_cons_bound tag c .empty n
    have wideA := countPrefix_replace_wide tag s c i n
    have wideB := countPrefix_replace_wide tag s (c.cons .empty) i n
    simp only [countPrefix_cons,countLevel] at wideB hx
    have hm := countPrefix_mono tag c (Nat.le_succ n)
    have hm' := countPrefix_mono tag c (show n≤n+2 by omega)
    simp only [Nat.succ_eq_add_one] at *
    omega
  | bra s c x y =>
    have ha := countPrefix_replace_bound tag s ((c.cons x).cons y) i n
    have hb := countPrefix_replace_bound tag s (c.cons (.pair writer x y)) i n
    have hy := countPrefix_cons_bound tag (c.cons x) y n
    have hx := countPrefix_cons_bound tag c x n
    have hp := countPrefix_cons_bound tag c (.pair writer x y) n
    have wideA := countPrefix_replace_wide tag s ((c.cons x).cons y) i n
    have wideB := countPrefix_replace_wide tag s (c.cons (.pair writer x y)) i n
    simp only [countPrefix_cons,countLevel] at wideA wideB hp
    have hm := countPrefix_mono tag c (Nat.le_succ n)
    simp only [Nat.succ_eq_add_one] at *
    omega
  | appFun a | appArg a | lamBody a =>
    have hm := countPrefix_mono tag a (show n≤n+i+2 by omega)
    constructor <;> omega

 theorem TaggedTraversal.count_bound {event i kind p q a b}
    (h : TaggedTraversal event i kind p q a b) (tag : Origin) (n : Nat) :
    countPrefix tag b n≤countPrefix tag a (n+i+2)+originDelta tag (.written event) := by
  cases h with
  | direct step => exact (step.count_bounds tag n).2
  | inverse writer step =>
    have old := (step.count_bounds tag n).1
    omega

 theorem TaggedTraversal.no_copy {event i kind p q a b}
    (h : TaggedTraversal event i kind p q a b) (unique : UniqueOrigins a)
    (fresh : ¬TaggedContext.HasOrigin (.written event) a) : UniqueOrigins b := by
  intro tag n
  have bound := h.count_bound tag n
  by_cases current : tag=.written event
  · subst tag
    have old := countPrefix_zero_of_absent _ a fresh (n+i+2)
    simp [originDelta] at bound
    omega
  · have old := unique tag (n+i+2)
    simp only [originDelta,if_neg current] at bound
    omega

 theorem TaggedLevel.initial_origin {tag : Origin} (level : Nat) (address : List Bool) (a : Level)
    (present : tag∈(TaggedLevel.initial level address a).origins) :
    ∃ suffix, tag=.input level (address++suffix) := by
  induction a generalizing address with
  | empty => cases present
  | o a ih | star a ih =>
    simp only [TaggedLevel.initial,TaggedLevel.origins,List.mem_cons] at present
    rcases present with same | child
    · exact ⟨[],by simpa using same⟩
    · obtain ⟨suffix,same⟩ := ih _ child
      exact ⟨false::suffix,by simpa only [List.append_assoc,List.singleton_append] using same⟩
  | pair a b ia ib =>
    simp only [TaggedLevel.initial,TaggedLevel.origins,List.mem_cons,List.mem_append] at present
    rcases present with same | left | right
    · exact ⟨[],by simpa using same⟩
    · obtain ⟨suffix,same⟩ := ia _ left
      exact ⟨false::suffix,by simpa only [List.append_assoc,List.singleton_append] using same⟩
    · obtain ⟨suffix,same⟩ := ib _ right
      exact ⟨true::suffix,by simpa only [List.append_assoc,List.singleton_append] using same⟩

private theorem initial_parent_absent (level : Nat) (address : List Bool) (branch : Bool) (a : Level) :
    Origin.input level address ∉ (TaggedLevel.initial level (address++[branch]) a).origins := by
  intro present
  obtain ⟨suffix,same⟩ := TaggedLevel.initial_origin level (address++[branch]) a present
  have lengths := congrArg List.length (Origin.input.inj same).2
  simp only [List.length_append,List.length_singleton] at lengths
  omega

private theorem initial_children_disjoint (tag : Origin) (level : Nat) (address : List Bool)
    (a b : Level)
    (left : tag∈(TaggedLevel.initial level (address++[false]) a).origins)
    (right : tag∈(TaggedLevel.initial level (address++[true]) b).origins) : False := by
  obtain ⟨xs,hx⟩ := TaggedLevel.initial_origin _ _ _ left
  obtain ⟨ys,hy⟩ := TaggedLevel.initial_origin _ _ _ right
  have same := (Origin.input.inj (hx.symm.trans hy)).2
  simp only [List.append_assoc,List.singleton_append,List.append_cancel_left_eq,List.cons.injEq] at same
  cases same.1

 theorem TaggedLevel.initial_count_unique (tag : Origin) (level : Nat) (address : List Bool) (a : Level) :
    countLevel tag (TaggedLevel.initial level address a)≤1 := by
  induction a generalizing address with
  | empty => simp [TaggedLevel.initial,countLevel]
  | o a ih | star a ih =>
    by_cases root : tag=.input level address
    · subst tag
      have hz := (countLevel_zero_iff _ _).mpr (initial_parent_absent level address false a)
      simp only [TaggedLevel.initial,countLevel,originDelta,if_true]
      omega
    · have child := ih (address++[false])
      simp only [TaggedLevel.initial,countLevel,originDelta,if_neg root]
      omega
  | pair a b ia ib =>
    by_cases root : tag=.input level address
    · subst tag
      have hzA := (countLevel_zero_iff _ _).mpr (initial_parent_absent level address false a)
      have hzB := (countLevel_zero_iff _ _).mpr (initial_parent_absent level address true b)
      simp only [TaggedLevel.initial,countLevel,originDelta,if_true]
      omega
    · by_cases left : tag∈(TaggedLevel.initial level (address++[false]) a).origins
      · have noRight : tag∉(TaggedLevel.initial level (address++[true]) b).origins :=
          fun right => initial_children_disjoint tag level address a b left right
        have hz := (countLevel_zero_iff _ _).mpr noRight
        have hc := ia (address++[false])
        simp only [TaggedLevel.initial,countLevel,originDelta,if_neg root]
        omega
      · have hz := (countLevel_zero_iff _ _).mpr left
        have hc := ib (address++[true])
        simp only [TaggedLevel.initial,countLevel,originDelta,if_neg root]
        omega

 theorem countPrefix_single_level (tag : Origin) (a : TaggedContext) (level : Nat)
    (only : ∀ k, k≠level → countLevel tag (a.get k)=0) (n : Nat) :
    countPrefix tag a n=if level<n then countLevel tag (a.get level) else 0 := by
  induction n with
  | zero => simp [countPrefix]
  | succ n ih =>
    by_cases same : n=level
    · subst n
      simp only [countPrefix,ih,Nat.lt_irrefl,if_false,Nat.lt_succ_self,if_true,Nat.zero_add]
    · have hz := only n same
      by_cases lower : level<n
      · have next : level<n+1 := by omega
        simp only [countPrefix,ih,hz,if_pos lower,if_pos next,Nat.add_zero]
      · have next : ¬level<n+1 := by omega
        simp only [countPrefix,ih,hz,if_neg lower,if_neg next,Nat.add_zero]

 theorem TaggedContext.initial_unique (a : Context) : UniqueOrigins (TaggedContext.initial a) := by
  intro tag n
  cases tag with
  | written event =>
    have hz := countPrefix_zero_of_absent _ _ (TaggedContext.initial_no_written a event) n
    omega
  | input level address =>
    have only : ∀ k, k≠level → countLevel (.input level address) ((TaggedContext.initial a).get k)=0 := by
      intro k different
      apply (countLevel_zero_iff _ _).mpr
      intro present
      obtain ⟨suffix,same⟩ := TaggedLevel.initial_origin k [] (a.get k) present
      exact different (Origin.input.inj same).1.symm
    rw [countPrefix_single_level _ _ level only n]
    split
    · exact TaggedLevel.initial_count_unique _ level [] (a.get level)
    · omega

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

 theorem TaggedTurn.no_copy {event e f a b} (h : TaggedTurn g event e f a b)
    (unique : UniqueOrigins a) (fresh : ¬TaggedContext.HasOrigin (.written event) a) : UniqueOrigins b := by
  cases h with
  | node n p q rule => exact rule.no_copy unique fresh
  | transparent => exact unique

 theorem TaggedLabelling.no_copy {event es a b} (h : TaggedLabelling g event es a b)
    (unique : UniqueOrigins a) (causal : OriginsBefore event a) : UniqueOrigins b := by
  induction h with
  | single => exact unique
  | cons turn tail ih => exact ih (turn.no_copy unique causal.fresh) (turn.originsBefore causal)

/-- No two final marker positions share one origin along a true physical
path. Origins come from actual input addresses or distinct writer turns. -/
theorem actual_path_no_copy {es a b} (h : Labelling g es a b) :
    ∃ output, TaggedLabelling g 0 es (TaggedContext.initial a) output ∧ output.erase=b ∧
      UniqueOrigins output ∧
      ∀ writer, TaggedContext.HasOrigin (.written writer) output → WriterAt writer 0 es := by
  obtain ⟨output,tagged,erased,provenance⟩ := actual_writer_attribution h
  exact ⟨output,tagged,erased,tagged.no_copy (TaggedContext.initial_unique a)
    (TaggedContext.initial_originsBefore a),provenance⟩
end

 theorem hasOrigin_positive_count (tag : Origin) (a : TaggedContext)
    (present : TaggedContext.HasOrigin tag a) : ∃ n,0<countPrefix tag a n := by
  obtain ⟨k,hk⟩ := present
  have nonzero : countLevel tag (a.get k)≠0 :=
    fun hz => (countLevel_zero_iff tag _).mp hz hk
  refine ⟨k+1,?_⟩
  simp only [countPrefix]
  omega

/-- A surviving newly written constructor contributes one additional resource,
not merely the weak origin-membership alternative. -/
theorem TaggedPassage.write_count_increases {writer i kind p q a b}
    (h : TaggedPassage writer i kind p q a b) (writes : WriteKind kind p q)
    (tag : Origin) (n : Nat) :
    countPrefix tag a n+originDelta tag writer≤countPrefix tag b (n+i+2) := by
  cases h with
  | fanO s c x =>
    have ha := countPrefix_replace_bound tag s (c.cons x) i n
    have hx := countPrefix_cons_bound tag c x n
    have wideB := countPrefix_replace_wide tag s (c.cons (.o writer x)) i n
    simp only [countPrefix_cons,countLevel] at wideB
    have hm := countPrefix_mono tag c (Nat.le_succ n)
    simp only [Nat.succ_eq_add_one] at hm
    omega
  | fanStar s c x =>
    have ha := countPrefix_replace_bound tag s (c.cons x) i n
    have hx := countPrefix_cons_bound tag c x n
    have wideB := countPrefix_replace_wide tag s (c.cons (.star writer x)) i n
    simp only [countPrefix_cons,countLevel] at wideB
    have hm := countPrefix_mono tag c (Nat.le_succ n)
    simp only [Nat.succ_eq_add_one] at hm
    omega
  | cro => exact False.elim writes
  | bra s c x y =>
    have ha := countPrefix_replace_bound tag s ((c.cons x).cons y) i n
    have hy := countPrefix_cons_bound tag (c.cons x) y n
    have hx := countPrefix_cons_bound tag c x n
    have wideB := countPrefix_replace_wide tag s (c.cons (.pair writer x y)) i n
    simp only [countPrefix_cons,countLevel] at wideB
    have hm := countPrefix_mono tag c (Nat.le_succ n)
    simp only [Nat.succ_eq_add_one] at hm
    omega
  | appFun | appArg | lamBody => exact False.elim writes

/-- With one origin per position, an inverse cannot both remove that origin
and leave another occurrence of it alive elsewhere in the output. -/
theorem TaggedPassage.no_surviving_own_origin {writer i kind p q a b}
    (h : TaggedPassage writer i kind p q a b) (writes : WriteKind kind p q)
    (unique : UniqueOrigins b) : ¬TaggedContext.HasOrigin writer a := by
  intro present
  obtain ⟨n,positive⟩ := hasOrigin_positive_count writer a present
  have bound := h.write_count_increases writes writer n
  have old := unique writer (n+i+2)
  simp [originDelta] at bound
  omega
end Lamping.AG.Marker










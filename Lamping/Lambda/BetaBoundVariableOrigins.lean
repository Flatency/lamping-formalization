import Lamping.Lambda.ExtractionRename
import Lamping.Lambda.NestedBinderCoordinates
namespace Lamping.Lambda
/-- Every binder internal to this path is internalBound by arbitrary renaming. -/
theorem occurrenceRenaming_bound (rho : Nat → Nat) (p : Path) (k : Nat) (bound : k<binderDepth p) :
    occurrenceRenaming rho p k=k := by
  induction p generalizing rho k with
  | nil => exact False.elim (Nat.not_lt_zero _ bound)
  | cons step rest ih =>
    cases step with
    | fn | arg => exact ih rho k bound
    | body =>
      change occurrenceRenaming (liftRen rho) rest k=k
      rw [occurrenceRenaming_lift]
      cases k with
      | zero => rfl
      | succ k =>
        have inner : k<binderDepth rest := by simpa only [binderDepth,Nat.succ_lt_succ_iff] using bound
        simp only [liftRen,ih rho k inner]
/-- Renaming may identify free variables, but cannot identify them with an
internal binder. This is reflection at the SAME literal occurrence. -/
theorem renamed_bound_variable_iff (rho : Nat → Nat) (term : Term) (p : Path) (k : Nat)
    (bound : k<binderDepth p) :
    subtermAt (rename rho term) p=some (.var k) ↔ subtermAt term p=some (.var k) := by
  constructor
  · intro current
    rw [subtermAt_rename] at current
    cases old : subtermAt term p with
    | none => rw [old] at current; cases current
    | some sub =>
      rw [old,Option.map_some] at current
      cases sub with
      | lam => cases current
      | app => cases current
      | var index =>
        have eq : occurrenceRenaming rho p index=k := Term.var.inj (Option.some.inj current)
        have internalBound : index<binderDepth p := by
          by_cases inside : index<binderDepth p
          · exact inside
          · have split : index=(index-binderDepth p)+binderDepth p := by omega
            rw [split,occurrenceRenaming_free_index] at eq
            omega
        have same : index=k := (occurrenceRenaming_bound rho p index internalBound).symm.trans eq
        simp only [same]
  · intro old
    rw [subtermAt_rename,old,Option.map_some]
    simp only [rename,occurrenceRenaming_bound rho p k bound]

/-- An old nonselected variable that becomes an outer-bound variable had
exactly the additional binder removed by beta. -/
theorem liftSingle_outer_variable_iff (argument : Term) (depth index outer : Nat)
    (notSelected : index≠depth) :
    liftSubN depth (singleSub argument) index=.var (outer+depth) ↔ index=outer+depth+1 := by
  induction depth generalizing index with
  | zero =>
    cases index with
    | zero => exact False.elim (notSelected rfl)
    | succ index => simp only [liftSubN,singleSub,Term.var.injEq,Nat.add_zero]; omega
  | succ depth ih =>
    cases index with
    | zero => simp only [liftSubN,liftSub]; constructor <;> intro impossible <;> cases impossible
    | succ index =>
      have other : index≠depth := by omega
      obtain ⟨j,keep⟩ := liftSingle_other depth index argument other
      have prior := ih index other
      rw [keep] at prior
      simp only [Term.var.injEq] at prior
      simp only [liftSubN,liftSub,keep,rename,Term.var.injEq]
      omega

/-- A target outer-bound leaf in a contractum either retains the old body
leaf (whose index included the contracted binder), or comes from an exact
argument copy and an original argument leaf. -/
theorem contract_outer_bound_variable_origins {body argument : Term} {p : Path} (outer : Nat)
    (target : subtermAt (contract body argument) p=some (.var (outer+binderDepth p))) :
    subtermAt body p=some (.var (outer+binderDepth p+1)) ∨
    ∃ q r,p=q++r ∧ ArgumentOccurrence body q ∧
      subtermAt argument r=some (.var (outer+binderDepth r)) := by
  rcases subtermAt_contract_origins target with ⟨old,atOld,nonvar,shape⟩ |
    ⟨index,j,atOld,other,keep,shape⟩ | ⟨q,r,split,occurs,copy⟩
  · cases old with
    | var k => exact False.elim (nonvar k rfl)
    | lam => cases shape
    | app => cases shape
  · have jEq : j=outer+binderDepth p := Term.var.inj shape.symm
    rw [jEq] at keep
    have indexEq := (liftSingle_outer_variable_iff argument (binderDepth p) index outer other).mp keep
    exact Or.inl (by simpa only [indexEq] using atOld)
  · right
    refine ⟨q,r,split,occurs,?_⟩
    have current : subtermAt (contract body argument) (q++r)=some (.var (outer+binderDepth (q++r))) := by
      simpa only [split] using target
    exact (contract_copied_outer_variable_iff occurs r outer).mp current

/-- The actual contextual event supplies both old syntax coordinates. The
outer binder is retained outside this inner beta, with no INIT premise. -/
theorem BetaAt.outer_bound_variable_origins (event : BetaAt before site after)
    (lookup : subtermAt before site=some (.app (.lam body) argument))
    (target : subtermAt after (site++p)=some (.var (binderDepth (site++p)))) :
    subtermAt before ((site++[.fn,.body])++p)=some (.var (binderDepth (site++p)+1)) ∨
    ∃ q r,p=q++r ∧ ArgumentOccurrence body q ∧
      subtermAt argument r=some (.var (binderDepth site+binderDepth r)) := by
  have localTarget : subtermAt (contract body argument) p=
      some (.var (binderDepth site+binderDepth p)) := by
    rw [subtermAt_append,event.contract_lookup lookup,Option.bind_some,binderDepth_append] at target
    exact target
  rcases contract_outer_bound_variable_origins (binderDepth site) localTarget with retained | copied
  · left
    simpa only [List.append_assoc,subtermAt_append,lookup,Option.bind_some,subtermAt,binderDepth_append] using retained
  · exact Or.inr copied

/-- Copying an argument lambda cannot capture its internal bound variables.
The exact original lambda occurrence r and descendant z are preserved. -/
theorem contract_copied_lambda_bound_variable_iff {body argument lambdaBody : Term} {q r : Path}
    (occurs : ArgumentOccurrence body q) (atLambda : subtermAt argument r=some (.lam lambdaBody)) (z : Path) :
    subtermAt (contract body argument) ((q++r)++(.body::z))=some (.var (binderDepth z)) ↔
    subtermAt lambdaBody z=some (.var (binderDepth z)) := by
  have internalBound : binderDepth z<binderDepth (r++(.body::z)) := by rw [binderDepth_append,binderDepth]; omega
  rw [List.append_assoc,subtermAt_append,argument_copy occurs argument,Option.bind_some]
  rw [renamed_bound_variable_iff _ _ _ _ internalBound,subtermAt_append,atLambda,Option.bind_some]
  rfl
/-- Both alternatives include their complete OLD source position. This is
the coordinate interface for a lambda retained outside the actual beta. -/
theorem BetaAt.outer_bound_variable_source_coordinates (event : BetaAt before site after)
    (lookup : subtermAt before site=some (.app (.lam body) argument))
    (target : subtermAt after (site++p)=some (.var (binderDepth (site++p)))) :
    subtermAt before ((site++[.fn,.body])++p)=some (.var (binderDepth (site++p)+1)) ∨
    ∃ q r,p=q++r ∧ ArgumentOccurrence body q ∧
      subtermAt argument r=some (.var (binderDepth site+binderDepth r)) ∧
      subtermAt before ((site++[.arg])++r)=some (.var (binderDepth site+binderDepth r)) := by
  rcases event.outer_bound_variable_origins lookup target with retained | ⟨q,r,split,occurs,argumentLookup⟩
  · exact Or.inl retained
  · exact Or.inr ⟨q,r,split,occurs,argumentLookup,by
      simpa only [List.append_assoc,subtermAt_append,lookup,Option.bind_some,subtermAt] using argumentLookup⟩

/-- A copied lambda's internal binder is identified at the SAME original
argument occurrence, even when the whole beta has a nonempty context. -/
theorem BetaAt.copied_lambda_bound_variable_iff (event : BetaAt before site after)
    (lookup : subtermAt before site=some (.app (.lam body) argument))
    (occurs : ArgumentOccurrence body q) (atLambda : subtermAt argument r=some (.lam lambdaBody)) (z : Path) :
    subtermAt after ((site++(q++r))++(.body::z))=some (.var (binderDepth z)) ↔
    subtermAt before (((site++[.arg])++r)++(.body::z))=some (.var (binderDepth z)) := by
  rw [List.append_assoc site,subtermAt_append,event.contract_lookup lookup,Option.bind_some]
  rw [contract_copied_lambda_bound_variable_iff occurs atLambda z]
  simp only [List.append_assoc,subtermAt_append,lookup,Option.bind_some,subtermAt,atLambda]
end Lamping.Lambda
namespace Lamping.Lambda
 theorem BetaAt.bound_variable_outside_or_below (event : BetaAt before site after)
    (lookup : subtermAt before site=some (.app (.lam body) argument))
    (target : subtermAt after leaf=some (.var index)) :
    (DisjointPositions site leaf ∧ subtermAt before leaf=some (.var index)) ∨ ∃ suffix,leaf=site++suffix := by
  classical
  by_cases below : ∃ suffix,leaf=site++suffix
  · exact Or.inr below
  · have apart : DisjointPositions site leaf := by
      refine ⟨below,?_⟩
      rintro ⟨suffix,path⟩
      have atSite := event.contract_lookup lookup
      rw [path] at atSite
      have empty := (variable_descendant_lookup target atSite).1
      exact below ⟨[],by simpa only [empty,List.append_nil] using path.symm⟩
    exact Or.inl ⟨apart,(event.disjoint_subterm apart).symm.trans target⟩
end Lamping.Lambda
namespace Lamping.Lambda
 theorem BetaAt.all_outer_bound_variable_sources (event : BetaAt before site after)
    (lookup : subtermAt before site=some (.app (.lam body) argument))
    (target : subtermAt after leaf=some (.var (binderDepth leaf))) :
    (DisjointPositions site leaf ∧ subtermAt before leaf=some (.var (binderDepth leaf))) ∨
    ∃ p,leaf=site++p ∧
      (subtermAt before ((site++[.fn,.body])++p)=some (.var (binderDepth leaf+1)) ∨
      ∃ q r,p=q++r ∧ ArgumentOccurrence body q ∧
        subtermAt argument r=some (.var (binderDepth site+binderDepth r)) ∧
        subtermAt before ((site++[.arg])++r)=some (.var (binderDepth site+binderDepth r))) := by
  rcases event.bound_variable_outside_or_below lookup target with apart | ⟨p,split⟩
  · exact Or.inl apart
  · subst leaf
    exact Or.inr ⟨p,rfl,event.outer_bound_variable_source_coordinates lookup target⟩
end Lamping.Lambda


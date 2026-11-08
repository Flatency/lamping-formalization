import Lamping.Lambda.LabelContractedOccurrences
namespace Lamping.Lambda.Labelled

/-- A surviving original lambda and its protected ancestry. Right siblings
may change, but all other current labels recursively avoid the binder atom. -/
inductive ProtectedLambdaCut (n : Nat) : Path → LTerm → LTerm → Prop where
  | here (safe : body.Supported (fun m => m≠n)) :
      ProtectedLambdaCut n [] (.lam (Label.atom n) original) (.lam (Label.atom n) body)
  | fn : ProtectedLambdaCut n p fn fn' → label.Supported (fun m => m≠n) →
      arg'.Supported (fun m => m≠n) →
      ProtectedLambdaCut n (.fn::p) (.app label fn arg) (.app label fn' arg')
  | arg : ProtectedLambdaCut n p arg arg' → label.Supported (fun m => m≠n) →
      fn.Supported (fun m => m≠n) →
      ProtectedLambdaCut n (.arg::p) (.app label fn arg) (.app label fn arg')
  | body : ProtectedLambdaCut n p body body' → label.Supported (fun m => m≠n) →
      ProtectedLambdaCut n (.body::p) (.lam label body) (.lam label body')

private theorem initial_label_avoid (initial : INIT t) (member : l∈t.labels) (different : l≠Label.atom n) :
    l.Supported (fun m => m≠n) := by
  obtain ⟨m,atomic⟩ := initial.1 l member
  rw [atomic]
  intro same
  exact different (atomic.trans (congrArg Label.atom same))

private theorem initial_term_avoid (initial : INIT t) (absent : Label.atom n∉t.labels) :
    t.Supported (fun m => m≠n) := by
  apply (LTerm.supported_iff _ _).mpr
  intro l member
  exact initial_label_avoid initial member (fun equal => absent (equal ▸ member))

/-- Construct the protected syntax relation from actual INIT and the actual
lambda occurrence. No future degree-support premise is used. -/
theorem INIT.protected_lambda_cut (initial : INIT t)
    (lookup : t.subterm p=some (.lam (Label.atom n) original)) : ProtectedLambdaCut n p t t := by
  induction p generalizing t with
  | nil =>
    have equal : t=.lam (Label.atom n) original := by simpa only [LTerm.subterm,Option.some.injEq] using lookup
    subst t
    exact .here (initial_term_avoid (initial.subterm (p := [.body]) (by simp [LTerm.subterm]))
      (List.nodup_cons.mp initial.2).1)
  | cons step rest ih =>
    cases t with
    | var => cases step <;> simp [LTerm.subterm] at lookup
    | lam label body =>
      cases step with
      | fn => simp [LTerm.subterm] at lookup
      | arg => simp [LTerm.subterm] at lookup
      | body =>
        have member : Label.atom n∈body.labels := LTerm.label_mem_of_subterm (t := body) (p := rest) lookup
        have different : label≠Label.atom n :=
          fun equal => (List.nodup_cons.mp initial.2).1 (equal.symm ▸ member)
        exact .body (ih (initial.subterm (p := [.body]) (by simp [LTerm.subterm])) lookup)
          (initial_label_avoid initial List.mem_cons_self different)
    | app label fn arg =>
      cases step with
      | body => simp [LTerm.subterm] at lookup
      | fn =>
        have member : Label.atom n∈fn.labels := LTerm.label_mem_of_subterm (t := fn) (p := rest) lookup
        have different : label≠Label.atom n := by
          intro equal
          exact (List.nodup_cons.mp initial.2).1 (equal.symm ▸ List.mem_append_left _ member)
        have absent : Label.atom n∉arg.labels := by
          intro other
          exact (List.nodup_append.mp (List.nodup_cons.mp initial.2).2).2.2 _ member _ other rfl
        exact .fn (ih (initial.subterm (p := [.fn]) (by simp [LTerm.subterm])) lookup)
          (initial_label_avoid initial List.mem_cons_self different)
          (initial_term_avoid (initial.subterm (p := [.arg]) (by simp [LTerm.subterm])) absent)
      | arg =>
        have member : Label.atom n∈arg.labels := LTerm.label_mem_of_subterm (t := arg) (p := rest) lookup
        have different : label≠Label.atom n := by
          intro equal
          exact (List.nodup_cons.mp initial.2).1 (equal.symm ▸ List.mem_append_right _ member)
        have absent : Label.atom n∉fn.labels := by
          intro other
          exact (List.nodup_append.mp (List.nodup_cons.mp initial.2).2).2.2 _ other _ member rfl
        exact .arg (ih (initial.subterm (p := [.arg]) (by simp [LTerm.subterm])) lookup)
          (initial_label_avoid initial List.mem_cons_self different)
          (initial_term_avoid (initial.subterm (p := [.fn]) (by simp [LTerm.subterm])) absent)

/-- At and left of this surviving lambda, every actual redex degree is still
exactly its original source degree, including a parent applying this lambda. -/
theorem ProtectedLambdaCut.left_degree (cut : ProtectedLambdaCut n p t u)
    (before : LeftOf q p) (degree : u.degreeAt q=some l) : t.degreeAt q=some l := by
  induction cut generalizing q with
  | here => cases before
  | fn child safe right ih =>
    cases q with
    | nil =>
      cases child with
      | here => exact degree
      | fn => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | arg => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | body => exact degree
    | cons edge q =>
      cases edge with
      | fn => cases before with | child _ earlier => exact ih earlier degree
      | arg => cases before
      | body => simp [LTerm.degreeAt,LTerm.subterm] at degree
  | arg child safe left ih =>
    cases q with
    | nil => cases ‹LTerm› <;> simpa only [LTerm.degreeAt,LTerm.subterm,LTerm.degree] using degree
    | cons edge q =>
      cases edge with
      | fn => exact degree
      | arg => cases before with | child _ earlier => exact ih earlier degree
      | body => simp [LTerm.degreeAt,LTerm.subterm] at degree
  | body child safe ih =>
    cases q with
    | nil => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
    | cons edge q =>
      cases edge with
      | fn => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | arg => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | body => cases before with | child _ earlier => exact ih earlier degree

private theorem supported_step (step : StepAt p t u) (safe : t.Supported region) : u.Supported region := by
  induction step with
  | root => exact safe.2.1.2.contract safe.2.2 safe.1 safe.2.1.1
  | fn _ ih => exact ⟨safe.1,ih safe.2.1,safe.2.2⟩
  | arg _ ih => exact ⟨safe.1,safe.2.1,ih safe.2.2⟩
  | body _ ih => exact ⟨safe.1,ih safe.2⟩

/-- Inside steps preserve the old lambda and cannot propagate its atom. -/
theorem ProtectedLambdaCut.step_inside (cut : ProtectedLambdaCut n p t u)
    (step : StepAt (p++suffix) u v) : ProtectedLambdaCut n p t v := by
  induction cut generalizing v with
  | here safe =>
    cases suffix with
    | nil => cases step
    | cons edge rest =>
      cases edge with
      | fn => cases step
      | arg => cases step
      | body => cases step with | body actual => exact .here (supported_step actual safe)
  | fn child safe right ih => cases step with | fn actual => exact .fn (ih actual) safe right
  | arg child safe left ih => cases step with | arg actual => exact .arg (ih actual) safe left
  | body child safe ih => cases step with | body actual => exact .body (ih actual) safe

/-- Actual right-disjoint steps only change supported right siblings. -/
theorem ProtectedLambdaCut.step_right (cut : ProtectedLambdaCut n p t u)
    (step : StepAt q u v) (right : LeftOf p q) (apart : DisjointPositions p q) : ProtectedLambdaCut n p t v := by
  induction cut generalizing q v with
  | here => exact False.elim (DisjointPositions.nil_left apart)
  | fn child safe argSafe ih =>
    cases step with
    | root => exact False.elim (DisjointPositions.nil_right apart)
    | fn actual => cases right with | child _ earlier => exact .fn (ih actual earlier apart.child) safe argSafe
    | arg actual => exact .fn child safe (supported_step actual argSafe)
  | arg child safe fnSafe ih =>
    cases step with
    | root => exact False.elim (DisjointPositions.nil_right apart)
    | fn actual => cases right
    | arg actual => cases right with | child _ earlier => exact .arg (ih actual earlier apart.child) safe fnSafe
  | body child safe ih =>
    cases step with
    | body actual => cases right with | child _ earlier => exact .body (ih actual earlier apart.child) safe

private theorem supported_label_at {t node : LTerm} (safe : t.Supported region) (lookup : t.subterm q=some node) :
    node.label.Supported region :=
  (LTerm.supported_iff _ _).mp safe _ (LTerm.label_mem_of_subterm lookup)

/-- The unique protected lambda is the only current node label which can
contain its atom. Its actual occurrence, rather than an origin map, is kept. -/
theorem ProtectedLambdaCut.node_label (cut : ProtectedLambdaCut n p t u)
    (lookup : u.subterm q=some node) :
    node.label.Supported (fun m => m≠n) ∨ (node.label=Label.atom n ∧ q=p) := by
  induction cut generalizing q with
  | here safe =>
    cases q with
    | nil =>
      simp only [LTerm.subterm,Option.some.injEq] at lookup
      cases lookup
      exact .inr ⟨rfl,rfl⟩
    | cons edge q =>
      cases edge with
      | fn => simp [LTerm.subterm] at lookup
      | arg => simp [LTerm.subterm] at lookup
      | body => exact .inl (supported_label_at safe lookup)
  | fn child safe right ih =>
    cases q with
    | nil =>
      have label : node.label=_ := congrArg LTerm.label (Option.some.inj lookup.symm)
      exact .inl (label.symm ▸ safe)
    | cons edge q =>
      cases edge with
      | body => simp [LTerm.subterm] at lookup
      | arg => exact .inl (supported_label_at right lookup)
      | fn =>
        rcases ih lookup with supported | ⟨label,site⟩
        · exact .inl supported
        · exact .inr ⟨label,congrArg (Step.fn::·) site⟩
  | arg child safe left ih =>
    cases q with
    | nil =>
      have label : node.label=_ := congrArg LTerm.label (Option.some.inj lookup.symm)
      exact .inl (label.symm ▸ safe)
    | cons edge q =>
      cases edge with
      | body => simp [LTerm.subterm] at lookup
      | fn => exact .inl (supported_label_at left lookup)
      | arg =>
        rcases ih lookup with supported | ⟨label,site⟩
        · exact .inl supported
        · exact .inr ⟨label,congrArg (Step.arg::·) site⟩
  | body child safe ih =>
    cases q with
    | nil =>
      have label : node.label=_ := congrArg LTerm.label (Option.some.inj lookup.symm)
      exact .inl (label.symm ▸ safe)
    | cons edge q =>
      cases edge with
      | fn => simp [LTerm.subterm] at lookup
      | arg => simp [LTerm.subterm] at lookup
      | body =>
        rcases ih lookup with supported | ⟨label,site⟩
        · exact .inl supported
        · exact .inr ⟨label,congrArg (Step.body::·) site⟩

theorem ProtectedLambdaCut.degree_avoid (cut : ProtectedLambdaCut n p t u)
    (degree : u.degreeAt q=some l) (notParent : q++[.fn]≠p) : l.Supported (fun m => m≠n) := by
  obtain ⟨body,atLambda⟩ := LTerm.degreeAt_lambda degree
  rcases cut.node_label atLambda with safe | ⟨_,site⟩
  · exact safe
  · exact False.elim (notParent site)

theorem ProtectedLambdaCut.current_lookup (cut : ProtectedLambdaCut n p t u) :
    ∃ body,u.subterm p=some (.lam (Label.atom n) body) := by
  induction cut with
  | @here old current safe => exact ⟨current,by simp [LTerm.subterm]⟩
  | fn _ _ _ ih => exact ih
  | arg _ _ _ ih => exact ih
  | body _ _ ih => exact ih

private theorem binder_standard_no_return (first : BetaAt source head middle)
    (tail : ParallelHistory middle target) (standard : Standard (.cons (singleContraction first) tail)) :
    DoesNotReturnLeft ⟨head,first.redex⟩ (.cons (singleContraction first) tail) := by
  cases standard with
  | cons _ witness selected noReturn rest =>
    have same : witness=⟨head,first.redex⟩ := Subtype.ext (List.mem_singleton.mp selected.1)
    cases same
    exact noReturn

/-- A left event would use a genuine initial redex left of the actual first
step. Full Standardness excludes it, with no degree-avoidance premise. -/
theorem ProtectedLambdaCut.event_not_left (cut : ProtectedLambdaCut n site t u) (initial : INIT t)
    (pre : History before t u) (event : StepAt q u v) (post : History after v z)
    (head : BetaAt t.erase first headTarget) (tail : ParallelHistory headTarget z.erase)
    (ordinary : Atomic tail) (standard : Standard (.cons (singleContraction head) tail))
    (paths : (ParallelHistory.cons (singleContraction head) tail).derivation.paths=before++q::after)
    (ancestor : LeftOf site first) : ¬LeftOf q site := by
  intro earlier
  obtain ⟨l,degree⟩ := degreeAt_exists u ⟨q,event.betaAt.redex⟩
  have oldDegree := cut.left_degree earlier degree
  obtain ⟨body,lookup⟩ := LTerm.degreeAt_lambda oldDegree
  obtain ⟨m,atomic⟩ := initial.1 l (LTerm.label_mem_of_subterm lookup)
  obtain ⟨beta,b,argument,atRedex⟩ := LTerm.degreeAt_redex oldDegree
  let old : RedexOcc t.erase := ⟨q,by
    refine ⟨.app (.lam b.erase) argument.erase,?_,True.intro⟩
    rw [←LTerm.erase_subterm,atRedex]
    rfl⟩
  have fired : FiresAtom (before++q::after) t z m :=
    ⟨before,q,after,u,v,rfl,pre,event,by simpa only [atomic] using degree,post⟩
  have used := fired.used_source initial old (by simpa only [atomic] using oldDegree)
    (.cons (singleContraction head) tail) (.cons head ordinary) paths
  exact (binder_standard_no_return head tail standard).no_used_left (.cons head ordinary)
    old (earlier.trans ancestor) used

private theorem protect_history (history : History qs u v)
    (cut : ProtectedLambdaCut n site t u) (pre : History before t u) (initial : INIT t)
    (head : BetaAt t.erase first headTarget) (tail : ParallelHistory headTarget v.erase)
    (ordinary : Atomic tail) (standard : Standard (.cons (singleContraction head) tail))
    (paths : (ParallelHistory.cons (singleContraction head) tail).derivation.paths=before++qs)
    (ancestor : LeftOf site first) :
    RegionalHistory (fun m => m≠n) qs u v ∧ ProtectedLambdaCut n site t v := by
  induction history generalizing before with
  | nil => exact ⟨.nil _,cut⟩
  | @cons q u middle qs v event rest ih =>
    obtain ⟨body,lookup⟩ := cut.current_lookup
    have sitePosition : (subtermAt u.erase site).isSome := by rw [←LTerm.erase_subterm,lookup]; rfl
    obtain ⟨redex,atRedex,_⟩ := event.betaAt.redex
    have eventPosition : (subtermAt u.erase q).isSome := by rw [atRedex]; rfl
    have geometry : (∃ suffix,q=site++suffix) ∨ (LeftOf site q ∧ DisjointPositions site q) := by
      rcases compare_positions u.erase site q sitePosition eventPosition with same | later | earlier
      · exact .inl ⟨[],by simpa only [List.append_nil] using same.symm⟩
      · rcases later.inside_or_disjoint with inside | apart
        · exact .inl inside
        · exact .inr ⟨later,apart⟩
      · exact False.elim (cut.event_not_left initial pre event rest head tail ordinary standard paths ancestor earlier)
    obtain ⟨l,degree⟩ := degreeAt_exists u ⟨q,event.betaAt.redex⟩
    have safe : l.Supported (fun m => m≠n) := by
      apply cut.degree_avoid degree
      intro parent
      rcases geometry with ⟨suffix,equal⟩ | ⟨_,apart⟩
      · have lengths := congrArg List.length parent
        simp only [List.length_append,List.length_cons,List.length_nil,equal] at lengths
        omega
      · exact apart.2 ⟨[.fn],parent.symm⟩
    have nextCut : ProtectedLambdaCut n site t middle := by
      rcases geometry with ⟨suffix,equal⟩ | ⟨right,apart⟩
      · rw [equal] at event
        exact cut.step_inside event
      · exact cut.step_right event right apart
    have nextPaths : (ParallelHistory.cons (singleContraction head) tail).derivation.paths=(before++[q])++qs := by
      simpa only [List.append_assoc,List.singleton_append] using paths
    obtain ⟨colours,finalCut⟩ := ih nextCut (pre.append (.cons event (.nil _))) tail ordinary standard nextPaths
    exact ⟨.cons event degree safe colours,finalCut⟩

/-- Actual Standard histories protect every original lambda strictly above
the first step and recursively avoid its atom at every fired degree. -/
theorem History.standard_ancestor_binder_protection (history : History ps t u) (initial : INIT t)
    (lookup : t.subterm site=some (.lam (Label.atom n) body))
    (head : BetaAt t.erase first headTarget) (tail : ParallelHistory headTarget u.erase)
    (ordinary : Atomic tail) (standard : Standard (.cons (singleContraction head) tail))
    (paths : (ParallelHistory.cons (singleContraction head) tail).derivation.paths=ps)
    (strictAncestor : first=site++(.body::suffix)) :
    RegionalHistory (fun m => m≠n) ps t u ∧ ProtectedLambdaCut n site t u := by
  apply protect_history history (initial.protected_lambda_cut lookup) (.nil t) initial head tail ordinary standard paths
  rw [strictAncestor]
  simpa only [List.append_nil] using (LeftOf.outer .body suffix).prefix_append site
private theorem regional_last_support (regional : RegionalHistory region (ps++[q]) t v)
    (pre : History ps t u) (degree : u.degreeAt q=some l) : l.Supported region := by
  induction pre with
  | nil =>
    cases regional with
    | cons step lastDegree support rest =>
      have equal : l=_ := Option.some.inj (degree.symm.trans lastDegree)
      exact equal.symm ▸ support
  | cons head rest ih =>
    cases regional with
    | cons other firstDegree support tail =>
      have same := head.deterministic other
      cases same
      exact ih tail degree

/-- In particular, the final redex degree recursively avoids each original
lambda strictly above the actual first event. This retains the whole
Standard schedule and works with arbitrary original INIT labels. -/
theorem History.standard_ancestor_degree_avoid (history : History ps t u) (last : StepAt q u v)
    (initial : INIT t) (lookup : t.subterm site=some (.lam (Label.atom n) body))
    (head : BetaAt t.erase first headTarget) (tail : ParallelHistory headTarget v.erase)
    (ordinary : Atomic tail) (standard : Standard (.cons (singleContraction head) tail))
    (paths : (ParallelHistory.cons (singleContraction head) tail).derivation.paths=ps++[q])
    (strictAncestor : first=site++(.body::suffix)) (degree : u.degreeAt q=some l) :
    l.Supported (fun m => m≠n) := by
  have protection :=  (history.append (.cons last (.nil _))).standard_ancestor_binder_protection
    initial lookup head tail ordinary standard paths strictAncestor
  exact regional_last_support protection.1 history degree
end Lamping.Lambda.Labelled








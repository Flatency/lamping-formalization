import Lamping.Lambda.LabelAtomicFamilies
import Lamping.Lambda.LabelRegionTransport
import Lamping.Lambda.ExtractionFamilyInvariance
namespace Lamping.Lambda.Labelled

/-- Regional degrees retain old redex names across contractions whose degree
is not supported in that region. New boundary crossings cannot pass the guard. -/
inductive RegionalOrigins (region : Nat → Prop) : Marked → LTerm → Prop where
  | var (l i) : RegionalOrigins region (.var i) (.var l i)
  | lam : RegionalOrigins region b c → RegionalOrigins region (.lam b) (.lam l c)
  | app : RegionalOrigins region f g → RegionalOrigins region a b →
      (∀ l c,g=.lam l c → l.Supported region → tags≠[]) →
      RegionalOrigins region (.app tags f a) (.app beta g b)
  | red : RegionalOrigins region b c → RegionalOrigins region a e → tags≠[] →
      RegionalOrigins region (.red tags b a) (.app beta (.lam alpha c) e)

namespace RegionalOrigins

theorem prepend (h : RegionalOrigins region m t) (a : Label) :
    RegionalOrigins region m (t.prepend a) := by
  cases h with
  | var => exact .var _ _
  | lam body => exact .lam body
  | app fn arg tags => exact .app fn arg tags
  | red body arg tags => exact .red body arg tags

theorem rename (h : RegionalOrigins region m t) (rho : Nat → Nat) :
    RegionalOrigins region (m.rename rho) (t.rename rho) := by
  induction h generalizing rho with
  | var => exact .var _ _
  | lam _ ih => exact .lam (ih _)
  | app fn arg tags hf ha =>
    apply RegionalOrigins.app (hf rho) (ha rho)
    intro l c eq support
    cases fn with
    | var => cases eq
    | lam body => cases eq; exact tags _ _ rfl support
    | app => cases eq
    | red => cases eq
  | red body arg tags hb ha => exact .red (hb _) (ha _) tags

/-- A replacement may contain old regional redexes internally, but a newly
exposed root lambda must carry the nonregional crossing prefix. -/
def Value (region : Nat → Prop) (m : Marked) : LTerm.SubValue → Prop
  | .keep i => m=.var i
  | .put t => RegionalOrigins region m t ∧ ∀ l b,t=.lam l b → ¬l.Supported region

theorem lift_values (h : ∀ i,Value region (sigma i) (tau i)) :
    ∀ i,Value region (Marked.liftSub sigma i) (LTerm.lift tau i) := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
    cases ht : tau i with
    | keep j =>
      have hm : sigma i=.var j := by simpa [Value,ht] using h i
      simp [LTerm.lift,Marked.liftSub,ht,Value,hm,Marked.rename]
    | put t =>
      have hm : RegionalOrigins region (sigma i) t ∧ ∀ l b,t=.lam l b → ¬l.Supported region := by
        simpa only [Value,ht] using h i
      simp only [Marked.liftSub,LTerm.lift,ht,Value]
      refine ⟨hm.1.rename Nat.succ,?_⟩
      intro l b shape
      cases t with
      | var => cases shape
      | app => cases shape
      | lam alpha body => cases shape; exact hm.2 _ _ rfl

theorem subst (h : RegionalOrigins region m t) (values : ∀ i,Value region (sigma i) (tau i)) :
    RegionalOrigins region (m.subst sigma) (t.subst tau) := by
  induction h generalizing sigma tau with
  | var l i =>
    cases ht : tau i with
    | keep j =>
      have hm : sigma i=.var j := by simpa [Value,ht] using values i
      simpa [Marked.subst,LTerm.subst,ht,hm] using RegionalOrigins.var (region := region) l j
    | put t =>
      have hm : RegionalOrigins region (sigma i) t := ((by simpa only [Value,ht] using values i) :
        RegionalOrigins region (sigma i) t ∧ _).1
      simpa only [Marked.subst,LTerm.subst,ht] using hm.prepend l
  | lam body ih => exact .lam (ih (lift_values values))
  | app fn arg old hf ha =>
    apply RegionalOrigins.app (hf values) (ha values)
    intro l c eq support
    cases fn with
    | var label i =>
      cases hv : tau i with
      | keep j => simp [LTerm.subst,hv] at eq
      | put t =>
        have blocked : ∀ alpha b,t=.lam alpha b → ¬alpha.Supported region :=
          ((by simpa only [Value,hv] using values i) : RegionalOrigins region (sigma i) t ∧ _).2
        cases t with
        | var => simp [LTerm.subst,hv,LTerm.prepend] at eq
        | app => simp [LTerm.subst,hv,LTerm.prepend] at eq
        | lam alpha body =>
          simp only [LTerm.subst,hv,LTerm.prepend] at eq
          cases eq
          exact False.elim (blocked _ _ rfl ((Label.supported_concat _ _ _).mp support).2)
    | lam body => cases eq; exact old _ _ rfl support
    | app => cases eq
    | red => cases eq
  | red body arg tags hb ha => exact .red (hb (lift_values values)) (ha values) tags

theorem contract (body : RegionalOrigins region b c) (arg : RegionalOrigins region a e)
    (outside : ¬alpha.Supported region) :
    RegionalOrigins region (Marked.contract b a) (LTerm.contract beta alpha c e) := by
  apply RegionalOrigins.prepend
  apply body.subst
  intro i
  cases i with
  | succ i => rfl
  | zero =>
    refine ⟨arg.prepend alpha.under,?_⟩
    intro l b shape support
    cases e with
    | var => cases shape
    | app => cases shape
    | lam label body =>
      simp only [LTerm.prepend,LTerm.lam.injEq] at shape
      obtain ⟨rfl,rfl⟩ := shape
      exact outside ((Label.supported_concat _ _ _).mp support).1
end RegionalOrigins

theorem StepAt.regional_lambda_reflect {body : LTerm} (step : StepAt p t u)
    (outside : ∀ alpha,t.degreeAt p=some alpha → ¬alpha.Supported region)
    (shape : u=.lam l body) (support : l.Supported region) : ∃ sourceBody,t=.lam l sourceBody := by
  cases step with
  | root beta alpha b a =>
    have labelEq := congrArg LTerm.label shape
    rw [LTerm.contract,label_prepend] at labelEq
    have crossed : ((beta.concat alpha.over).concat
        (b.subst (LTerm.single (a.prepend alpha.under))).label).Supported region := by
      simpa only [labelEq] using support
    have headSupport := ((Label.supported_concat _ _ _).mp
      ((Label.supported_concat _ _ _).mp crossed).1).2
    exact False.elim (outside alpha rfl headSupport)
  | fn => cases shape
  | arg => cases shape
  | body => cases shape; exact ⟨_,rfl⟩

theorem RegionalOrigins.step (marked : Marked.ReductionAt p m n)
    (source : RegionalOrigins region m t) (step : StepAt p t u)
    (outside : ∀ alpha,t.degreeAt p=some alpha → ¬alpha.Supported region) :
    RegionalOrigins region n u := by
  induction marked generalizing t u with
  | appRoot tags b a =>
    cases source with
    | app fn arg old =>
      cases fn with
      | lam body => cases step with | root => exact body.contract arg (outside _ rfl)
  | redRoot tags b a =>
    cases source with
    | red body arg old => cases step with | root => exact body.contract arg (outside _ rfl)
  | lam marked ih =>
    cases source with
    | lam body => cases step with | body step => exact .lam (ih body step outside)
  | appL marked ih =>
    cases source with
    | app fn arg old =>
      cases step with
      | fn step =>
        apply RegionalOrigins.app (ih fn step outside) arg
        intro l body shape support
        obtain ⟨sourceBody,sourceShape⟩ := step.regional_lambda_reflect outside shape support
        exact old l sourceBody sourceShape support
  | appR marked ih =>
    cases source with
    | app fn arg old => cases step with | arg step => exact .app fn (ih arg step outside) old
  | redL marked ih =>
    cases source with
    | red body arg old =>
      cases step with
      | fn step => cases step with | body step => exact .red (ih body step outside) arg old
  | redR marked ih =>
    cases source with
    | red body arg old => cases step with | arg step => exact .red body (ih arg step outside) old

theorem RegionalOrigins.markAt (t : LTerm) (selected : List Path) (p : Path) :
    RegionalOrigins region (Marked.markAt selected t.erase p) t := by
  induction t generalizing p with
  | var l i => exact .var _ _
  | lam l b ih => exact .lam (ih _)
  | app l f a hf ha =>
    cases f with
    | var label i => exact .app (hf _) (ha _) (by intro l b eq; cases eq)
    | app label g b => exact .app (hf _) (ha _) (by intro l b eq; cases eq)
    | lam label b =>
      have body := hf (p++[.fn])
      cases body with
      | lam body =>
        simp only [LTerm.erase,Marked.markAt]
        split
        · exact .red body (ha _) (by simp)
        · exact .app (.lam body) (ha _) (by simp)

theorem RegionalOrigins.initial (t : LTerm) : RegionalOrigins region (Marked.mark [] t.erase) t :=
  RegionalOrigins.markAt t [] []
theorem RegionalOrigins.regional_trace (aligned : RegionalOrigins region m t)
    (degree : t.degreeAt p=some l) (support : l.Supported region) :
    ∃ r,p∈Marked.tracePositions r m := by
  induction p generalizing m t with
  | nil =>
    cases aligned with
    | var => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
    | lam => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
    | app fn arg old =>
      cases fn with
      | var => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | app => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | red => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | lam body =>
        simp only [LTerm.degreeAt,LTerm.subterm,Option.bind_some,LTerm.degree,Option.some.injEq] at degree
        cases degree
        obtain ⟨r,member⟩ := List.exists_mem_of_ne_nil _ (old _ _ rfl support)
        exact ⟨r,by simp [Marked.tracePositions,member]⟩
    | red body arg old =>
      obtain ⟨r,member⟩ := List.exists_mem_of_ne_nil _ old
      exact ⟨r,by simp [Marked.tracePositions,member]⟩
  | cons s p ih =>
    cases aligned with
    | var => cases s <;> simp [LTerm.degreeAt,LTerm.subterm] at degree
    | lam body =>
      cases s with
      | fn => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | arg => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | body =>
        obtain ⟨r,member⟩ := ih body degree
        exact ⟨r,List.mem_map_of_mem member⟩
    | app fn arg old =>
      cases s with
      | body => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | fn =>
        obtain ⟨r,member⟩ := ih fn degree
        exact ⟨r,List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem member))⟩
      | arg =>
        obtain ⟨r,member⟩ := ih arg degree
        exact ⟨r,List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem member))⟩
    | red body arg old =>
      cases s with
      | body => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | fn =>
        cases p with
        | nil => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
        | cons s p =>
          cases s with
          | fn => simp [LTerm.degreeAt,LTerm.subterm] at degree
          | arg => simp [LTerm.degreeAt,LTerm.subterm] at degree
          | body =>
            obtain ⟨r,member⟩ := ih (.lam (l := Label.atom 0) body) degree
            simp only [Marked.tracePositions,List.mem_map] at member
            obtain ⟨q,member,eq⟩ := member
            have same : q=p := (List.cons.inj eq).2
            cases same
            exact ⟨r,List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem member))⟩
      | arg =>
        obtain ⟨r,member⟩ := ih arg degree
        exact ⟨r,List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem member))⟩

private theorem source_trace_valid (tracked : Marked.History ps (Marked.mark [] source) target)
    (trace : p∈Marked.tracePositions r target) :
    ∃ node,subtermAt source r=some node ∧ IsRedex node := by
  by_cases found : r∈redexPositions source
  · exact (mem_redexPositions source r).mp found
  · have empty : Marked.tracePositions r (Marked.mark [] source)=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q member
      obtain ⟨same,redex⟩ := (Marked.trace_mark [] source r q).mp member
      exact found (same ▸ redex)
    have finalEmpty := tracked.trace_empty empty
    exact False.elim (List.not_mem_nil (finalEmpty ▸ trace))

/-- A nonregional contraction cannot newly create a regional-degree redex.
The conclusion is a genuine old-name residual of the one-step derivation. -/
theorem StepAt.regional_degree_residual (step : StepAt p t u)
    (outside : ∀ alpha,t.degreeAt p=some alpha → ¬alpha.Supported region)
    (s : RedexOcc u.erase) (degree : u.degreeAt s.val=some l) (support : l.Supported region) :
    ∃ r : RedexOcc t.erase,
      (⟨[p],.cons step.betaAt (.nil _)⟩ : Derivation t.erase u.erase).Residual r s := by
  let derivation : Derivation t.erase u.erase := ⟨[p],.cons step.betaAt (.nil _)⟩
  obtain ⟨target,tracked,erased⟩ := derivation.tracked
  have aligned : RegionalOrigins region target u := by
    change Marked.History [p] (Marked.mark [] t.erase) target at tracked
    cases tracked with
    | cons marked rest =>
      cases rest
      exact (RegionalOrigins.initial t).step marked step outside
  obtain ⟨r,trace⟩ := aligned.regional_trace degree support
  exact ⟨⟨r,source_trace_valid tracked trace⟩,target,tracked,erased,trace⟩

/-- For a normal two-event pointed run, every regional support predicate of
the final degree also supports the first degree. Otherwise real rule (i)
deletes the first event via the old residual just constructed. -/
theorem normal_two_events_support (step : StepAt p t u) (last : BetaAt u.erase q n)
    (normal : ExtractionNormal (.of
      (.cons (singleContraction step.betaAt) (.single (singleContraction last)))
      (.cons step.betaAt (.single last))))
    (atHead : t.degreeAt p=some headDegree) (atLast : u.degreeAt q=some lastDegree)
    (support : lastDegree.Supported region) : headDegree.Supported region := by
  classical
  by_cases safe : headDegree.Supported region
  · exact safe
  · have outside : ∀ alpha,t.degreeAt p=some alpha → ¬alpha.Supported region := by
      intro alpha atAlpha
      have same := Option.some.inj (atHead.symm.trans atAlpha)
      cases same
      exact safe
    obtain ⟨r,residual⟩ := step.regional_degree_residual outside ⟨q,last.redex⟩ atLast support
    let program : ParallelHistory t.erase u.erase := .single (singleContraction step.betaAt)
    have same : (⟨[p],.cons step.betaAt (.nil _)⟩ : Derivation t.erase u.erase)=program.derivation :=
      Lamping.Lambda.Derivation.ext rfl
    rw [same] at residual
    exact False.elim (normal_no_old_last program (.single step.betaAt) (by change 0<1; omega) last normal r residual)

/-- The complete two-event case of regional canonical internality. The
pointed run is proved internal as a whole, including its final contraction. -/
theorem normal_two_events_argument_internal (step : StepAt p t u) (last : BetaAt u.erase q n)
    (normal : ExtractionNormal (.of
      (.cons (singleContraction step.betaAt) (.single (singleContraction last)))
      (.cons step.betaAt (.single last))))
    (initial : INIT t) (atSite : t.subterm (site++[.arg])=some subtree)
    (atLast : u.degreeAt q=some lastDegree)
    (support : lastDegree.Supported (SourceRegion subtree)) :
    Internal (site++[.arg])
      (.cons (singleContraction step.betaAt) (.single (singleContraction last))) := by
  obtain ⟨headDegree,atHead⟩ := degreeAt_exists t ⟨p,step.betaAt.redex⟩
  have headSupport := normal_two_events_support step last normal atHead atLast support
  have firstInside := LTerm.initial_argument_degree_internal t initial atSite atHead
    ((Label.supported_iff_within _ _).mp headSupport)
  have history : History [p] t u := .cons step (.nil _)
  have confined : ∀ r∈([p] : List Path),∃ suffix,r=(site++[.arg])++suffix := by
    intro r member
    have same := List.mem_singleton.mp member
    exact same ▸ firstInside
  have cut := history.region_cut initial atSite confined
  obtain ⟨body,atLambda⟩ := LTerm.degreeAt_lambda atLast
  have lambdaInside := cut.supported_node_internal initial atSite atLambda support
  obtain ⟨suffix,position⟩ := lambdaInside
  have lastInside := Path.fn_inside_argument position
  intro r member
  change r∈[p,q] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact firstInside
  · exact lastInside

/-- A one-event ordinary pointed run represents an actual initial redex,
whose degree is atomic under the original INIT labelling. -/
theorem rank_one_degree_atomic (t : LTerm) (initial : INIT t)
    (run : ExtractionRun t.erase) (rank : run.rank=1)
    (a : RedexWithHistory t.erase) (represented : RunRepresents run a) :
    ∃ k,degreeAlong t a.history.derivation.paths a.redex.val=some (Label.atom k) := by
  rcases a with ⟨n,program,s⟩
  obtain ⟨last,ordinary,shape⟩ := represented
  have lengths : program.length+1=1 := by
    change run.history.length=1 at rank
    rw [shape,ParallelHistory.length_append] at rank
    exact rank
  cases program with
  | nil =>
    obtain ⟨l,degree⟩ := degreeAt_exists t s
    obtain ⟨body,atLambda⟩ := LTerm.degreeAt_lambda degree
    obtain ⟨k,equal⟩ := initial.1 l (LTerm.label_mem_of_subterm atLambda)
    exact ⟨k,by simpa only [degreeAlong,LTerm.replay,Option.bind_some,equal] using degree⟩
  | cons step tail =>
    simp only [ParallelHistory.length] at lengths
    omega

/-- In the two-event case a non-atomic pointed degree also certifies actual
extraction normality: any extraction successor would have rank one and an
atomic same-family degree. This uses only the proved forward family theorem. -/
theorem rank_two_compound_normal (t : LTerm) (initial : INIT t)
    (run : ExtractionRun t.erase) (rank : run.rank=2)
    (a : RedexWithHistory t.erase) (represented : RunRepresents run a)
    (compound : ¬∃ k,degreeAlong t a.history.derivation.paths a.redex.val=some (Label.atom k)) :
    ExtractionNormal run := by
  rintro ⟨next,step⟩
  have smaller := step.rank_lt
  have positive := step.positive
  have one : next.rank=1 := by omega
  obtain ⟨b,representsB⟩ := next.represents_exists positive
  obtain ⟨k,atomic⟩ := rank_one_degree_atomic t initial next one b representsB
  have family := step.family a b represented representsB
  have equal := Labelled.FamilyEq.degreeAlong family t rfl
  exact compound ⟨k,equal.trans atomic⟩

/-- Every carried old name already denoted an actual source redex. -/
def OldNamesValid (source : Term) (marked : Marked) : Prop :=
  ∀ r p,p∈Marked.tracePositions r marked → ∃ node,subtermAt source r=some node ∧ IsRedex node

theorem OldNamesValid.initial (source : Term) : OldNamesValid source (Marked.mark [] source) := by
  intro r p trace
  obtain ⟨same,redex⟩ := (Marked.trace_mark [] source r p).mp trace
  exact same ▸ (mem_redexPositions source p).mp redex

theorem OldNamesValid.step (valid : OldNamesValid source m) (step : Marked.ReductionAt p m n) :
    OldNamesValid source n := by
  intro r q member
  by_cases empty : Marked.tracePositions r m=[]
  · have finalEmpty := step.trace_empty empty
    exact False.elim (List.not_mem_nil (finalEmpty ▸ member))
  · obtain ⟨old,trace⟩ := List.exists_mem_of_ne_nil _ empty
    exact valid r old trace

theorem RegionalOrigins.outside_degree {original : LTerm} (regional : RegionalOrigins region m current)
    (aligned : DegreeAligned original.degreeAt m current) (valid : OldNamesValid original.erase m)
    (outside : ∀ r : RedexOcc original.erase,∀ l,original.degreeAt r.val=some l → ¬l.Supported region)
    (degree : current.degreeAt p=some l) : ¬l.Supported region := by
  intro support
  obtain ⟨r,trace⟩ := regional.regional_trace degree support
  have oldDegree := aligned.trace_degree trace
  exact outside ⟨r,valid r p trace⟩ l (oldDegree.symm.trans degree) support

/-- General length invariant. Nonregionality of each actual contracted degree
is derived from old-tag reflection and source-degree transport at that stage;
it is not supplied as an unproved property of the chosen history. -/
theorem RegionalOrigins.history_of_initial_outside {original : LTerm} (marked : Marked.History ps m n)
    (history : History ps current target) (regional : RegionalOrigins region m current)
    (aligned : DegreeAligned original.degreeAt m current) (valid : OldNamesValid original.erase m)
    (outside : ∀ r : RedexOcc original.erase,∀ l,original.degreeAt r.val=some l → ¬l.Supported region) :
    RegionalOrigins region n target ∧ DegreeAligned original.degreeAt n target ∧ OldNamesValid original.erase n := by
  induction marked generalizing current target with
  | nil => cases history; exact ⟨regional,aligned,valid⟩
  | cons step tail ih =>
    cases history with
    | cons beta rest =>
      exact ih rest (regional.step step beta
        (fun _ degree => regional.outside_degree aligned valid outside degree))
        (aligned.step step beta) (valid.step step)

/-- Every generated redex degree contains the original atomic degree of an
actual initial redex. This supplies a real source candidate for First Redex;
it does not yet identify the canonical first event with the LO candidate. -/
theorem History.redex_uses_initial_degree (history : History ps t u) (initial : INIT t)
    (degree : u.degreeAt p=some l) :
    ∃ r : RedexOcc t.erase,∃ n,t.degreeAt r.val=some (Label.atom n) ∧
      ∃ e∈l.edgeWord,e.atom=n := by
  classical
  let region : Nat → Prop := fun n => ∀ r : RedexOcc t.erase,t.degreeAt r.val≠some (Label.atom n)
  have outside : ∀ r : RedexOcc t.erase,∀ a,t.degreeAt r.val=some a → ¬a.Supported region := by
    intro r a atInitial support
    obtain ⟨body,atLambda⟩ := LTerm.degreeAt_lambda atInitial
    obtain ⟨n,equal⟩ := initial.1 a (LTerm.label_mem_of_subterm atLambda)
    cases equal
    exact support r atInitial
  let derivation : Derivation t.erase u.erase := ⟨ps,history.betaHistory⟩
  obtain ⟨marked,tracked,erased⟩ := derivation.tracked
  obtain ⟨regional,aligned,valid⟩ := RegionalOrigins.history_of_initial_outside tracked history
    (RegionalOrigins.initial t) (DegreeAligned.initial t []) (OldNamesValid.initial t.erase) outside
  have notRegional := regional.outside_degree aligned valid outside degree
  by_cases found : ∃ r : RedexOcc t.erase,∃ n,t.degreeAt r.val=some (Label.atom n) ∧ ∃ e∈l.edgeWord,e.atom=n
  · exact found
  · apply False.elim
    apply notRegional
    apply (Label.supported_iff_within _ _).mpr
    intro e member r atInitial
    exact found ⟨r,e.atom,atInitial,e,member,rfl⟩
end Lamping.Lambda.Labelled


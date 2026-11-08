import Lamping.Lambda.CopyRegionCases
import Lamping.Lambda.LabelArgumentRegionalSchedules
namespace Lamping.Lambda.Labelled

/-- The actual syntax at and to the left of a protected head cut. Ancestor
labels/constructors and left siblings are fixed; right siblings may change.
The cut root itself still carries the first contraction's atom. -/
inductive ProtectedHeadCut (a : Nat) : Path → LTerm → LTerm → Prop where
  | here (tainted : ¬current.label.Supported (fun n => n≠a)) : ProtectedHeadCut a [] original current
  | fn : ProtectedHeadCut a p fn fn' →
      ProtectedHeadCut a (.fn::p) (.app label fn arg) (.app label fn' arg')
  | arg : ProtectedHeadCut a p arg arg' →
      ProtectedHeadCut a (.arg::p) (.app label fn arg) (.app label fn arg')
  | body : ProtectedHeadCut a p body body' →
      ProtectedHeadCut a (.body::p) (.lam label body) (.lam label body')

/-- The first actual beta creates a root label requiring its entire degree,
including its atomic head a. This is recursive support, not degree equality. -/
theorem LTerm.contract_root_requires_head (beta : Label) (body argument : LTerm) (a : Nat) :
    ¬(LTerm.contract beta (Label.atom a) body argument).label.Supported (fun n => n≠a) := by
  intro support
  simp only [LTerm.contract,label_prepend,Label.supported_concat] at support
  exact support.1.2 rfl

/-- Establish the protected syntax cut from the real first contraction. -/
theorem StepAt.protected_head_cut (head : StepAt p t u) (degree : t.degreeAt p=some (Label.atom a)) :
    ProtectedHeadCut a p t u := by
  induction head with
  | root beta alpha body argument =>
    have equal : alpha=Label.atom a := Option.some.inj degree
    cases equal
    exact .here (LTerm.contract_root_requires_head _ _ _ _)
  | fn step ih => exact .fn (ih degree)
  | arg step ih => exact .arg (ih degree)
  | body step ih => exact .body (ih degree)

/-- Any real degree to the left of a protected cut is the same degree at
that original source occurrence, or itself requires the first head atom.
This is proved from the actual syntax relation, without origin fields. -/
theorem ProtectedHeadCut.left_degree (cut : ProtectedHeadCut a p t u)
    (before : LeftOf q p) (degree : u.degreeAt q=some l) :
    t.degreeAt q=some l ∨ ¬l.Supported (fun n => n≠a) := by
  induction cut generalizing q with
  | here tainted => cases before
  | @fn p fn fn' label arg arg' child ih =>
    cases q with
    | nil =>
      cases child with
      | here tainted =>
        exact .inr (by
          have same := LTerm.degree_root_function_label degree
          exact fun support => tainted (same.symm ▸ support))
      | fn child => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | arg child => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | body child => exact .inl degree
    | cons edge q =>
      cases edge with
      | fn =>
        cases before with
        | child _ earlier => exact ih earlier degree
      | arg => cases before
      | body => simp [LTerm.degreeAt,LTerm.subterm] at degree
  | @arg p arg arg' label fn child ih =>
    cases q with
    | nil =>
      apply Or.inl
      cases fn <;> simpa only [LTerm.degreeAt,LTerm.subterm,LTerm.degree] using degree
    | cons edge q =>
      cases edge with
      | fn => exact .inl degree
      | arg =>
        cases before with
        | child _ earlier => exact ih earlier degree
      | body => simp [LTerm.degreeAt,LTerm.subterm] at degree
  | @body p body body' label child ih =>
    cases q with
    | nil => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
    | cons edge q =>
      cases edge with
      | fn => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | arg => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | body =>
        cases before with
        | child _ earlier => exact ih earlier degree

/-- A true internal step preserves the protected ancestry and the head's
root taint. The latter follows by contraposing actual root-support reflection. -/
theorem ProtectedHeadCut.step_inside (cut : ProtectedHeadCut a p t u)
    (step : StepAt (p++suffix) u v) : ProtectedHeadCut a p t v := by
  induction cut generalizing v with
  | here tainted => exact .here (fun support => tainted (step.root_support support))
  | fn child ih => cases step with | fn localStep => exact .fn (ih localStep)
  | arg child ih => cases step with | arg localStep => exact .arg (ih localStep)
  | body child ih => cases step with | body localStep => exact .body (ih localStep)

/-- A real disjoint step to the right may change a right sibling, while
all protected left siblings and cut ancestors remain literally unchanged. -/
theorem ProtectedHeadCut.step_right (cut : ProtectedHeadCut a p t u)
    (step : StepAt q u v) (right : LeftOf p q) (apart : DisjointPositions p q) :
    ProtectedHeadCut a p t v := by
  induction cut generalizing q v with
  | here => exact False.elim (DisjointPositions.nil_left apart)
  | fn child ih =>
    cases step with
    | root => exact False.elim (DisjointPositions.nil_right apart)
    | fn localStep =>
      cases right with
      | child _ earlier => exact .fn (ih localStep earlier apart.child)
    | arg localStep => exact .fn child
  | arg child ih =>
    cases step with
    | root => exact False.elim (DisjointPositions.nil_right apart)
    | fn localStep => cases right
    | arg localStep =>
      cases right with
      | child _ earlier => exact .arg (ih localStep earlier apart.child)
  | body child ih =>
    cases step with
    | body localStep =>
      cases right with
      | child _ earlier => exact .body (ih localStep earlier apart.child)

/-- The protected cut remains an actual occurrence, carrying its tainted
current root label; no hypothetical source node is used. -/
theorem ProtectedHeadCut.current_lookup (cut : ProtectedHeadCut a p t u) :
    ∃ node,u.subterm p=some node ∧ ¬node.label.Supported (fun n => n≠a) := by
  induction cut with
  | here tainted => exact ⟨_,by simp [LTerm.subterm],tainted⟩
  | fn _ ih => exact ih
  | arg _ ih => exact ih
  | body _ ih => exact ih

private theorem protected_standard_head_no_return (first : BetaAt source p middle)
    (tail : ParallelHistory middle target) (standard : Standard (.cons (singleContraction first) tail)) :
    DoesNotReturnLeft ⟨p,first.redex⟩ (.cons (singleContraction first) tail) := by
  cases standard with
  | cons _ witness selected noReturn rest =>
    have same : witness=⟨p,first.redex⟩ := Subtype.ext (List.mem_singleton.mp selected.1)
    cases same
    exact noReturn
/-- A real left event would either contract a head-tainted degree, or use a
real initial redex left of the Standard head. Both alternatives are excluded
from actual degrees and the original DoesNotReturnLeft condition. -/
theorem ProtectedHeadCut.event_not_left
    (cut : ProtectedHeadCut a p t u) (initial : INIT t)
    (pre : History before t u) (event : StepAt q u v) (post : History after v z)
    (degree : u.degreeAt q=some l) (avoid : l.Supported (fun n => n≠a))
    (head : BetaAt t.erase p headTarget) (tail : ParallelHistory headTarget z.erase)
    (ordinary : Atomic tail) (standard : Standard (.cons (singleContraction head) tail))
    (paths : (ParallelHistory.cons (singleContraction head) tail).derivation.paths=before++q::after) :
    ¬LeftOf q p := by
  intro earlier
  rcases cut.left_degree earlier degree with oldDegree | tainted
  · obtain ⟨body,lookup⟩ := LTerm.degreeAt_lambda oldDegree
    obtain ⟨n,atomic⟩ := initial.1 l (LTerm.label_mem_of_subterm lookup)
    obtain ⟨beta,b,argument,atRedex⟩ := LTerm.degreeAt_redex oldDegree
    let old : RedexOcc t.erase := ⟨q,by
      refine ⟨.app (.lam b.erase) argument.erase,?_,True.intro⟩
      rw [←LTerm.erase_subterm,atRedex]
      rfl⟩
    have fired : FiresAtom (before++q::after) t z n :=
      ⟨before,q,after,u,v,rfl,pre,event,by simpa only [atomic] using degree,post⟩
    have used := fired.used_source initial old (by simpa only [atomic] using oldDegree)
      (.cons (singleContraction head) tail) (.cons head ordinary) paths
    have noReturn := protected_standard_head_no_return head tail standard
    exact noReturn.no_used_left (.cons head ordinary) old earlier used
  · exact tainted avoid

/-- Actual occurrence comparison plus the proved left-event exclusion gives
the precise inside/right-disjoint geometry for the next real event. -/
theorem ProtectedHeadCut.event_geometry
    (cut : ProtectedHeadCut a p t u) (initial : INIT t)
    (pre : History before t u) (event : StepAt q u v) (post : History after v z)
    (degree : u.degreeAt q=some l) (avoid : l.Supported (fun n => n≠a))
    (head : BetaAt t.erase p headTarget) (tail : ParallelHistory headTarget z.erase)
    (ordinary : Atomic tail) (standard : Standard (.cons (singleContraction head) tail))
    (paths : (ParallelHistory.cons (singleContraction head) tail).derivation.paths=before++q::after) :
    (∃ suffix,q=p++suffix) ∨ (LeftOf p q ∧ DisjointPositions p q) := by
  obtain ⟨node,lookup,_⟩ := cut.current_lookup
  have headPosition : (subtermAt u.erase p).isSome := by rw [←LTerm.erase_subterm,lookup]; rfl
  obtain ⟨redex,atRedex,_⟩ := event.betaAt.redex
  have eventPosition : (subtermAt u.erase q).isSome := by rw [atRedex]; rfl
  rcases compare_positions u.erase p q headPosition eventPosition with same | later | earlier
  · exact .inl ⟨[],by simpa only [List.append_nil] using same.symm⟩
  · rcases later.inside_or_disjoint with inside | apart
    · exact .inl inside
    · exact .inr ⟨later,apart⟩
  · exact False.elim (cut.event_not_left initial pre event post degree avoid head tail ordinary standard paths earlier)

/-- Protect the actual cut through a whole finite tail. Every left event is
ruled out using the original Standard run and its real decomposition, while
each accepted event transports the actual protected syntax relation. -/
theorem RegionalHistory.protected_geometry
    (regional : RegionalHistory (fun n => n≠a) qs u v)
    (cut : ProtectedHeadCut a p t u) (pre : History before t u) (initial : INIT t)
    (head : BetaAt t.erase p headTarget) (tail : ParallelHistory headTarget v.erase)
    (ordinary : Atomic tail) (standard : Standard (.cons (singleContraction head) tail))
    (paths : (ParallelHistory.cons (singleContraction head) tail).derivation.paths=before++qs) :
    ∀ q∈qs,(∃ suffix,q=p++suffix) ∨ (LeftOf p q ∧ DisjointPositions p q) := by
  induction regional generalizing before with
  | nil => simp
  | @cons q u middle l qs v step degree avoid rest ih =>
    have geometry := cut.event_geometry initial pre step rest.history degree avoid head tail ordinary standard paths
    have nextCut : ProtectedHeadCut a p t middle := by
      rcases geometry with ⟨suffix,equal⟩ | ⟨right,apart⟩
      · rw [equal] at step
        exact cut.step_inside step
      · exact cut.step_right step right apart
    have extended := pre.append (.cons step (.nil _))
    have nextPaths : (ParallelHistory.cons (singleContraction head) tail).derivation.paths=(before++[q])++qs := by
      simpa only [List.append_assoc,List.singleton_append] using paths
    have nextGeometry := ih nextCut extended tail ordinary standard nextPaths
    intro site member
    rcases List.mem_cons.mp member with first | later
    · exact first ▸ geometry
    · exact nextGeometry site later

/-- The exact protected-cut conclusion for an INIT first step followed by a
real nonempty or empty whole tail avoiding its head atom. Standardness and
recursive support are consumed; no geometric conclusion is an input field. -/
theorem RegionalHistory.head_tail_geometry
    (regional : RegionalHistory (fun n => n≠a) qs u v) (head : StepAt p t u)
    (initial : INIT t) (degree : t.degreeAt p=some (Label.atom a))
    (tail : ParallelHistory u.erase v.erase) (ordinary : Atomic tail)
    (standard : Standard (.cons (singleContraction head.betaAt) tail))
    (paths : tail.derivation.paths=qs) :
    ∀ q∈qs,(∃ suffix,q=p++suffix) ∨ (LeftOf p q ∧ DisjointPositions p q) := by
  apply regional.protected_geometry (head.protected_head_cut degree) (.cons head (.nil _)) initial
    head.betaAt tail ordinary standard
  change p::tail.derivation.paths=[p]++qs
  rw [paths]
  rfl
end Lamping.Lambda.Labelled








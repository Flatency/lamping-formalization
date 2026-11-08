import Lamping.Lambda.LabelHeadPorts
namespace Lamping.Lambda.Labelled

/- Every over/under payload in the word is supported in the region.
Ordinary outer atoms are deliberately unrestricted. -/
mutual
  def Label.BarsSafe (region : Nat → Prop) : Label → Prop
    | .single a => a.BarsSafe region
    | .cons a l => a.BarsSafe region ∧ l.BarsSafe region
  def Letter.BarsSafe (region : Nat → Prop) : Letter → Prop
    | .atom _ => True
    | .over l | .under l => l.Supported region
end

theorem Label.barsSafe_concat (region) : ∀ a b : Label,
    (a.concat b).BarsSafe region ↔ a.BarsSafe region ∧ b.BarsSafe region
  | .single _,_ => Iff.rfl
  | .cons a l,b => by simp [Label.concat,Label.BarsSafe,barsSafe_concat,and_assoc]

/-- The original degree atom of a real source redex has precisely that
redex's function/lambda ports. Initial edge uniqueness proves the identity. -/
theorem SourceRoute.head_atom_ports {body argument : LTerm}
    (atHead : SourceSubterm [] .external t p env ctx (.app beta (.lam (Label.atom n) body) argument))
    (initial : INIT t) (route : SourceRoute (sourceEdges [] .external t) start (Label.atom n) finish) :
    start=.appFn beta ∧ finish=.lamContext (Label.atom n) := by
  have headMember : (⟨Label.atom n,.appFn beta,.lamContext (Label.atom n)⟩ : SourceEdge)∈sourceEdges [] .external t :=
    atHead.edges_subset _ (List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self))
  obtain ⟨m,firstEdge,first,firstMember,firstAtomic,fromPortEq⟩ := route.first_atom
  have same : n=m := Option.some.inj first
  cases same
  have firstEq := sourceEdges_unique initial firstMember headMember firstAtomic
  obtain ⟨m,lastEdge,last,lastMember,lastAtomic,to⟩ := route.last_atom
  have same : n=m := Option.some.inj last
  cases same
  have lastEq := sourceEdges_unique initial lastMember headMember lastAtomic
  exact ⟨by simpa only [firstEq] using fromPortEq.symm,by simpa only [lastEq] using to.symm⟩

/-- An initial redex atom cannot occur as an ordinary outer piece of a larger
route: the adjoining app/body/binding ports would disagree. It must lie in a
bar payload unless the whole route is that one atomic edge. -/
theorem SourceRoute.initial_atom_exposure {body argument : LTerm}
    (atHead : SourceSubterm [] .external t p env ctx (.app beta (.lam (Label.atom n) body) argument))
    (initial : INIT t) (route : SourceRoute (sourceEdges [] .external t) start l finish)
    (bars : l.BarsSafe (fun m => m≠n)) : l.Supported (fun m => m≠n) ∨ l=Label.atom n := by
  induction route with
  | @atom e m member atomic =>
    by_cases equal : m=n
    · exact .inr (congrArg Label.atom equal)
    · exact .inl equal
  | over left middle right hl hm hr =>
    obtain ⟨prefixBars,rightBars⟩ := (Label.barsSafe_concat _ _ _).mp bars
    obtain ⟨leftBars,middleSupport⟩ := (Label.barsSafe_concat _ _ _).mp prefixBars
    have leftSupport := hl leftBars
    have rightSupport := hr rightBars
    rcases leftSupport with leftSupport | equal
    · rcases rightSupport with rightSupport | equal
      · exact .inl ((Label.supported_concat _ _ _).mpr
          ⟨(Label.supported_concat _ _ _).mpr ⟨leftSupport,middleSupport⟩,rightSupport⟩)
      · cases equal
        have wrong := (right.head_atom_ports atHead initial).1
        cases wrong
    · cases equal
      have wrong := (left.head_atom_ports atHead initial).2
      cases wrong
  | under left middle right hl hm hr =>
    obtain ⟨prefixBars,rightBars⟩ := (Label.barsSafe_concat _ _ _).mp bars
    obtain ⟨leftBars,middleSupport⟩ := (Label.barsSafe_concat _ _ _).mp prefixBars
    have leftSupport := hl leftBars
    have rightSupport := hr rightBars
    rcases leftSupport with leftSupport | equal
    · rcases rightSupport with rightSupport | equal
      · exact .inl ((Label.supported_concat _ _ _).mpr
          ⟨(Label.supported_concat _ _ _).mpr ⟨leftSupport,middleSupport⟩,rightSupport⟩)
      · cases equal
        have wrong := (right.head_atom_ports atHead initial).1
        cases wrong
    · cases equal
      have wrong := (left.head_atom_ports atHead initial).2
      cases wrong
namespace LTerm
/-- All existing bar payloads, independently of the outer atomic pieces. -/
def BarsSafe (region : Nat → Prop) : LTerm → Prop
  | .var l _ => l.BarsSafe region
  | .lam l b => l.BarsSafe region ∧ b.BarsSafe region
  | .app l f a => l.BarsSafe region ∧ f.BarsSafe region ∧ a.BarsSafe region

theorem barsSafe_iff (region) (t : LTerm) :
    t.BarsSafe region ↔ ∀ l∈t.labels,l.BarsSafe region := by
  induction t with
  | var => simp [BarsSafe,labels]
  | lam _ _ ih => simp [BarsSafe,labels,ih]
  | app _ _ _ hf ha => simp [BarsSafe,labels,hf,ha,or_imp,forall_and]

theorem BarsSafe.rename {t : LTerm} (safe : t.BarsSafe region) (rho) :
    (t.rename rho).BarsSafe region := by
  induction t generalizing rho with
  | var => exact safe
  | lam _ _ ih => exact ⟨safe.1,ih safe.2 _⟩
  | app _ _ _ hf ha => exact ⟨safe.1,hf safe.2.1 _,ha safe.2.2 _⟩

theorem BarsSafe.prepend {t : LTerm} (safe : t.BarsSafe region) (bar : l.BarsSafe region) :
    (t.prepend l).BarsSafe region := by
  cases t with
  | var => exact (Label.barsSafe_concat _ _ _).mpr ⟨bar,safe⟩
  | lam => exact ⟨(Label.barsSafe_concat _ _ _).mpr ⟨bar,safe.1⟩,safe.2⟩
  | app => exact ⟨(Label.barsSafe_concat _ _ _).mpr ⟨bar,safe.1⟩,safe.2⟩

def SubValue.BarsSafe (region : Nat → Prop) : SubValue → Prop
  | .keep _ => True
  | .put t => t.BarsSafe region

theorem BarsSafe.subst {t : LTerm} {sigma : Nat → SubValue}
    (safe : t.BarsSafe region) (values : ∀ i,(sigma i).BarsSafe region) :
    (t.subst sigma).BarsSafe region := by
  induction t generalizing sigma with
  | var l i =>
    cases he : sigma i with
    | keep j => simpa only [LTerm.subst,he,BarsSafe] using safe
    | put u =>
      have hu : u.BarsSafe region := by simpa [SubValue.BarsSafe,he] using values i
      simpa only [LTerm.subst,he] using hu.prepend safe
  | app _ _ _ hf ha => exact ⟨safe.1,hf safe.2.1 values,ha safe.2.2 values⟩
  | lam _ _ ih =>
    refine ⟨safe.1,ih safe.2 ?_⟩
    intro i
    cases i with
    | zero => trivial
    | succ i =>
      cases he : sigma i with
      | keep j => simp [lift,he,SubValue.BarsSafe]
      | put u =>
        have hu : u.BarsSafe region := by simpa [SubValue.BarsSafe,he] using values i
        simpa only [lift,he,SubValue.BarsSafe] using hu.rename Nat.succ

theorem BarsSafe.contract {b a : LTerm} (bodySafe : b.BarsSafe region)
    (argSafe : a.BarsSafe region) (appSafe : beta.BarsSafe region)
    (degreeSupport : alpha.Supported region) :
    (contract beta alpha b a).BarsSafe region := by
  apply BarsSafe.prepend
  · apply bodySafe.subst
    intro i
    cases i with
    | zero => exact argSafe.prepend degreeSupport
    | succ i => trivial
  · exact (Label.barsSafe_concat _ _ _).mpr ⟨appSafe,degreeSupport⟩
end LTerm

theorem INIT.barsSafe (initial : INIT t) (region) : t.BarsSafe region := by
  rw [LTerm.barsSafe_iff]
  intro l member
  obtain ⟨n,rfl⟩ := initial.1 l member
  trivial

theorem StepAt.barsSafe (step : StepAt p t u) (safe : t.BarsSafe region)
    (degreeSupport : ∀ l,t.degreeAt p=some l → l.Supported region) : u.BarsSafe region := by
  induction step with
  | root beta alpha b a =>
    exact safe.2.1.2.contract safe.2.2 safe.1 (degreeSupport alpha rfl)
  | fn _ ih => exact ⟨safe.1,ih safe.2.1 degreeSupport,safe.2.2⟩
  | arg _ ih => exact ⟨safe.1,safe.2.1,ih safe.2.2 degreeSupport⟩
  | body _ ih => exact ⟨safe.1,ih safe.2 degreeSupport⟩
/-- A genuine event inside the supplied schedule; the surrounding histories
are retained, so this predicate cannot insert a new reduction. -/
def FiresAtom (ps : List Path) (t u : LTerm) (n : Nat) : Prop :=
  ∃ before site after v w, ps=before++site::after ∧ History before t v ∧
    StepAt site v w ∧ v.degreeAt site=some (Label.atom n) ∧ History after w u

theorem History.barsSafe_or_fires_atom {body argument : LTerm}
    (history : History ps v w) (source : History qs t v) (initial : INIT t)
    (atHead : SourceSubterm [] .external t p env ctx (.app beta (.lam (Label.atom n) body) argument))
    (safe : v.BarsSafe (fun m => m≠n)) :
    w.BarsSafe (fun m => m≠n) ∨ FiresAtom ps v w n := by
  classical
  induction history generalizing qs with
  | nil => exact .inl safe
  | @cons site v middle rest w step tail ih =>
    obtain ⟨degree,atDegree⟩ := degreeAt_exists v ⟨site,step.betaAt.redex⟩
    obtain ⟨appId,lamId,route⟩ := (source.generated_source_routes initial).degree_route atDegree
    obtain ⟨b,atLambda⟩ := LTerm.degreeAt_lambda atDegree
    have bars := (LTerm.barsSafe_iff _ v).mp safe degree (LTerm.label_mem_of_subterm atLambda)
    rcases route.initial_atom_exposure atHead initial bars with supported | atomic
    · have nextSafe := step.barsSafe safe (by
        intro l atL
        have equal : l=degree := Option.some.inj (atL.symm.trans atDegree)
        cases equal
        exact supported)
      rcases ih (source.append (.cons step (.nil _))) nextSafe with safeEnd | fired
      · exact .inl safeEnd
      · obtain ⟨before,r,after,x,y,paths,pre,event,degreeAt,post⟩ := fired
        exact .inr ⟨site::before,r,after,x,y,by simp [paths],.cons step pre,event,degreeAt,post⟩
    · exact .inr ⟨[],site,rest,v,middle,rfl,.nil _,step,by simpa [atomic] using atDegree,tail⟩

/-- If a source redex atom occurs in a final redex degree, the full pointed
run really fires an atomic residual carrying that degree somewhere. This
asserts event existence, without selecting the first or leftmost event. -/
theorem History.pointed_fires_initial_atom {body argument : LTerm}
    (history : History ps t u) (last : StepAt q u v) (initial : INIT t)
    (atHead : SourceSubterm [] .external t p env ctx (.app beta (.lam (Label.atom n) body) argument))
    (degree : u.degreeAt q=some l) (occurs : ¬l.Supported (fun m => m≠n)) :
    FiresAtom (ps++[q]) t v n := by
  rcases history.barsSafe_or_fires_atom (.nil t) initial atHead (initial.barsSafe _) with safe | fired
  · obtain ⟨appId,lamId,route⟩ := (history.generated_source_routes initial).degree_route degree
    obtain ⟨b,atLambda⟩ := LTerm.degreeAt_lambda degree
    have bars := (LTerm.barsSafe_iff _ u).mp safe l (LTerm.label_mem_of_subterm atLambda)
    rcases route.initial_atom_exposure atHead initial bars with supported | atomic
    · exact False.elim (occurs supported)
    · exact ⟨ps,q,[],u,v,rfl,history,last,by simpa [atomic] using degree,.nil _⟩
  · obtain ⟨before,site,after,x,y,paths,pre,event,atDegree,post⟩ := fired
    exact ⟨before,site,after++[q],x,y,by simp [paths,List.append_assoc],pre,event,atDegree,
      post.append (.cons last (.nil _))⟩
/-- The event supplied above contracts an actual old residual of the
specified initial redex, not merely an unrelated equal labelled node. -/
theorem FiresAtom.initial_residual (fired : FiresAtom ps t u n) (initial : INIT t)
    (r : RedexOcc t.erase) (initialDegree : t.degreeAt r.val=some (Label.atom n)) :
    ∃ before site after v w,ps=before++site::after ∧
      ∃ pre : History before t v,∃ event : StepAt site v w,History after w u ∧
      (⟨before,pre.betaHistory⟩ : Derivation t.erase v.erase).Residual
        r ⟨site,event.betaAt.redex⟩ := by
  obtain ⟨before,site,after,v,w,paths,pre,event,degree,post⟩ := fired
  exact ⟨before,site,after,v,w,paths,pre,event,post,
    (pre.initial_degree_residual_iff initial r ⟨site,event.betaAt.redex⟩).mp
      (initialDegree.trans degree.symm)⟩
end Lamping.Lambda.Labelled

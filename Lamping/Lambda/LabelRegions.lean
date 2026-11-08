import Lamping.Lambda.LabelEdgeSubstitution
import Lamping.Lambda.DegreeFamily
namespace Lamping.Lambda.Labelled

/-- Every oriented edge of this word lies in the specified original region. -/
def EdgeWord.Within (region : Nat → Prop) (p : EdgeWord) : Prop :=
  ∀ e∈p, region e.atom

theorem EdgeWord.within_append (region) (p q : EdgeWord) :
    Within region (p++q) ↔ Within region p ∧ Within region q := by
  simp [Within,List.mem_append,or_imp,forall_and]

theorem EdgeWord.within_reverse (region) (p : EdgeWord) :
    Within region (EdgeWord.reverse p) ↔ Within region p := by
  simp [Within,EdgeWord.reverse,OrientedAtom.flip]

mutual
  theorem Label.supported_iff_within (region) : ∀ l : Label,
      l.Supported region ↔ EdgeWord.Within region l.edgeWord
    | .single a => Letter.supported_iff_within region a
    | .cons a l => by
        simp only [Label.Supported,Label.edgeWord,EdgeWord.within_append,
          Letter.supported_iff_within,Label.supported_iff_within]
  theorem Letter.supported_iff_within (region) : ∀ a : Letter,
      a.Supported region ↔ EdgeWord.Within region a.edgeWord
    | .atom n => by simp [Letter.Supported,Letter.edgeWord,EdgeWord.Within]
    | .over l => Label.supported_iff_within region l
    | .under l => by
        simpa only [Letter.Supported,Letter.edgeWord,EdgeWord.within_reverse] using
          Label.supported_iff_within region l
end

/-- A region is the actual edge identities of a source subtree. Bound-variable
edges retain their original binder ports even when that binder is outside. -/
def SourceRegion (subtree : LTerm) : Nat → Prop :=
  fun n => Label.atom n∈subtree.labels

theorem SourceRegion.edges (subtree : LTerm) (env ctx) (n : Nat) :
    SourceRegion subtree n ↔ ∃ e∈sourceEdges env ctx subtree, e.atom=Label.atom n := by
  rw [SourceRegion,←sourceEdges_atoms subtree env ctx,List.mem_map]

theorem LTerm.subterm_append (t : LTerm) (p q : Path) :
    t.subterm (p++q)=(t.subterm p).bind (fun u => u.subterm q) := by
  induction p generalizing t with
  | nil => simp [LTerm.subterm]
  | cons s p ih => cases t <;> cases s <;> simp [LTerm.subterm,ih]

theorem LTerm.label_mem_located (t : LTerm) (member : l∈t.labels) :
    ∃ p u, t.subterm p=some u ∧ u.label=l := by
  induction t with
  | var a i =>
    have eq : l=a := by simpa [LTerm.labels] using member
    exact ⟨[],.var a i,rfl,eq.symm⟩
  | lam a b ih =>
    simp only [LTerm.labels,List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨[],.lam l b,rfl,rfl⟩
    · obtain ⟨p,u,hp,eq⟩ := ih member
      exact ⟨.body::p,u,hp,eq⟩
  | app a f arg hf ha =>
    simp only [LTerm.labels,List.mem_cons,List.mem_append] at member
    rcases member with rfl | member | member
    · exact ⟨[],.app l f arg,rfl,rfl⟩
    · obtain ⟨p,u,hp,eq⟩ := hf member
      exact ⟨.fn::p,u,hp,eq⟩
    · obtain ⟨p,u,hp,eq⟩ := ha member
      exact ⟨.arg::p,u,hp,eq⟩

/-- In an INIT source, region membership identifies the actual occurrence,
not merely an equal label in another copy. -/
theorem LTerm.initial_region_locates (t : LTerm) (hi : INIT t)
    (atSite : t.subterm site=some subtree) (atPoint : t.subterm p=some u)
    (member : u.label∈subtree.labels) : ∃ suffix, p=site++suffix := by
  obtain ⟨suffix,v,hv,eq⟩ := subtree.label_mem_located member
  have located : t.subterm (site++suffix)=some v := by
    rw [LTerm.subterm_append,atSite]
    exact hv
  exact ⟨suffix,LTerm.subterm_label_injective t hi.2 atPoint located eq.symm⟩

theorem LTerm.labels_subset_of_subterm {t subtree : LTerm} (atSite : t.subterm site=some subtree) :
    ∀ l∈subtree.labels, l∈t.labels := by
  intro l member
  obtain ⟨p,u,hp,eq⟩ := subtree.label_mem_located member
  have located : t.subterm (site++p)=some u := by
    rw [LTerm.subterm_append,atSite]
    exact hp
  rw [←eq]
  exact LTerm.label_mem_of_subterm located

theorem LTerm.atomic_region_support {t : LTerm} (atomic : ∀ l∈t.labels,IsAtomic l) :
    t.Supported (SourceRegion t) := by
  rw [LTerm.supported_iff]
  intro l member
  obtain ⟨n,rfl⟩ := atomic l member
  exact member

/-- Real reduction inside an original subtree keeps every edge of every
resulting degree in that subtree, including under-bars and copied binders. -/
theorem History.local_region_degree (history : History ps subtree v)
    (initial : INIT t) (atSite : t.subterm site=some subtree)
    (degree : v.degreeAt p=some l) : EdgeWord.Within (SourceRegion subtree) l.edgeWord := by
  have source : subtree.Supported (SourceRegion subtree) :=
    LTerm.atomic_region_support (fun a member => initial.1 a
      (LTerm.labels_subset_of_subterm atSite a member))
  obtain ⟨b,atLambda⟩ := LTerm.degreeAt_lambda degree
  have labelMember : l∈v.labels := LTerm.label_mem_of_subterm atLambda
  have supported := (LTerm.supported_iff _ _).mp (history.supported source) l labelMember
  exact (Label.supported_iff_within _ _).mp supported

theorem StepAt.subterm_internal (site : Path) (step : StepAt (site++suffix) t u)
    (atSite : t.subterm site=some subtree) :
    ∃ result, u.subterm site=some result ∧ StepAt suffix subtree result := by
  induction site generalizing t u subtree with
  | nil =>
    simp only [LTerm.subterm,Option.some.injEq] at atSite
    cases atSite
    exact ⟨u,by simp [LTerm.subterm],step⟩
  | cons s site ih =>
    cases s with
    | fn =>
      cases step with
      | fn child => exact ih child atSite
    | arg =>
      cases step with
      | arg child => exact ih child atSite
    | body =>
      cases step with
      | body child => exact ih child atSite

/-- Restriction of an actual global schedule to a fixed internal subtree.
Every local contraction is still a real StepAt; paths are stripped literally. -/
theorem History.subterm_internal (history : History ps t u)
    (atSite : t.subterm site=some subtree)
    (inside : ∀ p∈ps,∃ suffix,p=site++suffix) :
    ∃ result, u.subterm site=some result ∧
      History (ps.map (List.drop site.length)) subtree result := by
  induction history generalizing subtree with
  | nil t => exact ⟨subtree,atSite,.nil _⟩
  | @cons p t middle ps u head tail ih =>
    obtain ⟨suffix,eq⟩ := inside p List.mem_cons_self
    cases eq
    obtain ⟨middleSub,atMiddle,localStep⟩ := head.subterm_internal site atSite
    obtain ⟨result,atResult,localTail⟩ := ih atMiddle (fun q member => inside q (List.mem_cons_of_mem _ member))
    refine ⟨result,atResult,?_⟩
    simpa only [List.map_cons,List.drop_left] using History.cons localStep localTail

/-- The forward regional implication consumes the entire actual internal
global history, with its final degree measured in the same global labelling. -/
theorem History.internal_region_degree (history : History ps t u) (initial : INIT t)
    (atSite : t.subterm site=some subtree)
    (inside : ∀ p∈ps,∃ suffix,p=site++suffix)
    (degree : u.degreeAt (site++suffix)=some l) :
    EdgeWord.Within (SourceRegion subtree) l.edgeWord := by
  obtain ⟨result,atResult,localHistory⟩ := history.subterm_internal atSite inside
  have localDegree : result.degreeAt suffix=some l := by
    simpa only [LTerm.degreeAt,LTerm.subterm_append,atResult,Option.bind_some] using degree
  exact localHistory.local_region_degree initial atSite localDegree

theorem Label.Supported.lastAtom {l : Label} (support : l.Supported region)
    (last : l.lastAtom=some n) : region n := by
  cases l with
  | single a => cases a <;> simp [Label.lastAtom] at last; cases last; exact support
  | cons a l => exact Label.Supported.lastAtom support.2 last
termination_by l

theorem SourceRoute.region_lam_origin
    (route : SourceRoute (sourceEdges env ctx t) start l (.lamContext origin))
    (inside : EdgeWord.Within (SourceRegion subtree) l.edgeWord) :
    origin∈subtree.labels := by
  obtain ⟨n,last,eq⟩ := route.lam_last_atom
  rw [eq]
  exact Label.Supported.lastAtom ((Label.supported_iff_within _ _).mpr inside) last

/-- A lambda principal endpoint in the original syntax graph is an actual
lambda occurrence, not a variable edge returning to an equally named binder. -/
theorem sourceEdges_lam_occurrence (t : LTerm)
    (member : e∈sourceEdges env ctx t) (target : e.toPort=.lamContext origin) :
    ∃ p body,t.subterm p=some (.lam origin body) := by
  induction t generalizing env ctx with
  | var a i =>
    simp only [sourceEdges,List.mem_singleton] at member
    cases member
    exfalso
    induction env generalizing i with
    | nil => simp [sourceBinder] at target
    | cons a env ih =>
      cases i with
      | zero => simp [sourceBinder] at target
      | succ i => exact ih i (by simpa only [sourceBinder_succ] using target)
  | lam a b ih =>
    simp only [sourceEdges,List.mem_cons] at member
    rcases member with rfl | member
    · have eq := SourcePort.lamContext.inj target
      cases eq
      exact ⟨[],b,by simp [LTerm.subterm]⟩
    · obtain ⟨p,body,atBody⟩ := ih member
      exact ⟨.body::p,body,atBody⟩
  | app a f arg hf ha =>
    simp only [sourceEdges,List.mem_cons,List.mem_append] at member
    rcases member with rfl | member | member
    · cases target
    · obtain ⟨p,body,atFn⟩ := hf member
      exact ⟨.fn::p,body,atFn⟩
    · obtain ⟨p,body,atArg⟩ := ha member
      exact ⟨.arg::p,body,atArg⟩

/-- A region-supported generated degree locates its original lambda node
inside that region. This alone does not choose among later copies of the node. -/
theorem SourceRoute.region_lam_occurrence
    (route : SourceRoute (sourceEdges env ctx t) start l (.lamContext origin))
    (initial : INIT t) (atSite : t.subterm site=some subtree)
    (inside : EdgeWord.Within (SourceRegion subtree) l.edgeWord) :
    ∃ suffix body,t.subterm (site++suffix)=some (.lam origin body) := by
  obtain ⟨n,e,last,member,atomic,target⟩ := route.last_atom
  obtain ⟨p,body,atLambda⟩ := sourceEdges_lam_occurrence t member target
  obtain ⟨suffix,eq⟩ := LTerm.initial_region_locates t initial atSite atLambda
    (route.region_lam_origin inside)
  exact ⟨suffix,body,eq ▸ atLambda⟩

theorem TermRoutes.degree_route (routes : TermRoutes edges env ctx t)
    (degree : t.degreeAt p=some l) :
    ∃ appId lamId,SourceRoute edges (.appFn appId) l (.lamContext lamId) := by
  induction p generalizing t env ctx with
  | nil =>
    cases routes with
    | var => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
    | lam => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
    | app root fn arg =>
      cases fn with
      | var => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | app => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | lam route body =>
        simp only [LTerm.degreeAt,LTerm.subterm,Option.bind_some,LTerm.degree,Option.some.injEq] at degree
        cases degree
        exact ⟨_,_,route⟩
  | cons s p ih =>
    cases routes with
    | var => cases s <;> simp [LTerm.degreeAt,LTerm.subterm] at degree
    | lam route body =>
      cases s with
      | fn => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | arg => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | body => exact ih body degree
    | app route fn arg =>
      cases s with
      | body => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | fn => exact ih fn degree
      | arg => exact ih arg degree

/-- Actual generated history plus degree support identifies an original
lambda occurrence in the specified subtree, while leaving copy selection open. -/
theorem History.region_original_lambda (history : History ps t u) (initial : INIT t)
    (atSite : t.subterm site=some subtree) (degree : u.degreeAt p=some l)
    (inside : EdgeWord.Within (SourceRegion subtree) l.edgeWord) :
    ∃ appId lamId suffix body,
      SourceRoute (sourceEdges [] .external t) (.appFn appId) l (.lamContext lamId) ∧
      t.subterm (site++suffix)=some (.lam lamId body) := by
  obtain ⟨appId,lamId,route⟩ := (history.generated_source_routes initial).degree_route degree
  obtain ⟨suffix,body,atLambda⟩ := route.region_lam_occurrence initial atSite inside
  exact ⟨appId,lamId,suffix,body,route,atLambda⟩

/-- Lookup with the actual original binder environment and root port. -/
inductive SourceSubterm : List Label → SourcePort → LTerm → Path → List Label → SourcePort → LTerm → Prop where
  | nil : SourceSubterm env ctx t [] env ctx t
  | fn : SourceSubterm env (.appFn l) f p innerEnv innerCtx sub →
      SourceSubterm env ctx (.app l f a) (.fn::p) innerEnv innerCtx sub
  | arg : SourceSubterm env (.appArg l) a p innerEnv innerCtx sub →
      SourceSubterm env ctx (.app l f a) (.arg::p) innerEnv innerCtx sub
  | body : SourceSubterm (l::env) (.lamBody l) b p innerEnv innerCtx sub →
      SourceSubterm env ctx (.lam l b) (.body::p) innerEnv innerCtx sub

theorem SourceSubterm.lookup (atSite : SourceSubterm env ctx t p innerEnv innerCtx sub) :
    t.subterm p=some sub := by
  induction atSite with
  | nil => simp [LTerm.subterm]
  | fn _ ih => exact ih
  | arg _ ih => exact ih
  | body _ ih => exact ih

theorem SourceSubterm.of_lookup (t : LTerm) (atSite : t.subterm p=some sub) (env ctx) :
    ∃ innerEnv innerCtx,SourceSubterm env ctx t p innerEnv innerCtx sub := by
  induction p generalizing t env ctx with
  | nil =>
    simp only [LTerm.subterm,Option.some.injEq] at atSite
    cases atSite
    exact ⟨env,ctx,.nil⟩
  | cons s p ih =>
    cases t with
    | var => cases s <;> simp [LTerm.subterm] at atSite
    | lam l b =>
      cases s with
      | fn => simp [LTerm.subterm] at atSite
      | arg => simp [LTerm.subterm] at atSite
      | body =>
        obtain ⟨env',ctx',path⟩ := ih b atSite (l::env) (.lamBody l)
        exact ⟨env',ctx',.body path⟩
    | app l f a =>
      cases s with
      | body => simp [LTerm.subterm] at atSite
      | fn =>
        obtain ⟨env',ctx',path⟩ := ih f atSite env (.appFn l)
        exact ⟨env',ctx',.fn path⟩
      | arg =>
        obtain ⟨env',ctx',path⟩ := ih a atSite env (.appArg l)
        exact ⟨env',ctx',.arg path⟩

theorem SourceSubterm.edges_subset (atSite : SourceSubterm env ctx t p innerEnv innerCtx sub) :
    ∀ e∈sourceEdges innerEnv innerCtx sub,e∈sourceEdges env ctx t := by
  induction atSite with
  | nil => exact fun _ h => h
  | fn _ ih => exact fun e h => List.mem_cons_of_mem _ (List.mem_append_left _ (ih e h))
  | arg _ ih => exact fun e h => List.mem_cons_of_mem _ (List.mem_append_right _ (ih e h))
  | body _ ih => exact fun e h => List.mem_cons_of_mem _ (ih e h)

theorem sourceEdges_from_appFn (t : LTerm) (member : e∈sourceEdges env ctx t)
    (start : e.fromPort=.appFn origin) : ctx=.appFn origin ∨ origin∈t.labels := by
  induction t generalizing env ctx with
  | var l i =>
    simp only [sourceEdges,List.mem_singleton] at member
    cases member
    exact .inl start
  | lam l b ih =>
    simp only [sourceEdges,List.mem_cons] at member
    rcases member with rfl | member
    · exact .inl start
    · rcases ih member with wrong | inside
      · cases wrong
      · exact .inr (List.mem_cons_of_mem _ inside)
  | app l f a hf ha =>
    simp only [sourceEdges,List.mem_cons,List.mem_append] at member
    rcases member with rfl | member | member
    · exact .inl start
    · rcases hf member with boundary | inside
      · have eq := SourcePort.appFn.inj boundary
        exact .inr (by simp [LTerm.labels,eq])
      · exact .inr (List.mem_cons_of_mem _ (List.mem_append_left _ inside))
    · rcases ha member with wrong | inside
      · cases wrong
      · exact .inr (List.mem_cons_of_mem _ (List.mem_append_right _ inside))

theorem Label.Supported.firstAtom {l : Label} (support : l.Supported region)
    (first : l.firstAtom=some n) : region n := by
  cases l with
  | single a => cases a <;> simp [Label.firstAtom] at first; cases first; exact support
  | cons a l => cases a <;> simp [Label.firstAtom] at first; cases first; exact support.1

/-- An argument region's context port cannot masquerade as a function port.
Thus a supported redex route also locates its original application node. -/
theorem SourceRoute.argument_region_app_origin
    (route : SourceRoute (sourceEdges env ctx t) (.appFn origin) l finish)
    (initial : INIT t)
    (atSite : SourceSubterm env ctx t site innerEnv (.appArg parent) subtree)
    (inside : EdgeWord.Within (SourceRegion subtree) l.edgeWord) :
    origin∈subtree.labels := by
  obtain ⟨n,e,first,member,atomic,start⟩ := route.first_atom
  have inRegion : SourceRegion subtree n :=
    Label.Supported.firstAtom ((Label.supported_iff_within _ _).mpr inside) first
  obtain ⟨edge,regionMember,regionAtomic⟩ := (SourceRegion.edges subtree innerEnv (.appArg parent) n).mp inRegion
  have equal := sourceEdges_unique initial member (atSite.edges_subset edge regionMember)
    (atomic.trans regionAtomic.symm)
  have regionStart : edge.fromPort=.appFn origin := equal ▸ start
  rcases sourceEdges_from_appFn subtree regionMember regionStart with wrong | located
  · cases wrong
  · exact located

theorem History.argument_region_origins (history : History ps t u) (initial : INIT t)
    (atSite : SourceSubterm [] .external t site innerEnv (.appArg parent) subtree)
    (degree : u.degreeAt p=some l)
    (inside : EdgeWord.Within (SourceRegion subtree) l.edgeWord) :
    ∃ appId lamId suffix body,
      SourceRoute (sourceEdges [] .external t) (.appFn appId) l (.lamContext lamId) ∧
      appId∈subtree.labels ∧ t.subterm (site++suffix)=some (.lam lamId body) := by
  obtain ⟨appId,lamId,route⟩ := (history.generated_source_routes initial).degree_route degree
  have appRegion := route.argument_region_app_origin initial atSite inside
  obtain ⟨suffix,body,atLambda⟩ := route.region_lam_occurrence initial atSite.lookup inside
  exact ⟨appId,lamId,suffix,body,route,appRegion,atLambda⟩

theorem sourceEdges_fn_occurrence (t : LTerm)
    (member : e∈sourceEdges env ctx t) (start : e.fromPort=.appFn origin) :
    ctx=.appFn origin ∨ ∃ p f a,t.subterm p=some (.app origin f a) := by
  induction t generalizing env ctx with
  | var l i =>
    simp only [sourceEdges,List.mem_singleton] at member
    cases member
    exact .inl start
  | lam l b ih =>
    simp only [sourceEdges,List.mem_cons] at member
    rcases member with rfl | member
    · exact .inl start
    · rcases ih member with wrong | ⟨p,f,a,atBody⟩
      · cases wrong
      · exact .inr ⟨.body::p,f,a,atBody⟩
  | app l f a hf ha =>
    simp only [sourceEdges,List.mem_cons,List.mem_append] at member
    rcases member with rfl | member | member
    · exact .inl start
    · rcases hf member with boundary | ⟨p,f',a',atFn⟩
      · have eq := SourcePort.appFn.inj boundary
        cases eq
        exact .inr ⟨[],f,a,by simp [LTerm.subterm]⟩
      · exact .inr ⟨.fn::p,f',a',atFn⟩
    · rcases ha member with wrong | ⟨p,f',a',atArg⟩
      · cases wrong
      · exact .inr ⟨.arg::p,f',a',atArg⟩

/-- Both endpoints of a region-supported redex degree identify actual original
application/lambda occurrences within that argument subtree. -/
theorem History.argument_region_node_occurrences (history : History ps t u) (initial : INIT t)
    (atSite : SourceSubterm [] .external t site innerEnv (.appArg parent) subtree)
    (degree : u.degreeAt p=some l)
    (inside : EdgeWord.Within (SourceRegion subtree) l.edgeWord) :
    ∃ appId lamId appSuffix lamSuffix f a body,
      SourceRoute (sourceEdges [] .external t) (.appFn appId) l (.lamContext lamId) ∧
      t.subterm (site++appSuffix)=some (.app appId f a) ∧
      t.subterm (site++lamSuffix)=some (.lam lamId body) := by
  obtain ⟨appId,lamId,lamSuffix,body,route,appRegion,atLambda⟩ :=
    history.argument_region_origins initial atSite degree inside
  obtain ⟨n,e,first,member,atomic,start⟩ := route.first_atom
  rcases sourceEdges_fn_occurrence t member start with wrong | ⟨appPath,f,a,atApp⟩
  · cases wrong
  · obtain ⟨appSuffix,eq⟩ := LTerm.initial_region_locates t initial atSite.lookup atApp appRegion
    exact ⟨appId,lamId,appSuffix,lamSuffix,f,a,body,route,eq ▸ atApp,atLambda⟩

/-- A function child inside an argument subtree has its application inside
that subtree as well. The different final direction excludes the boundary. -/
theorem Path.fn_inside_argument {p q suffix : Path}
    (eq : p++[.fn]=(q++[.arg])++suffix) : ∃ rest,p=(q++[.arg])++rest := by
  induction q generalizing p with
  | nil =>
    cases p with
    | nil => have wrong := (List.cons.inj eq).1; cases wrong
    | cons s p =>
      have first := (List.cons.inj eq).1
      cases first
      exact ⟨p,rfl⟩
  | cons s q ih =>
    cases p with
    | nil =>
      have lengths := congrArg List.length eq
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    | cons r p =>
      have heads := (List.cons.inj eq).1
      have tails := (List.cons.inj eq).2
      cases heads
      obtain ⟨rest,inside⟩ := ih tails
      exact ⟨rest,congrArg (s::·) inside⟩

/-- In the initial term, a degree supported by a redex-argument region forces
the actual redex application occurrence to lie inside that argument. -/
theorem LTerm.initial_argument_degree_internal (t : LTerm) (initial : INIT t)
    (atSite : t.subterm (q++[.arg])=some subtree)
    (degree : t.degreeAt p=some l)
    (inside : EdgeWord.Within (SourceRegion subtree) l.edgeWord) :
    ∃ rest,p=(q++[.arg])++rest := by
  obtain ⟨body,atLambda⟩ := LTerm.degreeAt_lambda degree
  have atomic := initial.1 l (LTerm.label_mem_of_subterm atLambda)
  obtain ⟨n,eq⟩ := atomic
  have member : l∈subtree.labels := by
    rw [eq]
    have supported := (Label.supported_iff_within _ _).mpr inside
    rw [eq] at supported
    exact supported
  obtain ⟨suffix,position⟩ := LTerm.initial_region_locates t initial atSite atLambda member
  exact Path.fn_inside_argument position
end Lamping.Lambda.Labelled

import Lamping.Lamping.MatchingRouteSyntaxWalk
namespace Lamping.Lambda.Labelled
/-- Bars denote the same fixed physical beta route. Their payload is kept
in the label syntax and validated by SelectedDegree, not flattened here. -/
def Letter.sourceWord {X : Type} (atoms : Nat → List X) (overWord underWord : List X) : Letter → List X
  | .atom n => atoms n
  | .over _ => overWord
  | .under _ => underWord

def Label.sourceWord {X : Type} (atoms : Nat → List X) (overWord underWord : List X) : Label → List X
  | .single letter => letter.sourceWord atoms overWord underWord
  | .cons letter rest => letter.sourceWord atoms overWord underWord++rest.sourceWord atoms overWord underWord

theorem Label.sourceWord_concat {X : Type} (atoms : Nat → List X) (overWord underWord : List X) :
    ∀ (a b : Label),(a.concat b).sourceWord atoms overWord underWord=
      a.sourceWord atoms overWord underWord++b.sourceWord atoms overWord underWord
  | .single _,_ => rfl
  | .cons _ rest,_ => by simp only [Label.concat,Label.sourceWord,sourceWord_concat,List.append_assoc]
namespace LTerm
/-- One partial evaluator for every current syntax position, using the SAME
atom selector and fixed principal words throughout. Invalid positions are
None; [] is never substituted for an invalid lookup. -/
def sourceTrail {X : Type} (atoms : Nat → List X) (overWord underWord : List X) : LTerm → Path → Option (List X)
  | t,[] => some (t.label.sourceWord atoms overWord underWord)
  | .app stamp fn _,.fn::p => (sourceTrail atoms overWord underWord fn p).map (fun word => stamp.sourceWord atoms overWord underWord++word)
  | .app stamp _ arg,.arg::p => (sourceTrail atoms overWord underWord arg p).map (fun word => stamp.sourceWord atoms overWord underWord++word)
  | .lam stamp body,.body::p => (sourceTrail atoms overWord underWord body p).map (fun word => stamp.sourceWord atoms overWord underWord++word)
  | _,_ => none
/-- The identical evaluation with the terminal node's own edge omitted. -/
def sourceStem {X : Type} (atoms : Nat → List X) (overWord underWord : List X) : LTerm → Path → Option (List X)
  | _,[] => some []
  | .app stamp fn _,.fn::p => (sourceStem atoms overWord underWord fn p).map (fun word => stamp.sourceWord atoms overWord underWord++word)
  | .app stamp _ arg,.arg::p => (sourceStem atoms overWord underWord arg p).map (fun word => stamp.sourceWord atoms overWord underWord++word)
  | .lam stamp body,.body::p => (sourceStem atoms overWord underWord body p).map (fun word => stamp.sourceWord atoms overWord underWord++word)
  | _,_ => none

theorem sourceTrail_prepend {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (prefixLabel : Label) (t : LTerm) (p : Path) :
    (t.prepend prefixLabel).sourceTrail atoms overWord underWord p=
      (t.sourceTrail atoms overWord underWord p).map (fun word => prefixLabel.sourceWord atoms overWord underWord++word) := by
  cases p with
  | nil => cases t <;> simp only [prepend,sourceTrail,label,Label.sourceWord_concat,Option.map_some]
  | cons step rest =>
    cases t <;> cases step <;>
      simp only [prepend,sourceTrail,Label.sourceWord_concat,Option.map_none,Option.map_map,Function.comp_def,List.append_assoc]

theorem sourceTrail_rename {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (rho : Nat → Nat) (t : LTerm) (p : Path) :
    (t.rename rho).sourceTrail atoms overWord underWord p=t.sourceTrail atoms overWord underWord p := by
  induction p generalizing rho t with
  | nil => cases t <;> rfl
  | cons step rest ih => cases t <;> cases step <;> simp only [rename,sourceTrail,ih]

/-- Literal shared-prefix equation, with the actual subterm and the SAME
selector on both sides. No RootAccess or generatedness is inferred. -/
theorem sourceTrail_split {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {t sub : LTerm} {p : Path} (lookup : t.subterm p=some sub) (q : Path) :
    t.sourceTrail atoms overWord underWord (p++q)=
      (t.sourceStem atoms overWord underWord p).bind
        (fun stem => (sub.sourceTrail atoms overWord underWord q).map (fun word => stem++word)) := by
  induction p generalizing t with
  | nil =>
    cases t <;> simp only [subterm,Option.some.injEq] at lookup <;> cases lookup <;>
      simp only [List.nil_append,sourceStem,Option.bind_some,List.nil_append,Option.map_id_fun',id_eq]
  | cons step rest ih =>
    cases t with
    | var => cases step <;> simp [subterm] at lookup
    | app stamp fn arg =>
      cases step with
      | body => simp [subterm] at lookup
      | fn =>
        simp only [List.cons_append,sourceTrail,sourceStem,ih lookup]
        cases sourceStem atoms overWord underWord fn rest <;>
          cases sub.sourceTrail atoms overWord underWord q <;> simp [List.append_assoc]
      | arg =>
        simp only [List.cons_append,sourceTrail,sourceStem,ih lookup]
        cases sourceStem atoms overWord underWord arg rest <;>
          cases sub.sourceTrail atoms overWord underWord q <;> simp [List.append_assoc]
    | lam stamp body =>
      cases step with
      | fn | arg => simp [subterm] at lookup
      | body =>
        simp only [List.cons_append,sourceTrail,sourceStem,ih lookup]
        cases sourceStem atoms overWord underWord body rest <;>
          cases sub.sourceTrail atoms overWord underWord q <;> simp [List.append_assoc]
/-- Exact literal replacement equation, including arbitrary capture depth. -/
theorem sourceTrail_subst_copy {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {body replacement : LTerm} {q : Path} {n : Nat} {sigma : Nat → SubValue}
    (lookup : subtermAt body.erase q=some (.var (n+binderDepth q)))
    (put : sigma n=.put replacement) (r : Path) :
    (body.subst sigma).sourceTrail atoms overWord underWord (q++r)=
      (body.sourceTrail atoms overWord underWord q).bind (fun bodyWord =>
        (replacement.sourceTrail atoms overWord underWord r).map (fun argWord => bodyWord++argWord)) := by
  induction q generalizing body replacement n sigma with
  | nil =>
    cases body with
    | app => simp [erase,subtermAt] at lookup
    | lam => simp [erase,subtermAt] at lookup
    | var stamp k =>
      have eq : k=n := by simpa [erase,subtermAt,binderDepth] using lookup
      subst k
      simp only [List.nil_append,subst,put,sourceTrail_prepend,sourceTrail,label,Option.bind_some]
  | cons step rest ih =>
    cases body with
    | var => cases step <;> simp [erase,subtermAt] at lookup
    | app stamp fn arg =>
      cases step with
      | body => simp [erase,subtermAt] at lookup
      | fn =>
        simp only [List.cons_append,subst,sourceTrail,ih lookup put]
        cases fn.sourceTrail atoms overWord underWord rest <;>
          cases replacement.sourceTrail atoms overWord underWord r <;> simp [List.append_assoc]
      | arg =>
        simp only [List.cons_append,subst,sourceTrail,ih lookup put]
        cases arg.sourceTrail atoms overWord underWord rest <;>
          cases replacement.sourceTrail atoms overWord underWord r <;> simp [List.append_assoc]
    | lam stamp innerBody =>
      cases step with
      | fn | arg => simp [erase,subtermAt] at lookup
      | body =>
        have atInner := lookup
        simp only [erase,subtermAt,binderDepth] at atInner
        rw [← Nat.add_assoc, Nat.add_right_comm n (binderDepth rest) 1] at atInner
        have lifted : lift sigma (n+1)=.put (replacement.rename Nat.succ) := by { simp only [lift,put] }
        simp only [List.cons_append,subst,sourceTrail,ih atInner lifted,sourceTrail_rename]
        cases innerBody.sourceTrail atoms overWord underWord rest <;>
          cases replacement.sourceTrail atoms overWord underWord r <;> simp [List.append_assoc]

/-- A true argument occurrence evaluates to the same old body prefix and
argument word, with precisely the fixed forward/backward principal words. -/
theorem sourceTrail_contract_copy {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (beta alpha : Label) {body argument : LTerm} {q : Path}
    (occurs : ArgumentOccurrence body.erase q) (r : Path) :
    (contract beta alpha body argument).sourceTrail atoms overWord underWord (q++r)=
      (body.sourceTrail atoms overWord underWord q).bind (fun bodyWord =>
        (argument.sourceTrail atoms overWord underWord r).map (fun argWord =>
          beta.sourceWord atoms overWord underWord++overWord++bodyWord++underWord++argWord)) := by
  have lookup : subtermAt body.erase q=some (.var (0+binderDepth q)) := by
    simpa only [ArgumentOccurrence,Nat.zero_add] using occurs
  rw [contract,sourceTrail_prepend,sourceTrail_subst_copy atoms overWord underWord lookup (show single (prepend alpha.under argument) 0=.put (prepend alpha.under argument) from rfl)]
  simp only [sourceTrail_prepend,Label.sourceWord_concat,Label.over,Label.under,Label.sourceWord,Letter.sourceWord]
  cases body.sourceTrail atoms overWord underWord q <;>
    cases argument.sourceTrail atoms overWord underWord r <;> simp [List.append_assoc]
/-- Substitution leaves every root edge on a retained nonvariable path intact. -/
theorem sourceTrail_subst_nonvariable {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {body old : LTerm} {p : Path} (lookup : body.subterm p=some old)
    (nonvariable : ∀ stamp k,old≠.var stamp k) (sigma : Nat → SubValue) :
    (body.subst sigma).sourceTrail atoms overWord underWord p=
      body.sourceTrail atoms overWord underWord p := by
  induction p generalizing body sigma with
  | nil =>
    cases body with
    | var stamp k => exact False.elim (nonvariable stamp k (Option.some.inj lookup).symm)
    | app => rfl
    | lam => rfl
  | cons step rest ih =>
    cases body with
    | var => cases step <;> simp [subterm] at lookup
    | app stamp fn arg =>
      cases step with
      | body => simp [subterm] at lookup
      | fn | arg => simp only [subst,sourceTrail,ih lookup]
    | lam stamp innerBody =>
      cases step with
      | fn | arg => simp [subterm] at lookup
      | body => simp only [subst,sourceTrail,ih lookup]

theorem sourceTrail_contract_nonvariable {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (beta alpha : Label) {body old : LTerm} {p : Path}
    (lookup : body.subterm p=some old) (nonvariable : ∀ stamp k,old≠.var stamp k) (argument : LTerm) :
    (contract beta alpha body argument).sourceTrail atoms overWord underWord p=
      (body.sourceTrail atoms overWord underWord p).map (fun word =>
        beta.sourceWord atoms overWord underWord++overWord++word) := by
  simp only [contract,sourceTrail_prepend,sourceTrail_subst_nonvariable atoms overWord underWord lookup nonvariable,
    Label.sourceWord_concat,Label.over,Label.sourceWord,Letter.sourceWord]

/-- Actual lookup supplies Some. The evaluator never manufactures a path for
an invalid position. -/
theorem sourceTrail_exists {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {t sub : LTerm} {p : Path} (lookup : t.subterm p=some sub) :
    ∃ word,t.sourceTrail atoms overWord underWord p=some word := by
  induction p generalizing t with
  | nil => exact ⟨t.label.sourceWord atoms overWord underWord,by cases t <;> rfl⟩
  | cons step rest ih =>
    cases t with
    | var => cases step <;> simp [subterm] at lookup
    | app stamp fn arg =>
      cases step with
      | body => simp [subterm] at lookup
      | fn => rcases ih lookup with ⟨word,eq⟩; exact ⟨stamp.sourceWord atoms overWord underWord++word,by simp only [sourceTrail,eq,Option.map_some]⟩
      | arg => rcases ih lookup with ⟨word,eq⟩; exact ⟨stamp.sourceWord atoms overWord underWord++word,by simp only [sourceTrail,eq,Option.map_some]⟩
    | lam stamp innerBody =>
      cases step with
      | fn | arg => simp [subterm] at lookup
      | body => rcases ih lookup with ⟨word,eq⟩; exact ⟨stamp.sourceWord atoms overWord underWord++word,by simp only [sourceTrail,eq,Option.map_some]⟩
/-- Along a retained variable path, every substitution action is genuinely
keep. The selected slot moves under binders; inner bound variables are kept too. -/
theorem sourceTrail_subst_outside {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {body : LTerm} {p : Path} {k n : Nat} {sigma : Nat → SubValue}
    (lookup : subtermAt body.erase p=some (.var k)) (outside : k≠n+binderDepth p)
    (kept : ∀ i,i≠n → ∃ j,sigma i=.keep j) :
    (body.subst sigma).sourceTrail atoms overWord underWord p=
      body.sourceTrail atoms overWord underWord p := by
  induction p generalizing body sigma n with
  | nil =>
    cases body with
    | app => simp [erase,subtermAt] at lookup
    | lam => simp [erase,subtermAt] at lookup
    | var stamp index =>
      have same : index=k := by simpa only [erase,subtermAt,Option.some.injEq,Term.var.injEq] using lookup
      subst index
      obtain ⟨j,keep⟩ := kept k (by simpa only [binderDepth,Nat.add_zero] using outside)
      simp only [subst,keep,sourceTrail,label]
  | cons step rest ih =>
    cases body with
    | var => cases step <;> simp [erase,subtermAt] at lookup
    | app stamp fn arg =>
      cases step with
      | body => simp [erase,subtermAt] at lookup
      | fn | arg => simp only [subst,sourceTrail,ih lookup outside kept]
    | lam stamp innerBody =>
      cases step with
      | fn | arg => simp [erase,subtermAt] at lookup
      | body =>
        have notSlot : k≠(n+1)+binderDepth rest := by { simpa only [binderDepth,Nat.add_assoc,Nat.add_comm 1] using outside }
        have keptLift : ∀ i,i≠n+1 → ∃ j,lift sigma i=.keep j := by {
          intro i notSelected
          cases i with
          | zero => exact ⟨0,rfl⟩
          | succ i =>
            have other : i≠n := by intro eq; exact notSelected (congrArg Nat.succ eq)
            obtain ⟨j,keep⟩ := kept i other
            exact ⟨j+1,by simp only [lift,keep]⟩ }
        simp only [subst,sourceTrail,ih lookup notSlot keptLift]

/-- The exact retained-variable branch for a real beta contractum. Unlike
the copied branch, no backward principal word or argument word is inserted. -/
theorem sourceTrail_contract_retained_variable {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (beta alpha : Label) {body : LTerm} {p : Path} {k : Nat}
    (lookup : subtermAt body.erase p=some (.var k)) (outside : k≠binderDepth p) (argument : LTerm) :
    (contract beta alpha body argument).sourceTrail atoms overWord underWord p=
      (body.sourceTrail atoms overWord underWord p).map (fun word =>
        beta.sourceWord atoms overWord underWord++overWord++word) := by
  have keep : ∀ i,i≠0 → ∃ j,single (prepend alpha.under argument) i=.keep j := by
    intro i nonzero
    cases i with
    | zero => exact False.elim (nonzero rfl)
    | succ i => exact ⟨i,rfl⟩
  simp only [contract,sourceTrail_prepend,
    sourceTrail_subst_outside atoms overWord underWord lookup (by simpa only [Nat.zero_add] using outside) keep,
    Label.sourceWord_concat,Label.over,Label.sourceWord,Letter.sourceWord]
end LTerm
end Lamping.Lambda.Labelled
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}
/-- One choice over the FINITE list of actual original edges. Every cell
contains a real fragment/occurrence/whole-assignment witness. -/
structure SourceEdgeSelection (original : LTerm) (g : Net signature N B W) (root : B) where
  chosen : (edge : {edge : SourceEdge // edge∈sourceEdges [] .external original}) →
    Sigma (fun p => SourceEdgeFragment original g root edge.val p)
/-- Construct the shared selector from actual source Matches and closed
syntax. No realization or map-correctness certificate is a caller input. -/
noncomputable def Matches.source_edge_selection
    (matching : Matches g root original.erase) (closed : Closed original.erase) : SourceEdgeSelection original g root where
  chosen := fun edge =>
    let existsFragment := matching.source_edge_member_fragment closed edge.property
    ⟨Classical.choose existsFragment,Classical.choice (Classical.choose_spec existsFragment)⟩
/-- Off-domain atom labels have no fragment. All legal route atoms are
proved to select their actual finite cell by atomWord_cell below. -/
noncomputable def SourceEdgeSelection.atomWord (selection : SourceEdgeSelection original g root) (n : Nat) : List (Endpoint g) := by
  classical
  exact if member : ∃ edge : {edge : SourceEdge // edge∈sourceEdges [] .external original},edge.val.atom=Labelled.Label.atom n
    then (selection.chosen (Classical.choose member)).2.segments else []

theorem SourceEdgeSelection.atomWord_cell (selection : SourceEdgeSelection original g root)
    (initial : INIT original) (edge : {edge : SourceEdge // edge∈sourceEdges [] .external original})
    (atomic : edge.val.atom=Labelled.Label.atom n) :
    selection.atomWord n=(selection.chosen edge).2.segments := by
  classical
  have member : ∃ e : {e : SourceEdge // e∈sourceEdges [] .external original},e.val.atom=Labelled.Label.atom n := ⟨edge,atomic⟩
  rw [SourceEdgeSelection.atomWord,dif_pos member]
  have same : Classical.choose member=edge := Subtype.ext
    (sourceEdges_unique initial (Classical.choose member).property edge.property
      ((Classical.choose_spec member).trans atomic.symm))
  rw [same]
noncomputable def SourceEdgeSelection.evalLabel (selection : SourceEdgeSelection original g root)
    (beta : BetaEdge g) (stamp : Labelled.Label) : List (Endpoint g) :=
  stamp.sourceWord selection.atomWord beta.principal beta.reverseRoute

theorem SourceEdgeSelection.evalLabel_concat (selection : SourceEdgeSelection original g root) (beta : BetaEdge g)
    (a b : Labelled.Label) : selection.evalLabel beta (a.concat b)=selection.evalLabel beta a++selection.evalLabel beta b :=
  Labelled.Label.sourceWord_concat _ _ _ a b

theorem SourceEdgeSelection.selected_route_walk (selection : SourceEdgeSelection original g root) {beta : BetaEdge g}
    (initial : INIT original) (matching : Matches g root original.erase)
    (allPorts : ∀ {degree appId lamId},allowed degree →
      SourceRoute (sourceEdges [] .external original) (.appFn appId) degree (.lamContext lamId) →
      degree=lamId ∧ BetaSourcePorts original root beta appId lamId)
    (route : SelectedSourceRoute (sourceEdges [] .external original) allowed start stamp finish) :
    ∃ walk : PhysicalSourceWalk original root beta start stamp finish,walk.edges=selection.evalLabel beta stamp := by
  induction route with
  | atom member atomic =>
    let cell : {edge : SourceEdge // edge∈sourceEdges [] .external original} := ⟨_,member⟩
    let fragment := (selection.chosen cell).2
    refine ⟨{
      edges := fragment.segments,fromEndpoint := fragment.fromEndpoint,toEndpoint := fragment.toEndpoint
      fromRealizes := fragment.fromRealizes,toRealizes := fragment.toRealizes
      head := fragment.start,last := fragment.finish,forward := fragment.forward.expanded,image := .atom fragment atomic },?_⟩
    exact (selection.atomWord_cell initial cell atomic).symm
  | over left selected middle right leftIH middleIH rightIH =>
    obtain ⟨equal,ports⟩ := allPorts selected middle.forget
    obtain ⟨leftWalk,leftEq⟩ := leftIH
    obtain ⟨rightWalk,rightEq⟩ := rightIH
    cases equal
    refine ⟨PhysicalSourceWalk.over initial matching ports leftWalk rightWalk,?_⟩
    change (leftWalk.edges++beta.principal)++rightWalk.edges=_
    rw [leftEq,rightEq]
    simp only [SourceEdgeSelection.evalLabel,Labelled.Label.sourceWord_concat,Labelled.Label.over,
      Labelled.Label.sourceWord,Letter.sourceWord]
  | under left selected middle right leftIH middleIH rightIH =>
    obtain ⟨equal,ports⟩ := allPorts selected middle.forget
    obtain ⟨leftWalk,leftEq⟩ := leftIH
    obtain ⟨rightWalk,rightEq⟩ := rightIH
    cases equal
    refine ⟨PhysicalSourceWalk.under initial matching ports leftWalk rightWalk,?_⟩
    change (leftWalk.edges++beta.reverseRoute)++rightWalk.edges=_
    rw [leftEq,rightEq]
    simp only [SourceEdgeSelection.evalLabel,Labelled.Label.sourceWord_concat,Labelled.Label.under,
      Labelled.Label.sourceWord,Letter.sourceWord]
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
/-- All legal selected routes share ONE actual finite edge selector and ONE
fixed physical principal route. In particular every atom is a real nonempty
fragment; the off-domain fallback is never treated as a legal atom. -/
theorem PathSite.shared_source_route_evaluation
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original) (closed : Closed original.erase)
    (matching : Matches site.net root original.erase) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
      ∃ selection : SourceEdgeSelection original site.net root,
      ∀ {start stamp finish},
      SelectedSourceRoute (sourceEdges [] .external original)
        (SelectedDegree original (site.betaSyntaxFiber root original.erase)) start stamp finish →
      ∃ walk : PhysicalSourceWalk original root beta start stamp finish,walk.edges=selection.evalLabel beta stamp := by
  obtain ⟨beta,app,lam,allPorts⟩ := site.selected_beta_source_ports initial matching
  let selection := matching.source_edge_selection closed
  exact ⟨beta,app,lam,selection,fun route => SourceEdgeSelection.selected_route_walk selection initial matching allPorts route⟩
end
end Lamping.AG




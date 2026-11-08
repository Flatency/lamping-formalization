import Lamping.Lamping.SourceActionPassiveBranch
import Lamping.Lamping.ActionSourceCanonicalBlocks
import Lamping.Lamping.ActionCrossingReplay
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
/-- Pure finite source block geometry. No target path, labels or replay
condition is stored. Partial typed terminals are handled outside this grammar. -/
inductive SourceActionRoute (principal : SiteActionPrincipal site) :
    s.Frontier → s.Frontier → List (Endpoint site.net) → Prop where
  | cross (p : Aux s.active) (q : Aux s.passive) :
      SourceActionRoute principal (.inl p) (.inr q) (principal.crossing site p q)
  | backward (p : Aux s.active) (q : Aux s.passive) :
      SourceActionRoute principal (.inr q) (.inl p) (reverseEdges (principal.crossing site p q))
  | passive (p q : Aux s.passive) :
      SourceActionRoute principal (.inr p) (.inr q) (site.passiveCanonical p q)
end

private theorem passive_app_ports (op : Op) (i : Nat) (p q : Aux op) {a b : Context}
    (rule : Traversal i (.op op) (.inr p) (.inr q) a b)
    (direction : ForwardPorts (.op op) (.inr p) (.inr q)) :
    op=.app ∧HEq p false ∧HEq q true ∧a=b := by
  cases op with
  | app =>
    refine ⟨rfl,heq_of_eq (Sum.inr.inj direction.1),?_,rule.proper_context⟩
    rcases direction.2 with impossible|same
    · cases impossible
    · exact heq_of_eq (Sum.inr.inj same)
  | lam => cases direction.1
  | fan => exact False.elim rule.aux_aux
  | cro => exact False.elim rule.aux_aux
  | bra => exact False.elim rule.aux_aux

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {f : Op} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))

theorem SourceActionRoute.fan_expand {principal : SiteActionPrincipal site} {entry exit old}
    (route : SourceActionRoute site principal entry exit old)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {pre : List (Endpoint site.net)} {rootInput a b : Context}
    (parentLabels : Labelling site.net pre rootInput a)
    (rooted : pre.head?=some (.inr (.inl root))) (finish : pre.getLast?=old.head?)
    (labels : Labelling site.net old a b) (forward : Forward site.net old) :
    ∃ path : LocalPath (fanRight f i j) entry exit a b,
      FanCanonicalLocal site principal path.edges old := by
  cases route with
  | cross p q =>
    have actual := (principal.crossing_labels_iff site p q a b).mp labels
    exact ⟨⟨fanCrossEdges p q,rfl,rfl,fanAction_cross_replay f i j lt p q a b actual⟩,.cross p q⟩
  | backward p q =>
    have actual := (principal.reverse_crossing_labels_iff site p q a b).mp labels
    have source := actual.reverse
    rw [reverseEdges_involutive] at source
    let path : LocalPath (fanRight f i j) (.inl p) (.inr q) b a :=
      ⟨fanCrossEdges p q,rfl,rfl,fanAction_cross_replay f i j lt p q b a source⟩
    exact ⟨path.reverse,.backward p q⟩
  | passive p q =>
    have direction := forward.actual_node_ports (g:=site.net) (.inr (.inr ())) (.inr p) (.inr q) []
    have localLabels := (site.passiveCanonical_labels_iff p q a b).mp labels
    have rule : Traversal j (.op f) (.inr p) (.inr q) a b := by
      cases localLabels with
      | cons turn last => cases last; cases turn with | node node p q rule => exact rule
    obtain ⟨app,pRole,qRole,contextEq⟩ := passive_app_ports f j p q rule direction
    subst f
    have pEq : p=false := eq_of_heq pRole
    have qEq : q=true := eq_of_heq qRole
    subst p
    subst q
    subst b
    obtain ⟨branch,uniform⟩ := site.fan_source_passive_branch matching inputs flow positive pre parentLabels rooted finish
    obtain ⟨path,shape⟩ := uniform rootInput a parentLabels
    exact ⟨path,by rw [shape]; exact FanCanonicalLocal.passive (site:=site) (principal:=principal) branch false true⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {f : Op} {i j : Nat} {lt : i<j}
variable (site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))

theorem SourceActionRoute.cro_expand {principal : SiteActionPrincipal site} {entry exit old}
    (route : SourceActionRoute site principal entry exit old)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {pre : List (Endpoint site.net)} {rootInput a b : Context}
    (parentLabels : Labelling site.net pre rootInput a)
    (rooted : pre.head?=some (.inr (.inl root))) (finish : pre.getLast?=old.head?)
    (labels : Labelling site.net old a b) (forward : Forward site.net old) :
    ∃ path : LocalPath (unaryRightCore .cro f (Bij.refl _) i (j-1)) entry exit a b,
      UnaryCanonicalLocal site (Bij.refl _) principal path.edges old := by
  cases route with
  | cross p q =>
    cases p
    have actual := (principal.crossing_labels_iff site () q a b).mp labels
    exact ⟨⟨unaryCrossEdges (s:=.croAction f i j lt) (k:=(j-1)) (Bij.refl _) q,rfl,rfl,
      croAction_cross_replay f i j lt q a b actual⟩,.cross q⟩
  | backward p q =>
    cases p
    have actual := (principal.reverse_crossing_labels_iff site () q a b).mp labels
    have source := actual.reverse
    rw [reverseEdges_involutive] at source
    let path : LocalPath (unaryRightCore .cro f (Bij.refl _) i (j-1)) (.inl ()) (.inr q) b a :=
      ⟨unaryCrossEdges (s:=.croAction f i j lt) (k:=(j-1)) (Bij.refl _) q,rfl,rfl,
        croAction_cross_replay f i j lt q b a source⟩
    exact ⟨path.reverse,.backward q⟩
  | passive p q =>
    have direction := forward.actual_node_ports (g:=site.net) (.inr (.inr ())) (.inr p) (.inr q) []
    have localLabels := (site.passiveCanonical_labels_iff p q a b).mp labels
    have rule : Traversal j (.op f) (.inr p) (.inr q) a b := by
      cases localLabels with
      | cons turn last => cases last; cases turn with | node node p q rule => exact rule
    obtain ⟨app,pRole,qRole,contextEq⟩ := passive_app_ports f j p q rule direction
    subst f
    have pEq : p=false := eq_of_heq pRole
    have qEq : q=true := eq_of_heq qRole
    subst p
    subst q
    subst b
    obtain ⟨path,shape⟩ := site.cro_source_passive_branch matching inputs flow positive pre parentLabels rooted finish
      rootInput a parentLabels
    exact ⟨path,by rw [shape]; exact UnaryCanonicalLocal.passive (site:=site) (single:=Bij.refl _) (principal:=principal) false true⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {f : Op} {i j : Nat} {lt : i<j}
variable (site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V))

theorem SourceActionRoute.bra_expand {principal : SiteActionPrincipal site} {entry exit old}
    (route : SourceActionRoute site principal entry exit old)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {pre : List (Endpoint site.net)} {rootInput a b : Context}
    (parentLabels : Labelling site.net pre rootInput a)
    (rooted : pre.head?=some (.inr (.inl root))) (finish : pre.getLast?=old.head?)
    (labels : Labelling site.net old a b) (forward : Forward site.net old) :
    ∃ path : LocalPath (unaryRightCore .bra f (Bij.refl _) i (j+1)) entry exit a b,
      UnaryCanonicalLocal site (Bij.refl _) principal path.edges old := by
  cases route with
  | cross p q =>
    cases p
    have actual := (principal.crossing_labels_iff site () q a b).mp labels
    exact ⟨⟨unaryCrossEdges (s:=.braAction f i j lt) (k:=(j+1)) (Bij.refl _) q,rfl,rfl,
      braAction_cross_replay f i j lt q a b actual⟩,.cross q⟩
  | backward p q =>
    cases p
    have actual := (principal.reverse_crossing_labels_iff site () q a b).mp labels
    have source := actual.reverse
    rw [reverseEdges_involutive] at source
    let path : LocalPath (unaryRightCore .bra f (Bij.refl _) i (j+1)) (.inl ()) (.inr q) b a :=
      ⟨unaryCrossEdges (s:=.braAction f i j lt) (k:=(j+1)) (Bij.refl _) q,rfl,rfl,
        braAction_cross_replay f i j lt q b a source⟩
    exact ⟨path.reverse,.backward q⟩
  | passive p q =>
    have direction := forward.actual_node_ports (g:=site.net) (.inr (.inr ())) (.inr p) (.inr q) []
    have localLabels := (site.passiveCanonical_labels_iff p q a b).mp labels
    have rule : Traversal j (.op f) (.inr p) (.inr q) a b := by
      cases localLabels with
      | cons turn last => cases last; cases turn with | node node p q rule => exact rule
    obtain ⟨app,pRole,qRole,contextEq⟩ := passive_app_ports f j p q rule direction
    subst f
    have pEq : p=false := eq_of_heq pRole
    have qEq : q=true := eq_of_heq qRole
    subst p
    subst q
    subst b
    obtain ⟨path,shape⟩ := site.bra_source_passive_branch matching inputs flow positive pre parentLabels rooted finish
      rootInput a parentLabels
    exact ⟨path,by rw [shape]; exact UnaryCanonicalLocal.passive (site:=site) (single:=Bij.refl _) (principal:=principal) false true⟩
end
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
/-- Actual finite source block expansion for all three actions. The target
local path is constructed from source geometry and its actual root prefix;
there is no RHS reference, target labels or uniform-replay premise. -/
theorem SourceActionRoute.expand (action : IsAction s)
    {principal : SiteActionPrincipal site} {entry exit old}
    (route : SourceActionRoute site principal entry exit old)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {pre : List (Endpoint site.net)} {rootInput a b : Context}
    (parentLabels : Labelling site.net pre rootInput a)
    (rooted : pre.head?=some (.inr (.inl root))) (finish : pre.getLast?=old.head?)
    (labels : Labelling site.net old a b) (forward : Forward site.net old) :
    ∃ path : LocalPath s.right.net entry exit a b,
      ActionCanonicalLocal site principal path.edges old := by
  cases action with
  | fan f i j lt =>
    obtain ⟨path,canonical⟩ := route.fan_expand site matching inputs flow positive parentLabels rooted finish labels forward
    exact ⟨path,.fan canonical⟩
  | cro f i j lt =>
    obtain ⟨path,canonical⟩ := route.cro_expand site matching inputs flow positive parentLabels rooted finish labels forward
    exact ⟨path,.cro canonical⟩
  | bra f i j lt =>
    obtain ⟨path,canonical⟩ := route.bra_expand site matching inputs flow positive parentLabels rooted finish labels forward
    exact ⟨path,.bra canonical⟩
end
end Lamping.AG

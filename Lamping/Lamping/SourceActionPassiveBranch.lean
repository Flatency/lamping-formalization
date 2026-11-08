import Lamping.Lamping.RootMatchedControlInputs
import Lamping.Lamping.ActionPassiveReplay
import Lamping.Lamping.ActionCanonicalResidual
namespace Lamping.AG
open Graph Lambda
private theorem app_kind (k : Kind) (ctx : Port k) (same : k=.op .app)
    (role : HEq ctx appCtx) : portKind k ctx=some .app := by
  subst k
  have equal : ctx=appCtx := eq_of_heq role
  subst ctx
  rfl
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- A real source parent prefix determines an inverse-control branch without
an RHS reference. Matches supplies its actual function child; RootInputs
relables that SAME child. The chosen auxiliary is fixed before any relabelling. -/
theorem PathSite.source_control_branch {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (passive : s.passive=.app)
    (pre : List (Endpoint site.net)) (ctx : Port (.op s.passive)) (ctxRole : HEq ctx appCtx)
    {input seam : Context} (labels : Labelling site.net pre input seam)
    (rooted : pre.head?=some (.inr (.inl root)))
    (finish : pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),ctx⟩))) :
    ∃ q : Aux s.active,∀ requested current,Labelling site.net pre requested current →
      ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr q) current middle := by
  have appKind := app_kind (.op s.passive) ctx (congrArg Kind.op passive) ctxRole
  have observed : accessKind site.net pre=some .app := by
    unfold accessKind
    rw [finish]
    simp only [Option.bind_some,Pairing.involutive]
    exact appKind
  let parent : RootAccess site.net root :=
    ⟨pre,⟨⟨⟨input,seam,labels⟩,labels.root_forward_of_flow flow root rooted positive⟩,
      rooted,⟨.app,observed⟩⟩⟩
  exact site.matched_control_inputs_root matching inputs control passive parent ctx ctxRole finish
end

/-- This is a constructed RHS local path, not a reference-path assumption. -/
def fanPassiveLocal (i j : Nat) (branch : Bool) (a middle : Context)
    (rule : Traversal i (.op .fan) (.inl ()) (.inr branch) a middle) :
    LocalPath (fanRight .app i j) (.inr false) (.inr true) a a where
  edges := fanPassiveEdges (f:=.app) (i:=i) (j:=j) branch false true
  start := rfl
  finish := rfl
  labeling := fanAction_passive_replay i j branch a middle rule

def unaryPassiveLocal (control : Op) (single : Bij Unit (Aux control))
    (i k : Nat) (a middle : Context)
    (rule : Traversal i (.op control) (.inl ()) (.inr (single ())) a middle) :
    LocalPath (unaryRightCore control .app single i k) (.inr false) (.inr true) a a where
  edges := [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr (single ())⟩,
    .inl ⟨.inl (),appArg⟩,.inl ⟨.inr true,.inl ()⟩]
  start := rfl
  finish := rfl
  labeling := unaryAction_passive_replay control single i k a middle rule

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j} {root : B} {t : Term}
variable {boundary : B → Bool}

/-- The fixed fan branch is obtained solely from the existing source parent.
Every labelling of that literal prefix constructs the corresponding four-edge
RHS excursion. In particular no RHS labelling or branch is a premise. -/
theorem PathSite.fan_source_passive_branch
    (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (pre : List (Endpoint site.net)) {input seam : Context}
    (labels : Labelling site.net pre input seam)
    (rooted : pre.head?=some (.inr (.inl root)))
    (finish : pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩))) :
    ∃ branch : Bool,∀ requested current,Labelling site.net pre requested current →
      ∃ path : LocalPath (fanRight .app i j) (.inr false) (.inr true) current current,
        path.edges=fanPassiveEdges (f:=.app) (i:=i) (j:=j) branch false true := by
  obtain ⟨branch,uniform⟩ := site.source_control_branch matching inputs flow positive (Or.inl rfl) rfl
    pre appCtx HEq.rfl labels rooted finish
  refine ⟨branch,?_⟩
  intro requested current parentLabels
  obtain ⟨middle,rule⟩ := uniform requested current parentLabels
  exact ⟨fanPassiveLocal i j branch current middle rule,rfl⟩

theorem PathSite.cro_source_passive_branch
    (site : PathSite (.croAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (pre : List (Endpoint site.net)) {input seam : Context}
    (labels : Labelling site.net pre input seam)
    (rooted : pre.head?=some (.inr (.inl root)))
    (finish : pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩))) :
    ∀ requested current,Labelling site.net pre requested current →
      ∃ path : LocalPath (unaryRightCore .cro .app (Bij.refl _) i (j-1)) (.inr false) (.inr true) current current,
        path.edges=[.inr (.inl (.inr false)),.inl ⟨.inr false,.inr ()⟩,
          .inl ⟨.inl (),appArg⟩,.inl ⟨.inr true,.inl ()⟩] := by
  obtain ⟨q,uniform⟩ := site.source_control_branch matching inputs flow positive (Or.inr (Or.inl rfl)) rfl
    pre appCtx HEq.rfl labels rooted finish
  cases q
  intro requested current parentLabels
  obtain ⟨middle,rule⟩ := uniform requested current parentLabels
  exact ⟨unaryPassiveLocal .cro (Bij.refl _) i (j-1) current middle rule,rfl⟩

theorem PathSite.bra_source_passive_branch
    (site : PathSite (.braAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (pre : List (Endpoint site.net)) {input seam : Context}
    (labels : Labelling site.net pre input seam)
    (rooted : pre.head?=some (.inr (.inl root)))
    (finish : pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩))) :
    ∀ requested current,Labelling site.net pre requested current →
      ∃ path : LocalPath (unaryRightCore .bra .app (Bij.refl _) i (j+1)) (.inr false) (.inr true) current current,
        path.edges=[.inr (.inl (.inr false)),.inl ⟨.inr false,.inr ()⟩,
          .inl ⟨.inl (),appArg⟩,.inl ⟨.inr true,.inl ()⟩] := by
  obtain ⟨q,uniform⟩ := site.source_control_branch matching inputs flow positive (Or.inr (Or.inr rfl)) rfl
    pre appCtx HEq.rfl labels rooted finish
  cases q
  intro requested current parentLabels
  obtain ⟨middle,rule⟩ := uniform requested current parentLabels
  exact ⟨unaryPassiveLocal .bra (Bij.refl _) i (j+1) current middle rule,rfl⟩
end
end Lamping.AG


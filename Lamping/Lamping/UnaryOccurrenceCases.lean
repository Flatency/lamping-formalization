import Lamping.Lamping.ActionSyntaxObservationKinds
import Lamping.Lamping.FragmentChildStepSeparation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
private theorem SyntaxChildPorts.app_steps {kind : Kind} {c d : Port kind} {step : Step}
    (roles : SyntaxChildPorts kind c d step) (shape : kind=.op .app) : step=.fn ∨step=.arg := by
  cases roles <;> simp_all
private theorem SyntaxChildPorts.lambda_step {kind : Kind} {c d : Port kind} {step : Step}
    (roles : SyntaxChildPorts kind c d step) (shape : kind=.op .lam) : step=.body := by
  cases roles <;> simp_all
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
/-- A supplied actual child prefix and APP parent finish force fn or arg. -/
theorem SourceEdgeFragment.step_of_app_parent
    (matching : Matches g root current.erase)
    (fragment : SourceEdgeFragment current g root edge position)
    (parent : RootAccess g root) (word : position=accessWord g parent.val++[step])
    (node : N) (ctx : Port (g.label node).sort)
    (shape : (g.label node).sort=.op .app)
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩))) : step=.fn ∨step=.arg := by
  obtain ⟨n,c,d,tail,roles,parentFinish,_⟩ := matching.syntax_child_fragment parent fragment.access step
    (fragment.word.trans word)
  have same := congrArg g.wire (Option.some.inj (parentFinish.symm.trans finish))
  simp only [Pairing.involutive] at same
  have ports := Sum.inl.inj same
  have nodes : n=node := congrArg Sigma.fst ports
  subst n
  exact roles.app_steps shape
/-- A supplied actual child prefix and lambda parent finish force body. -/
theorem SourceEdgeFragment.step_of_lambda_parent
    (matching : Matches g root current.erase)
    (fragment : SourceEdgeFragment current g root edge position)
    (parent : RootAccess g root) (word : position=accessWord g parent.val++[step])
    (node : N) (ctx : Port (g.label node).sort)
    (shape : (g.label node).sort=.op .lam)
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩))) : step=.body := by
  obtain ⟨n,c,d,tail,roles,parentFinish,_⟩ := matching.syntax_child_fragment parent fragment.access step
    (fragment.word.trans word)
  have same := congrArg g.wire (Option.some.inj (parentFinish.symm.trans finish))
  simp only [Pairing.involutive] at same
  have nodes : n=node := congrArg Sigma.fst (Sum.inl.inj same)
  subst n
  exact roles.lambda_step shape
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Finite typed classification of the actual RHS access, not a guessed node. -/
theorem PathSite.cro_app_access_cases {root : B} (path : RootAccess site.reduce root) :
    (∃ port : NodePort signature K kept,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∨      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)) := by
  rcases site.action_access_node_cases (IsAction.cro .app i j lt) path with old |⟨node,port,passive,finish⟩
  · exact Or.inl old
  · cases passive
    obtain ⟨kind,typed⟩ := path.property.2.2
    have actual := accessKind_at_actual_finish typed (.inr (.inl ())) port finish
    cases port with
    | inl u =>
      cases u
      change none=some kind at actual
      cases actual
    | inr b =>
      cases b
      · exact Or.inr finish
      · change none=some kind at actual;cases actual
end
#print axioms PathSite.cro_app_access_cases
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Finite typed classification of the actual RHS access, not a guessed node. -/
theorem PathSite.cro_lam_access_cases {root : B} (path : RootAccess site.reduce root) :
    (∃ port : NodePort signature K kept,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∨      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) ∨
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩)) := by
  rcases site.action_access_node_cases (IsAction.cro .lam i j lt) path with old |⟨node,port,passive,finish⟩
  · exact Or.inl old
  · cases passive
    obtain ⟨kind,typed⟩ := path.property.2.2
    have actual := accessKind_at_actual_finish typed (.inr (.inl ())) port finish
    cases port with
    | inl u =>
      cases u
      exact Or.inr (Or.inl finish)
    | inr b =>
      cases b
      · exact Or.inr (Or.inr finish)
      · change none=some kind at actual;cases actual
end
#print axioms PathSite.cro_lam_access_cases
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Finite typed classification of the actual RHS access, not a guessed node. -/
theorem PathSite.bra_app_access_cases {root : B} (path : RootAccess site.reduce root) :
    (∃ port : NodePort signature K kept,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∨      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)) := by
  rcases site.action_access_node_cases (IsAction.bra .app i j lt) path with old |⟨node,port,passive,finish⟩
  · exact Or.inl old
  · cases passive
    obtain ⟨kind,typed⟩ := path.property.2.2
    have actual := accessKind_at_actual_finish typed (.inr (.inl ())) port finish
    cases port with
    | inl u =>
      cases u
      change none=some kind at actual
      cases actual
    | inr b =>
      cases b
      · exact Or.inr finish
      · change none=some kind at actual;cases actual
end
#print axioms PathSite.bra_app_access_cases
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Finite typed classification of the actual RHS access, not a guessed node. -/
theorem PathSite.bra_lam_access_cases {root : B} (path : RootAccess site.reduce root) :
    (∃ port : NodePort signature K kept,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∨      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) ∨
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩)) := by
  rcases site.action_access_node_cases (IsAction.bra .lam i j lt) path with old |⟨node,port,passive,finish⟩
  · exact Or.inl old
  · cases passive
    obtain ⟨kind,typed⟩ := path.property.2.2
    have actual := accessKind_at_actual_finish typed (.inr (.inl ())) port finish
    cases port with
    | inl u =>
      cases u
      exact Or.inr (Or.inl finish)
    | inr b =>
      cases b
      · exact Or.inr (Or.inr finish)
      · change none=some kind at actual;cases actual
end
#print axioms PathSite.bra_lam_access_cases

#print axioms SourceEdgeFragment.step_of_app_parent
#print axioms SourceEdgeFragment.step_of_lambda_parent
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
/-- The real parent endpoint of an actual syntax child has syntax context ports. -/
theorem SourceEdgeFragment.parent_syntax_ports
    (matching : Matches g root current.erase)
    (fragment : SourceEdgeFragment current g root edge position)
    (parent : RootAccess g root) (word : position=accessWord g parent.val++[step])
    (node : N) (ctx : Port (g.label node).sort)
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩))) :
    ∃ departure,SyntaxChildPorts (g.label node).sort ctx departure step := by
  obtain ⟨n,c,d,tail,roles,parentFinish,_⟩ := matching.syntax_child_fragment parent fragment.access step
    (fragment.word.trans word)
  have same := congrArg g.wire (Option.some.inj (parentFinish.symm.trans finish))
  simp only [Pairing.involutive] at same
  have ports := Sum.inl.inj same
  have nodes : n=node := congrArg Sigma.fst ports
  subst n
  have contexts : c=ctx := eq_of_heq (Sigma.mk.inj ports).2
  subst c
  exact ⟨d,roles⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- A binding port is a valid terminal, but not a parent syntax context. -/
theorem PathSite.cro_lam_parent_cases {root : B} {current : LTerm}
    (matching : Matches site.reduce root current.erase)
    (fragment : SourceEdgeFragment current site.reduce root edge position)
    (parent : RootAccess site.reduce root) (word : position=accessWord site.reduce parent.val++[step]) :
    (∃ port : NodePort signature K kept,
      parent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∨
      parent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
  rcases site.cro_lam_access_cases parent with kept |ctx|binding
  · exact Or.inl kept
  · exact Or.inr ctx
  · obtain ⟨departure,roles⟩ := fragment.parent_syntax_ports matching parent word (.inr (.inl ())) lamBind binding
    cases roles
end
#print axioms PathSite.cro_lam_parent_cases
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- A binding port is a valid terminal, but not a parent syntax context. -/
theorem PathSite.bra_lam_parent_cases {root : B} {current : LTerm}
    (matching : Matches site.reduce root current.erase)
    (fragment : SourceEdgeFragment current site.reduce root edge position)
    (parent : RootAccess site.reduce root) (word : position=accessWord site.reduce parent.val++[step]) :
    (∃ port : NodePort signature K kept,
      parent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∨
      parent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
  rcases site.bra_lam_access_cases parent with kept |ctx|binding
  · exact Or.inl kept
  · exact Or.inr ctx
  · obtain ⟨departure,roles⟩ := fragment.parent_syntax_ports matching parent word (.inr (.inl ())) lamBind binding
    cases roles
end
#print axioms PathSite.bra_lam_parent_cases

#print axioms SourceEdgeFragment.parent_syntax_ports
end Lamping.AG

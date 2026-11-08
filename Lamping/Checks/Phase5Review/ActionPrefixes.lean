import Lamping.Lamping.MatchingBetaRootVisibility
import Lamping.Lamping.ActionBindingAccess
import Lamping.Lamping.ActionCopiedBindingAccess
import Lamping.Lamping.ActionPendingAccess
import Lamping.Lamping.ActionPendingWords
import Lamping.Checks.Soundness
import Lamping.Lamping.ActionSourcePrefixes
import Lamping.Lamping.ActionNewNodeAncestors
import Lamping.Lamping.Fixtures
namespace Lamping.Checks.Phase5Review.ActionPrefixes
open AG Graph
private def kept : Empty → Label signature := Empty.elim
private def fanSite : PathSite (.fanAction .app 2 3 (by decide)) kept (B:=Bool⊕Bool) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl k,_⟩ => nomatch k
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inl _),.inr a⟩ => .inr (.inl (.inl a))
      | .inl ⟨.inr (.inr _),.inr a⟩ => .inr (.inl (.inr a))
      | .inr (.inl (.inl a)) => .inl ⟨.inr (.inl ()),.inr a⟩
      | .inr (.inl (.inr a)) => .inl ⟨.inr (.inr ()),.inr a⟩
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
      · exact nomatch k
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · rfl
      · rfl
      · exact nomatch w
      · cases v; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩)) same
      · exact nomatch k
      · cases p <;> cases same
      · cases p <;> cases same
      · cases same
      · cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases v; cases b <;> rfl

private def croSite : PathSite (.croAction .app 2 3 (by decide)) kept (B:=Unit⊕Bool) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl k,_⟩ => nomatch k
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inl _),.inr a⟩ => .inr (.inl (.inl a))
      | .inl ⟨.inr (.inr _),.inr a⟩ => .inr (.inl (.inr a))
      | .inr (.inl (.inl a)) => .inl ⟨.inr (.inl ()),.inr a⟩
      | .inr (.inl (.inr a)) => .inl ⟨.inr (.inr ()),.inr a⟩
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
      · exact nomatch k
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · rfl
      · rfl
      · exact nomatch w
      · cases v; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩)) same
      · exact nomatch k
      · cases p <;> cases same
      · cases p <;> cases same
      · cases same
      · cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases v; cases b <;> rfl

private def braSite : PathSite (.braAction .app 2 3 (by decide)) kept (B:=Unit⊕Bool) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl k,_⟩ => nomatch k
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inl _),.inr a⟩ => .inr (.inl (.inl a))
      | .inl ⟨.inr (.inr _),.inr a⟩ => .inr (.inl (.inr a))
      | .inr (.inl (.inl a)) => .inl ⟨.inr (.inl ()),.inr a⟩
      | .inr (.inl (.inr a)) => .inl ⟨.inr (.inr ()),.inr a⟩
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
      · exact nomatch k
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · rfl
      · rfl
      · exact nomatch w
      · cases v; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩)) same
      · exact nomatch k
      · cases p <;> cases same
      · cases p <;> cases same
      · cases same
      · cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases v; cases b <;> rfl

private def fanBoundary : Bool⊕Bool → Bool := Sum.elim (fun _ => false) (fun b => !b)
private def fanFlow : FlowBalance fanSite.net fanBoundary where
  nodes := Sum.elim Empty.elim (Sum.elim (fun _ => false) (fun _ => true))
  vertices := fun _ => true
  wiring := by
    rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
    · exact nomatch k
    · cases p <;> rfl
    · cases p <;> rfl
    · rfl
    · cases a <;> rfl
    · exact nomatch w
    · cases d <;> rfl
private def croBoundary : Unit⊕Bool → Bool := Sum.elim (fun _ => false) (fun b => !b)
private def croFlow : FlowBalance croSite.net croBoundary where
  nodes := Sum.elim Empty.elim (Sum.elim (fun _ => false) (fun _ => true))
  vertices := fun _ => true
  wiring := by
    rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
    · exact nomatch k
    · cases p <;> rfl
    · cases p <;> rfl
    · rfl
    · cases a <;> rfl
    · exact nomatch w
    · cases d <;> rfl
private def braBoundary : Unit⊕Bool → Bool := Sum.elim (fun _ => false) (fun b => !b)
private def braFlow : FlowBalance braSite.net braBoundary where
  nodes := Sum.elim Empty.elim (Sum.elim (fun _ => false) (fun _ => true))
  vertices := fun _ => true
  wiring := by
    rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
    · exact nomatch k
    · cases p <;> rfl
    · cases p <;> rfl
    · rfl
    · cases a <;> rfl
    · exact nomatch w
    · cases d <;> rfl
private def fanEdges (branch : Bool) : List (Endpoint fanSite.reduce) :=
  [.inr (.inl (.inr false)),.inr (.inr (.inr (.inr false),true)),.inl ⟨.inr (.inr false),.inr branch⟩]
private def croEdges : List (Endpoint croSite.reduce) :=
  [.inr (.inl (.inr false)),.inr (.inr (.inr (.inr false),true)),.inl ⟨.inr (.inr false),.inr ()⟩]
private def braEdges : List (Endpoint braSite.reduce) :=
  [.inr (.inl (.inr false)),.inr (.inr (.inr (.inr false),true)),.inl ⟨.inr (.inr false),.inr ()⟩]

theorem fan_labels (branch : Bool) (shell tail : Context) (x : Level) :
    Labelling fanSite.reduce (fanEdges branch)
      (shell.replace 2 (tail.cons (if branch then .star x else .o x))) (shell.replace 2 (tail.cons x)) := by
  apply Labelling.cons (LabelledTurn.transparent (g:=fanSite.reduce) (.inr (.inr false)) false _)
  have rule : Traversal 2 (.op .fan) (.inl ()) (.inr branch)
      (shell.replace 2 (tail.cons (if branch then .star x else .o x))) (shell.replace 2 (tail.cons x)) := by
    cases branch
    · exact .inverse (.fanO shell tail x)
    · exact .inverse (.fanStar shell tail x)
  apply Labelling.cons (LabelledTurn.node (g:=fanSite.reduce) (.inr (.inr false)) (.inl ()) (.inr branch) rule)
  exact .single _ _

theorem cro_labels (shell tail : Context) :
    Labelling croSite.reduce croEdges (shell.replace 2 (tail.cons .empty)) (shell.replace 2 tail) := by
  apply Labelling.cons (LabelledTurn.transparent (g:=croSite.reduce) (.inr (.inr false)) false _)
  apply Labelling.cons (LabelledTurn.node (g:=croSite.reduce) (.inr (.inr false)) (.inl ()) (.inr ()) (.inverse (.cro shell tail)))
  exact .single _ _

theorem bra_labels (shell tail : Context) (x y : Level) :
    Labelling braSite.reduce braEdges (shell.replace 2 (tail.cons (.pair x y))) (shell.replace 2 ((tail.cons x).cons y)) := by
  apply Labelling.cons (LabelledTurn.transparent (g:=braSite.reduce) (.inr (.inr false)) false _)
  apply Labelling.cons (LabelledTurn.node (g:=braSite.reduce) (.inr (.inr false)) (.inl ()) (.inr ()) (.inverse (.bra shell tail x y)))
  exact .single _ _

theorem fan_actual_ancestor (branch : Bool) (shell tail : Context) (x : Level) :
    ∃ old oldContext,Labelling fanSite.net old (shell.replace 2 (tail.cons (if branch then .star x else .o x))) oldContext ∧
      Forward fanSite.net old ∧old.head?=some (.inr (.inl (.inr false))) ∧
      old.getLast?=some (fanSite.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) ∧
      oldContext.tail 3=(shell.replace 2 (tail.cons x)).tail 3 :=
  fanSite.fan_new_aux_ancestor fanFlow (.inr false) rfl (fan_labels branch shell tail x) rfl branch false rfl

theorem cro_actual_ancestor (shell tail : Context) :
    ∃ old oldContext,Labelling croSite.net old (shell.replace 2 (tail.cons .empty)) oldContext ∧
      Forward croSite.net old ∧old.head?=some (.inr (.inl (.inr false))) ∧
      old.getLast?=some (croSite.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) ∧
      oldContext.tail 3=(shell.replace 2 tail).tail 2 :=
  croSite.cro_new_aux_ancestor croFlow (.inr false) rfl (cro_labels shell tail) rfl false rfl

theorem bra_actual_ancestor (shell tail : Context) (x y : Level) :
    ∃ old oldContext,Labelling braSite.net old (shell.replace 2 (tail.cons (.pair x y))) oldContext ∧
      Forward braSite.net old ∧old.head?=some (.inr (.inl (.inr false))) ∧
      old.getLast?=some (braSite.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) ∧
      oldContext.tail 3=(shell.replace 2 ((tail.cons x).cons y)).tail 4 :=
  braSite.bra_new_aux_ancestor braFlow (.inr false) rfl (bra_labels shell tail x y) rfl false rfl

#print axioms fan_actual_ancestor
#print axioms cro_actual_ancestor
#print axioms bra_actual_ancestor
/-- The constructed old prefix ends at the very root boundary again, so its
context is the original root input, not the new node's low-level output. -/
theorem cro_source_context_is_input (shell tail : Context) :
    ∃ old oldContext,Labelling croSite.net old (shell.replace 2 (tail.cons .empty)) oldContext ∧
      oldContext=shell.replace 2 (tail.cons .empty) ∧oldContext.tail 3=(shell.replace 2 tail).tail 2 := by
  obtain ⟨old,oldContext,labels,_,_,last,tails⟩ := cro_actual_ancestor shell tail
  have unchanged : shell.replace 2 (tail.cons .empty)=oldContext := (labels.boundary_last (.inr false) last).2
  exact ⟨old,oldContext,labels,unchanged.symm,tails⟩

theorem bra_source_context_is_input (shell tail : Context) (x y : Level) :
    ∃ old oldContext,Labelling braSite.net old (shell.replace 2 (tail.cons (.pair x y))) oldContext ∧
      oldContext=shell.replace 2 (tail.cons (.pair x y)) ∧
      oldContext.tail 3=(shell.replace 2 ((tail.cons x).cons y)).tail 4 := by
  obtain ⟨old,oldContext,labels,_,_,last,tails⟩ := bra_actual_ancestor shell tail x y
  have unchanged : shell.replace 2 (tail.cons (.pair x y))=oldContext := (labels.boundary_last (.inr false) last).2
  exact ⟨old,oldContext,labels,unchanged.symm,tails⟩

-- Dropping the critical +/-1 shift gives genuinely unequal high tails.
example (shell : Context) :
    (shell.replace 2 ((Context.empty.cons (.star .empty)).cons .empty)).tail 3 ≠
      (shell.replace 2 (Context.empty.cons (.star .empty))).tail 3 := by
  intro same
  have impossible := congrArg (fun c : Context => c.get 0) same
  change Level.star .empty=Level.empty at impossible
  cases impossible
example (shell : Context) :
    (shell.replace 2 ((Context.empty.cons (.star .empty)).cons (.pair (.o .empty) (.star .empty)))).tail 3 ≠
      (shell.replace 2 (((Context.empty.cons (.star .empty)).cons (.o .empty)).cons (.star .empty))).tail 3 := by
  intro same
  have impossible := congrArg (fun c : Context => c.get 0) same
  change Level.star .empty=Level.o .empty at impossible
  cases impossible
example (shell tail : Context) : shell.replace 2 (tail.cons .empty) ≠ shell.replace 2 (tail.cons (.star .empty)) := by
  intro same
  have impossible := congrArg (fun c : Context => c.get 2) same
  change Level.empty=Level.star .empty at impossible
  cases impossible
example (tail : Context) := fan_actual_ancestor false (Context.empty.cons (.star .empty)) tail (.o .empty)
example (tail : Context) := fan_actual_ancestor true (Context.empty.cons (.star .empty)) tail (.star .empty)
example (tail : Context) := cro_source_context_is_input (Context.empty.cons (.star .empty)) tail
example (tail : Context) := bra_source_context_is_input (Context.empty.cons (.star .empty)) tail (.o .empty) (.star .empty)
#print axioms PathSite.fan_new_aux_ancestor
#print axioms PathSite.cro_new_aux_ancestor
#print axioms PathSite.bra_new_aux_ancestor
#print axioms PathSite.fan_new_lam_context_ancestor
#print axioms PathSite.cro_new_lam_context_ancestor
#print axioms PathSite.bra_new_lam_context_ancestor
#print axioms cro_source_context_is_input
namespace LambdaTerminal
open SoundnessCopiedTransparency
private def principal : SiteActionPrincipal site where
  edges := [.inl ⟨.inr (.inl ()),.inl ()⟩,.inr (.inr (.inr (),true))]
  first := rfl
  last := rfl
  transparent := by
    intro e f member
    change (e,f)∈[(.inl ⟨.inr (.inl ()),.inl ()⟩,.inr (.inr (.inr (),true)))] at member
    have same := List.mem_singleton.mp member
    cases same
    exact ⟨.inr (),false,rfl,rfl⟩

/-- The real fan2/lambda3 source path stops at lambda context after one W.
The typed-prefix theorem returns a singleton rather than inventing a turn. -/
theorem actual_singleton_lambda_suffix (branch : Bool) (a : Context) :
    ∃ suffix middle,suffix=[.inr (.inr (.inr (),true))] ∧
      middle=InitialOffsets.fanAt 2 branch a ∧
      Labelling site.net suffix middle (InitialOffsets.fanAt 2 branch a) := by
  have rule : Traversal 2 (.op .fan) (.inr branch) (.inl ()) a (InitialOffsets.fanAt 2 branch a) :=
    .direct (InitialOffsets.Event.apply_rel (.fan 2 branch) a)
  have labels : Labelling site.net (sourcePre branch) a (InitialOffsets.fanAt 2 branch a) :=
    .cons (LabelledTurn.node (g:=site.net) (.inr (.inl ())) (.inr branch) (.inl ()) rule)
      (.cons (LabelledTurn.transparent (g:=site.net) (.inr ()) false _) (.single _ _))
  obtain ⟨suffix,middle,split,_head,actualRule,after,_typed⟩ := site.typed_action_active_prefix
    (Or.inl rfl) principal branch labels ⟨.lam,rfl⟩ rfl
  have singleton : suffix=[.inr (.inr (.inr (),true))] := by
    change _::_::_= _::_::suffix at split
    exact (List.cons.inj (List.cons.inj split).2).2.symm
  exact ⟨suffix,middle,singleton,actualRule.output_unique rule,after⟩
end LambdaTerminal
#print axioms LambdaTerminal.actual_singleton_lambda_suffix
/-- The actual truncated three-segment app-context path is automatically a
pending block; the new word interface retains its old endpoint and high tail. -/
theorem fan_actual_pending_word (branch : Bool) (shell tail : Context) (x : Level) :
    ∃ old oldContext,Labelling fanSite.net old
      (shell.replace 2 (tail.cons (if branch then .star x else .o x))) oldContext ∧
      accessWord fanSite.net old=[] ∧
      oldContext.tail 3=(shell.replace 2 (tail.cons x)).tail 3 := by
  let c := cutFragment fanSite.net (pathPartition (Schema.fanAction Op.app 2 3 (by decide)) Unit) fanSite.closed
  let r := (Schema.fanAction Op.app 2 3 (by decide)).right.net
  let first : Endpoint c := .inr (.inl (.inl (.inr false)))
  have head : (fanEdges branch).head?=some (AG.plugLeft c r first) := rfl
  obtain ⟨pending,finish⟩ := (fan_labels branch shell tail x).pending_new_node c r first head (.inl branch) appCtx rfl
  have rawHead : ((fanEdges branch).map (plugEnd c.label r.label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd c.label r.label).left_inv (.inl first))
  obtain ⟨old,labels,_start,_last,word,tails⟩ :=
    fanSite.fan_pending_aux_ancestor_word pending first rawHead branch false finish
  have physical : accessWord fanSite.reduce (fanEdges branch)=accessWord fanSite.net old := by
    simpa only [plug_decomposition_flatten] using word
  exact ⟨old,pending.middle,labels,physical.symm.trans rfl,tails⟩
#print axioms fan_actual_pending_word
/-- Each actual three-segment root access exercises the TOTAL action wrapper,
not a caller-supplied pending certificate or only the auxiliary theorem. -/
theorem fan_total_root_access_backward (branch : Bool) (shell tail : Context) (x : Level) :
    ∃ source : RootAccess fanSite.net (.inr false),
      accessWord fanSite.net source.val=[] ∧ accessKind fanSite.net source.val=some .app := by
  have labels := fan_labels branch shell tail x
  obtain ⟨flow⟩ := fanSite.reduce_flowBalance fanFlow
  have forward := labels.root_forward_of_flow flow (.inr false) rfl rfl
  let target : RootAccess fanSite.reduce (.inr false) :=
    ⟨fanEdges branch,⟨⟨⟨_,_,labels⟩,forward⟩,rfl,⟨.app,rfl⟩⟩⟩
  obtain ⟨source,word,kind⟩ := fanSite.action_root_access_backward
    (.fan .app 2 3 (by decide)) fanFlow (.inr false) rfl target
  exact ⟨source,word,kind⟩

theorem cro_total_root_access_backward (shell tail : Context) :
    ∃ source : RootAccess croSite.net (.inr false),
      accessWord croSite.net source.val=[] ∧ accessKind croSite.net source.val=some .app := by
  have labels := cro_labels shell tail
  obtain ⟨flow⟩ := croSite.reduce_flowBalance croFlow
  have forward := labels.root_forward_of_flow flow (.inr false) rfl rfl
  let target : RootAccess croSite.reduce (.inr false) :=
    ⟨croEdges,⟨⟨⟨_,_,labels⟩,forward⟩,rfl,⟨.app,rfl⟩⟩⟩
  obtain ⟨source,word,kind⟩ := croSite.action_root_access_backward
    (.cro .app 2 3 (by decide)) croFlow (.inr false) rfl target
  exact ⟨source,word,kind⟩

theorem bra_total_root_access_backward (shell tail : Context) (x y : Level) :
    ∃ source : RootAccess braSite.net (.inr false),
      accessWord braSite.net source.val=[] ∧ accessKind braSite.net source.val=some .app := by
  have labels := bra_labels shell tail x y
  obtain ⟨flow⟩ := braSite.reduce_flowBalance braFlow
  have forward := labels.root_forward_of_flow flow (.inr false) rfl rfl
  let target : RootAccess braSite.reduce (.inr false) :=
    ⟨braEdges,⟨⟨⟨_,_,labels⟩,forward⟩,rfl,⟨.app,rfl⟩⟩⟩
  obtain ⟨source,word,kind⟩ := braSite.action_root_access_backward
    (.bra .app 2 3 (by decide)) braFlow (.inr false) rfl target
  exact ⟨source,word,kind⟩
#print axioms fan_total_root_access_backward
#print axioms cro_total_root_access_backward
#print axioms bra_total_root_access_backward
namespace CopiedLambdaTotal
open SoundnessCopiedTransparency
/-- The total backward-access API also handles the real copied binding port;
this tests word/kind and deliberately leaves BindingSuffix index separate. -/
theorem actual_copied_binding_access (branch : Bool) (a : Context) :
    ∃ source : RootAccess site.net (.inl branch),
      accessWord site.net source.val=accessWord site.reduce (targetEdges branch) ∧
      accessKind site.net source.val=some .var := by
  have labels := target_labels branch a
  obtain ⟨changed⟩ := site.reduce_flowBalance flow
  have forward := labels.root_forward_of_flow changed (.inl branch) rfl rfl
  let target : RootAccess site.reduce (.inl branch) :=
    ⟨targetEdges branch,⟨⟨⟨_,_,labels⟩,forward⟩,rfl,⟨.var,rfl⟩⟩⟩
  exact site.action_root_access_backward (.fan .lam 2 3 (by decide)) flow (.inl branch) rfl target
/-- The genuine seven-segment copied binding access consumes the public
index-preserving wrapper, with source T independently established by finite
path classification in the reused fixture. -/
theorem actual_copied_binding_same_index (branch : Bool) (a : Context) :
    ∃ source : RootAccess site.net (.inl branch),
      accessWord site.net source.val=accessWord site.reduce (targetEdges branch) ∧
      accessKind site.net source.val=some .var ∧
      ∃ index,BindingSuffix site.net source.val index ∧
        BindingSuffix site.reduce (targetEdges branch) index := by
  have labels := target_labels branch a
  obtain ⟨changed⟩ := site.reduce_flowBalance flow
  have forward := labels.root_forward_of_flow changed (.inl branch) rfl rfl
  let target : RootAccess site.reduce (.inl branch) :=
    ⟨targetEdges branch,⟨⟨⟨_,_,labels⟩,forward⟩,rfl,⟨.var,rfl⟩⟩⟩
  exact site.fan_copied_binding_access flow (.inl branch) rfl
    (source_transparency branch) target branch rfl
/-- The total variable API recovers the actual copied binder automatically;
no branch, endpoint metadata, pending decomposition or index is supplied. -/
theorem actual_total_binding_same_index (branch : Bool) (a : Context) :
    ∃ source : RootAccess site.net (.inl branch),
      accessWord site.net source.val=accessWord site.reduce (targetEdges branch) ∧
      accessKind site.net source.val=some .var ∧
      ∃ index,BindingSuffix site.net source.val index ∧
        BindingSuffix site.reduce (targetEdges branch) index := by
  have labels := target_labels branch a
  obtain ⟨changed⟩ := site.reduce_flowBalance flow
  have forward := labels.root_forward_of_flow changed (.inl branch) rfl rfl
  let target : RootAccess site.reduce (.inl branch) :=
    ⟨targetEdges branch,⟨⟨⟨_,_,labels⟩,forward⟩,rfl,⟨.var,rfl⟩⟩⟩
  exact site.action_variable_binding_access (.fan .lam 2 3 (by decide)) flow
    (.inl branch) rfl (source_transparency branch) target rfl
end CopiedLambdaTotal
#print axioms CopiedLambdaTotal.actual_copied_binding_access
#print axioms CopiedLambdaTotal.actual_copied_binding_same_index
#print axioms CopiedLambdaTotal.actual_total_binding_same_index
namespace BetaVisibility
open SoundnessInitialInsertion SoundnessMatchingChildren
/-- The real encoded I I application is visible in the physical beta fiber;
the public theorem uses its actual finite one-W principal route. -/
theorem actual_closed_beta_visible :
    ∃ redex : Lambda.RedexOcc identityApp,
      redex.val=[] ∧redex.val∈physicalBetaFiberPaths (encode 3 identityApp).net
        (.inl ()) identityApp (edge 3).app (edge 3).lam := by
  have closed : Lambda.Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have matching := encode_closed_matches identityApp closed 3
  obtain ⟨flow⟩ := encode_flowBalance identityApp 3
  exact (edge 3).root_app_visible matching flow rfl parentAccess rfl
end BetaVisibility
#print axioms BetaVisibility.actual_closed_beta_visible
end Lamping.Checks.Phase5Review.ActionPrefixes






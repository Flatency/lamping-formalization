import Lamping.Lamping.LocalActionTransport
import Lamping.Lamping.InitialPaths
import Lamping.Lamping.InitialPathControls
import Lamping.Lamping.InitialFlow
import Lamping.Lamping.InitialOffsetFormula
import Lamping.Lamping.PathSiteBeta
import Lamping.Lamping.Fixtures
import Lamping.Lamping.PathSiteTransport
namespace Lamping.Checks.Paths
open AG Graph
example : Context.cons Context.empty .empty = Context.empty := Context.cons_empty
example : Level.o .empty ≠ Level.star .empty := by decide
example (a b : Context) (i : Nat) : ¬Traversal i (.op .lam) lamBind (.inl ()) a b := by
  intro h; cases h with
  | direct h => cases h
  | inverse h => cases h
example (a b : Context) (i : Nat) : ¬Traversal i (.op .fan) fanO fanStar a b := by
  intro h; cases h with
  | direct h => cases h
  | inverse h => cases h
example (a b : Context) : Passage 0 (.op .cro) (.inr ()) (.inl ()) a (a.cons .empty) := by
  simpa using Passage.cro (i:=0) b a
example (a b : Context) (x y : Level) :
    Passage 0 (.op .bra) (.inr ()) (.inl ()) ((a.cons x).cons y) (a.cons (.pair x y)) := by
  simpa using Passage.bra (i:=0) b a x y
example : Context.SameShell 0 Context.empty (Context.empty.cons (.o .empty)) := by
  intro k hk; omega
example : Context.empty ≠ Context.empty.cons (.o .empty) := by
  intro h; have q := congrArg (fun c => c.get 0) h; cases q
/-- The action theorem really covers a passive control, not just lambda/application. -/
example (s a : Context) (x : Level) :
    Nonempty (LocalPath (Schema.fanAction .cro 0 1 (by omega)).right.net (.inl false) (.inr ())
      (s.replace 0 ((a.cons .empty).cons x)) (s.replace 0 (a.cons (.o x)))) := by
  have h : Traversal 0 (.op .cro) (.inl ()) (.inr ()) (a.cons .empty) a := by
    exact .inverse (by simpa using Passage.cro (i:=0) Context.empty a)
  exact ⟨(fanActionPaths .cro 0 0 () false s (a.cons .empty) a x h).2⟩
#print axioms Context.replace_nested
#print axioms Traversal.lift
#print axioms fanActionPaths
#print axioms croActionPaths
#print axioms braActionPaths
#print axioms expanded_rooted
/-- The beta occurrence comes from encode (I I), with its real one-W principal line. -/
def encodedBetaOccurrence : BetaEdge actualBetaSite.net where
  app := .inr (.inl ())
  lam := .inr (.inr ())
  index := 0
  appLabel := rfl
  lamLabel := rfl
  appFun := .inl ()
  appCtx := .inr false
  appArg := .inr true
  lamCtx := .inl ()
  lamBody := .inr true
  lamBind := .inr false
  appFun_role := HEq.rfl
  appCtx_role := HEq.rfl
  appArg_role := HEq.rfl
  lamCtx_role := HEq.rfl
  lamBody_role := HEq.rfl
  lamBind_role := HEq.rfl
  principal := [.inl ⟨.inr (.inl ()),.inl ()⟩, .inr (.inr (.inr (),true))]
  principalStart := rfl
  principalEnd := rfl
  transparent := by
    intro e f h
    change (e,f) ∈ [(Sum.inl ⟨Sum.inr (Sum.inl ()),Sum.inl ()⟩,
      Sum.inr (Sum.inr (Sum.inr (),true)))] at h
    simp only [List.mem_singleton,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact ⟨.inr (),false,rfl,rfl⟩
example : encodedBetaOccurrence.principal.length=2 := rfl
example : encodedBetaOccurrence.reverseRoute.length=2 := rfl
example (i : Nat) (lt : 0<i) :
    ¬Nonempty (LocalPath (Schema.fanAction .app 0 i lt).right.net (.inr false) (.inr true)
      Context.empty Context.empty) := no_empty_fanAction_passiveApp i lt
example : Nonempty (LocalPath (Schema.fanAction .app 0 1 (by omega)).left (.inr false) (.inr true)
    Context.empty Context.empty) := ⟨passiveAppLeft .fan 0 1 Context.empty⟩
#print axioms no_empty_fanAction_passiveApp
#print axioms LocalPath.reverse
example : Context.normalise [.o .empty,.empty,.empty]=[.o .empty] := rfl
example : Context.ofList [.o .empty,.empty,.empty]=Context.ofList [.o .empty] := by
  exact (Context.ofList_normalise [.o .empty,.empty,.empty]).symm
example (a : Context) : Labelling actualBetaSite.reduce
    (actualBetaSite.rhsEdges (betaRight 0 a)) a a := actualBetaSite.rhs_labeling _
example (a : Context) : ExpandedLabelling actualBetaSite.net
    encodedBetaOccurrence.reverseRoute a a := (encodedBetaOccurrence.reverse_labeling a).expanded
example (n : Nat) (shell tail : Context) :
    Nonempty (BindingLoop (encode n (.lam (.var 0))).net
      [.inl ⟨.inl (),lamBody⟩,.inr (.inr (.inr (.inl ()),true)),
       .inl ⟨.inr (),.inl ()⟩,.inr (.inr (.inr (.inr ⟨0,rfl⟩),false))]
      (shell.replace n tail) (shell.replace n (tail.cons .empty))) := ⟨identityBindingLoop n shell tail⟩
#print axioms Context.canonical_representation
#print axioms fanCancel_transport
#print axioms croCancel_transport
#print axioms braCancel_transport
#print axioms fanAction_transport
#print axioms croAction_transport
#print axioms braAction_transport
#print axioms BetaEdge.expand_loop_labeling
#print axioms ExpandedProperPath.forward
#print axioms PathSite.rhs_labeling
example : Nonempty (BetaEdge actualBetaSite.net) := actualBetaSite.betaEdge_exists
example (a : Context) : ExpandedLabelling actualBetaSite.net encodedBetaOccurrence.backwardPiece a a :=
  encodedBetaOccurrence.backward_piece_labeling a
example : ExpandedForward actualBetaSite.net encodedBetaOccurrence.backwardPiece :=
  encodedBetaOccurrence.backward_piece_forward
example (t : Lambda.Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (rooted : es.head?=some (.inr (.inl (.inl ())))) (proper : ProperPath (encode n t).net es) :
    Forward (encode n t).net es := encode_root_forward t n es rooted proper
#print axioms Context.width_bound
#print axioms encode_flow
#print axioms encode_root_initial
#print axioms encode_root_forward
#print axioms PathSite.betaEdge_exists
#print axioms BetaEdge.backward_piece_labeling
#print axioms BetaEdge.backward_piece_forward
#print axioms beta_context_body_transport
example : Lambda.Closed duplicatedVariable := duplicatedVariable_closed
example : bracketOffset (DupNet 0) (dupLeftControlEdges 0)=0 := dupLeftControlOffset 0
example : bracketOffset (DupNet 0) dupRightControlEdges=1 := dupRightControlOffset
example (x y : Level) : Context.empty.cons (.star (.pair .empty .empty)) ≠ Context.empty.cons (.pair x y) :=
  dupRight_not_printed_positive_offset x y
#print axioms dupLeftBindingLoop
#print axioms printed_zero_offset_counterexample
#print axioms dupRightBindingLoop
#print axioms dupRight_not_printed_positive_offset
open AG.InitialOffsets
example (t : Lambda.Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (a b : Context) (loop : RawLoop (encode n t).net es a b) :
    Context.SameShell ((encode n t).net.label loop.binder).index a b :=
  encode_rawLoop_shell t n es a b loop
example (t : Lambda.Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (a b c : Context) (loop : RawLoop (encode n t).net es a b) :
    ∃ d, Nonempty (BindingLoop (encode n t).net es c d) :=
  encode_rawLoop_transparent t n es loop c
example (t : Lambda.Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (a b : Context) (loop : RawLoop (encode n t).net es a b) :
    NoBinderRevisit (encode n t).net loop.binder es := encode_rawLoop_no_revisit t n es a b loop
#print axioms encode_rawLoop_composition
#print axioms corrected_program_all_runs
#print axioms encode_rawLoop_shell
#print axioms encode_rawLoop_binding
#print axioms encode_rawLoop_transparent
#print axioms lambdaUsed_rawLoop_child
#print axioms lambdaUnused_no_rawLoop
#print axioms lambdaUsed_rawLoop_events
#print axioms encode_rawLoop_no_revisit
example (t : Lambda.Term) (n : Nat) (x : FV t) (a b : Context)
    (p : LocalPath (encode n t).net (.inl ()) (.inr x) a b) :
    ∃ occurrence : FreeOccurrence t x.val, allEvents (encode n t).net p.edges=occurrence.shape.events n :=
  encode_FV_shape t n x p
example (t : Lambda.Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (a b : Context) (loop : RawLoop (encode n t).net es a b) :
    ∃ shape : Shape, eventsOfEdges (encode n t).net es=shape.events ((encode n t).net.label loop.binder).index ∧
      shape.offset=bracketOffset (encode n t).net es ∧
      b=a.replace ((encode n t).net.label loop.binder).index
        ((a.tail (((encode n t).net.label loop.binder).index+shape.offset)).cons
          (shape.level a ((encode n t).net.label loop.binder).index)) := encode_rawLoop_offset t n es a b loop
example : (Shape.base [false]).markerWords.length=1 := rfl
example : (Shape.lower (.base []) [true]).markerWords.length=2 := rfl
example : ((Shape.lower (.base []) [true]).events 0).head?=some (.cro 1) := rfl
#print axioms encode_FV_shape
#print axioms encode_rawLoop_shape
#print axioms encode_rawLoop_corrected
#print axioms InitialLabelling.bra_count
#print axioms encode_rawLoop_offset
#print axioms corrected_initial_invariants
end Lamping.Checks.Paths






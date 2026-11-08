import Lamping.Checks.Soundness
import Lamping.Lamping.PairedStreamHighTails
import Lamping.Lamping.PairedStreamCuts
import Lamping.Lamping.FixedBetaDetourBlocks
namespace Lamping.Checks.Phase5Review.PairedHighTails
open AG Graph Lambda SoundnessInitialInsertion

private theorem one_stream : BetaDetourBlocks (encode 0 identityApp).net
    (inserted 0) (input 0) (output 0) 1 := by
  have body := (bodyLabels 0).ordinary_of_forward _ (bodyForward 0)
  have tailLabels : Labelling (encode 0 identityApp).net ((edge 0).argEnd::suffix 0) (output 0) (output 0) :=
    .cons (.transparent (argumentW 0) false (output 0)) (.single _ _)
  have finish : (pre 0++(edge 0).principal++loopEdges 0).getLast?=
      some ((encode 0 identityApp).net.wire (.inl ⟨(edge 0).lam,(edge 0).lamBind⟩)) := by
    simp only [List.getLast?_append,(actualLoop 0).finish,Option.some_or]
    rfl
  have stream := BetaDetourBlocks.append_backward (encode 0 identityApp).net (edge 0)
    body finish rfl (tailLabels.detour_blocks _)
  simpa only [List.append_assoc,List.singleton_append] using stream

def replacement : Context := (Context.empty.cons (.o .empty)).cons (.star .empty)

/-- A genuine eleven-segment source stream has one reverse beta block.
The new high-tail theorem transports a concrete nonempty replacement while
retaining that exact physical list and count. -/
theorem actual_one_block_high_tail_replacement :
    ∃ width, (input 0).tail width=(output 0).tail 1 ∧
      BetaDetourBlocks (encode 0 identityApp).net (inserted 0)
        ((input 0).replace width replacement) ((output 0).replace 1 replacement) 1 := by
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  obtain ⟨width,_lower,tails,sync⟩ := one_stream.high_tail_sync_indexed
    flow (root:=.inl ()) rfl balance rfl 0 1
    (by
      intro e head
      have same : e=(.inr (.inl (.inl ())) : Endpoint (encode 0 identityApp).net) := Option.some.inj head.symm
      rw [same]
      rfl)
    (by
      intro e head
      have same : e=(.inr (.inl (.inl ())) : Endpoint (encode 0 identityApp).net) := Option.some.inj head.symm
      rw [same]
      rfl)
    (by
      intro e last
      have actual : (inserted 0).getLast?=some ((encode 0 identityApp).net.wire
          (.inl ⟨.inr (.inr (.inl ())),(.inl ())⟩)) := rfl
      have same := Option.some.inj (last.symm.trans actual)
      rw [same,balance.wiring]
      exact (AtProperRole.lamCtx (g:=(encode 0 identityApp).net) (root:=.inl ())
        (.inr (.inr (.inl ()))) (.inl ()) 1 rfl HEq.rfl).incoming_depth balance (.inl ()) trivial)
  exact ⟨width,tails,sync replacement⟩

example : replacement.get 0=.star .empty ∧ replacement.get 1=.o .empty := ⟨rfl,rfl⟩
example : (inserted 0).length=11 := rfl

/-- Cut the same actual stream immediately after its full reverse route.
Both pieces retain the selected argument departure and one extracted seam. -/
theorem actual_positive_argument_cut :
    ∃ middle leftCount rightCount,
      BetaDetourBlocks (encode 0 identityApp).net
        ((pre 0++(edge 0).principal++loopEdges 0++(edge 0).reverseRoute)++[(edge 0).argEnd])
        (input 0) middle leftCount ∧
      BetaDetourBlocks (encode 0 identityApp).net ((edge 0).argEnd::suffix 0)
        middle (output 0) rightCount ∧ 1=leftCount+rightCount := by
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  exact one_stream.split_at_positive flow (root:=.inl ()) rfl
    (pre 0++(edge 0).principal++loopEdges 0++(edge 0).reverseRoute)
    (edge 0).argEnd (suffix 0)
    (by simp only [inserted,List.append_assoc,List.singleton_append])
    ((AtProperRole.appArg (root:=.inl ()) (edge 0).app (edge 0).appArg 0 (edge 0).appLabel (edge 0).appArg_role).outgoing_flow
      trivial flow.nodes initialBoundaryPolarity flow.vertices rfl)
#print axioms one_stream
#print axioms actual_one_block_high_tail_replacement
#print axioms actual_positive_argument_cut
end Lamping.Checks.Phase5Review.PairedHighTails

namespace Lamping.Checks.Phase5Review.FixedBetaProvenance
open AG Graph Lambda SoundnessBetaAncestor

/-- The actual reduced I I path crosses both reconnections. Its same-site
ancestor has a positive fixed block count, and the production provenance
chain extracts the real old redex and bound-variable word at the first block. -/
theorem actual_fixed_stream_reaches_old_fiber :
    ∃ (edge : BetaEdge actualBetaSite.net) (old : List (Endpoint actualBetaSite.net)) (count : Nat),
      0<count ∧ FixedBetaDetourBlocks edge old Context.empty (Context.empty.cons .empty) count ∧
      ∃ (before : RootAccess actualBetaSite.net (.inl ())) (tail : List (Endpoint actualBetaSite.net))
        (seam : Context) (remaining : Nat) (redex : RedexOcc identityApp) (q : Path),
        count=remaining+1 ∧ old=before.val++edge.reverseRoute++tail ∧
        Labelling actualBetaSite.net before.val Context.empty seam ∧
        tail.head?=some edge.argEnd ∧ FixedBetaDetourBlocks edge tail seam (Context.empty.cons .empty) remaining ∧
        redex.val∈actualBetaSite.betaSyntaxFiber (.inl ()) identityApp ∧
        accessWord actualBetaSite.net before.val=redex.val++[.fn,.body]++q ∧
        subtermAt identityApp (accessWord actualBetaSite.net before.val)=some (.var (binderDepth q)) := by
  obtain ⟨edge,old,geometry,relation,_labels,first,_last⟩ := actual_ancestor Context.empty
  obtain ⟨count,stream⟩ := relation.fixed_detour_blocks actualBetaSite geometry ((reduced_labels Context.empty).plug_decomposition _ _)
  have entry : (.inr (.inr (.inl (.inr false)))) ∈ reduced.map (plugEnd _ _).invFun := by
    exact List.mem_map.mpr ⟨.inr (.inr (.inr (.inr false),true)),by simp [reduced],rfl⟩
  have positive := stream.erase.positive_count actualBetaSite.net actualFlow (.inl ()) rfl first edge
    (relation.reverse_occurs actualBetaSite entry)
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have matching := betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  obtain ⟨principal⟩ := actualBetaSite.actionPrincipal_exists
  exact ⟨edge,old,count,positive,stream,
    actualBetaSite.fixed_stream_old_fiber geometry principal actualFlow (.inl ()) rfl matching transparency
      stream positive first⟩

#print axioms actual_fixed_stream_reaches_old_fiber
end Lamping.Checks.Phase5Review.FixedBetaProvenance

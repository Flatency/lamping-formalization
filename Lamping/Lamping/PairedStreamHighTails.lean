import Lamping.Lamping.BetaDetourBlocks
import Lamping.Lamping.HighTailTransport
import Lamping.Lamping.FlowRootPaths
import Lamping.Lamping.ReducedOutsideProperRoles
namespace Lamping.AG
open Graph
private theorem shift_tail_sync (P : Context → Context → Prop)
    {a b : Context} {m n : Nat} (tails : a.tail m=b.tail n)
    (sync : ∀ replacement,P (a.replace m replacement) (b.replace n replacement)) (extra : Nat) :
    a.tail (m+extra)=b.tail (n+extra) ∧
      ∀ replacement,P (a.replace (m+extra) replacement) (b.replace (n+extra) replacement) := by
  constructor
  · ext k
    have same := congrArg (fun c : Context => c.get (extra+k)) tails
    simpa only [Context.tail,Nat.add_assoc] using same
  · intro replacement
    have left : a.replace m ((b.tail n).replace extra replacement)=a.replace (m+extra) replacement := by
      rw [←tails,←Context.replace_nested,Context.replace_tail]
    have right : b.replace n ((b.tail n).replace extra replacement)=b.replace (n+extra) replacement := by
      rw [←Context.replace_nested,Context.replace_tail]
    have changed := sync ((b.tail n).replace extra replacement)
    rw [left,right] at changed
    exact changed
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Bool} {heights : B → Int} {root : B}

/-- Tail synchronization of a GIVEN finite paired stream. A whole reverse
block is identity-labelled and connects lambda-binding to app-argument at
the same height. No labels or stream extension are invented. -/
theorem BetaDetourBlocks.high_tail_sync_indexed
    (flow : FlowBalance g boundary) (positive : boundary root=true)
    (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    {es : List (Endpoint g)} {a b : Context} {count : Nat}
    (path : BetaDetourBlocks g es a b count) (m n : Nat)
    (firstPositive : ∀ e,es.head?=some e → flowEndpoint g flow.nodes boundary flow.vertices e=true)
    (firstDepth : ∀ e,es.head?=some e → endpointDepth g balance.nodes heights balance.vertices e=(m : Int))
    (lastDepth : ∀ e,es.getLast?=some e → endpointDepth g balance.nodes heights balance.vertices e=(n : Int)) :
    ∃ width,m≤width ∧ a.tail width=b.tail n ∧
      ∀ replacement,BetaDetourBlocks g es (a.replace width replacement) (b.replace n replacement) count := by
  induction count using Nat.strongRecOn generalizing es a b m with
  | ind count ih =>
    by_cases zero : count=0
    · subst count
      have labels := path.zero_ordinary g
      have forward := labels.forward_of_flow flow firstPositive
      obtain ⟨width,lower,tails,sync⟩ := labels.high_tail_sync balance forward m n firstDepth lastDepth
      exact ⟨width,lower,tails,fun replacement => (sync replacement).detour_blocks g⟩
    · obtain ⟨edge,pre,tail,seam,remaining,countEq,decomp,prefixLabels,preEnd,tailHead,rest⟩ :=
        path.first_backward g (by omega)
      have prePositive : ∀ e,pre.head?=some e → flowEndpoint g flow.nodes boundary flow.vertices e=true := by
        intro e head
        apply firstPositive e
        simp only [decomp,List.head?_append,head,Option.some_or]
      have preDepth : ∀ e,pre.head?=some e → endpointDepth g balance.nodes heights balance.vertices e=(m : Int) := by
        intro e head
        apply firstDepth e
        simp only [decomp,List.head?_append,head,Option.some_or]
      have preForward := prefixLabels.forward_of_flow flow prePositive
      have preLast : ∀ e,pre.getLast?=some e →
          endpointDepth g balance.nodes heights balance.vertices e=((edge.index+1 : Nat) : Int) := by
        intro e last
        have equal := Option.some.inj (last.symm.trans preEnd)
        rw [equal,balance.wiring]
        exact (AtProperRole.lamBind edge.lam edge.lamBind edge.index edge.lamLabel edge.lamBind_role).incoming_depth balance root trivial
      have tailPositive : ∀ e,tail.head?=some e → flowEndpoint g flow.nodes boundary flow.vertices e=true := by
        intro e head
        have equal := Option.some.inj (head.symm.trans tailHead)
        rw [equal]
        exact (AtProperRole.appArg edge.app edge.appArg edge.index edge.appLabel edge.appArg_role).outgoing_flow
          trivial flow.nodes boundary flow.vertices positive
      have tailDepth : ∀ e,tail.head?=some e →
          endpointDepth g balance.nodes heights balance.vertices e=((edge.index+1 : Nat) : Int) := by
        intro e head
        have equal := Option.some.inj (head.symm.trans tailHead)
        rw [equal]
        exact (AtProperRole.appArg edge.app edge.appArg edge.index edge.appLabel edge.appArg_role).outgoing_depth balance root rootDepth trivial
      have tailLast : ∀ e,tail.getLast?=some e → endpointDepth g balance.nodes heights balance.vertices e=(n : Int) := by
        intro e last
        apply lastDepth e
        simp only [decomp,List.getLast?_append,last,Option.some_or]
      obtain ⟨tailWidth,tailLower,tailEq,tailSync⟩ := ih remaining (by omega) rest (edge.index+1)
        tailPositive tailDepth tailLast
      obtain ⟨preWidth,preLower,preEq,preSync⟩ := prefixLabels.high_tail_sync balance preForward m (edge.index+1) preDepth preLast
      let extra := tailWidth-(edge.index+1)
      have widthEq : edge.index+1+extra=tailWidth := by dsimp [extra]; omega
      obtain ⟨shiftEq,shiftSync⟩ := shift_tail_sync (Labelling g pre) preEq preSync extra
      rw [widthEq] at shiftEq shiftSync
      refine ⟨preWidth+extra,by omega,shiftEq.trans tailEq,?_⟩
      intro replacement
      have changed := (tailSync replacement).append_backward g edge (shiftSync replacement) preEnd tailHead
      simpa only [decomp,countEq] using changed

/-- Reset a GIVEN paired rooted application prefix to a same-shell output,
retaining the literal stream and its count. This constructs a new input,
not existence of arbitrary partial paths or arbitrary proper-source I. -/
theorem BetaDetourBlocks.relabel_app_prefix_indexed
    (flow : FlowBalance g boundary) (positive : boundary root=true)
    (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    (edge : BetaEdge g) {pre : List (Endpoint g)} {a seam target : Context} {count : Nat}
    (path : BetaDetourBlocks g pre a seam count)
    (rooted : pre.head?=some (.inr (.inl root)))
    (finish : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (shell : Context.SameShell edge.index seam target) :
    ∃ newInput,BetaDetourBlocks g pre newInput target count := by
  obtain ⟨width,_lower,_tails,sync⟩ := path.high_tail_sync_indexed flow positive balance rootDepth 0 edge.index
    (by intro e head; have equal := Option.some.inj (head.symm.trans rooted); rw [equal]; exact positive)
    (by intro e head; have equal := Option.some.inj (head.symm.trans rooted); rw [equal]; exact rootDepth)
    (by
      intro e last
      have equal := Option.some.inj (last.symm.trans finish)
      rw [equal,balance.wiring]
      exact (AtProperRole.appCtx edge.app edge.appCtx edge.index edge.appLabel edge.appCtx_role).incoming_depth balance root trivial)
  refine ⟨a.replace width (target.tail edge.index),?_⟩
  have changed := sync (target.tail edge.index)
  rw [Context.replace_of_sameShell seam target edge.index shell] at changed
  exact changed
end
end Lamping.AG

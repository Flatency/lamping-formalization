import Lamping.Lamping.ActionParentFunctionBranches
import Lamping.Lamping.ActionPrincipalInternal
import Lamping.Lamping.OutsideControlWriterSuffix
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}
private def departureToken : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []
private theorem child_token {node : N} {ctx departure : Port (g.label node).sort}
    (roles : SyntaxChildPorts (g.label node).sort ctx departure step) :
    arrivalWord g (.inl ⟨node,departure⟩)=[step] := by
  change departureToken (g.label node).sort departure=[step]
  have actual {kind : Kind} {ctx departure : Port kind}
      (roles : SyntaxChildPorts kind ctx departure step) : departureToken kind departure=[step] := by
    cases roles <;> rfl
  exact actual roles

theorem SourcePortRealizes.syntax_departure_word
    (realizes : SourcePortRealizes current g root port endpoint)
    (role : SourceDeparture term step port) : arrivalWord g endpoint=[step] := by
  cases role <;> cases realizes with
  | departure _ actualRole _ _ roles _ => cases actualRole; exact child_token roles
end
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
theorem PathSite.lambda_internal_tokens_empty
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (passive : s.passive=.lam)
    (index : Bool⊕(V×Bool)) : arrivalWord site.net (site.internalEnd index)=[] := by
  cases index with
  | inl d =>
    cases d with
    | false =>
      cases s with
      | beta n => rcases control with h|h|h <;> cases h
      | fanCancel | croCancel | braCancel | fanAction | croAction | braAction => rfl
    | true => cases s <;> cases passive <;> rfl
  | inr point => rfl

theorem SourceEdgeFragment.lambda_first_noninternal
    {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (passive : s.passive=.lam) :
    ∀ index,fragment.fromEndpoint≠site.internalEnd index := by
  obtain ⟨env,ctx,sub,occurrence,edgeEq⟩ := fragment.occurrence
  have fromPort : edge.fromPort=ctx := by
    rw [←edgeEq]; cases sub <;> rfl
  rcases occurrence.last_departure with ⟨_root,external⟩ |⟨parent,step,term,_split,_lookup,role⟩
  · have externalPort : edge.fromPort=.external := fromPort.trans external
    have realizes := fragment.fromRealizes
    rw [externalPort] at realizes
    have externalShape : ∀ {endpoint},SourcePortRealizes current site.net root .external endpoint →
        endpoint=.inr (.inl root) := by
      intro endpoint evidence
      cases evidence with
      | external => rfl
      | departure _ role => cases role
    have actual := externalShape realizes
    intro index same
    rw [actual] at same
    cases index with
    | inl d =>
      cases d <;> change Sum.inr (Sum.inl root)=Sum.inl _ at same <;> cases same
    | inr point =>
      change Sum.inr (Sum.inl root)=Sum.inr (Sum.inr _) at same
      cases same
  · have actualRole : SourceDeparture term step edge.fromPort := by rw [fromPort]; exact role
    have token := fragment.fromRealizes.syntax_departure_word actualRole
    intro index same
    rw [same,site.lambda_internal_tokens_empty control passive] at token
    cases token

theorem PathSite.outside_of_noninternal (endpoint : Endpoint site.net)
    (noninternal : ∀ index,endpoint≠site.internalEnd index) :
    ∃ outside,endpoint=site.outsideEnd outside := by
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  cases shape : split endpoint with
  | inl outside =>
    refine ⟨outside,?_⟩
    change endpoint=split.invFun (.inl outside)
    rw [←shape,split.left_inv]
  | inr index =>
    have same : endpoint=site.internalEnd index := by
      change endpoint=split.invFun (.inr index)
      rw [←shape,split.left_inv]
    exact False.elim (noninternal index same)

theorem PathSite.passive_aux_is_outside (q : Aux s.passive) :
    site.outsideEnd (.inr (.inl (.inr (.inr q))))=.inl ⟨.inr (.inr ()),.inr q⟩ := rfl

/-- A supplied actual lambda-context fragment contains its last writer.
The required outside start is derived through the real cut partition. -/
theorem SourceEdgeFragment.lambda_writer_suffix
    {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra) (passive : s.passive=.lam)
    (principal : SiteActionPrincipal site) {a b : Context}
    (whole : Labelling site.net fragment.access.val a b)
    (terminal : fragment.toEndpoint=.inl ⟨.inr (.inr ()),.inl ()⟩) :
    ∃ (pre : List (Endpoint site.net)) (q : Aux s.active) (input middle : Context),
      fragment.segments=pre++principal.edges ∧pre.head?=some fragment.fromEndpoint ∧
      pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr q⟩)) ∧
      Labelling site.net fragment.segments input b ∧Labelling site.net pre input middle ∧
      Traversal s.low (.op s.active) (.inr q) (.inl ()) middle b := by
  obtain ⟨outside,first⟩ := site.outside_of_noninternal fragment.fromEndpoint
    (fragment.lambda_first_noninternal site control passive)
  obtain ⟨input,_before,piece⟩ := fragment.assignments a b whole
  obtain ⟨pre,q,middle,split,head,last,labels,writer⟩ := site.outside_control_writer_suffix
    principal piece outside (fragment.start.trans (congrArg some first))
    (fragment.finish.trans (congrArg (fun e=>some (site.net.wire e)) terminal))
  exact ⟨pre,q,input,middle,split,head.trans (congrArg some first.symm),last,piece,labels,writer⟩

/-- The SAME principal suffix and literal piece determine the auxiliary
physically, even when their assignments and prefix lengths were presented separately. -/
theorem PathSite.writer_suffix_aux_unique
    (principal : SiteActionPrincipal site) {left right : List (Endpoint site.net)}
    {q r : Aux s.active} (same : left++principal.edges=right++principal.edges)
    (leftLast : left.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr q⟩)))
    (rightLast : right.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr r⟩))) : q=r := by
  have prefixes : left=right := List.append_cancel_right same
  have ends := congrArg List.getLast? prefixes
  have wires := Option.some.inj (leftLast.symm.trans (ends.trans rightLast))
  have endpoints := congrArg site.net.wire.mate wires
  simp only [Pairing.involutive] at endpoints
  exact Sum.inr.inj (eq_of_heq (sigma_snd_heq (Sum.inl.inj endpoints)))
end
end Lamping.AG
import Lamping.Lamping.SourceRouteEvaluation
import Lamping.Lamping.MatchingSelectedDegreeRealization
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}

private def departureWord : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []
private theorem function_word {kind : Kind} {p q : Port kind}
    (roles : SyntaxChildPorts kind p q .fn) : departureWord kind q=[.fn] := by
  cases roles
  rfl
private theorem function_departure_token {appId : Labelled.Label} {e : Endpoint g}
    (realizes : SourcePortRealizes original g root (.appFn appId) e) : arrivalWord g e=[.fn] := by
  cases realizes with
  | departure lookup role parent word roles finish =>
    cases role
    exact function_word roles

private theorem marked_suffix_cannot_be_later {xs ys tail : List (Endpoint g)} {e : Endpoint g}
    (split : xs=tail++ys) (empty : accessWord g xs=[])
    (head : ys.head?=some e) (token : arrivalWord g e≠[]) : tail=[] := by
  cases tail with
  | nil => rfl
  | cons first rest =>
    obtain ⟨after,same⟩ := List.head?_eq_some_iff.mp head
    rw [split,List.cons_append,accessWord,List.flatMap_append] at empty
    have suffixEmpty := (List.append_eq_nil_iff.mp empty).2
    rw [same,List.flatMap_cons] at suffixEmpty
    exact False.elim (token (List.append_eq_nil_iff.mp suffixEmpty).1)

/-- The same assigned root access has only one suffix starting with a
syntax-emitting departure and carrying no later syntax token. This keeps
actual segment ordinals; endpoint equality alone is not used as path equality. -/
private theorem marked_suffix_unique {before before' xs ys : List (Endpoint g)} {e f : Endpoint g}
    (literal : before++xs=before'++ys) (leftEmpty : accessWord g xs=[]) (rightEmpty : accessWord g ys=[])
    (leftHead : xs.head?=some e) (rightHead : ys.head?=some f)
    (leftToken : arrivalWord g e≠[]) (rightToken : arrivalWord g f≠[]) : xs=ys := by
  rcases List.append_eq_append_iff.mp literal with ⟨tail,_prefix,split⟩ | ⟨tail,_prefix,split⟩
  · have empty := marked_suffix_cannot_be_later split leftEmpty rightHead rightToken
    simpa only [empty,List.nil_append] using split
  · have empty := marked_suffix_cannot_be_later split rightEmpty leftHead leftToken
    exact (by simpa only [empty,List.nil_append] using split : ys=xs).symm

/-- For a genuine original function edge, any two real fragment choices
have the same literal segments. INIT locks the old occurrence and Matches
its whole access; the nonempty fn token then locks the cut ordinal. -/
theorem SourceEdgeFragment.function_segments_unique
    {appId degree : Labelled.Label} {p q : Path}
    (initial : INIT original) (matching : Matches g root original.erase)
    (left : SourceEdgeFragment original g root ⟨degree,.appFn appId,.lamContext degree⟩ p)
    (right : SourceEdgeFragment original g root ⟨degree,.appFn appId,.lamContext degree⟩ q) :
    left.segments=right.segments := by
  obtain ⟨env,ctx,sub,atLeft,leftEdge⟩ := left.occurrence
  obtain ⟨env',ctx',sub',atRight,rightEdge⟩ := right.occurrence
  have leftLabel : sub.label=degree := by
    have atom := congrArg SourceEdge.atom leftEdge
    cases sub <;> exact atom
  have rightLabel : sub'.label=degree := by
    have atom := congrArg SourceEdge.atom rightEdge
    cases sub' <;> exact atom
  have positions := LTerm.subterm_label_injective original initial.2 atLeft.lookup atRight.lookup
    (leftLabel.trans rightLabel.symm)
  have same := matching.accessWord_injective (left.word.trans (positions.trans right.word.symm))
  have whole : left.before++left.segments=right.before++right.segments := by
    rw [←left.literal,←right.literal,same]
  apply marked_suffix_unique whole left.emptyWord right.emptyWord left.start right.start
  · rw [function_departure_token left.fromRealizes]; simp
  · rw [function_departure_token right.fromRealizes]; simp
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}

/-- Every shared actual atom selector evaluates every permitted ORIGINAL
degree to the SAME fixed graph-site principal word. No equality-of-fragment
or generation certificate is supplied to connect syntax and graph beta. -/
theorem PathSite.selected_principal_word
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original)
    (matching : Matches site.net root original.erase) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
      ∀ selection : SourceEdgeSelection original site.net root,∀ degree,
      SelectedDegree original (site.betaSyntaxFiber root original.erase) degree →
      selection.evalLabel beta degree=beta.principal := by
  obtain ⟨beta,app,lam,allDegrees⟩ := site.selected_degree_principal_fragment matching
  refine ⟨beta,app,lam,?_⟩
  intro selection degree selected
  obtain ⟨name,appId,body,argument,_member,_lookup,fragment,principal⟩ := allDegrees degree selected
  obtain ⟨n,atomic⟩ := selected.atomic initial
  let cell : {edge : SourceEdge // edge∈sourceEdges [] .external original} :=
    ⟨⟨degree,.appFn appId,.lamContext degree⟩,fragment.source_member⟩
  let picked := (selection.chosen cell).2
  have segments := picked.function_segments_unique initial matching fragment
  have word : selection.evalLabel beta degree=selection.atomWord n := by
    rw [atomic]; rfl
  exact word.trans ((selection.atomWord_cell initial cell atomic).trans (segments.trans principal))
end
end Lamping.AG


import Lamping.Lamping.SourceRouteEvaluation
namespace Lamping.Lambda.Labelled.LTerm
private theorem sourceTrail_single_child {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {t parent child : LTerm} {p : Path} {step : Step}
    (lookup : t.subterm p=some parent) (atChild : parent.subterm [step]=some child) :
    t.sourceTrail atoms overWord underWord (p++[step])=
      (t.sourceTrail atoms overWord underWord p).map (fun pre => pre++child.label.sourceWord atoms overWord underWord) := by
  rw [sourceTrail_split atoms overWord underWord lookup [step]]
  have atRoot := sourceTrail_split atoms overWord underWord lookup []
  simp only [List.append_nil] at atRoot
  rw [atRoot]
  cases parent <;> cases step <;> simp only [subterm] at atChild
  all_goals cases atChild
  all_goals cases t.sourceStem atoms overWord underWord p <;>
    simp [sourceTrail,label,List.append_assoc]
end Lamping.Lambda.Labelled.LTerm
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm} {beta : BetaEdge g}
private def evaluatedHere
    (walk : PhysicalSourceWalk original root beta ctx stamp finish)
    (image : SyntaxTrailImage original root beta env ctx target [] target finish walk.edges) :
    PhysicalSyntaxTrail original root beta env ctx target [] target finish :=
  { edges := walk.edges,fromEndpoint := walk.fromEndpoint,toEndpoint := walk.toEndpoint
    fromRealizes := walk.fromRealizes,toRealizes := walk.toRealizes,head := walk.head,last := walk.last
    forward := walk.forward,image := image }
private def evaluatedPrepend
    (initial : INIT original) (matching : Matches g root original.erase)
    (left : PhysicalSourceWalk original root beta ctx stamp mid)
    (right : PhysicalSyntaxTrail original root beta childEnv childCtx child p sub finish)
    (step : SourceSyntaxStep mid childCtx s)
    (image : SyntaxTrailImage original root beta env ctx target whole sub finish (left.edges++right.edges)) :
    PhysicalSyntaxTrail original root beta env ctx target whole sub finish := by
  have direction := step.direction initial matching left.toRealizes right.fromRealizes
  exact {
    edges := left.edges++right.edges,fromEndpoint := left.fromEndpoint,toEndpoint := right.toEndpoint
    fromRealizes := left.fromRealizes,toRealizes := right.toRealizes
    head := by simp only [List.head?_append,left.head,Option.some_or]
    last := by simp only [List.getLast?_append,right.last,Option.some_or]
    forward := left.forward.splice left.last right.forward right.head (by simpa only [g.wire.involutive] using direction)
    image := image }
/-- A labelled path cannot leave a boundary in its interior. -/
private theorem no_boundary_suffix {pre tail : List (Endpoint g)} {a b : Context}
    (nonempty : pre≠[]) (labels : Labelling g (pre++(.inr (.inl root))::tail) a b) : False := by
  induction pre generalizing a with
  | nil => exact nonempty rfl
  | cons e pre ih =>
    cases pre with
    | nil => cases labels with | cons turn _ => exact turn.reverse.not_boundary root rfl
    | cons f pre => cases labels with | cons _ rest => exact ih (by simp) rest

/-- Two cuts immediately before the last nonempty syntax token have exactly
identical literal prefixes. No injectivity of arbitrary graph walks is used. -/
private theorem last_token_prefix_unique {X Y : Type} (token : X → List Y)
    {pre other tail suffix : List X} {e f : X}
    (split : pre++e::tail=other++f::suffix)
    (first : token e≠[]) (second : token f≠[])
    (afterFirst : tail.flatMap token=[]) (afterSecond : suffix.flatMap token=[]) : pre=other := by
  induction pre generalizing other with
  | nil =>
    cases other with
    | nil => rfl
    | cons h other =>
      have rest := (List.cons.inj split).2
      rw [rest] at afterFirst
      exact False.elim (second ((List.flatMap_eq_nil_iff.mp afterFirst) f (List.mem_append_right other (by simp))))
  | cons h pre ih =>
    cases other with
    | nil =>
      have rest := (List.cons.inj split).2.symm
      rw [rest] at afterSecond
      exact False.elim (first ((List.flatMap_eq_nil_iff.mp afterSecond) e (List.mem_append_right pre (by simp))))
    | cons k other =>
      have parts := List.cons.inj split
      cases parts.1
      exact congrArg (h::·) (ih parts.2)

/-- A real fragment beginning at the root boundary is the entire original
access. The assertion follows from ordinary labelling, not endpoint equality. -/
theorem SourceEdgeFragment.external_segments
    (fragment : SourceEdgeFragment original g root edge p) (external : edge.fromPort=.external) :
    fragment.segments=fragment.access.val := by
  have realizes := fragment.fromRealizes
  rw [external] at realizes
  have start : fragment.segments.head?=some (.inr (.inl root)) := by
    generalize eq : fragment.fromEndpoint=endpoint at realizes
    cases realizes with
    | external => exact fragment.start.trans (congrArg some eq)
    | departure _ role => cases role
  have before : fragment.before=[] := by
    classical
    by_cases empty : fragment.before=[]
    · exact empty
    · apply False.elim
      obtain ⟨a,b,labels⟩ := fragment.access.property.1.1
      rw [fragment.literal] at labels
      cases segmentsEq : fragment.segments with
      | nil => rw [segmentsEq] at start; cases start
      | cons e tail =>
        have same : e=.inr (.inl root) := Option.some.inj (by simpa only [segmentsEq,List.head?_cons] using start)
        rw [segmentsEq,same] at labels
        exact no_boundary_suffix empty labels
  simpa only [before,List.nil_append] using fragment.literal.symm
private def syntaxDepartureToken : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []
private theorem child_departure_token {kind : Kind} {ctx departure : Port kind}
    (roles : SyntaxChildPorts kind ctx departure step) : syntaxDepartureToken kind departure=[step] := by
  cases roles <;> rfl
private theorem physical_child_token {node : N} {ctx departure : Port (g.label node).sort}
    (roles : SyntaxChildPorts (g.label node).sort ctx departure step) :
    arrivalWord g (.inl ⟨node,departure⟩)=[step] := by
  change syntaxDepartureToken (g.label node).sort departure=[step]
  exact child_departure_token roles
private theorem source_departure_token
    (role : SourceDeparture term step port) (realizes : SourcePortRealizes original g root port endpoint) :
    arrivalWord g endpoint=[step] := by
  cases role <;> cases realizes with
  | departure _ role _ _ roles _ => cases role; exact physical_child_token roles
/-- Recover the real parent prefix from the fragment's ordinary rooted
access and its LAST syntax token. Physical endpoint agreement alone would
not imply this literal prefix equality. -/
theorem SourceEdgeFragment.child_prefix
    (fragment : SourceEdgeFragment original g root edge p)
    (matching : Matches g root original.erase)
    (role : SourceDeparture term step edge.fromPort) (parent : RootAccess g root)
    (word : p=accessWord g parent.val++[step]) :
    fragment.before=parent.val ∧ fragment.access.val=parent.val++fragment.segments := by
  have whole : accessWord g fragment.access.val=accessWord g parent.val++[step] := fragment.word.trans word
  obtain ⟨actualParent,node,ctx,departure,tail,roles,parentWord,_,split⟩ :=
    fragment.access.before_syntax_token (accessWord g parent.val) step whole
  have parentEq : actualParent=parent := matching.accessWord_injective parentWord
  rw [parentEq] at split
  have token : arrivalWord g (.inl ⟨node,departure⟩)=[step] := physical_child_token roles
  have tailTokens : tail.flatMap (arrivalWord g)=[] := by
    have tokens := whole
    rw [split,accessWord_append g parent.val _ parent.property.1.1.walk.nonempty,
      List.flatMap_cons,token] at tokens
    have after := List.append_cancel_left tokens
    exact (List.cons.inj (by simpa only [List.singleton_append] using after)).2
  have beforeEq : fragment.before=parent.val := by
    have firstToken := source_departure_token role fragment.fromRealizes
    cases segmentsEq : fragment.segments with
    | nil => have impossible := fragment.start; rw [segmentsEq] at impossible; cases impossible
    | cons first rest =>
      have firstEq : first=fragment.fromEndpoint := Option.some.inj (by simpa only [segmentsEq,List.head?_cons] using fragment.start)
      have restTokens : rest.flatMap (arrivalWord g)=[] := by
        have empty := fragment.emptyWord
        simpa only [segmentsEq,accessWord] using empty
      have both : fragment.before++first::rest=parent.val++(.inl ⟨node,departure⟩)::tail := by
        rw [←segmentsEq,←fragment.literal,split]
      exact last_token_prefix_unique (arrivalWord g) both
        (by rw [firstEq,firstToken]; simp) (by rw [token]; simp) restTokens tailTokens
  exact ⟨beforeEq,by simpa only [beforeEq] using fragment.literal⟩
private theorem source_edge_atom (env : List Labelled.Label) (ctx : SourcePort) (t : LTerm) :
    (sourceEdge env ctx t).atom=t.label := by cases t <;> rfl
private theorem source_edge_from (env : List Labelled.Label) (ctx : SourcePort) (t : LTerm) :
    (sourceEdge env ctx t).fromPort=ctx := by cases t <;> rfl
/-- INIT locates the original occurrence, after which Matches identifies
its actual rooted access. No endpoint/path converse is used. -/
theorem SourceEdgeFragment.access_eq_at
    (fragment : SourceEdgeFragment original g root (sourceEdge env ctx sub) q)
    (initial : INIT original) (matching : Matches g root original.erase)
    (site : SourceSubterm [] .external original p env ctx sub)
    (access : RootAccess g root) (word : accessWord g access.val=p) : fragment.access=access := by
  obtain ⟨actualEnv,actualCtx,actualSub,atActual,edgeEq⟩ := fragment.occurrence
  have labels : actualSub.label=sub.label := by
    have eq := congrArg SourceEdge.atom edgeEq
    simpa only [source_edge_atom] using eq
  have paths := LTerm.subterm_label_injective original initial.2 atActual.lookup site.lookup labels
  exact matching.accessWord_injective (fragment.word.trans (paths.trans word.symm))

private theorem selected_word_access (selection : SourceEdgeSelection original g root)
    (initial : INIT original) (matching : Matches g root original.erase)
    (site : SourceSubterm [] .external original p env ctx sub)
    (access : RootAccess g root) (word : accessWord g access.val=p) :
    ∃ q,∃ fragment : SourceEdgeFragment original g root (sourceEdge env ctx sub) q,
      selection.evalLabel beta sub.label=fragment.segments ∧ fragment.access=access := by
  have member : sourceEdge env ctx sub∈sourceEdges [] .external original :=
    site.edges_subset _ (by cases sub <;> simp [sourceEdges,sourceEdge])
  let cell : {edge : SourceEdge // edge∈sourceEdges [] .external original} := ⟨sourceEdge env ctx sub,member⟩
  let fragment := (selection.chosen cell).2
  refine ⟨_,fragment,?_,fragment.access_eq_at initial matching site access word⟩
  obtain ⟨n,atomic⟩ := initial.1 _ (LTerm.label_mem_of_subterm site.lookup)
  change sub.label.sourceWord selection.atomWord beta.principal beta.reverseRoute=_
  rw [atomic]
  exact selection.atomWord_cell initial cell (by simpa only [cell,source_edge_atom] using atomic)

private theorem reverse_path_induction {P : Path → Prop} (nil : P [])
    (append_singleton : ∀ p step,P p → P (p++[step])) : ∀ p,P p := by
  have all : ∀ reverse : Path,P reverse.reverse := by
    intro reverse
    induction reverse with
    | nil => exact nil
    | cons step reverse ih => simpa only [List.reverse_cons] using append_singleton reverse.reverse step ih
  intro p
  simpa only [List.reverse_reverse] using all p.reverse
/-- For ANY shared selector of real fragments, original syntax evaluates
to the supplied ordinary rooted access, literally. The proof cuts actual
last-token prefixes and uses Matches word injectivity, not endpoint equality. -/
theorem SourceEdgeSelection.original_access_evaluation (selection : SourceEdgeSelection original g root)
    (initial : INIT original) (matching : Matches g root original.erase)
    {p : Path} {sub : LTerm} (lookup : original.subterm p=some sub)
    (access : RootAccess g root) (word : accessWord g access.val=p) :
    original.sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some access.val := by
  induction p using reverse_path_induction generalizing sub access with
  | nil =>
    have eq : original=sub := by simpa only [LTerm.subterm,Option.some.injEq] using lookup
    subst sub
    obtain ⟨q,fragment,eval,actual⟩ := selected_word_access (beta:=beta) selection initial matching
      (SourceSubterm.nil (t:=original) (env:=[]) (ctx:=.external)) access word
    have segments := fragment.external_segments (source_edge_from _ _ _)
    have evaluated : selection.evalLabel beta original.label=access.val := by rw [eval,segments,actual]
    cases original <;> exact congrArg some evaluated
  | append_singleton parentPath step ih =>
    have parentChild := lookup
    rw [LTerm.subterm_append] at parentChild
    cases atParent : original.subterm parentPath with
    | none => rw [atParent] at parentChild; cases parentChild
    | some parentTerm =>
      rw [atParent,Option.bind_some] at parentChild
      let parentPosition : Position original.erase := ⟨parentPath,by rw [←LTerm.erase_subterm,atParent]; rfl⟩
      obtain ⟨parent,parentWord,_⟩ := Matches.observation g matching parentPosition
      have evaluatedParent := ih atParent parent parentWord
      obtain ⟨env,ctx,site⟩ := SourceSubterm.of_lookup original lookup [] .external
      obtain ⟨q,fragment,eval,actual⟩ := selected_word_access (beta:=beta) selection initial matching site access word
      rcases site.last_departure with ⟨empty,_⟩ | ⟨oldParent,oldStep,oldTerm,path,oldLookup,role⟩
      · have length := congrArg List.length empty; simp at length
      · have reverse := congrArg List.reverse path
        simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] at reverse
        have parts := List.cons.inj reverse
        have parents : parentPath=oldParent := List.reverse_inj.mp parts.2
        have steps : step=oldStep := parts.1
        subst oldParent; subst oldStep
        have terms : parentTerm=oldTerm := Option.some.inj (atParent.symm.trans oldLookup)
        subst oldTerm
        have cutPair := fragment.child_prefix matching (by simpa only [source_edge_from] using role) parent
          (by simpa only [actual,word,parentWord] using fragment.word.symm.trans (congrArg (accessWord g) (congrArg Subtype.val actual)))
        rw [LTerm.sourceTrail_single_child selection.atomWord beta.principal beta.reverseRoute atParent parentChild,
          evaluatedParent,Option.map_some]
        change some (parent.val++selection.evalLabel beta sub.label)=some access.val
        rw [eval,←cutPair.2,actual]
/-- The same atom choices are used at EVERY ancestor edge, not separately
chosen existential walks at each syntax node. -/
theorem SourceEdgeSelection.syntax_evaluation
    (selection : SourceEdgeSelection original g root)
    (initial : INIT original) (matching : Matches g root original.erase)
    (allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original) allowed start stamp finish →
      ∃ walk : PhysicalSourceWalk original root beta start stamp finish,walk.edges=selection.evalLabel beta stamp)
    (routes : SelectedTermRoutes (sourceEdges [] .external original) allowed env ctx target)
    (lookup : target.subterm p=some sub) :
    ∃ finish,∃ trail : PhysicalSyntaxTrail original root beta env ctx target p sub finish,
      target.sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some trail.edges := by
  induction routes generalizing p sub with
  | var route =>
    cases p with
    | nil =>
      cases lookup
      obtain ⟨walk,word⟩ := allWalks route
      exact ⟨_,evaluatedHere walk (.var walk.image),congrArg some word.symm⟩
    | cons step rest => cases step <;> simp [LTerm.subterm] at lookup
  | lam route body ih =>
    cases p with
    | nil =>
      cases lookup
      obtain ⟨walk,word⟩ := allWalks route
      exact ⟨_,evaluatedHere walk (.lam walk.image),congrArg some word.symm⟩
    | cons step rest =>
      cases step with
      | fn | arg => simp [LTerm.subterm] at lookup
      | body =>
        obtain ⟨finish,child,childEq⟩ := ih lookup
        obtain ⟨walk,word⟩ := allWalks route
        refine ⟨finish,evaluatedPrepend initial matching walk child .body (.body walk.image child.image),?_⟩
        simp only [LTerm.sourceTrail,childEq,Option.map_some]
        exact congrArg some (congrArg (·++child.edges) word.symm)
  | app route fn arg fnIH argIH =>
    cases p with
    | nil =>
      cases lookup
      obtain ⟨walk,word⟩ := allWalks route
      exact ⟨_,evaluatedHere walk (.app walk.image),congrArg some word.symm⟩
    | cons step rest =>
      cases step with
      | body => simp [LTerm.subterm] at lookup
      | fn =>
        obtain ⟨finish,child,childEq⟩ := fnIH lookup
        obtain ⟨walk,word⟩ := allWalks route
        refine ⟨finish,evaluatedPrepend initial matching walk child .fn (.fn walk.image child.image),?_⟩
        simp only [LTerm.sourceTrail,childEq,Option.map_some]
        exact congrArg some (congrArg (·++child.edges) word.symm)
      | arg =>
        obtain ⟨finish,child,childEq⟩ := argIH lookup
        obtain ⟨walk,word⟩ := allWalks route
        refine ⟨finish,evaluatedPrepend initial matching walk child .arg (.arg walk.image child.image),?_⟩
        simp only [LTerm.sourceTrail,childEq,Option.map_some]
        exact congrArg some (congrArg (·++child.edges) word.symm)
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
/-- Actual development, one original INIT, and one finite selector provide
whole physical trails whose literal words equal the SAME partial evaluator.
No generatedness or whole-path labelling is asserted. -/
theorem PathSite.relative_development_shared_syntax_evaluation
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original target : LTerm} (initial : INIT original) (closed : Closed original.erase)
    (matching : Matches site.net root original.erase)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (labels : History ps original target) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
    ∃ selection : SourceEdgeSelection original site.net root,
    ∀ {p sub},target.subterm p=some sub →
    ∃ finish,∃ trail : PhysicalSyntaxTrail original root beta [] .external target p sub finish,
      target.sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some trail.edges := by
  obtain ⟨beta,app,lam,selection,walks⟩ := site.shared_source_route_evaluation initial closed matching
  exact ⟨beta,app,lam,selection,fun lookup => SourceEdgeSelection.syntax_evaluation selection initial matching walks
    (relative_development_selected_routes initial relative labels) lookup⟩
end
end Lamping.AG

namespace Lamping.Lambda.Labelled.LTerm
/-- Public access to the existing literal child evaluator equation. The
private finite proof remains the single implementation. -/
theorem sourceTrail_single_child_evaluation {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {t parent child : LTerm} {p : Path} {step : Step}
    (lookup : t.subterm p=some parent) (atChild : parent.subterm [step]=some child) :
    t.sourceTrail atoms overWord underWord (p++[step])=
      (t.sourceTrail atoms overWord underWord p).map (fun pre => pre++child.label.sourceWord atoms overWord underWord) :=
  sourceTrail_single_child atoms overWord underWord lookup atChild
end Lamping.Lambda.Labelled.LTerm

import Lamping.Lamping.ActionSourceFrontiers
import Lamping.Lamping.ActionPrincipalInternal
import Lamping.Lamping.ControlOnlyConnections
import Lamping.Lamping.MatchingRedexEndpointUniqueness

namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

/-- A source-path partition with shared exit occurrences: recursion starts at
that same exit, not at an invented edge after it. Only complete forward or
backward principal crossings are permitted. The count is derived data in Prop,
not a supplied rank or desired target transport. -/
inductive WholeControlVisits (principal : SiteActionPrincipal site) :
    List (Endpoint site.net) → Nat → Prop where
  | single (e : Endpoint cut) : WholeControlVisits principal [site.outsideEnd e] 0
  | outside (e f : Endpoint cut) (tail : List (Endpoint site.net)) {n : Nat}
      (turn : ∃ a b,LabelledTurn cut ((cut).wire e) f a b)
      (rest : WholeControlVisits principal (site.outsideEnd f::tail) n) :
      WholeControlVisits principal (site.outsideEnd e::site.outsideEnd f::tail) n
  | cross (p : Aux s.active) (q : Aux s.passive) (tail : List (Endpoint site.net)) {n : Nat}
      (rest : WholeControlVisits principal ((.inl ⟨.inr (.inr ()),.inr q⟩)::tail) n) :
      WholeControlVisits principal (principal.crossing site p q++tail) (n+1)
  | backward (p : Aux s.active) (q : Aux s.passive) (tail : List (Endpoint site.net)) {n : Nat}
      (rest : WholeControlVisits principal ((.inl ⟨.inr (.inl ()),.inr p⟩)::tail) n) :
      WholeControlVisits principal (reverseEdges (principal.crossing site p q)++tail) (n+1)

private theorem visit_outside_turn {e : Endpoint cut} {f : Endpoint site.net} {a b : Context}
    (turn : LabelledTurn site.net (site.net.wire (site.outsideEnd e)) f a b) :
    (∃ next,f=site.outsideEnd next ∧LabelledTurn cut ((cut).wire e) next a b) ∨
      ∃ entry,(cut).wire e=.inr (.inl (.inr entry)) := by
  rw [site.outsideEnd_wire] at turn
  generalize (cut).wire e=endpoint at turn ⊢
  rcases endpoint with ⟨node,p⟩|((boundary|frontier)|⟨vertex,direction⟩)
  · change LabelledTurn site.net (.inl ⟨.inl node,p⟩) f a b at turn
    obtain ⟨q,same,rule⟩ := turn.from_node (.inl node) p rfl
    exact Or.inl ⟨.inl ⟨node,q⟩,same,.node node p q rule⟩
  · change LabelledTurn site.net (.inr (.inl boundary)) f a b at turn
    cases turn
  · exact Or.inr ⟨frontier,rfl⟩
  · change LabelledTurn site.net (.inr (.inr (.inl vertex,direction))) f a b at turn
    cases turn
    exact Or.inl ⟨.inr (.inr (vertex,!direction)),rfl,.transparent vertex direction a⟩

private theorem control_passive_impossible
    (control : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (p q : Aux s.passive) {a b : Context}
    (labels : Labelling site.net (site.passiveCanonical p q) a b) : False := by
  have localLabels := (site.passiveCanonical_labels_iff p q a b).mp labels
  have rule : Traversal s.high (.op s.passive) (.inr p) (.inr q) a b := by
    cases localLabels with
    | cons turn last => cases last; cases turn with | node node p q rule => exact rule
  have reject (op : Op) (p q : Aux op)
      (isControl : op=.fan ∨op=.cro ∨op=.bra)
      (traversal : Traversal s.high (.op op) (.inr p) (.inr q) a b) : False := by
    rcases isControl with rfl|rfl|rfl <;> exact traversal.aux_aux
  exact reject s.passive p q control rule

/-- All visits, including repeated visits to the same physical node and W
vertex, split into complete nonoverlapping crossing blocks. Existing typed
frontier reflection supplies the exact principal route and labelled suffix.
Outside endpoints rule out stopping partway through an internal component. -/
theorem PathSite.whole_control_visits
    (activeControl : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (principal : SiteActionPrincipal site)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first last : Endpoint cut) (head : es.head?=some (site.outsideEnd first))
    (finish : es.getLast?=some (site.outsideEnd last)) :
    ∃ n,WholeControlVisits site principal es n := by
  induction bound : es.length using Nat.strongRecOn generalizing es a b first last with
  | ind size ih =>
    cases labels with
    | single e a =>
      have same := Option.some.inj head
      subst e
      exact ⟨0,.single first⟩
    | @cons e f tail a seam b turn remaining =>
      have same := Option.some.inj head
      subst e
      rcases visit_outside_turn site turn with ⟨next,departure,localTurn⟩|⟨entry,arrival⟩
      · subst f
        have tailTyped : ∃ k,accessKind site.net (site.outsideEnd next::tail)=some k := by
          simpa only [accessKind,List.getLast?_cons_cons] using typed
        have tailFinish : (site.outsideEnd next::tail).getLast?=some (site.outsideEnd last) := by
          simpa only [List.getLast?_cons_cons] using finish
        obtain ⟨n,rest⟩ := ih (site.outsideEnd next::tail).length
          (by simp only [List.length_cons] at bound ⊢; omega) remaining tailTyped next last rfl tailFinish rfl
        exact ⟨n,.outside first next tail ⟨a,seam,localTurn⟩ rest⟩
      · have entering : site.outsideEnd first=site.net.wire (site.outsideEnd (.inr (.inl (.inr entry)))) := by
          have same : site.net.wire (site.outsideEnd first)=site.outsideEnd (.inr (.inl (.inr entry))) := by
            rw [site.outsideEnd_wire,arrival]
          have inverse := congrArg site.net.wire.mate same
          simpa only [Pairing.involutive] using inverse
        obtain ⟨exit,front,rest,middle,split,route,frontLast,frontLabels,suffixLabels⟩ :=
          site.typed_frontier_source_route activeControl principal entry (.cons turn remaining) typed
            (by simpa only [List.head?_cons] using congrArg some entering) last finish (by simp)
        have frontBound := route.length_ge_two site
        have lastSame : (front++rest).getLast?=
            (site.outsideEnd (.inr (.inl (.inr exit)))::rest).getLast? := by
          obtain ⟨pre,lastEq⟩ := List.getLast?_eq_some_iff.mp frontLast
          rw [lastEq,List.append_assoc,List.singleton_append]
          simp only [List.getLast?_append,List.getLast?_cons,Option.some_or]
        have suffixTyped : ∃ k,accessKind site.net
            (site.outsideEnd (.inr (.inl (.inr exit)))::rest)=some k := by
          simpa only [accessKind,split,lastSame] using typed
        have suffixFinish : (site.outsideEnd (.inr (.inl (.inr exit)))::rest).getLast?=
            some (site.outsideEnd last) := by
          simpa only [split,lastSame] using finish
        have smaller : (site.outsideEnd (.inr (.inl (.inr exit)))::rest).length<size := by
          have lengths := congrArg List.length split
          simp only [List.length_cons,List.length_append] at lengths bound ⊢
          omega
        obtain ⟨n,visits⟩ := ih _ smaller suffixLabels suffixTyped
          (.inr (.inl (.inr exit))) last rfl suffixFinish rfl
        rw [split]
        cases route with
        | cross p q => exact ⟨n+1,.cross p q rest visits⟩
        | backward p q => exact ⟨n+1,.backward p q rest visits⟩
        | passive p q => exact False.elim (control_passive_impossible site passiveControl p q frontLabels)

/-- Zero crossing count leaves only actual outside endpoints. This will let a
selected principal occurrence witness the strict (nonzero) branch separately. -/
theorem WholeControlVisits.outside_of_zero {principal : SiteActionPrincipal site} {es n}
    (visits : WholeControlVisits site principal es n) (zero : n=0) :
    ∀ e∈es,∃ outside,e=site.outsideEnd outside := by
  induction visits with
  | single e =>
    intro x member
    have same := List.mem_singleton.mp member
    exact ⟨e,same⟩
  | outside e f tail turn rest ih =>
    intro x member
    rcases List.mem_cons.mp member with same|member
    · exact ⟨e,same⟩
    · exact ih zero x member
  | cross p q tail rest ih => omega
  | backward p q tail rest ih => omega

/-- A real occurrence of the selected internal principal forces a positive
number of full visits; no simple-path or distinct-visit premise is needed. -/
theorem WholeControlVisits.positive_of_principal_occurs
    {principal : SiteActionPrincipal site} {es n}
    (visits : WholeControlVisits site principal es n)
    (occurs : (.inl ⟨.inr (.inl ()),.inl ()⟩ : Endpoint site.net)∈es) : 0<n := by
  by_cases zero : n=0
  · obtain ⟨outside,same⟩ := visits.outside_of_zero site zero _ occurs
    exact False.elim (site.internal_outside_ne (.inl false) outside same)
  · omega

private theorem proper_node_kept
    (activeControl : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (node : K⊕(Unit⊕Unit)) (op : Op) (proper : op=.app ∨op=.lam) (i : Nat)
    (lab : site.net.label node=label op i) : ∃ keptNode,node=.inl keptNode := by
  cases node with
  | inl node => exact ⟨node,rfl⟩
  | inr node =>
    cases node with
    | inl u =>
      cases u
      have same : s.active=op := Kind.op.inj (congrArg Graph.Label.sort lab)
      rcases proper with rfl|rfl <;>
        rcases activeControl with h|h|h <;> rw [h] at same <;> cases same
    | inr u =>
      cases u
      have same : s.passive=op := Kind.op.inj (congrArg Graph.Label.sort lab)
      rcases proper with rfl|rfl <;>
        rcases passiveControl with h|h|h <;> rw [h] at same <;> cases same

private theorem lambda_principal_kind (actual : Graph.Label signature)
    (port : Port actual.sort) (i : Nat) (lab : actual=label .lam i)
    (role : HEq port (Sum.inl () : Port (.op .lam))) :
    portKind actual.sort port=some .lam := by
  subst actual
  have same : port=Sum.inl () := eq_of_heq role
  subst port
  rfl

/-- THIS whole redex connection is in the decomposition domain automatically:
its app and lambda nodes are retained when both selected site nodes are
controls, and its genuine lambda finish supplies typedness. No outside-end,
simple-visit, full-I or desired target assumption is provided by the caller. -/
theorem RedexConnection.whole_control_visits
    (activeControl : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (principal : SiteActionPrincipal site) (connection : RedexConnection site.net) :
    ∃ n,WholeControlVisits site principal connection.edges n := by
  rcases connection with ⟨app,lam,appPort,lamPort,appIndex,lamIndex,appLabel,lamLabel,
    appPrincipal,lamPrincipal,es,proper,start,finish,emptyWord⟩
  obtain ⟨appNode,appEq⟩ := proper_node_kept site activeControl passiveControl app .app
    (Or.inl rfl) appIndex appLabel
  obtain ⟨lamNode,lamEq⟩ := proper_node_kept site activeControl passiveControl lam .lam
    (Or.inr rfl) lamIndex lamLabel
  subst app
  subst lam
  let first : Endpoint cut := .inl ⟨appNode,appPort⟩
  let last : Endpoint cut := (cut).wire (.inl ⟨lamNode,lamPort⟩)
  have lastImage : site.outsideEnd last=site.net.wire (.inl ⟨.inl lamNode,lamPort⟩) :=
    (site.outsideEnd_wire (.inl ⟨lamNode,lamPort⟩)).symm
  have typed : ∃ k,accessKind site.net es=some k := by
    refine ⟨.lam,?_⟩
    simp only [accessKind,finish,Option.bind_some,Pairing.involutive]
    exact lambda_principal_kind _ lamPort lamIndex lamLabel lamPrincipal
  obtain ⟨a,b,labels⟩ := proper.1
  exact site.whole_control_visits activeControl passiveControl principal labels typed first last
    start (finish.trans (congrArg some lastImage.symm))

/-- Retain the genuine syntax occurrence/root provenance without changing the
connection supplied by that exact source access. -/
theorem ActualRedexAccess.whole_control_visits
    (activeControl : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (principal : SiteActionPrincipal site) {root : B} {t : Lambda.Term}
    {redex : Lambda.RedexOcc t} (source : ActualRedexAccess site.net root redex) :
    ∃ n,WholeControlVisits site principal source.connection.edges n :=
  source.connection.whole_control_visits site activeControl passiveControl principal

/-- An actually selected occurrence of the principal corridor is one of the
complete visits. This proves nonempty decomposition, not a desired rewrite
rank or target-fragment equation. -/
theorem RedexConnection.selected_whole_control_visits
    (activeControl : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (principal : SiteActionPrincipal site) (connection : RedexConnection site.net)
    (before after : List (Endpoint site.net))
    (split : connection.edges=(before++principal.edges)++after) :
    ∃ n,0<n ∧WholeControlVisits site principal connection.edges n := by
  obtain ⟨n,visits⟩ := connection.whole_control_visits site activeControl passiveControl principal
  have occurs : (.inl ⟨.inr (.inl ()),.inl ()⟩ : Endpoint site.net)∈connection.edges := by
    obtain ⟨tail,routeEq⟩ := List.head?_eq_some_iff.mp principal.first
    rw [split,routeEq]
    simp
  exact ⟨n,visits.positive_of_principal_occurs site occurs,visits⟩
end
end Lamping.AG

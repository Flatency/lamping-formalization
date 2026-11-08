import Lamping.Lamping.ActionOutsideSourceBlocks
import Lamping.Lamping.ActionCanonicalAssembly
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem outside_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have mapped := congrArg split same
  change split (split.invFun (.inl e))=split (split.invFun (.inl f)) at mapped
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

private theorem outside_turn {e : Endpoint cut} {f : Endpoint site.net} {a b : Context}
    (turn : LabelledTurn site.net (site.net.wire (site.outsideEnd e)) f a b) :
    (∃ next,f=site.outsideEnd next ∧LabelledTurn cut ((cut).wire e) next a b) ∨
    ∃ frontier,(cut).wire e=.inr (.inl (.inr frontier)) := by
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

private theorem last_append {T : Type} (pre tail : List T) (nonempty : tail≠[]) :
    (pre++tail).getLast?=tail.getLast? := by
  cases result : tail.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp result))
  | some e => simp only [List.getLast?_append,result,Option.some_or]

private theorem overlap_labels {pre route : List (Endpoint site.net)} {e : Endpoint site.net} {a b c : Context}
    (parent : Labelling site.net (pre++[e]) a b) (labels : Labelling site.net route b c)
    (head : route.head?=some e) : Labelling site.net (pre++route) a c := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp head
  rw [split] at labels ⊢
  exact parent.join labels

private theorem overlap_root {T : Type} {pre route : List T} {e root : T}
    (before : (pre++[e]).head?=some root) (after : route.head?=some e) :
    (pre++route).head?=some root := by
  cases pre with
  | nil => simpa only [List.nil_append,List.head?_cons] using after.trans before
  | cons x pre => simpa only [List.cons_append,List.head?_cons] using before

/-- Finite source-to-RHS expansion of an existing LABELLED path with retained
outside endpoints. A real labelled root prefix is accumulated at every source
block, so the application passive branch is obtained from its true syntax
function child. The same canonical residual is constructed, never assumed. -/
theorem PathSite.expand_labelled_source_outside (action : IsAction s)
    (principal : SiteActionPrincipal site)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b)
    (first last : Endpoint cut) (head : es.head?=some (site.outsideEnd first))
    (finish : es.getLast?=some (site.outsideEnd last))
    (pre : List (Endpoint site.net)) (rootInput : Context)
    (parentLabels : Labelling site.net (pre++[site.outsideEnd first]) rootInput a)
    (rooted : (pre++[site.outsideEnd first]).head?=some (.inr (.inl root))) :
    ∃ raw,PlugExcursions cut s.right.net raw a b ∧ActionCanonicalBlocks site principal raw es ∧
      raw.head?=some (.inl first) ∧raw.getLast?=some (.inl last) := by
  have control : s.active=.fan ∨s.active=.cro ∨s.active=.bra := by
    cases action with
    | fan => exact Or.inl rfl
    | cro => exact Or.inr (Or.inl rfl)
    | bra => exact Or.inr (Or.inr rfl)
  induction bound : es.length using Nat.strongRecOn generalizing es a b first last pre with
  | ind size ih =>
    cases labels with
    | single e a =>
      have same := Option.some.inj head
      subst e
      have lastEq := outside_injective site (Option.some.inj finish)
      subst last
      exact ⟨[.inl first],.single first a,.single first,rfl,rfl⟩
    | @cons e f tail a seam b turn remaining =>
      have same := Option.some.inj head
      subst e
      rcases outside_turn site turn with ⟨next,departure,localTurn⟩|⟨entry,arrival⟩
      · subst f
        have tailFinish : (site.outsideEnd next::tail).getLast?=some (site.outsideEnd last) := by
          simpa only [List.getLast?_cons_cons] using finish
        have newLabels : Labelling site.net ((pre++[site.outsideEnd first])++[site.outsideEnd next]) rootInput seam := by
          simpa only [List.append_assoc,List.singleton_append] using parentLabels.join (.cons turn (.single _ _))
        have newRoot : ((pre++[site.outsideEnd first])++[site.outsideEnd next]).head?=some (.inr (.inl root)) := by
          cases pre with
          | nil => exact rooted
          | cons e pre => exact rooted
        obtain ⟨raw,path,residual,start,endEq⟩ := ih (site.outsideEnd next::tail).length
          (by simp only [List.length_cons] at bound ⊢; omega) remaining next last rfl tailFinish
          (pre++[site.outsideEnd first]) newLabels newRoot rfl
        obtain ⟨post,rawSplit⟩ := List.head?_eq_some_iff.mp start
        rw [rawSplit] at path residual
        refine ⟨.inl first::.inl next::post,.outside localTurn path,.outside residual,rfl,?_⟩
        simpa only [rawSplit,List.getLast?_cons_cons] using endEq
      · have entering : site.outsideEnd first=site.net.wire (site.outsideEnd (.inr (.inl (.inr entry)))) := by
          have same : site.net.wire (site.outsideEnd first)=site.outsideEnd (.inr (.inl (.inr entry))) := by
            rw [site.outsideEnd_wire,arrival]
          have inverse := congrArg site.net.wire.mate same
          simpa only [Pairing.involutive] using inverse
        obtain ⟨exit,front,rest,middle,split,route,frontLast,frontLabels,suffixLabels⟩ :=
          site.outside_frontier_source_route control principal entry (.cons turn remaining)
            (by simpa only [List.head?_cons] using congrArg some entering) last finish (by simp)
        have frontBound := route.length_ge_two site
        have frontNonempty : front≠[] := by intro empty; rw [empty] at frontBound; cases frontBound
        have frontHead : front.head?=some (site.outsideEnd first) := by
          cases front with
          | nil => exact False.elim (frontNonempty rfl)
          | cons e front => exact (congrArg List.head? split).symm
        have currentPositive : flowEndpoint site.net flow.nodes boundary flow.vertices (site.outsideEnd first)=true :=
          parentLabels.root_positive_departures flow root rooted positive _
            (List.mem_of_getLast? (by simp))
        have frontForward := frontLabels.forward_of_flow flow (by
          intro e atHead
          have equal := Option.some.inj (atHead.symm.trans frontHead)
          subst e
          exact currentPositive)
        obtain ⟨localPath,canonical⟩ := route.expand site action matching inputs flow positive parentLabels rooted
          (by simpa only [List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.some_or] using frontHead.symm)
          frontLabels frontForward
        obtain ⟨frontBefore,frontEq⟩ := List.getLast?_eq_some_iff.mp frontLast
        have newLabels : Labelling site.net ((pre++frontBefore)++[site.outsideEnd (.inr (.inl (.inr exit)))]) rootInput middle := by
          have combined := overlap_labels site parentLabels frontLabels frontHead
          simpa only [frontEq,List.append_assoc] using combined
        have newRoot : ((pre++frontBefore)++[site.outsideEnd (.inr (.inl (.inr exit)))]).head?=some (.inr (.inl root)) := by
          have combined := overlap_root rooted frontHead
          simpa only [frontEq,List.append_assoc] using combined
        have sameLast : (front++rest).getLast?=(site.outsideEnd (.inr (.inl (.inr exit)))::rest).getLast? := by
          rw [frontEq,List.append_assoc,List.singleton_append]
          exact last_append frontBefore _ (by simp)
        have suffixFinish : (site.outsideEnd (.inr (.inl (.inr exit)))::rest).getLast?=some (site.outsideEnd last) := by
          simpa only [split,sameLast] using finish
        have smaller : (site.outsideEnd (.inr (.inl (.inr exit)))::rest).length<size := by
          have lengths := congrArg List.length split
          simp only [List.length_cons,List.length_append] at lengths bound ⊢
          omega
        obtain ⟨raw,path,residual,start,endEq⟩ := ih _ smaller suffixLabels
          (.inr (.inl (.inr exit))) last rfl suffixFinish (pre++frontBefore) newLabels newRoot rfl
        obtain ⟨post,rawSplit⟩ := List.head?_eq_some_iff.mp start
        rw [rawSplit] at path residual
        refine ⟨.inl first::(localPath.edges.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::post),
          .through localPath arrival path,?_,rfl,?_⟩
        · rw [split,frontEq,List.append_assoc,List.singleton_append]
          exact .through localPath.edges frontBefore (by simpa only [frontEq] using canonical)
            (by simpa only [frontEq] using frontHead) residual
        · have lastEq := last_append (.inl first::localPath.edges.map Sum.inr)
            (.inl (.inr (.inl (.inr exit)))::post) (by simp)
          simpa only [List.cons_append] using lastEq.trans (by simpa only [rawSplit] using endEq)

/-- Physical wrapper for a source root path with an actual outside terminal.
No typed endpoint is required: physical outside endpoints prohibit an internal short stop. The target is built by finite source decomposition, not assumed as a
reference. This statement does not claim its terminal is a proper observation. -/
theorem PathSite.action_labelled_source_outside_expansion (action : IsAction s)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {old : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net old a b)
    (rooted : old.head?=some (.inr (.inl root)))
    (last : Endpoint cut) (finish : old.getLast?=some (site.outsideEnd last)) :
    ∃ (principal : SiteActionPrincipal site) (es : List (Endpoint site.reduce)),
      Labelling site.reduce es a b ∧
      ActionCanonicalBlocks site principal (es.map (plugEnd (cut).label s.right.net.label).invFun) old ∧
      es.head?=some (.inr (.inl root)) ∧
      es.getLast?=some (AG.plugLeft cut s.right.net last) := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨raw,path,residual,first,lastEq⟩ := site.expand_labelled_source_outside action principal matching inputs
    flow positive labels (.inr (.inl (.inl root))) last rooted finish [] a (.single _ _) rfl
  refine ⟨principal,raw.map (plugEnd (cut).label s.right.net.label),(path.labelling cut s.right.net).actual cut s.right.net,
    ?_,?_,?_⟩
  · simpa only [List.map_map,Function.comp_def,(plugEnd (cut).label s.right.net.label).left_inv,List.map_id_fun'] using residual
  · rw [List.head?_map,first]
    rfl
  · rw [List.getLast?_map,lastEq]
    rfl
end
end Lamping.AG


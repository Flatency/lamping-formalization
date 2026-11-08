import Lamping.Lamping.ActionCanonicalAssembly
import Lamping.Lamping.ActionCrossingReplay
import Lamping.Lamping.ActionPassiveReplay
namespace Lamping.AG
open Graph Lambda
section
variable {f : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))

private theorem node_rule {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    {g : Net signature N D U} {node : N} {p q : Port (g.label node).sort} {a b : Context}
    (turn : LabelledTurn g (.inl ⟨node,p⟩) (.inl ⟨node,q⟩) a b) :
    Traversal (g.label node).index (g.label node).sort p q a b := by
  cases turn with | node node p q rule => exact rule

/-- The complete passive block's real auxiliary passage forces application.
The root prefix selects its forward context port, rather than assuming it. -/
theorem FanCanonicalLocal.rooted_replay {principal : SiteActionPrincipal site}
    {rhs old} (relation : FanCanonicalLocal site principal rhs old)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (rootPolarity : boundary root=true)
    {pre : List (Endpoint site.net)} {referenceInput referenceSeam referenceOutput : Context}
    (referenceParent : Labelling site.net pre referenceInput referenceSeam)
    (rooted : pre.head?=some (.inr (.inl root))) (finish : pre.getLast?=old.head?)
    (original : Labelling (fanRight f i j) rhs referenceSeam referenceOutput)
    {requested current output : Context} (parent : Labelling site.net pre requested current)
    (labels : Labelling site.net old current output) : Labelling (fanRight f i j) rhs current output := by
  cases relation with
  | cross branch q =>
    exact fanAction_cross_replay f i j lt branch q current output
      ((principal.crossing_labels_iff site branch q current output).mp labels)
  | backward branch q =>
    have source := labels.reverse
    rw [reverseEdges_involutive] at source
    exact (fanAction_cross_replay f i j lt branch q output current
      ((principal.crossing_labels_iff site branch q output current).mp source)).reverse
  | passive branch p q =>
    have localLabels := (site.passiveCanonical_labels_iff p q current output).mp labels
    cases localLabels with
    | cons passage last =>
      cases last
      have rule := node_rule passage
      have app : f=.app := by
        cases f with
        | app => rfl
        | lam => exact False.elim rule.aux_aux
        | fan => exact False.elim rule.aux_aux
        | cro => exact False.elim rule.aux_aux
        | bra => exact False.elim rule.aux_aux
      subst f
      have ends : pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)) := finish
      have positive := referenceParent.root_positive_departures flow root rooted rootPolarity _ (List.mem_of_getLast? ends)
      rw [flow.wiring] at positive
      change (!p)=true at positive
      have port : p=false := by
        cases p <;> simp_all
      subst p
      have arg : q=true := by
        cases q
        · exact False.elim (rule.distinct rfl)
        · rfl
      subst q
      have same : current=output := rule.auxiliary_context
      subst output
      cases original with
      | cons first after =>
        obtain ⟨port,out,inverseRule⟩ := first.from_node (.inr false) (.inl ()) rfl
        have portEq : port=.inr branch := by
          have ports := sigma_snd_heq (Sum.inl.inj out)
          exact (eq_of_heq ports).symm
        subst port
        obtain ⟨middle,newRule⟩ := site.matched_control_input_of_prefix matching indep flow rootPolarity
          (Or.inl rfl) rfl pre appCtx HEq.rfl referenceInput referenceSeam _ referenceParent rooted ends
          branch inverseRule requested current parent
        exact fanAction_passive_replay i j branch current middle newRule
end
section
variable {f : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))

theorem cro_canonical_rooted_replay {principal : SiteActionPrincipal site}
    {rhs old} (relation : UnaryCanonicalLocal site (Bij.refl _) principal rhs old)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (rootPolarity : boundary root=true)
    {pre : List (Endpoint site.net)} {referenceInput referenceSeam referenceOutput : Context}
    (referenceParent : Labelling site.net pre referenceInput referenceSeam)
    (rooted : pre.head?=some (.inr (.inl root))) (finish : pre.getLast?=old.head?)
    (original : Labelling (unaryRightCore .cro f (Bij.refl _) i (j-1)) rhs referenceSeam referenceOutput)
    {requested current output : Context} (parent : Labelling site.net pre requested current)
    (labels : Labelling site.net old current output) :
    Labelling (unaryRightCore .cro f (Bij.refl _) i (j-1)) rhs current output := by
  cases relation with
  | cross q =>
    exact croAction_cross_replay f i j lt q current output
      ((principal.crossing_labels_iff site () q current output).mp labels)
  | backward q =>
    have source := labels.reverse
    rw [reverseEdges_involutive] at source
    exact (croAction_cross_replay f i j lt q output current
      ((principal.crossing_labels_iff site () q output current).mp source)).reverse
  | passive p q =>
    have localLabels := (site.passiveCanonical_labels_iff p q current output).mp labels
    cases localLabels with
    | cons passage last =>
      cases last
      have rule := node_rule passage
      have app : f=.app := by
        cases f with
        | app => rfl
        | lam => exact False.elim rule.aux_aux
        | fan => exact False.elim rule.aux_aux
        | cro => exact False.elim rule.aux_aux
        | bra => exact False.elim rule.aux_aux
      subst f
      have ends : pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)) := finish
      have positive := referenceParent.root_positive_departures flow root rooted rootPolarity _ (List.mem_of_getLast? ends)
      rw [flow.wiring] at positive
      change (!p)=true at positive
      have port : p=false := by cases p <;> simp_all
      subst p
      have arg : q=true := by
        cases q
        · exact False.elim (rule.distinct rfl)
        · rfl
      subst q
      have same : current=output := rule.auxiliary_context
      subst output
      cases original with
      | cons first after =>
        obtain ⟨port,out,inverseRule⟩ := first.from_node (.inr false) (.inl ()) rfl
        have portEq : port=.inr () := by
          have ports := sigma_snd_heq (Sum.inl.inj out)
          exact (eq_of_heq ports).symm
        subst port
        obtain ⟨middle,newRule⟩ := site.matched_control_input_of_prefix matching indep flow rootPolarity
          (Or.inr (Or.inl rfl)) rfl pre appCtx HEq.rfl referenceInput referenceSeam _ referenceParent rooted ends
          () inverseRule requested current parent
        exact unaryAction_passive_replay .cro (Bij.refl _) i (j-1) current middle newRule
end
section
variable {f : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V))

theorem bra_canonical_rooted_replay {principal : SiteActionPrincipal site}
    {rhs old} (relation : UnaryCanonicalLocal site (Bij.refl _) principal rhs old)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (rootPolarity : boundary root=true)
    {pre : List (Endpoint site.net)} {referenceInput referenceSeam referenceOutput : Context}
    (referenceParent : Labelling site.net pre referenceInput referenceSeam)
    (rooted : pre.head?=some (.inr (.inl root))) (finish : pre.getLast?=old.head?)
    (original : Labelling (unaryRightCore .bra f (Bij.refl _) i (j+1)) rhs referenceSeam referenceOutput)
    {requested current output : Context} (parent : Labelling site.net pre requested current)
    (labels : Labelling site.net old current output) :
    Labelling (unaryRightCore .bra f (Bij.refl _) i (j+1)) rhs current output := by
  cases relation with
  | cross q =>
    exact braAction_cross_replay f i j lt q current output
      ((principal.crossing_labels_iff site () q current output).mp labels)
  | backward q =>
    have source := labels.reverse
    rw [reverseEdges_involutive] at source
    exact (braAction_cross_replay f i j lt q output current
      ((principal.crossing_labels_iff site () q output current).mp source)).reverse
  | passive p q =>
    have localLabels := (site.passiveCanonical_labels_iff p q current output).mp labels
    cases localLabels with
    | cons passage last =>
      cases last
      have rule := node_rule passage
      have app : f=.app := by
        cases f with
        | app => rfl
        | lam => exact False.elim rule.aux_aux
        | fan => exact False.elim rule.aux_aux
        | cro => exact False.elim rule.aux_aux
        | bra => exact False.elim rule.aux_aux
      subst f
      have ends : pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)) := finish
      have positive := referenceParent.root_positive_departures flow root rooted rootPolarity _ (List.mem_of_getLast? ends)
      rw [flow.wiring] at positive
      change (!p)=true at positive
      have port : p=false := by cases p <;> simp_all
      subst p
      have arg : q=true := by
        cases q
        · exact False.elim (rule.distinct rfl)
        · rfl
      subst q
      have same : current=output := rule.auxiliary_context
      subst output
      cases original with
      | cons first after =>
        obtain ⟨port,out,inverseRule⟩ := first.from_node (.inr false) (.inl ()) rfl
        have portEq : port=.inr () := by
          have ports := sigma_snd_heq (Sum.inl.inj out)
          exact (eq_of_heq ports).symm
        subst port
        obtain ⟨middle,newRule⟩ := site.matched_control_input_of_prefix matching indep flow rootPolarity
          (Or.inr (Or.inr rfl)) rfl pre appCtx HEq.rfl referenceInput referenceSeam _ referenceParent rooted ends
          () inverseRule requested current parent
        exact unaryAction_passive_replay .bra (Bij.refl _) i (j+1) current middle newRule
end
section AllActions
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

theorem ActionCanonicalLocal.rooted_replay {principal : SiteActionPrincipal site}
    {rhs old} (relation : ActionCanonicalLocal site principal rhs old)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (rootPolarity : boundary root=true)
    {pre : List (Endpoint site.net)} {referenceInput referenceSeam referenceOutput : Context}
    (referenceParent : Labelling site.net pre referenceInput referenceSeam)
    (rooted : pre.head?=some (.inr (.inl root))) (finish : pre.getLast?=old.head?)
    (original : Labelling s.right.net rhs referenceSeam referenceOutput)
    {requested current output : Context} (parent : Labelling site.net pre requested current)
    (labels : Labelling site.net old current output) : Labelling s.right.net rhs current output := by
  cases relation with
  | fan relation => exact relation.rooted_replay _ matching indep flow rootPolarity referenceParent rooted finish original parent labels
  | cro relation => exact cro_canonical_rooted_replay _ relation matching indep flow rootPolarity referenceParent rooted finish original parent labels
  | bra relation => exact bra_canonical_rooted_replay _ relation matching indep flow rootPolarity referenceParent rooted finish original parent labels
end AllActions
section Whole
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem reflect_outside {x y : Endpoint cut} {originalA originalB a b : Context}
    (shape : LabelledTurn cut x y originalA originalB)
    (turn : LabelledTurn site.net (site.outsideEnd x) (site.outsideEnd y) a b) :
    LabelledTurn cut x y a b := by
  cases shape with
  | node node p q rule =>
    change LabelledTurn site.net (.inl ⟨.inl node,p⟩) (.inl ⟨.inl node,q⟩) a b at turn
    cases turn with | node node p q actual => exact .node _ _ _ actual
  | transparent vertex direction context =>
    change LabelledTurn site.net (.inr (.inr (.inl vertex,direction)))
      (.inr (.inr (.inl vertex,!direction))) a b at turn
    cases turn
    exact .transparent vertex direction a

private theorem overlap_labels {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    {g : Net signature N D U} {pre route : List (Endpoint g)} {e : Endpoint g} {a b c : Context}
    (before : Labelling g (pre++[e]) a b) (after : Labelling g route b c)
    (head : route.head?=some e) : Labelling g (pre++route) a c := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp head
  rw [split] at after ⊢
  exact before.join after

private theorem overlap_root {T : Type} {pre route : List T} {e root : T}
    (before : (pre++[e]).head?=some root) (after : route.head?=some e) :
    (pre++route).head?=some root := by
  cases pre with
  | nil => simpa only [List.nil_append,List.head?_cons] using after.trans before
  | cons x tail => simpa only [List.cons_append,List.head?_cons] using before

private theorem right_block_unique {L R : Type} {xs ys : List R} {x y : L}
    {tail post : List (L⊕R)}
    (same : xs.map Sum.inr++Sum.inl x::tail=ys.map Sum.inr++Sum.inl y::post) :
    xs=ys ∧x=y ∧tail=post := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => have eqs := List.cons.inj same; exact ⟨rfl,Sum.inl.inj eqs.1,eqs.2⟩
    | cons h ys => cases same
  | cons h xs ih =>
    cases ys with
    | nil => cases same
    | cons k ys =>
      obtain ⟨head,rest⟩ := List.cons.inj same
      have heads := Sum.inr.inj head
      obtain ⟨rfl,rfl,rfl⟩ := ih rest
      subst k
      exact ⟨rfl,rfl,rfl⟩

private theorem outside_view {e f : Endpoint cut} {tail} {a b : Context}
    (shape : PlugExcursions cut s.right.net (.inl e::.inl f::tail) a b) :
    ∃ middle,LabelledTurn cut ((cut).wire e) f a middle ∧
      PlugExcursions cut s.right.net (.inl f::tail) middle b := by
  generalize eqs : (.inl e::.inl f::tail : List (PlugSegment cut s.right.net))=raw at shape
  cases shape with
  | single => cases eqs
  | outside turn after =>
    cases eqs
    exact ⟨_,turn,after⟩
  | through path arrival after =>
    have nonempty := path.labeling.nonempty
    cases split : path.edges with
    | nil => exact False.elim (nonempty split)
    | cons h xs => rw [split,List.map_cons,List.cons_append] at eqs; cases eqs

private theorem through_view {e : Endpoint cut} {exit : s.Frontier} {inside tail} {a b : Context}
    (nonempty : inside≠[])
    (shape : PlugExcursions cut s.right.net
      (.inl e::(inside.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::tail)) a b) :
    ∃ entry middle,inside.head?=some (.inr (.inl entry)) ∧
      inside.getLast?=some (s.right.net.wire (.inr (.inl exit))) ∧
      Labelling s.right.net inside a middle ∧(cut).wire e=.inr (.inl (.inr entry)) ∧
      PlugExcursions cut s.right.net (.inl (.inr (.inl (.inr exit)))::tail) middle b := by
  generalize eqs : (.inl e::(inside.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::tail) :
    List (PlugSegment cut s.right.net))=raw at shape
  cases shape with
  | single =>
    cases inside with
    | nil => exact False.elim (nonempty rfl)
    | cons h xs => cases eqs
  | outside turn after =>
    cases inside with
    | nil => exact False.elim (nonempty rfl)
    | cons h xs => cases eqs
  | @through first entry other post a middle b path arrival after =>
    have initial := List.cons.inj eqs
    have firstEq := Sum.inl.inj initial.1
    subst first
    obtain ⟨edgeEq,exitEq,tailEq⟩ := right_block_unique initial.2
    have exits := Sum.inr.inj (Sum.inl.inj (Sum.inr.inj exitEq))
    subst other
    subst post
    refine ⟨entry,middle,?_,?_,?_,arrival,after⟩
    · rw [edgeEq]; exact path.start
    · rw [edgeEq]; exact path.finish
    · rw [edgeEq]; exact path.labeling

/-- Prefixes are accumulated as real labelled paths from the same root.
Every passive block consequently uses its own actual parent occurrence. -/
theorem ActionCanonicalBlocks.rooted_contract {principal : SiteActionPrincipal site}
    {raw old} (relation : ActionCanonicalBlocks site principal raw old)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (rootPolarity : boundary root=true)
    {originalA originalB : Context} (shape : PlugExcursions cut s.right.net raw originalA originalB)
    {e : Endpoint cut} (head : raw.head?=some (.inl e))
    {pre : List (Endpoint site.net)} {referenceInput requested current output : Context}
    (referenceParent : Labelling site.net (pre++[site.outsideEnd e]) referenceInput originalA)
    (rooted : (pre++[site.outsideEnd e]).head?=some (.inr (.inl root)))
    (parent : Labelling site.net (pre++[site.outsideEnd e]) requested current)
    (labels : Labelling site.net old current output) : PlugExcursions cut s.right.net raw current output := by
  induction relation generalizing originalA originalB e pre referenceInput requested current output with
  | single f =>
    cases labels
    exact .single _ _
  | @outside f h tail old rest ih =>
    have same := Sum.inl.inj (Option.some.inj head)
    subst e
    obtain ⟨originalMiddle,turn,after⟩ := outside_view site shape
    next =>
      have oldHead := rest.head site rfl
      obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp oldHead
      rw [split] at labels
      cases labels with
      | cons newTurn remaining =>
        have actualTurn := newTurn
        rw [site.outsideEnd_wire] at newTurn
        have reflected := reflect_outside site turn newTurn
        have referenceTurn := turn.outsideEnd site
        rw [←site.outsideEnd_wire] at referenceTurn
        have newParent := overlap_labels parent (Labelling.cons actualTurn (.single _ _)) rfl
        have oldParent := overlap_labels referenceParent (Labelling.cons referenceTurn (.single _ _)) rfl
        have newRoot := overlap_root rooted (rfl : [site.outsideEnd f,site.outsideEnd h].head?=some (site.outsideEnd f))
        apply PlugExcursions.outside reflected
        apply ih after rfl
          (pre:=pre++[site.outsideEnd f]) (referenceInput:=referenceInput) (requested:=requested)
        · simpa only [List.append_assoc,List.singleton_append] using oldParent
        · simpa only [List.append_assoc,List.singleton_append] using newRoot
        · simpa only [List.append_assoc,List.singleton_append] using newParent
        · simpa only [split] using remaining
  | @through f exit tail old inside front canonical start rest ih =>
    have same := Sum.inl.inj (Option.some.inj head)
    subst e
    obtain ⟨entry,middle,pathStart,pathFinish,pathLabels,arrival,after⟩ := through_view site canonical.nonempty shape
    next =>
      have oldHead := rest.head site rfl
      obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp oldHead
      rw [split] at labels
      obtain ⟨newMiddle,before,remaining⟩ := labels.split_segment
      have sourceReference := canonical.source_labels site pathLabels
      have newBlock : Labelling s.right.net inside current newMiddle := by
        apply canonical.rooted_replay site matching indep flow rootPolarity referenceParent rooted
          (by simpa only [List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.some_or] using start.symm)
          pathLabels parent
        exact before
      have oldParent := overlap_labels referenceParent sourceReference start
      have newParent := overlap_labels parent before start
      have newRoot := overlap_root rooted start
      apply PlugExcursions.through ⟨inside,pathStart,pathFinish,newBlock⟩ arrival
      apply ih after rfl
        (pre:=pre++front) (referenceInput:=referenceInput) (requested:=requested)
      · simpa only [List.append_assoc] using oldParent
      · simpa only [List.append_assoc] using newRoot
      · simpa only [List.append_assoc] using newParent
      · simpa only [split] using remaining

/-- Choose an actual whole source ancestor once. Any new assignment on that
same ordered ancestor replays on the original reduced root path. -/
theorem PathSite.action_root_relabelling_ancestor (action : IsAction s)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (rootPolarity : boundary root=true)
    {es : List (Endpoint site.reduce)} {a b : Context} (labels : Labelling site.reduce es a b)
    (rooted : es.head?=some (.inr (.inl root)))
    (last : Endpoint cut) (finish : es.getLast?=some (AG.plugLeft cut s.right.net last)) :
    ∃ principal : SiteActionPrincipal site,∃ old,
      ActionCanonicalBlocks site principal (es.map (plugEnd (cut).label s.right.net.label).invFun) old ∧
      Labelling site.net old a b ∧old.head?=some (.inr (.inl root)) ∧
      old.getLast?=some (site.outsideEnd last) ∧
      ∀ input output,Labelling site.net old input output → Labelling site.reduce es input output := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft cut s.right.net first) := rooted
  have rawHead : (es.map (plugEnd (cut).label s.right.net.label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd (cut).label s.right.net.label).left_inv (.inl first))
  have shape := labels.local_excursions cut s.right.net first last head finish
  obtain ⟨principal,old,relation,oldLabels,oldHead,oldLast⟩ := site.action_canonical_ancestor action labels first last head finish
  refine ⟨principal,old,relation,oldLabels,oldHead,oldLast,?_⟩
  intro input output changed
  have contracted := relation.rooted_contract site matching indep flow rootPolarity shape rawHead
    (pre:=[]) (referenceInput:=a) (requested:=input)
    (Labelling.single (site.outsideEnd first) a) rfl (Labelling.single (site.outsideEnd first) input) changed
  have physical := (contracted.labelling cut s.right.net).actual cut s.right.net
  simpa only [plug_decomposition_flatten] using physical
end Whole
end Lamping.AG


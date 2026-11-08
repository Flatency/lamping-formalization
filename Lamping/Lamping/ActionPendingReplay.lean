import Lamping.Lamping.ActionResidualReplay
import Lamping.Lamping.PlugPendingEndpoints
import Lamping.Lamping.ActionContextPrefixes
import Lamping.Lamping.SourceContextPrefixes
import Lamping.Lamping.BindingControlInputs
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

theorem PathSite.pending_canonical_prefix (action : IsAction s)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {raw : List (PlugSegment cut s.right.net)} {input output : Context}
    (pending : PendingRhsBlock cut s.right.net raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root))))) :
    ∃ principal : SiteActionPrincipal site,∃ old,
      ActionCanonicalBlocks site principal pending.pre old ∧
      Labelling site.net old input pending.middle ∧old.head?=some (.inr (.inl root)) ∧
      old.getLast?=some (site.outsideEnd pending.last) ∧
      ∀ requested result,Labelling site.net old requested result →
        PlugExcursions cut s.right.net pending.pre requested result := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have firstHead : pending.pre.head?=some (.inl first) := pending.prefixHead.trans head
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨old,relation,labels,oldHead,oldLast⟩ := pending.prefixPath.action_canonical_lift site action principal
    first pending.last firstHead pending.prefixLast
  refine ⟨principal,old,relation,labels,oldHead,oldLast,?_⟩
  intro requested result changed
  exact relation.rooted_contract site matching indep flow positive pending.prefixPath firstHead
    (pre:=[]) (referenceInput:=input) (requested:=requested)
    (Labelling.single (site.outsideEnd first) input) rfl (Labelling.single (site.outsideEnd first) requested) changed

/-- Reassemble a changed assignment on exactly the same pending pieces. -/
theorem PendingRhsBlock.with_labels {raw : List (PlugSegment cut s.right.net)} {input output : Context}
    (pending : PendingRhsBlock cut s.right.net raw input output)
    {requested middle result : Context} (prefixPath : PlugExcursions cut s.right.net pending.pre requested middle)
    (insideLabels : Labelling s.right.net pending.inside middle result) :
    PlugLabelling cut s.right.net raw requested result := by
  let changed : PendingRhsBlock cut s.right.net raw requested result := {
    pre:=pending.pre, last:=pending.last,enter:=pending.enter,middle:=middle,inside:=pending.inside
    equation:=pending.equation,prefixPath:=prefixPath,prefixHead:=pending.prefixHead,prefixLast:=pending.prefixLast
    arrival:=pending.arrival,insideHead:=pending.insideHead,insideLabels:=insideLabels }
  exact changed.labelling cut s.right.net

private theorem outside_aux_end (e : Endpoint cut) (entry : s.Frontier)
    (arrival : (cut).wire e=.inr (.inl (.inr entry))) :
    site.outsideEnd e=site.net.wire (site.outsideEnd (.inr (.inl (.inr entry)))) := by
  have wired : site.net.wire (site.outsideEnd e)=site.outsideEnd (.inr (.inl (.inr entry))) := by
    rw [site.outsideEnd_wire,arrival]
  have same := congrArg site.net.wire.mate wired
  simpa only [Pairing.involutive] using same

/-- Only the supplied finite labelled route to an actual old typed endpoint
is used. This is not an extension theorem for arbitrary control tails. -/
private theorem pending_singleton_inputs (action : IsAction s)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {raw : List (PlugSegment cut s.right.net)} {input output result : Context}
    (pending : PendingRhsBlock cut s.right.net raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root)))))
    (singleton : pending.inside=[.inr (.inl pending.enter)])
    (route : List (Endpoint site.net)) (target : Endpoint site.net) (role : ProperRole) (level : Nat)
    (routeHead : route.head?=some (site.outsideEnd pending.last))
    (routeLast : route.getLast?=some (site.net.wire target))
    (routeLabels : Labelling site.net route pending.middle result)
    (atTarget : AtProperRole site.net root target role level) (incoming : role.incoming) :
    ∀ requested,∃ final,PlugLabelling cut s.right.net raw requested final := by
  obtain ⟨principal,old,relation,labels,oldHead,oldLast,replay⟩ := site.pending_canonical_prefix
    action matching indep flow positive pending head
  obtain ⟨front,oldSplit⟩ := List.getLast?_eq_some_iff.mp oldLast
  obtain ⟨post,routeSplit⟩ := List.head?_eq_some_iff.mp routeHead
  have labels' := labels
  rw [oldSplit] at labels'
  rw [routeSplit] at routeLabels
  have full := labels'.join routeLabels
  have fullHead : (front++site.outsideEnd pending.last::post).head?=some (.inr (.inl root)) := by
    cases front with
    | nil => simpa only [oldSplit,List.nil_append,List.head?_cons] using oldHead
    | cons x front => simpa only [oldSplit,List.cons_append,List.head?_cons] using oldHead
  have fullLast : (front++site.outsideEnd pending.last::post).getLast?=some (site.net.wire target) := by
    rw [List.getLast?_append]
    rw [routeSplit] at routeLast
    rw [routeLast,Option.some_or]
  have forward := full.root_forward_of_flow flow root fullHead positive
  obtain ⟨inputs,_⟩ := indep _ (.inr (.inl root)) target .root role 0 level input result
    fullHead fullLast (.root) trivial atTarget incoming forward full
  intro requested
  obtain ⟨final,changed⟩ := inputs requested
  simp only [Context.replace_zero] at changed
  obtain ⟨seam,before,after⟩ := changed.split_segment
  have newPrefix : Labelling site.net old requested seam := by simpa only [oldSplit] using before
  have newInside : Labelling s.right.net pending.inside seam seam := by rw [singleton]; exact .single _ _
  exact ⟨seam,pending.with_labels site (replay requested seam newPrefix) newInside⟩
end
section FanApp
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.app i j lt) V) site.closed

theorem PathSite.fan_pending_app_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {raw : List (PlugSegment cut (fanRight .app i j))} {input output : Context}
    (pending : PendingRhsBlock cut (fanRight .app i j) raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root))))) (branch : Bool)
    (finish : pending.inside.getLast?=some ((fanRight .app i j).wire (.inl ⟨.inl branch,appCtx⟩))) :
    ∀ requested,∃ result,PlugLabelling cut (fanRight .app i j) raw requested result := by
  obtain ⟨entryEq,shape,inverseRule⟩ := fanRight_app_context_prefix i j branch pending.enter pending.inside
    pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨principal,old,relation,labels,rooted,last,replay⟩ := site.pending_canonical_prefix
    (.fan .app i j lt) matching indep flow positive pending head
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [entryEq] at ending
  have ends : old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) := by
    rw [ending] at last
    exact last
  have kind : accessKind site.net old=some .app := by
    unfold accessKind
    rw [ends]
    simp only [Option.bind_some,Pairing.involutive]
    rfl
  let parent : RootAccess site.net root := ⟨old,⟨⟨⟨input,pending.middle,labels⟩,
    labels.root_forward_of_flow flow root rooted positive⟩,rooted,⟨.app,kind⟩⟩⟩
  have fixed := site.matched_control_input_of_prefix matching indep flow positive (Or.inl rfl) rfl
    old appCtx HEq.rfl input pending.middle output labels rooted ends branch inverseRule
  intro requested
  obtain ⟨seam,changed⟩ := parent.inputs indep requested
  obtain ⟨result,rule⟩ := fixed requested seam changed
  have newInside : Labelling (fanRight .app i j) pending.inside seam result := by
    rw [shape]
    exact .cons (LabelledTurn.node (g:=fanRight .app i j) (.inr false) (.inl ()) (.inr branch) rule) (.single _ _)
  exact ⟨result,pending.with_labels site (replay requested seam changed) newInside⟩

theorem PathSite.fan_new_app_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (branch : Bool) (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩))) :
    ∀ requested,∃ result,Labelling site.reduce es requested result := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft cut (fanRight .app i j) first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node cut (fanRight .app i j) first head (.inl branch) appCtx finish
  have rawHead : (es.map (plugEnd (cut).label (fanRight .app i j).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd (cut).label (fanRight .app i j).label).left_inv (.inl first))
  intro requested
  obtain ⟨result,changed⟩ := site.fan_pending_app_root_inputs matching indep flow positive pending rawHead branch insideLast requested
  exact ⟨result,by simpa only [plug_decomposition_flatten] using changed.actual cut (fanRight .app i j)⟩
end FanApp
section croApp
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.croAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.app i j lt) V) site.closed
local notation "rhs" => unaryRightCore Op.cro Op.app (Bij.refl _) i (j-1)

theorem PathSite.cro_pending_app_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {raw : List (PlugSegment cut rhs)} {input output : Context}
    (pending : PendingRhsBlock cut rhs raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root)))))
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),appCtx⟩))) :
    ∀ requested,∃ result,PlugLabelling cut rhs raw requested result := by
  obtain ⟨entryEq,shape,inverseRule⟩ := unaryRight_app_context_prefix .cro (Bij.refl _) (Or.inr (Or.inl rfl))
    i (j-1) pending.enter pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨principal,old,relation,labels,rooted,last,replay⟩ := site.pending_canonical_prefix
    (.cro .app i j lt) matching indep flow positive pending head
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [entryEq] at ending
  have ends : old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) := by
    rw [ending] at last
    exact last
  have kind : accessKind site.net old=some .app := by
    unfold accessKind
    rw [ends]
    simp only [Option.bind_some,Pairing.involutive]
    rfl
  let parent : RootAccess site.net root := ⟨old,⟨⟨⟨input,pending.middle,labels⟩,
    labels.root_forward_of_flow flow root rooted positive⟩,rooted,⟨.app,kind⟩⟩⟩
  have fixed := site.matched_control_input_of_prefix matching indep flow positive (Or.inr (Or.inl rfl)) rfl
    old appCtx HEq.rfl input pending.middle output labels rooted ends () inverseRule
  intro requested
  obtain ⟨seam,changed⟩ := parent.inputs indep requested
  obtain ⟨result,rule⟩ := fixed requested seam changed
  have newInside : Labelling rhs pending.inside seam result := by
    rw [shape]
    exact .cons (LabelledTurn.node (g:=rhs) (.inr false) (.inl ()) (.inr ()) rule) (.single _ _)
  exact ⟨result,pending.with_labels site (replay requested seam changed) newInside⟩

theorem PathSite.cro_new_app_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩))) :
    ∀ requested,∃ result,Labelling site.reduce es requested result := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft cut rhs first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node cut rhs first head (.inl ()) appCtx finish
  have rawHead : (es.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  intro requested
  obtain ⟨result,changed⟩ := site.cro_pending_app_root_inputs matching indep flow positive pending rawHead insideLast requested
  exact ⟨result,by simpa only [plug_decomposition_flatten] using changed.actual cut rhs⟩
end croApp
section braApp
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.braAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.app i j lt) V) site.closed
local notation "rhs" => unaryRightCore Op.bra Op.app (Bij.refl _) i (j+1)

theorem PathSite.bra_pending_app_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {raw : List (PlugSegment cut rhs)} {input output : Context}
    (pending : PendingRhsBlock cut rhs raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root)))))
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),appCtx⟩))) :
    ∀ requested,∃ result,PlugLabelling cut rhs raw requested result := by
  obtain ⟨entryEq,shape,inverseRule⟩ := unaryRight_app_context_prefix .bra (Bij.refl _) (Or.inr (Or.inr rfl))
    i (j+1) pending.enter pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨principal,old,relation,labels,rooted,last,replay⟩ := site.pending_canonical_prefix
    (.bra .app i j lt) matching indep flow positive pending head
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [entryEq] at ending
  have ends : old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) := by
    rw [ending] at last
    exact last
  have kind : accessKind site.net old=some .app := by
    unfold accessKind
    rw [ends]
    simp only [Option.bind_some,Pairing.involutive]
    rfl
  let parent : RootAccess site.net root := ⟨old,⟨⟨⟨input,pending.middle,labels⟩,
    labels.root_forward_of_flow flow root rooted positive⟩,rooted,⟨.app,kind⟩⟩⟩
  have fixed := site.matched_control_input_of_prefix matching indep flow positive (Or.inr (Or.inr rfl)) rfl
    old appCtx HEq.rfl input pending.middle output labels rooted ends () inverseRule
  intro requested
  obtain ⟨seam,changed⟩ := parent.inputs indep requested
  obtain ⟨result,rule⟩ := fixed requested seam changed
  have newInside : Labelling rhs pending.inside seam result := by
    rw [shape]
    exact .cons (LabelledTurn.node (g:=rhs) (.inr false) (.inl ()) (.inr ()) rule) (.single _ _)
  exact ⟨result,pending.with_labels site (replay requested seam changed) newInside⟩

theorem PathSite.bra_new_app_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩))) :
    ∀ requested,∃ result,Labelling site.reduce es requested result := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft cut rhs first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node cut rhs first head (.inl ()) appCtx finish
  have rawHead : (es.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  intro requested
  obtain ⟨result,changed⟩ := site.bra_pending_app_root_inputs matching indep flow positive pending rawHead insideLast requested
  exact ⟨result,by simpa only [plug_decomposition_flatten] using changed.actual cut rhs⟩
end braApp
section fanLamCtx
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
local notation "rhs" => fanRight Op.lam i j

theorem PathSite.fan_pending_lam_ctx_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {raw : List (PlugSegment cut rhs)} {input output : Context}
    (pending : PendingRhsBlock cut rhs raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root))))) (branch : Bool)
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl branch,.inl ()⟩))) :
    ∀ requested,∃ result,PlugLabelling cut rhs raw requested result := by
  obtain ⟨entryEq,route,routeHead,routeLast,routeLabels,tails⟩ := site.fan_lam_context_ancestor
    branch pending.enter pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨_,shape,_⟩ := fanRight_lam_context_prefix i j branch pending.enter pending.inside pending.middle output
    pending.insideLabels pending.insideHead finish
  have singleton : pending.inside=[.inr (.inl pending.enter)] := by rw [shape,entryEq]
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [entryEq] at ending
  change site.outsideEnd pending.last=site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩) at ending
  rw [←ending] at routeHead
  exact pending_singleton_inputs site (.fan .lam i j lt) matching indep flow positive pending head singleton
    route (.inl ⟨.inr (.inr ()),.inl ()⟩) .lamCtx j routeHead routeLast routeLabels
    (AtProperRole.lamCtx (g:=site.net) (root:=root) (.inr (.inr ())) (.inl ()) j rfl HEq.rfl) trivial

theorem PathSite.fan_new_lam_ctx_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (branch : Bool) (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩))) :
    ∀ requested,∃ result,Labelling site.reduce es requested result := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft cut rhs first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node cut rhs first head (.inl branch) (.inl ()) finish
  have rawHead : (es.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  intro requested
  obtain ⟨result,changed⟩ := site.fan_pending_lam_ctx_root_inputs matching indep flow positive pending rawHead branch insideLast requested
  exact ⟨result,by simpa only [plug_decomposition_flatten] using changed.actual cut rhs⟩
end fanLamCtx
section croLamCtx
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.lam i j lt) V) site.closed
local notation "rhs" => unaryRightCore Op.cro Op.lam (Bij.refl _) i (j-1)

theorem PathSite.cro_pending_lam_ctx_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {raw : List (PlugSegment cut rhs)} {input output : Context}
    (pending : PendingRhsBlock cut rhs raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root))))) 
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),.inl ()⟩))) :
    ∀ requested,∃ result,PlugLabelling cut rhs raw requested result := by
  obtain ⟨entryEq,route,routeHead,routeLast,routeLabels,tails⟩ := site.cro_lam_context_ancestor
    pending.enter pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨_,shape,_⟩ := unaryRight_lam_context_prefix .cro (Bij.refl _) i (j-1) pending.enter pending.inside pending.middle output
    pending.insideLabels pending.insideHead finish
  have singleton : pending.inside=[.inr (.inl pending.enter)] := by rw [shape,entryEq]
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [entryEq] at ending
  change site.outsideEnd pending.last=site.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩) at ending
  rw [←ending] at routeHead
  exact pending_singleton_inputs site (.cro .lam i j lt) matching indep flow positive pending head singleton
    route (.inl ⟨.inr (.inr ()),.inl ()⟩) .lamCtx j routeHead routeLast routeLabels
    (AtProperRole.lamCtx (g:=site.net) (root:=root) (.inr (.inr ())) (.inl ()) j rfl HEq.rfl) trivial

theorem PathSite.cro_new_lam_ctx_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
     (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))) :
    ∀ requested,∃ result,Labelling site.reduce es requested result := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft cut rhs first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node cut rhs first head (.inl ()) (.inl ()) finish
  have rawHead : (es.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  intro requested
  obtain ⟨result,changed⟩ := site.cro_pending_lam_ctx_root_inputs matching indep flow positive pending rawHead insideLast requested
  exact ⟨result,by simpa only [plug_decomposition_flatten] using changed.actual cut rhs⟩
end croLamCtx
section braLamCtx
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.lam i j lt) V) site.closed
local notation "rhs" => unaryRightCore Op.bra Op.lam (Bij.refl _) i (j+1)

theorem PathSite.bra_pending_lam_ctx_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {raw : List (PlugSegment cut rhs)} {input output : Context}
    (pending : PendingRhsBlock cut rhs raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root))))) 
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),.inl ()⟩))) :
    ∀ requested,∃ result,PlugLabelling cut rhs raw requested result := by
  obtain ⟨entryEq,route,routeHead,routeLast,routeLabels,tails⟩ := site.bra_lam_context_ancestor
    pending.enter pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨_,shape,_⟩ := unaryRight_lam_context_prefix .bra (Bij.refl _) i (j+1) pending.enter pending.inside pending.middle output
    pending.insideLabels pending.insideHead finish
  have singleton : pending.inside=[.inr (.inl pending.enter)] := by rw [shape,entryEq]
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [entryEq] at ending
  change site.outsideEnd pending.last=site.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩) at ending
  rw [←ending] at routeHead
  exact pending_singleton_inputs site (.bra .lam i j lt) matching indep flow positive pending head singleton
    route (.inl ⟨.inr (.inr ()),.inl ()⟩) .lamCtx j routeHead routeLast routeLabels
    (AtProperRole.lamCtx (g:=site.net) (root:=root) (.inr (.inr ())) (.inl ()) j rfl HEq.rfl) trivial

theorem PathSite.bra_new_lam_ctx_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
     (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))) :
    ∀ requested,∃ result,Labelling site.reduce es requested result := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft cut rhs first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node cut rhs first head (.inl ()) (.inl ()) finish
  have rawHead : (es.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  intro requested
  obtain ⟨result,changed⟩ := site.bra_pending_lam_ctx_root_inputs matching indep flow positive pending rawHead insideLast requested
  exact ⟨result,by simpa only [plug_decomposition_flatten] using changed.actual cut rhs⟩
end braLamCtx
section fanLamBind
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
local notation "rhs" => fanRight Op.lam i j

theorem PathSite.fan_pending_lam_bind_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (nesting : Nesting site.net root) (transparency : Transparency site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {raw : List (PlugSegment cut rhs)} {input output : Context}
    (pending : PendingRhsBlock cut rhs raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root))))) (branch : Bool)
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl branch,lamBind⟩))) :
    ∀ requested,∃ result,PlugLabelling cut rhs raw requested result := by
  obtain ⟨entryEq,shape,inverseRule⟩ := fanRight_copied_aux_prefix .lam i j branch false pending.enter pending.inside pending.middle output
    pending.insideLabels pending.insideHead finish
  obtain ⟨principal,old,relation,labels,rooted,last,replay⟩ := site.pending_canonical_prefix
    (.fan .lam i j lt) matching indep flow positive pending head
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [entryEq] at ending
  have ends : old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),lamBind⟩)) := by
    rw [ending] at last
    exact last
  have kind : accessKind site.net old=some .var := by
    unfold accessKind
    rw [ends]
    simp only [Option.bind_some,Pairing.involutive]
    rfl
  have forward := labels.root_forward_of_flow flow root rooted positive
  let parent : RootAccess site.net root := ⟨old,⟨⟨⟨input,pending.middle,labels⟩,forward⟩,rooted,⟨.var,kind⟩⟩⟩
  have fixed := site.binding_control_input_stable indep nesting transparency (Or.inl rfl) rfl lt
    lamBody lamBind HEq.rfl HEq.rfl labels forward rooted ends branch inverseRule
  intro requested
  obtain ⟨seam,changed⟩ := parent.inputs indep requested
  obtain ⟨result,rule⟩ := fixed requested seam changed
  have newInside : Labelling rhs pending.inside seam result := by
    rw [shape]
    exact .cons (LabelledTurn.node (g:=rhs) (.inr false) (.inl ()) (.inr branch) rule) (.single _ _)
  exact ⟨result,pending.with_labels site (replay requested seam changed) newInside⟩

theorem PathSite.fan_new_lam_bind_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (nesting : Nesting site.net root) (transparency : Transparency site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (branch : Bool) (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),lamBind⟩))) :
    ∀ requested,∃ result,Labelling site.reduce es requested result := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft cut rhs first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node cut rhs first head (.inl branch) lamBind finish
  have rawHead : (es.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  intro requested
  obtain ⟨result,changed⟩ := site.fan_pending_lam_bind_root_inputs matching indep nesting transparency flow positive
    pending rawHead branch insideLast requested
  exact ⟨result,by simpa only [plug_decomposition_flatten] using changed.actual cut rhs⟩
end fanLamBind
section croLamBind
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.lam i j lt) V) site.closed
local notation "rhs" => unaryRightCore Op.cro Op.lam (Bij.refl _) i (j-1)

theorem PathSite.cro_pending_lam_bind_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (nesting : Nesting site.net root) (transparency : Transparency site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {raw : List (PlugSegment cut rhs)} {input output : Context}
    (pending : PendingRhsBlock cut rhs raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root))))) 
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),lamBind⟩))) :
    ∀ requested,∃ result,PlugLabelling cut rhs raw requested result := by
  obtain ⟨entryEq,shape,inverseRule⟩ := unaryRight_copied_aux_prefix .cro .lam (Bij.refl _) (Or.inr (Or.inl rfl)) i (j-1) false pending.enter pending.inside pending.middle output
    pending.insideLabels pending.insideHead finish
  obtain ⟨principal,old,relation,labels,rooted,last,replay⟩ := site.pending_canonical_prefix
    (.cro .lam i j lt) matching indep flow positive pending head
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [entryEq] at ending
  have ends : old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),lamBind⟩)) := by
    rw [ending] at last
    exact last
  have kind : accessKind site.net old=some .var := by
    unfold accessKind
    rw [ends]
    simp only [Option.bind_some,Pairing.involutive]
    rfl
  have forward := labels.root_forward_of_flow flow root rooted positive
  let parent : RootAccess site.net root := ⟨old,⟨⟨⟨input,pending.middle,labels⟩,forward⟩,rooted,⟨.var,kind⟩⟩⟩
  have fixed := site.binding_control_input_stable indep nesting transparency (Or.inr (Or.inl rfl)) rfl lt
    lamBody lamBind HEq.rfl HEq.rfl labels forward rooted ends () inverseRule
  intro requested
  obtain ⟨seam,changed⟩ := parent.inputs indep requested
  obtain ⟨result,rule⟩ := fixed requested seam changed
  have newInside : Labelling rhs pending.inside seam result := by
    rw [shape]
    exact .cons (LabelledTurn.node (g:=rhs) (.inr false) (.inl ()) (.inr ()) rule) (.single _ _)
  exact ⟨result,pending.with_labels site (replay requested seam changed) newInside⟩

theorem PathSite.cro_new_lam_bind_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (nesting : Nesting site.net root) (transparency : Transparency site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
     (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩))) :
    ∀ requested,∃ result,Labelling site.reduce es requested result := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft cut rhs first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node cut rhs first head (.inl ()) lamBind finish
  have rawHead : (es.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  intro requested
  obtain ⟨result,changed⟩ := site.cro_pending_lam_bind_root_inputs matching indep nesting transparency flow positive
    pending rawHead insideLast requested
  exact ⟨result,by simpa only [plug_decomposition_flatten] using changed.actual cut rhs⟩
end croLamBind
section braLamBind
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.lam i j lt) V) site.closed
local notation "rhs" => unaryRightCore Op.bra Op.lam (Bij.refl _) i (j+1)

theorem PathSite.bra_pending_lam_bind_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (nesting : Nesting site.net root) (transparency : Transparency site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {raw : List (PlugSegment cut rhs)} {input output : Context}
    (pending : PendingRhsBlock cut rhs raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root))))) 
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),lamBind⟩))) :
    ∀ requested,∃ result,PlugLabelling cut rhs raw requested result := by
  obtain ⟨entryEq,shape,inverseRule⟩ := unaryRight_copied_aux_prefix .bra .lam (Bij.refl _) (Or.inr (Or.inr rfl)) i (j+1) false pending.enter pending.inside pending.middle output
    pending.insideLabels pending.insideHead finish
  obtain ⟨principal,old,relation,labels,rooted,last,replay⟩ := site.pending_canonical_prefix
    (.bra .lam i j lt) matching indep flow positive pending head
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [entryEq] at ending
  have ends : old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),lamBind⟩)) := by
    rw [ending] at last
    exact last
  have kind : accessKind site.net old=some .var := by
    unfold accessKind
    rw [ends]
    simp only [Option.bind_some,Pairing.involutive]
    rfl
  have forward := labels.root_forward_of_flow flow root rooted positive
  let parent : RootAccess site.net root := ⟨old,⟨⟨⟨input,pending.middle,labels⟩,forward⟩,rooted,⟨.var,kind⟩⟩⟩
  have fixed := site.binding_control_input_stable indep nesting transparency (Or.inr (Or.inr rfl)) rfl lt
    lamBody lamBind HEq.rfl HEq.rfl labels forward rooted ends () inverseRule
  intro requested
  obtain ⟨seam,changed⟩ := parent.inputs indep requested
  obtain ⟨result,rule⟩ := fixed requested seam changed
  have newInside : Labelling rhs pending.inside seam result := by
    rw [shape]
    exact .cons (LabelledTurn.node (g:=rhs) (.inr false) (.inl ()) (.inr ()) rule) (.single _ _)
  exact ⟨result,pending.with_labels site (replay requested seam changed) newInside⟩

theorem PathSite.bra_new_lam_bind_root_inputs
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (nesting : Nesting site.net root) (transparency : Transparency site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
     (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩))) :
    ∀ requested,∃ result,Labelling site.reduce es requested result := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft cut rhs first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node cut rhs first head (.inl ()) lamBind finish
  have rawHead : (es.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  intro requested
  obtain ⟨result,changed⟩ := site.bra_pending_lam_bind_root_inputs matching indep nesting transparency flow positive
    pending rawHead insideLast requested
  exact ⟨result,by simpa only [plug_decomposition_flatten] using changed.actual cut rhs⟩
end braLamBind
end Lamping.AG



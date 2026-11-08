import Lamping.Lamping.ActionPendingWords
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

/-- A selected finite principal component gives the original passive
principal prefix. Every later departure is control/W and emits no syntax. -/
theorem SiteActionPrincipal.input_prefix_word (principal : SiteActionPrincipal site)
    (action : IsAction s) (p : Aux s.active) {a b : Context}
    (rule : Traversal s.low (.op s.active) (.inr p) (.inl ()) a b) :
    ∃ route,Labelling site.net route a b ∧
      route.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)) ∧
      route.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      accessWord site.net route=[] := by
  have nonempty : principal.edges≠[] := by
    intro empty
    have starts := principal.first
    rw [empty] at starts
    cases starts
  have labels := transparent_route_labelling site.net principal.edges nonempty principal.transparent b
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp principal.first
  refine ⟨site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::principal.edges,?_,rfl,?_,?_⟩
  · rw [split] at labels ⊢
    apply Labelling.cons
    · rw [Pairing.involutive]
      exact LabelledTurn.node (g:=site.net) (.inr (.inl ())) _ _ rule
    · exact labels
  · rw [split,List.getLast?_cons_cons]
    simpa only [split] using principal.last
  · exact principal.tokens_empty site action

private theorem join_word {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    {g : Net signature N D U} {xs ys : List (Endpoint g)} {a middle b : Context}
    (left : Labelling g xs a middle) (right : Labelling g ys middle b)
    (e first last : Endpoint g) (leftHead : xs.head?=some first) (leftLast : xs.getLast?=some e)
    (rightHead : ys.head?=some e) (rightLast : ys.getLast?=some last) :
    ∃ joined,Labelling g joined a b ∧joined.head?=some first ∧joined.getLast?=some last ∧
      accessWord g joined=accessWord g xs++accessWord g ys := by
  obtain ⟨pre,leftSplit⟩ := List.getLast?_eq_some_iff.mp leftLast
  obtain ⟨post,rightSplit⟩ := List.head?_eq_some_iff.mp rightHead
  have leftLabels : Labelling g (pre++[e]) a middle := by simpa only [leftSplit] using left
  have rightLabels : Labelling g (e::post) middle b := by simpa only [rightSplit] using right
  refine ⟨pre++e::post,leftLabels.join rightLabels,?_,?_,?_⟩
  · cases pre with
    | nil => simpa only [leftSplit,List.nil_append,List.head?_cons] using leftHead
    | cons x pre => simpa only [leftSplit,List.cons_append,List.head?_cons] using leftHead
  · rw [List.getLast?_append]
    have lastEq : (e::post).getLast?=some last := by simpa only [rightSplit] using rightLast
    rw [lastEq,Option.some_or]
  · have words : accessWord g (pre++e::post)=accessWord g (pre++[e])++accessWord g (e::post) := by
      cases pre with
      | nil => rfl
      | cons x pre => simp only [List.cons_append,accessWord,List.flatMap_append,List.flatMap_cons,
          List.flatMap_nil,List.append_nil,List.append_assoc]
    simpa only [←leftSplit,←rightSplit] using words

private theorem pending_principal_word (action : IsAction s)
    {raw : List (PlugSegment cut s.right.net)} {input output result : Context}
    (pending : PendingRhsBlock cut s.right.net raw input output)
    (first : Endpoint cut) (head : raw.head?=some (.inl first))
    (p : Aux s.active)
    (entry : site.outsideEnd (.inr (.inl (.inr pending.enter)))=.inl ⟨.inr (.inl ()),.inr p⟩)
    (tokens : accessTokens s.right.net pending.inside=[])
    (rule : Traversal s.low (.op s.active) (.inr p) (.inl ()) pending.middle result) :
    ∃ old,Labelling site.net old input result ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=accessWord site.net old := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨pre,labels,start,last,words⟩ := pending.action_canonical_word site action principal first head
  have wired : site.net.wire (site.outsideEnd pending.last)=
      site.outsideEnd (.inr (.inl (.inr pending.enter))) := by
    rw [site.outsideEnd_wire,pending.arrival]
  rw [entry] at wired
  have ending := congrArg site.net.wire.mate wired
  simp only [Pairing.involutive] at ending
  obtain ⟨route,routeLabels,routeHead,routeLast,routeWord⟩ := principal.input_prefix_word site action p rule
  rw [←ending] at routeHead
  obtain ⟨old,oldLabels,oldHead,oldLast,oldWord⟩ := join_word labels routeLabels _ _ _ start last routeHead routeLast
  rw [routeWord,List.append_nil] at oldWord
  rw [tokens,List.append_nil] at words
  exact ⟨old,oldLabels,oldHead,oldLast,words.trans oldWord.symm⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}

/-- The copied lambda context has an actual singleton RHS prefix. Its old
ancestor traverses only the original active control and finite W component. -/
theorem PathSite.fan_pending_lam_ancestor_word
    (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {raw : List (PlugSegment (cutFragment site.net (pathPartition (.fanAction .lam i j lt) V) site.closed)
      (Schema.fanAction .lam i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition (.fanAction .lam i j lt) V) site.closed)
      (Schema.fanAction .lam i j lt).right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition (.fanAction .lam i j lt) V) site.closed))
    (head : raw.head?=some (.inl first)) (branch : Bool)
    (finish : pending.inside.getLast?=some ((fanRight .lam i j).wire (.inl ⟨.inl branch,.inl ()⟩))) :
    ∃ old,Labelling site.net old input (InitialOffsets.fanAt i branch output) ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=accessWord site.net old := by
  obtain ⟨same,shape,contexts⟩ := fanRight_lam_context_prefix i j branch pending.enter pending.inside
    pending.middle output pending.insideLabels pending.insideHead finish
  apply pending_principal_word site (.fan .lam i j lt) pending first head branch
  · rw [same]; rfl
  · exact congrArg (accessTokens (fanRight .lam i j)) shape
  · rw [contexts]
    exact .direct (InitialOffsets.Event.apply_rel (.fan i branch) output)

theorem PathSite.cro_pending_lam_ancestor_word
    (site : PathSite (.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {raw : List (PlugSegment (cutFragment site.net (pathPartition (.croAction .lam i j lt) V) site.closed)
      (Schema.croAction .lam i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition (.croAction .lam i j lt) V) site.closed)
      (Schema.croAction .lam i j lt).right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition (.croAction .lam i j lt) V) site.closed))
    (head : raw.head?=some (.inl first))
    (finish : pending.inside.getLast?=some ((unaryRightCore .cro .lam (Bij.refl _) i (j-1)).wire
      (.inl ⟨.inl (),.inl ()⟩))) :
    ∃ old,Labelling site.net old input (InitialOffsets.croAt i output) ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=accessWord site.net old := by
  obtain ⟨same,shape,contexts⟩ := unaryRight_lam_context_prefix .cro (Bij.refl _) i (j-1)
    pending.enter pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  apply pending_principal_word site (.cro .lam i j lt) pending first head ()
  · rw [same]; rfl
  · exact congrArg (accessTokens (unaryRightCore .cro .lam (Bij.refl _) i (j-1))) shape
  · rw [contexts]
    exact .direct (InitialOffsets.Event.apply_rel (.cro i) output)

theorem PathSite.bra_pending_lam_ancestor_word
    (site : PathSite (.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {raw : List (PlugSegment (cutFragment site.net (pathPartition (.braAction .lam i j lt) V) site.closed)
      (Schema.braAction .lam i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition (.braAction .lam i j lt) V) site.closed)
      (Schema.braAction .lam i j lt).right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition (.braAction .lam i j lt) V) site.closed))
    (head : raw.head?=some (.inl first))
    (finish : pending.inside.getLast?=some ((unaryRightCore .bra .lam (Bij.refl _) i (j+1)).wire
      (.inl ⟨.inl (),.inl ()⟩))) :
    ∃ old,Labelling site.net old input (InitialOffsets.braAt i output) ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=accessWord site.net old := by
  obtain ⟨same,shape,contexts⟩ := unaryRight_lam_context_prefix .bra (Bij.refl _) i (j+1)
    pending.enter pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  apply pending_principal_word site (.bra .lam i j lt) pending first head ()
  · rw [same]; rfl
  · exact congrArg (accessTokens (unaryRightCore .bra .lam (Bij.refl _) i (j+1))) shape
  · rw [contexts]
    exact .direct (InitialOffsets.Event.apply_rel (.bra i) output)
end
end Lamping.AG

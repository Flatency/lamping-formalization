import Lamping.Lamping.ActionWholeWords
import Lamping.Lamping.ActionPendingAncestors
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

private theorem word_append (xs ys : List (Endpoint g)) (nonempty : xs≠[]) :
    accessWord g (xs++ys)=accessWord g xs++accessTokens g ys := by
  cases xs with
  | nil => exact False.elim (nonempty rfl)
  | cons e xs => exact List.flatMap_append
end
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

/-- The last genuinely truncated RHS block contributes all of its tokens.
The preceding outside prefix is reflected by actual canonical excursions,
with its original input and seam assignments. No extension is asserted. -/
theorem PendingRhsBlock.action_canonical_word (action : IsAction s)
    (principal : SiteActionPrincipal site)
    {raw : List (PlugSegment cut s.right.net)} {input output : Context}
    (pending : PendingRhsBlock cut s.right.net raw input output)
    (first : Endpoint cut) (head : raw.head?=some (.inl first)) :
    ∃ old,Labelling site.net old input pending.middle ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.outsideEnd pending.last) ∧
      accessWord site.reduce (raw.map (plugEnd (cut).label s.right.net.label))=
        accessWord site.net old++accessTokens s.right.net pending.inside := by
  obtain ⟨old,relation,labels,start,last⟩ := pending.prefixPath.action_canonical_lift site action principal
    first pending.last (pending.prefixHead.trans head) pending.prefixLast
  have words := relation.word site pending.prefixPath
  have preNonempty : pending.pre≠[] := by
    intro empty
    have starts := pending.prefixHead.trans head
    rw [empty] at starts
    cases starts
  have mappedNonempty : pending.pre.map (plugEnd (cut).label s.right.net.label)≠[] := by
    cases eqs : pending.pre with
    | nil => exact False.elim (preNonempty eqs)
    | cons e es => simp
  refine ⟨old,labels,start,last,?_⟩
  have expanded := congrArg
    (fun es => accessWord site.reduce (es.map (plugEnd (cut).label s.right.net.label))) pending.equation
  simp only [List.map_append] at expanded
  rw [word_append site.reduce _ _ mappedNonempty,words] at expanded
  have tokens : accessTokens site.reduce
      ((pending.inside.map Sum.inr).map (plugEnd (cut).label s.right.net.label))=
      accessTokens s.right.net pending.inside := by
    rw [List.map_map]
    exact accessTokens_plugRight cut s.right.net pending.inside
  exact expanded.trans (congrArg (fun tail => accessWord site.net old++tail) tokens)

private theorem outside_aux_end (e : Endpoint cut) (entry : s.Frontier)
    (arrival : (cut).wire e=.inr (.inl (.inr entry))) :
    site.outsideEnd e=site.net.wire (site.outsideEnd (.inr (.inl (.inr entry)))) := by
  have wired : site.net.wire (site.outsideEnd e)=site.outsideEnd (.inr (.inl (.inr entry))) := by
    rw [site.outsideEnd_wire,arrival]
  have same := congrArg site.net.wire.mate wired
  simpa only [Pairing.involutive] using same
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {f : Op} {i j : Nat} {lt : i<j}

/-- An actual copied auxiliary terminal reflects to its old passive auxiliary
with the same syntax word. The final two RHS segments are actual controls,
not syntax turns; high contexts are preserved separately. -/
theorem PathSite.fan_pending_aux_ancestor_word
    (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {raw : List (PlugSegment (cutFragment site.net (pathPartition (.fanAction f i j lt) V) site.closed)
      (Schema.fanAction f i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition (.fanAction f i j lt) V) site.closed)
      (Schema.fanAction f i j lt).right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition (.fanAction f i j lt) V) site.closed))
    (head : raw.head?=some (.inl first)) (branch : Bool) (q : Aux f)
    (finish : pending.inside.getLast?=some ((fanRight f i j).wire (.inl ⟨.inl branch,.inr q⟩))) :
    ∃ old,Labelling site.net old input pending.middle ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=accessWord site.net old ∧
      pending.middle.tail j=output.tail j := by
  obtain ⟨same,shape,_rule⟩ := fanRight_copied_aux_prefix f i j branch q pending.enter pending.inside
    pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨_entry,_prefix,tails⟩ := site.fan_aux_context_ancestor branch q pending.enter pending.inside
    pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨old,labels,start,last,words⟩ := pending.action_canonical_word site (.fan f i j lt) principal first head
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [same] at ending
  rw [ending] at last
  have tokens : accessTokens (Schema.fanAction f i j lt).right.net pending.inside=[] := by
    have eqs := congrArg (accessTokens (fanRight f i j)) shape
    exact eqs
  rw [tokens,List.append_nil] at words
  exact ⟨old,labels,start,last,words,tails⟩

theorem PathSite.cro_pending_aux_ancestor_word
    (site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {raw : List (PlugSegment (cutFragment site.net (pathPartition (.croAction f i j lt) V) site.closed)
      (Schema.croAction f i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition (.croAction f i j lt) V) site.closed)
      (Schema.croAction f i j lt).right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition (.croAction f i j lt) V) site.closed))
    (head : raw.head?=some (.inl first)) (q : Aux f)
    (finish : pending.inside.getLast?=some ((unaryRightCore .cro f (Bij.refl _) i (j-1)).wire
      (.inl ⟨.inl (),.inr q⟩))) :
    ∃ old,Labelling site.net old input pending.middle ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=accessWord site.net old ∧
      pending.middle.tail j=output.tail (j-1) := by
  obtain ⟨same,shape,_rule⟩ := unaryRight_copied_aux_prefix .cro f (Bij.refl _) (Or.inr (Or.inl rfl))
    i (j-1) q pending.enter pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨_entry,_prefix,tails⟩ := site.cro_aux_context_ancestor q pending.enter pending.inside
    pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨old,labels,start,last,words⟩ := pending.action_canonical_word site (.cro f i j lt) principal first head
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [same] at ending
  rw [ending] at last
  have tokens : accessTokens (Schema.croAction f i j lt).right.net pending.inside=[] :=
    congrArg (accessTokens (unaryRightCore .cro f (Bij.refl _) i (j-1))) shape
  rw [tokens,List.append_nil] at words
  exact ⟨old,labels,start,last,words,tails⟩

theorem PathSite.bra_pending_aux_ancestor_word
    (site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {raw : List (PlugSegment (cutFragment site.net (pathPartition (.braAction f i j lt) V) site.closed)
      (Schema.braAction f i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition (.braAction f i j lt) V) site.closed)
      (Schema.braAction f i j lt).right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition (.braAction f i j lt) V) site.closed))
    (head : raw.head?=some (.inl first)) (q : Aux f)
    (finish : pending.inside.getLast?=some ((unaryRightCore .bra f (Bij.refl _) i (j+1)).wire
      (.inl ⟨.inl (),.inr q⟩))) :
    ∃ old,Labelling site.net old input pending.middle ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=accessWord site.net old ∧
      pending.middle.tail j=output.tail (j+1) := by
  obtain ⟨same,shape,_rule⟩ := unaryRight_copied_aux_prefix .bra f (Bij.refl _) (Or.inr (Or.inr rfl))
    i (j+1) q pending.enter pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨_entry,_prefix,tails⟩ := site.bra_aux_context_ancestor q pending.enter pending.inside
    pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨old,labels,start,last,words⟩ := pending.action_canonical_word site (.bra f i j lt) principal first head
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [same] at ending
  rw [ending] at last
  have tokens : accessTokens (Schema.braAction f i j lt).right.net pending.inside=[] :=
    congrArg (accessTokens (unaryRightCore .bra f (Bij.refl _) i (j+1))) shape
  rw [tokens,List.append_nil] at words
  exact ⟨old,labels,start,last,words,tails⟩
end
end Lamping.AG

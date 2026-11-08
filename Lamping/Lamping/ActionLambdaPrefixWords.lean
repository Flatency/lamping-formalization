import Lamping.Lamping.ActionOccurrenceWords
import Lamping.Lamping.ActionLambdaPrefix
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- The proper body departure is the last source segment of this actual
lambda crossing. Its preceding control/W prefix emits no syntax. -/
theorem ActionLambdaCross.front_word {principal : SiteActionPrincipal site} {aux inside old}
    (cross : ActionLambdaCross site principal aux inside old) (front : List (Endpoint site.net))
    (split : old=front++[.inl ⟨.inr (.inr ()),.inr aux⟩]) : accessWord site.net front=[] := by
  cases cross with
  | @fan f i j lt actual principal branch q =>
    have same : (actual.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)::principal.edges)++
        [.inl ⟨.inr (.inr ()),.inr q⟩]=front++[.inl ⟨.inr (.inr ()),.inr q⟩] := by
      simpa only [SiteActionPrincipal.crossing,List.cons_append] using split
    have eqs := List.append_cancel_right same
    rw [←eqs]
    exact principal.tokens_empty _ (.fan _ _ _ _)
  | @cro f i j lt actual principal q =>
    have same : (actual.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩)::principal.edges)++
        [.inl ⟨.inr (.inr ()),.inr q⟩]=front++[.inl ⟨.inr (.inr ()),.inr q⟩] := by
      simpa only [SiteActionPrincipal.crossing,List.cons_append] using split
    have eqs := List.append_cancel_right same
    rw [←eqs]
    exact principal.tokens_empty _ (.cro _ _ _ _)
  | @bra f i j lt actual principal q =>
    have same : (actual.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩)::principal.edges)++
        [.inl ⟨.inr (.inr ()),.inr q⟩]=front++[.inl ⟨.inr (.inr ()),.inr q⟩] := by
      simpa only [SiteActionPrincipal.crossing,List.cons_append] using split
    have eqs := List.append_cancel_right same
    rw [←eqs]
    exact principal.tokens_empty _ (.bra _ _ _ _)
end

private theorem ActionLambdaCopy.context_token {s : Schema}
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    {branch : Aux s.active} {node : s.right.N} (copy : ActionLambdaCopy site branch node)
    (isLam : (s.right.net.label node).sort=.op .lam)
    (ctx : Port (s.right.net.label node).sort) (role : HEq ctx (Sum.inl () : Port (.op .lam))) :
    arrivalWord s.right.net (s.right.net.wire (.inl ⟨node,ctx⟩))=[] := by
  cases copy with
  | @fan f i j lt actual branch =>
    have same : f=.lam := Kind.op.inj isLam
    subst f
    have port : ctx=.inl () := eq_of_heq role
    subst ctx
    rfl
  | @cro f i j lt actual =>
    have same : f=.lam := Kind.op.inj isLam
    subst f
    have port : ctx=.inl () := eq_of_heq role
    subst ctx
    rfl
  | @bra f i j lt actual =>
    have same : f=.lam := Kind.op.inj isLam
    subst f
    have port : ctx=.inl () := eq_of_heq role
    subst ctx
    rfl
section Raw
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

private theorem split_raw {pre post : List (PlugSegment c r)} {e : PlugSegment c r} {a b : Context}
    (labels : PlugLabelling c r (pre++e::post) a b) :
    ∃ middle,PlugLabelling c r (pre++[e]) a middle ∧PlugLabelling c r (e::post) middle b := by
  induction pre generalizing a with
  | nil => exact ⟨a,.single _ _,labels⟩
  | cons x pre ih =>
    cases pre with
    | nil => cases labels with
      | cons turn tail => exact ⟨_,.cons turn (.single _ _),tail⟩
    | cons y pre => cases labels with
      | cons turn tail =>
        obtain ⟨middle,before,after⟩ := ih tail
        exact ⟨middle,.cons turn before,after⟩

private theorem right_block_unique {xs ys : List (Endpoint r)} {x y : Endpoint c}
    {tail post : List (PlugSegment c r)}
    (same : xs.map Sum.inr++Sum.inl x::tail=ys.map Sum.inr++Sum.inl y::post) :
    xs=ys ∧x=y ∧tail=post := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => have eqs := List.cons.inj same; exact ⟨rfl,Sum.inl.inj eqs.1,eqs.2⟩
    | cons h ys => cases same
  | cons h xs ih => cases ys with
    | nil => cases same
    | cons k ys =>
      obtain ⟨head,rest⟩ := List.cons.inj same
      have heads := Sum.inr.inj head
      obtain ⟨rfl,rfl,rfl⟩ := ih rest
      subst k
      exact ⟨rfl,rfl,rfl⟩

private theorem through_view {e : Endpoint c} {exit : F} {inside tail} {a b : Context}
    (nonempty : inside≠[])
    (shape : PlugExcursions c r (.inl e::(inside.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::tail)) a b) :
    ∃ middle,Labelling r inside a middle := by
  generalize eqs : (.inl e::(inside.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::tail) :
    List (PlugSegment c r))=raw at shape
  cases shape with
  | single => cases inside with
    | nil => exact False.elim (nonempty rfl)
    | cons h xs => cases eqs
  | outside turn after => cases inside with
    | nil => exact False.elim (nonempty rfl)
    | cons h xs => cases eqs
  | @through first entry other post a middle b path arrival after =>
    have initial := List.cons.inj eqs
    have firstEq := Sum.inl.inj initial.1
    subst first
    obtain ⟨edgeEq,exitEq,tailEq⟩ := right_block_unique c r initial.2
    exact ⟨middle,by rw [edgeEq]; exact path.labeling⟩

private theorem last_nonempty {T : Type} (pre tail : List T) (nonempty : tail≠[]) :
    (pre++tail).getLast?=tail.getLast? := by
  cases point : tail.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp point))
  | some e => simp only [List.getLast?_append,point,Option.some_or]
end Raw

private theorem primary_heq {f : Op} (lam : f=.lam) :
    HEq (Sum.inl () : Port (.op f)) (Sum.inl () : Port (.op .lam)) := by subst f; rfl

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
local notation "rhs" => s.right.net

/-- Reflect the ORIGINAL source binder prefix through a specified crossing
occurrence. The new prefix is literally part of the original target path;
the old and new middle contexts are related by an actual low writer. -/
theorem ActionLambdaOccurrence.prefix_writer_word {principal : SiteActionPrincipal site} {raw old aux ordinal}
    (cutAt : ActionLambdaOccurrence site principal raw old aux ordinal)
    (lam : s.passive=.lam) (bodyRole : HEq (Sum.inr aux : Port (.op s.passive)) lamBody)
    {a oldMiddle b : Context} (shape : PlugExcursions cut rhs raw a b)
    (sourcePrefix : Labelling site.net (cutAt.oldBefore++cutAt.front) a oldMiddle) :
    ∃ (branch : Aux s.active) (node : s.right.N) (ctx body : Port ((rhs).label node).sort)
      (targetPre targetTail : List (Endpoint site.reduce)) (newMiddle : Context),
      ActionLambdaCopy site branch node ∧((rhs).label node).sort=.op .lam ∧
      HEq ctx (Sum.inl () : Port (.op .lam)) ∧HEq body lamBody ∧
      raw.map (plugEnd (cut).label (rhs).label)=targetPre++(.inl ⟨.inr node,body⟩)::targetTail ∧
      targetPre.getLast?=some (site.reduce.wire (.inl ⟨.inr node,ctx⟩)) ∧
      Labelling site.reduce targetPre a newMiddle ∧
      Traversal s.low (.op s.active) (.inr branch) (.inl ()) newMiddle oldMiddle ∧
      accessWord site.reduce targetPre=accessWord site.net (cutAt.oldBefore++cutAt.front) := by
  have rawLabels := shape.labelling cut rhs
  rw [cutAt.raw_eq] at rawLabels
  obtain ⟨current,prefixRaw,suffixRaw⟩ := split_raw cut rhs rawLabels
  obtain ⟨last,rawLast⟩ := shape.last_outside cut rhs
  have suffixLast : (Sum.inl cutAt.entry::(cutAt.inside.map Sum.inr++
      Sum.inl (.inr (.inl (.inr cutAt.exit)))::cutAt.rawAfter) : List (PlugSegment cut rhs)).getLast?=some (.inl last) := by
    rw [cutAt.raw_eq,last_nonempty _ _ (by simp)] at rawLast
    exact rawLast
  have afterShape := suffixRaw.local_excursions cut rhs cutAt.entry last rfl suffixLast
  obtain ⟨blockOutput,insideLabels⟩ := through_view cut rhs (cutAt.cross.canonical site).nonempty afterShape
  obtain ⟨branch,node,ctx,body,insideTail,copy,isLam,ctxRole,bodyPortRole,insideSplit,writer⟩ :=
    cutAt.cross.body_writer site lam bodyRole insideLabels
  have sourceBlock := (cutAt.cross.canonical site).source_labels site insideLabels
  have frontNonempty : cutAt.front≠[] := by
    intro empty
    have bound := cutAt.cross.source_length site
    rw [empty,List.nil_append] at bound
    change 2≤1 at bound
    omega
  obtain ⟨sourceFront,sourceEnd⟩ := Labelling.before_lambda_body (g:=site.net) (.inr (.inr ()))
    (.inl ()) (.inr aux) (congrArg Kind.op lam) (primary_heq lam) bodyRole sourceBlock frontNonempty
  have prefixHead : ∃ first,(cutAt.rawBefore++[Sum.inl cutAt.entry]).head?=some (.inl first) := by
    have genericHead : ∀ {rs os},ActionCanonicalBlocks site principal rs os →∃ first,rs.head?=some (.inl first) := by
      intro rs os residual
      cases residual <;> exact ⟨_,rfl⟩
    exact genericHead cutAt.prefixResidual
  obtain ⟨first,prefixHead⟩ := prefixHead
  have prefixLast : (cutAt.rawBefore++[Sum.inl cutAt.entry]).getLast?=some (.inl cutAt.entry) := by simp
  have sourceBefore := cutAt.prefixResidual.source_labels site
    (prefixRaw.local_excursions cut rhs first cutAt.entry prefixHead prefixLast)
  have frontHead : cutAt.front.head?=some (site.outsideEnd cutAt.entry) := by
    cases front : cutAt.front with
    | nil => exact False.elim (frontNonempty front)
    | cons e es => simpa only [front,List.cons_append,List.head?_cons] using cutAt.start
  obtain ⟨frontTail,frontSplit⟩ := List.head?_eq_some_iff.mp frontHead
  have sourceWholePrefix : Labelling site.net (cutAt.oldBefore++cutAt.front) a blockOutput := by
    rw [frontSplit] at sourceFront ⊢
    exact sourceBefore.join sourceFront
  have same := sourceWholePrefix.output_unique sourcePrefix
  rw [same] at writer
  have entered := suffixRaw
  rw [insideSplit,List.map_cons,List.cons_append] at entered
  have entryLabels : PlugLabelling cut rhs
      [Sum.inl cutAt.entry,Sum.inr ((rhs).wire (.inl ⟨node,ctx⟩))] current current := by
    cases entered with
    | cons turn after =>
      have constant : ∀ {x : Endpoint cut} {y : Endpoint rhs} {d},
          PlugTurn cut rhs (.inl x) (.inr y) current d →current=d := by
        intro x y d step; cases step; rfl
      have contexts := constant turn
      subst contexts
      exact .cons turn (.single _ _)
  have prefixEntered := prefixRaw
  have newPrefixRaw := prefixEntered.splice cut rhs (.single (c:=cut) (r:=rhs)
      (Sum.inr ((rhs).wire (.inl ⟨node,ctx⟩))) current) (Sum.inl cutAt.entry)
      (Sum.inr ((rhs).wire (.inl ⟨node,ctx⟩))) prefixLast rfl (by
        cases entryLabels with | cons turn after => cases after; exact turn)
  let targetPre : List (Endpoint site.reduce) := (cutAt.rawBefore++[Sum.inl cutAt.entry,Sum.inr ((rhs).wire (.inl ⟨node,ctx⟩))]).map
    (plugEnd (cut).label (rhs).label)
  let targetTail : List (Endpoint site.reduce) :=
    (insideTail.map Sum.inr++ Sum.inl (.inr (.inl (.inr cutAt.exit)) : Endpoint cut)::cutAt.rawAfter).map
    (plugEnd (cut).label (rhs).label)
  refine ⟨branch,node,ctx,body,targetPre,targetTail,current,copy,isLam,ctxRole,bodyPortRole,?_,?_,?_,writer,?_⟩
  · have mapped := congrArg (List.map (plugEnd (cut).label (rhs).label)) cutAt.raw_eq
    simpa only [insideSplit,targetPre,targetTail,List.map_append,List.map_cons,List.map_nil,List.append_assoc,
      List.cons_append,List.singleton_append] using mapped
  · simp only [targetPre,List.getLast?_map,List.getLast?_append,List.getLast?_cons,
      List.getLast?_nil,Option.some_or,Option.map_some]
    exact congrArg some (plugRight_wire cut rhs (.inl ⟨node,ctx⟩)).symm
  · simpa only [targetPre,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append] using
      newPrefixRaw.actual cut rhs
  · have prefixShape := prefixRaw.local_excursions cut rhs first cutAt.entry prefixHead prefixLast
    have prefixWords := cutAt.prefixResidual.word site prefixShape
    have frontWords := cutAt.cross.front_word site cutAt.front rfl
    have sourceWord : accessWord site.net (cutAt.oldBefore++cutAt.front)=
        accessWord site.net (cutAt.oldBefore++[site.outsideEnd cutAt.entry]) := by
      have eqs := accessWord_overlap site.net cutAt.oldBefore (site.outsideEnd cutAt.entry) frontTail
      simpa only [←frontSplit,frontWords,List.append_nil] using eqs
    let base : List (Endpoint site.reduce) :=
      (cutAt.rawBefore++[Sum.inl cutAt.entry]).map (plugEnd (cut).label (rhs).label)
    have nonempty : base≠[] := by simp [base,List.map_append]
    have token := copy.context_token site isLam ctx ctxRole
    let departure : Endpoint site.reduce :=
      (plugEnd (cut).label (rhs).label) (.inr ((rhs).wire (.inl ⟨node,ctx⟩)))
    have physicalToken : arrivalWord site.reduce departure=[] := by
      exact (arrivalWord_plugRight cut rhs ((rhs).wire (.inl ⟨node,ctx⟩))).trans token
    have targetSplit : targetPre=base++[departure] := by
      simp only [targetPre,base,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append]
      rfl
    have targetWord : accessWord site.reduce targetPre=accessWord site.reduce base := by
      rw [targetSplit,accessWord_append site.reduce _ _ nonempty]
      simp only [List.flatMap_cons,List.flatMap_nil,physicalToken,List.append_nil]
    exact targetWord.trans (prefixWords.trans sourceWord.symm)
end
end Lamping.AG

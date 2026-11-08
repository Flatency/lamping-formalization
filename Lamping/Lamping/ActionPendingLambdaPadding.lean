import Lamping.Lamping.ActionPendingCanonicalAccess
namespace Lamping.AG
open Graph
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
private theorem append_last_nonempty {T : Type} (xs ys : List T) (nonempty : ys≠[]) :
    (xs++ys).getLast?=ys.getLast? := by
  cases eqs : ys.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp eqs))
  | some x => simp only [List.getLast?_append,eqs,Option.some_or]

/-- Join two actual finite paths at their SAME assignment, keeping the shared
outside segment once. -/
theorem PlugExcursions.overlap_join {raw : List (PlugSegment c r)} {a m : Context}
    (left : PlugExcursions c r raw a m) {pre : List (PlugSegment c r)} {pivot : Endpoint c}
    (split : raw=pre++[.inl pivot]) {tail : List (PlugSegment c r)} {b : Context}
    (right : PlugExcursions c r (.inl pivot::tail) m b) :
    PlugExcursions c r (pre++(.inl pivot::tail)) a b := by
  induction left generalizing pre pivot tail b with
  | single e a =>
    have count := congrArg List.length split
    simp only [List.length_singleton,List.length_append] at count
    have empty : pre=[] := List.length_eq_zero_iff.mp (by omega)
    subst pre
    have same : e=pivot := Sum.inl.inj (List.cons.inj split).1
    subst e
    exact right
  | @outside e f xs a m output turn rest ih =>
    cases pre with
    | nil => cases split
    | cons x pre =>
      obtain ⟨firstEq,tailEq⟩ := List.cons.inj split
      subst x
      have joined := ih tailEq right
      cases pre with
      | nil =>
        have same := (List.cons.inj tailEq).1
        rw [←same] at joined ⊢
        exact .outside turn joined
      | cons y ys =>
        have same := (List.cons.inj tailEq).1
        rw [←same] at joined ⊢
        exact .outside turn joined
  | @through e entry exit xs a m output inside arrival rest ih =>
    have last : (.inl (.inr (.inl (.inr exit)))::xs : List (PlugSegment c r)).getLast?=
        some (.inl pivot) := by
      have last := congrArg List.getLast? split
      have suffix := append_last_nonempty
        (.inl e::inside.edges.map (Sum.inr : Endpoint r → PlugSegment c r))
        (.inl (.inr (.inl (.inr exit)))::xs) (by simp)
      change ((.inl e::inside.edges.map Sum.inr)++(.inl (.inr (.inl (.inr exit)))::xs)).getLast?=_ at last
      rw [suffix] at last
      simpa only [List.getLast?_concat] using last
    obtain ⟨restPre,restSplit⟩ := List.getLast?_eq_some_iff.mp last
    have prefixEq : pre=.inl e::(inside.edges.map Sum.inr++restPre) := by
      have joined : pre++[Sum.inl pivot]=
          (Sum.inl e::(inside.edges.map Sum.inr++restPre))++[Sum.inl pivot] := by
        rw [←split]
        change (Sum.inl e::inside.edges.map Sum.inr)++(Sum.inl (.inr (.inl (.inr exit)))::xs)=_
        rw [restSplit]
        simp only [List.cons_append,List.append_assoc]
      exact List.append_cancel_right joined
    have joined := ih restSplit right
    rw [prefixEq,List.cons_append,List.append_assoc]
    cases restPre with
    | nil =>
      have same := (List.cons.inj restSplit).1
      rw [←same] at joined ⊢
      exact .through inside arrival joined
    | cons x restPre =>
      have same := (List.cons.inj restSplit).1
      rw [←same] at joined ⊢
      exact .through inside arrival joined
end
end Lamping.AG
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.lam i j lt) V) site.closed
private abbrev lambdaRight (i j : Nat) (lt : i<j) := (Schema.croAction Op.lam i j lt).right.net
local notation "rhs" => lambdaRight i j lt

/-- The actual copied lambda context permits these specific lambda-body and
low-writer segments. This is not a path completion principle. -/
theorem PendingRhsBlock.cro_lambda_padding
    {raw : List (PlugSegment cut rhs)} {a b : Context}
    (pending : PendingRhsBlock cut rhs raw a b)
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),.inl ()⟩))) :
    ∃ path : LocalPath rhs (.inl ()) (.inr true) b (InitialOffsets.croAt i b),
      pending.inside=[.inr (.inl (.inl ()))] ∧
      pending.enter=.inl () ∧pending.middle=b ∧
      path.edges=pending.inside++[.inl ⟨.inl (),.inr true⟩,.inl ⟨.inr true,.inl ()⟩] ∧
      PlugExcursions cut rhs
        (.inl pending.last::(path.edges.map Sum.inr++[.inl (.inr (.inl (.inr (.inr true))))]))
        b (InitialOffsets.croAt i b) ∧
      raw++[.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
        .inl (.inr (.inl (.inr (.inr true))))]=
        pending.pre++(.inl pending.last::(path.edges.map Sum.inr++
          [.inl (.inr (.inl (.inr (.inr true))))])).tail := by
  obtain ⟨entry,shape,contexts⟩ := unaryRight_lam_context_prefix .cro (Bij.refl Unit) i (j-1)
    pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead finish
  let path : LocalPath rhs (.inl ()) (.inr true) b (InitialOffsets.croAt i b) := {
    edges := [.inr (.inl (.inl ())),.inl ⟨.inl (),.inr true⟩,.inl ⟨.inr true,.inl ()⟩]
    start := rfl
    finish := rfl
    labeling := .cons (LabelledTurn.node (g:=rhs) (.inl ()) _ _ (.direct (.lamBody b)))
      (.cons (LabelledTurn.node (g:=rhs) (.inr true) _ _
        (.direct (InitialOffsets.Event.apply_rel (.cro i) b))) (.single _ _)) }
  have arrival : (cut).wire pending.last=.inr (.inl (.inr (.inl ()))) := by
    rw [pending.arrival,entry]
  refine ⟨path,shape,entry,contexts,?_,?_,?_⟩
  · rw [shape]; rfl
  · exact .through path arrival (.single _ _)
  · have eqs := pending.equation
    rw [shape] at eqs
    exact (congrArg (fun xs => xs++[.inr (.inl ⟨.inl (),.inr true⟩),
      .inr (.inl ⟨.inr true,.inl ()⟩),.inl (.inr (.inl (.inr (.inr true))))]) eqs).trans
      (by simp only [List.append_assoc];rfl)

/-- Join the real pending prefix to its finite padding and construct its
canonical source on the SAME supplied principal. -/
theorem PendingRhsBlock.cro_lambda_canonical_completion (principal : SiteActionPrincipal site)
    {raw : List (PlugSegment cut rhs)} {a b : Context}
    (pending : PendingRhsBlock cut rhs raw a b)
    (first : Endpoint cut) (head : raw.head?=some (.inl first))
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),.inl ()⟩))) :
    ∃ old, ActionCanonicalBlocks site principal
        (raw++[.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]) old ∧
      Labelling site.net old a (InitialOffsets.croAt i b) ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.outsideEnd (.inr (.inl (.inr (.inr true))))) ∧
      PlugExcursions cut rhs
        (raw++[.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]) a (InitialOffsets.croAt i b) := by
  obtain ⟨path,shape,entry,contexts,pathEq,rightPath,paddedEq⟩ := pending.cro_lambda_padding site finish
  obtain ⟨before,preEq⟩ := List.getLast?_eq_some_iff.mp pending.prefixLast
  have prePath := pending.prefixPath
  rw [contexts] at prePath
  have joined := prePath.overlap_join cut rhs preEq rightPath
  have whole : PlugExcursions cut rhs
      (raw++[.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
        .inl (.inr (.inl (.inr (.inr true))))]) a (InitialOffsets.croAt i b) := by
    rw [paddedEq]
    simpa only [preEq,List.append_assoc,List.cons_append,List.tail_cons] using joined
  have starts : (raw++[.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
      .inl (.inr (.inl (.inr (.inr true))))] : List (PlugSegment cut rhs)).head?=some (.inl first) := by
    rw [List.head?_append,head,Option.some_or]
  have ends : (raw++[.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
      .inl (.inr (.inl (.inr (.inr true))))] : List (PlugSegment cut rhs)).getLast?=
        some (.inl (.inr (.inl (.inr (.inr true))))) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨old,relation,labels,start,last⟩ := whole.action_canonical_lift site (.cro .lam i j lt)
    principal first (.inr (.inl (.inr (.inr true)))) starts ends
  exact ⟨old,relation,labels,start,last,whole⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.lam i j lt) V) site.closed
private abbrev braLambdaRight (i j : Nat) (lt : i<j) := (Schema.braAction Op.lam i j lt).right.net
local notation "rhs" => braLambdaRight i j lt

/-- The corresponding concrete bra writer padding. -/
theorem PendingRhsBlock.bra_lambda_padding
    {raw : List (PlugSegment cut rhs)} {a b : Context}
    (pending : PendingRhsBlock cut rhs raw a b)
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),.inl ()⟩))) :
    ∃ path : LocalPath rhs (.inl ()) (.inr true) b (InitialOffsets.braAt i b),
      pending.inside=[.inr (.inl (.inl ()))] ∧
      pending.enter=.inl () ∧pending.middle=b ∧
      path.edges=pending.inside++[.inl ⟨.inl (),.inr true⟩,.inl ⟨.inr true,.inl ()⟩] ∧
      PlugExcursions cut rhs
        (.inl pending.last::(path.edges.map Sum.inr++[.inl (.inr (.inl (.inr (.inr true))))]))
        b (InitialOffsets.braAt i b) ∧
      raw++[.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
        .inl (.inr (.inl (.inr (.inr true))))]=
        pending.pre++(.inl pending.last::(path.edges.map Sum.inr++
          [.inl (.inr (.inl (.inr (.inr true))))])).tail := by
  obtain ⟨entry,shape,contexts⟩ := unaryRight_lam_context_prefix .bra (Bij.refl Unit) i (j+1)
    pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead finish
  let path : LocalPath rhs (.inl ()) (.inr true) b (InitialOffsets.braAt i b) := {
    edges := [.inr (.inl (.inl ())),.inl ⟨.inl (),.inr true⟩,.inl ⟨.inr true,.inl ()⟩]
    start := rfl
    finish := rfl
    labeling := .cons (LabelledTurn.node (g:=rhs) (.inl ()) _ _ (.direct (.lamBody b)))
      (.cons (LabelledTurn.node (g:=rhs) (.inr true) _ _
        (.direct (InitialOffsets.Event.apply_rel (.bra i) b))) (.single _ _)) }
  have arrival : (cut).wire pending.last=.inr (.inl (.inr (.inl ()))) := by
    rw [pending.arrival,entry]
  refine ⟨path,shape,entry,contexts,?_,?_,?_⟩
  · rw [shape]; rfl
  · exact .through path arrival (.single _ _)
  · have eqs := pending.equation
    rw [shape] at eqs
    exact (congrArg (fun xs => xs++[.inr (.inl ⟨.inl (),.inr true⟩),
      .inr (.inl ⟨.inr true,.inl ()⟩),.inl (.inr (.inl (.inr (.inr true))))]) eqs).trans
      (by simp only [List.append_assoc];rfl)

/-- The corresponding bra-action canonical padded whole. -/
theorem PendingRhsBlock.bra_lambda_canonical_completion (principal : SiteActionPrincipal site)
    {raw : List (PlugSegment cut rhs)} {a b : Context}
    (pending : PendingRhsBlock cut rhs raw a b)
    (first : Endpoint cut) (head : raw.head?=some (.inl first))
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),.inl ()⟩))) :
    ∃ old, ActionCanonicalBlocks site principal
        (raw++[.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]) old ∧
      Labelling site.net old a (InitialOffsets.braAt i b) ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.outsideEnd (.inr (.inl (.inr (.inr true))))) ∧
      PlugExcursions cut rhs
        (raw++[.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]) a (InitialOffsets.braAt i b) := by
  obtain ⟨path,shape,entry,contexts,pathEq,rightPath,paddedEq⟩ := pending.bra_lambda_padding site finish
  obtain ⟨before,preEq⟩ := List.getLast?_eq_some_iff.mp pending.prefixLast
  have prePath := pending.prefixPath
  rw [contexts] at prePath
  have joined := prePath.overlap_join cut rhs preEq rightPath
  have whole : PlugExcursions cut rhs
      (raw++[.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
        .inl (.inr (.inl (.inr (.inr true))))]) a (InitialOffsets.braAt i b) := by
    rw [paddedEq]
    simpa only [preEq,List.append_assoc,List.cons_append,List.tail_cons] using joined
  have starts : (raw++[.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
      .inl (.inr (.inl (.inr (.inr true))))] : List (PlugSegment cut rhs)).head?=some (.inl first) := by
    rw [List.head?_append,head,Option.some_or]
  have ends : (raw++[.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
      .inl (.inr (.inl (.inr (.inr true))))] : List (PlugSegment cut rhs)).getLast?=
        some (.inl (.inr (.inl (.inr (.inr true))))) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨old,relation,labels,start,last⟩ := whole.action_canonical_lift site (.bra .lam i j lt)
    principal first (.inr (.inl (.inr (.inr true)))) starts ends
  exact ⟨old,relation,labels,start,last,whole⟩
end
end Lamping.AG

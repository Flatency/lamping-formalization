import Lamping.Lamping.ActionLambdaLocalOccurrences
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
local notation "rhs" => s.right.net

private theorem right_block_unique {L R : Type} {xs ys : List R} {x y : L}
    {tail post : List (L⊕R)}
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

private theorem outside_view {e f : Endpoint cut} {tail} {a b : Context}
    (shape : PlugExcursions cut rhs (.inl e::.inl f::tail) a b) :
    ∃ middle,LabelledTurn cut ((cut).wire e) f a middle ∧
      PlugExcursions cut rhs (.inl f::tail) middle b := by
  generalize eqs : (.inl e::.inl f::tail : List (PlugSegment cut rhs))=raw at shape
  cases shape with
  | single => cases eqs
  | outside turn after => cases eqs; exact ⟨_,turn,after⟩
  | through path arrival after =>
    have nonempty := path.labeling.nonempty
    cases split : path.edges with
    | nil => exact False.elim (nonempty split)
    | cons h xs => rw [split,List.map_cons,List.cons_append] at eqs; cases eqs

private theorem through_view {e : Endpoint cut} {exit : s.Frontier} {inside tail} {a b : Context}
    (nonempty : inside≠[])
    (shape : PlugExcursions cut rhs
      (.inl e::(inside.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::tail)) a b) :
    ∃ middle,Labelling rhs inside a middle ∧
      PlugExcursions cut rhs (.inl (.inr (.inl (.inr exit)))::tail) middle b := by
  generalize eqs : (.inl e::(inside.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::tail) :
    List (PlugSegment cut rhs))=raw at shape
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
    obtain ⟨edgeEq,exitEq,tailEq⟩ := right_block_unique initial.2
    have exits := Sum.inr.inj (Sum.inl.inj (Sum.inr.inj exitEq))
    subst other
    subst post
    exact ⟨middle,by rw [edgeEq]; exact path.labeling,after⟩

private theorem outside_not_passive_aux {e f : Endpoint cut} {a b : Context}
    (turn : LabelledTurn cut e f a b) (aux : Aux s.passive) :
    site.outsideEnd f≠(.inl ⟨.inr (.inr ()),.inr aux⟩ : Endpoint site.net) := by
  intro same
  cases turn with
  | node node p q rule =>
    change (.inl ⟨.inl node,q⟩ : Endpoint site.net)=.inl ⟨.inr (.inr ()),.inr aux⟩ at same
    cases same
  | transparent w d a =>
    change (.inr (.inr (.inl w,!d)) : Endpoint site.net)=.inl ⟨.inr (.inr ()),.inr aux⟩ at same
    cases same

/-- Finite decomposition at one specified removed-lambda auxiliary departure.
The selected source turn is the crossing's final front/rest overlap. The
already traversed blocks are retained as a canonical prefix residual. -/
structure ActionLambdaOccurrence (principal : SiteActionPrincipal site)
    (raw : List (PlugSegment cut rhs)) (old : List (Endpoint site.net))
    (aux : Aux s.passive) (ordinal : Nat) where
  rawBefore : List (PlugSegment cut rhs)
  oldBefore : List (Endpoint site.net)
  entry : Endpoint cut
  inside : List (Endpoint rhs)
  front : List (Endpoint site.net)
  exit : s.Frontier
  rawAfter : List (PlugSegment cut rhs)
  oldAfter : List (Endpoint site.net)
  cross : ActionLambdaCross site principal aux inside (front++[.inl ⟨.inr (.inr ()),.inr aux⟩])
  raw_eq : raw=rawBefore++ .inl entry::(inside.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::rawAfter)
  old_eq : old=oldBefore++front++(.inl ⟨.inr (.inr ()),.inr aux⟩)::oldAfter
  position : oldBefore.length+front.length=ordinal
  start : (front++[(.inl ⟨.inr (.inr ()),.inr aux⟩ : Endpoint site.net)]).head?=some (site.outsideEnd entry)
  prefixResidual : ActionCanonicalBlocks site principal (rawBefore++[.inl entry])
    (oldBefore++[site.outsideEnd entry])
  suffixResidual : ActionCanonicalBlocks site principal
    (.inl (.inr (.inl (.inr exit)))::rawAfter) ((.inl ⟨.inr (.inr ()),.inr aux⟩)::oldAfter)

theorem ActionLambdaOccurrence.prefix_head {principal : SiteActionPrincipal site} {raw old aux ordinal}
    (cutAt : ActionLambdaOccurrence site principal raw old aux ordinal) :
    (cutAt.rawBefore++[Sum.inl cutAt.entry]).head?=raw.head? := by
  apply Eq.trans _ (congrArg List.head? cutAt.raw_eq).symm
  cases cutAt.rawBefore <;> rfl

/-- Locate the actual source auxiliary occurrence by its positive ordinal.
At equality with front.length the turn belongs to this complete crossing,
rather than being discarded as an unhandled seam in the next block. -/
theorem ActionCanonicalBlocks.split_lambda_occurrence {principal : SiteActionPrincipal site} {raw old}
    (relation : ActionCanonicalBlocks site principal raw old) (lam : s.passive=.lam)
    {a b : Context} (shape : PlugExcursions cut rhs raw a b)
    (aux : Aux s.passive) (ordinal : Nat) (positive : 0<ordinal)
    (point : old[ordinal]?=some (.inl ⟨.inr (.inr ()),.inr aux⟩)) :
    Nonempty (ActionLambdaOccurrence site principal raw old aux ordinal) := by
  induction relation generalizing ordinal a b with
  | single e =>
    cases ordinal with
    | zero => omega
    | succ n => cases point
  | @outside e f tail old rest ih =>
    obtain ⟨middle,turn,after⟩ := outside_view site shape
    cases ordinal with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        have atHead : old.head?=some (.inl ⟨.inr (.inr ()),.inr aux⟩) := by
          simpa only [List.getElem?_cons_succ,List.head?_eq_getElem?] using point
        have same := Option.some.inj ((rest.head site rfl).symm.trans atHead)
        exact False.elim (outside_not_passive_aux site turn aux same)
      | succ n =>
        obtain ⟨cutAt⟩ := ih after (n+1) (by omega) point
        have head : (cutAt.rawBefore++[Sum.inl cutAt.entry]).head?=some (.inl f) := cutAt.prefix_head site
        obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp head
        have before := cutAt.prefixResidual
        rw [split] at before
        refine ⟨⟨.inl e::cutAt.rawBefore,site.outsideEnd e::cutAt.oldBefore,cutAt.entry,cutAt.inside,
          cutAt.front,cutAt.exit,cutAt.rawAfter,cutAt.oldAfter,cutAt.cross,?_,?_,?_,cutAt.start,?_,cutAt.suffixResidual⟩⟩
        · simpa only [List.cons_append] using congrArg (Sum.inl e::·) cutAt.raw_eq
        · simpa only [List.cons_append] using congrArg (site.outsideEnd e::·) cutAt.old_eq
        · simp only [List.length_cons]; have pos := cutAt.position; omega
        · simpa only [List.cons_append,←split] using ActionCanonicalBlocks.outside (e:=e) before
  | @through e exit tail old inside front route start rest ih =>
    obtain ⟨middle,insideLabels,after⟩ := through_view site route.nonempty shape
    by_cases within : ordinal≤front.length
    · have oldHead := rest.head site rfl
      have localPoint : (front++[site.outsideEnd (.inr (.inl (.inr exit)))])[ordinal]?=
          some (.inl ⟨.inr (.inr ()),.inr aux⟩) := by
        by_cases strict : ordinal<front.length
        · rw [List.getElem?_append_left strict] at point ⊢
          exact point
        · have equal : ordinal=front.length := by omega
          rw [equal,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at point ⊢
          simpa only [←List.head?_eq_getElem?,oldHead] using point
      obtain ⟨cross,last⟩ := route.lambda_aux_occurrence site lam insideLabels aux ordinal positive localPoint
      have equal : ordinal=front.length := by
        simp only [List.length_append,List.length_cons,List.length_nil] at last
        omega
      have exitEq : site.outsideEnd (.inr (.inl (.inr exit)))=(.inl ⟨.inr (.inr ()),.inr aux⟩ : Endpoint site.net) := by
        rw [equal,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at localPoint
        exact Option.some.inj localPoint
      obtain ⟨oldTail,oldSplit⟩ := List.head?_eq_some_iff.mp oldHead
      rw [exitEq] at oldSplit
      refine ⟨⟨[],[],e,inside,front,exit,tail,oldTail,?_,rfl,?_,?_,?_,.single e,?_⟩⟩
      · rw [←exitEq]; exact cross
      · simp only [oldSplit,List.nil_append]
      · simpa only [List.length_nil,Nat.zero_add] using equal.symm
      · rw [←exitEq]; exact start
      · rw [←oldSplit]; exact rest
    · have bound : front.length≤ordinal := by omega
      have beyond : 0<ordinal-front.length := by omega
      rw [List.getElem?_append_right bound] at point
      obtain ⟨cutAt⟩ := ih after (ordinal-front.length) beyond point
      have head : (cutAt.rawBefore++[Sum.inl cutAt.entry]).head?=some (.inl (.inr (.inl (.inr exit)))) := cutAt.prefix_head site
      obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp head
      have before := cutAt.prefixResidual
      rw [split] at before
      refine ⟨⟨.inl e::(inside.map Sum.inr++cutAt.rawBefore),front++cutAt.oldBefore,cutAt.entry,cutAt.inside,
        cutAt.front,cutAt.exit,cutAt.rawAfter,cutAt.oldAfter,cutAt.cross,?_,?_,?_,cutAt.start,?_,cutAt.suffixResidual⟩⟩
      · simpa only [List.cons_append,List.append_assoc] using
          congrArg (fun xs => Sum.inl e::(inside.map Sum.inr++xs)) cutAt.raw_eq
      · simpa only [List.append_assoc] using congrArg (front++·) cutAt.old_eq
      · rw [List.length_append]; have pos := cutAt.position; omega
      · simpa only [List.cons_append,List.append_assoc,←split] using
          ActionCanonicalBlocks.through inside front route start before
end
end Lamping.AG

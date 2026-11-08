import Lamping.Lamping.ActionLocalWords
import Lamping.Lamping.ActionCanonicalAssembly
import Lamping.Lamping.ActionResidualReplay
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private def emission : PlugSegment cut s.right.net → Path :=
  Sum.elim (arrivalWord cut) (arrivalWord s.right.net)

private def rawWord : List (PlugSegment cut s.right.net) → Path
  | [] => []
  | _::tail => tail.flatMap (emission site)

private theorem physical_word (raw : List (PlugSegment cut s.right.net)) :
    accessWord site.reduce (raw.map (plugEnd (cut).label s.right.net.label))=rawWord site raw := by
  have actual (e : PlugSegment cut s.right.net) :
      arrivalWord site.reduce ((plugEnd (cut).label s.right.net.label) e)=emission site e := by
    cases e with
    | inl e => exact arrivalWord_plugLeft cut s.right.net e
    | inr e => exact arrivalWord_plugRight cut s.right.net e
  cases raw with
  | nil => rfl
  | cons e tail =>
    change (tail.map (plugEnd (cut).label s.right.net.label)).flatMap (arrivalWord site.reduce)=_
    rw [List.flatMap_map]
    exact congrArg (fun f => tail.flatMap f) (funext actual)

private theorem outside_emission {e f : Endpoint cut} {a b : Context}
    (turn : LabelledTurn cut ((cut).wire e) f a b) :
    arrivalWord site.net (site.outsideEnd f)=arrivalWord cut f := by
  rcases f with ⟨node,p⟩ | ((boundary|frontier)|⟨vertex,direction⟩)
  · rfl
  · exact False.elim (turn.reverse.not_boundary (.inl boundary) rfl)
  · exact False.elim (turn.reverse.not_boundary (.inr frontier) rfl)
  · rfl

private theorem overlap_word (front : List (Endpoint site.net)) (nonempty : front≠[])
    (last : Endpoint site.net) (post : List (Endpoint site.net)) :
    accessWord site.net (front++last::post)=
      accessWord site.net (front++[last])++accessWord site.net (last::post) := by
  cases front with
  | nil => exact False.elim (nonempty rfl)
  | cons e front =>
    simp only [List.cons_append,accessWord,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc]

private theorem local_length {principal : SiteActionPrincipal site} {rhs old}
    (relation : ActionCanonicalLocal site principal rhs old) : 2≤old.length := by
  cases relation with
  | fan relation => cases relation <;> simp [SiteActionPrincipal.crossing,PathSite.passiveCanonical,reverseEdges]
  | cro relation => cases relation <;> simp [SiteActionPrincipal.crossing,PathSite.passiveCanonical,reverseEdges]
  | bra relation => cases relation <;> simp [SiteActionPrincipal.crossing,PathSite.passiveCanonical,reverseEdges]

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
  | outside turn after => cases eqs; exact ⟨_,turn,after⟩
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
      PlugExcursions cut s.right.net (.inl (.inr (.inl (.inr exit)))::tail) middle b := by
  generalize eqs : (.inl e::(inside.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::tail) :
    List (PlugSegment cut s.right.net))=raw at shape
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
    exact ⟨entry,middle,by rw [edgeEq]; exact path.start,after⟩

/-- Actual raw excursion shape is essential: a bare outside constructor
does not certify that its departure is a real kept-node/W turn. -/
theorem ActionCanonicalBlocks.word {principal : SiteActionPrincipal site} {raw old}
    (relation : ActionCanonicalBlocks site principal raw old) {a b : Context}
    (shape : PlugExcursions cut s.right.net raw a b) :
    accessWord site.reduce (raw.map (plugEnd (cut).label s.right.net.label))=accessWord site.net old := by
  rw [physical_word]
  induction relation generalizing a b with
  | single e => rfl
  | @outside e f tail old rest ih =>
    obtain ⟨middle,turn,after⟩ := outside_view site shape
    obtain ⟨post,oldSplit⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
    have tailWord := ih after
    rw [oldSplit] at tailWord ⊢
    change arrivalWord cut f++tail.flatMap (emission site)=
      arrivalWord site.net (site.outsideEnd f)++post.flatMap (arrivalWord site.net)
    change tail.flatMap (emission site)=post.flatMap (arrivalWord site.net) at tailWord
    rw [tailWord,outside_emission site turn]
  | @through e exit tail old inside front route start rest ih =>
    obtain ⟨entry,middle,insideHead,after⟩ := through_view site (route.nonempty site) shape
    obtain ⟨post,oldSplit⟩ := List.head?_eq_some_iff.mp (rest.head site rfl)
    have tailWord := ih after
    have positive : front≠[] := by
      have length := local_length site route
      simp only [List.length_append,List.length_singleton] at length
      intro empty; rw [empty] at length; simp at length
    have localWord := route.word site
    have insideWord := accessTokens_eq_accessWord s.right.net entry insideHead
    rw [oldSplit,overlap_word site front positive]
    simp only [rawWord,List.flatMap_append,List.flatMap_cons]
    change (inside.map Sum.inr).flatMap (emission site)++
      (arrivalWord cut (.inr (.inl (.inr exit)))++tail.flatMap (emission site))=_
    rw [List.flatMap_map]
    change inside.flatMap (arrivalWord s.right.net)++([]++tail.flatMap (emission site))=_
    change tail.flatMap (emission site)=accessWord site.net old at tailWord
    rw [oldSplit] at tailWord
    rw [localWord,←insideWord]
    exact congrArg (fun xs => accessTokens s.right.net inside++xs) tailWord

/-- An actual outside-ended target path has a same-assignment source
ancestor with precisely the same syntax word. The raw shape and all local
word equalities are discharged by the actual action, not caller certificates. -/
theorem PathSite.action_canonical_ancestor_word (action : IsAction s)
    {es : List (Endpoint site.reduce)} {a b : Context} (labels : Labelling site.reduce es a b)
    (first last : Endpoint cut)
    (head : es.head?=some (AG.plugLeft cut s.right.net first))
    (finish : es.getLast?=some (AG.plugLeft cut s.right.net last)) :
    ∃ old,Labelling site.net old a b ∧old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.outsideEnd last) ∧accessWord site.reduce es=accessWord site.net old := by
  obtain ⟨principal,old,relation,oldLabels,oldHead,oldLast⟩ :=
    site.action_canonical_ancestor action labels first last head finish
  have shape := labels.local_excursions cut s.right.net first last head finish
  have words := relation.word site shape
  rw [plug_decomposition_flatten] at words
  exact ⟨old,oldLabels,oldHead,oldLast,words⟩
end
end Lamping.AG

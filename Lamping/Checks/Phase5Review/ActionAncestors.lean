import Lamping.Lamping.ActionWholeWords
import Lamping.Lamping.ActionCanonicalWords
import Lamping.Lamping.ActionCanonicalAssembly
import Lamping.Lamping.ActionAncestor
import Lamping.Lamping.PlugPrefixExcursions
import Lamping.Lamping.Fixtures
namespace Lamping.Checks.Phase5Review.ActionAncestors
open AG Graph
private def kept : Empty → Label signature := Empty.elim
private abbrev schema : Schema := .fanAction .app 2 3 (by decide)
private def site : PathSite schema kept (B:=Bool⊕Bool) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl k,_⟩ => nomatch k
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inl _),.inr a⟩ => .inr (.inl (.inl a))
      | .inl ⟨.inr (.inr _),.inr a⟩ => .inl ⟨.inr (.inr ()),.inr (!a)⟩
      | .inr (.inl (.inl a)) => .inl ⟨.inr (.inl ()),.inr a⟩
      | .inr (.inl (.inr a)) => .inr (.inl (.inr (!a)))
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
      · exact nomatch k
      · cases u; cases p with | inl u => cases u; rfl | inr a => cases a <;> rfl
      · cases u; cases p with | inl u => cases u; rfl | inr a => cases a <;> rfl
      · rfl
      · cases a <;> rfl
      · exact nomatch w
      · cases v; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩)) same
      · exact nomatch k
      · cases p with | inl u => cases same | inr a => cases a <;> cases same
      · cases p with | inl u => cases same | inr a => cases a <;> cases same
      · cases same
      · cases a <;> cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases v; cases b <;> rfl

private abbrev actualCut := cutFragment site.net (pathPartition schema Unit) site.closed
private def seam : Endpoint actualCut := .inr (.inl (.inr (.inr true)))
private def input (tail : Context) := (Context.empty.cons (.star .empty)).replace 2 (tail.cons (.o .empty))
private def inside (tail : Context) := fanActionPassiveApp 2 0 false (Context.empty.cons (.star .empty)) tail .empty
private def blocks (tail : Context) : PlugExcursions actualCut schema.right.net
    (.inl seam::((inside tail).edges.map Sum.inr++ .inl seam::((inside tail).edges.map Sum.inr++[.inl seam])))
    (input tail) (input tail) :=
  .through (inside tail) rfl (.through (inside tail) rfl (.single seam (input tail)))
private def raw (tail : Context) : List (PlugSegment actualCut schema.right.net) :=
  .inl seam::((inside tail).edges.map Sum.inr++ .inl seam::((inside tail).edges.map Sum.inr++[.inl seam]))
private def edges (tail : Context) : List (Endpoint site.reduce) := (raw tail).map (plugEnd _ _)
theorem double_labels (tail : Context) : Labelling site.reduce (edges tail) (input tail) (input tail) :=
  ((blocks tail).labelling _ _).actual _ _
theorem double_ancestor (tail : Context) :
    ∃ old,ActionResidual site (edges tail) old ∧ Labelling site.net old (input tail) (input tail) ∧
      old.head?=some (site.outsideEnd seam) ∧old.getLast?=some (site.outsideEnd seam) :=
  site.action_ancestor (.fan .app 2 3 (by decide)) (double_labels tail) seam seam rfl rfl
example (tail : Context) : (edges tail).length=11 := rfl

/-- This real labelled partial tail reaches a newly copied app context, but
its last segment is inside the RHS and is not an outside endpoint. -/
private def partialEdges (tail : Context) := (edges tail).take 3
theorem partial_labels (tail : Context) : ∃ output,Labelling site.reduce (partialEdges tail) (input tail) output := by
  have split : edges tail=partialEdges tail++(edges tail).drop 3 := rfl
  have labels := double_labels tail
  rw [split] at labels
  exact labels.prefix (by simp [partialEdges,edges,raw])
theorem partial_not_outside (tail : Context) :
    ¬∃ last : Endpoint actualCut,(partialEdges tail).getLast?=some (AG.plugLeft actualCut _ last) := by
  rintro ⟨last,same⟩
  rcases last with ⟨n,p⟩ | ((b|f)|⟨w,d⟩)
  · exact nomatch n
  · cases same
  · cases same
  · exact nomatch w
example (tail : Context) : (partialEdges tail).getLast?=
    some (.inl ⟨.inr (.inr false),.inr false⟩) := rfl
example : site.reduce.wire (.inl ⟨.inr (.inr false),.inr false⟩)=
    .inl ⟨.inr (.inl false),appCtx⟩ := rfl
example : site.reduce.label (.inr (.inl false))=label .app 3 := rfl
#print axioms double_ancestor
#print axioms double_labels
#print axioms partial_not_outside
/-- The same valid new-proper-terminal prefix is captured by the new finite
prefix decomposition, while partial_not_outside still blocks the old wrapper. -/
theorem partial_prefix_excursions (tail : Context) : ∃ output,
    PlugPrefixExcursions actualCut schema.right.net
      ((partialEdges tail).map (plugEnd _ _).invFun) (input tail) output := by
  obtain ⟨output,labels⟩ := partial_labels tail
  exact ⟨output,labels.prefix_excursions actualCut schema.right.net seam rfl⟩
theorem partial_raw_reconstruction (tail : Context) : ∃ output,
    PlugLabelling actualCut schema.right.net
      ((partialEdges tail).map (plugEnd _ _).invFun) (input tail) output := by
  obtain ⟨output,blocks⟩ := partial_prefix_excursions tail
  exact ⟨output,blocks.labelling _ _⟩
#print axioms PlugLabelling.prefix_excursions
#print axioms partial_prefix_excursions
#print axioms partial_raw_reconstruction

theorem double_canonical_ancestor (tail : Context) :
    ∃ principal : SiteActionPrincipal site,∃ old,
      ActionCanonicalBlocks site principal ((edges tail).map (plugEnd _ _).invFun) old ∧
      Labelling site.net old (input tail) (input tail) ∧
      old.head?=some (site.outsideEnd seam) ∧old.getLast?=some (site.outsideEnd seam) :=
  site.action_canonical_ancestor (.fan .app 2 3 (by decide)) (double_labels tail) seam seam rfl rfl
#print axioms double_canonical_ancestor
/-- The actual one-W site retains the reverse app principal function token.
The source canonical forward/passive routes instead emit argument tokens. -/
theorem actual_one_w_canonical_words :
    ∃ principal : SiteActionPrincipal site,
      accessWord site.net (principal.crossing site false true)=[.arg] ∧
      accessWord site.net (reverseEdges (principal.crossing site false true))=[.fn] ∧
      accessWord site.net (site.passiveCanonical false true)=[.arg] := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  exact ⟨principal,principal.crossing_word site (.fan .app 2 3 (by decide)) false true,
    principal.reverse_crossing_word site (.fan .app 2 3 (by decide)) false true,
    site.passiveCanonical_word false true⟩

theorem actual_reverse_principal_token_is_not_empty :
    ∃ principal : SiteActionPrincipal site,
      accessWord site.net (reverseEdges (principal.crossing site false true))≠[] := by
  obtain ⟨principal,_forward,reverse,_passive⟩ := actual_one_w_canonical_words
  exact ⟨principal,by rw [reverse]; decide⟩
#print axioms actual_one_w_canonical_words
#print axioms actual_reverse_principal_token_is_not_empty
/-- Two genuine passive excursions share their outside delimiter. The whole
word contains both argument tokens, with neither deletion nor duplication. -/
theorem double_ancestor_word (tail : Context) :
    ∃ old,Labelling site.net old (input tail) (input tail) ∧
      accessWord site.net old=[.arg,.arg] := by
  obtain ⟨old,labels,_head,_last,word⟩ := site.action_canonical_ancestor_word
    (.fan .app 2 3 (by decide)) (double_labels tail) seam seam rfl rfl
  refine ⟨old,labels,?_⟩
  exact word.symm.trans rfl
#print axioms double_ancestor_word
/-- A bare outside constructor may name an arbitrary frontier twice. Its
source departure emits arg while the physical glue emits no token; genuine
excursion shape is therefore an essential premise of whole-word transport. -/
theorem bare_blocks_do_not_preserve_words :
    ∃ (principal : SiteActionPrincipal site) (raw : List (PlugSegment actualCut schema.right.net))
      (old : List (Endpoint site.net)),
      ActionCanonicalBlocks site principal raw old ∧
      accessWord site.reduce (raw.map (plugEnd actualCut.label schema.right.net.label))≠accessWord site.net old ∧
      ¬∃ a b,PlugExcursions actualCut schema.right.net raw a b := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  let f : Endpoint actualCut := .inr (.inl (.inr (.inr true)))
  let raw : List (PlugSegment actualCut schema.right.net) := [.inl f,.inl f]
  let old : List (Endpoint site.net) := [site.outsideEnd f,site.outsideEnd f]
  have relation : ActionCanonicalBlocks site principal raw old := .outside (.single f)
  have different : accessWord site.reduce (raw.map (plugEnd actualCut.label schema.right.net.label))≠
      accessWord site.net old := by
    change ([] : Lambda.Path)≠[.arg]
    decide
  exact ⟨principal,raw,old,relation,different,by
    rintro ⟨a,b,shape⟩
    exact different (relation.word site shape)⟩
#print axioms bare_blocks_do_not_preserve_words
end Lamping.Checks.Phase5Review.ActionAncestors










import Lamping.Lamping.MatchingSourceEdgeRealization
import Lamping.Lambda.PrerequisiteChains

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

/-- The actual occurrence and its rooted literal physical fragment. -/
structure OccurrenceFragment (current : LTerm) (g : Net signature N B W) (root : B)
    (position : Path) where
  term : LTerm
  environment : List Label
  context : SourcePort
  occurrence : SourceSubterm [] .external current position environment context term
  fragment : SourceEdgeFragment current g root (sourceEdge environment context term) position

/-- Choose once per current position, even when labelled edge values repeat. -/
abbrev OccurrenceFragmentSelection (current : LTerm) (g : Net signature N B W) (root : B) :=
  (position : Position current.erase) → OccurrenceFragment current g root position.val

 theorem Matches.occurrence_fragment_at {current : LTerm} {g : Net signature N B W} {root : B}
    (matching : Matches g root current.erase) (closed : Closed current.erase)
    (lookup : current.subterm p=some sub) : Nonempty (OccurrenceFragment current g root p) := by
  obtain ⟨environment,context,occurrence⟩ := SourceSubterm.of_lookup current lookup [] .external
  obtain ⟨fragment⟩ := matching.base_source_edge_fragment closed occurrence
  exact ⟨⟨sub,environment,context,occurrence,fragment⟩⟩

 theorem Matches.occurrence_fragment_selection {current : LTerm} {g : Net signature N B W} {root : B}
    (matching : Matches g root current.erase) (closed : Closed current.erase) :
    Nonempty (OccurrenceFragmentSelection current g root) := by
  classical
  have atPosition : ∀ position : Position current.erase,
      Nonempty (OccurrenceFragment current g root position.val) := by
    intro position
    have valid := position.property
    cases lookup : current.subterm position.val with
    | none =>
      rw [←LTerm.erase_subterm,lookup] at valid
      cases valid
    | some term => exact matching.occurrence_fragment_at closed lookup
  exact ⟨fun position=>Classical.choice (atPosition position)⟩

end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

private def chainEdgePosition (chain : PrerequisiteChain current p edges)
    (edge : {edge : Path // edge∈edges}) : Position current.erase :=
  ⟨edge.val,by
    rcases chain.eligible edge.property with ⟨parent,a,fn,arg,equal,lookup⟩ | ⟨a,body,lookup⟩
    · have actual : current.subterm edge.val=some fn := by
        rw [equal,LTerm.subterm_append,lookup]; cases fn <;> rfl
      rw [←LTerm.erase_subterm,actual]; rfl
    · rw [←LTerm.erase_subterm,lookup]; rfl⟩

/-- Canonical source-direction fragments, without flattening chase directions. -/
def canonicalChainImage (selection : OccurrenceFragmentSelection current g root)
    (chain : PrerequisiteChain current p edges) : List (List (Endpoint g)) :=
  edges.attach.map (fun edge=>(selection (chainEdgePosition chain edge)).fragment.segments)

theorem canonicalChainImage_length (selection : OccurrenceFragmentSelection current g root)
    (chain : PrerequisiteChain current p edges) :
    (canonicalChainImage selection chain).length=edges.length := by
  simp only [canonicalChainImage,List.length_map,List.length_attach]

theorem canonicalChainImage_nonempty (selection : OccurrenceFragmentSelection current g root)
    (chain : PrerequisiteChain current p edges) : canonicalChainImage selection chain≠[] := by
  intro empty
  have lengths := canonicalChainImage_length selection chain
  rw [empty] at lengths
  exact chain.nonempty (List.length_eq_zero_iff.mp lengths.symm)

def OccurrenceFragment.read (fragment : OccurrenceFragment current g root position)
    (forward : Bool) : List (Endpoint g) :=
  if forward then fragment.fragment.segments else reverseEdges fragment.fragment.segments

theorem OccurrenceFragment.read_reverse_endpoints
    (fragment : OccurrenceFragment current g root position) :
    (fragment.read false).head?=some fragment.fragment.toEndpoint ∧
    (fragment.read false).getLast?=some (g.wire fragment.fragment.fromEndpoint) :=
  fragment.fragment.reverse_endpoints

end
end Lamping.AG
/-
Occurrence-indexed supply for prerequisite representations. Canonical source
edge images and chase reading directions are deliberately separate. No
representation equality, graph isomorphism or REP invariant is defined here.
-/
namespace Lamping.Lambda.Labelled

inductive PrerequisiteReading (t : LTerm) : Path → List Path → List Bool → Prop where
  | redex_app (lookup : t.subterm p=some (.app a (.lam l b) arg)) :
      PrerequisiteReading t p [p++[.fn]] [true]
  | redex_lam (lookup : t.subterm p=some (.app a (.lam l b) arg)) :
      PrerequisiteReading t (p++[.fn]) [p++[.fn]] [false]
  | app (lookup : t.subterm p=some (.app a fn arg)) (notLambda : ∀ l b,fn≠.lam l b)
      (tail : PrerequisiteReading t (p++[.fn]) es directions) :
      PrerequisiteReading t p ((p++[.fn])::es) (true::directions)
  | lam (lookup : t.subterm (parent++[step])=some (.lam a body)) (notFunction : step≠.fn)
      (tail : PrerequisiteReading t parent es directions) :
      PrerequisiteReading t (parent++[step]) ((parent++[step])::es) (false::directions)
  | var (lookup : t.subterm leaf=some (.var a index))
      (binder : t.subterm parent=some (.lam origin body))
      (split : leaf=parent++(.body::rest)) (depth : index=binderDepth rest)
      (tail : PrerequisiteReading t parent es directions) :
      PrerequisiteReading t leaf es directions

 theorem PrerequisiteReading.chain (reading : PrerequisiteReading t p es directions) :
    PrerequisiteChain t p es := by
  induction reading with
  | redex_app lookup => exact .redex_app lookup
  | redex_lam lookup => exact .redex_lam lookup
  | app lookup notLambda _ ih => exact .app lookup notLambda ih
  | lam lookup notFunction _ ih => exact .lam lookup notFunction ih
  | var lookup binder split depth _ ih => exact .var lookup binder split depth ih

 theorem PrerequisiteReading.length (reading : PrerequisiteReading t p es directions) :
    directions.length=es.length := by
  induction reading <;> simp_all

 theorem PrerequisiteChain.reading (chain : PrerequisiteChain t p es) :
    ∃ directions,PrerequisiteReading t p es directions := by
  induction chain with
  | redex_app lookup => exact ⟨[true],.redex_app lookup⟩
  | redex_lam lookup => exact ⟨[false],.redex_lam lookup⟩
  | app lookup notLambda _ ih =>
    obtain ⟨directions,reading⟩ := ih
    exact ⟨true::directions,.app lookup notLambda reading⟩
  | lam lookup notFunction _ ih =>
    obtain ⟨directions,reading⟩ := ih
    exact ⟨false::directions,.lam lookup notFunction reading⟩
  | var lookup binder split depth _ ih =>
    obtain ⟨directions,reading⟩ := ih
    exact ⟨directions,.var lookup binder split depth reading⟩
end Lamping.Lambda.Labelled
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

theorem OccurrenceFragment.read_forward_endpoints
    (fragment : OccurrenceFragment current g root position) :
    (fragment.read true).head?=some fragment.fragment.fromEndpoint ∧
    (fragment.read true).getLast?=some (g.wire fragment.fragment.toEndpoint) :=
  ⟨fragment.fragment.start,fragment.fragment.finish⟩

theorem OccurrenceFragment.read_forward_assignment
    (fragment : OccurrenceFragment current g root position)
    (labels : Labelling g fragment.fragment.access.val a b) :
    ∃ middle,(fragment.fragment.before=[] ∧middle=a ∨
      Labelling g fragment.fragment.before a middle) ∧
      Labelling g (fragment.read true) middle b :=
  fragment.fragment.assignments a b labels

theorem OccurrenceFragment.read_reverse_assignment
    (fragment : OccurrenceFragment current g root position)
    (labels : Labelling g fragment.fragment.access.val a b) :
    ∃ middle,(fragment.fragment.before=[] ∧middle=a ∨
      Labelling g fragment.fragment.before a middle) ∧
      Labelling g (fragment.read false) b middle :=
  fragment.fragment.reverse_assignment labels

/-- Start nodes may differ (for example the two ends of one redex). The
canonical occurrence images depend on the actual edge list, not that start. -/
theorem canonicalChainImage_same_edges (selection : OccurrenceFragmentSelection current g root)
    (first : PrerequisiteChain current p edges) (second : PrerequisiteChain current q edges) :
    canonicalChainImage selection first=canonicalChainImage selection second := rfl

/-- Reading directions are interpreted per fragment. No ordinary/Forward
whole path or physical adjacency across a virtual binder jump is asserted. -/
def orientedChainImage (selection : OccurrenceFragmentSelection current g root)
    (reading : PrerequisiteReading current p edges directions) : List (List (Endpoint g)) :=
  List.zipWith (fun block forward=>if forward then block else reverseEdges block)
    (canonicalChainImage selection reading.chain) directions

theorem orientedChainImage_length (selection : OccurrenceFragmentSelection current g root)
    (reading : PrerequisiteReading current p edges directions) :
    (orientedChainImage selection reading).length=edges.length := by
  simp only [orientedChainImage,List.length_zipWith,canonicalChainImage_length,reading.length]
  omega

end
end Lamping.AG
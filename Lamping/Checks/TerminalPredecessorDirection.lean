import Lamping.Lamping.TerminalPredecessorDirection
import Lamping.Checks.TerminalHeadSuppliers
import Lamping.Checks.FanSuccessfulReachable

namespace Lamping.Checks.TerminalPredecessorDirectionChecks
open Graph Lambda Lambda.Labelled AG

namespace Larger
open TerminalHeadSuppliersChecks.Larger
open NormalFalseCanonicalOriginalComparisonChecks.Terminal

theorem actual_distinct_start_terminal :
    leftCut.forward=rightCut.forward ∧leftCut.before.length=1 ∧rightCut.before.length=1 ∧
    leftCut.after=[] ∧rightCut.after=[] ∧([.arg] : Path)≠[.arg,.body] := by
  have matching := encode_closed_matches current.erase targetClosed 0
  obtain ⟨selection⟩ := matching.occurrence_fragment_selection targetClosed
  have physical : SameChainRepresentation selection leftChain rightChain := rfl
  have actual := actual_terminal_predecessor_direction_eq matching selection leftChain rightChain
    physical leftCut rightCut rfl (by decide) rfl rfl
  exact ⟨actual,rfl,rfl,rfl,rfl,by decide⟩
end Larger

namespace Fan
open FanSuccessfulChains
abbrev F : List Path := [[.fn]]
abbrev degree : Label := .atom 2
abbrev edges : List Path := [xVar,[.fn]]
abbrev node : LTerm := match current with | .app _ fn _ => fn | t => t

def old : Marked.RelativeOldHistory F [[.fn]] (Marked.mark F original.erase)
    FanSuccessfulReachable.endpoint :=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.nil _)
theorem selected (p : Path) (member : p∈F) : original.degreeAt p=some degree := by
  have same := List.mem_singleton.mp member
  subst p
  rfl

def chain : PrerequisiteChain current [.fn,.body,.fn] edges :=
  .app rfl (by intro l b same;cases same)
    (.var (parent:=[.fn]) (rest:=[.fn,.fn]) rfl rfl rfl rfl outer_stop)
def segment : PrerequisitePrefix current [.fn,.body,.fn] [xVar] [.fn] :=
  .app rfl (by intro l b same;cases same)
    (.var (parent:=[.fn]) (rest:=[.fn,.fn]) rfl rfl rfl rfl .refl)
theorem reading : PrerequisiteReadsDirected current [.fn] [.fn] false :=
  ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
theorem lookup : current.subterm [.fn]=some node := rfl
theorem marked : ¬node.label.OuterBarsSafe (fun d=>d≠degree) := by
  intro safe
  change (degree≠degree) ∧True at safe
  exact safe.1 rfl
theorem beforeSafe (e : Path) (member : e∈([xVar] : List Path)) :
    degreeReadSafe degree (current.labelAt e) := by
  have same := List.mem_singleton.mp member
  subst e
  intro label equal
  have actual : label=Label.atom 6 := Option.some.inj equal.symm
  subst label
  trivial
private theorem beforeLookupSafe (e : Path) (member : e∈([xVar] : List Path))
    (t : LTerm) (atNode : current.subterm e=some t) : t.label.OuterBarsSafe (fun d=>d≠degree) :=
  beforeSafe e member t.label (by simp only [LTerm.labelAt,atNode,Option.map_some])

def spine : DirectedMarkerSpine F original degree false [[.fn]] current
    ([xVar].map current.labelAt) [.fn] :=
  old.directed_marker_spine actualHistory selected (initial.outerBarsSafe _)
    segment reading lookup marked beforeLookupSafe

def cut : ActualUnsafeMarkerCut F [[.fn]] original current degree [.fn,.body,.fn] edges where
  before := [xVar]
  edge := [.fn]
  after := []
  reader := [.fn]
  node := node
  forward := false
  split := rfl
  segment := segment
  remaining := outer_stop
  reading := reading
  lookup := lookup
  safeBefore := beforeSafe
  marked := marked
  spine := spine
  leaf := spine.leaf_output lookup

theorem actual_reachable_terminal_false_read :
    cut.forward=cut.forward ∧cut.before.length=1 ∧cut.after=[] ∧
    edges.map current.labelAt=[some (.atom 6),some functionLabel] ∧
    PrerequisiteReadsDirected current [.fn,.body,.fn] xVar true ∧
    PrerequisiteReadsDirected current [.fn] [.fn] false ∧
    degreeReadSafe degree (current.labelAt xVar) ∧
    ¬node.label.OuterBarsSafe (fun d=>d≠degree) := by
  have matching := FanSuccessfulReachable.beta_matches
  obtain ⟨selection⟩ := matching.occurrence_fragment_selection targetClosed
  have physical : SameChainRepresentation selection chain chain := rfl
  have actual := actual_terminal_predecessor_direction_eq matching selection chain chain physical
    cut cut rfl (by decide) rfl rfl
  exact ⟨actual,rfl,rfl,rfl,⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩,
    reading,beforeSafe _ (by simp),marked⟩
end Fan
#print axioms Larger.actual_distinct_start_terminal
#print axioms Fan.actual_reachable_terminal_false_read
end Lamping.Checks.TerminalPredecessorDirectionChecks

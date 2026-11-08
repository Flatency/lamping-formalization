import Lamping.Lamping.SafeReadSourceEndpointIso
import Lamping.Checks.UniformOldCreatedIncomingLabels
import Lamping.Lamping.RedexChainDegrees
namespace Lamping.Checks.SafeReadSourceEndpointIsoChecks
open Lambda Lambda.Labelled AG
open SyntaxIncidence
abbrev I : Term := WrappedSuccessfulChains.I
abbrev bare : Term := .app (.lam (.app (.var 0) (.var 0))) (.lam (.app I (.app I I)))
abbrev original : LTerm := initLabels bare
abbrev source : LTerm := WrappedSuccessfulChains.contractRoot original
abbrev middle : LTerm := match source with
  | .app stamp (.lam head body) arg => .app stamp (.lam head (WrappedSuccessfulChains.contractRoot body)) arg
  | t=>t
abbrev target : LTerm := match middle with
  | .app stamp fn (.lam head body) => .app stamp fn (.lam head (WrappedSuccessfulChains.contractRoot body))
  | t=>t
abbrev left : Path := [.fn,.body]
abbrev right : Path := [.arg,.body]
abbrev F : List Path := [left,right]
abbrev leaf : LTerm := .lam (.atom 10) (.var (.atom 11) 0)
abbrev otherLeaf : LTerm := .lam (.atom 12) (.var (.atom 13) 0)
abbrev argument : LTerm := .app (.atom 9) leaf otherLeaf

theorem initial : INIT original := init_is_INIT _
def globalHistory : History [[]] original source := .cons (.root _ _ _ _) (.nil _)
def firstStep : StepAt left source middle := .fn (.body (.root _ _ _ _))
def secondStep : StepAt right middle target := .arg (.body (.root _ _ _ _))
def labels : History [left,right] source target := .cons firstStep (.cons secondStep (.nil _))
def old : Marked.RelativeOldHistory F [left,right] (Marked.mark F source.erase)
    (.app [[]] (.lam (.app [left++[.arg]] (.lam (.var 0)) (.lam (.var 0))))
      (.lam (.app [right++[.arg]] (.lam (.var 0)) (.lam (.var 0))))) :=
  .cons (.appL (.lam (.redRoot _ _ _))) (by decide)
    (.cons (.appR (.lam (.redRoot _ _ _))) (by decide) (.nil _))
theorem selected (p : Path) (inside : p∈F) : source.degreeAt p=some (.atom 7) := by
  rcases List.mem_cons.mp inside with rfl | inside
  · rfl
  · have equal:=List.mem_singleton.mp inside;subst p;rfl

def leftTrace : BetaNodeHistoryPreimage labels (left++[.fn]) (left++[.arg,.fn]) := by
  apply BetaNodeHistoryPreimage.one (step:=firstStep)
    (show source.subterm left=some (.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) argument) from rfl)
    (BetaNodePreimage.copied (q:=[]) (relative:=[.fn]) (old:=leaf) (by rfl) (by rfl))
  exact BetaNodeHistoryPreimage.one (step:=secondStep) (by rfl)
    (BetaNodePreimage.context (by rintro ⟨rest,impossible⟩;cases impossible)) (.nil _ _)
def rightTrace : BetaNodeHistoryPreimage labels (right++[.fn]) (right++[.arg,.fn]) := by
  apply BetaNodeHistoryPreimage.one (step:=firstStep) (by rfl)
    (BetaNodePreimage.context (by rintro ⟨rest,impossible⟩;cases impossible))
  exact BetaNodeHistoryPreimage.one (step:=secondStep)
    (show middle.subterm right=some (.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) argument) from rfl)
    (BetaNodePreimage.copied (q:=[]) (relative:=[.fn]) (old:=leaf) (by rfl) (by rfl)) (.nil _ _)

theorem originalClosed : Closed original.erase := by
  change (0<1 ∧0<1) ∧(0<2 ∧(0<2 ∧0<2))
  decide
theorem sourceClosed : Closed source.erase := globalHistory.closed originalClosed
theorem targetClosed : Closed target.erase := labels.closed sourceClosed
abbrev currentStamp : Label :=
  (LTerm.contract (.atom 6) (.atom 7) (.var (.atom 8) 0) argument).label
def currentLeft : ProperPosition target := ⟨left,Or.inl ⟨currentStamp,leaf,otherLeaf,rfl⟩⟩
def currentRight : ProperPosition target := ⟨right,Or.inl ⟨currentStamp,leaf,otherLeaf,rfl⟩⟩
def oldLeft : ProperPosition source := ⟨left++[.arg],Or.inl ⟨.atom 9,leaf,otherLeaf,rfl⟩⟩
def oldRight : ProperPosition source := ⟨right++[.arg],Or.inl ⟨.atom 9,leaf,otherLeaf,rfl⟩⟩
theorem currentLeftSource : Source target (left++[.fn]) (some currentLeft) :=
  ⟨.fn,.app currentStamp leaf otherLeaf,.appFn currentStamp,rfl,rfl,.fn⟩
theorem currentRightSource : Source target (right++[.fn]) (some currentRight) :=
  ⟨.fn,.app currentStamp leaf otherLeaf,.appFn currentStamp,rfl,rfl,.fn⟩
theorem oldLeftSource : Source source (left++[.arg,.fn]) (some oldLeft) :=
  ⟨.fn,argument,.appFn (.atom 9),rfl,rfl,.fn⟩
theorem oldRightSource : Source source (right++[.arg,.fn]) (some oldRight) :=
  ⟨.fn,argument,.appFn (.atom 9),rfl,rfl,.fn⟩
theorem leftChain : EndpointChain target (some currentLeft) [left++[.fn]] :=
  PrerequisiteChain.redex_app (by rfl)
theorem rightChain : EndpointChain target (some currentRight) [right++[.fn]] :=
  PrerequisiteChain.redex_app (by rfl)
theorem incomingSafe : leaf.label.OuterBarsSafe (fun x=>x≠Label.atom 7) := by trivial
theorem leftReadSafe (edge : Path) (inside : edge∈[left++[.fn]]) (node : LTerm)
    (lookup : target.subterm edge=some node) :
    node.label.OuterBarsSafe (fun x=>x≠Label.atom 7) := by
  have equal:=List.mem_singleton.mp inside;subst edge
  have equal : node=leaf := Option.some.inj lookup.symm
  subst node;exact incomingSafe
theorem rightReadSafe (edge : Path) (inside : edge∈[right++[.fn]]) (node : LTerm)
    (lookup : target.subterm edge=some node) :
    node.label.OuterBarsSafe (fun x=>x≠Label.atom 7) := by
  have equal:=List.mem_singleton.mp inside;subst edge
  have equal : node=leaf := Option.some.inj lookup.symm
  subst node;exact incomingSafe
theorem currentIso : ChainIncidenceIsomorphic
    (chainSyntaxIncidence target targetClosed [left++[.fn]])
    (chainSyntaxIncidence target targetClosed [right++[.fn]]) := by
  exact (redex_chain_iso_iff_degree targetClosed
    (show target.subterm left=some (.app currentStamp leaf otherLeaf) from rfl)
    (show target.subterm right=some (.app currentStamp leaf otherLeaf) from rfl)).mpr rfl

theorem actual_old_source_iso :
    SuccessfulEndpointIso source sourceClosed (some oldLeft) (some oldRight) := by
  obtain ⟨a,b,ha,hb,_,_,iso⟩ := safe_incoming_safe_read_old_source_endpoint_iso old
    sourceClosed targetClosed (DegreeAligned.initial source F) selected leftTrace rightTrace
    (leftNode:=leaf) (rightNode:=leaf) rfl rfl incomingSafe incomingSafe
    currentLeftSource currentRightSource leftChain rightChain currentIso leftReadSafe rightReadSafe
  exact Source.unique ha oldLeftSource ▸ Source.unique hb oldRightSource ▸ iso

/-- Distinct actual SOURCE vertices before and after two OLD steps. All
incoming and READ labels are safe; the whole intermediate term is not assumed safe. -/
theorem actual_same_initial_history_source_iso :
    INIT original ∧History [[],left,right] original target ∧
    currentLeft.val≠currentRight.val ∧oldLeft.val≠oldRight.val ∧
    currentLeft.val≠oldLeft.val ∧
    EndpointChain target (some currentLeft) [left++[.fn]] ∧
    EndpointChain target (some currentRight) [right++[.fn]] ∧
    SuccessfulEndpointIso source sourceClosed (some oldLeft) (some oldRight) :=
  ⟨initial,globalHistory.append labels,by decide,by decide,by decide,leftChain,rightChain,actual_old_source_iso⟩
#print axioms old
#print axioms leftTrace
#print axioms rightTrace
#print axioms currentIso
#print axioms actual_old_source_iso
#print axioms actual_same_initial_history_source_iso
end Lamping.Checks.SafeReadSourceEndpointIsoChecks

import Lamping.Checks.WrappedSuccessfulChains
import Lamping.Lambda.LabelRegions
namespace Lamping.Checks.FanSuccessfulChains
open Lambda Lambda.Labelled
abbrev I : Term := WrappedSuccessfulChains.I
abbrev caller : Term := WrappedSuccessfulChains.caller
abbrev bare : Term := .app (.app (.lam (.lam (.app (.app (.var 0) (.var 1)) (.var 1)))) caller) I
abbrev original : LTerm := initLabels bare
abbrev current : LTerm := match original with
  | .app b fn arg => .app b (WrappedSuccessfulChains.contractRoot fn) arg
  | t => t
abbrev functionLabel : Label := ((Label.atom 1).concat (Label.atom 2).over).concat (.atom 3)
abbrev leftLabel : Label := ((Label.atom 7).concat (Label.atom 2).under).concat (.atom 9)
abbrev rightLabel : Label := ((Label.atom 8).concat (Label.atom 2).under).concat (.atom 9)
abbrev callerBody : LTerm := .app (.atom 10) (.var (.atom 11) 0) (.lam (.atom 12) (.var (.atom 13) 0))
def actualStep : StepAt [.fn] original current := .fn (.root _ _ _ _)
def actualHistory : History [[.fn]] original current := .cons actualStep (.nil _)
theorem initial : INIT original := init_is_INIT _
theorem sourceClosed : Closed original.erase := by
  change (((0<2 ∧1<2) ∧1<2) ∧(0<1 ∧0<2)) ∧0<1
  decide
theorem targetClosed : Closed current.erase := actualHistory.closed sourceClosed
theorem target_shape : current.erase=.app (.lam (.app (.app (.var 0) caller) caller)) I := rfl
abbrev left : Path := [.fn,.body,.fn,.arg]
abbrev right : Path := [.fn,.body,.arg]
abbrev leftBody : Path := left++[.body]
abbrev rightBody : Path := right++[.body]
abbrev leftVar : Path := leftBody++[.fn]
abbrev rightVar : Path := rightBody++[.fn]
abbrev xVar : Path := [.fn,.body,.fn,.fn]
abbrev leftEdges : List Path := [left,xVar,[.fn]]
abbrev rightEdges : List Path := [right,[.fn,.body,.fn],xVar,[.fn]]
abbrev leftBodyEdges : List Path := leftVar::leftEdges
abbrev rightBodyEdges : List Path := rightVar::rightEdges

def left_lambda_occurrence : SourceSubterm [] .external current left [functionLabel]
    (.appArg (.atom 5)) (.lam leftLabel callerBody) := .fn (.body (.fn (.arg .nil)))
def right_lambda_occurrence : SourceSubterm [] .external current right [functionLabel]
    (.appArg (.atom 4)) (.lam rightLabel callerBody) := .fn (.body (.arg .nil))
def left_body_occurrence : SourceSubterm [] .external current leftBody [leftLabel,functionLabel]
    (.lamBody leftLabel) callerBody := .fn (.body (.fn (.arg (.body .nil))))
def right_body_occurrence : SourceSubterm [] .external current rightBody [rightLabel,functionLabel]
    (.lamBody rightLabel) callerBody := .fn (.body (.arg (.body .nil)))
def left_variable_occurrence : SourceSubterm [] .external current leftVar [leftLabel,functionLabel]
    (.appFn (.atom 10)) (.var (.atom 11) 0) := .fn (.body (.fn (.arg (.body (.fn .nil)))))
def right_variable_occurrence : SourceSubterm [] .external current rightVar [rightLabel,functionLabel]
    (.appFn (.atom 10)) (.var (.atom 11) 0) := .fn (.body (.arg (.body (.fn .nil))))

def outer_stop : PrerequisiteChain current [.fn] [[.fn]] := .redex_lam (p:=[]) rfl
def left_lambda_chain : PrerequisiteChain current left leftEdges :=
  .lam (parent:=[.fn,.body,.fn]) (step:=.arg) rfl (by decide)
    (.app rfl (by intro l b same;cases same)
      (.var (parent:=[.fn]) (rest:=[.fn,.fn]) rfl rfl rfl rfl outer_stop))
def right_lambda_chain : PrerequisiteChain current right rightEdges :=
  .lam (parent:=[.fn,.body]) (step:=.arg) rfl (by decide)
    (.app rfl (by intro l b same;cases same)
      (.app rfl (by intro l b same;cases same)
        (.var (parent:=[.fn]) (rest:=[.fn,.fn]) rfl rfl rfl rfl outer_stop)))
def left_variable_chain : PrerequisiteChain current leftVar leftEdges :=
  .var (parent:=left) (rest:=[.fn]) rfl rfl rfl rfl left_lambda_chain
def right_variable_chain : PrerequisiteChain current rightVar rightEdges :=
  .var (parent:=right) (rest:=[.fn]) rfl rfl rfl rfl right_lambda_chain
def left_body_chain : PrerequisiteChain current leftBody leftBodyEdges :=
  .app rfl (by intro l b same;cases same) left_variable_chain
def right_body_chain : PrerequisiteChain current rightBody rightBodyEdges :=
  .app rfl (by intro l b same;cases same) right_variable_chain
def left_variable_jump : PrerequisitePrefix current leftVar [] left :=
  .var (parent:=left) (rest:=[.fn]) rfl rfl rfl rfl .refl
def right_variable_jump : PrerequisitePrefix current rightVar [] right :=
  .var (parent:=right) (rest:=[.fn]) rfl rfl rfl rfl .refl
def root_chain : PrerequisiteChain current [] [[.fn]] := .redex_app rfl

theorem exact_left_labels : leftEdges.map current.labelAt=
    [some leftLabel,some (.atom 6),some functionLabel] := rfl
theorem exact_right_labels : rightEdges.map current.labelAt=
    [some rightLabel,some (.atom 5),some (.atom 6),some functionLabel] := rfl
theorem exact_body_labels : leftBodyEdges.map current.labelAt=
    [some (.atom 11),some leftLabel,some (.atom 6),some functionLabel] ∧
    rightBodyEdges.map current.labelAt=
    [some (.atom 11),some rightLabel,some (.atom 5),some (.atom 6),some functionLabel] := ⟨rfl,rfl⟩
theorem lengths : leftEdges.length=3 ∧rightEdges.length=4 ∧
    leftBodyEdges.length=4 ∧rightBodyEdges.length=5 := ⟨rfl,rfl,rfl,rfl⟩
theorem original_caller_lookup : original.subterm [.fn,.arg]=some (.lam (.atom 9) callerBody) := rfl
theorem initial_redexes : redexPositions original.erase=[[.fn]] := rfl
#print axioms initial
#print axioms targetClosed
#print axioms left_body_chain
#print axioms right_body_chain
#print axioms left_variable_occurrence
#print axioms exact_body_labels
#print axioms lengths
end Lamping.Checks.FanSuccessfulChains

import Lamping.Lamping.InteriorSourceBlockEndpoints
import Lamping.Checks.UniformOldOuterImageAlignment

namespace Lamping.Checks.InteriorSourceBlockEndpointsChecks
open Lambda Lambda.Labelled AG
open Lambda.Labelled.InteriorSourceBlock

private abbrev nodeAt (term : LTerm) (path : Path) : LTerm :=
  (term.subterm path).getD (.var (.atom 0) 0)

private theorem located (out : OriginalAtom source F n leftKind rightKind)
    (lookup : (initLabels source.erase).subterm position=some node) (atomic : node.label=Label.atom n) :
    out.edge.val=position :=
  LTerm.subterm_label_injective _ (init_is_INIT _).2 out.basisOccurrence.occurrence.lookup lookup
    (out.basisOccurrence.atomic.trans atomic.symm)

namespace MarkedLast
open UniformOldOuterImageAlignmentChecks.MarkedLast

theorem interior_window : localCurrent.label.letters=
    [.atom 3]++[bar false (.atom 1),.atom 5,bar true (.atom 6)]++[.atom 7] := rfl

theorem actual_marked_last_interior :
    ∃out : Comparison source F 5 5 false true (globalPrefix.closed originalClosed),
      out.left.edge.val=[.arg] ∧out.right.edge.val=[.arg] ∧
      SyntaxIncidence.label source out.left.edge=oldBeta ∧¬IsAtomic oldBeta := by
  obtain ⟨out⟩:=actual_old_interior_atom_comparison (globalPrefix.closed originalClosed) selected
    old localLabels (by rfl : localTarget.subterm [.fn]=some localCurrent) interior_window
    old localLabels (by rfl : localTarget.subterm [.fn]=some localCurrent) interior_window rfl
  have leftAt : out.left.edge.val=[.arg] := located out.left
    (by rfl : localSource.subterm [.arg]=some (nodeAt localSource [.arg])) rfl
  have rightAt : out.right.edge.val=[.arg] := located out.right
    (by rfl : localSource.subterm [.arg]=some (nodeAt localSource [.arg])) rfl
  exact ⟨out,leftAt,rightAt,out.left.full_image,oldBetaCompound⟩
end MarkedLast

namespace CopiedSource
abbrev originalBare : Term:=.app (.lam (.app (.var 0) (.var 0))) UniformOldOuterImageAlignmentChecks.MarkedLast.bare
abbrev original : LTerm:=initLabels originalBare
private abbrev root := WrappedSuccessfulChains.contractRoot
private abbrev inArg (term : LTerm) : LTerm:=match term with
  | .app stamp fn arg=>.app stamp fn (root arg)
  | term=>term
private abbrev inFn (term : LTerm) : LTerm:=match term with
  | .app stamp fn arg=>.app stamp (root fn) arg
  | term=>term
abbrev first : LTerm:=inArg original
abbrev second : LTerm:=inArg first
abbrev third : LTerm:=match second with
  | .app stamp fn arg=>.app stamp fn (inArg arg)
  | term=>term
abbrev source : LTerm:=root third
abbrev F : List Path:=[[.fn],[.fn,.arg],[.arg],[.arg,.arg]]

def prefixHistory : History [[.arg],[.arg],[.arg,.arg],[]] original source :=
  .cons (.arg (.root _ _ _ _)) (.cons (.arg (.root _ _ _ _))
    (.cons (.arg (.arg (.root _ _ _ _))) (.cons (.root _ _ _ _) (.nil _))))

theorem initial : INIT original:=init_is_INIT _
theorem originalClosed : Closed original.erase := by
  change Scoped 0 originalBare
  simp [Scoped]

theorem selected (p : Path) (member : p∈F) : source.degreeAt p=some (.atom 15) := by
  simp only [F,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

abbrev leftMiddle : LTerm:=match source with
  | .app stamp fn arg=>.app stamp (inArg fn) arg
  | term=>term
abbrev leftTarget : LTerm:=inFn leftMiddle
abbrev rightMiddle : LTerm:=match source with
  | .app stamp fn arg=>.app stamp fn (inArg arg)
  | term=>term
abbrev rightTarget : LTerm:=inArg rightMiddle

def leftLabels : History [[.fn,.arg],[.fn]] source leftTarget:=
  .cons (.fn (.arg (.root _ _ _ _))) (.cons (.fn (.root _ _ _ _)) (.nil _))
def rightLabels : History [[.arg,.arg],[.arg]] source rightTarget:=
  .cons (.arg (.arg (.root _ _ _ _))) (.cons (.arg (.root _ _ _ _)) (.nil _))

private abbrev identity : Marked:=.lam (.var 0)
private abbrev deltaBody : Marked:=.app [] (.var 0) (.var 0)
private abbrev result : Marked:=.app [] (.app [] identity identity) (.app [] identity identity)
abbrev leftMarked : Marked:=.app [] result (.red [[.arg]] deltaBody (.red [[.arg,.arg]] deltaBody identity))
abbrev rightMarked : Marked:=.app [] (.red [[.fn]] deltaBody (.red [[.fn,.arg]] deltaBody identity)) result

def leftOld : Marked.RelativeOldHistory F [[.fn,.arg],[.fn]] (Marked.mark F source.erase) leftMarked :=
  .cons (.appL (.redR (.redRoot _ _ _))) (by decide)
    (.cons (.appL (.redRoot _ _ _)) (by decide) (.nil _))
def rightOld : Marked.RelativeOldHistory F [[.arg,.arg],[.arg]] (Marked.mark F source.erase) rightMarked :=
  .cons (.appR (.redR (.redRoot _ _ _))) (by decide)
    (.cons (.appR (.redRoot _ _ _)) (by decide) (.nil _))

abbrev localSource : LTerm:=initLabels source.erase
abbrev leftLocalMiddle : LTerm:=match localSource with
  | .app stamp fn arg=>.app stamp (inArg fn) arg
  | term=>term
abbrev leftLocalTarget : LTerm:=inFn leftLocalMiddle
abbrev rightLocalMiddle : LTerm:=match localSource with
  | .app stamp fn arg=>.app stamp fn (inArg arg)
  | term=>term
abbrev rightLocalTarget : LTerm:=inArg rightLocalMiddle
abbrev leftLocalNode : LTerm:=nodeAt leftLocalTarget [.fn,.fn]
abbrev rightLocalNode : LTerm:=nodeAt rightLocalTarget [.arg,.fn]

def leftLocalLabels : History [[.fn,.arg],[.fn]] localSource leftLocalTarget:=
  .cons (.fn (.arg (.root _ _ _ _))) (.cons (.fn (.root _ _ _ _)) (.nil _))
def rightLocalLabels : History [[.arg,.arg],[.arg]] localSource rightLocalTarget:=
  .cons (.arg (.arg (.root _ _ _ _))) (.cons (.arg (.root _ _ _ _)) (.nil _))

theorem leftWindow : leftLocalNode.label.letters=
    [.atom 4]++[bar false (.atom 2),.atom 6,bar true (.atom 7)]++[.atom 8] := rfl
theorem rightWindow : rightLocalNode.label.letters=
    [.atom 16]++[bar false (.atom 14),.atom 18,bar true (.atom 19)]++[.atom 20] := rfl
theorem equalOpaqueImages : initialRelabelling source 0 6=initialRelabelling source 0 18 := rfl

/-- Different actual SOURCE positions and local INIT atoms, SAME original prefix,
two genuine OLD schedules, and the complete inherited compound SOURCE label. -/
theorem actual_nonreflexive_interior :
    INIT original ∧History [[.arg],[.arg],[.arg,.arg],[]] original source ∧
    (6 : Nat)≠18 ∧
    ∃out : Comparison source F 6 18 false true (prefixHistory.closed originalClosed),
      out.left.edge.val=[.fn,.arg] ∧out.right.edge.val=[.arg,.arg] ∧
      out.left.edge.val≠out.right.edge.val ∧
      ¬IsAtomic (initialRelabelling source 0 6) := by
  obtain ⟨out⟩:=actual_old_interior_atom_comparison (prefixHistory.closed originalClosed) selected
    leftOld leftLocalLabels (by rfl : leftLocalTarget.subterm [.fn,.fn]=some leftLocalNode) leftWindow
    rightOld rightLocalLabels (by rfl : rightLocalTarget.subterm [.arg,.fn]=some rightLocalNode) rightWindow equalOpaqueImages
  have leftAt : out.left.edge.val=[.fn,.arg] := located out.left
    (by rfl : localSource.subterm [.fn,.arg]=some (nodeAt localSource [.fn,.arg])) rfl
  have rightAt : out.right.edge.val=[.arg,.arg] := located out.right
    (by rfl : localSource.subterm [.arg,.arg]=some (nodeAt localSource [.arg,.arg])) rfl
  have compound : ¬IsAtomic (initialRelabelling source 0 6) := by
    rintro ⟨n,equal⟩
    have large : 1<(initialRelabelling source 0 6).length:=by decide
    rw [equal] at large
    simp [Label.atom,Label.length] at large
  exact ⟨initial,prefixHistory,by decide,out,leftAt,rightAt,by rw [leftAt,rightAt];decide,compound⟩

section
variable {N B W : Type} [Graph.FiniteNames N] [Graph.FiniteNames B] [Graph.FiniteNames W]
variable {g : Graph.Net signature N B W} {root : B}

/-- Direct physical consumer for the two DISTINCT old blocks, under honest SOURCE Aux. -/
theorem actual_nonreflexive_atom_words
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (selection : SourceEdgeSelection localSource g root)
    (auxiliary : AuxiliarySeparation (prefixHistory.closed originalClosed) sourceSelection) :
    selection.atomWord 6=selection.atomWord 18 := by
  obtain ⟨_initial,_prefix,_different,out,_left,_right,_positions,_compound⟩:=actual_nonreflexive_interior
  exact out.atom_words_equal matching sourceSelection selection auxiliary
end
end CopiedSource

#print axioms MarkedLast.actual_marked_last_interior
#print axioms CopiedSource.prefixHistory
#print axioms CopiedSource.leftOld
#print axioms CopiedSource.rightOld
#print axioms CopiedSource.leftWindow
#print axioms CopiedSource.rightWindow
#print axioms CopiedSource.equalOpaqueImages
#print axioms CopiedSource.actual_nonreflexive_interior
#print axioms CopiedSource.actual_nonreflexive_atom_words
end Lamping.Checks.InteriorSourceBlockEndpointsChecks

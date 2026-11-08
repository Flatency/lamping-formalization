import Lamping.Checks.Q0LocalModelChains
import Lamping.Lamping.ActualChainLabelConverse
import Lamping.Lamping.FamilyRepresentation

namespace Lamping.Checks.Q0LocalModelReadLabels
open AG Graph Lambda Lambda.Labelled Q0LocalModelFixture Q0LocalModelChains

/-- The entire generated READ word at the root chain's FIRST edge. -/
def rootRead : Lambda.Labelled.Label :=
  ((Lambda.Labelled.Label.atom 3).concat Q0BodyLabelCounterexample.a.over).concat (.atom 12)

/-- Complete Option-valued READ vectors; no lookup slot is dropped. -/
def classRead : ChainClass → List (Option Lambda.Labelled.Label)
  | .root => [some rootRead,some (.atom 13),some (.atom 14)]
  | .BL => [some (.atom 13),some (.atom 14)]
  | .L => [some (.atom 14)]
  | .JL => [some (.atom 18),some (.atom 14)]
  | .KBL => [some (.atom 20),some (.atom 13),some (.atom 14)]

theorem concrete_chain_read (c : AccessCode) :
    (chainPaths c).map source.labelAt=classRead (classOf c) := by
  cases c <;> rfl

theorem classImage_injective : Function.Injective classImage := by
  intro left right same
  cases left <;> cases right <;> first | rfl | cases same

theorem classRead_injective : Function.Injective classRead := by
  intro left right same
  cases left <;> cases right <;> first | rfl | cases same

/-- Compare whole physical images and whole Option READ vectors of two
supplied genuine successful chains; equality of classes does not identify
their starting codes or their occurrence coordinates. -/
theorem actual_complete_chain_image_iff_labels
    (selection : OccurrenceFragmentSelection source net ())
    {p q : Path} {es fs : List Path}
    (first : PrerequisiteChain source p es)
    (second : PrerequisiteChain source q fs) :
    canonicalChainImage selection first=canonicalChainImage selection second ↔
      es.map source.labelAt=fs.map source.labelAt := by
  obtain ⟨left,_leftStart,leftEdges,leftImage⟩ := actual_chain_normal_form selection first
  obtain ⟨right,_rightStart,rightEdges,rightImage⟩ := actual_chain_normal_form selection second
  have leftRead : es.map source.labelAt=classRead (classOf left) := by
    rw [leftEdges]
    exact concrete_chain_read left
  have rightRead : fs.map source.labelAt=classRead (classOf right) := by
    rw [rightEdges]
    exact concrete_chain_read right
  constructor
  · intro same
    have classes : classOf left=classOf right :=
      classImage_injective ((leftImage.symm.trans same).trans rightImage)
    exact leftRead.trans ((congrArg classRead classes).trans rightRead.symm)
  · intro same
    have classes : classOf left=classOf right :=
      classRead_injective ((leftRead.symm.trans same).trans rightRead)
    exact leftImage.trans ((congrArg classImage classes).trans rightImage.symm)

/-- The chain subclause only, under the SAME actual original INIT/history.
No auxiliary separation or Joint representation is claimed. -/
theorem actual_chain_representation
    (selection : OccurrenceFragmentSelection source net ()) :
    ChainRepresentationInvariant source_closed selection := by
  intro p q es fs first second
  change canonicalChainImage selection first=canonicalChainImage selection second ↔
    ChainIncidenceIsomorphic (chainSyntaxIncidence source source_closed es)
      (chainSyntaxIncidence source source_closed fs)
  exact (actual_complete_chain_image_iff_labels selection first second).trans
    (actual_chain_iso_iff_labels Q0BodyLabelCounterexample.actualHistory
      Q0BodyLabelCounterexample.actual_initial.1 source_closed first second).symm

#print axioms concrete_chain_read
#print axioms classImage_injective
#print axioms classRead_injective
#print axioms actual_complete_chain_image_iff_labels
#print axioms actual_chain_representation

end Lamping.Checks.Q0LocalModelReadLabels

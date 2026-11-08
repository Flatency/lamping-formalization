import Lamping.Checks.Q0LocalModelReadLabels

namespace Lamping.Checks.Q0LocalModelAuxJoint
open AG Graph Lambda Lambda.Labelled Q0LocalModelFixture Q0LocalModelFragments
open Q0LocalModelChains Q0LocalModelReadLabels

private inductive AuxCode where
  | root | rightA | leftV | rightV | leftJV | rightJV | leftKV | rightKV

private def code : AuxCode → AccessCode
  | .root => .root
  | .rightA => .rightA
  | .leftV => .leftV
  | .rightV => .rightV
  | .leftJV => .leftJV
  | .rightJV => .rightJV
  | .leftKV => .leftKV
  | .rightKV => .rightKV

private def auxLabel : AuxCode → Lambda.Labelled.Label
  | .root => ((Lambda.Labelled.Label.atom 0).concat (Lambda.Labelled.Label.atom 1).over).concat (.atom 2)
  | .rightA => ((Lambda.Labelled.Label.atom 7).concat Q0BodyLabelCounterexample.b.over).concat (.atom 12)
  | .leftV => Q0BodyLabelCounterexample.gamma
  | .rightV => Q0BodyLabelCounterexample.delta
  | .leftJV | .rightJV => .atom 19
  | .leftKV | .rightKV => .atom 21

private theorem classify_aux (edge : SyntaxIncidence.Edge source)
    (aux : AuxiliaryAt source edge.val) :
    ∃ a : AuxCode,edge.val=coordinate (code a) := by
  obtain ⟨actual,word,_observes⟩ := Matches.observation net actual_matching edge
  obtain ⟨c,_path,atCode⟩ := actual_root_access_classification actual
  have position : edge.val=coordinate c := word.symm.trans atCode
  rw [position] at aux
  cases c with
  | root => exact ⟨.root,position⟩
  | leftA =>
    have forbidden : ¬AuxiliaryAt source (coordinate .leftA) :=
      (concrete_chain .root).not_auxiliary (by simp [chainPaths,chainCodes])
    exact False.elim (forbidden aux)
  | leftB =>
    have forbidden : ¬AuxiliaryAt source (coordinate .leftB) :=
      (concrete_chain .leftA).not_auxiliary (by simp [chainPaths,chainCodes])
    exact False.elim (forbidden aux)
  | leftL =>
    have forbidden : ¬AuxiliaryAt source (coordinate .leftL) :=
      (concrete_chain .leftB).not_auxiliary (by simp [chainPaths,chainCodes])
    exact False.elim (forbidden aux)
  | leftV => exact ⟨.leftV,position⟩
  | leftJ =>
    have forbidden : ¬AuxiliaryAt source (coordinate .leftJ) :=
      (concrete_chain .leftJ).not_auxiliary (by simp [chainPaths,chainCodes])
    exact False.elim (forbidden aux)
  | leftJV => exact ⟨.leftJV,position⟩
  | leftK =>
    have forbidden : ¬AuxiliaryAt source (coordinate .leftK) :=
      (concrete_chain .leftK).not_auxiliary (by simp [chainPaths,chainCodes])
    exact False.elim (forbidden aux)
  | leftKV => exact ⟨.leftKV,position⟩
  | rightA => exact ⟨.rightA,position⟩
  | rightB =>
    have forbidden : ¬AuxiliaryAt source (coordinate .rightB) :=
      (concrete_chain .rightA).not_auxiliary (by simp [chainPaths,chainCodes])
    exact False.elim (forbidden aux)
  | rightL =>
    have forbidden : ¬AuxiliaryAt source (coordinate .rightL) :=
      (concrete_chain .rightB).not_auxiliary (by simp [chainPaths,chainCodes])
    exact False.elim (forbidden aux)
  | rightV => exact ⟨.rightV,position⟩
  | rightJ =>
    have forbidden : ¬AuxiliaryAt source (coordinate .rightJ) :=
      (concrete_chain .rightJ).not_auxiliary (by simp [chainPaths,chainCodes])
    exact False.elim (forbidden aux)
  | rightJV => exact ⟨.rightJV,position⟩
  | rightK =>
    have forbidden : ¬AuxiliaryAt source (coordinate .rightK) :=
      (concrete_chain .rightK).not_auxiliary (by simp [chainPaths,chainCodes])
    exact False.elim (forbidden aux)
  | rightKV => exact ⟨.rightKV,position⟩

private theorem actual_label (edge : SyntaxIncidence.Edge source) (a : AuxCode)
    (position : edge.val=coordinate (code a)) :
    SyntaxIncidence.label source edge=auxLabel a := by
  cases a <;> exact SyntaxIncidence.label_of_lookup source edge (by rw [position]; rfl)

private theorem selected_piece (selection : OccurrenceFragmentSelection source net ())
    (edge : SyntaxIncidence.Edge source) (a : AuxCode)
    (position : edge.val=coordinate (code a)) :
    (selection edge).fragment.segments=piece (code a) := by
  rcases edge with ⟨path,valid⟩
  change path=coordinate (code a) at position
  subst path
  exact (literal_occurrence_fragment (code a) (selection ⟨_,valid⟩)).2.1

/-- A finite stronger support fact, only at actual Aux edges. It is not a
global converse between labels, pieces or occurrence coordinates. -/
private theorem aux_label_piece (selection : OccurrenceFragmentSelection source net ())
    (left right : SyntaxIncidence.Edge source)
    (leftAux : AuxiliaryAt source left.val) (rightAux : AuxiliaryAt source right.val)
    (same : SyntaxIncidence.label source left=SyntaxIncidence.label source right) :
    (selection left).fragment.segments=(selection right).fragment.segments := by
  obtain ⟨a,leftAt⟩ := classify_aux left leftAux
  obtain ⟨b,rightAt⟩ := classify_aux right rightAux
  have labels : auxLabel a=auxLabel b :=
    (actual_label left a leftAt).symm.trans (same.trans (actual_label right b rightAt))
  have pieces : piece (code a)=piece (code b) := by
    cases a <;> cases b <;> first | rfl | cases labels
  exact (selected_piece selection left a leftAt).trans
    (pieces.trans (selected_piece selection right b rightAt).symm)

/-- The exact approved successful-chain Aux interface. Undefined endpoints
do not contribute isomorphisms; equal full Aux labels already force equal
whole pieces in this concrete finite model. -/
theorem actual_auxiliary_separation
    (selection : OccurrenceFragmentSelection source net ()) :
    AuxiliarySeparation source_closed selection := by
  intro left right leftAux rightAux same different _successfulEndpoints
  exact different (aux_label_piece selection left right leftAux rightAux same)

/-- The existing finite Joint conjunction, using the already public
SAME-original-history chain clause and newly proved actual Aux. -/
theorem actual_joint (selection : OccurrenceFragmentSelection source net ()) :
    JointRepresentation source_closed selection :=
  ⟨actual_chain_representation selection,actual_auxiliary_separation selection⟩

#print axioms actual_auxiliary_separation
#print axioms actual_joint

end Lamping.Checks.Q0LocalModelAuxJoint

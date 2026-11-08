import Lamping.Lambda.AuxWritingFirstAtomOrigin
import Lamping.Checks.AuxiliaryNodeHistoryOrigins
import Lamping.Checks.DirectedReadingDecomposition
namespace Lamping.Checks.AuxWritingFirstAtomOriginChecks
open Lambda Lambda.Labelled SyntaxIncidence InteriorSourceBlock
namespace App
open NodeLabelSuffixOriginsChecks AuxiliaryNodeHistoryOriginsChecks
abbrev F : List Path := [[.arg]]
def old : Marked.RelativeOldHistory F [[.arg]] (Marked.mark F source.erase)
    (.app [[]] (.lam (.var 0)) (.app [[.arg,.arg]] (.lam (.var 0)) (.lam (.var 0)))) :=
  .cons (.appR (.redRoot _ _ _)) (by decide) (.nil _)
def localHistory : History [[.arg]] (initLabels source.erase) target:=actualHistory

theorem actual_app_first : INIT source ∧Closed source.erase ∧
    ∃oldParent : ProperPosition source,∃position env ctx basis,
      BetaVertexHistoryPreimage actualHistory (some currentOuter) (some oldParent) ∧
      SourceSubterm [] .external (initLabels source.erase) position env ctx basis ∧
      basis.label=Label.atom 3 ∧position=[.arg] ∧oldParent.val=[] ∧
      AuxiliaryAt source position ∧∃selected : SelectedRedex source F,
      selected.position=[.arg] ∧Source source position (some oldParent) ∧
      Target source position (some (selected.vertex false)) := by
  obtain ⟨oldParent,parentTrace,position,env,ctx,basis,occurrence,atomic,atOld,aux,selected,fromSpec,toSpec⟩:=
    aux_writing_first_atom_origin old actualHistory localHistory actual_lookup actual_auxiliary
      (by rfl : target.subterm [.arg]=some currentArgument)
      (by rfl : currentArgument.label.letters=[.atom 3,bar true (.atom 4)]++[.atom 5,.under (.atom 4),.atom 6])
      currentOuter target_source_endpoint
  have located : position=[.arg] :=
    LTerm.subterm_label_injective _ (init_is_INIT _).2 occurrence.lookup
      (by rfl : (initLabels source.erase).subterm [.arg]=some
        (.app (.atom 3) (.lam (.atom 4) (.var (.atom 5) 0)) argumentTerm)) atomic
  let originalOuter : ProperPosition source:=⟨[],Or.inl ⟨_,_,_,rfl⟩⟩
  have sourceAtOuter : Source source position (some originalOuter) := by
    rw [located];exact ⟨.arg,_,_,rfl,rfl,.arg⟩
  have parentEq : oldParent=originalOuter:=Option.some.inj (Source.unique fromSpec sourceAtOuter)
  exact ⟨initial,closed,oldParent,position,env,ctx,basis,parentTrace,occurrence,atomic,located,
    congrArg Subtype.val parentEq,aux,selected,List.mem_singleton.mp selected.member,fromSpec,toSpec⟩

theorem preserved_source_hom_negative :
    ¬BetaVertexPreimage (.var (.atom 5) 0) argumentTerm [.arg] source target
      (some currentOuter) (some oldInner) := no_created_source_incidence_map

theorem writing_first_not_own_last :
    source.subterm [.arg]=some (.app (.atom 3) (.lam (.atom 4) (.var (.atom 5) 0)) argumentTerm) ∧
    source.subterm [.arg,.arg]=some argumentTerm ∧([Step.arg] : Path)≠[.arg,.arg] :=
  ⟨rfl,rfl,by decide⟩
end App
namespace Var
open DirectedReadingDecompositionChecks
abbrev currentVar : LTerm:=.var (((Label.atom 5).concat (Label.atom 2).under).concat (.atom 6)) 0
abbrev F : List Path:=[[.body]]
def labels : History [[.body]] cSource cTarget:=.cons cStep (.nil _)
def old : Marked.RelativeOldHistory F [[.body]] (Marked.mark F cSource.erase)
    (.lam (.app [] (.var 0) (.var 0))) :=
  .cons (.lam (.redRoot _ _ _)) (by decide) (.nil _)
def localHistory : History [[.body]] (initLabels cSource.erase) cTarget:=labels
def parent : ProperPosition cTarget:=⟨[.body],Or.inl ⟨_,_,_,rfl⟩⟩
def oldParent : ProperPosition cSource:=⟨[.body,.fn,.body],Or.inl ⟨_,_,_,rfl⟩⟩
theorem lookup : cTarget.subterm [.body,.arg]=some currentVar:=rfl
theorem auxiliary : AuxiliaryAt cTarget [.body,.arg] := by
  constructor
  · rintro ⟨parent,a,fn,arg,split,atParent⟩
    have last:=congrArg List.getLast? split
    simp at last
  · rintro ⟨a,body,atLambda⟩;rw [lookup] at atLambda;cases atLambda
theorem closed : Closed cSource.erase := by change Scoped 0 (.lam (.app (.lam (.app (.var 0) (.var 0))) (.var 0)));simp [Scoped]
theorem actual_var_binder_first : INIT cSource ∧Closed cSource.erase ∧
    ∃originalParent : ProperPosition cSource,∃position env ctx basis,
      BetaVertexHistoryPreimage labels (some parent) (some originalParent) ∧
      SourceSubterm [] .external (initLabels cSource.erase) position env ctx basis ∧
      basis.label=Label.atom 5 ∧position=[.body,.fn,.body,.arg] ∧originalParent.val=oldParent.val ∧
      AuxiliaryAt cSource position ∧∃selected : SelectedRedex cSource F,
      selected.position=[.body] ∧Source cSource position (some originalParent) ∧
      Target cSource position (some (selected.vertex true)) := by
  obtain ⟨originalParent,parentTrace,position,env,ctx,basis,occurrence,atomic,atOld,aux,selected,fromSpec,toSpec⟩:=
    aux_writing_first_atom_origin old labels localHistory lookup auxiliary lookup
      (by rfl : currentVar.label.letters=[.atom 5,bar false (.atom 2)]++[.atom 6])
      parent ⟨.arg,_,_,rfl,rfl,.arg⟩
  have located : position=[.body,.fn,.body,.arg] :=
    LTerm.subterm_label_injective _ (init_is_INIT _).2 occurrence.lookup
      (by rfl : (initLabels cSource.erase).subterm [.body,.fn,.body,.arg]=some (.var (.atom 5) 0)) atomic
  have sourceAtParent : Source cSource position (some oldParent) := by
    rw [located];exact ⟨.arg,_,_,rfl,rfl,.arg⟩
  have parentEq : originalParent=oldParent:=Option.some.inj (Source.unique fromSpec sourceAtParent)
  exact ⟨init_is_INIT _,closed,originalParent,position,env,ctx,basis,parentTrace,occurrence,atomic,
    located,congrArg Subtype.val parentEq,aux,selected,List.mem_singleton.mp selected.member,fromSpec,toSpec⟩
end Var
#print axioms App.actual_app_first
#print axioms App.preserved_source_hom_negative
#print axioms App.writing_first_not_own_last
#print axioms Var.auxiliary
#print axioms Var.closed
#print axioms Var.actual_var_binder_first
end Lamping.Checks.AuxWritingFirstAtomOriginChecks

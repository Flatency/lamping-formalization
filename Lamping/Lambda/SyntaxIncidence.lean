import Lamping.Lambda.ClosedVariableBinders

namespace Lamping.Lambda.Labelled.SyntaxIncidence

/-- Proper vertices retain literal syntax coordinates, even when all labels
repeat. The external boundary is represented separately by none. -/
def ProperAt (term : LTerm) (position : Path) : Prop :=
  (∃ stamp fn arg,term.subterm position=some (.app stamp fn arg)) ∨
  (∃ stamp body,term.subterm position=some (.lam stamp body))
abbrev ProperPosition (term : LTerm) := {position : Path // ProperAt term position}
abbrev Vertex (term : LTerm) := Option (ProperPosition term)
abbrev Edge (term : LTerm) := Position term.erase

/-- The canonical source is the external root or the actual parent proper
node, with its genuine function/argument/body departure role. -/
def Source (term : LTerm) (edge : Path) : Vertex term → Prop
  | none => edge=[]
  | some parent => ∃ step child port,edge=parent.val++[step] ∧
      term.subterm parent.val=some child ∧SourceDeparture child step port

/-- A compound incoming edge ends at that very occurrence. A variable edge
ends at its actual lexical lambda, not another lambda with the same label. -/
def Target (term : LTerm) (edge : Path) : Vertex term → Prop
  | none => False
  | some vertex => edge=vertex.val ∨∃ stamp index origin body tail,
      term.subterm edge=some (.var stamp index) ∧
      term.subterm vertex.val=some (.lam origin body) ∧
      edge=vertex.val++(.body::tail) ∧index=binderDepth tail

theorem edge_lookup (term : LTerm) (edge : Edge term) :
    ∃ child,term.subterm edge.val=some child := by
  cases lookup : term.subterm edge.val with
  | none =>
    have valid := edge.property
    rw [←LTerm.erase_subterm,lookup] at valid
    cases valid
  | some child => exact ⟨child,rfl⟩

private theorem proper_not_variable (proper : ProperAt term position)
    (lookup : term.subterm position=some (.var stamp index)) : False := by
  rcases proper with ⟨a,fn,arg,actual⟩ |⟨a,body,actual⟩ <;>
    rw [lookup] at actual <;> cases actual

theorem source_total (term : LTerm) (edge : Edge term) : ∃ vertex,Source term edge.val vertex := by
  obtain ⟨child,lookup⟩ := edge_lookup term edge
  obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup term lookup [] .external
  rcases occurrence.last_departure with ⟨root,_⟩ |⟨parent,step,sub,split,atParent,departure⟩
  · exact ⟨none,root⟩
  · have proper : ProperAt term parent := by
      cases departure with
      | fn => exact Or.inl ⟨_,_,_,atParent⟩
      | arg => exact Or.inl ⟨_,_,_,atParent⟩
      | body => exact Or.inr ⟨_,_,atParent⟩
    exact ⟨some ⟨parent,proper⟩,step,sub,ctx,split,atParent,departure⟩

theorem Source.unique {term : LTerm} {edge : Path} {left right : Vertex term}
    (first : Source term edge left) (second : Source term edge right) : left=right := by
  cases left with
  | none =>
    cases right with
    | none => rfl
    | some parent =>
      obtain ⟨step,_,_,split,_,_⟩ := second
      have lengths := congrArg List.length (first.symm.trans split)
      simp only [List.length_nil,List.length_append,List.length_singleton] at lengths
      omega
  | some parent =>
    cases right with
    | none =>
      obtain ⟨step,_,_,split,_,_⟩ := first
      have lengths := congrArg List.length (second.symm.trans split)
      simp only [List.length_nil,List.length_append,List.length_singleton] at lengths
      omega
    | some other =>
      obtain ⟨step,_,_,split,_,_⟩ := first
      obtain ⟨otherStep,_,_,otherSplit,_,_⟩ := second
      have equal := split.symm.trans otherSplit
      have lengths : parent.val.length=other.val.length := by
        have sizes := congrArg List.length equal
        simp only [List.length_append,List.length_singleton] at sizes
        omega
      exact congrArg some (Subtype.ext (List.append_inj_left equal lengths))

theorem target_total (term : LTerm) (closed : Closed term.erase) (edge : Edge term) :
    ∃ vertex,Target term edge.val vertex := by
  obtain ⟨child,lookup⟩ := edge_lookup term edge
  cases child with
  | app stamp fn arg => exact ⟨some ⟨edge.val,Or.inl ⟨stamp,fn,arg,lookup⟩⟩,Or.inl rfl⟩
  | lam stamp body => exact ⟨some ⟨edge.val,Or.inr ⟨stamp,body,lookup⟩⟩,Or.inl rfl⟩
  | var stamp index =>
    obtain ⟨parent,tail,origin,body,split,atParent,_inside,_erased,depth⟩ :=
      term.closed_variable_binder closed lookup
    exact ⟨some ⟨parent,Or.inr ⟨origin,body,atParent⟩⟩,
      Or.inr ⟨stamp,index,origin,body,tail,lookup,atParent,split,depth⟩⟩

theorem Target.unique {term : LTerm} {edge : Path} {left right : Vertex term}
    (first : Target term edge left) (second : Target term edge right) : left=right := by
  cases left with
  | none => exact False.elim first
  | some parent =>
    cases right with
    | none => exact False.elim second
    | some other =>
      rcases first with compound |⟨stamp,index,origin,body,tail,lookup,atParent,split,depth⟩
      · rcases second with otherCompound |⟨a,k,l,b,rest,atVariable,_atOther,_otherSplit,_otherDepth⟩
        · exact congrArg some (Subtype.ext (compound.symm.trans otherCompound))
        · rw [compound] at atVariable
          exact False.elim (proper_not_variable parent.property atVariable)
      · rcases second with compound |⟨a,k,l,b,rest,atVariable,_atOther,otherSplit,otherDepth⟩
        · rw [compound] at lookup
          exact False.elim (proper_not_variable other.property lookup)
        · have indices : index=k := (LTerm.var.inj (Option.some.inj (lookup.symm.trans atVariable))).2
          have same := binding_prefix_depth_unique (split.symm.trans otherSplit)
            (depth.symm.trans (indices.trans otherDepth))
          exact congrArg some (Subtype.ext same.1)

/-- Pure semantic incidence coordinates. Classical choice selects only the
already uniquely proved syntax endpoints; these definitions are not the
readback algorithm and assert no chain isomorphism or physical REP. -/
noncomputable def source (term : LTerm) (edge : Edge term) : Vertex term :=
  Classical.choose (source_total term edge)
noncomputable def target (term : LTerm) (closed : Closed term.erase) (edge : Edge term) : Vertex term :=
  Classical.choose (target_total term closed edge)

theorem source_spec (term : LTerm) (edge : Edge term) : Source term edge.val (source term edge) :=
  Classical.choose_spec (source_total term edge)
theorem target_spec (term : LTerm) (closed : Closed term.erase) (edge : Edge term) :
    Target term edge.val (target term closed edge) :=
  Classical.choose_spec (target_total term closed edge)
theorem source_eq_of_spec (term : LTerm) (edge : Edge term) {vertex : Vertex term} (actual : Source term edge.val vertex) :
    source term edge=vertex := Source.unique (source_spec term edge) actual
theorem target_eq_of_spec (term : LTerm) (closed : Closed term.erase) (edge : Edge term) {vertex : Vertex term}
    (actual : Target term edge.val vertex) : target term closed edge=vertex :=
  Target.unique (target_spec term closed edge) actual

def label (term : LTerm) (edge : Edge term) : Label :=
  ((term.subterm edge.val).map LTerm.label).getD (.atom 0)

theorem label_of_lookup (term : LTerm) (edge : Edge term) (lookup : term.subterm edge.val=some child) :
    label term edge=child.label := by simp only [label,lookup,Option.map_some,Option.getD_some]

end Lamping.Lambda.Labelled.SyntaxIncidence

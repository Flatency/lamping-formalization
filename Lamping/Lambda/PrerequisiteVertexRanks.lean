import Lamping.Lambda.UncreatedChainTransport
import Lamping.Lambda.SyntaxIncidence
import Lamping.Lambda.UncreatedPrerequisiteReadings
import Lamping.Lambda.PrerequisiteEdgeOrder
namespace Lamping.Lambda.Labelled
open SyntaxIncidence
/-- A proper occurrence is actually incident with one of the selected edges.
This uses directed syntax incidence, not label membership. -/
def PrerequisiteIncident (t : LTerm) (edges : List Path) (p : Path) : Prop :=
  ∃ proper : ProperAt t p,∃ edge∈edges,
    Source t edge (some ⟨p,proper⟩) ∨Target t edge (some ⟨p,proper⟩)

private theorem target_position_eq (first : Target t edge (some left))
    (second : Target t edge (some right)) : left.val=right.val :=
  congrArg Subtype.val (Option.some.inj (Target.unique first second))
private theorem source_position_eq (first : Source t edge (some left))
    (second : Source t edge (some right)) : left.val=right.val :=
  congrArg Subtype.val (Option.some.inj (Source.unique first second))
private theorem Source.actual_parent
    (source : Source t (parent++[child]) (some vertex)) : vertex.val=parent := by
  obtain ⟨step,sub,port,split,lookup,departure⟩ := source
  have lengths := congrArg List.length split
  simp only [List.length_append,List.length_singleton] at lengths
  exact (List.append_inj_left split (by omega)).symm

/-- A zero-edge variable jump identifies the actual proper target node of
its start. The same complete chain starts at that proper target. -/
theorem PrerequisiteChain.at_actual_target (chain : PrerequisiteChain t start edges)
    (target : Target t start (some vertex)) : PrerequisiteChain t vertex.val edges := by
  cases chain with
  | @redex_app p a l b arg lookup =>
    have actual : Target t start (some ⟨start,Or.inl ⟨a,_,arg,lookup⟩⟩) := Or.inl rfl
    rw [target_position_eq target actual]
    exact .redex_app lookup
  | @redex_lam p a l b arg lookup =>
    have atChild : t.subterm (p++[.fn])=some (.lam l b) := by rw [LTerm.subterm_append,lookup]; rfl
    have actual : Target t (p++[.fn]) (some ⟨p++[.fn],Or.inr ⟨l,b,atChild⟩⟩) := Or.inl rfl
    rw [target_position_eq target actual]
    exact .redex_lam lookup
  | @app p a fn arg es lookup notLambda tail =>
    have actual : Target t start (some ⟨start,Or.inl ⟨a,fn,arg,lookup⟩⟩) := Or.inl rfl
    rw [target_position_eq target actual]
    exact .app lookup notLambda tail
  | @lam parent child a b es lookup notFunction tail =>
    have actual : Target t (parent++[child]) (some ⟨parent++[child],Or.inr ⟨a,b,lookup⟩⟩) := Or.inl rfl
    rw [target_position_eq target actual]
    exact .lam lookup notFunction tail
  | @var leaf a index parent origin body rest es lookup binder split depth tail =>
    have actual : Target t start (some ⟨parent,Or.inr ⟨origin,body,binder⟩⟩) :=
      Or.inr ⟨a,index,origin,body,rest,lookup,binder,split,depth⟩
    rw [target_position_eq target actual]
    exact tail

private theorem redex_incident_positions
    (lookup : t.subterm parent=some (.app appStamp (.lam lamStamp body) argument))
    (incident : PrerequisiteIncident t [parent++[.fn]] p) :
    p=parent ∨p=parent++[.fn] := by
  obtain ⟨proper,edge,member,endpoint⟩ := incident
  have edgeEq : edge=parent++[.fn] := List.mem_singleton.mp member
  subst edge
  rcases endpoint with source | target
  · have actual : Source t (parent++[.fn]) (some ⟨parent,Or.inl ⟨appStamp,_,argument,lookup⟩⟩) :=
      ⟨.fn,_,_,rfl,lookup,.fn⟩
    have equal := source_position_eq source actual
    change p=parent at equal
    subst p
    exact Or.inl rfl
  · have atChild : t.subterm (parent++[.fn])=some (.lam lamStamp body) := by
      rw [LTerm.subterm_append,lookup]; rfl
    have actual : Target t (parent++[.fn])
        (some ⟨parent++[.fn],Or.inr ⟨lamStamp,body,atChild⟩⟩) := Or.inl rfl
    have equal := target_position_eq target actual
    change p=parent++[.fn] at equal
    subst p
    exact Or.inr rfl

private theorem redex_incident_chain
    (lookup : t.subterm parent=some (.app appStamp (.lam lamStamp body) argument))
    (incident : PrerequisiteIncident t [parent++[.fn]] p) :
    PrerequisiteChain t p [parent++[.fn]] := by
  rcases redex_incident_positions lookup incident with equal | equal
  · subst p; exact .redex_app lookup
  · subst p; exact .redex_lam lookup
/-- Every incident proper node has its own actual chain using only selected
edges, with no greater edge count. This is not a graph-completion assertion. -/
theorem PrerequisiteChain.incident_chain
    (chain : PrerequisiteChain t start edges) (incident : PrerequisiteIncident t edges p) :
    ∃ more,PrerequisiteChain t p more ∧(∀ edge∈more,edge∈edges) ∧more.length≤edges.length := by
  induction chain with
  | redex_app lookup => exact ⟨_,redex_incident_chain lookup incident,fun _ member=>member,Nat.le_refl _⟩
  | redex_lam lookup => exact ⟨_,redex_incident_chain lookup incident,fun _ member=>member,Nat.le_refl _⟩
  | @app position stamp fn arg es lookup notLambda tail ih =>
    obtain ⟨proper,edge,member,endpoint⟩ := incident
    rcases List.mem_cons.mp member with equal | below
    · subst edge
      rcases endpoint with source | target
      · have actual : Source t (position++[.fn]) (some ⟨position,Or.inl ⟨stamp,fn,arg,lookup⟩⟩) :=
          ⟨.fn,_,_,rfl,lookup,.fn⟩
        have equal := source_position_eq source actual
        change p=position at equal
        subst p
        exact ⟨_,.app lookup notLambda tail,fun _ member=>member,Nat.le_refl _⟩
      · exact ⟨es,tail.at_actual_target target,fun _ member=>List.mem_cons_of_mem _ member,by simp⟩
    · obtain ⟨more,actual,subset,bound⟩ := ih ⟨proper,edge,below,endpoint⟩
      exact ⟨more,actual,fun edge member=>List.mem_cons_of_mem _ (subset edge member),by simp only [List.length_cons]; omega⟩
  | @lam parent child stamp body es lookup notFunction tail ih =>
    obtain ⟨proper,edge,member,endpoint⟩ := incident
    rcases List.mem_cons.mp member with equal | below
    · subst edge
      rcases endpoint with source | target
      · have equal := Source.actual_parent source
        change p=parent at equal
        have actualTarget : Target t parent (some ⟨p,proper⟩) := Or.inl equal.symm
        exact ⟨es,tail.at_actual_target actualTarget,fun _ member=>List.mem_cons_of_mem _ member,by simp⟩
      · have actual : Target t (parent++[child])
            (some ⟨parent++[child],Or.inr ⟨stamp,body,lookup⟩⟩) := Or.inl rfl
        have equal := target_position_eq target actual
        change p=parent++[child] at equal
        subst p
        exact ⟨_,.lam lookup notFunction tail,fun _ member=>member,Nat.le_refl _⟩
    · obtain ⟨more,actual,subset,bound⟩ := ih ⟨proper,edge,below,endpoint⟩
      exact ⟨more,actual,fun edge member=>List.mem_cons_of_mem _ (subset edge member),by simp only [List.length_cons]; omega⟩
  | var lookup binder split depth tail ih => exact ih incident
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
open SyntaxIncidence
private theorem PrerequisiteChain.proper_start_incident
    (chain : PrerequisiteChain t start edges) (proper : ProperAt t start) :
    PrerequisiteIncident t edges start := by
  cases chain with
  | redex_app lookup => exact ⟨proper,_,List.mem_cons_self,Or.inl ⟨.fn,_,_,rfl,lookup,.fn⟩⟩
  | redex_lam lookup => exact ⟨proper,_,List.mem_cons_self,Or.inr (Or.inl rfl)⟩
  | app lookup notLambda tail => exact ⟨proper,_,List.mem_cons_self,Or.inl ⟨.fn,_,_,rfl,lookup,.fn⟩⟩
  | lam lookup notFunction tail => exact ⟨proper,_,List.mem_cons_self,Or.inr (Or.inl rfl)⟩
  | var lookup binder split depth tail =>
    rcases proper with ⟨_,_,_,atApp⟩ | ⟨_,_,atLambda⟩
    · rw [lookup] at atApp; cases Option.some.inj atApp
    · rw [lookup] at atLambda; cases Option.some.inj atLambda
private theorem PrerequisiteChain.target_incident
    (chain : PrerequisiteChain t start edges) (target : Target t start (some vertex)) :
    PrerequisiteIncident t edges vertex.val :=
  (chain.at_actual_target target).proper_start_incident vertex.property

private theorem app_incident_cases
    (lookup : t.subterm position=some (.app stamp fn arg))
    (tail : PrerequisiteChain t (position++[.fn]) edges)
    (incident : PrerequisiteIncident t ((position++[.fn])::edges) p) :
    p=position ∨PrerequisiteIncident t edges p := by
  obtain ⟨proper,edge,member,endpoint⟩ := incident
  rcases List.mem_cons.mp member with equal | below
  · subst edge
    rcases endpoint with source | target
    · have actual : Source t (position++[.fn]) (some ⟨position,Or.inl ⟨stamp,fn,arg,lookup⟩⟩) :=
        ⟨.fn,_,_,rfl,lookup,.fn⟩
      exact Or.inl (source_position_eq source actual)
    · exact Or.inr (tail.target_incident target)
  · exact Or.inr ⟨proper,edge,below,endpoint⟩

private theorem lam_incident_cases
    (lookup : t.subterm (parent++[child])=some (.lam stamp body))
    (tail : PrerequisiteChain t parent edges)
    (incident : PrerequisiteIncident t ((parent++[child])::edges) p) :
    p=parent++[child] ∨PrerequisiteIncident t edges p := by
  obtain ⟨proper,edge,member,endpoint⟩ := incident
  rcases List.mem_cons.mp member with equal | below
  · subst edge
    rcases endpoint with source | target
    · have equal := Source.actual_parent source
      have actualTarget : Target t parent (some ⟨p,proper⟩) := Or.inl equal.symm
      exact Or.inr (tail.target_incident actualTarget)
    · have actual : Target t (parent++[child])
          (some ⟨parent++[child],Or.inr ⟨stamp,body,lookup⟩⟩) := Or.inl rfl
      exact Or.inl (target_position_eq target actual)
  · exact Or.inr ⟨proper,edge,below,endpoint⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem redex_endpoint_tags_ne
    {t left right body argument : LTerm} {parent : Path} {appStamp lamStamp : Label}
    (redex : t.subterm parent=some (.app appStamp (.lam lamStamp body) argument))
    (leftLookup : t.subterm parent=some left) (rightLookup : t.subterm (parent++[.fn])=some right) :
    left.constructorTag≠right.constructorTag := by
  have leftEq := Option.some.inj (leftLookup.symm.trans redex)
  have childLookup : t.subterm (parent++[.fn])=some (.lam lamStamp body) := by
    rw [LTerm.subterm_append,redex]; rfl
  have rightEq := Option.some.inj (rightLookup.symm.trans childLookup)
  rw [leftEq,rightEq]
  intro impossible
  cases impossible

private theorem redex_incident_tag_injective
    {t left right body argument : LTerm} {parent p q : Path} {appStamp lamStamp : Label}
    (redex : t.subterm parent=some (.app appStamp (.lam lamStamp body) argument))
    (leftIncident : PrerequisiteIncident t [parent++[.fn]] p)
    (rightIncident : PrerequisiteIncident t [parent++[.fn]] q)
    (leftLookup : t.subterm p=some left) (rightLookup : t.subterm q=some right)
    (sameTag : left.constructorTag=right.constructorTag) : p=q := by
  rcases redex_incident_positions redex leftIncident with leftEq | leftEq
  · rcases redex_incident_positions redex rightIncident with rightEq | rightEq
    · exact leftEq.trans rightEq.symm
    · subst p; subst q
      exact False.elim (redex_endpoint_tags_ne redex leftLookup rightLookup sameTag)
  · rcases redex_incident_positions redex rightIncident with rightEq | rightEq
    · subst p; subst q
      exact False.elim (redex_endpoint_tags_ne redex rightLookup leftLookup sameTag.symm)
    · exact leftEq.trans rightEq.symm

/-- On ONE actual chain, its own chain length plus constructor distinguishes
incident proper vertices. The terminal app/lambda pair has equal length1;
its different constructors are used explicitly, not a false strict-rank claim. -/
theorem PrerequisiteChain.incident_rank_constructor_injective
    {left right : LTerm} {p q : Path}
    (chain : PrerequisiteChain t start edges)
    (leftIncident : PrerequisiteIncident t edges p)
    (rightIncident : PrerequisiteIncident t edges q)
    (leftChain : PrerequisiteChain t p leftEdges)
    (rightChain : PrerequisiteChain t q rightEdges)
    (leftLookup : t.subterm p=some left) (rightLookup : t.subterm q=some right)
    (sameTag : left.constructorTag=right.constructorTag)
    (sameLength : leftEdges.length=rightEdges.length) : p=q := by
  induction chain with
  | redex_app lookup => exact redex_incident_tag_injective lookup leftIncident rightIncident leftLookup rightLookup sameTag
  | redex_lam lookup => exact redex_incident_tag_injective lookup leftIncident rightIncident leftLookup rightLookup sameTag
  | @app position stamp fn arg es lookup notLambda tail ih =>
    rcases app_incident_cases lookup tail leftIncident with atHead | inTail
    · rcases app_incident_cases lookup tail rightIncident with otherHead | otherTail
      · exact atHead.trans otherHead.symm
      · subst p
        obtain ⟨more,actual,subset,bound⟩ := tail.incident_chain otherTail
        have leftEq := leftChain.unique (.app lookup notLambda tail)
        have rightEq := rightChain.unique actual
        have leftLength := congrArg List.length leftEq
        have rightLength := congrArg List.length rightEq
        simp only [List.length_cons] at leftLength
        omega
    · rcases app_incident_cases lookup tail rightIncident with otherHead | otherTail
      · subst q
        obtain ⟨more,actual,subset,bound⟩ := tail.incident_chain inTail
        have leftEq := leftChain.unique actual
        have rightEq := rightChain.unique (.app lookup notLambda tail)
        have leftLength := congrArg List.length leftEq
        have rightLength := congrArg List.length rightEq
        simp only [List.length_cons] at rightLength
        omega
      · exact ih inTail otherTail
  | @lam parent child stamp body es lookup notFunction tail ih =>
    rcases lam_incident_cases lookup tail leftIncident with atHead | inTail
    · rcases lam_incident_cases lookup tail rightIncident with otherHead | otherTail
      · exact atHead.trans otherHead.symm
      · subst p
        obtain ⟨more,actual,subset,bound⟩ := tail.incident_chain otherTail
        have leftEq := leftChain.unique (.lam lookup notFunction tail)
        have rightEq := rightChain.unique actual
        have leftLength := congrArg List.length leftEq
        have rightLength := congrArg List.length rightEq
        simp only [List.length_cons] at leftLength
        omega
    · rcases lam_incident_cases lookup tail rightIncident with otherHead | otherTail
      · subst q
        obtain ⟨more,actual,subset,bound⟩ := tail.incident_chain inTail
        have leftEq := leftChain.unique actual
        have rightEq := rightChain.unique (.lam lookup notFunction tail)
        have leftLength := congrArg List.length leftEq
        have rightLength := congrArg List.length rightEq
        simp only [List.length_cons] at rightLength
        omega
      · exact ih inTail otherTail
  | var lookup binder split depth tail ih => exact ih leftIncident rightIncident
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem PrerequisiteIncident.lookup (incident : PrerequisiteIncident t edges p) :
    ∃ current,t.subterm p=some current := by
  obtain ⟨proper,edge,member,endpoint⟩ := incident
  rcases proper with ⟨stamp,fn,arg,lookup⟩ | ⟨stamp,body,lookup⟩
  · exact ⟨_,lookup⟩
  · exact ⟨_,lookup⟩

/-- Actual beta node preimages are injective on the incident proper vertices
of ONE all-old chain. They need not be injective on arbitrary copied syntax. -/
theorem StepAt.incident_preimage_injective
    {source target body argument : LTerm} {site p q oldPosition : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (chain : PrerequisiteChain target start edges)
    (uncreated : ∀ edge∈edges,¬BetaCreatedIncoming body site edge)
    (leftIncident : PrerequisiteIncident target edges p)
    (rightIncident : PrerequisiteIncident target edges q)
    (leftOrigin : BetaNodePreimage body argument site p oldPosition)
    (rightOrigin : BetaNodePreimage body argument site q oldPosition) : p=q := by
  obtain ⟨leftEdges,leftChain,leftSubset,leftBound⟩ := chain.incident_chain leftIncident
  obtain ⟨rightEdges,rightChain,rightSubset,rightBound⟩ := chain.incident_chain rightIncident
  obtain ⟨oldLeft,oldLeftChain,leftPreimages⟩ := leftChain.beta_uncreated_reflect step redex leftOrigin
    (fun edge member=>uncreated edge (leftSubset edge member))
  obtain ⟨oldRight,oldRightChain,rightPreimages⟩ := rightChain.beta_uncreated_reflect step redex rightOrigin
    (fun edge member=>uncreated edge (rightSubset edge member))
  have oldEdgesEq := oldLeftChain.unique oldRightChain
  have sameLength : leftEdges.length=rightEdges.length := by
    rw [leftPreimages.length_eq,rightPreimages.length_eq,oldEdgesEq]
  obtain ⟨left,leftLookup⟩ := leftIncident.lookup
  obtain ⟨right,rightLookup⟩ := rightIncident.lookup
  obtain ⟨oldLeftNode,oldLeftLookup,leftTag⟩ := step.preimage_node_constructor redex leftOrigin leftLookup
  obtain ⟨oldRightNode,oldRightLookup,rightTag⟩ := step.preimage_node_constructor redex rightOrigin rightLookup
  have oldNodesEq := Option.some.inj (oldLeftLookup.symm.trans oldRightLookup)
  have sameTag : left.constructorTag=right.constructorTag :=
    leftTag.symm.trans ((congrArg LTerm.constructorTag oldNodesEq).trans rightTag)
  exact chain.incident_rank_constructor_injective leftIncident rightIncident leftChain rightChain
    leftLookup rightLookup sameTag sameLength
end Lamping.Lambda.Labelled
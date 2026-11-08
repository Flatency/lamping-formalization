import Lamping.Lamping.ActionAncestor
import Lamping.Lamping.MatchingDefinitions
namespace Lamping.AG
open Graph Lambda
/-- The passive copies in the literal right side of each standard action. -/
inductive ActionPassiveNode : (s : Schema) →s.right.N →Prop where
  | fan {op : Op} {i j : Nat} {lt : i<j} (copy : Bool) :
      ActionPassiveNode (.fanAction op i j lt) (.inl copy)
  | cro {op : Op} {i j : Nat} {lt : i<j} :
      ActionPassiveNode (.croAction op i j lt) (.inl ())
  | bra {op : Op} {i j : Nat} {lt : i<j} :
      ActionPassiveNode (.braAction op i j lt) (.inl ())

theorem ActionPassiveNode.sort {s : Schema} {node : s.right.N} (passive : ActionPassiveNode s node) :
    (s.right.net.label node).sort=.op s.passive := by
  cases passive <;> rfl

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
/-- Classify the actual endpoint; no graph-node identity is inferred from labels. -/
theorem PathSite.action_access_node_cases (action : IsAction s) {root : B}
    (path : RootAccess site.reduce root) :
    (∃ port : NodePort signature K kept,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∨
    ∃ (node : s.right.N) (port : Port (s.right.net.label node).sort),
      ActionPassiveNode s node ∧
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr node,port⟩)) := by
  cases action with
  | fan op i j lt =>
    obtain ⟨kind,typed⟩ := path.property.2.2
    cases last : path.val.getLast? with
    | none => simp only [accessKind,last,Option.bind_none] at typed;cases typed
    | some e =>
      rw [accessKind,last] at typed
      cases arrival : site.reduce.wire e with
      | inr rest => simp only [Option.bind_some,arrival] at typed;cases typed
      | inl port =>
        rcases port with ⟨node,p⟩
        simp only [Option.bind_some,arrival] at typed
        cases node with
        | inl n =>
          refine Or.inl ⟨⟨n,p⟩,?_⟩
          rw [←arrival,Pairing.involutive]
        | inr fresh =>
          cases fresh with
          | inl copy =>
            refine Or.inr ⟨.inl copy,p,.fan copy,?_⟩
            rw [←arrival,Pairing.involutive]
          | inr active =>
            change portKind (.op .fan) p=some kind at typed
            cases p <;> cases typed
  | cro op i j lt =>
    obtain ⟨kind,typed⟩ := path.property.2.2
    cases last : path.val.getLast? with
    | none => simp only [accessKind,last,Option.bind_none] at typed;cases typed
    | some e =>
      rw [accessKind,last] at typed
      cases arrival : site.reduce.wire e with
      | inr rest => simp only [Option.bind_some,arrival] at typed;cases typed
      | inl port =>
        rcases port with ⟨node,p⟩
        simp only [Option.bind_some,arrival] at typed
        cases node with
        | inl n =>
          refine Or.inl ⟨⟨n,p⟩,?_⟩
          rw [←arrival,Pairing.involutive]
        | inr fresh =>
          cases fresh with
          | inl copy =>
            cases copy
            refine Or.inr ⟨.inl (),p,.cro,?_⟩
            rw [←arrival,Pairing.involutive]
          | inr active =>
            change portKind (.op .cro) p=some kind at typed
            cases p <;> cases typed
  | bra op i j lt =>
    obtain ⟨kind,typed⟩ := path.property.2.2
    cases last : path.val.getLast? with
    | none => simp only [accessKind,last,Option.bind_none] at typed;cases typed
    | some e =>
      rw [accessKind,last] at typed
      cases arrival : site.reduce.wire e with
      | inr rest => simp only [Option.bind_some,arrival] at typed;cases typed
      | inl port =>
        rcases port with ⟨node,p⟩
        simp only [Option.bind_some,arrival] at typed
        cases node with
        | inl n =>
          refine Or.inl ⟨⟨n,p⟩,?_⟩
          rw [←arrival,Pairing.involutive]
        | inr fresh =>
          cases fresh with
          | inl copy =>
            cases copy
            refine Or.inr ⟨.inl (),p,.bra,?_⟩
            rw [←arrival,Pairing.involutive]
          | inr active =>
            change portKind (.op .bra) p=some kind at typed
            cases p <;> cases typed
end
#print axioms ActionPassiveNode.sort
#print axioms PathSite.action_access_node_cases
end Lamping.AG

import Lamping.Lamping.RootedPortRoutes
import Lamping.Lamping.InitialPathRelabelling
namespace Lamping.AG
open Graph Lambda
def IsContextPort (kind : Kind) (p : Port kind) : Prop :=
  portKind kind p=some .app ∨portKind kind p=some .lam
private theorem context_port_address (kind : Kind) (p : Port kind) (address : Path)
    (context : IsContextPort kind p) : syntaxPortAddress kind p address=some address := by
  cases kind with
  | garbage => rcases context with bad | bad <;> cases bad
  | op op =>
    cases op <;> cases p <;> rename_i p <;> cases p
    all_goals first | rfl | simp_all [IsContextPort,portKind]

/-- Every actual proper context port, rather than just every syntax shape,
is reached by a labelled root path in the recursively encoded graph. -/
theorem encode_context_port_route (t : Term) (n : Nat) :
    ∀ (node : (encode n t).N) (p : Port ((encode n t).net.label node).sort),
      IsContextPort ((encode n t).net.label node).sort p →
      RootedPortRoute (encode n t).net (.inl ()) (.inl ⟨node,p⟩) := by
  induction t generalizing n with
  | var k =>
    intro node p context
    rcases context with bad | bad <;> cases bad
  | lam body ih =>
    dsimp only [encode]
    by_cases used : free body 0
    · rw [dif_pos used]
      rintro (node | node) p context
      · cases p with
        | inl u => exact ⟨[.inr (.inl (.inl ()))],Context.empty,Context.empty,.single _ _,rfl,rfl⟩
        | inr b => cases b <;> rcases context with bad | bad <;> cases bad
      · exact (ih n node p context).enter_child (lambdaUsed n body used) (encode n body).net
          (initialLambdaUsedBody n body used)
    · rw [dif_neg used]
      rintro ((node | node) | node) p context
      · cases p with
        | inl u => exact ⟨[.inr (.inl (.inl ()))],Context.empty,Context.empty,.single _ _,rfl,rfl⟩
        | inr b => cases b <;> rcases context with bad | bad <;> cases bad
      · rcases context with bad | bad <;> cases bad
      · exact (ih n node p context).enter_child (lambdaUnused n body used) (encode n body).net
          (initialLambdaUnusedBody n body used)
  | app f arg hf ha =>
    dsimp only [encode]
    rintro ((node | (node | node)) | (node | node)) p context
    · cases p with
      | inl u => rcases context with bad | bad <;> cases bad
      | inr b =>
        cases b with
        | false => exact ⟨[.inr (.inl (.inl ()))],Context.empty,Context.empty,.single _ _,rfl,rfl⟩
        | true => rcases context with bad | bad <;> cases bad
    · rcases context with bad | bad <;> cases bad
    · rcases context with bad | bad <;> cases bad
    · exact ((hf n node p context).unionLeft (encode n f).net (encode (n+1) arg).net).enter_child
        (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net) (initialAppFunction n f arg)
    · exact ((ha (n+1) node p context).unionRight (encode n f).net (encode (n+1) arg).net).enter_child
        (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net) (initialAppArgument n f arg)

/-- The same actual context-port route can be labelled by any input, with
exactly the same output context. This is source geometry, not an initial
Independence assumption. -/
theorem encode_context_port_identity (t : Term) (n : Nat) (node : (encode n t).N)
    (p : Port ((encode n t).net.label node).sort)
    (context : IsContextPort ((encode n t).net.label node).sort p) :
    ∃ es : List (Endpoint (encode n t).net),
      es.head?=some (.inr (.inl (.inl ()))) ∧
      es.getLast?=some ((encode n t).net.wire (.inl ⟨node,p⟩)) ∧
      ∀ input,Labelling (encode n t).net es input input := by
  obtain ⟨es,a,b,labels,rooted,last⟩ := encode_context_port_route t n node p context
  obtain ⟨addr⟩ := encode_addressing t n
  have finalState : endpointAddress (encode n t).net addr.nodes (boundaryAddressAt []) addr.vertices
      ((encode n t).net.wire (.inl ⟨node,p⟩))=some (addr.nodes node) := by
    rw [addr.wiring]
    exact context_port_address _ _ _ context
  refine ⟨es,rooted,last,?_⟩
  intro input
  obtain ⟨output,relabel⟩ := encode_root_relabel_input t n es rooted ⟨a,b,labels⟩ input
  have initial := encode_root_initial t n es rooted relabel
  have same := addr.path_context _ initial _ last _ finalState
  exact same ▸ relabel
end Lamping.AG

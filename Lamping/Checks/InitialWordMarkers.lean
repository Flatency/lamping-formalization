import Lamping.Lamping.InitialWordMarkers
import Lamping.Lamping.EncodedAddressing
import Lamping.Lamping.InitialPathControls

namespace Lamping.Checks.InitialWordMarkersChecks
open AG Graph Lambda

namespace ClosedIdentity
private abbrev term : Term := .lam (.var 0)
private abbrev net := (encode 0 term).net
private def bodyEdges : List (Endpoint net) :=
  [.inl ⟨.inl (),lamBody⟩,.inr (.inr (.inr (.inl ()),true)),
    .inl ⟨.inr (),.inl ()⟩,.inr (.inr (.inr (.inr ⟨0,rfl⟩),false))]
private def root : Endpoint net := .inr (.inl (.inl ()))
private def whole := root::bodyEdges
private theorem whole_labels (shell tail : Context) :
    Labelling net whole (shell.replace 0 tail) (shell.replace 0 (tail.cons .empty)) :=
  .cons (LabelledTurn.node (g:=net) (.inl ()) (.inl ()) lamBody (.direct (.lamBody _)))
    (identityBindingLoop 0 shell tail).proper

/-- Real closed INITIAL encode, actual whole assignment and its actual BODY
suffix. Its HEAD emits BODY, whereas its TAIL word is empty. -/
theorem actual_closed_body_marker (shell tail : Context) :
    Closed term ∧ arrivalWord net bodyEdges[0] = [.body] ∧ accessWord net bodyEdges=[] ∧
    ∃ (addr : Addressing net (boundaryAddressAt [])) (middle : Context),
      InitialLabelling (g:=net) bodyEdges middle (shell.replace 0 (tail.cons .empty)) ∧
      (∀ i : Fin whole.length,initialAtomAddress addr.nodes whole[i]=none) ∧
      ∃ i : Fin bodyEdges.length,i.val=1 ∧ InitialMarkerAt addr.nodes bodyEdges[i] [.body] ∧
        ∀ j : Fin bodyEdges.length,∀ p,InitialMarkerAt addr.nodes bodyEdges[j] p → j=i ∧ p=[.body] := by
  have closed : Closed term := by change 0<1;decide
  obtain ⟨addr⟩ := encode_addressing term 0
  have labels := encode_root_initial term 0 whole rfl (whole_labels shell tail)
  have suffix := labels.suffix (pre:=[root]) (es:=bodyEdges) (by intro empty;cases empty)
  obtain ⟨middle,bodyLabels⟩ := suffix
  have noInput := labels.no_initial_inputs addr.nodes (by
    intro e head
    have same : root=e := Option.some.inj head
    subst e;rfl)
  have rootAddress := addr.wiring root
  change some (addr.nodes (.inl ()))=some [] at rootAddress
  have lambdaAddress : addr.nodes (.inl ())=[] := Option.some.inj rootAddress
  have start : endpointAddress net addr.nodes (boundaryAddressAt []) addr.vertices bodyEdges[0]=some [.body] := by
    change some (addr.nodes (.inl ())++[.body])=some [.body]
    rw [lambdaAddress];rfl
  have finish : endpointAddress net addr.nodes (boundaryAddressAt []) addr.vertices
      bodyEdges[3]=none := by
    change endpointAddress net addr.nodes (boundaryAddressAt []) addr.vertices
      (net.wire (.inl ⟨.inl (),lamBind⟩))=none
    rw [addr.wiring];rfl
  obtain ⟨i,marked,unique⟩ := bodyLabels.drop_marker addr bodyEdges[0] bodyEdges[3] rfl rfl [.body] start finish rfl
  have ordinal : i.val=1 := by
    rcases i with ⟨k,bound⟩
    change k<4 at bound
    have casesK : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases casesK with rfl|rfl|rfl|rfl
    · change none=some ([.body] : Path) at marked;cases marked
    · rfl
    · change none=some ([.body] : Path) at marked;cases marked
    · change none=some ([.body] : Path) at marked;cases marked
  exact ⟨closed,rfl,rfl,addr,middle,bodyLabels,noInput,i,ordinal,marked,unique⟩
end ClosedIdentity

namespace RepeatedPrincipal
/-- A generic Cro/Fan graph. This is not claimed to be an encoded reachable graph. -/
private def labels : Bool → Graph.Label signature
  | false => label .cro 0
  | true => label .fan 0
private def net : Net signature Bool Unit Empty where
  label := labels
  wire := {
    mate := fun e => match e with
      | .inl ⟨false,.inr _⟩ => .inr (.inl ())
      | .inl ⟨false,.inl _⟩ => .inl ⟨true,.inr false⟩
      | .inl ⟨true,.inr false⟩ => .inl ⟨false,.inl ()⟩
      | .inl ⟨true,.inl _⟩ => .inl ⟨true,.inr true⟩
      | .inl ⟨true,.inr true⟩ => .inl ⟨true,.inl ()⟩
      | .inr (.inl _) => .inl ⟨false,.inr ()⟩
      | .inr (.inr ⟨v,_⟩) => nomatch v
    involutive := by
      rintro (⟨n,p⟩| (u|⟨v,d⟩))
      · cases n <;> cases p with
        | inl u => cases u;rfl
        | inr aux => cases aux <;> rfl
      · cases u;rfl
      · exact nomatch v
    fixedPointFree := by
      rintro (⟨n,p⟩| (u|⟨v,d⟩)) same
      · cases n <;> cases p with
        | inl u => cases u;cases same
        | inr aux => cases aux <;> cases same
      · cases same
      · exact nomatch v }
private def addr : Addressing net (fun _ => some []) where
  nodes _ := []
  vertices := Empty.elim
  wiring := by
    rintro (⟨n,p⟩| (u|⟨v,d⟩))
    · cases n <;> cases p with
      | inl u => cases u;rfl
      | inr aux => cases aux <;> rfl
    · rfl
    · exact nomatch v
private def edges : List (Endpoint net) :=
  [.inr (.inl ()),.inl ⟨false,.inl ()⟩,.inl ⟨true,.inl ()⟩,.inl ⟨true,.inl ()⟩]
private theorem actual_labels (shell tail : Context) :
    InitialLabelling (g:=net) edges (shell.replace 0 tail)
      (shell.replace 0 (tail.cons (.star (.o .empty)))) :=
  .cons (InitialTurn.node (g:=net) false (.inr ()) (.inl ()) (.cro shell tail))
    (.cons (InitialTurn.node (g:=net) true fanO (.inl ()) (.fanO shell tail .empty))
      (.cons (InitialTurn.node (g:=net) true fanStar (.inl ()) (.fanStar shell tail (.o .empty))) (.single _ _)))

theorem actual_repeated_endpoint_unique_ordinal (shell tail : Context) :
    edges[2]=edges[3] ∧ (⟨2,by decide⟩ : Fin edges.length)≠⟨3,by decide⟩ ∧
    ∃ i : Fin edges.length,i.val=0 ∧ InitialMarkerAt addr.nodes edges[i] [] ∧
      ∀ j : Fin edges.length,∀ p,InitialMarkerAt addr.nodes edges[j] p → j=i ∧ p=[] := by
  have labels := actual_labels shell tail
  obtain ⟨i,marked,unique⟩ := labels.drop_marker addr edges[0] edges[3] rfl rfl [] rfl rfl rfl
  have first : InitialMarkerAt addr.nodes edges[0] [] := rfl
  have same := (unique ⟨0,by decide⟩ [] first).1
  have ordinal : i.val=0 := congrArg Fin.val same.symm
  have different : (⟨2,by decide⟩ : Fin edges.length)≠⟨3,by decide⟩ := by decide
  exact ⟨rfl,different,i,ordinal,marked,unique⟩
end RepeatedPrincipal

#print axioms ClosedIdentity.actual_closed_body_marker
#print axioms RepeatedPrincipal.actual_repeated_endpoint_unique_ordinal
end Lamping.Checks.InitialWordMarkersChecks

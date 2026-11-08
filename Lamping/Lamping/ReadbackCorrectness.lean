import Lamping.Lamping.ExecutableTraversal

namespace Lamping.AG.Readback.ContextData

@[simp] theorem denote_get (a : ContextData) (i : Nat) :
    (Context.ofList a).get i = a.get i := by
  induction a generalizing i with
  | nil => simp [get,Context.ofList,Context.empty]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simpa [get,Context.ofList] using ih i

@[simp] theorem denote_drop (a : ContextData) (i : Nat) :
    Context.ofList (a.drop i) = (Context.ofList a).tail i := by
  induction i generalizing a with
  | zero => ext k; simp [Context.tail]
  | succ i ih =>
    cases a with
    | nil => ext k; rfl
    | cons x xs =>
      rw [List.drop_succ_cons,ih]
      ext k
      change (Context.ofList xs).get (i+k) =
        ((Context.ofList xs).cons x).get (i+1+k)
      rw [show i+1+k=(i+k)+1 by omega,Context.cons_succ]

private theorem replace_cons_successor (a b : Context) (x : Level) (i : Nat) :
    (a.cons x).replace (i+1) b = (a.replace i b).cons x := by
  ext k
  cases k with
  | zero => simp [Context.replace]
  | succ k => simp [Context.replace,Context.cons]

@[simp] theorem denote_replaceTail (a tail : ContextData) (i : Nat) :
    Context.ofList (a.replaceTail i tail) =
      (Context.ofList a).replace i (Context.ofList tail) := by
  unfold replaceTail
  rw [Context.ofList_normalise]
  induction i generalizing a with
  | zero => simp [lowPrefix]
  | succ i ih =>
    cases a with
    | nil =>
      simp only [lowPrefix,List.cons_append,Context.ofList_cons]
      rw [ih]
      simpa using (replace_cons_successor Context.empty (Context.ofList tail) .empty i).symm
    | cons x xs =>
      simp only [lowPrefix,List.cons_append,Context.ofList_cons]
      rw [ih,replace_cons_successor]

@[simp] theorem denote_put (a : ContextData) (i : Nat) (x : Level) :
    Context.ofList (a.put i x) =
      (Context.ofList a).replace i (((Context.ofList a).tail (i+1)).cons x) := by
  simp [put]

end Lamping.AG.Readback.ContextData

namespace Lamping.AG.Readback
open Graph

private theorem rebuild (a : Context) (n : Nat) :
    a.replace n ((a.tail (n+1)).cons (a.get n)) = a := by
  ext k
  by_cases low : k<n
  · simp [Context.replace,low]
  · by_cases eq : k=n
    · subst k; simp [Context.replace]
    · have diff : k-n=(k-(n+1))+1 := by omega
      simp [Context.replace,low,diff,Context.tail]
      congr 1
      omega

private theorem rebuild_two (a : Context) (n : Nat) :
    a.replace n (((a.tail (n+2)).cons (a.get (n+1))).cons (a.get n)) = a := by
  ext k
  by_cases low : k<n
  · simp [Context.replace,low]
  · by_cases eq : k=n
    · subst k; simp [Context.replace]
    · by_cases next : k=n+1
      · subst k; simp [Context.replace]
      · have diff : k-n=(k-(n+2))+1+1 := by omega
        simp [Context.replace,low,diff,Context.tail]
        congr 1
        omega

/-- Each successful executable control step is exactly an existing AG traversal.
This theorem has no graph correctness or matching premise. -/
theorem executeControl_sound (i : Nat) (kind : Kind) (incoming outgoing : Port kind)
    (a b : ContextData) (success : executeControl i kind incoming a=some (outgoing,b)) :
    Traversal i kind incoming outgoing (Context.ofList a) (Context.ofList b) := by
  cases kind with
  | garbage => simp [executeControl] at success
  | op op =>
    cases op with
    | app => simp [executeControl] at success
    | lam => simp [executeControl] at success
    | fan =>
      cases incoming with
      | inr branch =>
        cases branch <;> simp only [executeControl,Option.some.injEq,Prod.mk.injEq] at success
        · obtain ⟨rfl,rfl⟩ := success
          simpa only [ContextData.denote_put,←ContextData.denote_get,rebuild] using
            (Traversal.direct (Passage.fanO (i:=i) (Context.ofList a)
              ((Context.ofList a).tail (i+1)) ((Context.ofList a).get i)))
        · obtain ⟨rfl,rfl⟩ := success
          simpa only [ContextData.denote_put,←ContextData.denote_get,rebuild] using
            (Traversal.direct (Passage.fanStar (i:=i) (Context.ofList a)
              ((Context.ofList a).tail (i+1)) ((Context.ofList a).get i)))
      | inl slot =>
        cases slot
        simp only [executeControl] at success
        split at success <;> try contradiction
        · rename_i child shape
          obtain ⟨rfl,rfl⟩ := Option.some.inj success
          have shape' : (Context.ofList a).get i=.o child := by simpa using shape
          have traversal := Traversal.inverse (Passage.fanO (i:=i) (Context.ofList a)
            ((Context.ofList a).tail (i+1)) child)
          have input : (Context.ofList a).replace i
              (((Context.ofList a).tail (i+1)).cons (.o child))=Context.ofList a := by
            rw [←shape',rebuild]
          simpa only [input,ContextData.denote_put] using traversal
        · rename_i child shape
          obtain ⟨rfl,rfl⟩ := Option.some.inj success
          have shape' : (Context.ofList a).get i=.star child := by simpa using shape
          have traversal := Traversal.inverse (Passage.fanStar (i:=i) (Context.ofList a)
            ((Context.ofList a).tail (i+1)) child)
          have input : (Context.ofList a).replace i
              (((Context.ofList a).tail (i+1)).cons (.star child))=Context.ofList a := by
            rw [←shape',rebuild]
          simpa only [input,ContextData.denote_put] using traversal
    | cro =>
      cases incoming with
      | inr slot =>
        cases slot
        obtain ⟨rfl,rfl⟩ := Option.some.inj success
        simpa only [ContextData.denote_replaceTail,Context.ofList_cons,
          ContextData.denote_drop,Context.replace_tail] using
          (Traversal.direct (Passage.cro (i:=i) (Context.ofList a) ((Context.ofList a).tail i)))
      | inl slot =>
        cases slot
        simp only [executeControl] at success
        split at success <;> try contradiction
        rename_i shape
        obtain ⟨rfl,rfl⟩ := Option.some.inj success
        have input : (Context.ofList a).replace i
            (((Context.ofList a).tail (i+1)).cons .empty)=Context.ofList a := by
          rw [←show (Context.ofList a).get i=.empty by simpa using shape,rebuild]
        simpa only [input,ContextData.denote_replaceTail,ContextData.denote_drop] using
          (Traversal.inverse (Passage.cro (i:=i) (Context.ofList a)
            ((Context.ofList a).tail (i+1))))
    | bra =>
      cases incoming with
      | inr slot =>
        cases slot
        obtain ⟨rfl,rfl⟩ := Option.some.inj success
        simpa only [ContextData.denote_replaceTail,Context.ofList_cons,
          ContextData.denote_drop,←ContextData.denote_get,rebuild_two] using
          (Traversal.direct (Passage.bra (i:=i) (Context.ofList a)
            ((Context.ofList a).tail (i+2)) ((Context.ofList a).get (i+1))
              ((Context.ofList a).get i)))
      | inl slot =>
        cases slot
        simp only [executeControl] at success
        split at success <;> try contradiction
        rename_i left right shape
        obtain ⟨rfl,rfl⟩ := Option.some.inj success
        have input : (Context.ofList a).replace i
            (((Context.ofList a).tail (i+1)).cons (.pair left right))=Context.ofList a := by
          rw [←show (Context.ofList a).get i=.pair left right by simpa using shape,rebuild]
        simpa only [input,ContextData.denote_replaceTail,Context.ofList_cons,
          ContextData.denote_drop] using
          (Traversal.inverse (Passage.bra (i:=i) (Context.ofList a)
            ((Context.ofList a).tail (i+1)) left right))

end Lamping.AG.Readback

namespace Lamping.AG.Readback
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

/-- Advancing the executable scanner is a genuine labelled graph turn at the
actual wire endpoint, including subdivision occurrences. -/
theorem scanOne_next_sound (g : Net signature N B W) (departure next : Endpoint g)
    (a b : ContextData) (success : scanOne g departure a=.next next b) :
    LabelledTurn g (g.wire departure) next (Context.ofList a) (Context.ofList b) := by
  cases wireEq : g.wire departure with
  | inl arrival =>
    obtain ⟨node,port⟩ := arrival
    cases role : portKind (g.label node).sort port with
    | some kind => simp [scanOne,wireEq,role] at success
    | none =>
      cases control : executeControl (g.label node).index (g.label node).sort port a with
      | none => simp [scanOne,wireEq,role,control] at success
      | some result =>
        obtain ⟨out,after⟩ := result
        simp only [scanOne,wireEq,role,control,ScanResult.next.injEq] at success
        obtain ⟨rfl,rfl⟩ := success
        exact .node node port out (executeControl_sound _ _ _ _ _ _ control)
  | inr target =>
    cases target with
    | inl boundary => simp [scanOne,wireEq] at success
    | inr wire =>
      obtain ⟨vertex,direction⟩ := wire
      simp only [scanOne,wireEq,ScanResult.next.injEq] at success
      obtain ⟨rfl,rfl⟩ := success
      exact .transparent vertex direction _

/-- Terminal metadata is the actual arrival, and a scan does not relabel at
that stopping point. -/
theorem scanOne_terminal_sound (g : Net signature N B W) (departure : Endpoint g)
    (arrival : NodePort signature N g.label) (kind : AccessKind) (a b : ContextData)
    (success : scanOne g departure a=.terminal arrival kind b) :
    g.wire departure=.inl arrival ∧
      portKind (g.label arrival.1).sort arrival.2=some kind ∧ b=a := by
  cases wireEq : g.wire departure with
  | inl actual =>
    obtain ⟨node,port⟩ := actual
    cases role : portKind (g.label node).sort port with
    | some actualKind =>
      simp only [scanOne,wireEq,role,ScanResult.terminal.injEq] at success
      obtain ⟨rfl,rfl,rfl⟩ := success
      exact ⟨rfl,role,rfl⟩
    | none =>
      cases control : executeControl (g.label node).index (g.label node).sort port a <;>
        simp [scanOne,wireEq,role,control] at success
  | inr target => cases target <;> simp [scanOne,wireEq] at success

end
end Lamping.AG.Readback


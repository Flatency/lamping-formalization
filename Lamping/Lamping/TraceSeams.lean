import Lamping.Lamping.ExpandedLabelSurgery
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Join at the selected directed segment and retain its actual context at
that precise ordinal, even when the same physical endpoint occurs elsewhere. -/
theorem Labelling.join_contextTrace {pre post : List (Endpoint g)} {e : Endpoint g} {input a b : Context}
    (first : Labelling g (pre++[e]) input a) (last : Labelling g (e::post) a b) :
    ∃ cs,ContextTrace g (pre++e::post) cs ∧ cs[pre.length]?=some a ∧ cs.getLast?=some b ∧ cs.head?=some input := by
  induction pre generalizing input with
  | nil =>
    cases first
    obtain ⟨cs,trace,head,finish⟩ := last.contextTrace g
    refine ⟨cs,trace,?_,finish,head⟩
    cases cs with
    | nil => cases head
    | cons => exact head
  | cons x pre ih =>
    cases pre with
    | nil =>
      cases first with
      | cons turn rest =>
        cases rest
        obtain ⟨cs,trace,head,finish⟩ := last.contextTrace g
        cases cs with
        | nil => cases head
        | cons y cs =>
          have same : y=a := Option.some.inj head
          subst y
          exact ⟨input::a::cs,.cons turn trace,rfl,by simpa only [List.getLast?_cons_cons] using finish,rfl⟩
    | cons y pre =>
      cases first with
      | cons turn rest =>
        obtain ⟨cs,trace,point,finish,head⟩ := ih rest
        cases cs with
        | nil => cases head
        | cons middle cs =>
          have same := Option.some.inj head
          subst middle
          exact ⟨input::_::cs,.cons turn trace,by simpa only [List.length_cons,List.getElem?_cons_succ] using point,
            by simpa only [List.getLast?_cons_cons] using finish,rfl⟩
/-- Split the supplied assignment at its selected ordinal. The same segment
is retained on both sides, and both labels use the supplied seam context. -/
theorem ContextTrace.split_segment_at {es cs} (trace : ContextTrace g es cs)
    (i : Nat) (e : Endpoint g) (a input b : Context)
    (atE : es[i]?=some e) (atA : cs[i]?=some a)
    (head : cs.head?=some input) (finish : cs.getLast?=some b) :
    ∃ pre post,pre.length=i ∧ es=pre++e::post ∧
      Labelling g (pre++[e]) input a ∧ Labelling g (e::post) a b := by
  induction trace generalizing i input with
  | single x c =>
    cases i with
    | zero =>
      have hx := Option.some.inj atE
      have ha := Option.some.inj atA
      have hi := Option.some.inj head
      have hb := Option.some.inj finish
      subst x; subst c; subst input; subst b
      exact ⟨[],[],rfl,rfl,.single _ _,.single _ _⟩
    | succ i => simp at atE
  | @cons x y tail start middle rest turn after ih =>
    have hi : start=input := Option.some.inj head
    subst input
    cases i with
    | zero =>
      have hx := Option.some.inj atE
      have ha := Option.some.inj atA
      subst e; subst a
      exact ⟨[],y::tail,rfl,rfl,.single _ _,(ContextTrace.cons turn after).labelling g rfl finish⟩
    | succ i =>
      have last : (middle::rest).getLast?=some b := by
        simpa only [List.getLast?_cons_cons] using finish
      obtain ⟨pre,post,len,decomp,prefLabels,suffix⟩ := ih i middle atE atA rfl last
      refine ⟨x::pre,post,by simp [len],by simp [decomp],?_,suffix⟩
      cases pre with
      | nil =>
        have same : y=e := Option.some.inj (congrArg List.head? decomp)
        subst e
        exact .cons turn prefLabels
      | cons z pre =>
        have same : y=z := Option.some.inj (congrArg List.head? decomp)
        subst z
        exact .cons turn prefLabels

 theorem Forward.suffix_at {es : List (Endpoint g)} (fw : Forward g es)
    (i : Nat) (e : Endpoint g) (atE : es[i]?=some e) : Forward g (es.drop i) := by
  induction fw generalizing i with
  | single x =>
    cases i with
    | zero => exact .single x
    | succ i => simp at atE
  | node n p q arrives leaves direction after ih =>
    cases i with
    | zero => exact .node n p q arrives leaves direction after
    | succ i => exact ih i atE
  | transparent w d arrives leaves after ih =>
    cases i with
    | zero => exact .transparent w d arrives leaves after
    | succ i => exact ih i atE
 theorem Forward.prefix_of_append {pre tail : List (Endpoint g)}
     (fw : Forward g (pre++tail)) (nonempty : pre≠[]) : Forward g pre := by
  induction pre with
  | nil => exact False.elim (nonempty rfl)
  | cons x pre ih =>
    cases pre with
    | nil => exact .single x
    | cons y pre =>
      cases fw with
      | node n p q arrives leaves direction after =>
        exact .node n p q arrives leaves direction (ih after (by simp))
      | transparent w d arrives leaves after => exact .transparent w d arrives leaves (ih after (by simp))
end
end Lamping.AG







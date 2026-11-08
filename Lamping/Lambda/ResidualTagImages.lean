import Lamping.Lambda.ResidualNodePreimages
import Lamping.Lambda.CreationExterior

namespace Lamping.Lambda.Labelled

private theorem BetaNodePreimage.uncons
    (origin : BetaNodePreimage body argument (child::site) p q) :
    (p=q ∧ ¬∃relative,p=(child::site)++relative) ∨
    ∃ inside old,p=child::inside ∧q=child::old ∧
      BetaNodePreimage body argument site inside old := by
  cases origin with
  | context outside => exact .inl ⟨rfl,outside⟩
  | @retained relative node lookup nonselected =>
    exact .inr ⟨site++relative,(site++[.fn,.body])++relative,rfl,rfl,
      .retained lookup nonselected⟩
  | @copied whereCopy relative node occurs lookup =>
    exact .inr ⟨(site++whereCopy)++relative,(site++[.arg])++relative,rfl,rfl,
      .copied occurs lookup⟩

end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Marked
open Labelled

private theorem valid_passive (valid : Valid m) : Valid m.passive := by
  induction m with
  | var => trivial
  | lam b ih => exact ih valid
  | app tags f a hf ha =>
    refine ⟨hf valid.1,ha valid.2.1,?_⟩
    intro nonempty
    obtain ⟨b,equal⟩ := valid.2.2 nonempty
    subst f
    exact ⟨b.passive,rfl⟩
  | red tags b a hb ha => exact ⟨hb valid.1,ha valid.2,fun _=>⟨b.passive,rfl⟩⟩

private theorem context_image (reduction : ReductionAt site m n)
    (outside : ¬∃relative,p=site++relative) (oldTag : p∈tracePositions name m) :
    p∈tracePositions name n := by
  apply (mem_tagsAt _ _ _).mp
  rw [reduction.tagsAt_outside outside]
  exact (mem_tagsAt _ _ _).mpr oldTag

private theorem root_image {mb ma : Marked} {lb la : LTerm} {tags : List Path}
    (bodyErase : lb.erase=mb.erase)
    (origin : BetaNodePreimage lb la [] p q)
    (oldTag : q∈tracePositions name (.app tags (.lam mb) ma)) :
    p∈tracePositions name (contract mb ma) := by
  cases origin with
  | context outside => exact False.elim (outside ⟨p,rfl⟩)
  | @retained relative node lookup nonselected =>
    apply contract_trace_iff.mpr
    left
    apply (mem_tagsAt _ _ _).mp
    have tag := (mem_tagsAt _ _ _).mpr oldTag
    simpa only [List.nil_append,List.cons_append,tagsAt] using tag
  | @copied whereCopy relative node occurs lookup =>
    apply contract_trace_iff.mpr
    right
    refine ⟨whereCopy,relative,?_,rfl,?_⟩
    · rw [←bodyErase]
      exact occurs
    · apply (mem_tagsAt _ _ _).mp
      have tag := (mem_tagsAt _ _ _).mpr oldTag
      simpa only [List.nil_append,List.cons_append,tagsAt] using tag

private theorem passive_image
    (reduction : ReductionAt site m n) (passive : m.passive=m) (valid : Valid m)
    (turn : Labelled.StepAt site source target) (erased : source.erase=m.erase)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p q)
    (lookup : target.subterm p=some (.app currentStamp currentFn currentArg))
    (oldTag : q∈tracePositions name m) : p∈tracePositions name n := by
  induction reduction generalizing source target p q with
  | appRoot tags mb ma =>
    cases turn with
    | root appStamp lamStamp lb la =>
      have parts : lb.erase=mb.erase ∧la.erase=ma.erase := by
        simpa only [LTerm.erase,Marked.erase,Term.app.injEq,Term.lam.injEq] using erased
      have nodes := Option.some.inj redex
      cases nodes
      exact root_image parts.1 origin oldTag
  | redRoot => cases passive
  | @lam site m n reduction ih =>
    cases turn with
    | body turn =>
      rcases origin.uncons with ⟨equal,outside⟩ | ⟨inside,old,atP,atQ,childOrigin⟩
      · subst q
        exact context_image (.lam reduction) outside oldTag
      · subst p;subst q
        have childTag : old∈tracePositions name m := by simpa [tracePositions] using oldTag
        have childLookup := lookup
        simp only [LTerm.subterm] at childLookup redex
        exact List.mem_map.mpr ⟨inside,
          ih (Marked.lam.inj passive) valid turn (Term.lam.inj erased)
            redex childOrigin childLookup childTag,rfl⟩
  | @appL site f g tags a reduction ih =>
    cases turn with
    | fn turn =>
      rcases origin.uncons with ⟨equal,outside⟩ | ⟨inside,old,atP,atQ,childOrigin⟩
      · subst q
        exact context_image (.appL reduction) outside oldTag
      · subst p;subst q
        have childTag : old∈tracePositions name f := by simpa [tracePositions] using oldTag
        have childLookup := lookup
        simp only [LTerm.subterm] at childLookup redex
        have child := ih (Marked.app.inj passive).2.1 valid.1 turn (Term.app.inj erased).1
          redex childOrigin childLookup childTag
        simpa [tracePositions] using child
  | @appR site a b tags f reduction ih =>
    cases turn with
    | arg turn =>
      rcases origin.uncons with ⟨equal,outside⟩ | ⟨inside,old,atP,atQ,childOrigin⟩
      · subst q
        exact context_image (.appR reduction) outside oldTag
      · subst p;subst q
        have childTag : old∈tracePositions name a := by simpa [tracePositions] using oldTag
        have childLookup := lookup
        simp only [LTerm.subterm] at childLookup redex
        have child := ih (Marked.app.inj passive).2.2 valid.2.1 turn (Term.app.inj erased).2
          redex childOrigin childLookup childTag
        simpa [tracePositions] using child
  | redL => cases passive
  | redR => cases passive

/-- A real surviving APP occurrence carries each of its SOURCE names through
THIS beta step. The final tag is proved, not a residual input. -/
theorem ReductionAt.trace_node_image
    {m n : Marked} {source target body argument currentFn currentArg : LTerm}
    {site p q name : Path} {beta alpha currentStamp : Labelled.Label}
    (reduction : ReductionAt site m n) (valid : Valid m)
    (turn : Labelled.StepAt site source target) (erased : source.erase=m.erase)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p q)
    (lookup : target.subterm p=some (.app currentStamp currentFn currentArg))
    (oldTag : q∈tracePositions name m) : p∈tracePositions name n := by
  have member : q∈tracePositions name m.passive := by simpa only [passive_trace] using oldTag
  have result := passive_image reduction.passive (passive_idempotent m) (valid_passive valid)
    turn (erased.trans (passive_erase m).symm) redex origin lookup member
  simpa only [passive_trace] using result

#print axioms ReductionAt.trace_node_image
end Lamping.Lambda.Marked

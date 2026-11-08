import Lamping.Lamping.ExpandedInsertionGeometry
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

/-- A new assignment-indexed refinement of the frozen bare generation.
Every inserted loop has the actual body seam and body-end contexts; the
argument premise is genuinely relabelled to that body-end input. No global
independence, nesting, transparency or soundness conclusion is a field. -/
inductive CoherentExpandedCore (root : B) : List (Endpoint g) → Context → Context → Prop
  | base {es input output} (labels : Labelling g es input output) (forward : Forward g es)
      (rooted : es.head?=some (.inr (.inl root))) : CoherentExpandedCore root es input output
  | insert (r : BetaEdge g) (pre loop suffix : List (Endpoint g))
      {input argumentInput seam endBody output : Context}
      (argument : CoherentExpandedCore root (pre++r.argEnd::suffix) argumentInput output)
      (body : CoherentExpandedCore root (pre++r.principal++loop) input endBody)
      (bodyPrefix : ExpandedLabelling g pre input seam)
      (argumentPrefix : ExpandedLabelling g pre argumentInput endBody)
      (preEnd : pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩)))
      (loopStart : loop.head?=some (.inl ⟨r.lam,r.lamBody⟩))
      (loopEnd : loop.getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩)))
      (binding : BindingLoop g loop seam endBody) (sameBinder : binding.binder=r.lam) :
      CoherentExpandedCore root
        (pre++r.principal++loop++r.reverseRoute++[r.argEnd]++suffix) input output

 theorem CoherentExpandedCore.erase {root es input output}
     (h : CoherentExpandedCore g root es input output) : ExpandedProperPath g root es := by
  induction h with
  | base labels forward rooted => exact .base ⟨⟨_,_,labels⟩,forward⟩ rooted
  | insert r pre loop suffix argument body bodyPrefix argumentPrefix preEnd loopStart loopEnd binding sameBinder ia ib =>
    exact .insert r pre loop suffix ia ib preEnd loopStart loopEnd _ _ binding sameBinder

/-- Actual labels are derived from the indexed constructors and genuine local
splicing; they are not a target certificate on a completed inserted path. -/
theorem CoherentExpandedCore.labelling {root es input output}
    (h : CoherentExpandedCore g root es input output) : ExpandedLabelling g es input output := by
  induction h with
  | base labels forward rooted => exact labels.expanded
  | insert r pre loop suffix argument body bodyPrefix argumentPrefix preEnd loopStart loopEnd binding sameBinder ia ib =>
    have tail := r.argument_tail_labeling pre suffix argumentPrefix preEnd ia
    exact r.insert_labeling pre loop suffix ib loopEnd tail

 theorem CoherentExpandedCore.rooted {root es input output}
     (h : CoherentExpandedCore g root es input output) : es.head?=some (.inr (.inl root)) :=
   expanded_rooted g (h.erase g)

/-- Nonempty physical prefixes of genuinely coherent core derivations. The
root input is retained. The final context is extracted by the theorem below,
so prefix closure does not postulate labels or arbitrary input existence. -/
def CoherentExpandedPrefix (root : B) (es : List (Endpoint g)) (input : Context) : Prop :=
  es≠[] ∧∃ suffix output,CoherentExpandedCore g root (es++suffix) input output

 theorem CoherentExpandedCore.prefix {root es input output}
     (h : CoherentExpandedCore g root es input output) : CoherentExpandedPrefix g root es input := by
  have nonempty : es≠[] := by intro empty; have start := h.rooted g; rw [empty] at start; cases start
  exact ⟨nonempty,[],output,by simpa only [List.append_nil] using h⟩

 theorem CoherentExpandedPrefix.generated {root es input}
     (h : CoherentExpandedPrefix g root es input) : GeneratedExpandedProperPath g root es := by
  obtain ⟨nonempty,suffix,output,core⟩ := h
  exact .takePrefix ((core.erase g).generated g) nonempty

 theorem CoherentExpandedPrefix.labelling {root es input}
     (h : CoherentExpandedPrefix g root es input) : ∃ output,ExpandedLabelling g es input output := by
  obtain ⟨nonempty,suffix,output,core⟩ := h
  exact (core.labelling g).prefix nonempty

 theorem CoherentExpandedPrefix.takePrefix {root pre tail input}
     (h : CoherentExpandedPrefix g root (pre++tail) input) (nonempty : pre≠[]) :
     CoherentExpandedPrefix g root pre input := by
  obtain ⟨_,suffix,output,core⟩ := h
  exact ⟨nonempty,tail++suffix,output,by simpa only [List.append_assoc] using core⟩
end
end Lamping.AG

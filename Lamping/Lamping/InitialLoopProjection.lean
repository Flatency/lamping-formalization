import Lamping.Lamping.InitialPatchFlow
import Lamping.Lamping.InitialPathProjection
namespace Lamping.AG
open Graph

section Flow
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {bp : B → Bool} {wp : W → Bool}

theorem Labelling.all_outgoing (h : Labelling g es A B') (flow : FlowOn g bp wp)
    (first : ∀ e, es.head?=some e → endPolarity bp wp e=true) :
    ∀ e ∈ es, endPolarity bp wp e=true := by
  induction h with
  | single e A => simpa using first e rfl
  | @cons e f es A C B' turn rest ih =>
    have pe := first e rfl
    have arrival : endPolarity bp wp (g.wire e)=false := by rw [flow e,pe]; rfl
    have pf := (turn.initial_of_polarity arrival).2
    have tail := ih (by intro x hx; cases hx; exact pf)
    intro x hx
    rcases List.mem_cons.mp hx with eq | hx
    · subst x; exact pe
    · exact tail x hx

theorem Labelling.finish_sink (h : Labelling g es A B') (flow : FlowOn g bp wp)
    (start : es.head?=some e) (out : endPolarity bp wp e=true)
    (finish : es.getLast?=some (g.wire f)) : endPolarity bp wp f=false := by
  have all := h.all_outgoing flow (by intro x hx; rw [start] at hx; cases hx; exact out)
  have last := all (g.wire f) (List.mem_of_getLast? finish)
  rw [flow f] at last
  cases hp : endPolarity bp wp f <;> simp_all
end Flow

section Plug
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
variable {bp : B → Bool} {fp : F → Bool} {wp : W → Bool} {vp : V → Bool}

private theorem last_append_cons {T : Type} (xs : List T) (x : T) (tail : List T) :
    (xs++x::tail).getLast?=(x::tail).getLast? := by
  rw [List.getLast?_append]
  cases h : (x::tail).getLast? with
  | none => have impossible := List.getLast?_eq_none_iff.mp h; cases impossible
  | some y => simp

theorem plug_sides_ne (x : Endpoint c) (y : Endpoint r) :
    AG.plugLeft c r x ≠ AG.plugRight c r y := by
  intro eq
  have hh := (plugEnd c.label r.label).injective eq
  cases hh

/-- Once a child path has exited at an FV boundary, its continuation cannot
reenter a child if the actual surrounding patch has no FV-to-root path.
The input is a property of the source patch, not the desired no-escape result. -/
theorem Labelling.patch_exit_stays_left
    (flow : FlowOn c (Sum.elim bp (fun z => !(fp z))) wp)
    (noReturn : ∀ (z z' : F) (A B' : Context), fp z=false → fp z'=true →
      LocalPath c (.inr z) (.inr z') A B' → False)
    {z : F} {tail : List (Endpoint (plug c r))} {A B' : Context}
    (hz : fp z=false)
    (h : Labelling (plug c r) (AG.plugLeft c r (.inr (.inl (.inr z)))::tail) A B') :
    ∃ xs : List (Endpoint c), tail=xs.map (AG.plugLeft c r) ∧
      Labelling c (.inr (.inl (.inr z))::xs) A B' := by
  rcases h.plugLeft_first c r with stay | ⟨xs,z',rest,mid,eq,labels,finish,last⟩
  · exact stay
  · have source : endPolarity (Sum.elim bp (fun z => !(fp z))) wp
        (.inr (.inl (.inr z)) : Endpoint c)=true := by simp [endPolarity,hz]
    have sink := labels.finish_sink flow rfl source finish
    have back : fp z'=true := by
      change (!(fp z'))=false at sink
      cases hx : fp z' <;> simp_all
    exact False.elim (noReturn z z' A mid hz back ⟨_,rfl,finish,labels⟩)

/-- A path with both endpoints in an encoded child cannot leave and return
through the surrounding patch. The patch's FV/root separation and actual
wire polarity imply this; no loop-shell or no-escape certificate is input. -/
theorem Labelling.child_no_escape
    (cflow : FlowOn c (Sum.elim bp (fun z => !(fp z))) wp)
    (rflow : FlowOn r fp vp)
    (noReturn : ∀ (z z' : F) (A B' : Context), fp z=false → fp z'=true →
      LocalPath c (.inr z) (.inr z') A B' → False)
    {x y : Endpoint r} {tail : List (Endpoint (plug c r))} {A B' : Context}
    (out : endPolarity fp vp x=true)
    (h : Labelling (plug c r) (AG.plugRight c r x::tail) A B')
    (finish : (AG.plugRight c r x::tail).getLast?=some (AG.plugRight c r y)) :
    ∃ xs : List (Endpoint r), tail=xs.map (AG.plugRight c r) ∧ Labelling r (x::xs) A B' := by
  rcases h.plugRight_first c r with stay | ⟨xs,z,rest,mid,eq,labels,exit,remaining⟩
  · exact stay
  · have hz : fp z=false := labels.finish_sink rflow rfl out exit
    obtain ⟨ys,restEq,leftLabels⟩ := remaining.patch_exit_stays_left c r cflow noReturn hz
    have wholeEq : AG.plugRight c r x::tail =
        (AG.plugRight c r x::xs.map (AG.plugRight c r)) ++
          AG.plugLeft c r (.inr (.inl (.inr z)))::rest := by rw [eq]; rfl
    rw [wholeEq,last_append_cons] at finish
    have suffixEq : AG.plugLeft c r (.inr (.inl (.inr z)))::rest =
        (.inr (.inl (.inr z))::ys).map (AG.plugLeft c r) := by rw [restEq]; rfl
    rw [suffixEq,List.getLast?_map] at finish
    cases last : (.inr (.inl (.inr z))::ys).getLast? with
    | none => simp [last] at finish
    | some e =>
      simp only [last,Option.map_some,Option.some.injEq] at finish
      exact False.elim (plug_sides_ne c r e y finish)

/-- An outer-to-outer path either stays in its patch or visits a child once:
actual patch prefix, actual child LocalPath, actual patch suffix. FV/root
separation rules out additional excursions; the three contexts are retained. -/
theorem Labelling.outer_child_decompose
    (cflow : FlowOn c (Sum.elim bp (fun z => !(fp z))) wp)
    (rflow : FlowOn r fp vp)
    (noReturn : ∀ (z z' : F) (A B' : Context), fp z=false → fp z'=true →
      LocalPath c (.inr z) (.inr z') A B' → False)
    {x y : Endpoint c} {tail : List (Endpoint (plug c r))} {A B' : Context}
    (out : endPolarity (Sum.elim bp (fun z => !(fp z))) wp x=true)
    (h : Labelling (plug c r) (AG.plugLeft c r x::tail) A B')
    (finish : (AG.plugLeft c r x::tail).getLast?=some (AG.plugLeft c r y)) :
    (∃ xs : List (Endpoint c), tail=xs.map (AG.plugLeft c r) ∧ Labelling c (x::xs) A B') ∨
    ∃ (xs : List (Endpoint c)) (z z' : F) (mid last : Context)
      (p : LocalPath r z z' mid last) (ys : List (Endpoint c)),
      fp z=true ∧ fp z'=false ∧
      tail=xs.map (AG.plugLeft c r) ++ p.edges.map (AG.plugRight c r) ++
        (.inr (.inl (.inr z'))::ys).map (AG.plugLeft c r) ∧
      Labelling c (x::xs) A mid ∧
      (x::xs).getLast?=some (c.wire (.inr (.inl (.inr z)))) ∧
      Labelling c (.inr (.inl (.inr z'))::ys) last B' := by
  rcases h.plugLeft_first c r with stay | ⟨xs,z,rest,mid,eq,leading,entry,remaining⟩
  · exact Or.inl stay
  · have sink := leading.finish_sink cflow rfl out entry
    have hz : fp z=true := by
      change (!(fp z))=false at sink
      cases e : fp z <;> simp_all
    have wholeEq : AG.plugLeft c r x::tail =
        (AG.plugLeft c r x::xs.map (AG.plugLeft c r)) ++ AG.plugRight c r (.inr (.inl z))::rest := by
      rw [eq]; rfl
    rw [wholeEq,last_append_cons] at finish
    rcases remaining.plugRight_first c r with ⟨zs,rightEq,rightLabels⟩ |
        ⟨zs,z',lastRest,last,rightEq,middle,exit,remainingLeft⟩
    · have suffixEq : AG.plugRight c r (.inr (.inl z))::rest =
          (.inr (.inl z)::zs).map (AG.plugRight c r) := by rw [rightEq]; rfl
      rw [suffixEq,List.getLast?_map] at finish
      cases endEq : (.inr (.inl z)::zs).getLast? with
      | none => simp [endEq] at finish
      | some e =>
        simp only [endEq,Option.map_some,Option.some.injEq] at finish
        exact False.elim (plug_sides_ne c r y e finish.symm)
    · have hout : endPolarity fp vp (.inr (.inl z) : Endpoint r)=true := hz
      have hz' : fp z'=false := middle.finish_sink rflow rfl hout exit
      obtain ⟨ys,leftEq,leftLabels⟩ := remainingLeft.patch_exit_stays_left c r cflow noReturn hz'
      refine Or.inr ⟨xs,z,z',mid,last,⟨.inr (.inl z)::zs,rfl,exit,middle⟩,
        ys,hz,hz',?_,leading,entry,leftLabels⟩
      simp only [eq,rightEq,leftEq,List.map_cons,List.append_assoc,List.cons_append]
end Plug
end Lamping.AG


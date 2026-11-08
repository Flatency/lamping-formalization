import Lamping.Lambda.LabelContextualImageCollisions
namespace Lamping.Lambda.Labelled
namespace LTerm

/-- Every original lambda retains its constructor and label at the same
syntax path under real capture-avoiding substitution. -/
theorem subst_lambda_lookup {t body : LTerm} {p : Path} {nodeLabel : Label} (old : t.subterm p=some (.lam nodeLabel body)) (sigma : Nat → SubValue) :
    ∃ current,(t.subst sigma).subterm p=some (.lam nodeLabel current) := by
  induction p generalizing t sigma with
  | nil =>
    have equal : t=.lam nodeLabel body := by simpa only [subterm,Option.some.injEq] using old
    subst t
    exact ⟨body.subst (lift sigma),by simp [subst,subterm]⟩
  | cons edge rest ih =>
    cases t with
    | var => cases edge <;> simp [subterm] at old
    | lam l b =>
      cases edge with
      | fn => simp [subterm] at old
      | arg => simp [subterm] at old
      | body => exact ih old (lift sigma)
    | app l fn arg =>
      cases edge with
      | body => simp [subterm] at old
      | fn => exact ih old sigma
      | arg => exact ih old sigma

/-- A real argument-insertion variable strictly under this body edge has
an actual old lambda at that same ancestor position. -/
theorem argument_occurrence_ancestor_lambda {body : LTerm}
    (occurs : ArgumentOccurrence body.erase site) (strict : site=before++(.body::suffix)) :
    ∃ label old,body.subterm before=some (.lam label old) := by
  change subtermAt body.erase site=some (.var (binderDepth site)) at occurs
  rw [strict,subtermAt_append,←erase_subterm] at occurs
  cases lookup : body.subterm before with
  | none => simp [lookup] at occurs
  | some old =>
    cases old with
    | var l i => simp [lookup,erase,subtermAt] at occurs
    | app l fn arg => simp [lookup,erase,subtermAt] at occurs
    | lam l b => exact ⟨l,b,rfl⟩

/-- A lambda outside an actual inserted argument copy is a retained body
lambda. The incoming contract prefix may change its full label at the root,
but its last atomic origin is exactly the old body's, never a captured arg node. -/
theorem contract_copy_ancestor_origin {body argument : LTerm}
    {nodeLabel : Label} (occurs : ArgumentOccurrence body.erase site) (strict : site=before++(.body::suffix))
    (lookup : (contract beta alpha body argument).subterm before=some (.lam nodeLabel current)) :
    ∃ oldLabel oldBody,body.subterm before=some (.lam oldLabel oldBody) ∧ nodeLabel.lastAtom=oldLabel.lastAtom := by
  obtain ⟨oldLabel,oldBody,oldLookup⟩ := argument_occurrence_ancestor_lambda occurs strict
  obtain ⟨substitutedBody,substitutedLookup⟩ := subst_lambda_lookup oldLookup (single (argument.prepend alpha.under))
  by_cases root : before=[]
  · subst before
    have substitutedEq : body.subst (single (argument.prepend alpha.under))=.lam oldLabel substitutedBody := by
      simpa only [subterm,Option.some.injEq] using substitutedLookup
    have labels : nodeLabel=(beta.concat alpha.over).concat oldLabel := by
      have equal : LTerm.lam ((beta.concat alpha.over).concat oldLabel) substitutedBody=LTerm.lam nodeLabel current := by
        rw [contract,substitutedEq] at lookup
        exact Option.some.inj lookup
      exact (LTerm.lam.inj equal).1.symm
    exact ⟨oldLabel,oldBody,oldLookup,by rw [labels,Label.lastAtom_concat]⟩
  · rw [contract,prepend_subterm_nonempty _ _ root] at lookup
    have labels := (LTerm.lam.inj (Option.some.inj (lookup.symm.trans substitutedLookup))).1
    exact ⟨oldLabel,oldBody,oldLookup,congrArg Label.lastAtom labels⟩

/-- With the real original INIT source, that retained binder origin is
provably outside the original argument's node set. -/
theorem contract_copy_ancestor_origin_outside {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    {nodeLabel : Label} (occurs : ArgumentOccurrence body.erase site) (strict : site=before++(.body::suffix))
    (lookup : (contract beta alpha body argument).subterm before=some (.lam nodeLabel current)) :
    ∃ n,nodeLabel.lastAtom=some n ∧ Label.atom n∈body.labels ∧ Label.atom n∉argument.labels := by
  obtain ⟨oldLabel,oldBody,oldLookup,last⟩ := contract_copy_ancestor_origin occurs strict lookup
  have bodyInitial : INIT body := initial.subterm (p := [.fn,.body]) (by simp [subterm])
  have member : oldLabel∈body.labels := label_mem_of_subterm oldLookup
  obtain ⟨n,atomic⟩ := bodyInitial.1 oldLabel member
  have absent : oldLabel∉argument.labels := by
    intro other
    exact (List.nodup_append.mp (List.nodup_cons.mp initial.2).2).2.2 _ (List.mem_cons_of_mem _ member) _ other rfl
  refine ⟨n,?_,atomic ▸ member,atomic ▸ absent⟩
  rw [last,atomic]
  rfl
end LTerm
end Lamping.Lambda.Labelled




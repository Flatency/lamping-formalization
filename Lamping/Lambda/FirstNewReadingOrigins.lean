import Lamping.Lambda.BetaIncomingEdgeOrigins
import Lamping.Lambda.CopiedLambdaBodies
import Lamping.Lambda.PrerequisitePrefixes
namespace Lamping.Lambda.Labelled
/-- Actual first bar read at a newly formed incoming edge, with its two
old neighboring edges. FUNCTION is read forward, lambda context backward. -/
inductive BetaIncomingReadingOrigin (body argument : LTerm) (site edge middle : Path) :
    Path → Path → Path → Prop where
  | resultFunction (result : edge=site) (function : site=middle++[.fn]) :
      BetaIncomingReadingOrigin body argument site edge middle middle site (site++[.fn,.body])
  | resultLambda (result : edge=site) (reading : middle=site)
      (oldLambda : body=.lam stamp inner) :
      BetaIncomingReadingOrigin body argument site edge middle
        (site++[.fn,.body]) (site++[.fn,.body]) site
  | copyFunction (occurs : ArgumentOccurrence body.erase (parent++[.fn]))
      (copy : edge=site++(parent++[.fn])) (reading : middle=site++parent) :
      BetaIncomingReadingOrigin body argument site edge middle
        ((site++[.fn,.body])++parent) ((site++[.fn,.body])++(parent++[.fn])) (site++[.arg])
  | copyLambda (occurs : ArgumentOccurrence body.erase q)
      (copy : edge=site++q) (reading : middle=edge)
      (oldLambda : argument=.lam stamp inner) :
      BetaIncomingReadingOrigin body argument site edge middle
        (site++[.arg]) (site++[.arg]) ((site++[.fn,.body])++q)

private theorem same_last_step {left right : Path} {s u : Step}
    (equal : left++[s]=right++[u]) : left=right ∧s=u := by
  have reversed := congrArg List.reverse equal
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] at reversed
  have parts := List.cons.inj reversed
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse parts.2,parts.1⟩
private theorem unsnoc_path (p : Path) (nonempty : p≠[]) : ∃ before last,p=before++[last] := by
  induction p with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail ih =>
    cases tail with
    | nil => exact ⟨[],head,rfl⟩
    | cons next rest =>
      obtain ⟨before,last,equal⟩ := ih (by simp)
      exact ⟨head::before,last,congrArg (head::·) equal⟩

theorem BetaIncomingReadingOrigin.old_prerequisite
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge middle oldStart first last) :
    PrerequisiteChain source oldStart [first,site++[.fn]] ∧
      ∃ oldLast,source.subterm last=some oldLast := by
  cases origin with
  | resultFunction result function =>
    refine ⟨?_,body,?_⟩
    · rw [function] at redex ⊢
      exact result_function_old_chain redex
    · rw [LTerm.subterm_append,redex]; cases body <;> rfl
  | resultLambda result reading oldLambda =>
    subst body
    exact ⟨result_lambda_prerequisite redex,_,redex⟩
  | copyFunction occurs copy reading =>
    refine ⟨?_,argument,?_⟩
    · simpa only [List.append_assoc] using substituted_function_old_chain redex occurs
    · rw [LTerm.subterm_append,redex]; cases argument <;> rfl
  | copyLambda occurs copy reading oldLambda =>
    subst argument
    refine ⟨copied_lambda_prerequisite redex,?_⟩
    change subtermAt body.erase _=some (.var _) at occurs
    rw [←LTerm.erase_subterm] at occurs
    cases oldLookup : body.subterm _ with
    | none => rw [oldLookup] at occurs; cases occurs
    | some old =>
      exact ⟨old,by rw [List.append_assoc,LTerm.subterm_append,redex]; simpa only [LTerm.subterm,Option.bind_some] using oldLookup⟩

theorem StepAt.created_reading_origin
    {source target body argument : LTerm} {site edge middle : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (reads : PrerequisiteReads target middle edge)
    (created : edge=site ∨∃q,ArgumentOccurrence body.erase q ∧edge=site++q) :
    ∃ oldStart first last,BetaIncomingReadingOrigin body argument site edge middle oldStart first last := by
  rcases reads with ⟨stamp,fn,arg,lookup,edgeEq⟩ | ⟨stamp,inner,lookup,edgeEq⟩
  · rcases created with result | ⟨q,occurs,copyEq⟩
    · exact ⟨_,_,_,.resultFunction result (result.symm.trans edgeEq)⟩
    · by_cases empty : q=[]
      · have result : edge=site := by simpa only [empty,List.append_nil] using copyEq
        exact ⟨_,_,_,.resultFunction result (result.symm.trans edgeEq)⟩
      · obtain ⟨parent,last,split⟩ := unsnoc_path q empty
        have lastEq : (site++parent)++[last]=middle++[.fn] := by
          simpa only [split,List.append_assoc] using copyEq.symm.trans edgeEq
        obtain ⟨parentEq,childEq⟩ := same_last_step lastEq
        have atFunction : ArgumentOccurrence body.erase (parent++[.fn]) := by
          simpa only [split,childEq] using occurs
        exact ⟨_,_,_,.copyFunction atFunction (by simpa only [split,childEq] using copyEq) parentEq.symm⟩
  · rw [←edgeEq] at lookup
    rcases created with result | ⟨q,occurs,copyEq⟩
    · have shape : LTerm.contract beta alpha body argument=.lam stamp inner :=
        Option.some.inj ((step.contract_lookup redex).symm.trans (result ▸ lookup))
      rcases LTerm.contract_root_lambda_origin shape with ⟨oldStamp,oldBody,oldShape,_⟩ |
          ⟨variableStamp,argumentStamp,argumentBody,bodyEq,argEq,_⟩
      · exact ⟨_,_,_,.resultLambda result (edgeEq.symm.trans result) oldShape⟩
      · have occurs : ArgumentOccurrence body.erase [] := by rw [bodyEq]; rfl
        exact ⟨_,_,_,.copyLambda occurs (by simpa only [List.append_nil] using result) edgeEq.symm argEq⟩
    · have current : (LTerm.contract beta alpha body argument).subterm (q++[])=some (.lam stamp inner) := by
        rw [copyEq,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
        simpa only [List.append_nil] using lookup
      obtain ⟨oldStamp,oldBody,oldLookup,_⟩ := LTerm.contract_copied_lambda_origin occurs current
      have argEq : argument=.lam oldStamp oldBody := by simpa only [LTerm.subterm,Option.some.injEq] using oldLookup
      exact ⟨_,_,_,.copyLambda occurs copyEq edgeEq.symm argEq⟩

/-- Actual chain membership supplies the reading occurrence and prefix.
Only the newly-created incoming-edge position is specified, not any old
chain or any chain at the other old endpoint. -/
theorem StepAt.created_chain_reading_origins
    {source target body argument : LTerm} {site edge start : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (chain : PrerequisiteChain target start edges) (member : edge∈edges)
    (created : edge=site ∨∃q,ArgumentOccurrence body.erase q ∧edge=site++q) :
    ∃ before after middle oldStart first last,
      edges=before++(edge::after) ∧PrerequisitePrefix target start before middle ∧
      PrerequisiteChain target middle (edge::after) ∧
      BetaIncomingReadingOrigin body argument site edge middle oldStart first last ∧
      PrerequisiteChain source oldStart [first,site++[.fn]] ∧
      ∃ oldLast,source.subterm last=some oldLast := by
  obtain ⟨before,after,middle,equal,segment,remainder,reads⟩ := chain.split_at_member member
  obtain ⟨oldStart,first,last,origin⟩ := step.created_reading_origin redex reads created
  obtain ⟨oldChain,oldLast⟩ := origin.old_prerequisite redex
  exact ⟨before,after,middle,oldStart,first,last,equal,segment,remainder,origin,oldChain,oldLast⟩
end Lamping.Lambda.Labelled


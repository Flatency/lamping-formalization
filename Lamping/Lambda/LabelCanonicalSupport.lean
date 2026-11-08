import Lamping.Lambda.LabelSilentHeadProjection
import Lamping.Lambda.ArgumentRunContexts
namespace Lamping.Lambda.Labelled

/-- Relabel a true coloured history with the exact preimage predicate. -/
theorem RegionalHistory.relabel (s : Nat → Label) (region : Nat → Prop)
    (regional : RegionalHistory (fun n => (s n).Supported region) ps t u) :
    RegionalHistory region ps (t.relabel s) (u.relabel s) := by
  induction regional with
  | nil => exact .nil _
  | cons step degree support rest ih =>
    refine .cons (step.relabel s) ?_ ((Label.supported_relabel s region _).mpr support) ih
    rw [LTerm.degreeAt_relabel,degree]
    rfl

private theorem canonical_cast_source (equal : source=target) (run : ExtractionRun source) :
    CanonicalRun (run.castSource equal) ↔ CanonicalRun run := by cases equal; rfl

private def CanonicalSupportAt (n : Nat) : Prop :=
  ∀ {t u v : LTerm} {ps : List Path} {q : Path} {l : Label} {region : Nat → Prop},
    History ps t u → StepAt q u v → INIT t → (run : ExtractionRun t.erase) → CanonicalRun run →
    run.history.derivation.paths=ps++[q] → u.degreeAt q=some l → l.Supported region → ps.length+1=n →
    RegionalHistory region (ps++[q]) t v

/-- The only recursion hypothesis is the strictly shorter actual pointed
length. It is discharged here, never exported as a semantic certificate. -/
private theorem canonical_support_all : ∀ n,CanonicalSupportAt n := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t u v ps q l region prefixHistory last initial run canonical paths degree support count
    cases prefixHistory with
    | nil t => exact .cons last degree support (.nil _)
    | @cons headSite source middle restPaths current head rest =>
      have globalTail : History (restPaths++[q]) middle v := rest.append (.cons last (.nil _))
      obtain ⟨tail,tailAtomic,tailPaths⟩ := globalTail.betaHistory.atomic
      have runEq : run=ExtractionRun.of (.cons (singleContraction head.betaAt) tail) (.cons head.betaAt tailAtomic) := by
        apply ExtractionRun.ext_paths
        change run.history.derivation.paths=headSite::tail.derivation.paths
        rw [paths,tailPaths]
        rfl
      rw [runEq] at canonical
      have tailPositive : 0<tail.length := by
        have lengths := congrArg List.length tailPaths
        rw [tailAtomic.paths_length,List.length_append] at lengths
        simp only [List.length_cons,List.length_nil] at lengths
        omega
      let tailRun : ExtractionRun middle.erase := .of tail tailAtomic
      have tailCanonical : CanonicalRun tailRun := by
        refine ⟨tailPositive,?_,?_⟩
        · exact canonical.2.1.suffix (ρ := .single (singleContraction head.betaAt)) (σ := tail)
        · exact ExtractionNormal.of_prepend (r := tailRun)
            (pre := .single (singleContraction head.betaAt)) (ha := .single head.betaAt) canonical.2.2
      obtain ⟨basisCurrent,basisRest,erasedCurrent,_⟩ := rest.local_initial_basis
      obtain ⟨basisTarget,basisLast,_⟩ := lift_betaAt (t := basisCurrent) (by rw [erasedCurrent]; exact last.betaAt)
      obtain ⟨basisLabel,basisDegree⟩ := degreeAt_exists basisCurrent ⟨q,basisLast.betaAt.redex⟩
      have transported := rest.local_degree_transport basisRest basisDegree
      have labelEq : basisLabel.relabel (initialRelabelling middle 0)=l :=
        Option.some.inj (transported.1.symm.trans degree)
      let basisRun : ExtractionRun (initLabels middle.erase).erase :=
        tailRun.castSource (erase_initLabels middle.erase).symm
      have basisCanonical : CanonicalRun basisRun :=
        (canonical_cast_source (erase_initLabels middle.erase).symm tailRun).mpr tailCanonical
      have basisPaths : basisRun.history.derivation.paths=restPaths++[q] := by
        rw [ExtractionRun.castSource_paths]
        exact tailPaths
      have shorter : restPaths.length+1<n := by
        simp only [List.length_cons] at count
        omega
      have basisColours : ∀ colour,basisLabel.Supported colour →
          RegionalHistory colour (restPaths++[q]) (initLabels middle.erase) basisTarget := by
        intro colour coloured
        exact ih (restPaths.length+1) shorter basisRest basisLast (init_is_INIT middle.erase)
          basisRun basisCanonical basisPaths basisDegree coloured rfl
      have tailColours : ∀ colour,l.Supported colour → RegionalHistory colour (restPaths++[q]) middle v := by
        intro colour coloured
        have localSupport := (Label.supported_relabel (initialRelabelling middle 0) colour basisLabel).mp
          (labelEq.symm ▸ coloured)
        have changed := (basisColours _ localSupport).relabel (initialRelabelling middle 0) colour
        rw [show (initLabels middle.erase).relabel (initialRelabelling middle 0)=middle from initialRelabelling_factor middle 0] at changed
        have endpoint := changed.history.deterministic globalTail
        rw [endpoint] at changed
        exact changed
      obtain ⟨beta,alpha,body,argument,sourceAt,_⟩ := head.head_lookups
      have headDegree : t.degreeAt headSite=some alpha := by
        simp only [LTerm.degreeAt,sourceAt,Option.bind_some,LTerm.degree]
      obtain ⟨headBody,atLambda⟩ := LTerm.degreeAt_lambda headDegree
      obtain ⟨a,atomic⟩ := initial.1 alpha (LTerm.label_mem_of_subterm atLambda)
      cases atomic
      have firstSupport : (Label.atom a).Supported region := by
        by_cases supportedHead : region a
        · exact supportedHead
        · have finalAvoid : l.Supported (fun n => n≠a) := support.mono (fun n member equal => by
            cases equal
            exact supportedHead member)
          have avoidingTail := tailColours _ finalAvoid
          have wholeInside := avoidingTail.normal_head_internal head initial headDegree tail tailAtomic
            canonical.2.1 tailPaths (by simp) canonical.2.2
          have prefixInside : ∀ site∈headSite::restPaths,∃ suffix,site=headSite++suffix := by
            intro site member
            apply wholeInside site
            change site∈headSite::tail.derivation.paths
            rw [tailPaths]
            rcases List.mem_cons.mp member with first | earlier
            · exact first ▸ List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_append_left _ earlier)
          obtain ⟨localCurrent,atCurrent,localPrefix⟩ :=
            (History.cons head rest).subterm_internal sourceAt prefixInside
          have lastInside : ∃ suffix,q=headSite++suffix := by
            apply wholeInside q
            change q∈headSite::tail.derivation.paths
            rw [tailPaths]
            exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
          obtain ⟨localSite,atLast⟩ := lastInside
          have localDegree : localCurrent.degreeAt localSite=some l := by
            have globalAt : u.degreeAt (headSite++localSite)=some l := atLast ▸ degree
            simpa only [LTerm.degreeAt,LTerm.subterm_append,atCurrent,Option.bind_some] using globalAt
          have headInitial := initial.subterm sourceAt
          have split := localPrefix.root_head_degree_strict_region headInitial
            (region := fun n => n≠a) (by intro bad; exact bad rfl) localDegree finalAvoid
          rcases split with ⟨inBody,_⟩ | ⟨inArgument,strictArgument⟩
          · have colouredBody := tailColours _ inBody
            have tailInside : ∀ site∈restPaths++[q],∃ suffix,site=headSite++suffix := by
              intro site member
              exact wholeInside site (by change site∈headSite::tail.derivation.paths; rw [tailPaths]; exact List.mem_cons_of_mem _ member)
            exact False.elim ((colouredBody.contextual_body_not_normal head initial sourceAt tailInside tail tailAtomic
              tailPaths (by simp)) canonical.2.2)
          · have avoidArgument : l.Supported (fun n => Label.atom n≠argument.label) :=
              (Label.supported_iff_within _ _).mpr strictArgument
            obtain ⟨occurrence,env,ctx,copy,occurs,atCopy,copySupport,copyStrict⟩ :=
              head.argument_subregion_degree initial sourceAt (regionSite := [])
                (regionTerm := argument) (by simp [LTerm.subterm]) rest basisRest degree basisDegree inArgument avoidArgument
            have strictSupport : basisLabel.Supported (fun n => SourceRegion copy n ∧ Label.atom n≠copy.label) :=
              (Label.supported_iff_within _ _).mpr (fun e member =>
                ⟨(Label.supported_iff_within _ _).mp copySupport e member,copyStrict e member⟩)
            have colouredCopy := basisColours _ strictSupport
            have copyInside := colouredCopy.internal_of_strict_region (init_is_INIT middle.erase) atCopy.lookup
            have actualInside : Internal (headSite++occurrence) tail := by
              intro site member
              have inside := copyInside site (tailPaths ▸ member)
              simpa only [List.append_nil] using inside
            have sourceErase : subtermAt t.erase headSite=some (.app (.lam body.erase) argument.erase) := by
              rw [←LTerm.erase_subterm,sourceAt]
              rfl
            exact False.elim ((normal_head_not_argument_copy head.betaAt sourceErase occurs tail tailAtomic tailPositive
              canonical.2.2) actualInside)
      exact .cons head headDegree firstSupport (tailColours _ support)

/-- In any actual canonical pointed history from an arbitrary INIT labelling,
every fired degree is supported by every atom predicate supporting the final
degree. Local INIT coordinates in the proof are always transported back. -/
theorem History.canonical_degree_support (prefixHistory : History ps t u) (last : StepAt q u v)
    (initial : INIT t) (run : ExtractionRun t.erase) (canonical : CanonicalRun run)
    (paths : run.history.derivation.paths=ps++[q]) (degree : u.degreeAt q=some l)
    (support : l.Supported region) : RegionalHistory region (ps++[q]) t v :=
  canonical_support_all (ps.length+1) prefixHistory last initial run canonical paths degree support rfl
end Lamping.Lambda.Labelled



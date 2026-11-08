import Lamping.Lamping.OriginalRootFold
import Lamping.Lamping.LocalBetaSelectorResidual
import Lamping.Lamping.LocalOuterSignedEvaluation
import Lamping.Lamping.MatchingSelectedDegreeRealization
import Lamping.Lambda.LabelPathInjective

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem lookup_of_label_member {t : LTerm} {label : Label}
    (member : label∈t.labels) : ∃p node,t.subterm p=some node ∧node.label=label := by
  induction t with
  | var stamp index =>
    have eq := List.mem_singleton.mp member
    exact ⟨[],.var stamp index,rfl,eq.symm⟩
  | lam stamp body ih =>
    rcases List.mem_cons.mp member with eq | inside
    · exact ⟨[],.lam stamp body,rfl,eq.symm⟩
    · obtain ⟨p,node,atNode,same⟩ := ih inside
      exact ⟨.body::p,node,atNode,same⟩
  | app stamp fn arg hf ha =>
    rcases List.mem_cons.mp member with eq | inside
    · exact ⟨[],.app stamp fn arg,rfl,eq.symm⟩
    · rcases List.mem_append.mp inside with left | right
      · obtain ⟨p,node,atNode,same⟩ := hf left
        exact ⟨.fn::p,node,atNode,same⟩
      · obtain ⟨p,node,atNode,same⟩ := ha right
        exact ⟨.arg::p,node,atNode,same⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {source : LTerm}

theorem supported_basis_atom_fold
    (closed : Closed source.erase) (matching : Matches g root source.erase)
    (weights : Endpoint g → EdgeWord) (oldIH : OriginalRootFold g root source weights)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    {n : Nat} (supported : Label.atom n∈(initLabels source.erase).labels) :
    physicalOriginalWord weights (selection.atomWord n)=
      (initialRelabelling source 0 n).edgeWord := by
  obtain ⟨p,node,lookup,atomic⟩ := lookup_of_label_member supported
  obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup (initLabels source.erase) lookup [] .external
  let h := initialRelabelling source 0
  have factor : (initLabels source.erase).relabel h=source := initialRelabelling_factor source 0
  have atSource := congrArg (fun t : LTerm=>t.subterm p) factor
  change ((initLabels source.erase).relabel h).subterm p=source.subterm p at atSource
  rw [LTerm.subterm_relabel,lookup,Option.map_some] at atSource
  obtain ⟨fragment⟩ := matching.occurrence_fragment_at closed atSource.symm
  have localMatching : Matches g root (initLabels source.erase).erase := by
    simpa only [erase_initLabels] using matching
  have atomWord := selection.atomWord_occurrence_segments (init_is_INIT _) localMatching matching
    occurrence atomic fragment
  have sameNode := Option.some.inj (fragment.occurrence.lookup.symm.trans atSource.symm)
  have labels : fragment.term.label=h n := by
    rw [sameNode]
    have lab : (node.relabel h).label=node.label.relabel h := by cases node <;> rfl
    rw [lab,atomic,Label.relabel_atom]
  rw [atomWord,fragment.original_word_of_root_fold matching weights oldIH,labels]
end
end Lamping.AG

namespace Lamping.Lambda.Labelled.LTerm

private theorem label_sourceWord_flatMap {X Y : Type}
    (atoms : Nat→List X) (overWord underWord : List X) (f : X→List Y) :
    ∀label : Label,(label.sourceWord atoms overWord underWord).flatMap f=
      label.sourceWord (fun n=>(atoms n).flatMap f) (overWord.flatMap f) (underWord.flatMap f)
  | .single letter => by cases letter <;> rfl
  | .cons letter rest => by cases letter <;>
      simp only [Label.sourceWord,Letter.sourceWord,List.flatMap_append,label_sourceWord_flatMap atoms overWord underWord f rest]

theorem sourceTrail_flatMap {X Y : Type}
    (atoms : Nat→List X) (overWord underWord : List X)
    (f : X→List Y) (term : LTerm) (p : Path) :
    (term.sourceTrail atoms overWord underWord p).map (fun xs=>xs.flatMap f)=
      term.sourceTrail (fun n=>(atoms n).flatMap f)
        (overWord.flatMap f) (underWord.flatMap f) p := by
  induction p generalizing term with
  | nil => cases term <;> simp only [sourceTrail,Option.map_some,label_sourceWord_flatMap]
  | cons step rest ih =>
    cases term <;> cases step <;>
      simp only [sourceTrail,Option.map_none,Option.map_map,Function.comp_def,List.flatMap_append,
        label_sourceWord_flatMap,←ih]

private theorem label_sourceWord_supported_congr {X : Type}
    {region : Nat→Prop} (left right : Nat→List X) (overWord underWord : List X)
    (onSupport : ∀n,region n→left n=right n) :
    ∀label : Label,label.Supported region →
      label.sourceWord left overWord underWord=label.sourceWord right overWord underWord
  | .single (.atom n),supported => onSupport n supported
  | .single (.over _),_ => rfl
  | .single (.under _),_ => rfl
  | .cons (.atom n) rest,supported => by
      simp only [Label.sourceWord,Letter.sourceWord,onSupport n supported.1,
        label_sourceWord_supported_congr left right overWord underWord onSupport rest supported.2]
  | .cons (.over _) rest,supported => by
      simp only [Label.sourceWord,Letter.sourceWord,
        label_sourceWord_supported_congr left right overWord underWord onSupport rest supported.2]
  | .cons (.under _) rest,supported => by
      simp only [Label.sourceWord,Letter.sourceWord,
        label_sourceWord_supported_congr left right overWord underWord onSupport rest supported.2]

theorem sourceTrail_supported_atoms_congr {X : Type}
    {region : Nat→Prop} (term : LTerm) (supported : term.Supported region)
    (left right : Nat→List X) (overWord underWord : List X)
    (onSupport : ∀n,region n→left n=right n) (p : Path) :
    term.sourceTrail left overWord underWord p=term.sourceTrail right overWord underWord p := by
  induction p generalizing term with
  | nil =>
    cases term with
    | var stamp index => exact congrArg some (label_sourceWord_supported_congr left right overWord underWord onSupport stamp supported)
    | lam stamp body => exact congrArg some (label_sourceWord_supported_congr left right overWord underWord onSupport stamp supported.1)
    | app stamp fn arg => exact congrArg some (label_sourceWord_supported_congr left right overWord underWord onSupport stamp supported.1)
  | cons step rest ih =>
    cases term with
    | var => cases step <;> rfl
    | lam stamp body =>
      cases step with
      | fn | arg => rfl
      | body => simp only [sourceTrail,label_sourceWord_supported_congr left right overWord underWord onSupport stamp supported.1,ih _ supported.2]
    | app stamp fn arg =>
      cases step with
      | body => rfl
      | fn => simp only [sourceTrail,label_sourceWord_supported_congr left right overWord underWord onSupport stamp supported.1,ih _ supported.2.1]
      | arg => simp only [sourceTrail,label_sourceWord_supported_congr left right overWord underWord onSupport stamp supported.1,ih _ supported.2.2]
end Lamping.Lambda.Labelled.LTerm

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

theorem given_beta_principal_fold_and_degree
    {root : B} {original source : LTerm} {prior : List Path}
    (initial : INIT original) (prefixHistory : History prior original source)
    (_closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (weights : Endpoint site.net→EdgeWord) (oldIH : OriginalRootFold site.net root source weights)
    (edge : BetaEdge site.net) (geometry : SiteBetaGeometry site edge)
    (nonempty : site.betaSyntaxFiber root source.erase≠[]) :
    ∃alpha : Label,physicalOriginalWord weights edge.principal=alpha.edgeWord ∧
      ∀name∈site.betaSyntaxFiber root source.erase,source.degreeAt name=some alpha := by
  have app : edge.app=.inr (.inl ()) := congrArg Sigma.fst (Sum.inl.inj geometry.appCtx)
  have lam : edge.lam=.inr (.inr ()) := congrArg Sigma.fst (Sum.inl.inj geometry.body)
  have one (name : Path) (member : name∈site.betaSyntaxFiber root source.erase) :
      ∃degree,source.degreeAt name=some degree ∧degree∈source.labels ∧
        physicalOriginalWord weights edge.principal=degree.edgeWord := by
    obtain ⟨redex,access,same,atApp,atLam⟩ :=
      (mem_physicalBetaFiberPaths site.net root source.erase (.inr (.inl ())) (.inr (.inr ())) name).mp member
    obtain ⟨degree,atDegree⟩ := degreeAt_exists source redex
    obtain ⟨appId,body,argument,lookup⟩ := LTerm.degreeAt_redex atDegree
    obtain ⟨fragment,segments⟩ := access.source_function_fragment matching lookup
    obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup source lookup [] .external
    have child := occurrence.append (show SourceSubterm env ctx
      (.app appId (.lam degree body) argument) [.fn] env (.appFn appId) (.lam degree body) from .fn .nil)
    let actual : OccurrenceFragment source site.net root (redex.val++[.fn]) :=
      ⟨.lam degree body,env,.appFn appId,child,fragment⟩
    have principal := access.connection.beta_principal_unique edge (atApp.trans app.symm) (atLam.trans lam.symm)
    have fold := actual.original_word_of_root_fold matching weights oldIH
    have degreeMember : degree∈source.labels := LTerm.label_mem_of_subterm child.lookup
    refine ⟨degree,?_,degreeMember,?_⟩
    · simpa only [same] using atDegree
    · change physicalOriginalWord weights fragment.segments=degree.edgeWord at fold
      rw [segments,principal] at fold
      exact fold
  have chosen : ∃name,name∈site.betaSyntaxFiber root source.erase := by
    cases eq : site.betaSyntaxFiber root source.erase with
    | nil => exact False.elim (nonempty eq)
    | cons name rest => exact ⟨name,List.mem_cons_self⟩
  obtain ⟨name,member⟩ := chosen
  obtain ⟨alpha,atAlpha,alphaMember,principal⟩ := one name member
  refine ⟨alpha,principal,?_⟩
  intro other selected
  obtain ⟨degree,atDegree,degreeMember,otherPrincipal⟩ := one other selected
  have same := prefixHistory.generated_label_path_injective prefixHistory initial degreeMember alphaMember
    (otherPrincipal.symm.trans principal)
  exact atDegree.trans (congrArg some same)
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem sourceTrail_of_label_evaluations
    (atoms : Nat→EdgeWord) (overWord underWord : EdgeWord) (h : Nat→Label)
    (term : LTerm)
    (labels : ∀label∈term.labels,label.sourceWord atoms overWord underWord=(label.relabel h).edgeWord)
    (p : Path) :
    term.sourceTrail atoms overWord underWord p=(term.relabel h).originalIncomingTrail p := by
  induction p generalizing term with
  | nil =>
    cases term with
    | var stamp index => exact congrArg some (labels stamp List.mem_cons_self)
    | lam stamp body => exact congrArg some (labels stamp List.mem_cons_self)
    | app stamp fn arg => exact congrArg some (labels stamp List.mem_cons_self)
  | cons step rest ih =>
    cases term with
    | var => cases step <;> rfl
    | lam stamp body =>
      have head := labels stamp List.mem_cons_self
      have tail : ∀label∈body.labels,label.sourceWord atoms overWord underWord=(label.relabel h).edgeWord :=
        fun label member=>labels label (List.mem_cons_of_mem _ member)
      cases step with
      | fn | arg => rfl
      | body => simp only [LTerm.sourceTrail,LTerm.relabel,LTerm.originalIncomingTrail,head,ih body tail]
    | app stamp fn arg =>
      have head := labels stamp List.mem_cons_self
      have left : ∀label∈fn.labels,label.sourceWord atoms overWord underWord=(label.relabel h).edgeWord :=
        fun label member=>labels label (List.mem_cons_of_mem _ (List.mem_append_left _ member))
      have right : ∀label∈arg.labels,label.sourceWord atoms overWord underWord=(label.relabel h).edgeWord :=
        fun label member=>labels label (List.mem_cons_of_mem _ (List.mem_append_right _ member))
      cases step with
      | body => rfl
      | fn => simp only [LTerm.sourceTrail,LTerm.relabel,LTerm.originalIncomingTrail,head,ih fn left]
      | arg => simp only [LTerm.sourceTrail,LTerm.relabel,LTerm.originalIncomingTrail,head,ih arg right]

private theorem local_cumulative_original_word
    {source target localTarget : LTerm} {F ps : List Path} {endpoint : Marked} {alpha : Label}
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) endpoint)
    (globalHistory : History ps source target)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (selected : ∀name∈F,source.degreeAt name=some alpha) :
    ∀p : Path,localTarget.sourceTrail (fun n=>(initialRelabelling source 0 n).edgeWord)
      alpha.edgeWord (EdgeWord.reverse alpha.edgeWord) p=target.originalIncomingTrail p := by
  let h := initialRelabelling source 0
  have transported := localHistory.relabel h
  have factor : (initLabels source.erase).relabel h=source := initialRelabelling_factor source 0
  rw [factor] at transported
  have sameTarget := transported.deterministic globalHistory
  have labels : ∀label∈localTarget.labels,
      label.sourceWord (fun n=>(h n).edgeWord) alpha.edgeWord (EdgeWord.reverse alpha.edgeWord)=
        (label.relabel h).edgeWord := by
    intro label member
    obtain ⟨p,node,lookup,sameLabel⟩ := lookup_of_label_member member
    obtain ⟨globalNode,globalLookup,evaluation⟩ :=
      old.local_outer_signed_evaluation globalHistory localHistory selected lookup
    have atSame := congrArg (fun t : LTerm=>t.subterm p) sameTarget
    change (localTarget.relabel h).subterm p=target.subterm p at atSame
    rw [LTerm.subterm_relabel,lookup,Option.map_some,globalLookup] at atSame
    have sameNode := Option.some.inj atSame
    have relabelLabel : (node.relabel h).label=node.label.relabel h := by cases node <;> rfl
    have image : globalNode.label=label.relabel h :=
      (congrArg LTerm.label sameNode).symm.trans
        (relabelLabel.trans (congrArg (fun l : Label=>l.relabel h) sameLabel))
    rw [sameLabel,image] at evaluation
    exact evaluation
  intro p
  have result := sourceTrail_of_label_evaluations (fun n=>(h n).edgeWord) alpha.edgeWord
    (EdgeWord.reverse alpha.edgeWord) h localTarget labels p
  rw [sameTarget] at result
  exact result

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

theorem PathSite.beta_original_word_root_access
    {root : B} {original source target : LTerm} {prior ps : List Path} {marked : Marked}
    (initial : INIT original) (prefixHistory : History prior original source)
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (globalHistory : History ps source target)
    (weights : Endpoint site.net→EdgeWord) (reverseLaw : OriginalWordReversal weights)
    (oldIH : OriginalRootFold site.net root source weights) :
    ∃localTarget,∃_localHistory : History ps (initLabels source.erase) localTarget,
      localTarget.erase=target.erase ∧
      ∃edge : BetaEdge site.net,
      ∃_selection : SourceEdgeSelection (initLabels source.erase) site.net root,
        SiteBetaGeometry site edge ∧
        OriginalWordReversal (site.betaOriginalWordWeights edge weights) ∧
        OriginalRootFold site.reduce root target (site.betaOriginalWordWeights edge weights) := by
  obtain ⟨localTarget,localHistory,sameErase,targetMatches,edge,selection,geometry,all⟩ :=
    site.beta_local_selector_residuals closed matching inputs flow positive balance rootDepth transparency
      relative normal globalHistory
  have old := (Marked.relativeOld_iff_relative
    (Marked.selected_mark (site.betaSyntaxFiber root source.erase) source.erase)).mpr relative
  have cumulative : ∀p : Path,
      (localTarget.sourceTrail selection.atomWord edge.principal edge.reverseRoute p).map
        (physicalOriginalWord weights)=target.originalIncomingTrail p := by
    by_cases empty : site.betaSyntaxFiber root source.erase=[]
    · have noSteps : ps=[] := by
        rw [empty] at old
        cases old with
        | nil => rfl
        | cons turn member rest => simp [Marked.setResidualPositions] at member
      cases noSteps
      cases globalHistory
      cases localHistory
      let h := initialRelabelling source 0
      have labels : ∀label∈(initLabels source.erase).labels,
          label.sourceWord (fun n=>physicalOriginalWord weights (selection.atomWord n))
            (physicalOriginalWord weights edge.principal) (physicalOriginalWord weights edge.reverseRoute)=
              (label.relabel h).edgeWord := by
        intro label member
        obtain ⟨n,atomic⟩ := (init_is_INIT source.erase).1 label member
        cases atomic
        exact supported_basis_atom_fold closed matching weights oldIH selection member
      intro p
      change Option.map (fun xs : List (Endpoint site.net)=>xs.flatMap weights) _ = _
      rw [LTerm.sourceTrail_flatMap]
      have result := sourceTrail_of_label_evaluations
        (fun n=>physicalOriginalWord weights (selection.atomWord n))
        (physicalOriginalWord weights edge.principal) (physicalOriginalWord weights edge.reverseRoute)
        h (initLabels source.erase) labels p
      have factor : (initLabels source.erase).relabel h=source := initialRelabelling_factor source 0
      rw [factor] at result
      exact result
    · obtain ⟨alpha,principal,selected⟩ := given_beta_principal_fold_and_degree site initial prefixHistory
        closed matching weights oldIH edge geometry empty
      have backwards : physicalOriginalWord weights edge.reverseRoute=EdgeWord.reverse alpha.edgeWord :=
        (physicalOriginalWord_reverse weights reverseLaw edge.principal).trans (congrArg EdgeWord.reverse principal)
      have support := localHistory.supported (init_is_INIT source.erase).supported
      have onSupport : ∀n,Label.atom n∈(initLabels source.erase).labels →
          physicalOriginalWord weights (selection.atomWord n)=(initialRelabelling source 0 n).edgeWord :=
        fun n member=>supported_basis_atom_fold closed matching weights oldIH selection member
      intro p
      change Option.map (fun xs : List (Endpoint site.net)=>xs.flatMap weights) _ = _
      rw [LTerm.sourceTrail_flatMap]
      have atoms := localTarget.sourceTrail_supported_atoms_congr support
        (fun n=>physicalOriginalWord weights (selection.atomWord n))
        (fun n=>(initialRelabelling source 0 n).edgeWord)
        (physicalOriginalWord weights edge.principal) (physicalOriginalWord weights edge.reverseRoute) onSupport p
      change localTarget.sourceTrail (fun n=>physicalOriginalWord weights (selection.atomWord n))
        (physicalOriginalWord weights edge.principal) (physicalOriginalWord weights edge.reverseRoute) p = _
      rw [atoms,principal,backwards]
      exact local_cumulative_original_word old globalHistory localHistory selected p
  refine ⟨localTarget,localHistory,sameErase,edge,selection,geometry,
    site.beta_original_word_reversal edge weights reverseLaw,?_⟩
  intro access
  obtain ⟨bijection,corresponds,_⟩ := targetMatches
  let position := bijection access
  have word := (corresponds access).1
  have valid := position.property
  cases lookup : target.subterm position.val with
  | none => rw [←LTerm.erase_subterm,lookup] at valid;cases valid
  | some sub =>
    obtain ⟨a,b,whole⟩ := access.property.1.1
    obtain ⟨localSub,_localLookup,_sameSub,finish,trail,output,_node,_port,
      evaluation,residual,assignment,_ending,_proper⟩ := all lookup access word a
    have sameOutput := assignment.output_unique whole
    cases sameOutput
    have value := congrArg (Option.map (physicalOriginalWord weights)) evaluation
    rw [Option.map_some] at value
    have syntacticWord := (cumulative position.val).symm.trans value
    have actual := residual.original_word_transport_actual site weights reverseLaw
    rw [word]
    exact syntacticWord.trans (congrArg some actual.symm)
end
end Lamping.AG

#print axioms Lamping.AG.supported_basis_atom_fold
#print axioms Lamping.Lambda.Labelled.LTerm.sourceTrail_flatMap
#print axioms Lamping.Lambda.Labelled.LTerm.sourceTrail_supported_atoms_congr
#print axioms Lamping.AG.given_beta_principal_fold_and_degree
#print axioms Lamping.AG.PathSite.beta_original_word_root_access

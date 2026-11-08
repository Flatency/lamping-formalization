import Lamping.Lambda.LabelCopyBinderOrigins
import Lamping.Lambda.LabelAncestorBinderProtection
namespace Lamping.Lambda.Labelled

/-- An atomic route in the actual INIT graph is precisely its unique old edge. -/
theorem SourceRoute.initial_atom_edge (initial : INIT t)
    (route : SourceRoute (sourceEdges env ctx t) start (Label.atom n) finish) :
    ∃ e∈sourceEdges env ctx t,e.atom=Label.atom n ∧ e.fromPort=start ∧ e.toPort=finish := by
  obtain ⟨m,e,first,member,atomic,fromEq⟩ := route.first_atom
  have same : n=m := Option.some.inj first
  cases same
  obtain ⟨m,lastEdge,last,lastMember,lastAtomic,toEq⟩ := route.last_atom
  have same : n=m := Option.some.inj last
  cases same
  have equal := sourceEdges_unique initial lastMember member (lastAtomic.trans atomic.symm)
  exact ⟨e,member,atomic,fromEq,by simpa only [equal] using toEq⟩

/-- A real edge of one subtree cannot bind a node in a disjoint subtree.
The external environment is checked by its actual syntax ancestors. -/
theorem SourceSubterm.edge_not_bind_disjoint
    (atSite : SourceSubterm [] .external t p env ctx subtree)
    (initial : INIT t) (other : t.subterm q=some sibling)
    (apart : DisjointPositions p q) (member : e∈sourceEdges env ctx subtree)
    (inside : l∈sibling.labels) : e.toPort≠.lamBind l := by
  intro target
  rcases sourceEdges_to_port subtree member with ⟨node,nodeMember,nodeEq⟩ | ⟨node,outer,nodeEq⟩ | ⟨i,freeEq⟩
  · have same : node=l := by simpa only [target,SourcePort.node,Option.some.injEq] using nodeEq.symm
    exact t.disjoint_subterm_labels initial atSite.lookup other apart l (same ▸ nodeMember) inside
  · have same : node=l := SourcePort.lamBind.inj (nodeEq.symm.trans target)
    exact atSite.binder_not_in_disjoint initial other apart (same ▸ outer) inside
  · rw [target] at freeEq
    cases freeEq

/-- In particular, an atomic original-argument route cannot terminate at an
original body binder, including when its current copied occurrence is shifted. -/
theorem SourceSubterm.argument_atom_not_body_binder {body argument : LTerm}
    (atHead : SourceSubterm [] .external t head env ctx (.app beta (.lam alpha body) argument))
    (initial : INIT t) (argumentAtom : Label.atom m∈argument.labels)
    (bodyAtom : Label.atom n∈body.labels)
    (route : SourceRoute (sourceEdges [] .external t) start (Label.atom m) (.lamBind (Label.atom n))) : False := by
  let atArgument : SourceSubterm [] .external t (head++[.arg]) env (.appArg beta) argument :=
    atHead.append (.arg .nil)
  have bodyLookup : t.subterm (head++[.fn,.body])=some body :=
    (atHead.append (.fn (.body .nil))).lookup
  obtain ⟨e,member,atomic⟩ := sourceEdges_has_label (env := env) (atPort := .appArg beta) argumentAtom
  obtain ⟨globalEdge,globalMember,globalAtomic,_,target⟩ := route.initial_atom_edge initial
  have equal := sourceEdges_unique initial globalMember (atArgument.edges_subset e member) (globalAtomic.trans atomic.symm)
  have target' : e.toPort=.lamBind (Label.atom n) := by simpa only [equal] using target
  exact atArgument.edge_not_bind_disjoint initial bodyLookup
    ((DisjointPositions.head_ne (by decide : Step.arg≠Step.fn)).prefix head) member bodyAtom target'

/-- A copied old-argument atom cannot bind a retained body lambda above its
copy. The degree and node substitutions are kept separate throughout. -/
theorem StepAt.argument_atom_not_body_copy_binder {body argument : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite)
    (strict : copySite=before++(.body::suffix))
    (binderLookup : (initLabels u.erase).subterm (head++before)=some (.lam (Label.atom j) current))
    (edgeMember : e∈sourceEdges [] .external (initLabels u.erase))
    (edgeTarget : e.toPort=.lamBind (Label.atom j))
    (edgeImage : e.atom.relabel (initialRelabelling u 0)=Label.atom m)
    (argumentAtom : Label.atom m∈argument.labels) : False := by
  let f := initialRelabelling u 0
  obtain ⟨env,ctx,atHead⟩ := SourceSubterm.of_lookup t source [] .external
  have actualBinder := LTerm.basis_node_transport u binderLookup
  change u.subterm (head++before)=some (.lam (f j) (current.relabel f)) at actualBinder
  have contractBinder : (LTerm.contract beta alpha body argument).subterm before=
      some (.lam (f j) (current.relabel f)) := by
    rw [LTerm.subterm_append,step.contract_lookup source] at actualBinder
    exact actualBinder
  obtain ⟨n,last,bodyAtom,_⟩ := LTerm.contract_copy_ancestor_origin_outside
    (initial.subterm source) occurs strict contractBinder
  obtain ⟨nodes,replacements⟩ := (History.cons step (.nil u)).induced_edge_routes initial
  obtain ⟨binderEnv,binderCtx,atBinder⟩ := SourceSubterm.of_lookup (initLabels u.erase) binderLookup [] .external
  let binderEdge : SourceEdge := ⟨Label.atom j,binderCtx,.lamContext (Label.atom j)⟩
  have binderMember : binderEdge∈sourceEdges [] .external (initLabels u.erase) :=
    atBinder.edges_subset binderEdge List.mem_cons_self
  have binderRoute := replacements binderEdge binderMember
  change SourceRoute (sourceEdges [] .external t) (binderCtx.relabel nodes) (f j) (.lamContext (nodes j)) at binderRoute
  obtain ⟨k,originLast,origin⟩ := binderRoute.lam_last_atom
  have same : k=n := Option.some.inj (originLast.symm.trans last)
  subst k
  have variableRoute := replacements e edgeMember
  rw [edgeImage,edgeTarget] at variableRoute
  change SourceRoute (sourceEdges [] .external t) (e.fromPort.relabel nodes) (Label.atom m) (.lamBind (nodes j)) at variableRoute
  rw [origin] at variableRoute
  exact atHead.argument_atom_not_body_binder initial argumentAtom bodyAtom variableRoute


/-- A lambda strictly above the actual contraction retains its full label;
its descendant contraction necessarily passes through the body edge. -/
theorem StepAt.strict_lambda_ancestor {nodeLabel : Label}
    (step : StepAt head t u) (lookup : u.subterm q=some (.lam nodeLabel current))
    (paths : head=q++rest) (nonempty : rest≠[]) :
    ∃ suffix oldBody,rest=.body::suffix ∧ t.subterm q=some (.lam nodeLabel oldBody) := by
  induction q generalizing head t u with
  | nil =>
    simp only [List.nil_append] at paths
    subst head
    cases step with
    | root => exact False.elim (nonempty rfl)
    | fn => simp [LTerm.subterm] at lookup
    | arg => simp [LTerm.subterm] at lookup
    | body inner =>
      have same := LTerm.lam.inj (Option.some.inj lookup)
      cases same.1
      exact ⟨_,_,rfl,rfl⟩
  | cons edge qs ih =>
    cases step with
    | root => cases paths
    | fn inner =>
      cases edge with
      | body => simp [LTerm.subterm] at lookup
      | arg => cases paths
      | fn => exact ih inner lookup (List.cons.inj paths).2
    | arg inner =>
      cases edge with
      | body => simp [LTerm.subterm] at lookup
      | fn => cases paths
      | arg => exact ih inner lookup (List.cons.inj paths).2
    | body inner =>
      cases edge with
      | fn => simp [LTerm.subterm] at lookup
      | arg => simp [LTerm.subterm] at lookup
      | body => exact ih inner lookup (List.cons.inj paths).2

/-- A copied argument atom bound outside that copy can only use a lambda
strictly above the actual head. The retained body-binder alternative is
excluded by actual replacement routes and capture-avoiding scope. -/
theorem StepAt.argument_copy_external_binder {body argument : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite)
    (strict : head++copySite=binderSite++(.body::suffix))
    (binderLookup : (initLabels u.erase).subterm binderSite=some (.lam (Label.atom j) current))
    (edgeMember : e∈sourceEdges [] .external (initLabels u.erase))
    (edgeTarget : e.toPort=.lamBind (Label.atom j))
    (edgeImage : e.atom.relabel (initialRelabelling u 0)=Label.atom m)
    (argumentAtom : Label.atom m∈argument.labels) :
    ∃ n tail oldBody,head=binderSite++(.body::tail) ∧
      initialRelabelling u 0 j=Label.atom n ∧
      t.subterm binderSite=some (.lam (Label.atom n) oldBody) := by
  have notInside : ¬ head <+: binderSite := by
    rintro ⟨before,rfl⟩
    have copyPath : copySite=before++(.body::suffix) :=
      List.append_cancel_left (strict.trans (List.append_assoc _ _ _))
    exact step.argument_atom_not_body_copy_binder initial source occurs copyPath binderLookup edgeMember edgeTarget edgeImage argumentAtom
  have binderPrefix : binderSite <+: head := by
    rcases List.prefix_or_prefix_of_prefix (show head <+: head++copySite from ⟨copySite,rfl⟩)
      (show binderSite <+: head++copySite from ⟨.body::suffix,strict.symm⟩) with inside | above
    · exact False.elim (notInside inside)
    · exact above
  obtain ⟨rest,paths⟩ := binderPrefix
  have nonempty : rest≠[] := by
    intro empty
    apply notInside
    exact ⟨[],by simpa only [empty,List.append_nil] using paths.symm⟩
  have actualBinder := LTerm.basis_node_transport u binderLookup
  change u.subterm binderSite=some (.lam (initialRelabelling u 0 j) (current.relabel (initialRelabelling u 0))) at actualBinder
  obtain ⟨tail,oldBody,restPath,old⟩ := step.strict_lambda_ancestor actualBinder paths.symm nonempty
  obtain ⟨n,atomic⟩ := initial.1 (initialRelabelling u 0 j) (LTerm.label_mem_of_subterm old)
  exact ⟨n,tail,oldBody,by rw [paths.symm,restPath],atomic,by simpa only [atomic] using old⟩


/-- The only external-copy binding alternative is protected by the actual
whole Standard schedule. This rules out that binder atom in the final degree,
rather than asserting any global injectivity of the induced node map. -/
theorem History.standard_argument_copy_binder_avoid {body argument : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite)
    (strict : head++copySite=binderSite++(.body::suffix))
    (binderLookup : (initLabels u.erase).subterm binderSite=some (.lam (Label.atom j) current))
    (edgeMember : e∈sourceEdges [] .external (initLabels u.erase))
    (edgeTarget : e.toPort=.lamBind (Label.atom j))
    (edgeImage : e.atom.relabel (initialRelabelling u 0)=Label.atom m)
    (argumentAtom : Label.atom m∈argument.labels)
    (history : History ps t v) (last : StepAt q v z)
    (tail : ParallelHistory u.erase z.erase) (ordinary : Atomic tail)
    (standard : Standard (.cons (singleContraction step.betaAt) tail))
    (paths : (ParallelHistory.cons (singleContraction step.betaAt) tail).derivation.paths=ps++[q])
    (degree : v.degreeAt q=some l) :
    ∃ n,initialRelabelling u 0 j=Label.atom n ∧ l.Supported (fun k => k≠n) := by
  obtain ⟨n,headSuffix,oldBody,headPath,atomic,old⟩ := step.argument_copy_external_binder
    initial source occurs strict binderLookup edgeMember edgeTarget edgeImage argumentAtom
  exact ⟨n,atomic,history.standard_ancestor_degree_avoid last initial old step.betaAt
    tail ordinary standard paths headPath degree⟩

end Lamping.Lambda.Labelled







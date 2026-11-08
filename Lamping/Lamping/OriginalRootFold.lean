import Lamping.Lamping.InitialOriginalWordSeed
import Lamping.Lamping.FragmentRelabelling
import Lamping.Lamping.NetIsoPathTransport
import Lamping.Lamping.InitialMatching

namespace Lamping.Lambda.Labelled.LTerm

def originalIncomingTrail : LTerm → Path → Option EdgeWord
  | t, [] => some t.label.edgeWord
  | .app stamp fn _, .fn::p => (originalIncomingTrail fn p).map (stamp.edgeWord ++ ·)
  | .app stamp _ arg, .arg::p => (originalIncomingTrail arg p).map (stamp.edgeWord ++ ·)
  | .lam stamp body, .body::p => (originalIncomingTrail body p).map (stamp.edgeWord ++ ·)
  | _, _ => none

theorem originalIncomingTrail_single_child
    {t parent child : LTerm} {p : Path} {s : Step}
    (lookup : t.subterm p=some parent) (atChild : parent.subterm [s]=some child) :
    t.originalIncomingTrail (p++[s])=
      (t.originalIncomingTrail p).map (fun pre=>pre++child.label.edgeWord) := by
  induction p generalizing t with
  | nil =>
    have root : t.subterm []=some t := by cases t <;> rfl
    rw [root] at lookup
    cases Option.some.inj lookup
    cases parent <;> cases s <;> simp_all [subterm,originalIncomingTrail,LTerm.label]
  | cons step p ih =>
    cases t <;> cases step <;>
      simp_all [subterm,originalIncomingTrail,Option.map_map,Function.comp_def,List.append_assoc]
end Lamping.Lambda.Labelled.LTerm

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

def OriginalRootFold (g : Net signature N B W) (root : B) (current : LTerm)
    (weights : Endpoint g→EdgeWord) : Prop :=
  ∀ access : RootAccess g root,
    current.originalIncomingTrail (accessWord g access.val)=
      some (physicalOriginalWord weights access.val)

theorem OccurrenceFragment.original_word_of_root_fold
    {current : LTerm} {p : Path}
    (matching : Matches g root current.erase)
    (weights : Endpoint g→EdgeWord) (constructed : OriginalRootFold g root current weights)
    (fragment : OccurrenceFragment current g root p) :
    physicalOriginalWord weights fragment.fragment.segments=fragment.term.label.edgeWord := by
  rcases fragment.occurrence.last_departure with ⟨empty,external⟩ |
      ⟨parentPath,step,parentTerm,split,lookup,role⟩
  · have fromExternal : (sourceEdge fragment.environment fragment.context fragment.term).fromPort=.external := by
      cases fragment.term <;> exact external
    have root : current.subterm []=some current := by cases current <;> rfl
    have atRoot := root.symm.trans ((congrArg current.subterm empty).symm.trans fragment.occurrence.lookup)
    have termEq := Option.some.inj atRoot
    have eq := (congrArg current.originalIncomingTrail (fragment.fragment.word.trans empty)).symm.trans
      (constructed fragment.fragment.access)
    have emptyTrail : current.originalIncomingTrail []=some current.label.edgeWord := by cases current <;> rfl
    rw [emptyTrail] at eq
    rw [fragment.fragment.external_segments fromExternal]
    exact (Option.some.inj eq).symm.trans (congrArg (fun t : LTerm=>t.label.edgeWord) termEq)
  · let parentPosition : Position current.erase := ⟨parentPath,by
      rw [←LTerm.erase_subterm,lookup];rfl⟩
    obtain ⟨parent,parentWord,_⟩ := Matches.observation g matching parentPosition
    have expanded : current.subterm p=parentTerm.subterm [step] :=
      (congrArg current.subterm split).trans (by rw [LTerm.subterm_append,lookup,Option.bind_some])
    have atChild := expanded.symm.trans fragment.occurrence.lookup
    have departure : SourceDeparture parentTerm step
        (sourceEdge fragment.environment fragment.context fragment.term).fromPort := by
      cases fragment.term <;> exact role
    have word : p=accessWord g parent.val++[step] := by rw [parentWord];exact split
    have cut := fragment.fragment.child_prefix matching departure parent word
    have eq := (congrArg current.originalIncomingTrail (fragment.fragment.word.trans split)).symm.trans
      (constructed fragment.fragment.access)
    have before := constructed parent
    rw [parentWord] at before
    rw [LTerm.originalIncomingTrail_single_child lookup atChild,before] at eq
    have totals : physicalOriginalWord weights parent.val++fragment.term.label.edgeWord=
        physicalOriginalWord weights parent.val++physicalOriginalWord weights fragment.fragment.segments := by
      simpa only [Option.map_some,Option.some.injEq,cut.2,physicalOriginalWord,List.flatMap_append] using eq
    exact (List.append_cancel_left totals).symm
end

theorem initial_original_root_fold
    (original : LTerm) (closed : Closed original.erase) (level : Nat)
    (addr : Addressing (encode level original.erase).net (boundaryAddressAt [])) :
    OriginalRootFold (encode level original.erase).net (.inl ()) original
      (initialOriginalWeights original level addr) := by
  let g := (encode level original.erase).net
  let weights := initialOriginalWeights original level addr
  have matching : Matches g (.inl ()) original.erase := encode_closed_matches original.erase closed level
  have go : ∀ n,∀ (p : Path),p.length=n →∀ (node : LTerm),original.subterm p=some node →
      ∀ access : RootAccess g (.inl ()),accessWord g access.val=p →
        original.originalIncomingTrail p=some (physicalOriginalWord weights access.val) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro p length node lookup access word
      by_cases empty : p=[]
      · cases empty
        obtain ⟨fragment⟩ := matching.occurrence_fragment_at closed lookup
        have fromExternal : (sourceEdge fragment.environment fragment.context fragment.term).fromPort=.external := by
          rcases fragment.occurrence.last_departure with ⟨_,external⟩ |
              ⟨parent,step,term,split,_lookup,_role⟩
          · cases fragment.term <;> exact external
          · have sizes := congrArg List.length split
            simp only [List.length_nil,List.length_append,List.length_singleton] at sizes
            omega
        have sameAccess : fragment.fragment.access=access :=
          matching.accessWord_injective (fragment.fragment.word.trans word.symm)
        obtain ⟨a,b,whole⟩ := fragment.fragment.access.property.1.1
        have seed := fragment.initial_original_word_given_assignment addr whole
        have root : original.subterm []=some original := by cases original <;> rfl
        have termEq := fragment.occurrence.lookup
        rw [root] at termEq
        have labels := congrArg (fun t : LTerm=>t.label.edgeWord) (Option.some.inj termEq)
        rw [fragment.fragment.external_segments fromExternal,sameAccess] at seed
        have emptyTrail : original.originalIncomingTrail []=some original.label.edgeWord := by cases original <;> rfl
        rw [emptyTrail]
        exact congrArg some (labels.trans seed.symm)
      · cases rev : p.reverse with
        | nil =>
          have back := congrArg List.reverse rev
          have eq : p=[] := by simpa only [List.reverse_reverse,List.reverse_nil] using back
          exact False.elim (empty eq)
        | cons step rest =>
          let parentPath := rest.reverse
          have split : p=parentPath++[step] := by
            have back := congrArg List.reverse rev
            simpa only [List.reverse_reverse,List.reverse_cons] using back
          have atChildLookup := lookup
          rw [split,LTerm.subterm_append] at atChildLookup
          cases parentLookup : original.subterm parentPath with
          | none => rw [parentLookup] at atChildLookup;cases atChildLookup
          | some parentTerm =>
            rw [parentLookup,Option.bind_some] at atChildLookup
            let position : Position original.erase := ⟨parentPath,by
              rw [←LTerm.erase_subterm,parentLookup];rfl⟩
            obtain ⟨parent,parentWord,_⟩ := Matches.observation g matching position
            have shorter : parentPath.length<n := by rw [←length,split,List.length_append];simp
            have parentFold := ih parentPath.length shorter parentPath rfl parentTerm parentLookup parent parentWord
            obtain ⟨fragment⟩ := matching.occurrence_fragment_at closed lookup
            have sameAccess : fragment.fragment.access=access :=
              matching.accessWord_injective (fragment.fragment.word.trans word.symm)
            have departure : SourceDeparture parentTerm step
                (sourceEdge fragment.environment fragment.context fragment.term).fromPort := by
              rcases fragment.occurrence.last_departure with ⟨root,_⟩ |
                  ⟨other,child,term,equal,atTerm,role⟩
              · exact False.elim (empty root)
              · have pair := List.append_inj' (split.symm.trans equal) rfl
                have steps : step=child := (List.cons.inj pair.2).1
                have parents := pair.1
                subst other
                subst child
                have terms := Option.some.inj (parentLookup.symm.trans atTerm)
                subst term
                cases fragment.term <;> exact role
            have wordChild : p=accessWord g parent.val++[step] := by rw [parentWord];exact split
            have cut := fragment.fragment.child_prefix matching departure parent wordChild
            obtain ⟨a,b,whole⟩ := fragment.fragment.access.property.1.1
            have seed := fragment.initial_original_word_given_assignment addr whole
            have nodeEq := Option.some.inj (lookup.symm.trans fragment.occurrence.lookup)
            have labels := congrArg (fun t : LTerm=>t.label.edgeWord) nodeEq
            rw [split,LTerm.originalIncomingTrail_single_child parentLookup atChildLookup,parentFold]
            rw [Option.map_some]
            apply congrArg some
            rw [←sameAccess,cut.2]
            change _=physicalOriginalWord weights (parent.val++fragment.fragment.segments)
            simp only [physicalOriginalWord,List.flatMap_append]
            have seed' : physicalOriginalWord weights fragment.fragment.segments=node.label.edgeWord :=
              seed.trans labels.symm
            exact congrArg (physicalOriginalWord weights parent.val++·) seed'.symm
  intro access
  obtain ⟨bij,corresponds,_⟩ := matching
  let position := bij access
  have word := (corresponds access).1
  have valid := position.property
  cases lookup : original.subterm position.val with
  | none => rw [←LTerm.erase_subterm,lookup] at valid;cases valid
  | some node =>
    rw [word]
    exact go position.val.length position.val rfl node lookup access word
end Lamping.AG

namespace Lamping.Graph
open Lamping.AG Lamping.Lambda Lamping.Lambda.Labelled
section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V}

theorem NetIso.original_word_reversal
    (iso : NetIso g h) (weights : Endpoint g→EdgeWord)
    (old : OriginalWordReversal weights) :
    OriginalWordReversal (fun e=>weights (iso.symm.ends e)) := by
  intro e
  change weights (iso.symm.ends (h.wire e))=EdgeWord.reverse (weights (iso.symm.ends e))
  rw [iso.symm.wiring]
  exact old _

theorem NetIso.original_root_fold
    (iso : NetIso g h) {root : B} {current : LTerm}
    (weights : Endpoint g→EdgeWord) (old : OriginalRootFold g root current weights) :
    OriginalRootFold h root current (fun e=>weights (iso.symm.ends e)) := by
  intro access
  let source : RootAccess g root := ⟨access.val.map iso.symm.ends,iso.symm.rootAccess access.property⟩
  have eq := old source
  change current.originalIncomingTrail (AG.accessWord g (access.val.map iso.symm.ends))=_ at eq
  rw [iso.symm.accessWord] at eq
  simpa only [source,physicalOriginalWord,List.flatMap_map,Function.comp_def] using eq
end
end Lamping.Graph

#print axioms Lamping.Lambda.Labelled.LTerm.originalIncomingTrail
#print axioms Lamping.AG.OriginalRootFold
#print axioms Lamping.Lambda.Labelled.LTerm.originalIncomingTrail_single_child
#print axioms Lamping.AG.OccurrenceFragment.original_word_of_root_fold
#print axioms Lamping.AG.initial_original_root_fold
#print axioms Lamping.Graph.NetIso.original_word_reversal
#print axioms Lamping.Graph.NetIso.original_root_fold

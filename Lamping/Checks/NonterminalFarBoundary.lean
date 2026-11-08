import Lamping.Lamping.NonterminalFarBoundary
import Lamping.Checks.UniformOldOuterImageAlignment
import Lamping.Checks.CopyOverlapOriginalAuxiliary
import Lamping.Checks.ActualSpineAfterAlignment
import Lamping.Checks.ForwardOtherLastEndpoints
import Lamping.Checks.ActualUnsafeMarkerLeaves

namespace Lamping.Checks.NonterminalFarBoundaryChecks
open Lambda Lambda.Labelled AG SyntaxIncidence
open Lambda.Labelled.NonterminalFarBoundary

namespace MarkedLast
open UniformOldOuterImageAlignmentChecks.MarkedLast

theorem currentMarked : ¬current.label.OuterBarsSafe (fun d=>d≠Label.atom 10) := by
  intro safe
  change (Label.atom 10≠Label.atom 10) ∧_ at safe
  exact safe.1 rfl

def markedSpine : DirectedMarkerSpine F source (.atom 10) true [[.arg],[]] target [] [.fn] :=
  old.directed_marker_spine labels selected sourceSafe .refl reading rfl currentMarked (by simp)

def cut : ActualUnsafeMarkerCut F [[.arg],[]] source target (.atom 10) [] [[.fn],[.fn,.fn]] where
  before:=[]
  edge:=[.fn]
  after:=[[.fn,.fn]]
  reader:=[]
  node:=current
  forward:=true
  split:=rfl
  segment:=.refl
  remaining:=chain
  reading:=reading
  lookup:=rfl
  safeBefore:=by simp
  marked:=currentMarked
  spine:=markedSpine
  leaf:=markedSpine.leaf_output rfl


theorem actual_whole_marked_last_far :
    INIT original ∧History [[],[],[.arg],[.arg],[]] original target ∧
    ∃snapshot : IncomingIncidenceSnapshot target cut.edge,
      ∃canonical : CanonicalAfterFarOutput labels cut snapshot,
        ∃out : OriginalFarAtom source F 7 true true canonical.sourceProper,
          out.position=[.arg,.fn,.body] ∧
          Nonempty (Comparison source F 7 7 true true (globalPrefix.closed originalClosed) canonical.sourceProper canonical.sourceProper) := by
  obtain ⟨leaf,snapshot,⟨geometry⟩⟩:=cut.spine.incidence_leaf_output (globalPrefix.closed originalClosed) cut.lookup
  obtain ⟨canonical⟩:=cut.canonical_far_output labels (globalPrefix.closed originalClosed) (by decide) snapshot
  obtain ⟨out⟩:=actual_old_far_atom labels old localLabels cut (by decide) snapshot canonical
    (by rfl : localTarget.subterm [.fn]=some localCurrent)
    (by rfl : localCurrent.label.readLetters true=[.atom 3,.under (.atom 1),.atom 5]++[InteriorSourceBlock.bar true (.atom 6),.atom 7])
  have located : out.position=[.arg,.fn,.body] :=
    LTerm.subterm_label_injective _ (init_is_INIT _).2 out.occurrence.lookup
      (by rfl : localSource.subterm [.arg,.fn,.body]=some (.app (.atom 7) (.var (.atom 8) 0) (.var (.atom 9) 0))) out.atomic
  have good : CanonicalFarFullComparison (globalPrefix.closed originalClosed) canonical canonical:=⟨rfl,⟨ChainIncidenceIso.refl _⟩⟩
  exact ⟨initial,globalPrefix.append labels,snapshot,canonical,out,located,
    ⟨compare_original_atoms (globalPrefix.closed originalClosed) selected canonical canonical good out out rfl⟩⟩
end MarkedLast
namespace VariableFar
open ForwardOtherLastEndpointsChecks.ArgOuterBinder
abbrev F : List Path:=[site]
abbrev labels : History [site] source target:=event.final_history
abbrev old:=event.final_old
abbrev currentNode : LTerm:=.var (((Label.atom 5).concat (Label.atom 3).under).concat (.atom 7)) 0

theorem selected (p : Path) (member : p∈F) : source.degreeAt p=some (.atom 3) := by
  have same:=List.mem_singleton.mp member
  subst p;rfl

theorem reading : PrerequisiteReadsDirected target site (site++[.fn]) true :=⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
theorem marked : ¬currentNode.label.OuterBarsSafe (fun d=>d≠Label.atom 3) := by
  intro safe
  change (Label.atom 3≠Label.atom 3) ∧_ at safe
  exact safe.1 rfl

def spine : DirectedMarkerSpine F source (.atom 3) true [site] target [] (site++[.fn]) :=
  old.directed_marker_spine labels selected ((init_is_INIT _).outerBarsSafe _) .refl reading rfl marked (by simp)

def cut : ActualUnsafeMarkerCut F [site] source target (.atom 3) site [site++[.fn],[.fn]] where
  before:=[]
  edge:=([Step.fn,Step.body,Step.fn] : Path)
  after:=[[.fn]]
  reader:=site
  node:=currentNode
  forward:=true
  split:=rfl
  segment:=.refl
  remaining:=remaining
  reading:=reading
  lookup:=rfl
  safeBefore:=by simp
  marked:=marked
  spine:=by simpa only [site,List.cons_append,List.nil_append,List.map_nil] using spine
  leaf:=spine.leaf_output rfl

def localHistory : History [site] (initLabels source.erase) target:=.cons (.fn (.body (.root _ _ _ _))) (.nil _)

theorem actual_variable_binder_far :
    INIT source ∧Closed source.erase ∧History [site] source target ∧
      ∃snapshot : IncomingIncidenceSnapshot target cut.edge,
        ∃canonical : CanonicalAfterFarOutput labels cut snapshot,
          ∃out : OriginalFarAtom source F 7 false true canonical.sourceProper,
            out.position=site++[.arg] ∧canonical.sourceProper.val=[.fn] ∧
            out.position≠canonical.sourceProper.val := by
  have closed:=actual_history.2.1
  obtain ⟨leaf,snapshot,⟨geometry⟩⟩:=cut.spine.incidence_leaf_output closed cut.lookup
  obtain ⟨canonical⟩:=cut.canonical_far_output labels closed (by decide) snapshot
  obtain ⟨out⟩:=actual_old_far_atom labels old localHistory cut (by decide) snapshot canonical
    (by rfl : target.subterm (site++[.fn])=some currentNode)
    (by rfl : currentNode.label.readLetters true=[.atom 5]++[InteriorSourceBlock.bar false (.atom 3),.atom 7])
  have located : out.position=site++[.arg] :=
    LTerm.subterm_label_injective _ (init_is_INIT _).2 out.occurrence.lookup
      (by rfl : (initLabels source.erase).subterm (site++[.arg])=some (.var (.atom 7) 0)) out.atomic
  have binder : Target source out.position (some far) := by
    rw [located]
    exact Or.inr ⟨.atom 7,0,.atom 1,_,[.arg],rfl,rfl,rfl,rfl⟩
  have farEq : canonical.sourceProper=far := Option.some.inj (Target.unique out.endpoints.2 binder)
  have coordinate : canonical.sourceProper.val=[.fn]:=congrArg Subtype.val farEq
  exact ⟨actual_history.1,closed,labels,snapshot,canonical,out,located,coordinate,by rw [located,coordinate];decide⟩
end VariableFar
namespace ReverseArg
open ActualUnsafeMarkerLeavesChecks.Nonterminal

theorem reading : PrerequisiteReadsDirected current [.arg] [.arg] false:=⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
theorem currentMarked : ¬result.label.OuterBarsSafe (fun d=>d≠Label.atom 4) := by
  intro safe
  change (Label.atom 4≠Label.atom 4) ∧_ at safe
  exact safe.1 rfl

def spine : DirectedMarkerSpine F source (.atom 4) false [[.arg]] current [] [.arg]:=
  old.directed_marker_spine labels selected (initial.outerBarsSafe _) .refl reading rfl currentMarked (by simp)

def cut : ActualUnsafeMarkerCut F [[.arg]] source current (.atom 4) [.arg] edges where
  before:=[]
  edge:=[.arg]
  after:=[[.fn]]
  reader:=[.arg]
  node:=result
  forward:=false
  split:=rfl
  segment:=.refl
  remaining:=chain
  reading:=reading
  lookup:=rfl
  safeBefore:=by simp
  marked:=currentMarked
  spine:=spine
  leaf:=spine.leaf_output rfl

def localHistory : History [[.arg]] (initLabels source.erase) current:=.cons (.arg (.root _ _ _ _)) (.nil _)
def parent : ProperPosition source:=⟨[],Or.inl ⟨_,_,_,rfl⟩⟩

theorem actual_arg_parent_far :
    ∃snapshot : IncomingIncidenceSnapshot current cut.edge,
      ∃canonical : CanonicalAfterFarOutput labels cut snapshot,
        ∃out : OriginalFarAtom source F 3 true false canonical.sourceProper,
          out.position=[.arg] ∧canonical.sourceProper.val=[] := by
  obtain ⟨leaf,snapshot,⟨geometry⟩⟩:=cut.spine.incidence_leaf_output sourceClosed cut.lookup
  obtain ⟨canonical⟩:=cut.canonical_far_output labels sourceClosed (by decide) snapshot
  obtain ⟨out⟩:=actual_old_far_atom labels old localHistory cut (by decide) snapshot canonical
    (by rfl : current.subterm [.arg]=some result)
    (by rfl : result.label.readLetters false=[.atom 6,.under (.atom 4),.atom 5]++[InteriorSourceBlock.bar true (.atom 4),.atom 3])
  have located : out.position=[.arg] :=
    LTerm.subterm_label_injective _ (init_is_INIT _).2 out.occurrence.lookup
      (by rfl : (initLabels source.erase).subterm [.arg]=some (.app (.atom 3) (.lam (.atom 4) (.var (.atom 5) 0)) argument)) out.atomic
  have parentSource : Source source out.position (some parent) := by
    rw [located];exact ⟨.arg,_,_,rfl,rfl,.arg⟩
  have eq : canonical.sourceProper=parent:=Option.some.inj (Source.unique out.endpoints.1 parentSource)
  exact ⟨snapshot,canonical,out,located,congrArg Subtype.val eq⟩
end ReverseArg

namespace ReverseBody
abbrev I : Term:=.lam (.var 0)
abbrev bare : Term:=.app (.lam (.app I I)) I
abbrev source : LTerm:=initLabels bare
abbrev result : LTerm:=LTerm.contract (.atom 2) (.atom 3) (.var (.atom 4) 0) (.lam (.atom 5) (.var (.atom 6) 0))
abbrev target : LTerm:=.app (.atom 0) (.lam (.atom 1) result) (.lam (.atom 7) (.var (.atom 8) 0))
abbrev F : List Path:=[[.fn,.body]]

def labels : History [[.fn,.body]] source target:=.cons (.fn (.body (.root _ _ _ _))) (.nil _)
def old : Marked.RelativeOldHistory F [[.fn,.body]] (Marked.mark F source.erase)
    (.app [[]] (.lam (.lam (.var 0))) (.lam (.var 0))) :=
  .cons (.appL (.lam (.redRoot _ _ _))) (by decide) (.nil _)

theorem initial : INIT source:=init_is_INIT _
theorem closed : Closed source.erase:=by change Scoped 0 bare;simp [Scoped]
theorem selected (p : Path) (member : p∈F) : source.degreeAt p=some (.atom 3) := by
  have same:=List.mem_singleton.mp member;subst p;rfl

def chain : PrerequisiteChain target [.fn,.body] [[.fn,.body],[.fn]]:=
  .lam (parent:=[.fn]) (step:=.body) rfl (by decide) (.redex_lam (p:=[]) rfl)
theorem reading : PrerequisiteReadsDirected target [.fn,.body] [.fn,.body] false:=⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
theorem currentMarked : ¬result.label.OuterBarsSafe (fun d=>d≠Label.atom 3) := by
  intro safe
  change (Label.atom 3≠Label.atom 3) ∧_ at safe
  exact safe.1 rfl

def spine : DirectedMarkerSpine F source (.atom 3) false [[.fn,.body]] target [] [.fn,.body]:=
  old.directed_marker_spine labels selected (initial.outerBarsSafe _) .refl reading rfl currentMarked (by simp)

def cut : ActualUnsafeMarkerCut F [[.fn,.body]] source target (.atom 3) [.fn,.body] [[.fn,.body],[.fn]] where
  before:=[]
  edge:=[.fn,.body]
  after:=[[.fn]]
  reader:=[.fn,.body]
  node:=result
  forward:=false
  split:=rfl
  segment:=.refl
  remaining:=chain
  reading:=reading
  lookup:=rfl
  safeBefore:=by simp
  marked:=currentMarked
  spine:=spine
  leaf:=spine.leaf_output rfl

def localHistory : History [[.fn,.body]] (initLabels source.erase) target:=.cons (.fn (.body (.root _ _ _ _))) (.nil _)
def parent : ProperPosition source:=⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩

theorem actual_body_parent_far :
    INIT source ∧Closed source.erase ∧History [[.fn,.body]] source target ∧
      ∃snapshot : IncomingIncidenceSnapshot target cut.edge,
        ∃canonical : CanonicalAfterFarOutput labels cut snapshot,
          ∃out : OriginalFarAtom source F 2 true false canonical.sourceProper,
            out.position=[.fn,.body] ∧canonical.sourceProper.val=[.fn] := by
  obtain ⟨leaf,snapshot,⟨geometry⟩⟩:=cut.spine.incidence_leaf_output closed cut.lookup
  obtain ⟨canonical⟩:=cut.canonical_far_output labels closed (by decide) snapshot
  obtain ⟨out⟩:=actual_old_far_atom labels old localHistory cut (by decide) snapshot canonical
    (by rfl : target.subterm [.fn,.body]=some result)
    (by rfl : result.label.readLetters false=[.atom 5,.under (.atom 3),.atom 4]++[InteriorSourceBlock.bar true (.atom 3),.atom 2])
  have located : out.position=[.fn,.body] :=
    LTerm.subterm_label_injective _ (init_is_INIT _).2 out.occurrence.lookup
      (by rfl : (initLabels source.erase).subterm [.fn,.body]=some (.app (.atom 2) (.lam (.atom 3) (.var (.atom 4) 0)) (.lam (.atom 5) (.var (.atom 6) 0)))) out.atomic
  have parentSource : Source source out.position (some parent) := by
    rw [located];exact ⟨.body,_,_,rfl,rfl,.body⟩
  have eq : canonical.sourceProper=parent:=Option.some.inj (Source.unique out.endpoints.1 parentSource)
  exact ⟨initial,closed,labels,snapshot,canonical,out,located,congrArg Subtype.val eq⟩
end ReverseBody
end Lamping.Checks.NonterminalFarBoundaryChecks

#print axioms Lamping.Checks.NonterminalFarBoundaryChecks.MarkedLast.actual_whole_marked_last_far

#print axioms Lamping.Checks.NonterminalFarBoundaryChecks.VariableFar.actual_variable_binder_far

#print axioms Lamping.Checks.NonterminalFarBoundaryChecks.ReverseArg.actual_arg_parent_far

#print axioms Lamping.Checks.NonterminalFarBoundaryChecks.ReverseBody.actual_body_parent_far

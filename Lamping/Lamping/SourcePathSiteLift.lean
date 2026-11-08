import Lamping.Lamping.SourcePathShapes
import Lamping.Lamping.PrincipalCrossings
import Lamping.Lamping.PathSiteBetaAncestor
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

private theorem active_lift (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (p : Aux s.active) (exit : s.Frontier) (a b : Context)
    (path : LocalPath s.left (.inl p) exit a b) :
    ∃ es : List (Endpoint site.net),
      es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr (.inl p)))))) ∧
      es.getLast?=some (site.outsideEnd (.inr (.inl (.inr exit)))) ∧Labelling site.net es a b := by
  obtain ⟨q,same,shape⟩ := left_active_path_shape s.active s.passive control s.low s.high
    p exit path.edges a b path.labeling path.start path.finish
  subst exit
  have labels := path.labeling
  rw [shape] at labels
  obtain ⟨middle,first,second⟩ := (leftRoute_labeling_iff s.active s.passive s.low s.high p q a b).mp labels
  obtain ⟨route,start,finish,turns⟩ := site.principal_route
  have actual := principal_crossing_labels site.net (.inr (.inl ())) (.inr (.inr ()))
    (.inr p) (.inl ()) (.inl ()) (.inr q) route start finish turns first second
  refine ⟨_,rfl,?_,actual⟩
  simp only [List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.some_or]
  rfl

private theorem passive_lift (p q : Aux s.passive) (a b : Context)
    (labels : Labelling s.left [.inr (.inl (.inr p)),.inl ⟨.inr (),.inr q⟩] a b) :
    ∃ es : List (Endpoint site.net),
      es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr (.inr p)))))) ∧
      es.getLast?=some (site.outsideEnd (.inr (.inl (.inr (.inr q))))) ∧Labelling site.net es a b := by
  cases labels with
  | cons turn last =>
    cases last
    obtain ⟨port,out,rule⟩ := turn.from_node (.inr ()) (.inr p) rfl
    have same : port=.inr q := by
      have ports := sigma_snd_heq (Sum.inl.inj out)
      exact (eq_of_heq ports).symm
    subst port
    refine ⟨[site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩),.inl ⟨.inr (.inr ()),.inr q⟩],rfl,rfl,?_⟩
    apply Labelling.cons
    · rw [Pairing.involutive]
      exact LabelledTurn.node (g:=site.net) (.inr (.inr ())) _ _ rule
    · exact .single _ _

private theorem reverse_actual (x y : s.Frontier) (a b : Context)
    (path : ∃ es : List (Endpoint site.net),
      es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr y))))) ∧
      es.getLast?=some (site.outsideEnd (.inr (.inl (.inr x)))) ∧Labelling site.net es b a) :
    ∃ es : List (Endpoint site.net),
      es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr x))))) ∧
      es.getLast?=some (site.outsideEnd (.inr (.inl (.inr y)))) ∧Labelling site.net es a b := by
  obtain ⟨es,start,finish,labels⟩ := path
  refine ⟨reverseEdges es,?_,?_,labels.reverse⟩
  · simp only [reverseEdges,List.head?_map,List.head?_reverse,finish,Option.map_some]
  · simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,start,Option.map_some,Pairing.involutive]

/-- Lift every actual LHS local path into the matched physical graph, keeping
all selected principal subdivisions. Only active control geometry is required. -/
theorem PathSite.left_local_path_lift
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (entry exit : s.Frontier) (a b : Context) (path : LocalPath s.left entry exit a b) :
    ∃ es : List (Endpoint site.net),
      es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr entry))))) ∧
      es.getLast?=some (site.outsideEnd (.inr (.inl (.inr exit)))) ∧Labelling site.net es a b := by
  cases entry with
  | inl p => exact active_lift site control p exit a b path
  | inr p =>
    cases exit with
    | inl q =>
      exact reverse_actual site (.inr p) (.inl q) a b (active_lift site control q (.inr p) b a path.reverse)
    | inr q =>
      rcases left_passive_path_shape s.active s.passive s.low s.high p (.inr q)
        path.edges a b path.labeling path.start path.finish with ⟨r,impossible,_⟩ |⟨r,same,shape⟩
      · cases impossible
      · have ports : q=r := Sum.inr.inj same
        subst r
        have labels := path.labeling
        rw [shape] at labels
        exact passive_lift site p q a b labels
end
end Lamping.AG


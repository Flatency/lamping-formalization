import Lamping.Lamping.OccurrencePhysicalNodes
import Lamping.Lamping.InitialNesting

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

private theorem child_addressable {kind : Kind} {ctx departure : Port kind}
    (roles : SyntaxChildPorts kind ctx departure step) (address : Path) :
    ∃ word,syntaxPortAddress kind departure address=some word := by
  cases roles <;> exact ⟨_,rfl⟩

private theorem departure_addressable (nodes : N → Path) (boundary : B → Option Path)
    (vertices : W → Option Path) (role : SourceDeparture sub step port)
    (actual : SourcePortRealizes current g root port endpoint) :
    ∃ word,endpointAddress g nodes boundary vertices endpoint=some word := by
  cases role <;> cases actual with
  | departure lookup sourceRole parent word roles finish =>
    exact child_addressable roles (nodes _)
private theorem external_endpoint (actual : SourcePortRealizes current g root .external endpoint) :
    endpoint=.inr (.inl root) := by
  cases actual with
  | external => rfl
  | departure _ role _ _ _ _ => cases role
end

section
variable {current : LTerm} {level : Nat}

/-- At initial translation, the departure endpoint of any actual occurrence
fragment retains exactly that literal syntax address. -/
theorem OccurrenceFragment.initial_start_address
    (fragment : OccurrenceFragment current (encode level current.erase).net (.inl ()) position)
    (addr : Addressing (encode level current.erase).net (boundaryAddressAt [])) :
    endpointAddress (encode level current.erase).net addr.nodes (boundaryAddressAt [])
      addr.vertices fragment.fragment.fromEndpoint=some position := by
  have sourceFrom : (sourceEdge fragment.environment fragment.context fragment.term).fromPort=fragment.context := by
    cases fragment.term <;> rfl
  have source := fragment.fragment.fromRealizes
  rw [sourceFrom] at source
  have addressed : ∃ word,endpointAddress (encode level current.erase).net addr.nodes
      (boundaryAddressAt []) addr.vertices fragment.fragment.fromEndpoint=some word := by
    rcases fragment.occurrence.last_departure with ⟨_empty,external⟩ |⟨_parent,_step,_sub,_split,_lookup,role⟩
    · have asExternal : SourcePortRealizes current (encode level current.erase).net (.inl ())
          .external fragment.fragment.fromEndpoint :=
        Eq.mp (congrArg (fun port=>SourcePortRealizes current (encode level current.erase).net
          (.inl ()) port fragment.fragment.fromEndpoint) external) source
      rw [external_endpoint asExternal]
      exact ⟨[],rfl⟩
    · exact departure_addressable addr.nodes (boundaryAddressAt []) addr.vertices role source
  obtain ⟨word,address⟩ := addressed
  cases segments : fragment.fragment.segments with
  | nil => have impossible := fragment.fragment.start; rw [segments] at impossible; cases impossible
  | cons first rest =>
    have firstEqual : first=fragment.fragment.fromEndpoint :=
      Option.some.inj (by simpa only [segments,List.head?_cons] using fragment.fragment.start)
    subst first
    let pre := fragment.fragment.before++[fragment.fragment.fromEndpoint]
    have nonempty : pre≠[] := by simp [pre]
    have split : fragment.fragment.access.val=pre++rest := by
      simpa only [pre,segments,List.append_assoc,List.singleton_append] using fragment.fragment.literal
    obtain ⟨a,b,labels⟩ := fragment.fragment.access.property.1.1
    rw [split] at labels
    obtain ⟨c,prefixLabels⟩ := labels.prefix nonempty
    have root : pre.head?=some (.inr (.inl (.inl ()))) := by
      have rooted := fragment.fragment.access.property.2.1
      rw [split,List.head?_append] at rooted
      cases h : pre.head? with
      | none => exact False.elim (nonempty (List.head?_eq_none_iff.mp h))
      | some e => simpa only [h,Option.some_or] using rooted
    have last : pre.getLast?=some fragment.fragment.fromEndpoint := by simp [pre]
    have initial := encode_root_initial current.erase level pre root prefixLabels
    obtain ⟨before,rootState,same⟩ := addr.path_predecessor _ initial _ _ root last word address
    change some ([] : Path)=some before at rootState
    have empty : before=[] := (Option.some.inj rootState).symm
    have startWord : word=accessWord (encode level current.erase).net pre := by
      simpa only [empty,List.nil_append] using same
    have noTail : rest.flatMap (arrivalWord (encode level current.erase).net)=[] := by
      simpa only [segments,accessWord] using fragment.fragment.emptyWord
    have wholeWord := fragment.fragment.word
    rw [split,accessWord_append _ pre rest nonempty,noTail,List.append_nil] at wholeWord
    rw [startWord,wholeWord] at address
    exact address
/-- This injectivity is a fact about the recursively encoded initial graph,
not about different positions in a general shared reachable graph. -/
theorem OccurrenceFragment.initial_start_injective
    (first : OccurrenceFragment current (encode level current.erase).net (.inl ()) left)
    (second : OccurrenceFragment current (encode level current.erase).net (.inl ()) right)
    (same : first.fragment.fromEndpoint=second.fragment.fromEndpoint) : left=right := by
  obtain ⟨addr⟩ := encode_addressing current.erase level
  have leftAddress := first.initial_start_address addr
  have rightAddress := second.initial_start_address addr
  rw [same] at leftAddress
  exact Option.some.inj (leftAddress.symm.trans rightAddress)

theorem OccurrenceFragment.initial_segments_injective
    (first : OccurrenceFragment current (encode level current.erase).net (.inl ()) left)
    (second : OccurrenceFragment current (encode level current.erase).net (.inl ()) right)
    (same : first.fragment.segments=second.fragment.segments) : left=right := by
  have heads := congrArg List.head? same
  rw [first.fragment.start,second.fragment.start] at heads
  exact first.initial_start_injective second (Option.some.inj heads)
end
end Lamping.AG

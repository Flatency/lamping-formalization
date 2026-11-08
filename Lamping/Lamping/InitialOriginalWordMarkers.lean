import Lamping.Lamping.InitialWordMarkers
import Lamping.Lamping.InitialFragmentReflection
import Lamping.Lamping.InitialPathRelabelling
import Lamping.Lamping.BetaOriginalWordTransport

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- The original positive entry reads only the actual geometric input address. -/
def initialOriginalEntry (original : LTerm) (level : Nat)
    (addr : Addressing (encode level original.erase).net (boundaryAddressAt []))
    (e : Endpoint (encode level original.erase).net) : EdgeWord :=
  match initialAtomAddress addr.nodes ((encode level original.erase).net.wire e) with
  | none => []
  | some p => match original.subterm p with
    | none => []
    | some t => t.label.edgeWord

def initialOriginalWeights (original : LTerm) (level : Nat)
    (addr : Addressing (encode level original.erase).net (boundaryAddressAt []))
    (e : Endpoint (encode level original.erase).net) : EdgeWord :=
  initialOriginalEntry original level addr e ++
    EdgeWord.reverse (initialOriginalEntry original level addr
      ((encode level original.erase).net.wire e))

/-- Pure wire involution; it supplies no seed semantic or path-fold premise. -/
theorem symmetrizedOriginalWord_reversal
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (entry : Endpoint g → EdgeWord) :
    OriginalWordReversal (fun e => entry e ++ EdgeWord.reverse (entry (g.wire e))) := by
  intro e
  simp only [Pairing.involutive,EdgeWord.reverse_append,EdgeWord.reverse_reverse]

private theorem app_input {kind : Kind} {port : Port kind}
    (shape : kind=.op .app) (role : HEq port appCtx) : initialAtomInput kind port=true := by
  subst kind
  have same : port=appCtx := eq_of_heq role
  subst port;rfl

private theorem lambda_input {kind : Kind} {port : Port kind}
    (shape : kind=.op .lam) (role : HEq port (Sum.inl () : Port (.op .lam))) :
    initialAtomInput kind port=true := by
  subst kind
  have same : port=(Sum.inl () : Port (.op .lam)) := eq_of_heq role
  subst port;rfl

private theorem binding_none {kind : Kind} {port : Port kind}
    (shape : kind=.op .lam) (role : HEq port lamBind) (address : Path) :
    syntaxPortAddress kind port address=none := by
  subst kind
  have same : port=lamBind := eq_of_heq role
  subst port;rfl

section Terminal
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm} {position : Path}

private theorem app_terminal_marker {target : Endpoint g} {origin : Label}
    (actual : SourcePortRealizes original g root (.appContext origin) target) (nodes : N → Path) :
    ∃ q,InitialMarkerAt nodes (g.wire target) q := by
  cases actual with
  | appContext lookup access word shape role finish =>
    unfold InitialMarkerAt
    rw [Pairing.involutive]
    simp only [initialAtomAddress,app_input shape role,ite_true]
    exact ⟨_,rfl⟩
  | departure lookup role parent word ports finish => cases role

private theorem lambda_terminal_marker {target : Endpoint g} {origin : Label}
    (actual : SourcePortRealizes original g root (.lamContext origin) target) (nodes : N → Path) :
    ∃ q,InitialMarkerAt nodes (g.wire target) q := by
  cases actual with
  | lamContext lookup access word shape role finish =>
    unfold InitialMarkerAt
    rw [Pairing.involutive]
    simp only [initialAtomAddress,lambda_input shape role,ite_true]
    exact ⟨_,rfl⟩
  | departure lookup role parent word ports finish => cases role

private theorem no_free_terminal {target : Endpoint g} {index : Nat}
    (actual : SourcePortRealizes original g root (.free index) target) : False := by
  cases actual with
  | departure lookup role parent word ports finish => cases role

private theorem binder_terminal_none {target : Endpoint g} {origin : Label}
    (actual : SourcePortRealizes original g root (.lamBind origin) target)
    {boundary : B → Option Path} (addr : Addressing g boundary) :
    endpointAddress g addr.nodes boundary addr.vertices (g.wire target)=none := by
  cases actual with
  | binding lookup access word shape contextRole bindingRole finish =>
    rw [addr.wiring]
    exact binding_none shape bindingRole _
  | departure lookup role parent word ports finish => cases role

/-- Private actual terminal split. The variable branch returns a lexical
binder occurrence as well as NONE; no marker conclusion is a caller field. -/
private theorem actual_terminal_split
    (fragment : OccurrenceFragment original g root position)
    {boundary : B → Option Path} (addr : Addressing g boundary) :
    (∃ q,InitialMarkerAt addr.nodes (g.wire fragment.fragment.toEndpoint) q) ∨
    (endpointAddress g addr.nodes boundary addr.vertices (g.wire fragment.fragment.toEndpoint)=none ∧
      ∃ varLabel index origin parent tail body,
        fragment.term=.var varLabel index ∧ sourceBinder fragment.environment index=.lamBind origin ∧
        position=parent++(.body::tail) ∧ original.subterm parent=some (.lam origin body) ∧ index=binderDepth tail) := by
  rcases fragment with ⟨term,env,context,occurrence,physical⟩
  cases term with
  | app origin fn arg =>
    have terminal : SourcePortRealizes original g root (.appContext origin) physical.toEndpoint := by
      simpa only [sourceEdge] using physical.toRealizes
    exact Or.inl (app_terminal_marker terminal addr.nodes)
  | lam origin body =>
    have terminal : SourcePortRealizes original g root (.lamContext origin) physical.toEndpoint := by
      simpa only [sourceEdge] using physical.toRealizes
    exact Or.inl (lambda_terminal_marker terminal addr.nodes)
  | var varLabel index =>
    have terminal : SourcePortRealizes original g root (sourceBinder env index)
        physical.toEndpoint := by
      simpa only [sourceEdge] using physical.toRealizes
    cases entry : env[index]? with
    | none =>
      have free : sourceBinder env index=.free (index-env.length) := by
        simp only [sourceBinder,entry]
      rw [free] at terminal
      exact False.elim (no_free_terminal terminal)
    | some origin =>
      have bound : sourceBinder env index=.lamBind origin := by simp only [sourceBinder,entry]
      obtain ⟨parent,tail,body,split,lookup,depth⟩ := occurrence.sourceBinder_occurrence bound
      rw [bound] at terminal
      exact Or.inr ⟨binder_terminal_none terminal addr,
        varLabel,index,origin,parent,tail,body,rfl,bound,split,lookup,depth⟩
end Terminal

/-- For the original encode, a real whole assignment restricts to the SAME
fragment seam and supplies its unique marker ordinal at the literal occurrence.
There is no Closed, INIT, marker oracle, or label-to-current-coordinate premise. -/
theorem OccurrenceFragment.initial_unique_marker_given_assignment
    {original : LTerm} {level : Nat} {position : Path}
    (fragment : OccurrenceFragment original (encode level original.erase).net (.inl ()) position)
    (addr : Addressing (encode level original.erase).net (boundaryAddressAt []))
    {a b : Context}
    (whole : Labelling (encode level original.erase).net fragment.fragment.access.val a b) :
    ∃ middle,
      (fragment.fragment.before=[] ∧ middle=a ∨
        Labelling (encode level original.erase).net fragment.fragment.before a middle) ∧
      InitialLabelling (g:=(encode level original.erase).net) fragment.fragment.segments middle b ∧
      ∃ i : Fin fragment.fragment.segments.length,
        InitialMarkerAt addr.nodes fragment.fragment.segments[i] position ∧
        ∀ j : Fin fragment.fragment.segments.length,∀ q,
          InitialMarkerAt addr.nodes fragment.fragment.segments[j] q → j=i ∧ q=position := by
  obtain ⟨middle,prefixEvidence,suffix⟩ := fragment.fragment.assignments a b whole
  have initial := encode_root_initial original.erase level fragment.fragment.access.val
    fragment.fragment.access.property.2.1 whole
  rw [fragment.fragment.literal] at initial
  have nonempty : fragment.fragment.segments≠[] := by
    intro empty
    have head := fragment.fragment.start
    rw [empty] at head
    cases head
  obtain ⟨initialMiddle,initialSuffix⟩ := initial.suffix nonempty
  have sameMiddle : middle=initialMiddle := suffix.reverse.output_unique initialSuffix.labelling.reverse
  rw [←sameMiddle] at initialSuffix
  have start := fragment.initial_start_address addr
  rcases actual_terminal_split fragment addr with ⟨q,marked⟩ | ⟨none,_lexicalBinder⟩
  · obtain ⟨i,_ordinal,_endpoint,hit,unique⟩ := initialSuffix.final_marker addr
      fragment.fragment.fromEndpoint ((encode level original.erase).net.wire fragment.fragment.toEndpoint)
      fragment.fragment.start fragment.fragment.finish position q start marked fragment.fragment.emptyWord
    exact ⟨middle,prefixEvidence,initialSuffix,i,hit,unique⟩
  · obtain ⟨i,hit,unique⟩ := initialSuffix.drop_marker addr
      fragment.fragment.fromEndpoint ((encode level original.erase).net.wire fragment.fragment.toEndpoint)
      fragment.fragment.start fragment.fragment.finish position start none fragment.fragment.emptyWord
    exact ⟨middle,prefixEvidence,initialSuffix,i,hit,unique⟩

#print axioms symmetrizedOriginalWord_reversal
#print axioms OccurrenceFragment.initial_unique_marker_given_assignment
end Lamping.AG

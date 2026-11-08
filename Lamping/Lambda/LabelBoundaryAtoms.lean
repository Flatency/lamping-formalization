import Lamping.Lambda.LabelRouteWords
namespace Lamping.Lambda.Labelled

def Label.firstAtom : Label → Option Nat
  | .single (.atom n) | .cons (.atom n) _ => some n
  | _ => none

def Label.lastAtom : Label → Option Nat
  | .single (.atom n) => some n
  | .single _ => none
  | .cons _ a => a.lastAtom

theorem Label.firstAtom_concat (a b : Label) : (a.concat b).firstAtom=a.firstAtom := by
  cases a with
  | single l => cases l <;> rfl
  | cons l a => cases l <;> rfl

theorem Label.lastAtom_concat : ∀ (a b : Label), (a.concat b).lastAtom=b.lastAtom
  | .single _,_ => rfl
  | .cons _ a,b => lastAtom_concat a b

theorem SourceRoute.first_atom (route : SourceRoute edges start l finish) :
    ∃ n e, l.firstAtom=some n ∧ e∈edges ∧ e.atom=Label.atom n ∧ e.fromPort=start := by
  induction route with
  | atom member atomic => exact ⟨_,_,rfl,member,atomic,rfl⟩
  | over _ _ _ head _ _ =>
    obtain ⟨n,e,hf,he,ha,hs⟩ := head
    exact ⟨n,e,by simpa only [Label.firstAtom_concat] using hf,he,ha,hs⟩
  | under _ _ _ head _ _ =>
    obtain ⟨n,e,hf,he,ha,hs⟩ := head
    exact ⟨n,e,by simpa only [Label.firstAtom_concat] using hf,he,ha,hs⟩

theorem SourceRoute.last_atom (route : SourceRoute edges start l finish) :
    ∃ n e, l.lastAtom=some n ∧ e∈edges ∧ e.atom=Label.atom n ∧ e.toPort=finish := by
  induction route with
  | atom member atomic => exact ⟨_,_,rfl,member,atomic,rfl⟩
  | over _ _ _ _ _ tail =>
    obtain ⟨n,e,hf,he,ha,hs⟩ := tail
    exact ⟨n,e,by simpa only [Label.lastAtom_concat] using hf,he,ha,hs⟩
  | under _ _ _ _ _ tail =>
    obtain ⟨n,e,hf,he,ha,hs⟩ := tail
    exact ⟨n,e,by simpa only [Label.lastAtom_concat] using hf,he,ha,hs⟩

private theorem binder_not_context (env : List Label) (i : Nat) (l : Label) :
    sourceBinder env i≠.lamContext l ∧ sourceBinder env i≠.appContext l := by
  unfold sourceBinder
  split <;> constructor <;> intro h <;> cases h

/-- A source node's context edge is its own original atomic label; variable
binding edges cannot masquerade as node-context edges. -/
theorem sourceEdges_to_lam (t : LTerm) (member : e∈sourceEdges env ctx t)
    (target : e.toPort=.lamContext l) : e.atom=l := by
  induction t generalizing env ctx with
  | var a i =>
    simp only [sourceEdges,List.mem_singleton] at member
    cases member
    exact False.elim ((binder_not_context env i l).1 target)
  | lam a b hb =>
    simp only [sourceEdges,List.mem_cons] at member
    rcases member with rfl | member
    · exact SourcePort.lamContext.inj target
    · exact hb member
  | app a f b hf hb =>
    simp only [sourceEdges,List.mem_cons,List.mem_append] at member
    rcases member with rfl | member | member
    · cases target
    · exact hf member
    · exact hb member

theorem sourceEdges_to_app (t : LTerm) (member : e∈sourceEdges env ctx t)
    (target : e.toPort=.appContext l) : e.atom=l := by
  induction t generalizing env ctx with
  | var a i =>
    simp only [sourceEdges,List.mem_singleton] at member
    cases member
    exact False.elim ((binder_not_context env i l).2 target)
  | lam a b hb =>
    simp only [sourceEdges,List.mem_cons] at member
    rcases member with rfl | member
    · cases target
    · exact hb member
  | app a f b hf hb =>
    simp only [sourceEdges,List.mem_cons,List.mem_append] at member
    rcases member with rfl | member | member
    · exact SourcePort.appContext.inj target
    · exact hf member
    · exact hb member

/-- Every route to an original lambda principal port ends with that lambda's
original atom, even if its current label has acquired a compound prefix. -/
theorem SourceRoute.lam_last_atom
    (route : SourceRoute (sourceEdges env ctx t) start l (.lamContext origin)) :
    ∃ n, l.lastAtom=some n ∧ origin=Label.atom n := by
  obtain ⟨n,e,last,member,atomic,target⟩ := route.last_atom
  exact ⟨n,last,(sourceEdges_to_lam t member target).symm.trans atomic⟩

theorem SourceRoute.app_last_atom
    (route : SourceRoute (sourceEdges env ctx t) start l (.appContext origin)) :
    ∃ n, l.lastAtom=some n ∧ origin=Label.atom n := by
  obtain ⟨n,e,last,member,atomic,target⟩ := route.last_atom
  exact ⟨n,last,(sourceEdges_to_app t member target).symm.trans atomic⟩
end Lamping.Lambda.Labelled



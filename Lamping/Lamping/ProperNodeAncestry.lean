import Lamping.Lamping.GlobalGraphSteps
namespace Lamping.AG
open Graph

/-- The real passive copy of an action RHS. Fresh active controls are not
proper-node ancestors. Fan branches remain distinct witnesses. -/
inductive RightPassiveCopy : (s : Schema) → s.right.N → Prop where
  | fan (f : Op) (i j : Nat) (lt : i<j) (branch : Bool) :
      RightPassiveCopy (.fanAction f i j lt) (.inl branch)
  | cro (f : Op) (i j : Nat) (lt : i<j) :
      RightPassiveCopy (.croAction f i j lt) (.inl ())
  | bra (f : Op) (i j : Nat) (lt : i<j) :
      RightPassiveCopy (.braAction f i j lt) (.inl ())

def Schema.passiveCopyIndex : Schema → Nat
  | .croAction _ _ j _ => j-1
  | .braAction _ _ j _ => j+1
  | s => s.high

theorem RightPassiveCopy.target_label {s child} (copy : RightPassiveCopy s child) :
    s.right.net.label child=label s.passive s.passiveCopyIndex := by
  cases copy <;> rfl

/-- Every proper RHS node is one of the actual passive copies. Beta and
all cancellations have no RHS nodes; fresh action controls fail the kind. -/
theorem right_passive_copy_of_proper (s : Schema) (child : s.right.N)
    (proper : op=.app ∨op=.lam) (kind : (s.right.net.label child).sort=.op op) :
    RightPassiveCopy s child := by
  cases s with
  | beta i => exact nomatch child
  | fanCancel i => exact nomatch child
  | croCancel i => exact nomatch child
  | braCancel i => exact nomatch child
  | fanAction f i j lt =>
    cases child with
    | inl branch => exact .fan f i j lt branch
    | inr aux => rcases proper with rfl |rfl <;> cases kind
  | croAction f i j lt =>
    cases child with
    | inl singleton => cases singleton; exact .cro f i j lt
    | inr aux => rcases proper with rfl |rfl <;> cases kind
  | braAction f i j lt =>
    cases child with
    | inl singleton => cases singleton; exact .bra f i j lt
    | inr aux => rcases proper with rfl |rfl <;> cases kind

section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}

/-- Canonical physical parenthood is exactly retained carrier identity or
one real passive-copy occurrence at this SAME site. -/
inductive SiteNodeParent (site : PathSite s kept (B:=B) (W:=W) (V:=V)) :
    K⊕(Unit⊕Unit) → K⊕s.right.N → Prop where
  | kept (node : K) : SiteNodeParent site (.inl node) (.inl node)
  | copied (child : s.right.N) (copy : RightPassiveCopy s child) :
      SiteNodeParent site (.inr (.inr ())) (.inr child)

theorem SiteNodeParent.same_sort {site : PathSite s kept (B:=B) (W:=W) (V:=V)}
    {parent child} (origin : SiteNodeParent site parent child) :
    (site.net.label parent).sort=(site.reduce.label child).sort := by
  cases origin with
  | kept => rfl
  | copied child copy => cases copy <;> rfl

/-- The classified parents preserve exact canonical labels. This is not
an assertion of injectivity: both fan branches have the same parent. -/
theorem SiteNodeParent.labels {site : PathSite s kept (B:=B) (W:=W) (V:=V)}
    {parent child} (origin : SiteNodeParent site parent child) :
    (∃ node,parent=.inl node ∧child=.inl node ∧
      site.net.label parent=kept node ∧site.reduce.label child=kept node) ∨
    (parent=.inr (.inr ()) ∧∃ rhs,child=.inr rhs ∧RightPassiveCopy s rhs ∧
      site.net.label parent=label s.passive s.high ∧
      site.reduce.label child=label s.passive s.passiveCopyIndex) := by
  cases origin with
  | kept node => exact .inl ⟨node,rfl,rfl,rfl,rfl⟩
  | copied child copy => exact .inr ⟨rfl,child,rfl,copy,rfl,copy.target_label⟩

theorem PathSite.proper_node_parent (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    (child : K⊕s.right.N) (proper : op=.app ∨op=.lam)
    (kind : (site.reduce.label child).sort=.op op) :
    ∃ parent,SiteNodeParent site parent child ∧(site.net.label parent).sort=.op op := by
  cases child with
  | inl node => exact ⟨.inl node,.kept node,kind⟩
  | inr child =>
    have copy := right_passive_copy_of_proper s child proper kind
    have origin : SiteNodeParent site (.inr (.inr ())) (.inr child) := .copied child copy
    exact ⟨_,origin,origin.same_sort.trans kind⟩
end

section
variable {B : Type} [FiniteNames B]
/-- A physical parent stores the real site, both boundary-fixing carrier
isomorphisms, the classified canonical nodes, and their actual node equations. -/
inductive PhysicalNodeParent (s : Schema) (g h : ActualNet B) : g.Node → h.Node → Prop where
  | atSite {K W V : Type} [FiniteNames K] [FiniteNames W] [FiniteNames V]
      (kept : K → Label signature) (site : PathSite s kept (B:=B) (W:=W) (V:=V))
      (sourceIso : NetIso g.net site.net) (targetIso : NetIso site.reduce h.net)
      (parent : g.Node) (child : h.Node) (oldCanonical : K⊕(Unit⊕Unit)) (newCanonical : K⊕s.right.N)
      (sourceAt : sourceIso.nodes parent=oldCanonical)
      (targetAt : targetIso.nodes newCanonical=child)
      (origin : SiteNodeParent site oldCanonical newCanonical) :
      PhysicalNodeParent s g h parent child

theorem PhysicalNodeParent.same_sort {s g h parent child}
    (origin : PhysicalNodeParent (B:=B) s g h parent child) :
    (g.net.label parent).sort=(h.net.label child).sort := by
  cases origin with
  | atSite kept site before after parent child old new sourceAt targetAt actual =>
    have oldLabel : site.net.label old=g.net.label parent := by
      rw [←sourceAt];exact before.labels parent
    have newLabel : h.net.label child=site.reduce.label new := by
      rw [←targetAt];exact after.labels new
    exact (congrArg Graph.Label.sort oldLabel).symm.trans
      (actual.same_sort.trans (congrArg Graph.Label.sort newLabel).symm)

/-- Classification is constructed from the supplied actual graph step.
Neither root visibility nor any semantic invariant is required. -/
theorem GraphStep.proper_node_parent {s : Schema} {g h : ActualNet B}
    (step : GraphStep s g h) (child : h.Node) (proper : op=.app ∨op=.lam)
    (kind : (h.net.label child).sort=.op op) :
    ∃ parent,PhysicalNodeParent s g h parent child ∧(g.net.label parent).sort=.op op := by
  cases step with
  | atSite kept site before after =>
    let current := after.nodes.invFun child
    have targetAt : after.nodes current=child := after.nodes.right_inv child
    have currentKind : (site.reduce.label current).sort=.op op := by
      rw [←after.labels current,targetAt];exact kind
    obtain ⟨old,origin,oldKind⟩ := site.proper_node_parent current proper currentKind
    let parent := before.nodes.invFun old
    have sourceAt : before.nodes parent=old := before.nodes.right_inv old
    have witness : PhysicalNodeParent s _ _ parent child :=
      .atSite kept site before after parent child old current sourceAt targetAt origin
    exact ⟨parent,witness,witness.same_sort.trans kind⟩

/-- Finite actual carrier ancestry. Every rewrite constructor retains its
real physical-parent proof; zero steps retain the actual final isomorphism. -/
inductive ProperNodeAncestry : (g h : ActualNet B) → List Schema → g.Node → h.Node → Prop where
  | iso {g h : ActualNet B} (same : NetIso g.net h.net) (parent : g.Node) :
      ProperNodeAncestry g h [] parent (same.nodes parent)
  | cons {g h k : ActualNet B} {s : Schema} {ss : List Schema}
      {parent : g.Node} {middle : h.Node} {child : k.Node}
      (first : PhysicalNodeParent s g h parent middle)
      (tail : ProperNodeAncestry h k ss middle child) :
      ProperNodeAncestry g k (s::ss) parent child

theorem ProperNodeAncestry.same_sort {g h ss parent child}
    (origin : ProperNodeAncestry (B:=B) g h ss parent child) :
    (g.net.label parent).sort=(h.net.label child).sort := by
  induction origin with
  | iso same parent => exact (congrArg Graph.Label.sort (same.labels parent)).symm
  | cons first _ ih => exact first.same_sort.trans ih

/-- Every actual target proper node has a finite actual ancestry to a source
proper node along this trace, even in components invisible from the root. -/
theorem GraphTrace.proper_node_ancestry {g h : ActualNet B} {ss : List Schema}
    (trace : GraphTrace g h ss) (child : h.Node) (proper : op=.app ∨op=.lam)
    (kind : (h.net.label child).sort=.op op) :
    ∃ parent,ProperNodeAncestry g h ss parent child ∧(g.net.label parent).sort=.op op := by
  induction trace with
  | iso same =>
    let parent := same.nodes.invFun child
    have atParent : same.nodes parent=child := same.nodes.right_inv child
    have witness : ProperNodeAncestry _ _ [] parent child := by
      rw [←atParent];exact .iso same parent
    exact ⟨parent,witness,witness.same_sort.trans kind⟩
  | cons step tail ih =>
    obtain ⟨middle,remaining,middleKind⟩ := ih child kind
    obtain ⟨parent,first,parentKind⟩ := step.proper_node_parent middle proper middleKind
    exact ⟨parent,.cons first remaining,parentKind⟩
end
end Lamping.AG


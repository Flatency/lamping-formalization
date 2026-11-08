import Lamping.Lambda.LabelAncestorBinderProtection
namespace Lamping.Lambda.Labelled

/- Letters already inserted by the one common beta step. Outer old atoms
exclude the removed lambda atom; every existing bar is its literal singleton. -/
mutual
  def Label.HeadFlat (a : Nat) : Label → Prop
    | .single l => l.HeadFlat a
    | .cons l rest => l.HeadFlat a ∧ rest.HeadFlat a
  def Letter.HeadFlat (a : Nat) : Letter → Prop
    | .atom n => n≠a
    | .over l | .under l => l=Label.atom a
end

theorem Label.headFlat_concat (a) : ∀ x y : Label,
    (x.concat y).HeadFlat a ↔ x.HeadFlat a ∧ y.HeadFlat a
  | .single _,_ => Iff.rfl
  | .cons l rest,y => by simp [Label.concat,Label.HeadFlat,headFlat_concat,and_assoc]

theorem Label.HeadFlat.ne_head (flat : l.HeadFlat a) : l≠Label.atom a := by
  intro equal
  rw [equal] at flat
  exact flat rfl

namespace LTerm

def HeadFlat (a : Nat) : LTerm → Prop
  | .var l _ => l.HeadFlat a
  | .lam l body => l.HeadFlat a ∧ body.HeadFlat a
  | .app l fn arg => l.HeadFlat a ∧ fn.HeadFlat a ∧ arg.HeadFlat a

theorem headFlat_iff (a) (t : LTerm) : t.HeadFlat a ↔ ∀ l∈t.labels,l.HeadFlat a := by
  induction t with
  | var => simp [HeadFlat,labels]
  | lam _ _ ih => simp [HeadFlat,labels,ih]
  | app _ _ _ hf ha => simp [HeadFlat,labels,hf,ha,or_imp,forall_and]

theorem HeadFlat.rename {t : LTerm} (flat : t.HeadFlat a) (rho) : (t.rename rho).HeadFlat a := by
  induction t generalizing rho with
  | var => exact flat
  | lam _ _ ih => exact ⟨flat.1,ih flat.2 _⟩
  | app _ _ _ hf ha => exact ⟨flat.1,hf flat.2.1 _,ha flat.2.2 _⟩

theorem HeadFlat.prepend {t : LTerm} {l : Label} (flat : t.HeadFlat a) (word : l.HeadFlat a) : (t.prepend l).HeadFlat a := by
  cases t with
  | var => exact (Label.headFlat_concat _ _ _).mpr ⟨word,flat⟩
  | lam => exact ⟨(Label.headFlat_concat _ _ _).mpr ⟨word,flat.1⟩,flat.2⟩
  | app => exact ⟨(Label.headFlat_concat _ _ _).mpr ⟨word,flat.1⟩,flat.2⟩

def SubValue.HeadFlat (a : Nat) : SubValue → Prop
  | .keep _ => True
  | .put t => t.HeadFlat a

theorem HeadFlat.subst {t : LTerm} {sigma : Nat → SubValue} (flat : t.HeadFlat a) (values : ∀ i,(sigma i).HeadFlat a) :
    (t.subst sigma).HeadFlat a := by
  induction t generalizing sigma with
  | var l i =>
    cases put : sigma i with
    | keep j => simpa only [LTerm.subst,put,HeadFlat] using flat
    | put value =>
      have safe : value.HeadFlat a := by simpa only [put,SubValue.HeadFlat] using values i
      simpa only [LTerm.subst,put] using safe.prepend flat
  | app _ _ _ hf ha => exact ⟨flat.1,hf flat.2.1 values,ha flat.2.2 values⟩
  | lam _ _ ih =>
    refine ⟨flat.1,ih flat.2 ?_⟩
    intro i
    cases i with
    | zero => trivial
    | succ i =>
      cases put : sigma i with
      | keep j => simp [lift,put,SubValue.HeadFlat]
      | put value =>
        have safe : value.HeadFlat a := by simpa only [put,SubValue.HeadFlat] using values i
        simpa only [lift,put,SubValue.HeadFlat] using safe.rename Nat.succ

theorem HeadFlat.contract {body argument : LTerm} (bodyFlat : body.HeadFlat a)
    (argFlat : argument.HeadFlat a) (betaFlat : beta.HeadFlat a) :
    (contract beta (Label.atom a) body argument).HeadFlat a := by
  apply HeadFlat.prepend
  · apply bodyFlat.subst
    intro i
    cases i with
    | zero => exact argFlat.prepend (show (Label.atom a).under.HeadFlat a from rfl)
    | succ i => trivial
  · exact (Label.headFlat_concat _ _ _).mpr ⟨betaFlat,rfl⟩
end LTerm

private theorem initial_headFlat (initial : INIT t) (absent : Label.atom a∉t.labels) : t.HeadFlat a := by
  apply (LTerm.headFlat_iff _ _).mpr
  intro l member
  obtain ⟨n,atomic⟩ := initial.1 l member
  rw [atomic]
  intro same
  exact absent ((atomic.trans (congrArg Label.atom same)) ▸ member)

/-- The complete actual single-beta target has only old outer atoms and
literal bars carrying the contracted head atom, even under real contexts. -/
theorem StepAt.headFlat (step : StepAt p t u) (initial : INIT t)
    (degree : t.degreeAt p=some (Label.atom a)) : u.HeadFlat a := by
  induction step with
  | root beta alpha body argument =>
    have equal : alpha=Label.atom a := Option.some.inj degree
    cases equal
    have bodyInitial : INIT body := initial.subterm (p := [.fn,.body]) (by simp [LTerm.subterm])
    have argInitial : INIT argument := initial.subterm (p := [.arg]) (by simp [LTerm.subterm])
    have lambdaInitial : INIT (.lam (Label.atom a) body) := initial.subterm (p := [.fn]) (by simp [LTerm.subterm])
    have bodyAbsent : Label.atom a∉body.labels := (List.nodup_cons.mp lambdaInitial.2).1
    have argAbsent : Label.atom a∉argument.labels := by
      intro member
      exact (List.nodup_append.mp (List.nodup_cons.mp initial.2).2).2.2 _ List.mem_cons_self _ member rfl
    have betaFlat : beta.HeadFlat a := by
      obtain ⟨n,atomic⟩ := initial.1 beta List.mem_cons_self
      rw [atomic]
      intro same
      have betaEq := atomic.trans (congrArg Label.atom same)
      exact (List.nodup_cons.mp initial.2).1 (betaEq.symm ▸ List.mem_append_left _ List.mem_cons_self)
    exact (initial_headFlat bodyInitial bodyAbsent).contract (initial_headFlat argInitial argAbsent) betaFlat
  | @fn p fn fn' beta argument actual ih =>
    have fnInitial : INIT fn := initial.subterm (p := [.fn]) (by simp [LTerm.subterm])
    obtain ⟨body,atLambda⟩ := LTerm.degreeAt_lambda (t := fn) degree
    have member : Label.atom a∈fn.labels := LTerm.label_mem_of_subterm atLambda
    have argAbsent : Label.atom a∉argument.labels := by
      intro other
      exact (List.nodup_append.mp (List.nodup_cons.mp initial.2).2).2.2 _ member _ other rfl
    have betaFlat : beta.HeadFlat a := by
      obtain ⟨n,atomic⟩ := initial.1 beta List.mem_cons_self
      rw [atomic]
      intro same
      exact (List.nodup_cons.mp initial.2).1 ((atomic.trans (congrArg Label.atom same)).symm ▸ List.mem_append_left _ member)
    exact ⟨betaFlat,ih fnInitial degree,initial_headFlat
      (initial.subterm (p := [.arg]) (by simp [LTerm.subterm])) argAbsent⟩
  | @arg p argument argument' beta fn actual ih =>
    have argInitial : INIT argument := initial.subterm (p := [.arg]) (by simp [LTerm.subterm])
    obtain ⟨body,atLambda⟩ := LTerm.degreeAt_lambda (t := argument) degree
    have member : Label.atom a∈argument.labels := LTerm.label_mem_of_subterm atLambda
    have fnAbsent : Label.atom a∉fn.labels := by
      intro other
      exact (List.nodup_append.mp (List.nodup_cons.mp initial.2).2).2.2 _ other _ member rfl
    have betaFlat : beta.HeadFlat a := by
      obtain ⟨n,atomic⟩ := initial.1 beta List.mem_cons_self
      rw [atomic]
      intro same
      exact (List.nodup_cons.mp initial.2).1 ((atomic.trans (congrArg Label.atom same)).symm ▸ List.mem_append_right _ member)
    exact ⟨betaFlat,initial_headFlat (initial.subterm (p := [.fn]) (by simp [LTerm.subterm])) fnAbsent,
      ih argInitial degree⟩
  | @body p body body' alpha actual ih =>
    have bodyInitial : INIT body := initial.subterm (p := [.body]) (by simp [LTerm.subterm])
    obtain ⟨b,atLambda⟩ := LTerm.degreeAt_lambda (t := body) degree
    have member : Label.atom a∈body.labels := LTerm.label_mem_of_subterm atLambda
    have different : alpha≠Label.atom a :=
      fun equal => (List.nodup_cons.mp initial.2).1 (equal.symm ▸ member)
    obtain ⟨n,atomic⟩ := initial.1 alpha List.mem_cons_self
    have distinct : n≠a := fun equal => different (atomic.trans (congrArg Label.atom equal))
    have alphaFlat : alpha.HeadFlat a := Eq.mpr (congrArg (fun l => l.HeadFlat a) atomic) distinct
    exact ⟨alphaFlat,ih bodyInitial degree⟩

/-- A valid local label cannot substitute to the removed bare head atom.
The finite support condition excludes unconstrained fallback coordinates. -/
theorem Label.relabel_ne_head {l : Label} {region : Nat → Prop} {s : Nat → Label} (images : ∀ n,region n → s n≠Label.atom a)
    (support : l.Supported region) : l.relabel s≠Label.atom a := by
  cases l with
  | single letter =>
    cases letter with
    | atom n => exact images n support
    | over d => intro equal; cases equal
    | under d => intro equal; cases equal
  | cons letter rest =>
    intro equal
    have lengths := congrArg Label.length equal
    change ((letter.relabel s).concat (rest.relabel s)).length=1 at lengths
    rw [Label.length_concat] at lengths
    have leftPositive := Label.length_pos (letter.relabel s)
    have rightPositive := Label.length_pos (rest.relabel s)
    omega

theorem StepAt.basis_images_headFlat (step : StepAt p t u) (initial : INIT t)
    (degree : t.degreeAt p=some (Label.atom a)) (member : Label.atom n∈(initLabels u.erase).labels) :
    (initialRelabelling u 0 n).HeadFlat a := by
  have flat := step.headFlat initial degree
  apply (LTerm.headFlat_iff _ _).mp flat
  apply initialRelabelling_mem u 0 n (Nat.zero_le n)
  simpa only [Nat.zero_add] using LTerm.basis_atom_bound u member

/-- A bar is a genuine post-head separator exactly when its payload is not
the literal removed singleton atom. Old outer atoms stay inside image blocks. -/
def Letter.headSeparator (a : Nat) : Letter → Bool
  | .atom _ => false
  | .over d | .under d => decide (d≠Label.atom a)

def headGroups (a : Nat) : List Letter → List (Sum (List Letter) Letter)
  | [] => []
  | letter::rest =>
      if letter.headSeparator a then .inr letter::headGroups a rest else
      match headGroups a rest with
      | .inl block::groups => .inl (letter::block)::groups
      | groups => .inl [letter]::groups

private theorem Letter.HeadFlat.separator_false {l : Letter} (flat : l.HeadFlat a) : l.headSeparator a=false := by
  cases l with
  | atom => rfl
  | over d => simp only [Letter.HeadFlat] at flat; simp [Letter.headSeparator,flat]
  | under d => simp only [Letter.HeadFlat] at flat; simp [Letter.headSeparator,flat]

/-- One actual initial-edge image forms exactly one complete opaque block. -/
theorem Label.HeadFlat.headGroups : ∀ {l : Label},l.HeadFlat a → headGroups a l.letters=[.inl l.letters]
  | .single letter,flat => by
    simp [Label.letters,Lamping.Lambda.Labelled.headGroups,Letter.HeadFlat.separator_false flat]
  | .cons letter rest,flat => by
    simp [Label.letters,Lamping.Lambda.Labelled.headGroups,Letter.HeadFlat.separator_false flat.1,Label.HeadFlat.headGroups flat.2]
private theorem headGroups_separator_append (separator : bar.headSeparator a=true) :
    ∀ xs ys,headGroups a (xs++bar::ys)=headGroups a xs++(.inr bar::headGroups a ys) := by
  intro xs
  induction xs with
  | nil => intro ys; simp [headGroups,separator]
  | cons letter rest ih =>
    intro ys
    simp only [List.cons_append,headGroups,ih]
    by_cases sep : letter.headSeparator a=true
    · simp [sep]
    · have notSep : letter.headSeparator a=false := Bool.eq_false_iff.mpr sep
      simp only [notSep,Bool.false_eq_true,ite_false]
      cases groups : headGroups a rest with
      | nil => rfl
      | cons first rest => cases first <;> rfl

theorem Label.letters_concat : ∀ x y : Label,(x.concat y).letters=x.letters++y.letters
  | .single _,_ => rfl
  | .cons letter rest,y => by simp [Label.concat,Label.letters,letters_concat]

/-- Exact one-level local word after edge-image expansion: atom blocks keep
complete image words, while each new bar keeps its complete substituted payload. -/
def Label.expansionTokens (s : Nat → Label) (l : Label) : List (Sum (List Letter) Letter) :=
  l.letters.map (fun letter => match letter with
    | .atom n => .inl (s n).letters
    | .over d => .inr (.over (d.relabel s))
    | .under d => .inr (.under (d.relabel s)))

theorem Label.expansionTokens_concat (s) (x y : Label) :
    (x.concat y).expansionTokens s=x.expansionTokens s++y.expansionTokens s := by
  simp only [expansionTokens,letters_concat,List.map_append]

/-- Deterministic full image-block alignment. Alternation prevents adjacent
local atom images from merging; no runtime bar can be mistaken for a head bar. -/
theorem Label.Alternating.relabel_headGroups {l : Label} {region : Nat → Prop} {s : Nat → Label} (alternating : l.Alternating)
    (images : ∀ n,region n → (s n).HeadFlat a) (support : l.Supported region) :
    headGroups a (l.relabel s).letters=l.expansionTokens s := by
  revert support
  induction alternating with
  | atom n =>
    intro support
    exact (images n support).headGroups
  | @over x d y left middle right hl hm hr =>
    intro support
    obtain ⟨prefixSupport,rightSupport⟩ := (Label.supported_concat _ _ _).mp support
    obtain ⟨leftSupport,middleSupport⟩ := (Label.supported_concat _ _ _).mp prefixSupport
    have different := Label.relabel_ne_head (l := d) (fun n member => (images n member).ne_head) middleSupport
    have separator : (Letter.over (d.relabel s)).headSeparator a=true := by simp [Letter.headSeparator,different]
    simp only [Label.relabel_concat,Label.relabel_over,Label.letters_concat,Label.expansionTokens_concat]
    simp only [Label.over,Label.letters,Label.expansionTokens,List.map_cons,List.map_nil,
      List.singleton_append,List.append_assoc]
    rw [headGroups_separator_append separator,hl leftSupport,hr rightSupport]
    rfl
  | @under x d y left middle right hl hm hr =>
    intro support
    obtain ⟨prefixSupport,rightSupport⟩ := (Label.supported_concat _ _ _).mp support
    obtain ⟨leftSupport,middleSupport⟩ := (Label.supported_concat _ _ _).mp prefixSupport
    have different := Label.relabel_ne_head (l := d) (fun n member => (images n member).ne_head) middleSupport
    have separator : (Letter.under (d.relabel s)).headSeparator a=true := by simp [Letter.headSeparator,different]
    simp only [Label.relabel_concat,Label.relabel_under,Label.letters_concat,Label.expansionTokens_concat]
    simp only [Label.under,Label.letters,Label.expansionTokens,List.map_cons,List.map_nil,
      List.singleton_append,List.append_assoc]
    rw [headGroups_separator_append separator,hl leftSupport,hr rightSupport]
    rfl
/-- Actual local INIT coordinates recover every whole atomic image block
and every runtime separator from the unchanged global final degree. -/
theorem StepAt.local_degree_outer_alignment (head : StepAt p t u) (initial : INIT t)
    (headDegree : t.degreeAt p=some (Label.atom a))
    (global : History ps u v) (basis : History ps (initLabels u.erase) z)
    (degree : v.degreeAt q=some l) (basisDegree : z.degreeAt q=some localLabel) :
    headGroups a l.letters=localLabel.expansionTokens (initialRelabelling u 0) := by
  obtain ⟨body,lookup⟩ := LTerm.degreeAt_lambda basisDegree
  have alternating := basis.generated_label_alternating (init_is_INIT _) (LTerm.label_mem_of_subterm lookup)
  have support := (LTerm.supported_iff _ _).mp (basis.supported (init_is_INIT _).supported)
    _ (LTerm.label_mem_of_subterm lookup)
  have images : ∀ n,Label.atom n∈(initLabels u.erase).labels → (initialRelabelling u 0 n).HeadFlat a :=
    fun n member => head.basis_images_headFlat initial headDegree member
  have parsed := alternating.relabel_headGroups images support
  have transported := global.local_degree_transport basis basisDegree
  have equal := Option.some.inj (transported.1.symm.trans degree)
  exact equal ▸ parsed

/-- Equal degrees after one shared beta give an exact ordered alignment of
whole local edge images and runtime bars. This is not yet atom injectivity. -/
theorem StepAt.same_degree_outer_alignment (head : StepAt p t u) (initial : INIT t)
    (headDegree : t.degreeAt p=some (Label.atom a))
    (left : History ps u v) (leftBasis : History ps (initLabels u.erase) z)
    (right : History qs u w) (rightBasis : History qs (initLabels u.erase) z')
    (leftDegree : v.degreeAt q=some l) (leftLocal : z.degreeAt q=some localLeft)
    (rightDegree : w.degreeAt r=some l) (rightLocal : z'.degreeAt r=some localRight) :
    localLeft.expansionTokens (initialRelabelling u 0)=localRight.expansionTokens (initialRelabelling u 0) := by
  exact (head.local_degree_outer_alignment initial headDegree left leftBasis leftDegree leftLocal).symm.trans
    (head.local_degree_outer_alignment initial headDegree right rightBasis rightDegree rightLocal)
end Lamping.Lambda.Labelled










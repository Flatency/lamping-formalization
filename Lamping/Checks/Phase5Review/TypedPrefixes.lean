import Lamping.Lamping.ForwardAccessDeterminism
import Lamping.Lamping.TypedTransparentPrefixes
namespace Lamping.Checks.Phase5Review.TypedPrefixes
open AG Graph
private def chain : Net signature Unit Unit Bool where
  label := fun _ => label .app 4
  wire := {
    mate := fun e => match e with
      | .inr (.inl _) => .inr (.inr (false,false))
      | .inr (.inr (false,false)) => .inr (.inl ())
      | .inr (.inr (false,true)) => .inr (.inr (true,false))
      | .inr (.inr (true,false)) => .inr (.inr (false,true))
      | .inr (.inr (true,true)) => .inl ⟨(),appCtx⟩
      | .inl ⟨_,.inr false⟩ => .inr (.inr (true,true))
      | .inl ⟨_,.inl _⟩ => .inl ⟨(),appArg⟩
      | .inl ⟨_,.inr true⟩ => .inl ⟨(),(.inl ())⟩
    involutive := by
      rintro (⟨u,p⟩ | (u | ⟨w,d⟩))
      · cases p with | inl u => rfl | inr a => cases a <;> rfl
      · rfl
      · cases w <;> cases d <;> rfl
    fixedPointFree := by
      rintro (⟨u,p⟩ | (u | ⟨w,d⟩)) same
      · cases p with | inl u => cases same | inr a => cases a <;> cases same
      · cases same
      · cases w <;> cases d <;> cases same }
private abbrev start : Endpoint chain := .inr (.inl ())
private abbrev one : Endpoint chain := .inr (.inr (false,true))
private abbrev two : Endpoint chain := .inr (.inr (true,true))
private theorem labels (a : Context) : Labelling chain [start,one,two] a a :=
  .cons (.transparent false false a) (.cons (.transparent true false a) (.single _ _))
private theorem turns : ∀ e f,(e,f)∈([start,one,two].zip [one,two]) →
    ∃ w d,chain.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)) := by
  intro e f member
  simp only [List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal <;> cases equal
  · exact ⟨false,false,rfl,rfl⟩
  · exact ⟨true,false,rfl,rfl⟩
theorem two_W_reflection (a : Context) : ∃ suffix,
    [start,one,two]=[start,one,two].dropLast++suffix ∧
    suffix.head?=some two ∧Labelling chain suffix a a :=
  (labels a).typed_transparent_prefix ⟨.app,rfl⟩ [start,one,two] (by simp) rfl turns

theorem one_W_reflection (a : Context) : ∃ suffix,
    [start,one,two]=[start,one].dropLast++suffix ∧
    suffix.head?=some one ∧Labelling chain suffix a a := by
  apply (labels a).typed_transparent_prefix ⟨.app,rfl⟩ [start,one] (by simp) rfl
  intro e f member
  simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
  cases member
  exact ⟨false,false,rfl,rfl⟩
example : ¬∃k,accessKind chain [start]=some k := by rintro ⟨k,h⟩; cases h
example : ¬∃k,accessKind chain [start,one]=some k := by rintro ⟨k,h⟩; cases h
example (a : Context) : Labelling (leftNet .cro .app 2 3)
    [.inl ⟨.inr (),(.inl ())⟩] a a := .single _ _
example : ¬∃k,accessKind (leftNet .cro .app 2 3) [.inl ⟨.inr (),(.inl ())⟩]=some k := by
  rintro ⟨k,h⟩; cases h
#print axioms two_W_reflection
#print axioms one_W_reflection
#print axioms Labelling.typed_nonterminal_departure

theorem actual_two_W_unique (a b : Context) (es : List (Endpoint chain))
    (given : Labelling chain es a b) (forward : Forward chain es)
    (head : es.head?=some start) (word : accessWord chain es=[])
    (terminal : ∃k,accessKind chain es=some k) : es=[start,one,two] := by
  have fw : Forward chain [start,one,two] :=
    .transparent false false rfl rfl (.transparent true false rfl rfl (.single _))
  exact given.forward_access_word_unique forward (labels a) fw head word terminal ⟨.app,rfl⟩

theorem proper_terminal_is_needed (a : Context) :
    Labelling chain [start] a a ∧Labelling chain [start,one] a a ∧
      Forward chain [start] ∧Forward chain [start,one] ∧
      accessWord chain [start]=accessWord chain [start,one] ∧
      ([start] : List (Endpoint chain))≠[start,one] := by
  refine ⟨.single _ _,.cons (.transparent false false a) (.single _ _),.single _,
    .transparent false false rfl rfl (.single _),rfl,?_⟩
  intro same
  have impossible := congrArg List.length same
  cases impossible
#print axioms actual_two_W_unique
#print axioms proper_terminal_is_needed
end Lamping.Checks.Phase5Review.TypedPrefixes



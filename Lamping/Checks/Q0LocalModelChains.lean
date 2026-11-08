import Lamping.Checks.Q0LocalModelFragments

namespace Lamping.Checks.Q0LocalModelChains
open AG Graph Lambda Lambda.Labelled Q0LocalModelFixture Q0LocalModelFragments

def chainCodes : AccessCode → List AccessCode
  | .root => [.leftA,.leftB,.leftL]
  | .leftA => [.leftB,.leftL]
  | .leftB => [.leftL]
  | .leftL => [.leftL]
  | .leftV => [.leftL]
  | .leftJ => [.leftJ,.leftL]
  | .leftJV => [.leftJ,.leftL]
  | .leftK => [.leftK,.leftB,.leftL]
  | .leftKV => [.leftK,.leftB,.leftL]
  | .rightA => [.rightB,.rightL]
  | .rightB => [.rightL]
  | .rightL => [.rightL]
  | .rightV => [.rightL]
  | .rightJ => [.rightJ,.rightL]
  | .rightJV => [.rightJ,.rightL]
  | .rightK => [.rightK,.rightB,.rightL]
  | .rightKV => [.rightK,.rightB,.rightL]

def chainPaths (c : AccessCode) : List Path := (chainCodes c).map coordinate

inductive ChainClass where | root | BL | L | JL | KBL

def classOf : AccessCode → ChainClass
  | .root => .root
  | .leftA => .BL
  | .leftB => .L
  | .leftL => .L
  | .leftV => .L
  | .leftJ => .JL
  | .leftJV => .JL
  | .leftK => .KBL
  | .leftKV => .KBL
  | .rightA => .BL
  | .rightB => .L
  | .rightL => .L
  | .rightV => .L
  | .rightJ => .JL
  | .rightJV => .JL
  | .rightK => .KBL
  | .rightKV => .KBL

def classImage : ChainClass → List (List (Endpoint net))
  | .root => [[.inl ⟨Node.R,.inl ()⟩,.inl ⟨Node.C0,.inl ()⟩,.inl ⟨Node.F,.inl ()⟩],
      [.inl ⟨Node.A,.inl ()⟩],[.inl ⟨Node.B,.inl ()⟩]]
  | .BL => [[.inl ⟨Node.A,.inl ()⟩],[.inl ⟨Node.B,.inl ()⟩]]
  | .L => [[.inl ⟨Node.B,.inl ()⟩]]
  | .JL => [[.inl ⟨Node.B,.inr true⟩],[.inl ⟨Node.B,.inl ()⟩]]
  | .KBL => [[.inl ⟨Node.A,.inr true⟩],[.inl ⟨Node.A,.inl ()⟩],[.inl ⟨Node.B,.inl ()⟩]]

/-- Real complete chains are constructed before invoking uniqueness. Variables
jump to the actual immediate lexical lambda, with rest=[] and depth0. -/
theorem concrete_chain (c : AccessCode) :
    PrerequisiteChain source (coordinate c) (chainPaths c) := by
  have leftB : PrerequisiteChain source (coordinate .leftB) [coordinate .leftL] :=
    .redex_app (p:=coordinate .leftB) (by rfl)
  have leftL : PrerequisiteChain source (coordinate .leftL) [coordinate .leftL] :=
    .redex_lam (p:=coordinate .leftB) (by rfl)
  have leftA : PrerequisiteChain source (coordinate .leftA)
      [coordinate .leftB,coordinate .leftL] :=
    .app (p:=coordinate .leftA) (by rfl) (by intro l b equal; cases equal) leftB
  have leftJ : PrerequisiteChain source (coordinate .leftJ)
      [coordinate .leftJ,coordinate .leftL] :=
    .lam (parent:=coordinate .leftB) (step:=.arg) (by rfl) (by decide) leftB
  have leftK : PrerequisiteChain source (coordinate .leftK)
      [coordinate .leftK,coordinate .leftB,coordinate .leftL] :=
    .lam (parent:=coordinate .leftA) (step:=.arg) (by rfl) (by decide) leftA
  have rightB : PrerequisiteChain source (coordinate .rightB) [coordinate .rightL] :=
    .redex_app (p:=coordinate .rightB) (by rfl)
  have rightL : PrerequisiteChain source (coordinate .rightL) [coordinate .rightL] :=
    .redex_lam (p:=coordinate .rightB) (by rfl)
  have rightA : PrerequisiteChain source (coordinate .rightA)
      [coordinate .rightB,coordinate .rightL] :=
    .app (p:=coordinate .rightA) (by rfl) (by intro l b equal; cases equal) rightB
  have rightJ : PrerequisiteChain source (coordinate .rightJ)
      [coordinate .rightJ,coordinate .rightL] :=
    .lam (parent:=coordinate .rightB) (step:=.arg) (by rfl) (by decide) rightB
  have rightK : PrerequisiteChain source (coordinate .rightK)
      [coordinate .rightK,coordinate .rightB,coordinate .rightL] :=
    .lam (parent:=coordinate .rightA) (step:=.arg) (by rfl) (by decide) rightA
  cases c with
  | root => exact .app (p:=[]) (by rfl) (by intro l b equal; cases equal) leftA
  | leftA => exact leftA
  | leftB => exact leftB
  | leftL => exact leftL
  | leftV => exact .var (leaf:=coordinate .leftV) (parent:=coordinate .leftL) (rest:=[]) (by rfl) (by rfl) (by rfl) (by rfl) leftL
  | leftJ => exact leftJ
  | leftJV => exact .var (leaf:=coordinate .leftJV) (parent:=coordinate .leftJ) (rest:=[]) (by rfl) (by rfl) (by rfl) (by rfl) leftJ
  | leftK => exact leftK
  | leftKV => exact .var (leaf:=coordinate .leftKV) (parent:=coordinate .leftK) (rest:=[]) (by rfl) (by rfl) (by rfl) (by rfl) leftK
  | rightA => exact rightA
  | rightB => exact rightB
  | rightL => exact rightL
  | rightV => exact .var (leaf:=coordinate .rightV) (parent:=coordinate .rightL) (rest:=[]) (by rfl) (by rfl) (by rfl) (by rfl) rightL
  | rightJ => exact rightJ
  | rightJV => exact .var (leaf:=coordinate .rightJV) (parent:=coordinate .rightJ) (rest:=[]) (by rfl) (by rfl) (by rfl) (by rfl) rightJ
  | rightK => exact rightK
  | rightKV => exact .var (leaf:=coordinate .rightKV) (parent:=coordinate .rightK) (rest:=[]) (by rfl) (by rfl) (by rfl) (by rfl) rightK

private theorem starting_lookup {p : Path} {es : List Path}
    (chain : PrerequisiteChain source p es) : ∃ u,source.subterm p=some u := by
  cases chain with
  | redex_app lookup => exact ⟨_,lookup⟩
  | @redex_lam p a l b arg lookup =>
    refine ⟨.lam l b,?_⟩
    rw [LTerm.subterm_append,lookup]
    rfl
  | app lookup _ _ => exact ⟨_,lookup⟩
  | lam lookup _ _ => exact ⟨_,lookup⟩
  | var lookup _ _ _ _ => exact ⟨_,lookup⟩

private def positionAt (c : AccessCode) : Position source.erase :=
  ⟨coordinate c,by
    obtain ⟨u,lookup⟩ := starting_lookup (concrete_chain c)
    rw [←LTerm.erase_subterm,lookup]
    rfl⟩

private theorem selected_piece (selection : OccurrenceFragmentSelection source net ())
    (c : AccessCode) : (selection (positionAt c)).fragment.segments=piece c :=
  (literal_occurrence_fragment c (selection (positionAt c))).2.1

private theorem concrete_image (selection : OccurrenceFragmentSelection source net ())
    (c : AccessCode) :
    canonicalChainImage selection (concrete_chain c)=classImage (classOf c) := by
  cases c with
  | root =>
    change [(selection (positionAt .leftA)).fragment.segments,(selection (positionAt .leftB)).fragment.segments,(selection (positionAt .leftL)).fragment.segments] = classImage .root
    rw [selected_piece selection .leftA,selected_piece selection .leftB,selected_piece selection .leftL]
    rfl
  | leftA =>
    change [(selection (positionAt .leftB)).fragment.segments,(selection (positionAt .leftL)).fragment.segments] = classImage .BL
    rw [selected_piece selection .leftB,selected_piece selection .leftL]
    rfl
  | leftB =>
    change [(selection (positionAt .leftL)).fragment.segments] = classImage .L
    rw [selected_piece selection .leftL]
    rfl
  | leftL =>
    change [(selection (positionAt .leftL)).fragment.segments] = classImage .L
    rw [selected_piece selection .leftL]
    rfl
  | leftV =>
    change [(selection (positionAt .leftL)).fragment.segments] = classImage .L
    rw [selected_piece selection .leftL]
    rfl
  | leftJ =>
    change [(selection (positionAt .leftJ)).fragment.segments,(selection (positionAt .leftL)).fragment.segments] = classImage .JL
    rw [selected_piece selection .leftJ,selected_piece selection .leftL]
    rfl
  | leftJV =>
    change [(selection (positionAt .leftJ)).fragment.segments,(selection (positionAt .leftL)).fragment.segments] = classImage .JL
    rw [selected_piece selection .leftJ,selected_piece selection .leftL]
    rfl
  | leftK =>
    change [(selection (positionAt .leftK)).fragment.segments,(selection (positionAt .leftB)).fragment.segments,(selection (positionAt .leftL)).fragment.segments] = classImage .KBL
    rw [selected_piece selection .leftK,selected_piece selection .leftB,selected_piece selection .leftL]
    rfl
  | leftKV =>
    change [(selection (positionAt .leftK)).fragment.segments,(selection (positionAt .leftB)).fragment.segments,(selection (positionAt .leftL)).fragment.segments] = classImage .KBL
    rw [selected_piece selection .leftK,selected_piece selection .leftB,selected_piece selection .leftL]
    rfl
  | rightA =>
    change [(selection (positionAt .rightB)).fragment.segments,(selection (positionAt .rightL)).fragment.segments] = classImage .BL
    rw [selected_piece selection .rightB,selected_piece selection .rightL]
    rfl
  | rightB =>
    change [(selection (positionAt .rightL)).fragment.segments] = classImage .L
    rw [selected_piece selection .rightL]
    rfl
  | rightL =>
    change [(selection (positionAt .rightL)).fragment.segments] = classImage .L
    rw [selected_piece selection .rightL]
    rfl
  | rightV =>
    change [(selection (positionAt .rightL)).fragment.segments] = classImage .L
    rw [selected_piece selection .rightL]
    rfl
  | rightJ =>
    change [(selection (positionAt .rightJ)).fragment.segments,(selection (positionAt .rightL)).fragment.segments] = classImage .JL
    rw [selected_piece selection .rightJ,selected_piece selection .rightL]
    rfl
  | rightJV =>
    change [(selection (positionAt .rightJ)).fragment.segments,(selection (positionAt .rightL)).fragment.segments] = classImage .JL
    rw [selected_piece selection .rightJ,selected_piece selection .rightL]
    rfl
  | rightK =>
    change [(selection (positionAt .rightK)).fragment.segments,(selection (positionAt .rightB)).fragment.segments,(selection (positionAt .rightL)).fragment.segments] = classImage .KBL
    rw [selected_piece selection .rightK,selected_piece selection .rightB,selected_piece selection .rightL]
    rfl
  | rightKV =>
    change [(selection (positionAt .rightK)).fragment.segments,(selection (positionAt .rightB)).fragment.segments,(selection (positionAt .rightL)).fragment.segments] = classImage .KBL
    rw [selected_piece selection .rightK,selected_piece selection .rightB,selected_piece selection .rightL]
    rfl

/-- Every supplied genuine successful chain has its COMPLETE edge list and
whole canonical physical image. No READ comparison or Joint is assumed. -/
theorem actual_chain_normal_form
    (selection : OccurrenceFragmentSelection source net ())
    {p : Path} {es : List Path} (chain : PrerequisiteChain source p es) :
    ∃ c : AccessCode,p=coordinate c ∧ es=chainPaths c ∧
      canonicalChainImage selection chain=classImage (classOf c) := by
  obtain ⟨u,lookup⟩ := starting_lookup chain
  let position : Position source.erase := ⟨p,by
    rw [←LTerm.erase_subterm,lookup]
    rfl⟩
  obtain ⟨actual,word,_observation⟩ := Matches.observation net actual_matching position
  obtain ⟨c,_edges,coordinateEq⟩ := actual_root_access_classification actual
  have start : p=coordinate c := word.symm.trans coordinateEq
  subst p
  have complete : es=chainPaths c := chain.unique (concrete_chain c)
  subst es
  refine ⟨c,rfl,rfl,?_⟩
  rw [canonicalChainImage_same_edges selection chain (concrete_chain c)]
  exact concrete_image selection c

#print axioms concrete_chain
#print axioms actual_chain_normal_form

end Lamping.Checks.Q0LocalModelChains

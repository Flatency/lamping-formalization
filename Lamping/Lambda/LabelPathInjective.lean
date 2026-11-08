import Lamping.Lambda.LabelPathCode
namespace Lamping.Lambda.Labelled

def PathCodeToken.flip : PathCodeToken → PathCodeToken
  | .edge e => .edge e.flip
  | .openTok d u => .closeTok (!d) u
  | .closeTok d u => .openTok (!d) u

def reversePathCode (code : List PathCodeToken) : List PathCodeToken :=
  (List.reverse code).map PathCodeToken.flip

theorem reversePathCode_append (a b : List PathCodeToken) :
    reversePathCode (a++b)=reversePathCode b++reversePathCode a := by
  simp [reversePathCode,List.reverse_append,List.map_append]

theorem reversePathCode_cons (a : PathCodeToken) (b) :
    reversePathCode (a::b)=reversePathCode b++[a.flip] := by simp [reversePathCode]

theorem Label.pathCode_concat : ∀ (a b : Label) (direction : Bool),
    (a.concat b).pathCode direction=if direction then b.pathCode direction++a.pathCode direction
      else a.pathCode direction++b.pathCode direction
  | .single _,_,d => by cases d <;> rfl
  | .cons l a,b,d => by cases d <;> simp [Label.concat,Label.pathCode,pathCode_concat,List.append_assoc]

theorem reversePathCode_nil : reversePathCode []=[] := rfl

theorem reversePathCode_singleton (t : PathCodeToken) : reversePathCode [t]=[t.flip] := rfl

mutual
  theorem Label.pathCode_reverse : ∀ (a : Label) (direction : Bool),
      a.pathCode (!direction)=reversePathCode (a.pathCode direction)
    | .single l,d => Letter.pathCode_reverse l d
    | .cons l a,false => by
      change a.pathCode true++l.pathCode true=reversePathCode (l.pathCode false++a.pathCode false)
      rw [reversePathCode_append,← Label.pathCode_reverse a false,← Letter.pathCode_reverse l false]
      simp only [Bool.not_false]
    | .cons l a,true => by
      change l.pathCode false++a.pathCode false=reversePathCode (a.pathCode true++l.pathCode true)
      rw [reversePathCode_append,← Label.pathCode_reverse a true,← Letter.pathCode_reverse l true]
      simp only [Bool.not_true]
  theorem Letter.pathCode_reverse : ∀ (l : Letter) (direction : Bool),
      l.pathCode (!direction)=reversePathCode (l.pathCode direction)
    | .atom n,d => by cases d <;> rfl
    | .over a,d => by
      cases d <;> simp only [Letter.pathCode,reversePathCode_cons,reversePathCode_append,
        reversePathCode_nil,PathCodeToken.flip,Bool.not_false,Bool.not_true,List.nil_append,List.singleton_append]
      · rw [← Label.pathCode_reverse a false]; simp only [Bool.not_false,List.cons_append]
      · rw [← Label.pathCode_reverse a true]; simp only [Bool.not_true,List.cons_append]
    | .under a,d => by
      cases d <;> simp only [Letter.pathCode,reversePathCode_cons,reversePathCode_append,
        reversePathCode_nil,PathCodeToken.flip,Bool.not_false,Bool.not_true,List.nil_append,List.singleton_append]
      · rw [← Label.pathCode_reverse a true]; simp only [Bool.not_true,List.cons_append]
      · rw [← Label.pathCode_reverse a false]; simp only [Bool.not_false,List.cons_append]
end

theorem Label.pathCode_over (a : Label) (d : Bool) : a.over.pathCode d=
    .openTok d false::(a.pathCode d++[.closeTok d false]) := rfl
theorem Label.pathCode_under (a : Label) (d : Bool) : a.under.pathCode d=
    .openTok d true::(a.pathCode (!d)++[.closeTok d true]) := rfl

def codeEdges : List PathCodeToken → EdgeWord
  | [] => []
  | .edge e::rest => e::codeEdges rest
  | _::rest => codeEdges rest

theorem codeEdges_append (a b) : codeEdges (a++b)=codeEdges a++codeEdges b := by
  induction a with
  | nil => rfl
  | cons a as ih => cases a <;> simp [codeEdges,ih]

/-- Each token determines exactly one of the eight physical port turns. -/
inductive CodeTurn : SourcePort → PathCodeToken → SourcePort → Prop where
  | overOpen (l) : CodeTurn (.appContext l) (.openTok false false) (.appFn l)
  | overClose (l) : CodeTurn (.lamContext l) (.closeTok false false) (.lamBody l)
  | underOpen (l) : CodeTurn (.lamBind l) (.openTok false true) (.lamContext l)
  | underClose (l) : CodeTurn (.appFn l) (.closeTok false true) (.appArg l)
  | overOpenRev (l) : CodeTurn (.lamBody l) (.openTok true false) (.lamContext l)
  | overCloseRev (l) : CodeTurn (.appFn l) (.closeTok true false) (.appContext l)
  | underOpenRev (l) : CodeTurn (.appArg l) (.openTok true true) (.appFn l)
  | underCloseRev (l) : CodeTurn (.lamContext l) (.closeTok true true) (.lamBind l)

theorem CodeTurn.flip (h : CodeTurn a token b) : CodeTurn b token.flip a := by
  cases h
  · exact .overCloseRev _
  · exact .overOpenRev _
  · exact .underCloseRev _
  · exact .underOpenRev _
  · exact .overClose _
  · exact .overOpen _
  · exact .underClose _
  · exact .underOpen _

theorem CodeTurn.deterministic (h : CodeTurn a token b) (k : CodeTurn a token' b) : token=token' := by
  cases h <;> cases k <;> rfl

theorem CodeTurn.codeEdges (h : CodeTurn a token b) (rest) : codeEdges (token::rest)=codeEdges rest := by
  cases h <;> rfl

/-- Canonically alternating edge/turn/edge walks. Their atom projection loses
no turn information when original edges are globally named by INIT. -/
inductive CodedWalk (edges : List SourceEdge) : SourcePort → List PathCodeToken → SourcePort → Prop where
  | last : SourceTraverse edges a e b → CodedWalk edges a [.edge e] b
  | cons : SourceTraverse edges a e b → CodeTurn b token c → CodedWalk edges c rest d →
      CodedWalk edges a (.edge e::token::rest) d

theorem CodedWalk.join (left : CodedWalk edges a p b) (turn : CodeTurn b token c)
    (right : CodedWalk edges c q d) : CodedWalk edges a (p++token::q) d := by
  induction left with
  | last edge => exact .cons edge turn right
  | cons edge first tail ih => exact .cons edge first (ih turn)

theorem CodedWalk.reverse (h : CodedWalk edges a p b) : CodedWalk edges b (reversePathCode p) a := by
  induction h with
  | last edge => exact .last edge.flip
  | cons edge turn tail ih =>
    simp only [reversePathCode_cons,List.append_assoc]
    exact ih.join turn.flip (.last edge.flip)

/-- Geometric route generation recovers precisely the full pathCode, including
turns inside a reversed underlined degree. -/
theorem SourceRoute.pathCode (route : SourceRoute edges start l finish) :
    CodedWalk edges start (l.pathCode false) finish := by
  induction route with
  | atom member atomic => exact .last (.forward member atomic)
  | over head degree tail hh hd ht =>
    simp only [Label.pathCode_concat,Label.pathCode_over,
      Bool.false_eq_true,ite_false]
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      ((hh.join (.overOpen _) hd).join (.overClose _) ht)
  | under head degree tail hh hd ht =>
    simp only [Label.pathCode_concat,Label.pathCode_under,
      Bool.false_eq_true,ite_false,Bool.not_false]
    have reverse := hd.reverse
    rw [← Label.pathCode_reverse] at reverse
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      ((hh.join (.underOpen _) reverse).join (.underClose _) ht)

/-- An atom's orientation and INIT identity determine both endpoint ports. -/
theorem SourceTraverse.endpoints (hi : INIT t)
    (h : SourceTraverse (sourceEdges env ctx t) a e b)
    (k : SourceTraverse (sourceEdges env ctx t) a' e b') : a=a' ∧ b=b' := by
  cases h with
  | forward member atomic =>
    cases k with
    | forward member' atomic' =>
      have eq := sourceEdges_unique hi member member' (atomic.trans atomic'.symm)
      cases eq; exact ⟨rfl,rfl⟩
  | backward member atomic =>
    cases k with
    | backward member' atomic' =>
      have eq := sourceEdges_unique hi member member' (atomic.trans atomic'.symm)
      cases eq; exact ⟨rfl,rfl⟩

theorem CodedWalk.codeEdges_nonempty (h : CodedWalk edges a code b) : codeEdges code≠[] := by
  cases h with
  | last => simp [codeEdges]
  | cons edge turn tail => simp [codeEdges,turn.codeEdges]

/-- Same directed original edges force identical interleaving turns, even
when the walks belong to different reducts or have different given endpoints. -/
theorem CodedWalk.codeEdges_injective (hi : INIT t)
    (h : CodedWalk (sourceEdges env ctx t) a code b)
    (k : CodedWalk (sourceEdges env ctx t) a' code' b')
    (same : codeEdges code=codeEdges code') : a=a' ∧ b=b' ∧ code=code' := by
  induction h generalizing a' code' b' with
  | last edge =>
    cases k with
    | last edge' =>
      simp only [codeEdges,List.cons.injEq] at same
      cases same.1
      obtain ⟨start,finish⟩ := edge.endpoints hi edge'
      exact ⟨start,finish,rfl⟩
    | cons edge' turn' tail' =>
      simp only [codeEdges,turn'.codeEdges,List.cons.injEq] at same
      exact False.elim (tail'.codeEdges_nonempty same.2.symm)
  | cons edge turn tail ih =>
    cases k with
    | last edge' =>
      simp only [codeEdges,turn.codeEdges,List.cons.injEq] at same
      exact False.elim (tail.codeEdges_nonempty same.2)
    | cons edge' turn' tail' =>
      simp only [codeEdges,turn.codeEdges,turn'.codeEdges,List.cons.injEq] at same
      cases same.1
      obtain ⟨start,firstEnd⟩ := edge.endpoints hi edge'
      obtain ⟨nextStart,finish,rest⟩ := ih tail' same.2
      cases firstEnd; cases nextStart
      have turnEq := turn.deterministic turn'
      cases turnEq; cases rest
      exact ⟨start,finish,rfl⟩

end Lamping.Lambda.Labelled


namespace Lamping.Lambda.Labelled
theorem codeEdges_reverse (code : List PathCodeToken) :
    codeEdges (reversePathCode code)=EdgeWord.reverse (codeEdges code) := by
  induction code with
  | nil => rfl
  | cons token rest ih =>
    rw [reversePathCode_cons,codeEdges_append,ih]
    cases token <;> simp [codeEdges,PathCodeToken.flip,EdgeWord.reverse]

mutual
  theorem Label.codeEdges_pathCode : ∀ (a : Label) (d : Bool),
      codeEdges (a.pathCode d)=if d then EdgeWord.reverse a.edgeWord else a.edgeWord
    | .single l,d => Letter.codeEdges_pathCode l d
    | .cons l a,d => by
      cases d <;> simp [Label.pathCode,codeEdges_append,Label.edgeWord,
        Label.codeEdges_pathCode,Letter.codeEdges_pathCode,EdgeWord.reverse_append]
  theorem Letter.codeEdges_pathCode : ∀ (l : Letter) (d : Bool),
      codeEdges (l.pathCode d)=if d then EdgeWord.reverse l.edgeWord else l.edgeWord
    | .atom n,d => by cases d <;> rfl
    | .over a,d => by
      cases d <;> simp [Letter.pathCode,codeEdges,codeEdges_append,Label.codeEdges_pathCode,Letter.edgeWord]
    | .under a,d => by
      cases d <;> simp [Letter.pathCode,codeEdges,codeEdges_append,Label.codeEdges_pathCode,Letter.edgeWord]
end

/-- AG6.2.8 on genuine original-edge routes. INIT edge uniqueness recovers
all turns from the directed edges; the deterministic code parser recovers bars. -/
theorem SourceRoute.edgeWord_injective (hi : INIT t)
    (left : SourceRoute (sourceEdges env ctx t) a l b)
    (right : SourceRoute (sourceEdges env ctx t) a' l' b') (same : l.edgeWord=l'.edgeWord) : l=l' := by
  have atomCode : codeEdges (l.pathCode false)=codeEdges (l'.pathCode false) := by
    simpa only [Label.codeEdges_pathCode,Bool.false_eq_true,ite_false] using same
  have codeEq := (left.pathCode.codeEdges_injective hi right.pathCode atomCode).2.2
  exact Label.pathCode_injective false codeEq

/-- Every actual current node label has a route; no equality with a family
or common endpoint is part of this statement. -/
theorem TermRoutes.labels_routes (h : TermRoutes edges env ctx t) (member : l∈t.labels) :
    ∃ start finish, SourceRoute edges start l finish := by
  induction h with
  | var route =>
    simp only [LTerm.labels,List.mem_singleton] at member
    cases member; exact ⟨_,_,route⟩
  | lam route body ih =>
    simp only [LTerm.labels,List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨_,_,route⟩
    · exact ih member
  | app route fn arg hf ha =>
    simp only [LTerm.labels,List.mem_cons,List.mem_append] at member
    rcases member with rfl | member | member
    · exact ⟨_,_,route⟩
    · exact hf member
    · exact ha member

/-- The path map is injective over labels generated along any two actual
histories from the same INIT labelling, including different final terms. -/
theorem History.generated_label_path_injective (left : History ps t u) (right : History qs t v)
    (hi : INIT t) (hl : l∈u.labels) (hl' : l'∈v.labels) (same : l.edgeWord=l'.edgeWord) : l=l' := by
  obtain ⟨a,b,lr⟩ := (left.generated_source_routes hi).labels_routes hl
  obtain ⟨a',b',rr⟩ := (right.generated_source_routes hi).labels_routes hl'
  exact lr.edgeWord_injective hi rr same
end Lamping.Lambda.Labelled

import Lamping.Lambda.Residuals
namespace Lamping.Lambda.Marked

/-- Original occurrences are distinct names, including passive redexes outside F. -/
def markAt (F : List Path) : Term → Path → Marked
  | .var i, _ => .var i
  | .lam b, p => .lam (markAt F b (p ++ [.body]))
  | .app (.lam b) a, p =>
    if p ∈ F then .red [p] (markAt F b ((p ++ [.fn]) ++ [.body])) (markAt F a (p ++ [.arg]))
    else .app [p] (.lam (markAt F b ((p ++ [.fn]) ++ [.body]))) (markAt F a (p ++ [.arg]))
  | .app f a, p => .app [] (markAt F f (p ++ [.fn])) (markAt F a (p ++ [.arg]))

def mark (F : List Path) (t : Term) : Marked := markAt F t []

theorem erase_markAt (F : List Path) (t : Term) (p : Path) : (markAt F t p).erase = t := by
  induction t generalizing p with
  | var i => rfl
  | lam b hb => simp only [markAt,erase,hb]
  | app f a hf ha =>
    cases f with
    | var i => simp only [markAt,erase,ha]
    | app f b => simp only [markAt,erase,hf,ha]
    | lam b =>
      have hb : (markAt F b ((p ++ [.fn]) ++ [.body])).erase = b := by
        have hh := hf (p ++ [Lambda.Step.fn])
        simpa only [markAt,erase,Term.lam.injEq] using hh
      simp only [markAt]
      split <;> simp only [erase,hb,ha]

theorem erase_mark (F : List Path) (t : Term) : (mark F t).erase = t := erase_markAt F t []

theorem valid_markAt (F : List Path) (t : Term) (p : Path) : Valid (markAt F t p) := by
  induction t generalizing p with
  | var i => trivial
  | lam b hb => exact hb _
  | app f a hf ha =>
    cases f with
    | var i => exact ⟨trivial,ha _,fun h => False.elim (h rfl)⟩
    | app f b => exact ⟨hf _,ha _,fun h => False.elim (h rfl)⟩
    | lam b =>
      have hb : Valid (markAt F b ((p ++ [.fn]) ++ [.body])) := by
        have hh := hf (p ++ [Lambda.Step.fn])
        simpa only [markAt,Valid] using hh
      simp only [markAt]
      split
      · exact ⟨hb,ha _⟩
      · exact ⟨hb,ha _,fun _ => ⟨_,rfl⟩⟩

theorem valid_mark (F : List Path) (t : Term) : Valid (mark F t) := valid_markAt F t []

theorem active_markAt (F : List Path) (t : Term) (p q : Path) :
    q ∈ activePositions (markAt F t p) ↔ p ++ q ∈ F ∧ q ∈ redexPositions t := by
  induction t generalizing p q with
  | var i => simp [markAt,activePositions,redexPositions,positions,subtermAt,IsRedex]
  | lam b hb =>
    cases q with
    | nil => simp [markAt,activePositions,mem_redexPositions,subtermAt,IsRedex]
    | cons s q => cases s <;> simp [markAt,activePositions,hb,mem_redexPositions,subtermAt,IsRedex,List.append_assoc]
  | app f a hf ha =>
    cases f with
    | var i =>
      cases q with
      | nil => simp [markAt,activePositions,mem_redexPositions,subtermAt,IsRedex]
      | cons s q => cases s <;> simp [markAt,activePositions,ha,subtermAt,IsRedex,List.append_assoc,redexPositions,positions]
    | app f b =>
      cases q with
      | nil => simp [markAt,activePositions,mem_redexPositions,subtermAt,IsRedex]
      | cons s q => cases s <;> simp [markAt,activePositions,hf,ha,mem_redexPositions,subtermAt,IsRedex,List.append_assoc]
    | lam b =>
      have hb (p q : Path) : q ∈ activePositions (markAt F b (p ++ [.body])) ↔
          (p ++ [.body]) ++ q ∈ F ∧ q ∈ redexPositions b := by
        have hh := hf p (.body :: q)
        simpa [markAt,activePositions,mem_redexPositions,subtermAt,List.append_assoc] using hh
      by_cases hp : p ∈ F
      all_goals
        cases q with
        | nil => simp [markAt,hp,activePositions,mem_redexPositions,subtermAt,IsRedex]
        | cons s q =>
          cases s with
          | fn =>
            cases q with
            | nil => simp [markAt,hp,activePositions,mem_redexPositions,subtermAt,IsRedex]
            | cons k q =>
              cases k with
              | fn => simp [markAt,hp,activePositions,mem_redexPositions,subtermAt,IsRedex]
              | arg => simp [markAt,hp,activePositions,mem_redexPositions,subtermAt,IsRedex]
              | body =>
                have hbb := hb (p ++ [Lambda.Step.fn]) q
                simpa [markAt,hp,activePositions,mem_redexPositions,subtermAt,IsRedex,List.append_assoc] using hbb
          | arg => simp [markAt,hp,activePositions,ha,mem_redexPositions,subtermAt,IsRedex,List.append_assoc]
          | body => simp [markAt,hp,activePositions,mem_redexPositions,subtermAt,IsRedex]

theorem trace_markAt (F : List Path) (t : Term) (r p q : Path) :
    q ∈ tracePositions r (markAt F t p) ↔ r = p ++ q ∧ q ∈ redexPositions t := by
  induction t generalizing p q with
  | var i => simp [markAt,tracePositions,redexPositions,positions,subtermAt,IsRedex]
  | lam b hb =>
    cases q with
    | nil => simp [markAt,tracePositions,mem_redexPositions,subtermAt,IsRedex]
    | cons s q => cases s <;> simp [markAt,tracePositions,hb,mem_redexPositions,subtermAt,IsRedex,List.append_assoc]
  | app f a hf ha =>
    cases f with
    | var i =>
      cases q with
      | nil => simp [markAt,tracePositions,mem_redexPositions,subtermAt,IsRedex]
      | cons s q => cases s <;> simp [markAt,tracePositions,ha,subtermAt,IsRedex,List.append_assoc,redexPositions,positions]
    | app f b =>
      cases q with
      | nil => simp [markAt,tracePositions,mem_redexPositions,subtermAt,IsRedex]
      | cons s q => cases s <;> simp [markAt,tracePositions,hf,ha,mem_redexPositions,subtermAt,IsRedex,List.append_assoc]
    | lam b =>
      have hb (p q : Path) : q ∈ tracePositions r (markAt F b (p ++ [.body])) ↔
          r = (p ++ [.body]) ++ q ∧ q ∈ redexPositions b := by
        have hh := hf p (.body :: q)
        simpa [markAt,tracePositions,mem_redexPositions,subtermAt,List.append_assoc] using hh
      by_cases hp : p ∈ F
      all_goals
        cases q with
        | nil => simp [markAt,hp,tracePositions,mem_redexPositions,subtermAt,IsRedex]
        | cons s q =>
          cases s with
          | fn =>
            cases q with
            | nil => simp [markAt,hp,tracePositions,mem_redexPositions,subtermAt,IsRedex]
            | cons k q =>
              cases k with
              | fn => simp [markAt,hp,tracePositions,mem_redexPositions,subtermAt,IsRedex]
              | arg => simp [markAt,hp,tracePositions,mem_redexPositions,subtermAt,IsRedex]
              | body =>
                have hbb := hb (p ++ [Lambda.Step.fn]) q
                simpa [markAt,hp,tracePositions,mem_redexPositions,subtermAt,IsRedex,List.append_assoc] using hbb
          | arg => simp [markAt,hp,tracePositions,ha,mem_redexPositions,subtermAt,IsRedex,List.append_assoc]
          | body => simp [markAt,hp,tracePositions,mem_redexPositions,subtermAt,IsRedex]

theorem active_mark (F : List Path) (t : Term) (q : Path) :
    q ∈ activePositions (mark F t) ↔ q ∈ F ∧ q ∈ redexPositions t := by
  simpa only [mark,List.nil_append] using active_markAt F t [] q

theorem trace_mark (F : List Path) (t : Term) (r q : Path) :
    q ∈ tracePositions r (mark F t) ↔ r = q ∧ q ∈ redexPositions t := by
  simpa only [mark,List.nil_append] using trace_markAt F t r [] q

end Lamping.Lambda.Marked

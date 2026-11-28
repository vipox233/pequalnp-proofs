import PEqualNP.Library.Helpers.L17550FreeOr

namespace PEqualNP.MetaComplexity.L17550Projection.FreeOr.Partners

open Bounded

private abbrev Atom := Nat × Word

private def atoms : List Atom :=
  (List.finRange 8).map fun i => (i.val, seedUnion (BitVec.ofNat 8 (2 ^ i.val)))

private def pick (m : Mask) : List Atom → Word
  | [] => 0
  | (i,w) :: more => (if m.getLsbD i then w else 0) ||| pick m more

private theorem pick_all (m : Mask) : pick m atoms = seedUnion m := by rfl

private abbrev forbid : Word := 2095104
private abbrev need : Word := 2047

private def allowed (x s : Word) : Word :=
  if (x &&& s &&& forbid) = 0 then x &&& s else 0

private def collect (x : Word) : List Atom → Word
  | [] => 0
  | (_,s) :: more => allowed x s ||| collect x more

/-- The maximum coverage available to one fixed operand using only clean products. -/
def coverage (d : Word) (o : Operand) : Word :=
  let x := operand d o
  collect x atoms ||| allowed x d

private def Below (a b : Word) : Prop := a &&& b = a

private theorem join {x a b c e : Word} (ha : Below (x &&& a) c)
    (hb : Below (x &&& b) e) : Below (x &&& (a ||| b)) (c ||| e) := by
  unfold Below at *
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i _
  have hai := congrArg (fun w : Word => w.getLsbD i) ha
  have hbi := congrArg (fun w : Word => w.getLsbD i) hb
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_zero] at hai hbi ⊢
  grind

private theorem clean_left {x a b : Word} (h : (x &&& (a ||| b) &&& forbid) = 0) :
    x &&& a &&& forbid = 0 := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i _
  have hi := congrArg (fun w : Word => w.getLsbD i) h
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_zero] at hi ⊢
  grind

private theorem clean_right {x a b : Word} (h : (x &&& (a ||| b) &&& forbid) = 0) :
    x &&& b &&& forbid = 0 := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i _
  have hi := congrArg (fun w : Word => w.getLsbD i) h
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_zero] at hi ⊢
  grind

private theorem optional (x a : Word) (f : Bool)
    (h : x &&& (if f then a else 0) &&& forbid = 0) :
    Below (x &&& (if f then a else 0)) (allowed x a) := by
  cases f <;> simp_all [allowed,Below]

private theorem pick_below (x : Word) (m : Mask) (l : List Atom)
    (h : x &&& pick m l &&& forbid = 0) : Below (x &&& pick m l) (collect x l) := by
  induction l with
  | nil => simp [pick,collect,Below]
  | cons a more ih =>
    rcases a with ⟨i,s⟩
    simp only [pick] at h ⊢
    exact join (optional x s _ (clean_left h)) (ih (clean_right h))

private theorem term_below (d : Word) (p : Term) (h : term d p &&& forbid = 0) :
    Below (term d p) (coverage d p.1) := by
  let x := operand d p.1
  change x &&& (seedUnion p.2.1 ||| (if p.2.2 then d else 0)) &&& forbid = 0 at h
  have hl := clean_left h
  rw [← pick_all] at hl
  have hp := pick_below x p.2.1 atoms hl
  rw [pick_all] at hp
  exact join hp (optional x d _ (clean_right h))

private theorem join_pick (m n : Mask) (l : List Atom) :
    pick (m ||| n) l = pick m l ||| pick n l := by
  induction l with
  | nil => simp [pick]
  | cons a more ih =>
    rcases a with ⟨i,t⟩
    simp only [pick,BitVec.getLsbD_or,ih]
    cases m.getLsbD i <;> cases n.getLsbD i <;> simp <;> ac_rfl

private theorem seed_join (m n : Mask) :
    seedUnion (m ||| n) = seedUnion m ||| seedUnion n := by
  simpa only [pick_all] using join_pick m n atoms

private theorem zero_seed : seedUnion 0 = 0 := by decide

private theorem and_or (x a b : Word) : x &&& (a ||| b) = (x &&& a) ||| (x &&& b) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i _
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_and]
  grind

private theorem joined_clean (a b : Word) (ha : a &&& forbid = 0) (hb : b &&& forbid = 0) :
    (a ||| b) &&& forbid = 0 := by
  rw [BitVec.and_comm, and_or, BitVec.and_comm forbid a, ha, BitVec.and_comm forbid b, hb]
  rfl

private theorem attain_atoms (x : Word) (l : List Atom)
    (h : ∀ a ∈ l, ∃ m, seedUnion m = a.2) :
    (∃ m, x &&& seedUnion m = collect x l) ∧ collect x l &&& forbid = 0 := by
  induction l with
  | nil => exact ⟨⟨0,by rw [zero_seed]; simp [collect]⟩,by simp [collect]⟩
  | cons a l ih =>
    obtain ⟨j,sj⟩ := h a (by simp)
    obtain ⟨⟨m,hm⟩,hc⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    rcases a with ⟨i,t⟩
    dsimp at sj
    by_cases ht : x &&& t &&& forbid = 0
    · have hv : allowed x t = x &&& t := if_pos ht
      exact ⟨⟨j ||| m,by simp [seed_join,and_or,sj,hm,collect,hv]⟩,
        by simpa [collect,hv] using joined_clean _ _ ht hc⟩
    · have hv : allowed x t = 0 := if_neg ht
      exact ⟨⟨m,by simpa [collect,hv] using hm⟩,by simpa [collect,hv] using hc⟩

/-- Saturating a partner still uses one legal pair and preserves cleanliness. -/
theorem attain (d : Word) (o : Operand) :
    ∃ r : Operand, term d (o,r) = coverage d o ∧ coverage d o &&& forbid = 0 := by
  let x := operand d o
  obtain ⟨⟨m,hm⟩,hc⟩ := attain_atoms x atoms (by
    intro a ha
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    exact ⟨_,rfl⟩)
  change ∃ r, x &&& operand d r = collect x atoms ||| allowed x d ∧
    (collect x atoms ||| allowed x d) &&& forbid = 0
  by_cases hd : x &&& d &&& forbid = 0
  · have hv : allowed x d = x &&& d := if_pos hd
    exact ⟨(m,true),by simp [operand,and_or,hm,hv],by simpa [hv] using joined_clean _ _ hc hd⟩
  · have hv : allowed x d = 0 := if_neg hd
    exact ⟨(m,false),by simp [operand,hv,hm],by simpa [hv] using hc⟩

/-- Two masks for the shared AND and three left operands suffice for this rejection. -/
def RejectCoverage : Prop := ∀ (u v : Mask) (a b c : Operand),
  let d := seedUnion u &&& seedUnion v
  ((coverage d a ||| coverage d b ||| coverage d c) &&& need) ≠ need

private theorem keep {a b c A B C : Word} (ha : Below a A) (hb : Below b B) (hc : Below c C)
    (h : (a ||| b ||| c) &&& need = need) : (A ||| B ||| C) &&& need = need := by
  unfold Below at *
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i _
  have hai := congrArg (fun w : Word => w.getLsbD i) ha
  have hbi := congrArg (fun w : Word => w.getLsbD i) hb
  have hci := congrArg (fun w : Word => w.getLsbD i) hc
  have hi := congrArg (fun w : Word => w.getLsbD i) h
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_zero] at hai hbi hci hi ⊢
  grind

theorem rejectThree (h : RejectCoverage) : RejectThree := by
  intro u v a b c
  cases he : fits u v [a,b,c] with
  | false => rfl
  | true =>
    let d := seedUnion u &&& seedUnion v
    have hf : (term d a &&& forbid = 0 ∧ term d b &&& forbid = 0 ∧ term d c &&& forbid = 0) ∧
        ((term d a ||| term d b ||| term d c) &&& need = need) := by
      simpa [fits,d,Bool.and_eq_true,and_assoc] using he
    exact False.elim (h u v a.1 b.1 c.1
      (keep (term_below d a hf.1.1) (term_below d b hf.1.2.1) (term_below d c hf.1.2.2) hf.2))

theorem rejectCoverage_iff : RejectCoverage ↔ RejectThree := by
  refine ⟨rejectThree,?_⟩
  intro h u v a b c
  dsimp only
  intro cover
  let d := seedUnion u &&& seedUnion v
  obtain ⟨a',ha,ca⟩ := attain d a
  obtain ⟨b',hb,cb⟩ := attain d b
  obtain ⟨c',hc,cc⟩ := attain d c
  have noFit := h u v (a,a') (b,b') (c,c')
  change (coverage d a ||| coverage d b ||| coverage d c) &&& need = need at cover
  have yesFit : fits u v [(a,a'),(b,b'),(c,c')] = true := by
    simp [fits,show seedUnion u &&& seedUnion v = d from rfl,ha,hb,hc]
    exact ⟨⟨ca,cb,cc⟩,cover⟩
  simp [noFit] at yesFit

end PEqualNP.MetaComplexity.L17550Projection.FreeOr.Partners

import PEqualNP.Library.Helpers.L17550Projection

namespace PEqualNP.MetaComplexity.L17550Projection.Bounded

abbrev Word := BitVec 21
abbrev Idx := BitVec 5
abbrev Terminal := Idx × Idx
abbrev Op := Bool × Terminal

/-- A fixed wire list reduces to a Boolean multiplexer even for a symbolic index. -/
def read : List Word → Idx → Word
  | [], _ => 0
  | x :: xs, i => if i = 0 then x else read xs (i - 1)

def product (w : List Word) (p : Terminal) := read w p.1 &&& read w p.2

def advance (w : List Word) (g : Op) :=
  w ++ [if g.1 then product w g.2 else read w g.2.1 ||| read w g.2.2]

def withinAndBudget : Bool → List Op → Bool
  | _, [] => true
  | used, g :: gs => (!(used && g.1)) && withinAndBudget (used || g.1) gs

def accepts (gs : List Op) (ps : List Terminal) : Bool :=
  let w := gs.foldl advance (seeds.map (BitVec.ofNat 21))
  withinAndBudget false gs &&
    ps.all (fun p => (product w p &&& 2095104) == 0) &&
    ((ps.foldl (fun acc p => acc ||| product w p) 0 &&& 2047) == 2047)

/-- At fixed arities the bodies contain only bounded word and Boolean operations.
    The operand multiplexer permits out-of-range reads as zero. -/
def Reject (k q : Nat) : Prop :=
  ∀ (gs : Fin k → Op) (ps : Fin q → Terminal), accepts (List.ofFn gs) (List.ofFn ps) = false

private def encPair (p : Pair) : Terminal := (BitVec.ofNat 5 p.1.val, BitVec.ofNat 5 p.2.val)
private def encOp (g : Gate) : Op := (g.1, encPair g.2)

private theorem read_get (w : List Word) (i : Nat) (hi : i < 32) :
    read w (BitVec.ofNat 5 i) = w.getD i 0 := by
  induction w generalizing i with
  | nil => simp [read]
  | cons x xs ih =>
    cases i with
    | zero => simp [read]
    | succ i =>
      have hn : BitVec.ofNat 5 (i+1) ≠ 0 := by
        intro hz
        have hv := congrArg BitVec.toNat hz
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] at hv
      have hp : BitVec.ofNat 5 (i+1) - 1 = BitVec.ofNat 5 i := by
        change BitVec.ofNat 5 (i+1) - BitVec.ofNat 5 1 = _
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), Nat.add_sub_cancel]
      rw [read, if_neg hn, hp]
      exact ih i (by omega)

private theorem read_map (w : List Nat) (i : Fin 32) :
    read (w.map (BitVec.ofNat 21)) (BitVec.ofNat 5 i.val) = BitVec.ofNat 21 (w.getD i.val 0) := by
  rw [read_get _ _ i.isLt]
  exact (List.getD_map (f := BitVec.ofNat 21) (l := w) (n := i.val) (d := 0))

private theorem product_map (w : List Nat) (p : Pair) :
    product (w.map (BitVec.ofNat 21)) (encPair p) = BitVec.ofNat 21 (mulPair w p) := by
  simp only [product,encPair,mulPair,read_map,BitVec.ofNat_and]

private theorem fold_map (gs : List Gate) (w : List Nat) :
    (gs.map encOp).foldl advance (w.map (BitVec.ofNat 21)) =
      (gs.foldl step w).map (BitVec.ofNat 21) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    have h : advance (w.map (BitVec.ofNat 21)) (encOp g) = (step w g).map (BitVec.ofNat 21) := by
      cases hg : g.1 <;>
        simp only [advance,encOp,step,hg,Bool.false_eq_true,if_false,if_true,
          List.map_append,List.map_cons,List.map_nil,product_map,encPair,read_map,BitVec.ofNat_or]
      exact congrArg (fun x => w.map (BitVec.ofNat 21) ++ [x]) (product_map w g.2)
    rw [h,ih]

private theorem or_map (ps : List Pair) (w : List Nat) (a : Nat) :
    (ps.map encPair).foldl (fun acc p => acc ||| product (w.map (BitVec.ofNat 21)) p)
      (BitVec.ofNat 21 a) = BitVec.ofNat 21 (cover w ps a) := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.foldl_cons,product_map,← BitVec.ofNat_or]
    exact ih _

private theorem budget_ok (gs : List Gate) (used : Bool) :
    (gs.filter (fun g => g.1)).length ≤ (if used then 0 else 1) →
    withinAndBudget used (gs.map encOp) = true := by
  induction gs generalizing used with
  | nil => simp [withinAndBudget]
  | cons g gs ih =>
    cases hu : used <;> cases hg : g.1 <;>
      simp [List.filter_cons,hg,encOp,withinAndBudget] at * <;> grind

private theorem clean_bits (a : Nat) (h : ∀ i : Fin 10, a.testBit (11+i.val) = false) :
    BitVec.ofNat 21 a &&& 2095104 = 0 := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  by_cases hlo : i < 11
  · have hm : ∀ j : Fin 11, (2095104 : Word).getLsbD j.val = false := by decide
    rw [BitVec.getLsbD_and, hm ⟨i,hlo⟩, Bool.and_false]
    exact BitVec.getLsbD_zero.symm
  · let j : Fin 10 := ⟨i-11,by omega⟩
    have hj : 11+j.val = i := by dsimp [j]; omega
    have ha := h j
    rw [hj] at ha
    rw [BitVec.getLsbD_and,BitVec.getLsbD_ofNat,ha]
    simp only [Bool.and_false,Bool.false_and]
    exact BitVec.getLsbD_zero.symm

private theorem full_bits (a : Nat) (h : ∀ i : Fin 11, a.testBit i.val = true) :
    BitVec.ofNat 21 a &&& 2047 = 2047 := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  by_cases hlo : i < 11
  · simp [BitVec.getLsbD_ofNat,hi,h ⟨i,hlo⟩]
  · have hm : ∀ j : Fin 10, (2047 : Word).getLsbD (11+j.val) = false := by decide
    let j : Fin 10 := ⟨i-11,by omega⟩
    have hj : 11+j.val = i := by dsimp [j]; omega
    have ha := hm j
    rw [hj] at ha
    rw [BitVec.getLsbD_and,ha,Bool.and_false]

theorem encode {gs : List Gate} {ps : List Pair} (h : Admissible gs ps) :
    accepts (gs.map encOp) (ps.map encPair) = true := by
  obtain ⟨_,_,hb,hn,hp⟩ := h
  unfold accepts
  rw [fold_map]
  have clean : (ps.map encPair).all (fun p =>
      (product ((gs.foldl step seeds).map (BitVec.ofNat 21)) p &&& 2095104) == 0) = true := by
    apply List.all_eq_true.mpr
    intro p hmem
    rcases List.mem_map.mp hmem with ⟨u,hu,rfl⟩
    apply beq_iff_eq.mpr
    rw [product_map]
    exact clean_bits _ (hn u hu).2.2
  have full := full_bits _ hp
  simp only [Bool.and_eq_true]
  refine ⟨⟨budget_ok gs false hb,clean⟩,beq_iff_eq.mpr ?_⟩
  exact (congrArg (fun v : Word => v &&& 2047) (or_map ps (gs.foldl step seeds) 0)).trans full

theorem reject_exact {gs : List Gate} {ps : List Pair} (h : Admissible gs ps)
    (exc : Reject gs.length ps.length) : False := by
  have he := exc (fun i => encOp (gs.get i)) (fun i => encPair (ps.get i))
  have hgs : List.ofFn (fun i => encOp (gs.get i)) = gs.map encOp := by simp [← List.map_ofFn]
  have hps : List.ofFn (fun i => encPair (ps.get i)) = ps.map encPair := by simp [← List.map_ofFn]
  rw [hgs,hps,encode h] at he
  contradiction


private def dummy : Gate := (false,0,0)

private theorem extension (gs : List Gate) (w : List Nat) :
    ∃ tail, gs.foldl step w = w ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons g gs ih =>
    obtain ⟨tail,ht,hl⟩ := ih (step w g)
    rw [List.foldl_cons,ht]
    unfold step
    rw [List.append_assoc]
    exact ⟨_,rfl,by simp [hl]⟩

private theorem same_cover {u v : List Nat} (ps : List Pair)
    (h : ∀ p ∈ ps, mulPair u p = mulPair v p) (a : Nat) : cover u ps a = cover v ps a := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    change cover u ps (a ||| mulPair u p) = cover v ps (a ||| mulPair v p)
    rw [h p (by simp)]
    exact ih (fun p hp => h p (by simp [hp])) _

private theorem pad {gs : List Gate} {ps : List Pair} (h : Admissible gs ps) {k : Nat}
    (hk : gs.length ≤ k) (hcost : k + 2*ps.length ≤ 15) :
    Admissible (gs ++ List.replicate (k-gs.length) dummy) ps := by
  obtain ⟨_,hb,ha,hn,hp⟩ := h
  let w := gs.foldl step seeds
  obtain ⟨ext,he,hl⟩ := extension gs seeds
  have hw : w.length = 16+gs.length := by simp [w,he,hl,seeds]; omega
  obtain ⟨tail,ht,_⟩ := extension (List.replicate (k-gs.length) dummy) w
  have hs : ∀ p ∈ ps, mulPair (w++tail) p = mulPair w p := by
    intro p hmem
    obtain ⟨h1,h2,_⟩ := hn p hmem
    rw [← hw] at h1 h2
    simp only [mulPair,List.getD_eq_getElem?_getD,List.getElem?_append_left h1,
      List.getElem?_append_left h2]
  unfold Admissible
  simp only [List.foldl_append,← show w = gs.foldl step seeds from rfl,ht,
    List.length_append,List.length_replicate,Nat.add_sub_of_le hk]
  refine ⟨hcost,?_,?_,?_,?_⟩
  · intro i
    by_cases hi : i.val < gs.length
    · simpa only [List.get_eq_getElem,List.getElem_append_left hi] using hb ⟨i.val,hi⟩
    · rw [List.get_eq_getElem,List.getElem_append_right (Nat.le_of_not_gt hi),
        List.getElem_replicate]
      simp [dummy]
  · simpa [List.filter_append,List.filter_replicate,dummy] using ha
  · intro p hm
    obtain ⟨h1,h2,h3⟩ := hn p hm
    exact ⟨by omega,by omega,by rw [hs p hm]; exact h3⟩
  · rw [same_cover ps hs]
    exact hp

theorem reject_padded {gs : List Gate} {ps : List Pair} (h : Admissible gs ps) {k : Nat}
    (hk : gs.length ≤ k) (hc : k+2*ps.length ≤ 15) (exc : Reject k ps.length) : False := by
  apply reject_exact (pad h hk hc)
  simpa [Nat.add_sub_of_le hk] using exc

/-- A proof of the small-pair relaxation plus four fixed-length bit-vector rejections
    is a proof of the literal registered negative. -/
theorem of_four_replays
    (small : ∀ g p, Admissible g p → p.length ≤ 3 → False)
    (four : Reject 7 4) (five : Reject 5 5) (six : Reject 3 6) (seven : Reject 1 7) : Claim := by
  apply of_exclusions small
  · intro g p h hq hg
    exact reject_padded h hg (by omega) (hq.symm ▸ four)
  · intro g p h hq hg
    exact reject_padded h hg (by omega) (hq.symm ▸ five)
  · intro g p h hq hg
    exact reject_padded h hg (by omega) (hq.symm ▸ six)
  · intro g p h hq hg
    exact reject_padded h hg (by omega) (hq.symm ▸ seven)

/-- Three further bounded replays can replace the free-OR small-pair argument. -/
theorem of_seven_replays
    (one : Reject 13 1) (two : Reject 11 2) (three : Reject 9 3)
    (four : Reject 7 4) (five : Reject 5 5) (six : Reject 3 6) (seven : Reject 1 7) : Claim := by
  apply of_four_replays _ four five six seven
  intro g p h hq
  have hc := h.1
  by_cases hz : p.length = 0
  · have he : p = [] := List.length_eq_zero_iff.mp hz
    subst p
    have impossible := h.2.2.2.2 (0 : Fin 11)
    simp [cover] at impossible
  · have cases' : p.length = 1 ∨ p.length = 2 ∨ p.length = 3 := by omega
    rcases cases' with hn | hn | hn
    · exact reject_padded h (k := 13) (by omega) (by omega) (hn.symm ▸ one)
    · exact reject_padded h (k := 11) (by omega) (by omega) (hn.symm ▸ two)
    · exact reject_padded h (k := 9) (by omega) (by omega) (hn.symm ▸ three)

/-- A node of a disjoint Boolean partition of a finite replay. -/
def RejectWhere (k q : Nat) (domain : (Fin k → Op) → (Fin q → Terminal) → Prop) : Prop :=
  ∀ g p, domain g p → accepts (List.ofFn g) (List.ofFn p) = false

theorem split {k q : Nat} {domain : (Fin k → Op) → (Fin q → Terminal) → Prop}
    (bit : (Fin k → Op) → (Fin q → Terminal) → Bool)
    (low : RejectWhere k q (fun g p => domain g p ∧ bit g p = false))
    (high : RejectWhere k q (fun g p => domain g p ∧ bit g p = true)) :
    RejectWhere k q domain := by
  intro g p h
  cases e : bit g p with
  | false => exact low g p ⟨h,e⟩
  | true => exact high g p ⟨h,e⟩

theorem root {k q : Nat} (h : RejectWhere k q (fun _ _ => True)) : Reject k q :=
  fun g p => h g p trivial

end PEqualNP.MetaComplexity.L17550Projection.Bounded

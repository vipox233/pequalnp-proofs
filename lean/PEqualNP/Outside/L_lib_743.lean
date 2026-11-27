import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_743_aux

section CyclicCode

variable (a b h s q : Nat) (hn : 0 < a + b)

private abbrev nW (a b : Nat) : Nat := a + b

private def locW (a b : Nat) (hn : 0 < a + b) (k : Nat) : Fin (a + b) :=
  ⟨k % (a + b), Nat.mod_lt _ hn⟩

private def offsetOf (n : Nat) (pos t : Fin n) : Nat :=
  if pos.val ≤ t.val then t.val - pos.val else n - pos.val + t.val

private lemma locW_add_offset (pos t : Fin (a + b)) :
    locW a b hn (pos.val + offsetOf (a + b) pos t) = t := by
  apply Fin.ext
  dsimp only [locW, offsetOf]
  have hp : pos.val < a + b := pos.isLt
  have ht : t.val < a + b := t.isLt
  split_ifs with hle
  · have heq : pos.val + (t.val - pos.val) = t.val := by omega
    rw [heq, Nat.mod_eq_of_lt ht]
  · have heq : pos.val + (a + b - pos.val + t.val) = t.val + (a + b) := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt ht]

private def readPat (pos t : Fin (a + b)) (pat : Fin (a + b - h) → Bool) : Bool :=
  if ho : offsetOf (a + b) pos t < a + b - h then pat ⟨offsetOf (a + b) pos t, ho⟩ else false

private lemma readPat_winAt (x : Fin (a + b) → Bool) (pos t : Fin (a + b))
    (ho : offsetOf (a + b) pos t < a + b - h) :
    readPat a b h pos t (fun j => x (locW a b hn (pos.val + j.val))) = x t := by
  dsimp only [readPat]
  simp only [ho, ↓reduceDIte]
  rw [locW_add_offset a b hn pos t]

private def tileL (hqa : q * h < a) (r : Fin q) (c : Fin h) : Fin (a + b) :=
  ⟨r.val * h + c.val, by
    have hr : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
    have hr' : r.val * h + h = (r.val + 1) * h := by ring
    omega⟩

private def tileR (hqb : (q + 1) * h ≤ b) (r : Fin q) (c : Fin h) : Fin (a + b) :=
  ⟨a + r.val * h + c.val, by
    have hr : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
    have hr' : r.val * h + h = (r.val + 1) * h := by ring
    have hq' : (q + 1) * h = q * h + h := by ring
    omega⟩

private def posL (hqa : q * h < a) (r : Fin q) : Fin (a + b) :=
  ⟨(r.val + 1) * h, by
    have hr : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
    omega⟩

private def posR (hh : 0 < h) (hqb : (q + 1) * h ≤ b) (r : Fin q) : Fin (a + b) :=
  ⟨a + (r.val + 1) * h, by
    have hr : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
    have hq' : (q + 1) * h = q * h + h := by ring
    omega⟩

private def iGuard : Fin (a + b) :=
  ⟨(a + (q + 1) * h) % (a + b), Nat.mod_lt _ hn⟩

private lemma offset_iGuard_lt (hqb : (q + 1) * h ≤ b) (t : Fin (a + b)) (ht : t.val < a + q * h) :
    offsetOf (a + b) (iGuard a b h q hn) t < a + b - h := by
  dsimp only [offsetOf]
  have hval : (iGuard a b h q hn).val = (a + (q + 1) * h) % (a + b) := rfl
  have hq' : (q + 1) * h = q * h + h := by ring
  by_cases hlt : a + (q + 1) * h < a + b
  · rw [hval, Nat.mod_eq_of_lt hlt]
    have hnot : ¬(a + (q + 1) * h ≤ t.val) := by omega
    simp only [hnot, ↓reduceIte]
    omega
  · have heq : a + (q + 1) * h = a + b := by omega
    rw [hval, heq, Nat.mod_self]
    simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero]
    omega

private lemma offset_posL_lt (hqa : q * h < a) (r : Fin q) (t : Fin (a + b))
    (hout : t.val < r.val * h ∨ (r.val + 1) * h ≤ t.val) :
    offsetOf (a + b) (posL a b h q hqa r) t < a + b - h := by
  dsimp only [offsetOf, posL]
  have hr : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
  have hr' : r.val * h + h = (r.val + 1) * h := by ring
  have htk : t.val < a + b := t.isLt
  split_ifs with hle <;> omega

private lemma offset_posR_lt (hh : 0 < h) (hqb : (q + 1) * h ≤ b) (r : Fin q) (t : Fin (a + b))
    (hout : t.val < a + r.val * h ∨ a + (r.val + 1) * h ≤ t.val) :
    offsetOf (a + b) (posR a b h q hh hqb r) t < a + b - h := by
  dsimp only [offsetOf, posR]
  have hr : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
  have hq' : (q + 1) * h = q * h + h := by ring
  have hr' : r.val * h + h = (r.val + 1) * h := by ring
  have htk : t.val < a + b := t.isLt
  split_ifs with hle <;> omega

private lemma iGuard_ne_posL (hs : 0 < s) (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) (r : Fin q) :
    iGuard a b h q hn ≠ posL a b h q hqa r := by
  intro heq
  have hv := congrArg Fin.val heq
  dsimp only [iGuard, posL] at hv
  have hr1 : h ≤ (r.val + 1) * h := by
    calc h = 1 * h := (Nat.one_mul h).symm
    _ ≤ (r.val + 1) * h := Nat.mul_le_mul_right h (Nat.succ_pos _)
  have hr2 : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
  by_cases hlt : a + (q + 1) * h < a + b
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have hEq : a + (q + 1) * h = a + b := by omega
    rw [hEq, Nat.mod_self] at hv; omega

private lemma iGuard_ne_posR (hh : 0 < h) (hqb : (q + 1) * h ≤ b) (r : Fin q) :
    iGuard a b h q hn ≠ posR a b h q hh hqb r := by
  intro heq
  have hv := congrArg Fin.val heq
  dsimp only [iGuard, posR] at hv
  have hr1 : h ≤ (r.val + 1) * h := by
    calc h = 1 * h := (Nat.one_mul h).symm
    _ ≤ (r.val + 1) * h := Nat.mul_le_mul_right h (Nat.succ_pos _)
  have hr2 : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
  have hq' : (q + 1) * h = q * h + h := by ring
  by_cases hlt : a + (q + 1) * h < a + b
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have hEq : a + (q + 1) * h = a + b := by omega
    rw [hEq, Nat.mod_self] at hv; omega

private lemma posL_ne_posR (hh : 0 < h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) (r1 r2 : Fin q) :
    posL a b h q hqa r1 ≠ posR a b h q hh hqb r2 := by
  intro heq
  have hv := congrArg Fin.val heq
  dsimp only [posL, posR] at hv
  have hr1 : (r1.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r1.isLt)
  omega

private lemma posL_inj (hh : 0 < h) (hqa : q * h < a) :
    Function.Injective (posL a b h q hqa) := by
  intro r1 r2 heq
  have hv := congrArg Fin.val heq
  dsimp only [posL] at hv
  have h1 : r1.val + 1 = r2.val + 1 := Nat.eq_of_mul_eq_mul_right hh hv
  exact Fin.ext (by omega)

private lemma posR_inj (hh : 0 < h) (hqb : (q + 1) * h ≤ b) :
    Function.Injective (posR a b h q hh hqb) := by
  intro r1 r2 heq
  have hv := congrArg Fin.val heq
  dsimp only [posR] at hv
  have h0 : (r1.val + 1) * h = (r2.val + 1) * h := by omega
  have h1 : r1.val + 1 = r2.val + 1 := Nat.eq_of_mul_eq_mul_right hh h0
  exact Fin.ext (by omega)

private def isZeroL (hsh : s ≤ h) (hqa : q * h < a)
    (w : Fin (a + b) → Bool) (r : Fin q) : Bool :=
  decide (∀ c : Fin s, w (tileL a b h q hqa r ⟨c.val, by omega⟩) = false)

private def isZeroR (hsh : s ≤ h) (hqb : (q + 1) * h ≤ b)
    (w : Fin (a + b) → Bool) (r : Fin q) : Bool :=
  decide (∀ c : Fin s, w (tileR a b h q hqb r ⟨c.val, by omega⟩) = false)

private def bodyParity (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (w : Fin (a + b) → Bool) (d : Fin (h - s)) : Bool :=
  (((Finset.univ : Finset (Fin q)).filter (fun r => w (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true)).card +
   ((Finset.univ : Finset (Fin q)).filter (fun r => w (tileR a b h q hqb r ⟨s + d.val, by omega⟩) = true)).card) % 2 == 0

private def isGoodOn (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (w : Fin (a + b) → Bool) : Bool :=
  (((Finset.univ : Finset (Fin q)).filter (fun r => isZeroL a b h s q hsh hqa w r = true)).card == 1) &&
  (((Finset.univ : Finset (Fin q)).filter (fun r => isZeroR a b h s q hsh hqb w r = true)).card == 1) &&
  decide (∀ d : Fin (h - s), bodyParity a b h s q hsh hqa hqb w d = true)

private abbrev isGoodPair (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (rL rR : Fin q) (w : Fin (a + b) → Bool) : Prop :=
  (∀ r : Fin q, isZeroL a b h s q hsh hqa w r = decide (r = rL)) ∧
  (∀ r : Fin q, isZeroR a b h s q hsh hqb w r = decide (r = rR)) ∧
  (∀ d : Fin (h - s), bodyParity a b h s q hsh hqa hqb w d = true)

private lemma isGoodOn_iff_exists_unique (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (w : Fin (a + b) → Bool) :
    isGoodOn a b h s q hsh hqa hqb w = true ↔
      ∃ rL rR : Fin q, isGoodPair a b h s q hsh hqa hqb rL rR w := by
  unfold isGoodOn isGoodPair
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hL, hR⟩, hP⟩
    rcases Finset.card_eq_one.mp hL with ⟨rL, hrL⟩
    rcases Finset.card_eq_one.mp hR with ⟨rR, hrR⟩
    refine ⟨rL, rR, ?_, ?_, hP⟩
    · intro r
      have hm : r ∈ (Finset.univ : Finset (Fin q)).filter (fun r => isZeroL a b h s q hsh hqa w r = true) ↔ r = rL := by
        rw [hrL, Finset.mem_singleton]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      cases hz : isZeroL a b h s q hsh hqa w r <;> by_cases heq : r = rL <;> simp_all
    · intro r
      have hm : r ∈ (Finset.univ : Finset (Fin q)).filter (fun r => isZeroR a b h s q hsh hqb w r = true) ↔ r = rR := by
        rw [hrR, Finset.mem_singleton]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      cases hz : isZeroR a b h s q hsh hqb w r <;> by_cases heq : r = rR <;> simp_all
  · rintro ⟨rL, rR, hL, hR, hP⟩
    refine ⟨⟨?_, ?_⟩, hP⟩
    · have heq : (Finset.univ : Finset (Fin q)).filter (fun r => isZeroL a b h s q hsh hqa w r = true) = {rL} := by
        ext r; simp [hL r]
      rw [heq, Finset.card_singleton]
    · have heq : (Finset.univ : Finset (Fin q)).filter (fun r => isZeroR a b h s q hsh hqb w r = true) = {rR} := by
        ext r; simp [hR r]
      rw [heq, Finset.card_singleton]

private lemma isGoodPair_unique {hsh : s ≤ h} {hqa : q * h < a} {hqb : (q + 1) * h ≤ b}
    {rL1 rR1 rL2 rR2 : Fin q} {w : Fin (a + b) → Bool}
    (h1 : isGoodPair a b h s q hsh hqa hqb rL1 rR1 w)
    (h2 : isGoodPair a b h s q hsh hqa hqb rL2 rR2 w) :
    rL1 = rL2 ∧ rR1 = rR2 := by
  have hL := (h1.1 rL1).symm.trans (h2.1 rL1)
  have hR := (h1.2.1 rR1).symm.trans (h2.2.1 rR1)
  simp only [decide_true] at hL hR
  exact ⟨of_decide_eq_true hL.symm, of_decide_eq_true hR.symm⟩

private lemma bodyParity_congr_otherL {hsh : s ≤ h} {hqa : q * h < a} {hqb : (q + 1) * h ≤ b}
    (r0 : Fin q) (w1 w2 : Fin (a + b) → Bool) (d : Fin (h - s))
    (hp1 : bodyParity a b h s q hsh hqa hqb w1 d = true)
    (hp2 : bodyParity a b h s q hsh hqa hqb w2 d = true)
    (hL : ∀ r : Fin q, r ≠ r0 → w1 (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = w2 (tileL a b h q hqa r ⟨s + d.val, by omega⟩))
    (hR : ∀ r : Fin q, w1 (tileR a b h q hqb r ⟨s + d.val, by omega⟩) = w2 (tileR a b h q hqb r ⟨s + d.val, by omega⟩)) :
    w1 (tileL a b h q hqa r0 ⟨s + d.val, by omega⟩) = w2 (tileL a b h q hqa r0 ⟨s + d.val, by omega⟩) := by
  unfold bodyParity at hp1 hp2
  simp only [beq_iff_eq] at hp1 hp2
  have hReq : ((Finset.univ : Finset (Fin q)).filter (fun r => w1 (tileR a b h q hqb r ⟨s + d.val, by omega⟩) = true)).card =
      ((Finset.univ : Finset (Fin q)).filter (fun r => w2 (tileR a b h q hqb r ⟨s + d.val, by omega⟩) = true)).card := by
    congr 1; ext r; simp [hR r]
  have hsplit : ∀ w : Fin (a + b) → Bool,
      ((Finset.univ : Finset (Fin q)).filter (fun r => w (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true)).card =
      (((Finset.univ : Finset (Fin q)).erase r0).filter (fun r => w (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true)).card +
      if w (tileL a b h q hqa r0 ⟨s + d.val, by omega⟩) = true then 1 else 0 := by
    intro w
    have h1 : (Finset.univ : Finset (Fin q)) = insert r0 ((Finset.univ : Finset (Fin q)).erase r0) :=
      (Finset.insert_erase (Finset.mem_univ r0)).symm
    conv_lhs => rw [h1, Finset.filter_insert]
    split_ifs with hw
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rw [Nat.add_zero]
  have hLeq : (((Finset.univ : Finset (Fin q)).erase r0).filter (fun r => w1 (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true)).card =
      (((Finset.univ : Finset (Fin q)).erase r0).filter (fun r => w2 (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true)).card := by
    congr 1; ext r
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨hne, hw⟩; exact ⟨hne, by rw [← hL r hne]; exact hw⟩
    · rintro ⟨hne, hw⟩; exact ⟨hne, by rw [hL r hne]; exact hw⟩
  rw [hsplit w1] at hp1
  rw [hsplit w2, ← hLeq, ← hReq] at hp2
  cases hb1 : w1 (tileL a b h q hqa r0 ⟨s + d.val, by omega⟩) <;>
  cases hb2 : w2 (tileL a b h q hqa r0 ⟨s + d.val, by omega⟩) <;>
  simp only [hb1, hb2, ↓reduceIte, Bool.false_eq_true] at hp1 hp2 ⊢ <;> omega

private lemma bodyParity_congr_otherR {hsh : s ≤ h} {hqa : q * h < a} {hqb : (q + 1) * h ≤ b}
    (r0 : Fin q) (w1 w2 : Fin (a + b) → Bool) (d : Fin (h - s))
    (hp1 : bodyParity a b h s q hsh hqa hqb w1 d = true)
    (hp2 : bodyParity a b h s q hsh hqa hqb w2 d = true)
    (hL : ∀ r : Fin q, w1 (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = w2 (tileL a b h q hqa r ⟨s + d.val, by omega⟩))
    (hR : ∀ r : Fin q, r ≠ r0 → w1 (tileR a b h q hqb r ⟨s + d.val, by omega⟩) = w2 (tileR a b h q hqb r ⟨s + d.val, by omega⟩)) :
    w1 (tileR a b h q hqb r0 ⟨s + d.val, by omega⟩) = w2 (tileR a b h q hqb r0 ⟨s + d.val, by omega⟩) := by
  unfold bodyParity at hp1 hp2
  simp only [beq_iff_eq] at hp1 hp2
  have hLeq : ((Finset.univ : Finset (Fin q)).filter (fun r => w1 (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true)).card =
      ((Finset.univ : Finset (Fin q)).filter (fun r => w2 (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true)).card := by
    congr 1; ext r; simp [hL r]
  have hsplit : ∀ w : Fin (a + b) → Bool,
      ((Finset.univ : Finset (Fin q)).filter (fun r => w (tileR a b h q hqb r ⟨s + d.val, by omega⟩) = true)).card =
      (((Finset.univ : Finset (Fin q)).erase r0).filter (fun r => w (tileR a b h q hqb r ⟨s + d.val, by omega⟩) = true)).card +
      if w (tileR a b h q hqb r0 ⟨s + d.val, by omega⟩) = true then 1 else 0 := by
    intro w
    have h1 : (Finset.univ : Finset (Fin q)) = insert r0 ((Finset.univ : Finset (Fin q)).erase r0) :=
      (Finset.insert_erase (Finset.mem_univ r0)).symm
    conv_lhs => rw [h1, Finset.filter_insert]
    split_ifs with hw
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rw [Nat.add_zero]
  have hReq : (((Finset.univ : Finset (Fin q)).erase r0).filter (fun r => w1 (tileR a b h q hqb r ⟨s + d.val, by omega⟩) = true)).card =
      (((Finset.univ : Finset (Fin q)).erase r0).filter (fun r => w2 (tileR a b h q hqb r ⟨s + d.val, by omega⟩) = true)).card := by
    congr 1; ext r
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨hne, hw⟩; exact ⟨hne, by rw [← hR r hne]; exact hw⟩
    · rintro ⟨hne, hw⟩; exact ⟨hne, by rw [hR r hne]; exact hw⟩
  rw [hsplit w1] at hp1
  rw [hsplit w2, ← hLeq, ← hReq] at hp2
  cases hb1 : w1 (tileR a b h q hqb r0 ⟨s + d.val, by omega⟩) <;>
  cases hb2 : w2 (tileR a b h q hqb r0 ⟨s + d.val, by omega⟩) <;>
  simp only [hb1, hb2, ↓reduceIte, Bool.false_eq_true] at hp1 hp2 ⊢ <;> omega

private lemma card_nz (s : Nat) :
    Fintype.card {v : Fin s → Bool // ∃ c : Fin s, v c = true} = 2 ^ s - 1 := by
  have hcompl : Fintype.card {v : Fin s → Bool // ∃ c : Fin s, v c = true} +
      Fintype.card {v : Fin s → Bool // ¬∃ c : Fin s, v c = true} = Fintype.card (Fin s → Bool) := by
    rw [Fintype.card_subtype, Fintype.card_subtype, ← Finset.card_union_of_disjoint]
    · have huniv : Finset.univ.filter (fun v : Fin s → Bool => ∃ c, v c = true) ∪
          Finset.univ.filter (fun v : Fin s → Bool => ¬∃ c, v c = true) = Finset.univ := by
        ext v
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact em _
      rw [huniv, Finset.card_univ]
    · rw [Finset.disjoint_left]; intro v h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact h2 h1
  have h1 : Fintype.card {v : Fin s → Bool // ¬∃ c : Fin s, v c = true} = 1 := by
    rw [Fintype.card_subtype]
    have hsing : Finset.univ.filter (fun v : Fin s → Bool => ¬∃ c, v c = true) = {fun _ => false} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, not_exists]
      constructor
      · intro hv; funext c; cases hvc : v c; rfl; exact (hv c hvc).elim
      · intro hv c; rw [hv]; exact Bool.false_ne_true
    rw [hsing, Finset.card_singleton]
  have htot : Fintype.card (Fin s → Bool) = 2 ^ s := by simp
  omega

private lemma card_goodPair (hq : 0 < q) (hs : 0 < s) (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b)
    (rL rR : Fin q) :
    Fintype.card {w : Fin (a + b) → Bool // isGoodPair a b h s q hsh hqa hqb rL rR w} =
      (2 ^ s - 1) ^ (2 * (q - 1)) * 2 ^ (a + b - (2 * q * s + (h - s))) := by
  let isLabL (t : Fin (a + b)) : Prop := ∃ r : Fin q, ∃ c : Fin s, t = tileL a b h q hqa r ⟨c.val, by omega⟩
  let isLabR (t : Fin (a + b)) : Prop := ∃ r : Fin q, ∃ c : Fin s, t = tileR a b h q hqb r ⟨c.val, by omega⟩
  let isBodyL0 (t : Fin (a + b)) : Prop := ∃ d : Fin (h - s), t = tileL a b h q hqa rL ⟨s + d.val, by omega⟩
  let isFree (t : Fin (a + b)) : Prop := ¬isLabL t ∧ ¬isLabR t ∧ ¬isBodyL0 t
  have htileL_inj : ∀ r1 r2 : Fin q, ∀ c1 c2 : Fin h,
      tileL a b h q hqa r1 c1 = tileL a b h q hqa r2 c2 → r1 = r2 ∧ c1 = c2 := by
    intro r1 r2 c1 c2 heq
    have hv := congrArg Fin.val heq
    dsimp only [tileL] at hv
    have hdiv : (h * r1.val + c1.val) / h = (h * r2.val + c2.val) / h := by
      rw [Nat.mul_comm h r1.val, Nat.mul_comm h r2.val]; exact congrArg (· / h) hv
    have hmod : (h * r1.val + c1.val) % h = (h * r2.val + c2.val) % h := by
      rw [Nat.mul_comm h r1.val, Nat.mul_comm h r2.val]; exact congrArg (· % h) hv
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt c1.isLt, Nat.add_zero,
      Nat.mul_add_div (by omega), Nat.div_eq_of_lt c2.isLt, Nat.add_zero] at hdiv
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt c1.isLt, Nat.mul_add_mod, Nat.mod_eq_of_lt c2.isLt] at hmod
    exact ⟨Fin.ext hdiv, Fin.ext hmod⟩
  have htileR_inj : ∀ r1 r2 : Fin q, ∀ c1 c2 : Fin h,
      tileR a b h q hqb r1 c1 = tileR a b h q hqb r2 c2 → r1 = r2 ∧ c1 = c2 := by
    intro r1 r2 c1 c2 heq
    have hv := congrArg Fin.val heq
    dsimp only [tileR] at hv
    have hv' : r1.val * h + c1.val = r2.val * h + c2.val := by omega
    have hdiv : (h * r1.val + c1.val) / h = (h * r2.val + c2.val) / h := by
      rw [Nat.mul_comm h r1.val, Nat.mul_comm h r2.val]; exact congrArg (· / h) hv'
    have hmod : (h * r1.val + c1.val) % h = (h * r2.val + c2.val) % h := by
      rw [Nat.mul_comm h r1.val, Nat.mul_comm h r2.val]; exact congrArg (· % h) hv'
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt c1.isLt, Nat.add_zero,
      Nat.mul_add_div (by omega), Nat.div_eq_of_lt c2.isLt, Nat.add_zero] at hdiv
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt c1.isLt, Nat.mul_add_mod, Nat.mod_eq_of_lt c2.isLt] at hmod
    exact ⟨Fin.ext hdiv, Fin.ext hmod⟩
  have htileL_ne_tileR : ∀ r1 r2 : Fin q, ∀ c1 c2 : Fin h,
      tileL a b h q hqa r1 c1 ≠ tileR a b h q hqb r2 c2 := by
    intro r1 r2 c1 c2 heq
    have hv := congrArg Fin.val heq
    dsimp only [tileL, tileR] at hv
    have hr1 : (r1.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r1.isLt)
    have hr1' : r1.val * h + h = (r1.val + 1) * h := by ring
    omega
  have hlabL_ne_bodyL0 : ∀ t, isLabL t → ¬isBodyL0 t := by
    rintro t ⟨r, c, ht1⟩ ⟨d, ht2⟩
    have h := htileL_inj r rL ⟨c.val, by omega⟩ ⟨s + d.val, by omega⟩ (ht1.symm.trans ht2)
    have hv := congrArg Fin.val h.2
    dsimp only at hv; omega
  have hlabR_ne_bodyL0 : ∀ t, isLabR t → ¬isBodyL0 t := by
    rintro t ⟨r, c, ht1⟩ ⟨d, ht2⟩
    exact htileL_ne_tileR rL r ⟨s + d.val, by omega⟩ ⟨c.val, by omega⟩ (ht2.symm.trans ht1)
  have hlabL_ne_labR : ∀ t, isLabL t → ¬isLabR t := by
    rintro t ⟨r1, c1, ht1⟩ ⟨r2, c2, ht2⟩
    exact htileL_ne_tileR r1 r2 ⟨c1.val, by omega⟩ ⟨c2.val, by omega⟩ (ht1.symm.trans ht2)
  have hbody_otherL_free : ∀ (r : Fin q) (d : Fin (h - s)), r ≠ rL →
      isFree (tileL a b h q hqa r ⟨s + d.val, by omega⟩) := by
    intro r d hne
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨r', c', hEq⟩
      have h := htileL_inj r r' ⟨s + d.val, by omega⟩ ⟨c'.val, by omega⟩ hEq
      have hv := congrArg Fin.val h.2; dsimp only at hv; omega
    · rintro ⟨r', c', hEq⟩
      exact htileL_ne_tileR r r' ⟨s + d.val, by omega⟩ ⟨c'.val, by omega⟩ hEq
    · rintro ⟨d', hEq⟩
      have h := htileL_inj r rL ⟨s + d.val, by omega⟩ ⟨s + d'.val, by omega⟩ hEq
      exact hne h.1
  have hbody_R_free : ∀ (r : Fin q) (d : Fin (h - s)),
      isFree (tileR a b h q hqb r ⟨s + d.val, by omega⟩) := by
    intro r d
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨r', c', hEq⟩
      exact htileL_ne_tileR r' r ⟨c'.val, by omega⟩ ⟨s + d.val, by omega⟩ hEq.symm
    · rintro ⟨r', c', hEq⟩
      have h := htileR_inj r r' ⟨s + d.val, by omega⟩ ⟨c'.val, by omega⟩ hEq
      have hv := congrArg Fin.val h.2; dsimp only at hv; omega
    · rintro ⟨d', hEq⟩
      exact htileL_ne_tileR rL r ⟨s + d'.val, by omega⟩ ⟨s + d.val, by omega⟩ hEq.symm
  let NZ := {v : Fin s → Bool // ∃ c : Fin s, v c = true}
  let OL := {r : Fin q // r ≠ rL}
  let OR := {r : Fin q // r ≠ rR}
  let FP := {t : Fin (a + b) // isFree t}
  let e : {w : Fin (a + b) → Bool // isGoodPair a b h s q hsh hqa hqb rL rR w} ≃
      ((OL → NZ) × (OR → NZ) × (FP → Bool)) := by
    classical
    refine
      { toFun := fun w =>
          (fun r => ⟨fun c => w.val (tileL a b h q hqa r.val ⟨c.val, by omega⟩), by
              have hz := w.property.1 r.val
              simp only [r.property, decide_false] at hz
              unfold isZeroL at hz
              simp only [decide_eq_false_iff_not, not_forall] at hz
              rcases hz with ⟨c, hc⟩
              exact ⟨c, by cases hv : w.val (tileL a b h q hqa r.val ⟨c.val, by omega⟩) <;> simp_all⟩⟩,
           fun r => ⟨fun c => w.val (tileR a b h q hqb r.val ⟨c.val, by omega⟩), by
              have hz := w.property.2.1 r.val
              simp only [r.property, decide_false] at hz
              unfold isZeroR at hz
              simp only [decide_eq_false_iff_not, not_forall] at hz
              rcases hz with ⟨c, hc⟩
              exact ⟨c, by cases hv : w.val (tileR a b h q hqb r.val ⟨c.val, by omega⟩) <;> simp_all⟩⟩,
           fun t => w.val t.val)
        invFun := fun ⟨fL, fR, fF⟩ =>
          let w : Fin (a + b) → Bool := fun t =>
            if hf : isFree t then fF ⟨t, hf⟩
            else if h1 : isLabL t then
              let r := h1.choose
              let c := h1.choose_spec.choose
              if hne : r = rL then false else (fL ⟨r, hne⟩).val c
            else if h2 : isLabR t then
              let r := h2.choose
              let c := h2.choose_spec.choose
              if hne : r = rR then false else (fR ⟨r, hne⟩).val c
            else if h3 : isBodyL0 t then
              let d := h3.choose
              let cntL := ((Finset.univ : Finset (Fin q)).erase rL).filter (fun r =>
                if hr : r = rL then false else fF ⟨tileL a b h q hqa r ⟨s + d.val, by omega⟩, hbody_otherL_free r d hr⟩ = true)
              let cntR := (Finset.univ : Finset (Fin q)).filter (fun r =>
                fF ⟨tileR a b h q hqb r ⟨s + d.val, by omega⟩, hbody_R_free r d⟩ = true)
              decide ((cntL.card + cntR.card) % 2 = 1)
            else false
          ⟨w, by
            have hw_free : ∀ t (ht : isFree t), w t = fF ⟨t, ht⟩ := by
              intro t ht; dsimp only [w]; simp only [ht, ↓reduceDIte]
            have hw_labL : ∀ (r : Fin q) (c : Fin s),
                w (tileL a b h q hqa r ⟨c.val, by omega⟩) =
                  if hne : r = rL then false else (fL ⟨r, hne⟩).val c := by
              intro r c
              have h1 : isLabL (tileL a b h q hqa r ⟨c.val, by omega⟩) := ⟨r, c, rfl⟩
              have hnf : ¬isFree (tileL a b h q hqa r ⟨c.val, by omega⟩) := fun hf => hf.1 h1
              dsimp only [w]
              simp only [hnf, h1, ↓reduceDIte]
              have heq := htileL_inj h1.choose r ⟨h1.choose_spec.choose.val, by omega⟩ ⟨c.val, by omega⟩ h1.choose_spec.choose_spec.symm
              have hcv : h1.choose_spec.choose.val = c.val := congrArg (Fin.val : Fin h → Nat) heq.2
              have hc : h1.choose_spec.choose = c := Fin.ext hcv
              have hfn : ∀ (r1 r2 : Fin q) (c1 c2 : Fin s), r1 = r2 → c1 = c2 →
                  (if hne : r1 = rL then false else (fL ⟨r1, hne⟩).val c1) =
                  (if hne : r2 = rL then false else (fL ⟨r2, hne⟩).val c2) := by
                rintro r1 _ c1 _ rfl rfl; rfl
              exact hfn _ _ _ _ heq.1 hc
            have hw_labR : ∀ (r : Fin q) (c : Fin s),
                w (tileR a b h q hqb r ⟨c.val, by omega⟩) =
                  if hne : r = rR then false else (fR ⟨r, hne⟩).val c := by
              intro r c
              have h2 : isLabR (tileR a b h q hqb r ⟨c.val, by omega⟩) := ⟨r, c, rfl⟩
              have hnf : ¬isFree (tileR a b h q hqb r ⟨c.val, by omega⟩) := fun hf => hf.2.1 h2
              have hnl : ¬isLabL (tileR a b h q hqb r ⟨c.val, by omega⟩) := fun h1 => hlabL_ne_labR _ h1 h2
              dsimp only [w]
              simp only [hnf, hnl, h2, ↓reduceDIte]
              have heq := htileR_inj h2.choose r ⟨h2.choose_spec.choose.val, by omega⟩ ⟨c.val, by omega⟩ h2.choose_spec.choose_spec.symm
              have hcv : h2.choose_spec.choose.val = c.val := congrArg (Fin.val : Fin h → Nat) heq.2
              have hc : h2.choose_spec.choose = c := Fin.ext hcv
              have hfn : ∀ (r1 r2 : Fin q) (c1 c2 : Fin s), r1 = r2 → c1 = c2 →
                  (if hne : r1 = rR then false else (fR ⟨r1, hne⟩).val c1) =
                  (if hne : r2 = rR then false else (fR ⟨r2, hne⟩).val c2) := by
                rintro r1 _ c1 _ rfl rfl; rfl
              exact hfn _ _ _ _ heq.1 hc
            have hw_body0 : ∀ d : Fin (h - s),
                w (tileL a b h q hqa rL ⟨s + d.val, by omega⟩) =
                  decide (((((Finset.univ : Finset (Fin q)).erase rL).filter (fun r =>
                    if hr : r = rL then false else fF ⟨tileL a b h q hqa r ⟨s + d.val, by omega⟩, hbody_otherL_free r d hr⟩ = true)).card +
                    ((Finset.univ : Finset (Fin q)).filter (fun r =>
                      fF ⟨tileR a b h q hqb r ⟨s + d.val, by omega⟩, hbody_R_free r d⟩ = true)).card) % 2 = 1) := by
              intro d
              have h3 : isBodyL0 (tileL a b h q hqa rL ⟨s + d.val, by omega⟩) := ⟨d, rfl⟩
              have hnf : ¬isFree (tileL a b h q hqa rL ⟨s + d.val, by omega⟩) := fun hf => hf.2.2 h3
              have hnl : ¬isLabL (tileL a b h q hqa rL ⟨s + d.val, by omega⟩) := fun h1 => hlabL_ne_bodyL0 _ h1 h3
              have hnr : ¬isLabR (tileL a b h q hqa rL ⟨s + d.val, by omega⟩) := fun h2 => hlabR_ne_bodyL0 _ h2 h3
              dsimp only [w]
              simp only [hnf, hnl, hnr, h3, ↓reduceDIte]
              have heq := htileL_inj rL rL ⟨s + h3.choose.val, by omega⟩ ⟨s + d.val, by omega⟩ h3.choose_spec.symm
              have hd : h3.choose = d := Fin.ext (by have := congrArg Fin.val heq.2; dsimp only at this; omega)
              have hfn : ∀ d1 d2 : Fin (h - s), d1 = d2 →
                  decide (((((Finset.univ : Finset (Fin q)).erase rL).filter (fun r =>
                    if hr : r = rL then false else fF ⟨tileL a b h q hqa r ⟨s + d1.val, by omega⟩, hbody_otherL_free r d1 hr⟩ = true)).card +
                    ((Finset.univ : Finset (Fin q)).filter (fun r =>
                      fF ⟨tileR a b h q hqb r ⟨s + d1.val, by omega⟩, hbody_R_free r d1⟩ = true)).card) % 2 = 1) =
                  decide (((((Finset.univ : Finset (Fin q)).erase rL).filter (fun r =>
                    if hr : r = rL then false else fF ⟨tileL a b h q hqa r ⟨s + d2.val, by omega⟩, hbody_otherL_free r d2 hr⟩ = true)).card +
                    ((Finset.univ : Finset (Fin q)).filter (fun r =>
                      fF ⟨tileR a b h q hqb r ⟨s + d2.val, by omega⟩, hbody_R_free r d2⟩ = true)).card) % 2 = 1) := by
                rintro d1 _ rfl; rfl
              exact hfn _ _ hd
            refine ⟨?_, ?_, ?_⟩
            · intro r
              unfold isZeroL
              by_cases hrr : r = rL
              · subst hrr
                simp only [decide_true, decide_eq_true_eq]
                intro c; rw [hw_labL r c]; simp
              · simp only [hrr, decide_false, decide_eq_false_iff_not, not_forall]
                rcases (fL ⟨r, hrr⟩).property with ⟨c, hc⟩
                refine ⟨c, ?_⟩
                rw [hw_labL r c]; simp [hrr, hc]
            · intro r
              unfold isZeroR
              by_cases hrr : r = rR
              · subst hrr
                simp only [decide_true, decide_eq_true_eq]
                intro c; rw [hw_labR r c]; simp
              · simp only [hrr, decide_false, decide_eq_false_iff_not, not_forall]
                rcases (fR ⟨r, hrr⟩).property with ⟨c, hc⟩
                refine ⟨c, ?_⟩
                rw [hw_labR r c]; simp [hrr, hc]
            · intro d
              unfold bodyParity
              simp only [beq_iff_eq]
              have hsplitL : ((Finset.univ : Finset (Fin q)).filter (fun r => w (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true)).card =
                  (if w (tileL a b h q hqa rL ⟨s + d.val, by omega⟩) = true then
                    insert rL (((Finset.univ : Finset (Fin q)).erase rL).filter (fun r => w (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true))
                  else ((Finset.univ : Finset (Fin q)).erase rL).filter (fun r => w (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true)).card := by
                have h1 : (Finset.univ : Finset (Fin q)) = insert rL ((Finset.univ : Finset (Fin q)).erase rL) :=
                  (Finset.insert_erase (Finset.mem_univ rL)).symm
                conv_lhs => rw [h1, Finset.filter_insert]
              have hLeq : ((Finset.univ : Finset (Fin q)).erase rL).filter (fun r => w (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true) =
                  ((Finset.univ : Finset (Fin q)).erase rL).filter (fun r =>
                    if hr : r = rL then false else fF ⟨tileL a b h q hqa r ⟨s + d.val, by omega⟩, hbody_otherL_free r d hr⟩ = true) := by
                ext r
                simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
                constructor
                · rintro ⟨hne, hw'⟩; refine ⟨hne, ?_⟩; simp only [hne, ↓reduceDIte]; rw [← hw_free _ (hbody_otherL_free r d hne)]; exact hw'
                · rintro ⟨hne, hw'⟩; refine ⟨hne, ?_⟩; simp only [hne, ↓reduceDIte] at hw'; rw [hw_free _ (hbody_otherL_free r d hne)]; exact hw'
              have hReq : (Finset.univ : Finset (Fin q)).filter (fun r => w (tileR a b h q hqb r ⟨s + d.val, by omega⟩) = true) =
                  (Finset.univ : Finset (Fin q)).filter (fun r => fF ⟨tileR a b h q hqb r ⟨s + d.val, by omega⟩, hbody_R_free r d⟩ = true) := by
                ext r
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rw [hw_free _ (hbody_R_free r d)]
              rw [hsplitL, hLeq, hReq, hw_body0 d]
              split_ifs with hodd
              · rw [Finset.card_insert_of_notMem (by simp)]
                simp only [decide_eq_true_eq] at hodd
                omega
              · simp only [decide_eq_true_eq] at hodd
                omega⟩
        left_inv := by
          rintro ⟨w0, hw0⟩
          apply Subtype.ext
          funext t
          dsimp only
          by_cases hf : isFree t
          · simp only [hf, ↓reduceDIte]
          · simp only [hf, ↓reduceDIte]
            by_cases h1 : isLabL t
            · simp only [h1, ↓reduceDIte]
              have ht := h1.choose_spec.choose_spec
              by_cases hne : h1.choose = rL
              · simp only [hne, ↓reduceDIte]
                have hz := hw0.1 rL
                simp only [decide_true] at hz
                unfold isZeroL at hz
                simp only [decide_eq_true_eq] at hz
                have hfn : ∀ (r1 r2 : Fin q) (c1 : Fin s), r1 = r2 →
                    w0 (tileL a b h q hqa r1 ⟨c1.val, by omega⟩) = w0 (tileL a b h q hqa r2 ⟨c1.val, by omega⟩) := by
                  rintro r1 _ c1 rfl; rfl
                rw [ht, hfn _ _ _ hne, hz h1.choose_spec.choose]
              · simp only [hne, ↓reduceDIte, ← ht]
            · simp only [h1, ↓reduceDIte]
              by_cases h2 : isLabR t
              · simp only [h2, ↓reduceDIte]
                have ht := h2.choose_spec.choose_spec
                by_cases hne : h2.choose = rR
                · simp only [hne, ↓reduceDIte]
                  have hz := hw0.2.1 rR
                  simp only [decide_true] at hz
                  unfold isZeroR at hz
                  simp only [decide_eq_true_eq] at hz
                  have hfn : ∀ (r1 r2 : Fin q) (c1 : Fin s), r1 = r2 →
                      w0 (tileR a b h q hqb r1 ⟨c1.val, by omega⟩) = w0 (tileR a b h q hqb r2 ⟨c1.val, by omega⟩) := by
                    rintro r1 _ c1 rfl; rfl
                  rw [ht, hfn _ _ _ hne, hz h2.choose_spec.choose]
                · simp only [hne, ↓reduceDIte, ← ht]
              · simp only [h2, ↓reduceDIte]
                have h3 : isBodyL0 t := by
                  by_contra hn3; exact hf ⟨h1, h2, hn3⟩
                simp only [h3, ↓reduceDIte]
                set d := h3.choose
                have ht : t = tileL a b h q hqa rL ⟨s + d.val, by omega⟩ := h3.choose_spec
                conv_rhs => rw [ht]
                have hp := hw0.2.2 d
                unfold bodyParity at hp
                simp only [beq_iff_eq] at hp
                have hsplitL : ((Finset.univ : Finset (Fin q)).filter (fun r => w0 (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true)).card =
                    (if w0 (tileL a b h q hqa rL ⟨s + d.val, by omega⟩) = true then
                      insert rL (((Finset.univ : Finset (Fin q)).erase rL).filter (fun r => w0 (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true))
                    else ((Finset.univ : Finset (Fin q)).erase rL).filter (fun r => w0 (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true)).card := by
                  have h1u : (Finset.univ : Finset (Fin q)) = insert rL ((Finset.univ : Finset (Fin q)).erase rL) :=
                    (Finset.insert_erase (Finset.mem_univ rL)).symm
                  conv_lhs => rw [h1u, Finset.filter_insert]
                have hLeq : ((Finset.univ : Finset (Fin q)).erase rL).filter (fun r => w0 (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true) =
                    ((Finset.univ : Finset (Fin q)).erase rL).filter (fun r =>
                      if hr : r = rL then false else w0 (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true) := by
                  ext r; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
                  constructor
                  · rintro ⟨hne, hw'⟩; exact ⟨hne, by simp [hne, hw']⟩
                  · rintro ⟨hne, hw'⟩; exact ⟨hne, by simpa [hne] using hw'⟩
                rw [hsplitL, hLeq] at hp
                change decide (((((Finset.univ : Finset (Fin q)).erase rL).filter (fun r =>
                    if hr : r = rL then false else w0 (tileL a b h q hqa r ⟨s + d.val, by omega⟩) = true)).card +
                  ((Finset.univ : Finset (Fin q)).filter (fun r =>
                    w0 (tileR a b h q hqb r ⟨s + d.val, by omega⟩) = true)).card) % 2 = 1) =
                  w0 (tileL a b h q hqa rL ⟨s + d.val, by omega⟩)
                cases hval : w0 (tileL a b h q hqa rL ⟨s + d.val, by omega⟩)
                · simp only [hval, Bool.false_eq_true, ↓reduceIte] at hp
                  exact decide_eq_false (by omega)
                · simp only [hval, ↓reduceIte] at hp
                  rw [Finset.card_insert_of_notMem (by simp)] at hp
                  exact decide_eq_true (by omega)
        right_inv := by
          rintro ⟨fL, fR, fF⟩
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · funext ⟨r, hr⟩
            apply Subtype.ext
            funext c
            dsimp only
            have h1 : isLabL (tileL a b h q hqa r ⟨c.val, by omega⟩) := ⟨r, c, rfl⟩
            have hnf : ¬isFree (tileL a b h q hqa r ⟨c.val, by omega⟩) := fun hf => hf.1 h1
            simp only [hnf, h1, ↓reduceDIte]
            have heq := htileL_inj h1.choose r ⟨h1.choose_spec.choose.val, by omega⟩ ⟨c.val, by omega⟩ h1.choose_spec.choose_spec.symm
            have hcv : h1.choose_spec.choose.val = c.val := congrArg (Fin.val : Fin h → Nat) heq.2
            have hc : h1.choose_spec.choose = c := Fin.ext hcv
            have hfn : ∀ (r1 r2 : Fin q) (c1 c2 : Fin s), r1 = r2 → c1 = c2 →
                (if hne : r1 = rL then false else (fL ⟨r1, hne⟩).val c1) =
                (if hne : r2 = rL then false else (fL ⟨r2, hne⟩).val c2) := by
              rintro r1 _ c1 _ rfl rfl; rfl
            rw [hfn _ _ _ _ heq.1 hc]
            simp only [hr, ↓reduceDIte]
          · funext ⟨r, hr⟩
            apply Subtype.ext
            funext c
            dsimp only
            have h2 : isLabR (tileR a b h q hqb r ⟨c.val, by omega⟩) := ⟨r, c, rfl⟩
            have hnf : ¬isFree (tileR a b h q hqb r ⟨c.val, by omega⟩) := fun hf => hf.2.1 h2
            have hnl : ¬isLabL (tileR a b h q hqb r ⟨c.val, by omega⟩) := fun h1 => hlabL_ne_labR _ h1 h2
            simp only [hnf, hnl, h2, ↓reduceDIte]
            have heq := htileR_inj h2.choose r ⟨h2.choose_spec.choose.val, by omega⟩ ⟨c.val, by omega⟩ h2.choose_spec.choose_spec.symm
            have hcv : h2.choose_spec.choose.val = c.val := congrArg (Fin.val : Fin h → Nat) heq.2
            have hc : h2.choose_spec.choose = c := Fin.ext hcv
            have hfn : ∀ (r1 r2 : Fin q) (c1 c2 : Fin s), r1 = r2 → c1 = c2 →
                (if hne : r1 = rR then false else (fR ⟨r1, hne⟩).val c1) =
                (if hne : r2 = rR then false else (fR ⟨r2, hne⟩).val c2) := by
              rintro r1 _ c1 _ rfl rfl; rfl
            rw [hfn _ _ _ _ heq.1 hc]
            simp only [hr, ↓reduceDIte]
          · funext ⟨t, ht⟩
            dsimp only
            simp only [ht, ↓reduceDIte] }
  have hcard_e := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_bool, card_nz s] at hcard_e
  have hcard_OL : Fintype.card OL = q - 1 := by
    have : Fintype.card {r : Fin q // r ≠ rL} = ((Finset.univ : Finset (Fin q)).erase rL).card := by
      rw [Fintype.card_subtype]; congr 1; ext r; simp
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ rL), Finset.card_univ, Fintype.card_fin]
  have hcard_OR : Fintype.card OR = q - 1 := by
    have : Fintype.card {r : Fin q // r ≠ rR} = ((Finset.univ : Finset (Fin q)).erase rR).card := by
      rw [Fintype.card_subtype]; congr 1; ext r; simp
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ rR), Finset.card_univ, Fintype.card_fin]
  have hcard_FP : Fintype.card FP = a + b - (2 * q * s + (h - s)) := by
    classical
    let S1 : Finset (Fin (a + b)) := Finset.univ.image (fun p : Fin q × Fin s => tileL a b h q hqa p.1 ⟨p.2.val, by omega⟩)
    let S2 : Finset (Fin (a + b)) := Finset.univ.image (fun p : Fin q × Fin s => tileR a b h q hqb p.1 ⟨p.2.val, by omega⟩)
    let S3 : Finset (Fin (a + b)) := Finset.univ.image (fun d : Fin (h - s) => tileL a b h q hqa rL ⟨s + d.val, by omega⟩)
    have hS1_card : S1.card = q * s := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro p1 p2 hEq
        have heq := htileL_inj p1.1 p2.1 ⟨p1.2.val, by omega⟩ ⟨p2.2.val, by omega⟩ hEq
        have hv : p1.2.val = p2.2.val := congrArg (Fin.val : Fin h → Nat) heq.2
        exact Prod.ext heq.1 (Fin.ext hv)
    have hS2_card : S2.card = q * s := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro p1 p2 hEq
        have heq := htileR_inj p1.1 p2.1 ⟨p1.2.val, by omega⟩ ⟨p2.2.val, by omega⟩ hEq
        have hv : p1.2.val = p2.2.val := congrArg (Fin.val : Fin h → Nat) heq.2
        exact Prod.ext heq.1 (Fin.ext hv)
    have hS3_card : S3.card = h - s := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro d1 d2 hEq
        have h := htileL_inj rL rL ⟨s + d1.val, by omega⟩ ⟨s + d2.val, by omega⟩ hEq
        exact Fin.ext (by have := congrArg Fin.val h.2; dsimp only at this; omega)
    have hd12 : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      rcases Finset.mem_image.mp ht1 with ⟨p1, _, rfl⟩
      rcases Finset.mem_image.mp ht2 with ⟨p2, _, hEq⟩
      exact htileL_ne_tileR p1.1 p2.1 ⟨p1.2.val, by omega⟩ ⟨p2.2.val, by omega⟩ hEq.symm
    have hd13 : Disjoint S1 S3 := by
      rw [Finset.disjoint_left]
      intro t ht1 ht3
      rcases Finset.mem_image.mp ht1 with ⟨p1, _, rfl⟩
      rcases Finset.mem_image.mp ht3 with ⟨d, _, hEq⟩
      have h := htileL_inj p1.1 rL ⟨p1.2.val, by omega⟩ ⟨s + d.val, by omega⟩ hEq.symm
      have hv := congrArg Fin.val h.2; dsimp only at hv; omega
    have hd23 : Disjoint S2 S3 := by
      rw [Finset.disjoint_left]
      intro t ht2 ht3
      rcases Finset.mem_image.mp ht2 with ⟨p2, _, rfl⟩
      rcases Finset.mem_image.mp ht3 with ⟨d, _, hEq⟩
      exact htileL_ne_tileR rL p2.1 ⟨s + d.val, by omega⟩ ⟨p2.2.val, by omega⟩ hEq
    have hU_card : (S1 ∪ S2 ∪ S3).card = 2 * q * s + (h - s) := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
        Finset.card_union_of_disjoint hd12, hS1_card, hS2_card, hS3_card]
      ring
    have hFP_eq : (Finset.univ : Finset (Fin (a + b))).filter (fun t => isFree t) = Finset.univ \ (S1 ∪ S2 ∪ S3) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_union,
        S1, S2, S3, Finset.mem_image, isFree, isLabL, isLabR, isBodyL0, Prod.exists]
      constructor
      · rintro ⟨h1, h2, h3⟩ ((⟨r, c, hc⟩ | ⟨r, c, hc⟩) | ⟨d, hd⟩)
        · exact h1 ⟨r, c, hc.symm⟩
        · exact h2 ⟨r, c, hc.symm⟩
        · exact h3 ⟨d, hd.symm⟩
      · intro hnot
        refine ⟨?_, ?_, ?_⟩
        · rintro ⟨r, c, hc⟩; exact hnot (Or.inl (Or.inl ⟨r, c, hc.symm⟩))
        · rintro ⟨r, c, hc⟩; exact hnot (Or.inl (Or.inr ⟨r, c, hc.symm⟩))
        · rintro ⟨d, hd⟩; exact hnot (Or.inr ⟨d, hd.symm⟩)
    rw [Fintype.card_subtype, hFP_eq, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin, hU_card]
  rw [hcard_OL, hcard_OR, hcard_FP] at hcard_e
  rw [hcard_e, ← mul_assoc, ← pow_add, show (q - 1) + (q - 1) = 2 * (q - 1) by omega]

private lemma card_goodOn (hq : 0 < q) (hs : 0 < s) (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) :
    Fintype.card {w : Fin (a + b) → Bool // isGoodOn a b h s q hsh hqa hqb w = true} =
      q ^ 2 * (2 ^ s - 1) ^ (2 * (q - 1)) * 2 ^ (a + b - (2 * q * s + (h - s))) := by
  classical
  let e : {w : Fin (a + b) → Bool // isGoodOn a b h s q hsh hqa hqb w = true} ≃
      Σ p : Fin q × Fin q, {w : Fin (a + b) → Bool // isGoodPair a b h s q hsh hqa hqb p.1 p.2 w} :=
    { toFun := fun w =>
        have hex := (isGoodOn_iff_exists_unique a b h s q hsh hqa hqb w.val).mp w.property
        ⟨(hex.choose, hex.choose_spec.choose), ⟨w.val, hex.choose_spec.choose_spec⟩⟩
      invFun := fun ⟨⟨rL, rR⟩, ⟨w, hw⟩⟩ =>
        ⟨w, (isGoodOn_iff_exists_unique a b h s q hsh hqa hqb w).mpr ⟨rL, rR, hw⟩⟩
      left_inv := by rintro ⟨w, hw⟩; rfl
      right_inv := by
        rintro ⟨⟨rL, rR⟩, ⟨w, hw⟩⟩
        have hex := (isGoodOn_iff_exists_unique a b h s q hsh hqa hqb w).mp
          ((isGoodOn_iff_exists_unique a b h s q hsh hqa hqb w).mpr ⟨rL, rR, hw⟩)
        have hu := isGoodPair_unique a b h s q hex.choose_spec.choose_spec hw
        refine Sigma.ext (Prod.ext hu.1 hu.2) ?_
        cases hu.1; cases hu.2; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [card_goodPair a b h s q hq hs hsh hqa hqb, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  ring

private lemma main_743 (hq : 0 < q) (hs : 0 < s) (hsh : s ≤ h) (hqa : q * h < a) (hqb : (q + 1) * h ≤ b) :
    let n := a + b
    let M := q ^ 2 * (2 ^ s - 1) ^ (2 * (q - 1)) * 2 ^ (n - (2 * q * s + (h - s)))
    let Word := Fin n → Bool
    let Pat := Fin (n - h) → Bool
    let Slot := Fin n × Pat
    let solutions := fun (tab : Slot → Bool) =>
      (Finset.univ : Finset Word).filter (fun x =>
        ∀ i : Fin n, tab (i, fun j => x (locW a b hn (i.val + j.val))) = true)
    ∃ (code : Fin M → Word) (base : Slot → Bool) (left right : Fin M → Slot),
      Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
      (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
        base (left i) = false ∧ base (right i) = false) ∧
      ∀ A B : Finset (Fin M), solutions (fun slot =>
        base slot || decide (slot ∈ A.image left) || decide (slot ∈ B.image right)) =
          (A ∩ B).image code := by
  classical
  intro n M Word Pat Slot solutions
  have hh : 0 < h := by omega
  let Good := {w : Word // isGoodOn a b h s q hsh hqa hqb w = true}
  let eqv : Good ≃ Fin M := Fintype.equivFinOfCardEq (card_goodOn a b h s q hq hs hsh hqa hqb)
  let code : Fin M → Word := fun i => (eqv.symm i).val
  have hcode_inj : Function.Injective code := fun i1 i2 hEq =>
    eqv.symm.injective (Subtype.ext hEq)
  have hcode_good : ∀ i : Fin M, isGoodOn a b h s q hsh hqa hqb (code i) = true :=
    fun i => (eqv.symm i).property
  let rLOf (i : Fin M) : Fin q :=
    ((isGoodOn_iff_exists_unique a b h s q hsh hqa hqb (code i)).mp (hcode_good i)).choose
  let rROf (i : Fin M) : Fin q :=
    ((isGoodOn_iff_exists_unique a b h s q hsh hqa hqb (code i)).mp (hcode_good i)).choose_spec.choose
  have hpair_code : ∀ i : Fin M, isGoodPair a b h s q hsh hqa hqb (rLOf i) (rROf i) (code i) :=
    fun i => ((isGoodOn_iff_exists_unique a b h s q hsh hqa hqb (code i)).mp (hcode_good i)).choose_spec.choose_spec
  let winAt (x : Word) (pos : Fin n) : Pat := fun j => x (locW a b hn (pos.val + j.val))
  let left : Fin M → Slot := fun i => (posL a b h q hqa (rLOf i), winAt (code i) (posL a b h q hqa (rLOf i)))
  let right : Fin M → Slot := fun i => (posR a b h q hh hqb (rROf i), winAt (code i) (posR a b h q hh hqb (rROf i)))
  let base : Slot → Bool := fun ⟨pos, pat⟩ =>
    if pos = iGuard a b h q hn then isGoodOn a b h s q hsh hqa hqb (fun t => readPat a b h pos t pat)
    else if ∃ r : Fin q, pos = posL a b h q hqa r ∧
        ∀ r' : Fin q, r' ≠ r → isZeroL a b h s q hsh hqa (fun t => readPat a b h pos t pat) r' = false then false
    else if ∃ r : Fin q, pos = posR a b h q hh hqb r ∧
        ∀ r' : Fin q, r' ≠ r → isZeroR a b h s q hsh hqb (fun t => readPat a b h pos t pat) r' = false then false
    else true
  have hleft_inj : Function.Injective left := by
    intro i1 i2 hEq
    have hpos : posL a b h q hqa (rLOf i1) = posL a b h q hqa (rLOf i2) := congrArg Prod.fst hEq
    have hr : rLOf i1 = rLOf i2 := posL_inj a b h q hh hqa hpos
    have hpat : winAt (code i1) (posL a b h q hqa (rLOf i1)) = winAt (code i2) (posL a b h q hqa (rLOf i1)) := by
      have h2 := congrArg Prod.snd hEq; dsimp only [left] at h2; rw [← hr] at h2; exact h2
    dsimp only [winAt] at hpat
    apply hcode_inj
    funext t
    set r0 := rLOf i1
    by_cases hout : t.val < r0.val * h ∨ (r0.val + 1) * h ≤ t.val
    · have ho := offset_posL_lt a b h q hqa r0 t hout
      rw [← readPat_winAt a b h hn (code i1) (posL a b h q hqa r0) t ho, hpat,
        readPat_winAt a b h hn (code i2) (posL a b h q hqa r0) t ho]
    · have htrng : r0.val * h ≤ t.val ∧ t.val < (r0.val + 1) * h := by omega
      have hr' : r0.val * h + h = (r0.val + 1) * h := by ring
      set c := t.val - r0.val * h
      have hch : c < h := by omega
      have hteq : t = tileL a b h q hqa r0 ⟨c, hch⟩ := Fin.ext (by dsimp only [tileL]; omega)
      rw [hteq]
      by_cases hcs : c < s
      · have hz1 := (hpair_code i1).1 r0
        have hz2 := (hpair_code i2).1 r0
        simp only [r0, decide_true] at hz1
        rw [← hr] at hz2; simp only [r0, decide_true] at hz2
        unfold isZeroL at hz1 hz2
        simp only [decide_eq_true_eq] at hz1 hz2
        exact (hz1 ⟨c, hcs⟩).trans (hz2 ⟨c, hcs⟩).symm
      · set d : Fin (h - s) := ⟨c - s, by omega⟩
        have hceq : (⟨c, hch⟩ : Fin h) = ⟨s + d.val, by omega⟩ := Fin.ext (by dsimp only [d]; omega)
        rw [hceq]
        refine bodyParity_congr_otherL a b h s q r0 (code i1) (code i2) d
          ((hpair_code i1).2.2 d) ((hpair_code i2).2.2 d) ?_ ?_
        · intro r hne
          have hout_r : (tileL a b h q hqa r ⟨s + d.val, by omega⟩).val < r0.val * h ∨
              (r0.val + 1) * h ≤ (tileL a b h q hqa r ⟨s + d.val, by omega⟩).val := by
            dsimp only [tileL]
            have hne' : r.val ≠ r0.val := fun hv => hne (Fin.ext hv)
            rcases lt_or_gt_of_ne hne' with hlt | hgt
            · left
              have h1 : (r.val + 1) * h ≤ r0.val * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt hlt)
              have h2 : r.val * h + h = (r.val + 1) * h := by ring
              omega
            · right
              have h1 : (r0.val + 1) * h ≤ r.val * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt hgt)
              omega
          have ho := offset_posL_lt a b h q hqa r0 _ hout_r
          rw [← readPat_winAt a b h hn (code i1) (posL a b h q hqa r0) _ ho, hpat,
            readPat_winAt a b h hn (code i2) (posL a b h q hqa r0) _ ho]
        · intro r
          have hout_r : (tileR a b h q hqb r ⟨s + d.val, by omega⟩).val < r0.val * h ∨
              (r0.val + 1) * h ≤ (tileR a b h q hqb r ⟨s + d.val, by omega⟩).val := by
            right; dsimp only [tileR]
            have h1 : (r0.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r0.isLt)
            omega
          have ho := offset_posL_lt a b h q hqa r0 _ hout_r
          rw [← readPat_winAt a b h hn (code i1) (posL a b h q hqa r0) _ ho, hpat,
            readPat_winAt a b h hn (code i2) (posL a b h q hqa r0) _ ho]
  have hright_inj : Function.Injective right := by
    intro i1 i2 hEq
    have hpos : posR a b h q hh hqb (rROf i1) = posR a b h q hh hqb (rROf i2) := congrArg Prod.fst hEq
    have hr : rROf i1 = rROf i2 := posR_inj a b h q hh hqb hpos
    have hpat : winAt (code i1) (posR a b h q hh hqb (rROf i1)) = winAt (code i2) (posR a b h q hh hqb (rROf i1)) := by
      have h2 := congrArg Prod.snd hEq; dsimp only [right] at h2; rw [← hr] at h2; exact h2
    dsimp only [winAt] at hpat
    apply hcode_inj
    funext t
    set r0 := rROf i1
    by_cases hout : t.val < a + r0.val * h ∨ a + (r0.val + 1) * h ≤ t.val
    · have ho := offset_posR_lt a b h q hh hqb r0 t hout
      rw [← readPat_winAt a b h hn (code i1) (posR a b h q hh hqb r0) t ho, hpat,
        readPat_winAt a b h hn (code i2) (posR a b h q hh hqb r0) t ho]
    · have htrng : a + r0.val * h ≤ t.val ∧ t.val < a + (r0.val + 1) * h := by omega
      have hr' : r0.val * h + h = (r0.val + 1) * h := by ring
      set c := t.val - (a + r0.val * h)
      have hch : c < h := by omega
      have hteq : t = tileR a b h q hqb r0 ⟨c, hch⟩ := Fin.ext (by dsimp only [tileR]; omega)
      rw [hteq]
      by_cases hcs : c < s
      · have hz1 := (hpair_code i1).2.1 r0
        have hz2 := (hpair_code i2).2.1 r0
        simp only [r0, decide_true] at hz1
        rw [← hr] at hz2; simp only [r0, decide_true] at hz2
        unfold isZeroR at hz1 hz2
        simp only [decide_eq_true_eq] at hz1 hz2
        exact (hz1 ⟨c, hcs⟩).trans (hz2 ⟨c, hcs⟩).symm
      · set d : Fin (h - s) := ⟨c - s, by omega⟩
        have hceq : (⟨c, hch⟩ : Fin h) = ⟨s + d.val, by omega⟩ := Fin.ext (by dsimp only [d]; omega)
        rw [hceq]
        refine bodyParity_congr_otherR a b h s q r0 (code i1) (code i2) d
          ((hpair_code i1).2.2 d) ((hpair_code i2).2.2 d) ?_ ?_
        · intro r
          have hout_r : (tileL a b h q hqa r ⟨s + d.val, by omega⟩).val < a + r0.val * h ∨
              a + (r0.val + 1) * h ≤ (tileL a b h q hqa r ⟨s + d.val, by omega⟩).val := by
            left; dsimp only [tileL]
            have h1 : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
            have h2 : r.val * h + h = (r.val + 1) * h := by ring
            omega
          have ho := offset_posR_lt a b h q hh hqb r0 _ hout_r
          rw [← readPat_winAt a b h hn (code i1) (posR a b h q hh hqb r0) _ ho, hpat,
            readPat_winAt a b h hn (code i2) (posR a b h q hh hqb r0) _ ho]
        · intro r hne
          have hout_r : (tileR a b h q hqb r ⟨s + d.val, by omega⟩).val < a + r0.val * h ∨
              a + (r0.val + 1) * h ≤ (tileR a b h q hqb r ⟨s + d.val, by omega⟩).val := by
            dsimp only [tileR]
            have hne' : r.val ≠ r0.val := fun hv => hne (Fin.ext hv)
            rcases lt_or_gt_of_ne hne' with hlt | hgt
            · left
              have h1 : (r.val + 1) * h ≤ r0.val * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt hlt)
              have h2 : r.val * h + h = (r.val + 1) * h := by ring
              omega
            · right
              have h1 : (r0.val + 1) * h ≤ r.val * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt hgt)
              omega
          have ho := offset_posR_lt a b h q hh hqb r0 _ hout_r
          rw [← readPat_winAt a b h hn (code i1) (posR a b h q hh hqb r0) _ ho, hpat,
            readPat_winAt a b h hn (code i2) (posR a b h q hh hqb r0) _ ho]
  have hisZeroL_readPosL : ∀ (x : Word) (r r' : Fin q), r' ≠ r →
      isZeroL a b h s q hsh hqa (fun t => readPat a b h (posL a b h q hqa r) t (winAt x (posL a b h q hqa r))) r' =
        isZeroL a b h s q hsh hqa x r' := by
    intro x r r' hne
    unfold isZeroL
    congr 1; apply propext
    refine forall_congr' fun c => ?_
    have hout : (tileL a b h q hqa r' ⟨c.val, by omega⟩).val < r.val * h ∨
        (r.val + 1) * h ≤ (tileL a b h q hqa r' ⟨c.val, by omega⟩).val := by
      dsimp only [tileL]
      have hne' : r'.val ≠ r.val := fun hv => hne (Fin.ext hv)
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · left
        have h1 : (r'.val + 1) * h ≤ r.val * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt hlt)
        have h2 : r'.val * h + h = (r'.val + 1) * h := by ring
        omega
      · right
        have h1 : (r.val + 1) * h ≤ r'.val * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt hgt)
        omega
    dsimp only [winAt]
    rw [readPat_winAt a b h hn x (posL a b h q hqa r) _ (offset_posL_lt a b h q hqa r _ hout)]
  have hisZeroR_readPosR : ∀ (x : Word) (r r' : Fin q), r' ≠ r →
      isZeroR a b h s q hsh hqb (fun t => readPat a b h (posR a b h q hh hqb r) t (winAt x (posR a b h q hh hqb r))) r' =
        isZeroR a b h s q hsh hqb x r' := by
    intro x r r' hne
    unfold isZeroR
    congr 1; apply propext
    refine forall_congr' fun c => ?_
    have hout : (tileR a b h q hqb r' ⟨c.val, by omega⟩).val < a + r.val * h ∨
        a + (r.val + 1) * h ≤ (tileR a b h q hqb r' ⟨c.val, by omega⟩).val := by
      dsimp only [tileR]
      have hne' : r'.val ≠ r.val := fun hv => hne (Fin.ext hv)
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · left
        have h1 : (r'.val + 1) * h ≤ r.val * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt hlt)
        have h2 : r'.val * h + h = (r'.val + 1) * h := by ring
        omega
      · right
        have h1 : (r.val + 1) * h ≤ r'.val * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt hgt)
        omega
    dsimp only [winAt]
    rw [readPat_winAt a b h hn x (posR a b h q hh hqb r) _ (offset_posR_lt a b h q hh hqb r _ hout)]
  have hisGood_readGuard : ∀ x : Word,
      isGoodOn a b h s q hsh hqa hqb (fun t => readPat a b h (iGuard a b h q hn) t (winAt x (iGuard a b h q hn))) =
        isGoodOn a b h s q hsh hqa hqb x := by
    intro x
    have hL : ∀ (r : Fin q) (c : Fin h),
        readPat a b h (iGuard a b h q hn) (tileL a b h q hqa r c) (winAt x (iGuard a b h q hn)) =
          x (tileL a b h q hqa r c) := by
      intro r c
      apply readPat_winAt a b h hn x (iGuard a b h q hn)
      apply offset_iGuard_lt a b h q hn hqb
      dsimp only [tileL]
      have hr : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
      have hr' : r.val * h + h = (r.val + 1) * h := by ring
      omega
    have hR : ∀ (r : Fin q) (c : Fin h),
        readPat a b h (iGuard a b h q hn) (tileR a b h q hqb r c) (winAt x (iGuard a b h q hn)) =
          x (tileR a b h q hqb r c) := by
      intro r c
      apply readPat_winAt a b h hn x (iGuard a b h q hn)
      apply offset_iGuard_lt a b h q hn hqb
      dsimp only [tileR]
      have hr : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
      have hr' : r.val * h + h = (r.val + 1) * h := by ring
      omega
    unfold isGoodOn isZeroL isZeroR bodyParity
    simp only [hL, hR]
  have hbase_left : ∀ i : Fin M, base (left i) = false := by
    intro i
    dsimp only [base, left]
    have hne : posL a b h q hqa (rLOf i) ≠ iGuard a b h q hn :=
      (iGuard_ne_posL a b h s q hn hs hsh hqa hqb (rLOf i)).symm
    have hex : ∃ r : Fin q, posL a b h q hqa (rLOf i) = posL a b h q hqa r ∧
        ∀ r' : Fin q, r' ≠ r → isZeroL a b h s q hsh hqa (fun t => readPat a b h (posL a b h q hqa (rLOf i)) t (winAt (code i) (posL a b h q hqa (rLOf i)))) r' = false := by
      refine ⟨rLOf i, rfl, fun r' hne' => ?_⟩
      rw [hisZeroL_readPosL (code i) (rLOf i) r' hne', (hpair_code i).1 r']
      simp [hne']
    simp only [hne, hex, ↓reduceIte]
  have hbase_right : ∀ i : Fin M, base (right i) = false := by
    intro i
    dsimp only [base, right]
    have hneG : posR a b h q hh hqb (rROf i) ≠ iGuard a b h q hn :=
      (iGuard_ne_posR a b h q hn hh hqb (rROf i)).symm
    have hneL : ¬∃ r : Fin q, posR a b h q hh hqb (rROf i) = posL a b h q hqa r ∧
        ∀ r' : Fin q, r' ≠ r → isZeroL a b h s q hsh hqa (fun t => readPat a b h (posR a b h q hh hqb (rROf i)) t (winAt (code i) (posR a b h q hh hqb (rROf i)))) r' = false := by
      rintro ⟨r, hEq, _⟩
      exact posL_ne_posR a b h q hh hqa hqb r (rROf i) hEq.symm
    have hex : ∃ r : Fin q, posR a b h q hh hqb (rROf i) = posR a b h q hh hqb r ∧
        ∀ r' : Fin q, r' ≠ r → isZeroR a b h s q hsh hqb (fun t => readPat a b h (posR a b h q hh hqb (rROf i)) t (winAt (code i) (posR a b h q hh hqb (rROf i)))) r' = false := by
      refine ⟨rROf i, rfl, fun r' hne' => ?_⟩
      rw [hisZeroR_readPosR (code i) (rROf i) r' hne', (hpair_code i).2.1 r']
      simp [hne']
    simp only [hneG, hneL, hex, ↓reduceIte]
  refine ⟨code, base, left, right, hcode_inj, hleft_inj, hright_inj, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_, hbase_left i, hbase_right i⟩
    · dsimp only [left, posL]
      have hr : ((rLOf i).val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt (rLOf i).isLt)
      omega
    · dsimp only [right, posR]; omega
  · intro A B
    ext x
    simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hsat
      have hG := hsat (iGuard a b h q hn)
      have hG_notL : (iGuard a b h q hn, winAt x (iGuard a b h q hn)) ∉ A.image left := by
        intro hmem; rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
        exact iGuard_ne_posL a b h s q hn hs hsh hqa hqb (rLOf i) (congrArg Prod.fst hi).symm
      have hG_notR : (iGuard a b h q hn, winAt x (iGuard a b h q hn)) ∉ B.image right := by
        intro hmem; rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
        exact iGuard_ne_posR a b h q hn hh hqb (rROf i) (congrArg Prod.fst hi).symm
      change (base (iGuard a b h q hn, winAt x (iGuard a b h q hn)) ||
        decide ((iGuard a b h q hn, winAt x (iGuard a b h q hn)) ∈ A.image left) ||
        decide ((iGuard a b h q hn, winAt x (iGuard a b h q hn)) ∈ B.image right)) = true at hG
      simp only [hG_notL, hG_notR, decide_false, Bool.or_false] at hG
      dsimp only [base] at hG
      simp only [↓reduceIte, hisGood_readGuard x] at hG
      let i : Fin M := eqv ⟨x, hG⟩
      have hci : code i = x := congrArg Subtype.val (eqv.symm_apply_apply ⟨x, hG⟩)
      refine Finset.mem_image.mpr ⟨i, Finset.mem_inter.mpr ⟨?_, ?_⟩, hci⟩
      · have hL := hsat (posL a b h q hqa (rLOf i))
        change (base (posL a b h q hqa (rLOf i), winAt x (posL a b h q hqa (rLOf i))) ||
          decide ((posL a b h q hqa (rLOf i), winAt x (posL a b h q hqa (rLOf i))) ∈ A.image left) ||
          decide ((posL a b h q hqa (rLOf i), winAt x (posL a b h q hqa (rLOf i))) ∈ B.image right)) = true at hL
        rw [← hci] at hL
        change (base (left i) || decide (left i ∈ A.image left) || decide (left i ∈ B.image right)) = true at hL
        have hnotR : left i ∉ B.image right := by
          intro hmem; rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
          exact posL_ne_posR a b h q hh hqa hqb (rLOf i) (rROf j) (congrArg Prod.fst hj).symm
        simp only [hbase_left i, hnotR, decide_false, Bool.false_or, Bool.or_false, decide_eq_true_eq] at hL
        rcases Finset.mem_image.mp hL with ⟨j, hjA, hjeq⟩
        rw [← hleft_inj hjeq]; exact hjA
      · have hR := hsat (posR a b h q hh hqb (rROf i))
        change (base (posR a b h q hh hqb (rROf i), winAt x (posR a b h q hh hqb (rROf i))) ||
          decide ((posR a b h q hh hqb (rROf i), winAt x (posR a b h q hh hqb (rROf i))) ∈ A.image left) ||
          decide ((posR a b h q hh hqb (rROf i), winAt x (posR a b h q hh hqb (rROf i))) ∈ B.image right)) = true at hR
        rw [← hci] at hR
        change (base (right i) || decide (right i ∈ A.image left) || decide (right i ∈ B.image right)) = true at hR
        have hnotL : right i ∉ A.image left := by
          intro hmem; rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
          exact posL_ne_posR a b h q hh hqa hqb (rLOf j) (rROf i) (congrArg Prod.fst hj)
        simp only [hbase_right i, hnotL, decide_false, Bool.false_or, decide_eq_true_eq] at hR
        rcases Finset.mem_image.mp hR with ⟨j, hjB, hjeq⟩
        rw [← hright_inj hjeq]; exact hjB
    · intro hxAB pos
      rcases Finset.mem_image.mp hxAB with ⟨i, hiAB, rfl⟩
      rcases Finset.mem_inter.mp hiAB with ⟨hiA, hiB⟩
      change (base (pos, winAt (code i) pos) ||
        decide ((pos, winAt (code i) pos) ∈ A.image left) ||
        decide ((pos, winAt (code i) pos) ∈ B.image right)) = true
      by_cases hposG : pos = iGuard a b h q hn
      · subst hposG
        have hb : base (iGuard a b h q hn, winAt (code i) (iGuard a b h q hn)) = true := by
          dsimp only [base]
          simp only [↓reduceIte, hisGood_readGuard (code i), hcode_good i]
        simp [hb]
      · by_cases hposL : pos = posL a b h q hqa (rLOf i)
        · subst hposL
          have hmem : (posL a b h q hqa (rLOf i), winAt (code i) (posL a b h q hqa (rLOf i))) ∈ A.image left :=
            Finset.mem_image.mpr ⟨i, hiA, rfl⟩
          simp [hmem]
        · by_cases hposR : pos = posR a b h q hh hqb (rROf i)
          · subst hposR
            have hmem : (posR a b h q hh hqb (rROf i), winAt (code i) (posR a b h q hh hqb (rROf i))) ∈ B.image right :=
              Finset.mem_image.mpr ⟨i, hiB, rfl⟩
            simp [hmem]
          · have hb : base (pos, winAt (code i) pos) = true := by
              dsimp only [base]
              have hnoL : ¬∃ r : Fin q, pos = posL a b h q hqa r ∧
                  ∀ r' : Fin q, r' ≠ r → isZeroL a b h s q hsh hqa (fun t => readPat a b h pos t (winAt (code i) pos)) r' = false := by
                rintro ⟨r, rfl, hall⟩
                have hne : rLOf i ≠ r := fun hEq => hposL (by rw [hEq])
                have h0 := hall (rLOf i) hne
                rw [hisZeroL_readPosL (code i) r (rLOf i) hne, (hpair_code i).1 (rLOf i)] at h0
                simp at h0
              have hnoR : ¬∃ r : Fin q, pos = posR a b h q hh hqb r ∧
                  ∀ r' : Fin q, r' ≠ r → isZeroR a b h s q hsh hqb (fun t => readPat a b h pos t (winAt (code i) pos)) r' = false := by
                rintro ⟨r, rfl, hall⟩
                have hne : rROf i ≠ r := fun hEq => hposR (by rw [hEq])
                have h0 := hall (rROf i) hne
                rw [hisZeroR_readPosR (code i) r (rROf i) hne, (hpair_code i).2.1 (rROf i)] at h0
                simp at h0
              simp only [hposG, hnoL, hnoR, ↓reduceIte]
            simp [hb]

end CyclicCode

end PEqualNP.Outside.L_lib_743_aux

theorem PEqualNP.Outside.L_lib_743 :
∀ (a b h s q : Nat) (hn : 0 < a+b), 0 < q → 0 < s → s ≤ h →
  q*h < a → (q+1)*h ≤ b →
  let n := a+b
  let M := q^2 * (2^s-1)^(2*(q-1)) * 2^(n-(2*q*s+(h-s)))
  let Word := Fin n → Bool
  let Pat := Fin (n-h) → Bool
  let Slot := Fin n × Pat
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let solutions := fun (tab : Slot → Bool) =>
    (Finset.univ : Finset Word).filter (fun x =>
      ∀ i : Fin n, tab (i,fun j => x (loc (i.val+j.val))) = true)
  ∃ (code : Fin M → Word) (base : Slot → Bool) (left right : Fin M → Slot),
    Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
    (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
      base (left i) = false ∧ base (right i) = false) ∧
    ∀ A B : Finset (Fin M), solutions (fun slot =>
      base slot || decide (slot ∈ A.image left) || decide (slot ∈ B.image right)) =
        (A ∩ B).image code := by
  intro a b h s q hn hq hs hsh hqa hqb n M Word Pat Slot loc solutions
  exact PEqualNP.Outside.L_lib_743_aux.main_743 a b h s q hn hq hs hsh hqa hqb

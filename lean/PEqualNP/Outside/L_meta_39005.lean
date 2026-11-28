import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39005

private def chiFn (bits : Nat → Bool) (j : Nat) : Bool :=
  xor (bits j) (!(bits (j + 1)) && bits (j + 2))

private def fromBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | m + 1, f => (if f 0 then 1 else 0) + 2 * fromBits m (fun i => f (i + 1))

private lemma fromBits_lt (m : Nat) (f : Nat → Bool) : fromBits m f < 2 ^ m := by
  induction m generalizing f with
  | zero => simp [fromBits]
  | succ m ih =>
    have hrec := ih (fun i => f (i + 1))
    cases h0 : f 0 <;> simp [fromBits, h0, pow_succ] <;> omega

private lemma testBit_fromBits (m : Nat) (f : Nat → Bool) (i : Nat) :
    (fromBits m f).testBit i = (decide (i < m) && f i) := by
  induction m generalizing f i with
  | zero => simp [fromBits]
  | succ m ih =>
    cases i with
    | zero =>
      simp only [fromBits, Nat.testBit_zero]
      have hmod : ((if f 0 then 1 else 0) + 2 * fromBits m (fun k => f (k + 1))) % 2 =
          if f 0 then 1 else 0 := by
        cases f 0 <;> simp
      rw [hmod]
      cases f 0 <;> simp
    | succ i =>
      simp only [fromBits, Nat.testBit_succ]
      have hdiv : ((if f 0 then 1 else 0) + 2 * fromBits m (fun k => f (k + 1))) / 2 =
          fromBits m (fun k => f (k + 1)) := by
        cases f 0
        · simp
        · simp; omega
      rw [hdiv, ih (fun k => f (k + 1)) i]
      by_cases h : i < m
      · have h' : i + 1 < m + 1 := by omega
        simp [h, h']
      · have h' : ¬ (i + 1 < m + 1) := by omega
        simp [h, h']

private def fillState (h : Nat) (z : Nat → Bool) (b0 b1 : Bool) : Nat → Bool × Bool
  | 0 => (b0, b1)
  | k + 1 =>
    let st := fillState h z b0 b1 k
    (xor (z (h - 1 - k)) (!st.1 && st.2), st.1)

private def fillBit (h : Nat) (z : Nat → Bool) (b0 b1 : Bool) (i : Nat) : Bool :=
  if i ≤ h then (fillState h z b0 b1 (h - i)).1
  else if i = h + 1 then b1
  else false

private lemma fillBit_h (h : Nat) (z : Nat → Bool) (b0 b1 : Bool) :
    fillBit h z b0 b1 h = b0 := by
  simp [fillBit, fillState]

private lemma fillBit_h1 (h : Nat) (z : Nat → Bool) (b0 b1 : Bool) :
    fillBit h z b0 b1 (h + 1) = b1 := by
  have hn : ¬ (h + 1 ≤ h) := by omega
  simp [fillBit, hn]

private lemma fillState_snd (h : Nat) (z : Nat → Bool) (b0 b1 : Bool) {k : Nat} (hk : k ≤ h) :
    (fillState h z b0 b1 k).2 = fillBit h z b0 b1 (h + 1 - k) := by
  cases k with
  | zero =>
    simp [fillState, fillBit_h1]
  | succ k =>
    have hle : h - k ≤ h := by omega
    have heq : h + 1 - (k + 1) = h - k := by omega
    have hsub : h - (h - k) = k := by omega
    rw [heq, fillBit]
    simp [fillState, hle, hsub]

private lemma chi_fillBit (h : Nat) (z : Nat → Bool) (b0 b1 : Bool) {j : Nat} (hj : j < h) :
    chiFn (fillBit h z b0 b1) j = z j := by
  have hj0 : j ≤ h := by omega
  have hj1 : j + 1 ≤ h := by omega
  have hsub : h - j = (h - 1 - j) + 1 := by omega
  have hsub1 : h - 1 - j ≤ h := by omega
  have hid : h - 1 - (h - 1 - j) = j := by omega
  have hs1 : (fillState h z b0 b1 (h - 1 - j)).1 = fillBit h z b0 b1 (j + 1) := by
    rw [fillBit]
    have hs : h - (j + 1) = h - 1 - j := by omega
    simp [hj1, hs]
  have hs2 : (fillState h z b0 b1 (h - 1 - j)).2 = fillBit h z b0 b1 (j + 2) := by
    rw [fillState_snd h z b0 b1 hsub1]
    have hs : h + 1 - (h - 1 - j) = j + 2 := by omega
    rw [hs]
  have hval : fillBit h z b0 b1 j =
      xor (z j) (!(fillBit h z b0 b1 (j + 1)) && fillBit h z b0 b1 (j + 2)) := by
    rw [fillBit]
    simp only [hj0, ↓reduceIte, hsub, fillState, hid, hs1, hs2]
  rw [chiFn, hval]
  cases z j <;> cases (!(fillBit h z b0 b1 (j + 1)) && fillBit h z b0 b1 (j + 2)) <;> rfl

private lemma fillState_shift (h L : Nat) (hl : L ≤ h) (z : Nat → Bool) (b0 b1 : Bool)
    {k : Nat} (hk : k ≤ L) :
    fillState h z b0 b1 k = fillState L (fun i => z (h - L + i)) b0 b1 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k ≤ L := by omega
    have hidx : h - L + (L - 1 - k) = h - 1 - k := by omega
    simp only [fillState, ih hk', hidx]

private lemma fillBit_shift (h L : Nat) (hl : L ≤ h) (z : Nat → Bool) (b0 b1 : Bool)
    {t : Nat} (ht : t ≤ L + 1) :
    fillBit h z b0 b1 (h - L + t) = fillBit L (fun i => z (h - L + i)) b0 b1 t := by
  by_cases htl : t ≤ L
  · have h1 : h - L + t ≤ h := by omega
    have h2 : h - (h - L + t) = L - t := by omega
    have h3 : L - t ≤ L := by omega
    simp only [fillBit, h1, htl, ↓reduceIte, h2]
    rw [fillState_shift h L hl z b0 b1 h3]
  · have ht_eq : t = L + 1 := by omega
    subst ht_eq
    have h1 : h - L + (L + 1) = h + 1 := by omega
    rw [h1, fillBit_h1, fillBit_h1]

private def zPad (h : Nat) (z : Fin h → Bool) (i : Nat) : Bool :=
  if hi : i < h then z ⟨i, hi⟩ else false

private def liftWord (h : Nat) (z : Fin h → Bool) (b0 b1 : Bool) : Nat :=
  fromBits (h + 2) (fillBit h (zPad h z) b0 b1)

private lemma liftWord_lt (h : Nat) (z : Fin h → Bool) (b0 b1 : Bool) :
    liftWord h z b0 b1 < 2 ^ (h + 2) :=
  fromBits_lt (h + 2) _

private lemma liftWord_testBit (h : Nat) (z : Fin h → Bool) (b0 b1 : Bool) {i : Nat}
    (hi : i < h + 2) :
    (liftWord h z b0 b1).testBit i = fillBit h (zPad h z) b0 b1 i := by
  simp [liftWord, testBit_fromBits, hi]

private lemma liftWord_mem_fiber (h : Nat) (z : Fin h → Bool) (b0 b1 : Bool) :
    liftWord h z b0 b1 < 2 ^ (h + 2) ∧
      ∀ j : Fin h, chiFn (fun i => (liftWord h z b0 b1).testBit i) j.val = z j := by
  refine ⟨liftWord_lt h z b0 b1, fun j => ?_⟩
  have h0 : j.val < h + 2 := by omega
  have h1 : j.val + 1 < h + 2 := by omega
  have h2 : j.val + 2 < h + 2 := by omega
  simp only [chiFn, liftWord_testBit h z b0 b1 h0, liftWord_testBit h z b0 b1 h1,
    liftWord_testBit h z b0 b1 h2]
  have hc := chi_fillBit h (zPad h z) b0 b1 j.isLt
  simpa [chiFn, zPad, j.isLt] using hc

private lemma xor_cancel_right {a b c : Bool} (h : xor a c = xor b c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp at h ⊢

private lemma fiber_eq_fillBit (h : Nat) (z : Fin h → Bool) (u : Nat)
    (hu_chi : ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = z j) :
    ∀ k : Nat, k ≤ h + 1 →
      u.testBit (h + 1 - k) = fillBit h (zPad h z) (u.testBit h) (u.testBit (h + 1)) (h + 1 - k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    cases k with
    | zero =>
      simp [fillBit_h1]
    | succ k =>
      cases k with
      | zero =>
        simp [fillBit_h]
      | succ k =>
        let j := h - 1 - k
        have hj_eq : h + 1 - (k + 2) = j := by omega
        have hj_lt : j < h := by omega
        have h1_lt : k + 1 ≤ h + 1 := by omega
        have h2_lt : k ≤ h + 1 := by omega
        have hj1 : h + 1 - (k + 1) = j + 1 := by omega
        have hj2 : h + 1 - k = j + 2 := by omega
        have ih1 := ih (k + 1) (by omega) h1_lt
        have ih2 := ih k (by omega) h2_lt
        rw [hj1] at ih1
        rw [hj2] at ih2
        rw [hj_eq]
        have hcu := hu_chi ⟨j, hj_lt⟩
        have hcf := chi_fillBit h (zPad h z) (u.testBit h) (u.testBit (h + 1)) hj_lt
        have hzp : zPad h z j = z ⟨j, hj_lt⟩ := by simp [zPad, hj_lt]
        rw [hzp] at hcf
        have heq : chiFn (fun i => u.testBit i) j =
            chiFn (fillBit h (zPad h z) (u.testBit h) (u.testBit (h + 1))) j :=
          hcu.trans hcf.symm
        simp only [chiFn, ih1, ih2] at heq
        exact xor_cancel_right heq

private lemma fiber_testBit_eq (h : Nat) (z : Fin h → Bool) {u : Nat}
    (hu_chi : ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = z j)
    {i : Nat} (hi : i < h + 2) :
    u.testBit i = fillBit h (zPad h z) (u.testBit h) (u.testBit (h + 1)) i := by
  have hk : h + 1 - i ≤ h + 1 := by omega
  have heq : h + 1 - (h + 1 - i) = i := by omega
  simpa [heq] using fiber_eq_fillBit h z u hu_chi (h + 1 - i) hk

private lemma fiber_unique_of_top (h : Nat) (z : Fin h → Bool) {u v : Nat}
    (hu_lt : u < 2 ^ (h + 2))
    (hu_chi : ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = z j)
    (hv_lt : v < 2 ^ (h + 2))
    (hv_chi : ∀ j : Fin h, chiFn (fun i => v.testBit i) j.val = z j)
    (hb0 : u.testBit h = v.testBit h)
    (hb1 : u.testBit (h + 1) = v.testBit (h + 1)) :
    u = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < h + 2
  · rw [fiber_testBit_eq h z hu_chi hi, fiber_testBit_eq h z hv_chi hi, hb0, hb1]
  · have hi' : h + 2 ≤ i := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hu_lt (Nat.pow_le_pow_right (by omega) hi')),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hv_lt (Nat.pow_le_pow_right (by omega) hi'))]

private def b0Of (b : Fin 4) : Bool := decide (b.val % 2 = 1)
private def b1Of (b : Fin 4) : Bool := decide (b.val / 2 % 2 = 1)

private lemma fin4_eq_of_b0_b1 {a b : Fin 4}
    (h0 : b0Of a = b0Of b) (h1 : b1Of a = b1Of b) : a = b := by
  fin_cases a <;> fin_cases b <;> simp [b0Of, b1Of] at h0 h1 ⊢

private def outCode (L pNat zNat : Nat) (b0 b1 : Bool) : Nat :=
  fromBits L (fun j =>
    chiFn (fun i => xor (fillBit L (fun k => zNat.testBit k) b0 b1 i) (pNat.testBit i)) j)

private def witRow (p : Nat) : Fin 8 × Fin 4 × Fin 4 :=
  match p / 2 with
  | 0 => (0, 0, 1) | 1 => (0, 0, 1) | 2 => (0, 0, 2) | 3 => (0, 1, 3)
  | 4 => (0, 0, 1) | 5 => (0, 0, 1) | 6 => (0, 1, 3) | 7 => (0, 1, 3)
  | 8 => (0, 0, 2) | 9 => (0, 1, 3) | 10 => (0, 0, 2) | 11 => (0, 1, 3)
  | 12 => (0, 1, 3) | 13 => (0, 1, 3) | 14 => (0, 1, 3) | 15 => (0, 1, 3)
  | 16 => (0, 0, 1) | 17 => (0, 0, 1) | 18 => (4, 0, 1) | 19 => (4, 0, 1)
  | 20 => (0, 0, 1) | 21 => (0, 0, 1) | 22 => (4, 0, 1) | 23 => (4, 0, 1)
  | 24 => (4, 2, 3) | 25 => (6, 2, 3) | 26 => (4, 2, 3) | 27 => (6, 2, 3)
  | 28 => (2, 2, 3) | 29 => (2, 2, 3) | 30 => (1, 2, 3) | 31 => (0, 2, 3)
  | 32 => (0, 0, 2) | 33 => (0, 1, 3) | 34 => (0, 0, 2) | 35 => (0, 1, 3)
  | 36 => (0, 1, 3) | 37 => (0, 1, 3) | 38 => (0, 1, 3) | 39 => (0, 1, 3)
  | 40 => (0, 0, 2) | 41 => (0, 1, 3) | 42 => (0, 0, 2) | 43 => (0, 1, 3)
  | 44 => (0, 1, 3) | 45 => (0, 1, 3) | 46 => (0, 1, 3) | 47 => (0, 1, 3)
  | 48 => (0, 0, 3) | 49 => (0, 0, 3) | 50 => (4, 0, 3) | 51 => (4, 0, 3)
  | 52 => (0, 0, 3) | 53 => (0, 0, 3) | 54 => (4, 0, 3) | 55 => (4, 0, 3)
  | 56 => (4, 1, 2) | 57 => (6, 1, 2) | 58 => (4, 1, 2) | 59 => (6, 1, 2)
  | 60 => (2, 1, 2) | 61 => (2, 1, 2) | 62 => (1, 1, 2) | _ => (0, 1, 2)

private def witCol (p : Nat) : Fin 4 × Fin 4 × Fin 4 :=
  match p / 2 with
  | 0 => (0, 0, 1) | 1 => (0, 0, 2) | 2 => (0, 0, 1) | 3 => (0, 1, 3)
  | 4 => (0, 0, 2) | 5 => (0, 0, 2) | 6 => (0, 1, 3) | 7 => (0, 1, 3)
  | 8 => (0, 0, 1) | 9 => (2, 0, 1) | 10 => (0, 0, 1) | 11 => (2, 0, 1)
  | 12 => (2, 2, 3) | 13 => (2, 2, 3) | 14 => (1, 2, 3) | 15 => (0, 2, 3)
  | 16 => (0, 0, 2) | 17 => (0, 0, 2) | 18 => (0, 1, 3) | 19 => (0, 1, 3)
  | 20 => (0, 0, 2) | 21 => (0, 0, 2) | 22 => (0, 1, 3) | 23 => (0, 1, 3)
  | 24 => (0, 0, 3) | 25 => (2, 0, 3) | 26 => (0, 0, 3) | 27 => (2, 0, 3)
  | 28 => (2, 1, 2) | 29 => (2, 1, 2) | 30 => (1, 1, 2) | _ => (0, 1, 2)

private def checkRowWit (p : Nat) : Bool :=
  let w := witRow p
  decide (w.2.1.val < w.2.2.val) &&
    decide (outCode 5 p (4 * w.1.val) (b0Of w.2.1) (b1Of w.2.1) =
      outCode 5 p (4 * w.1.val) (b0Of w.2.2) (b1Of w.2.2))

private def checkColWit (p : Nat) : Bool :=
  let w := witCol p
  decide (w.2.1.val < w.2.2.val) &&
    decide (outCode 4 p (4 * w.1.val) (b0Of w.2.1) (b1Of w.2.1) =
      outCode 4 p (4 * w.1.val) (b0Of w.2.2) (b1Of w.2.2))

private lemma row_slice0 : ∀ i : Fin 32, checkRowWit i.val = true := by decide
private lemma row_slice1 : ∀ i : Fin 32, checkRowWit (i.val + 32) = true := by decide
private lemma row_slice2 : ∀ i : Fin 32, checkRowWit (i.val + 64) = true := by decide
private lemma row_slice3 : ∀ i : Fin 32, checkRowWit (i.val + 96) = true := by decide

private lemma col_slice0 : ∀ i : Fin 32, checkColWit i.val = true := by decide
private lemma col_slice1 : ∀ i : Fin 32, checkColWit (i.val + 32) = true := by decide

private lemma row_all_collide (p : Fin 128) : checkRowWit p.val = true := by
  by_cases h0 : p.val < 32
  · exact row_slice0 ⟨p.val, h0⟩
  · by_cases h1 : p.val < 64
    · have := row_slice1 ⟨p.val - 32, by omega⟩
      have heq : p.val - 32 + 32 = p.val := by omega
      simpa [heq] using this
    · by_cases h2 : p.val < 96
      · have := row_slice2 ⟨p.val - 64, by omega⟩
        have heq : p.val - 64 + 64 = p.val := by omega
        simpa [heq] using this
      · have h3 : p.val - 96 < 32 := by omega
        have := row_slice3 ⟨p.val - 96, h3⟩
        have heq : p.val - 96 + 96 = p.val := by omega
        simpa [heq] using this

private lemma col_all_collide (p : Fin 64) : checkColWit p.val = true := by
  by_cases h0 : p.val < 32
  · exact col_slice0 ⟨p.val, h0⟩
  · have h1 : p.val - 32 < 32 := by omega
    have := col_slice1 ⟨p.val - 32, h1⟩
    have heq : p.val - 32 + 32 = p.val := by omega
    simpa [heq] using this

private def pfToNat (pf : Fin 7 → Bool) : Nat :=
  fromBits 7 (fun i => if hi : i < 7 then pf ⟨i, hi⟩ else false)

private def ptToNat (pt : Fin 6 → Bool) : Nat :=
  fromBits 6 (fun i => if hi : i < 6 then pt ⟨i, hi⟩ else false)

private lemma pfToNat_lt (pf : Fin 7 → Bool) : pfToNat pf < 128 := by
  simpa [pfToNat] using fromBits_lt 7 (fun i => if hi : i < 7 then pf ⟨i, hi⟩ else false)

private lemma ptToNat_lt (pt : Fin 6 → Bool) : ptToNat pt < 64 := by
  simpa [ptToNat] using fromBits_lt 6 (fun i => if hi : i < 6 then pt ⟨i, hi⟩ else false)

private lemma testBit_pfToNat (pf : Fin 7 → Bool) {t : Nat} (ht : t < 7) :
    (pfToNat pf).testBit t = pf ⟨t, ht⟩ := by
  simp [pfToNat, testBit_fromBits, ht]

private lemma testBit_ptToNat (pt : Fin 6 → Bool) {t : Nat} (ht : t < 6) :
    (ptToNat pt).testBit t = pt ⟨t, ht⟩ := by
  simp [ptToNat, testBit_fromBits, ht]

private lemma zPad_shift_of_mul4 {h L k : Nat} (hl : L ≤ h)
    (z : Fin h → Bool)
    (hz : ∀ t : Fin L, z ⟨h - L + t.val, by omega⟩ = k.testBit t.val)
    {t : Nat} (ht : t < L) :
    zPad h z (h - L + t) = k.testBit t := by
  have hlt : h - L + t < h := by omega
  simp only [zPad, hlt, ↓reduceDIte]
  exact hz ⟨t, ht⟩

private lemma exists_z_matching (h L : Nat) (hl : L ≤ h) (k : Nat) :
    ∃ z : Fin h → Bool, ∀ t : Fin L, z ⟨h - L + t.val, by omega⟩ = k.testBit t.val := by
  refine ⟨fun i => if h_lt : h - L ≤ i.val then k.testBit (i.val - (h - L)) else false, fun t => ?_⟩
  have hle : h - L ≤ h - L + t.val := by omega
  have hsub : h - L + t.val - (h - L) = t.val := by omega
  simp [hle, hsub]

private lemma not_inj_row_general (h : Nat) (hh : 5 ≤ h)
    (pulseR : Nat → Bool) :
    ∃ r : Fin h → Bool,
      ¬ Set.InjOn
        (fun u => (Finset.range 5).filter (fun j =>
          chiFn (fun i => xor (u.testBit i) (pulseR i)) (h - 5 + j)))
        {u : Nat | u < 2 ^ (h + 2) ∧ ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = r j} := by
  let pf : Fin 7 → Bool := fun t => pulseR (h - 5 + t.val)
  let pVal := pfToNat pf
  have hpVal : pVal < 128 := pfToNat_lt pf
  have hcol := row_all_collide ⟨pVal, hpVal⟩
  dsimp only [checkRowWit] at hcol
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcol
  let z3 := (witRow pVal).1
  let a := (witRow pVal).2.1
  let b := (witRow pVal).2.2
  have hab_lt : a.val < b.val := hcol.1
  have hout : outCode 5 pVal (4 * z3.val) (b0Of a) (b1Of a) =
      outCode 5 pVal (4 * z3.val) (b0Of b) (b1Of b) := hcol.2
  let zNat : Nat := 4 * z3.val
  rcases exists_z_matching h 5 hh zNat with ⟨r, hr_match⟩
  refine ⟨r, fun hinj => ?_⟩
  let u := liftWord h r (b0Of a) (b1Of a)
  let v := liftWord h r (b0Of b) (b1Of b)
  have hu_mem : u ∈ {u : Nat | u < 2 ^ (h + 2) ∧ ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = r j} :=
    liftWord_mem_fiber h r (b0Of a) (b1Of a)
  have hv_mem : v ∈ {u : Nat | u < 2 ^ (h + 2) ∧ ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = r j} :=
    liftWord_mem_fiber h r (b0Of b) (b1Of b)
  have htail_eq :
      (Finset.range 5).filter (fun j => chiFn (fun i => xor (u.testBit i) (pulseR i)) (h - 5 + j)) =
      (Finset.range 5).filter (fun j => chiFn (fun i => xor (v.testBit i) (pulseR i)) (h - 5 + j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    refine and_congr_right fun hj => ?_
    have hbit : ∀ w b0 b1 (hw : w = liftWord h r b0 b1),
        chiFn (fun i => xor (w.testBit i) (pulseR i)) (h - 5 + j) =
        (outCode 5 pVal zNat b0 b1).testBit j := by
      intro w b0 b1 hw
      subst hw
      have hi0 : h - 5 + j < h + 2 := by omega
      have hi1 : h - 5 + j + 1 < h + 2 := by omega
      have hi2 : h - 5 + j + 2 < h + 2 := by omega
      have hs0 := fillBit_shift h 5 hh (zPad h r) b0 b1 (t := j) (by omega)
      have hs1 := fillBit_shift h 5 hh (zPad h r) b0 b1 (t := j + 1) (by omega)
      have hs2 := fillBit_shift h 5 hh (zPad h r) b0 b1 (t := j + 2) (by omega)
      have hp0 : pVal.testBit j = pulseR (h - 5 + j) := by
        simpa [pVal, pf] using testBit_pfToNat pf (t := j) (by omega)
      have hp1 : pVal.testBit (j + 1) = pulseR (h - 5 + (j + 1)) := by
        simpa [pVal, pf] using testBit_pfToNat pf (t := j + 1) (by omega)
      have hp2 : pVal.testBit (j + 2) = pulseR (h - 5 + (j + 2)) := by
        simpa [pVal, pf] using testBit_pfToNat pf (t := j + 2) (by omega)
      have hsub1 : h - 5 + j + 1 = h - 5 + (j + 1) := by omega
      have hsub2 : h - 5 + j + 2 = h - 5 + (j + 2) := by omega
      have hzfun : ∀ t < 5, zPad h r (h - 5 + t) = zNat.testBit t :=
        fun t ht => zPad_shift_of_mul4 hh r hr_match ht
      have hfill : ∀ t ≤ 6,
          fillBit 5 (fun t => zPad h r (h - 5 + t)) b0 b1 t =
          fillBit 5 (fun t => zNat.testBit t) b0 b1 t := by
        intro t ht
        by_cases ht5 : t ≤ 5
        · simp only [fillBit, ht5, ↓reduceIte]
          have hst : ∀ m ≤ 5,
              fillState 5 (fun t => zPad h r (h - 5 + t)) b0 b1 m =
              fillState 5 (fun t => zNat.testBit t) b0 b1 m := by
            intro m hm
            induction m with
            | zero => rfl
            | succ m ihm =>
              have hlt5 : 5 - 1 - m < 5 := by omega
              simp only [fillState, ihm (by omega), hzfun _ hlt5]
          exact congrArg Prod.fst (hst (5 - t) (by omega))
        · have ht6 : t = 6 := by omega
          subst ht6
          rw [fillBit_h1, fillBit_h1]
      simp only [chiFn, outCode, testBit_fromBits, hj, decide_true, Bool.true_and]
      rw [liftWord_testBit h r b0 b1 hi0, liftWord_testBit h r b0 b1 hi1,
        liftWord_testBit h r b0 b1 hi2]
      rw [hsub1, hsub2, hs0, hs1, hs2]
      rw [hfill j (by omega), hfill (j + 1) (by omega), hfill (j + 2) (by omega)]
      rw [hp0, hp1, hp2, ← hsub1, ← hsub2]
    rw [hbit u (b0Of a) (b1Of a) rfl, hbit v (b0Of b) (b1Of b) rfl, hout]
  have huv := hinj hu_mem hv_mem htail_eq
  have h0 : (liftWord h r (b0Of a) (b1Of a)).testBit h =
      (liftWord h r (b0Of b) (b1Of b)).testBit h := congrArg (fun n => n.testBit h) huv
  have h1 : (liftWord h r (b0Of a) (b1Of a)).testBit (h + 1) =
      (liftWord h r (b0Of b) (b1Of b)).testBit (h + 1) := congrArg (fun n => n.testBit (h + 1)) huv
  rw [liftWord_testBit h r (b0Of a) (b1Of a) (by omega),
      liftWord_testBit h r (b0Of b) (b1Of b) (by omega), fillBit_h, fillBit_h] at h0
  rw [liftWord_testBit h r (b0Of a) (b1Of a) (by omega),
      liftWord_testBit h r (b0Of b) (b1Of b) (by omega), fillBit_h1, fillBit_h1] at h1
  have hab_eq : a = b := fin4_eq_of_b0_b1 h0 h1
  omega

private lemma not_inj_col_general (h : Nat) (hh : 5 ≤ h)
    (pulseC : Nat → Bool) :
    ∃ c : Fin h → Bool,
      ¬ Set.InjOn
        (fun u => (Finset.range 4).filter (fun j =>
          chiFn (fun i => xor (u.testBit i) (pulseC i)) (h - 4 + j)))
        {u : Nat | u < 2 ^ (h + 2) ∧ ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = c j} := by
  have hh4 : 4 ≤ h := by omega
  let pt : Fin 6 → Bool := fun t => pulseC (h - 4 + t.val)
  let pVal := ptToNat pt
  have hpVal : pVal < 64 := ptToNat_lt pt
  have hcol := col_all_collide ⟨pVal, hpVal⟩
  dsimp only [checkColWit] at hcol
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcol
  let z2 := (witCol pVal).1
  let a := (witCol pVal).2.1
  let b := (witCol pVal).2.2
  have hab_lt : a.val < b.val := hcol.1
  have hout : outCode 4 pVal (4 * z2.val) (b0Of a) (b1Of a) =
      outCode 4 pVal (4 * z2.val) (b0Of b) (b1Of b) := hcol.2
  let zNat : Nat := 4 * z2.val
  rcases exists_z_matching h 4 hh4 zNat with ⟨c, hc_match⟩
  refine ⟨c, fun hinj => ?_⟩
  let u := liftWord h c (b0Of a) (b1Of a)
  let v := liftWord h c (b0Of b) (b1Of b)
  have hu_mem : u ∈ {u : Nat | u < 2 ^ (h + 2) ∧ ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = c j} :=
    liftWord_mem_fiber h c (b0Of a) (b1Of a)
  have hv_mem : v ∈ {u : Nat | u < 2 ^ (h + 2) ∧ ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = c j} :=
    liftWord_mem_fiber h c (b0Of b) (b1Of b)
  have htail_eq :
      (Finset.range 4).filter (fun j => chiFn (fun i => xor (u.testBit i) (pulseC i)) (h - 4 + j)) =
      (Finset.range 4).filter (fun j => chiFn (fun i => xor (v.testBit i) (pulseC i)) (h - 4 + j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    refine and_congr_right fun hj => ?_
    have hbit : ∀ w b0 b1 (hw : w = liftWord h c b0 b1),
        chiFn (fun i => xor (w.testBit i) (pulseC i)) (h - 4 + j) =
        (outCode 4 pVal zNat b0 b1).testBit j := by
      intro w b0 b1 hw
      subst hw
      have hi0 : h - 4 + j < h + 2 := by omega
      have hi1 : h - 4 + j + 1 < h + 2 := by omega
      have hi2 : h - 4 + j + 2 < h + 2 := by omega
      have hs0 := fillBit_shift h 4 hh4 (zPad h c) b0 b1 (t := j) (by omega)
      have hs1 := fillBit_shift h 4 hh4 (zPad h c) b0 b1 (t := j + 1) (by omega)
      have hs2 := fillBit_shift h 4 hh4 (zPad h c) b0 b1 (t := j + 2) (by omega)
      have hp0 : pVal.testBit j = pulseC (h - 4 + j) := by
        simpa [pVal, pt] using testBit_ptToNat pt (t := j) (by omega)
      have hp1 : pVal.testBit (j + 1) = pulseC (h - 4 + (j + 1)) := by
        simpa [pVal, pt] using testBit_ptToNat pt (t := j + 1) (by omega)
      have hp2 : pVal.testBit (j + 2) = pulseC (h - 4 + (j + 2)) := by
        simpa [pVal, pt] using testBit_ptToNat pt (t := j + 2) (by omega)
      have hsub1 : h - 4 + j + 1 = h - 4 + (j + 1) := by omega
      have hsub2 : h - 4 + j + 2 = h - 4 + (j + 2) := by omega
      have hzfun : ∀ t < 4, zPad h c (h - 4 + t) = zNat.testBit t :=
        fun t ht => zPad_shift_of_mul4 hh4 c hc_match ht
      have hfill : ∀ t ≤ 5,
          fillBit 4 (fun t => zPad h c (h - 4 + t)) b0 b1 t =
          fillBit 4 (fun t => zNat.testBit t) b0 b1 t := by
        intro t ht
        by_cases ht4 : t ≤ 4
        · simp only [fillBit, ht4, ↓reduceIte]
          have hst : ∀ m ≤ 4,
              fillState 4 (fun t => zPad h c (h - 4 + t)) b0 b1 m =
              fillState 4 (fun t => zNat.testBit t) b0 b1 m := by
            intro m hm
            induction m with
            | zero => rfl
            | succ m ihm =>
              have hlt4 : 4 - 1 - m < 4 := by omega
              simp only [fillState, ihm (by omega), hzfun _ hlt4]
          exact congrArg Prod.fst (hst (4 - t) (by omega))
        · have ht5 : t = 5 := by omega
          subst ht5
          rw [fillBit_h1, fillBit_h1]
      simp only [chiFn, outCode, testBit_fromBits, hj, decide_true, Bool.true_and]
      rw [liftWord_testBit h c b0 b1 hi0, liftWord_testBit h c b0 b1 hi1,
        liftWord_testBit h c b0 b1 hi2]
      rw [hsub1, hsub2, hs0, hs1, hs2]
      rw [hfill j (by omega), hfill (j + 1) (by omega), hfill (j + 2) (by omega)]
      rw [hp0, hp1, hp2, ← hsub1, ← hsub2]
    rw [hbit u (b0Of a) (b1Of a) rfl, hbit v (b0Of b) (b1Of b) rfl, hout]
  have huv := hinj hu_mem hv_mem htail_eq
  have h0 : (liftWord h c (b0Of a) (b1Of a)).testBit h =
      (liftWord h c (b0Of b) (b1Of b)).testBit h := congrArg (fun n => n.testBit h) huv
  have h1 : (liftWord h c (b0Of a) (b1Of a)).testBit (h + 1) =
      (liftWord h c (b0Of b) (b1Of b)).testBit (h + 1) := congrArg (fun n => n.testBit (h + 1)) huv
  rw [liftWord_testBit h c (b0Of a) (b1Of a) (by omega),
      liftWord_testBit h c (b0Of b) (b1Of b) (by omega), fillBit_h, fillBit_h] at h0
  rw [liftWord_testBit h c (b0Of a) (b1Of a) (by omega),
      liftWord_testBit h c (b0Of b) (b1Of b) (by omega), fillBit_h1, fillBit_h1] at h1
  have hab_eq : a = b := fin4_eq_of_b0_b1 h0 h1
  omega

-- Fin 8 bitmask representation of subsets of Fin 3 for kernel-fast canSolve

private def inMask (m : Fin 8) (a : Fin 3) : Bool := m.val.testBit a.val

private def filtMask (m : Fin 8) (p : Fin 3 → Bool) : Fin 8 :=
  ⟨(if inMask m 0 && p 0 then 1 else 0) +
   (if inMask m 1 && p 1 then 2 else 0) +
   (if inMask m 2 && p 2 then 4 else 0), by
     cases inMask m 0 && p 0 <;> cases inMask m 1 && p 1 <;>
       cases inMask m 2 && p 2 <;> simp⟩

private lemma testBit_triple (b0 b1 b2 : Bool) (a : Fin 3) :
    ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0)).testBit a.val =
      match a with | ⟨0, _⟩ => b0 | ⟨1, _⟩ => b1 | ⟨2, _⟩ => b2 := by
  fin_cases a <;> cases b0 <;> cases b1 <;> cases b2 <;> decide

private lemma inMask_filtMask (m : Fin 8) (p : Fin 3 → Bool) (a : Fin 3) :
    inMask (filtMask m p) a = (inMask m a && p a) := by
  exact (testBit_triple (inMask m 0 && p 0) (inMask m 1 && p 1) (inMask m 2 && p 2) a).trans
    (by fin_cases a <;> rfl)

private lemma exists_inMask {m : Fin 8} (hm : m.val ≠ 0) : ∃ a : Fin 3, inMask m a = true := by
  fin_cases m
  · contradiction
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩

private def univMask : Fin 8 := ⟨7, by omega⟩

private lemma inMask_univMask (a : Fin 3) : inMask univMask a = true := by
  fin_cases a <;> decide

private def canSolve : Nat → Fin 8 → Fin 8 → Bool
  | 0, A, B =>
    !(decide (A.val ≠ 0) && decide (B.val ≠ 0)) ||
      (List.finRange 3).any (fun m => (!inMask A m) && (!inMask B m))
  | d + 1, A, B =>
    !(decide (A.val ≠ 0) && decide (B.val ≠ 0)) ||
      (List.finRange 8).any (fun mask =>
        canSolve d (filtMask A (fun a => !(mask.val.testBit a.val))) B &&
        canSolve d (filtMask A (fun a => mask.val.testBit a.val)) B) ||
      (List.finRange 8).any (fun mask =>
        canSolve d A (filtMask B (fun b => !(mask.val.testBit b.val))) &&
        canSolve d A (filtMask B (fun b => mask.val.testBit b.val)))

private lemma canSolve_2_univ : canSolve 2 univMask univMask = false := by
  decide

private lemma canSolve_nonempty {d : Nat} {A B : Fin 8}
    (h : canSolve d A B = false) : A.val ≠ 0 ∧ B.val ≠ 0 := by
  cases d with
  | zero =>
    simp only [canSolve, Bool.or_eq_false_iff, Bool.not_eq_false'] at h
    simpa [Bool.and_eq_true, decide_eq_true_eq] using h.1
  | succ d =>
    simp only [canSolve, Bool.or_eq_false_iff, Bool.not_eq_false'] at h
    simpa [Bool.and_eq_true, decide_eq_true_eq] using h.1.1

private lemma filtMask_false (A : Fin 8) :
    filtMask A (fun _ => true) = A ∧ filtMask A (fun _ => false) = 0 := by
  constructor
  · apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 3
    · have hi0 := inMask_filtMask A (fun _ => true) ⟨i, hi⟩
      simpa [inMask] using hi0
    · have ha1 : (filtMask A (fun _ => true)).val < 8 := (filtMask A (fun _ => true)).isLt
      have ha2 : A.val < 8 := A.isLt
      have hpow : (8 : Nat) ≤ 2 ^ i := by
        show (2 : Nat) ^ 3 ≤ 2 ^ i
        exact Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha1 hpow),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le ha2 hpow)]
  · apply Fin.ext
    simp [filtMask]

private lemma canSolve_zero_left (d : Nat) (B : Fin 8) : canSolve d 0 B = true := by
  cases d <;> simp [canSolve]

private lemma canSolve_mono {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {A B : Fin 8}
    (h : canSolve d₁ A B = true) : canSolve d₂ A B = true := by
  induction hle with
  | refl => exact h
  | @step d₂ hle ih =>
    simp only [canSolve, Bool.or_eq_true, List.any_eq_true]
    left; right
    refine ⟨0, List.mem_finRange 0, ?_⟩
    simp only [Bool.and_eq_true]
    have hf1 : filtMask A (fun a => !(0 : Fin 8).val.testBit a.val) = A := by
      have heq : (fun a : Fin 3 => !(0 : Fin 8).val.testBit a.val) = fun _ => true := by
        funext a; simp
      rw [heq]; exact (filtMask_false A).1
    have hf2 : filtMask A (fun a => (0 : Fin 8).val.testBit a.val) = 0 := by
      have heq : (fun a : Fin 3 => (0 : Fin 8).val.testBit a.val) = fun _ => false := by
        funext a; simp
      rw [heq]; exact (filtMask_false A).2
    rw [hf1, hf2]
    exact ⟨ih, canSolve_zero_left d₂ B⟩

private lemma canSolve_mono_false {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {A B : Fin 8}
    (h : canSolve d₂ A B = false) : canSolve d₁ A B = false := by
  cases h1 : canSolve d₁ A B with
  | false => rfl
  | true => exact absurd (canSolve_mono hle h1) (by rw [h]; decide)

private lemma exists_mask_for_pred (p : Fin 3 → Bool) :
    ∃ mask : Fin 8, ∀ a : Fin 3, mask.val.testBit a.val = p a := by
  refine ⟨⟨(if p 0 then 1 else 0) + (if p 1 then 2 else 0) + (if p 2 then 4 else 0), by
    cases p 0 <;> cases p 1 <;> cases p 2 <;> simp⟩, fun a => ?_⟩
  rw [testBit_triple]
  fin_cases a <;> rfl

private lemma canSolve_split_row {d : Nat} {A B : Fin 8}
    (h : canSolve (d + 1) A B = false) (p : Fin 3 → Bool) :
    ∃ bit : Bool, canSolve d (filtMask A (fun a => p a == bit)) B = false := by
  rcases exists_mask_for_pred p with ⟨mask, hmask⟩
  simp only [canSolve, Bool.or_eq_false_iff] at h
  have hmask' := h.1.2
  have hp0 : (fun a => !mask.val.testBit a.val) = fun a => p a == false := by
    funext a; simp [hmask a]
  have hp1 : (fun a => mask.val.testBit a.val) = fun a => p a == true := by
    funext a; simp [hmask a]
  cases hf : canSolve d (filtMask A (fun a => p a == false)) B with
  | false => exact ⟨false, hf⟩
  | true =>
    cases ht : canSolve d (filtMask A (fun a => p a == true)) B with
    | false => exact ⟨true, ht⟩
    | true =>
      have htrue : (List.finRange 8).any (fun m =>
          canSolve d (filtMask A (fun a => !(m.val.testBit a.val))) B &&
          canSolve d (filtMask A (fun a => m.val.testBit a.val)) B) = true := by
        rw [List.any_eq_true]
        refine ⟨mask, List.mem_finRange mask, ?_⟩
        rw [Bool.and_eq_true, hp0, hp1]
        exact ⟨hf, ht⟩
      rw [htrue] at hmask'
      exact absurd hmask' (by decide)

private lemma canSolve_split_col {d : Nat} {A B : Fin 8}
    (h : canSolve (d + 1) A B = false) (p : Fin 3 → Bool) :
    ∃ bit : Bool, canSolve d A (filtMask B (fun b => p b == bit)) = false := by
  rcases exists_mask_for_pred p with ⟨mask, hmask⟩
  simp only [canSolve, Bool.or_eq_false_iff] at h
  have hmask' := h.2
  have hp0 : (fun b => !mask.val.testBit b.val) = fun b => p b == false := by
    funext b; simp [hmask b]
  have hp1 : (fun b => mask.val.testBit b.val) = fun b => p b == true := by
    funext b; simp [hmask b]
  cases hf : canSolve d A (filtMask B (fun b => p b == false)) with
  | false => exact ⟨false, hf⟩
  | true =>
    cases ht : canSolve d A (filtMask B (fun b => p b == true)) with
    | false => exact ⟨true, ht⟩
    | true =>
      have htrue : (List.finRange 8).any (fun m =>
          canSolve d A (filtMask B (fun b => !(m.val.testBit b.val))) &&
          canSolve d A (filtMask B (fun b => m.val.testBit b.val))) = true := by
        rw [List.any_eq_true]
        refine ⟨mask, List.mem_finRange mask, ?_⟩
        rw [Bool.and_eq_true, hp0, hp1]
        exact ⟨hf, ht⟩
      rw [htrue] at hmask'
      exact absurd hmask' (by decide)

-- Upper-bound finite definitions

private def winKeyBits (m : Fin 3) (d : Fin 11) : Bool :=
  match m with
  | ⟨0, _⟩ => d.val = 1 ∨ d.val = 5 ∨ d.val = 6 ∨ d.val = 9
  | ⟨1, _⟩ => 4 ≤ d.val ∧ d.val ≤ 9
  | ⟨2, _⟩ => d.val = 1 ∨ d.val = 4 ∨ d.val = 7

private def winKeyMask (h k start : Nat) (m : Fin 3) (i : Nat) : Bool :=
  (List.finRange 11).any (fun d =>
    winKeyBits m d && decide ((start + h + k - 9 + d.val) % k = i))

private def mkKey (h k start : Nat) (m : Fin 3) : Fin (2 ^ k) :=
  ⟨fromBits k (winKeyMask h k start m), fromBits_lt k _⟩

private lemma pos_inj {start h k : Nat} (hk : h + 6 ≤ k) (hh : 5 ≤ h)
    {d₁ d₂ : Fin 11}
    (heq : (start + h + k - 9 + d₁.val) % k = (start + h + k - 9 + d₂.val) % k) :
    d₁ = d₂ := by
  have hk11 : 11 ≤ k := by omega
  have aux : ∀ a b : Fin 11, a.val ≤ b.val →
      (start + h + k - 9 + a.val) % k = (start + h + k - 9 + b.val) % k → a = b := by
    intro a b hab hmod
    set base := start + h + k - 9 + a.val
    set diff := b.val - a.val
    have hdiff : diff < k := by omega
    have hb : start + h + k - 9 + b.val = base + diff := by omega
    rw [hb, Nat.add_mod base diff k] at hmod
    have hmod_lt : base % k < k := Nat.mod_lt _ (by omega)
    by_cases hsum : base % k + diff < k
    · rw [Nat.mod_eq_of_lt hdiff, Nat.mod_eq_of_lt hsum] at hmod
      have : diff = 0 := by omega
      exact Fin.ext (by omega)
    · rw [Nat.mod_eq_of_lt hdiff] at hmod
      have hbd_lt : base % k + diff - k < k := by omega
      have hsub : (base % k + diff) % k = base % k + diff - k := by
        rw [Nat.mod_eq_sub_mod]
        all_goals first | exact Nat.mod_eq_of_lt hbd_lt | omega
      rw [hsub] at hmod
      omega
  by_cases hle : d₁.val ≤ d₂.val
  · exact aux d₁ d₂ hle heq
  · exact (aux d₂ d₁ (by omega) heq.symm).symm

private lemma mkKey_testBit {start h k : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    (m : Fin 3) (d : Fin 11) :
    (mkKey h k start m).val.testBit ((start + h + k - 9 + d.val) % k) = winKeyBits m d := by
  have hkpos : 0 < k := by omega
  have hlt : (start + h + k - 9 + d.val) % k < k := Nat.mod_lt _ hkpos
  simp only [mkKey, testBit_fromBits, hlt, decide_true, Bool.true_and, winKeyMask]
  cases hwd : winKeyBits m d with
  | true =>
    rw [List.any_eq_true]
    refine ⟨d, List.mem_finRange d, ?_⟩
    simp [hwd]
  | false =>
    rw [Bool.eq_false_iff]
    intro htrue
    rw [List.any_eq_true] at htrue
    rcases htrue with ⟨d', _, hd'⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd'
    have heq := pos_inj hk hh hd'.2
    subst heq
    rw [hwd] at hd'
    exact Bool.false_ne_true hd'.1

private def pfKey (m : Fin 3) : Nat :=
  fromBits 7 (fun i =>
    if hi : i < 7 then
      let b0 := winKeyBits m ⟨i + 4, by omega⟩
      let b1 := winKeyBits m ⟨i + 3, by omega⟩
      let b2 := winKeyBits m ⟨i + 2, by omega⟩
      xor b0 (xor b1 b2)
    else false)

private def ptKey (m : Fin 3) : Nat :=
  fromBits 6 (fun i =>
    if hi : i < 6 then
      let b1 := winKeyBits m ⟨i + 4, by omega⟩
      let b3 := winKeyBits m ⟨i + 2, by omega⟩
      let b5 := winKeyBits m ⟨i, by omega⟩
      xor b1 (xor b3 b5)
    else false)

private def rowBadMask (m : Fin 3) (z5 : Fin 32) : Bool :=
  let r2 := z5.val.testBit 2
  let r3 := z5.val.testBit 3
  let r4 := z5.val.testBit 4
  match m with
  | ⟨0, _⟩ => r3 && r4
  | ⟨1, _⟩ => r2 && !r3 && !r4
  | ⟨2, _⟩ => !r2 && !r3 && !r4

private def colBadMask (m : Fin 3) (z4 : Fin 16) : Bool :=
  let c2 := z4.val.testBit 2
  let c3 := z4.val.testBit 3
  match m with
  | ⟨0, _⟩ => c2 && !c3
  | ⟨1, _⟩ => c3
  | ⟨2, _⟩ => !c2 && !c3

private lemma key_row_inj_decide :
    ∀ (m : Fin 3) (z5 : Fin 32) (a b : Fin 4),
      rowBadMask m z5 = false → a.val < b.val →
        outCode 5 (pfKey m) z5.val (b0Of a) (b1Of a) ≠
        outCode 5 (pfKey m) z5.val (b0Of b) (b1Of b) := by
  decide

private lemma key_col_inj_decide :
    ∀ (m : Fin 3) (z4 : Fin 16) (a b : Fin 4),
      colBadMask m z4 = false → a.val < b.val →
        outCode 4 (ptKey m) z4.val (b0Of a) (b1Of a) ≠
        outCode 4 (ptKey m) z4.val (b0Of b) (b1Of b) := by
  decide

private lemma mkKey_inj {h k start : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k) :
    Function.Injective (mkKey h k start) := by
  intro m₁ m₂ heq
  have h1 := congrArg (fun x : Fin (2 ^ k) => x.val.testBit ((start + h + k - 9 + 1) % k)) heq
  have h5 := congrArg (fun x : Fin (2 ^ k) => x.val.testBit ((start + h + k - 9 + 5) % k)) heq
  have h6 := congrArg (fun x : Fin (2 ^ k) => x.val.testBit ((start + h + k - 9 + 6) % k)) heq
  rw [mkKey_testBit hh hk m₁ ⟨1, by omega⟩, mkKey_testBit hh hk m₂ ⟨1, by omega⟩] at h1
  rw [mkKey_testBit hh hk m₁ ⟨5, by omega⟩, mkKey_testBit hh hk m₂ ⟨5, by omega⟩] at h5
  rw [mkKey_testBit hh hk m₁ ⟨6, by omega⟩, mkKey_testBit hh hk m₂ ⟨6, by omega⟩] at h6
  fin_cases m₁ <;> fin_cases m₂ <;> simp [winKeyBits] at h1 h5 h6 ⊢

private lemma mkKey_pulseR {h k start : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    (m : Fin 3) {t : Nat} (ht : t < 7) :
    (let tap := fun (x j back : Nat) => x.testBit ((start + j + k - back) % k)
     xor (tap (mkKey h k start m).val (h - 5 + t) 0)
       (xor (tap (mkKey h k start m).val (h - 5 + t) 1)
            (tap (mkKey h k start m).val (h - 5 + t) 2))) = (pfKey m).testBit t := by
  dsimp only
  have e0 : start + (h - 5 + t) + k - 0 = start + h + k - 9 + (t + 4) := by omega
  have e1 : start + (h - 5 + t) + k - 1 = start + h + k - 9 + (t + 3) := by omega
  have e2 : start + (h - 5 + t) + k - 2 = start + h + k - 9 + (t + 2) := by omega
  rw [e0, e1, e2]
  rw [mkKey_testBit hh hk m ⟨t + 4, by omega⟩,
      mkKey_testBit hh hk m ⟨t + 3, by omega⟩,
      mkKey_testBit hh hk m ⟨t + 2, by omega⟩]
  simp [pfKey, testBit_fromBits, ht]

private lemma mkKey_pulseC {h k start : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    (m : Fin 3) {t : Nat} (ht : t < 6) :
    (let tap := fun (x j back : Nat) => x.testBit ((start + j + k - back) % k)
     xor (tap (mkKey h k start m).val (h - 4 + t) 1)
       (xor (tap (mkKey h k start m).val (h - 4 + t) 3)
            (tap (mkKey h k start m).val (h - 4 + t) 5))) = (ptKey m).testBit t := by
  dsimp only
  have e1 : start + (h - 4 + t) + k - 1 = start + h + k - 9 + (t + 4) := by omega
  have e3 : start + (h - 4 + t) + k - 3 = start + h + k - 9 + (t + 2) := by omega
  have e5 : start + (h - 4 + t) + k - 5 = start + h + k - 9 + t := by omega
  rw [e1, e3, e5]
  rw [mkKey_testBit hh hk m ⟨t + 4, by omega⟩,
      mkKey_testBit hh hk m ⟨t + 2, by omega⟩,
      mkKey_testBit hh hk m ⟨t, by omega⟩]
  simp [ptKey, testBit_fromBits, ht]

private def codeOfBool2 (b0 b1 : Bool) : Fin 4 :=
  ⟨(if b0 then 1 else 0) + 2 * (if b1 then 1 else 0), by cases b0 <;> cases b1 <;> simp⟩

private lemma b0Of_codeOfBool2 (b0 b1 : Bool) : b0Of (codeOfBool2 b0 b1) = b0 := by
  cases b0 <;> cases b1 <;> rfl

private lemma b1Of_codeOfBool2 (b0 b1 : Bool) : b1Of (codeOfBool2 b0 b1) = b1 := by
  cases b0 <;> cases b1 <;> rfl

private def packBits (L : Nat) (f : Fin L → Bool) : Fin (2 ^ L) :=
  ⟨fromBits L (fun i => if hi : i < L then f ⟨i, hi⟩ else false), fromBits_lt L _⟩

private lemma packBits_testBit (L : Nat) (f : Fin L → Bool) {t : Nat} (ht : t < L) :
    (packBits L f).val.testBit t = f ⟨t, ht⟩ := by
  simp [packBits, testBit_fromBits, ht]

private lemma mkKey_rowInj {h k start : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    (m : Fin 3) (r : Fin h → Bool)
    (hgood :
      let r2 := r ⟨h - 3, by omega⟩
      let r3 := r ⟨h - 2, by omega⟩
      let r4 := r ⟨h - 1, by omega⟩
      match m with
      | ⟨0, _⟩ => (r3 && r4) = false
      | ⟨1, _⟩ => (r2 && !r3 && !r4) = false
      | ⟨2, _⟩ => (!r2 && !r3 && !r4) = false) :
    Set.InjOn
      (fun u => (Finset.range 5).filter (fun j =>
        chiFn (fun i =>
          xor (u.testBit i)
            (let tap := fun (x j back : Nat) => x.testBit ((start + j + k - back) % k)
             xor (tap (mkKey h k start m).val i 0)
               (xor (tap (mkKey h k start m).val i 1)
                    (tap (mkKey h k start m).val i 2)))) (h - 5 + j)))
      {u : Nat | u < 2 ^ (h + 2) ∧ ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = r j} := by
  let z5 : Fin 32 := packBits 5 (fun t => r ⟨h - 5 + t.val, by omega⟩)
  have hmask : rowBadMask m z5 = false := by
    have ht2 : z5.val.testBit 2 = r ⟨h - 3, by omega⟩ := by
      have hidx : h - 5 + 2 = h - 3 := by omega
      simpa [z5, hidx] using packBits_testBit 5 (fun t => r ⟨h - 5 + t.val, by omega⟩) (t := 2) (by omega)
    have ht3 : z5.val.testBit 3 = r ⟨h - 2, by omega⟩ := by
      have hidx : h - 5 + 3 = h - 2 := by omega
      simpa [z5, hidx] using packBits_testBit 5 (fun t => r ⟨h - 5 + t.val, by omega⟩) (t := 3) (by omega)
    have ht4 : z5.val.testBit 4 = r ⟨h - 1, by omega⟩ := by
      have hidx : h - 5 + 4 = h - 1 := by omega
      simpa [z5, hidx] using packBits_testBit 5 (fun t => r ⟨h - 5 + t.val, by omega⟩) (t := 4) (by omega)
    fin_cases m <;> simpa [rowBadMask, ht2, ht3, ht4] using hgood
  intro u hu v hv htail
  have hout_eq :
      outCode 5 (pfKey m) z5.val (u.testBit h) (u.testBit (h + 1)) =
      outCode 5 (pfKey m) z5.val (v.testBit h) (v.testBit (h + 1)) := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 5
    · have hmem := Finset.ext_iff.mp htail j
      simp only [Finset.mem_filter, Finset.mem_range, hj, true_and] at hmem
      have hrewrite : ∀ w : Nat, (w < 2 ^ (h + 2) ∧ ∀ i : Fin h, chiFn (fun t => w.testBit t) i.val = r i) →
          chiFn (fun i =>
            xor (w.testBit i)
              (let tap := fun (x j back : Nat) => x.testBit ((start + j + k - back) % k)
               xor (tap (mkKey h k start m).val i 0)
                 (xor (tap (mkKey h k start m).val i 1)
                      (tap (mkKey h k start m).val i 2)))) (h - 5 + j) =
          (outCode 5 (pfKey m) z5.val (w.testBit h) (w.testBit (h + 1))).testBit j := by
        intro w hw
        have hi0 : h - 5 + j < h + 2 := by omega
        have hi1 : h - 5 + j + 1 < h + 2 := by omega
        have hi2 : h - 5 + j + 2 < h + 2 := by omega
        have hsub1 : h - 5 + j + 1 = h - 5 + (j + 1) := by omega
        have hsub2 : h - 5 + j + 2 = h - 5 + (j + 2) := by omega
        have hzfun : ∀ t < 5, zPad h r (h - 5 + t) = z5.val.testBit t := by
          intro t ht
          have hlt : h - 5 + t < h := by omega
          simp only [zPad, hlt, ↓reduceDIte]
          exact (packBits_testBit 5 (fun t => r ⟨h - 5 + t.val, by omega⟩) ht).symm
        have hfill : ∀ t ≤ 6,
            fillBit h (zPad h r) (w.testBit h) (w.testBit (h + 1)) (h - 5 + t) =
            fillBit 5 (fun k => z5.val.testBit k) (w.testBit h) (w.testBit (h + 1)) t := by
          intro t ht
          rw [fillBit_shift h 5 hh (zPad h r) (w.testBit h) (w.testBit (h + 1)) ht]
          by_cases ht5 : t ≤ 5
          · simp only [fillBit, ht5, ↓reduceIte]
            have hst : ∀ q ≤ 5,
                fillState 5 (fun i => zPad h r (h - 5 + i)) (w.testBit h) (w.testBit (h + 1)) q =
                fillState 5 (fun i => z5.val.testBit i) (w.testBit h) (w.testBit (h + 1)) q := by
              intro q hq
              induction q with
              | zero => rfl
              | succ q ihq =>
                simp only [fillState, ihq (by omega), hzfun (5 - 1 - q) (by omega)]
            exact congrArg Prod.fst (hst (5 - t) (by omega))
          · have ht6 : t = 6 := by omega
            subst ht6
            rw [fillBit_h1, fillBit_h1]
        simp only [chiFn, outCode, testBit_fromBits, hj, decide_true, Bool.true_and]
        rw [fiber_testBit_eq h r hw.2 hi0,
            fiber_testBit_eq h r hw.2 hi1,
            fiber_testBit_eq h r hw.2 hi2]
        rw [hsub1, hsub2]
        rw [mkKey_pulseR hh hk m (t := j) (by omega),
            mkKey_pulseR hh hk m (t := j + 1) (by omega),
            mkKey_pulseR hh hk m (t := j + 2) (by omega)]
        rw [hfill j (by omega), hfill (j + 1) (by omega), hfill (j + 2) (by omega)]
      rw [← hrewrite u hu, ← hrewrite v hv]
      exact Bool.eq_iff_iff.mpr hmem
    · simp [outCode, testBit_fromBits, hj]
  let a := codeOfBool2 (u.testBit h) (u.testBit (h + 1))
  let b := codeOfBool2 (v.testBit h) (v.testBit (h + 1))
  have ha0 : b0Of a = u.testBit h := b0Of_codeOfBool2 _ _
  have ha1 : b1Of a = u.testBit (h + 1) := b1Of_codeOfBool2 _ _
  have hb0 : b0Of b = v.testBit h := b0Of_codeOfBool2 _ _
  have hb1 : b1Of b = v.testBit (h + 1) := b1Of_codeOfBool2 _ _
  rw [← ha0, ← ha1, ← hb0, ← hb1] at hout_eq
  have hab : a = b := by
    by_cases hlt1 : a.val < b.val
    · exact absurd hout_eq (key_row_inj_decide m z5 a b hmask hlt1)
    · by_cases hlt2 : b.val < a.val
      · exact absurd hout_eq.symm (key_row_inj_decide m z5 b a hmask hlt2)
      · exact Fin.ext (by omega)
  have hu0 : u.testBit h = v.testBit h := by rw [← ha0, ← hb0, hab]
  have hu1 : u.testBit (h + 1) = v.testBit (h + 1) := by rw [← ha1, ← hb1, hab]
  exact fiber_unique_of_top h r hu.1 hu.2 hv.1 hv.2 hu0 hu1

private lemma mkKey_colInj {h k start : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    (m : Fin 3) (c : Fin h → Bool)
    (hgood :
      let c2 := c ⟨h - 2, by omega⟩
      let c3 := c ⟨h - 1, by omega⟩
      match m with
      | ⟨0, _⟩ => (c2 && !c3) = false
      | ⟨1, _⟩ => c3 = false
      | ⟨2, _⟩ => (!c2 && !c3) = false) :
    Set.InjOn
      (fun u => (Finset.range 4).filter (fun j =>
        chiFn (fun i =>
          xor (u.testBit i)
            (let tap := fun (x j back : Nat) => x.testBit ((start + j + k - back) % k)
             xor (tap (mkKey h k start m).val i 1)
               (xor (tap (mkKey h k start m).val i 3)
                    (tap (mkKey h k start m).val i 5)))) (h - 4 + j)))
      {u : Nat | u < 2 ^ (h + 2) ∧ ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = c j} := by
  have hh4 : 4 ≤ h := by omega
  let z4 : Fin 16 := packBits 4 (fun t => c ⟨h - 4 + t.val, by omega⟩)
  have hmask : colBadMask m z4 = false := by
    have ht2 : z4.val.testBit 2 = c ⟨h - 2, by omega⟩ := by
      have hidx : h - 4 + 2 = h - 2 := by omega
      simpa [z4, hidx] using packBits_testBit 4 (fun t => c ⟨h - 4 + t.val, by omega⟩) (t := 2) (by omega)
    have ht3 : z4.val.testBit 3 = c ⟨h - 1, by omega⟩ := by
      have hidx : h - 4 + 3 = h - 1 := by omega
      simpa [z4, hidx] using packBits_testBit 4 (fun t => c ⟨h - 4 + t.val, by omega⟩) (t := 3) (by omega)
    fin_cases m <;> simpa [colBadMask, ht2, ht3] using hgood
  intro u hu v hv htail
  have hout_eq :
      outCode 4 (ptKey m) z4.val (u.testBit h) (u.testBit (h + 1)) =
      outCode 4 (ptKey m) z4.val (v.testBit h) (v.testBit (h + 1)) := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 4
    · have hmem := Finset.ext_iff.mp htail j
      simp only [Finset.mem_filter, Finset.mem_range, hj, true_and] at hmem
      have hrewrite : ∀ w : Nat, (w < 2 ^ (h + 2) ∧ ∀ i : Fin h, chiFn (fun t => w.testBit t) i.val = c i) →
          chiFn (fun i =>
            xor (w.testBit i)
              (let tap := fun (x j back : Nat) => x.testBit ((start + j + k - back) % k)
               xor (tap (mkKey h k start m).val i 1)
                 (xor (tap (mkKey h k start m).val i 3)
                      (tap (mkKey h k start m).val i 5)))) (h - 4 + j) =
          (outCode 4 (ptKey m) z4.val (w.testBit h) (w.testBit (h + 1))).testBit j := by
        intro w hw
        have hi0 : h - 4 + j < h + 2 := by omega
        have hi1 : h - 4 + j + 1 < h + 2 := by omega
        have hi2 : h - 4 + j + 2 < h + 2 := by omega
        have hsub1 : h - 4 + j + 1 = h - 4 + (j + 1) := by omega
        have hsub2 : h - 4 + j + 2 = h - 4 + (j + 2) := by omega
        have hzfun : ∀ t < 4, zPad h c (h - 4 + t) = z4.val.testBit t := by
          intro t ht
          have hlt : h - 4 + t < h := by omega
          simp only [zPad, hlt, ↓reduceDIte]
          exact (packBits_testBit 4 (fun t => c ⟨h - 4 + t.val, by omega⟩) ht).symm
        have hfill : ∀ t ≤ 5,
            fillBit h (zPad h c) (w.testBit h) (w.testBit (h + 1)) (h - 4 + t) =
            fillBit 4 (fun k => z4.val.testBit k) (w.testBit h) (w.testBit (h + 1)) t := by
          intro t ht
          rw [fillBit_shift h 4 hh4 (zPad h c) (w.testBit h) (w.testBit (h + 1)) ht]
          by_cases ht4 : t ≤ 4
          · simp only [fillBit, ht4, ↓reduceIte]
            have hst : ∀ q ≤ 4,
                fillState 4 (fun i => zPad h c (h - 4 + i)) (w.testBit h) (w.testBit (h + 1)) q =
                fillState 4 (fun i => z4.val.testBit i) (w.testBit h) (w.testBit (h + 1)) q := by
              intro q hq
              induction q with
              | zero => rfl
              | succ q ihq =>
                simp only [fillState, ihq (by omega), hzfun (4 - 1 - q) (by omega)]
            exact congrArg Prod.fst (hst (4 - t) (by omega))
          · have ht5 : t = 5 := by omega
            subst ht5
            rw [fillBit_h1, fillBit_h1]
        simp only [chiFn, outCode, testBit_fromBits, hj, decide_true, Bool.true_and]
        rw [fiber_testBit_eq h c hw.2 hi0,
            fiber_testBit_eq h c hw.2 hi1,
            fiber_testBit_eq h c hw.2 hi2]
        rw [hsub1, hsub2]
        rw [mkKey_pulseC hh hk m (t := j) (by omega),
            mkKey_pulseC hh hk m (t := j + 1) (by omega),
            mkKey_pulseC hh hk m (t := j + 2) (by omega)]
        rw [hfill j (by omega), hfill (j + 1) (by omega), hfill (j + 2) (by omega)]
      rw [← hrewrite u hu, ← hrewrite v hv]
      exact Bool.eq_iff_iff.mpr hmem
    · simp [outCode, testBit_fromBits, hj]
  let a := codeOfBool2 (u.testBit h) (u.testBit (h + 1))
  let b := codeOfBool2 (v.testBit h) (v.testBit (h + 1))
  have ha0 : b0Of a = u.testBit h := b0Of_codeOfBool2 _ _
  have ha1 : b1Of a = u.testBit (h + 1) := b1Of_codeOfBool2 _ _
  have hb0 : b0Of b = v.testBit h := b0Of_codeOfBool2 _ _
  have hb1 : b1Of b = v.testBit (h + 1) := b1Of_codeOfBool2 _ _
  rw [← ha0, ← ha1, ← hb0, ← hb1] at hout_eq
  have hab : a = b := by
    by_cases hlt1 : a.val < b.val
    · exact absurd hout_eq (key_col_inj_decide m z4 a b hmask hlt1)
    · by_cases hlt2 : b.val < a.val
      · exact absurd hout_eq.symm (key_col_inj_decide m z4 b a hmask hlt2)
      · exact Fin.ext (by omega)
  have hu0 : u.testBit h = v.testBit h := by rw [← ha0, ← hb0, hab]
  have hu1 : u.testBit (h + 1) = v.testBit (h + 1) := by rw [← ha1, ← hb1, hab]
  exact fiber_unique_of_top h c hu.1 hu.2 hv.1 hv.2 hu0 hu1

-- Adaptive 3-query protocol definitions

private def revGet (xs : List Bool) (idx : Nat) : Bool :=
  (xs[xs.length - 1 - idx]?).getD false

private lemma revGet_cons_head (b : Bool) (xs : List Bool) :
    revGet (b :: xs) xs.length = b := by
  simp [revGet]

private lemma revGet_cons_prev (b : Bool) (xs : List Bool) {idx : Nat} (hidx : idx < xs.length) :
    revGet (b :: xs) idx = revGet xs idx := by
  have h1 : (b :: xs).length - 1 - idx = (xs.length - 1 - idx) + 1 := by
    simp only [List.length_cons]
    omega
  rw [revGet, h1]
  rfl

private def askProto (h n : Nat) (hh : 5 ≤ h) (hist : List Bool) :
    Option (Fin n × Bool × Fin h) :=
  let t := hist.length
  let j := t / 3
  if hj : j < n then
    let jF : Fin n := ⟨j, hj⟩
    let s := t % 3
    if s = 0 then
      some (jF, true, ⟨h - 1, by omega⟩)
    else if s = 1 then
      let b0 := revGet hist (3 * j)
      if b0 then some (jF, false, ⟨h - 1, by omega⟩)
      else some (jF, true, ⟨h - 2, by omega⟩)
    else
      let b0 := revGet hist (3 * j)
      let b1 := revGet hist (3 * j + 1)
      if b0 then none
      else if !b1 then some (jF, false, ⟨h - 1, by omega⟩)
      else some (jF, false, ⟨h - 3, by omega⟩)
  else none

private def outProto (n : Nat) (trace : List Bool) (j : Fin n) : Fin 3 :=
  let b0 := revGet trace (3 * j.val)
  let b1 := revGet trace (3 * j.val + 1)
  let b2 := revGet trace (3 * j.val + 2)
  if b0 then
    if !b1 then 0 else 2
  else
    if !b1 then
      if !b2 then 0 else 1
    else
      if !b2 then 1 else 2

private lemma askProto_0 {h n : Nat} (hh : 5 ≤ h) {hist : List Bool} {j : Fin n}
    (hlen : hist.length = 3 * j.val) :
    askProto h n hh hist = some (j, true, ⟨h - 1, by omega⟩) := by
  have hdiv : hist.length / 3 = j.val := by omega
  have hmod : hist.length % 3 = 0 := by omega
  simp [askProto, hdiv, hmod, j.isLt]

private lemma askProto_1 {h n : Nat} (hh : 5 ≤ h) {hist : List Bool} {j : Fin n}
    (hlen : hist.length = 3 * j.val + 1) :
    askProto h n hh hist =
      if revGet hist (3 * j.val) then some (j, false, ⟨h - 1, by omega⟩)
      else some (j, true, ⟨h - 2, by omega⟩) := by
  have hdiv : hist.length / 3 = j.val := by omega
  have hmod : hist.length % 3 = 1 := by omega
  simp [askProto, hdiv, hmod, j.isLt]

private lemma askProto_2 {h n : Nat} (hh : 5 ≤ h) {hist : List Bool} {j : Fin n}
    (hlen : hist.length = 3 * j.val + 2) :
    askProto h n hh hist =
      if revGet hist (3 * j.val) then none
      else if !revGet hist (3 * j.val + 1) then some (j, false, ⟨h - 1, by omega⟩)
      else some (j, false, ⟨h - 3, by omega⟩) := by
  have hdiv : hist.length / 3 = j.val := by omega
  have hmod : hist.length % 3 = 2 := by omega
  simp [askProto, hdiv, hmod, j.isLt]

private lemma foldl_len {α : Type*} (f : List α → Nat → List α)
    (hf : ∀ xs x, (f xs x).length = xs.length + 1) (t : Nat) :
    ((List.range t).foldl f []).length = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hf, ih]

private lemma foldl_revGet_lt (eval : List Bool → Bool)
    {t k : Nat} (hk : k < t) :
    revGet ((List.range t).foldl (fun hs _ => eval hs :: hs) []) k =
      eval ((List.range k).foldl (fun hs _ => eval hs :: hs) []) := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : ((List.range t).foldl (fun hs _ => eval hs :: hs) []).length = t := by
      apply foldl_len
      intro xs x; rfl
    by_cases hkt : k = t
    · subst hkt
      conv_lhs => arg 2; rw [← hlen]
      exact revGet_cons_head _ _
    · have hk_lt : k < t := by omega
      rw [revGet_cons_prev _ _ (by rw [hlen]; exact hk_lt)]
      exact ih hk_lt

private lemma filtMask_nonempty_of {m : Fin 8} {p : Fin 3 → Bool} {a₀ : Fin 3}
    (hm : inMask m a₀ = true) : (filtMask m (fun a => p a == p a₀)).val ≠ 0 := by
  intro hzero
  have hze : filtMask m (fun a => p a == p a₀) = 0 := Fin.ext hzero
  have ht := congrArg (fun k : Fin 8 => inMask k a₀) hze
  rw [inMask_filtMask, hm] at ht
  have h0b : inMask 0 a₀ = false := by fin_cases a₀ <;> rfl
  rw [h0b] at ht
  simp at ht

private lemma sum_rem_step {n : Nat} (rem : Fin n → Nat) (j₀ : Fin n) (hpos : 0 < rem j₀) :
    Finset.univ.sum rem = Finset.univ.sum (fun j => if j = j₀ then rem j₀ - 1 else rem j) + 1 := by
  let rem' : Fin n → Nat := fun j => if j = j₀ then rem j₀ - 1 else rem j
  have hrest : (Finset.univ.erase j₀).sum rem = (Finset.univ.erase j₀).sum rem' := by
    apply Finset.sum_congr rfl
    intro j hj
    have hnej : j ≠ j₀ := (Finset.mem_erase.mp hj).1
    simp [rem', hnej]
  have hj0val : rem' j₀ = rem j₀ - 1 := by simp [rem']
  calc
    Finset.univ.sum rem
        = rem j₀ + (Finset.univ.erase j₀).sum rem := (Finset.add_sum_erase Finset.univ rem (Finset.mem_univ j₀)).symm
    _ = (rem' j₀ + 1) + (Finset.univ.erase j₀).sum rem' := by rw [hrest, hj0val]; omega
    _ = (rem' j₀ + (Finset.univ.erase j₀).sum rem') + 1 := by omega
    _ = Finset.univ.sum rem' + 1 := by rw [Finset.add_sum_erase Finset.univ rem' (Finset.mem_univ j₀)]

private lemma lower_bound_adv
    {h n q : Nat}
    (ask : List Bool → Option (Fin n × Bool × Fin h))
    (out : List Bool → Fin n → Fin 3)
    (r₀ c₀ : Fin 3 → Fin h → Bool)
    (hq : q < 3 * n) :
    ∃ (r c : Fin n → Fin h → Bool) (j : Fin n),
      let trace := (List.range q).foldl (fun (hist : List Bool) _ =>
        let bit := ((ask hist).map (fun u =>
          if u.2.1 then c u.1 u.2.2 else r u.1 u.2.2)).getD false
        bit :: hist) []
      r j = r₀ (out trace j) ∨ c j = c₀ (out trace j) := by
  have hinv : ∀ t : Nat,
      ∃ (r_rem : Fin n → Fin 8) (c_rem : Fin n → Fin 8)
        (rem : Fin n → Nat) (hist : List Bool),
        (∀ j, (r_rem j).val ≠ 0 ∧ (c_rem j).val ≠ 0) ∧
        (∀ j, 0 < rem j → canSolve (rem j - 1) (r_rem j) (c_rem j) = false) ∧
        3 * n ≤ t + Finset.univ.sum rem ∧
        (∀ (r c : Fin n → Fin h → Bool),
          (∀ j, ∃ a : Fin 3, inMask (r_rem j) a = true ∧ r j = r₀ a) →
          (∀ j, ∃ b : Fin 3, inMask (c_rem j) b = true ∧ c j = c₀ b) →
          (List.range t).foldl (fun (hs : List Bool) _ =>
            let bit := ((ask hs).map (fun u =>
              if u.2.1 then c u.1 u.2.2 else r u.1 u.2.2)).getD false
            bit :: hs) [] = hist) := by
    intro t
    induction t with
    | zero =>
      refine ⟨fun _ => univMask, fun _ => univMask, fun _ => 3, [], ?_, ?_, ?_, ?_⟩
      · intro _; exact ⟨by simp [univMask], by simp [univMask]⟩
      · intro _ _; exact canSolve_2_univ
      · simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        omega
      · intro _ _ _ _; rfl
    | succ t ih =>
      rcases ih with ⟨r_rem, c_rem, rem, hist, hne, hcs, hsum, hfold⟩
      cases hask : ask hist with
      | none =>
        refine ⟨r_rem, c_rem, rem, false :: hist, hne, hcs, by omega, ?_⟩
        intro r c hr hc
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hfold r c hr hc]
        simp [hask]
      | some u =>
        rcases u with ⟨j₀, side, coord⟩
        cases side with
        | false =>
          by_cases hrem0 : rem j₀ = 0
          · rcases exists_inMask (hne j₀).1 with ⟨a₀, ha₀⟩
            let bit := r₀ a₀ coord
            let r_rem' : Fin n → Fin 8 := fun j =>
              if j = j₀ then filtMask (r_rem j₀) (fun a => r₀ a coord == bit) else r_rem j
            refine ⟨r_rem', c_rem, rem, bit :: hist, ?_, ?_, by omega, ?_⟩
            · intro j
              by_cases hj : j = j₀
              · subst hj
                refine ⟨?_, (hne j).2⟩
                simpa [r_rem', bit] using filtMask_nonempty_of (p := fun a => r₀ a coord) ha₀
              · simp [r_rem', hj, hne j]
            · intro j hjpos
              have hnej : j ≠ j₀ := by intro heq; subst heq; omega
              simpa [r_rem', hnej] using hcs j hjpos
            · intro r c hr hc
              have hr0 : ∀ j, ∃ a : Fin 3, inMask (r_rem j) a = true ∧ r j = r₀ a := by
                intro j
                rcases hr j with ⟨a, ha, haeq⟩
                by_cases hj : j = j₀
                · subst hj
                  simp only [r_rem', ↓reduceIte, inMask_filtMask, Bool.and_eq_true] at ha
                  exact ⟨a, ha.1, haeq⟩
                · simp only [r_rem', hj, ↓reduceIte] at ha
                  exact ⟨a, ha, haeq⟩
              rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
                hfold r c hr0 hc]
              rcases hr j₀ with ⟨a, ha, haeq⟩
              simp only [r_rem', ↓reduceIte, inMask_filtMask, Bool.and_eq_true, beq_iff_eq] at ha
              simp [hask, haeq, ha.2]
          · have hrem_pos : 0 < rem j₀ := by omega
            let rem' : Fin n → Nat := fun j => if j = j₀ then rem j₀ - 1 else rem j
            have hsum_step := sum_rem_step rem j₀ hrem_pos
            have hsum' : 3 * n ≤ t + 1 + Finset.univ.sum rem' := by
              have hrem_eq : Finset.univ.sum rem' = Finset.univ.sum (fun j => if j = j₀ then rem j₀ - 1 else rem j) := rfl
              omega
            by_cases hrem1 : rem j₀ = 1
            · rcases exists_inMask (hne j₀).1 with ⟨a₀, ha₀⟩
              let bit := r₀ a₀ coord
              let r_rem' : Fin n → Fin 8 := fun j =>
                if j = j₀ then filtMask (r_rem j₀) (fun a => r₀ a coord == bit) else r_rem j
              refine ⟨r_rem', c_rem, rem', bit :: hist, ?_, ?_, hsum', ?_⟩
              · intro j
                by_cases hj : j = j₀
                · subst hj
                  refine ⟨?_, (hne j).2⟩
                  simpa [r_rem', bit] using filtMask_nonempty_of (p := fun a => r₀ a coord) ha₀
                · simp [r_rem', hj, hne j]
              · intro j hjpos
                by_cases hj : j = j₀
                · subst hj; simp [rem', hrem1] at hjpos
                · simp only [rem', hj, ↓reduceIte] at hjpos ⊢
                  simpa [r_rem', hj] using hcs j hjpos
              · intro r c hr hc
                have hr0 : ∀ j, ∃ a : Fin 3, inMask (r_rem j) a = true ∧ r j = r₀ a := by
                  intro j
                  rcases hr j with ⟨a, ha, haeq⟩
                  by_cases hj : j = j₀
                  · subst hj
                    simp only [r_rem', ↓reduceIte, inMask_filtMask, Bool.and_eq_true] at ha
                    exact ⟨a, ha.1, haeq⟩
                  · simp only [r_rem', hj, ↓reduceIte] at ha
                    exact ⟨a, ha, haeq⟩
                rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
                  hfold r c hr0 hc]
                rcases hr j₀ with ⟨a, ha, haeq⟩
                simp only [r_rem', ↓reduceIte, inMask_filtMask, Bool.and_eq_true, beq_iff_eq] at ha
                simp [hask, haeq, ha.2]
            · have hrem2 : 2 ≤ rem j₀ := by omega
              have hcs0 : canSolve (rem j₀ - 2 + 1) (r_rem j₀) (c_rem j₀) = false := by
                have heq : rem j₀ - 2 + 1 = rem j₀ - 1 := by omega
                rw [heq]; exact hcs j₀ hrem_pos
              rcases canSolve_split_row hcs0 (fun a => r₀ a coord) with ⟨bit, hbit⟩
              have hne_new := canSolve_nonempty hbit
              let r_rem' : Fin n → Fin 8 := fun j =>
                if j = j₀ then filtMask (r_rem j₀) (fun a => r₀ a coord == bit) else r_rem j
              refine ⟨r_rem', c_rem, rem', bit :: hist, ?_, ?_, hsum', ?_⟩
              · intro j
                by_cases hj : j = j₀
                · subst hj; exact ⟨by simpa [r_rem'] using hne_new.1, (hne j).2⟩
                · simp [r_rem', hj, hne j]
              · intro j hjpos
                by_cases hj : j = j₀
                · subst hj
                  have heq : rem' j - 1 = rem j - 2 := by simp [rem']; omega
                  rw [heq]; simpa [r_rem'] using hbit
                · simp only [rem', hj, ↓reduceIte] at hjpos ⊢
                  simpa [r_rem', hj] using hcs j hjpos
              · intro r c hr hc
                have hr0 : ∀ j, ∃ a : Fin 3, inMask (r_rem j) a = true ∧ r j = r₀ a := by
                  intro j
                  rcases hr j with ⟨a, ha, haeq⟩
                  by_cases hj : j = j₀
                  · subst hj
                    simp only [r_rem', ↓reduceIte, inMask_filtMask, Bool.and_eq_true] at ha
                    exact ⟨a, ha.1, haeq⟩
                  · simp only [r_rem', hj, ↓reduceIte] at ha
                    exact ⟨a, ha, haeq⟩
                rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
                  hfold r c hr0 hc]
                rcases hr j₀ with ⟨a, ha, haeq⟩
                simp only [r_rem', ↓reduceIte, inMask_filtMask, Bool.and_eq_true, beq_iff_eq] at ha
                simp [hask, haeq, ha.2]
        | true =>
          by_cases hrem0 : rem j₀ = 0
          · rcases exists_inMask (hne j₀).2 with ⟨b₀, hb₀⟩
            let bit := c₀ b₀ coord
            let c_rem' : Fin n → Fin 8 := fun j =>
              if j = j₀ then filtMask (c_rem j₀) (fun b => c₀ b coord == bit) else c_rem j
            refine ⟨r_rem, c_rem', rem, bit :: hist, ?_, ?_, by omega, ?_⟩
            · intro j
              by_cases hj : j = j₀
              · subst hj
                refine ⟨(hne j).1, ?_⟩
                simpa [c_rem', bit] using filtMask_nonempty_of (p := fun b => c₀ b coord) hb₀
              · simp [c_rem', hj, hne j]
            · intro j hjpos
              have hnej : j ≠ j₀ := by intro heq; subst heq; omega
              simpa [c_rem', hnej] using hcs j hjpos
            · intro r c hr hc
              have hc0 : ∀ j, ∃ b : Fin 3, inMask (c_rem j) b = true ∧ c j = c₀ b := by
                intro j
                rcases hc j with ⟨b, hb, hbeq⟩
                by_cases hj : j = j₀
                · subst hj
                  simp only [c_rem', ↓reduceIte, inMask_filtMask, Bool.and_eq_true] at hb
                  exact ⟨b, hb.1, hbeq⟩
                · simp only [c_rem', hj, ↓reduceIte] at hb
                  exact ⟨b, hb, hbeq⟩
              rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
                hfold r c hr hc0]
              rcases hc j₀ with ⟨b, hb, hbeq⟩
              simp only [c_rem', ↓reduceIte, inMask_filtMask, Bool.and_eq_true, beq_iff_eq] at hb
              simp [hask, hbeq, hb.2]
          · have hrem_pos : 0 < rem j₀ := by omega
            let rem' : Fin n → Nat := fun j => if j = j₀ then rem j₀ - 1 else rem j
            have hsum_step := sum_rem_step rem j₀ hrem_pos
            have hsum' : 3 * n ≤ t + 1 + Finset.univ.sum rem' := by
              have hrem_eq : Finset.univ.sum rem' = Finset.univ.sum (fun j => if j = j₀ then rem j₀ - 1 else rem j) := rfl
              omega
            by_cases hrem1 : rem j₀ = 1
            · rcases exists_inMask (hne j₀).2 with ⟨b₀, hb₀⟩
              let bit := c₀ b₀ coord
              let c_rem' : Fin n → Fin 8 := fun j =>
                if j = j₀ then filtMask (c_rem j₀) (fun b => c₀ b coord == bit) else c_rem j
              refine ⟨r_rem, c_rem', rem', bit :: hist, ?_, ?_, hsum', ?_⟩
              · intro j
                by_cases hj : j = j₀
                · subst hj
                  refine ⟨(hne j).1, ?_⟩
                  simpa [c_rem', bit] using filtMask_nonempty_of (p := fun b => c₀ b coord) hb₀
                · simp [c_rem', hj, hne j]
              · intro j hjpos
                by_cases hj : j = j₀
                · subst hj; simp [rem', hrem1] at hjpos
                · simp only [rem', hj, ↓reduceIte] at hjpos ⊢
                  simpa [c_rem', hj] using hcs j hjpos
              · intro r c hr hc
                have hc0 : ∀ j, ∃ b : Fin 3, inMask (c_rem j) b = true ∧ c j = c₀ b := by
                  intro j
                  rcases hc j with ⟨b, hb, hbeq⟩
                  by_cases hj : j = j₀
                  · subst hj
                    simp only [c_rem', ↓reduceIte, inMask_filtMask, Bool.and_eq_true] at hb
                    exact ⟨b, hb.1, hbeq⟩
                  · simp only [c_rem', hj, ↓reduceIte] at hb
                    exact ⟨b, hb, hbeq⟩
                rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
                  hfold r c hr hc0]
                rcases hc j₀ with ⟨b, hb, hbeq⟩
                simp only [c_rem', ↓reduceIte, inMask_filtMask, Bool.and_eq_true, beq_iff_eq] at hb
                simp [hask, hbeq, hb.2]
            · have hrem2 : 2 ≤ rem j₀ := by omega
              have hcs0 : canSolve (rem j₀ - 2 + 1) (r_rem j₀) (c_rem j₀) = false := by
                have heq : rem j₀ - 2 + 1 = rem j₀ - 1 := by omega
                rw [heq]; exact hcs j₀ hrem_pos
              rcases canSolve_split_col hcs0 (fun b => c₀ b coord) with ⟨bit, hbit⟩
              have hne_new := canSolve_nonempty hbit
              let c_rem' : Fin n → Fin 8 := fun j =>
                if j = j₀ then filtMask (c_rem j₀) (fun b => c₀ b coord == bit) else c_rem j
              refine ⟨r_rem, c_rem', rem', bit :: hist, ?_, ?_, hsum', ?_⟩
              · intro j
                by_cases hj : j = j₀
                · subst hj; exact ⟨(hne j).1, by simpa [c_rem'] using hne_new.2⟩
                · simp [c_rem', hj, hne j]
              · intro j hjpos
                by_cases hj : j = j₀
                · subst hj
                  have heq : rem' j - 1 = rem j - 2 := by simp [rem']; omega
                  rw [heq]; simpa [c_rem'] using hbit
                · simp only [rem', hj, ↓reduceIte] at hjpos ⊢
                  simpa [c_rem', hj] using hcs j hjpos
              · intro r c hr hc
                have hc0 : ∀ j, ∃ b : Fin 3, inMask (c_rem j) b = true ∧ c j = c₀ b := by
                  intro j
                  rcases hc j with ⟨b, hb, hbeq⟩
                  by_cases hj : j = j₀
                  · subst hj
                    simp only [c_rem', ↓reduceIte, inMask_filtMask, Bool.and_eq_true] at hb
                    exact ⟨b, hb.1, hbeq⟩
                  · simp only [c_rem', hj, ↓reduceIte] at hb
                    exact ⟨b, hb, hbeq⟩
                rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
                  hfold r c hr hc0]
                rcases hc j₀ with ⟨b, hb, hbeq⟩
                simp only [c_rem', ↓reduceIte, inMask_filtMask, Bool.and_eq_true, beq_iff_eq] at hb
                simp [hask, hbeq, hb.2]
  rcases hinv q with ⟨r_rem, c_rem, rem, hist, hne, hcs, hsum, hfold⟩
  have hex : ∃ j : Fin n, 0 < rem j := by
    by_contra hall
    push Not at hall
    have hzero : Finset.univ.sum rem = 0 :=
      Finset.sum_eq_zero fun j _ => by have := hall j; omega
    omega
  rcases hex with ⟨j₀, hj₀⟩
  have hcs0 : canSolve 0 (r_rem j₀) (c_rem j₀) = false :=
    canSolve_mono_false (Nat.zero_le _) (hcs j₀ hj₀)
  let m₀ := out hist j₀
  have hdisj : inMask (r_rem j₀) m₀ = true ∨ inMask (c_rem j₀) m₀ = true := by
    by_contra hnot
    have hr_f : inMask (r_rem j₀) m₀ = false := by
      cases h : inMask (r_rem j₀) m₀ <;> simp_all
    have hc_f : inMask (c_rem j₀) m₀ = false := by
      cases h : inMask (c_rem j₀) m₀ <;> simp_all
    have htrue : canSolve 0 (r_rem j₀) (c_rem j₀) = true := by
      simp only [canSolve, Bool.or_eq_true, List.any_eq_true]
      right
      refine ⟨m₀, List.mem_finRange m₀, ?_⟩
      simp [hr_f, hc_f]
    exact absurd hcs0 (by rw [htrue]; decide)
  let aPick : Fin n → Fin 3 := fun j =>
    if j = j₀ then if inMask (r_rem j₀) m₀ then m₀ else (exists_inMask (hne j₀).1).choose
    else (exists_inMask (hne j).1).choose
  let bPick : Fin n → Fin 3 := fun j =>
    if j = j₀ then if inMask (r_rem j₀) m₀ then (exists_inMask (hne j₀).2).choose else m₀
    else (exists_inMask (hne j).2).choose
  let r : Fin n → Fin h → Bool := fun j => r₀ (aPick j)
  let c : Fin n → Fin h → Bool := fun j => c₀ (bPick j)
  have hr_mem : ∀ j, ∃ a : Fin 3, inMask (r_rem j) a = true ∧ r j = r₀ a := by
    intro j
    refine ⟨aPick j, ?_, rfl⟩
    by_cases hj : j = j₀
    · subst hj
      by_cases hm : inMask (r_rem j) m₀ = true
      · simp [aPick, hm]
      · simp [aPick, hm]; exact (exists_inMask (hne j).1).choose_spec
    · simp [aPick, hj]; exact (exists_inMask (hne j).1).choose_spec
  have hc_mem : ∀ j, ∃ b : Fin 3, inMask (c_rem j) b = true ∧ c j = c₀ b := by
    intro j
    refine ⟨bPick j, ?_, rfl⟩
    by_cases hj : j = j₀
    · subst hj
      by_cases hm : inMask (r_rem j) m₀ = true
      · simp [bPick, hm]; exact (exists_inMask (hne j).2).choose_spec
      · simp [bPick, hm]; exact hdisj.resolve_left hm
    · simp [bPick, hj]; exact (exists_inMask (hne j).2).choose_spec
  refine ⟨r, c, j₀, ?_⟩
  have htr := hfold r c hr_mem hc_mem
  dsimp only
  rw [htr]
  rcases hdisj with hm | hm
  · left; simp [r, aPick, hm, m₀]
  · by_cases hm' : inMask (r_rem j₀) m₀ = true
    · left; simp [r, aPick, hm', m₀]
    · right; simp [c, bPick, hm', m₀]

theorem mainProof :
    ∀ (h k start n q : Nat), 5 ≤ h → h+6 ≤ k →
      let tap := fun (x j back : Nat) => x.testBit ((start+j+k-back) % k)
      let pulse := fun (col : Bool) (x j : Nat) =>
        if col then xor (tap x j 1) (xor (tap x j 3) (tap x j 5))
        else xor (tap x j 0) (xor (tap x j 1) (tap x j 2))
      let chi := fun (bits : Nat → Bool) (j : Nat) =>
        xor (bits j) (!(bits (j+1)) && bits (j+2))
      let fiber := fun (z : Fin h → Bool) =>
        {u : Nat | u < 2^(h+2) ∧ ∀ j : Fin h, chi (fun i => u.testBit i) j = z j}
      let tail := fun (col : Bool) (x len u : Nat) =>
        (Finset.range len).filter (fun j =>
          chi (fun i => xor (u.testBit i) (pulse col x i)) (h-len+j))
      let ok := fun (x : Nat) (r c : Fin h → Bool) =>
        Set.InjOn (tail false x 5) (fiber r) ∧ Set.InjOn (tail true x 4) (fiber c)
      let Query := Option (Fin n × Bool × Fin h)
      (∃ (menu : Fin 3 → Fin (2^k)) (ask : List Bool → Query)
          (out : List Bool → Fin n → Fin 3),
        Function.Injective menu ∧ ∀ (r c : Fin n → Fin h → Bool),
          let trace := (List.range q).foldl (fun (hist : List Bool) _ =>
            let bit := ((ask hist).map (fun u =>
              if u.2.1 then c u.1 u.2.2 else r u.1 u.2.2)).getD false
            bit :: hist) []
          ∀ j, ok (menu (out trace j)).val (r j) (c j)) ↔ 3*n ≤ q := by
  intro h k start n q hh hk
  dsimp only
  constructor
  · rintro ⟨menu, ask, out, _, hvalid⟩
    by_contra hq
    have hq_lt : q < 3 * n := by omega
    have hfailR : ∀ m : Fin 3, ∃ r : Fin h → Bool,
        ¬ Set.InjOn (fun u => (Finset.range 5).filter (fun j =>
            chiFn (fun i => xor (u.testBit i)
              (let tap := fun (x j back : Nat) => x.testBit ((start + j + k - back) % k)
               xor (tap (menu m).val i 0)
                 (xor (tap (menu m).val i 1) (tap (menu m).val i 2)))) (h - 5 + j)))
          {u : Nat | u < 2 ^ (h + 2) ∧ ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = r j} :=
      fun m => not_inj_row_general h hh _
    have hfailC : ∀ m : Fin 3, ∃ c : Fin h → Bool,
        ¬ Set.InjOn (fun u => (Finset.range 4).filter (fun j =>
            chiFn (fun i => xor (u.testBit i)
              (let tap := fun (x j back : Nat) => x.testBit ((start + j + k - back) % k)
               xor (tap (menu m).val i 1)
                 (xor (tap (menu m).val i 3) (tap (menu m).val i 5)))) (h - 4 + j)))
          {u : Nat | u < 2 ^ (h + 2) ∧ ∀ j : Fin h, chiFn (fun i => u.testBit i) j.val = c j} :=
      fun m => not_inj_col_general h hh _
    let r₀ : Fin 3 → Fin h → Bool := fun m => (hfailR m).choose
    let c₀ : Fin 3 → Fin h → Bool := fun m => (hfailC m).choose
    rcases lower_bound_adv ask out r₀ c₀ hq_lt with ⟨r, c, j, hbad⟩
    have hok := hvalid r c j
    let trace := (List.range q).foldl (fun (hist : List Bool) _ =>
      let bit := ((ask hist).map (fun u =>
        if u.2.1 then c u.1 u.2.2 else r u.1 u.2.2)).getD false
      bit :: hist) []
    rcases hbad with hr | hc
    · have hnr := (hfailR (out trace j)).choose_spec
      dsimp only [r₀] at hr
      change ¬ Set.InjOn _ _ at hnr
      rw [← hr] at hnr
      exact hnr hok.1
    · have hnc := (hfailC (out trace j)).choose_spec
      dsimp only [c₀] at hc
      change ¬ Set.InjOn _ _ at hnc
      rw [← hc] at hnc
      exact hnc hok.2
  · intro hq
    refine ⟨mkKey h k start, askProto h n hh, outProto n, mkKey_inj hh hk, fun r c j => ?_⟩
    let eval : List Bool → Bool := fun hist =>
      ((askProto h n hh hist).map (fun u =>
        if u.2.1 then c u.1 u.2.2 else r u.1 u.2.2)).getD false
    let step : List Bool → Nat → List Bool := fun hist _ => eval hist :: hist
    have hstep_len : ∀ xs x, (step xs x).length = xs.length + 1 := fun _ _ => rfl
    have hrev : ∀ {t : Nat}, t < q →
        revGet ((List.range q).foldl step []) t = eval ((List.range t).foldl step []) :=
      fun hk => foldl_revGet_lt eval hk
    have ht0 : 3 * j.val < q := by omega
    have ht1 : 3 * j.val + 1 < q := by omega
    have ht2 : 3 * j.val + 2 < q := by omega
    have hl0 : ((List.range (3 * j.val)).foldl step []).length = 3 * j.val :=
      foldl_len step hstep_len _
    have hl1 : ((List.range (3 * j.val + 1)).foldl step []).length = 3 * j.val + 1 :=
      foldl_len step hstep_len _
    have hl2 : ((List.range (3 * j.val + 2)).foldl step []).length = 3 * j.val + 2 :=
      foldl_len step hstep_len _
    have hb0 : revGet ((List.range q).foldl step []) (3 * j.val) = c j ⟨h - 1, by omega⟩ := by
      rw [hrev ht0]; dsimp only [eval]; rw [askProto_0 hh hl0]; rfl
    have hhist1_b0 : revGet ((List.range (3 * j.val + 1)).foldl step []) (3 * j.val) =
        c j ⟨h - 1, by omega⟩ := by
      rw [foldl_revGet_lt eval (t := 3 * j.val + 1) (k := 3 * j.val) (by omega)]
      dsimp only [eval]; rw [askProto_0 hh hl0]; rfl
    have hb1 : revGet ((List.range q).foldl step []) (3 * j.val + 1) =
        if c j ⟨h - 1, by omega⟩ then r j ⟨h - 1, by omega⟩ else c j ⟨h - 2, by omega⟩ := by
      rw [hrev ht1]; dsimp only [eval]; rw [askProto_1 hh hl1, hhist1_b0]
      cases c j ⟨h - 1, by omega⟩ <;> rfl
    have hhist2_b0 : revGet ((List.range (3 * j.val + 2)).foldl step []) (3 * j.val) =
        c j ⟨h - 1, by omega⟩ := by
      rw [foldl_revGet_lt eval (t := 3 * j.val + 2) (k := 3 * j.val) (by omega)]
      dsimp only [eval]; rw [askProto_0 hh hl0]; rfl
    have hhist2_b1 : revGet ((List.range (3 * j.val + 2)).foldl step []) (3 * j.val + 1) =
        if c j ⟨h - 1, by omega⟩ then r j ⟨h - 1, by omega⟩ else c j ⟨h - 2, by omega⟩ := by
      rw [foldl_revGet_lt eval (t := 3 * j.val + 2) (k := 3 * j.val + 1) (by omega)]
      dsimp only [eval]; rw [askProto_1 hh hl1, hhist1_b0]
      cases c j ⟨h - 1, by omega⟩ <;> rfl
    have hb2 : c j ⟨h - 1, by omega⟩ = false →
        revGet ((List.range q).foldl step []) (3 * j.val + 2) =
          if !(c j ⟨h - 2, by omega⟩) then r j ⟨h - 1, by omega⟩ else r j ⟨h - 3, by omega⟩ := by
      intro hcf
      rw [hrev ht2]; dsimp only [eval]; rw [askProto_2 hh hl2, hhist2_b0, hhist2_b1, hcf]
      cases c j ⟨h - 2, by omega⟩ <;> rfl
    change Set.InjOn _ _ ∧ Set.InjOn _ _
    cases hc1 : c j ⟨h - 1, by omega⟩ with
    | true =>
      have hb0' : revGet ((List.range q).foldl step []) (3 * j.val) = true := hb0.trans hc1
      have hb1' : revGet ((List.range q).foldl step []) (3 * j.val + 1) = r j ⟨h - 1, by omega⟩ := by
        simpa [hc1] using hb1
      cases hr1 : r j ⟨h - 1, by omega⟩ with
      | false =>
        have hout : outProto n ((List.range q).foldl step []) j = 0 := by
          simp [outProto, hb0', hb1', hr1]
        rw [hout]
        exact ⟨mkKey_rowInj hh hk 0 (r j) (by simp [hr1]),
               mkKey_colInj hh hk 0 (c j) (by simp [hc1])⟩
      | true =>
        have hout : outProto n ((List.range q).foldl step []) j = 2 := by
          simp [outProto, hb0', hb1', hr1]
        rw [hout]
        exact ⟨mkKey_rowInj hh hk 2 (r j) (by simp [hr1]),
               mkKey_colInj hh hk 2 (c j) (by simp [hc1])⟩
    | false =>
      have hb0' : revGet ((List.range q).foldl step []) (3 * j.val) = false := hb0.trans hc1
      have hb1' : revGet ((List.range q).foldl step []) (3 * j.val + 1) = c j ⟨h - 2, by omega⟩ := by
        simpa [hc1] using hb1
      have hb2' := hb2 hc1
      cases hc2 : c j ⟨h - 2, by omega⟩ with
      | false =>
        have hb2'' : revGet ((List.range q).foldl step []) (3 * j.val + 2) = r j ⟨h - 1, by omega⟩ := by
          simpa [hc2] using hb2'
        cases hr1 : r j ⟨h - 1, by omega⟩ with
        | false =>
          have hout : outProto n ((List.range q).foldl step []) j = 0 := by
            simp [outProto, hb0', hb1', hc2, hb2'', hr1]
          rw [hout]
          exact ⟨mkKey_rowInj hh hk 0 (r j) (by simp [hr1]),
                 mkKey_colInj hh hk 0 (c j) (by simp [hc2, hc1])⟩
        | true =>
          have hout : outProto n ((List.range q).foldl step []) j = 1 := by
            simp [outProto, hb0', hb1', hc2, hb2'', hr1]
          rw [hout]
          exact ⟨mkKey_rowInj hh hk 1 (r j) (by simp [hr1]),
                 mkKey_colInj hh hk 1 (c j) (by simp [hc1])⟩
      | true =>
        have hb2'' : revGet ((List.range q).foldl step []) (3 * j.val + 2) = r j ⟨h - 3, by omega⟩ := by
          simpa [hc2] using hb2'
        cases hr3 : r j ⟨h - 3, by omega⟩ with
        | false =>
          have hout : outProto n ((List.range q).foldl step []) j = 1 := by
            simp [outProto, hb0', hb1', hc2, hb2'', hr3]
          rw [hout]
          exact ⟨mkKey_rowInj hh hk 1 (r j) (by simp [hr3]),
                 mkKey_colInj hh hk 1 (c j) (by simp [hc1])⟩
        | true =>
          have hout : outProto n ((List.range q).foldl step []) j = 2 := by
            simp [outProto, hb0', hb1', hc2, hb2'', hr3]
          rw [hout]
          exact ⟨mkKey_rowInj hh hk 2 (r j) (by simp [hr3]),
                 mkKey_colInj hh hk 2 (c j) (by simp [hc2, hc1])⟩

end PEqualNP.Outside.L_meta_39005

theorem PEqualNP.Outside.L_meta_39005 :
    ∀ (h k start n q : Nat), 5 ≤ h → h+6 ≤ k →
      let tap := fun (x j back : Nat) => x.testBit ((start+j+k-back) % k)
      let pulse := fun (col : Bool) (x j : Nat) =>
        if col then xor (tap x j 1) (xor (tap x j 3) (tap x j 5))
        else xor (tap x j 0) (xor (tap x j 1) (tap x j 2))
      let chi := fun (bits : Nat → Bool) (j : Nat) =>
        xor (bits j) (!(bits (j+1)) && bits (j+2))
      let fiber := fun (z : Fin h → Bool) =>
        {u : Nat | u < 2^(h+2) ∧ ∀ j : Fin h, chi (fun i => u.testBit i) j = z j}
      let tail := fun (col : Bool) (x len u : Nat) =>
        (Finset.range len).filter (fun j =>
          chi (fun i => xor (u.testBit i) (pulse col x i)) (h-len+j))
      let ok := fun (x : Nat) (r c : Fin h → Bool) =>
        Set.InjOn (tail false x 5) (fiber r) ∧ Set.InjOn (tail true x 4) (fiber c)
      let Query := Option (Fin n × Bool × Fin h)
      (∃ (menu : Fin 3 → Fin (2^k)) (ask : List Bool → Query)
          (out : List Bool → Fin n → Fin 3),
        Function.Injective menu ∧ ∀ (r c : Fin n → Fin h → Bool),
          let trace := (List.range q).foldl (fun (hist : List Bool) _ =>
            let bit := ((ask hist).map (fun u =>
              if u.2.1 then c u.1 u.2.2 else r u.1 u.2.2)).getD false
            bit :: hist) []
          ∀ j, ok (menu (out trace j)).val (r j) (c j)) ↔ 3*n ≤ q :=
  PEqualNP.Outside.L_meta_39005.mainProof

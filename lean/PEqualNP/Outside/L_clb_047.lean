import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_047

private def atPos {n : ℕ} (hn : 0 < n) (word : Fin n → Bool) (k : ℕ) : Bool :=
  word ⟨k % n, Nat.mod_lt _ hn⟩

private lemma atPos_add_n {n : ℕ} (hn : 0 < n) (word : Fin n → Bool) (k : ℕ) :
    atPos hn word (n + k) = atPos hn word k := by
  simp only [atPos, Nat.add_mod_left]

private lemma atPos_of_lt {n : ℕ} (hn : 0 < n) (word : Fin n → Bool) (idx : Fin n) :
    atPos hn word idx.val = word idx := by
  dsimp only [atPos]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt idx.isLt)

private lemma mul_add_div_right (a b r : ℕ) (hb : 0 < b) (hr : r < b) :
    (a * b + r) / b = a := by
  rw [Nat.mul_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt hr, add_zero]

private lemma mul_add_mod_right (a b r : ℕ) (hr : r < b) :
    (a * b + r) % b = r := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

private def vecXor {d : ℕ} (x y : Fin d → Bool) : Fin d → Bool :=
  fun j => xor (x j) (y j)

private lemma vecXor_invol {d : ℕ} (x y : Fin d → Bool) : vecXor (vecXor x y) y = x := by
  funext j
  dsimp only [vecXor]
  cases x j <;> cases y j <;> rfl

private lemma vecXor_comm {d : ℕ} (x y : Fin d → Bool) : vecXor x y = vecXor y x := by
  funext j
  dsimp only [vecXor]
  cases x j <;> cases y j <;> rfl

private lemma vecXor_eq_iff {d : ℕ} (x y z : Fin d → Bool) :
    vecXor x y = z ↔ y = vecXor x z := by
  constructor
  · intro h; subst h; funext j; dsimp only [vecXor]; cases x j <;> cases y j <;> rfl
  · intro h; subst h; funext j; dsimp only [vecXor]; cases x j <;> cases z j <;> rfl

private def bitsOf (d : ℕ) (m : ℕ) : Fin d → Bool :=
  fun j => m.testBit j.val

private lemma bitsOf_inj (d : ℕ) : Function.Injective (fun m : Fin (2 ^ d) => bitsOf d m.val) := by
  intro m1 m2 heq
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < d
  · exact congrFun heq ⟨k, hk⟩
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le m1.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le m2.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))]

private lemma bitsOf_bijective (d : ℕ) : Function.Bijective (fun m : Fin (2 ^ d) => bitsOf d m.val) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨bitsOf_inj d, ?_⟩
  simp [Fintype.card_bool, Fintype.card_fin]

private noncomputable def findM0 (d : ℕ) (δ : Fin d → Bool) : Fin (2 ^ d) :=
  Classical.choose ((bitsOf_bijective d).2 δ)

private lemma bitsOf_findM0 (d : ℕ) (δ : Fin d → Bool) :
    bitsOf d (findM0 d δ).val = δ :=
  Classical.choose_spec ((bitsOf_bijective d).2 δ)

private def listXor : List Bool → Bool
  | [] => false
  | b :: bs => xor b (listXor bs)

private lemma listXor_append (l1 l2 : List Bool) :
    listXor (l1 ++ l2) = xor (listXor l1) (listXor l2) := by
  induction l1 with
  | nil => simp [listXor]
  | cons a t ih =>
    simp only [List.cons_append, listXor, ih]
    cases a <;> cases listXor t <;> cases listXor l2 <;> rfl

private def evenParity {k : ℕ} (pat : Fin k → Bool) : Bool :=
  !(listXor (List.ofFn pat))

private lemma listXor_ofFn_succ_front {w : ℕ} (f : Fin (w + 1) → Bool) :
    listXor (List.ofFn f) = xor (f 0) (listXor (List.ofFn (fun j : Fin w => f j.succ))) := by
  rw [List.ofFn_succ, listXor]

private lemma listXor_ofFn_succ_back {w : ℕ} (f : Fin (w + 1) → Bool) :
    listXor (List.ofFn f) =
      xor (listXor (List.ofFn (fun j : Fin w => f j.castSucc))) (f (Fin.last w)) := by
  rw [List.ofFn_succ', List.concat_eq_append, listXor_append]
  simp only [listXor]
  cases listXor (List.ofFn (fun j : Fin w => f j.castSucc)) <;> cases f (Fin.last w) <;> rfl

private lemma evenParity_shift {w : ℕ} (g : ℕ → Bool) (i : ℕ)
    (h1 : evenParity (fun j : Fin (w + 1) => g (i + j.val)) = true)
    (h2 : evenParity (fun j : Fin (w + 1) => g (i + 1 + j.val)) = true) :
    g (i + w + 1) = g i := by
  have hx1 : listXor (List.ofFn (fun j : Fin (w + 1) => g (i + j.val))) = false := by
    simpa [evenParity] using h1
  have hx2 : listXor (List.ofFn (fun j : Fin (w + 1) => g (i + 1 + j.val))) = false := by
    simpa [evenParity] using h2
  rw [listXor_ofFn_succ_front] at hx1
  rw [listXor_ofFn_succ_back] at hx2
  have hmid : (fun j : Fin w => g (i + j.succ.val)) = (fun j : Fin w => g (i + 1 + j.castSucc.val)) := by
    funext j; congr 1; simp; omega
  have h0 : g (i + (0 : Fin (w + 1)).val) = g i := by simp
  have hlast : g (i + 1 + (Fin.last w).val) = g (i + w + 1) := by congr 1; simp; omega
  rw [h0, hmid] at hx1
  rw [hlast] at hx2
  set mid := listXor (List.ofFn (fun j : Fin w => g (i + 1 + j.castSucc.val)))
  cases hgi : g i <;> cases hgw : g (i + w + 1) <;> cases hm : mid <;> simp_all

private lemma evenParity_last_bit {w : ℕ} (g : ℕ → Bool) (i : ℕ)
    (h : evenParity (fun j : Fin (w + 1) => g (i + j.val)) = true) :
    g (i + w) = listXor (List.ofFn (fun j : Fin w => g (i + j.val))) := by
  have hx : listXor (List.ofFn (fun j : Fin (w + 1) => g (i + j.val))) = false := by
    simpa [evenParity] using h
  rw [listXor_ofFn_succ_back] at hx
  have hlast : g (i + (Fin.last w).val) = g (i + w) := by simp
  rw [hlast] at hx
  set mid := listXor (List.ofFn (fun j : Fin w => g (i + j.castSucc.val)))
  change g (i + w) = mid
  cases hgw : g (i + w) <;> cases hm : mid <;> simp_all

private def blockBit {d : ℕ} (u : Fin d → Bool) (t : Bool) (r : ℕ) : Bool :=
  if h : r < d then u ⟨r, h⟩ else t

private def transferRow (d : ℕ) (flipTag : Bool)
    (M : (Fin d → Bool) → (Fin d → Bool) → Bool)
    (row : Fin (3 * (d + 1) * 2 ^ d)) (pat : Fin (d + 2) → Bool) : Bool :=
  let w := d + 1
  let blk := row.val / w
  let r := row.val % w
  let m := blk / 3
  let phase := blk % 3
  let δ := bitsOf d m
  let pinOK := if row.val = 0 then decide (pat ⟨d, by omega⟩ = flipTag) else true
  let stepOK :=
    if phase = 1 then
      if r < d then
        decide (pat ⟨w, by omega⟩ = pat ⟨0, by omega⟩)
      else
        let t1 := pat ⟨0, by omega⟩
        let t2 := pat ⟨w, by omega⟩
        let v : Fin d → Bool := fun j => pat ⟨j.val + 1, by omega⟩
        if t1 = flipTag then
          if t2 = flipTag then true else M (vecXor v δ) v
        else
          decide (t2 = !flipTag)
    else
      if hr : r < d then
        let t := pat ⟨d - r, by omega⟩
        let x0 := pat ⟨0, by omega⟩
        let x1 := pat ⟨w, by omega⟩
        decide (x1 = if t = flipTag then xor x0 (δ ⟨r, hr⟩) else x0)
      else
        decide (pat ⟨w, by omega⟩ = pat ⟨0, by omega⟩)
  pinOK && stepOK

private lemma transferRow_projection (d : ℕ) (flipTag : Bool) :
    ∀ (row : Fin (3 * (d + 1) * 2 ^ d)) (pat : Fin (d + 2) → Bool),
      (∃ c : Bool, ∀ M, transferRow d flipTag M row pat = c) ∨
      ∃ u v : Fin d → Bool, ∀ M, transferRow d flipTag M row pat = M u v := by
  intro row pat
  dsimp only [transferRow]
  by_cases hp : row.val / (d + 1) % 3 = 1
  · by_cases hrow0 : row.val = 0
    · rw [hrow0] at hp; simp at hp
    · by_cases hrd : row.val % (d + 1) < d
      · left
        refine ⟨decide (pat ⟨d + 1, by omega⟩ = pat ⟨0, by omega⟩), fun M => ?_⟩
        simp only [hp, hrow0, hrd, ite_true, ite_false, Bool.true_and]
      · by_cases ht1 : pat ⟨0, by omega⟩ = flipTag
        · by_cases ht2 : pat ⟨d + 1, by omega⟩ = flipTag
          · left
            refine ⟨true, fun M => ?_⟩
            simp only [hp, hrow0, hrd, ht1, ht2, ite_true, ite_false, Bool.true_and]
          · right
            let v : Fin d → Bool := fun j => pat ⟨j.val + 1, by omega⟩
            refine ⟨vecXor v (bitsOf d (row.val / (d + 1) / 3)), v, fun M => ?_⟩
            simp only [hp, hrow0, hrd, ht1, ht2, ite_true, ite_false, Bool.true_and, v]
        · left
          refine ⟨decide (pat ⟨d + 1, by omega⟩ = !flipTag), fun M => ?_⟩
          simp only [hp, hrow0, hrd, ht1, ite_true, ite_false, Bool.true_and]
  · left
    refine ⟨(if row.val = 0 then decide (pat ⟨d, by omega⟩ = flipTag) else true) &&
      (if hr : row.val % (d + 1) < d then
        decide (pat ⟨d + 1, by omega⟩ =
          if pat ⟨d - row.val % (d + 1), by omega⟩ = flipTag
          then xor (pat ⟨0, by omega⟩) (bitsOf d (row.val / (d + 1) / 3) ⟨row.val % (d + 1), hr⟩)
          else pat ⟨0, by omega⟩)
      else decide (pat ⟨d + 1, by omega⟩ = pat ⟨0, by omega⟩)), fun M => ?_⟩
    simp only [hp, ite_false]

private def mkHalf (d : ℕ) (flipTag : Bool) (u v : Fin d → Bool) (m0 : ℕ)
    (i : Fin (3 * (d + 1) * 2 ^ d)) : Bool :=
  let w := d + 1
  let blk := i.val / w
  let r := i.val % w
  let m := blk / 3
  let phase := blk % 3
  let δ := bitsOf d m
  if m < m0 then
    if phase = 0 then blockBit u flipTag r else blockBit (vecXor u δ) flipTag r
  else if m = m0 then
    if phase = 0 then blockBit u flipTag r
    else if phase = 1 then blockBit v flipTag r
    else blockBit v (!flipTag) r
  else
    blockBit v (!flipTag) r

private def readData {n : ℕ} (hn : 0 < n) (d : ℕ) (word : Fin n → Bool) (start : ℕ) :
    Fin d → Bool :=
  fun j => atPos hn word (start + j.val)

private def readTag {n : ℕ} (hn : 0 < n) (d : ℕ) (word : Fin n → Bool) (start : ℕ) : Bool :=
  atPos hn word (start + d)

private lemma read_xor_block {n : ℕ} (hn : 0 < n) (d : ℕ) (flipTag : Bool)
    (word : Fin n → Bool) (base : ℕ) (δ : Fin d → Bool)
    (hstep : ∀ r : ℕ, r < d + 1 →
      (if hr' : r < d then
        decide (atPos hn word (base + r + (d + 1)) =
          if atPos hn word (base + r + (d - r)) = flipTag
          then xor (atPos hn word (base + r)) (δ ⟨r, hr'⟩)
          else atPos hn word (base + r))
      else
        decide (atPos hn word (base + r + (d + 1)) = atPos hn word (base + r))) = true) :
    readTag hn d word (base + (d + 1)) = readTag hn d word base ∧
    readData hn d word (base + (d + 1)) =
      if readTag hn d word base = flipTag then vecXor (readData hn d word base) δ
      else readData hn d word base := by
  constructor
  · have hd := hstep d (Nat.lt_succ_self d)
    simp only [lt_irrefl, dite_false, decide_eq_true_eq] at hd
    dsimp only [readTag]
    rw [show base + (d + 1) + d = base + d + (d + 1) by omega]
    exact hd
  · funext j
    have hj := hstep j.val (Nat.lt_succ_of_lt j.isLt)
    simp only [j.isLt, dite_true, decide_eq_true_eq] at hj
    dsimp only [readData, readTag, vecXor]
    rw [show base + (d + 1) + j.val = base + j.val + (d + 1) by omega, hj,
      show base + j.val + (d - j.val) = base + d by omega]
    by_cases hc : atPos hn word (base + d) = flipTag
    · simp [hc, vecXor, readData]
    · simp [hc, readData]

private lemma read_switch_block {n : ℕ} (hn : 0 < n) (d : ℕ) (flipTag : Bool)
    (M : (Fin d → Bool) → (Fin d → Bool) → Bool)
    (word : Fin n → Bool) (base : ℕ) (δ : Fin d → Bool)
    (hcopy : ∀ r : ℕ, r < d →
      atPos hn word (base + r + (d + 1)) = atPos hn word (base + r))
    (hlast :
      (let t1 := atPos hn word (base + d)
       let t2 := atPos hn word (base + d + (d + 1))
       let v : Fin d → Bool := fun j => atPos hn word (base + d + (j.val + 1))
       if t1 = flipTag then
         if t2 = flipTag then true else M (vecXor v δ) v
       else
         decide (t2 = !flipTag)) = true) :
    readData hn d word (base + (d + 1)) = readData hn d word base ∧
    (readTag hn d word base = !flipTag → readTag hn d word (base + (d + 1)) = !flipTag) ∧
    (readTag hn d word base = flipTag → readTag hn d word (base + (d + 1)) = !flipTag →
      M (vecXor (readData hn d word base) δ) (readData hn d word base) = true) := by
  have hdata : readData hn d word (base + (d + 1)) = readData hn d word base := by
    funext j
    dsimp only [readData]
    rw [show base + (d + 1) + j.val = base + j.val + (d + 1) by omega]
    exact hcopy j.val j.isLt
  refine ⟨hdata, ?_, ?_⟩
  · intro ht1
    dsimp only [readTag] at ht1 ⊢
    have hne : atPos hn word (base + d) ≠ flipTag := by
      rw [ht1]; cases flipTag <;> decide
    simp only [hne, ite_false, decide_eq_true_eq] at hlast
    rw [show base + (d + 1) + d = base + d + (d + 1) by omega]
    exact hlast
  · intro ht1 ht2
    dsimp only [readTag] at ht1 ht2
    have hne : atPos hn word (base + d + (d + 1)) ≠ flipTag := by
      rw [show base + d + (d + 1) = base + (d + 1) + d by omega, ht2]
      cases flipTag <;> decide
    simp only [ht1, ite_true, hne, ite_false] at hlast
    have hv : (fun j : Fin d => atPos hn word (base + d + (j.val + 1))) =
        readData hn d word base := by
      funext j
      rw [← hdata]
      dsimp only [readData]
      rw [show base + d + (j.val + 1) = base + (d + 1) + j.val by omega]
    rwa [hv] at hlast

private lemma transfer_step_summary {n : ℕ} (hn : 0 < n) (d : ℕ) (flipTag : Bool)
    (M : (Fin d → Bool) → (Fin d → Bool) → Bool)
    (word : Fin n → Bool) (base : ℕ)
    (hall : ∀ i : Fin (3 * (d + 1) * 2 ^ d),
      transferRow d flipTag M i (fun j => atPos hn word (base + i.val + j.val)) = true)
    (m : ℕ) (hm : m < 2 ^ d) :
    let w := d + 1
    let b0 := base + 3 * m * w
    let b1 := b0 + w
    let b2 := b1 + w
    let b3 := b2 + w
    let δ := bitsOf d m
    (readTag hn d word b0 = !flipTag →
      readTag hn d word b1 = !flipTag ∧ readData hn d word b1 = readData hn d word b0 ∧
      readTag hn d word b2 = !flipTag ∧ readData hn d word b2 = readData hn d word b0 ∧
      readTag hn d word b3 = !flipTag ∧ readData hn d word b3 = readData hn d word b0) ∧
    (readTag hn d word b0 = flipTag →
      readTag hn d word b1 = flipTag ∧ readData hn d word b1 = vecXor (readData hn d word b0) δ ∧
      readData hn d word b2 = vecXor (readData hn d word b0) δ ∧
      ((readTag hn d word b2 = flipTag ∧
          readTag hn d word b3 = flipTag ∧ readData hn d word b3 = readData hn d word b0) ∨
       (readTag hn d word b2 = !flipTag ∧
          readTag hn d word b3 = !flipTag ∧ readData hn d word b3 = vecXor (readData hn d word b0) δ ∧
          M (readData hn d word b0) (vecXor (readData hn d word b0) δ) = true))) := by
  intro w b0 b1 b2 b3 δ
  have hrow : ∀ (phase r : ℕ) (hp : phase < 3) (hr : r < d + 1),
      let idx := (3 * m + phase) * (d + 1) + r
      have hidx : idx < 3 * (d + 1) * 2 ^ d := by
        have h1 : 3 * m + phase + 1 ≤ 3 * 2 ^ d := by omega
        have h2 : (3 * m + phase) * (d + 1) + (d + 1) ≤ (3 * 2 ^ d) * (d + 1) := by
          calc (3 * m + phase) * (d + 1) + (d + 1) = (3 * m + phase + 1) * (d + 1) := by ring
            _ ≤ (3 * 2 ^ d) * (d + 1) := Nat.mul_le_mul_right (d + 1) h1
        have h3 : (3 * 2 ^ d) * (d + 1) = 3 * (d + 1) * 2 ^ d := by ring
        omega
      transferRow d flipTag M ⟨idx, hidx⟩
        (fun j => atPos hn word (base + idx + j.val)) = true :=
    fun phase r _ _ => hall _
  have hblk_div : ∀ (phase r : ℕ), r < d + 1 → ((3 * m + phase) * (d + 1) + r) / (d + 1) = 3 * m + phase :=
    fun phase r hr => mul_add_div_right (3 * m + phase) (d + 1) r (by omega) hr
  have hblk_mod : ∀ (phase r : ℕ), r < d + 1 → ((3 * m + phase) * (d + 1) + r) % (d + 1) = r :=
    fun phase r hr => mul_add_mod_right (3 * m + phase) (d + 1) r hr
  have hph_div : ∀ phase : ℕ, phase < 3 → (3 * m + phase) / 3 = m :=
    fun phase hp => by rw [Nat.mul_add_div (by omega : 0 < 3), Nat.div_eq_of_lt hp, add_zero]
  have hph_mod : ∀ phase : ℕ, phase < 3 → (3 * m + phase) % 3 = phase :=
    fun phase hp => by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hp]
  have h0 : readTag hn d word b1 = readTag hn d word b0 ∧
      readData hn d word b1 =
        if readTag hn d word b0 = flipTag then vecXor (readData hn d word b0) δ
        else readData hn d word b0 := by
    apply read_xor_block hn d flipTag word b0 δ
    intro r hr
    have h := hrow 0 r (by omega) hr
    dsimp only [transferRow] at h
    rw [hblk_div 0 r hr, hblk_mod 0 r hr, hph_div 0 (by omega), hph_mod 0 (by omega)] at h
    simp only [show (0 : ℕ) ≠ 1 by omega, ite_false, Bool.and_eq_true] at h
    have hs := h.2
    have hadd : base + ((3 * m + 0) * (d + 1) + r) = b0 + r := by dsimp only [b0, w]; ring
    rw [hadd] at hs
    simp only [add_zero] at hs
    exact hs
  have h1s : readData hn d word b2 = readData hn d word b1 ∧
      (readTag hn d word b1 = !flipTag → readTag hn d word b2 = !flipTag) ∧
      (readTag hn d word b1 = flipTag → readTag hn d word b2 = !flipTag →
        M (vecXor (readData hn d word b1) δ) (readData hn d word b1) = true) := by
    apply read_switch_block hn d flipTag M word b1 δ
    · intro r hr
      have h := hrow 1 r (by omega) (by omega)
      dsimp only [transferRow] at h
      rw [hblk_div 1 r (by omega), hblk_mod 1 r (by omega), hph_div 1 (by omega), hph_mod 1 (by omega)] at h
      simp only [ite_true, hr, Bool.and_eq_true, decide_eq_true_eq] at h
      have hs := h.2
      have hadd : base + ((3 * m + 1) * (d + 1) + r) = b1 + r := by dsimp only [b1, b0, w]; ring
      simp only [hadd, add_zero] at hs
      exact hs
    · have h := hrow 1 d (by omega) (by omega)
      dsimp only [transferRow] at h
      rw [hblk_div 1 d (by omega), hblk_mod 1 d (by omega), hph_div 1 (by omega), hph_mod 1 (by omega)] at h
      simp only [ite_true, lt_irrefl, ite_false, Bool.and_eq_true] at h
      have hs := h.2
      have hadd : base + ((3 * m + 1) * (d + 1) + d) = b1 + d := by dsimp only [b1, b0, w]; ring
      simp only [hadd, add_zero] at hs
      exact hs
  have h2 : readTag hn d word b3 = readTag hn d word b2 ∧
      readData hn d word b3 =
        if readTag hn d word b2 = flipTag then vecXor (readData hn d word b2) δ
        else readData hn d word b2 := by
    apply read_xor_block hn d flipTag word b2 δ
    intro r hr
    have h := hrow 2 r (by omega) hr
    dsimp only [transferRow] at h
    rw [hblk_div 2 r hr, hblk_mod 2 r hr, hph_div 2 (by omega), hph_mod 2 (by omega)] at h
    simp only [show (2 : ℕ) ≠ 1 by omega, ite_false, Bool.and_eq_true] at h
    have hs := h.2
    have hadd : base + ((3 * m + 2) * (d + 1) + r) = b2 + r := by dsimp only [b2, b1, b0, w]; ring
    simp only [hadd, add_zero] at hs
    exact hs
  constructor
  · intro ht0
    have hne : readTag hn d word b0 ≠ flipTag := by rw [ht0]; cases flipTag <;> decide
    have ht1 : readTag hn d word b1 = !flipTag := by rw [h0.1, ht0]
    have hd1 : readData hn d word b1 = readData hn d word b0 := by rw [h0.2, if_neg hne]
    have ht2 : readTag hn d word b2 = !flipTag := h1s.2.1 ht1
    have hd2 : readData hn d word b2 = readData hn d word b0 := by rw [h1s.1, hd1]
    have hne2 : readTag hn d word b2 ≠ flipTag := by rw [ht2]; cases flipTag <;> decide
    have ht3 : readTag hn d word b3 = !flipTag := by rw [h2.1, ht2]
    have hd3 : readData hn d word b3 = readData hn d word b0 := by rw [h2.2, if_neg hne2, hd2]
    exact ⟨ht1, hd1, ht2, hd2, ht3, hd3⟩
  · intro ht0
    have ht1 : readTag hn d word b1 = flipTag := by rw [h0.1, ht0]
    have hd1 : readData hn d word b1 = vecXor (readData hn d word b0) δ := by rw [h0.2, if_pos ht0]
    have hd2 : readData hn d word b2 = vecXor (readData hn d word b0) δ := by rw [h1s.1, hd1]
    refine ⟨ht1, hd1, hd2, ?_⟩
    by_cases ht2 : readTag hn d word b2 = flipTag
    · left
      have ht3 : readTag hn d word b3 = flipTag := by rw [h2.1, ht2]
      have hd3 : readData hn d word b3 = readData hn d word b0 := by
        rw [h2.2, if_pos ht2, hd2, vecXor_invol]
      exact ⟨ht2, ht3, hd3⟩
    · right
      have ht2' : readTag hn d word b2 = !flipTag := by
        cases h : readTag hn d word b2 <;> cases hf : flipTag <;> simp_all
      have ht3 : readTag hn d word b3 = !flipTag := by rw [h2.1, ht2']
      have hd3 : readData hn d word b3 = vecXor (readData hn d word b0) δ := by
        rw [h2.2, if_neg ht2, hd2]
      have hM := h1s.2.2 ht1 ht2'
      rw [hd1, vecXor_invol] at hM
      exact ⟨ht2', ht3, hd3, hM⟩

private lemma transfer_unique_decode {n : ℕ} (hn : 0 < n) (d : ℕ) (flipTag : Bool)
    (M : (Fin d → Bool) → (Fin d → Bool) → Bool)
    (word : Fin n → Bool) (base : ℕ)
    (hall : ∀ i : Fin (3 * (d + 1) * 2 ^ d),
      transferRow d flipTag M i (fun j => atPos hn word (base + i.val + j.val)) = true)
    (hend : readTag hn d word (base + 3 * (d + 1) * 2 ^ d) = !flipTag) :
    let u := readData hn d word base
    let v := readData hn d word (base + 3 * (d + 1) * 2 ^ d)
    readTag hn d word base = flipTag ∧
    M u v = true ∧
    ∃ m0 : Fin (2 ^ d), bitsOf d m0.val = vecXor u v ∧
      ∀ i : Fin (3 * (d + 1) * 2 ^ d),
        atPos hn word (base + i.val) = mkHalf d flipTag u v m0.val i := by
  intro u v
  have hstart : readTag hn d word base = flipTag := by
    have h0 := hall ⟨0, by positivity⟩
    dsimp only [transferRow] at h0
    simp only [ite_true, Bool.and_eq_true, decide_eq_true_eq] at h0
    simpa [readTag] using h0.1
  have hstep := transfer_step_summary hn d flipTag M word base hall
  have hmono : ∀ m ≤ 2 ^ d,
      (readTag hn d word (base + 3 * m * (d + 1)) = flipTag →
        readData hn d word (base + 3 * m * (d + 1)) = u) ∧
      (∀ k ≤ m, readTag hn d word (base + 3 * k * (d + 1)) = !flipTag →
        readTag hn d word (base + 3 * m * (d + 1)) = !flipTag ∧
        readData hn d word (base + 3 * m * (d + 1)) = readData hn d word (base + 3 * k * (d + 1))) := by
    intro m hm
    induction m with
    | zero =>
      refine ⟨fun _ => by simp [u], fun k hk hk1 => ?_⟩
      have hk0 : k = 0 := by omega
      subst hk0; exact ⟨hk1, rfl⟩
    | succ m ih =>
      have ihm := ih (by omega)
      have hs := hstep m (by omega)
      have hb3 : base + 3 * m * (d + 1) + (d + 1) + (d + 1) + (d + 1) = base + 3 * (m + 1) * (d + 1) := by ring
      constructor
      · intro htm1
        by_cases htm : readTag hn d word (base + 3 * m * (d + 1)) = flipTag
        · rcases (hs.2 htm).2.2.2 with ⟨_, _, hd3⟩ | ⟨_, ht3, _, _⟩
          · rw [hb3] at hd3; rw [hd3, ihm.1 htm]
          · rw [hb3] at ht3; rw [ht3] at htm1; cases flipTag <;> simp at htm1
        · have htm' : readTag hn d word (base + 3 * m * (d + 1)) = !flipTag := by
            cases h : readTag hn d word (base + 3 * m * (d + 1)) <;> cases hf : flipTag <;> simp_all
          have h3 := (hs.1 htm').2.2.2.2.1
          rw [hb3] at h3; rw [h3] at htm1; cases flipTag <;> simp at htm1
      · intro k hk hk1
        by_cases hkm : k = m + 1
        · subst hkm; exact ⟨hk1, rfl⟩
        · have hkm' : k ≤ m := by omega
          have ⟨ht_m, hd_m⟩ := ihm.2 k hkm' hk1
          have h3 := hs.1 ht_m
          rw [hb3] at h3
          exact ⟨h3.2.2.2.2.1, h3.2.2.2.2.2.trans hd_m⟩
  have hex_flip : ∃ m : Fin (2 ^ d),
      readTag hn d word (base + 3 * m.val * (d + 1)) = flipTag ∧
      readTag hn d word (base + 3 * (m.val + 1) * (d + 1)) = !flipTag := by
    have haux : ∀ k ≤ 2 ^ d, readTag hn d word (base + 3 * k * (d + 1)) = !flipTag →
        ∃ m < k,
          readTag hn d word (base + 3 * m * (d + 1)) = flipTag ∧
          readTag hn d word (base + 3 * (m + 1) * (d + 1)) = !flipTag := by
      intro k
      induction k with
      | zero =>
        intro _ h0
        simp only [Nat.mul_zero, zero_mul, add_zero] at h0
        rw [hstart] at h0; cases flipTag <;> simp at h0
      | succ k ih =>
        intro hk hsk
        by_cases htk : readTag hn d word (base + 3 * k * (d + 1)) = flipTag
        · exact ⟨k, Nat.lt_succ_self k, htk, hsk⟩
        · have htk' : readTag hn d word (base + 3 * k * (d + 1)) = !flipTag := by
            cases h : readTag hn d word (base + 3 * k * (d + 1)) <;> cases hf : flipTag <;> simp_all
          obtain ⟨m, hm, h1, h2⟩ := ih (by omega) htk'
          exact ⟨m, Nat.lt_succ_of_lt hm, h1, h2⟩
    have hend' : readTag hn d word (base + 3 * (2 ^ d) * (d + 1)) = !flipTag := by
      have : 3 * (2 ^ d) * (d + 1) = 3 * (d + 1) * 2 ^ d := by ring
      rwa [this]
    obtain ⟨m, hm, h1, h2⟩ := haux (2 ^ d) le_rfl hend'
    exact ⟨⟨m, hm⟩, h1, h2⟩
  obtain ⟨m0, hm0_pre, hm0_post⟩ := hex_flip
  have hu_m0 : readData hn d word (base + 3 * m0.val * (d + 1)) = u :=
    (hmono m0.val (by omega)).1 hm0_pre
  have hs0 := (hstep m0.val m0.isLt).2 hm0_pre
  have hb3_0 : base + 3 * m0.val * (d + 1) + (d + 1) + (d + 1) + (d + 1) =
      base + 3 * (m0.val + 1) * (d + 1) := by ring
  have hsw : readTag hn d word (base + 3 * m0.val * (d + 1) + (d + 1) + (d + 1)) = !flipTag ∧
      readData hn d word (base + 3 * (m0.val + 1) * (d + 1)) = vecXor u (bitsOf d m0.val) ∧
      M u (vecXor u (bitsOf d m0.val)) = true := by
    rcases hs0.2.2.2 with ⟨_, ht3, _⟩ | ⟨ht2, _, hd3, hM⟩
    · rw [hb3_0] at ht3; rw [hm0_post] at ht3; cases flipTag <;> simp at ht3
    · rw [hb3_0] at hd3; rw [hu_m0] at hd3 hM; exact ⟨ht2, hd3, hM⟩
  have hv_eq : v = vecXor u (bitsOf d m0.val) := by
    have hfin := (hmono (2 ^ d) le_rfl).2 (m0.val + 1) (by omega) hm0_post
    have heqL : 3 * (2 ^ d) * (d + 1) = 3 * (d + 1) * 2 ^ d := by ring
    dsimp only [v]
    rw [← heqL, hfin.2, hsw.2.1]
  have hMuv : M u v = true := by rw [hv_eq]; exact hsw.2.2
  have hδ0 : bitsOf d m0.val = vecXor u v := by
    rw [hv_eq]; exact (vecXor_eq_iff u (bitsOf d m0.val) (vecXor u (bitsOf d m0.val))).1 rfl
  refine ⟨hstart, hMuv, m0, hδ0, ?_⟩
  intro i
  let w := d + 1
  let blk := i.val / w
  let r := i.val % w
  let m := blk / 3
  let phase := blk % 3
  have hr : r < w := Nat.mod_lt _ (by omega)
  have hblk : blk < 3 * 2 ^ d := by
    apply Nat.div_lt_of_lt_mul
    have := i.isLt
    have : 3 * (d + 1) * 2 ^ d = w * (3 * 2 ^ d) := by dsimp only [w]; ring
    omega
  have hm : m < 2 ^ d := Nat.div_lt_of_lt_mul hblk
  have hphase : phase < 3 := Nat.mod_lt _ (by omega)
  have hi_eq : i.val = (3 * m + phase) * w + r := by
    have h1 : blk = 3 * m + phase := by simpa [m, phase] using (Nat.div_add_mod blk 3).symm
    have h2 : i.val = blk * w + r := by simpa [blk, r, mul_comm] using (Nat.div_add_mod i.val w).symm
    rw [h2, h1]
  have hread_bit : ∀ (start : ℕ) (x : Fin d → Bool) (t : Bool),
      readData hn d word start = x → readTag hn d word start = t →
      atPos hn word (start + r) = blockBit x t r := by
    intro start x t hdx htx
    dsimp only [blockBit]
    by_cases hrd : r < d
    · simp only [hrd, dite_true]
      have := congrFun hdx ⟨r, hrd⟩
      simpa [readData] using this
    · simp only [hrd, dite_false]
      have hrd' : r = d := by omega
      rw [hrd']
      simpa [readTag] using htx
  have hbi : base + i.val = (base + 3 * m * w + phase * w) + r := by rw [hi_eq]; ring
  rw [hbi]
  dsimp only [mkHalf]
  change atPos hn word (base + 3 * m * w + phase * w + r) =
    if m < m0.val then
      if phase = 0 then blockBit u flipTag r else blockBit (vecXor u (bitsOf d m)) flipTag r
    else if m = m0.val then
      if phase = 0 then blockBit u flipTag r
      else if phase = 1 then blockBit v flipTag r
      else blockBit v (!flipTag) r
    else
      blockBit v (!flipTag) r
  by_cases hlt : m < m0.val
  · simp only [hlt, ite_true]
    have htm : readTag hn d word (base + 3 * m * w) = flipTag := by
      by_contra hne
      have htm' : readTag hn d word (base + 3 * m * w) = !flipTag := by
        cases h : readTag hn d word (base + 3 * m * w) <;> cases hf : flipTag <;>
          first | rfl | exact absurd (h.trans hf.symm) hne
      have hbad := ((hmono m0.val (by omega)).2 m (by omega) htm').1
      rw [hm0_pre] at hbad; cases flipTag <;> simp at hbad
    have hdm : readData hn d word (base + 3 * m * w) = u := (hmono m (by omega)).1 htm
    have hsm := (hstep m hm).2 htm
    have htm1 : readTag hn d word (base + 3 * (m + 1) * w) = flipTag := by
      by_contra hne
      have htm1' : readTag hn d word (base + 3 * (m + 1) * w) = !flipTag := by
        cases h : readTag hn d word (base + 3 * (m + 1) * w) <;> cases hf : flipTag <;>
          first | rfl | exact absurd (h.trans hf.symm) hne
      have hbad := ((hmono m0.val (by omega)).2 (m + 1) (by omega) htm1').1
      rw [hm0_pre] at hbad; cases flipTag <;> simp at hbad
    have hb3m : base + 3 * m * w + w + w + w = base + 3 * (m + 1) * w := by ring
    have htm_p2 : readTag hn d word (base + 3 * m * w + w + w) = flipTag := by
      rcases hsm.2.2.2 with ⟨ht2, _, _⟩ | ⟨_, ht3, _, _⟩
      · exact ht2
      · rw [hb3m] at ht3; rw [htm1] at ht3; cases flipTag <;> simp at ht3
    have hph_cases : phase = 0 ∨ phase = 1 ∨ phase = 2 := by omega
    rcases hph_cases with hp0 | hp1 | hp2
    · rw [hp0]; simp only [Nat.zero_mul, add_zero, ite_true]
      exact hread_bit _ u flipTag hdm htm
    · rw [hp1]; simp only [Nat.one_mul, show (1 : ℕ) ≠ 0 by omega, ite_false]
      exact hread_bit _ (vecXor u (bitsOf d m)) flipTag (by rw [hsm.2.1, hdm]) hsm.1
    · rw [hp2]; simp only [show (2 : ℕ) ≠ 0 by omega, ite_false,
        show base + 3 * m * w + 2 * w = base + 3 * m * w + w + w by ring]
      exact hread_bit _ (vecXor u (bitsOf d m)) flipTag (by rw [hsm.2.2.1, hdm]) htm_p2
  · simp only [hlt, ite_false]
    by_cases heq : m = m0.val
    · rw [heq]; simp only [ite_true]
      have hph_cases : phase = 0 ∨ phase = 1 ∨ phase = 2 := by omega
      rcases hph_cases with hp0 | hp1 | hp2
      · rw [hp0]; simp only [Nat.zero_mul, add_zero, ite_true]
        exact hread_bit _ u flipTag hu_m0 hm0_pre
      · rw [hp1]; simp only [Nat.one_mul, show (1 : ℕ) ≠ 0 by omega, ite_false, ite_true]
        exact hread_bit _ v flipTag (by rw [hs0.2.1, hu_m0, hv_eq]) hs0.1
      · rw [hp2]; simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ite_false,
          show base + 3 * m0.val * w + 2 * w = base + 3 * m0.val * w + w + w by ring]
        exact hread_bit _ v (!flipTag) (by rw [hs0.2.2.1, hu_m0, hv_eq]) hsw.1
    · simp only [heq, ite_false]
      have hgt : m0.val + 1 ≤ m := by omega
      have ⟨htm, hdm⟩ := (hmono m (by omega)).2 (m0.val + 1) hgt hm0_post
      rw [hsw.2.1, ← hv_eq] at hdm
      have hsm := (hstep m hm).1 htm
      have hph_cases : phase = 0 ∨ phase = 1 ∨ phase = 2 := by omega
      rcases hph_cases with hp0 | hp1 | hp2
      · rw [hp0]; simp only [Nat.zero_mul, add_zero]
        exact hread_bit _ v (!flipTag) hdm htm
      · rw [hp1]; simp only [Nat.one_mul]
        exact hread_bit _ v (!flipTag) (hsm.2.1.trans hdm) hsm.1
      · rw [hp2]; simp only [show base + 3 * m * w + 2 * w = base + 3 * m * w + w + w by ring]
        exact hread_bit _ v (!flipTag) (hsm.2.2.2.1.trans hdm) hsm.2.2.1

private lemma mkHalf_satisfies {n : ℕ} (hn : 0 < n) (d : ℕ) (flipTag : Bool)
    (M : (Fin d → Bool) → (Fin d → Bool) → Bool)
    (u v : Fin d → Bool) (m0 : Fin (2 ^ d)) (hδ0 : bitsOf d m0.val = vecXor u v)
    (hMuv : M u v = true)
    (word : Fin n → Bool) (base : ℕ)
    (hinside : ∀ i : Fin (3 * (d + 1) * 2 ^ d),
      atPos hn word (base + i.val) = mkHalf d flipTag u v m0.val i)
    (hexit : ∀ r : ℕ, r < d + 1 →
      atPos hn word (base + 3 * (d + 1) * 2 ^ d + r) = blockBit v (!flipTag) r) :
    ∀ i : Fin (3 * (d + 1) * 2 ^ d),
      transferRow d flipTag M i (fun j => atPos hn word (base + i.val + j.val)) = true := by
  intro i
  let w := d + 1
  let L := 3 * w * 2 ^ d
  have hblk_val : ∀ (m phase r : ℕ), m < 2 ^ d → phase < 3 → r < d + 1 →
      atPos hn word (base + ((3 * m + phase) * (d + 1) + r)) =
        if m < m0.val then
          if phase = 0 then blockBit u flipTag r else blockBit (vecXor u (bitsOf d m)) flipTag r
        else if m = m0.val then
          if phase = 0 then blockBit u flipTag r
          else if phase = 1 then blockBit v flipTag r
          else blockBit v (!flipTag) r
        else
          blockBit v (!flipTag) r := by
    intro m phase r hm hp hr
    have hidx : (3 * m + phase) * (d + 1) + r < 3 * (d + 1) * 2 ^ d := by
      have h1 : 3 * m + phase + 1 ≤ 3 * 2 ^ d := by omega
      have h2 : (3 * m + phase) * (d + 1) + (d + 1) ≤ (3 * 2 ^ d) * (d + 1) := by
        calc (3 * m + phase) * (d + 1) + (d + 1) = (3 * m + phase + 1) * (d + 1) := by ring
          _ ≤ (3 * 2 ^ d) * (d + 1) := Nat.mul_le_mul_right (d + 1) h1
      have h3 : (3 * 2 ^ d) * (d + 1) = 3 * (d + 1) * 2 ^ d := by ring
      omega
    rw [hinside ⟨(3 * m + phase) * (d + 1) + r, hidx⟩]
    dsimp only [mkHalf]
    rw [mul_add_div_right (3 * m + phase) (d + 1) r (by omega) hr,
      mul_add_mod_right (3 * m + phase) (d + 1) r hr,
      show (3 * m + phase) / 3 = m by rw [Nat.mul_add_div (by omega : 0 < 3), Nat.div_eq_of_lt hp, add_zero],
      show (3 * m + phase) % 3 = phase by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hp]]
  have hnext_blk : ∀ (m r : ℕ), m < 2 ^ d → r < d + 1 →
      atPos hn word (base + ((3 * m + 2) * (d + 1) + r + (d + 1))) =
        if m < m0.val then blockBit u flipTag r else blockBit v (!flipTag) r := by
    intro m r hm hr
    by_cases hlast : m + 1 = 2 ^ d
    · have hsum : base + ((3 * m + 2) * (d + 1) + r + (d + 1)) = base + 3 * (d + 1) * 2 ^ d + r := by
        have h1 : 3 * m + 3 = 3 * 2 ^ d := by omega
        calc base + ((3 * m + 2) * (d + 1) + r + (d + 1)) = base + (3 * m + 3) * (d + 1) + r := by ring
          _ = base + (3 * 2 ^ d) * (d + 1) + r := by rw [h1]
          _ = base + 3 * (d + 1) * 2 ^ d + r := by ring
      rw [hsum, hexit r hr]
      have hnotlt : ¬ m < m0.val := by have := m0.isLt; omega
      simp [hnotlt]
    · have hm1 : m + 1 < 2 ^ d := by omega
      have hsum : base + ((3 * m + 2) * (d + 1) + r + (d + 1)) =
          base + ((3 * (m + 1) + 0) * (d + 1) + r) := by ring
      rw [hsum, hblk_val (m + 1) 0 r hm1 (by omega) hr]
      by_cases hlt : m < m0.val
      · by_cases hlt1 : m + 1 < m0.val
        · simp [hlt, hlt1]
        · have heq : m + 1 = m0.val := by omega
          simp [hlt, hlt1, heq]
      · have hnotlt : ¬ m + 1 < m0.val := by omega
        have hne : ¬ m + 1 = m0.val := by omega
        simp [hlt, hnotlt, hne]
  let blk := i.val / (d + 1)
  let r := i.val % (d + 1)
  let m := blk / 3
  let phase := blk % 3
  have hr : r < d + 1 := Nat.mod_lt _ (by omega)
  have hblk : blk < 3 * 2 ^ d := by
    apply Nat.div_lt_of_lt_mul
    have := i.isLt
    have : 3 * (d + 1) * 2 ^ d = (d + 1) * (3 * 2 ^ d) := by ring
    omega
  have hm : m < 2 ^ d := Nat.div_lt_of_lt_mul hblk
  have hphase : phase < 3 := Nat.mod_lt _ (by omega)
  have hi_eq : i.val = (3 * m + phase) * (d + 1) + r := by
    have h1 : blk = 3 * m + phase := by simpa [m, phase] using (Nat.div_add_mod blk 3).symm
    have h2 : i.val = blk * (d + 1) + r := by
      simpa [blk, r, mul_comm] using (Nat.div_add_mod i.val (d + 1)).symm
    rw [h2, h1]
  have hv_m0 : vecXor u (bitsOf d m0.val) = v := by
    rw [hδ0]; funext j; dsimp only [vecXor]; cases u j <;> cases v j <;> rfl
  have hu_m0 : vecXor v (bitsOf d m0.val) = u := by
    rw [← hv_m0, vecXor_invol]
  dsimp only [transferRow]
  rw [Bool.and_eq_true]
  constructor
  · by_cases hi0 : i.val = 0
    · simp only [hi0, ite_true, add_zero, decide_eq_true_eq]
      rw [show base + d = base + ((3 * 0 + 0) * (d + 1) + d) by simp,
        hblk_val 0 0 d (by positivity) (by omega) (by omega)]
      by_cases h0 : 0 < m0.val
      · simp [h0, blockBit]
      · have hm00 : 0 = m0.val := by omega
        simp [h0, hm00, blockBit]
    · simp [hi0]
  · rw [hi_eq]
    rw [mul_add_div_right (3 * m + phase) (d + 1) r (by omega) hr,
      mul_add_mod_right (3 * m + phase) (d + 1) r hr,
      show (3 * m + phase) / 3 = m by rw [Nat.mul_add_div (by omega : 0 < 3), Nat.div_eq_of_lt hphase, add_zero],
      show (3 * m + phase) % 3 = phase by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hphase]]
    have hph_cases : phase = 0 ∨ phase = 1 ∨ phase = 2 := by omega
    rcases hph_cases with hp0 | hp1 | hp2
    · rw [hp0]; simp only [show (0 : ℕ) ≠ 1 by omega, ite_false]
      by_cases hrd : r < d
      · simp only [hrd, dite_true, decide_eq_true_eq, add_zero]
        rw [show base + (3 * m * (d + 1) + r) + (d + 1) = base + ((3 * m + 1) * (d + 1) + r) by ring,
          show base + (3 * m * (d + 1) + r) + (d - r) = base + ((3 * m + 0) * (d + 1) + d) by simp only [add_zero]; omega,
          show base + (3 * m * (d + 1) + r) = base + ((3 * m + 0) * (d + 1) + r) by ring,
          hblk_val m 1 r hm (by omega) hr, hblk_val m 0 d hm (by omega) (by omega),
          hblk_val m 0 r hm (by omega) hr]
        by_cases hlt : m < m0.val
        · simp [hlt, blockBit, hrd, vecXor]
        · by_cases heq : m = m0.val
          · rw [heq]
            simp only [lt_irrefl, ite_false, ite_true, show (1 : ℕ) ≠ 0 by omega, blockBit, hrd,
              dite_false, dite_true]
            have := congrFun hv_m0 ⟨r, hrd⟩
            simpa [vecXor] using this.symm
          · simp only [hlt, heq, ite_false, blockBit, hrd, lt_irrefl, dite_false, dite_true]
            have hne : (!flipTag) ≠ flipTag := by cases flipTag <;> decide
            simp [hne]
      · have hrd' : r = d := by omega
        rw [hrd']
        simp only [lt_irrefl, dite_false, decide_eq_true_eq, add_zero]
        rw [show base + (3 * m * (d + 1) + d) + (d + 1) = base + ((3 * m + 1) * (d + 1) + d) by ring,
          show base + (3 * m * (d + 1) + d) = base + ((3 * m + 0) * (d + 1) + d) by ring,
          hblk_val m 1 d hm (by omega) (by omega), hblk_val m 0 d hm (by omega) (by omega)]
        by_cases hlt : m < m0.val
        · simp [hlt, blockBit]
        · by_cases heq : m = m0.val <;> simp [hlt, heq, blockBit]
    · rw [hp1]; simp only [ite_true]
      by_cases hrd : r < d
      · simp only [hrd, ite_true, decide_eq_true_eq, add_zero]
        rw [show base + ((3 * m + 1) * (d + 1) + r) + (d + 1) = base + ((3 * m + 2) * (d + 1) + r) by ring,
          hblk_val m 2 r hm (by omega) hr, hblk_val m 1 r hm (by omega) hr]
        by_cases hlt : m < m0.val
        · simp [hlt, blockBit, hrd]
        · by_cases heq : m = m0.val <;> simp [hlt, heq, blockBit, hrd]
      · have hrd' : r = d := by omega
        rw [hrd']
        simp only [lt_irrefl, ite_false, add_zero]
        rw [show base + ((3 * m + 1) * (d + 1) + d) + (d + 1) = base + ((3 * m + 2) * (d + 1) + d) by ring,
          hblk_val m 2 d hm (by omega) (by omega), hblk_val m 1 d hm (by omega) (by omega)]
        by_cases hlt : m < m0.val
        · simp [hlt, blockBit]
        · by_cases heq : m = m0.val
          · rw [heq]
            have hne : (!flipTag) ≠ flipTag := by cases flipTag <;> decide
            simp only [lt_irrefl, ite_false, ite_true, show (1 : ℕ) ≠ 0 by omega,
              show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, blockBit, dite_false, hne]
            have hv_read : (fun j : Fin d =>
                atPos hn word (base + ((3 * m0.val + 1) * (d + 1) + d) + (j.val + 1))) = v := by
              funext j
              rw [show base + ((3 * m0.val + 1) * (d + 1) + d) + (j.val + 1) =
                  base + ((3 * m0.val + 2) * (d + 1) + j.val) by ring,
                hblk_val m0.val 2 j.val m0.isLt (by omega) (by omega)]
              simp [blockBit, j.isLt]
            rw [hv_read, hu_m0]
            exact hMuv
          · have hne : (!flipTag) ≠ flipTag := by cases flipTag <;> decide
            simp [hlt, heq, blockBit, hne]
    · rw [hp2]; simp only [show (2 : ℕ) ≠ 1 by omega, ite_false]
      by_cases hrd : r < d
      · simp only [hrd, dite_true, decide_eq_true_eq, add_zero]
        rw [show base + ((3 * m + 2) * (d + 1) + r) + (d + 1) = base + ((3 * m + 2) * (d + 1) + r + (d + 1)) by ring,
          show base + ((3 * m + 2) * (d + 1) + r) + (d - r) = base + ((3 * m + 2) * (d + 1) + d) by omega,
          hnext_blk m r hm hr, hblk_val m 2 d hm (by omega) (by omega),
          hblk_val m 2 r hm (by omega) hr]
        by_cases hlt : m < m0.val
        · simp only [hlt, ite_true, show (2 : ℕ) ≠ 0 by omega, ite_false, blockBit, hrd, lt_irrefl,
            dite_false, dite_true]
          have := congrFun (vecXor_invol u (bitsOf d m)) ⟨r, hrd⟩
          simpa [vecXor] using this.symm
        · have hne : (!flipTag) ≠ flipTag := by cases flipTag <;> decide
          by_cases heq : m = m0.val <;> simp [hlt, heq, blockBit, hrd, hne]
      · have hrd' : r = d := by omega
        rw [hrd']
        simp only [lt_irrefl, dite_false, decide_eq_true_eq, add_zero]
        rw [show base + ((3 * m + 2) * (d + 1) + d) + (d + 1) = base + ((3 * m + 2) * (d + 1) + d + (d + 1)) by ring,
          hnext_blk m d hm (by omega), hblk_val m 2 d hm (by omega) (by omega)]
        by_cases hlt : m < m0.val
        · simp [hlt, blockBit]
        · by_cases heq : m = m0.val <;> simp [hlt, heq, blockBit]

end PEqualNP.Outside.L_clb_047

theorem PEqualNP.Outside.L_clb_047 : ∀ (d p q : ℕ),
  let w := d + 1
  let D := Fin d → Bool
  let L := 3 * w * 2 ^ d
  let R := L + p * w + q * (w + 1)
  let n := L + R
  let pos := fun (i : ℕ) => (⟨i % n, Nat.mod_lt _ (by dsimp [n, R, L, w]; positivity)⟩ : Fin n)
  let Part := fun k : ℕ => Fin k → (Fin (w + 1) → Bool) → Bool
  let accepts := fun (P : Part L) (Q : Part R) (word : Fin n → Bool) =>
    (∀ i : Fin L, P i (fun j => word (pos (i.val + j.val))) = true) ∧
    (∀ k : Fin R, Q k (fun t => word (pos (L + k.val + t.val))) = true)
  let projection := fun (k : ℕ) (enc : (D → D → Bool) → Part k) =>
    ∀ row pat, (∃ c : Bool, ∀ M, enc M row pat = c) ∨
      ∃ u v : D, ∀ M, enc M row pat = M u v
  ∃ (first : (D → D → Bool) → Part L) (last : (D → D → Bool) → Part R),
    projection L first ∧ projection R last ∧
    (∀ A B : D → D → Bool,
      (Finset.univ.filter (accepts (first A) (last B))).card =
        (Finset.univ.filter (fun e : D × D => A e.1 e.2 = true ∧ B e.1 e.2 = true)).card) ∧
    ∀ (s : ℕ) (save : Part L → Fin s) (finish : Fin s → Part R → Bool),
      (∀ A B, finish (save (first A)) (last B) = true ↔
        ∃ x, accepts (first A) (last B) x) → 2 ^ (4 ^ d) ≤ s := by
  intro d p q w D L R n pos Part accepts projection
  have hn : 0 < n := Nat.add_pos_left
    (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos 2) (Nat.succ_pos d)) (Nat.pow_pos (Nat.succ_pos 1))) _
  have hw_eq : w = d + 1 := rfl
  have hL_def : 3 * (d + 1) * 2 ^ d = L := rfl
  have hR_eq : R = L + p * w + q * (w + 1) := rfl
  have hn_eq : n = L + L + p * w + q * (w + 1) := by dsimp only [n, R]; ring
  have hL_ge : w ≤ L := by
    have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    dsimp only [L]; nlinarith
  let first : (D → D → Bool) → Part L := fun A =>
    PEqualNP.Outside.L_clb_047.transferRow d false A
  let last : (D → D → Bool) → Part R := fun B k pat =>
    if hk1 : k.val < L then
      PEqualNP.Outside.L_clb_047.transferRow d true (fun v u => B u v) ⟨k.val, hk1⟩ pat
    else if k.val < L + p * w then
      decide (pat ⟨w, by omega⟩ = pat ⟨0, by omega⟩)
    else
      PEqualNP.Outside.L_clb_047.evenParity pat
  have hproj_first : projection L first :=
    PEqualNP.Outside.L_clb_047.transferRow_projection d false
  have hproj_last : projection R last := by
    intro k pat
    dsimp only [last]
    by_cases hk1 : k.val < L
    · simp only [hk1, dite_true]
      rcases PEqualNP.Outside.L_clb_047.transferRow_projection d true ⟨k.val, hk1⟩ pat with
        ⟨c, hc⟩ | ⟨v, u, huv⟩
      · left; exact ⟨c, fun B => hc (fun v' u' => B u' v')⟩
      · right; exact ⟨u, v, fun B => huv (fun v' u' => B u' v')⟩
    · left
      simp only [hk1, dite_false]
      exact ⟨_, fun _ => rfl⟩
  have hcard : ∀ A B : D → D → Bool,
      (Finset.univ.filter (accepts (first A) (last B))).card =
        (Finset.univ.filter (fun e : D × D => A e.1 e.2 = true ∧ B e.1 e.2 = true)).card := by
    intro A B
    let mkWord : D × D → (Fin n → Bool) := fun ⟨u, v⟩ idx =>
      let m0 := PEqualNP.Outside.L_clb_047.findM0 d (PEqualNP.Outside.L_clb_047.vecXor u v)
      if h1 : idx.val < L then
        PEqualNP.Outside.L_clb_047.mkHalf d false u v m0.val ⟨idx.val, h1⟩
      else if h2 : idx.val < L + L then
        PEqualNP.Outside.L_clb_047.mkHalf d true v u m0.val ⟨idx.val - L, by omega⟩
      else if idx.val < L + L + p * w then
        PEqualNP.Outside.L_clb_047.blockBit u false ((idx.val - (L + L)) % w)
      else
        let rem := (idx.val - (L + L + p * w)) % (w + 1)
        if rem < w then
          PEqualNP.Outside.L_clb_047.blockBit u false rem
        else
          PEqualNP.Outside.L_clb_047.listXor
            (List.ofFn (fun j : Fin w => PEqualNP.Outside.L_clb_047.blockBit u false j.val))
    symm
    refine Finset.card_bij (fun e _ => mkWord e) ?_ ?_ ?_
    · rintro ⟨u, v⟩ he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      rcases he with ⟨hAuv, hBuv⟩
      let m0 := PEqualNP.Outside.L_clb_047.findM0 d (PEqualNP.Outside.L_clb_047.vecXor u v)
      have hm0_spec : PEqualNP.Outside.L_clb_047.bitsOf d m0.val =
          PEqualNP.Outside.L_clb_047.vecXor u v :=
        PEqualNP.Outside.L_clb_047.bitsOf_findM0 d _
      have hm0_spec_rev : PEqualNP.Outside.L_clb_047.bitsOf d m0.val =
          PEqualNP.Outside.L_clb_047.vecXor v u := by
        rw [hm0_spec, PEqualNP.Outside.L_clb_047.vecXor_comm]
      have hmk_start : ∀ r < w,
          PEqualNP.Outside.L_clb_047.atPos hn (mkWord (u, v)) r =
            PEqualNP.Outside.L_clb_047.blockBit u false r := by
        intro r hr
        have hltL : r < L := by omega
        have hltN : r < n := by omega
        dsimp only [PEqualNP.Outside.L_clb_047.atPos, mkWord]
        simp only [Nat.mod_eq_of_lt hltN, hltL, dite_true]
        dsimp only [PEqualNP.Outside.L_clb_047.mkHalf]
        have hdiv : r / (d + 1) = 0 := Nat.div_eq_of_lt (by omega)
        have hmod : r % (d + 1) = r := Nat.mod_eq_of_lt (by omega)
        simp only [hdiv, hmod, Nat.zero_div, Nat.zero_mod, ite_true]
        change (if 0 < m0.val then PEqualNP.Outside.L_clb_047.blockBit u false r
          else if 0 = m0.val then PEqualNP.Outside.L_clb_047.blockBit u false r
          else PEqualNP.Outside.L_clb_047.blockBit v (!false) r) = _
        by_cases h0 : 0 < m0.val
        · simp [h0]
        · have hm00 : 0 = m0.val := by omega
          simp [h0, hm00]
      have hmk_cut : ∀ r < w,
          PEqualNP.Outside.L_clb_047.atPos hn (mkWord (u, v)) (L + r) =
            PEqualNP.Outside.L_clb_047.blockBit v true r := by
        intro r hr
        have hltL : r < L := by omega
        have hltN : L + r < n := by omega
        dsimp only [PEqualNP.Outside.L_clb_047.atPos, mkWord]
        simp only [Nat.mod_eq_of_lt hltN, show ¬ L + r < L by omega, show L + r < L + L by omega,
          dite_false, dite_true, show L + r - L = r by omega]
        dsimp only [PEqualNP.Outside.L_clb_047.mkHalf]
        have hdiv : r / (d + 1) = 0 := Nat.div_eq_of_lt (by omega)
        have hmod : r % (d + 1) = r := Nat.mod_eq_of_lt (by omega)
        simp only [hdiv, hmod, Nat.zero_div, Nat.zero_mod, ite_true]
        change (if 0 < m0.val then PEqualNP.Outside.L_clb_047.blockBit v true r
          else if 0 = m0.val then PEqualNP.Outside.L_clb_047.blockBit v true r
          else PEqualNP.Outside.L_clb_047.blockBit u (!true) r) = _
        by_cases h0 : 0 < m0.val
        · simp [h0]
        · have hm00 : 0 = m0.val := by omega
          simp [h0, hm00]
      have hmk_pad : ∀ (t : ℕ), t ≤ p * w + q * (w + 1) + w - 1 →
          PEqualNP.Outside.L_clb_047.atPos hn (mkWord (u, v)) (L + L + t) =
            if t < p * w then
              PEqualNP.Outside.L_clb_047.blockBit u false (t % w)
            else if t < p * w + q * (w + 1) then
              let rem := (t - p * w) % (w + 1)
              if rem < w then
                PEqualNP.Outside.L_clb_047.blockBit u false rem
              else
                PEqualNP.Outside.L_clb_047.listXor
                  (List.ofFn (fun j : Fin w => PEqualNP.Outside.L_clb_047.blockBit u false j.val))
            else
              PEqualNP.Outside.L_clb_047.blockBit u false (t - (p * w + q * (w + 1))) := by
        intro t ht
        by_cases h1 : t < p * w
        · have hltN : L + L + t < n := by omega
          dsimp only [PEqualNP.Outside.L_clb_047.atPos, mkWord]
          simp only [Nat.mod_eq_of_lt hltN, show ¬ L + L + t < L by omega,
            show ¬ L + L + t < L + L by omega, show L + L + t < L + L + p * w by omega,
            dite_false, ite_true, show L + L + t - (L + L) = t by omega, h1]
        · by_cases h2 : t < p * w + q * (w + 1)
          · have hltN : L + L + t < n := by omega
            dsimp only [PEqualNP.Outside.L_clb_047.atPos, mkWord]
            simp only [Nat.mod_eq_of_lt hltN, show ¬ L + L + t < L by omega,
              show ¬ L + L + t < L + L by omega, show ¬ L + L + t < L + L + p * w by omega,
              dite_false, ite_false, h1, h2, ite_true,
              show L + L + t - (L + L + p * w) = t - p * w by omega]
          · have hrem : t - (p * w + q * (w + 1)) < w := by omega
            have heqN : L + L + t = n + (t - (p * w + q * (w + 1))) := by omega
            simp only [h1, h2, ite_false]
            rw [heqN, PEqualNP.Outside.L_clb_047.atPos_add_n, hmk_start _ hrem]
      have hmk_2L : ∀ r < w,
          PEqualNP.Outside.L_clb_047.atPos hn (mkWord (u, v)) (L + L + r) =
            PEqualNP.Outside.L_clb_047.blockBit u false r := by
        intro r hr
        rw [hmk_pad r (by omega)]
        by_cases hp : p = 0
        · subst hp
          simp only [Nat.zero_mul, Nat.not_lt_zero, ite_false, Nat.zero_add, Nat.sub_zero]
          by_cases hq : q = 0
          · subst hq; simp
          · have hlt : r < q * (w + 1) := by
              have : 1 * (w + 1) ≤ q * (w + 1) := Nat.mul_le_mul_right _ (by omega)
              omega
            simp only [hlt, ite_true, Nat.mod_eq_of_lt (by omega : r < w + 1), hr]
        · have hlt : r < p * w := by
            have : 1 * w ≤ p * w := Nat.mul_le_mul_right _ (by omega)
            omega
          simp only [hlt, ite_true, Nat.mod_eq_of_lt hr]
      constructor
      · intro i
        have hsat := PEqualNP.Outside.L_clb_047.mkHalf_satisfies hn d false A u v m0 hm0_spec hAuv
          (mkWord (u, v)) 0
          (fun idx => by
            have hltL : idx.val < L := idx.isLt
            have hltN : idx.val < n := by omega
            dsimp only [PEqualNP.Outside.L_clb_047.atPos, mkWord]
            simp only [zero_add, Nat.mod_eq_of_lt hltN, hltL, dite_true]
            rfl)
          (fun r hr => by
            have := hmk_cut r hr
            simpa [zero_add, L] using this)
          i
        simpa [first, pos, PEqualNP.Outside.L_clb_047.atPos, zero_add] using hsat
      · intro k
        dsimp only [last]
        by_cases hk1 : k.val < L
        · simp only [hk1, dite_true]
          have hsat := PEqualNP.Outside.L_clb_047.mkHalf_satisfies hn d true (fun v' u' => B u' v')
            v u m0 hm0_spec_rev hBuv (mkWord (u, v)) L
            (fun idx => by
              have hltL : idx.val < L := idx.isLt
              have hltN : L + idx.val < n := by omega
              dsimp only [PEqualNP.Outside.L_clb_047.atPos, mkWord]
              simp only [Nat.mod_eq_of_lt hltN, show ¬ L + idx.val < L by omega,
                show L + idx.val < L + L by omega, dite_false, dite_true,
                show L + idx.val - L = idx.val by omega]
              rfl)
            (fun r hr => by
              have := hmk_2L r hr
              simpa [L, Bool.not_true] using this)
            ⟨k.val, hk1⟩
          simpa [pos, PEqualNP.Outside.L_clb_047.atPos] using hsat
        · simp only [hk1, dite_false]
          by_cases hk2 : k.val < L + p * w
          · simp only [hk2, ite_true, decide_eq_true_eq, add_zero]
            change PEqualNP.Outside.L_clb_047.atPos hn (mkWord (u, v)) (L + k.val + w) =
              PEqualNP.Outside.L_clb_047.atPos hn (mkWord (u, v)) (L + k.val)
            set t := k.val - L
            have ht_lt : t < p * w := by omega
            have h1 : L + k.val = L + L + t := by omega
            have h2 : L + L + t + w = L + L + (t + w) := by omega
            rw [h1, h2, hmk_pad t (by omega), hmk_pad (t + w) (by omega)]
            simp only [ht_lt, ite_true]
            by_cases htw : t + w < p * w
            · simp only [htw, ite_true, Nat.add_mod_right]
            · have htw_ge : p * w ≤ t + w := by omega
              have hrem_lt : t + w - p * w < w := by omega
              have hrem_eq : t + w - p * w = t % w := by
                have hp1 : 1 ≤ p := by
                  by_contra hp0
                  have hp0' : p = 0 := by omega
                  rw [hp0', Nat.zero_mul] at ht_lt
                  omega
                have hpw : (p - 1) * w + w = p * w := by
                  calc (p - 1) * w + w = (p - 1 + 1) * w := by ring
                    _ = p * w := by rw [Nat.sub_add_cancel hp1]
                have hquot : t / w = p - 1 := by
                  have h1' := Nat.div_le_div_right (c := w) (show (p - 1) * w ≤ t by omega)
                  rw [Nat.mul_div_cancel _ (by omega : 0 < w)] at h1'
                  have h2' := Nat.div_lt_of_lt_mul (show t < w * (p - 1 + 1) by rw [mul_comm, Nat.sub_add_cancel hp1]; exact ht_lt)
                  omega
                have hdivmod := Nat.div_add_mod t w
                rw [hquot] at hdivmod
                have hcomm : w * (p - 1) = (p - 1) * w := Nat.mul_comm _ _
                omega
              simp only [htw, ite_false]
              by_cases hq : q = 0
              · subst hq
                simp only [Nat.zero_mul, add_zero, htw, ite_false, hrem_eq]
              · have hltq : t + w < p * w + q * (w + 1) := by
                  have : 1 * (w + 1) ≤ q * (w + 1) := Nat.mul_le_mul_right _ (by omega)
                  omega
                simp only [hltq, ite_true]
                rw [Nat.mod_eq_of_lt (by omega : t + w - p * w < w + 1)]
                simp only [hrem_eq, Nat.mod_lt t (by omega : 0 < w), ite_true]
          · simp only [hk2, ite_false]
            set s := k.val - (L + p * w)
            have hs_lt : s < q * (w + 1) := by have := k.isLt; omega
            let f : ℕ → Bool := fun x =>
              if x % (w + 1) < w then
                PEqualNP.Outside.L_clb_047.blockBit u false (x % (w + 1))
              else
                PEqualNP.Outside.L_clb_047.listXor
                  (List.ofFn (fun j : Fin w => PEqualNP.Outside.L_clb_047.blockBit u false j.val))
            have hpat_eq : (fun t : Fin (w + 1) => mkWord (u, v) (pos (L + k.val + t.val))) =
                (fun t : Fin (w + 1) => f (s + t.val)) := by
              funext t
              change PEqualNP.Outside.L_clb_047.atPos hn (mkWord (u, v)) (L + k.val + t.val) = f (s + t.val)
              rw [show L + k.val + t.val = L + L + (p * w + s + t.val) by omega,
                hmk_pad (p * w + s + t.val) (by omega)]
              have hnot1 : ¬ p * w + s + t.val < p * w := by omega
              simp only [hnot1, ite_false]
              by_cases h2 : p * w + s + t.val < p * w + q * (w + 1)
              · simp only [h2, ite_true, show p * w + s + t.val - p * w = s + t.val by omega, f]
              · simp only [h2, ite_false, f]
                have hrem_lt : p * w + s + t.val - (p * w + q * (w + 1)) < w := by
                  have := t.isLt; omega
                have hmod : (s + t.val) % (w + 1) = p * w + s + t.val - (p * w + q * (w + 1)) := by
                  have heq : s + t.val = q * (w + 1) + (p * w + s + t.val - (p * w + q * (w + 1))) := by omega
                  rw [heq, PEqualNP.Outside.L_clb_047.mul_add_mod_right _ _ _ (by omega)]
                simp [hmod, hrem_lt]
            rw [hpat_eq]
            have hf_per : ∀ x : ℕ, f (x + (w + 1)) = f x := by
              intro x; dsimp only [f]; rw [Nat.add_mod_right]
            have hf_even : ∀ r ≤ w,
                PEqualNP.Outside.L_clb_047.evenParity (fun t : Fin (w + 1) => f (r + t.val)) = true := by
              intro r
              induction r with
              | zero =>
                intro _
                dsimp only [PEqualNP.Outside.L_clb_047.evenParity]
                rw [PEqualNP.Outside.L_clb_047.listXor_ofFn_succ_back]
                have hfront : (fun j : Fin w => f (0 + j.castSucc.val)) =
                    (fun j : Fin w => PEqualNP.Outside.L_clb_047.blockBit u false j.val) := by
                  funext j; dsimp only [f]
                  simp only [zero_add, Fin.val_castSucc, Nat.mod_eq_of_lt (by omega : j.val < w + 1),
                    j.isLt, ite_true]
                have hback : f (0 + (Fin.last w).val) =
                    PEqualNP.Outside.L_clb_047.listXor
                      (List.ofFn (fun j : Fin w => PEqualNP.Outside.L_clb_047.blockBit u false j.val)) := by
                  dsimp only [f]
                  simp only [zero_add, Fin.val_last, Nat.mod_eq_of_lt (Nat.lt_succ_self w),
                    lt_irrefl, ite_false]
                rw [hfront, hback]
                cases PEqualNP.Outside.L_clb_047.listXor
                  (List.ofFn (fun j : Fin w => PEqualNP.Outside.L_clb_047.blockBit u false j.val)) <;> rfl
              | succ r ih =>
                intro hr
                have hprev := ih (by omega)
                dsimp only [PEqualNP.Outside.L_clb_047.evenParity] at hprev ⊢
                have hxprev : PEqualNP.Outside.L_clb_047.listXor
                    (List.ofFn (fun t : Fin (w + 1) => f (r + t.val))) = false := by
                  simpa using hprev
                rw [PEqualNP.Outside.L_clb_047.listXor_ofFn_succ_front] at hxprev
                rw [PEqualNP.Outside.L_clb_047.listXor_ofFn_succ_back]
                have hmid : (fun j : Fin w => f (r + 1 + j.castSucc.val)) =
                    (fun j : Fin w => f (r + j.succ.val)) := by
                  funext j; congr 1; simp; omega
                have hlast : f (r + 1 + (Fin.last w).val) = f (r + (0 : Fin (w + 1)).val) := by
                  have h1 : r + 1 + (Fin.last w).val = r + (w + 1) := by simp; omega
                  have h2 : r + (0 : Fin (w + 1)).val = r := by simp
                  rw [h1, h2, hf_per]
                rw [hmid, hlast]
                set a := f (r + (0 : Fin (w + 1)).val)
                set b := PEqualNP.Outside.L_clb_047.listXor (List.ofFn (fun j : Fin w => f (r + j.succ.val)))
                cases ha : a <;> cases hb : b <;> simp_all
            have hshift : (fun t : Fin (w + 1) => f (s + t.val)) =
                (fun t : Fin (w + 1) => f (s % (w + 1) + t.val)) := by
              funext t
              dsimp only [f]
              have hmod : (s + t.val) % (w + 1) = (s % (w + 1) + t.val) % (w + 1) := by
                rw [Nat.add_mod s t.val, Nat.add_mod (s % (w + 1)) t.val, Nat.mod_mod]
              rw [hmod]
            rw [hshift]
            exact hf_even (s % (w + 1)) (by have := Nat.mod_lt s (by omega : 0 < w + 1); omega)
    · rintro ⟨u1, v1⟩ _ ⟨u2, v2⟩ _ heq
      have hblock_first : ∀ (u' v' : D) (j : Fin d),
          mkWord (u', v') ⟨j.val, by have := j.isLt; omega⟩ = u' j := by
        intro u' v' j
        have hjL : j.val < L := by have := j.isLt; omega
        dsimp only [mkWord]
        simp only [hjL, dite_true]
        dsimp only [PEqualNP.Outside.L_clb_047.mkHalf]
        have hdiv : j.val / (d + 1) = 0 := Nat.div_eq_of_lt (by have := j.isLt; omega)
        have hmod : j.val % (d + 1) = j.val := Nat.mod_eq_of_lt (by have := j.isLt; omega)
        simp only [hdiv, hmod, Nat.zero_div, Nat.zero_mod, ite_true]
        set m' := (PEqualNP.Outside.L_clb_047.findM0 d (PEqualNP.Outside.L_clb_047.vecXor u' v')).val
        by_cases h0 : 0 < m'
        · simp [h0, PEqualNP.Outside.L_clb_047.blockBit, j.isLt]
        · have : 0 = m' := by omega
          simp [h0, this, PEqualNP.Outside.L_clb_047.blockBit, j.isLt]
      have hblock_cut : ∀ (u' v' : D) (j : Fin d),
          mkWord (u', v') ⟨L + j.val, by have := j.isLt; omega⟩ = v' j := by
        intro u' v' j
        have hjL : j.val < L := by have := j.isLt; omega
        dsimp only [mkWord]
        simp only [show ¬ L + j.val < L by omega, show L + j.val < L + L by omega,
          dite_false, dite_true, show L + j.val - L = j.val by omega]
        dsimp only [PEqualNP.Outside.L_clb_047.mkHalf]
        have hdiv : j.val / (d + 1) = 0 := Nat.div_eq_of_lt (by have := j.isLt; omega)
        have hmod : j.val % (d + 1) = j.val := Nat.mod_eq_of_lt (by have := j.isLt; omega)
        simp only [hdiv, hmod, Nat.zero_div, Nat.zero_mod, ite_true]
        set m' := (PEqualNP.Outside.L_clb_047.findM0 d (PEqualNP.Outside.L_clb_047.vecXor u' v')).val
        by_cases h0 : 0 < m'
        · simp [h0, PEqualNP.Outside.L_clb_047.blockBit, j.isLt]
        · have : 0 = m' := by omega
          simp [h0, this, PEqualNP.Outside.L_clb_047.blockBit, j.isLt]
      have hu : u1 = u2 := by
        funext j
        have h := congrFun heq ⟨j.val, by have := j.isLt; omega⟩
        rw [hblock_first, hblock_first] at h
        exact h
      have hv : v1 = v2 := by
        funext j
        have h := congrFun heq ⟨L + j.val, by have := j.isLt; omega⟩
        rw [hblock_cut, hblock_cut] at h
        exact h
      exact Prod.ext hu hv
    · intro word hword
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hword
      rcases hword with ⟨hF, hL⟩
      have hF' : ∀ i : Fin (3 * (d + 1) * 2 ^ d),
          PEqualNP.Outside.L_clb_047.transferRow d false A i
            (fun j => PEqualNP.Outside.L_clb_047.atPos hn word (0 + i.val + j.val)) = true := by
        intro i; simpa [first, pos, PEqualNP.Outside.L_clb_047.atPos, zero_add] using hF i
      have hL_transfer : ∀ i : Fin (3 * (d + 1) * 2 ^ d),
          PEqualNP.Outside.L_clb_047.transferRow d true (fun v u => B u v) i
            (fun j => PEqualNP.Outside.L_clb_047.atPos hn word (L + i.val + j.val)) = true := by
        intro i
        have hiL : i.val < L := by have := i.isLt; omega
        have hk : i.val < R := by omega
        have h := hL ⟨i.val, hk⟩
        dsimp only [last] at h
        simp only [hiL, dite_true] at h
        simpa [pos, PEqualNP.Outside.L_clb_047.atPos] using h
      have htag0 : PEqualNP.Outside.L_clb_047.readTag hn d word 0 = false := by
        have h0 := hF' ⟨0, by positivity⟩
        dsimp only [PEqualNP.Outside.L_clb_047.transferRow] at h0
        simp only [ite_true, Bool.and_eq_true, decide_eq_true_eq] at h0
        simpa [PEqualNP.Outside.L_clb_047.readTag] using h0.1
      have htagL : PEqualNP.Outside.L_clb_047.readTag hn d word L = true := by
        have h0 := hL_transfer ⟨0, by positivity⟩
        dsimp only [PEqualNP.Outside.L_clb_047.transferRow] at h0
        simp only [ite_true, Bool.and_eq_true, decide_eq_true_eq] at h0
        simpa [PEqualNP.Outside.L_clb_047.readTag] using h0.1
      have hcopy_step : ∀ t < p * w,
          PEqualNP.Outside.L_clb_047.atPos hn word (L + L + t + w) =
            PEqualNP.Outside.L_clb_047.atPos hn word (L + L + t) := by
        intro t ht
        have hk : L + t < R := by omega
        have h := hL ⟨L + t, hk⟩
        dsimp only [last] at h
        simp only [show ¬ L + t < L by omega, show L + t < L + p * w by omega,
          dite_false, ite_true, decide_eq_true_eq] at h
        change PEqualNP.Outside.L_clb_047.atPos hn word (L + (L + t) + w) =
          PEqualNP.Outside.L_clb_047.atPos hn word (L + (L + t) + 0) at h
        rw [show L + (L + t) + w = L + L + t + w by omega,
          show L + (L + t) + 0 = L + L + t by omega] at h
        exact h
      have hcopy_mod : ∀ k ≤ p * w + w - 1,
          PEqualNP.Outside.L_clb_047.atPos hn word (L + L + k) =
            PEqualNP.Outside.L_clb_047.atPos hn word (L + L + k % w) := by
        intro k
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          intro hk
          by_cases hkw : k < w
          · rw [Nat.mod_eq_of_lt hkw]
          · have hcs := hcopy_step (k - w) (by omega)
            rw [show L + L + (k - w) + w = L + L + k by omega] at hcs
            rw [hcs, ih (k - w) (by omega) (by omega)]
            congr 2
            exact (Nat.mod_eq_sub_mod (by omega)).symm
      have hparity_row : ∀ s < q * (w + 1),
          PEqualNP.Outside.L_clb_047.evenParity
            (fun j : Fin (w + 1) => PEqualNP.Outside.L_clb_047.atPos hn word (L + L + p * w + s + j.val)) = true := by
        intro s hs
        have hk : L + p * w + s < R := by omega
        have h := hL ⟨L + p * w + s, hk⟩
        dsimp only [last] at h
        simp only [show ¬ L + p * w + s < L by omega, show ¬ L + p * w + s < L + p * w by omega,
          dite_false, ite_false] at h
        have heq : (fun j : Fin (w + 1) => word (pos (L + (L + p * w + s) + j.val))) =
            (fun j : Fin (w + 1) => PEqualNP.Outside.L_clb_047.atPos hn word (L + L + p * w + s + j.val)) := by
          funext j; change PEqualNP.Outside.L_clb_047.atPos hn word (L + (L + p * w + s) + j.val) = _
          rw [show L + (L + p * w + s) + j.val = L + L + p * w + s + j.val by omega]
        rwa [heq] at h
      have hpar_blk : ∀ (c : ℕ), c < q →
          (∀ r < w,
            PEqualNP.Outside.L_clb_047.atPos hn word (L + L + p * w + (c + 1) * (w + 1) + r) =
              PEqualNP.Outside.L_clb_047.atPos hn word (L + L + p * w + c * (w + 1) + r)) ∧
          PEqualNP.Outside.L_clb_047.atPos hn word (L + L + p * w + c * (w + 1) + w) =
            PEqualNP.Outside.L_clb_047.listXor
              (List.ofFn (fun j : Fin w => PEqualNP.Outside.L_clb_047.atPos hn word (L + L + p * w + c * (w + 1) + j.val))) := by
        intro c hc
        let g : ℕ → Bool := fun x => PEqualNP.Outside.L_clb_047.atPos hn word (L + L + p * w + c * (w + 1) + x)
        have hge : ∀ r ≤ w, PEqualNP.Outside.L_clb_047.evenParity (fun j : Fin (w + 1) => g (r + j.val)) = true := by
          intro r hr
          have hs : c * (w + 1) + r < q * (w + 1) := by
            have : (c + 1) * (w + 1) ≤ q * (w + 1) := Nat.mul_le_mul_right _ (by omega)
            linarith
          have h := hparity_row (c * (w + 1) + r) hs
          have heq : (fun j : Fin (w + 1) => PEqualNP.Outside.L_clb_047.atPos hn word (L + L + p * w + (c * (w + 1) + r) + j.val)) =
              (fun j : Fin (w + 1) => g (r + j.val)) := by
            funext j; dsimp only [g]; rw [show L + L + p * w + (c * (w + 1) + r) + j.val =
              L + L + p * w + c * (w + 1) + (r + j.val) by omega]
          rwa [heq] at h
        constructor
        · intro r hr
          have hsh := PEqualNP.Outside.L_clb_047.evenParity_shift g r (hge r (by omega)) (hge (r + 1) (by omega))
          rw [show L + L + p * w + (c + 1) * (w + 1) + r = L + L + p * w + c * (w + 1) + (r + w + 1) by ring]
          exact hsh
        · have hlb := PEqualNP.Outside.L_clb_047.evenParity_last_bit g 0 (hge 0 (by omega))
          simpa [g, zero_add] using hlb
      have hpar_all : ∀ c ≤ q, ∀ r < w,
          PEqualNP.Outside.L_clb_047.atPos hn word (L + L + p * w + c * (w + 1) + r) =
            PEqualNP.Outside.L_clb_047.atPos hn word (L + L + p * w + r) := by
        intro c hc
        induction c with
        | zero => intro r _; simp
        | succ c ih =>
          intro r hr
          rw [(hpar_blk c (by omega)).1 r hr, ih (by omega) r hr]
      have h2L_eq_0 : ∀ r < w,
          PEqualNP.Outside.L_clb_047.atPos hn word (L + L + r) =
            PEqualNP.Outside.L_clb_047.atPos hn word r := by
        intro r hr
        have h1 := hcopy_mod (p * w + r) (by omega)
        rw [PEqualNP.Outside.L_clb_047.mul_add_mod_right p w r hr] at h1
        have h2 := hpar_all q le_rfl r hr
        rw [show L + L + p * w + q * (w + 1) + r = n + r by omega,
          PEqualNP.Outside.L_clb_047.atPos_add_n] at h2
        rw [show L + L + (p * w + r) = L + L + p * w + r by omega] at h1
        rw [← h1, ← h2]
      have htag2L : PEqualNP.Outside.L_clb_047.readTag hn d word (L + L) = false := by
        dsimp only [PEqualNP.Outside.L_clb_047.readTag]
        rw [h2L_eq_0 d (by omega)]
        simpa [PEqualNP.Outside.L_clb_047.readTag] using htag0
      have hdec1 := PEqualNP.Outside.L_clb_047.transfer_unique_decode hn d false A word 0 hF'
        (by simpa [zero_add, L] using htagL)
      have hdec2 := PEqualNP.Outside.L_clb_047.transfer_unique_decode hn d true (fun v u => B u v) word L
        hL_transfer (by simpa [L] using htag2L)
      set u := PEqualNP.Outside.L_clb_047.readData hn d word 0
      set v := PEqualNP.Outside.L_clb_047.readData hn d word L
      have hdata2L : PEqualNP.Outside.L_clb_047.readData hn d word (L + L) = u := by
        funext j; dsimp only [PEqualNP.Outside.L_clb_047.readData, u]
        rw [h2L_eq_0 j.val (by have := j.isLt; omega)]; simp
      have hAuv : A u v = true := by simpa [u, v, L, zero_add] using hdec1.2.1
      have hBuv : B u v = true := by
        have h := hdec2.2.1
        change B (PEqualNP.Outside.L_clb_047.readData hn d word (L + L)) v = true at h
        rwa [hdata2L] at h
      obtain ⟨m1, hm1_δ, hm1_bits⟩ := hdec1.2.2
      obtain ⟨m2, hm2_δ, hm2_bits⟩ := hdec2.2.2
      let m0 := PEqualNP.Outside.L_clb_047.findM0 d (PEqualNP.Outside.L_clb_047.vecXor u v)
      have hm0_δ : PEqualNP.Outside.L_clb_047.bitsOf d m0.val = PEqualNP.Outside.L_clb_047.vecXor u v :=
        PEqualNP.Outside.L_clb_047.bitsOf_findM0 d _
      have hm1_eq : m1 = m0 := by
        apply PEqualNP.Outside.L_clb_047.bitsOf_inj d
        have h1 : PEqualNP.Outside.L_clb_047.bitsOf d m1.val = PEqualNP.Outside.L_clb_047.vecXor u v := by
          simpa [u, v, L, zero_add] using hm1_δ
        exact h1.trans hm0_δ.symm
      have hm2_eq : m2 = m0 := by
        apply PEqualNP.Outside.L_clb_047.bitsOf_inj d
        change PEqualNP.Outside.L_clb_047.bitsOf d m2.val =
          PEqualNP.Outside.L_clb_047.vecXor v (PEqualNP.Outside.L_clb_047.readData hn d word (L + L)) at hm2_δ
        rw [hdata2L, PEqualNP.Outside.L_clb_047.vecXor_comm] at hm2_δ
        exact hm2_δ.trans hm0_δ.symm
      refine ⟨(u, v), by simp [hAuv, hBuv], ?_⟩
      funext idx
      have hblk0 : ∀ r < w,
          PEqualNP.Outside.L_clb_047.atPos hn word r = PEqualNP.Outside.L_clb_047.blockBit u false r := by
        intro r hr
        dsimp only [PEqualNP.Outside.L_clb_047.blockBit]
        by_cases hrd : r < d
        · simp only [hrd, dite_true]; dsimp only [u, PEqualNP.Outside.L_clb_047.readData]; simp
        · have hrd' : r = d := by omega
          rw [hrd']
          simp only [lt_irrefl, dite_false]
          simpa [PEqualNP.Outside.L_clb_047.readTag] using htag0
      dsimp only [mkWord]
      by_cases h1 : idx.val < L
      · simp only [h1, dite_true]
        have h := hm1_bits ⟨idx.val, h1⟩
        rw [hm1_eq] at h
        have h' : PEqualNP.Outside.L_clb_047.atPos hn word idx.val =
            PEqualNP.Outside.L_clb_047.mkHalf d false u v m0.val ⟨idx.val, h1⟩ := by
          simpa [u, v, L, zero_add] using h
        rw [PEqualNP.Outside.L_clb_047.atPos_of_lt] at h'
        exact h'.symm
      · simp only [h1, dite_false]
        by_cases h2 : idx.val < L + L
        · simp only [h2, dite_true]
          have h := hm2_bits ⟨idx.val - L, by omega⟩
          rw [hm2_eq] at h
          have h' : PEqualNP.Outside.L_clb_047.atPos hn word idx.val =
              PEqualNP.Outside.L_clb_047.mkHalf d true v u m0.val ⟨idx.val - L, by omega⟩ := by
            have hsum : L + (idx.val - L) = idx.val := by omega
            change PEqualNP.Outside.L_clb_047.atPos hn word (L + (idx.val - L)) =
              PEqualNP.Outside.L_clb_047.mkHalf d true v (PEqualNP.Outside.L_clb_047.readData hn d word (L + L)) m0.val
                ⟨idx.val - L, by omega⟩ at h
            rwa [hsum, hdata2L] at h
          rw [PEqualNP.Outside.L_clb_047.atPos_of_lt] at h'
          exact h'.symm
        · simp only [h2, dite_false]
          by_cases h3 : idx.val < L + L + p * w
          · simp only [h3, ite_true]
            set t := idx.val - (L + L)
            have ht : t < p * w := by omega
            have hcp := hcopy_mod t (by omega)
            rw [show L + L + t = idx.val by omega, PEqualNP.Outside.L_clb_047.atPos_of_lt,
              h2L_eq_0 _ (Nat.mod_lt _ (by omega)), hblk0 _ (Nat.mod_lt _ (by omega))] at hcp
            exact hcp.symm
          · simp only [h3, ite_false]
            set s := idx.val - (L + L + p * w)
            have hs : s < q * (w + 1) := by have := idx.isLt; omega
            set c := s / (w + 1)
            set rem := s % (w + 1)
            have hc : c < q := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hs)
            have hs_eq : s = c * (w + 1) + rem := by
              simpa [c, rem, mul_comm] using (Nat.div_add_mod s (w + 1)).symm
            have hidx_eq : L + L + p * w + c * (w + 1) + rem = idx.val := by omega
            have hpw_eq : ∀ r < w,
                PEqualNP.Outside.L_clb_047.atPos hn word (L + L + p * w + r) =
                  PEqualNP.Outside.L_clb_047.blockBit u false r := by
              intro r hr
              have hc1 := hcopy_mod (p * w + r) (by omega)
              rw [show L + L + (p * w + r) = L + L + p * w + r by omega,
                PEqualNP.Outside.L_clb_047.mul_add_mod_right p w r hr, h2L_eq_0 r hr, hblk0 r hr] at hc1
              exact hc1
            by_cases hrem : rem < w
            · simp only [hrem, ite_true]
              have hp1 := hpar_all c (by omega) rem hrem
              rw [hidx_eq, PEqualNP.Outside.L_clb_047.atPos_of_lt, hpw_eq rem hrem] at hp1
              exact hp1.symm
            · have hrem_eq : rem = w := by have := Nat.mod_lt s (by omega : 0 < w + 1); omega
              simp only [hrem, ite_false]
              have hpb := (hpar_blk c hc).2
              rw [hrem_eq] at hidx_eq
              rw [hidx_eq, PEqualNP.Outside.L_clb_047.atPos_of_lt] at hpb
              have hfn : (fun j : Fin w => PEqualNP.Outside.L_clb_047.atPos hn word (L + L + p * w + c * (w + 1) + j.val)) =
                  (fun j : Fin w => PEqualNP.Outside.L_clb_047.blockBit u false j.val) := by
                funext j
                rw [hpar_all c (by omega) j.val j.isLt, hpw_eq j.val j.isLt]
              rw [hfn] at hpb
              exact hpb.symm
  refine ⟨first, last, hproj_first, hproj_last, hcard, ?_⟩
  intro s save finish hsf
  have hinj : Function.Injective (fun A : D → D → Bool => save (first A)) := by
    intro A1 A2 heq
    dsimp only at heq
    by_contra hne
    have hex : ∃ u v : D, A1 u v ≠ A2 u v := by
      by_contra hall
      push Not at hall
      apply hne
      funext u v
      exact hall u v
    obtain ⟨u, v, huv⟩ := hex
    let B : D → D → Bool := fun u' v' => decide (u' = u ∧ v' = v)
    have hiff : ∀ A : D → D → Bool,
        finish (save (first A)) (last B) = true ↔ A u v = true := by
      intro A
      rw [hsf A B]
      have hne_iff : (∃ x, accepts (first A) (last B) x) ↔
          0 < (Finset.univ.filter (accepts (first A) (last B))).card := by
        rw [Finset.card_pos]
        constructor
        · rintro ⟨x, hx⟩; exact ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩⟩
        · rintro ⟨x, hx⟩; exact ⟨x, (Finset.mem_filter.1 hx).2⟩
      rw [hne_iff, hcard A B, Finset.card_pos]
      constructor
      · rintro ⟨⟨u', v'⟩, h⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, B, decide_eq_true_eq] at h
        rcases h with ⟨hA, rfl, rfl⟩
        exact hA
      · intro hA
        exact ⟨(u, v), by simp [B, hA]⟩
    have h1 := hiff A1
    have h2 := hiff A2
    rw [heq] at h1
    have heqv : A1 u v = true ↔ A2 u v = true := h1.symm.trans h2
    cases hA1 : A1 u v <;> cases hA2 : A2 u v <;> simp_all
  have hle := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hle
  have hpow : (2 ^ 2 ^ d) ^ 2 ^ d = 2 ^ (4 ^ d) := by
    rw [← pow_mul, ← mul_pow]; norm_num
  simpa [D, hpow] using hle

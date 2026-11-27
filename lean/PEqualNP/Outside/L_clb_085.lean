import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_085_aux

def bitsToNat (m : ℕ) (f : ℕ → Bool) : ℕ :=
  (List.range m).foldl (fun (acc bit : ℕ) => acc ||| ((f bit).toNat <<< bit)) 0

lemma bitsToNat_zero (f : ℕ → Bool) : bitsToNat 0 f = 0 := rfl

lemma bitsToNat_succ_raw (m : ℕ) (f : ℕ → Bool) :
    bitsToNat (m + 1) f = bitsToNat m f ||| ((f m).toNat <<< m) := by
  simp only [bitsToNat, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma one_testBit_of_ne_zero (k : ℕ) (hk : k ≠ 0) : (1 : ℕ).testBit k = false := by
  apply Nat.testBit_lt_two_pow
  have h1 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  omega

lemma bitsToNat_testBit (m : ℕ) (f : ℕ → Bool) (i : ℕ) :
    (bitsToNat m f).testBit i = if i < m then f i else false := by
  induction m with
  | zero => simp [bitsToNat]
  | succ m ih =>
    rw [bitsToNat_succ_raw, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases h1 : i < m
    · have h2 : i < m + 1 := by omega
      have h3 : ¬ m ≤ i := by omega
      simp [h1, h2, h3]
    · by_cases h2 : i = m
      · subst h2
        have hlt : i < i + 1 := Nat.lt_succ_self i
        simp only [h1, hlt, Nat.le_refl, Nat.sub_self, ↓reduceIte, Bool.false_or, decide_true, Bool.true_and]
        cases f i <;> rfl
      · have h3 : ¬ i < m + 1 := by omega
        have hne : i - m ≠ 0 := by omega
        simp only [h1, h3, ↓reduceIte, Bool.false_or]
        by_cases hle : m ≤ i
        · simp only [hle, decide_true, Bool.true_and]
          cases f m
          · simp
          · exact one_testBit_of_ne_zero (i - m) hne
        · simp [hle]

lemma bitsToNat_lt (m : ℕ) (f : ℕ → Bool) : bitsToNat m f < 2 ^ m := by
  induction m with
  | zero => simp [bitsToNat]
  | succ m ih =>
    have hor : bitsToNat m f ||| ((f m).toNat <<< m) = bitsToNat m f + (f m).toNat * 2 ^ m := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_or, bitsToNat_testBit, Nat.testBit_shiftLeft,
        Nat.add_comm (bitsToNat m f), Nat.mul_comm ((f m).toNat),
        Nat.testBit_two_pow_mul_add _ ih, bitsToNat_testBit]
      by_cases h : i < m
      · have hle : ¬ m ≤ i := by omega
        simp [h, hle]
      · have hle : m ≤ i := by omega
        simp [h, hle]
    rw [bitsToNat_succ_raw, hor]
    have hbit : (f m).toNat ≤ 1 := by cases f m <;> decide
    rw [pow_succ']
    have : (f m).toNat * 2 ^ m ≤ 2 ^ m := by
      calc (f m).toNat * 2 ^ m ≤ 1 * 2 ^ m := Nat.mul_le_mul_right _ hbit
        _ = 2 ^ m := Nat.one_mul _
    omega

lemma bitsToNat_succ (m : ℕ) (f : ℕ → Bool) :
    bitsToNat (m + 1) f = bitsToNat m f + (f m).toNat * 2 ^ m := by
  have hlt := bitsToNat_lt m f
  apply Nat.eq_of_testBit_eq
  intro i
  rw [bitsToNat_testBit]
  have hadd : (bitsToNat m f + (f m).toNat * 2 ^ m).testBit i =
      if i < m then (bitsToNat m f).testBit i else ((f m).toNat).testBit (i - m) := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hlt]
  rw [hadd, bitsToNat_testBit]
  by_cases h1 : i < m
  · have h2 : i < m + 1 := by omega
    simp [h1, h2]
  · by_cases h2 : i = m
    · subst h2
      simp only [Nat.lt_irrefl, Nat.lt_succ_self, Nat.sub_self, ↓reduceIte]
      cases f i <;> rfl
    · have h3 : ¬ i < m + 1 := by omega
      simp only [h1, h3, ↓reduceIte]
      cases f m
      · simp
      · exact (one_testBit_of_ne_zero (i - m) (by omega)).symm

lemma bitsToNat_shift (w : ℕ) (hw : 0 < w) (f : ℕ → Bool) :
    bitsToNat w (fun j => f (j + 1)) = bitsToNat w f / 2 + (f w).toNat * 2 ^ (w - 1) := by
  have hlt : bitsToNat w f / 2 < 2 ^ (w - 1) := by
    have h1 := bitsToNat_lt w f
    have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
      have : w = (w - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [bitsToNat_testBit]
  rw [Nat.add_comm (bitsToNat w f / 2), Nat.mul_comm ((f w).toNat), Nat.testBit_two_pow_mul_add _ hlt]
  by_cases h1 : i < w - 1
  · have h2 : i < w := by omega
    have h3 : i + 1 < w := by omega
    simp only [h1, h2, ↓reduceIte]
    rw [Nat.testBit_div_two, bitsToNat_testBit]
    simp [h3]
  · by_cases h2 : i = w - 1
    · subst h2
      have h3 : w - 1 < w := by omega
      have h4 : w - 1 + 1 = w := by omega
      simp only [Nat.lt_irrefl, h3, h4, Nat.sub_self, ↓reduceIte]
      cases f w <;> rfl
    · have h3 : ¬ i < w := by omega
      simp only [h1, h3, ↓reduceIte]
      cases f w
      · simp
      · exact (one_testBit_of_ne_zero (i - (w - 1)) (by omega)).symm

lemma bitsToNat_self (n x : ℕ) (hx : x < 2 ^ n) :
    bitsToNat n (fun j => x.testBit j) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [bitsToNat_testBit]
  by_cases h : i < n
  · simp [h]
  · simp only [h, ↓reduceIte]
    symm
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))

def baseEncode (B : ℕ) : (m : ℕ) → (Fin m → Fin B) → ℕ
  | 0, _ => 0
  | m + 1, f => baseEncode B m (fun i => f i.castSucc) + (f (Fin.last m)).val * B ^ m

lemma baseEncode_lt (B : ℕ) (hB : 0 < B) :
    ∀ (m : ℕ) (f : Fin m → Fin B), baseEncode B m f < B ^ m
  | 0, _ => by simp [baseEncode]
  | m + 1, f => by
    simp only [baseEncode]
    have ih := baseEncode_lt B hB m (fun i => f i.castSucc)
    have hf := (f (Fin.last m)).isLt
    have h1 : (f (Fin.last m)).val + 1 ≤ B := hf
    have h2 : ((f (Fin.last m)).val + 1) * B ^ m ≤ B * B ^ m := Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    rw [pow_succ']
    omega

def baseDecode (B : ℕ) (hB : 0 < B) (m : ℕ) (code : ℕ) (i : Fin m) : Fin B :=
  ⟨(code / B ^ i.val) % B, Nat.mod_lt _ hB⟩

lemma baseDecode_encode (B : ℕ) (hB : 0 < B) :
    ∀ (m : ℕ) (f : Fin m → Fin B) (i : Fin m),
      baseDecode B hB m (baseEncode B m f) i = f i
  | 0, _, i => Fin.elim0 i
  | m + 1, f, i => by
    apply Fin.ext
    simp only [baseDecode, baseEncode]
    by_cases hi : i.val = m
    · have hieq : i = Fin.last m := Fin.ext hi
      subst hieq
      simp only [Fin.val_last]
      have hlt := baseEncode_lt B hB m (fun j => f j.castSucc)
      have hpos : 0 < B ^ m := Nat.pow_pos hB
      rw [Nat.add_comm, Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt, Nat.add_zero,
        Nat.mod_eq_of_lt (f (Fin.last m)).isLt]
    · have hlt_i : i.val < m := by have := i.isLt; omega
      let j : Fin m := ⟨i.val, hlt_i⟩
      have hj_eq : j.castSucc = i := Fin.ext rfl
      have hpow : B ^ m = B ^ i.val * B ^ (m - i.val) := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hlt_i)]
      have hpos : 0 < B ^ i.val := Nat.pow_pos hB
      have hdiv : (baseEncode B m (fun k => f k.castSucc) + (f (Fin.last m)).val * B ^ m) / B ^ i.val =
          baseEncode B m (fun k => f k.castSucc) / B ^ i.val + (f (Fin.last m)).val * B ^ (m - i.val) := by
        rw [hpow, ← Nat.mul_assoc, Nat.mul_comm _ (B ^ i.val), Nat.mul_assoc,
          Nat.add_mul_div_left _ _ hpos]
      have hdvd : B ∣ B ^ (m - i.val) := by
        have hsub : m - i.val = (m - i.val - 1) + 1 := by omega
        rw [hsub, pow_succ']
        exact Nat.dvd_mul_right B _
      rcases hdvd with ⟨q, hq⟩
      rw [hdiv, hq, ← Nat.mul_assoc, Nat.mul_comm ((f (Fin.last m)).val) B, Nat.mul_assoc,
        Nat.add_mul_mod_self_left]
      have ih := congrArg Fin.val (baseDecode_encode B hB m (fun k => f k.castSucc) j)
      simp only [baseDecode, j] at ih
      rw [ih, hj_eq]

def totalCount (n w : ℕ) (rows : ℕ → ℕ → Bool) : ℕ :=
  ((List.range (2 ^ n)).filter (fun word => (List.range n).all (fun site =>
    let pat := (List.range (w + 1)).foldl (fun (acc bit : ℕ) =>
      acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) 0
    rows site pat))).length

lemma branch_raw_table (n w : ℕ) (hn : 0 < n) :
    let S₁ := 2 ^ (n * 2 ^ (w + 1))
    ∃ (start : Fin S₁) (step : ℕ → Fin S₁ → (ℕ → Bool) → Fin S₁) (readout : Fin S₁ → ℕ),
      ∀ table : ℕ → ℕ → Bool,
        readout ((List.range n).foldl (fun state i => step i state (table i)) start) =
          totalCount n w table := by
  intro S₁
  let P := 2 ^ (w + 1)
  let B := 2 ^ P
  have hBpos : 0 < B := Nat.pow_pos (by omega)
  have hS1eq : S₁ = B ^ n := by
    simp only [S₁, B, P]
    rw [← pow_mul, Nat.mul_comm]
  have hS1pos : 0 < S₁ := by rw [hS1eq]; exact Nat.pow_pos hBpos
  let encRow : (ℕ → Bool) → Fin B := fun r => ⟨bitsToNat P r, bitsToNat_lt P r⟩
  let start : Fin S₁ := ⟨0, hS1pos⟩
  let step : ℕ → Fin S₁ → (ℕ → Bool) → Fin S₁ := fun i state row =>
    let nextVal := state.val + (encRow row).val * B ^ i
    if h : nextVal < S₁ then ⟨nextVal, h⟩ else state
  let decodeTbl : Fin S₁ → ℕ → ℕ → Bool := fun state site pat =>
    if hs : site < n then
      (baseDecode B hBpos n state.val ⟨site, hs⟩).val.testBit pat
    else false
  let readout : Fin S₁ → ℕ := fun state => totalCount n w (decodeTbl state)
  refine ⟨start, step, readout, ?_⟩
  intro table
  have hfold : ∀ m (hm : m ≤ n),
      ((List.range m).foldl (fun state i => step i state (table i)) start).val =
        baseEncode B m (fun i => encRow (table i.val)) := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have ihm := ih (by omega)
      simp only [step, ihm]
      have hlt_enc : baseEncode B (m + 1) (fun i => encRow (table i.val)) < B ^ (m + 1) :=
        baseEncode_lt B hBpos (m + 1) _
      have hle_S1 : B ^ (m + 1) ≤ S₁ := by
        rw [hS1eq]; exact Nat.pow_le_pow_right hBpos hm
      have hlt_S1 : baseEncode B m (fun i => encRow (table i.val)) + (encRow (table m)).val * B ^ m < S₁ := by
        have heq : baseEncode B (m + 1) (fun i => encRow (table i.val)) =
            baseEncode B m (fun i => encRow (table i.val)) + (encRow (table m)).val * B ^ m := rfl
        omega
      simp only [hlt_S1, ↓reduceDIte]
      rfl
  have hfin := hfold n (Nat.le_refl n)
  simp only [readout, totalCount]
  congr 1
  apply List.filter_congr
  intro word _
  have hall_congr : ∀ (l : List ℕ) (p q : ℕ → Bool), (∀ a ∈ l, p a = q a) → l.all p = l.all q := by
    intro l p q h
    induction l with
    | nil => rfl
    | cons a tl ih =>
      simp only [List.all_cons, h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
  apply hall_congr
  intro site hsite
  rw [List.mem_range] at hsite
  simp only [decodeTbl, hsite, ↓reduceDIte, hfin]
  have hdec := baseDecode_encode B hBpos n (fun i => encRow (table i.val)) ⟨site, hsite⟩
  rw [hdec]
  have hpat_lt : (List.range (w + 1)).foldl (fun (acc bit : ℕ) =>
      acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) 0 < P :=
    bitsToNat_lt (w + 1) _
  change (bitsToNat P (table site)).testBit _ = table site _
  rw [bitsToNat_testBit]
  simp [hpat_lt]

def roundDown (H x : ℕ) : ℕ :=
  if x < H then x
  else
    let e := Nat.log 2 (x / H)
    (x / 2 ^ e) * 2 ^ e

lemma roundDown_le (H x : ℕ) : roundDown H x ≤ x := by
  unfold roundDown
  split_ifs
  · exact Nat.le_refl x
  · rw [Nat.mul_comm]; exact Nat.mul_div_le x _

lemma roundDown_lower (H x : ℕ) (hH : 0 < H) :
    (H - 1) * x ≤ H * roundDown H x := by
  unfold roundDown
  split_ifs with hlt
  · exact Nat.mul_le_mul_right x (by omega)
  · have hge : H ≤ x := by omega
    have hpos : 0 < x / H := Nat.div_pos hge hH
    let e := Nat.log 2 (x / H)
    have he1 : 2 ^ e ≤ x / H := Nat.pow_log_le_self 2 (by omega)
    have hHe : H * 2 ^ e ≤ x := by
      calc H * 2 ^ e ≤ H * (x / H) := Nat.mul_le_mul_left H he1
        _ ≤ x := Nat.mul_div_le x H
    have h2e : 0 < 2 ^ e := Nat.pow_pos (by omega)
    have hHq : H ≤ x / 2 ^ e := by
      rw [Nat.le_div_iff_mul_le h2e]; exact hHe
    have hdivmod : x = (x / 2 ^ e) * 2 ^ e + x % 2 ^ e := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod x (2 ^ e)).symm
    have hrem : x % 2 ^ e < 2 ^ e := Nat.mod_lt x h2e
    have h1 : (H - 1) * (x % 2 ^ e) ≤ (x / 2 ^ e) * 2 ^ e := by
      calc (H - 1) * (x % 2 ^ e) ≤ H * 2 ^ e := Nat.mul_le_mul (by omega) (Nat.le_of_lt hrem)
        _ ≤ (x / 2 ^ e) * 2 ^ e := Nat.mul_le_mul_right _ hHq
    have h2 : (H - 1) * ((x / 2 ^ e) * 2 ^ e) + (x / 2 ^ e) * 2 ^ e = H * ((x / 2 ^ e) * 2 ^ e) := by
      have : H = (H - 1) + 1 := by omega
      conv_rhs => rw [this, Nat.add_mul, Nat.one_mul]
    calc (H - 1) * x
        = (H - 1) * ((x / 2 ^ e) * 2 ^ e) + (H - 1) * (x % 2 ^ e) := by
          conv_lhs => rw [hdivmod, Nat.mul_add]
      _ ≤ (H - 1) * ((x / 2 ^ e) * 2 ^ e) + (x / 2 ^ e) * 2 ^ e := Nat.add_le_add_left h1 _
      _ = H * ((x / 2 ^ e) * 2 ^ e) := h2

def encVal (H x : ℕ) : ℕ :=
  if x < H then x
  else
    let e := Nat.log 2 (x / H)
    let m := x / 2 ^ e
    (e + 1) * (2 * H) + m

def decVal (H code : ℕ) : ℕ :=
  if code < 2 * H then code
  else
    let e := code / (2 * H) - 1
    let m := code % (2 * H)
    m * 2 ^ e

lemma encVal_lt (n H x : ℕ) (hn : 0 < n) (hH : 2 ≤ H) (hx : x ≤ 2 ^ n) :
    encVal H x < (n + 1) * (2 * H) := by
  unfold encVal
  split_ifs with hlt
  · calc x < H := hlt
      _ ≤ 1 * (2 * H) := by omega
      _ ≤ (n + 1) * (2 * H) := Nat.mul_le_mul_right _ (by omega)
  · have hge : H ≤ x := by omega
    have hpos : 0 < x / H := Nat.div_pos hge (by omega)
    let e := Nat.log 2 (x / H)
    have hdiv_lt : x / H < 2 ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      calc x ≤ 2 ^ n := hx
        _ < 2 ^ n * 2 := by have := Nat.pow_pos (a := 2) (n := n) (by omega); omega
        _ ≤ 2 ^ n * H := Nat.mul_le_mul_left _ hH
    have he_lt : e < n := by
      by_contra hge_e
      have hle : n ≤ e := by omega
      have h1 : 2 ^ n ≤ 2 ^ e := Nat.pow_le_pow_right (by omega) hle
      have h2 : 2 ^ e ≤ x / H := Nat.pow_log_le_self 2 (by omega)
      omega
    have hm_lt : x / 2 ^ e < 2 * H := by
      have h2e : 0 < 2 ^ e := Nat.pow_pos (by omega)
      rw [Nat.div_lt_iff_lt_mul h2e]
      have hlog : x / H < 2 ^ (e + 1) := Nat.lt_pow_succ_log_self (by omega) (x / H)
      have hdivmod : x = H * (x / H) + x % H := (Nat.div_add_mod x H).symm
      have hrem : x % H < H := Nat.mod_lt x (by omega)
      have h1 : x / H + 1 ≤ 2 ^ (e + 1) := hlog
      have h2 : H * (x / H + 1) ≤ H * 2 ^ (e + 1) := Nat.mul_le_mul_left H h1
      rw [Nat.mul_add, Nat.mul_one] at h2
      have h3 : H * 2 ^ (e + 1) = 2 * H * 2 ^ e := by
        rw [pow_succ']; ring
      omega
    have he1 : e + 1 ≤ n := he_lt
    have h3 : (e + 1) * (2 * H) + (x / 2 ^ e) < (e + 2) * (2 * H) := by
      have : (e + 2) * (2 * H) = (e + 1) * (2 * H) + 2 * H := by ring
      omega
    have h4 : (e + 2) * (2 * H) ≤ (n + 1) * (2 * H) := Nat.mul_le_mul_right _ (by omega)
    exact lt_of_lt_of_le h3 h4

lemma decVal_encVal (H x : ℕ) (hH : 0 < H) :
    decVal H (encVal H x) = roundDown H x := by
  unfold decVal encVal roundDown
  by_cases hlt : x < H
  · have hlt2 : x < 2 * H := by omega
    simp [hlt, hlt2]
  · simp only [hlt, ↓reduceIte]
    let e := Nat.log 2 (x / H)
    have h2H : 0 < 2 * H := by omega
    have hm_lt : x / 2 ^ e < 2 * H := by
      have h2e : 0 < 2 ^ e := Nat.pow_pos (by omega)
      rw [Nat.div_lt_iff_lt_mul h2e]
      have hlog : x / H < 2 ^ (e + 1) := Nat.lt_pow_succ_log_self (by omega) (x / H)
      have hdivmod : x = H * (x / H) + x % H := (Nat.div_add_mod x H).symm
      have hrem : x % H < H := Nat.mod_lt x hH
      have h1 : H * (x / H + 1) ≤ H * 2 ^ (e + 1) := Nat.mul_le_mul_left H hlog
      rw [Nat.mul_add, Nat.mul_one] at h1
      have h2 : H * 2 ^ (e + 1) = 2 * H * 2 ^ e := by rw [pow_succ']; ring
      omega
    have hge2 : ¬ (e + 1) * (2 * H) + x / 2 ^ e < 2 * H :=
      Nat.not_lt.mpr (le_trans (Nat.le_mul_of_pos_left (2 * H) (Nat.succ_pos e)) (Nat.le_add_right _ _))
    change (if (e + 1) * (2 * H) + x / 2 ^ e < 2 * H then _ else _) = _
    simp only [hge2, ↓reduceIte]
    have hdiv : ((e + 1) * (2 * H) + x / 2 ^ e) / (2 * H) = e + 1 := by
      rw [Nat.mul_comm, Nat.mul_add_div h2H, Nat.div_eq_of_lt hm_lt, Nat.add_zero]
    have hmod : ((e + 1) * (2 * H) + x / 2 ^ e) % (2 * H) = x / 2 ^ e := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hm_lt]
    rw [hdiv, hmod, Nat.add_sub_cancel]

def nextState (w : ℕ) (hw : 0 < w) (u : Fin (2 ^ w)) (b : Bool) : Fin (2 ^ w) :=
  ⟨u.val / 2 + b.toNat * 2 ^ (w - 1), by
    have h1 := u.isLt
    have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
      have : w = (w - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    have h3 : b.toNat ≤ 1 := by cases b <;> decide
    have h4 : b.toNat * 2 ^ (w - 1) ≤ 2 ^ (w - 1) := by
      calc b.toNat * 2 ^ (w - 1) ≤ 1 * 2 ^ (w - 1) := Nat.mul_le_mul_right _ h3
        _ = 2 ^ (w - 1) := Nat.one_mul _
    omega⟩

def transMat (w : ℕ) (hw : 0 < w) (row : ℕ → Bool) (u v : Fin (2 ^ w)) : ℕ :=
  (if v = nextState w hw u false ∧ row u.val then 1 else 0) +
  (if v = nextState w hw u true ∧ row (u.val + 2 ^ w) then 1 else 0)

def mulStep (w : ℕ) (hw : 0 < w) (A : Fin (2 ^ w) → Fin (2 ^ w) → ℕ)
    (row : ℕ → Bool) (u v : Fin (2 ^ w)) : ℕ :=
  ∑ s : Fin (2 ^ w), A u s * transMat w hw row s v

def idMat (w : ℕ) (u v : Fin (2 ^ w)) : ℕ := if u = v then 1 else 0

def exactMat (w : ℕ) (hw : 0 < w) (table : ℕ → ℕ → Bool) :
    ℕ → Fin (2 ^ w) → Fin (2 ^ w) → ℕ
  | 0 => idMat w
  | k + 1 => mulStep w hw (exactMat w hw table k) (table k)

def approxMat (w : ℕ) (hw : 0 < w) (H : ℕ) (table : ℕ → ℕ → Bool) :
    ℕ → Fin (2 ^ w) → Fin (2 ^ w) → ℕ
  | 0 => idMat w
  | k + 1 => fun u v => roundDown H (mulStep w hw (approxMat w hw H table k) (table k) u v)

lemma mulStep_mono (w : ℕ) (hw : 0 < w) (A B : Fin (2 ^ w) → Fin (2 ^ w) → ℕ)
    (row : ℕ → Bool) (hAB : ∀ u v, A u v ≤ B u v) (u v : Fin (2 ^ w)) :
    mulStep w hw A row u v ≤ mulStep w hw B row u v := by
  apply Finset.sum_le_sum
  intro s _
  exact Nat.mul_le_mul_right _ (hAB u s)

lemma mulStep_scale (w : ℕ) (hw : 0 < w) (c : ℕ) (A : Fin (2 ^ w) → Fin (2 ^ w) → ℕ)
    (row : ℕ → Bool) (u v : Fin (2 ^ w)) :
    mulStep w hw (fun x y => c * A x y) row u v = c * mulStep w hw A row u v := by
  simp only [mulStep, Finset.mul_sum, Nat.mul_assoc]

lemma approxMat_le_exactMat (w : ℕ) (hw : 0 < w) (H : ℕ) (table : ℕ → ℕ → Bool) :
    ∀ k u v, approxMat w hw H table k u v ≤ exactMat w hw table k u v
  | 0, u, v => Nat.le_refl _
  | k + 1, u, v => by
    calc approxMat w hw H table (k + 1) u v
        = roundDown H (mulStep w hw (approxMat w hw H table k) (table k) u v) := rfl
      _ ≤ mulStep w hw (approxMat w hw H table k) (table k) u v := roundDown_le _ _
      _ ≤ mulStep w hw (exactMat w hw table k) (table k) u v :=
          mulStep_mono w hw _ _ _ (approxMat_le_exactMat w hw H table k) u v

lemma approxMat_lower (w : ℕ) (hw : 0 < w) (H : ℕ) (hH : 0 < H) (table : ℕ → ℕ → Bool) :
    ∀ k (hk : k ≤ H) u v,
      (H - k) * exactMat w hw table k u v ≤ H * approxMat w hw H table k u v
  | 0, _, u, v => by simp [approxMat, exactMat]
  | k + 1, hk, u, v => by
    have ih := approxMat_lower w hw H hH table k (by omega)
    let X := mulStep w hw (approxMat w hw H table k) (table k) u v
    have hstep1 : (H - k) * exactMat w hw table (k + 1) u v ≤ H * X := by
      calc (H - k) * exactMat w hw table (k + 1) u v
          = mulStep w hw (fun a b => (H - k) * exactMat w hw table k a b) (table k) u v :=
            (mulStep_scale w hw (H - k) (exactMat w hw table k) (table k) u v).symm
        _ ≤ mulStep w hw (fun a b => H * approxMat w hw H table k a b) (table k) u v :=
            mulStep_mono w hw _ _ _ ih u v
        _ = H * X := mulStep_scale w hw H (approxMat w hw H table k) (table k) u v
    have hround : (H - 1) * X ≤ H * approxMat w hw H table (k + 1) u v :=
      roundDown_lower H X hH
    have hcoeff : H * (H - (k + 1)) ≤ (H - 1) * (H - k) := by
      have h1 : H * (H - (k + 1)) + H = H * (H - k) := by
        have : H - k = (H - (k + 1)) + 1 := by omega
        rw [this, Nat.mul_add, Nat.mul_one]
      have h2 : (H - 1) * (H - k) + (H - k) = H * (H - k) := by
        calc (H - 1) * (H - k) + (H - k) = ((H - 1) + 1) * (H - k) := by ring
          _ = H * (H - k) := by rw [show H - 1 + 1 = H by omega]
      omega
    have hmul : H * ((H - (k + 1)) * exactMat w hw table (k + 1) u v) ≤
        H * (H * approxMat w hw H table (k + 1) u v) := by
      calc H * ((H - (k + 1)) * exactMat w hw table (k + 1) u v)
          = (H * (H - (k + 1))) * exactMat w hw table (k + 1) u v := (Nat.mul_assoc _ _ _).symm
        _ ≤ ((H - 1) * (H - k)) * exactMat w hw table (k + 1) u v :=
            Nat.mul_le_mul_right _ hcoeff
        _ = (H - 1) * ((H - k) * exactMat w hw table (k + 1) u v) := Nat.mul_assoc _ _ _
        _ ≤ (H - 1) * (H * X) := Nat.mul_le_mul_left _ hstep1
        _ = H * ((H - 1) * X) := by ring
        _ ≤ H * (H * approxMat w hw H table (k + 1) u v) := Nat.mul_le_mul_left _ hround
    exact Nat.le_of_mul_le_mul_left hmul hH

def runStates (w : ℕ) (hw : 0 < w) (u : Fin (2 ^ w)) : (k : ℕ) → (Fin k → Bool) → Fin (2 ^ w)
  | 0, _ => u
  | k + 1, seq => nextState w hw (runStates w hw u k (fun i => seq i.castSucc)) (seq (Fin.last k))

def validSeq (w : ℕ) (hw : 0 < w) (table : ℕ → ℕ → Bool) (u : Fin (2 ^ w)) :
    (k : ℕ) → (Fin k → Bool) → Bool
  | 0, _ => true
  | k + 1, seq =>
      validSeq w hw table u k (fun i => seq i.castSucc) &&
      table k ((runStates w hw u k (fun i => seq i.castSucc)).val + (seq (Fin.last k)).toNat * 2 ^ w)

lemma exactMat_eq_card (w : ℕ) (hw : 0 < w) (table : ℕ → ℕ → Bool) :
    ∀ (k : ℕ) (u v : Fin (2 ^ w)),
      exactMat w hw table k u v =
        ((Finset.univ : Finset (Fin k → Bool)).filter
          (fun seq => runStates w hw u k seq = v ∧ validSeq w hw table u k seq = true)).card
  | 0, u, v => by
    simp only [exactMat, idMat, runStates, validSeq, and_true]
    have huniv : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      ext f; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i; exact Fin.elim0 i
    rw [huniv]
    by_cases h : u = v <;> simp [h]
  | k + 1, u, v => by
    simp only [exactMat, mulStep]
    have ih := exactMat_eq_card w hw table k u
    simp_rw [ih]
    let e : ((Fin k → Bool) × Bool) ≃ (Fin (k + 1) → Bool) :=
      { toFun := fun p i => if h : i.val < k then p.1 ⟨i.val, h⟩ else p.2
        invFun := fun seq => (fun i => seq i.castSucc, seq (Fin.last k))
        left_inv := fun ⟨seq, b⟩ => by
          ext
          · rename_i i; simp [i.isLt]
          · simp
        right_inv := fun seq => by
          funext i
          by_cases h : i.val < k
          · simp only [h, ↓reduceDIte]; congr 1
          · have heq : i = Fin.last k := Fin.ext (by simp only [Fin.val_last]; have := i.isLt; omega)
            subst heq; simp }
    have hcard_rhs :
        ((Finset.univ : Finset (Fin (k + 1) → Bool)).filter
          (fun seq => runStates w hw u (k + 1) seq = v ∧ validSeq w hw table u (k + 1) seq = true)).card =
        ((Finset.univ : Finset ((Fin k → Bool) × Bool)).filter
          (fun p => nextState w hw (runStates w hw u k p.1) p.2 = v ∧
            validSeq w hw table u k p.1 = true ∧
            table k ((runStates w hw u k p.1).val + p.2.toNat * 2 ^ w) = true)).card := by
      symm
      refine Finset.card_bij (fun p _ => e p) ?_ ?_ ?_
      · intro ⟨seq, b⟩ hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        have hcast : (fun i : Fin k => e (seq, b) i.castSucc) = seq := by
          funext i; simp [e, i.isLt]
        have hlast : e (seq, b) (Fin.last k) = b := by simp [e]
        simp only [runStates, validSeq, Bool.and_eq_true, hcast, hlast]
        exact ⟨hp.1, hp.2.1, hp.2.2⟩
      · intro p₁ _ p₂ _ heq; exact e.injective heq
      · intro seq hseq
        rw [Finset.mem_filter] at hseq
        have hseq' := hseq.2
        simp only [runStates, validSeq, Bool.and_eq_true] at hseq'
        refine ⟨e.symm seq, ?_, e.apply_symm_apply seq⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, Equiv.coe_fn_symm_mk]
        exact ⟨hseq'.1, hseq'.2.1, hseq'.2.2⟩
    rw [hcard_rhs]
    have hfib :
        ((Finset.univ : Finset ((Fin k → Bool) × Bool)).filter
          (fun p => nextState w hw (runStates w hw u k p.1) p.2 = v ∧
            validSeq w hw table u k p.1 = true ∧
            table k ((runStates w hw u k p.1).val + p.2.toNat * 2 ^ w) = true)).card =
        ∑ s : Fin (2 ^ w),
          (((Finset.univ : Finset ((Fin k → Bool) × Bool)).filter
            (fun p => nextState w hw (runStates w hw u k p.1) p.2 = v ∧
              validSeq w hw table u k p.1 = true ∧
              table k ((runStates w hw u k p.1).val + p.2.toNat * 2 ^ w) = true)).filter
            (fun p => runStates w hw u k p.1 = s)).card :=
      Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ (runStates w hw u k p.1))
    rw [hfib]
    apply Finset.sum_congr rfl
    intro s _
    let A := (Finset.univ : Finset (Fin k → Bool)).filter (fun seq => runStates w hw u k seq = s ∧ validSeq w hw table u k seq = true)
    let B := (Finset.univ : Finset Bool).filter (fun b => v = nextState w hw s b ∧ table k (s.val + b.toNat * 2 ^ w) = true)
    have hB : B.card = transMat w hw (table k) s v := by
      have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
      simp only [B, transMat]
      rw [Finset.card_filter, huniv, Finset.sum_pair (by decide : false ≠ true)]
      simp only [Bool.toNat_false, Bool.toNat_true, Nat.zero_mul, Nat.one_mul, Nat.add_zero]
    rw [← hB, ← Finset.card_product]
    congr 1
    ext ⟨seq, b⟩
    simp only [A, B, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hs, hv⟩, hvb, htbl⟩
      refine ⟨⟨?_, hv, ?_⟩, hs⟩
      · rw [hs]; exact hvb.symm
      · rw [hs]; exact htbl
    · rintro ⟨⟨hvb, hv, htbl⟩, hs⟩
      refine ⟨⟨hs, hv⟩, ?_, ?_⟩
      · rw [← hs]; exact hvb.symm
      · rw [← hs]; exact htbl

lemma exactMat_le_pow (w : ℕ) (hw : 0 < w) (table : ℕ → ℕ → Bool) (k : ℕ) (u v : Fin (2 ^ w)) :
    exactMat w hw table k u v ≤ 2 ^ k := by
  rw [exactMat_eq_card]
  calc ((Finset.univ : Finset (Fin k → Bool)).filter _).card
      ≤ (Finset.univ : Finset (Fin k → Bool)).card := Finset.card_filter_le _ _
    _ = 2 ^ k := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

lemma runStates_testBit (w : ℕ) (hw : 0 < w) (u : Fin (2 ^ w)) :
    ∀ (k : ℕ) (seq : Fin k → Bool) (j : ℕ) (hj : j < w),
      (runStates w hw u k seq).val.testBit j =
        if h : k + j < w then u.val.testBit (k + j)
        else seq ⟨k + j - w, by omega⟩
  | 0, seq, j, hj => by simp [runStates, hj]
  | k + 1, seq, j, hj => by
    simp only [runStates, nextState]
    have hlt : (runStates w hw u k (fun i => seq i.castSucc)).val / 2 < 2 ^ (w - 1) := by
      have h1 := (runStates w hw u k (fun i => seq i.castSucc)).isLt
      have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
        have : w = (w - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ']
      omega
    rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hlt]
    by_cases hj1 : j < w - 1
    · simp only [hj1, ↓reduceIte, Nat.testBit_div_two]
      rw [runStates_testBit w hw u k (fun i => seq i.castSucc) (j + 1) (by omega)]
      have heq : k + (j + 1) = k + 1 + j := by omega
      simp only [heq]
      split_ifs with h
      · rfl
      · rfl
    · have hjeq : j = w - 1 := by omega
      subst hjeq
      have hnot : ¬ k + 1 + (w - 1) < w := by omega
      simp only [Nat.lt_irrefl, Nat.sub_self, hnot, ↓reduceIte, ↓reduceDIte]
      have hidx : (⟨k + 1 + (w - 1) - w, by omega⟩ : Fin (k + 1)) = Fin.last k :=
        Fin.ext (by simp only [Fin.val_last]; omega)
      rw [hidx]
      cases seq (Fin.last k) <;> rfl

lemma validSeq_iff (w : ℕ) (hw : 0 < w) (table : ℕ → ℕ → Bool) (u : Fin (2 ^ w)) :
    ∀ (k : ℕ) (seq : Fin k → Bool),
      validSeq w hw table u k seq = true ↔
        ∀ site : Fin k,
          table site.val ((runStates w hw u site.val (fun i => seq ⟨i.val, by omega⟩)).val +
            (seq site).toNat * 2 ^ w) = true
  | 0, seq => by simp [validSeq]
  | k + 1, seq => by
    simp only [validSeq, Bool.and_eq_true, validSeq_iff w hw table u k]
    constructor
    · rintro ⟨hprev, hlast⟩ site
      by_cases hs : site.val < k
      · exact hprev ⟨site.val, hs⟩
      · have hseq : site = Fin.last k := Fin.ext (by simp only [Fin.val_last]; have := site.isLt; omega)
        subst hseq
        exact hlast
    · intro hall
      refine ⟨fun site => hall site.castSucc, hall (Fin.last k)⟩

lemma trace_exactMat_eq_total (n w : ℕ) (hn : 0 < n) (hw : 0 < w) (table : ℕ → ℕ → Bool) :
    ∑ u : Fin (2 ^ w), exactMat w hw table n u u = totalCount n w table := by
  simp_rw [exactMat_eq_card]
  have hsum :
      ∑ u : Fin (2 ^ w),
        ((Finset.univ : Finset (Fin n → Bool)).filter
          (fun seq => runStates w hw u n seq = u ∧ validSeq w hw table u n seq = true)).card =
      ((Finset.univ : Finset (Fin (2 ^ w) × (Fin n → Bool))).filter
        (fun p => runStates w hw p.1 n p.2 = p.1 ∧ validSeq w hw table p.1 n p.2 = true)).card := by
    symm
    rw [Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ p.1)]
    apply Finset.sum_congr rfl
    intro u _
    refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [← hp.2]; exact hp.1
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
      exact Prod.ext (hp₁.2.trans hp₂.2.symm) heq
    · intro seq hseq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hseq
      refine ⟨(u, seq), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hseq, trivial⟩
  rw [hsum]
  have htotal : totalCount n w table =
      ((Finset.univ : Finset (Fin (2 ^ n))).filter (fun word =>
        ∀ site : Fin n, table site.val (bitsToNat (w + 1) (fun bit => word.val.testBit ((site.val + bit) % n))) = true)).card := by
    simp only [totalCount]
    have hlen : ∀ (P : ℕ → Bool),
        ((List.range (2 ^ n)).filter P).length =
        ((Finset.univ : Finset (Fin (2 ^ n))).filter (fun x => P x.val = true)).card := by
      intro P
      rw [Finset.card_filter]
      have h1 : ((List.range (2 ^ n)).filter P).length =
          ∑ x ∈ Finset.range (2 ^ n), if P x = true then 1 else 0 := by
        have hgen : ∀ m, ((List.range m).filter P).length =
            ∑ x ∈ Finset.range m, if P x = true then 1 else 0 := by
          intro m
          induction m with
          | zero => simp
          | succ m ih =>
            rw [List.range_succ, List.filter_append, List.length_append, Finset.sum_range_succ, ih]
            simp only [List.filter_cons, List.filter_nil]
            cases P m <;> simp
        exact hgen (2 ^ n)
      rw [h1, ← Fin.sum_univ_eq_sum_range (fun x => if P x = true then 1 else 0) (2 ^ n)]
    rw [hlen]
    congr 1
    ext word
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, List.all_eq_true, List.mem_range]
    exact ⟨fun h (site : Fin n) => h site.val site.isLt, fun h s hs => h ⟨s, hs⟩⟩
  rw [htotal]
  let mkPair : Fin (2 ^ n) → Fin (2 ^ w) × (Fin n → Bool) := fun word =>
    (⟨bitsToNat w (fun j => word.val.testBit (j % n)), bitsToNat_lt w _⟩,
     fun i => word.val.testBit ((i.val + w) % n))
  symm
  refine Finset.card_bij (fun word _ => mkPair word) ?_ ?_ ?_
  · intro word hword
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hword ⊢
    have hrun : ∀ k (hk : k ≤ n),
        (runStates w hw (mkPair word).1 k (fun i => (mkPair word).2 ⟨i.val, by omega⟩)).val =
          bitsToNat w (fun j => word.val.testBit ((k + j) % n)) := by
      intro k hk
      apply Nat.eq_of_testBit_eq
      intro j
      rw [bitsToNat_testBit]
      by_cases hj : j < w
      · simp only [hj, ↓reduceIte]
        rw [runStates_testBit w hw _ k _ j hj]
        split_ifs with hkj
        · simp only [mkPair, bitsToNat_testBit, hkj, ↓reduceIte]
        · simp only [mkPair]
          congr 2; omega
      · simp only [hj, ↓reduceIte]
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (runStates w hw _ k _).isLt
          (Nat.pow_le_pow_right (by omega) (by omega)))
    refine ⟨?_, ?_⟩
    · apply Fin.ext
      have hn' := hrun n (Nat.le_refl n)
      have hseq_eq : (fun i : Fin n => (mkPair word).2 ⟨i.val, i.isLt⟩) = (mkPair word).2 := rfl
      rw [hseq_eq] at hn'
      rw [hn']
      apply Nat.eq_of_testBit_eq
      intro j
      simp only [mkPair, bitsToNat_testBit]
      by_cases hj : j < w
      · simp only [hj, ↓reduceIte]; congr 1; exact Nat.add_mod_left n j
      · simp [hj]
    · rw [validSeq_iff]
      intro site
      rw [hrun site.val (Nat.le_of_lt site.isLt)]
      have hpat : bitsToNat w (fun j => word.val.testBit ((site.val + j) % n)) +
          ((mkPair word).2 site).toNat * 2 ^ w =
          bitsToNat (w + 1) (fun bit => word.val.testBit ((site.val + bit) % n)) := by
        rw [bitsToNat_succ]
      rw [hpat]
      exact hword site
  · intro w₁ _ w₂ _ heq
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < n
    · have h1 := congrArg (fun p => p.1.val.testBit j) heq
      have h2 := congrArg (fun p => p.2) heq
      by_cases hjw : j < w
      · simp only [mkPair, bitsToNat_testBit, hjw, ↓reduceIte, Nat.mod_eq_of_lt hj] at h1
        exact h1
      · let r := (j + n - w % n) % n
        have hr_lt : r < n := Nat.mod_lt _ hn
        have h2r := congrFun h2 ⟨r, hr_lt⟩
        simp only [mkPair] at h2r
        have hmod : (r + w) % n = j := by
          simp only [r]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have hw_eq : (w / n) * n + w % n = w := by
            rw [Nat.mul_comm]; exact Nat.div_add_mod w n
          have hwm : w % n < n := Nat.mod_lt w hn
          have hsum : j + n - w % n + w = j + (w / n + 1) * n := by
            calc j + n - w % n + w
                = j + n - w % n + (w % n + (w / n) * n) := by congr 1; exact hw_eq.symm.trans (Nat.add_comm _ _)
              _ = j + n + (w / n) * n := by omega
              _ = j + (w / n + 1) * n := by ring
          rw [hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
        rwa [hmod] at h2r
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le w₁.isLt (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le w₂.isLt (Nat.pow_le_pow_right (by omega) (by omega)))]
  · intro ⟨u, seq⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨hclose, hval⟩
    let stream : ℕ → Bool := fun t =>
      if h : t < w then u.val.testBit t
      else if h2 : t - w < n then seq ⟨t - w, h2⟩
      else false
    have hper_step : ∀ j < w, stream (n + j) = stream j := by
      intro j hj
      have hc := congrArg (fun s => s.val.testBit j) hclose
      rw [runStates_testBit w hw u n seq j hj] at hc
      simp only [stream, hj, ↓reduceDIte]
      split_ifs at hc with hnj
      · simp only [hnj, ↓reduceDIte]; exact hc
      · have hlt : n + j - w < n := by omega
        simp only [hnj, hlt, ↓reduceDIte]
        exact hc
    have hper : ∀ t, t < n + w → stream t = stream (t % n) := by
      intro t ht
      induction t using Nat.strong_induction_on with
      | ind t ih =>
        by_cases htn : t < n
        · rw [Nat.mod_eq_of_lt htn]
        · have hsub : t - n < w := by omega
          have heq : t = n + (t - n) := by omega
          rw [heq, hper_step (t - n) hsub, Nat.add_mod_left]
          exact ih (t - n) (by omega) (by omega)
    let word : Fin (2 ^ n) := ⟨bitsToNat n (fun j => stream j), bitsToNat_lt n _⟩
    have hword_bit : ∀ t, t < n + w → word.val.testBit (t % n) = stream t := by
      intro t ht
      simp only [word, bitsToNat_testBit, Nat.mod_lt t hn, ↓reduceIte]
      exact (hper t ht).symm
    have hmk : mkPair word = (u, seq) := by
      apply Prod.ext
      · apply Fin.ext
        apply Nat.eq_of_testBit_eq
        intro j
        simp only [mkPair, bitsToNat_testBit]
        by_cases hj : j < w
        · simp only [hj, ↓reduceIte]
          rw [hword_bit j (by omega)]
          simp [stream, hj]
        · simp only [hj, ↓reduceIte]
          symm
          exact Nat.testBit_lt_two_pow (lt_of_lt_of_le u.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
      · funext i
        simp only [mkPair]
        have hi := i.isLt
        rw [hword_bit (i.val + w) (by omega)]
        have hnot : ¬ i.val + w < w := by omega
        have hsub : i.val + w - w = i.val := by omega
        simp only [stream, hnot, ↓reduceDIte, hsub, hi]
    refine ⟨word, ?_, hmk⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro site
    rw [validSeq_iff] at hval
    have hs := hval site
    have hpat : (runStates w hw u site.val (fun i => seq ⟨i.val, by omega⟩)).val +
        (seq site).toNat * 2 ^ w =
        bitsToNat (w + 1) (fun bit => word.val.testBit ((site.val + bit) % n)) := by
      rw [bitsToNat_succ]
      congr 1
      · apply Nat.eq_of_testBit_eq
        intro j
        rw [bitsToNat_testBit]
        by_cases hj : j < w
        · simp only [hj, ↓reduceIte]
          rw [runStates_testBit w hw u site.val _ j hj, hword_bit (site.val + j) (by have := site.isLt; omega)]
          simp only [stream]
          split_ifs with h1 h2
          · rfl
          · rfl
          · exfalso; have := site.isLt; omega
        · simp only [hj, ↓reduceIte]
          exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (runStates w hw u site.val _).isLt
            (Nat.pow_le_pow_right (by omega) (by omega)))
      · congr 2
        have h := congrFun (congrArg Prod.snd hmk) site
        simpa [mkPair] using h.symm
    rwa [← hpat]

lemma branch_approx_matrix (n w b : ℕ) (hn : 0 < n) (hw : 0 < w) :
    let D := 2 ^ w
    let K := 2 ^ b
    let S₂ := (1 + 4 * (n + 1) ^ 2 * K) ^ (D * D)
    ∃ (start : Fin S₂) (step : ℕ → Fin S₂ → (ℕ → Bool) → Fin S₂) (readout : Fin S₂ → ℕ),
      ∀ table : ℕ → ℕ → Bool,
        let estimate := readout ((List.range n).foldl (fun state i => step i state (table i)) start)
        estimate ≤ totalCount n w table ∧ K * totalCount n w table ≤ (K + 1) * estimate := by
  intro D K S₂
  let M := 1 + 4 * (n + 1) ^ 2 * K
  let H := 2 * (n + 1) * K
  have hKpos : 0 < K := Nat.pow_pos (by omega)
  have hHeq : H = 2 * ((n + 1) * K) := by simp only [H]; ring
  have hHge2 : 2 ≤ H := by
    have : 1 ≤ (n + 1) * K := Nat.mul_pos (by omega) hKpos
    omega
  have hHpos : 0 < H := by omega
  have hMpos : 0 < M := by omega
  have hHM : (n + 1) * (2 * H) < M := by
    have h1 : (n + 1) * (2 * H) = 4 * (n + 1) ^ 2 * K := by
      simp only [H]; ring
    omega
  have hS2pos : 0 < S₂ := Nat.pow_pos hMpos
  let toFlat : (Fin D → Fin D → Fin M) → (Fin (D * D) → Fin M) := fun A idx =>
    have hD : 0 < D := Nat.pow_pos (by omega)
    A ⟨idx.val / D, Nat.div_lt_of_lt_mul idx.isLt⟩
      ⟨idx.val % D, Nat.mod_lt _ hD⟩
  let encMat : (Fin D → Fin D → ℕ) → Fin S₂ := fun A =>
    ⟨baseEncode M (D * D) (toFlat (fun u v => ⟨encVal H (A u v) % M, Nat.mod_lt _ hMpos⟩)),
      baseEncode_lt M hMpos (D * D) _⟩
  let decMat : Fin S₂ → Fin D → Fin D → ℕ := fun state u v =>
    have hidx : u.val * D + v.val < D * D := by
      have h1 : (u.val + 1) * D ≤ D * D := Nat.mul_le_mul_right D u.isLt
      rw [Nat.add_mul, Nat.one_mul] at h1
      have := v.isLt; omega
    decVal H (baseDecode M hMpos (D * D) state.val ⟨u.val * D + v.val, hidx⟩).val
  have hdec_enc : ∀ A : Fin D → Fin D → ℕ, (∀ u v, A u v ≤ 2 ^ n) →
      ∀ u v, decMat (encMat A) u v = roundDown H (A u v) := by
    intro A hA u v
    simp only [decMat, encMat]
    have hD : 0 < D := Nat.pow_pos (by omega)
    have hidx : u.val * D + v.val < D * D := by
      have h1 : (u.val + 1) * D ≤ D * D := Nat.mul_le_mul_right D u.isLt
      rw [Nat.add_mul, Nat.one_mul] at h1
      have := v.isLt; omega
    rw [baseDecode_encode M hMpos (D * D) _ ⟨u.val * D + v.val, hidx⟩]
    simp only [toFlat]
    have hdiv : (u.val * D + v.val) / D = u.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hD, Nat.div_eq_of_lt v.isLt, Nat.add_zero]
    have hmod : (u.val * D + v.val) % D = v.val := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt v.isLt]
    have hu_eq : (⟨(u.val * D + v.val) / D, Nat.div_lt_of_lt_mul hidx⟩ : Fin D) = u :=
      Fin.ext hdiv
    have hv_eq : (⟨(u.val * D + v.val) % D, Nat.mod_lt _ hD⟩ : Fin D) = v :=
      Fin.ext hmod
    rw [hu_eq, hv_eq]
    have hltM : encVal H (A u v) < M :=
      lt_trans (encVal_lt n H (A u v) hn hHge2 (hA u v)) hHM
    rw [Nat.mod_eq_of_lt hltM, decVal_encVal H (A u v) hHpos]
  let start : Fin S₂ := encMat (idMat w)
  let step : ℕ → Fin S₂ → (ℕ → Bool) → Fin S₂ := fun _ state row =>
    encMat (mulStep w hw (decMat state) row)
  let readout : Fin S₂ → ℕ := fun state => ∑ u : Fin D, decMat state u u
  refine ⟨start, step, readout, ?_⟩
  intro table
  have hfold : ∀ k (hk : k ≤ n),
      decMat ((List.range k).foldl (fun state i => step i state (table i)) start) =
        approxMat w hw H table k := by
    intro k hk
    induction k with
    | zero =>
      funext u v
      simp only [List.range_zero, List.foldl_nil, start, approxMat]
      have hid_le : ∀ a b, idMat w a b ≤ 2 ^ n := by
        intro a b
        have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
        simp only [idMat]; split_ifs <;> omega
      rw [hdec_enc (idMat w) hid_le u v]
      have hid_lt : idMat w u v < H := by simp only [idMat]; split_ifs <;> omega
      simp [roundDown, hid_lt]
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hprev := ih (by omega)
      simp only [step, hprev]
      funext u v
      have hbound : ∀ a b, mulStep w hw (approxMat w hw H table k) (table k) a b ≤ 2 ^ n := by
        intro a b
        calc mulStep w hw (approxMat w hw H table k) (table k) a b
            ≤ mulStep w hw (exactMat w hw table k) (table k) a b :=
              mulStep_mono w hw _ _ _ (approxMat_le_exactMat w hw H table k) a b
          _ = exactMat w hw table (k + 1) a b := rfl
          _ ≤ 2 ^ (k + 1) := exactMat_le_pow w hw table (k + 1) a b
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hk
      exact hdec_enc _ hbound u v
  have hfin := hfold n (Nat.le_refl n)
  dsimp only
  simp only [readout, hfin]
  have htr : ∑ u : Fin D, exactMat w hw table n u u = totalCount n w table :=
    trace_exactMat_eq_total n w hn hw table
  constructor
  · rw [← htr]
    apply Finset.sum_le_sum
    intro u _
    exact approxMat_le_exactMat w hw H table n u u
  · have hnH : n ≤ H := by
      have h1 : n ≤ (n + 1) * K := by
        calc n ≤ n + 1 := Nat.le_succ n
          _ = (n + 1) * 1 := (Nat.mul_one _).symm
          _ ≤ (n + 1) * K := Nat.mul_le_mul_left _ hKpos
      omega
    have hlow : (H - n) * totalCount n w table ≤ H * ∑ u : Fin D, approxMat w hw H table n u u := by
      rw [← htr, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro u _
      exact approxMat_lower w hw H hHpos table n hnH u u
    have hKH : K * H ≤ (K + 1) * (H - n) := by
      have h1 : (K + 1) * (H - n) + (K + 1) * n = (K + 1) * H := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hnH]
      have h2 : (K + 1) * n ≤ H := by
        have hK1 : K + 1 ≤ 2 * K := by omega
        calc (K + 1) * n ≤ (2 * K) * n := Nat.mul_le_mul_right n hK1
          _ = 2 * n * K := by ring
          _ ≤ 2 * (n + 1) * K := Nat.mul_le_mul_right K (by omega)
      have h3 : (K + 1) * H = K * H + H := by ring
      omega
    have hmul : H * (K * totalCount n w table) ≤
        H * ((K + 1) * ∑ u : Fin D, approxMat w hw H table n u u) := by
      calc H * (K * totalCount n w table)
          = (K * H) * totalCount n w table := by ring
        _ ≤ ((K + 1) * (H - n)) * totalCount n w table := Nat.mul_le_mul_right _ hKH
        _ = (K + 1) * ((H - n) * totalCount n w table) := Nat.mul_assoc _ _ _
        _ ≤ (K + 1) * (H * ∑ u : Fin D, approxMat w hw H table n u u) :=
            Nat.mul_le_mul_left _ hlow
        _ = H * ((K + 1) * ∑ u : Fin D, approxMat w hw H table n u u) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hHpos

end PEqualNP.Outside.L_clb_085_aux

theorem PEqualNP.Outside.L_clb_085 :
∀ (n w b : Nat), 0 < n → 0 < w →
  let D := 2^w
  let K := 2^b
  let S := min (2^(n*2^(w+1))) ((1+4*(n+1)^2*K)^(D*D))
  let Row := Nat → Bool
  let total := fun (rows : Nat → Row) =>
    ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
      let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
        acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
      rows site pat))).length
  ∃ (start : Fin S) (step : Nat → Fin S → Row → Fin S) (readout : Fin S → Nat),
    ∀ table : Nat → Row,
      let estimate := readout ((List.range n).foldl (fun state i => step i state (table i)) start)
      estimate ≤ total table ∧ K * total table ≤ (K+1)*estimate := by
  intro n w b hn hw D K S Row total
  by_cases hle : 2 ^ (n * 2 ^ (w + 1)) ≤ (1 + 4 * (n + 1) ^ 2 * K) ^ (D * D)
  · have hSeq : S = 2 ^ (n * 2 ^ (w + 1)) := Nat.min_eq_left hle
    rcases PEqualNP.Outside.L_clb_085_aux.branch_raw_table n w hn with ⟨start, step, readout, hspec⟩
    let castS : Fin (2 ^ (n * 2 ^ (w + 1))) → Fin S := fun x => ⟨x.val, by omega⟩
    let uncastS : Fin S → Fin (2 ^ (n * 2 ^ (w + 1))) := fun x => ⟨x.val, by omega⟩
    refine ⟨castS start, fun i st r => castS (step i (uncastS st) r), fun st => readout (uncastS st), ?_⟩
    intro table
    have hfold : ∀ m,
        uncastS ((List.range m).foldl (fun state i => castS (step i (uncastS state) (table i))) (castS start)) =
        (List.range m).foldl (fun state i => step i state (table i)) start := by
      intro m
      induction m with
      | zero => exact Fin.ext rfl
      | succ m ih =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.foldl_append, List.foldl_cons, List.foldl_nil]
        change step m (uncastS _) (table m) = _
        rw [ih]
    have heq : readout (uncastS ((List.range n).foldl
        (fun state i => castS (step i (uncastS state) (table i))) (castS start))) = total table := by
      rw [hfold n]
      exact hspec table
    dsimp only
    rw [heq]
    exact ⟨Nat.le_refl _, Nat.mul_le_mul_right _ (Nat.le_succ K)⟩
  · have hSeq : S = (1 + 4 * (n + 1) ^ 2 * K) ^ (D * D) := Nat.min_eq_right (by omega)
    rcases PEqualNP.Outside.L_clb_085_aux.branch_approx_matrix n w b hn hw with ⟨start, step, readout, hspec⟩
    let castS : Fin ((1 + 4 * (n + 1) ^ 2 * K) ^ (D * D)) → Fin S := fun x => ⟨x.val, by omega⟩
    let uncastS : Fin S → Fin ((1 + 4 * (n + 1) ^ 2 * K) ^ (D * D)) := fun x => ⟨x.val, by omega⟩
    refine ⟨castS start, fun i st r => castS (step i (uncastS st) r), fun st => readout (uncastS st), ?_⟩
    intro table
    have hfold : ∀ m,
        uncastS ((List.range m).foldl (fun state i => castS (step i (uncastS state) (table i))) (castS start)) =
        (List.range m).foldl (fun state i => step i state (table i)) start := by
      intro m
      induction m with
      | zero => exact Fin.ext rfl
      | succ m ih =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.foldl_append, List.foldl_cons, List.foldl_nil]
        change step m (uncastS _) (table m) = _
        rw [ih]
    dsimp only
    rw [hfold n]
    exact hspec table

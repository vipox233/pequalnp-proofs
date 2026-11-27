import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_208_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.ProofComplexity

lemma testBit_lt_of_lt {a m i : ℕ} (ha : a < 2 ^ m) (hi : m ≤ i) : a.testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hi)

def stepFold (f : ℕ → Bool) (m : ℕ) : ℕ :=
  (List.range m).foldl (fun acc i => acc ||| ((f i).toNat <<< i)) 0

lemma stepFold_lt (f : ℕ → Bool) (m : ℕ) : stepFold f m < 2 ^ m := by
  induction m with
  | zero => simp [stepFold]
  | succ m ih =>
    unfold stepFold
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change stepFold f m ||| ((f m).toNat <<< m) < 2 ^ (m + 1)
    have hbit : ((f m).toNat <<< m) < 2 ^ (m + 1) := by
      rw [Nat.shiftLeft_eq]
      cases f m <;> simp [Nat.pow_succ]
    have hlt1 : stepFold f m < 2 ^ (m + 1) := lt_trans ih (by rw [Nat.pow_succ]; omega)
    have heq : (stepFold f m ||| ((f m).toNat <<< m)) =
        (stepFold f m ||| ((f m).toNat <<< m)) % 2 ^ (m + 1) := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow, Nat.testBit_or]
      by_cases hi : i < m + 1
      · simp [hi]
      · have h1 : (stepFold f m).testBit i = false := testBit_lt_of_lt hlt1 (by omega)
        have h2 : ((f m).toNat <<< m).testBit i = false := testBit_lt_of_lt hbit (by omega)
        simp [hi, h1, h2]
    rw [heq]
    exact Nat.mod_lt _ (Nat.two_pow_pos (m + 1))

lemma stepFold_testBit (f : ℕ → Bool) (m i : ℕ) :
    (stepFold f m).testBit i = if i < m then f i else false := by
  induction m with
  | zero => simp [stepFold]
  | succ m ih =>
    unfold stepFold
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (stepFold f m ||| ((f m).toNat <<< m)).testBit i = if i < m + 1 then f i else false
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases him : i < m
    · have hnot : ¬(m ≤ i) := by omega
      have hlt : i < m + 1 := by omega
      simp [him, hnot, hlt]
    · by_cases heq : i = m
      · subst heq
        cases hfm : f i <;> simp
      · have hgt : ¬(i < m + 1) := by omega
        have htb : (f m).toNat.testBit (i - m) = false := by
          apply testBit_lt_of_lt (m := 1)
          · cases f m <;> simp
          · omega
        simp [him, hgt, htb]

lemma two_pow_add_eq_four_pow (w : ℕ) : 2 ^ (w + w) = 4 ^ w := by
  rw [Nat.pow_add, ← Nat.mul_pow]

def posOf {n w : ℕ} (hn : 0 < n) (start : Fin n) (offset : Fin (w + 1)) : Fin n :=
  ⟨(start.val + offset.val) % n, Nat.mod_lt _ hn⟩

def maxPos (n w : ℕ) (start : Fin n) : ℕ :=
  if start.val + w < n then start.val + w else n - 1

lemma maxPos_lt {n w : ℕ} (hn : 0 < n) (start : Fin n) : maxPos n w start < n := by
  unfold maxPos
  split_ifs <;> omega

def isActive (w t v : ℕ) : Prop :=
  v < t ∧ (v < w ∨ t - w ≤ v)

lemma posOf_le_maxPos {n w : ℕ} (hn : 0 < n) (start : Fin n) (o : Fin (w + 1)) :
    (posOf hn start o).val ≤ maxPos n w start := by
  unfold posOf maxPos
  dsimp only
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have := Nat.mod_lt (start.val + o.val) hn
    omega

lemma posOf_active_of_lt_maxPos {n w : ℕ} (hn : 0 < n) (start : Fin n) (o : Fin (w + 1))
    (hlt : (posOf hn start o).val < maxPos n w start) :
    isActive w (maxPos n w start) (posOf hn start o).val := by
  refine ⟨hlt, ?_⟩
  unfold posOf maxPos at hlt ⊢
  dsimp only at hlt ⊢
  split_ifs at hlt ⊢ with h
  · right
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · by_cases hvw : (start.val + o.val) % n < w
    · left; exact hvw
    · right
      have hwn : w < n := by
        have := Nat.mod_lt (start.val + o.val) hn
        omega
      by_cases hsum : start.val + o.val < n
      · rw [Nat.mod_eq_of_lt hsum]
        omega
      · have hmod : (start.val + o.val) % n = start.val + o.val - n := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega

def nextState (w t st : ℕ) (b : Bool) : ℕ :=
  stepFold (fun idx =>
    if idx < w then
      if idx = t then b else st.testBit idx
    else
      if idx = w then b else st.testBit (idx - 1)) (w + w)

lemma nextState_lt (w t st : ℕ) (b : Bool) : nextState w t st b < 4 ^ w := by
  rw [← two_pow_add_eq_four_pow]
  exact stepFold_lt _ (w + w)

def stVal (w t st v : ℕ) : Bool :=
  if v < w then st.testBit v else st.testBit (w + (t - 1 - v))

lemma stVal_nextState {w t st v : ℕ} {b : Bool} (hact : isActive w (t + 1) v) :
    stVal w (t + 1) (nextState w t st b) v = if v = t then b else stVal w t st v := by
  rcases hact with ⟨hvlt, hvw | hvr⟩
  · unfold stVal nextState
    rw [ite_eq_left_iff.mpr (fun h => absurd hvw h),
      ite_eq_left_iff.mpr (fun h => absurd hvw h),
      stepFold_testBit]
    have hlt2 : v < w + w := by omega
    simp only [hlt2, hvw, ↓reduceIte]
  · by_cases hvw : v < w
    · unfold stVal nextState
      rw [ite_eq_left_iff.mpr (fun h => absurd hvw h),
        ite_eq_left_iff.mpr (fun h => absurd hvw h),
        stepFold_testBit]
      have hlt2 : v < w + w := by omega
      simp only [hlt2, hvw, ↓reduceIte]
    · unfold stVal nextState
      rw [ite_eq_right_iff.mpr (fun h => absurd h hvw),
        ite_eq_right_iff.mpr (fun h => absurd h hvw),
        stepFold_testBit]
      have hlt2 : w + (t + 1 - 1 - v) < w + w := by omega
      have hnw : ¬(w + (t + 1 - 1 - v) < w) := by omega
      simp only [hlt2, hnw, ↓reduceIte]
      by_cases hvt : v = t
      · subst hvt
        simp
      · have hne : t - v ≠ 0 := by omega
        have hsub : w + (t - v) - 1 = w + (t - 1 - v) := by omega
        simp [hvt, hne, hsub]

lemma active_succ_subset {w t v : ℕ} (h : isActive w (t + 1) v) (hne : v ≠ t) :
    isActive w t v := by
  rcases h with ⟨h1, h2 | h2⟩
  · exact ⟨by omega, Or.inl h2⟩
  · exact ⟨by omega, Or.inr (by omega)⟩

def extVal (w t st : ℕ) (b : Bool) (v : ℕ) : Bool :=
  if v = t then b else stVal w t st v

def windowPat {n w : ℕ} (hn : 0 < n) (t st : ℕ) (b : Bool) (start : Fin n) :
    Fin (w + 1) → Bool :=
  fun o => extVal w t st b (posOf hn start o).val

def startsAt (n w t : ℕ) : List (Fin n) :=
  (List.finRange n).filter (fun s => decide (maxPos n w s = t))

def touchBool {n : ℕ} (w : ℕ) (hn : 0 < n) (start : Fin n) (v : Fin n) : Bool :=
  (List.finRange (w + 1)).any (fun o => decide (posOf hn start o = v))

lemma touchBool_eq_true_iff {n : ℕ} (w : ℕ) (hn : 0 < n) (start v : Fin n) :
    touchBool w hn start v = true ↔ ∃ o : Fin (w + 1), posOf hn start o = v := by
  simp [touchBool]

def patCode {w : ℕ} (p : Fin (w + 1) → Bool) : ℕ :=
  stepFold (fun i => if h : i < w + 1 then p ⟨i, h⟩ else false) (w + 1)

lemma patCode_lt {w : ℕ} (p : Fin (w + 1) → Bool) : patCode p < 2 ^ (w + 1) :=
  stepFold_lt _ (w + 1)

lemma patCode_testBit {w : ℕ} (p : Fin (w + 1) → Bool) (o : Fin (w + 1)) :
    (patCode p).testBit o.val = p o := by
  unfold patCode
  rw [stepFold_testBit]
  simp [o.isLt]

def inpWire {n w : ℕ} (start : Fin n) (p : Fin (w + 1) → Bool) : ℕ :=
  start.val * 2 ^ (w + 1) + patCode p

lemma inpWire_lt {n w : ℕ} (start : Fin n) (p : Fin (w + 1) → Bool) :
    inpWire start p < n * 2 ^ (w + 1) := by
  unfold inpWire
  have hp := patCode_lt p
  have h1 : (start.val + 1) * 2 ^ (w + 1) ≤ n * 2 ^ (w + 1) :=
    Nat.mul_le_mul_right _ start.isLt
  have h2 : (start.val + 1) * 2 ^ (w + 1) = start.val * 2 ^ (w + 1) + 2 ^ (w + 1) := by ring
  omega

lemma inputs_getD_inpWire {n w : ℕ} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (start : Fin n) (p : Fin (w + 1) → Bool) :
    let I := n * 2 ^ (w + 1)
    let inputs := List.ofFn (fun a : Fin I =>
      table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
        (fun inputBit => a.val.testBit inputBit.val))
    inputs.getD (inpWire start p) false = table start p := by
  have hlt : inpWire start p < n * 2 ^ (w + 1) := inpWire_lt start p
  simp only [List.getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
  congr 1
  · apply Fin.ext
    dsimp only
    unfold inpWire
    have hdiv : (start.val * 2 ^ (w + 1) + patCode p) / 2 ^ (w + 1) = start.val := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos (w + 1)),
        Nat.div_eq_of_lt (patCode_lt p), Nat.add_zero]
    rw [hdiv, Nat.mod_eq_of_lt start.isLt]
  · funext o
    unfold inpWire
    have hbit : (start.val * 2 ^ (w + 1) + patCode p).testBit o.val = (patCode p).testBit o.val := by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
      have hpow : 2 ^ (w + 1) = 2 ^ (w + 1 - o.val) * 2 ^ o.val := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      have hmul : start.val * 2 ^ (w + 1) = 2 ^ o.val * (start.val * 2 ^ (w + 1 - o.val)) := by
        rw [hpow]; ring
      rw [hmul, Nat.mul_add_div (Nat.two_pow_pos o.val)]
      have heven : 2 ^ (w + 1 - o.val) % 2 = 0 := by
        have hsplit : 2 ^ (w + 1 - o.val) = 2 * 2 ^ (w + 1 - o.val - 1) := by
          conv_lhs => rw [show w + 1 - o.val = (w + 1 - o.val - 1) + 1 by omega]
          rw [Nat.pow_succ']
        rw [hsplit]; omega
      have hmod : (start.val * 2 ^ (w + 1 - o.val) + patCode p / 2 ^ o.val) % 2 =
          (patCode p / 2 ^ o.val) % 2 := by
        rw [Nat.add_mod, Nat.mul_mod, heven, Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.mod_mod]
      simp [hmod]
    rw [hbit, patCode_testBit]

def branchAxLoop {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t st : ℕ) (b : Bool) : List (Fin n) → Bool × (Fin n → Bool)
  | [] => (false, fun _ => false)
  | s :: rest =>
    let (anyF, mask) := branchAxLoop hn table t st b rest
    let fail := !(table s (windowPat hn t st b s))
    let pick := fail && !anyF
    (anyF || fail, fun v => mask v || (if touchBool w hn s v then pick else false))

lemma branchAxLoop_spec {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t st : ℕ) (b : Bool) (ss : List (Fin n)) :
    let (anyF, mask) := branchAxLoop hn table t st b ss
    (anyF = true ↔ ∃ s ∈ ss, table s (windowPat hn t st b s) = false) ∧
    (anyF = false → ∀ v, mask v = false) ∧
    (anyF = true → ∃ s ∈ ss, table s (windowPat hn t st b s) = false ∧
      ∀ v, mask v = touchBool w hn s v) := by
  induction ss with
  | nil =>
    simp [branchAxLoop]
  | cons s rest ih =>
    rcases ih with ⟨hiff, hfalse, htrue⟩
    simp only [branchAxLoop]
    set r := branchAxLoop hn table t st b rest
    cases hany : r.1
    · have h0 := hfalse hany
      cases htab : table s (windowPat hn t st b s)
      · refine ⟨by simp [htab], by simp, ?_⟩
        intro _
        refine ⟨s, List.mem_cons_self, htab, ?_⟩
        intro v
        simp [h0 v]
      · refine ⟨?_, ?_, by simp⟩
        · constructor
          · intro hc; simp at hc
          · rintro ⟨s', hs', htf⟩
            rcases List.mem_cons.mp hs' with rfl | hmem
            · rw [htab] at htf; exact Bool.noConfusion htf
            · have := hiff.mpr ⟨s', hmem, htf⟩
              rw [hany] at this; exact Bool.noConfusion this
        · intro _ v
          simp [h0 v]
    · rcases htrue hany with ⟨s0, hs0, htf0, hmask0⟩
      refine ⟨by simp; exact Or.inr ⟨s0, hs0, htf0⟩, by simp, ?_⟩
      intro _
      refine ⟨s0, List.mem_cons_of_mem s hs0, htf0, ?_⟩
      intro v
      simp [hmask0 v]

def combMask (hasPos hasNeg m0 m1 : Bool) : Bool :=
  ((!hasPos || hasNeg) && m0) || (hasPos && m1)

lemma combMask_cases (hasPos hasNeg m0 m1 : Bool) :
    combMask hasPos hasNeg m0 m1 =
      if !hasPos then m0 else if !hasNeg then m1 else (m0 || m1) := by
  cases hasPos <;> cases hasNeg <;> cases m0 <;> cases m1 <;> rfl

structure StageVal (n w : ℕ) where
  dead : Fin (4 ^ w) → Bool
  mask : Fin (4 ^ w) → Fin n → Bool

def dpFrom {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    ℕ → StageVal n w
  | 0 => ⟨fun _ => false, fun _ _ => false⟩
  | d + 1 =>
    let child := dpFrom hn table d
    let t := n - 1 - d
    let ss := startsAt n w t
    let stepSt := fun st : Fin (4 ^ w) =>
      let (af0, am0) := branchAxLoop hn table t st.val false ss
      let (af1, am1) := branchAxLoop hn table t st.val true ss
      let c0 : Fin (4 ^ w) := ⟨nextState w t st.val false, nextState_lt w t st.val false⟩
      let c1 : Fin (4 ^ w) := ⟨nextState w t st.val true, nextState_lt w t st.val true⟩
      let d0 := af0 || child.dead c0
      let d1 := af1 || child.dead c1
      let m0 := fun v : Fin n => am0 v || (!af0 && child.mask c0 v)
      let m1 := fun v : Fin n => am1 v || (!af1 && child.mask c1 v)
      let hp := if h : t < n then m0 ⟨t, h⟩ else false
      let hn' := if h : t < n then m1 ⟨t, h⟩ else false
      (d0 && d1, fun v : Fin n => if v.val = t then false else combMask hp hn' (m0 v) (m1 v))
    ⟨fun st => (stepSt st).1, fun st => (stepSt st).2⟩

def dpStage {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t : ℕ) : StageVal n w :=
  dpFrom hn table (n - t)

def slotIndex (w t st kind : ℕ) : ℕ :=
  (t * 4 ^ w + st) * 3 + kind

lemma slotIndex_lt {n w t st kind : ℕ} (ht : t < n) (hst : st < 4 ^ w) (hk : kind < 3) :
    slotIndex w t st kind < 3 * n * 4 ^ w := by
  unfold slotIndex
  have h1 : t * 4 ^ w + st + 1 ≤ n * 4 ^ w := by
    have hmul : (t + 1) * 4 ^ w ≤ n * 4 ^ w := Nat.mul_le_mul_right _ ht
    have hadd : (t + 1) * 4 ^ w = t * 4 ^ w + 4 ^ w := by ring
    omega
  have hmul3 : 3 * (n * 4 ^ w) = 3 * n * 4 ^ w := by ring
  omega

def semSlotLive {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t : Fin n) (st : Fin (4 ^ w)) (kind : Fin 3) : Bool :=
  let child := dpStage hn table (t.val + 1)
  let ss := startsAt n w t.val
  let (af0, am0) := branchAxLoop hn table t.val st.val false ss
  let (af1, am1) := branchAxLoop hn table t.val st.val true ss
  let c0 : Fin (4 ^ w) := ⟨nextState w t.val st.val false, nextState_lt w t.val st.val false⟩
  let c1 : Fin (4 ^ w) := ⟨nextState w t.val st.val true, nextState_lt w t.val st.val true⟩
  let d0 := af0 || child.dead c0
  let d1 := af1 || child.dead c1
  let hp := am0 t || (!af0 && child.mask c0 t)
  let hn' := am1 t || (!af1 && child.mask c1 t)
  match kind.val with
  | 0 => d0 && d1 && hp && hn'
  | 1 => af0
  | _ => af1

def semSlotMask {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t : Fin n) (st : Fin (4 ^ w)) (kind : Fin 3) : Fin n → Bool :=
  let child := dpStage hn table (t.val + 1)
  let ss := startsAt n w t.val
  let (af0, am0) := branchAxLoop hn table t.val st.val false ss
  let (af1, am1) := branchAxLoop hn table t.val st.val true ss
  let c0 : Fin (4 ^ w) := ⟨nextState w t.val st.val false, nextState_lt w t.val st.val false⟩
  let c1 : Fin (4 ^ w) := ⟨nextState w t.val st.val true, nextState_lt w t.val st.val true⟩
  let m0 := fun v : Fin n => am0 v || (!af0 && child.mask c0 v)
  let m1 := fun v : Fin n => am1 v || (!af1 && child.mask c1 v)
  let hp := m0 t
  let hn' := m1 t
  match kind.val with
  | 0 => fun v => if v.val = t.val then false else combMask hp hn' (m0 v) (m1 v)
  | 1 => am0
  | _ => am1

def slotPol {n w : ℕ} (t : Fin n) (st : Fin (4 ^ w)) (kind : Fin 3) (v : Fin n) : Bool :=
  match kind.val with
  | 0 => !(stVal w t.val st.val v.val)
  | 1 => !(extVal w t.val st.val false v.val)
  | _ => !(extVal w t.val st.val true v.val)

def clauseFromMask {n : ℕ} (mask : Fin n → Bool) (pol : Fin n → Bool) : Clause (Fin n) :=
  Finset.univ.filter (fun l : Literal (Fin n) => mask l.1 && (l.2 == pol l.1))

lemma mem_clauseFromMask {n : ℕ} (mask pol : Fin n → Bool) (v : Fin n) (b : Bool) :
    (v, b) ∈ clauseFromMask mask pol ↔ mask v = true ∧ b = pol v := by
  simp [clauseFromMask]

def decodeSlot {n w : ℕ} (_hn : 0 < n) (s : Fin (3 * n * 4 ^ w)) :
    Fin n × Fin (4 ^ w) × Fin 3 :=
  let q := s.val / 3
  let kind : Fin 3 := ⟨s.val % 3, Nat.mod_lt _ (by omega)⟩
  let hw : 0 < 4 ^ w := Nat.pos_of_ne_zero (by positivity)
  let t : Fin n := ⟨q / 4 ^ w, by
    have hs := s.isLt
    have hmul3 : 3 * n * 4 ^ w = 3 * (n * 4 ^ w) := by ring
    have hq : q < n * 4 ^ w := by omega
    exact (Nat.div_lt_iff_lt_mul hw).mpr hq⟩
  let st : Fin (4 ^ w) := ⟨q % 4 ^ w, Nat.mod_lt _ hw⟩
  (t, st, kind)

lemma decodeSlot_slotIndex {n w : ℕ} (hn : 0 < n) (t : Fin n) (st : Fin (4 ^ w)) (kind : Fin 3) :
    decodeSlot hn ⟨slotIndex w t.val st.val kind.val, slotIndex_lt t.isLt st.isLt kind.isLt⟩ =
      (t, st, kind) := by
  unfold decodeSlot slotIndex
  have hw : 0 < 4 ^ w := Nat.pos_of_ne_zero (by positivity)
  have hq : ((t.val * 4 ^ w + st.val) * 3 + kind.val) / 3 = t.val * 4 ^ w + st.val := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt kind.isLt, Nat.add_zero]
  have hk : ((t.val * 4 ^ w + st.val) * 3 + kind.val) % 3 = kind.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt kind.isLt]
  have ht : (t.val * 4 ^ w + st.val) / 4 ^ w = t.val := by
    rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt st.isLt, Nat.add_zero]
  have hst : (t.val * 4 ^ w + st.val) % 4 ^ w = st.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt st.isLt]
  refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
  · simp [hq, ht]
  · simp [hq, hst]
  · simp [hk]

def semLive {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (s : Fin (3 * n * 4 ^ w)) : Bool :=
  let (t, st, kind) := decodeSlot hn s
  semSlotLive hn table t st kind

def semMember {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (s : Fin (3 * n * 4 ^ w)) (l : Literal (Fin n)) : Bool :=
  let (t, st, kind) := decodeSlot hn s
  semSlotMask hn table t st kind l.1 && (l.2 == slotPol t st kind l.1)

def semClause {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (s : Fin (3 * n * 4 ^ w)) : Clause (Fin n) :=
  Finset.univ.filter (fun l => semMember hn table s l = true)

lemma semClause_eq_clauseFromMask {n w : ℕ} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (s : Fin (3 * n * 4 ^ w)) :
    let (t, st, kind) := decodeSlot hn s
    semClause hn table s = clauseFromMask (semSlotMask hn table t st kind) (slotPol t st kind) := by
  rfl

lemma semClause_slotIndex {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t : Fin n) (st : Fin (4 ^ w)) (kind : Fin 3) :
    semClause hn table ⟨slotIndex w t.val st.val kind.val, slotIndex_lt t.isLt st.isLt kind.isLt⟩ =
      clauseFromMask (semSlotMask hn table t st kind) (slotPol t st kind) := by
  unfold semClause semMember clauseFromMask
  rw [decodeSlot_slotIndex]

lemma card_clauseFromMask_le_active {n w : ℕ} (mask pol : Fin n → Bool) (t : ℕ)
    (hact : ∀ v : Fin n, mask v = true → isActive w t v.val) :
    (clauseFromMask mask pol).card ≤ 2 * w := by
  have hsub : (clauseFromMask mask pol).image Prod.fst ⊆
      (Finset.univ.filter (fun v : Fin n => v.val < w)) ∪
      (Finset.univ.filter (fun v : Fin n => t - w ≤ v.val ∧ v.val < t)) := by
    intro v hv
    rw [Finset.mem_image] at hv
    rcases hv with ⟨⟨v', b⟩, hmem, rfl⟩
    rw [mem_clauseFromMask] at hmem
    rcases hact v' hmem.1 with ⟨hlt, h1 | h2⟩
    · exact Finset.mem_union_left _ (by simp [h1])
    · exact Finset.mem_union_right _ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h2, hlt⟩)
  have hinj : Set.InjOn Prod.fst (clauseFromMask mask pol : Set (Literal (Fin n))) := by
    intro ⟨v1, b1⟩ h1 ⟨v2, b2⟩ h2 heq
    dsimp only at heq
    subst heq
    rw [Finset.mem_coe, mem_clauseFromMask] at h1 h2
    rw [h1.2, h2.2]
  have hcard1 : (clauseFromMask mask pol).card = ((clauseFromMask mask pol).image Prod.fst).card :=
    (Finset.card_image_of_injOn hinj).symm
  have h1 : (Finset.univ.filter (fun v : Fin n => v.val < w)).card ≤ w := by
    have hinj' : Set.InjOn Fin.val ((Finset.univ.filter (fun v : Fin n => v.val < w)) : Set (Fin n)) :=
      fun _ _ _ _ h => Fin.ext h
    rw [← Finset.card_image_of_injOn hinj']
    have hsub' : (Finset.univ.filter (fun v : Fin n => v.val < w)).image Fin.val ⊆ Finset.range w := by
      intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨v, hv, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact Finset.mem_range.mpr hv
    exact le_trans (Finset.card_le_card hsub') (by simp)
  have h2 : (Finset.univ.filter (fun v : Fin n => t - w ≤ v.val ∧ v.val < t)).card ≤ w := by
    let f : Fin n → ℕ := fun v => v.val - (t - w)
    have hinj' : Set.InjOn f
        ((Finset.univ.filter (fun v : Fin n => t - w ≤ v.val ∧ v.val < t)) : Set (Fin n)) := by
      intro v1 h1 v2 h2 heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      dsimp only [f] at heq
      exact Fin.ext (by omega)
    rw [← Finset.card_image_of_injOn hinj']
    have hsub' : (Finset.univ.filter (fun v : Fin n => t - w ≤ v.val ∧ v.val < t)).image f ⊆
        Finset.range w := by
      intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨v, hv, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact Finset.mem_range.mpr (by dsimp [f]; omega)
    exact le_trans (Finset.card_le_card hsub') (by simp)
  calc (clauseFromMask mask pol).card
      = ((clauseFromMask mask pol).image Prod.fst).card := hcard1
    _ ≤ ((Finset.univ.filter (fun v : Fin n => v.val < w)) ∪
          (Finset.univ.filter (fun v : Fin n => t - w ≤ v.val ∧ v.val < t))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun v : Fin n => v.val < w)).card +
          (Finset.univ.filter (fun v : Fin n => t - w ≤ v.val ∧ v.val < t)).card :=
        Finset.card_union_le _ _
    _ ≤ w + w := Nat.add_le_add h1 h2
    _ = 2 * w := by omega

lemma axClause_eq_image {n w : ℕ} (hn : 0 < n) (t st : ℕ) (b : Bool) (start : Fin n) :
    clauseFromMask (touchBool w hn start) (fun v => !(extVal w t st b v.val)) =
      Finset.univ.image (fun o : Fin (w + 1) => (posOf hn start o, !(windowPat hn t st b start o))) := by
  ext ⟨v, pol⟩
  rw [mem_clauseFromMask, Finset.mem_image, touchBool_eq_true_iff]
  constructor
  · rintro ⟨⟨o, ho⟩, rfl⟩
    refine ⟨o, Finset.mem_univ o, ?_⟩
    simp [windowPat, ho]
  · rintro ⟨o, _, heq⟩
    have hv : posOf hn start o = v := congrArg Prod.fst heq
    have hp : (!windowPat hn t st b start o) = pol := congrArg Prod.snd heq
    refine ⟨⟨o, hv⟩, ?_⟩
    rw [← hp, windowPat, hv]

lemma axClause_card_le {n w : ℕ} (hn : 0 < n) (t st : ℕ) (b : Bool) (start : Fin n) :
    (clauseFromMask (touchBool w hn start) (fun v => !(extVal w t st b v.val))).card ≤ 2 * w + 1 := by
  rw [axClause_eq_image]
  calc (Finset.univ.image (fun o : Fin (w + 1) => (posOf hn start o, !(windowPat hn t st b start o)))).card
      ≤ (Finset.univ : Finset (Fin (w + 1))).card := Finset.card_image_le
    _ = w + 1 := by simp
    _ ≤ 2 * w + 1 := by omega

lemma dpStage_eq_step {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t : Fin n) :
    let child := dpStage hn table (t.val + 1)
    let ss := startsAt n w t.val
    ∀ st : Fin (4 ^ w),
      let (af0, am0) := branchAxLoop hn table t.val st.val false ss
      let (af1, am1) := branchAxLoop hn table t.val st.val true ss
      let c0 : Fin (4 ^ w) := ⟨nextState w t.val st.val false, nextState_lt w t.val st.val false⟩
      let c1 : Fin (4 ^ w) := ⟨nextState w t.val st.val true, nextState_lt w t.val st.val true⟩
      let d0 := af0 || child.dead c0
      let d1 := af1 || child.dead c1
      let m0 := fun v : Fin n => am0 v || (!af0 && child.mask c0 v)
      let m1 := fun v : Fin n => am1 v || (!af1 && child.mask c1 v)
      (dpStage hn table t.val).dead st = (d0 && d1) ∧
      ∀ v : Fin n, (dpStage hn table t.val).mask st v =
        if v.val = t.val then false else combMask (m0 t) (m1 t) (m0 v) (m1 v) := by
  dsimp only
  intro st
  have hsub : n - t.val = (n - (t.val + 1)) + 1 := by omega
  have hteq : n - 1 - (n - (t.val + 1)) = t.val := by omega
  unfold dpStage
  rw [hsub]
  simp only [dpFrom, hteq, t.isLt, ↓reduceDIte, and_self, implies_true]

lemma isResolvent_of_combMask {n w : ℕ} (t : Fin n) (st : Fin (4 ^ w))
    (m0 m1 : Fin n → Bool)
    (hact0 : ∀ v : Fin n, m0 v = true → v = t ∨ isActive w t.val v.val)
    (hact1 : ∀ v : Fin n, m1 v = true → v = t ∨ isActive w t.val v.val)
    (hp : m0 t = true) (hn' : m1 t = true) :
    IsResolvent
      (clauseFromMask m0 (fun v => !(extVal w t.val st.val false v.val)))
      (clauseFromMask m1 (fun v => !(extVal w t.val st.val true v.val)))
      (clauseFromMask (fun v => if v.val = t.val then false else combMask true true (m0 v) (m1 v))
        (fun v => !(stVal w t.val st.val v.val))) := by
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [mem_clauseFromMask]; exact ⟨hp, by simp [extVal]⟩
  · rw [mem_clauseFromMask]; exact ⟨hn', by simp [extVal]⟩
  · ext ⟨v, pol⟩
    simp only [Finset.mem_union, Finset.mem_erase, mem_clauseFromMask, combMask,
      Bool.not_true, Bool.false_or, Bool.true_and]
    by_cases hvt : v = t
    · subst hvt
      cases pol <;> simp [extVal]
    · have hne : v.val ≠ t.val := fun h => hvt (Fin.ext h)
      simp only [hne, ↓reduceIte, extVal, Bool.or_eq_true, ne_eq, Prod.mk.injEq, hvt,
        false_and, not_false_eq_true, true_and]
      tauto

lemma dpStage_sound_and_witness {n w : ℕ} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    let F : Set (Clause (Fin n)) :=
      {D | ∃ (i : Fin n) (p : Fin (w + 1) → Bool), table i p = false ∧
        D = Finset.univ.image (fun o : Fin (w + 1) => (posOf hn i o, !(p o)))}
    ∀ d ≤ n,
      let t := n - d
      (∀ st : Fin (4 ^ w),
        (∀ v : Fin n, (dpStage hn table t).mask st v = true → isActive w t v.val) ∧
        ((dpStage hn table t).dead st = true →
          ∃ s : Fin (3 * n * 4 ^ w),
            t * 4 ^ w * 3 ≤ s.val ∧
            semLive hn table s = true ∧
            semClause hn table s =
              clauseFromMask ((dpStage hn table t).mask st) (fun v => !(stVal w t st.val v.val)))) ∧
      (∀ s : Fin (3 * n * 4 ^ w), t * 4 ^ w * 3 ≤ s.val → semLive hn table s = true →
        (semClause hn table s).card ≤ 2 * w + 1 ∧
        (semClause hn table s ∈ F ∨
          ∃ s1 s2 : Fin (3 * n * 4 ^ w), s.val < s1.val ∧ s.val < s2.val ∧
            semLive hn table s1 = true ∧ semLive hn table s2 = true ∧
            IsResolvent (semClause hn table s1) (semClause hn table s2) (semClause hn table s))) := by
  intro F d hd
  induction d with
  | zero =>
    have htn : n - 0 = n := Nat.sub_zero n
    rw [htn]
    refine ⟨?_, ?_⟩
    · intro st
      simp [dpStage, dpFrom]
    · intro s hs
      have hlt := s.isLt
      have hmul : n * 4 ^ w * 3 = 3 * n * 4 ^ w := by ring
      omega
  | succ d ih =>
    rcases ih (by omega) with ⟨ihSt, ihSlot⟩
    set t_val := n - (d + 1)
    have htlt : t_val < n := by omega
    let t : Fin n := ⟨t_val, htlt⟩
    have htp1 : n - d = t_val + 1 := by omega
    rw [htp1] at ihSt ihSlot
    have hstep := dpStage_eq_step hn table t
    have hbranch : ∀ (st : Fin (4 ^ w)) (b : Bool),
        let ss := startsAt n w t.val
        let (af, am) := branchAxLoop hn table t.val st.val b ss
        let c : Fin (4 ^ w) := ⟨nextState w t.val st.val b, nextState_lt w t.val st.val b⟩
        let db := af || (dpStage hn table (t.val + 1)).dead c
        let mb := fun v : Fin n => am v || (!af && (dpStage hn table (t.val + 1)).mask c v)
        (∀ v : Fin n, mb v = true → v = t ∨ isActive w t.val v.val) ∧
        (af = true →
          clauseFromMask am (fun v => !(extVal w t.val st.val b v.val)) ∈ F ∧
          (clauseFromMask am (fun v => !(extVal w t.val st.val b v.val))).card ≤ 2 * w + 1) ∧
        (db = true →
          ∃ s : Fin (3 * n * 4 ^ w),
            slotIndex w t.val st.val 0 < s.val ∧
            semLive hn table s = true ∧
            semClause hn table s = clauseFromMask mb (fun v => !(extVal w t.val st.val b v.val))) := by
      intro st b
      set ss := startsAt n w t.val
      rcases branchAxLoop_spec hn table t.val st.val b ss with ⟨hiff, hfalse, htrue⟩
      set ar := branchAxLoop hn table t.val st.val b ss
      set c : Fin (4 ^ w) := ⟨nextState w t.val st.val b, nextState_lt w t.val st.val b⟩
      rcases ihSt c with ⟨hactC, hwitC⟩
      refine ⟨?_, ?_, ?_⟩
      · intro v hv
        cases haf : ar.1
        · change ar.2 v || (!ar.1 && (dpStage hn table (t_val + 1)).mask c v) = true at hv
          rw [haf, hfalse haf v] at hv
          simp only [Bool.false_or, Bool.not_false, Bool.true_and] at hv
          have ha1 := hactC v hv
          by_cases hvt : v = t
          · exact Or.inl hvt
          · exact Or.inr (active_succ_subset ha1 (fun h => hvt (Fin.ext h)))
        · change (ar.2 v || ((!ar.1) && (dpStage hn table (t_val + 1)).mask c v)) = true at hv
          rw [haf] at hv
          rcases htrue haf with ⟨s0, hs0, _, hmask0⟩
          rw [hmask0 v] at hv
          simp only [Bool.not_true, Bool.false_and, Bool.or_false, touchBool_eq_true_iff] at hv
          rcases hv with ⟨o, ho⟩
          have hmax : maxPos n w s0 = t.val := by
            simp only [ss, startsAt, List.mem_filter, List.mem_finRange, true_and,
              decide_eq_true_eq] at hs0
            exact hs0
          have hle := posOf_le_maxPos hn s0 o
          rw [ho, hmax] at hle
          by_cases hvt : v = t
          · exact Or.inl hvt
          · have hlt : v.val < maxPos n w s0 := by
              have hne : v.val ≠ t.val := fun h => hvt (Fin.ext h)
              omega
            rw [← ho] at hlt
            have ha := posOf_active_of_lt_maxPos hn s0 o hlt
            rw [ho, hmax] at ha
            exact Or.inr ha
      · intro haf
        rcases htrue haf with ⟨s0, _, htf0, hmask0⟩
        have hmeq : ar.2 = touchBool w hn s0 := funext hmask0
        rw [hmeq]
        refine ⟨?_, axClause_card_le hn t.val st.val b s0⟩
        rw [axClause_eq_image]
        exact ⟨s0, windowPat hn t.val st.val b s0, htf0, rfl⟩
      · intro hdb
        cases haf : ar.1
        · rw [haf] at hdb
          simp only [Bool.false_or] at hdb
          rcases hwitC hdb with ⟨s, hs_ge, hslive, hscl⟩
          refine ⟨s, ?_, hslive, ?_⟩
          · unfold slotIndex
            dsimp only [t]
            have h1 : t_val * 4 ^ w + st.val + 1 ≤ (t_val + 1) * 4 ^ w := by
              have hmul : (t_val + 1) * 4 ^ w = t_val * 4 ^ w + 4 ^ w := by ring
              omega
            omega
          · rw [hscl]
            ext ⟨v, pol⟩
            change (v, pol) ∈ clauseFromMask ((dpStage hn table (t_val + 1)).mask c) _ ↔
              (v, pol) ∈ clauseFromMask (fun v => ar.2 v || (!false && (dpStage hn table (t_val + 1)).mask c v)) _
            simp only [mem_clauseFromMask, hfalse haf v, Bool.not_false, Bool.true_and,
              Bool.false_or]
            constructor
            · rintro ⟨hm, rfl⟩
              refine ⟨hm, ?_⟩
              have ha := hactC v hm
              congr 1
              exact stVal_nextState ha
            · rintro ⟨hm, rfl⟩
              refine ⟨hm, ?_⟩
              have ha := hactC v hm
              congr 1
              exact (stVal_nextState ha).symm
        · let kind : Fin 3 := if b then ⟨2, by omega⟩ else ⟨1, by omega⟩
          let s : Fin (3 * n * 4 ^ w) :=
            ⟨slotIndex w t.val st.val kind.val, slotIndex_lt t.isLt st.isLt kind.isLt⟩
          refine ⟨s, ?_, ?_, ?_⟩
          · unfold s slotIndex kind
            cases b <;> dsimp <;> omega
          · unfold semLive
            rw [decodeSlot_slotIndex]
            cases b <;> simpa [kind, semSlotLive, ss] using haf
          · dsimp only [s]
            rw [semClause_slotIndex]
            change clauseFromMask (semSlotMask hn table t st kind) (slotPol t st kind) =
              clauseFromMask (fun v => ar.2 v || (!true && (dpStage hn table (t.val + 1)).mask c v)) _
            cases b
            · have hpol : slotPol t st kind = fun v => !(extVal w t.val st.val false v.val) := by
                funext v; simp [slotPol, kind]
              rw [hpol]
              simp only [kind, semSlotMask, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
                Bool.false_and, Bool.or_false]
              rfl
            · have hpol : slotPol t st kind = fun v => !(extVal w t.val st.val true v.val) := by
                funext v; simp [slotPol, kind]
              rw [hpol]
              simp only [kind, semSlotMask, ↓reduceIte, Bool.not_true,
                Bool.false_and, Bool.or_false]
              rfl
    refine ⟨?_, ?_⟩
    · intro st
      rcases hstep st with ⟨hdeadEq, hmaskEq⟩
      rcases hbranch st false with ⟨hact0, _, hwit0⟩
      rcases hbranch st true with ⟨hact1, _, hwit1⟩
      refine ⟨?_, ?_⟩
      · intro v hv
        rw [hmaskEq v] at hv
        by_cases hvt : v.val = t.val
        · simp [hvt] at hv
        · rw [ite_eq_right_iff.mpr (fun h => absurd h hvt)] at hv
          have hvt' : v ≠ t := fun h => hvt (congrArg Fin.val h)
          rw [combMask_cases] at hv
          split_ifs at hv
          · rcases hact0 v hv with rfl | ha
            · exact absurd rfl hvt'
            · exact ha
          · rcases hact1 v hv with rfl | ha
            · exact absurd rfl hvt'
            · exact ha
          · rcases Bool.or_eq_true _ _ |>.mp hv with h0 | h1
            · rcases hact0 v h0 with rfl | ha
              · exact absurd rfl hvt'
              · exact ha
            · rcases hact1 v h1 with rfl | ha
              · exact absurd rfl hvt'
              · exact ha
      · intro hdead
        rw [hdeadEq, Bool.and_eq_true] at hdead
        rcases hdead with ⟨hd0, hd1⟩
        set ss := startsAt n w t.val
        set ar0 := branchAxLoop hn table t.val st.val false ss
        set ar1 := branchAxLoop hn table t.val st.val true ss
        set c0 : Fin (4 ^ w) := ⟨nextState w t.val st.val false, nextState_lt w t.val st.val false⟩
        set c1 : Fin (4 ^ w) := ⟨nextState w t.val st.val true, nextState_lt w t.val st.val true⟩
        set m0 := fun v : Fin n => ar0.2 v || (!ar0.1 && (dpStage hn table (t.val + 1)).mask c0 v)
        set m1 := fun v : Fin n => ar1.2 v || (!ar1.1 && (dpStage hn table (t.val + 1)).mask c1 v)
        by_cases hhp : m0 t = false
        · rcases hwit0 hd0 with ⟨s, hsgt, hslive, hscl⟩
          refine ⟨s, ?_, hslive, ?_⟩
          · unfold slotIndex at hsgt; dsimp only [t] at hsgt; omega
          · rw [hscl]
            ext ⟨v, pol⟩
            have hm_eq : (dpStage hn table t_val).mask st v =
                if v.val = t.val then false else combMask (m0 t) (m1 t) (m0 v) (m1 v) := hmaskEq v
            rw [mem_clauseFromMask, mem_clauseFromMask, hm_eq, combMask_cases, hhp]
            by_cases hvt : v.val = t.val
            · have hvteq : v = t := Fin.ext hvt
              subst hvteq
              simp only [↓reduceIte, Bool.false_eq_true, false_and, iff_false, not_and]
              intro hm0
              change m0 t = true at hm0
              rw [hhp] at hm0; exact Bool.noConfusion hm0
            · simp only [hvt, Bool.not_false, ↓reduceIte, extVal]
              rfl
        · have hhpT : m0 t = true := by
            cases h : m0 t
            · exact absurd h hhp
            · rfl
          by_cases hhn : m1 t = false
          · rcases hwit1 hd1 with ⟨s, hsgt, hslive, hscl⟩
            refine ⟨s, ?_, hslive, ?_⟩
            · unfold slotIndex at hsgt; dsimp only [t] at hsgt; omega
            · rw [hscl]
              ext ⟨v, pol⟩
              have hm_eq : (dpStage hn table t_val).mask st v =
                  if v.val = t.val then false else combMask (m0 t) (m1 t) (m0 v) (m1 v) := hmaskEq v
              rw [mem_clauseFromMask, mem_clauseFromMask, hm_eq, combMask_cases, hhpT, hhn]
              by_cases hvt : v.val = t.val
              · have hvteq : v = t := Fin.ext hvt
                subst hvteq
                simp only [↓reduceIte, Bool.false_eq_true, false_and, iff_false, not_and]
                intro hm1
                change m1 t = true at hm1
                rw [hhn] at hm1; exact Bool.noConfusion hm1
              · simp only [hvt, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, extVal]
                rfl
          · have hhnT : m1 t = true := by
              cases h : m1 t
              · exact absurd h hhn
              · rfl
            let k0 : Fin 3 := ⟨0, by omega⟩
            let s : Fin (3 * n * 4 ^ w) :=
              ⟨slotIndex w t.val st.val k0.val, slotIndex_lt t.isLt st.isLt k0.isLt⟩
            refine ⟨s, ?_, ?_, ?_⟩
            · dsimp only [s, t, k0]; unfold slotIndex; omega
            · dsimp only [s, semLive]
              rw [decodeSlot_slotIndex hn t st k0]
              simp only [semSlotLive, k0, Bool.and_eq_true]
              exact ⟨⟨⟨hd0, hd1⟩, hhpT⟩, hhnT⟩
            · dsimp only [s]
              rw [semClause_slotIndex hn table t st k0]
              have hpol0 : slotPol t st k0 = fun v => !(stVal w t_val st.val v.val) := by
                funext v; simp [slotPol, k0, t]
              rw [hpol0]
              congr 1
              funext v
              exact (hmaskEq v).symm
    · intro s hs_ge hslive
      by_cases hnext : (t_val + 1) * 4 ^ w * 3 ≤ s.val
      · exact ihSlot s hnext hslive
      · rcases hd_eq : decodeSlot hn s with ⟨t', st', kind'⟩
        have hst_eq : s.val = slotIndex w t'.val st'.val kind'.val := by
          unfold decodeSlot at hd_eq
          have h1 : t'.val = (s.val / 3) / 4 ^ w := by
            have := congrArg (fun x => x.1.val) hd_eq; simpa using this.symm
          have h2 : st'.val = (s.val / 3) % 4 ^ w := by
            have := congrArg (fun x => x.2.1.val) hd_eq; simpa using this.symm
          have h3 : kind'.val = s.val % 3 := by
            have := congrArg (fun x => x.2.2.val) hd_eq; simpa using this.symm
          unfold slotIndex
          have hdiv1 : (s.val / 3) / 4 ^ w * 4 ^ w + (s.val / 3) % 4 ^ w = s.val / 3 := by
            rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
          have hdiv2 : (s.val / 3) * 3 + s.val % 3 = s.val := by
            rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
          rw [h1, h2, h3, hdiv1, hdiv2]
        have ht'_eq : t' = t := by
          apply Fin.ext
          have hw : 0 < 4 ^ w := Nat.pos_of_ne_zero (by positivity)
          have hst_val : s.val = (t'.val * 4 ^ w + st'.val) * 3 + kind'.val := hst_eq
          have hlo : t_val * 4 ^ w * 3 ≤ (t'.val * 4 ^ w + st'.val) * 3 + kind'.val := by
            rw [← hst_val]; exact hs_ge
          have hhi : (t'.val * 4 ^ w + st'.val) * 3 + kind'.val < (t_val + 1) * 4 ^ w * 3 := by
            rw [← hst_val]; omega
          have hmul1 : t_val * 4 ^ w ≤ t'.val * 4 ^ w + st'.val := by omega
          have hmul2 : t'.val * 4 ^ w + st'.val < (t_val + 1) * 4 ^ w := by omega
          have hle1 : t_val ≤ t'.val := by
            by_contra hlt
            have h1 : (t'.val + 1) * 4 ^ w ≤ t_val * 4 ^ w := Nat.mul_le_mul_right _ (by omega)
            have h2 : (t'.val + 1) * 4 ^ w = t'.val * 4 ^ w + 4 ^ w := by ring
            have := st'.isLt
            omega
          have hle2 : t'.val ≤ t_val := by
            by_contra hgt
            have h1 : (t_val + 1) * 4 ^ w ≤ t'.val * 4 ^ w := Nat.mul_le_mul_right _ (by omega)
            omega
          change t'.val = t_val
          omega
        subst ht'_eq
        have hslive' : semSlotLive hn table t st' kind' = true := by
          simpa [semLive, hd_eq] using hslive
        have hcl_eq : semClause hn table s =
            clauseFromMask (semSlotMask hn table t st' kind') (slotPol t st' kind') := by
          have := semClause_eq_clauseFromMask hn table s
          simpa [hd_eq] using this
        rw [hcl_eq]
        rcases hbranch st' false with ⟨hact0, hax0, hwit0⟩
        rcases hbranch st' true with ⟨hact1, hax1, hwit1⟩
        have hkv : kind'.val = 0 ∨ kind'.val = 1 ∨ kind'.val = 2 := by omega
        rcases hkv with hk0 | hk1 | hk2
        · simp only [semSlotLive, hk0, Bool.and_eq_true] at hslive'
          rcases hslive' with ⟨⟨⟨hd0, hd1⟩, hhp⟩, hhn⟩
          rcases hwit0 hd0 with ⟨s1, hs1gt, hs1live, hs1cl⟩
          rcases hwit1 hd1 with ⟨s2, hs2gt, hs2live, hs2cl⟩
          have hcard : (clauseFromMask (semSlotMask hn table t st' kind') (slotPol t st' kind')).card ≤
              2 * w + 1 := by
            have hle := card_clauseFromMask_le_active (semSlotMask hn table t st' kind')
              (slotPol t st' kind') t.val (by
                intro v hv
                simp only [semSlotMask, hk0] at hv
                by_cases hvt : v.val = t.val
                · simp [hvt] at hv
                · rw [ite_eq_right_iff.mpr (fun h => absurd h hvt)] at hv
                  have hvt' : v ≠ t := fun h => hvt (congrArg Fin.val h)
                  rw [combMask_cases] at hv
                  split_ifs at hv
                  · exact (hact0 v hv).resolve_left hvt'
                  · exact (hact1 v hv).resolve_left hvt'
                  · rcases Bool.or_eq_true _ _ |>.mp hv with h0 | h1
                    · exact (hact0 v h0).resolve_left hvt'
                    · exact (hact1 v h1).resolve_left hvt')
            omega
          refine ⟨hcard, Or.inr ⟨s1, s2, ?_, ?_, hs1live, hs2live, ?_⟩⟩
          · rw [hst_eq, hk0]; exact hs1gt
          · rw [hst_eq, hk0]; exact hs2gt
          · rw [hs1cl, hs2cl]
            have hpol : slotPol t st' kind' = fun v => !(stVal w t.val st'.val v.val) := by
              funext v; simp [slotPol, hk0]
            rw [hpol]
            simp only [semSlotMask, hk0, hhp, hhn]
            exact isResolvent_of_combMask t st' _ _ hact0 hact1 hhp hhn
        · simp only [semSlotLive, hk1] at hslive'
          rcases hax0 hslive' with ⟨hmem, hcard⟩
          have hpol : slotPol t st' kind' = fun v => !(extVal w t.val st'.val false v.val) := by
            funext v; simp [slotPol, hk1]
          rw [hpol]
          simp only [semSlotMask, hk1]
          exact ⟨hcard, Or.inl hmem⟩
        · simp only [semSlotLive, hk2] at hslive'
          rcases hax1 hslive' with ⟨hmem, hcard⟩
          have hpol : slotPol t st' kind' = fun v => !(extVal w t.val st'.val true v.val) := by
            funext v; simp [slotPol, hk2]
          rw [hpol]
          simp only [semSlotMask, hk2]
          exact ⟨hcard, Or.inl hmem⟩

lemma isDerivation_of_suffix {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {α : Type} (l : List α) (f : α → Clause V) (p : α → Bool)
    (h : ∀ (a : α) (rest : List α), (a :: rest) <:+ l → p a = true →
      f a ∈ F ∨ ∃ b ∈ rest, ∃ c ∈ rest, p b = true ∧ p c = true ∧ IsResolvent (f b) (f c) (f a)) :
    IsDerivation F ((l.filter p).map f) := by
  induction l with
  | nil => exact IsDerivation.nil
  | cons a rest ih =>
    have ih' : IsDerivation F ((rest.filter p).map f) :=
      ih (fun x r hsuf hp => h x r (hsuf.trans (List.suffix_cons a rest)) hp)
    cases hpa : p a
    · simp only [List.filter_cons, hpa, Bool.false_eq_true, ↓reduceIte]
      exact ih'
    · simp only [List.filter_cons, hpa, ↓reduceIte, List.map_cons]
      rcases h a rest List.suffix_rfl hpa with hax | ⟨b, hb, c, hc, hpb, hpc, hres⟩
      · exact IsDerivation.ax ih' hax
      · have hfb : f b ∈ (rest.filter p).map f :=
          List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, hpb⟩, rfl⟩
        have hfc : f c ∈ (rest.filter p).map f :=
          List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, hpc⟩, rfl⟩
        exact IsDerivation.res ih' hfb hfc hres

lemma mem_suffix_finRange_of_lt {S : ℕ} {s s' : Fin S} {rest : List (Fin S)}
    (hsuf : (s :: rest) <:+ List.finRange S) (hlt : s.val < s'.val) : s' ∈ rest := by
  rcases hsuf with ⟨pre, hpre⟩
  have hmem : s' ∈ List.finRange S := List.mem_finRange s'
  rw [← hpre, List.mem_append, List.mem_cons] at hmem
  rcases hmem with hInPre | rfl | hInRest
  · exfalso
    have hsorted : (List.finRange S).Pairwise (fun a b : Fin S => a.val < b.val) := by
      rw [List.finRange_eq_pmap_range]
      apply List.Pairwise.pmap (R := (· < ·))
      · exact List.pairwise_lt_range
      · intro _ _ _ _ h; exact h
    rw [← hpre, List.pairwise_append] at hsorted
    have hlt' := hsorted.2.2 s' hInPre s List.mem_cons_self
    omega
  · omega
  · exact hInRest

lemma resolvent_sound {V : Type} [DecidableEq V] {a : V → Bool} {C D R : Clause V}
    (hC : ClauseSat a C) (hD : ClauseSat a D) (hR : IsResolvent C D R) : ClauseSat a R := by
  rcases hR with ⟨v, hvC, hvD, rfl⟩
  cases hav : a v
  · rcases hC with ⟨⟨u, b⟩, huC, hub⟩
    by_cases huv : (u, b) = (v, true)
    · have hu : u = v := congrArg Prod.fst huv
      have hb : b = true := congrArg Prod.snd huv
      subst hu; subst hb
      rw [hav] at hub; exact Bool.noConfusion hub
    · exact ⟨(u, b), Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨huv, huC⟩), hub⟩
  · rcases hD with ⟨⟨u, b⟩, huD, hub⟩
    by_cases huv : (u, b) = (v, false)
    · have hu : u = v := congrArg Prod.fst huv
      have hb : b = false := congrArg Prod.snd huv
      subst hu; subst hb
      rw [hav] at hub; exact Bool.noConfusion hub
    · exact ⟨(u, b), Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨huv, huD⟩), hub⟩

lemma derivation_sound {V : Type} [DecidableEq V] {F : Set (Clause V)} {π : List (Clause V)}
    {a : V → Bool} (hder : IsDerivation F π) (hsat : Satisfies a F) :
    ∀ C ∈ π, ClauseSat a C := by
  induction hder with
  | nil => intro _ h; simp at h
  | ax _ hmem ih =>
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hrest
    · exact hsat C hmem
    · exact ih C hrest
  | res _ h1 h2 hres ih =>
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hrest
    · exact resolvent_sound (ih _ h1) (ih _ h2) hres
    · exact ih C hrest

lemma refutation_unsat {V : Type} [DecidableEq V] {F : Set (Clause V)} {π : List (Clause V)}
    (href : IsRefutation F π) : ¬ Satisfiable F := by
  rintro ⟨a, ha⟩
  rcases derivation_sound href.1 ha ∅ href.2 with ⟨l, hl, _⟩
  simp at hl

lemma dpDead_zero_false_sat {n w : ℕ} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (h0 : (dpStage hn table 0).dead ⟨0, Nat.pos_of_ne_zero (by positivity)⟩ = false) :
    Satisfiable {D | ∃ (i : Fin n) (p : Fin (w + 1) → Bool), table i p = false ∧
      D = Finset.univ.image (fun o : Fin (w + 1) => (posOf hn i o, !(p o)))} := by
  have hbuild : ∀ t ≤ n,
      ∃ (a : Fin n → Bool) (st : Fin (4 ^ w)),
        (dpStage hn table t).dead st = false ∧
        (∀ v : Fin n, isActive w t v.val → stVal w t st.val v.val = a v) ∧
        (∀ start : Fin n, maxPos n w start < t →
          table start (fun o => a (posOf hn start o)) = true) := by
    intro t ht
    induction t with
    | zero =>
      exact ⟨fun _ => false, ⟨0, Nat.pos_of_ne_zero (by positivity)⟩, h0,
        fun _ h => by rcases h with ⟨h1, _⟩; omega, fun _ h => by omega⟩
    | succ t ih =>
      rcases ih (by omega) with ⟨a, st, hdead, hact, hok⟩
      let tf : Fin n := ⟨t, by omega⟩
      have hstep := (dpStage_eq_step hn table tf st).1
      rw [hdead] at hstep
      set ss := startsAt n w t
      set af0 := (branchAxLoop hn table t st.val false ss).1
      set af1 := (branchAxLoop hn table t st.val true ss).1
      set c0 : Fin (4 ^ w) := ⟨nextState w t st.val false, nextState_lt w t st.val false⟩
      set c1 : Fin (4 ^ w) := ⟨nextState w t st.val true, nextState_lt w t st.val true⟩
      have hbr : ∃ b : Bool,
          (branchAxLoop hn table t st.val b ss).1 = false ∧
          (dpStage hn table (t + 1)).dead ⟨nextState w t st.val b, nextState_lt w t st.val b⟩ = false := by
        cases h0' : af0 || (dpStage hn table (t + 1)).dead c0
        · rw [Bool.or_eq_false_iff] at h0'
          exact ⟨false, h0'.1, h0'.2⟩
        · have h1' : (af1 || (dpStage hn table (t + 1)).dead c1) = false := by
            have hstep' : false = ((af0 || (dpStage hn table (t + 1)).dead c0) &&
                (af1 || (dpStage hn table (t + 1)).dead c1)) := hstep
            rw [h0', Bool.true_and] at hstep'
            exact hstep'.symm
          rw [Bool.or_eq_false_iff] at h1'
          exact ⟨true, h1'.1, h1'.2⟩
      rcases hbr with ⟨b, haf, hcd⟩
      let a' : Fin n → Bool := fun v => if v.val = t then b else a v
      refine ⟨a', ⟨nextState w t st.val b, nextState_lt w t st.val b⟩, hcd, ?_, ?_⟩
      · intro v hv
        rw [stVal_nextState hv]
        by_cases hvt : v.val = t
        · simp [a', hvt]
        · simp only [a', hvt, ↓reduceIte]
          exact hact v (active_succ_subset hv hvt)
      · intro start hmax
        by_cases hlt : maxPos n w start < t
        · have heq : (fun o : Fin (w + 1) => a' (posOf hn start o)) =
              (fun o : Fin (w + 1) => a (posOf hn start o)) := by
            funext o
            have hle := posOf_le_maxPos hn start o
            simp [a', show (posOf hn start o).val ≠ t by omega]
          rw [heq]
          exact hok start hlt
        · have hmeq : maxPos n w start = t := by omega
          have hmem : start ∈ ss := by
            simp [ss, startsAt, hmeq]
          have hpass : table start (windowPat hn t st.val b start) = true := by
            by_contra hnt
            have hff : table start (windowPat hn t st.val b start) = false := by
              cases h : table start (windowPat hn t st.val b start)
              · rfl
              · exact absurd h hnt
            have := (branchAxLoop_spec hn table t st.val b ss).1.mpr ⟨start, hmem, hff⟩
            rw [haf] at this; exact Bool.noConfusion this
          have hpat : (fun o : Fin (w + 1) => a' (posOf hn start o)) = windowPat hn t st.val b start := by
            funext o
            unfold windowPat extVal
            by_cases hvt : (posOf hn start o).val = t
            · simp [a', hvt]
            · simp only [a', hvt, ↓reduceIte]
              have hle := posOf_le_maxPos hn start o
              have hlt' : (posOf hn start o).val < maxPos n w start := by omega
              have ha := posOf_active_of_lt_maxPos hn start o hlt'
              rw [hmeq] at ha
              exact (hact (posOf hn start o) ha).symm
          rw [hpat]
          exact hpass
  rcases hbuild n le_rfl with ⟨a, _, _, _, hok⟩
  refine ⟨a, ?_⟩
  rintro D ⟨start, p, htf, rfl⟩
  have htr : table start (fun o => a (posOf hn start o)) = true :=
    hok start (maxPos_lt hn start)
  have hne : ∃ o : Fin (w + 1), a (posOf hn start o) ≠ p o := by
    by_contra hall
    push Not at hall
    have heq : (fun o => a (posOf hn start o)) = p := funext hall
    rw [heq, htf] at htr
    exact Bool.noConfusion htr
  rcases hne with ⟨o, ho⟩
  refine ⟨(posOf hn start o, !(p o)), Finset.mem_image.mpr ⟨o, Finset.mem_univ o, rfl⟩, ?_⟩
  dsimp only
  cases ha : a (posOf hn start o) <;> cases hp : p o <;> simp_all

def wireStep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def wireVal (gs : List Gate) (x : List Bool) (w : ℕ) : Bool :=
  (gs.foldl wireStep x).getD w false

def Valid (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j)

def Extends (gs1 gs2 : List Gate) : Prop :=
  ∃ d, gs2 = gs1 ++ d

lemma extends_rfl (gs : List Gate) : Extends gs gs := ⟨[], by simp⟩

lemma extends_trans {a b c : List Gate} (h1 : Extends a b) (h2 : Extends b c) : Extends a c := by
  rcases h1 with ⟨d1, rfl⟩
  rcases h2 with ⟨d2, rfl⟩
  exact ⟨d1 ++ d2, by simp [List.append_assoc]⟩

lemma extends_len {a b : List Gate} (h : Extends a b) : a.length ≤ b.length := by
  rcases h with ⟨d, rfl⟩
  simp

lemma foldl_wireStep_len (gs : List Gate) (x : List Bool) :
    (gs.foldl wireStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, wireStep, List.length_append, List.length_nil]
    omega

lemma getD_append_left {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_right {α : Type} (l r : List α) (i : ℕ) (d : α) (h : l.length ≤ i) :
    (l ++ r).getD i d = r.getD (i - l.length) d := by
  simp [List.getD, List.getElem?_append_right h]

lemma foldl_wireStep_getD_lt (gs : List Gate) (base : List Bool) (w : ℕ) (hw : w < base.length) :
    (gs.foldl wireStep base).getD w false = base.getD w false := by
  induction gs generalizing base with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hw' : w < (wireStep base g).length := by simp [wireStep]; omega
    rw [ih (wireStep base g) hw']
    exact getD_append_left base _ w false hw

lemma wireVal_append_left {n : ℕ} (gs1 gs2 : List Gate) (x : List Bool) (hx : x.length = n)
    (w : ℕ) (hw : w < n + gs1.length) :
    wireVal (gs1 ++ gs2) x w = wireVal gs1 x w := by
  unfold wireVal
  rw [List.foldl_append]
  have hlen : (gs1.foldl wireStep x).length = n + gs1.length := by rw [foldl_wireStep_len, hx]
  exact foldl_wireStep_getD_lt gs2 (gs1.foldl wireStep x) w (by omega)

lemma wireVal_of_extends {n : ℕ} {gs1 gs2 : List Gate} (hext : Extends gs1 gs2)
    (x : List Bool) (hx : x.length = n) (w : ℕ) (hw : w < n + gs1.length) :
    wireVal gs2 x w = wireVal gs1 x w := by
  rcases hext with ⟨d, rfl⟩
  exact wireVal_append_left gs1 d x hx w hw

lemma wireVal_input {n : ℕ} (gs : List Gate) (x : List Bool) (hx : x.length = n)
    (w : ℕ) (hw : w < n) :
    wireVal gs x w = x.getD w false := by
  have h := wireVal_append_left (n := n) [] gs x hx w (by simpa using hw)
  simpa [wireVal] using h

def addGate (n : ℕ) (gs : List Gate) (g : Gate) : List Gate × ℕ :=
  (gs ++ [g], n + gs.length)

lemma addGate_valid {n : ℕ} {gs : List Gate} {g : Gate} (hv : Valid n gs)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < n + gs.length) :
    Valid n (addGate n gs g).1 := by
  constructor
  · intro g' hg'
    simp only [addGate, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hv.1 g' h
    · exact ⟨hop, hlen⟩
  · intro j hj i hi
    simp only [addGate, List.length_append, List.length_cons, List.length_nil] at hj
    simp only [addGate] at hi
    by_cases hlt : j < gs.length
    · rw [getD_append_left gs [g] j _ hlt] at hi
      exact hv.2 j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      rw [getD_append_right gs [g] gs.length _ le_rfl] at hi
      simp only [Nat.sub_self, List.getD_cons_zero] at hi
      exact hin i hi

lemma addGate_extends (n : ℕ) (gs : List Gate) (g : Gate) : Extends gs (addGate n gs g).1 :=
  ⟨[g], rfl⟩

lemma addGate_len (n : ℕ) (gs : List Gate) (g : Gate) : (addGate n gs g).1.length = gs.length + 1 := by
  simp [addGate]

lemma addGate_out_lt (n : ℕ) (gs : List Gate) (g : Gate) :
    (addGate n gs g).2 < n + (addGate n gs g).1.length := by
  simp [addGate]

lemma addGate_val {n : ℕ} (gs : List Gate) (g : Gate) (x : List Bool) (hx : x.length = n) :
    wireVal (addGate n gs g).1 x (addGate n gs g).2 =
      g.op.eval (g.inputs.map fun i => wireVal gs x i) := by
  unfold addGate wireVal
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, wireStep]
  have hlen : (gs.foldl wireStep x).length = n + gs.length := by rw [foldl_wireStep_len, hx]
  rw [getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]

def addConst0 (n : ℕ) (gs : List Gate) : List Gate × ℕ := addGate n gs ⟨GateOp.or, []⟩
def addNot (n : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ := addGate n gs ⟨GateOp.not, [a]⟩
def addAnd (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ := addGate n gs ⟨GateOp.and, [a, b]⟩
def addOr (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ := addGate n gs ⟨GateOp.or, [a, b]⟩

lemma addConst0_spec {n : ℕ} {gs : List Gate} (hv : Valid n gs) :
    let r := addConst0 n gs
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ x : List Bool, x.length = n → wireVal r.1 x r.2 = false := by
  refine ⟨addGate_valid hv (by simp) (by simp) (by simp), addGate_extends _ _ _,
    addGate_len _ _ _, addGate_out_lt _ _ _, fun x hx => by rw [addConst0, addGate_val gs _ x hx]; rfl⟩

lemma addNot_spec {n : ℕ} {gs : List Gate} {a : ℕ} (hv : Valid n gs) (ha : a < n + gs.length) :
    let r := addNot n gs a
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ x : List Bool, x.length = n → wireVal r.1 x r.2 = !(wireVal gs x a) := by
  refine ⟨addGate_valid hv (by simp) (by simp) (by intro i hi; simp at hi; subst hi; exact ha),
    addGate_extends _ _ _, addGate_len _ _ _, addGate_out_lt _ _ _,
    fun x hx => by rw [addNot, addGate_val gs _ x hx]; rfl⟩

lemma addAnd_spec {n : ℕ} {gs : List Gate} {a b : ℕ} (hv : Valid n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := addAnd n gs a b
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ x : List Bool, x.length = n → wireVal r.1 x r.2 = (wireVal gs x a && wireVal gs x b) := by
  refine ⟨addGate_valid hv (by simp) (by simp) (by
      intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    addGate_extends _ _ _, addGate_len _ _ _, addGate_out_lt _ _ _,
    fun x hx => by rw [addAnd, addGate_val gs _ x hx]; simp [GateOp.eval]⟩

lemma addOr_spec {n : ℕ} {gs : List Gate} {a b : ℕ} (hv : Valid n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := addOr n gs a b
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ x : List Bool, x.length = n → wireVal r.1 x r.2 = (wireVal gs x a || wireVal gs x b) := by
  refine ⟨addGate_valid hv (by simp) (by simp) (by
      intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    addGate_extends _ _ _, addGate_len _ _ _, addGate_out_lt _ _ _,
    fun x hx => by rw [addOr, addGate_val gs _ x hx]; simp [GateOp.eval]⟩

def buildVec {n : ℕ} (I : ℕ) (step : List Gate → Fin n → List Gate × ℕ) (gs : List Gate) :
    (m : ℕ) → m ≤ n → List Gate × (Fin n → ℕ)
  | 0, _ => (gs, fun _ => 0)
  | m + 1, hm =>
    let r1 := buildVec I step gs m (by omega)
    let r2 := step r1.1 ⟨m, hm⟩
    (r2.1, fun v => if v.val = m then r2.2 else r1.2 v)

lemma buildVec_spec {n I c : ℕ} {step : List Gate → Fin n → List Gate × ℕ}
    {sem : List Bool → Fin n → Bool} {gs : List Gate}
    (hv : Valid I gs)
    (hstep : ∀ (gs' : List Gate) (v : Fin n), Valid I gs' → Extends gs gs' →
      let r := step gs' v
      Valid I r.1 ∧ Extends gs' r.1 ∧ r.1.length ≤ gs'.length + c ∧ r.2 < I + r.1.length ∧
      ∀ x : List Bool, x.length = I → wireVal r.1 x r.2 = sem x v) :
    ∀ (m : ℕ) (hm : m ≤ n),
      let r := buildVec I step gs m hm
      Valid I r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + m * c ∧
      (∀ v : Fin n, v.val < m → r.2 v < I + r.1.length) ∧
      (∀ x : List Bool, x.length = I → ∀ v : Fin n, v.val < m → wireVal r.1 x (r.2 v) = sem x v) := by
  intro m hm
  induction m with
  | zero =>
    exact ⟨hv, extends_rfl gs, by simp [buildVec], fun _ h => by omega, fun _ _ _ h => by omega⟩
  | succ m ih =>
    rcases ih (by omega) with ⟨v1, e1, l1, bd1, val1⟩
    set r1 := buildVec I step gs m (by omega) with hr1
    set r2 := step r1.1 ⟨m, hm⟩ with hr2
    have h2 := hstep r1.1 ⟨m, hm⟩ v1 e1
    dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨v2, e2, l2, w2, val2⟩
    have hlen2 : r1.1.length ≤ r2.1.length := extends_len e2
    change Valid I r2.1 ∧ Extends gs r2.1 ∧ r2.1.length ≤ gs.length + (m + 1) * c ∧
      (∀ v : Fin n, v.val < m + 1 → (if v.val = m then r2.2 else r1.2 v) < I + r2.1.length) ∧
      (∀ x : List Bool, x.length = I → ∀ v : Fin n, v.val < m + 1 →
        wireVal r2.1 x (if v.val = m then r2.2 else r1.2 v) = sem x v)
    refine ⟨v2, extends_trans e1 e2, ?_, ?_, ?_⟩
    · have hmul : (m + 1) * c = m * c + c := by ring
      omega
    · intro v hvlt
      by_cases hvm : v.val = m
      · rw [ite_eq_left_iff.mpr (fun h => absurd hvm h)]; exact w2
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hvm)]
        have := bd1 v (by omega); omega
    · intro x hx v hvlt
      by_cases hvm : v.val = m
      · have hveq : v = ⟨m, hm⟩ := Fin.ext hvm
        subst hveq
        rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
        exact val2 x hx
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hvm),
          wireVal_of_extends e2 x hx (r1.2 v) (bd1 v (by omega)), val1 x hx v (by omega)]

def buildBranchAx {n : ℕ} (w : ℕ) (hn : 0 < n) (t st w0 : ℕ) (b : Bool) (gs : List Gate) :
    List (Fin n) → List Gate × ℕ × (Fin n → ℕ)
  | [] => (gs, w0, fun _ => w0)
  | s :: rest =>
    let I := n * 2 ^ (w + 1)
    let r0 := buildBranchAx w hn t st w0 b gs rest
    let r1 := addNot I r0.1 (inpWire s (windowPat (w := w) hn t st b s))
    let r2 := addNot I r1.1 r0.2.1
    let r3 := addAnd I r2.1 r1.2 r2.2
    let r4 := addOr I r3.1 r0.2.1 r1.2
    let r5 := buildVec I (fun gs' v =>
      if touchBool w hn s v then addOr I gs' (r0.2.2 v) r3.2 else (gs', r0.2.2 v)) r4.1 n le_rfl
    (r5.1, r4.2, r5.2)

lemma buildBranchAx_spec {n : ℕ} (w : ℕ) (hn : 0 < n) (t st w0 : ℕ) (b : Bool) (gs : List Gate)
    (hv : Valid (n * 2 ^ (w + 1)) gs)
    (hw0 : w0 < n * 2 ^ (w + 1) + gs.length)
    (hv0 : ∀ x : List Bool, x.length = n * 2 ^ (w + 1) → wireVal gs x w0 = false)
    (ss : List (Fin n)) :
    let I := n * 2 ^ (w + 1)
    let r := buildBranchAx w hn t st w0 b gs ss
    Valid I r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + ss.length * (n + 4) ∧
    r.2.1 < I + r.1.length ∧ (∀ v : Fin n, r.2.2 v < I + r.1.length) ∧
    (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := List.ofFn (fun a : Fin I =>
        table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun inputBit => a.val.testBit inputBit.val))
      let sem := branchAxLoop hn table t st b ss
      wireVal r.1 inputs r.2.1 = sem.1 ∧
      ∀ v : Fin n, wireVal r.1 inputs (r.2.2 v) = sem.2 v) := by
  set I := n * 2 ^ (w + 1)
  induction ss with
  | nil =>
    refine ⟨hv, extends_rfl gs, by simp [buildBranchAx], hw0, fun _ => hw0, ?_⟩
    intro table
    have hlen : (List.ofFn (fun a : Fin I =>
      table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
        (fun inputBit => a.val.testBit inputBit.val))).length = I := List.length_ofFn
    exact ⟨hv0 _ hlen, fun _ => hv0 _ hlen⟩
  | cons s rest ih =>
    rcases ih with ⟨v0, e0, l0, waf0, wm0, val0⟩
    set r0 := buildBranchAx w hn t st w0 b gs rest with hr0
    set r1 := addNot I r0.1 (inpWire s (windowPat (w := w) hn t st b s)) with hr1
    have h1 := addNot_spec (a := inpWire s (windowPat (w := w) hn t st b s)) v0
      (by have := inpWire_lt s (windowPat (w := w) hn t st b s); dsimp only [I]; omega)
    dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨v1, e1, l1, w1, val1⟩
    set r2 := addNot I r1.1 r0.2.1 with hr2
    have h2 := addNot_spec (a := r0.2.1) v1 (by omega)
    dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨v2, e2, l2, w2, val2⟩
    set r3 := addAnd I r2.1 r1.2 r2.2 with hr3
    have h3 := addAnd_spec (a := r1.2) (b := r2.2) v2 (by omega) w2
    dsimp only at h3; rw [← hr3] at h3
    rcases h3 with ⟨v3, e3, l3, w3, val3⟩
    set r4 := addOr I r3.1 r0.2.1 r1.2 with hr4
    have h4 := addOr_spec (a := r0.2.1) (b := r1.2) v3 (by omega) (by omega)
    dsimp only at h4; rw [← hr4] at h4
    rcases h4 with ⟨v4, e4, l4, w4, val4⟩
    have e04 : Extends r0.1 r4.1 := extends_trans e1 (extends_trans e2 (extends_trans e3 e4))
    set stepFn : List Gate → Fin n → List Gate × ℕ :=
      fun gs' v => if touchBool w hn s v then addOr I gs' (r0.2.2 v) r3.2 else (gs', r0.2.2 v)
    set r5 := buildVec I stepFn r4.1 n le_rfl with hr5
    have h5 := buildVec_spec (c := 1) (step := stepFn)
      (sem := fun x v => wireVal r0.1 x (r0.2.2 v) || (if touchBool w hn s v then wireVal r3.1 x r3.2 else false))
      v4 (by
        intro gs' v hv' hext'
        have hlen' : r4.1.length ≤ gs'.length := extends_len hext'
        have hext0 : Extends r0.1 gs' := extends_trans e04 hext'
        have hext3 : Extends r3.1 gs' := extends_trans e4 hext'
        dsimp only [stepFn]
        cases htch : touchBool w hn s v
        · simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false]
          refine ⟨hv', extends_rfl gs', by omega, by have := wm0 v; omega, ?_⟩
          intro x hx
          exact wireVal_of_extends hext0 x hx (r0.2.2 v) (wm0 v)
        · simp only [↓reduceIte]
          have hor := addOr_spec (a := r0.2.2 v) (b := r3.2) hv'
            (by have := wm0 v; omega) (by omega)
          rcases hor with ⟨va, ea, la, wa, vala⟩
          refine ⟨va, ea, by omega, wa, ?_⟩
          intro x hx
          rw [vala x hx, wireVal_of_extends hext0 x hx (r0.2.2 v) (wm0 v),
            wireVal_of_extends hext3 x hx r3.2 w3]) n le_rfl
    dsimp only at h5; rw [← hr5] at h5
    rcases h5 with ⟨v5, e5, l5, bd5, val5⟩
    have hlen5 : r4.1.length ≤ r5.1.length := extends_len e5
    change Valid I r5.1 ∧ Extends gs r5.1 ∧ r5.1.length ≤ gs.length + (s :: rest).length * (n + 4) ∧
      r4.2 < I + r5.1.length ∧ (∀ v : Fin n, r5.2 v < I + r5.1.length) ∧
      (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
        let inputs := List.ofFn (fun a : Fin I =>
          table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
            (fun inputBit => a.val.testBit inputBit.val))
        let sem := branchAxLoop hn table t st b (s :: rest)
        wireVal r5.1 inputs r4.2 = sem.1 ∧
        ∀ v : Fin n, wireVal r5.1 inputs (r5.2 v) = sem.2 v)
    refine ⟨v5, extends_trans e0 (extends_trans e04 e5), ?_, by omega, fun v => bd5 v v.isLt, ?_⟩
    · simp only [List.length_cons]
      have hmul : (rest.length + 1) * (n + 4) = rest.length * (n + 4) + (n + 4) := by ring
      omega
    · intro table
      set inputs := List.ofFn (fun a : Fin I =>
        table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun inputBit => a.val.testBit inputBit.val))
      have hlen : inputs.length = I := List.length_ofFn
      rcases val0 table with ⟨haf_eq, ham_eq⟩
      have hfail : wireVal r1.1 inputs r1.2 = !(table s (windowPat hn t st b s)) := by
        rw [val1 inputs hlen, wireVal_input r0.1 inputs hlen _ (inpWire_lt s _),
          inputs_getD_inpWire hn table s (windowPat hn t st b s)]
      have hnotAny : wireVal r2.1 inputs r2.2 = !(branchAxLoop hn table t st b rest).1 := by
        rw [val2 inputs hlen, wireVal_of_extends e1 inputs hlen r0.2.1 waf0, haf_eq]
      have hpick : wireVal r3.1 inputs r3.2 =
          (!(table s (windowPat hn t st b s)) && !(branchAxLoop hn table t st b rest).1) := by
        rw [val3 inputs hlen, wireVal_of_extends e2 inputs hlen r1.2 w1, hfail, hnotAny]
      refine ⟨?_, ?_⟩
      · rw [wireVal_of_extends e5 inputs hlen r4.2 w4, val4 inputs hlen,
          wireVal_of_extends (extends_trans e1 (extends_trans e2 e3)) inputs hlen r0.2.1 waf0,
          wireVal_of_extends (extends_trans e2 e3) inputs hlen r1.2 w1,
          haf_eq, hfail]
        rfl
      · intro v
        rw [val5 inputs hlen v v.isLt, ham_eq v, hpick]
        rfl

structure StageWires (n w : ℕ) where
  dead : Fin (4 ^ w) → ℕ
  mask : Fin (4 ^ w) → Fin n → ℕ
  slotLive : Fin (4 ^ w) → Fin 3 → ℕ
  slotMask : Fin (4 ^ w) → Fin 3 → Fin n → ℕ

def buildState {n w : ℕ} (hn : 0 < n) (t : Fin n) (w0 : ℕ)
    (childDead : Fin (4 ^ w) → ℕ) (childMask : Fin (4 ^ w) → Fin n → ℕ)
    (gs : List Gate) (st : Fin (4 ^ w)) :
    List Gate × (ℕ × (Fin n → ℕ) × (Fin 3 → ℕ) × (Fin 3 → Fin n → ℕ)) :=
  let I := n * 2 ^ (w + 1)
  let ss := startsAt n w t.val
  let c0 : Fin (4 ^ w) := ⟨nextState w t.val st.val false, nextState_lt w t.val st.val false⟩
  let c1 : Fin (4 ^ w) := ⟨nextState w t.val st.val true, nextState_lt w t.val st.val true⟩
  let rA0 := buildBranchAx w hn t.val st.val w0 false gs ss
  let rA1 := buildBranchAx w hn t.val st.val w0 true rA0.1 ss
  let rNF0 := addNot I rA1.1 rA0.2.1
  let rNF1 := addNot I rNF0.1 rA1.2.1
  let rD0 := addOr I rNF1.1 rA0.2.1 (childDead c0)
  let rD1 := addOr I rD0.1 rA1.2.1 (childDead c1)
  let rM0 := buildVec I (fun gs' v =>
    let ra := addAnd I gs' rNF0.2 (childMask c0 v)
    addOr I ra.1 (rA0.2.2 v) ra.2) rD1.1 n le_rfl
  let rM1 := buildVec I (fun gs' v =>
    let ra := addAnd I gs' rNF1.2 (childMask c1 v)
    addOr I ra.1 (rA1.2.2 v) ra.2) rM0.1 n le_rfl
  let rDead := addAnd I rM1.1 rD0.2 rD1.2
  let hp := rM0.2 t
  let hn' := rM1.2 t
  let rNotP := addNot I rDead.1 hp
  let rKeep0 := addOr I rNotP.1 rNotP.2 hn'
  let rBoth := addAnd I rKeep0.1 hp hn'
  let rDoRes := addAnd I rBoth.1 rDead.2 rBoth.2
  let rRes := buildVec I (fun gs' v =>
    if v.val = t.val then (gs', w0)
    else
      let ra0 := addAnd I gs' rKeep0.2 (rM0.2 v)
      let ra1 := addAnd I ra0.1 hp (rM1.2 v)
      addOr I ra1.1 ra0.2 ra1.2) rDoRes.1 n le_rfl
  let sLive : Fin 3 → ℕ := fun k =>
    match k.val with
    | 0 => rDoRes.2
    | 1 => rA0.2.1
    | _ => rA1.2.1
  let sMask : Fin 3 → Fin n → ℕ := fun k =>
    match k.val with
    | 0 => rRes.2
    | 1 => rA0.2.2
    | _ => rA1.2.2
  (rRes.1, (rDead.2, rRes.2, sLive, sMask))

lemma buildState_spec {n w : ℕ} (hn : 0 < n) (t : Fin n) (w0 : ℕ)
    (childDead : Fin (4 ^ w) → ℕ) (childMask : Fin (4 ^ w) → Fin n → ℕ)
    (gs : List Gate) (st : Fin (4 ^ w))
    (hv : Valid (n * 2 ^ (w + 1)) gs)
    (hw0 : w0 < n * 2 ^ (w + 1) + gs.length)
    (hv0 : ∀ x : List Bool, x.length = n * 2 ^ (w + 1) → wireVal gs x w0 = false)
    (hcd : ∀ c, childDead c < n * 2 ^ (w + 1) + gs.length)
    (hcm : ∀ c v, childMask c v < n * 2 ^ (w + 1) + gs.length)
    (hcval : ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let I := n * 2 ^ (w + 1)
      let inputs := List.ofFn (fun a : Fin I =>
        table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun inputBit => a.val.testBit inputBit.val))
      ∀ c, wireVal gs inputs (childDead c) = (dpStage hn table (t.val + 1)).dead c ∧
        ∀ v, wireVal gs inputs (childMask c v) = (dpStage hn table (t.val + 1)).mask c v) :
    let I := n * 2 ^ (w + 1)
    let r := buildState hn t w0 childDead childMask gs st
    Valid I r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + (2 * (startsAt n w t.val).length * (n + 4) + 7 * n + 9) ∧
    r.2.1 < I + r.1.length ∧
    (∀ v, r.2.2.1 v < I + r.1.length) ∧
    (∀ k, r.2.2.2.1 k < I + r.1.length) ∧
    (∀ k v, r.2.2.2.2 k v < I + r.1.length) ∧
    (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := List.ofFn (fun a : Fin I =>
        table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun inputBit => a.val.testBit inputBit.val))
      wireVal r.1 inputs r.2.1 = (dpStage hn table t.val).dead st ∧
      (∀ v, wireVal r.1 inputs (r.2.2.1 v) = (dpStage hn table t.val).mask st v) ∧
      (∀ k, wireVal r.1 inputs (r.2.2.2.1 k) = semSlotLive hn table t st k) ∧
      (∀ k v, wireVal r.1 inputs (r.2.2.2.2 k v) = semSlotMask hn table t st k v)) := by
  set I := n * 2 ^ (w + 1)
  set ss := startsAt n w t.val
  set c0 : Fin (4 ^ w) := ⟨nextState w t.val st.val false, nextState_lt w t.val st.val false⟩
  set c1 : Fin (4 ^ w) := ⟨nextState w t.val st.val true, nextState_lt w t.val st.val true⟩
  set rA0 := buildBranchAx w hn t.val st.val w0 false gs ss with hrA0
  have hA0 := buildBranchAx_spec w hn t.val st.val w0 false gs hv hw0 hv0 ss
  dsimp only at hA0; rw [← hrA0] at hA0
  rcases hA0 with ⟨vA0, eA0, lA0, waf0, wm0, valA0⟩
  have hlenA0 : gs.length ≤ rA0.1.length := extends_len eA0
  set rA1 := buildBranchAx w hn t.val st.val w0 true rA0.1 ss with hrA1
  have hA1 := buildBranchAx_spec w hn t.val st.val w0 true rA0.1 vA0 (by omega)
    (fun x hx => by rw [wireVal_of_extends eA0 x hx w0 hw0, hv0 x hx]) ss
  dsimp only at hA1; rw [← hrA1] at hA1
  rcases hA1 with ⟨vA1, eA1, lA1, waf1, wm1, valA1⟩
  have hlenA1 : rA0.1.length ≤ rA1.1.length := extends_len eA1
  set rNF0 := addNot I rA1.1 rA0.2.1 with hrNF0
  have hNF0 := addNot_spec (a := rA0.2.1) vA1 (by omega)
  dsimp only at hNF0; rw [← hrNF0] at hNF0
  rcases hNF0 with ⟨vNF0, eNF0, lNF0, wNF0, valNF0⟩
  set rNF1 := addNot I rNF0.1 rA1.2.1 with hrNF1
  have hNF1 := addNot_spec (a := rA1.2.1) vNF0 (by omega)
  dsimp only at hNF1; rw [← hrNF1] at hNF1
  rcases hNF1 with ⟨vNF1, eNF1, lNF1, wNF1, valNF1⟩
  set rD0 := addOr I rNF1.1 rA0.2.1 (childDead c0) with hrD0
  have hD0 := addOr_spec (a := rA0.2.1) (b := childDead c0) vNF1 (by omega) (by have := hcd c0; omega)
  dsimp only at hD0; rw [← hrD0] at hD0
  rcases hD0 with ⟨vD0, eD0, lD0, wD0, valD0⟩
  set rD1 := addOr I rD0.1 rA1.2.1 (childDead c1) with hrD1
  have hD1 := addOr_spec (a := rA1.2.1) (b := childDead c1) vD0 (by omega) (by have := hcd c1; omega)
  dsimp only at hD1; rw [← hrD1] at hD1
  rcases hD1 with ⟨vD1, eD1, lD1, wD1, valD1⟩
  have eA0D1 : Extends rA0.1 rD1.1 :=
    extends_trans eA1 (extends_trans eNF0 (extends_trans eNF1 (extends_trans eD0 eD1)))
  have eA1D1 : Extends rA1.1 rD1.1 :=
    extends_trans eNF0 (extends_trans eNF1 (extends_trans eD0 eD1))
  have eNF0D1 : Extends rNF0.1 rD1.1 := extends_trans eNF1 (extends_trans eD0 eD1)
  have eNF1D1 : Extends rNF1.1 rD1.1 := extends_trans eD0 eD1
  have e0D1 : Extends gs rD1.1 := extends_trans eA0 eA0D1
  set stepM0 : List Gate → Fin n → List Gate × ℕ := fun gs' v =>
    let ra := addAnd I gs' rNF0.2 (childMask c0 v)
    addOr I ra.1 (rA0.2.2 v) ra.2
  set rM0 := buildVec I stepM0 rD1.1 n le_rfl with hrM0
  have hM0 := buildVec_spec (c := 2) (step := stepM0)
    (sem := fun x v => wireVal rA0.1 x (rA0.2.2 v) || (wireVal rNF0.1 x rNF0.2 && wireVal gs x (childMask c0 v)))
    vD1 (by
      intro gs' v hv' hext'
      have hlen' : rD1.1.length ≤ gs'.length := extends_len hext'
      set ra := addAnd I gs' rNF0.2 (childMask c0 v) with hra
      have ha := addAnd_spec (a := rNF0.2) (b := childMask c0 v) hv'
        (by omega) (by have := hcm c0 v; omega)
      dsimp only at ha; rw [← hra] at ha
      rcases ha with ⟨va, ea, la, wa, vala⟩
      set rb := addOr I ra.1 (rA0.2.2 v) ra.2 with hrb
      have hb := addOr_spec (a := rA0.2.2 v) (b := ra.2) va (by have := wm0 v; omega) wa
      dsimp only at hb; rw [← hrb] at hb
      rcases hb with ⟨vb, eb, lb, wb, valb⟩
      refine ⟨vb, extends_trans ea eb, by change rb.1.length ≤ gs'.length + 2; omega, wb, ?_⟩
      intro x hx
      rw [valb x hx,
        wireVal_of_extends (extends_trans eA0D1 (extends_trans hext' ea)) x hx (rA0.2.2 v) (wm0 v),
        vala x hx,
        wireVal_of_extends (extends_trans eNF0D1 hext') x hx rNF0.2 wNF0,
        wireVal_of_extends (extends_trans e0D1 hext') x hx (childMask c0 v) (hcm c0 v)]) n le_rfl
  dsimp only at hM0; rw [← hrM0] at hM0
  rcases hM0 with ⟨vM0, eM0, lM0, bdM0, valM0⟩
  have hlenM0 : rD1.1.length ≤ rM0.1.length := extends_len eM0
  set stepM1 : List Gate → Fin n → List Gate × ℕ := fun gs' v =>
    let ra := addAnd I gs' rNF1.2 (childMask c1 v)
    addOr I ra.1 (rA1.2.2 v) ra.2
  set rM1 := buildVec I stepM1 rM0.1 n le_rfl with hrM1
  have hM1 := buildVec_spec (c := 2) (step := stepM1)
    (sem := fun x v => wireVal rA1.1 x (rA1.2.2 v) || (wireVal rNF1.1 x rNF1.2 && wireVal gs x (childMask c1 v)))
    vM0 (by
      intro gs' v hv' hext'
      have hlen' : rM0.1.length ≤ gs'.length := extends_len hext'
      set ra := addAnd I gs' rNF1.2 (childMask c1 v) with hra
      have ha := addAnd_spec (a := rNF1.2) (b := childMask c1 v) hv'
        (by omega) (by have := hcm c1 v; omega)
      dsimp only at ha; rw [← hra] at ha
      rcases ha with ⟨va, ea, la, wa, vala⟩
      set rb := addOr I ra.1 (rA1.2.2 v) ra.2 with hrb
      have hb := addOr_spec (a := rA1.2.2 v) (b := ra.2) va (by have := wm1 v; omega) wa
      dsimp only at hb; rw [← hrb] at hb
      rcases hb with ⟨vb, eb, lb, wb, valb⟩
      refine ⟨vb, extends_trans ea eb, by change rb.1.length ≤ gs'.length + 2; omega, wb, ?_⟩
      intro x hx
      rw [valb x hx,
        wireVal_of_extends (extends_trans eA1D1 (extends_trans eM0 (extends_trans hext' ea))) x hx (rA1.2.2 v) (wm1 v),
        vala x hx,
        wireVal_of_extends (extends_trans eNF1D1 (extends_trans eM0 hext')) x hx rNF1.2 wNF1,
        wireVal_of_extends (extends_trans e0D1 (extends_trans eM0 hext')) x hx (childMask c1 v) (hcm c1 v)]) n le_rfl
  dsimp only at hM1; rw [← hrM1] at hM1
  rcases hM1 with ⟨vM1, eM1, lM1, bdM1, valM1⟩
  have hlenM1 : rM0.1.length ≤ rM1.1.length := extends_len eM1
  set rDead := addAnd I rM1.1 rD0.2 rD1.2 with hrDead
  have hDead := addAnd_spec (a := rD0.2) (b := rD1.2) vM1 (by omega) (by omega)
  dsimp only at hDead; rw [← hrDead] at hDead
  rcases hDead with ⟨vDead, eDead, lDead, wDead, valDead⟩
  set hp := rM0.2 t
  set hn' := rM1.2 t
  set rNotP := addNot I rDead.1 hp with hrNotP
  have hNotP := addNot_spec (a := hp) vDead (by have := bdM0 t t.isLt; omega)
  dsimp only at hNotP; rw [← hrNotP] at hNotP
  rcases hNotP with ⟨vNotP, eNotP, lNotP, wNotP, valNotP⟩
  set rKeep0 := addOr I rNotP.1 rNotP.2 hn' with hrKeep0
  have hKeep0 := addOr_spec (a := rNotP.2) (b := hn') vNotP wNotP (by have := bdM1 t t.isLt; omega)
  dsimp only at hKeep0; rw [← hrKeep0] at hKeep0
  rcases hKeep0 with ⟨vKeep0, eKeep0, lKeep0, wKeep0, valKeep0⟩
  set rBoth := addAnd I rKeep0.1 hp hn' with hrBoth
  have hBoth := addAnd_spec (a := hp) (b := hn') vKeep0
    (by have := bdM0 t t.isLt; omega) (by have := bdM1 t t.isLt; omega)
  dsimp only at hBoth; rw [← hrBoth] at hBoth
  rcases hBoth with ⟨vBoth, eBoth, lBoth, wBoth, valBoth⟩
  set rDoRes := addAnd I rBoth.1 rDead.2 rBoth.2 with hrDoRes
  have hDoRes := addAnd_spec (a := rDead.2) (b := rBoth.2) vBoth (by omega) wBoth
  dsimp only at hDoRes; rw [← hrDoRes] at hDoRes
  rcases hDoRes with ⟨vDoRes, eDoRes, lDoRes, wDoRes, valDoRes⟩
  have eM0DoRes : Extends rM0.1 rDoRes.1 :=
    extends_trans eM1 (extends_trans eDead (extends_trans eNotP
      (extends_trans eKeep0 (extends_trans eBoth eDoRes))))
  have eM1DoRes : Extends rM1.1 rDoRes.1 :=
    extends_trans eDead (extends_trans eNotP (extends_trans eKeep0 (extends_trans eBoth eDoRes)))
  have eKeep0DoRes : Extends rKeep0.1 rDoRes.1 := extends_trans eBoth eDoRes
  have e0DoRes : Extends gs rDoRes.1 := extends_trans e0D1 (extends_trans eM0 eM0DoRes)
  set stepRes : List Gate → Fin n → List Gate × ℕ := fun gs' v =>
    if v.val = t.val then (gs', w0)
    else
      let ra0 := addAnd I gs' rKeep0.2 (rM0.2 v)
      let ra1 := addAnd I ra0.1 hp (rM1.2 v)
      addOr I ra1.1 ra0.2 ra1.2
  set rRes := buildVec I stepRes rDoRes.1 n le_rfl with hrRes
  have hRes := buildVec_spec (c := 3) (step := stepRes)
    (sem := fun x v =>
      if v.val = t.val then false
      else (wireVal rKeep0.1 x rKeep0.2 && wireVal rM0.1 x (rM0.2 v)) ||
        (wireVal rM0.1 x hp && wireVal rM1.1 x (rM1.2 v)))
    vDoRes (by
      intro gs' v hv' hext'
      have hlen' : rDoRes.1.length ≤ gs'.length := extends_len hext'
      dsimp only [stepRes]
      by_cases hvt : v.val = t.val
      · simp only [hvt, ↓reduceIte]
        refine ⟨hv', extends_rfl gs', by omega, by omega, ?_⟩
        intro x hx
        rw [wireVal_of_extends (extends_trans e0DoRes hext') x hx w0 hw0, hv0 x hx]
      · simp only [hvt, ↓reduceIte]
        set ra0 := addAnd I gs' rKeep0.2 (rM0.2 v) with hra0
        have ha0 := addAnd_spec (a := rKeep0.2) (b := rM0.2 v) hv'
          (by omega) (by have := bdM0 v v.isLt; omega)
        dsimp only at ha0; rw [← hra0] at ha0
        rcases ha0 with ⟨va0, ea0, la0, wa0, vala0⟩
        set ra1 := addAnd I ra0.1 hp (rM1.2 v) with hra1
        have ha1 := addAnd_spec (a := hp) (b := rM1.2 v) va0
          (by have := bdM0 t t.isLt; omega) (by have := bdM1 v v.isLt; omega)
        dsimp only at ha1; rw [← hra1] at ha1
        rcases ha1 with ⟨va1, ea1, la1, wa1, vala1⟩
        set rb := addOr I ra1.1 ra0.2 ra1.2 with hrb
        have hb := addOr_spec (a := ra0.2) (b := ra1.2) va1 (by omega) wa1
        dsimp only at hb; rw [← hrb] at hb
        rcases hb with ⟨vb, eb, lb, wb, valb⟩
        refine ⟨vb, extends_trans ea0 (extends_trans ea1 eb), by omega, wb, ?_⟩
        intro x hx
        rw [valb x hx, wireVal_of_extends ea1 x hx ra0.2 wa0, vala0 x hx, vala1 x hx,
          wireVal_of_extends (extends_trans eKeep0DoRes hext') x hx rKeep0.2 wKeep0,
          wireVal_of_extends (extends_trans eM0DoRes hext') x hx (rM0.2 v) (bdM0 v v.isLt),
          wireVal_of_extends (extends_trans eM0DoRes (extends_trans hext' ea0)) x hx hp (bdM0 t t.isLt),
          wireVal_of_extends (extends_trans eM1DoRes (extends_trans hext' ea0)) x hx (rM1.2 v) (bdM1 v v.isLt)])
    n le_rfl
  dsimp only at hRes; rw [← hrRes] at hRes
  rcases hRes with ⟨vRes, eRes, lRes, bdRes, valRes⟩
  have hlenRes : rDoRes.1.length ≤ rRes.1.length := extends_len eRes
  have e0Res : Extends gs rRes.1 := extends_trans e0DoRes eRes
  have eA0Res : Extends rA0.1 rRes.1 := extends_trans eA0D1 (extends_trans eM0 (extends_trans eM0DoRes eRes))
  have eA1Res : Extends rA1.1 rRes.1 := extends_trans eA1D1 (extends_trans eM0 (extends_trans eM0DoRes eRes))
  have eDeadRes : Extends rDead.1 rRes.1 :=
    extends_trans eNotP (extends_trans eKeep0 (extends_trans eBoth (extends_trans eDoRes eRes)))
  change Valid I rRes.1 ∧ Extends gs rRes.1 ∧
    rRes.1.length ≤ gs.length + (2 * ss.length * (n + 4) + 7 * n + 9) ∧
    rDead.2 < I + rRes.1.length ∧
    (∀ v, rRes.2 v < I + rRes.1.length) ∧
    (∀ k : Fin 3, (match k.val with | 0 => rDoRes.2 | 1 => rA0.2.1 | _ => rA1.2.1) < I + rRes.1.length) ∧
    (∀ k : Fin 3, ∀ v, (match k.val with | 0 => rRes.2 | 1 => rA0.2.2 | _ => rA1.2.2) v < I + rRes.1.length) ∧
    (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := List.ofFn (fun a : Fin I =>
        table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun inputBit => a.val.testBit inputBit.val))
      wireVal rRes.1 inputs rDead.2 = (dpStage hn table t.val).dead st ∧
      (∀ v, wireVal rRes.1 inputs (rRes.2 v) = (dpStage hn table t.val).mask st v) ∧
      (∀ k : Fin 3, wireVal rRes.1 inputs (match k.val with | 0 => rDoRes.2 | 1 => rA0.2.1 | _ => rA1.2.1) =
        semSlotLive hn table t st k) ∧
      (∀ k : Fin 3, ∀ v, wireVal rRes.1 inputs
        ((match k.val with | 0 => rRes.2 | 1 => rA0.2.2 | _ => rA1.2.2) v) =
        semSlotMask hn table t st k v))
  have hmul2 : 2 * ss.length * (n + 4) = 2 * (ss.length * (n + 4)) := by ring
  refine ⟨vRes, e0Res, by omega, by omega, fun v => bdRes v v.isLt, ?_, ?_, ?_⟩
  · intro k
    rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 by omega) with h | h | h <;> simp only [h] <;> omega
  · intro k v
    rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 by omega) with h | h | h
    · simp only [h]; exact bdRes v v.isLt
    · simp only [h]; have := wm0 v; omega
    · simp only [h]; have := wm1 v; omega
  · intro table
    set inputs := List.ofFn (fun a : Fin I =>
      table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
        (fun inputBit => a.val.testBit inputBit.val))
    have hlen : inputs.length = I := List.length_ofFn
    rcases valA0 table with ⟨hAf0, hAm0⟩
    rcases valA1 table with ⟨hAf1, hAm1⟩
    rcases hcval table c0 with ⟨hCd0, hCm0⟩
    rcases hcval table c1 with ⟨hCd1, hCm1⟩
    have hNF0_v : wireVal rNF0.1 inputs rNF0.2 = !(branchAxLoop hn table t.val st.val false ss).1 := by
      rw [valNF0 inputs hlen, wireVal_of_extends eA1 inputs hlen rA0.2.1 waf0, hAf0]
    have hNF1_v : wireVal rNF1.1 inputs rNF1.2 = !(branchAxLoop hn table t.val st.val true ss).1 := by
      rw [valNF1 inputs hlen, wireVal_of_extends eNF0 inputs hlen rA1.2.1 waf1, hAf1]
    have hD0_v : wireVal rD0.1 inputs rD0.2 =
        ((branchAxLoop hn table t.val st.val false ss).1 || (dpStage hn table (t.val + 1)).dead c0) := by
      rw [valD0 inputs hlen,
        wireVal_of_extends (extends_trans eA1 (extends_trans eNF0 eNF1)) inputs hlen rA0.2.1 waf0,
        wireVal_of_extends (extends_trans eA0 (extends_trans eA1 (extends_trans eNF0 eNF1)))
          inputs hlen (childDead c0) (hcd c0), hAf0, hCd0]
    have hD1_v : wireVal rD1.1 inputs rD1.2 =
        ((branchAxLoop hn table t.val st.val true ss).1 || (dpStage hn table (t.val + 1)).dead c1) := by
      rw [valD1 inputs hlen,
        wireVal_of_extends (extends_trans eNF0 (extends_trans eNF1 eD0)) inputs hlen rA1.2.1 waf1,
        wireVal_of_extends (extends_trans eA0 (extends_trans eA1 (extends_trans eNF0 (extends_trans eNF1 eD0))))
          inputs hlen (childDead c1) (hcd c1), hAf1, hCd1]
    have hM0_v : ∀ v, wireVal rM0.1 inputs (rM0.2 v) =
        ((branchAxLoop hn table t.val st.val false ss).2 v ||
          (!(branchAxLoop hn table t.val st.val false ss).1 && (dpStage hn table (t.val + 1)).mask c0 v)) := by
      intro v
      rw [valM0 inputs hlen v v.isLt, hAm0 v, hNF0_v, hCm0 v]
    have hM1_v : ∀ v, wireVal rM1.1 inputs (rM1.2 v) =
        ((branchAxLoop hn table t.val st.val true ss).2 v ||
          (!(branchAxLoop hn table t.val st.val true ss).1 && (dpStage hn table (t.val + 1)).mask c1 v)) := by
      intro v
      rw [valM1 inputs hlen v v.isLt, hAm1 v, hNF1_v, hCm1 v]
    have hDead_v : wireVal rDead.1 inputs rDead.2 = (dpStage hn table t.val).dead st := by
      rw [valDead inputs hlen,
        wireVal_of_extends (extends_trans eD1 (extends_trans eM0 eM1)) inputs hlen rD0.2 wD0,
        wireVal_of_extends (extends_trans eM0 eM1) inputs hlen rD1.2 wD1,
        hD0_v, hD1_v, (dpStage_eq_step hn table t st).1]
    have hKeep0_v : wireVal rKeep0.1 inputs rKeep0.2 =
        (!(wireVal rM0.1 inputs hp) || wireVal rM1.1 inputs hn') := by
      rw [valKeep0 inputs hlen, valNotP inputs hlen,
        wireVal_of_extends (extends_trans eM1 eDead) inputs hlen hp (bdM0 t t.isLt),
        wireVal_of_extends (extends_trans eDead eNotP) inputs hlen hn' (bdM1 t t.isLt)]
    have hBoth_v : wireVal rBoth.1 inputs rBoth.2 =
        (wireVal rM0.1 inputs hp && wireVal rM1.1 inputs hn') := by
      rw [valBoth inputs hlen,
        wireVal_of_extends (extends_trans eM1 (extends_trans eDead (extends_trans eNotP eKeep0)))
          inputs hlen hp (bdM0 t t.isLt),
        wireVal_of_extends (extends_trans eDead (extends_trans eNotP eKeep0))
          inputs hlen hn' (bdM1 t t.isLt)]
    have hDoRes_v : wireVal rDoRes.1 inputs rDoRes.2 =
        ((dpStage hn table t.val).dead st && wireVal rM0.1 inputs hp && wireVal rM1.1 inputs hn') := by
      rw [valDoRes inputs hlen,
        wireVal_of_extends (extends_trans eNotP (extends_trans eKeep0 eBoth)) inputs hlen rDead.2 wDead,
        hDead_v, hBoth_v, Bool.and_assoc]
    have hRes_v : ∀ v, wireVal rRes.1 inputs (rRes.2 v) = (dpStage hn table t.val).mask st v := by
      intro v
      rw [valRes inputs hlen v v.isLt, hKeep0_v, hM0_v t, hM1_v t, hM0_v v, hM1_v v,
        (dpStage_eq_step hn table t st).2 v]
      rfl
    refine ⟨?_, hRes_v, ?_, ?_⟩
    · rw [wireVal_of_extends eDeadRes inputs hlen rDead.2 wDead, hDead_v]
    · intro k
      rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 by omega) with h | h | h
      · simp only [h, semSlotLive]
        rw [wireVal_of_extends eRes inputs hlen rDoRes.2 wDoRes, hDoRes_v, hM0_v t, hM1_v t,
          (dpStage_eq_step hn table t st).1]
      · simp only [h, semSlotLive]
        rw [wireVal_of_extends eA0Res inputs hlen rA0.2.1 waf0, hAf0]
      · simp only [h, semSlotLive]
        rw [wireVal_of_extends eA1Res inputs hlen rA1.2.1 waf1, hAf1]
    · intro k v
      rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 by omega) with h | h | h
      · simp only [h, semSlotMask]
        rw [hRes_v v, (dpStage_eq_step hn table t st).2 v]
      · simp only [h, semSlotMask]
        rw [wireVal_of_extends eA0Res inputs hlen (rA0.2.2 v) (wm0 v), hAm0 v]
      · simp only [h, semSlotMask]
        rw [wireVal_of_extends eA1Res inputs hlen (rA1.2.2 v) (wm1 v), hAm1 v]

def buildStageLoop {n w : ℕ} (hn : 0 < n) (t : Fin n) (w0 : ℕ)
    (childDead : Fin (4 ^ w) → ℕ) (childMask : Fin (4 ^ w) → Fin n → ℕ)
    (gs : List Gate) : (m : ℕ) → m ≤ 4 ^ w → List Gate × StageWires n w
  | 0, _ => (gs, ⟨fun _ => w0, fun _ _ => w0, fun _ _ => w0, fun _ _ _ => w0⟩)
  | m + 1, hm =>
    let r1 := buildStageLoop hn t w0 childDead childMask gs m (by omega)
    let st : Fin (4 ^ w) := ⟨m, hm⟩
    let r2 := buildState hn t w0 childDead childMask r1.1 st
    (r2.1,
      ⟨fun c => if c.val = m then r2.2.1 else r1.2.dead c,
       fun c => if c.val = m then r2.2.2.1 else r1.2.mask c,
       fun c => if c.val = m then r2.2.2.2.1 else r1.2.slotLive c,
       fun c => if c.val = m then r2.2.2.2.2 else r1.2.slotMask c⟩)

lemma buildStageLoop_spec {n w : ℕ} (hn : 0 < n) (t : Fin n) (w0 : ℕ)
    (childDead : Fin (4 ^ w) → ℕ) (childMask : Fin (4 ^ w) → Fin n → ℕ)
    (gs : List Gate)
    (hv : Valid (n * 2 ^ (w + 1)) gs)
    (hw0 : w0 < n * 2 ^ (w + 1) + gs.length)
    (hv0 : ∀ x : List Bool, x.length = n * 2 ^ (w + 1) → wireVal gs x w0 = false)
    (hcd : ∀ c, childDead c < n * 2 ^ (w + 1) + gs.length)
    (hcm : ∀ c v, childMask c v < n * 2 ^ (w + 1) + gs.length)
    (hcval : ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let I := n * 2 ^ (w + 1)
      let inputs := List.ofFn (fun a : Fin I =>
        table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun inputBit => a.val.testBit inputBit.val))
      ∀ c, wireVal gs inputs (childDead c) = (dpStage hn table (t.val + 1)).dead c ∧
        ∀ v, wireVal gs inputs (childMask c v) = (dpStage hn table (t.val + 1)).mask c v) :
    ∀ (m : ℕ) (hm : m ≤ 4 ^ w),
      let I := n * 2 ^ (w + 1)
      let r := buildStageLoop hn t w0 childDead childMask gs m hm
      Valid I r.1 ∧ Extends gs r.1 ∧
      r.1.length ≤ gs.length + m * (2 * (startsAt n w t.val).length * (n + 4) + 7 * n + 9) ∧
      (∀ c : Fin (4 ^ w), c.val < m →
        r.2.dead c < I + r.1.length ∧
        (∀ v, r.2.mask c v < I + r.1.length) ∧
        (∀ k, r.2.slotLive c k < I + r.1.length) ∧
        (∀ k v, r.2.slotMask c k v < I + r.1.length)) ∧
      (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
        let inputs := List.ofFn (fun a : Fin I =>
          table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
            (fun inputBit => a.val.testBit inputBit.val))
        ∀ c : Fin (4 ^ w), c.val < m →
          wireVal r.1 inputs (r.2.dead c) = (dpStage hn table t.val).dead c ∧
          (∀ v, wireVal r.1 inputs (r.2.mask c v) = (dpStage hn table t.val).mask c v) ∧
          (∀ k, wireVal r.1 inputs (r.2.slotLive c k) = semSlotLive hn table t c k) ∧
          (∀ k v, wireVal r.1 inputs (r.2.slotMask c k v) = semSlotMask hn table t c k v)) := by
  set I := n * 2 ^ (w + 1)
  intro m hm
  induction m with
  | zero =>
    exact ⟨hv, extends_rfl gs, by simp [buildStageLoop], fun _ h => by omega, fun _ _ h => by omega⟩
  | succ m ih =>
    rcases ih (by omega) with ⟨v1, e1, l1, bd1, val1⟩
    set r1 := buildStageLoop hn t w0 childDead childMask gs m (by omega) with hr1
    have hlen1 : gs.length ≤ r1.1.length := extends_len e1
    set st : Fin (4 ^ w) := ⟨m, hm⟩
    set r2 := buildState hn t w0 childDead childMask r1.1 st with hr2
    have h2 := buildState_spec hn t w0 childDead childMask r1.1 st v1 (by omega)
      (fun x hx => by rw [wireVal_of_extends e1 x hx w0 hw0, hv0 x hx])
      (fun c => by have := hcd c; omega)
      (fun c v => by have := hcm c v; omega)
      (fun table c => by
        set inputs := List.ofFn (fun a : Fin I =>
          table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
            (fun inputBit => a.val.testBit inputBit.val))
        have hlen : inputs.length = I := List.length_ofFn
        rcases hcval table c with ⟨hd, hm'⟩
        exact ⟨by rw [wireVal_of_extends e1 inputs hlen (childDead c) (hcd c), hd],
          fun v => by rw [wireVal_of_extends e1 inputs hlen (childMask c v) (hcm c v), hm' v]⟩)
    dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨v2, e2, l2, wd2, wm2, wsl2, wsm2, val2⟩
    have hlen2 : r1.1.length ≤ r2.1.length := extends_len e2
    refine ⟨v2, extends_trans e1 e2, ?_, ?_, ?_⟩
    · have hmul : (m + 1) * (2 * (startsAt n w t.val).length * (n + 4) + 7 * n + 9) =
          m * (2 * (startsAt n w t.val).length * (n + 4) + 7 * n + 9) +
          (2 * (startsAt n w t.val).length * (n + 4) + 7 * n + 9) := by ring
      change r2.1.length ≤ _
      omega
    · intro c hc
      change (if c.val = m then r2.2.1 else r1.2.dead c) < I + r2.1.length ∧
        (∀ v, (if c.val = m then r2.2.2.1 else r1.2.mask c) v < I + r2.1.length) ∧
        (∀ k, (if c.val = m then r2.2.2.2.1 else r1.2.slotLive c) k < I + r2.1.length) ∧
        (∀ k v, (if c.val = m then r2.2.2.2.2 else r1.2.slotMask c) k v < I + r2.1.length)
      by_cases hcm' : c.val = m
      · simp only [hcm', ↓reduceIte]
        exact ⟨wd2, wm2, wsl2, wsm2⟩
      · simp only [hcm', ↓reduceIte]
        rcases bd1 c (by omega) with ⟨b1, b2, b3, b4⟩
        exact ⟨by omega, fun v => by have := b2 v; omega,
          fun k => by have := b3 k; omega, fun k v => by have := b4 k v; omega⟩
    · intro table
      dsimp only
      intro c hc
      set inputs := List.ofFn (fun a : Fin I =>
        table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun inputBit => a.val.testBit inputBit.val))
      have hlen : inputs.length = I := List.length_ofFn
      change wireVal r2.1 inputs (if c.val = m then r2.2.1 else r1.2.dead c) = _ ∧
        (∀ v, wireVal r2.1 inputs ((if c.val = m then r2.2.2.1 else r1.2.mask c) v) = _) ∧
        (∀ k, wireVal r2.1 inputs ((if c.val = m then r2.2.2.2.1 else r1.2.slotLive c) k) = _) ∧
        (∀ k v, wireVal r2.1 inputs ((if c.val = m then r2.2.2.2.2 else r1.2.slotMask c) k v) = _)
      by_cases hcm' : c.val = m
      · simp only [hcm', ↓reduceIte]
        have hceq : c = st := Fin.ext hcm'
        subst hceq
        exact val2 table
      · simp only [hcm', ↓reduceIte]
        rcases bd1 c (by omega) with ⟨b1, b2, b3, b4⟩
        rcases val1 table c (by omega) with ⟨v1d, v1m, v1l, v1sm⟩
        exact ⟨by rw [wireVal_of_extends e2 inputs hlen _ b1, v1d],
          fun v => by rw [wireVal_of_extends e2 inputs hlen _ (b2 v), v1m v],
          fun k => by rw [wireVal_of_extends e2 inputs hlen _ (b3 k), v1l k],
          fun k v => by rw [wireVal_of_extends e2 inputs hlen _ (b4 k v), v1sm k v]⟩

def buildAllStages {n w : ℕ} (hn : 0 < n) (w0 : ℕ) (gs : List Gate) :
    (d : ℕ) → d ≤ n →
      List Gate × (Fin (4 ^ w) → ℕ) × (Fin (4 ^ w) → Fin n → ℕ) ×
        (Fin n → Fin (4 ^ w) → Fin 3 → ℕ) × (Fin n → Fin (4 ^ w) → Fin 3 → Fin n → ℕ)
  | 0, _ => (gs, fun _ => w0, fun _ _ => w0, fun _ _ _ => w0, fun _ _ _ _ => w0)
  | d + 1, hd =>
    let r1 := buildAllStages hn w0 gs d (by omega)
    let t : Fin n := ⟨n - 1 - d, by omega⟩
    let r2 := buildStageLoop hn t w0 r1.2.1 r1.2.2.1 r1.1 (4 ^ w) le_rfl
    (r2.1, r2.2.dead, r2.2.mask,
      fun t' => if t'.val = t.val then r2.2.slotLive else r1.2.2.2.1 t',
      fun t' => if t'.val = t.val then r2.2.slotMask else r1.2.2.2.2 t')

def sumStarts (n w : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => sumStarts n w d + (startsAt n w (n - 1 - d)).length

lemma sumStarts_eq_card_filter (n w : ℕ) (d : ℕ) (hd : d ≤ n) :
    sumStarts n w d = ((List.finRange n).filter (fun s => decide (n - d ≤ maxPos n w s))).length := by
  induction d with
  | zero =>
    unfold sumStarts
    have hemp : (List.finRange n).filter (fun s => decide (n - 0 ≤ maxPos n w s)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro s _
      simp only [Nat.sub_zero, decide_eq_true_eq, not_le]
      exact maxPos_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt) s
    rw [hemp]; rfl
  | succ d ih =>
    unfold sumStarts
    rw [ih (by omega)]
    have hpart : ∀ l : List (Fin n),
        (l.filter (fun s => decide (n - d ≤ maxPos n w s))).length +
        (l.filter (fun s => decide (maxPos n w s = n - 1 - d))).length =
        (l.filter (fun s => decide (n - (d + 1) ≤ maxPos n w s))).length := by
      intro l
      induction l with
      | nil => simp
      | cons a rest ihr =>
        simp only [List.filter_cons]
        by_cases h1 : n - d ≤ maxPos n w a
        · have h2 : maxPos n w a ≠ n - 1 - d := by omega
          have h3 : n - (d + 1) ≤ maxPos n w a := by omega
          rw [decide_eq_true h1, decide_eq_false h2, decide_eq_true h3]
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
          omega
        · by_cases h2 : maxPos n w a = n - 1 - d
          · have h3 : n - (d + 1) ≤ maxPos n w a := by omega
            rw [decide_eq_false h1, decide_eq_true h2, decide_eq_true h3]
            simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
            omega
          · have h3 : ¬(n - (d + 1) ≤ maxPos n w a) := by omega
            rw [decide_eq_false h1, decide_eq_false h2, decide_eq_false h3]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ihr
    exact hpart (List.finRange n)

lemma sumStarts_n_le (n w : ℕ) : sumStarts n w n ≤ n := by
  rw [sumStarts_eq_card_filter n w n le_rfl]
  calc ((List.finRange n).filter _).length ≤ (List.finRange n).length := List.length_filter_le _ _
    _ = n := List.length_finRange

lemma buildAllStages_spec {n w : ℕ} (hn : 0 < n) (w0 : ℕ) (gs : List Gate)
    (hv : Valid (n * 2 ^ (w + 1)) gs)
    (hw0 : w0 < n * 2 ^ (w + 1) + gs.length)
    (hv0 : ∀ x : List Bool, x.length = n * 2 ^ (w + 1) → wireVal gs x w0 = false) :
    ∀ (d : ℕ) (hd : d ≤ n),
      let I := n * 2 ^ (w + 1)
      let r := buildAllStages hn w0 gs d hd
      Valid I r.1 ∧ Extends gs r.1 ∧
      r.1.length ≤ gs.length + 4 ^ w * (2 * sumStarts n w d * (n + 4) + d * (7 * n + 9)) ∧
      (∀ c, r.2.1 c < I + r.1.length) ∧
      (∀ c v, r.2.2.1 c v < I + r.1.length) ∧
      (∀ t c k, r.2.2.2.1 t c k < I + r.1.length) ∧
      (∀ t c k v, r.2.2.2.2 t c k v < I + r.1.length) ∧
      (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
        let inputs := List.ofFn (fun a : Fin I =>
          table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
            (fun inputBit => a.val.testBit inputBit.val))
        (∀ c, wireVal r.1 inputs (r.2.1 c) = (dpStage hn table (n - d)).dead c ∧
          ∀ v, wireVal r.1 inputs (r.2.2.1 c v) = (dpStage hn table (n - d)).mask c v) ∧
        (∀ t : Fin n, n - d ≤ t.val → ∀ c k,
          wireVal r.1 inputs (r.2.2.2.1 t c k) = semSlotLive hn table t c k ∧
          ∀ v, wireVal r.1 inputs (r.2.2.2.2 t c k v) = semSlotMask hn table t c k v)) := by
  set I := n * 2 ^ (w + 1)
  intro d hd
  induction d with
  | zero =>
    refine ⟨hv, extends_rfl gs, by simp [buildAllStages, sumStarts],
      fun _ => hw0, fun _ _ => hw0, fun _ _ _ => hw0, fun _ _ _ _ => hw0, ?_⟩
    intro table
    set inputs := List.ofFn (fun a : Fin I =>
      table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
        (fun inputBit => a.val.testBit inputBit.val))
    have hlen : inputs.length = I := List.length_ofFn
    refine ⟨fun c => ⟨?_, fun v => ?_⟩, fun t ht => by omega⟩
    · simp only [buildAllStages, dpStage, Nat.sub_zero, Nat.sub_self, dpFrom]
      exact hv0 inputs hlen
    · simp only [buildAllStages, dpStage, Nat.sub_zero, Nat.sub_self, dpFrom]
      exact hv0 inputs hlen
  | succ d ih =>
    rcases ih (by omega) with ⟨v1, e1, l1, bd1d, bd1m, bd1l, bd1sm, val1⟩
    set r1 := buildAllStages hn w0 gs d (by omega) with hr1
    have hlen1 : gs.length ≤ r1.1.length := extends_len e1
    set t : Fin n := ⟨n - 1 - d, by omega⟩
    have htp1 : t.val + 1 = n - d := by dsimp [t]; omega
    set r2 := buildStageLoop hn t w0 r1.2.1 r1.2.2.1 r1.1 (4 ^ w) le_rfl with hr2
    have h2 := buildStageLoop_spec hn t w0 r1.2.1 r1.2.2.1 r1.1 v1 (by omega)
      (fun x hx => by rw [wireVal_of_extends e1 x hx w0 hw0, hv0 x hx])
      bd1d bd1m
      (fun table c => by rw [htp1]; exact (val1 table).1 c) (4 ^ w) le_rfl
    dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨v2, e2, l2, bd2, val2⟩
    have hlen2 : r1.1.length ≤ r2.1.length := extends_len e2
    refine ⟨v2, extends_trans e1 e2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change r2.1.length ≤ gs.length + 4 ^ w * (2 * sumStarts n w (d + 1) * (n + 4) + (d + 1) * (7 * n + 9))
      have hss : sumStarts n w (d + 1) = sumStarts n w d + (startsAt n w t.val).length := rfl
      rw [hss]
      have hmul : 4 ^ w * (2 * (sumStarts n w d + (startsAt n w t.val).length) * (n + 4) +
          (d + 1) * (7 * n + 9)) =
          4 ^ w * (2 * sumStarts n w d * (n + 4) + d * (7 * n + 9)) +
          4 ^ w * (2 * (startsAt n w t.val).length * (n + 4) + 7 * n + 9) := by ring
      omega
    · intro c; exact (bd2 c c.isLt).1
    · intro c v; exact (bd2 c c.isLt).2.1 v
    · intro t' c k
      change (if t'.val = t.val then r2.2.slotLive else r1.2.2.2.1 t') c k < I + r2.1.length
      by_cases ht' : t'.val = t.val
      · simp only [ht', ↓reduceIte]; exact (bd2 c c.isLt).2.2.1 k
      · simp only [ht', ↓reduceIte]; have := bd1l t' c k; omega
    · intro t' c k v
      change (if t'.val = t.val then r2.2.slotMask else r1.2.2.2.2 t') c k v < I + r2.1.length
      by_cases ht' : t'.val = t.val
      · simp only [ht', ↓reduceIte]; exact (bd2 c c.isLt).2.2.2 k v
      · simp only [ht', ↓reduceIte]; have := bd1sm t' c k v; omega
    · intro table
      set inputs := List.ofFn (fun a : Fin I =>
        table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun inputBit => a.val.testBit inputBit.val))
      have hlen : inputs.length = I := List.length_ofFn
      have hteq : n - (d + 1) = t.val := by dsimp [t]; omega
      refine ⟨fun c => ?_, fun t' ht' c k => ?_⟩
      · rw [hteq]
        exact ⟨(val2 table c c.isLt).1, (val2 table c c.isLt).2.1⟩
      · change wireVal r2.1 inputs ((if t'.val = t.val then r2.2.slotLive else r1.2.2.2.1 t') c k) = _ ∧
          ∀ v, wireVal r2.1 inputs ((if t'.val = t.val then r2.2.slotMask else r1.2.2.2.2 t') c k v) = _
        by_cases ht'' : t'.val = t.val
        · have ht'eq : t' = t := Fin.ext ht''
          subst ht'eq
          simp only [↓reduceIte]
          exact ⟨(val2 table c c.isLt).2.2.1 k, (val2 table c c.isLt).2.2.2 k⟩
        · simp only [ht'', ↓reduceIte]
          have hgt : n - d ≤ t'.val := by dsimp [t] at ht''; omega
          rcases (val1 table).2 t' hgt c k with ⟨vl, vsm⟩
          exact ⟨by rw [wireVal_of_extends e2 inputs hlen _ (bd1l t' c k), vl],
            fun v => by rw [wireVal_of_extends e2 inputs hlen _ (bd1sm t' c k v), vsm v]⟩

end PEqualNP.Outside.L_pcx_208_aux

theorem PEqualNP.Outside.L_pcx_208 : (∀ (n w : ℕ) (hn : 0 < n),
  let I := n * 2 ^ (w + 1)
  let S := 3 * n * 4 ^ w
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
    (live : Fin S → ℕ)
    (memberWire : Fin S → PEqualNP.ProofComplexity.Literal (Fin n) → ℕ),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
    C.size ≤ 200 * (n + 1) ^ 2 * 4 ^ w ∧
    C.output < I + C.size ∧ (∀ s, live s < I + C.size) ∧
    (∀ s l, memberWire s l < I + C.size) ∧
    ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let pos := fun (start : Fin n) (offset : Fin (w + 1)) =>
        (⟨(start.val + offset.val) % n, Nat.mod_lt _ hn⟩ : Fin n)
      let inputs := List.ofFn (fun a : Fin I =>
        table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun inputBit => a.val.testBit inputBit.val))
      let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) :=
        {D | ∃ (i : Fin n) (p : Fin (w + 1) → Bool), table i p = false ∧
          D = Finset.univ.image (fun clauseBit : Fin (w + 1) => (pos i clauseBit, !(p clauseBit)))}
      let bit := fun wire : ℕ => (C.wires inputs).getD wire false
      let lines := ((List.finRange S).filter (fun s => bit (live s))).map
        (fun s => Finset.univ.filter (fun l => bit (memberWire s l) = true))
      (C.eval inputs = true ↔ ¬ PEqualNP.ProofComplexity.Satisfiable F) ∧
        (C.eval inputs = true →
          PEqualNP.ProofComplexity.IsRefutation F lines ∧
          ∀ D ∈ lines, D.card ≤ 2 * w + 1)) := by
  intro n w hn
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_208_aux in
  set I := n * 2 ^ (w + 1)
  set S := 3 * n * 4 ^ w
  have hv0 : Valid I [] := ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
  set r0 := addConst0 I [] with hr0
  have h0 := addConst0_spec hv0
  dsimp only at h0; rw [← hr0] at h0
  rcases h0 with ⟨v0, e0, l0, w0lt, val0⟩
  set rAll := buildAllStages hn r0.2 r0.1 n le_rfl with hrAll
  have hAll := buildAllStages_spec hn r0.2 r0.1 v0 w0lt val0 n le_rfl
  dsimp only at hAll; rw [← hrAll] at hAll
  rcases hAll with ⟨vAll, eAll, lAll, bdD, _, bdL, bdSM, valAll⟩
  have hlenAll : r0.1.length ≤ rAll.1.length := extends_len eAll
  have h4pos : 0 < 4 ^ w := Nat.pos_of_ne_zero (by positivity)
  let rootSt : Fin (4 ^ w) := ⟨0, h4pos⟩
  let C : Circuit := ⟨rAll.1, rAll.2.1 rootSt⟩
  let live : Fin S → ℕ := fun s =>
    let (t, st, kind) := decodeSlot hn s
    rAll.2.2.2.1 t st kind
  let memberWire : Fin S → Literal (Fin n) → ℕ := fun s l =>
    let (t, st, kind) := decodeSlot hn s
    if l.2 = slotPol t st kind l.1 then rAll.2.2.2.2 t st kind l.1 else r0.2
  refine ⟨C, live, memberWire, vAll.1, vAll.2, ?_, bdD rootSt, ?_, ?_, ?_⟩
  · change rAll.1.length ≤ 200 * (n + 1) ^ 2 * 4 ^ w
    have hsum : sumStarts n w n ≤ n := sumStarts_n_le n w
    have hle1 : 2 * sumStarts n w n * (n + 4) ≤ 2 * n * (n + 4) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hsum)
    have hle2 : 1 + 4 ^ w * (2 * n * (n + 4) + n * (7 * n + 9)) ≤ 200 * (n + 1) ^ 2 * 4 ^ w := by
      have h1 : 1 ≤ 4 ^ w := h4pos
      have hcoef : 1 + (2 * n * (n + 4) + n * (7 * n + 9)) ≤ 200 * (n + 1) ^ 2 := by
        nlinarith
      calc 1 + 4 ^ w * (2 * n * (n + 4) + n * (7 * n + 9))
          ≤ 4 ^ w + 4 ^ w * (2 * n * (n + 4) + n * (7 * n + 9)) := by omega
        _ = (1 + (2 * n * (n + 4) + n * (7 * n + 9))) * 4 ^ w := by ring
        _ ≤ 200 * (n + 1) ^ 2 * 4 ^ w := Nat.mul_le_mul_right _ hcoef
    simp only [List.length_nil] at l0
    have hle3 : 4 ^ w * (2 * sumStarts n w n * (n + 4) + n * (7 * n + 9)) ≤
        4 ^ w * (2 * n * (n + 4) + n * (7 * n + 9)) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · intro s
    dsimp only [live]
    exact bdL _ _ _
  · intro s l
    dsimp only [memberWire]
    split_ifs
    · exact bdSM _ _ _ _
    · change r0.2 < I + rAll.1.length
      exact lt_of_lt_of_le w0lt (by omega)
  · intro table
    set inputs := List.ofFn (fun a : Fin I =>
      table ⟨(a.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
        (fun inputBit => a.val.testBit inputBit.val))
    have hlen : inputs.length = I := List.length_ofFn
    set F : Set (Clause (Fin n)) :=
      {D | ∃ (i : Fin n) (p : Fin (w + 1) → Bool), table i p = false ∧
        D = Finset.univ.image (fun clauseBit : Fin (w + 1) => (posOf hn i clauseBit, !(p clauseBit)))}
    rcases valAll table with ⟨hvalD, hvalSlot⟩
    have heval : C.eval inputs = (dpStage hn table 0).dead rootSt := by
      change wireVal rAll.1 inputs (rAll.2.1 rootSt) = _
      simpa [Nat.sub_self] using (hvalD rootSt).1
    have hliveEq : ∀ s : Fin S, (C.wires inputs).getD (live s) false = semLive hn table s := by
      intro s
      change wireVal rAll.1 inputs (live s) = semLive hn table s
      unfold live semLive
      rcases hd : decodeSlot hn s with ⟨t, st, kind⟩
      exact (hvalSlot t (by omega) st kind).1
    have hmemEq : ∀ s : Fin S, ∀ l : Literal (Fin n),
        (C.wires inputs).getD (memberWire s l) false = semMember hn table s l := by
      intro s l
      change wireVal rAll.1 inputs (memberWire s l) = semMember hn table s l
      unfold memberWire semMember
      rcases hd : decodeSlot hn s with ⟨t, st, kind⟩
      by_cases hpol : l.2 = slotPol t st kind l.1
      · simp only [hpol, ↓reduceIte, beq_self_eq_true, Bool.and_true]
        exact (hvalSlot t (by omega) st kind).2 l.1
      · simp only [hpol, ↓reduceIte, beq_eq_false_iff_ne.mpr hpol, Bool.and_false]
        rw [wireVal_of_extends eAll inputs hlen r0.2 w0lt, val0 inputs hlen]
    have hlinesEq :
        ((List.finRange S).filter (fun s => (C.wires inputs).getD (live s) false)).map
          (fun s => Finset.univ.filter (fun l => (C.wires inputs).getD (memberWire s l) false = true)) =
        ((List.finRange S).filter (semLive hn table)).map (semClause hn table) := by
      have hf : (fun s => (C.wires inputs).getD (live s) false) = semLive hn table := funext hliveEq
      rw [hf]
      apply List.map_congr_left
      intro s _
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, semClause]
      rw [hmemEq s l]
    have hrefOfTrue : C.eval inputs = true →
        IsRefutation F (((List.finRange S).filter (semLive hn table)).map (semClause hn table)) ∧
        ∀ D ∈ ((List.finRange S).filter (semLive hn table)).map (semClause hn table),
          D.card ≤ 2 * w + 1 := by
      intro htr
      rw [heval] at htr
      rcases dpStage_sound_and_witness hn table n le_rfl with ⟨hSt0, hSlot0⟩
      rw [Nat.sub_self] at hSt0 hSlot0
      rcases hSt0 rootSt with ⟨hact0, hwit0⟩
      rcases hwit0 htr with ⟨s0, _, hs0live, hs0cl⟩
      have hempty : semClause hn table s0 = ∅ := by
        rw [hs0cl]
        ext ⟨v, pol⟩
        simp only [mem_clauseFromMask, Finset.notMem_empty, iff_false, not_and]
        intro hm
        rcases hact0 v hm with ⟨hlt, _⟩
        omega
      have hder : IsDerivation F (((List.finRange S).filter (semLive hn table)).map (semClause hn table)) := by
        apply isDerivation_of_suffix
        intro s rest hsuf hsl
        rcases (hSlot0 s (by omega) hsl).2 with hax | ⟨s1, s2, h1, h2, hl1, hl2, hres⟩
        · exact Or.inl hax
        · exact Or.inr ⟨s1, mem_suffix_finRange_of_lt hsuf h1,
            s2, mem_suffix_finRange_of_lt hsuf h2, hl1, hl2, hres⟩
      have hmemEmpty : (∅ : Clause (Fin n)) ∈
          ((List.finRange S).filter (semLive hn table)).map (semClause hn table) := by
        rw [← hempty]
        exact List.mem_map.mpr ⟨s0, List.mem_filter.mpr ⟨List.mem_finRange s0, hs0live⟩, rfl⟩
      refine ⟨⟨hder, hmemEmpty⟩, ?_⟩
      intro D hD
      rcases List.mem_map.mp hD with ⟨s, hs, rfl⟩
      exact (hSlot0 s (by omega) (List.mem_filter.mp hs).2).1
    refine ⟨?_, ?_⟩
    · constructor
      · intro htr
        exact refutation_unsat (hrefOfTrue htr).1
      · intro hunsat
        by_contra hnt
        have hff : (dpStage hn table 0).dead rootSt = false := by
          rw [← heval]
          cases h : C.eval inputs <;> simp_all
        exact hunsat (dpDead_zero_false_sat hn table hff)
    · intro htr
      rw [hlinesEq]
      exact hrefOfTrue htr

import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25582

namespace PEqualNP.Outside.L_meta_25628_aux

open PEqualNP.Outside.L_meta_25582_aux

private def pubF (k rowName : ℕ) (constants : ℕ → Fin (2 ^ k)) (t : ℕ) (z : ℤ) : Bool :=
  xor (pz k rowName (z + 1 - 2 * ((t - 1 : ℕ) : ℤ))) (pz k (constants t).val z)

private def startClip (k cutSite period : ℕ) (site : ℤ) : Bool :=
  if site < (cutSite : ℤ) then pz k period site else false

private def clippedZ (k r q iVal cutSite rowName : ℕ) (constants : ℕ → Fin (2 ^ k)) (period : ℕ) : ℕ :=
  (List.range q).foldl (fun (total j : ℕ) =>
    total ||| ((stZ (pubF k rowName constants) (startClip k cutSite period) r ((iVal : ℤ) + (j : ℤ))).toNat <<< j)) 0

private def mateF (k r iVal word : ℕ) : ℕ :=
  word ^^^ (1 <<< ((iVal + k + 2 - 2 * r) % k))

private def piF (k rowName raw : ℕ) : ℕ :=
  rotF k 1 raw ^^^ rowName

private def visOutF (k r q iVal rowName : ℕ) (constants : ℕ → Fin (2 ^ k)) (raw : ℕ) : ℕ :=
  (List.range q).foldl (fun out bitNo =>
    out ||| (((st k rowName (fun j => (constants j).val) raw r).testBit ((iVal + bitNo) % k)).toNat <<< bitNo)) 0

private def traceWeightF (k cutSite rowName : ℕ) (constants : ℕ → Fin (2 ^ k)) (raw m : ℕ) : ℕ :=
  (List.range m).foldl (fun (ones tickNo : ℕ) =>
    let now := 5 + tickNo
    let pos := cutSite + k - 3 * now + ones
    let layer := st k rowName (fun j => (constants j).val) raw (now - 1)
    ones + (xor (xor (layer.testBit (pos % k)) (layer.testBit ((pos + 1) % k)))
                 (layer.testBit ((pos + 2) % k))).toNat) 0

private def tracePairF (k cutSite rowName : ℕ) (constants : ℕ → Fin (2 ^ k)) (raw : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | m + 1 =>
    let p := tracePairF k cutSite rowName constants raw m
    let now := 5 + m
    let pos := cutSite + k - 3 * now + p.1
    let layer := st k rowName (fun j => (constants j).val) raw (now - 1)
    let b := xor (xor (layer.testBit (pos % k)) (layer.testBit ((pos + 1) % k)))
                 (layer.testBit ((pos + 2) % k))
    (p.1 + b.toNat, p.2 ||| (b.toNat <<< m))

private lemma testBit_clippedZ (k r q iVal cutSite rowName : ℕ) (constants : ℕ → Fin (2 ^ k))
    (period j : ℕ) :
    (clippedZ k r q iVal cutSite rowName constants period).testBit j =
      (decide (j < q) && stZ (pubF k rowName constants) (startClip k cutSite period) r ((iVal : ℤ) + (j : ℤ))) :=
  testBit_foldl_or _ q j

private lemma clippedZ_lt (k r q iVal cutSite rowName : ℕ) (constants : ℕ → Fin (2 ^ k))
    (period : ℕ) :
    clippedZ k r q iVal cutSite rowName constants period < 2 ^ q :=
  Nat.lt_pow_two_of_testBit _ fun j hj => by
    rw [testBit_clippedZ]; simp [show ¬ j < q by omega]

private lemma testBit_visOutF (k r q iVal rowName : ℕ) (constants : ℕ → Fin (2 ^ k))
    (raw j : ℕ) :
    (visOutF k r q iVal rowName constants raw).testBit j =
      (decide (j < q) && (st k rowName (fun j => (constants j).val) raw r).testBit ((iVal + j) % k)) :=
  testBit_foldl_or _ q j

private lemma visOutF_lt (k r q iVal rowName : ℕ) (constants : ℕ → Fin (2 ^ k)) (raw : ℕ) :
    visOutF k r q iVal rowName constants raw < 2 ^ q :=
  Nat.lt_pow_two_of_testBit _ fun j hj => by
    rw [testBit_visOutF]; simp [show ¬ j < q by omega]

private lemma finalTape_eq_stZ (k rowName : ℕ) (constants : ℕ → Fin (2 ^ k))
    (start : ℤ → Bool) (rounds : ℕ) :
    let residue := fun (place : ℤ) => (place % (k : ℤ)).toNat
    let mix := fun (tape : ℤ → Bool) (atSite : ℤ) =>
      xor (xor (tape (atSite - 1)) (tape atSite)) (tape (atSite + 1))
    (List.range rounds).foldl (fun (previous : ℤ → Bool) (tick : ℕ) (z : ℤ) =>
      let p := z + 1 - 2 * (tick : ℤ)
      let ordinary := xor (mix previous z) (!(mix previous (z + 1)) && mix previous (z + 2))
      xor (xor (xor ordinary (start p)) (rowName.testBit (residue p)))
        ((constants (tick + 1)).val.testBit (residue z))) start =
      stZ (pubF k rowName constants) start rounds := by
  intro residue mix
  induction rounds with
  | zero => rfl
  | succ t ih =>
    rw [fold_succ, ih]
    funext z
    rw [stZ_succ]
    have hmix : ∀ (f : ℤ → Bool) (a : ℤ), mix f a = mixZ f a := fun f a => by
      simp only [mix, mixZ, Bool.xor_comm (f (a - 1)) (f a)]
    have hord : xor (mix (stZ (pubF k rowName constants) start t) z)
        (!(mix (stZ (pubF k rowName constants) start t) (z + 1)) &&
          mix (stZ (pubF k rowName constants) start t) (z + 2)) =
        befZ (stZ (pubF k rowName constants) start t) z := by
      simp only [befZ, hmix]
    rw [hord]
    simp only [pubF, pz, residue, Nat.add_sub_cancel, Bool.xor_assoc]

private lemma pz_st_eq_stZ {k rowName : ℕ} (hk : 0 < k) (hrow : rowName < 2 ^ k)
    (constants : ℕ → Fin (2 ^ k)) {raw : ℕ} (hraw : raw < 2 ^ k) (rounds : ℕ) (z : ℤ) :
    pz k (st k rowName (fun j => (constants j).val) raw rounds) z =
      stZ (pubF k rowName constants) (pz k (piF k rowName raw)) rounds z := by
  induction rounds generalizing z with
  | zero => rfl
  | succ t ih =>
    rw [pz_st_succ hk hraw, stZ_succ]
    have hst_lt : st k rowName (fun j => (constants j).val) raw t < 2 ^ k :=
      st_lt hrow (fun j => (constants j).isLt) raw t
    have hpre : pz k (preF k (st k rowName (fun j => (constants j).val) raw t)) z =
        befZ (stZ (pubF k rowName constants) (pz k (piF k rowName raw)) t) z := by
      rw [pz_preF hk hst_lt, befZ_eq, ih, ih, ih, ih, ih]
    have hkey : pz k raw (z - ((2 * t : ℕ) : ℤ)) =
        xor (pz k (piF k rowName raw) (z + 1 - 2 * (t : ℤ)))
            (pz k rowName (z + 1 - 2 * (t : ℤ))) := by
      unfold piF
      rw [pz_xor, pz_rotF hk hraw]
      have hsub : z + 1 - 2 * (t : ℤ) - ((1 : ℕ) : ℤ) = z - ((2 * t : ℕ) : ℤ) := by push_cast; ring
      rw [hsub, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    rw [hpre, hkey]
    simp only [pubF, Nat.add_sub_cancel, Bool.xor_assoc]

private lemma piF_lt {k rowName : ℕ} (hrow : rowName < 2 ^ k) (raw : ℕ) :
    piF k rowName raw < 2 ^ k :=
  Nat.xor_lt_two_pow (rotF_lt k 1 raw) hrow

private lemma rotF_inv_one {k x : ℕ} (hk : 0 < k) (hx : x < 2 ^ k) :
    rotF k 1 (rotF k (k - 1) x) = x := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < k
  · rw [← pz_lt k _ b hb, ← pz_lt k _ b hb, pz_rot1 hk _ (rotF_lt _ _ _), pz_rotkm1 hk _ hx]
    have : (b : ℤ) + -1 + 1 = (b : ℤ) := by ring
    rw [this]
  · rw [big_false (rotF_lt _ _ _) (by omega), big_false hx (by omega)]

private lemma rotF_one_inv {k x : ℕ} (hk : 0 < k) (hx : x < 2 ^ k) :
    rotF k (k - 1) (rotF k 1 x) = x := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < k
  · rw [← pz_lt k _ b hb, ← pz_lt k _ b hb, pz_rotkm1 hk _ (rotF_lt _ _ _), pz_rot1 hk _ hx]
    have : (b : ℤ) + 1 + -1 = (b : ℤ) := by ring
    rw [this]
  · rw [big_false (rotF_lt _ _ _) (by omega), big_false hx (by omega)]

private def piEquiv {k rowName : ℕ} (hk : 0 < k) (hrow : rowName < 2 ^ k) :
    Fin (2 ^ k) ≃ Fin (2 ^ k) where
  toFun raw := ⟨piF k rowName raw.val, piF_lt hrow raw.val⟩
  invFun w := ⟨rotF k (k - 1) (w.val ^^^ rowName), rotF_lt _ _ _⟩
  left_inv raw := Fin.ext <| by
    show rotF k (k - 1) ((rotF k 1 raw.val ^^^ rowName) ^^^ rowName) = raw.val
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    exact rotF_one_inv hk raw.isLt
  right_inv w := Fin.ext <| by
    show rotF k 1 (rotF k (k - 1) (w.val ^^^ rowName)) ^^^ rowName = w.val
    rw [rotF_inv_one hk (Nat.xor_lt_two_pow w.isLt hrow), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

private lemma mateF_lt {k r iVal word : ℕ} (hk : 0 < k) (hw : word < 2 ^ k) :
    mateF k r iVal word < 2 ^ k := by
  unfold mateF
  apply Nat.xor_lt_two_pow hw
  rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt _ hk)

private lemma mateF_invol (k r iVal word : ℕ) :
    mateF k r iVal (mateF k r iVal word) = word := by
  unfold mateF
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

private lemma mateF_ne {k r iVal word : ℕ} (_hk : 0 < k) :
    mateF k r iVal word ≠ word := by
  intro h
  set p := (iVal + k + 2 - 2 * r) % k with hpdef
  have hbit := congrArg (fun x => x.testBit p) h
  simp only [mateF, ← hpdef, Nat.testBit_xor, Nat.testBit_shiftLeft, ge_iff_le, le_refl,
    decide_true, Nat.sub_self, Bool.true_and] at hbit
  change xor (word.testBit p) true = word.testBit p at hbit
  cases word.testBit p <;> simp at hbit

private lemma one_shiftLeft_eq_rotF {k p : ℕ} (hp : p < k) :
    1 <<< p = rotF k p 1 := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < k
  · rw [testBit_rotF (show 1 < 2 ^ k from Nat.one_lt_two_pow (by omega)) hb]
    rw [Nat.mod_eq_of_lt hp, Nat.testBit_shiftLeft]
    by_cases hbp : b = p
    · subst hbp
      simp
    · have hne0 : (b + k - p) % k ≠ 0 := by
        intro hz
        by_cases hle : p ≤ b
        · have : (b + k - p) % k = b - p := by
            rw [show b + k - p = (b - p) + k by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)]
          omega
        · have : (b + k - p) % k = b + k - p := Nat.mod_eq_of_lt (by omega)
          omega
      have hbf : (1 : ℕ).testBit ((b + k - p) % k) = false :=
        big_false (show (1 : ℕ) < 2 ^ 1 by norm_num) (by omega)
      rw [hbf]
      by_cases hle : p ≤ b
      · have hbf2 : (1 : ℕ).testBit (b - p) = false :=
          big_false (show (1 : ℕ) < 2 ^ 1 by norm_num) (by omega)
        simp [hle, hbf2]
      · simp [hle]
  · rw [big_false (rotF_lt _ _ _) (by omega)]
    rw [Nat.testBit_shiftLeft]
    by_cases hle : p ≤ b
    · have hbf2 : (1 : ℕ).testBit (b - p) = false :=
        big_false (show (1 : ℕ) < 2 ^ 1 by norm_num) (by omega)
      simp [hle, hbf2]
    · simp [hle]

private lemma piF_mateF {k r iVal rowName raw : ℕ} (hk : 0 < k) (h2rk : 2 * r ≤ iVal + k + 2)
    (hrow : rowName < 2 ^ k) (hraw : raw < 2 ^ k) :
    piF k rowName (mateF k r iVal raw) =
      flipK k ((iVal + k + 3 - 2 * r : ℕ) : ℤ) (piF k rowName raw) := by
  have hm_lt : mateF k r iVal raw < 2 ^ k := mateF_lt hk hraw
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < k
  · rw [← pz_lt k _ b hb, ← pz_lt k _ b hb]
    unfold piF
    rw [pz_xor, pz_rotF hk hm_lt, pz_flipK hk, pz_xor, pz_rotF hk hraw]
    unfold mateF
    rw [pz_xor]
    set p := (iVal + k + 2 - 2 * r) % k
    have hp : p < k := Nat.mod_lt _ hk
    rw [one_shiftLeft_eq_rotF hp, pz_rotF hk (Nat.one_lt_two_pow (by omega))]
    have hmod : ((b : ℤ) - ((1 : ℕ) : ℤ) - (p : ℤ)) ≡
        ((b : ℤ) - ((iVal + k + 3 - 2 * r : ℕ) : ℤ)) [ZMOD (k : ℤ)] := by
      have hpmod : ((p : ℕ) : ℤ) ≡ ((iVal + k + 2 - 2 * r : ℕ) : ℤ) [ZMOD (k : ℤ)] := by
        simpa [p, Int.natCast_mod] using Int.mod_modEq ((iVal + k + 2 - 2 * r : ℕ) : ℤ) (k : ℤ)
      have hsucc : ((iVal + k + 3 - 2 * r : ℕ) : ℤ) = ((iVal + k + 2 - 2 * r : ℕ) : ℤ) + 1 := by
        omega
      rw [hsucc]
      have := (hpmod.neg.add_left ((b : ℤ) - 1))
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
    rw [pz_modEq hmod]
    cases pz k raw ((b : ℤ) - ((1 : ℕ) : ℤ)) <;> cases pz k 1 ((b : ℤ) - ((iVal + k + 3 - 2 * r : ℕ) : ℤ)) <;>
      cases pz k rowName (b : ℤ) <;> rfl
  · rw [big_false (piF_lt hrow _) (by omega),
        big_false (flipK_lt hk _ (piF_lt hrow _)) (by omega)]

private lemma startClip_flip_off {k cutSite w : ℕ} (hk : 0 < k) (l y : ℤ)
    (hl : l < y) (hy : y < l + k) :
    startClip k cutSite (flipK k l w) y = startClip k cutSite w y := by
  unfold startClip
  split_ifs
  · exact pz_flipK_off hk l w y (by omega) (by omega)
  · rfl

private lemma clippedZ_flip_cut {k r q iVal rowName : ℕ} (constants : ℕ → Fin (2 ^ k))
    (hq : 0 < q) (hr : 4 ≤ r) (hqk : q < k) (h2rk : 2 * r ≤ iVal + k + 3) (w : ℕ) :
    let cutSite := iVal + k + 3 - 2 * r
    clippedZ k r q iVal cutSite rowName constants (flipK k (cutSite : ℤ) w) =
      clippedZ k r q iVal cutSite rowName constants w ^^^ 1 := by
  intro cutSite
  have hk : 0 < k := by omega
  have hcutZ : (cutSite : ℤ) = (iVal : ℤ) + (k : ℤ) + 3 - 2 * (r : ℤ) := by
    dsimp only [cutSite]; omega
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hs3 : 3 ≤ s := by omega
  have hlo : loZ (s + 1) = 1 - 2 * (s : ℤ) := by unfold loZ; split_ifs <;> push_cast <;> omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_clippedZ, Nat.testBit_xor, testBit_clippedZ]
  by_cases hj : j < q
  · simp only [hj, decide_true, Bool.true_and]
    cases j with
    | zero =>
      change stZ (pubF k rowName constants) (startClip k cutSite (flipK k (cutSite : ℤ) w)) (s + 1)
          ((iVal : ℤ) + ((0 : ℕ) : ℤ)) =
        xor (stZ (pubF k rowName constants) (startClip k cutSite w) (s + 1)
          ((iVal : ℤ) + ((0 : ℕ) : ℤ))) true
      have hlead := zlead (pubF k rowName constants)
        (startClip k cutSite (flipK k (cutSite : ℤ) w)) (startClip k cutSite w) s hs3
        ((iVal : ℤ) + ((0 : ℕ) : ℤ)) (fun y hy1 _ => by
          unfold startClip
          split_ifs with hlt
          · have h1 : 1 ≤ (y + k) - (cutSite : ℤ) := by rw [hlo] at hy1; omega
            have h2 : (y + k) - (cutSite : ℤ) < k := by omega
            rw [← pz_add_k k _ y, ← pz_add_k k w y]
            exact pz_flipK_off hk (cutSite : ℤ) w (y + k) h1 h2
          · rfl)
      have hpos : (iVal : ℤ) + ((0 : ℕ) : ℤ) + loZ (s + 1) = (cutSite : ℤ) - (k : ℤ) := by
        rw [hlo]; push_cast at hcutZ ⊢; omega
      rw [hpos] at hlead
      have hflip0 : startClip k cutSite (flipK k (cutSite : ℤ) w) ((cutSite : ℤ) - (k : ℤ)) =
          !startClip k cutSite w ((cutSite : ℤ) - (k : ℤ)) := by
        unfold startClip
        have hlt : (cutSite : ℤ) - (k : ℤ) < (cutSite : ℤ) := by omega
        simp only [hlt, ↓reduceIte, pz_sub_k, pz_flipK_on hk]
      rw [hflip0] at hlead
      revert hlead
      cases stZ (pubF k rowName constants) (startClip k cutSite (flipK k (cutSite : ℤ) w)) (s + 1)
          ((iVal : ℤ) + ((0 : ℕ) : ℤ)) <;>
      cases stZ (pubF k rowName constants) (startClip k cutSite w) (s + 1)
          ((iVal : ℤ) + ((0 : ℕ) : ℤ)) <;>
      cases startClip k cutSite w ((cutSite : ℤ) - (k : ℤ)) <;> simp
    | succ j' =>
      have h1b : (1 : ℕ).testBit (j' + 1) = false :=
        big_false (show (1 : ℕ) < 2 ^ 1 by norm_num) (by omega)
      rw [h1b, Bool.xor_false]
      apply zdep
      intro y hy1 _
      unfold startClip
      split_ifs with hlt
      · have h1 : 1 ≤ (y + k) - (cutSite : ℤ) := by rw [hlo] at hy1; push_cast at hcutZ hy1 ⊢; omega
        have h2 : (y + k) - (cutSite : ℤ) < k := by omega
        rw [← pz_add_k k _ y, ← pz_add_k k w y]
        exact pz_flipK_off hk (cutSite : ℤ) w (y + k) h1 h2
      · rfl
  · have h1b : (1 : ℕ).testBit j = false :=
      big_false (show (1 : ℕ) < 2 ^ 1 by norm_num) (by omega)
    simp [hj, h1b]

private lemma card_clippedZ_eq {k r q iVal rowName : ℕ} (constants : ℕ → Fin (2 ^ k))
    (hq : 0 < q) (hr : 4 ≤ r) (hqk : q < k) (h2rk : 2 * r ≤ iVal + k + 3) (y : Fin (2 ^ q)) :
    let cutSite := iVal + k + 3 - 2 * r
    ((Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun w => clippedZ k r q iVal cutSite rowName constants w.val = y.val)).card = 2 ^ (k - q) := by
  intro cutSite
  have hk : 0 < k := by omega
  have hcutZ : (cutSite : ℤ) = (iVal : ℤ) + (k : ℤ) + 3 - 2 * (r : ℤ) := by
    dsimp only [cutSite]; omega
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hs3 : 3 ≤ s := by omega
  have hlo : loZ (s + 1) = 1 - 2 * (s : ℤ) := by unfold loZ; split_ifs <;> push_cast <;> omega
  let C : ℕ → Fin (2 ^ k) → Bool := fun m w =>
    stZ (pubF k rowName constants) (startClip k cutSite w.val) (s + 1) ((iVal : ℤ) + ((q - 1 - m : ℕ) : ℤ))
  let σ : ℕ → Bool := fun m => y.val.testBit (q - 1 - m)
  let piv : ℕ → ℤ := fun m => (cutSite : ℤ) - (k : ℤ) + ((q - 1 - m : ℕ) : ℤ)
  let F : ℕ → Fin (2 ^ k) → Fin (2 ^ k) := fun m w =>
    ⟨flipK k (piv m) w.val, flipK_lt hk _ w.isLt⟩
  have hhalv := halving q C σ F
    (fun m _ w => Fin.ext (flipK_flipK k _ _))
    (fun m hm m' hm' w => by
      dsimp only [C, F]
      apply zdep
      intro z hz1 _
      unfold startClip
      split_ifs with hlt
      · apply pz_flipK_off hk (piv m) w.val z
        · dsimp only [piv]; rw [hlo] at hz1; push_cast at hcutZ hz1 ⊢; omega
        · dsimp only [piv]; omega
      · rfl)
    (fun m hm w => by
      dsimp only [C, F]
      have hlead := zlead (pubF k rowName constants)
        (startClip k cutSite (flipK k (piv m) w.val)) (startClip k cutSite w.val) s hs3
        ((iVal : ℤ) + ((q - 1 - m : ℕ) : ℤ)) (fun z hz1 _ => by
          unfold startClip
          split_ifs with hlt
          · apply pz_flipK_off hk (piv m) w.val z
            · dsimp only [piv]; rw [hlo] at hz1; push_cast at hcutZ hz1 ⊢; omega
            · dsimp only [piv]; omega
          · rfl)
      have hpos : (iVal : ℤ) + ((q - 1 - m : ℕ) : ℤ) + loZ (s + 1) = piv m := by
        dsimp only [piv]; rw [hlo]; push_cast at hcutZ ⊢; omega
      rw [hpos] at hlead
      have hflip : startClip k cutSite (flipK k (piv m) w.val) (piv m) =
          !startClip k cutSite w.val (piv m) := by
        unfold startClip
        have hlt : piv m < (cutSite : ℤ) := by dsimp only [piv]; omega
        simp only [hlt, ↓reduceIte, pz_flipK_on hk]
      rw [hflip] at hlead
      revert hlead
      cases stZ (pubF k rowName constants) (startClip k cutSite (flipK k (piv m) w.val)) (s + 1)
          ((iVal : ℤ) + ((q - 1 - m : ℕ) : ℤ)) <;>
      cases stZ (pubF k rowName constants) (startClip k cutSite w.val) (s + 1)
          ((iVal : ℤ) + ((q - 1 - m : ℕ) : ℤ)) <;>
      cases startClip k cutSite w.val (piv m) <;> simp)
    q le_rfl
  have hfilt : (Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun w => clippedZ k (s + 1) q iVal cutSite rowName constants w.val = y.val) =
      (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w => ∀ m, m < q → C m w = σ m) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h m hm
      have hbit := congrArg (fun x => x.testBit (q - 1 - m)) h
      rw [testBit_clippedZ] at hbit
      simpa [C, σ, show q - 1 - m < q by omega] using hbit
    · intro h
      apply Nat.eq_of_testBit_eq
      intro j
      rw [testBit_clippedZ]
      by_cases hj : j < q
      · simp only [hj, decide_true, Bool.true_and]
        have hm := h (q - 1 - j) (by omega)
        have hidx : q - 1 - (q - 1 - j) = j := by omega
        simpa [C, σ, hidx] using hm
      · simp only [hj, decide_false, Bool.false_and]
        exact (big_false y.isLt (by omega)).symm
  rw [hfilt]
  rw [Fintype.card_fin] at hhalv
  have hpow : 2 ^ k = 2 ^ (k - q) * 2 ^ q := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  exact Nat.eq_of_mul_eq_mul_right (by positivity) (hhalv.trans hpow)

private lemma xor_one_div_two (a : ℕ) : (a ^^^ 1) / 2 = a / 2 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_xor]
  have h1 : (1 : ℕ).testBit (j + 1) = false :=
    big_false (show (1 : ℕ) < 2 ^ 1 by norm_num) (by omega)
  rw [h1, Bool.xor_false]

private lemma card_pairs_clipped_div2 {k r q iVal rowName : ℕ} (constants : ℕ → Fin (2 ^ k))
    (hq : 0 < q) (hr : 4 ≤ r) (hqk : q < k) (h2rk : 2 * r ≤ iVal + k + 2)
    (hrow : rowName < 2 ^ k) (c : ℕ) (hc : c < 2 ^ (q - 1)) :
    let cutSite := iVal + k + 3 - 2 * r
    let clipRaw := fun raw => clippedZ k r q iVal cutSite rowName constants (piF k rowName raw)
    ((Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun x => x.val < mateF k r iVal x.val ∧ clipRaw x.val / 2 = c)).card = 2 ^ (k - q) := by
  intro cutSite clipRaw
  have hk : 0 < k := by omega
  have h2c : 2 * c < 2 ^ q := by
    have : 2 * 2 ^ (q - 1) = 2 ^ q := by
      conv_rhs => rw [show q = (q - 1) + 1 by omega, pow_succ, mul_comm]
    omega
  have h2c1 : 2 * c + 1 < 2 ^ q := by
    have : 2 * 2 ^ (q - 1) = 2 ^ q := by
      conv_rhs => rw [show q = (q - 1) + 1 by omega, pow_succ, mul_comm]
    omega
  have hraw_eq : ∀ y : Fin (2 ^ q),
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => clipRaw x.val = y.val)).card = 2 ^ (k - q) := by
    intro y
    have hbij : ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => clipRaw x.val = y.val)).card =
        ((Finset.univ : Finset (Fin (2 ^ k))).filter
          (fun w => clippedZ k r q iVal cutSite rowName constants w.val = y.val)).card := by
      refine Finset.card_bij (fun x _ => piEquiv hk hrow x) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx
      · intro x₁ _ x₂ _ h; exact (piEquiv hk hrow).injective h
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        refine ⟨(piEquiv hk hrow).symm w, ?_, (piEquiv hk hrow).apply_symm_apply w⟩
        have heq := congrArg Fin.val ((piEquiv hk hrow).apply_symm_apply w)
        dsimp only [clipRaw]
        change clippedZ k r q iVal cutSite rowName constants ((piEquiv hk hrow ((piEquiv hk hrow).symm w)).val) = y.val
        rw [heq]; exact hw
    rw [hbij]
    exact card_clippedZ_eq constants hq hr hqk (by omega) y
  have hall_div2 :
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => clipRaw x.val / 2 = c)).card =
        2 * 2 ^ (k - q) := by
    have hunion :
        (Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => clipRaw x.val / 2 = c) =
        ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => clipRaw x.val = 2 * c)) ∪
        ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => clipRaw x.val = 2 * c + 1)) := by
      ext x; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hdisj : Disjoint
        ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => clipRaw x.val = 2 * c))
        ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => clipRaw x.val = 2 * c + 1)) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      omega
    rw [hunion, Finset.card_union_of_disjoint hdisj,
        hraw_eq ⟨2 * c, h2c⟩, hraw_eq ⟨2 * c + 1, h2c1⟩, two_mul]
  have hclip_mate : ∀ x : Fin (2 ^ k), clipRaw (mateF k r iVal x.val) / 2 = clipRaw x.val / 2 := by
    intro x
    dsimp only [clipRaw]
    rw [piF_mateF hk h2rk hrow x.isLt, clippedZ_flip_cut constants hq hr hqk (by omega), xor_one_div_two]
  let S := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => clipRaw x.val / 2 = c)
  let Slt := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => x.val < mateF k r iVal x.val ∧ clipRaw x.val / 2 = c)
  let Sgt := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => mateF k r iVal x.val < x.val ∧ clipRaw x.val / 2 = c)
  have hpart : S = Slt ∪ Sgt := by
    ext x
    simp only [S, Slt, Sgt, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    have hne := mateF_ne (k := k) (r := r) (iVal := iVal) (word := x.val) hk
    constructor
    · intro h
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inr ⟨hlt, h⟩
      · exact Or.inl ⟨hgt, h⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  have hdisj : Disjoint Slt Sgt := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Slt, Sgt, Finset.mem_filter] at h1 h2
    omega
  have hswap : Slt.card = Sgt.card := by
    refine Finset.card_bij (fun x _ => ⟨mateF k r iVal x.val, mateF_lt hk x.isLt⟩) ?_ ?_ ?_
    · intro x hx
      simp only [Slt, Sgt, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨by rw [mateF_invol]; exact hx.1, by rw [hclip_mate x]; exact hx.2⟩
    · intro x₁ _ x₂ _ h
      apply Fin.ext
      have hval := congrArg Fin.val h
      have := congrArg (mateF k r iVal) hval
      simpa [mateF_invol] using this
    · intro y hy
      simp only [Slt, Sgt, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      refine ⟨⟨mateF k r iVal y.val, mateF_lt hk y.isLt⟩,
        ⟨by rw [mateF_invol]; exact hy.1, by rw [hclip_mate y]; exact hy.2⟩,
        Fin.ext (mateF_invol k r iVal y.val)⟩
  have hsum : S.card = 2 * Slt.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj, hswap, two_mul]
  change S.card = 2 * 2 ^ (k - q) at hall_div2
  change Slt.card = 2 ^ (k - q)
  omega

private lemma tracePairF_fst_eq (k cutSite rowName : ℕ) (constants : ℕ → Fin (2 ^ k))
    (raw m : ℕ) :
    (tracePairF k cutSite rowName constants raw m).1 =
      traceWeightF k cutSite rowName constants raw m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [tracePairF, traceWeightF, fold_succ]
    rw [ih]
    rfl

private lemma tracePairF_snd_lt (k cutSite rowName : ℕ) (constants : ℕ → Fin (2 ^ k))
    (raw m : ℕ) :
    (tracePairF k cutSite rowName constants raw m).2 < 2 ^ m := by
  induction m with
  | zero => simp [tracePairF]
  | succ m ih =>
    simp only [tracePairF]
    apply Nat.lt_pow_two_of_testBit
    intro b hb
    rw [Nat.testBit_or, big_false ih (by omega), Bool.false_or, Nat.testBit_shiftLeft]
    by_cases hmb : m ≤ b
    · have h1 : 1 ≤ b - m := by omega
      have hlt2 : ∀ x : Bool, x.toNat.testBit (b - m) = false := fun x =>
        big_false (k := 1) (by cases x <;> norm_num) h1
      simp [hmb, hlt2]
    · simp [hmb]

private lemma tracePairF_snd_testBit (k cutSite rowName : ℕ) (constants : ℕ → Fin (2 ^ k))
    (raw : ℕ) : ∀ m j, j < m →
    (tracePairF k cutSite rowName constants raw m).2.testBit j =
      let o := (tracePairF k cutSite rowName constants raw j).1
      let pos := cutSite + k - 3 * (5 + j) + o
      let layer := st k rowName (fun j => (constants j).val) raw (4 + j)
      xor (xor (layer.testBit (pos % k)) (layer.testBit ((pos + 1) % k)))
          (layer.testBit ((pos + 2) % k)) := by
  intro m
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
    intro j hj
    simp only [tracePairF]
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [ih j hlt]
      simp [show ¬ m ≤ j by omega]
    · rw [big_false (tracePairF_snd_lt k cutSite rowName constants raw j) le_rfl, Bool.false_or]
      simp only [le_refl, decide_true, Nat.sub_self, Bool.true_and, show 5 + j - 1 = 4 + j by omega]
      cases xor (xor ((st k rowName (fun j => (constants j).val) raw (4 + j)).testBit
          ((cutSite + k - 3 * (5 + j) + (tracePairF k cutSite rowName constants raw j).1) % k))
        ((st k rowName (fun j => (constants j).val) raw (4 + j)).testBit
          ((cutSite + k - 3 * (5 + j) + (tracePairF k cutSite rowName constants raw j).1 + 1) % k)))
        ((st k rowName (fun j => (constants j).val) raw (4 + j)).testBit
          ((cutSite + k - 3 * (5 + j) + (tracePairF k cutSite rowName constants raw j).1 + 2) % k)) <;> rfl

private lemma tracePairF_ones_eq (k cutSite rowName : ℕ) (constants : ℕ → Fin (2 ^ k))
    (raw n : ℕ) : ∀ j, j ≤ n →
    ((List.range j).filter (fun h => (tracePairF k cutSite rowName constants raw n).2.testBit h)).length =
      (tracePairF k cutSite rowName constants raw j).1 := by
  intro j
  induction j with
  | zero => intro _; simp [tracePairF]
  | succ j ih =>
    intro hj
    rw [List.range_succ, List.filter_append, List.length_append, ih (by omega)]
    simp only [List.filter_cons, List.filter_nil]
    rw [tracePairF_snd_testBit k cutSite rowName constants raw n j (by omega)]
    simp only [tracePairF, show 5 + j - 1 = 4 + j by omega]
    cases xor (xor ((st k rowName (fun j => (constants j).val) raw (4 + j)).testBit
        ((cutSite + k - 3 * (5 + j) + (tracePairF k cutSite rowName constants raw j).1) % k))
      ((st k rowName (fun j => (constants j).val) raw (4 + j)).testBit
        ((cutSite + k - 3 * (5 + j) + (tracePairF k cutSite rowName constants raw j).1 + 1) % k)))
      ((st k rowName (fun j => (constants j).val) raw (4 + j)).testBit
        ((cutSite + k - 3 * (5 + j) + (tracePairF k cutSite rowName constants raw j).1 + 2) % k)) <;> simp

private lemma realizesTrace_of_raw {k r e q n : ℕ} (i : Fin k) (constants : ℕ → Fin (2 ^ k))
    (hq : 0 < q) (hkr : k + e + 3 = 5 * r) (hnr : n + 4 ≤ r) (hnk : 5 * n + 15 ≤ k) (heqn : e + q ≤ n)
    (rowName raw : Fin (2 ^ k)) :
    let cutSite := i.val + k + 3 - 2 * r
    let code : Fin (2 ^ n) :=
      ⟨(tracePairF k cutSite rowName.val constants raw.val n).2,
        tracePairF_snd_lt k cutSite rowName.val constants raw.val n⟩
    let w : Fin (2 ^ k) := ⟨piF k rowName.val raw.val, piF_lt rowName.isLt raw.val⟩
    let pub := pubF k rowName.val constants
    let ones := fun j : ℕ => ((List.range j).filter (fun h => code.val.testBit h)).length
    let place := fun j : ℕ => (cutSite : ℤ) - 3 * (5 + (j : ℤ)) + (ones j : ℤ)
    ∀ j < n,
      let z := stZ pub (pz k w.val) (4 + j)
      let a := place j
      xor (xor (z a) (z (a + 1))) (z (a + 2)) = code.val.testBit j := by
  intro cutSite code w pub ones place j hj
  have hk : 0 < k := by omega
  have hones_j : ones j = (tracePairF k cutSite rowName.val constants raw.val j).1 :=
    tracePairF_ones_eq k cutSite rowName.val constants raw.val n j (by omega)
  have hpos_cast : ((cutSite + k - 3 * (5 + j) + ones j : ℕ) : ℤ) = place j + (k : ℤ) := by
    have h3 : 3 * (5 + j) ≤ cutSite + k := by omega
    dsimp only [place]
    omega
  have hbit_eq : ∀ c : ℕ,
      (st k rowName.val (fun t => (constants t).val) raw.val (4 + j)).testBit
        ((cutSite + k - 3 * (5 + j) + ones j + c) % k) =
      stZ pub (pz k w.val) (4 + j) (place j + (c : ℤ)) := by
    intro c
    rw [← pz_nat, pz_st_eq_stZ hk rowName.isLt constants raw.isLt]
    have hmod : (((cutSite + k - 3 * (5 + j) + ones j + c : ℕ) : ℤ)) ≡
        (place j + (c : ℤ)) [ZMOD (k : ℤ)] := by
      rw [Nat.cast_add, hpos_cast]
      have : place j + (k : ℤ) + (c : ℤ) = (place j + (c : ℤ)) + (k : ℤ) := by ring
      rw [this]
      simp [Int.ModEq]
    have hper : ∀ (t : ℕ) (x y : ℤ), x ≡ y [ZMOD (k : ℤ)] →
        stZ pub (pz k w.val) t x = stZ pub (pz k w.val) t y := by
      intro t
      induction t with
      | zero => intro x y hxy; exact pz_modEq hxy
      | succ t iht =>
        intro x y hxy
        rw [stZ_succ, stZ_succ]
        have hbef : befZ (stZ pub (pz k w.val) t) x = befZ (stZ pub (pz k w.val) t) y := by
          rw [befZ_eq, befZ_eq]
          rw [iht _ _ (hxy.sub_right 1), iht _ _ hxy, iht _ _ (hxy.add_right 1),
              iht _ _ (hxy.add_right 2), iht _ _ (hxy.add_right 3)]
        have hpz : pz k w.val (x + 1 - 2 * (t : ℤ)) = pz k w.val (y + 1 - 2 * (t : ℤ)) :=
          pz_modEq ((hxy.add_right 1).sub_right (2 * (t : ℤ)))
        have hpub : pub (t + 1) x = pub (t + 1) y := by
          simp only [pub, pubF]
          rw [pz_modEq ((hxy.add_right 1).sub_right _), pz_modEq hxy]
        rw [hbef, hpz, hpub]
    exact hper (4 + j) _ _ hmod
  have h0 := hbit_eq 0
  have h1 := hbit_eq 1
  have h2 := hbit_eq 2
  simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at h0 h1 h2
  dsimp only
  rw [← h0, ← h1, ← h2]
  dsimp only [code]
  rw [tracePairF_snd_testBit k cutSite rowName.val constants raw.val n j hj, hones_j]

private lemma agree_of_not_lowTrace {k r e q n : ℕ} (i : Fin k) (constants : ℕ → Fin (2 ^ k))
    (hq : 0 < q) (hkr : k + e + 3 = 5 * r) (hnr : n + 4 ≤ r) (hnk : 5 * n + 15 ≤ k) (heqn : e + q ≤ n)
    (rowName raw : Fin (2 ^ k))
    (hhigh : e + q ≤ traceWeightF k (i.val + k + 3 - 2 * r) rowName.val constants raw.val n) :
    visOutF k r q i.val rowName.val constants raw.val =
      clippedZ k r q i.val (i.val + k + 3 - 2 * r) rowName.val constants (piF k rowName.val raw.val) := by
  have hk : 0 < k := by omega
  have hn : 0 < n := by omega
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  set cutSite := i.val + k + 3 - 2 * (s + 1)
  let code : Fin (2 ^ n) :=
    ⟨(tracePairF k cutSite rowName.val constants raw.val n).2,
      tracePairF_snd_lt k cutSite rowName.val constants raw.val n⟩
  let w : Fin (2 ^ k) := ⟨piF k rowName.val raw.val, piF_lt rowName.isLt raw.val⟩
  let pub := pubF k rowName.val constants
  have hreal := realizesTrace_of_raw i constants hq hkr hnr hnk heqn rowName raw
  have h82 := (PEqualNP.Outside.L_meta_25582 k n hn hnk (cutSite : ℤ) pub code).2
    w hreal (startClip k cutSite w.val) (fun z hz => by simp [startClip, hz, pz]) (s + 1) hnr
  have hones_n : ((List.range n).filter (fun h => code.val.testBit h)).length =
      traceWeightF k cutSite rowName.val constants raw.val n := by
    rw [← tracePairF_fst_eq]
    exact tracePairF_ones_eq k cutSite rowName.val constants raw.val n n le_rfl
  have hcutZ : (cutSite : ℤ) = (i.val : ℤ) + (k : ℤ) + 3 - 2 * ((s + 1 : ℕ) : ℤ) := by
    dsimp only [cutSite]; omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_visOutF, testBit_clippedZ]
  by_cases hj : j < q
  · simp only [hj, decide_true, Bool.true_and]
    rw [← pz_nat, pz_st_eq_stZ hk rowName.isLt constants raw.isLt]
    have hcast : ((i.val + j : ℕ) : ℤ) = (i.val : ℤ) + (j : ℤ) := by push_cast; ring
    rw [hcast, stZ_succ, stZ_succ]
    have hlt_cut : ((i.val : ℤ) + (j : ℤ)) + 3 * ((s + 1 : ℕ) : ℤ) <
        (cutSite : ℤ) + (((List.range n).filter (fun h => code.val.testBit h)).length : ℤ) := by
      rw [hones_n]
      omega
    have hbef : befZ (stZ pub (pz k w.val) s) ((i.val : ℤ) + (j : ℤ)) =
        befZ (stZ pub (startClip k cutSite w.val) s) ((i.val : ℤ) + (j : ℤ)) :=
      h82 ((i.val : ℤ) + (j : ℤ)) hlt_cut
    have hp_lt : (i.val : ℤ) + (j : ℤ) + 1 - 2 * (s : ℤ) < (cutSite : ℤ) := by omega
    have hstart : startClip k cutSite w.val ((i.val : ℤ) + (j : ℤ) + 1 - 2 * (s : ℤ)) =
        pz k w.val ((i.val : ℤ) + (j : ℤ) + 1 - 2 * (s : ℤ)) := by
      simp [startClip, hp_lt]
    rw [hbef, hstart]
  · simp [hj]

private lemma card_realizesTrace_le {k n : ℕ} (hn : 0 < n) (hnk : 5 * n + 15 ≤ k)
    (cut : ℤ) (pub : ℕ → ℤ → Bool) (code : Fin (2 ^ n)) :
    let ones := fun j : ℕ => ((List.range j).filter (fun h => code.val.testBit h)).length
    let place := fun j : ℕ => cut - 3 * (5 + (j : ℤ)) + (ones j : ℤ)
    let realizesTrace := fun w : Fin (2 ^ k) => ∀ j < n,
      let z := stZ pub (pz k w.val) (4 + j)
      let a := place j
      xor (xor (z a) (z (a + 1))) (z (a + 2)) = code.val.testBit j
    ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w => realizesTrace w)).card ≤ 2 ^ (k - n) := by
  classical
  intro ones place realizesTrace
  have hk : 0 < k := by omega
  let pivot : Fin n → Fin k := fun j =>
    ⟨((cut + 5 - 5 * (5 + (j.val : ℤ)) + (ones j.val : ℤ)) % (k : ℤ)).toNat, toNat_lt hk _⟩
  have hones_mono : ∀ j j', j ≤ j' → ones j ≤ ones j' ∧ ones j' - ones j ≤ j' - j := by
    intro j j' h
    have heq : ones = cntC (fun h => code.val.testBit h) := funext fun t => cntC_list _ t
    rw [heq]
    exact cntC_mono _ j j' h
  have hpiv_inj : Function.Injective pivot := by
    intro j j' hEq
    by_contra hne
    have hval : (pivot j).val = (pivot j').val := congrArg Fin.val hEq
    have hne' : j.val ≠ j'.val := fun h => hne (Fin.ext h)
    have h0 := Int.emod_nonneg (cut + 5 - 5 * (5 + (j.val : ℤ)) + (ones j.val : ℤ)) (by omega : (k : ℤ) ≠ 0)
    have h0' := Int.emod_nonneg (cut + 5 - 5 * (5 + (j'.val : ℤ)) + (ones j'.val : ℤ)) (by omega : (k : ℤ) ≠ 0)
    have hmod : (cut + 5 - 5 * (5 + (j.val : ℤ)) + (ones j.val : ℤ)) % (k : ℤ) =
        (cut + 5 - 5 * (5 + (j'.val : ℤ)) + (ones j'.val : ℤ)) % (k : ℤ) := by
      dsimp only [pivot] at hval; omega
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hgt
    · have hm := hones_mono j.val j'.val hlt.le
      exact int_mod_ne (k := (k : ℤ))
        (a := cut + 5 - 5 * (5 + (j'.val : ℤ)) + (ones j'.val : ℤ))
        (b := cut + 5 - 5 * (5 + (j.val : ℤ)) + (ones j.val : ℤ))
        (by omega) (by omega) (by have := j'.isLt; omega) hmod.symm
    · have hm := hones_mono j'.val j.val hgt.le
      exact int_mod_ne (k := (k : ℤ))
        (a := cut + 5 - 5 * (5 + (j.val : ℤ)) + (ones j.val : ℤ))
        (b := cut + 5 - 5 * (5 + (j'.val : ℤ)) + (ones j'.val : ℤ))
        (by omega) (by omega) (by have := j.isLt; omega) hmod
  let nonPiv : Finset (Fin k) := Finset.univ \ (Finset.univ.image pivot)
  have hnonPiv_card : nonPiv.card = k - n := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_image_of_injective _ hpiv_inj,
        Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  have h82 := (PEqualNP.Outside.L_meta_25582 k n hn hnk cut pub code).1
  let proj : Fin (2 ^ k) → (nonPiv → Bool) := fun w b => w.val.testBit b.val.val
  have hinj : Set.InjOn proj (((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w => realizesTrace w)) : Set (Fin (2 ^ k))) := by
    intro w₁ hw₁ w₂ hw₂ hEq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂
    obtain ⟨w₀, _, huniq⟩ := h82 w₁
    have h1 : w₁ = w₀ := huniq w₁ ⟨hw₁, fun _ _ _ => rfl⟩
    have h2 : w₂ = w₀ := huniq w₂ ⟨hw₂, fun b hb hnp => by
      have hmem : (⟨b, hb⟩ : Fin k) ∈ nonPiv := by
        simp only [nonPiv, Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro h
        rcases Finset.mem_image.mp h with ⟨j, _, hj⟩
        exact hnp j.val j.isLt (congrArg Fin.val hj)
      exact (congrFun hEq ⟨⟨b, hb⟩, hmem⟩).symm⟩
    exact h1.trans h2.symm
  calc ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w => realizesTrace w)).card
      ≤ (Finset.univ : Finset (nonPiv → Bool)).card :=
        Finset.card_le_card_of_injOn proj (fun _ _ => Finset.mem_univ _) hinj
    _ = 2 ^ nonPiv.card := by simp [Fintype.card_pi]
    _ = 2 ^ (k - n) := by rw [hnonPiv_card]

private lemma card_low_codes (n bound : ℕ) :
    ((Finset.univ : Finset (Fin (2 ^ n))).filter
      (fun code => ((List.range n).filter (fun h => code.val.testBit h)).length < bound)).card =
      ∑ m ∈ Finset.range bound, Nat.choose n m := by
  let toSet : Fin (2 ^ n) → Finset (Fin n) := fun code =>
    Finset.univ.filter (fun j : Fin n => code.val.testBit j.val = true)
  let ofSet : Finset (Fin n) → Fin (2 ^ n) := fun s =>
    ⟨(List.range n).foldl (fun acc j => acc ||| ((decide (∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∈ s)).toNat <<< j)) 0,
      Nat.lt_pow_two_of_testBit _ fun j hj => by
        rw [testBit_foldl_or]; simp [show ¬ j < n by omega]⟩
  let hbij : Fin (2 ^ n) ≃ Finset (Fin n) :=
    { toFun := toSet
      invFun := ofSet
      left_inv := fun code => Fin.ext <| Nat.eq_of_testBit_eq fun j => by
        dsimp only [ofSet, toSet]
        rw [testBit_foldl_or]
        by_cases hj : j < n
        · simp [hj]
        · simp only [hj, decide_false, Bool.false_and]
          exact (big_false (k := n) code.isLt (by omega)).symm
      right_inv := fun s => by
        ext j
        dsimp only [ofSet, toSet]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [testBit_foldl_or]
        simp [j.isLt] }
  have hlen : ∀ code : Fin (2 ^ n),
      ((List.range n).filter (fun h => code.val.testBit h)).length = (toSet code).card := by
    intro code
    rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    refine Finset.card_bij (fun h hh => ⟨h, (List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp hh)).1)⟩)
      ?_ ?_ ?_
    · intro h hh
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range] at hh
      simp only [toSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hh.2
    · intro h₁ _ h₂ _ hEq; exact congrArg Fin.val hEq
    · intro j hj
      simp only [toSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine ⟨j.val, ?_, Fin.ext rfl⟩
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range]
      exact ⟨j.isLt, hj⟩
  have hcard1 : ((Finset.univ : Finset (Fin (2 ^ n))).filter
      (fun code => ((List.range n).filter (fun h => code.val.testBit h)).length < bound)).card =
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card < bound)).card := by
    refine Finset.card_bij (fun code _ => hbij code) ?_ ?_ ?_
    · intro code hcode
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcode ⊢
      change (toSet code).card < bound
      rwa [← hlen code]
    · intro c₁ _ c₂ _ h; exact hbij.injective h
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      refine ⟨hbij.symm s, ?_, hbij.apply_symm_apply s⟩
      rw [hlen, show toSet (hbij.symm s) = hbij (hbij.symm s) from rfl, hbij.apply_symm_apply]
      exact hs
  rw [hcard1]
  have hunion : (Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card < bound) =
      (Finset.range bound).biUnion (fun m => Finset.powersetCard m (Finset.univ : Finset (Fin n))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact ⟨fun h => ⟨s.card, h, rfl⟩, fun ⟨m, hm, hEq⟩ => hEq ▸ hm⟩
  rw [hunion, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro m₁ _ m₂ _ hne
    exact Finset.disjoint_left.mpr fun s h1 h2 => by
      rw [Finset.mem_powersetCard] at h1 h2
      exact hne (h1.2.symm.trans h2.2)

private lemma card_lowTrace_le {k r e q n : ℕ} (i : Fin k) (constants : ℕ → Fin (2 ^ k))
    (hq : 0 < q) (hkr : k + e + 3 = 5 * r) (hnr : n + 4 ≤ r) (hnk : 5 * n + 15 ≤ k) (heqn : e + q ≤ n)
    (rowName : Fin (2 ^ k)) :
    let cutSite := i.val + k + 3 - 2 * r
    ((List.range (2 ^ k)).filter (fun w =>
      decide (traceWeightF k cutSite rowName.val constants w n < e + q))).length ≤
      2 ^ (k - n) * (∑ m ∈ Finset.range (e + q), Nat.choose n m) := by
  classical
  intro cutSite
  have hk : 0 < k := by omega
  have hn : 0 < n := by omega
  let lowSet : Finset (Fin (2 ^ k)) := (Finset.univ : Finset (Fin (2 ^ k))).filter
    (fun raw => traceWeightF k cutSite rowName.val constants raw.val n < e + q)
  have hlen_eq : ((List.range (2 ^ k)).filter (fun w =>
      decide (traceWeightF k cutSite rowName.val constants w n < e + q))).length = lowSet.card := by
    rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    refine Finset.card_bij (fun x hx => ⟨x, List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp hx)).1⟩)
      ?_ ?_ ?_
    · intro x hx
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
      simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx.2
    · intro x₁ _ x₂ _ h; exact congrArg Fin.val h
    · intro raw hraw
      simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hraw
      refine ⟨raw.val, ?_, Fin.ext rfl⟩
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨raw.isLt, hraw⟩
  rw [hlen_eq]
  let codeOf : Fin (2 ^ k) → Fin (2 ^ n) := fun raw =>
    ⟨(tracePairF k cutSite rowName.val constants raw.val n).2,
      tracePairF_snd_lt k cutSite rowName.val constants raw.val n⟩
  let lowCodes : Finset (Fin (2 ^ n)) := (Finset.univ : Finset (Fin (2 ^ n))).filter
    (fun code => ((List.range n).filter (fun h => code.val.testBit h)).length < e + q)
  have hsub : lowSet ⊆ lowCodes.biUnion (fun code => lowSet.filter (fun raw => codeOf raw = code)) := by
    intro raw hraw
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    refine ⟨codeOf raw, ?_, hraw, rfl⟩
    simp only [lowCodes, Finset.mem_filter, Finset.mem_univ, true_and]
    have hones := tracePairF_ones_eq k cutSite rowName.val constants raw.val n n le_rfl
    rw [tracePairF_fst_eq] at hones
    rw [hones]
    exact (Finset.mem_filter.mp hraw).2
  have hfiber_le : ∀ code ∈ lowCodes, (lowSet.filter (fun raw => codeOf raw = code)).card ≤ 2 ^ (k - n) := by
    intro code _
    let pub := pubF k rowName.val constants
    let ones := fun j : ℕ => ((List.range j).filter (fun h => code.val.testBit h)).length
    let place := fun j : ℕ => (cutSite : ℤ) - 3 * (5 + (j : ℤ)) + (ones j : ℤ)
    let realizesTrace := fun w : Fin (2 ^ k) => ∀ j < n,
      let z := stZ pub (pz k w.val) (4 + j)
      let a := place j
      xor (xor (z a) (z (a + 1))) (z (a + 2)) = code.val.testBit j
    calc (lowSet.filter (fun raw => codeOf raw = code)).card
        ≤ ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w => realizesTrace w)).card := by
          apply Finset.card_le_card_of_injOn (piEquiv hk rowName.isLt)
          · intro raw hraw
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hraw ⊢
            have hreal := realizesTrace_of_raw i constants hq hkr hnr hnk heqn rowName raw
            have hceq : (tracePairF k cutSite rowName.val constants raw.val n).2 = code.val :=
              congrArg Fin.val hraw.2
            dsimp only [realizesTrace, place, ones, pub, piEquiv]
            rw [← hceq]
            exact hreal
          · intro r₁ _ r₂ _ h; exact (piEquiv hk rowName.isLt).injective h
      _ ≤ 2 ^ (k - n) := card_realizesTrace_le hn hnk (cutSite : ℤ) pub code
  calc lowSet.card
      ≤ (lowCodes.biUnion (fun code => lowSet.filter (fun raw => codeOf raw = code))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ code ∈ lowCodes, (lowSet.filter (fun raw => codeOf raw = code)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _code ∈ lowCodes, 2 ^ (k - n) := Finset.sum_le_sum hfiber_le
    _ = lowCodes.card * 2 ^ (k - n) := by simp
    _ = 2 ^ (k - n) * (∑ m ∈ Finset.range (e + q), Nat.choose n m) := by
        rw [mul_comm, card_low_codes]

private lemma prove_25628 (k r e q n : ℕ) (i : Fin k) (constants : ℕ → Fin (2 ^ k))
    (hq : 0 < q) (hkr : k + e + 3 = 5 * r) (hnr : n + 4 ≤ r) (hnk : 5 * n + 15 ≤ k) (heqn : e + q ≤ n) :
    let rot := fun (s word : ℕ) =>
      ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
    let step := fun (word : ℕ) =>
      (List.range k).foldl (fun acc cell =>
        acc ||| ((xor (word.testBit cell)
          (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0
    let state := fun (row raw rounds : ℕ) =>
      (List.range rounds).foldl (fun prev tick =>
        step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) raw ^^^
          (constants (tick + 1)).val) (rot 1 raw ^^^ row)
    let visibleOutput := fun (row raw : ℕ) => (List.range q).foldl (fun out bitNo =>
      out ||| (((state row raw r).testBit ((i.val + bitNo) % k)).toNat <<< bitNo)) 0
    let mate := fun (word : ℕ) => word ^^^ (1 <<< ((i.val + k + 2 - 2 * r) % k))
    let budget := 2 ^ (k - n) * (∑ m ∈ Finset.range (e + q), Nat.choose n m)
    let cutSite := i.val + k + 3 - 2 * r
    let lowTrace := fun (input nameKey : ℕ) =>
      let weight := (List.range n).foldl (fun (ones tickNo : ℕ) =>
        let now := 5 + tickNo
        let pos := cutSite + k - 3 * now + ones
        let layer := state input nameKey (now - 1)
        ones + (xor (xor (layer.testBit (pos % k)) (layer.testBit ((pos + 1) % k)))
                     (layer.testBit ((pos + 2) % k))).toNat) 0
      decide (weight < e + q)
    let clipped := fun (fixedRow candidate : ℕ) =>
      let residue := fun (place : ℤ) => (place % (k : ℤ)).toNat
      let period := rot 1 candidate ^^^ fixedRow
      let start := fun (site : ℤ) => if site < (cutSite : ℤ) then period.testBit (residue site) else false
      let mix := fun (tape : ℤ → Bool) (atSite : ℤ) =>
        xor (xor (tape (atSite - 1)) (tape atSite)) (tape (atSite + 1))
      let finalTape := (List.range r).foldl (fun (previous : ℤ → Bool) (tick : ℕ) (z : ℤ) =>
        let p := z + 1 - 2 * (tick : ℤ)
        let ordinary := xor (mix previous z) (!(mix previous (z + 1)) && mix previous (z + 2))
        xor (xor (xor ordinary (start p)) (fixedRow.testBit (residue p)))
          ((constants (tick + 1)).val.testBit (residue z))) start
      (List.range q).foldl (fun (total j : ℕ) => total ||| ((finalTape ((i.val : ℤ) + (j : ℤ))).toNat <<< j)) 0
    ∀ rowName : Fin (2 ^ k),
      let wordOut := visibleOutput rowName.val
      let selected := (List.range (2 ^ k)).filter (fun w =>
        lowTrace rowName.val w && (decide (w < mate w) || !(lowTrace rowName.val (mate w))))
      let touched := fun (c : ℕ) =>
        (selected.filter (fun v => clipped rowName.val v / 2 == c)).length
      let follows := fun (lab : ℕ → Bool) (x : ℕ) => lab (wordOut x) ≠ lab (wordOut (mate x))
      selected.length ≤ budget ∧
      (∀ y z : Fin (2 ^ q),
        (∃ base : Fin (2 ^ k), wordOut base.val = y.val ∧ wordOut (mate base.val) = z.val) ↔
          (∃ p ∈ selected, (wordOut p = y.val ∧ wordOut (mate p) = z.val) ∨
            (wordOut p = z.val ∧ wordOut (mate p) = y.val)) ∨
          (z.val = (y.val ^^^ 1) ∧ touched (y.val / 2) < 2 ^ (k - q))) ∧
      (budget < 2 ^ (k - q) → ∀ coloring : ℕ → Bool,
        (∀ rawKey : Fin (2 ^ k), follows coloring rawKey.val) ↔
          (∀ pair : Fin (2 ^ (q - 1)), coloring (2 * pair.val) ≠ coloring (2 * pair.val + 1)) ∧
          ∀ representative ∈ selected, follows coloring representative) := by
  intro rot step state visibleOutput mate budget cutSite lowTrace clipped rowName wordOut selected touched follows
  have hk : 0 < k := by omega
  have hr4 : 4 ≤ r := by omega
  have hqk : q < k := by omega
  have h2rk : 2 * r ≤ i.val + k + 2 := by omega
  have hclip_eq : ∀ raw : ℕ, clipped rowName.val raw =
      clippedZ k r q i.val cutSite rowName.val constants (piF k rowName.val raw) := by
    intro raw
    apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_clippedZ]
    dsimp only [clipped]
    rw [testBit_foldl_or]
    congr 1
    exact congrFun (finalTape_eq_stZ k rowName.val constants
      (startClip k cutSite (piF k rowName.val raw)) r) ((i.val : ℤ) + (j : ℤ))
  have hclip_mate : ∀ raw : Fin (2 ^ k), clipped rowName.val (mate raw.val) = clipped rowName.val raw.val ^^^ 1 := by
    intro raw
    rw [hclip_eq, hclip_eq]
    change clippedZ k r q i.val cutSite rowName.val constants (piF k rowName.val (mateF k r i.val raw.val)) = _
    rw [piF_mateF hk h2rk rowName.isLt raw.isLt]
    exact clippedZ_flip_cut constants hq hr4 hqk (by omega) _
  have hclip_mate_div2 : ∀ raw : Fin (2 ^ k),
      clipped rowName.val (mate raw.val) / 2 = clipped rowName.val raw.val / 2 := fun raw => by
    rw [hclip_mate raw, xor_one_div_two]
  have hagree : ∀ raw : Fin (2 ^ k), lowTrace rowName.val raw.val = false →
      wordOut raw.val = clipped rowName.val raw.val := by
    intro raw hlow
    rw [hclip_eq]
    have hhigh : e + q ≤ traceWeightF k cutSite rowName.val constants raw.val n := by
      change decide (traceWeightF k cutSite rowName.val constants raw.val n < e + q) = false at hlow
      rw [decide_eq_false_iff_not] at hlow
      omega
    exact agree_of_not_lowTrace i constants hq hkr hnr hnk heqn rowName raw hhigh
  have hmate_lt : ∀ w : ℕ, w < 2 ^ k → mate w < 2 ^ k := fun w hw => mateF_lt hk hw
  have hmate_invol : ∀ w : ℕ, mate (mate w) = w := fun w => mateF_invol k r i.val w
  have hmate_ne : ∀ w : ℕ, mate w ≠ w := fun w => mateF_ne hk
  have hmem_sel : ∀ p : ℕ, p ∈ selected ↔
      p < 2 ^ k ∧ lowTrace rowName.val p = true ∧
      (p < mate p ∨ lowTrace rowName.val (mate p) = false) := by
    intro p
    simp only [selected, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, Bool.not_eq_true']
  have hpair_sel : ∀ x : Fin (2 ^ k),
      (x.val ∈ selected ∨ mate x.val ∈ selected) ↔
      (lowTrace rowName.val x.val = true ∨ lowTrace rowName.val (mate x.val) = true) := by
    intro x
    rw [hmem_sel, hmem_sel]
    have hlt1 := x.isLt
    have hlt2 := hmate_lt x.val x.isLt
    have hinv := hmate_invol x.val
    have hne := hmate_ne x.val
    constructor
    · rintro (⟨_, h, _⟩ | ⟨_, h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (hx | hm)
      · by_cases hm2 : lowTrace rowName.val (mate x.val) = true
        · rcases Nat.lt_or_gt_of_ne hne with hgt | hlt
          · exact Or.inr ⟨hlt2, hm2, Or.inl (by rw [hinv]; exact hgt)⟩
          · exact Or.inl ⟨hlt1, hx, Or.inl hlt⟩
        · exact Or.inl ⟨hlt1, hx, Or.inr (Bool.eq_false_iff.mpr hm2)⟩
      · by_cases hx2 : lowTrace rowName.val x.val = true
        · rcases Nat.lt_or_gt_of_ne hne with hgt | hlt
          · exact Or.inr ⟨hlt2, hm, Or.inl (by rw [hinv]; exact hgt)⟩
          · exact Or.inl ⟨hlt1, hx2, Or.inl hlt⟩
        · exact Or.inr ⟨hlt2, hm, Or.inr (by rw [hinv]; exact Bool.eq_false_iff.mpr hx2)⟩

  have hgoal1 : selected.length ≤ budget := by
    have hle1 : selected.length ≤ ((List.range (2 ^ k)).filter (fun w => lowTrace rowName.val w)).length := by
      rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _),
          ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
      apply Finset.card_le_card
      intro w hw
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Bool.and_eq_true] at hw ⊢
      exact ⟨hw.1, hw.2.1⟩
    exact hle1.trans (card_lowTrace_le i constants hq hkr hnr hnk heqn rowName)

  have htouched_lt : ∀ c : ℕ, c < 2 ^ (q - 1) →
      (touched c < 2 ^ (k - q) ↔
        ∃ x : Fin (2 ^ k), clipped rowName.val x.val / 2 = c ∧
          lowTrace rowName.val x.val = false ∧ lowTrace rowName.val (mate x.val) = false) := by
    intro c hc
    let Pairs : Finset (Fin (2 ^ k)) := (Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun x => x.val < mate x.val ∧ clipped rowName.val x.val / 2 = c)
    have hPairs_card : Pairs.card = 2 ^ (k - q) := by
      have hcard := card_pairs_clipped_div2 constants hq hr4 hqk h2rk rowName.isLt c hc
      have hEq : Pairs = (Finset.univ : Finset (Fin (2 ^ k))).filter
          (fun x => x.val < mateF k r i.val x.val ∧
            clippedZ k r q i.val (i.val + k + 3 - 2 * r) rowName.val constants (piF k rowName.val x.val) / 2 = c) := by
        ext x
        dsimp only [Pairs]
        rw [Finset.mem_filter, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and, hclip_eq, mate, mateF, cutSite]
      rw [hEq]
      exact hcard
    let TouchedPairs : Finset (Fin (2 ^ k)) := Pairs.filter
      (fun x => lowTrace rowName.val x.val = true ∨ lowTrace rowName.val (mate x.val) = true)
    have htouched_eq : touched c = TouchedPairs.card := by
      have hnodup : (selected.filter (fun v => clipped rowName.val v / 2 == c)).Nodup :=
        (List.nodup_range.filter _).filter _
      rw [show touched c = (selected.filter (fun v => clipped rowName.val v / 2 == c)).toFinset.card from
        (List.toFinset_card_of_nodup hnodup).symm]
      refine Finset.card_bij (fun v hv =>
        let hvlt : v < 2 ^ k := by
          have := (List.mem_filter.mp (List.mem_toFinset.mp hv)).1
          exact (hmem_sel v).mp this |>.1
        if v < mate v then ⟨v, hvlt⟩ else ⟨mate v, hmate_lt v hvlt⟩) ?_ ?_ ?_
      · intro v hv
        simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hv
        obtain ⟨hvlt, hvlow, hvc⟩ := (hmem_sel v).mp hv.1
        split_ifs with hlt
        · simp only [TouchedPairs, Pairs, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨hlt, hv.2⟩, Or.inl hvlow⟩
        · simp only [TouchedPairs, Pairs, Finset.mem_filter, Finset.mem_univ, true_and]
          have hne := hmate_ne v
          exact ⟨⟨by rw [hmate_invol]; omega, by rw [hclip_mate_div2 ⟨v, hvlt⟩]; exact hv.2⟩,
            Or.inr (by rw [hmate_invol]; exact hvlow)⟩
      · intro v₁ hv₁ v₂ hv₂ hEq
        simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hv₁ hv₂
        obtain ⟨h1lt, h1low, h1c⟩ := (hmem_sel v₁).mp hv₁.1
        obtain ⟨h2lt, h2low, h2c⟩ := (hmem_sel v₂).mp hv₂.1
        have hval := congrArg Fin.val hEq
        split_ifs at hval with hlt1 hlt2 hlt2
        · exact hval
        · exfalso
          have : v₁ = mate v₂ := hval
          have hm1 : mate v₁ = v₂ := by rw [this, hmate_invol]
          rcases h2c with hlt2' | hm2f
          · exact hlt2 hlt2'
          · rw [← this] at hm2f; rw [h1low] at hm2f; exact Bool.noConfusion hm2f
        · exfalso
          have : mate v₁ = v₂ := hval
          rcases h1c with hlt1' | hm1f
          · exact hlt1 hlt1'
          · rw [this, h2low] at hm1f; exact Bool.noConfusion hm1f
        · have := congrArg mate hval
          simpa [hmate_invol] using this
      · intro x hx
        simp only [TouchedPairs, Pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨⟨hxlt, hxc⟩, hxlow⟩ := hx
        rcases (hpair_sel x).mpr hxlow with hxsel | hmsel
        · refine ⟨x.val, ?_, ?_⟩
          · simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq]
            exact ⟨hxsel, hxc⟩
          · simp [hxlt]
        · refine ⟨mate x.val, ?_, ?_⟩
          · simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq]
            exact ⟨hmsel, by rw [hclip_mate_div2 x]; exact hxc⟩
          · have hnotlt : ¬ (mate x.val < x.val) := by omega
            simp [hmate_invol, hnotlt]
    rw [htouched_eq, ← hPairs_card]
    constructor
    · intro hlt
      have hne : TouchedPairs ≠ Pairs := fun h => by rw [h] at hlt; omega
      have hss : TouchedPairs ⊂ Pairs := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, hne⟩
      obtain ⟨x, hxP, hxNT⟩ := Finset.exists_of_ssubset hss
      simp only [TouchedPairs, Finset.mem_filter, not_and, not_or] at hxNT
      have hboth := hxNT hxP
      simp only [Pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxP
      exact ⟨x, hxP.2, Bool.eq_false_iff.mpr hboth.1, Bool.eq_false_iff.mpr hboth.2⟩
    · rintro ⟨x, hxc, hxf, hmf⟩
      let x₀ : Fin (2 ^ k) := if x.val < mate x.val then x else ⟨mate x.val, hmate_lt x.val x.isLt⟩
      have hx₀P : x₀ ∈ Pairs := by
        dsimp only [x₀]
        split_ifs with hlt
        · simp only [Pairs, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hlt, hxc⟩
        · simp only [Pairs, Finset.mem_filter, Finset.mem_univ, true_and]
          have hne := hmate_ne x.val
          exact ⟨by rw [hmate_invol]; omega, by rw [hclip_mate_div2 x]; exact hxc⟩
      have hx₀NT : x₀ ∉ TouchedPairs := by
        simp only [TouchedPairs, Finset.mem_filter, not_and, not_or]
        intro _
        dsimp only [x₀]
        split_ifs
        · exact ⟨by simp [hxf], by simp [hmf]⟩
        · exact ⟨by simp [hmf], by simp [hmate_invol, hxf]⟩
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.filter_subset _ _, fun h => hx₀NT (h ▸ hx₀P)⟩)

  have hgoal2 : ∀ y z : Fin (2 ^ q),
      (∃ base : Fin (2 ^ k), wordOut base.val = y.val ∧ wordOut (mate base.val) = z.val) ↔
        (∃ p ∈ selected, (wordOut p = y.val ∧ wordOut (mate p) = z.val) ∨
          (wordOut p = z.val ∧ wordOut (mate p) = y.val)) ∨
        (z.val = (y.val ^^^ 1) ∧ touched (y.val / 2) < 2 ^ (k - q)) := by
    intro y z
    have hydiv : y.val / 2 < 2 ^ (q - 1) := by
      have : 2 ^ q = 2 * 2 ^ (q - 1) := by
        conv_lhs => rw [show q = (q - 1) + 1 by omega, pow_succ, mul_comm]
      omega
    constructor
    · rintro ⟨base, hby, hbz⟩
      by_cases hlow : lowTrace rowName.val base.val = true ∨ lowTrace rowName.val (mate base.val) = true
      · left
        rcases (hpair_sel base).mpr hlow with hsel | hmsel
        · exact ⟨base.val, hsel, Or.inl ⟨hby, hbz⟩⟩
        · exact ⟨mate base.val, hmsel, Or.inr ⟨hbz, by rw [hmate_invol]; exact hby⟩⟩
      · right
        push Not at hlow
        have hbf : lowTrace rowName.val base.val = false := Bool.eq_false_iff.mpr hlow.1
        have hmf : lowTrace rowName.val (mate base.val) = false := Bool.eq_false_iff.mpr hlow.2
        have h1 : y.val = clipped rowName.val base.val := by rw [← hby, hagree base hbf]
        have h2 : z.val = clipped rowName.val (mate base.val) := by
          rw [← hbz, hagree ⟨mate base.val, hmate_lt base.val base.isLt⟩ hmf]
        refine ⟨by rw [h2, hclip_mate base, ← h1], ?_⟩
        exact (htouched_lt (y.val / 2) hydiv).mpr ⟨base, by rw [← h1], hbf, hmf⟩
    · rintro (⟨p, hp, (⟨hpy, hpz⟩ | ⟨hpz, hpy⟩)⟩ | ⟨hzy, hlt⟩)
      · exact ⟨⟨p, ((hmem_sel p).mp hp).1⟩, hpy, hpz⟩
      · refine ⟨⟨mate p, hmate_lt p ((hmem_sel p).mp hp).1⟩, hpy, ?_⟩
        rw [hmate_invol]; exact hpz
      · obtain ⟨x, hxc, hxf, hmf⟩ := (htouched_lt (y.val / 2) hydiv).mp hlt
        have hwx : wordOut x.val = clipped rowName.val x.val := hagree x hxf
        have hwm : wordOut (mate x.val) = clipped rowName.val x.val ^^^ 1 := by
          rw [hagree ⟨mate x.val, hmate_lt x.val x.isLt⟩ hmf, hclip_mate x]
        have hor : clipped rowName.val x.val = y.val ∨ clipped rowName.val x.val = y.val ^^^ 1 := by
          have hbit : ∀ b, 1 ≤ b → (clipped rowName.val x.val).testBit b = y.val.testBit b := by
            intro b hb
            obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
            rw [← Nat.testBit_div_two, ← Nat.testBit_div_two, hxc]
          by_cases hb0 : (clipped rowName.val x.val).testBit 0 = y.val.testBit 0
          · left
            apply Nat.eq_of_testBit_eq
            intro b
            cases b with
            | zero => exact hb0
            | succ b' => exact hbit (b' + 1) (by omega)
          · right
            apply Nat.eq_of_testBit_eq
            intro b
            cases b with
            | zero =>
              rw [Nat.testBit_xor]
              change (clipped rowName.val x.val).testBit 0 = xor (y.val.testBit 0) true
              revert hb0
              cases (clipped rowName.val x.val).testBit 0 <;> cases y.val.testBit 0 <;> simp
            | succ b' =>
              rw [Nat.testBit_xor, big_false (show (1 : ℕ) < 2 ^ 1 by norm_num) (by omega), Bool.xor_false]
              exact hbit (b' + 1) (by omega)
        rcases hor with heq | heq
        · exact ⟨x, by rw [hwx, heq], by rw [hwm, heq, ← hzy]⟩
        · refine ⟨⟨mate x.val, hmate_lt x.val x.isLt⟩, ?_, ?_⟩
          · rw [hwm, heq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          · rw [hmate_invol, hwx, heq, ← hzy]

  refine ⟨hgoal1, hgoal2, ?_⟩
  intro hbud coloring
  have htouch_all : ∀ c : ℕ, touched c < 2 ^ (k - q) := fun c =>
    lt_of_le_of_lt (List.length_filter_le _ _) (lt_of_le_of_lt hgoal1 hbud)
  constructor
  · intro hall
    refine ⟨?_, fun rep hrep => hall ⟨rep, ((hmem_sel rep).mp hrep).1⟩⟩
    intro pair
    have h2p : 2 * pair.val < 2 ^ q := by
      have : 2 * 2 ^ (q - 1) = 2 ^ q := by
        conv_rhs => rw [show q = (q - 1) + 1 by omega, pow_succ, mul_comm]
      omega
    have h2p1 : 2 * pair.val + 1 < 2 ^ q := by
      have : 2 * 2 ^ (q - 1) = 2 ^ q := by
        conv_rhs => rw [show q = (q - 1) + 1 by omega, pow_succ, mul_comm]
      omega
    have hxor1 : 2 * pair.val + 1 = (2 * pair.val) ^^^ 1 := by
      apply Nat.eq_of_testBit_eq
      intro b
      cases b with
      | zero =>
        rw [Nat.testBit_xor]
        simp [Nat.testBit_zero]
      | succ b' =>
        rw [Nat.testBit_xor, big_false (show (1 : ℕ) < 2 ^ 1 by norm_num) (by omega), Bool.xor_false,
            ← Nat.testBit_div_two, ← Nat.testBit_div_two]
        congr 1; omega
    obtain ⟨base, hby, hbz⟩ := (hgoal2 ⟨2 * pair.val, h2p⟩ ⟨2 * pair.val + 1, h2p1⟩).mpr
      (Or.inr ⟨hxor1, htouch_all _⟩)
    have hf := hall base
    dsimp only [follows] at hf
    rwa [hby, hbz] at hf
  · rintro ⟨hpairs, hsel⟩ rawKey
    have hylt : wordOut rawKey.val < 2 ^ q := visOutF_lt k r q i.val rowName.val constants rawKey.val
    have hzlt : wordOut (mate rawKey.val) < 2 ^ q := visOutF_lt k r q i.val rowName.val constants (mate rawKey.val)
    have hedge := (hgoal2 ⟨wordOut rawKey.val, hylt⟩ ⟨wordOut (mate rawKey.val), hzlt⟩).mp
      ⟨rawKey, rfl, rfl⟩
    rcases hedge with ⟨p, hp, (⟨hpy, hpz⟩ | ⟨hpz, hpy⟩)⟩ | ⟨hzy, _⟩
    · have hf := hsel p hp
      dsimp only [follows] at hf ⊢
      dsimp only at hpy hpz
      rwa [← hpy, ← hpz]
    · have hf := hsel p hp
      dsimp only [follows] at hf ⊢
      dsimp only at hpy hpz
      rw [← hpy, ← hpz]
      exact Ne.symm hf
    · have hp_lt : wordOut rawKey.val / 2 < 2 ^ (q - 1) := by
        have : 2 ^ q = 2 * 2 ^ (q - 1) := by
          conv_lhs => rw [show q = (q - 1) + 1 by omega, pow_succ, mul_comm]
        omega
      have hpc : coloring (2 * (wordOut rawKey.val / 2)) ≠ coloring (2 * (wordOut rawKey.val / 2) + 1) :=
        hpairs ⟨wordOut rawKey.val / 2, hp_lt⟩
      dsimp only at hzy
      dsimp only [follows]
      have heven : ∀ a : ℕ, a % 2 = 0 → a ^^^ 1 = a + 1 := fun a ha => by
        apply Nat.eq_of_testBit_eq
        intro b
        cases b with
        | zero =>
          have h1 : (a + 1) % 2 = 1 := by omega
          rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero]
          simp [ha, h1]
        | succ b' =>
          rw [Nat.testBit_xor, big_false (show (1 : ℕ) < 2 ^ 1 by norm_num) (by omega), Bool.xor_false,
              ← Nat.testBit_div_two, ← Nat.testBit_div_two]
          congr 1; omega
      have hodd : ∀ a : ℕ, a % 2 = 1 → a ^^^ 1 = a - 1 := fun a ha => by
        have h1 : (a - 1) % 2 = 0 := by omega
        have h2 := heven (a - 1) h1
        rw [show a - 1 + 1 = a by omega] at h2
        conv_lhs => rw [← h2]
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rcases Nat.mod_two_eq_zero_or_one (wordOut rawKey.val) with h0 | h1
      · have h2 : wordOut rawKey.val = 2 * (wordOut rawKey.val / 2) := by omega
        have hz : wordOut (mate rawKey.val) = 2 * (wordOut rawKey.val / 2) + 1 := by
          rw [hzy, heven _ h0, ← h2]
        rw [hz]
        conv_lhs => rw [h2]
        exact hpc
      · have h2 : wordOut rawKey.val = 2 * (wordOut rawKey.val / 2) + 1 := by omega
        have hz : wordOut (mate rawKey.val) = 2 * (wordOut rawKey.val / 2) := by
          rw [hzy, hodd _ h1]; omega
        rw [hz]
        conv_lhs => rw [h2]
        exact Ne.symm hpc

end PEqualNP.Outside.L_meta_25628_aux

theorem PEqualNP.Outside.L_meta_25628 : (∀ (k r e q n : Nat) (i : Fin k) (constants : Nat → Fin (2^k)),
  0 < q → k + e + 3 = 5*r → n+4 ≤ r → 5*n+15 ≤ k → e+q ≤ n →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2^k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell+1) % k)) && word.testBit ((cell+2) % k))).toNat <<< cell)) 0
  let state := fun (row raw rounds : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k-1) prev) ^^^ rot (2*tick) raw ^^^
        (constants (tick+1)).val) (rot 1 raw ^^^ row)
  let visibleOutput := fun (row raw : Nat) => (List.range q).foldl (fun out bitNo =>
    out ||| (((state row raw r).testBit ((i.val + bitNo) % k)).toNat <<< bitNo)) 0
  let mate := fun (word : Nat) => word ^^^ (1 <<< ((i.val + k + 2 - 2*r) % k))
  let budget := 2^(k-n) * (∑ m ∈ Finset.range (e+q), Nat.choose n m)
  let cutSite := i.val + k + 3 - 2*r
  let lowTrace := fun (input nameKey : Nat) =>
    let weight := (List.range n).foldl (fun (ones tickNo : Nat) =>
      let now := 5 + tickNo
      let pos := cutSite + k - 3*now + ones
      let layer := state input nameKey (now-1)
      ones + (xor (xor (layer.testBit (pos % k)) (layer.testBit ((pos+1) % k)))
                   (layer.testBit ((pos+2) % k))).toNat) 0
    decide (weight < e+q)
  let clipped := fun (fixedRow candidate : Nat) =>
    let residue := fun (place : Int) => (place % (k : Int)).toNat
    let period := rot 1 candidate ^^^ fixedRow
    let start := fun (site : Int) => if site < (cutSite : Int) then period.testBit (residue site) else false
    let mix := fun (tape : Int → Bool) (atSite : Int) =>
      xor (xor (tape (atSite-1)) (tape atSite)) (tape (atSite+1))
    let finalTape := (List.range r).foldl (fun (previous : Int → Bool) (tick : Nat) (z : Int) =>
      let p := z + 1 - 2*(tick : Int)
      let ordinary := xor (mix previous z) (!(mix previous (z+1)) && mix previous (z+2))
      xor (xor (xor ordinary (start p)) (fixedRow.testBit (residue p)))
        ((constants (tick+1)).val.testBit (residue z))) start
    (List.range q).foldl (fun (total j : Nat) => total ||| ((finalTape ((i.val : Int)+(j : Int))).toNat <<< j)) 0
  ∀ rowName : Fin (2^k),
    let wordOut := visibleOutput rowName.val
    let selected := (List.range (2^k)).filter (fun w =>
      lowTrace rowName.val w && (decide (w < mate w) || !(lowTrace rowName.val (mate w))))
    let touched := fun (c : Nat) =>
      (selected.filter (fun v => clipped rowName.val v / 2 == c)).length
    let follows := fun (lab : Nat → Bool) (x : Nat) => lab (wordOut x) ≠ lab (wordOut (mate x))
    selected.length ≤ budget ∧
    (∀ y z : Fin (2^q),
      (∃ base : Fin (2^k), wordOut base.val = y.val ∧ wordOut (mate base.val) = z.val) ↔
        (∃ p ∈ selected, (wordOut p = y.val ∧ wordOut (mate p) = z.val) ∨
          (wordOut p = z.val ∧ wordOut (mate p) = y.val)) ∨
        (z.val = (y.val ^^^ 1) ∧ touched (y.val / 2) < 2^(k-q))) ∧
    (budget < 2^(k-q) → ∀ coloring : Nat → Bool,
      (∀ rawKey : Fin (2^k), follows coloring rawKey.val) ↔
        (∀ pair : Fin (2^(q-1)), coloring (2*pair.val) ≠ coloring (2*pair.val+1)) ∧
        ∀ representative ∈ selected, follows coloring representative)) :=
  PEqualNP.Outside.L_meta_25628_aux.prove_25628

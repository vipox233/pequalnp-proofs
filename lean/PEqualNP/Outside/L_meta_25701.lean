import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25701

theorem boolcore : ∀ x1 x2 x3 x4 x5 x6 y1 y2 y3 : Bool,
    xor (xor x1 x5) (xor x3 x6) = xor y1 y3 → xor (xor x2 x5) (xor x4 x6) = xor y2 y3 →
    xor (xor x1 x2) (xor x1 x2) = xor y1 y2 → x1 = x2 → x3 = x4 := by decide

theorem xcancel : ∀ s x y : Bool, xor s x = xor s y → x = y := by decide

theorem boxzero : ∀ s s' t : Bool,
    xor (xor (xor s true) (xor s' true)) (xor (xor s t) (xor s' t)) = false := by decide

theorem arith (k a h : ℕ) (h1 : a + 2 ≤ h) (h2 : h ≤ k) :
    h * (2 * 2^(k-h)) ≤ (a+1) * 2^(k-a) := by
  obtain ⟨d, rfl⟩ : ∃ d, h = a + 2 + d := ⟨h - (a+2), by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, k = a + 2 + d + e := ⟨k - (a+2+d), by omega⟩
  have e1 : a + 2 + d + e - (a + 2 + d) = e := by omega
  have e2 : a + 2 + d + e - a = (d + 2) + e := by omega
  rw [e1, e2, pow_add]
  have hd : d + 2 ≤ 2^(d+1) := by
    have := @Nat.lt_two_pow_self (d+1)
    omega
  have h3 : 2^(d+2) = 2 * 2^(d+1) := by ring
  have h4 : (a + 2 + d) * 2 ≤ (a+1) * 2^(d+2) := by
    rw [h3]
    nlinarith [Nat.mul_le_mul_left (a+1) hd, Nat.zero_le (a*d)]
  calc (a+2+d) * (2 * 2^e) = ((a+2+d)*2) * 2^e := by ring
    _ ≤ ((a+1) * 2^(d+2)) * 2^e := Nat.mul_le_mul_right _ h4
    _ = (a+1) * (2^(d+2) * 2^e) := by ring

theorem upper (k a : ℕ) (hk : 2^a ≤ k)
    (π : Equiv.Perm (Fin (2^k))) (K L : Finset (Fin (2^k)))
    (h : ∀ i ∈ K, ∀ j ∈ K,
      xor (xor (i.val.testBit ((π i).val % 2^a)) (j.val.testBit ((π j).val % 2^a)))
          (xor (i.val.testBit ((π j).val % 2^a)) (j.val.testBit ((π i).val % 2^a))) =
        xor (decide (i ∈ L)) (decide (j ∈ L))) :
    K.card ≤ (a+1)*2^(k-a) := by
  classical
  have ha2 : a < 2^a := Nat.lt_two_pow_self
  obtain ⟨c, hc⟩ : ∃ c : Fin (2^k) → ℕ, ∀ i, c i = (π i).val % 2^a := ⟨_, fun _ => rfl⟩
  simp only [← hc] at h
  have hcA : ∀ i, c i < 2^a := fun i => by rw [hc]; exact Nat.mod_lt _ (Nat.two_pow_pos a)
  have hTk : K.image c ⊆ Finset.range k := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_range.mpr (lt_of_lt_of_le (hcA i) hk)
  have hTcard : (K.image c).card ≤ k := by simpa using Finset.card_le_card hTk
  have hsum : K.card = ∑ p ∈ K.image c, (K.filter (fun i => c i = p)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi => Finset.mem_image_of_mem c hi)
  have h2k : 2^k = 2^a * 2^(k-a) := by
    rw [← pow_add]; congr 1; omega
  have b1 : ∀ p, (K.filter (fun i => c i = p)).card ≤ 2^(k-a) := by
    intro p
    have hle : (K.filter (fun i => c i = p)).card ≤ (Finset.range (2^(k-a))).card := by
      apply Finset.card_le_card_of_injOn (fun i => (π i).val / 2^a)
      · intro i _
        refine Finset.mem_coe.mpr (Finset.mem_range.mpr ?_)
        show (π i).val / 2^a < 2^(k-a)
        apply Nat.div_lt_of_lt_mul
        rw [← h2k]
        exact (π i).isLt
      · intro i hi j hj e
        have hi' := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
        have hj' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        rw [hc] at hi' hj'
        have e' : (π i).val / 2^a = (π j).val / 2^a := e
        have e2 : (π i).val = (π j).val := by
          calc (π i).val = 2^a * ((π i).val / 2^a) + (π i).val % 2^a := (Nat.div_add_mod _ _).symm
            _ = 2^a * ((π j).val / 2^a) + (π j).val % 2^a := by rw [e', hi', hj']
            _ = (π j).val := Nat.div_add_mod _ _
        exact π.injective (Fin.ext e2)
    simpa using hle
  have b2 : ∀ p, (K.filter (fun i => c i = p)).card ≤ 2 * 2^(k - (K.image c).card) := by
    intro p
    have hcard : ((Finset.univ : Finset Bool) ×ˢ (Finset.range k \ K.image c).powerset).card
        = 2 * 2^(k - (K.image c).card) := by
      rw [Finset.card_product, Finset.card_powerset, Finset.card_sdiff_of_subset hTk]
      simp
    rw [← hcard]
    apply Finset.card_le_card_of_injOn (fun i => (i.val.testBit p,
      (Finset.range k \ K.image c).filter (fun q => i.val.testBit q = true)))
    · intro i _
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr
        ⟨Finset.mem_univ _, Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩)
    · intro i hi i' hi' e
      obtain ⟨hiK, hci⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
      obtain ⟨hi'K, hci'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hi')
      have e1 : i.val.testBit p = i'.val.testBit p := congrArg Prod.fst e
      have e2 : (Finset.range k \ K.image c).filter (fun q => i.val.testBit q = true)
          = (Finset.range k \ K.image c).filter (fun q => i'.val.testBit q = true) :=
        congrArg Prod.snd e
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro q
      by_cases hqk : k ≤ q
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hqk)),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le i'.isLt (Nat.pow_le_pow_right (by norm_num) hqk))]
      · by_cases hqT : q ∈ K.image c
        · obtain ⟨r, hrK, hrc⟩ := Finset.mem_image.mp hqT
          have h1 := h i hiK r hrK
          have h2 := h i' hi'K r hrK
          have h3 := h i hiK i' hi'K
          rw [hci, hrc] at h1
          rw [hci', hrc] at h2
          rw [hci, hci'] at h3
          exact boolcore _ _ _ _ _ _ _ _ _ h1 h2 h3 e1
        · have hq' : q ∈ Finset.range k \ K.image c :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega), hqT⟩
          rw [Bool.eq_iff_iff]
          constructor
          · intro hb
            have hm : q ∈ (Finset.range k \ K.image c).filter (fun q => i.val.testBit q = true) :=
              Finset.mem_filter.mpr ⟨hq', hb⟩
            rw [e2] at hm
            exact (Finset.mem_filter.mp hm).2
          · intro hb
            have hm : q ∈ (Finset.range k \ K.image c).filter (fun q => i'.val.testBit q = true) :=
              Finset.mem_filter.mpr ⟨hq', hb⟩
            rw [← e2] at hm
            exact (Finset.mem_filter.mp hm).2
  rw [hsum]
  by_cases hh : (K.image c).card ≤ a + 1
  · calc ∑ p ∈ K.image c, (K.filter (fun i => c i = p)).card
        ≤ (K.image c).card • 2^(k-a) := Finset.sum_le_card_nsmul _ _ _ (fun p _ => b1 p)
      _ = (K.image c).card * 2^(k-a) := smul_eq_mul _ _
      _ ≤ (a+1) * 2^(k-a) := Nat.mul_le_mul_right _ hh
  · calc ∑ p ∈ K.image c, (K.filter (fun i => c i = p)).card
        ≤ (K.image c).card • (2 * 2^(k - (K.image c).card)) :=
          Finset.sum_le_card_nsmul _ _ _ (fun p _ => b2 p)
      _ = (K.image c).card * (2 * 2^(k - (K.image c).card)) := smul_eq_mul _ _
      _ ≤ (a+1) * 2^(k-a) := arith k a _ (by omega) hTcard

def low (a p : ℕ) (s : Bool) : ℕ := if s then 2^(a+1) - (2^p + 1) else 2^p

def row (a p w : ℕ) : ℕ := 2^(a+1) * (w / 2) + low a p (decide (w % 2 = 1))

def col (a p w : ℕ) : ℕ := 2^a * w + p

theorem low_lt (a p : ℕ) (s : Bool) (hp : p ≤ a) : low a p s < 2^(a+1) := by
  have h1 : 2^p < 2^(a+1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  cases s
  · show 2^p < 2^(a+1)
    exact h1
  · show 2^(a+1) - (2^p + 1) < 2^(a+1)
    exact Nat.sub_lt (Nat.two_pow_pos _) (Nat.succ_pos _)

theorem low_bit (a p q : ℕ) (s : Bool) (hp : p ≤ a) (hq : q ≤ a) :
    (low a p s).testBit q = xor s (decide (p = q)) := by
  have h1 : 2^p < 2^(a+1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hq' : q < a + 1 := by omega
  cases s
  · show (2^p).testBit q = xor false (decide (p = q))
    rw [Nat.testBit_two_pow, Bool.false_xor]
  · show (2^(a+1) - (2^p + 1)).testBit q = xor true (decide (p = q))
    rw [Nat.testBit_two_pow_sub_succ h1, Nat.testBit_two_pow, Bool.true_xor, decide_eq_true hq',
      Bool.true_and]

theorem row_bit (a p w q : ℕ) (hp : p ≤ a) (hq : q ≤ a) :
    (row a p w).testBit q = xor (decide (w % 2 = 1)) (decide (p = q)) := by
  have hq' : q < a + 1 := by omega
  unfold row
  rw [Nat.testBit_two_pow_mul_add _ (low_lt a p _ hp), low_bit a p q _ hp hq]
  simp only [hq', ↓reduceIte]

theorem row_lt (k a p w : ℕ) (hak : a + 1 ≤ k) (hp : p ≤ a) (hw : w < 2^(k-a)) :
    row a p w < 2^k := by
  have h1 := low_lt a p (decide (w % 2 = 1)) hp
  have h2 : 2^(k-a) = 2 * 2^(k-a-1) := by
    rw [← pow_succ']; congr 1; omega
  have h3 : 2^k = 2^(a+1) * 2^(k-a-1) := by
    rw [← pow_add]; congr 1; omega
  have h4 : w / 2 + 1 ≤ 2^(k-a-1) := by omega
  unfold row
  calc 2^(a+1) * (w/2) + low a p (decide (w % 2 = 1)) < 2^(a+1) * (w/2) + 2^(a+1) := by omega
    _ = 2^(a+1) * (w/2 + 1) := by ring
    _ ≤ 2^(a+1) * 2^(k-a-1) := Nat.mul_le_mul_left _ h4
    _ = 2^k := h3.symm

theorem row_div (a p w : ℕ) (hp : p ≤ a) : row a p w / 2^(a+1) = w / 2 := by
  unfold row
  rw [Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (low_lt a p _ hp), Nat.add_zero]

theorem row_inj (a p w p' w' : ℕ) (ha : 2 ≤ a) (hp : p ≤ a) (hp' : p' ≤ a)
    (e : row a p w = row a p' w') : p = p' ∧ w = w' := by
  have hb : ∀ q, q ≤ a → xor (decide (w % 2 = 1)) (decide (p = q))
      = xor (decide (w' % 2 = 1)) (decide (p' = q)) := by
    intro q hq
    rw [← row_bit a p w q hp hq, ← row_bit a p' w' q hp' hq, e]
  have hd : w / 2 = w' / 2 := by
    rw [← row_div a p w hp, ← row_div a p' w' hp', e]
  obtain ⟨q, hq2, hqp, hqp'⟩ : ∃ q, q ≤ 2 ∧ p ≠ q ∧ p' ≠ q := by
    by_cases h0 : p ≠ 0 ∧ p' ≠ 0
    · exact ⟨0, by omega⟩
    · by_cases h1 : p ≠ 1 ∧ p' ≠ 1
      · exact ⟨1, by omega⟩
      · exact ⟨2, by omega⟩
  have hs : decide (w % 2 = 1) = decide (w' % 2 = 1) := by
    have h2 := hb q (by omega)
    rw [decide_eq_false hqp, decide_eq_false hqp', Bool.xor_false, Bool.xor_false] at h2
    exact h2
  have h1 := hb p hp
  rw [hs] at h1
  have h3 := xcancel _ _ _ h1
  rw [decide_eq_true rfl] at h3
  have hpp : p' = p := of_decide_eq_true h3.symm
  have hw := decide_eq_decide.mp hs
  exact ⟨hpp.symm, by omega⟩

theorem col_lt (k a p w : ℕ) (hak : a ≤ k) (hp : p < 2^a) (hw : w < 2^(k-a)) :
    col a p w < 2^k := by
  have h3 : 2^k = 2^a * 2^(k-a) := by
    rw [← pow_add]; congr 1; omega
  unfold col
  calc 2^a * w + p < 2^a * w + 2^a := by omega
    _ = 2^a * (w+1) := by ring
    _ ≤ 2^a * 2^(k-a) := Nat.mul_le_mul_left _ hw
    _ = 2^k := h3.symm

theorem col_mod (a p w : ℕ) (hp : p < 2^a) : col a p w % 2^a = p := by
  unfold col
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hp]

theorem col_div (a p w : ℕ) (hp : p < 2^a) : col a p w / 2^a = w := by
  unfold col
  rw [Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hp, Nat.add_zero]

theorem lower (k a : ℕ) (ha : 2 ≤ a) (hk : 2^a ≤ k) :
    ∃ (π : Equiv.Perm (Fin (2^k))) (K : Finset (Fin (2^k))), (a+1)*2^(k-a) ≤ K.card ∧
      ∀ i ∈ K, ∀ j ∈ K,
        xor (xor (i.val.testBit ((π i).val % 2^a)) (j.val.testBit ((π j).val % 2^a)))
            (xor (i.val.testBit ((π j).val % 2^a)) (j.val.testBit ((π i).val % 2^a))) = false := by
  classical
  have ha2 : a < 2^a := Nat.lt_two_pow_self
  have hak : a + 1 ≤ k := by omega
  have hpos : 0 < 2^k := Nat.two_pow_pos k
  obtain ⟨rowF, hrowF⟩ : ∃ rowF : ℕ × ℕ → Fin (2^k), ∀ pw, (rowF pw).val = row a pw.1 pw.2 % 2^k :=
    ⟨fun pw => ⟨row a pw.1 pw.2 % 2^k, Nat.mod_lt _ hpos⟩, fun _ => rfl⟩
  obtain ⟨colF, hcolF⟩ : ∃ colF : ℕ × ℕ → Fin (2^k), ∀ pw, (colF pw).val = col a pw.1 pw.2 % 2^k :=
    ⟨fun pw => ⟨col a pw.1 pw.2 % 2^k, Nat.mod_lt _ hpos⟩, fun _ => rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Finset (ℕ × ℕ), P = Finset.range (a+1) ×ˢ Finset.range (2^(k-a)) :=
    ⟨_, rfl⟩
  have hP : ∀ pw ∈ P, pw.1 ≤ a ∧ pw.2 < 2^(k-a) := by
    intro pw hpw
    rw [hPdef, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hpw
    omega
  have hrow : ∀ pw ∈ P, (rowF pw).val = row a pw.1 pw.2 := fun pw hpw => by
    rw [hrowF]
    exact Nat.mod_eq_of_lt (row_lt k a _ _ hak (hP pw hpw).1 (hP pw hpw).2)
  have hcol : ∀ pw ∈ P, (colF pw).val = col a pw.1 pw.2 := fun pw hpw => by
    rw [hcolF]
    exact Nat.mod_eq_of_lt (col_lt k a _ _ (by omega) (by have := (hP pw hpw).1; omega) (hP pw hpw).2)
  have hrinj : ∀ pw ∈ P, ∀ pw' ∈ P, rowF pw = rowF pw' → pw = pw' := by
    intro pw hpw pw' hpw' e
    have e' : row a pw.1 pw.2 = row a pw'.1 pw'.2 := by
      rw [← hrow pw hpw, ← hrow pw' hpw', e]
    obtain ⟨e1, e2⟩ := row_inj a _ _ _ _ ha (hP pw hpw).1 (hP pw' hpw').1 e'
    exact Prod.ext e1 e2
  have hf : ∀ pw ∈ P, rowF ((colF pw).val % 2^a, (colF pw).val / 2^a) = rowF pw := by
    intro pw hpw
    have hp : pw.1 < 2^a := by have := (hP pw hpw).1; omega
    rw [hcol pw hpw, col_mod a _ _ hp, col_div a _ _ hp]
  have hfinj : Set.InjOn (fun y : Fin (2^k) => rowF (y.val % 2^a, y.val / 2^a))
      (P.image colF : Finset (Fin (2^k))) := by
    intro y hy y' hy' e
    obtain ⟨pw, hpw, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    obtain ⟨pw', hpw', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy')
    have e' : rowF ((colF pw).val % 2^a, (colF pw).val / 2^a)
        = rowF ((colF pw').val % 2^a, (colF pw').val / 2^a) := e
    rw [hf pw hpw, hf pw' hpw'] at e'
    rw [hrinj pw hpw pw' hpw' e']
  obtain ⟨σ, hσ⟩ := Finset.exists_equiv_extend_of_card_eq
    (t := (Finset.univ : Finset (Fin (2^k)))) Finset.card_univ.symm (Finset.subset_univ _) hfinj
  have hπ : ∀ pw ∈ P,
      (σ.trans (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x))).symm (rowF pw) = colF pw := by
    intro pw hpw
    rw [Equiv.symm_apply_eq]
    have h1 := hσ (colF pw) (Finset.mem_image_of_mem _ hpw)
    have h2 : (σ (colF pw) : Fin (2^k)) = rowF pw := by
      rw [h1]; exact hf pw hpw
    exact h2.symm
  refine ⟨(σ.trans (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x))).symm, P.image rowF, ?_, ?_⟩
  · have hc : (P.image rowF).card = P.card :=
      Finset.card_image_of_injOn (fun pw hpw pw' hpw' e =>
        hrinj pw (Finset.mem_coe.mp hpw) pw' (Finset.mem_coe.mp hpw') e)
    rw [hc, hPdef, Finset.card_product, Finset.card_range, Finset.card_range]
  · intro i hi j hj
    obtain ⟨pw, hpw, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨pw', hpw', rfl⟩ := Finset.mem_image.mp hj
    have hp : pw.1 < 2^a := by have := (hP pw hpw).1; omega
    have hp' : pw'.1 < 2^a := by have := (hP pw' hpw').1; omega
    rw [hπ pw hpw, hπ pw' hpw', hcol pw hpw, hcol pw' hpw', col_mod a _ _ hp, col_mod a _ _ hp',
      hrow pw hpw, hrow pw' hpw',
      row_bit a pw.1 pw.2 pw.1 (hP pw hpw).1 (hP pw hpw).1,
      row_bit a pw'.1 pw'.2 pw'.1 (hP pw' hpw').1 (hP pw' hpw').1,
      row_bit a pw.1 pw.2 pw'.1 (hP pw hpw).1 (hP pw' hpw').1,
      row_bit a pw'.1 pw'.2 pw.1 (hP pw' hpw').1 (hP pw hpw).1,
      decide_eq_true (rfl : pw.1 = pw.1), decide_eq_true (rfl : pw'.1 = pw'.1),
      decide_eq_decide.mpr (eq_comm : pw'.1 = pw.1 ↔ pw.1 = pw'.1)]
    exact boxzero _ _ _

end PEqualNP.Outside.L_meta_25701

theorem PEqualNP.Outside.L_meta_25701 : ∀ (k a u m : ℕ), 2 ≤ a → 2^a ≤ k →
  let N := 2^k
  let F := fun (x y : Fin N) => x.val.testBit (y.val % 2^a)
  ((∃ (π : Equiv.Perm (Fin N)) (K L : Finset (Fin N)),
    m ≤ K.card ∧ L ⊆ K ∧ L.card ≤ u ∧
    ∀ i ∈ K, ∀ j ∈ K,
      xor (xor (F i (π i)) (F j (π j))) (xor (F i (π j)) (F j (π i))) =
        xor (decide (i ∈ L)) (decide (j ∈ L))) ↔
    m ≤ (a+1)*2^(k-a)) := by
  intro k a u m ha hk
  dsimp only
  constructor
  · rintro ⟨π, K, L, hm, _, _, h⟩
    exact hm.trans (PEqualNP.Outside.L_meta_25701.upper k a hk π K L h)
  · intro hm
    obtain ⟨π, K, hK, h⟩ := PEqualNP.Outside.L_meta_25701.lower k a ha hk
    refine ⟨π, K, ∅, hm.trans hK, Finset.empty_subset _, by simp, ?_⟩
    intro i hi j hj
    rw [h i hi j hj]
    simp

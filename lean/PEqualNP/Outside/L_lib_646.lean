import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_646_aux

def sym0 {q : ℕ} (hq : 2 ≤ q) : Fin q := ⟨0, by omega⟩
def sym1 {q : ℕ} (hq : 2 ≤ q) : Fin q := ⟨1, by omega⟩

def constVec {q m : ℕ} (c : Fin q) : Fin m → Fin q := fun _ => c

def boolToSym {q : ℕ} (hq : 2 ≤ q) (b : Bool) : Fin q :=
  if b then sym1 hq else sym0 hq

def boolVecToW {q m : ℕ} (hq : 2 ≤ q) (v : Fin m → Bool) : Fin m → Fin q :=
  fun i => boolToSym hq (v i)

def posBitVec {q m : ℕ} (hq : 2 ≤ q) (r : ℕ) : Fin m → Fin q :=
  fun i => if i.val.testBit r then sym1 hq else sym0 hq

def negBitVec {q m : ℕ} (hq : 2 ≤ q) (r : ℕ) : Fin m → Fin q :=
  fun i => if i.val.testBit r then sym0 hq else sym1 hq

lemma sym0_ne_sym1 {q : ℕ} (hq : 2 ≤ q) : sym0 hq ≠ sym1 hq := by
  intro h
  have hv := congrArg Fin.val h
  simp [sym0, sym1] at hv

lemma testBit_diff_of_lt_two_pow {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) (hne : a ≠ b) :
    ∃ r < k, a.testBit r ≠ b.testBit r := by
  by_contra hall
  push Not at hall
  apply hne
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < k
  · exact hall r hr
  · have hge : k ≤ r := Nat.le_of_not_lt hr
    have ha2 : a < 2 ^ r := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hge)
    have hb2 : b < 2 ^ r := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hge)
    rw [Nat.testBit_lt_two_pow ha2, Nat.testBit_lt_two_pow hb2]

lemma part3 {q m : ℕ} (hq : 2 ≤ q) (hqm : q = m) :
    ∃ C : Finset (Fin m → Fin q),
      (∀ w : Fin m → Fin q, ∃ y ∈ C, ∀ i, y i ≠ w i) ∧
      C.card ≤ q + 2 * Nat.clog 2 q := by
  classical
  let k := Nat.clog 2 q
  let Cconsts : Finset (Fin m → Fin q) := Finset.univ.image constVec
  let Cpos : Finset (Fin m → Fin q) := (Finset.range k).image (posBitVec hq)
  let Cneg : Finset (Fin m → Fin q) := (Finset.range k).image (negBitVec hq)
  let C := Cconsts ∪ Cpos ∪ Cneg
  refine ⟨C, ?_, ?_⟩
  · intro w
    by_cases hsurj : Function.Surjective w
    · have hcard_eq : Fintype.card (Fin m) = Fintype.card (Fin q) := by
        simp [hqm]
      have hbij : Function.Bijective w :=
        (Fintype.bijective_iff_surjective_and_card w).mpr ⟨hsurj, hcard_eq⟩
      rcases hbij.2 (sym0 hq) with ⟨i0, hi0⟩
      rcases hbij.2 (sym1 hq) with ⟨i1, hi1⟩
      have hi01 : i0 ≠ i1 := by
        intro heq
        apply sym0_ne_sym1 hq
        rw [← hi0, ← hi1, heq]
      have hval_ne : i0.val ≠ i1.val := Fin.val_ne_of_ne hi01
      have hm_le : m ≤ 2 ^ k := by
        rw [← hqm]
        exact Nat.le_pow_clog (by decide : 1 < 2) q
      have hi0_lt : i0.val < 2 ^ k := lt_of_lt_of_le i0.isLt hm_le
      have hi1_lt : i1.val < 2 ^ k := lt_of_lt_of_le i1.isLt hm_le
      rcases testBit_diff_of_lt_two_pow hi0_lt hi1_lt hval_ne with ⟨r, hrk, hbit⟩
      cases hb0 : i0.val.testBit r
      · have hb1 : i1.val.testBit r = true := by
          cases hb : i1.val.testBit r
          · exfalso; exact hbit (hb0.trans hb.symm)
          · rfl
        refine ⟨negBitVec hq r, ?_, ?_⟩
        · apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hrk, rfl⟩
        · intro i
          by_cases h0 : i = i0
          · subst h0
            simp [negBitVec, hb0, hi0, (sym0_ne_sym1 hq).symm]
          · by_cases h1 : i = i1
            · subst h1
              simp [negBitVec, hb1, hi1, sym0_ne_sym1 hq]
            · have hwi0 : w i ≠ sym0 hq := fun h => h0 (hbij.1 (h.trans hi0.symm))
              have hwi1 : w i ≠ sym1 hq := fun h => h1 (hbij.1 (h.trans hi1.symm))
              dsimp [negBitVec]
              split_ifs
              · exact hwi0.symm
              · exact hwi1.symm
      · have hb1 : i1.val.testBit r = false := by
          cases hb : i1.val.testBit r
          · rfl
          · exfalso; exact hbit (hb0.trans hb.symm)
        refine ⟨posBitVec hq r, ?_, ?_⟩
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hrk, rfl⟩
        · intro i
          by_cases h0 : i = i0
          · subst h0
            simp [posBitVec, hb0, hi0, (sym0_ne_sym1 hq).symm]
          · by_cases h1 : i = i1
            · subst h1
              simp [posBitVec, hb1, hi1, sym0_ne_sym1 hq]
            · have hwi0 : w i ≠ sym0 hq := fun h => h0 (hbij.1 (h.trans hi0.symm))
              have hwi1 : w i ≠ sym1 hq := fun h => h1 (hbij.1 (h.trans hi1.symm))
              dsimp [posBitVec]
              split_ifs
              · exact hwi1.symm
              · exact hwi0.symm
    · unfold Function.Surjective at hsurj
      push Not at hsurj
      rcases hsurj with ⟨c, hc⟩
      refine ⟨constVec c, ?_, ?_⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
      · intro i
        exact (hc i).symm
  · have hc1 : Cconsts.card ≤ q := by
      calc Cconsts.card ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
        _ = q := by simp
    have hc2 : Cpos.card ≤ k := by
      calc Cpos.card ≤ (Finset.range k).card := Finset.card_image_le
        _ = k := Finset.card_range k
    have hc3 : Cneg.card ≤ k := by
      calc Cneg.card ≤ (Finset.range k).card := Finset.card_image_le
        _ = k := Finset.card_range k
    calc C.card ≤ (Cconsts ∪ Cpos).card + Cneg.card := Finset.card_union_le _ _
      _ ≤ Cconsts.card + Cpos.card + Cneg.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ q + k + k := by omega
      _ = q + 2 * k := by omega

lemma two_mul_pred_pow_lt_pow {M : ℕ} (hM : 2 ≤ M) : 2 * (M - 1) ^ M < M ^ M := by
  have hbernoulli : ∀ (a k : ℕ), a ^ k + k * a ^ (k - 1) ≤ (a + 1) ^ k := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih =>
      cases k with
      | zero => simp
      | succ k =>
        have hsub1 : k + 1 + 1 - 1 = k + 1 := rfl
        have hsub0 : k + 1 - 1 = k := rfl
        rw [hsub1]
        rw [hsub0] at ih
        calc a ^ (k + 2) + (k + 2) * a ^ (k + 1)
            = a * (a ^ (k + 1) + (k + 1) * a ^ k) + a ^ (k + 1) := by ring
          _ ≤ a * (a + 1) ^ (k + 1) + (a + 1) ^ (k + 1) :=
              Nat.add_le_add (Nat.mul_le_mul_left a ih) (Nat.pow_le_pow_left (by omega) _)
          _ = (a + 1) ^ (k + 2) := by ring
  let d := M - 2
  have hM1 : M - 1 = d + 1 := by omega
  have hM2 : M = d + 2 := by omega
  have hb := hbernoulli (d + 1) (d + 1)
  have hsub : d + 1 - 1 = d := rfl
  rw [hsub] at hb
  have hterm : (d + 1) * (d + 1) ^ d = (d + 1) ^ (d + 1) := by rw [pow_succ']
  have hd2 : d + 1 + 1 = d + 2 := rfl
  rw [hd2, hterm] at hb
  have h1 : 2 * (d + 1) ^ (d + 1) ≤ (d + 2) ^ (d + 1) := by linarith
  calc 2 * (M - 1) ^ M = 2 * (d + 1) ^ (d + 2) := by rw [hM1, hM2]
    _ = (d + 1) * (2 * (d + 1) ^ (d + 1)) := by ring
    _ ≤ (d + 1) * (d + 2) ^ (d + 1) := Nat.mul_le_mul_left (d + 1) h1
    _ < (d + 2) * (d + 2) ^ (d + 1) := by
      apply Nat.mul_lt_mul_of_pos_right (by omega)
      positivity
    _ = M ^ M := by rw [← pow_succ', ← hM2]

lemma card_match_pattern {m : ℕ} (S : Finset (Fin m)) (p : S → Bool) :
    (Finset.univ.filter (fun v : Fin m → Bool => ∀ i : S, v i.1 = p i)).card = 2 ^ (m - S.card) := by
  classical
  let e : {v : Fin m → Bool // ∀ i : S, v i.1 = p i} ≃ ({i : Fin m // i ∉ S} → Bool) :=
    { toFun := fun v j => v.1 j.1
      invFun := fun u => ⟨fun i => if hi : i ∈ S then p ⟨i, hi⟩ else u ⟨i, hi⟩,
        fun ⟨i, hi⟩ => by simp [hi]⟩
      left_inv := by
        rintro ⟨v, hv⟩
        ext i
        dsimp
        by_cases hi : i ∈ S
        · simp [hi, hv ⟨i, hi⟩]
        · simp [hi]
      right_inv := by
        intro u
        ext ⟨j, hj⟩
        simp [hj] }
  have h1 : (Finset.univ.filter (fun v : Fin m → Bool => ∀ i : S, v i.1 = p i)).card =
      Fintype.card {v : Fin m → Bool // ∀ i : S, v i.1 = p i} := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact
      { toFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
        invFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h1, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool]
  congr 1
  have hcompl : Fintype.card {i : Fin m // i ∉ S} = (Sᶜ : Finset (Fin m)).card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact
      { toFun := fun x => ⟨x.1, Finset.mem_compl.mpr x.2⟩
        invFun := fun x => ⟨x.1, Finset.mem_compl.mp x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hcompl, Finset.card_compl, Fintype.card_fin]

lemma card_bad_vec {m t : ℕ} (S : Finset (Fin m)) (hS : S.card = t) (p : S → Bool) :
    (Finset.univ.filter (fun v : Fin m → Bool => ¬ ∀ i : S, v i.1 = p i)).card =
      2 ^ (m - t) * (2 ^ t - 1) := by
  classical
  have hle : t ≤ m := by
    rw [← hS]
    calc S.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ S
      _ = m := Fintype.card_fin m
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m → Bool))) (fun v => ∀ i : S, v i.1 = p i)
  have huniv : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by
    simp
  rw [card_match_pattern S p, hS, huniv] at htot
  have hpow : 2 ^ m = 2 ^ (m - t) * 2 ^ t := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have h1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  rw [Nat.mul_sub_left_distrib, mul_one, ← hpow]
  omega

lemma choose_le_pow_self (m t : ℕ) : m.choose t ≤ m ^ t := by
  induction m generalizing t with
  | zero =>
    cases t with
    | zero => simp
    | succ t => simp
  | succ m ih =>
    cases t with
    | zero => simp
    | succ t =>
      rw [Nat.choose_succ_succ]
      have h1 : m.choose t ≤ m ^ t := ih t
      have h2 : m.choose (t + 1) ≤ m ^ (t + 1) := ih (t + 1)
      have h3 : m ^ (t + 1) = m * m ^ t := by rw [pow_succ']
      have h4 : m ^ t ≤ (m + 1) ^ t := Nat.pow_le_pow_left (by omega) t
      calc m.choose t + m.choose (t + 1) ≤ m ^ t + m * m ^ t := by linarith
        _ = (m + 1) * m ^ t := by ring
        _ ≤ (m + 1) * (m + 1) ^ t := Nat.mul_le_mul_left (m + 1) h4
        _ = (m + 1) ^ (t + 1) := by rw [pow_succ']

lemma universal_family_exists (m t : ℕ) (ht : 2 ≤ t) :
    let b := 2 ^ t * (t * (Nat.clog 2 m + 1) + 1)
    ∃ B : Finset (Fin m → Bool),
      B.card ≤ b ∧
      ∀ (S : Finset (Fin m)), S.card ≤ t → ∀ p : Fin m → Bool,
        ∃ v ∈ B, ∀ i ∈ S, v i = p i := by
  classical
  intro b
  by_cases hmt : m ≤ t
  · refine ⟨Finset.univ, ?_, ?_⟩
    · have hc : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by simp
      rw [hc]
      have h1 : 2 ^ m ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) hmt
      have h2 : 1 ≤ t * (Nat.clog 2 m + 1) + 1 := by omega
      calc 2 ^ m ≤ 2 ^ t * 1 := by omega
        _ ≤ 2 ^ t * (t * (Nat.clog 2 m + 1) + 1) := Nat.mul_le_mul_left _ h2
    · intro S _ p
      exact ⟨p, Finset.mem_univ p, fun _ _ => rfl⟩
  · push Not at hmt
    let K := t * (Nat.clog 2 m + 1) + 1
    have hb_eq : b = 2 ^ t * K := rfl
    let Ω := Fin b → (Fin m → Bool)
    let Idx := Σ S : {S : Finset (Fin m) // S.card = t}, (S.1 → Bool)
    let badSet : Idx → Finset Ω := fun ⟨⟨S, _⟩, p⟩ =>
      Finset.univ.filter (fun F : Ω => ∀ r : Fin b, ¬ ∀ i : S, F r i.1 = p i)
    have hbad_card : ∀ idx : Idx, (badSet idx).card = (2 ^ (m - t) * (2 ^ t - 1)) ^ b := by
      rintro ⟨⟨S, hS⟩, p⟩
      let Vbad := Finset.univ.filter (fun v : Fin m → Bool => ¬ ∀ i : S, v i.1 = p i)
      have heq : badSet ⟨⟨S, hS⟩, p⟩ = Fintype.piFinset (fun _ : Fin b => Vbad) := by
        ext F
        rw [Fintype.mem_piFinset]
        simp only [badSet, Vbad, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [heq, Fintype.card_piFinset_const]
      exact congrArg (· ^ b) (card_bad_vec S hS p)
    have hIdx_card : Fintype.card Idx = m.choose t * 2 ^ t := by
      dsimp [Idx]
      rw [Fintype.card_sigma]
      have hconst : ∀ S : {S : Finset (Fin m) // S.card = t}, Fintype.card (S.1 → Bool) = 2 ^ t := by
        rintro ⟨S, hS⟩
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hS]
      simp_rw [hconst, Finset.sum_const, smul_eq_mul]
      congr 1
      rw [Finset.card_univ]
      have hpow_card : Fintype.card {S : Finset (Fin m) // S.card = t} =
          ((Finset.univ : Finset (Fin m)).powersetCard t).card := by
        rw [← Fintype.card_coe]
        apply Fintype.card_congr
        exact
          { toFun := fun S => ⟨S.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.2⟩⟩
            invFun := fun S => ⟨S.1, (Finset.mem_powersetCard.mp S.2).2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [hpow_card, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    have hineq_core : m.choose t * 2 ^ t * (2 ^ t - 1) ^ b < (2 ^ t) ^ b := by
      have hM : 2 ≤ 2 ^ t := by
        calc 2 = 2 ^ 1 := by ring
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)
      have hbern := two_mul_pred_pow_lt_pow hM
      have hK_pos : 0 < K := by dsimp [K]; omega
      have hpowK : (2 * (2 ^ t - 1) ^ 2 ^ t) ^ K < ((2 ^ t) ^ 2 ^ t) ^ K :=
        Nat.pow_lt_pow_left hbern (by omega)
      have hLHS1 : (2 * (2 ^ t - 1) ^ 2 ^ t) ^ K = 2 ^ K * (2 ^ t - 1) ^ b := by
        rw [mul_pow, ← pow_mul, hb_eq]
      have hRHS1 : ((2 ^ t) ^ 2 ^ t) ^ K = (2 ^ t) ^ b := by
        rw [← pow_mul, hb_eq]
      rw [hLHS1, hRHS1] at hpowK
      have hchoose_le : m.choose t ≤ m ^ t := choose_le_pow_self m t
      have hm_le : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by decide : 1 < 2) m
      have hmt_le : m ^ t ≤ (2 ^ Nat.clog 2 m) ^ t := Nat.pow_le_pow_left hm_le t
      have h2K : m.choose t * 2 ^ t ≤ 2 ^ K := by
        calc m.choose t * 2 ^ t ≤ m ^ t * 2 ^ t := Nat.mul_le_mul_right _ hchoose_le
          _ ≤ (2 ^ Nat.clog 2 m) ^ t * 2 ^ t := Nat.mul_le_mul_right _ hmt_le
          _ = 2 ^ (Nat.clog 2 m * t + t) := by rw [← pow_mul, ← pow_add]
          _ ≤ 2 ^ K := by
            apply Nat.pow_le_pow_right (by decide)
            dsimp [K]
            linarith
      calc m.choose t * 2 ^ t * (2 ^ t - 1) ^ b ≤ 2 ^ K * (2 ^ t - 1) ^ b :=
            Nat.mul_le_mul_right _ h2K
        _ < (2 ^ t) ^ b := hpowK
    have hunion_lt : (Finset.univ.biUnion badSet).card < (Finset.univ : Finset Ω).card := by
      have h1 : (Finset.univ.biUnion badSet).card ≤ ∑ idx : Idx, (badSet idx).card :=
        Finset.card_biUnion_le
      simp_rw [hbad_card, Finset.sum_const, Finset.card_univ, hIdx_card, smul_eq_mul] at h1
      have hΩ : (Finset.univ : Finset Ω).card = (2 ^ m) ^ b := by
        simp [Ω]
      rw [hΩ]
      have hfactor : (2 ^ (m - t) * (2 ^ t - 1)) ^ b = (2 ^ (m - t)) ^ b * (2 ^ t - 1) ^ b :=
        mul_pow _ _ _
      have h2m : (2 ^ m) ^ b = (2 ^ (m - t)) ^ b * (2 ^ t) ^ b := by
        rw [← mul_pow, ← pow_add, Nat.sub_add_cancel (le_of_lt hmt)]
      rw [hfactor] at h1
      rw [h2m]
      calc (Finset.univ.biUnion badSet).card
          ≤ m.choose t * 2 ^ t * ((2 ^ (m - t)) ^ b * (2 ^ t - 1) ^ b) := h1
        _ = (2 ^ (m - t)) ^ b * (m.choose t * 2 ^ t * (2 ^ t - 1) ^ b) := by ring
        _ < (2 ^ (m - t)) ^ b * (2 ^ t) ^ b := by
          apply Nat.mul_lt_mul_of_pos_left hineq_core
          positivity
    have hex : ∃ F : Ω, F ∉ Finset.univ.biUnion badSet := by
      by_contra hall
      push Not at hall
      have hsub : (Finset.univ : Finset Ω) ⊆ Finset.univ.biUnion badSet := fun F _ => hall F
      exact absurd (Finset.card_le_card hsub) (not_le_of_gt hunion_lt)
    rcases hex with ⟨F, hF⟩
    refine ⟨Finset.univ.image F, ?_, ?_⟩
    · calc (Finset.univ.image F).card ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
        _ = b := Fintype.card_fin b
    · intro S hSle p
      have ht_le_univ : t ≤ (Finset.univ : Finset (Fin m)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        exact le_of_lt hmt
      rcases Finset.exists_subsuperset_card_eq (Finset.subset_univ S) hSle ht_le_univ with
        ⟨T, hST, _, hT⟩
      let idx : Idx := ⟨⟨T, hT⟩, fun i => p i.1⟩
      have hnotbad : F ∉ badSet idx := fun hm =>
        hF (Finset.mem_biUnion.mpr ⟨idx, Finset.mem_univ idx, hm⟩)
      have hgood : ∃ r : Fin b, ∀ i : T, F r i.1 = p i.1 := by
        by_contra hall
        apply hnotbad
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ F, fun r hr => hall ⟨r, hr⟩⟩
      rcases hgood with ⟨r, hr⟩
      exact ⟨F r, Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩,
        fun i hi => hr ⟨i, hST hi⟩⟩

lemma part2 {q m : ℕ} (hq : 2 ≤ q) (hqm : q ≤ m) :
    let t := m - q + 2
    let b := 2 ^ t * (t * (Nat.clog 2 m + 1) + 1)
    ∃ C : Finset (Fin m → Fin q),
      (∀ w : Fin m → Fin q, ∃ y ∈ C, ∀ i, y i ≠ w i) ∧
      C.card ≤ q - 2 + b := by
  classical
  intro t b
  have ht : 2 ≤ t := by omega
  rcases universal_family_exists m t ht with ⟨B, hBcard, hBuniv⟩
  let Chigh : Finset (Fin m → Fin q) :=
    (Finset.univ.filter (fun c : Fin q => 2 ≤ c.val)).image constVec
  let Cbin : Finset (Fin m → Fin q) := B.image (boolVecToW hq)
  let C := Chigh ∪ Cbin
  refine ⟨C, ?_, ?_⟩
  · intro w
    by_cases hmiss : ∃ c : Fin q, 2 ≤ c.val ∧ ∀ i : Fin m, w i ≠ c
    · rcases hmiss with ⟨c, hc2, hcw⟩
      refine ⟨constVec c, ?_, ?_⟩
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc2⟩, rfl⟩
      · intro i
        exact (hcw i).symm
    · push Not at hmiss
      let High : Finset (Fin q) := Finset.univ.filter (fun c : Fin q => 2 ≤ c.val)
      let S : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => (w i).val < 2)
      let Sc : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => 2 ≤ (w i).val)
      have hHigh_sub : High ⊆ Sc.image w := by
        intro c hc
        have hc2 : 2 ≤ c.val := (Finset.mem_filter.mp hc).2
        rcases hmiss c hc2 with ⟨i, rfl⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc2⟩, rfl⟩
      have hHigh_card : High.card = q - 2 := by
        have hpart := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin q))) (fun c : Fin q => 2 ≤ c.val)
        have hlow : (Finset.univ.filter (fun c : Fin q => ¬ 2 ≤ c.val)).card = 2 := by
          have heq : Finset.univ.filter (fun c : Fin q => ¬ 2 ≤ c.val) = {sym0 hq, sym1 hq} := by
            ext c
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le, Finset.mem_insert,
              Finset.mem_singleton]
            constructor
            · intro hlt
              rcases c with ⟨v, hv⟩
              have hlt' : v < 2 := hlt
              have hv01 : v = 0 ∨ v = 1 := by omega
              rcases hv01 with rfl | rfl
              · left; rfl
              · right; rfl
            · rintro (rfl | rfl) <;> simp [sym0, sym1]
          rw [heq, Finset.card_pair (sym0_ne_sym1 hq)]
        have huniv : (Finset.univ : Finset (Fin q)).card = q := Fintype.card_fin q
        dsimp [High]
        omega
      have hSc_ge : q - 2 ≤ Sc.card := by
        calc q - 2 = High.card := hHigh_card.symm
          _ ≤ (Sc.image w).card := Finset.card_le_card hHigh_sub
          _ ≤ Sc.card := Finset.card_image_le
      have hS_add_Sc : S.card + Sc.card = m := by
        have h := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin m))) (fun i : Fin m => (w i).val < 2)
        have heq : Finset.univ.filter (fun i : Fin m => ¬ (w i).val < 2) = Sc := by
          ext i
          simp only [Sc, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        rw [heq, Finset.card_univ, Fintype.card_fin] at h
        exact h
      have hS_le : S.card ≤ t := by omega
      let p : Fin m → Bool := fun i => decide (w i = sym0 hq)
      rcases hBuniv S hS_le p with ⟨v, hvB, hvp⟩
      refine ⟨boolVecToW hq v, ?_, ?_⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨v, hvB, rfl⟩
      · intro i
        by_cases hi : i ∈ S
        · have hvi := hvp i hi
          by_cases hw0 : w i = sym0 hq
          · have hp1 : p i = true := decide_eq_true hw0
            rw [hp1] at hvi
            simp [boolVecToW, boolToSym, hvi, hw0, (sym0_ne_sym1 hq).symm]
          · have hp0 : p i = false := decide_eq_false hw0
            have hlt2 : (w i).val < 2 := (Finset.mem_filter.mp hi).2
            have hw1 : w i = sym1 hq := by
              ext
              have hv0 : (w i).val ≠ 0 := fun h => hw0 (Fin.ext h)
              simp [sym1]
              omega
            rw [hp0] at hvi
            simp [boolVecToW, boolToSym, hvi, hw1, sym0_ne_sym1 hq]
        · have hge2 : 2 ≤ (w i).val := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
            exact hi
          intro heq
          have hval := congrArg Fin.val heq
          cases hv : v i <;> simp [boolVecToW, boolToSym, sym0, sym1, hv] at hval <;> omega
  · have hc_high : Chigh.card ≤ q - 2 := by
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin q))) (fun c : Fin q => 2 ≤ c.val)
      have hlow : (Finset.univ.filter (fun c : Fin q => ¬ 2 ≤ c.val)).card = 2 := by
        have heq : Finset.univ.filter (fun c : Fin q => ¬ 2 ≤ c.val) = {sym0 hq, sym1 hq} := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · intro hlt
            rcases c with ⟨v, hv⟩
            have hlt' : v < 2 := hlt
            have hv01 : v = 0 ∨ v = 1 := by omega
            rcases hv01 with rfl | rfl
            · left; rfl
            · right; rfl
          · rintro (rfl | rfl) <;> simp [sym0, sym1]
        rw [heq, Finset.card_pair (sym0_ne_sym1 hq)]
      have huniv : (Finset.univ : Finset (Fin q)).card = q := Fintype.card_fin q
      calc Chigh.card ≤ (Finset.univ.filter (fun c : Fin q => 2 ≤ c.val)).card := Finset.card_image_le
        _ = q - 2 := by omega
    have hc_bin : Cbin.card ≤ b := by
      calc Cbin.card ≤ B.card := Finset.card_image_le
        _ ≤ b := hBcard
    calc C.card ≤ Chigh.card + Cbin.card := Finset.card_union_le _ _
      _ ≤ q - 2 + b := Nat.add_le_add hc_high hc_bin

def IsGroupFam {N m q : ℕ} (row : Fin N → Fin m → Fin q) (j : Fin m)
    (h : ℕ) (P : Finset (Finset (Fin N))) : Prop :=
  (P : Set (Finset (Fin N))).PairwiseDisjoint id ∧
  (∀ G ∈ P, 2 ≤ G.card ∧ ∃ a : Fin q, ∀ r ∈ G, row r j = a) ∧
  ∑ G ∈ P, (G.card - 1) = h

lemma groupFam_card_le {N m q : ℕ} {row : Fin N → Fin m → Fin q} {j : Fin m}
    {h : ℕ} {P : Finset (Finset (Fin N))} (hP : IsGroupFam row j h P) :
    P.card ≤ h ∧ (P.biUnion id).card ≤ 2 * h := by
  rcases hP with ⟨hdisj, hG2, hsum⟩
  have hcard_le : P.card ≤ h := by
    calc P.card = ∑ _G ∈ P, 1 := by simp
      _ ≤ ∑ G ∈ P, (G.card - 1) := by
        apply Finset.sum_le_sum
        intro G hG
        have h2 := (hG2 G hG).1
        omega
      _ = h := hsum
  have hbi : (P.biUnion id).card = P.card + h := by
    rw [Finset.card_biUnion hdisj]
    have h1 : ∀ G ∈ P, G.card = 1 + (G.card - 1) := by
      intro G hG
      have h2 := (hG2 G hG).1
      omega
    calc ∑ G ∈ P, (id G).card = ∑ G ∈ P, (1 + (G.card - 1)) :=
          Finset.sum_congr rfl fun G hG => h1 G hG
      _ = (∑ _G ∈ P, 1) + ∑ G ∈ P, (G.card - 1) := Finset.sum_add_distrib
      _ = P.card + h := by simp [hsum]
  exact ⟨hcard_le, by omega⟩

lemma trim_groups_aux {N m q : ℕ} (row : Fin N → Fin m → Fin q) (j : Fin m) :
    ∀ (F : Finset (Finset (Fin N))),
      (F : Set (Finset (Fin N))).PairwiseDisjoint id →
      (∀ G ∈ F, 2 ≤ G.card ∧ ∃ a : Fin q, ∀ r ∈ G, row r j = a) →
      ∀ h : ℕ, h ≤ ∑ G ∈ F, (G.card - 1) →
        ∃ P : Finset (Finset (Fin N)), P.biUnion id ⊆ F.biUnion id ∧ IsGroupFam row j h P := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _ _ h hh
    simp at hh
    subst hh
    refine ⟨∅, by simp, ?_⟩
    exact ⟨by simp, by simp, by simp⟩
  | @insert G0 F hnotmem ih =>
    intro hdisj hG2 h hh
    rw [Finset.sum_insert hnotmem] at hh
    have hdisjF : (F : Set (Finset (Fin N))).PairwiseDisjoint id :=
      hdisj.subset (Finset.subset_insert G0 F)
    have hG2F : ∀ G ∈ F, 2 ≤ G.card ∧ ∃ a : Fin q, ∀ r ∈ G, row r j = a :=
      fun G hG => hG2 G (Finset.mem_insert_of_mem hG)
    have hG0 := hG2 G0 (Finset.mem_insert_self G0 F)
    by_cases hle : h ≤ ∑ G ∈ F, (G.card - 1)
    · rcases ih hdisjF hG2F h hle with ⟨P, hPsub, hPfam⟩
      refine ⟨P, ?_, hPfam⟩
      intro r hr
      rcases Finset.mem_biUnion.mp (hPsub hr) with ⟨G, hGF, hrG⟩
      exact Finset.mem_biUnion.mpr ⟨G, Finset.mem_insert_of_mem hGF, hrG⟩
    · push Not at hle
      let rem := h - ∑ G ∈ F, (G.card - 1)
      have hrem_pos : 1 ≤ rem := by omega
      have hrem_le : rem + 1 ≤ G0.card := by omega
      rcases Finset.exists_subset_card_eq hrem_le with ⟨G0', hG0'sub, hG0'card⟩
      have hdisj_G0_F : ∀ G ∈ F, Disjoint G0 G := by
        intro G hG
        have hne : G0 ≠ G := fun heq => hnotmem (heq ▸ hG)
        exact hdisj (Finset.mem_insert_self G0 F) (Finset.mem_insert_of_mem hG) hne
      have hG0'_notmem : G0' ∉ F := by
        intro hm
        have hd := (hdisj_G0_F G0' hm).mono_left hG0'sub
        rw [disjoint_self, Finset.bot_eq_empty] at hd
        rw [hd] at hG0'card
        simp at hG0'card
      refine ⟨insert G0' F, ?_, ?_⟩
      · intro r hr
        rw [Finset.mem_biUnion] at hr ⊢
        rcases hr with ⟨G, hG, hrG⟩
        rcases Finset.mem_insert.mp hG with rfl | hGF
        · exact ⟨G0, Finset.mem_insert_self G0 F, hG0'sub hrG⟩
        · exact ⟨G, Finset.mem_insert_of_mem hGF, hrG⟩
      · refine ⟨?_, ?_, ?_⟩
        · rw [Finset.coe_insert, Set.pairwiseDisjoint_insert_of_notMem hG0'_notmem]
          refine ⟨hdisjF, fun G hG => ?_⟩
          exact (hdisj_G0_F G hG).mono_left hG0'sub
        · intro G hG
          rcases Finset.mem_insert.mp hG with rfl | hGF
          · refine ⟨by omega, ?_⟩
            rcases hG0.2 with ⟨a, ha⟩
            exact ⟨a, fun r hr => ha r (hG0'sub hr)⟩
          · exact hG2F G hGF
        · rw [Finset.sum_insert hG0'_notmem, hG0'card]
          omega

lemma col_has_groupFam {q m h : ℕ} (hqm : q ≤ m) (row : Fin (m + h) → Fin m → Fin q) (j : Fin m) :
    ∃ P : Finset (Finset (Fin (m + h))), IsGroupFam row j h P := by
  classical
  let fib : Fin q → Finset (Fin (m + h)) := fun a => Finset.univ.filter (fun r => row r j = a)
  let A2 : Finset (Fin q) := Finset.univ.filter (fun a => 2 ≤ (fib a).card)
  let F : Finset (Finset (Fin (m + h))) := A2.image fib
  have hfib_inj : Set.InjOn fib A2 := by
    intro a1 ha1 a2 ha2 heq
    have hc1 : 2 ≤ (fib a1).card := (Finset.mem_filter.mp ha1).2
    have hne : (fib a1).Nonempty := Finset.card_pos.mp (by omega)
    rcases hne with ⟨r, hr⟩
    have hr2 : r ∈ fib a2 := heq ▸ hr
    have h1 : row r j = a1 := (Finset.mem_filter.mp hr).2
    have h2 : row r j = a2 := (Finset.mem_filter.mp hr2).2
    exact h1.symm.trans h2
  have hdisj : (F : Set (Finset (Fin (m + h)))).PairwiseDisjoint id := by
    rintro G1 hG1 G2 hG2 hne
    rcases Finset.mem_image.mp hG1 with ⟨a1, _, rfl⟩
    rcases Finset.mem_image.mp hG2 with ⟨a2, _, rfl⟩
    have ha12 : a1 ≠ a2 := fun h => hne (congrArg fib h)
    change Disjoint (fib a1) (fib a2)
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    have e1 : row r j = a1 := (Finset.mem_filter.mp hr1).2
    have e2 : row r j = a2 := (Finset.mem_filter.mp hr2).2
    exact ha12 (e1.symm.trans e2)
  have hG2 : ∀ G ∈ F, 2 ≤ G.card ∧ ∃ a : Fin q, ∀ r ∈ G, row r j = a := by
    intro G hG
    rcases Finset.mem_image.mp hG with ⟨a, ha, rfl⟩
    refine ⟨(Finset.mem_filter.mp ha).2, a, fun r hr => (Finset.mem_filter.mp hr).2⟩
  have htot_fib : ∑ a : Fin q, (fib a).card = m + h := by
    have hb := Finset.card_biUnion (s := (Finset.univ : Finset (Fin q))) (t := fib)
      (by
        intro a1 _ a2 _ hne
        change Disjoint (fib a1) (fib a2)
        rw [Finset.disjoint_left]
        intro r hr1 hr2
        exact hne ((Finset.mem_filter.mp hr1).2.symm.trans (Finset.mem_filter.mp hr2).2))
    have hu : Finset.univ.biUnion fib = (Finset.univ : Finset (Fin (m + h))) := by
      ext r
      simp [fib]
    rw [hu, Finset.card_univ, Fintype.card_fin] at hb
    exact hb.symm
  have hle_each : ∀ a : Fin q, (fib a).card ≤ 1 + ((fib a).card - 1) := fun a => by omega
  have hsum_le : m + h ≤ q + ∑ a : Fin q, ((fib a).card - 1) := by
    calc m + h = ∑ a : Fin q, (fib a).card := htot_fib.symm
      _ ≤ ∑ a : Fin q, (1 + ((fib a).card - 1)) := Finset.sum_le_sum fun a _ => hle_each a
      _ = (∑ _a : Fin q, 1) + ∑ a : Fin q, ((fib a).card - 1) := Finset.sum_add_distrib
      _ = q + ∑ a : Fin q, ((fib a).card - 1) := by simp
  have hsum_eq_F : ∑ G ∈ F, (G.card - 1) = ∑ a : Fin q, ((fib a).card - 1) := by
    dsimp [F]
    rw [Finset.sum_image hfib_inj]
    apply Finset.sum_subset (Finset.subset_univ A2)
    intro a _ ha_not
    have hlt2 : (fib a).card < 2 := by
      simp only [A2, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at ha_not
      exact ha_not
    omega
  have hh_le : h ≤ ∑ G ∈ F, (G.card - 1) := by omega
  rcases trim_groups_aux row j F hdisj hG2 h hh_le with ⟨P, _, hPfam⟩
  exact ⟨P, hPfam⟩

lemma split_sum_prefix {α : Type*} [DecidableEq α] (w : α → ℕ) (P : Finset α) (L M : ℕ)
    (hmax : ∀ x ∈ P, w x ≤ M) (hsum : L ≤ ∑ x ∈ P, w x) :
    ∃ Q ⊆ P, L ≤ ∑ x ∈ Q, w x ∧ ∑ x ∈ Q, w x ≤ L - 1 + M := by
  induction P using Finset.induction_on with
  | empty =>
    have hL0 : L = 0 := by simpa using hsum
    subst hL0
    exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | @insert a P hnotmem ih =>
    rw [Finset.sum_insert hnotmem] at hsum
    have hmaxP : ∀ x ∈ P, w x ≤ M := fun x hx => hmax x (Finset.mem_insert_of_mem hx)
    have haM : w a ≤ M := hmax a (Finset.mem_insert_self a P)
    by_cases hL : L ≤ ∑ x ∈ P, w x
    · rcases ih hmaxP hL with ⟨Q, hQP, hQL, hQM⟩
      exact ⟨Q, hQP.trans (Finset.subset_insert a P), hQL, hQM⟩
    · push Not at hL
      refine ⟨insert a P, Finset.Subset.refl _, ?_, ?_⟩
      · rw [Finset.sum_insert hnotmem]; exact hsum
      · rw [Finset.sum_insert hnotmem]; omega

lemma split_groupFam {N m q : ℕ} {row : Fin N → Fin m → Fin q} {j : Fin m}
    {h : ℕ} (hh : 2 ≤ h) {P : Finset (Finset (Fin N))} (hP : IsGroupFam row j h P) :
    (∃ G ∈ P, G.card - 1 = h) ∨
    (∃ G ∈ P, 2 * h / 3 < G.card - 1 ∧ G.card - 1 < h ∧
      IsGroupFam row j (h - (G.card - 1)) (P.erase G)) ∨
    (∃ Q1 Q2 : Finset (Finset (Fin N)),
      ∃ h1 : ℕ, Q1 ⊆ P ∧ Q2 ⊆ P ∧ 1 ≤ h1 ∧ h1 ≤ 2 * h / 3 ∧ h - h1 ≤ 2 * h / 3 ∧
      Disjoint (Q1.biUnion id) (Q2.biUnion id) ∧
      IsGroupFam row j h1 Q1 ∧ IsGroupFam row j (h - h1) Q2) := by
  classical
  rcases hP with ⟨hdisj, hG2, hsum⟩
  let B := 2 * h / 3
  by_cases hbig : ∃ G ∈ P, B < G.card - 1
  · rcases hbig with ⟨G, hGP, hGB⟩
    have hGle : G.card - 1 ≤ h := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun E : Finset (Fin N) => E.card - 1)
        (fun _ _ => Nat.zero_le _) hGP
    by_cases heq : G.card - 1 = h
    · exact Or.inl ⟨G, hGP, heq⟩
    · right; left
      refine ⟨G, hGP, hGB, lt_of_le_of_ne hGle heq, ?_⟩
      refine ⟨hdisj.subset (Finset.erase_subset G P),
        fun E hE => hG2 E (Finset.mem_of_mem_erase hE), ?_⟩
      have hadd := Finset.add_sum_erase P (fun E => E.card - 1) hGP
      omega
  · push Not at hbig
    right; right
    by_cases hmed : ∃ G ∈ P, h - B ≤ G.card - 1
    · rcases hmed with ⟨G, hGP, hGge⟩
      have hGB : G.card - 1 ≤ B := hbig G hGP
      let h1 := G.card - 1
      have hh1_pos : 1 ≤ h1 := by
        have h2 := (hG2 G hGP).1
        dsimp [h1]; omega
      let Q1 : Finset (Finset (Fin N)) := {G}
      let Q2 : Finset (Finset (Fin N)) := P.erase G
      refine ⟨Q1, Q2, h1, Finset.singleton_subset_iff.mpr hGP, Finset.erase_subset G P,
        hh1_pos, hGB, by omega, ?_, ?_, ?_⟩
      · rw [Finset.disjoint_left]
        intro r hr1 hr2
        rw [Finset.mem_biUnion] at hr1 hr2
        rcases hr1 with ⟨E1, hE1, hrE1⟩
        rcases hr2 with ⟨E2, hE2, hrE2⟩
        rw [Finset.mem_singleton] at hE1
        subst hE1
        have hne : E1 ≠ E2 := fun heq => (Finset.mem_erase.mp hE2).1 heq.symm
        have hd := hdisj hGP (Finset.mem_of_mem_erase hE2) hne
        exact Finset.disjoint_left.mp hd hrE1 hrE2
      · refine ⟨by simp [Q1], ?_, by simp [Q1, h1]⟩
        intro E hE
        rw [Finset.mem_singleton] at hE
        subst hE
        exact hG2 E hGP
      · refine ⟨hdisj.subset (Finset.erase_subset G P),
          fun E hE => hG2 E (Finset.mem_of_mem_erase hE), ?_⟩
        have hadd := Finset.add_sum_erase P (fun E => E.card - 1) hGP
        dsimp [Q2, h1]
        omega
    · push Not at hmed
      have hmax : ∀ G ∈ P, G.card - 1 ≤ h - B - 1 := by
        intro G hG
        have hlt := hmed G hG
        omega
      have hLB : h - B ≤ ∑ G ∈ P, (G.card - 1) := by omega
      rcases split_sum_prefix (fun G => G.card - 1) P (h - B) (h - B - 1) hmax hLB with
        ⟨Q1, hQ1P, hQ1ge, hQ1le⟩
      let h1 := ∑ G ∈ Q1, (G.card - 1)
      have hh1_B : h1 ≤ B := by dsimp [h1, B] at *; omega
      have hh1_pos : 1 ≤ h1 := by dsimp [h1, B] at *; omega
      let Q2 := P \ Q1
      refine ⟨Q1, Q2, h1, hQ1P, Finset.sdiff_subset, hh1_pos, hh1_B, by omega, ?_, ?_, ?_⟩
      · rw [Finset.disjoint_left]
        intro r hr1 hr2
        rw [Finset.mem_biUnion] at hr1 hr2
        rcases hr1 with ⟨E1, hE1, hrE1⟩
        rcases hr2 with ⟨E2, hE2, hrE2⟩
        have hne : E1 ≠ E2 := fun heq => (Finset.mem_sdiff.mp hE2).2 (heq ▸ hE1)
        have hd := hdisj (hQ1P hE1) (Finset.mem_sdiff.mp hE2).1 hne
        exact Finset.disjoint_left.mp hd hrE1 hrE2
      · exact ⟨hdisj.subset hQ1P, fun E hE => hG2 E (hQ1P hE), rfl⟩
      · refine ⟨hdisj.subset Finset.sdiff_subset,
          fun E hE => hG2 E (Finset.sdiff_subset hE), ?_⟩
        have hsdiff := Finset.sum_sdiff hQ1P (f := fun E => E.card - 1)
        dsimp [Q2, h1] at *
        omega

lemma card_two_coloring_sep {N : ℕ} (A B : Finset (Fin N)) (hdisj : Disjoint A B) :
    (Finset.univ.filter (fun χ : Fin N → Bool =>
      (∀ r ∈ A, χ r = false) ∧ (∀ r ∈ B, χ r = true))).card = 2 ^ (N - (A.card + B.card)) := by
  classical
  let AB := A ∪ B
  let p : AB → Bool := fun x => decide (x.1 ∈ B)
  have heq : Finset.univ.filter (fun χ : Fin N → Bool =>
      (∀ r ∈ A, χ r = false) ∧ (∀ r ∈ B, χ r = true)) =
      Finset.univ.filter (fun χ : Fin N → Bool => ∀ x : AB, χ x.1 = p x) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.forall]
    constructor
    · rintro ⟨hA, hB⟩ r hr
      rcases Finset.mem_union.mp hr with hrA | hrB
      · have hrnotB : r ∉ B := Finset.disjoint_left.mp hdisj hrA
        simp [p, hrnotB, hA r hrA]
      · simp [p, hrB, hB r hrB]
    · intro h
      refine ⟨fun r hrA => ?_, fun r hrB => ?_⟩
      · have hrnotB : r ∉ B := Finset.disjoint_left.mp hdisj hrA
        have h1 := h r (Finset.mem_union_left B hrA)
        simpa [p, hrnotB] using h1
      · have h1 := h r (Finset.mem_union_right A hrB)
        simpa [p, hrB] using h1
  rw [heq, card_match_pattern AB p, Finset.card_union_of_disjoint hdisj]

lemma exists_two_coloring_many {N α : ℕ} {M : Finset (Fin α)}
    (A B : Fin α → Finset (Fin N)) (k : ℕ)
    (hdisj : ∀ j ∈ M, Disjoint (A j) (B j))
    (hsize : ∀ j ∈ M, (A j).card + (B j).card ≤ k) :
    ∃ χ : Fin N → Bool,
      M.card ≤ 2 ^ k * (M.filter (fun j =>
        (∀ r ∈ A j, χ r = false) ∧ (∀ r ∈ B j, χ r = true))).card := by
  classical
  let good : (Fin N → Bool) → Fin α → Prop :=
    fun χ j => (∀ r ∈ A j, χ r = false) ∧ (∀ r ∈ B j, χ r = true)
  by_cases hNk : N < k
  · by_cases hM : M = ∅
    · subst hM
      exact ⟨fun _ => false, by simp⟩
    · rcases Finset.nonempty_iff_ne_empty.mpr hM with ⟨j0, hj0⟩
      have hAB_le : (A j0).card + (B j0).card ≤ N := by
        rw [← Finset.card_union_of_disjoint (hdisj j0 hj0)]
        calc (A j0 ∪ B j0).card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
          _ = N := Fintype.card_fin N
      have hk_ge : (A j0).card + (B j0).card ≤ k := hsize j0 hj0
      let k' := N
      have hsize' : ∀ j ∈ M, (A j).card + (B j).card ≤ N := by
        intro j hj
        rw [← Finset.card_union_of_disjoint (hdisj j hj)]
        calc (A j ∪ B j).card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
          _ = N := Fintype.card_fin N
      have hdouble : ∑ χ : Fin N → Bool, (M.filter (good χ)).card =
          ∑ j ∈ M, (Finset.univ.filter (fun χ : Fin N → Bool => good χ j)).card := by
        simp_rw [Finset.card_filter]
        exact Finset.sum_comm
      have hterm_ge : ∀ j ∈ M, 1 ≤ (Finset.univ.filter (fun χ : Fin N → Bool => good χ j)).card := by
        intro j hj
        rw [card_two_coloring_sep (A j) (B j) (hdisj j hj)]
        exact Nat.one_le_two_pow
      have hsum_ge : M.card ≤ ∑ χ : Fin N → Bool, (M.filter (good χ)).card := by
        rw [hdouble]
        calc M.card = ∑ _j ∈ M, 1 := by simp
          _ ≤ ∑ j ∈ M, (Finset.univ.filter (fun χ : Fin N → Bool => good χ j)).card :=
            Finset.sum_le_sum hterm_ge
      by_contra hall
      push Not at hall
      have hsum_lt : (2 ^ k) * ∑ χ : Fin N → Bool, (M.filter (good χ)).card < (2 ^ N) * M.card := by
        have h1 : ∑ χ : Fin N → Bool, 2 ^ k * (M.filter (good χ)).card <
            ∑ _χ : Fin N → Bool, M.card := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro χ _
          exact hall χ
        rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin, smul_eq_mul] at h1
        exact h1
      have hpow : 2 ^ N ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (le_of_lt hNk)
      have hle2 : 2 ^ N * M.card ≤ 2 ^ k * ∑ χ : Fin N → Bool, (M.filter (good χ)).card :=
        Nat.mul_le_mul hpow hsum_ge
      omega
  · push Not at hNk
    have hdouble : ∑ χ : Fin N → Bool, (M.filter (good χ)).card =
        ∑ j ∈ M, (Finset.univ.filter (fun χ : Fin N → Bool => good χ j)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have hterm_ge : ∀ j ∈ M,
        2 ^ (N - k) ≤ (Finset.univ.filter (fun χ : Fin N → Bool => good χ j)).card := by
      intro j hj
      rw [card_two_coloring_sep (A j) (B j) (hdisj j hj)]
      have hsub : N - k ≤ N - ((A j).card + (B j).card) := by
        have hs := hsize j hj
        omega
      exact Nat.pow_le_pow_right (by decide) hsub
    have hsum_ge : M.card * 2 ^ (N - k) ≤ ∑ χ : Fin N → Bool, (M.filter (good χ)).card := by
      rw [hdouble]
      calc M.card * 2 ^ (N - k) = ∑ _j ∈ M, 2 ^ (N - k) := by simp
        _ ≤ ∑ j ∈ M, (Finset.univ.filter (fun χ : Fin N → Bool => good χ j)).card :=
          Finset.sum_le_sum hterm_ge
    by_contra hall
    push Not at hall
    have hsum_lt : 2 ^ k * ∑ χ : Fin N → Bool, (M.filter (good χ)).card < 2 ^ N * M.card := by
      have h1 : ∑ χ : Fin N → Bool, 2 ^ k * (M.filter (good χ)).card <
          ∑ _χ : Fin N → Bool, M.card := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro χ _
        exact hall χ
      rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, smul_eq_mul] at h1
      exact h1
    have h2N : 2 ^ k * (M.card * 2 ^ (N - k)) = 2 ^ N * M.card := by
      calc 2 ^ k * (M.card * 2 ^ (N - k)) = (2 ^ k * 2 ^ (N - k)) * M.card := by ring
        _ = 2 ^ N * M.card := by rw [← pow_add, Nat.add_sub_of_le hNk]
    have hle2 : 2 ^ N * M.card ≤ 2 ^ k * ∑ χ : Fin N → Bool, (M.filter (good χ)).card := by
      rw [← h2N]
      exact Nat.mul_le_mul_left (2 ^ k) hsum_ge
    omega

lemma two_mul_sub_two_le_two_pow : ∀ h : ℕ, 2 ≤ h → 2 * h - 2 ≤ 2 ^ h := by
  intro h hh
  rcases Nat.exists_eq_add_of_le hh with ⟨d, rfl⟩
  induction d with
  | zero => decide
  | succ d ih =>
    have h1 : 2 ≤ 2 + d := by omega
    have ih' := ih h1
    have hp : 2 ^ (2 + (d + 1)) = 2 * 2 ^ (2 + d) := by
      rw [show 2 + (d + 1) = (2 + d) + 1 by omega, pow_succ']
    have hp2 : 4 ≤ 2 ^ (2 + d) := by
      calc 4 = 2 ^ 2 := by decide
        _ ≤ 2 ^ (2 + d) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

lemma two_pow_ge_linear : ∀ b : ℕ, b + 1 ≤ 2 ^ (9 * b)
  | 0 => by decide
  | b + 1 => by
    have ih := two_pow_ge_linear b
    have hp : 2 ^ (9 * (b + 1)) = 512 * 2 ^ (9 * b) := by
      rw [show 9 * (b + 1) = 9 * b + 9 by omega, pow_add]
      ring
    omega

lemma dyadic_selection {N m q : ℕ} (row : Fin N → Fin m → Fin q) :
    ∀ h : ℕ, 1 ≤ h →
      ∀ (M : Finset (Fin m)) (P : Fin m → Finset (Finset (Fin N))),
        2 ^ (9 * h) ≤ M.card →
        (∀ j ∈ M, IsGroupFam row j h (P j)) →
        ∃ (K : Finset (Fin m)) (sel : Fin m → Finset (Fin N)),
          K ⊆ M ∧ K.card ≤ h ∧
          (K : Set (Fin m)).PairwiseDisjoint sel ∧
          (∀ j ∈ K, sel j ∈ P j) ∧
          h ≤ ∑ j ∈ K, ((sel j).card - 1) := by
  classical
  intro h
  induction h using Nat.strongRecOn with
  | ind h ih =>
    intro hh1 M P hMcard hPfam
    by_cases hh2 : h = 1
    · subst hh2
      have hMpos : 0 < M.card := lt_of_lt_of_le (by positivity) hMcard
      rcases Finset.card_pos.mp hMpos with ⟨j0, hj0⟩
      rcases hPfam j0 hj0 with ⟨_, hG2, hsum⟩
      have hPne : (P j0).Nonempty := by
        by_contra he
        rw [Finset.not_nonempty_iff_eq_empty] at he
        simp [he] at hsum
      rcases hPne with ⟨G0, hG0⟩
      refine ⟨{j0}, fun _ => G0, Finset.singleton_subset_iff.mpr hj0, by simp,
        by simp, ?_, ?_⟩
      · intro j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact hG0
      · simp only [Finset.sum_singleton]
        have h2 := (hG2 G0 hG0).1
        omega
    · have hh_ge2 : 2 ≤ h := by omega
      by_cases hex1 : ∃ j ∈ M, ∃ G ∈ P j, G.card - 1 = h
      · rcases hex1 with ⟨j0, hj0, G0, hG0, hG0eq⟩
        refine ⟨{j0}, fun _ => G0, Finset.singleton_subset_iff.mpr hj0,
          by simp; omega, by simp, ?_, ?_⟩
        · intro j hj
          rw [Finset.mem_singleton] at hj
          subst hj
          exact hG0
        · simp [hG0eq]
      · push Not at hex1
        let B := 2 * h / 3
        have hsplit_all : ∀ j : Fin m, j ∈ M →
            ∃ (Q1 Q2 : Finset (Finset (Fin N))) (h1 : ℕ),
              Q1 ⊆ P j ∧ Q2 ⊆ P j ∧
              1 ≤ h1 ∧ h1 < h ∧ h - h1 ≤ B ∧
              Disjoint (Q1.biUnion id) (Q2.biUnion id) ∧
              IsGroupFam row j h1 Q1 ∧ IsGroupFam row j (h - h1) Q2 ∧
              (B < h1 → ∃ G ∈ Q1, G.card - 1 = h1) := by
          intro j hj
          rcases split_groupFam hh_ge2 (hPfam j hj) with
            ⟨G, hG, heq⟩ | ⟨G, hG, hGB, hGlt, hQ2⟩ |
            ⟨Q1, Q2, h1, hQ1P, hQ2P, hh1_pos, hh1B, hh2B, hdisj, hQ1, hQ2⟩
          · exfalso; exact hex1 j hj G hG heq
          · let h1 := G.card - 1
            have hh1_pos : 1 ≤ h1 := by omega
            have hh2_le : h - h1 ≤ B := by dsimp [h1, B] at *; omega
            have hdisj_G : Disjoint (({G} : Finset (Finset (Fin N))).biUnion id)
                (((P j).erase G).biUnion id) := by
              rw [Finset.disjoint_left]
              intro r hr1 hr2
              rw [Finset.mem_biUnion] at hr1 hr2
              rcases hr1 with ⟨E1, hE1, hrE1⟩
              rcases hr2 with ⟨E2, hE2, hrE2⟩
              rw [Finset.mem_singleton] at hE1
              subst hE1
              have hne : E1 ≠ E2 := fun heq => (Finset.mem_erase.mp hE2).1 heq.symm
              exact Finset.disjoint_left.mp
                ((hPfam j hj).1 hG (Finset.mem_of_mem_erase hE2) hne) hrE1 hrE2
            have hQ1 : IsGroupFam row j h1 {G} := by
              refine ⟨by simp, ?_, by simp [h1]⟩
              intro E hE
              rw [Finset.mem_singleton] at hE
              subst hE
              exact (hPfam j hj).2.1 E hG
            exact ⟨{G}, (P j).erase G, h1, Finset.singleton_subset_iff.mpr hG,
              Finset.erase_subset G (P j), hh1_pos, hGlt, hh2_le, hdisj_G, hQ1, hQ2,
              fun _ => ⟨G, Finset.mem_singleton_self G, rfl⟩⟩
          · exact ⟨Q1, Q2, h1, hQ1P, hQ2P, hh1_pos, by omega, hh2B, hdisj, hQ1, hQ2,
              fun hlt => by omega⟩
        let Q1_fn : Fin m → Finset (Finset (Fin N)) := fun j =>
          if hj : j ∈ M then (hsplit_all j hj).choose else ∅
        let Q2_fn : Fin m → Finset (Finset (Fin N)) := fun j =>
          if hj : j ∈ M then (hsplit_all j hj).choose_spec.choose else ∅
        let h1_fn : Fin m → ℕ := fun j =>
          if hj : j ∈ M then (hsplit_all j hj).choose_spec.choose_spec.choose else 1
        have hspec : ∀ j (hj : j ∈ M),
            Q1_fn j ⊆ P j ∧ Q2_fn j ⊆ P j ∧
            1 ≤ h1_fn j ∧ h1_fn j < h ∧ h - h1_fn j ≤ B ∧
            Disjoint ((Q1_fn j).biUnion id) ((Q2_fn j).biUnion id) ∧
            IsGroupFam row j (h1_fn j) (Q1_fn j) ∧
            IsGroupFam row j (h - h1_fn j) (Q2_fn j) ∧
            (B < h1_fn j → ∃ G ∈ Q1_fn j, G.card - 1 = h1_fn j) := by
          intro j hj
          simp only [Q1_fn, Q2_fn, h1_fn, hj, ↓reduceDIte]
          exact (hsplit_all j hj).choose_spec.choose_spec.choose_spec
        let A : Fin m → Finset (Fin N) := fun j => (Q1_fn j).biUnion id
        let D : Fin m → Finset (Fin N) := fun j => (Q2_fn j).biUnion id
        have hAD_disj : ∀ j ∈ M, Disjoint (A j) (D j) :=
          fun j hj => (hspec j hj).2.2.2.2.2.1
        have hAD_size : ∀ j ∈ M, (A j).card + (D j).card ≤ 2 * h := by
          intro j hj
          have hc1 := (groupFam_card_le (hspec j hj).2.2.2.2.2.2.1).2
          have hc2 := (groupFam_card_le (hspec j hj).2.2.2.2.2.2.2.1).2
          have hh1_lt := (hspec j hj).2.2.2.1
          dsimp [A, D]
          omega
        rcases exists_two_coloring_many A D (2 * h) hAD_disj hAD_size with ⟨χ, hχ_card⟩
        let M' := M.filter (fun j => (∀ r ∈ A j, χ r = false) ∧ (∀ r ∈ D j, χ r = true))
        have hM'_sub : M' ⊆ M := Finset.filter_subset _ M
        let Hset := Finset.Ico 1 h
        have hM'_union : M' = Hset.biUnion (fun v => M'.filter (fun j => h1_fn j = v)) := by
          ext j
          rw [Finset.mem_biUnion]
          constructor
          · intro hj'
            have hjM : j ∈ M := hM'_sub hj'
            exact ⟨h1_fn j, Finset.mem_Ico.mpr ⟨(hspec j hjM).2.2.1, (hspec j hjM).2.2.2.1⟩,
              Finset.mem_filter.mpr ⟨hj', rfl⟩⟩
          · rintro ⟨_, _, hj'⟩
            exact (Finset.mem_filter.mp hj').1
        have hex_v : ∃ v ∈ Hset, 2 * 2 ^ (9 * B) ≤ (M'.filter (fun j => h1_fn j = v)).card := by
          by_contra hall
          push Not at hall
          have hcard_lt : M'.card ≤ ∑ v ∈ Hset, (2 * 2 ^ (9 * B) - 1) := by
            rw [hM'_union]
            calc (Hset.biUnion (fun v => M'.filter (fun j => h1_fn j = v))).card
                ≤ ∑ v ∈ Hset, (M'.filter (fun j => h1_fn j = v)).card := Finset.card_biUnion_le
              _ ≤ ∑ v ∈ Hset, (2 * 2 ^ (9 * B) - 1) := by
                apply Finset.sum_le_sum
                intro v hv
                have hlt := hall v hv
                omega
          rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul] at hcard_lt
          have h9B_pos : 1 ≤ 2 ^ (9 * B) := Nat.one_le_two_pow
          have hH_nonempty : 1 ≤ h - 1 := by omega
          have hstrict_M' : M'.card < (h - 1) * (2 * 2 ^ (9 * B)) := by
            calc M'.card ≤ (h - 1) * (2 * 2 ^ (9 * B) - 1) := hcard_lt
              _ < (h - 1) * (2 * 2 ^ (9 * B)) :=
                Nat.mul_lt_mul_of_pos_left (by omega) hH_nonempty
          have hmul2h : M.card < 2 ^ (2 * h) * ((2 * h - 2) * 2 ^ (9 * B)) := by
            have heq : (h - 1) * (2 * 2 ^ (9 * B)) = (2 * h - 2) * 2 ^ (9 * B) := by
              have hsub2 : 2 * (h - 1) = 2 * h - 2 := by omega
              calc (h - 1) * (2 * 2 ^ (9 * B)) = (2 * (h - 1)) * 2 ^ (9 * B) := by ring
                _ = (2 * h - 2) * 2 ^ (9 * B) := by rw [hsub2]
            rw [← heq]
            calc M.card ≤ 2 ^ (2 * h) * M'.card := hχ_card
              _ < 2 ^ (2 * h) * ((h - 1) * (2 * 2 ^ (9 * B))) :=
                Nat.mul_lt_mul_of_pos_left hstrict_M' (by positivity)
          have h2pow_h : 2 * h - 2 ≤ 2 ^ h := two_mul_sub_two_le_two_pow h hh_ge2
          have h9B_le : 9 * B ≤ 6 * h := by dsimp [B]; omega
          have hbound : 2 ^ (2 * h) * ((2 * h - 2) * 2 ^ (9 * B)) ≤ 2 ^ (9 * h) := by
            calc 2 ^ (2 * h) * ((2 * h - 2) * 2 ^ (9 * B))
                ≤ 2 ^ (2 * h) * (2 ^ h * 2 ^ (6 * h)) := by
                  apply Nat.mul_le_mul_left
                  exact Nat.mul_le_mul h2pow_h (Nat.pow_le_pow_right (by decide) h9B_le)
              _ = 2 ^ (2 * h + h + 6 * h) := by rw [← pow_add, ← pow_add]; ring_nf
              _ = 2 ^ (9 * h) := by congr 1; omega
          omega
        rcases hex_v with ⟨h1, hh1_mem, hMv_card⟩
        rw [Finset.mem_Ico] at hh1_mem
        rcases hh1_mem with ⟨hh1_ge1, hh1_lth⟩
        let Mv := M'.filter (fun j => h1_fn j = h1)
        have hMv_card' : 2 * 2 ^ (9 * B) ≤ Mv.card := hMv_card
        have hMv_sub_M' : Mv ⊆ M' := Finset.filter_subset _ M'
        have hMv_sub_M : Mv ⊆ M := hMv_sub_M'.trans hM'_sub
        have hh2_ge1 : 1 ≤ h - h1 := by omega
        have hh2_lt : h - h1 < h := by omega
        have hMv_nonempty : Mv.Nonempty := by
          apply Finset.card_pos.mp
          have h9B_pos : 1 ≤ 2 ^ (9 * B) := Nat.one_le_two_pow
          omega
        rcases hMv_nonempty with ⟨j_sample, hj_sample⟩
        have hh1_sample : h1_fn j_sample = h1 := (Finset.mem_filter.mp hj_sample).2
        have hh2_le_B : h - h1 ≤ B := by
          rw [← hh1_sample]
          exact (hspec j_sample (hMv_sub_M hj_sample)).2.2.2.2.1
        have hK1_exists : ∃ (K1 : Finset (Fin m)) (sel1 : Fin m → Finset (Fin N)),
            K1 ⊆ Mv ∧
            (K1 : Set (Fin m)).PairwiseDisjoint sel1 ∧
            (∀ j ∈ K1, sel1 j ∈ Q1_fn j) ∧
            h1 ≤ ∑ j ∈ K1, ((sel1 j).card - 1) ∧
            K1.card ≤ h1 ∧
            K1.card ≤ 2 ^ (9 * B) := by
          by_cases hh1_B : h1 ≤ B
          · have hcard1 : 2 ^ (9 * h1) ≤ Mv.card := by
              have hp : 2 ^ (9 * h1) ≤ 2 ^ (9 * B) :=
                Nat.pow_le_pow_right (by decide) (by omega)
              omega
            have hfam1 : ∀ j ∈ Mv, IsGroupFam row j h1 (Q1_fn j) := by
              intro j hj
              have heq := (Finset.mem_filter.mp hj).2
              rw [← heq]
              exact (hspec j (hMv_sub_M hj)).2.2.2.2.2.2.1
            rcases ih h1 hh1_lth hh1_ge1 Mv Q1_fn hcard1 hfam1 with
              ⟨K1, sel1, hK1sub, hK1card, hK1disj, hK1mem, hK1sum⟩
            have hBlin := two_pow_ge_linear B
            exact ⟨K1, sel1, hK1sub, hK1disj, hK1mem, hK1sum, hK1card, by omega⟩
          · push Not at hh1_B
            have hh1_sample_gt : B < h1_fn j_sample := by omega
            rcases (hspec j_sample (hMv_sub_M hj_sample)).2.2.2.2.2.2.2.2 hh1_sample_gt with
              ⟨G1, hG1_mem, hG1_gain⟩
            have h1_pow : 1 ≤ 2 ^ (9 * B) := Nat.one_le_two_pow
            refine ⟨{j_sample}, fun _ => G1, Finset.singleton_subset_iff.mpr hj_sample,
              by simp, ?_, ?_, by simp; omega, by simp [h1_pow]⟩
            · intro j hj
              rw [Finset.mem_singleton] at hj
              subst hj
              exact hG1_mem
            · simp [hG1_gain, hh1_sample]
        rcases hK1_exists with
          ⟨K1, sel1, hK1sub, hK1disj, hK1mem, hK1sum, hK1card_h1, hK1card_pow⟩
        let Mv2 := Mv \ K1
        have hMv2_sub_Mv : Mv2 ⊆ Mv := Finset.sdiff_subset
        have hMv2_card : 2 ^ (9 * (h - h1)) ≤ Mv2.card := by
          have hsdiff_card : Mv2.card + K1.card = Mv.card :=
            Finset.card_sdiff_add_card_eq_card hK1sub
          have hp : 2 ^ (9 * (h - h1)) ≤ 2 ^ (9 * B) :=
            Nat.pow_le_pow_right (by decide) (by omega)
          omega
        have hfam2 : ∀ j ∈ Mv2, IsGroupFam row j (h - h1) (Q2_fn j) := by
          intro j hj
          have hjMv : j ∈ Mv := hMv2_sub_Mv hj
          have heq := (Finset.mem_filter.mp hjMv).2
          rw [← heq]
          exact (hspec j (hMv_sub_M hjMv)).2.2.2.2.2.2.2.1
        rcases ih (h - h1) hh2_lt hh2_ge1 Mv2 Q2_fn hMv2_card hfam2 with
          ⟨K2, sel2, hK2sub, hK2card, hK2disj, hK2mem, hK2sum⟩
        have hK12_disj : Disjoint K1 K2 := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          exact (Finset.mem_sdiff.mp (hK2sub hj2)).2 hj1
        let sel : Fin m → Finset (Fin N) := fun j => if j ∈ K1 then sel1 j else sel2 j
        have hsel1_eq : ∀ j ∈ K1, sel j = sel1 j := fun j hj => by simp [sel, hj]
        have hsel2_eq : ∀ j ∈ K2, sel j = sel2 j :=
          fun j hj => by simp [sel, Finset.disjoint_right.mp hK12_disj hj]
        have hχ_false : ∀ j ∈ K1, ∀ r ∈ sel1 j, χ r = false := by
          intro j hj r hr
          have hjM' : j ∈ M' := hMv_sub_M' (hK1sub hj)
          have hA := (Finset.mem_filter.mp hjM').2.1
          exact hA r (Finset.mem_biUnion.mpr ⟨sel1 j, hK1mem j hj, hr⟩)
        have hχ_true : ∀ j ∈ K2, ∀ r ∈ sel2 j, χ r = true := by
          intro j hj r hr
          have hjM' : j ∈ M' := hMv_sub_M' (hMv2_sub_Mv (hK2sub hj))
          have hD := (Finset.mem_filter.mp hjM').2.2
          exact hD r (Finset.mem_biUnion.mpr ⟨sel2 j, hK2mem j hj, hr⟩)
        refine ⟨K1 ∪ K2, sel, ?_, ?_, ?_, ?_, ?_⟩
        · exact Finset.union_subset (hK1sub.trans hMv_sub_M)
            (hK2sub.trans (hMv2_sub_Mv.trans hMv_sub_M))
        · calc (K1 ∪ K2).card ≤ K1.card + K2.card := Finset.card_union_le _ _
            _ ≤ h1 + (h - h1) := Nat.add_le_add hK1card_h1 hK2card
            _ = h := by omega
        · intro j1 hj1 j2 hj2 hne
          change Disjoint (sel j1) (sel j2)
          rw [Finset.mem_coe, Finset.mem_union] at hj1 hj2
          rcases hj1 with hj1 | hj1 <;> rcases hj2 with hj2 | hj2
          · rw [hsel1_eq j1 hj1, hsel1_eq j2 hj2]
            exact hK1disj hj1 hj2 hne
          · rw [hsel1_eq j1 hj1, hsel2_eq j2 hj2, Finset.disjoint_left]
            intro r hr1 hr2
            have hf := hχ_false j1 hj1 r hr1
            have ht := hχ_true j2 hj2 r hr2
            rw [hf] at ht
            exact Bool.false_ne_true ht
          · rw [hsel2_eq j1 hj1, hsel1_eq j2 hj2, Finset.disjoint_left]
            intro r hr1 hr2
            have ht := hχ_true j1 hj1 r hr1
            have hf := hχ_false j2 hj2 r hr2
            rw [hf] at ht
            exact Bool.false_ne_true ht
          · rw [hsel2_eq j1 hj1, hsel2_eq j2 hj2]
            exact hK2disj hj1 hj2 hne
        · intro j hj
          rcases Finset.mem_union.mp hj with hj1 | hj2
          · rw [hsel1_eq j hj1]
            exact (hspec j (hMv_sub_M (hK1sub hj1))).1 (hK1mem j hj1)
          · rw [hsel2_eq j hj2]
            exact (hspec j (hMv_sub_M (hMv2_sub_Mv (hK2sub hj2)))).2.1 (hK2mem j hj2)
        · rw [Finset.sum_union hK12_disj]
          have hs1 : ∑ j ∈ K1, ((sel j).card - 1) = ∑ j ∈ K1, ((sel1 j).card - 1) :=
            Finset.sum_congr rfl fun j hj => by rw [hsel1_eq j hj]
          have hs2 : ∑ j ∈ K2, ((sel j).card - 1) = ∑ j ∈ K2, ((sel2 j).card - 1) :=
            Finset.sum_congr rfl fun j hj => by rw [hsel2_eq j hj]
          rw [hs1, hs2]
          omega

lemma strike_set_with_cols {N m q : ℕ} (hq : 2 ≤ q) (row : Fin N → Fin m → Fin q)
    (R : Finset (Fin N)) (J : Finset (Fin m)) (hcard : R.card ≤ J.card) :
    ∃ f : Fin m → Fin q, ∀ r ∈ R, ∃ j ∈ J, row r j = f j := by
  classical
  induction R using Finset.induction_on generalizing J with
  | empty =>
    exact ⟨fun _ => sym0 hq, fun _ hr => absurd hr (Finset.notMem_empty _)⟩
  | @insert r0 R hnotmem ih =>
    rw [Finset.card_insert_of_notMem hnotmem] at hcard
    have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
    rcases hJne with ⟨j0, hj0⟩
    have hcard' : R.card ≤ (J.erase j0).card := by
      rw [Finset.card_erase_of_mem hj0]
      omega
    rcases ih (J.erase j0) hcard' with ⟨f, hf⟩
    refine ⟨Function.update f j0 (row r0 j0), ?_⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hrR
    · exact ⟨j0, hj0, by simp⟩
    · rcases hf r hrR with ⟨j, hj, hreq⟩
      have hj_ne : j ≠ j0 := (Finset.mem_erase.mp hj).1
      exact ⟨j, Finset.mem_of_mem_erase hj, by simpa [Function.update, hj_ne] using hreq⟩

lemma part1 {q m : ℕ} (hq : 2 ≤ q) (hqm : q ≤ m) :
    ∀ (h : ℕ) (C : Finset (Fin m → Fin q)), 2 ^ (9 * h) ≤ m → C.card ≤ m + h →
      ∃ x : Fin m → Fin q, ∀ y ∈ C, ∃ j, y j = x j := by
  classical
  intro h C hm hCcard
  by_cases hCempty : C = ∅
  · subst hCempty
    exact ⟨fun _ => sym0 hq, fun _ hy => absurd hy (Finset.notMem_empty _)⟩
  · rcases Finset.nonempty_iff_ne_empty.mpr hCempty with ⟨y0, hy0⟩
    let e := C.equivFin
    let N := m + h
    let row : Fin N → Fin m → Fin q := fun r =>
      if hr : r.val < C.card then (e.symm ⟨r.val, hr⟩).1 else y0
    have hsurj : ∀ y ∈ C, ∃ r : Fin N, row r = y := by
      intro y hy
      let idx := e ⟨y, hy⟩
      have hlt : idx.val < N := lt_of_lt_of_le idx.isLt hCcard
      refine ⟨⟨idx.val, hlt⟩, ?_⟩
      have hr : idx.val < C.card := idx.isLt
      simp only [row, hr, ↓reduceDIte, Fin.eta]
      have hsymm := e.symm_apply_apply ⟨y, hy⟩
      exact congrArg Subtype.val hsymm
    by_cases hh0 : h = 0
    · subst hh0
      have hUN : (Finset.univ : Finset (Fin N)).card ≤ (Finset.univ : Finset (Fin m)).card := by
        simp [N]
      rcases strike_set_with_cols hq row Finset.univ Finset.univ hUN with ⟨x, hx⟩
      refine ⟨x, fun y hy => ?_⟩
      rcases hsurj y hy with ⟨r, rfl⟩
      rcases hx r (Finset.mem_univ r) with ⟨j, _, hj⟩
      exact ⟨j, hj⟩
    · have hh1 : 1 ≤ h := by omega
      have hexP : ∀ j : Fin m, ∃ P : Finset (Finset (Fin N)), IsGroupFam row j h P :=
        fun j => col_has_groupFam hqm row j
      let P_fn : Fin m → Finset (Finset (Fin N)) := fun j => (hexP j).choose
      have hPfam : ∀ j ∈ (Finset.univ : Finset (Fin m)), IsGroupFam row j h (P_fn j) :=
        fun j _ => (hexP j).choose_spec
      have hUcard : 2 ^ (9 * h) ≤ (Finset.univ : Finset (Fin m)).card := by
        simpa using hm
      rcases dyadic_selection row h hh1 Finset.univ P_fn hUcard hPfam with
        ⟨K, sel, _, hKcard, hKdisj, hKmem, hKsum⟩
      let S := K.biUnion sel
      have hS_card : K.card + h ≤ S.card := by
        rw [Finset.card_biUnion hKdisj]
        have h1 : ∀ j ∈ K, (sel j).card = 1 + ((sel j).card - 1) := by
          intro j hj
          have h2 := ((hPfam j (Finset.mem_univ j)).2.1 (sel j) (hKmem j hj)).1
          omega
        have hsum_eq : ∑ j ∈ K, (sel j).card = K.card + ∑ j ∈ K, ((sel j).card - 1) := by
          calc ∑ j ∈ K, (sel j).card = ∑ j ∈ K, (1 + ((sel j).card - 1)) :=
                Finset.sum_congr rfl h1
            _ = (∑ _j ∈ K, 1) + ∑ j ∈ K, ((sel j).card - 1) := Finset.sum_add_distrib
            _ = K.card + ∑ j ∈ K, ((sel j).card - 1) := by simp
        omega
      let R := (Finset.univ : Finset (Fin N)) \ S
      let J := (Finset.univ : Finset (Fin m)) \ K
      have hRJ_card : R.card ≤ J.card := by
        have hS_sub : S ⊆ Finset.univ := Finset.subset_univ S
        have hK_sub : K ⊆ Finset.univ := Finset.subset_univ K
        have hcR := Finset.card_sdiff_add_card_eq_card hS_sub
        have hcJ := Finset.card_sdiff_add_card_eq_card hK_sub
        rw [Finset.card_univ, Fintype.card_fin] at hcR hcJ
        have hK_le_m : K.card ≤ m := by
          calc K.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ K
            _ = m := Fintype.card_fin m
        dsimp [R, J, N] at *
        omega
      rcases strike_set_with_cols hq row R J hRJ_card with ⟨f, hf⟩
      have hmono : ∀ j : Fin m, j ∈ K → ∃ a : Fin q, ∀ r ∈ sel j, row r j = a :=
        fun j hj => ((hPfam j (Finset.mem_univ j)).2.1 (sel j) (hKmem j hj)).2
      let x : Fin m → Fin q := fun j =>
        if hj : j ∈ K then (hmono j hj).choose else f j
      refine ⟨x, fun y hy => ?_⟩
      rcases hsurj y hy with ⟨r, rfl⟩
      by_cases hrS : r ∈ S
      · rcases Finset.mem_biUnion.mp hrS with ⟨j, hjK, hr_sel⟩
        refine ⟨j, ?_⟩
        simp only [x, hjK, ↓reduceDIte]
        exact (hmono j hjK).choose_spec r hr_sel
      · have hrR : r ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, hrS⟩
        rcases hf r hrR with ⟨j, hjJ, hreq⟩
        have hjnotK : j ∉ K := (Finset.mem_sdiff.mp hjJ).2
        refine ⟨j, ?_⟩
        simp only [x, hjnotK, ↓reduceDIte]
        exact hreq

end PEqualNP.Outside.L_lib_646_aux

theorem PEqualNP.Outside.L_lib_646 : (∀ (q m : Nat), 2 ≤ q → q ≤ m →
  let W := Fin m → Fin q
  let covers := fun (C : Finset W) => ∀ w : W, ∃ y ∈ C, ∀ i, y i ≠ w i
  let t := m-q+2
  let b := 2^t * (t*(Nat.clog 2 m + 1)+1)
  (∀ (h : Nat) (C : Finset W), 2^(9*h) ≤ m → C.card ≤ m+h →
    ∃ x : W, ∀ y ∈ C, ∃ j, y j = x j) ∧
  (∃ C : Finset W, covers C ∧ C.card ≤ q-2+b) ∧
  (q = m → ∃ C : Finset W, covers C ∧ C.card ≤ q+2*Nat.clog 2 q)) := by
  intro q m hq hqm
  dsimp only
  refine ⟨PEqualNP.Outside.L_lib_646_aux.part1 hq hqm,
    PEqualNP.Outside.L_lib_646_aux.part2 hq hqm,
    fun h => PEqualNP.Outside.L_lib_646_aux.part3 hq h⟩

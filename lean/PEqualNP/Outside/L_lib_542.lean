import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_542_aux

open Classical

private def loc (n : ℕ) (hn : 0 < n) (k : ℕ) : Fin n :=
  ⟨k % n, Nat.mod_lt _ hn⟩

private lemma loc_mod_right (n : ℕ) (hn : 0 < n) (a b : ℕ) :
    loc n hn (a + b % n) = loc n hn (a + b) := by
  apply Fin.ext
  change (a + b % n) % n = (a + b) % n
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private lemma loc_mod_left (n : ℕ) (hn : 0 < n) (a b : ℕ) :
    loc n hn (a % n + b) = loc n hn (a + b) := by
  apply Fin.ext
  change (a % n + b) % n = (a + b) % n
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private def shiftFin (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n ≃ Fin n where
  toFun x := loc n hn (i.val + x.val)
  invFun y := loc n hn (y.val + (n - i.val))
  left_inv x := by
    apply Fin.ext
    change ((i.val + x.val) % n + (n - i.val)) % n = x.val
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h1 : i.val + x.val + (n - i.val) = x.val + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
  right_inv y := by
    apply Fin.ext
    change (i.val + (y.val + (n - i.val)) % n) % n = y.val
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h1 : i.val + (y.val + (n - i.val)) = y.val + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]

private def shift (n : ℕ) (hn : 0 < n) (i : Fin n) (w : Fin n → Bool) : Fin n → Bool :=
  fun x => w (loc n hn (i.val + x.val))

private def shiftEquiv (n : ℕ) (hn : 0 < n) (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun w := fun x => w (shiftFin n hn i x)
  invFun v := fun y => v ((shiftFin n hn i).symm y)
  left_inv w := by
    funext y
    simp
  right_inv v := by
    funext x
    simp

private lemma shiftEquiv_apply (n : ℕ) (hn : 0 < n) (i : Fin n) (w : Fin n → Bool) :
    shiftEquiv n hn i w = shift n hn i w := rfl

private lemma shift_injective (n : ℕ) (hn : 0 < n) (i : Fin n) :
    Function.Injective (shift n hn i) :=
  (shiftEquiv n hn i).injective

private def hasRun (n t : ℕ) (hn : 0 < n) (w : Fin n → Bool) (s : Fin n) : Prop :=
  ∀ k : Fin t, w (loc n hn (s.val + k.val)) = false

private lemma hasRun_shift (n t : ℕ) (hn : 0 < n) (i : Fin n) (w : Fin n → Bool) (s : Fin n) :
    hasRun n t hn (shift n hn i w) s ↔ hasRun n t hn w (loc n hn (i.val + s.val)) := by
  have heq : ∀ k : Fin t,
      loc n hn (i.val + (loc n hn (s.val + k.val)).val) =
      loc n hn ((loc n hn (i.val + s.val)).val + k.val) := by
    intro k
    apply Fin.ext
    change (i.val + (s.val + k.val) % n) % n = ((i.val + s.val) % n + k.val) % n
    rw [Nat.add_mod i.val, Nat.mod_mod, ← Nat.add_mod]
    rw [Nat.add_mod ((i.val + s.val) % n), Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
  constructor
  · intro h k
    have hk := h k
    dsimp only [shift] at hk
    rw [heq k] at hk
    exact hk
  · intro h k
    have hk := h k
    dsimp only [shift]
    rw [heq k]
    exact hk

private noncomputable def Prescribed0 (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) :
    Finset (Fin n → Bool) :=
  Finset.univ.filter (fun v =>
    v ⟨0, hn⟩ = true ∧
    v ⟨n - t - 1, by omega⟩ = true ∧
    ∀ k : Fin t, v ⟨n - t + k.val, by omega⟩ = false)

private def mkWord (n t : ℕ) (htn : t + 3 ≤ n) (f : Fin (n - t - 2) → Bool) : Fin n → Bool :=
  fun x =>
    if hx : 1 ≤ x.val ∧ x.val < n - t - 1 then
      f ⟨x.val - 1, by omega⟩
    else if x.val = 0 ∨ x.val = n - t - 1 then
      true
    else
      false

private lemma mkWord_injective (n t : ℕ) (htn : t + 3 ≤ n) :
    Function.Injective (mkWord n t htn) := by
  intro f g hfg
  funext j
  have h1 := congrFun hfg ⟨j.val + 1, by omega⟩
  have hcond : 1 ≤ j.val + 1 ∧ j.val + 1 < n - t - 1 := by omega
  dsimp only [mkWord] at h1
  rw [dif_pos hcond, dif_pos hcond] at h1
  have hidx : (⟨j.val + 1 - 1, by omega⟩ : Fin (n - t - 2)) = j := by
    apply Fin.ext
    simp
  rw [hidx] at h1
  exact h1

private lemma prescribed0_eq_image (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) :
    Prescribed0 n t hn htn = Finset.univ.image (mkWord n t htn) := by
  ext v
  simp only [Prescribed0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hv0, hvl, hvz⟩
    refine ⟨fun j => v ⟨j.val + 1, by omega⟩, ?_⟩
    funext x
    dsimp only [mkWord]
    by_cases hx : 1 ≤ x.val ∧ x.val < n - t - 1
    · rw [dif_pos hx]
      congr 1
      apply Fin.ext
      dsimp
      omega
    · rw [dif_neg hx]
      by_cases h0 : x.val = 0 ∨ x.val = n - t - 1
      · rw [if_pos h0]
        rcases h0 with h0 | hl
        · have hx0 : x = ⟨0, hn⟩ := Fin.ext h0
          rw [hx0, hv0]
        · have hxl : x = ⟨n - t - 1, by omega⟩ := Fin.ext hl
          rw [hxl, hvl]
      · rw [if_neg h0]
        have hklt : x.val - (n - t) < t := by omega
        have hkx : (⟨n - t + (x.val - (n - t)), by omega⟩ : Fin n) = x := by
          apply Fin.ext
          dsimp
          omega
        have hz := hvz ⟨x.val - (n - t), hklt⟩
        rw [hkx] at hz
        exact hz.symm
  · rintro ⟨f, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [mkWord]
      have h1 : ¬ (1 ≤ (0 : ℕ) ∧ (0 : ℕ) < n - t - 1) := by omega
      rw [dif_neg h1, if_pos (Or.inl rfl)]
    · dsimp only [mkWord]
      have h1 : ¬ (1 ≤ n - t - 1 ∧ n - t - 1 < n - t - 1) := by omega
      rw [dif_neg h1, if_pos (Or.inr rfl)]
    · intro k
      dsimp only [mkWord]
      have h1 : ¬ (1 ≤ n - t + k.val ∧ n - t + k.val < n - t - 1) := by omega
      have h2 : ¬ (n - t + k.val = 0 ∨ n - t + k.val = n - t - 1) := by omega
      rw [dif_neg h1, if_neg h2]

private lemma card_Prescribed0 (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) :
    (Prescribed0 n t hn htn).card = 2 ^ (n - t - 2) := by
  rw [prescribed0_eq_image, Finset.card_image_of_injective _ (mkWord_injective n t htn),
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

private noncomputable def Good0 (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) :
    Finset (Fin n → Bool) :=
  (Prescribed0 n t hn htn).filter (fun v => ∀ s : Fin n, s.val ≠ n - t → ¬ hasRun n t hn v s)

private lemma bad_s_range (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (ht : 0 < t)
    {v : Fin n → Bool} (hv : v ∈ Prescribed0 n t hn htn)
    {s : Fin n} (hsne : s.val ≠ n - t) (hrun : hasRun n t hn v s) :
    1 ≤ s.val ∧ s.val + t ≤ n - t - 1 := by
  simp only [Prescribed0, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with ⟨hv0, hvl, _⟩
  constructor
  · by_contra h0
    have hs0 : s.val = 0 := by omega
    have hr := hrun ⟨0, ht⟩
    have hloc : loc n hn (s.val + 0) = ⟨0, hn⟩ := by
      apply Fin.ext
      simp [loc, hs0]
    rw [hloc, hv0] at hr
    exact Bool.noConfusion hr
  · by_contra hbig
    by_cases hle : s.val ≤ n - t - 1
    · have hklt : n - t - 1 - s.val < t := by omega
      have hr := hrun ⟨n - t - 1 - s.val, hklt⟩
      have hloc : loc n hn (s.val + (n - t - 1 - s.val)) = ⟨n - t - 1, by omega⟩ := by
        apply Fin.ext
        have hsum : s.val + (n - t - 1 - s.val) = n - t - 1 := by omega
        change (s.val + (n - t - 1 - s.val)) % n = n - t - 1
        rw [hsum, Nat.mod_eq_of_lt (by omega)]
      rw [hloc, hvl] at hr
      exact Bool.noConfusion hr
    · have hklt : n - s.val < t := by omega
      have hr := hrun ⟨n - s.val, hklt⟩
      have hloc : loc n hn (s.val + (n - s.val)) = ⟨0, hn⟩ := by
        apply Fin.ext
        have hsum : s.val + (n - s.val) = n := by omega
        change (s.val + (n - s.val)) % n = 0
        rw [hsum, Nat.mod_self]
      rw [hloc, hv0] at hr
      exact Bool.noConfusion hr

private lemma card_bad_s_mul (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n)
    (s : Fin n) (hs1 : 1 ≤ s.val) (hs2 : s.val + t ≤ n - t - 1) :
    ((Prescribed0 n t hn htn).filter (fun v => hasRun n t hn v s)).card * 2 ^ t ≤
      2 ^ (n - t - 2) := by
  let B := (Prescribed0 n t hn htn).filter (fun v => hasRun n t hn v s)
  let φ : (Fin n → Bool) × (Fin t → Bool) → (Fin n → Bool) :=
    fun p x =>
      if hx : s.val ≤ x.val ∧ x.val < s.val + t then
        p.2 ⟨x.val - s.val, by omega⟩
      else
        p.1 x
  have hmaps : ∀ p ∈ B ×ˢ (Finset.univ : Finset (Fin t → Bool)),
      φ p ∈ Prescribed0 n t hn htn := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true, B, Finset.mem_filter] at hp
    rcases hp with ⟨hpP, _⟩
    simp only [Prescribed0, Finset.mem_filter, Finset.mem_univ, true_and] at hpP ⊢
    rcases hpP with ⟨hv0, hvl, hvz⟩
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [φ]
      have hc : ¬ (s.val ≤ 0 ∧ 0 < s.val + t) := by omega
      rw [dif_neg hc]
      exact hv0
    · dsimp only [φ]
      have hc : ¬ (s.val ≤ n - t - 1 ∧ n - t - 1 < s.val + t) := by omega
      rw [dif_neg hc]
      exact hvl
    · intro k
      dsimp only [φ]
      have hc : ¬ (s.val ≤ n - t + k.val ∧ n - t + k.val < s.val + t) := by omega
      rw [dif_neg hc]
      exact hvz k
  have hinj : Set.InjOn φ ↑(B ×ˢ (Finset.univ : Finset (Fin t → Bool))) := by
    rintro ⟨v₁, g₁⟩ h1 ⟨v₂, g₂⟩ h2 heq
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true, B,
      Finset.mem_filter] at h1 h2
    have hg : g₁ = g₂ := by
      funext k
      have hx := congrFun heq ⟨s.val + k.val, by omega⟩
      have hc : s.val ≤ s.val + k.val ∧ s.val + k.val < s.val + t := by omega
      dsimp only [φ] at hx
      rw [dif_pos hc, dif_pos hc] at hx
      have hidx : (⟨s.val + k.val - s.val, by omega⟩ : Fin t) = k := by
        apply Fin.ext
        dsimp
        omega
      rw [hidx] at hx
      exact hx
    have hv : v₁ = v₂ := by
      funext x
      by_cases hc : s.val ≤ x.val ∧ x.val < s.val + t
      · have hklt : x.val - s.val < t := by omega
        have hloc : loc n hn (s.val + (x.val - s.val)) = x := by
          apply Fin.ext
          have hsum : s.val + (x.val - s.val) = x.val := by omega
          change (s.val + (x.val - s.val)) % n = x.val
          rw [hsum, Nat.mod_eq_of_lt x.isLt]
        have hr1 := h1.2 ⟨x.val - s.val, hklt⟩
        have hr2 := h2.2 ⟨x.val - s.val, hklt⟩
        rw [hloc] at hr1 hr2
        rw [hr1, hr2]
      · have hx := congrFun heq x
        dsimp only [φ] at hx
        rw [dif_neg hc, dif_neg hc] at hx
        exact hx
    exact Prod.ext hv hg
  have hle := Finset.card_le_card_of_injOn φ hmaps hinj
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, card_Prescribed0] at hle
  exact hle

private lemma card_Good0 (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (h2n : 2 * n ≤ 2 ^ t) :
    2 ^ (n - t - 3) ≤ (Good0 n t hn htn).card := by
  have ht : 0 < t := by
    by_contra h0
    have ht0 : t = 0 := by omega
    rw [ht0] at h2n
    norm_num at h2n
    omega
  let Bad := Prescribed0 n t hn htn \ Good0 n t hn htn
  let S := (Finset.univ : Finset (Fin n)).filter (fun s => s.val ≠ n - t)
  have hsub : Bad ⊆ S.biUnion (fun s => (Prescribed0 n t hn htn).filter (fun v => hasRun n t hn v s)) := by
    intro v hv
    simp only [Bad, Good0, Finset.mem_sdiff, Finset.mem_filter] at hv
    rcases hv with ⟨hvP, hvnot⟩
    have hex : ∃ s : Fin n, s.val ≠ n - t ∧ hasRun n t hn v s := by
      by_contra hall
      push Not at hall
      exact hvnot ⟨hvP, hall⟩
    rcases hex with ⟨s, hsne, hrun⟩
    exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsne⟩,
      Finset.mem_filter.mpr ⟨hvP, hrun⟩⟩
  have hbad_le : Bad.card ≤ ∑ s ∈ S, ((Prescribed0 n t hn htn).filter (fun v => hasRun n t hn v s)).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hterm : ∀ s ∈ S,
      ((Prescribed0 n t hn htn).filter (fun v => hasRun n t hn v s)).card * 2 ^ t ≤ 2 ^ (n - t - 2) := by
    intro s hs
    have hsne : s.val ≠ n - t := (Finset.mem_filter.mp hs).2
    by_cases hr : 1 ≤ s.val ∧ s.val + t ≤ n - t - 1
    · exact card_bad_s_mul n t hn htn s hr.1 hr.2
    · have hemp : (Prescribed0 n t hn htn).filter (fun v => hasRun n t hn v s) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro v hv hrun
        exact hr (bad_s_range n t hn htn ht hv hsne hrun)
      rw [hemp, Finset.card_empty, zero_mul]
      exact Nat.zero_le _
  have hS_card : S.card ≤ n := by
    calc S.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n := by simp
  have hbad_mul : Bad.card * 2 ^ t ≤ n * 2 ^ (n - t - 2) := by
    calc Bad.card * 2 ^ t
        ≤ (∑ s ∈ S, ((Prescribed0 n t hn htn).filter (fun v => hasRun n t hn v s)).card) * 2 ^ t :=
          Nat.mul_le_mul_right _ hbad_le
      _ = ∑ s ∈ S, ((Prescribed0 n t hn htn).filter (fun v => hasRun n t hn v s)).card * 2 ^ t :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ _s ∈ S, 2 ^ (n - t - 2) := Finset.sum_le_sum hterm
      _ = S.card * 2 ^ (n - t - 2) := by simp
      _ ≤ n * 2 ^ (n - t - 2) := Nat.mul_le_mul_right _ hS_card
  have h2mul : (2 * Bad.card) * 2 ^ t ≤ 2 ^ (n - t - 2) * 2 ^ t := by
    calc (2 * Bad.card) * 2 ^ t
        = 2 * (Bad.card * 2 ^ t) := by ring
      _ ≤ 2 * (n * 2 ^ (n - t - 2)) := Nat.mul_le_mul_left 2 hbad_mul
      _ = (2 * n) * 2 ^ (n - t - 2) := by ring
      _ ≤ 2 ^ t * 2 ^ (n - t - 2) := Nat.mul_le_mul_right _ h2n
      _ = 2 ^ (n - t - 2) * 2 ^ t := by ring
  have h2bad : 2 * Bad.card ≤ 2 ^ (n - t - 2) :=
    Nat.le_of_mul_le_mul_right h2mul (by positivity)
  have hpow : 2 ^ (n - t - 2) = 2 * 2 ^ (n - t - 3) := by
    have heq : n - t - 2 = (n - t - 3) + 1 := by omega
    rw [heq, pow_succ']
  have hbad_bound : Bad.card ≤ 2 ^ (n - t - 3) := by omega
  have hsum : Bad.card + (Good0 n t hn htn).card = (Prescribed0 n t hn htn).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  rw [card_Prescribed0] at hsum
  omega

private lemma good0_hasRun_iff (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n)
    {v : Fin n → Bool} (hv : v ∈ Good0 n t hn htn) (s : Fin n) :
    hasRun n t hn v s ↔ s.val = n - t := by
  simp only [Good0, Prescribed0, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with ⟨⟨_, _, hvz⟩, huniq⟩
  constructor
  · intro hrun
    by_contra hne
    exact huniq s hne hrun
  · intro hs k
    have hloc : loc n hn (s.val + k.val) = ⟨n - t + k.val, by omega⟩ := by
      apply Fin.ext
      change (s.val + k.val) % n = n - t + k.val
      rw [hs, Nat.mod_eq_of_lt (by omega)]
    rw [hloc]
    exact hvz k

private noncomputable def Good (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (i : Fin n) :
    Finset (Fin n → Bool) :=
  (Good0 n t hn htn).image (shiftEquiv n hn i).symm

private lemma mem_Good_iff (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n)
    (i : Fin n) (w : Fin n → Bool) :
    w ∈ Good n t hn htn i ↔ shift n hn i w ∈ Good0 n t hn htn := by
  simp only [Good, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [← shiftEquiv_apply, Equiv.apply_symm_apply]
    exact hv
  · intro h
    exact ⟨shift n hn i w, h, by rw [← shiftEquiv_apply, Equiv.symm_apply_apply]⟩

private lemma card_Good (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (i : Fin n) :
    (Good n t hn htn i).card = (Good0 n t hn htn).card :=
  Finset.card_image_of_injective _ (shiftEquiv n hn i).symm.injective

private lemma good_unique_site (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (ht : 0 < t)
    {i j : Fin n} {w : Fin n → Bool}
    (hi : w ∈ Good n t hn htn i) (hj : w ∈ Good n t hn htn j) :
    i = j := by
  rw [mem_Good_iff] at hi hj
  have hri : hasRun n t hn w (loc n hn (i.val + (n - t))) :=
    (hasRun_shift n t hn i w ⟨n - t, by omega⟩).mp
      ((good0_hasRun_iff n t hn htn hi ⟨n - t, by omega⟩).mpr rfl)
  have hrj_shift : hasRun n t hn (shift n hn j w) (loc n hn (i.val + (n - t) + (n - j.val))) := by
    rw [hasRun_shift]
    have hloc : loc n hn (j.val + (loc n hn (i.val + (n - t) + (n - j.val))).val) =
        loc n hn (i.val + (n - t)) := by
      apply Fin.ext
      change (j.val + (i.val + (n - t) + (n - j.val)) % n) % n = (i.val + (n - t)) % n
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have hsum : j.val + (i.val + (n - t) + (n - j.val)) = i.val + (n - t) + n := by omega
      rw [hsum, Nat.add_mod_right]
    rw [hloc]
    exact hri
  have heq := (good0_hasRun_iff n t hn htn hj _).mp hrj_shift
  change (i.val + (n - t) + (n - j.val)) % n = n - t at heq
  have hmod : (i.val + (n - j.val)) % n = 0 := by
    have hstep : ((i.val + (n - t) + (n - j.val)) + t) % n = (n - t + t) % n := by
      calc ((i.val + (n - t) + (n - j.val)) + t) % n
          = ((i.val + (n - t) + (n - j.val)) % n + t % n) % n := Nat.add_mod _ _ _
        _ = ((n - t) % n + t % n) % n := by rw [heq, Nat.mod_eq_of_lt (show n - t < n by omega)]
        _ = (n - t + t) % n := (Nat.add_mod _ _ _).symm
    have hl : i.val + (n - t) + (n - j.val) + t = i.val + (n - j.val) + n := by omega
    have hr : n - t + t = n := by omega
    rw [hl, hr, Nat.add_mod_right, Nat.mod_self] at hstep
    exact hstep
  have hij : i.val = j.val := by
    by_cases hle : j.val ≤ i.val
    · have h1 : i.val + (n - j.val) = (i.val - j.val) + n := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hmod
      omega
    · have hlt : i.val + (n - j.val) < n := by omega
      rw [Nat.mod_eq_of_lt hlt] at hmod
      omega
  exact Fin.ext hij

private lemma main_proof :
    ∀ (n h t : Nat) (hn : 0 < n), h ≤ t → t+3 ≤ n → 2*n ≤ 2^t →
      let Word := Fin n → Bool
      let loc' := fun k : Nat => (⟨k%n, Nat.mod_lt _ hn⟩ : Fin n)
      ∀ sites : Finset (Fin n), ∃ (pool : Finset Word) (owner : ↥pool → ↥sites),
        (∀ i : ↥sites, 2^(n-t-3) ≤
          ((Finset.univ : Finset (↥pool)).filter (fun z => owner z = i)).card) ∧
        ∀ a b : ↥pool,
          (∀ j : Fin (n-h), a.val (loc' ((owner a).val.val+j.val)) =
              b.val (loc' ((owner a).val.val+j.val))) → a = b := by
  intro n h t hn hht htn h2n Word loc' sites
  have ht : 0 < t := by
    by_contra h0
    have ht0 : t = 0 := by omega
    rw [ht0] at h2n
    norm_num at h2n
    omega
  let pool : Finset (Fin n → Bool) := sites.biUnion (Good n t hn htn)
  let owner : ↥pool → ↥sites := fun z =>
    let hex := Finset.mem_biUnion.mp z.property
    ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩
  have howner_mem : ∀ z : ↥pool, z.val ∈ Good n t hn htn (owner z).val := fun z =>
    (Classical.choose_spec (Finset.mem_biUnion.mp z.property)).2
  have howner_eq : ∀ (z : ↥pool) (i : ↥sites), z.val ∈ Good n t hn htn i.val → owner z = i := by
    intro z i hzi
    exact Subtype.ext (good_unique_site n t hn htn ht (howner_mem z) hzi)
  refine ⟨pool, owner, ?_, ?_⟩
  · intro i
    have hcard :
        ((Finset.univ : Finset (↥pool)).filter (fun z => owner z = i)).card =
          (Good n t hn htn i.val).card := by
      refine Finset.card_bij (fun z _ => z.val) ?_ ?_ ?_
      · intro z hz
        have ho : owner z = i := (Finset.mem_filter.mp hz).2
        rw [← ho]
        exact howner_mem z
      · intro z₁ _ z₂ _ heq
        exact Subtype.ext heq
      · intro w hw
        have hwp : w ∈ pool := Finset.mem_biUnion.mpr ⟨i.val, i.property, hw⟩
        refine ⟨⟨w, hwp⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, howner_eq ⟨w, hwp⟩ i hw⟩
    rw [hcard, card_Good]
    exact card_Good0 n t hn htn h2n
  · intro a b hagree
    let i := (owner a).val
    let va := shift n hn i a.val
    let vb := shift n hn i b.val
    have hva : va ∈ Good0 n t hn htn := (mem_Good_iff n t hn htn i a.val).mp (howner_mem a)
    have hvb_exists : ∃ s : Fin n, hasRun n t hn vb s := by
      have hbm : shift n hn (owner b).val b.val ∈ Good0 n t hn htn :=
        (mem_Good_iff n t hn htn (owner b).val b.val).mp (howner_mem b)
      have hrb : hasRun n t hn b.val (loc n hn ((owner b).val.val + (n - t))) :=
        (hasRun_shift n t hn (owner b).val b.val ⟨n - t, by omega⟩).mp
          ((good0_hasRun_iff n t hn htn hbm ⟨n - t, by omega⟩).mpr rfl)
      refine ⟨loc n hn ((owner b).val.val + (n - t) + (n - i.val)), ?_⟩
      rw [hasRun_shift]
      have hloc : loc n hn (i.val + (loc n hn ((owner b).val.val + (n - t) + (n - i.val))).val) =
          loc n hn ((owner b).val.val + (n - t)) := by
        apply Fin.ext
        change (i.val + ((owner b).val.val + (n - t) + (n - i.val)) % n) % n =
          ((owner b).val.val + (n - t)) % n
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hsum : i.val + ((owner b).val.val + (n - t) + (n - i.val)) =
            (owner b).val.val + (n - t) + n := by omega
        rw [hsum, Nat.add_mod_right]
      rw [hloc]
      exact hrb
    have hfalse_imp : ∀ x : Fin n, vb x = false → va x = false := by
      intro x hxf
      by_cases hlt : x.val < n - h
      · have hag := hagree ⟨x.val, hlt⟩
        change va x = vb x at hag
        rw [hag, hxf]
      · have hvP := (Finset.mem_filter.mp hva).1
        have hvz := (Finset.mem_filter.mp hvP).2.2.2
        have hklt : x.val - (n - t) < t := by omega
        have hkx : (⟨n - t + (x.val - (n - t)), by omega⟩ : Fin n) = x := by
          apply Fin.ext
          dsimp
          omega
        have hz := hvz ⟨x.val - (n - t), hklt⟩
        rw [hkx] at hz
        exact hz
    rcases hvb_exists with ⟨sb, hsb⟩
    have hsa : hasRun n t hn va sb := fun k => hfalse_imp _ (hsb k)
    have hsb_val : sb.val = n - t := (good0_hasRun_iff n t hn htn hva sb).mp hsa
    have hv_eq : va = vb := by
      funext x
      by_cases hlt : x.val < n - h
      · exact hagree ⟨x.val, hlt⟩
      · have hklt : x.val - (n - t) < t := by omega
        have hloc : loc n hn (sb.val + (x.val - (n - t))) = x := by
          apply Fin.ext
          change (sb.val + (x.val - (n - t))) % n = x.val
          rw [hsb_val]
          have hsum : n - t + (x.val - (n - t)) = x.val := by omega
          rw [hsum, Nat.mod_eq_of_lt x.isLt]
        have hbx := hsb ⟨x.val - (n - t), hklt⟩
        rw [hloc] at hbx
        have hax := hfalse_imp x hbx
        rw [hax, hbx]
    exact Subtype.ext (shift_injective n hn i hv_eq)

end PEqualNP.Outside.L_lib_542_aux

open PEqualNP.Outside.L_lib_542_aux in
theorem PEqualNP.Outside.L_lib_542 :
∀ (n h t : Nat) (hn : 0 < n), h ≤ t → t+3 ≤ n → 2*n ≤ 2^t →
  let Word := Fin n → Bool
  let loc := fun k : Nat => (⟨k%n, Nat.mod_lt _ hn⟩ : Fin n)
  ∀ sites : Finset (Fin n), ∃ (pool : Finset Word) (owner : ↥pool → ↥sites),
    (∀ i : ↥sites, 2^(n-t-3) ≤
      ((Finset.univ : Finset (↥pool)).filter (fun z => owner z = i)).card) ∧
    ∀ a b : ↥pool,
      (∀ j : Fin (n-h), a.val (loc ((owner a).val.val+j.val)) =
          b.val (loc ((owner a).val.val+j.val))) → a = b :=
  main_proof

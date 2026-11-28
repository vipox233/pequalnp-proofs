import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_826

open Classical

def loc (n : ℕ) (hn : 0 < n) (k : ℕ) : Fin n :=
  ⟨k % n, Nat.mod_lt _ hn⟩

lemma loc_mod_right (n : ℕ) (hn : 0 < n) (a b : ℕ) :
    loc n hn (a + b % n) = loc n hn (a + b) := by
  apply Fin.ext
  change (a + b % n) % n = (a + b) % n
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma loc_mod_left (n : ℕ) (hn : 0 < n) (a b : ℕ) :
    loc n hn (a % n + b) = loc n hn (a + b) := by
  apply Fin.ext
  change (a % n + b) % n = (a + b) % n
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

def shiftFin (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n ≃ Fin n where
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

def shift (n : ℕ) (hn : 0 < n) (i : Fin n) (w : Fin n → Bool) : Fin n → Bool :=
  fun x => w (loc n hn (i.val + x.val))

def shiftEquiv (n : ℕ) (hn : 0 < n) (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun w := fun x => w (shiftFin n hn i x)
  invFun v := fun y => v ((shiftFin n hn i).symm y)
  left_inv w := by
    funext y
    simp
  right_inv v := by
    funext x
    simp

lemma shiftEquiv_apply (n : ℕ) (hn : 0 < n) (i : Fin n) (w : Fin n → Bool) :
    shiftEquiv n hn i w = shift n hn i w := rfl

lemma shift_injective (n : ℕ) (hn : 0 < n) (i : Fin n) :
    Function.Injective (shift n hn i) :=
  (shiftEquiv n hn i).injective

def hasRun (n t : ℕ) (hn : 0 < n) (w : Fin n → Bool) (s : Fin n) : Prop :=
  ∀ k : Fin t, w (loc n hn (s.val + k.val)) = false

lemma hasRun_shift (n t : ℕ) (hn : 0 < n) (i : Fin n) (w : Fin n → Bool) (s : Fin n) :
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

noncomputable def Prescribed0 (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) :
    Finset (Fin n → Bool) :=
  Finset.univ.filter (fun v =>
    v ⟨0, hn⟩ = true ∧
    v ⟨n - t - 1, by omega⟩ = true ∧
    ∀ k : Fin t, v ⟨n - t + k.val, by omega⟩ = false)

def mkWord (n t : ℕ) (htn : t + 3 ≤ n) (f : Fin (n - t - 2) → Bool) : Fin n → Bool :=
  fun x =>
    if hx : 1 ≤ x.val ∧ x.val < n - t - 1 then
      f ⟨x.val - 1, by omega⟩
    else if x.val = 0 ∨ x.val = n - t - 1 then
      true
    else
      false

lemma mkWord_injective (n t : ℕ) (htn : t + 3 ≤ n) :
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

lemma prescribed0_eq_image (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) :
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

lemma card_Prescribed0 (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) :
    (Prescribed0 n t hn htn).card = 2 ^ (n - t - 2) := by
  rw [prescribed0_eq_image, Finset.card_image_of_injective _ (mkWord_injective n t htn),
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

noncomputable def Good0 (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) :
    Finset (Fin n → Bool) :=
  (Prescribed0 n t hn htn).filter (fun v => ∀ s : Fin n, s.val ≠ n - t → ¬ hasRun n t hn v s)

lemma bad_s_range (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (ht : 0 < t)
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

lemma card_bad_s_mul (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n)
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

lemma card_Good0 (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (h2n : 2 * n ≤ 2 ^ t) :
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

lemma good0_hasRun_iff (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n)
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

noncomputable def Good (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (i : Fin n) :
    Finset (Fin n → Bool) :=
  (Good0 n t hn htn).image (shiftEquiv n hn i).symm

lemma mem_Good_iff (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n)
    (i : Fin n) (w : Fin n → Bool) :
    w ∈ Good n t hn htn i ↔ shift n hn i w ∈ Good0 n t hn htn := by
  simp only [Good, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [← shiftEquiv_apply, Equiv.apply_symm_apply]
    exact hv
  · intro h
    exact ⟨shift n hn i w, h, by rw [← shiftEquiv_apply, Equiv.symm_apply_apply]⟩

lemma card_Good (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (i : Fin n) :
    (Good n t hn htn i).card = (Good0 n t hn htn).card :=
  Finset.card_image_of_injective _ (shiftEquiv n hn i).symm.injective

lemma good_unique_site (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (ht : 0 < t)
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

def win (n w : ℕ) (hn : 0 < n) (x : Fin n → Bool) (i : Fin n) : Fin (w + 1) → Bool :=
  fun j => x (loc n hn (i.val + j.val))

def solSet (n w : ℕ) (hn : 0 < n) (tab : (Fin n × (Fin (w + 1) → Bool)) → Bool) :
    Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).filter
    (fun x => ∀ i : Fin n, tab (i, win n w hn x i) = true)

-- Case 1: n ≤ w + 1
theorem case_small_n (n w : ℕ) (hn : 0 < n) (hw : 0 < w) (hle : n ≤ w + 1) :
    let D := 2 ^ w
    let J := 2 ^ (min n (w + 1))
    let K := min (2 ^ n) (n * D)
    let Word := Fin n → Bool
    let Slot := Fin n × (Fin (w + 1) → Bool)
    ∃ (M : ℕ) (base : Slot → Bool) (port : Fin M → Slot)
        (code : Fin M → Word) (fixed : Finset Word),
      J ≤ M ∧ K ≤ 64 * M ∧ (n - w) * D ≤ 2 * M ∧ Function.Injective port ∧
      Function.Injective code ∧ (∀ i, base (port i) = false ∧ code i ∉ fixed) ∧
      (fixed.card = 0 ∨ fixed.card = D) ∧ (n ≤ w + 1 → M = 2 ^ n ∧ fixed = ∅) ∧
      ∀ enabled : Finset (Fin M), solSet n w hn (fun slot =>
        base slot || decide (slot ∈ enabled.image port)) = fixed ∪ enabled.image code := by
  intro D J K Word Slot
  let M := 2 ^ n
  let eW : Fin M ≃ Word := (Fintype.equivFinOfCardEq (by simp [M, Word])).symm
  let code : Fin M → Word := fun k => eW k
  let port : Fin M → Slot := fun k => (⟨0, hn⟩, win n w hn (code k) ⟨0, hn⟩)
  let base : Slot → Bool := fun slot => decide (slot.1.val ≠ 0)
  have hwin0_inj : ∀ x y : Word, win n w hn x ⟨0, hn⟩ = win n w hn y ⟨0, hn⟩ → x = y := by
    intro x y hxy
    funext j
    have hj : j.val < w + 1 := by omega
    have h := congrFun hxy ⟨j.val, hj⟩
    dsimp only [win, loc] at h
    have hmod : (0 + j.val) % n = j.val := by rw [Nat.zero_add, Nat.mod_eq_of_lt j.isLt]
    have hfin : (⟨(0 + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = j := Fin.ext hmod
    rw [hfin] at h
    exact h
  have hcode_inj : Function.Injective code := eW.injective
  have hport_inj : Function.Injective port := by
    intro a b hab
    have h2 := (Prod.ext_iff.mp hab).2
    exact hcode_inj (hwin0_inj _ _ h2)
  refine ⟨M, base, port, code, ∅, ?_, ?_, ?_, hport_inj, hcode_inj, ?_, ?_, ?_, ?_⟩
  · dsimp only [J, M]; rw [Nat.min_eq_left hle]
  · have hK : K ≤ 2 ^ n := Nat.min_le_left _ _
    dsimp only [M]; omega
  · by_cases hnw : n ≤ w
    · have : n - w = 0 := by omega
      rw [this, zero_mul]; exact Nat.zero_le _
    · have hnw1 : n = w + 1 := by omega
      have hsub : n - w = 1 := by omega
      rw [hsub, one_mul]
      dsimp only [D, M]
      rw [hnw1, pow_succ']
      omega
  · intro k
    exact ⟨by simp [base, port], Finset.notMem_empty _⟩
  · left; rfl
  · intro _; exact ⟨rfl, rfl⟩
  · intro enabled
    ext x
    simp only [solSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.empty_union,
      Finset.mem_image, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · intro hall
      have h0 := hall ⟨0, hn⟩
      simp only [base, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, false_or] at h0
      obtain ⟨k, hk, hpk⟩ := h0
      have h2 : win n w hn (code k) ⟨0, hn⟩ = win n w hn x ⟨0, hn⟩ := (Prod.ext_iff.mp hpk).2
      exact ⟨k, hk, hwin0_inj _ _ h2⟩
    · rintro ⟨k, hk, rfl⟩ i
      by_cases hi : i.val = 0
      · right
        have hi0 : i = ⟨0, hn⟩ := Fin.ext hi
        rw [hi0]
        exact ⟨k, hk, rfl⟩
      · left
        simp [base, hi]

-- Case 2: w + 2 ≤ n ≤ w + 3
theorem case_mid_small (n w : ℕ) (hn : 0 < n) (hw : 0 < w) (hlo : w + 2 ≤ n) (hhi : n ≤ w + 3) :
    let D := 2 ^ w
    let J := 2 ^ (min n (w + 1))
    let K := min (2 ^ n) (n * D)
    let Word := Fin n → Bool
    let Slot := Fin n × (Fin (w + 1) → Bool)
    ∃ (M : ℕ) (base : Slot → Bool) (port : Fin M → Slot)
        (code : Fin M → Word) (fixed : Finset Word),
      J ≤ M ∧ K ≤ 64 * M ∧ (n - w) * D ≤ 2 * M ∧ Function.Injective port ∧
      Function.Injective code ∧ (∀ i, base (port i) = false ∧ code i ∉ fixed) ∧
      (fixed.card = 0 ∨ fixed.card = D) ∧ (n ≤ w + 1 → M = 2 ^ n ∧ fixed = ∅) ∧
      ∀ enabled : Finset (Fin M), solSet n w hn (fun slot =>
        base slot || decide (slot ∈ enabled.image port)) = fixed ∪ enabled.image code := by
  intro D J K Word Slot
  let M := 2 ^ (w + 1)
  let ePat : Fin M ≃ (Fin (w + 1) → Bool) := (Fintype.equivFinOfCardEq (by simp [M])).symm
  let port : Fin M → Slot := fun k => (⟨0, hn⟩, ePat k)
  let code : Fin M → Word := fun k j => if hj : j.val < w + 1 then ePat k ⟨j.val, hj⟩ else false
  let base : Slot → Bool := fun slot =>
    if slot.1.val = 0 then false
    else if slot.1.val + w < n then !(slot.2 ⟨w, by omega⟩)
    else true
  have hport_inj : Function.Injective port := by
    intro a b hab
    exact ePat.injective (Prod.ext_iff.mp hab).2
  have hcode_inj : Function.Injective code := by
    intro a b hab
    apply ePat.injective
    funext j
    have h := congrFun hab ⟨j.val, by omega⟩
    dsimp only [code] at h
    rw [dif_pos j.isLt, dif_pos j.isLt] at h
    exact h
  refine ⟨M, base, port, code, ∅, ?_, ?_, ?_, hport_inj, hcode_inj, ?_, ?_, ?_, ?_⟩
  · dsimp only [J, M]; rw [Nat.min_eq_right (by omega)]
  · have hK : K ≤ 2 ^ n := Nat.min_le_left _ _
    have hpow : 2 ^ n ≤ 2 ^ (w + 3) := Nat.pow_le_pow_right (by omega) hhi
    have h4 : 2 ^ (w + 3) = 4 * 2 ^ (w + 1) := by
      have : w + 3 = (w + 1) + 2 := by omega
      rw [this, pow_add]; ring
    dsimp only [M]; omega
  · have h1 : (n - w) * D ≤ 3 * 2 ^ w := Nat.mul_le_mul_right _ (by omega)
    have h2 : 2 * M = 4 * 2 ^ w := by dsimp only [M]; rw [pow_succ']; ring
    omega
  · intro k
    exact ⟨by simp [base, port], Finset.notMem_empty _⟩
  · left; rfl
  · intro hle; omega
  · intro enabled
    ext x
    simp only [solSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.empty_union,
      Finset.mem_image, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · intro hall
      have h0 := hall ⟨0, hn⟩
      simp only [base, ↓reduceIte, Bool.false_eq_true, false_or] at h0
      obtain ⟨k, hk, hpk⟩ := h0
      have hpat : ePat k = win n w hn x ⟨0, hn⟩ := (Prod.ext_iff.mp hpk).2
      refine ⟨k, hk, ?_⟩
      funext j
      dsimp only [code]
      by_cases hj : j.val < w + 1
      · rw [dif_pos hj]
        have hv := congrFun hpat ⟨j.val, hj⟩
        dsimp only [win, loc] at hv
        have hfin : (⟨(0 + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = j :=
          Fin.ext (by dsimp; rw [Nat.zero_add, Nat.mod_eq_of_lt j.isLt])
        rw [hfin] at hv
        exact hv
      · rw [dif_neg hj]
        have hi_lt : j.val - w < n := by omega
        have hi_ne0 : j.val - w ≠ 0 := by omega
        have hi_add : (j.val - w) + w < n := by omega
        have hi := hall ⟨j.val - w, hi_lt⟩
        rcases hi with hbase | ⟨k', _, hpk'⟩
        · dsimp only [base] at hbase
          rw [if_neg hi_ne0, if_pos hi_add] at hbase
          dsimp only [win, loc] at hbase
          have hfin : (⟨((j.val - w) + w) % n, Nat.mod_lt _ hn⟩ : Fin n) = j :=
            Fin.ext (by
              dsimp
              have hs : j.val - w + w = j.val := by omega
              rw [hs, Nat.mod_eq_of_lt j.isLt])
          rw [hfin] at hbase
          cases hxj : x j <;> simp [hxj] at hbase ⊢
        · have h1 := congrArg Fin.val (Prod.ext_iff.mp hpk').1
          dsimp only [port] at h1
          omega
    · rintro ⟨k, hk, rfl⟩ i
      by_cases hi0 : i.val = 0
      · right
        have hi : i = ⟨0, hn⟩ := Fin.ext hi0
        rw [hi]
        refine ⟨k, hk, Prod.ext rfl ?_⟩
        funext j
        dsimp only [port, win, loc, code]
        have hlt : (0 + j.val) % n = j.val := by rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
        simp only [hlt, j.isLt, ↓reduceDIte]
      · left
        dsimp only [base]
        rw [if_neg hi0]
        by_cases hiw : i.val + w < n
        · rw [if_pos hiw]
          dsimp only [win, loc, code]
          have hnot : ¬ (i.val + w) % n < w + 1 := by rw [Nat.mod_eq_of_lt hiw]; omega
          simp [hnot]
        · rw [if_neg hiw]

-- Case 3: Parity-flip construction for n ≥ w + 4 and (n - w ≤ 8 ∨ n ≤ 32 * (n - w))
def parBool (k : ℕ) : Bool := k % 2 == 1

theorem parBool_add (a b : ℕ) : parBool (a + b) = xor (parBool a) (parBool b) := by
  unfold parBool
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [Nat.add_mod, ha, hb]

def statePar {w : ℕ} (s : Fin w → Bool) : Bool :=
  parBool (∑ r : Fin w, (s r).toNat)

def mkEven {w : ℕ} (hw : 0 < w) (f : Fin (w - 1) → Bool) : Fin w → Bool :=
  fun r => if hr : r.val = 0 then parBool (∑ j : Fin (w - 1), (f j).toNat) else f ⟨r.val - 1, by omega⟩

theorem mkEven_inj {w : ℕ} (hw : 0 < w) : Function.Injective (mkEven hw) := by
  intro f g hfg
  funext j
  have h := congrFun hfg ⟨j.val + 1, by omega⟩
  dsimp only [mkEven] at h
  have hne : j.val + 1 ≠ 0 := by omega
  rw [dif_neg hne, dif_neg hne] at h
  have hidx : (⟨j.val + 1 - 1, by omega⟩ : Fin (w - 1)) = j := Fin.ext (by simp)
  rw [hidx] at h
  exact h

theorem statePar_mkEven {w : ℕ} (hw : 0 < w) (f : Fin (w - 1) → Bool) :
    statePar (mkEven hw f) = false := by
  unfold statePar
  let i0 : Fin w := ⟨0, hw⟩
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)]
  have hrest : (∑ r ∈ Finset.univ.erase i0, (mkEven hw f r).toNat) =
      ∑ j : Fin (w - 1), (f j).toNat := by
    refine Finset.sum_bij (fun r hr => ⟨r.val - 1, by
      have hne : r ≠ i0 := (Finset.mem_erase.mp hr).1
      have hv : r.val ≠ 0 := fun h => hne (Fin.ext h)
      omega⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a ha b hb hab
      have ha0 : a.val ≠ 0 := fun h => (Finset.mem_erase.mp ha).1 (Fin.ext h)
      have hb0 : b.val ≠ 0 := fun h => (Finset.mem_erase.mp hb).1 (Fin.ext h)
      have hv := congrArg Fin.val hab; dsimp only at hv
      exact Fin.ext (by omega)
    · intro j _
      refine ⟨⟨j.val + 1, by omega⟩, Finset.mem_erase.mpr ⟨by simp [i0, Fin.ext_iff], Finset.mem_univ _⟩,
        Fin.ext (by simp)⟩
    · intro r hr
      have hv : r.val ≠ 0 := fun h => (Finset.mem_erase.mp hr).1 (Fin.ext h)
      dsimp only [mkEven]
      rw [dif_neg hv]
  rw [hrest, parBool_add]
  have h0 : mkEven hw f i0 = parBool (∑ j : Fin (w - 1), (f j).toNat) := by
    dsimp only [mkEven, i0]; rw [dif_pos rfl]
  rw [h0]
  have hp : ∀ b : Bool, parBool b.toNat = b := fun b => by cases b <;> rfl
  rw [hp]
  cases parBool (∑ j : Fin (w - 1), (f j).toNat) <;> rfl

theorem mkEven_surj_even {w : ℕ} (hw : 0 < w) (s : Fin w → Bool) (hs : statePar s = false) :
    ∃ f : Fin (w - 1) → Bool, mkEven hw f = s := by
  let f : Fin (w - 1) → Bool := fun j => s ⟨j.val + 1, by omega⟩
  refine ⟨f, ?_⟩
  funext r
  by_cases hr : r.val = 0
  · have hr0 : r = ⟨0, hw⟩ := Fin.ext hr
    rw [hr0]
    dsimp only [mkEven]
    rw [dif_pos rfl]
    let i0 : Fin w := ⟨0, hw⟩
    have hsum : (∑ x : Fin w, (s x).toNat) = (s i0).toNat + ∑ j : Fin (w - 1), (f j).toNat := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)]
      congr 1
      refine Finset.sum_bij (fun x hx => ⟨x.val - 1, by
        have hv : x.val ≠ 0 := fun h => (Finset.mem_erase.mp hx).1 (Fin.ext h)
        omega⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a ha b hb hab
        have ha0 : a.val ≠ 0 := fun h => (Finset.mem_erase.mp ha).1 (Fin.ext h)
        have hb0 : b.val ≠ 0 := fun h => (Finset.mem_erase.mp hb).1 (Fin.ext h)
        have hv := congrArg Fin.val hab; dsimp only at hv
        exact Fin.ext (by omega)
      · intro j _
        refine ⟨⟨j.val + 1, by omega⟩, Finset.mem_erase.mpr ⟨by simp [i0, Fin.ext_iff], Finset.mem_univ _⟩,
          Fin.ext (by simp)⟩
      · intro x hx
        have hv : x.val ≠ 0 := fun h => (Finset.mem_erase.mp hx).1 (Fin.ext h)
        dsimp only [f]
        congr 1; congr 1; apply Fin.ext; dsimp; omega
    unfold statePar at hs
    rw [hsum, parBool_add] at hs
    have hp : ∀ b : Bool, parBool b.toNat = b := fun b => by cases b <;> rfl
    rw [hp] at hs
    cases h1 : s i0 <;> cases h2 : parBool (∑ j : Fin (w - 1), (f j).toNat) <;>
      rw [h1, h2] at hs <;> first | rfl | exact Bool.noConfusion hs
  · dsimp only [mkEven, f]
    rw [dif_neg hr]
    congr 1; apply Fin.ext; dsimp; omega

theorem winPar_step {n w : ℕ} (hn : 0 < n) (hw : 0 < w) (x : Fin n → Bool)
    (i : ℕ) (hiw : i + w < n) :
    statePar (fun r : Fin w => x ⟨i + 1 + r.val, by omega⟩) =
      xor (statePar (fun r : Fin w => x ⟨i + r.val, by omega⟩))
          (xor (x ⟨i, by omega⟩) (x ⟨i + w, hiw⟩)) := by
  unfold statePar
  have hL : (∑ r : Fin w, (x ⟨i + 1 + r.val, by omega⟩).toNat) =
      (∑ r : Fin (w - 1), (x ⟨i + 1 + r.val, by omega⟩).toNat) + (x ⟨i + w, hiw⟩).toNat := by
    let lastW : Fin w := ⟨w - 1, by omega⟩
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ lastW), Nat.add_comm]
    congr 1
    · refine Finset.sum_bij (fun r hr => ⟨r.val, by
        have hne : r ≠ lastW := (Finset.mem_erase.mp hr).1
        have hv : r.val ≠ w - 1 := fun h => hne (Fin.ext h)
        omega⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h
        have hv := congrArg Fin.val h
        exact Fin.ext hv
      · intro r _
        refine ⟨⟨r.val, by omega⟩, Finset.mem_erase.mpr ⟨by simp [lastW, Fin.ext_iff]; omega, Finset.mem_univ _⟩,
          Fin.ext rfl⟩
      · intro r _; rfl
    · congr 1; congr 1; apply Fin.ext; dsimp [lastW]; omega
  have hR : (∑ r : Fin w, (x ⟨i + r.val, by omega⟩).toNat) =
      (x ⟨i, by omega⟩).toNat + ∑ r : Fin (w - 1), (x ⟨i + 1 + r.val, by omega⟩).toNat := by
    let zeroW : Fin w := ⟨0, hw⟩
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ zeroW)]
    congr 1
    refine Finset.sum_bij (fun r hr => ⟨r.val - 1, by
      have hv : r.val ≠ 0 := fun h => (Finset.mem_erase.mp hr).1 (Fin.ext h)
      omega⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a ha b hb h
      have ha0 : a.val ≠ 0 := fun h => (Finset.mem_erase.mp ha).1 (Fin.ext h)
      have hb0 : b.val ≠ 0 := fun h => (Finset.mem_erase.mp hb).1 (Fin.ext h)
      have hv := congrArg Fin.val h; dsimp only at hv
      exact Fin.ext (by omega)
    · intro r _
      refine ⟨⟨r.val + 1, by omega⟩, Finset.mem_erase.mpr ⟨by simp [zeroW, Fin.ext_iff], Finset.mem_univ _⟩,
        Fin.ext (by simp)⟩
    · intro r hr
      have hv : r.val ≠ 0 := fun h => (Finset.mem_erase.mp hr).1 (Fin.ext h)
      congr 1; congr 1; apply Fin.ext; dsimp; omega
  rw [hL, hR, parBool_add, parBool_add]
  have hp : ∀ b : Bool, parBool b.toNat = b := fun b => by cases b <;> rfl
  rw [hp, hp]
  cases parBool (∑ r : Fin (w - 1), (x ⟨i + 1 + r.val, by omega⟩).toNat) <;>
    cases x ⟨i, by omega⟩ <;> cases x ⟨i + w, hiw⟩ <;> rfl

theorem case_parity_flip (n w : ℕ) (hn : 0 < n) (hw : 0 < w)
    (hge : w + 4 ≤ n) (hreg : n - w ≤ 8 ∨ n ≤ 32 * (n - w)) :
    let D := 2 ^ w
    let J := 2 ^ (min n (w + 1))
    let K := min (2 ^ n) (n * D)
    let Word := Fin n → Bool
    let Slot := Fin n × (Fin (w + 1) → Bool)
    ∃ (M : ℕ) (base : Slot → Bool) (port : Fin M → Slot)
        (code : Fin M → Word) (fixed : Finset Word),
      J ≤ M ∧ K ≤ 64 * M ∧ (n - w) * D ≤ 2 * M ∧ Function.Injective port ∧
      Function.Injective code ∧ (∀ i, base (port i) = false ∧ code i ∉ fixed) ∧
      (fixed.card = 0 ∨ fixed.card = D) ∧ (n ≤ w + 1 → M = 2 ^ n ∧ fixed = ∅) ∧
      ∀ enabled : Finset (Fin M), solSet n w hn (fun slot =>
        base slot || decide (slot ∈ enabled.image port)) = fixed ∪ enabled.image code := by
  intro D J K Word Slot
  let M := (n - w) * 2 ^ (w - 1)
  let eIdx : Fin M ≃ Fin (n - w) × (Fin (w - 1) → Bool) :=
    (Fintype.equivFinOfCardEq (by simp [M])).symm
  let base : Slot → Bool := fun slot =>
    if slot.1.val + w < n then slot.2 ⟨w, by omega⟩ == slot.2 ⟨0, by omega⟩ else true
  let portOf : Fin (n - w) × (Fin (w - 1) → Bool) → Slot := fun pf =>
    let s := mkEven hw pf.2
    (⟨pf.1.val, by omega⟩, fun j => if hj : j.val < w then s ⟨j.val, hj⟩ else !(s ⟨0, hw⟩))
  let idxW : ℕ → ℕ → Fin w := fun p j => ⟨(j + w - p % w) % w, Nat.mod_lt _ hw⟩
  have hidx_shift : ∀ p j : ℕ, idxW p (j + w) = idxW p j := by
    intro p j; apply Fin.ext
    dsimp only [idxW]
    have hlt : p % w < w := Nat.mod_lt _ hw
    have heq : j + w + w - p % w = (j + w - p % w) + w := by omega
    rw [heq, Nat.add_mod_right]
  have hidx_at : ∀ (p r : ℕ) (hr : r < w), idxW p (p + r) = ⟨r, hr⟩ := by
    intro p r hr; apply Fin.ext
    dsimp only [idxW]
    have hlt : p % w < w := Nat.mod_lt _ hw
    have hdiv : p = w * (p / w) + p % w := (Nat.div_add_mod p w).symm
    have heq : p + r + w - p % w = r + w * (p / w + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have hidx_zero_iff : ∀ p j : ℕ, idxW p j = ⟨0, hw⟩ ↔ j % w = p % w := by
    intro p j
    have hlt : p % w < w := Nat.mod_lt _ hw
    have hltj : j % w < w := Nat.mod_lt _ hw
    constructor
    · intro h
      have hv := congrArg Fin.val h; dsimp only [idxW] at hv
      have hdiv : j = w * (j / w) + j % w := (Nat.div_add_mod j w).symm
      have heq : j + w - p % w = (j % w + w - p % w) + w * (j / w) := by omega
      rw [heq, Nat.add_mul_mod_self_left] at hv
      by_cases hle : p % w ≤ j % w
      · have h1 : j % w + w - p % w = (j % w - p % w) + w := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hv
        omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hv
        omega
    · intro h
      apply Fin.ext; dsimp only [idxW]
      have hdiv : j = w * (j / w) + j % w := (Nat.div_add_mod j w).symm
      have heq : j + w - p % w = w * (j / w + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
      rw [heq, Nat.mul_mod_right]
  let codeOf : Fin (n - w) × (Fin (w - 1) → Bool) → Word := fun pf j =>
    let s := mkEven hw pf.2
    if pf.1.val + w ≤ j.val ∧ idxW pf.1.val j.val = ⟨0, hw⟩ then !(s ⟨0, hw⟩)
    else s (idxW pf.1.val j.val)
  let port : Fin M → Slot := fun k => portOf (eIdx k)
  let code : Fin M → Word := fun k => codeOf (eIdx k)
  let fixed : Finset Word :=
    Finset.univ.filter (fun x : Word => ∀ (i : Fin n) (hiw : i.val + w < n), x ⟨i.val + w, hiw⟩ = x i)
  have hcodeOf_win : ∀ pf : Fin (n - w) × (Fin (w - 1) → Bool),
      win n w hn (codeOf pf) ⟨pf.1.val, by omega⟩ = (portOf pf).2 := by
    intro ⟨p, f⟩
    funext j
    dsimp only [win, loc, codeOf, portOf]
    have hlt : p.val + j.val < n := by omega
    have hmod : (p.val + j.val) % n = p.val + j.val := Nat.mod_eq_of_lt hlt
    simp only [hmod]
    by_cases hj : j.val < w
    · rw [dif_pos hj]
      have hnot : ¬ (p.val + w ≤ p.val + j.val ∧ idxW p.val (p.val + j.val) = ⟨0, hw⟩) := by omega
      rw [if_neg hnot, hidx_at p.val j.val hj]
    · rw [dif_neg hj]
      have hjw : j.val = w := by omega
      have hcond : p.val + w ≤ p.val + j.val ∧ idxW p.val (p.val + j.val) = ⟨0, hw⟩ := by
        refine ⟨by omega, ?_⟩
        rw [hjw, hidx_shift]
        have h0 := hidx_at p.val 0 hw
        simpa using h0
      rw [if_pos hcond]
  have hcodeOf_step : ∀ (pf : Fin (n - w) × (Fin (w - 1) → Bool)) (i : Fin n) (hiw : i.val + w < n),
      i.val ≠ pf.1.val → codeOf pf ⟨i.val + w, hiw⟩ = codeOf pf i := by
    intro ⟨p, f⟩ i hiw hne
    dsimp only at hne
    dsimp only [codeOf]
    rw [hidx_shift]
    by_cases h0 : idxW p.val i.val = ⟨0, hw⟩
    · have hmod : i.val % w = p.val % w := (hidx_zero_iff p.val i.val).mp h0
      have hdiv_i : i.val = w * (i.val / w) + i.val % w := (Nat.div_add_mod i.val w).symm
      have hdiv_p : p.val = w * (p.val / w) + p.val % w := (Nat.div_add_mod p.val w).symm
      by_cases hlt : i.val < p.val
      · have hle : i.val + w ≤ p.val := by
          have : i.val / w + 1 ≤ p.val / w := by
            by_contra hge
            have : p.val / w ≤ i.val / w := by omega
            have : w * (p.val / w) ≤ w * (i.val / w) := Nat.mul_le_mul_left w this
            omega
          have hmul : w * (i.val / w + 1) ≤ w * (p.val / w) := Nat.mul_le_mul_left w this
          rw [Nat.mul_add, Nat.mul_one] at hmul
          omega
        have hc1 : ¬ (p.val + w ≤ i.val + w ∧ idxW p.val i.val = ⟨0, hw⟩) := by omega
        have hc2 : ¬ (p.val + w ≤ i.val ∧ idxW p.val i.val = ⟨0, hw⟩) := by omega
        rw [if_neg hc1, if_neg hc2]
      · have hge_p : p.val + w ≤ i.val := by
          have : p.val / w + 1 ≤ i.val / w := by
            by_contra hge
            have : i.val / w ≤ p.val / w := by omega
            have : w * (i.val / w) ≤ w * (p.val / w) := Nat.mul_le_mul_left w this
            omega
          have hmul : w * (p.val / w + 1) ≤ w * (i.val / w) := Nat.mul_le_mul_left w this
          rw [Nat.mul_add, Nat.mul_one] at hmul
          omega
        have hc1 : p.val + w ≤ i.val + w ∧ idxW p.val i.val = ⟨0, hw⟩ := ⟨by omega, h0⟩
        have hc2 : p.val + w ≤ i.val ∧ idxW p.val i.val = ⟨0, hw⟩ := ⟨hge_p, h0⟩
        rw [if_pos hc1, if_pos hc2]
    · have hc1 : ¬ (p.val + w ≤ i.val + w ∧ idxW p.val i.val = ⟨0, hw⟩) := fun h => h0 h.2
      have hc2 : ¬ (p.val + w ≤ i.val ∧ idxW p.val i.val = ⟨0, hw⟩) := fun h => h0 h.2
      rw [if_neg hc1, if_neg hc2]
  have hcodeOf_flip : ∀ pf : Fin (n - w) × (Fin (w - 1) → Bool),
      codeOf pf ⟨pf.1.val + w, by omega⟩ ≠ codeOf pf ⟨pf.1.val, by omega⟩ := by
    intro ⟨p, f⟩
    have hwin := hcodeOf_win (p, f)
    have h0 := congrFun hwin ⟨0, by omega⟩
    have hw' := congrFun hwin ⟨w, by omega⟩
    dsimp only [win, loc, portOf] at h0 hw'
    have hm0 : (p.val + 0) % n = p.val := Nat.mod_eq_of_lt (by omega)
    have hmw : (p.val + w) % n = p.val + w := Nat.mod_eq_of_lt (by omega)
    have hfin0 : (⟨(p.val + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨p.val, by omega⟩ := Fin.ext hm0
    have hfinw : (⟨(p.val + w) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨p.val + w, by omega⟩ := Fin.ext hmw
    rw [hfin0, dif_pos hw] at h0
    rw [hfinw, dif_neg (by omega)] at hw'
    rw [h0, hw']
    cases mkEven hw f ⟨0, hw⟩ <;> decide
  have hport_inj : Function.Injective port := by
    intro a b hab
    apply eIdx.injective
    have h1 := congrArg Fin.val (Prod.ext_iff.mp hab).1
    dsimp only [port, portOf] at h1
    have hp : (eIdx a).1 = (eIdx b).1 := Fin.ext h1
    have h2 := (Prod.ext_iff.mp hab).2
    have hf : (eIdx a).2 = (eIdx b).2 := by
      apply mkEven_inj hw
      funext r
      have hr := congrFun h2 ⟨r.val, by omega⟩
      dsimp only [port, portOf] at hr
      rw [dif_pos r.isLt, dif_pos r.isLt] at hr
      exact hr
    exact Prod.ext hp hf
  have hcode_inj : Function.Injective code := by
    intro a b hab
    apply eIdx.injective
    have hp : (eIdx a).1 = (eIdx b).1 := by
      by_contra hne
      have hne_val : (eIdx a).1.val ≠ (eIdx b).1.val := fun h => hne (Fin.ext h)
      have ha_lt := (eIdx a).1.isLt
      have hstep := hcodeOf_step (eIdx b) ⟨(eIdx a).1.val, by omega⟩ (by dsimp; omega) hne_val
      have hfl := hcodeOf_flip (eIdx a)
      dsimp only [code] at hab
      rw [hab] at hfl
      exact hfl hstep
    have hwin : (portOf (eIdx a)).2 = (portOf (eIdx b)).2 := by
      have ha_lt := (eIdx a).1.isLt
      have hb_lt := (eIdx b).1.isLt
      have hfin : (⟨(eIdx a).1.val, by omega⟩ : Fin n) = ⟨(eIdx b).1.val, by omega⟩ :=
        Fin.ext (by have := congrArg Fin.val hp; exact this)
      rw [← hcodeOf_win (eIdx a), ← hcodeOf_win (eIdx b), hfin]
      dsimp only [code] at hab
      rw [hab]
    have hf : (eIdx a).2 = (eIdx b).2 := by
      apply mkEven_inj hw
      funext r
      have hr := congrFun hwin ⟨r.val, by omega⟩
      dsimp only [portOf] at hr
      rw [dif_pos r.isLt, dif_pos r.isLt] at hr
      exact hr
    exact Prod.ext hp hf
  have hfixed_card : fixed.card = D := by
    let mkFix : (Fin w → Bool) → Word := fun a j => a ⟨j.val % w, Nat.mod_lt _ hw⟩
    have hmk_inj : Function.Injective mkFix := by
      intro a b hab
      funext r
      have h := congrFun hab ⟨r.val, by omega⟩
      dsimp only [mkFix] at h
      have hmod : r.val % w = r.val := Nat.mod_eq_of_lt r.isLt
      have hfin : (⟨r.val % w, Nat.mod_lt _ hw⟩ : Fin w) = r := Fin.ext hmod
      rw [hfin] at h
      exact h
    have hfeq : fixed = Finset.univ.image mkFix := by
      ext x
      simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hper
        refine ⟨fun r => x ⟨r.val, by omega⟩, ?_⟩
        funext j
        dsimp only [mkFix]
        have hind : ∀ (m : ℕ) (hm : m < n), x ⟨m, hm⟩ = x ⟨m % w, by have := Nat.mod_lt m hw; omega⟩ := by
          intro m
          induction m using Nat.strong_induction_on with
          | ind m ih =>
            intro hm
            by_cases hmw : m < w
            · congr 1; apply Fin.ext; dsimp; exact (Nat.mod_eq_of_lt hmw).symm
            · have hsub : m - w < m := by omega
              have hstep := hper ⟨m - w, by omega⟩ (by dsimp; omega)
              have hadd : m - w + w = m := by omega
              have hfin : (⟨m - w + w, by omega⟩ : Fin n) = ⟨m, hm⟩ := Fin.ext hadd
              rw [hfin] at hstep
              rw [hstep, ih (m - w) hsub (by omega)]
              congr 1; apply Fin.ext; dsimp
              have : m = (m - w) + w := by omega
              conv_rhs => rw [this, Nat.add_mod_right]
        exact (hind j.val j.isLt).symm
      · rintro ⟨a, rfl⟩ i hiw
        dsimp only [mkFix]
        congr 1; apply Fin.ext; dsimp
        exact Nat.add_mod_right i.val w
    rw [hfeq, Finset.card_image_of_injective _ hmk_inj, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  have h2M : 2 * M = (n - w) * D := by
    dsimp only [M, D]
    have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
      have hw1 : w = (w - 1) + 1 := by omega
      conv_lhs => rw [hw1, pow_succ']
    rw [hpow]; ring
  refine ⟨M, base, port, code, fixed, ?_, ?_, ?_, hport_inj, hcode_inj, ?_, ?_, ?_, ?_⟩
  · have hJ : J = 2 * D := by
      dsimp only [J, D]; rw [Nat.min_eq_right (by omega), pow_succ']
    have h4 : 4 * D ≤ (n - w) * D := Nat.mul_le_mul_right D (by omega)
    omega
  · rcases hreg with hle8 | hle32
    · have hK : K ≤ 2 ^ n := Nat.min_le_left _ _
      have hpow : 2 ^ n = 2 ^ (n - w) * D := by
        dsimp only [D]; rw [← pow_add]; congr 1; omega
      have h8 : 2 ^ (n - w) ≤ 32 * (n - w) := by
        have hd : n - w = 4 ∨ n - w = 5 ∨ n - w = 6 ∨ n - w = 7 ∨ n - w = 8 := by omega
        rcases hd with h | h | h | h | h <;> rw [h] <;> decide
      have : 2 ^ n ≤ 32 * ((n - w) * D) := by
        rw [hpow]
        calc 2 ^ (n - w) * D ≤ (32 * (n - w)) * D := Nat.mul_le_mul_right D h8
          _ = 32 * ((n - w) * D) := by ring
      omega
    · have hK : K ≤ n * D := Nat.min_le_right _ _
      have : n * D ≤ 32 * ((n - w) * D) := by
        calc n * D ≤ (32 * (n - w)) * D := Nat.mul_le_mul_right D hle32
          _ = 32 * ((n - w) * D) := by ring
      omega
  · omega
  · intro k
    refine ⟨?_, ?_⟩
    · dsimp only [base, port, portOf]
      have hlt : (eIdx k).1.val + w < n := by omega
      rw [if_pos hlt, dif_neg (by omega), dif_pos hw]
      cases mkEven hw (eIdx k).2 ⟨0, hw⟩ <;> rfl
    · intro hmem
      have hk_lt := (eIdx k).1.isLt
      have hper := (Finset.mem_filter.mp hmem).2 ⟨(eIdx k).1.val, by omega⟩ (by dsimp; omega)
      exact hcodeOf_flip (eIdx k) hper
  · right; exact hfixed_card
  · intro hle; omega
  · intro enabled
    ext x
    simp only [solSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · intro hall
      have hport_step : ∀ (i : Fin n) (hiw : i.val + w < n),
          x ⟨i.val + w, hiw⟩ ≠ x i →
          ∃ k ∈ enabled, (eIdx k).1.val = i.val ∧ win n w hn x i = (port k).2 := by
        intro i hiw hdiff
        rcases hall i with hbase | ⟨k, hk, hpk⟩
        · exfalso
          dsimp only [base] at hbase
          rw [if_pos hiw] at hbase
          dsimp only [win, loc] at hbase
          have hm0 : (i.val + 0) % n = i.val := Nat.mod_eq_of_lt i.isLt
          have hmw : (i.val + w) % n = i.val + w := Nat.mod_eq_of_lt hiw
          have hf0 : (⟨(i.val + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := Fin.ext hm0
          have hfw : (⟨(i.val + w) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨i.val + w, hiw⟩ := Fin.ext hmw
          rw [hf0, hfw] at hbase
          exact hdiff (beq_iff_eq.mp hbase)
        · have h1 := congrArg Fin.val (Prod.ext_iff.mp hpk).1
          dsimp only [port, portOf] at h1
          exact ⟨k, hk, h1, (Prod.ext_iff.mp hpk).2.symm⟩
      have hport_even : ∀ (i : Fin n) (hiw : i.val + w < n),
          x ⟨i.val + w, hiw⟩ ≠ x i →
          statePar (fun r : Fin w => x ⟨i.val + r.val, by omega⟩) = false := by
        intro i hiw hdiff
        obtain ⟨k, _, hki, hwin⟩ := hport_step i hiw hdiff
        have hseq : (fun r : Fin w => x ⟨i.val + r.val, by omega⟩) = mkEven hw (eIdx k).2 := by
          funext r
          have hr := congrFun hwin ⟨r.val, by omega⟩
          dsimp only [win, loc, port, portOf] at hr
          have hmr : (i.val + r.val) % n = i.val + r.val := Nat.mod_eq_of_lt (by omega)
          have hfr : (⟨(i.val + r.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨i.val + r.val, by omega⟩ := Fin.ext hmr
          rw [hfr, dif_pos r.isLt] at hr
          exact hr
        rw [hseq]
        exact statePar_mkEven hw (eIdx k).2
      have huniq_flip : ∀ (i₁ i₂ : Fin n) (h1 : i₁.val + w < n) (h2 : i₂.val + w < n),
          x ⟨i₁.val + w, h1⟩ ≠ x i₁ → x ⟨i₂.val + w, h2⟩ ≠ x i₂ → i₁ = i₂ := by
        intro i₁ i₂ h1 h2 hd1 hd2
        by_contra hne
        wlog hlt : i₁.val < i₂.val generalizing i₁ i₂ h1 h2 hd1 hd2
        · exact this i₂ i₁ h2 h1 hd2 hd1 (Ne.symm hne) (by omega)
        let P_even : ℕ → Prop := fun t => i₁.val < t ∧ ∃ ht : t + w ≤ n,
          statePar (fun r : Fin w => x ⟨t + r.val, by omega⟩) = false
        have hex_t : ∃ t, P_even t := ⟨i₂.val, hlt, by omega, hport_even i₂ h2 hd2⟩
        let t₀ := Nat.find hex_t
        have ht₀ : P_even t₀ := Nat.find_spec hex_t
        have ht₀_le : t₀ + w ≤ n := ht₀.2.1
        have ht₀_min : ∀ t < t₀, ¬ P_even t := fun t ht => Nat.find_min hex_t ht
        have hp1 : statePar (fun r : Fin w => x ⟨i₁.val + 1 + r.val, by omega⟩) = true := by
          rw [winPar_step hn hw x i₁.val h1, hport_even i₁ h1 hd1]
          cases hxa : x ⟨i₁.val, by omega⟩ <;> cases hxb : x ⟨i₁.val + w, h1⟩
          · exact absurd (hxb.trans hxa.symm) hd1
          · rfl
          · rfl
          · exact absurd (hxb.trans hxa.symm) hd1
        have ht₀_gt : i₁.val + 1 < t₀ := by
          by_contra hle
          have heq : t₀ = i₁.val + 1 := by omega
          have hpar := ht₀.2.2
          have hpar' : statePar (fun r : Fin w => x ⟨i₁.val + 1 + r.val, by omega⟩) = false := by
            simpa only [heq] using hpar
          rw [hp1] at hpar'
          exact Bool.noConfusion hpar'
        have hprev_true : statePar (fun r : Fin w => x ⟨(t₀ - 1) + r.val, by omega⟩) = true := by
          have hnot := ht₀_min (t₀ - 1) (by omega)
          dsimp only [P_even] at hnot
          cases hv : statePar (fun r : Fin w => x ⟨(t₀ - 1) + r.val, by omega⟩)
          · exfalso; exact hnot ⟨by omega, by omega, hv⟩
          · rfl
        have hstep_prev := winPar_step hn hw x (t₀ - 1) (by omega)
        have heq_t : t₀ - 1 + 1 = t₀ := by omega
        have ht0_f : statePar (fun r : Fin w => x ⟨(t₀ - 1) + 1 + r.val, by omega⟩) = false := by
          simpa only [heq_t] using ht₀.2.2
        rw [ht0_f, hprev_true] at hstep_prev
        have hdiff_prev : x ⟨(t₀ - 1) + w, by omega⟩ ≠ x ⟨t₀ - 1, by omega⟩ := by
          intro heq
          rw [heq] at hstep_prev
          cases x ⟨t₀ - 1, by omega⟩ <;> simp at hstep_prev
        have heven_prev := hport_even ⟨t₀ - 1, by omega⟩ (by dsimp; omega) hdiff_prev
        rw [hprev_true] at heven_prev
        exact Bool.noConfusion heven_prev
      by_cases hfix : ∀ (i : Fin n) (hiw : i.val + w < n), x ⟨i.val + w, hiw⟩ = x i
      · left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfix⟩
      · right
        push Not at hfix
        obtain ⟨i₀, hi0w, hdiff0⟩ := hfix
        obtain ⟨k, hk, hki0, hwin0⟩ := hport_step i₀ hi0w hdiff0
        refine ⟨k, hk, ?_⟩
        have hagree_all : ∀ j : Fin n, code k j = x j := by
          have hagree_win : ∀ r : Fin w, code k ⟨i₀.val + r.val, by omega⟩ = x ⟨i₀.val + r.val, by omega⟩ := by
            intro r
            have h1 := congrFun (hcodeOf_win (eIdx k)) ⟨r.val, by omega⟩
            have h2 := congrFun hwin0 ⟨r.val, by omega⟩
            dsimp only [win, loc, port] at h1 h2
            rw [hki0] at h1
            have hmr : (i₀.val + r.val) % n = i₀.val + r.val := Nat.mod_eq_of_lt (by omega)
            have hfr : (⟨(i₀.val + r.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨i₀.val + r.val, by omega⟩ := Fin.ext hmr
            rw [hfr] at h1 h2
            dsimp only [code]
            exact h1.trans h2.symm
          have hagree_w : code k ⟨i₀.val + w, hi0w⟩ = x ⟨i₀.val + w, hi0w⟩ := by
            have h1 := congrFun (hcodeOf_win (eIdx k)) ⟨w, by omega⟩
            have h2 := congrFun hwin0 ⟨w, by omega⟩
            dsimp only [win, loc, port] at h1 h2
            rw [hki0] at h1
            have hmw : (i₀.val + w) % n = i₀.val + w := Nat.mod_eq_of_lt hi0w
            have hfw : (⟨(i₀.val + w) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨i₀.val + w, hi0w⟩ := Fin.ext hmw
            rw [hfw] at h1 h2
            dsimp only [code]
            exact h1.trans h2.symm
          have hstep_eq : ∀ (i : Fin n) (hiw : i.val + w < n), i.val ≠ i₀.val →
              x ⟨i.val + w, hiw⟩ = x i := by
            intro i hiw hne
            by_contra hdiff
            exact hne (congrArg Fin.val (huniq_flip i i₀ hiw hi0w hdiff hdiff0))
          have hup : ∀ (d : ℕ) (hd : i₀.val + d < n), code k ⟨i₀.val + d, hd⟩ = x ⟨i₀.val + d, hd⟩ := by
            intro d
            induction d using Nat.strong_induction_on with
            | ind d ih =>
              intro hd
              by_cases hdw : d < w
              · exact hagree_win ⟨d, hdw⟩
              · by_cases hdweq : d = w
                · subst hdweq; exact hagree_w
                · have hprev_ne : i₀.val + (d - w) ≠ i₀.val := by omega
                  have h1 := hcodeOf_step (eIdx k) ⟨i₀.val + (d - w), by omega⟩ (by dsimp; omega) (by dsimp; omega)
                  have h2 := hstep_eq ⟨i₀.val + (d - w), by omega⟩ (by dsimp; omega) hprev_ne
                  have hfin : (⟨i₀.val + (d - w) + w, by omega⟩ : Fin n) = ⟨i₀.val + d, hd⟩ :=
                    Fin.ext (by dsimp; omega)
                  rw [hfin] at h1 h2
                  dsimp only [code]
                  rw [h1, h2]
                  exact ih (d - w) (by omega) (by omega)
          have hdown : ∀ (d : ℕ) (hd : d ≤ i₀.val),
              code k ⟨i₀.val - d, by omega⟩ = x ⟨i₀.val - d, by omega⟩ := by
            intro d
            induction d using Nat.strong_induction_on with
            | ind d ih =>
              intro hd
              by_cases hd0 : d = 0
              · subst hd0; simpa using hagree_win ⟨0, hw⟩
              · have hne : i₀.val - d ≠ i₀.val := by omega
                have h1 := hcodeOf_step (eIdx k) ⟨i₀.val - d, by omega⟩ (by dsimp; omega) (by dsimp; omega)
                have h2 := hstep_eq ⟨i₀.val - d, by omega⟩ (by dsimp; omega) hne
                dsimp only [code]
                rw [← h1, ← h2]
                by_cases hdw : d ≤ w
                · have hfin : (⟨i₀.val - d + w, by omega⟩ : Fin n) = ⟨i₀.val + (w - d), by omega⟩ :=
                    Fin.ext (by dsimp; omega)
                  rw [hfin]
                  exact hagree_win ⟨w - d, by omega⟩
                · have hfin : (⟨i₀.val - d + w, by omega⟩ : Fin n) = ⟨i₀.val - (d - w), by omega⟩ :=
                    Fin.ext (by dsimp; omega)
                  rw [hfin]
                  exact ih (d - w) (by omega) (by omega)
          intro j
          by_cases hle : i₀.val ≤ j.val
          · have hfin : (⟨i₀.val + (j.val - i₀.val), by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
            rw [← hfin]; exact hup (j.val - i₀.val) (by omega)
          · have hfin : (⟨i₀.val - (i₀.val - j.val), by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
            rw [← hfin]; exact hdown (i₀.val - j.val) (by omega)
        funext j; exact hagree_all j
    · rintro (hfix | ⟨k, hk, rfl⟩) i
      · left
        dsimp only [base]
        by_cases hiw : i.val + w < n
        · rw [if_pos hiw]
          dsimp only [win, loc]
          have hm0 : (i.val + 0) % n = i.val := Nat.mod_eq_of_lt i.isLt
          have hmw : (i.val + w) % n = i.val + w := Nat.mod_eq_of_lt hiw
          have hf0 : (⟨(i.val + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := Fin.ext hm0
          have hfw : (⟨(i.val + w) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨i.val + w, hiw⟩ := Fin.ext hmw
          rw [hf0, hfw]
          have hper := (Finset.mem_filter.mp hfix).2 i hiw
          simp [hper]
        · rw [if_neg hiw]
      · by_cases hip : i.val = (eIdx k).1.val
        · right
          refine ⟨k, hk, ?_⟩
          apply Prod.ext
          · apply Fin.ext; dsimp only [port, portOf]; exact hip.symm
          · have hi_eq : i = ⟨(eIdx k).1.val, by omega⟩ := Fin.ext hip
            rw [hi_eq]
            exact (hcodeOf_win (eIdx k)).symm
        · left
          dsimp only [base]
          by_cases hiw : i.val + w < n
          · rw [if_pos hiw]
            dsimp only [win, loc, code]
            have hm0 : (i.val + 0) % n = i.val := Nat.mod_eq_of_lt i.isLt
            have hmw : (i.val + w) % n = i.val + w := Nat.mod_eq_of_lt hiw
            have hf0 : (⟨(i.val + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := Fin.ext hm0
            have hfw : (⟨(i.val + w) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨i.val + w, hiw⟩ := Fin.ext hmw
            rw [hf0, hfw, hcodeOf_step (eIdx k) i hiw hip]
            simp
          · rw [if_neg hiw]

-- Case 4: Large n, small h = n - w - 1 (n - w ≥ 9 ∧ 32 * (n - w) < n)
theorem pow2_ge_32_mul (d : ℕ) (hd : 9 ≤ d) : 32 * d ≤ 2 ^ d := by
  induction d with
  | zero => omega
  | succ d ih =>
    by_cases h9 : d = 8
    · subst h9; decide
    · have hd9 : 9 ≤ d := by omega
      have hih := ih hd9
      rw [pow_succ']
      omega

theorem pow2_gt_4_mul_large (k : ℕ) (hk : 16 ≤ k) : 4 * (16 * k + 15) < 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h16 : k = 15
    · subst h16; decide
    · have hk16 : 16 ≤ k := by omega
      have hih := ih hk16
      rw [pow_succ']
      omega

theorem case_large_dense (n w : ℕ) (hn : 0 < n) (hw : 0 < w)
    (hd9 : 9 ≤ n - w) (h32 : 32 * (n - w) < n) :
    let D := 2 ^ w
    let J := 2 ^ (min n (w + 1))
    let K := min (2 ^ n) (n * D)
    let Word := Fin n → Bool
    let Slot := Fin n × (Fin (w + 1) → Bool)
    ∃ (M : ℕ) (base : Slot → Bool) (port : Fin M → Slot)
        (code : Fin M → Word) (fixed : Finset Word),
      J ≤ M ∧ K ≤ 64 * M ∧ (n - w) * D ≤ 2 * M ∧ Function.Injective port ∧
      Function.Injective code ∧ (∀ i, base (port i) = false ∧ code i ∉ fixed) ∧
      (fixed.card = 0 ∨ fixed.card = D) ∧ (n ≤ w + 1 → M = 2 ^ n ∧ fixed = ∅) ∧
      ∀ enabled : Finset (Fin M), solSet n w hn (fun slot =>
        base slot || decide (slot ∈ enabled.image port)) = fixed ∪ enabled.image code := by
  intro D J K Word Slot
  let h := n - w - 1
  have hh8 : 8 ≤ h := by omega
  have hnw : n - h = w + 1 := by omega
  have hn288 : 288 < n := by omega
  let t0 := Nat.clog 2 (2 * n)
  let t := max h t0
  have hht : h ≤ t := le_max_left h t0
  have h2n_le : 2 * n ≤ 2 ^ t := by
    have h1 : 2 * n ≤ 2 ^ t0 := Nat.le_pow_clog (by omega : 1 < 2) (2 * n)
    exact h1.trans (Nat.pow_le_pow_right (by omega) (le_max_right h t0))
  have ht_pos : 0 < t := by omega
  have ht_lt_div : t + h + 2 < n / 2 := by
    have hsmall_t0 : t0 ≤ n / 16 := by
      apply Nat.clog_le_of_le_pow
      have hk16 : 16 ≤ n / 16 := by omega
      have hp := pow2_gt_4_mul_large (n / 16) hk16
      have hdiv : n ≤ 16 * (n / 16) + 15 := by omega
      omega
    have hsmall_h : h < n / 32 := by omega
    have : t ≤ n / 16 := max_le (by omega) hsmall_t0
    omega
  have htn : t + 3 ≤ n := by omega
  let sites : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val < n / 2)
  have hsites_card : sites.card = n / 2 := by
    have hbij : sites = (Finset.univ : Finset (Fin (n / 2))).image (fun j => ⟨j.val, by omega⟩) := by
      ext i
      simp only [sites, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hi; exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
      · rintro ⟨j, rfl⟩; exact j.isLt
    have hinj_s : Function.Injective (fun j : Fin (n / 2) => (⟨j.val, by omega⟩ : Fin n)) :=
      fun a b hab => Fin.ext (by have := congrArg Fin.val hab; exact this)
    rw [hbij, Finset.card_image_of_injective _ hinj_s,
      Finset.card_univ, Fintype.card_fin]
  let pool : Finset Word := sites.biUnion (Good n t hn htn)
  let owner : ↥pool → Fin n := fun z =>
    Classical.choose (Finset.mem_biUnion.mp z.property)
  have howner_site : ∀ z : ↥pool, owner z ∈ sites := fun z =>
    (Classical.choose_spec (Finset.mem_biUnion.mp z.property)).1
  have howner_good : ∀ z : ↥pool, z.val ∈ Good n t hn htn (owner z) := fun z =>
    (Classical.choose_spec (Finset.mem_biUnion.mp z.property)).2
  have howner_eq : ∀ (z : ↥pool) (i : Fin n), z.val ∈ Good n t hn htn i → owner z = i :=
    fun z i hzi => good_unique_site n t hn htn ht_pos (howner_good z) hzi
  have hpool_card : (n / 2) * 2 ^ (n - t - 3) ≤ pool.card := by
    have hdisj : Set.PairwiseDisjoint (sites : Set (Fin n)) (Good n t hn htn) := by
      intro i _ j _ hij
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro w hwi hwj
      exact hij (good_unique_site n t hn htn ht_pos hwi hwj)
    rw [Finset.card_biUnion hdisj]
    calc (n / 2) * 2 ^ (n - t - 3)
        = sites.card * 2 ^ (n - t - 3) := by rw [hsites_card]
      _ = ∑ _i ∈ sites, 2 ^ (n - t - 3) := by simp
      _ ≤ ∑ i ∈ sites, (Good n t hn htn i).card := Finset.sum_le_sum fun i _ => by
            rw [card_Good]; exact card_Good0 n t hn htn h2n_le
  let M := pool.card
  let ePool : Fin M ≃ ↥pool := (Fintype.equivFinOfCardEq (by simp [M])).symm
  let code : Fin M → Word := fun k => (ePool k).val
  let port : Fin M → Slot := fun k => (owner (ePool k), win n w hn (code k) (owner (ePool k)))
  let base : Slot → Bool := fun slot =>
    decide ((∃ a ∈ pool, slot.2 = win n w hn a slot.1) ∧ ∀ k : Fin M, port k ≠ slot)
  have huniq_pool : ∀ (a b : ↥pool),
      win n w hn a.val (owner a) = win n w hn b.val (owner a) → a = b := by
    intro a b hwin
    let i := owner a
    let va := shift n hn i a.val
    let vb := shift n hn i b.val
    have hva : va ∈ Good0 n t hn htn := (mem_Good_iff n t hn htn i a.val).mp (howner_good a)
    have hagree : ∀ j : Fin (n - h), a.val (loc n hn (i.val + j.val)) = b.val (loc n hn (i.val + j.val)) := by
      intro j
      have hj := congrFun hwin ⟨j.val, by omega⟩
      exact hj
    have hvb_exists : ∃ s : Fin n, hasRun n t hn vb s := by
      have hbm : shift n hn (owner b) b.val ∈ Good0 n t hn htn :=
        (mem_Good_iff n t hn htn (owner b) b.val).mp (howner_good b)
      have hrb : hasRun n t hn b.val (loc n hn ((owner b).val + (n - t))) :=
        (hasRun_shift n t hn (owner b) b.val ⟨n - t, by omega⟩).mp
          ((good0_hasRun_iff n t hn htn hbm ⟨n - t, by omega⟩).mpr rfl)
      refine ⟨loc n hn ((owner b).val + (n - t) + (n - i.val)), ?_⟩
      rw [hasRun_shift]
      have hloc : loc n hn (i.val + (loc n hn ((owner b).val + (n - t) + (n - i.val))).val) =
          loc n hn ((owner b).val + (n - t)) := by
        apply Fin.ext
        change (i.val + ((owner b).val + (n - t) + (n - i.val)) % n) % n =
          ((owner b).val + (n - t)) % n
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hsum : i.val + ((owner b).val + (n - t) + (n - i.val)) =
            (owner b).val + (n - t) + n := by omega
        rw [hsum, Nat.add_mod_right]
      rw [hloc]; exact hrb
    have hfalse_imp : ∀ x : Fin n, vb x = false → va x = false := by
      intro x hxf
      by_cases hlt : x.val < n - h
      · have hag := hagree ⟨x.val, hlt⟩
        change va x = vb x at hag
        rw [hag, hxf]
      · have hvP := (Finset.mem_filter.mp hva).1
        have hvz := (Finset.mem_filter.mp hvP).2.2.2
        have hklt : x.val - (n - t) < t := by omega
        have hkx : (⟨n - t + (x.val - (n - t)), by omega⟩ : Fin n) = x := Fin.ext (by dsimp; omega)
        have hz := hvz ⟨x.val - (n - t), hklt⟩
        rw [hkx] at hz; exact hz
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
        rw [hfalse_imp x hbx, hbx]
    exact Subtype.ext (shift_injective n hn i hv_eq)
  have hcode_inj : Function.Injective code := fun a b hab => ePool.injective (Subtype.ext hab)
  have hport_inj : Function.Injective port := by
    intro a b hab
    have h1 : owner (ePool a) = owner (ePool b) := (Prod.ext_iff.mp hab).1
    have h2 : win n w hn (code a) (owner (ePool a)) = win n w hn (code b) (owner (ePool b)) :=
      (Prod.ext_iff.mp hab).2
    rw [← h1] at h2
    exact ePool.injective (huniq_pool (ePool a) (ePool b) h2)
  have hK64 : K ≤ 64 * M ∧ (n - w) * D ≤ 2 * M := by
    by_cases hth : t = h
    · have hnt3 : n - t - 3 = w - 2 := by omega
      have hM : (n / 2) * 2 ^ (w - 2) ≤ M := by rw [← hnt3]; exact hpool_card
      have hD4 : D = 4 * 2 ^ (w - 2) := by
        dsimp only [D]; have hw2 : w = (w - 2) + 2 := by omega
        conv_lhs => rw [hw2, pow_add]
        ring
      have hn_half : n ≤ 2 * (n / 2) + 1 := by omega
      constructor
      · have hK : K ≤ n * D := Nat.min_le_right _ _
        have h1 : 64 * M ≥ 16 * (n / 2) * D := by
          calc 64 * M ≥ 64 * ((n / 2) * 2 ^ (w - 2)) := Nat.mul_le_mul_left 64 hM
            _ = 16 * (n / 2) * (4 * 2 ^ (w - 2)) := by ring
            _ = 16 * (n / 2) * D := by rw [← hD4]
        have h2 : n * D ≤ 16 * (n / 2) * D := Nat.mul_le_mul_right D (by omega)
        omega
      · have h1 : 2 * M * 2 ≥ (n / 2) * D := by
          calc 2 * M * 2 = 4 * M := by ring
            _ ≥ 4 * ((n / 2) * 2 ^ (w - 2)) := Nat.mul_le_mul_left 4 hM
            _ = (n / 2) * (4 * 2 ^ (w - 2)) := by ring
            _ = (n / 2) * D := by rw [← hD4]
        have h2 : 2 * (n - w) ≤ n / 2 := by omega
        have h3 : 2 * ((n - w) * D) ≤ (n / 2) * D := by
          calc 2 * ((n - w) * D) = (2 * (n - w)) * D := by ring
            _ ≤ (n / 2) * D := Nat.mul_le_mul_right D h2
        omega
    · have ht_eq : t = t0 := by omega
      have ht_ge3 : 3 ≤ t := by omega
      have hprev : 2 ^ (t - 1) < 2 * n := by
        by_contra hge_p
        have hle_t0 : t0 ≤ t - 1 := Nat.clog_le_of_le_pow (by omega)
        omega
      have hpow_le : 2 ^ t ≤ 8 * (n / 2) := by
        have hdiv4 : 4 ∣ 2 ^ (t - 1) := by
          have : t - 1 = (t - 3) + 2 := by omega
          rw [this, pow_add]; exact ⟨2 ^ (t - 3), by ring⟩
        obtain ⟨q, hq⟩ := hdiv4
        have hq_le : 4 * q ≤ 4 * (n / 2) := by omega
        have ht_exp : 2 ^ t = 2 * 2 ^ (t - 1) := by
          have : t = (t - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ']
        rw [ht_exp, hq]
        omega
      have h2n_64M : 2 ^ n ≤ 64 * M := by
        have h2n_split : 2 ^ n = 2 ^ (n - 3) * 8 := by
          have hn3 : n = (n - 3) + 3 := by omega
          conv_lhs => rw [hn3, pow_add]
          rfl
        have hmul : 2 ^ n * 2 ^ t ≤ (64 * M) * 2 ^ t := by
          calc 2 ^ n * 2 ^ t
              ≤ 2 ^ n * (8 * (n / 2)) := Nat.mul_le_mul_left _ hpow_le
            _ = 64 * ((n / 2) * 2 ^ (n - 3)) := by rw [h2n_split]; ring
            _ = 64 * ((n / 2) * (2 ^ (n - t - 3) * 2 ^ t)) := by
                rw [← pow_add]; congr 3; omega
            _ = (64 * ((n / 2) * 2 ^ (n - t - 3))) * 2 ^ t := by ring
            _ ≤ (64 * M) * 2 ^ t := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 64 hpool_card)
        exact Nat.le_of_mul_le_mul_right hmul (by positivity)
      constructor
      · exact (Nat.min_le_left _ _).trans h2n_64M
      · have h32d := pow2_ge_32_mul (n - w) hd9
        have hpow_split : 2 ^ n = 2 ^ (n - w) * D := by
          dsimp only [D]; rw [← pow_add]; congr 1; omega
        have h1 : 32 * ((n - w) * D) ≤ 64 * M := by
          calc 32 * ((n - w) * D) = (32 * (n - w)) * D := by ring
            _ ≤ 2 ^ (n - w) * D := Nat.mul_le_mul_right D h32d
            _ = 2 ^ n := hpow_split.symm
            _ ≤ 64 * M := h2n_64M
        omega
  refine ⟨M, base, port, code, ∅, ?_, hK64.1, hK64.2, hport_inj, hcode_inj, ?_, ?_, ?_, ?_⟩
  · have hJ : J = 2 * D := by dsimp only [J, D]; rw [Nat.min_eq_right (by omega), pow_succ']
    have : 9 * D ≤ (n - w) * D := Nat.mul_le_mul_right D hd9
    omega
  · intro k
    exact ⟨by simp [base], Finset.notMem_empty _⟩
  · left; rfl
  · intro hle; omega
  · intro enabled
    ext y
    simp only [solSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.empty_union,
      Finset.mem_image, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · intro hall
      have hmatch : ∀ j : Fin n, ∃ a : ↥pool, win n w hn y j = win n w hn a.val j := by
        intro j
        rcases hall j with hbase | ⟨k, _, hpk⟩
        · simp only [base, decide_eq_true_eq] at hbase
          obtain ⟨⟨a, hap, hwin⟩, _⟩ := hbase
          exact ⟨⟨a, hap⟩, hwin⟩
        · have h1 : owner (ePool k) = j := (Prod.ext_iff.mp hpk).1
          have h2 : win n w hn (code k) (owner (ePool k)) = win n w hn y j := (Prod.ext_iff.mp hpk).2
          rw [h1] at h2
          exact ⟨ePool k, h2.symm⟩
      let jstar : Fin n := ⟨n / 2 + h, by omega⟩
      obtain ⟨astar, hastar⟩ := hmatch jstar
      let istar : Fin n := owner astar
      have histar_lt : istar.val < n / 2 := (Finset.mem_filter.mp (howner_site astar)).2
      have hin_jstar : ∀ x : Fin n, x.val < n / 2 ∨ n / 2 + h ≤ x.val → y x = astar.val x := by
        intro x hx
        rcases hx with hlt | hge
        · let off : ℕ := n - (n / 2 + h) + x.val
          have hoff : off < w + 1 := by omega
          have hv := congrFun hastar ⟨off, hoff⟩
          dsimp only [win, loc, jstar] at hv
          have hsum : n / 2 + h + off = x.val + n := by omega
          have hfin : (⟨(n / 2 + h + off) % n, Nat.mod_lt _ hn⟩ : Fin n) = x :=
            Fin.ext (by dsimp; rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt])
          rw [hfin] at hv; exact hv
        · let off : ℕ := x.val - (n / 2 + h)
          have hoff : off < w + 1 := by omega
          have hv := congrFun hastar ⟨off, hoff⟩
          dsimp only [win, loc, jstar] at hv
          have hsum : n / 2 + h + off = x.val := by omega
          have hfin : (⟨(n / 2 + h + off) % n, Nat.mod_lt _ hn⟩ : Fin n) = x :=
            Fin.ext (by dsimp; rw [hsum, Nat.mod_eq_of_lt x.isLt])
          rw [hfin] at hv; exact hv
      have hsite_in_jstar : ∀ (i : Fin n), i.val < n / 2 → ∀ r : ℕ, r ≤ t + 1 →
          (loc n hn (i.val + (n - r))).val < n / 2 ∨ n / 2 + h ≤ (loc n hn (i.val + (n - r))).val := by
        intro i hi r hr
        dsimp only [loc]
        by_cases hri : r ≤ i.val
        · left
          have h1 : i.val + (n - r) = (i.val - r) + n := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
        · right
          have h1 : i.val + (n - r) < n := by omega
          rw [Nat.mod_eq_of_lt h1]; omega
      obtain ⟨b, hb⟩ := hmatch istar
      let ib : Fin n := owner b
      have hib_lt : ib.val < n / 2 := (Finset.mem_filter.mp (howner_site b)).2
      have ha_good0 : shift n hn istar astar.val ∈ Good0 n t hn htn :=
        (mem_Good_iff n t hn htn istar astar.val).mp (howner_good astar)
      have hb_good0 : shift n hn ib b.val ∈ Good0 n t hn htn :=
        (mem_Good_iff n t hn htn ib b.val).mp (howner_good b)
      have ha_val0 : astar.val istar = true := by
        have hvP := (Finset.mem_filter.mp ha_good0).1
        have hv0 := (Finset.mem_filter.mp hvP).2.1
        dsimp only [shift, loc] at hv0
        have hf : (⟨(istar.val + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = istar :=
          Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt istar.isLt])
        rw [hf] at hv0; exact hv0
      have ha_flank : astar.val (loc n hn (istar.val + (n - t - 1))) = true := by
        have hvP := (Finset.mem_filter.mp ha_good0).1
        exact (Finset.mem_filter.mp hvP).2.2.1
      have ha_zero : ∀ r : ℕ, 1 ≤ r → r ≤ t → astar.val (loc n hn (istar.val + (n - r))) = false := by
        intro r hr1 hrt
        have hvP := (Finset.mem_filter.mp ha_good0).1
        have hvz := (Finset.mem_filter.mp hvP).2.2.2 ⟨t - r, by omega⟩
        dsimp only [shift] at hvz
        have heq : loc n hn (istar.val + (n - t + (t - r))) = loc n hn (istar.val + (n - r)) := by
          congr 1; omega
        rw [heq] at hvz; exact hvz
      have hb_zero : ∀ r : ℕ, 1 ≤ r → r ≤ t → b.val (loc n hn (ib.val + (n - r))) = false := by
        intro r hr1 hrt
        have hvP := (Finset.mem_filter.mp hb_good0).1
        have hvz := (Finset.mem_filter.mp hvP).2.2.2 ⟨t - r, by omega⟩
        dsimp only [shift] at hvz
        have heq : loc n hn (ib.val + (n - t + (t - r))) = loc n hn (ib.val + (n - r)) := by
          congr 1; omega
        rw [heq] at hvz; exact hvz
      have hin_istar : ∀ off : ℕ, off < w + 1 →
          y (loc n hn (istar.val + off)) = b.val (loc n hn (istar.val + off)) := fun off hoff =>
        congrFun hb ⟨off, hoff⟩
      have hib_eq : ib = istar := by
        by_contra hne
        by_cases hall_in : ∀ r : ℕ, 1 ≤ r → r ≤ t →
            (loc n hn (ib.val + (n - r) + (n - istar.val))).val < w + 1
        · have hrun : hasRun n t hn astar.val (loc n hn (ib.val + (n - t))) := by
            intro r
            have hloc1 : loc n hn ((loc n hn (ib.val + (n - t))).val + r.val) =
                loc n hn (ib.val + (n - (t - r.val))) := by
              apply Fin.ext
              change ((ib.val + (n - t)) % n + r.val) % n = (ib.val + (n - (t - r.val))) % n
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              congr 1; omega
            rw [hloc1]
            let r' := t - r.val
            have hr'1 : 1 ≤ r' := by omega
            have hr't : r' ≤ t := by omega
            let off := (loc n hn (ib.val + (n - r') + (n - istar.val))).val
            have hoff : off < w + 1 := hall_in r' hr'1 hr't
            have hloc2 : loc n hn (istar.val + off) = loc n hn (ib.val + (n - r')) := by
              apply Fin.ext
              change (istar.val + (ib.val + (n - r') + (n - istar.val)) % n) % n = (ib.val + (n - r')) % n
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have hsum : istar.val + (ib.val + (n - r') + (n - istar.val)) = ib.val + (n - r') + n := by omega
              rw [hsum, Nat.add_mod_right]
            have hya := hin_jstar (loc n hn (ib.val + (n - r'))) (hsite_in_jstar ib hib_lt r' (by omega))
            have hyb := hin_istar off hoff
            rw [hloc2] at hyb
            rw [← hya, hyb]
            exact hb_zero r' hr'1 hr't
          have hrun_s : hasRun n t hn (shift n hn istar astar.val)
              (loc n hn (ib.val + (n - t) + (n - istar.val))) := by
            rw [hasRun_shift]
            have hloc : loc n hn (istar.val + (loc n hn (ib.val + (n - t) + (n - istar.val))).val) =
                loc n hn (ib.val + (n - t)) := by
              apply Fin.ext
              change (istar.val + (ib.val + (n - t) + (n - istar.val)) % n) % n = (ib.val + (n - t)) % n
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have hsum : istar.val + (ib.val + (n - t) + (n - istar.val)) = ib.val + (n - t) + n := by omega
              rw [hsum, Nat.add_mod_right]
            rw [hloc]; exact hrun
          have heq := (good0_hasRun_iff n t hn htn ha_good0 _).mp hrun_s
          change (ib.val + (n - t) + (n - istar.val)) % n = n - t at heq
          have hmod : (ib.val + (n - istar.val)) % n = 0 := by
            have hstep : ((ib.val + (n - t) + (n - istar.val)) + t) % n = (n - t + t) % n := by
              calc ((ib.val + (n - t) + (n - istar.val)) + t) % n
                  = ((ib.val + (n - t) + (n - istar.val)) % n + t % n) % n := Nat.add_mod _ _ _
                _ = ((n - t) % n + t % n) % n := by rw [heq]; conv_rhs => rw [Nat.mod_eq_of_lt (show n - t < n by omega)]
                _ = (n - t + t) % n := (Nat.add_mod _ _ _).symm
            have hl : ib.val + (n - t) + (n - istar.val) + t = ib.val + (n - istar.val) + n := by omega
            have hr : n - t + t = n := by omega
            rw [hl, hr, Nat.add_mod_right, Nat.mod_self] at hstep; exact hstep
          have hij : ib.val = istar.val := by
            by_cases hle : istar.val ≤ ib.val
            · have h1 : ib.val + (n - istar.val) = (ib.val - istar.val) + n := by omega
              rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hmod; omega
            · rw [Nat.mod_eq_of_lt (by omega)] at hmod; omega
          exact hne (Fin.ext hij)
        · push Not at hall_in
          obtain ⟨rb, hrb1, hrbt, hge_off⟩ := hall_in
          let off0 := (loc n hn (ib.val + (n - rb) + (n - istar.val))).val
          have hoff0_ge : w + 1 ≤ off0 := hge_off
          have hoff0_lt : off0 < n := Nat.mod_lt _ hn
          let r0 := n - off0
          have hr0_1 : 1 ≤ r0 := by omega
          have hr0_h : r0 ≤ h := by omega
          have hcong : (ib.val + (n - rb) + (n - istar.val)) % n = n - r0 := by
            dsimp only [off0, r0, loc] at *; omega
          by_cases hcmp : r0 < rb
          · let d := rb - r0
            have hd1 : 1 ≤ d := by omega
            have hdt : d ≤ t := by omega
            have hist_eq : istar = loc n hn (ib.val + (n - d)) := by
              apply Fin.ext
              have hmod : (ib.val + (n - d) + (n - istar.val)) % n = 0 := by
                have hstep : ((ib.val + (n - rb) + (n - istar.val)) + r0) % n = ((n - r0) + r0) % n := by
                  calc ((ib.val + (n - rb) + (n - istar.val)) + r0) % n
                      = ((ib.val + (n - rb) + (n - istar.val)) % n + r0 % n) % n := Nat.add_mod _ _ _
                    _ = ((n - r0) % n + r0 % n) % n := by rw [hcong]; conv_rhs => rw [Nat.mod_eq_of_lt (show n - r0 < n by omega)]
                    _ = ((n - r0) + r0) % n := (Nat.add_mod _ _ _).symm
                have hl : ib.val + (n - rb) + (n - istar.val) + r0 = ib.val + (n - d) + (n - istar.val) := by omega
                have hr : n - r0 + r0 = n := by omega
                rw [hl, hr, Nat.mod_self] at hstep; exact hstep
              have hsum : (ib.val + (n - d)) % n = istar.val := by
                have hlt_m : (ib.val + (n - d)) % n < n := Nat.mod_lt _ hn
                by_cases hle : istar.val ≤ (ib.val + (n - d)) % n
                · have h1 : (ib.val + (n - d)) % n + (n - istar.val) = ((ib.val + (n - d)) % n - istar.val) + n := by omega
                  have h2 : ((ib.val + (n - d)) % n + (n - istar.val)) % n = 0 := by
                    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; exact hmod
                  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h2; omega
                · have h2 : ((ib.val + (n - d)) % n + (n - istar.val)) % n = 0 := by
                    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; exact hmod
                  rw [Nat.mod_eq_of_lt (by omega)] at h2; omega
              exact hsum.symm
            have hb_f : b.val istar = false := by rw [hist_eq]; exact hb_zero d hd1 hdt
            have hy_a : y istar = astar.val istar := hin_jstar istar (Or.inl histar_lt)
            have hy_b : y istar = b.val istar := by
              have h0 := hin_istar 0 (by omega)
              have hf : loc n hn (istar.val + 0) = istar := Fin.ext (by dsimp [loc]; rw [Nat.mod_eq_of_lt istar.isLt])
              rw [hf] at h0; exact h0
            rw [hy_a, ha_val0] at hy_b
            rw [hb_f] at hy_b
            exact Bool.noConfusion hy_b
          · by_cases heq_r : rb = r0
            · have hmod : (ib.val + (n - istar.val)) % n = 0 := by
                have hstep : ((ib.val + (n - rb) + (n - istar.val)) + rb) % n = ((n - r0) + rb) % n := by
                  calc ((ib.val + (n - rb) + (n - istar.val)) + rb) % n
                      = ((ib.val + (n - rb) + (n - istar.val)) % n + rb % n) % n := Nat.add_mod _ _ _
                    _ = ((n - r0) % n + rb % n) % n := by rw [hcong]; conv_rhs => rw [Nat.mod_eq_of_lt (show n - r0 < n by omega)]
                    _ = ((n - r0) + rb) % n := (Nat.add_mod _ _ _).symm
                have hl : ib.val + (n - rb) + (n - istar.val) + rb = ib.val + (n - istar.val) + n := by omega
                have hr : n - r0 + rb = n := by omega
                rw [hl, hr, Nat.add_mod_right, Nat.mod_self] at hstep; exact hstep
              have hij : ib.val = istar.val := by
                by_cases hle : istar.val ≤ ib.val
                · have h1 : ib.val + (n - istar.val) = (ib.val - istar.val) + n := by omega
                  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hmod; omega
                · rw [Nat.mod_eq_of_lt (by omega)] at hmod; omega
              exact hne (Fin.ext hij)
            · let q := r0 - rb
              have hq1 : 1 ≤ q := by omega
              have hqh : q < h := by omega
              let d := t + 1 - q
              have hd1 : 1 ≤ d := by omega
              have hdt : d ≤ t := by omega
              let pstar := loc n hn (istar.val + (n - t - 1))
              have hp_eq : pstar = loc n hn (ib.val + (n - d)) := by
                apply Fin.ext
                change (istar.val + (n - t - 1)) % n = (ib.val + (n - d)) % n
                have hstep : ((ib.val + (n - rb) + (n - istar.val)) + (istar.val + (n - t - 1))) % n =
                    ((n - r0) + (istar.val + (n - t - 1))) % n := by
                  calc ((ib.val + (n - rb) + (n - istar.val)) + (istar.val + (n - t - 1))) % n
                      = ((ib.val + (n - rb) + (n - istar.val)) % n + (istar.val + (n - t - 1)) % n) % n := Nat.add_mod _ _ _
                    _ = ((n - r0) % n + (istar.val + (n - t - 1)) % n) % n := by rw [hcong]; conv_rhs => rw [Nat.mod_eq_of_lt (show n - r0 < n by omega)]
                    _ = ((n - r0) + (istar.val + (n - t - 1))) % n := (Nat.add_mod _ _ _).symm
                have hl : ib.val + (n - rb) + (n - istar.val) + (istar.val + (n - t - 1)) =
                    (ib.val + (n - d) + (n - r0)) + n := by omega
                rw [hl, Nat.add_mod_right] at hstep
                have hadd_cancel : ∀ A B C : ℕ, (A + C) % n = (B + C) % n → A % n = B % n := by
                  intro A B C hAB
                  have h1 : (A + C + (n - C % n)) % n = (B + C + (n - C % n)) % n := by
                    rw [Nat.add_mod (A + C), hAB, ← Nat.add_mod (B + C)]
                  have hC : C + (n - C % n) = n * (C / n + 1) := by
                    have hdiv := (Nat.div_add_mod C n).symm
                    have hlt := Nat.mod_lt C hn
                    rw [Nat.mul_add, Nat.mul_one]; omega
                  have hA : A + C + (n - C % n) = A + n * (C / n + 1) := by omega
                  have hB : B + C + (n - C % n) = B + n * (C / n + 1) := by omega
                  rw [hA, hB, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at h1
                  exact h1
                have hsw : n - r0 + (istar.val + (n - t - 1)) = (istar.val + (n - t - 1)) + (n - r0) := by ring
                rw [hsw] at hstep
                exact (hadd_cancel _ _ (n - r0) hstep).symm
              have hb_f : b.val pstar = false := by rw [hp_eq]; exact hb_zero d hd1 hdt
              have hy_a : y pstar = astar.val pstar := by
                have hps : pstar = loc n hn (istar.val + (n - (t + 1))) := rfl
                rw [hps]; exact hin_jstar _ (hsite_in_jstar istar histar_lt (t + 1) le_rfl)
              have hy_b : y pstar = b.val pstar := hin_istar (n - t - 1) (by omega)
              rw [hy_a, ha_flank] at hy_b
              rw [hb_f] at hy_b
              exact Bool.noConfusion hy_b
      have hy_eq_b : y = b.val := by
        funext x
        let off := (loc n hn (x.val + (n - istar.val))).val
        have hloc : loc n hn (istar.val + off) = x := by
          apply Fin.ext
          change (istar.val + (x.val + (n - istar.val)) % n) % n = x.val
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have hsum : istar.val + (x.val + (n - istar.val)) = x.val + n := by omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
        by_cases hoff : off < w + 1
        · have hyb := hin_istar off hoff
          rw [hloc] at hyb; exact hyb
        · let r := n - off
          have hr1 : 1 ≤ r := by have := Nat.mod_lt (x.val + (n - istar.val)) hn; omega
          have hrh : r ≤ h := by omega
          have hrt : r ≤ t := by omega
          have hx_eq : x = loc n hn (istar.val + (n - r)) := by
            rw [← hloc]; congr 1; omega
          have hya := hin_jstar x (by rw [hx_eq]; exact hsite_in_jstar istar histar_lt r (by omega))
          rw [hya, hx_eq, ha_zero r hr1 hrt, ← hib_eq, hb_zero r hr1 hrt]
      let kb : Fin M := ePool.symm b
      have hcode_kb : code kb = y := by
        dsimp only [code, kb]; rw [ePool.apply_symm_apply, hy_eq_b]
      have hport_kb : port kb = (istar, win n w hn y istar) := by
        dsimp only [port, kb, code]
        have hob : owner b = istar := hib_eq
        rw [ePool.apply_symm_apply, hy_eq_b, hob]
      rcases hall istar with hbase | ⟨k', hk', hpk'⟩
      · exfalso
        rw [← hport_kb] at hbase
        simp only [base, decide_eq_true_eq] at hbase
        exact hbase.2 kb rfl
      · have hkeq : k' = kb := hport_inj (hpk'.trans hport_kb.symm)
        rw [hkeq] at hk'
        exact ⟨kb, hk', hcode_kb⟩
    · rintro ⟨k, hk, rfl⟩ j
      by_cases hj : j = owner (ePool k)
      · right
        rw [hj]
        exact ⟨k, hk, rfl⟩
      · left
        simp only [base, decide_eq_true_eq]
        refine ⟨⟨code k, (ePool k).property, rfl⟩, fun k' hpk' => ?_⟩
        have h1 : owner (ePool k') = j := (Prod.ext_iff.mp hpk').1
        have h2 : win n w hn (code k') (owner (ePool k')) = win n w hn (code k) j := (Prod.ext_iff.mp hpk').2
        rw [← h1] at h2
        have heq := huniq_pool (ePool k') (ePool k) h2
        rw [heq] at h1
        exact hj h1.symm

end PEqualNP.Outside.L_lib_826

theorem PEqualNP.Outside.L_lib_826 :
∀ (n w : Nat) (hn : 0 < n), 0 < w →
  let D := 2^w
  let J := 2^(min n (w+1))
  let K := min (2^n) (n*D)
  let Word := Fin n → Bool
  let Slot := Fin n × (Fin (w+1) → Bool)
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let solutions := fun (tab : Slot → Bool) => (Finset.univ : Finset Word).filter
    (fun x => ∀ i : Fin n, tab (i,fun j => x (loc (i.val+j.val))) = true)
  ∃ (M : Nat) (base : Slot → Bool) (port : Fin M → Slot)
      (code : Fin M → Word) (fixed : Finset Word),
    J ≤ M ∧ K ≤ 64*M ∧ (n-w)*D ≤ 2*M ∧ Function.Injective port ∧
    Function.Injective code ∧ (∀ i, base (port i) = false ∧ code i ∉ fixed) ∧
    (fixed.card = 0 ∨ fixed.card = D) ∧ (n ≤ w+1 → M = 2^n ∧ fixed = ∅) ∧
    ∀ enabled : Finset (Fin M), solutions (fun slot =>
      base slot || decide (slot ∈ enabled.image port)) = fixed ∪ enabled.image code := by
  intro n w hn hw D J K Word Slot loc solutions
  by_cases h1 : n ≤ w + 1
  · exact PEqualNP.Outside.L_lib_826.case_small_n n w hn hw h1
  · by_cases h2 : n ≤ w + 3
    · exact PEqualNP.Outside.L_lib_826.case_mid_small n w hn hw (by omega) h2
    · by_cases h3 : n - w ≤ 8 ∨ n ≤ 32 * (n - w)
      · exact PEqualNP.Outside.L_lib_826.case_parity_flip n w hn hw (by omega) h3
      · push Not at h3
        exact PEqualNP.Outside.L_lib_826.case_large_dense n w hn hw (by omega) h3.2

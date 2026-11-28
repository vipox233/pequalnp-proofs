import PEqualNP.CircuitLowerBounds.L016

namespace PEqualNP.Outside.L_clb_115

namespace Lib845
namespace PW

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
    simp at h2n
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
      rw [hemp, Finset.card_empty, Nat.zero_mul]
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
        = 2 * (Bad.card * 2 ^ t) := Nat.mul_assoc _ _ _
      _ ≤ 2 * (n * 2 ^ (n - t - 2)) := Nat.mul_le_mul_left 2 hbad_mul
      _ = (2 * n) * 2 ^ (n - t - 2) := (Nat.mul_assoc _ _ _).symm
      _ ≤ 2 ^ t * 2 ^ (n - t - 2) := Nat.mul_le_mul_right _ h2n
      _ = 2 ^ (n - t - 2) * 2 ^ t := Nat.mul_comm _ _
  have h2bad : 2 * Bad.card ≤ 2 ^ (n - t - 2) :=
    Nat.le_of_mul_le_mul_right h2mul (Nat.two_pow_pos t)
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
    simp at h2n
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

end PW

open Classical

private lemma card_sites_gt (m h : ℕ) (hh : h < m) :
    ((Finset.univ : Finset (Fin m)).filter (fun i : Fin m => h < i.val)).card = m - h - 1 := by
  let S := (Finset.univ : Finset (Fin m)).filter (fun i : Fin m => h < i.val)
  let f : Fin (m - h - 1) → Fin m := fun k => ⟨h + 1 + k.val, by omega⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Fin.ext
    have := congrArg Fin.val hxy
    dsimp [f] at this
    omega
  have hS : S = Finset.univ.image f := by
    ext i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      refine ⟨⟨i.val - (h + 1), by omega⟩, ?_⟩
      apply Fin.ext
      dsimp [f]
      omega
    · rintro ⟨k, rfl⟩
      dsimp [f]
      omega
  change S.card = m - h - 1
  rw [hS, Finset.card_image_of_injective _ hf, Finset.card_fin]

private lemma card_pool_ge {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (owner : α → β) (c : ℕ)
    (hc : ∀ i : β, c ≤ ((Finset.univ : Finset α).filter (fun z => owner z = i)).card) :
    Fintype.card β * c ≤ Fintype.card α := by
  have hsum : ∑ i : β, ((Finset.univ : Finset α).filter (fun z => owner z = i)).card =
      Fintype.card α := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext z
      simp
    · intro i _ j _ hij
      simp only [Function.onFun, Finset.disjoint_left]
      intro z hzi hzj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzi hzj
      exact hij (hzi.symm.trans hzj)
  calc
    Fintype.card β * c = ∑ _i : β, c := by simp
    _ ≤ ∑ i : β, ((Finset.univ : Finset α).filter (fun z => owner z = i)).card :=
      Finset.sum_le_sum (fun i _ => hc i)
    _ = Fintype.card α := hsum

private def concatWord (a b : ℕ) (x : Fin a → Bool) (y : Fin b → Bool) : Fin (a + b) → Bool :=
  fun k => if hk : k.val < a then x ⟨k.val, hk⟩ else y ⟨k.val - a, by omega⟩

private lemma concatWord_lt (a b : ℕ) (x : Fin a → Bool) (y : Fin b → Bool) (k : ℕ) (hk : k < a) (hkn : k < a + b) :
    concatWord a b x y ⟨k, hkn⟩ = x ⟨k, hk⟩ := by
  dsimp [concatWord]
  rw [dif_pos hk]

private lemma concatWord_ge (a b : ℕ) (x : Fin a → Bool) (y : Fin b → Bool) (k : ℕ) (hk : k < b) (hkn : a + k < a + b) :
    concatWord a b x y ⟨a + k, hkn⟩ = y ⟨k, hk⟩ := by
  dsimp [concatWord]
  have hnot : ¬ (a + k < a) := by omega
  rw [dif_neg hnot]
  congr 1
  apply Fin.ext
  dsimp
  omega

private lemma concatWord_left (a b : ℕ) (x : Fin a → Bool) (y : Fin b → Bool) (u : Fin a) :
    concatWord a b x y ⟨u.val, by omega⟩ = x u := by
  dsimp [concatWord]
  rw [dif_pos u.isLt]

private lemma concatWord_right (a b : ℕ) (x : Fin a → Bool) (y : Fin b → Bool) (v : Fin b) :
    concatWord a b x y ⟨a + v.val, by omega⟩ = y v := by
  dsimp [concatWord]
  have hnot : ¬ (a + v.val < a) := by omega
  rw [dif_neg hnot]
  congr 1
  apply Fin.ext
  dsimp
  omega

private lemma concatWord_injective (a b : ℕ) :
    Function.Injective (fun p : (Fin a → Bool) × (Fin b → Bool) => concatWord a b p.1 p.2) := by
  rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
  apply Prod.ext
  · funext u
    have := congrFun h ⟨u.val, by omega⟩
    dsimp only at this
    rw [concatWord_left, concatWord_left] at this
    exact this
  · funext v
    have := congrFun h ⟨a + v.val, by omega⟩
    dsimp only at this
    rw [concatWord_right, concatWord_right] at this
    exact this

private lemma concatWord_eq_self (a b : ℕ) (z : Fin (a + b) → Bool) :
    concatWord a b (fun u : Fin a => z ⟨u.val, by omega⟩) (fun v : Fin b => z ⟨a + v.val, by omega⟩) = z := by
  funext k
  dsimp [concatWord]
  split_ifs with hk
  · rfl
  · congr 1
    apply Fin.ext
    dsimp
    omega

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
private theorem main_theorem :
∀ (a b w t : Nat) (hn : 0 < a+b),
  let n := a+b
  let h := n-(w+1)
  h ≤ t → t+3 ≤ min a b → 2*max a b ≤ 2^t →
  let Word := Fin n → Bool
  let Pat := Fin (w+1) → Bool
  let Slot := Fin n × Pat
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let solutions := fun (tab : Slot → Bool) =>
    (Finset.univ : Finset Word).filter (fun x =>
      ∀ i : Fin n, tab (i,fun j => x (loc (i.val+j.val))) = true)
  ∃ (M : Nat) (code : Fin M → Word) (base : Slot → Bool) (left right : Fin M → Slot),
    (a-h-1)*2^(a-t-3)*((b-h-1)*2^(b-t-3)) ≤ M ∧
    Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
    (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
      base (left i) = false ∧ base (right i) = false) ∧
    ∀ A B : Finset (Fin M), solutions (fun slot =>
      base slot || decide (slot ∈ A.image left) || decide (slot ∈ B.image right)) =
        (A ∩ B).image code := by
  intro a b w t hn
  dsimp only
  intro hht htab h2
  have hta : t + 3 ≤ a := le_trans htab (min_le_left a b)
  have htb : t + 3 ≤ b := le_trans htab (min_le_right a b)
  have ha : 0 < a := by omega
  have hb : 0 < b := by omega
  have h2a : 2 * a ≤ 2 ^ t := le_trans (Nat.mul_le_mul_left 2 (le_max_left a b)) h2
  have h2b : 2 * b ≤ 2 ^ t := le_trans (Nat.mul_le_mul_left 2 (le_max_right a b)) h2
  let n := a + b
  let h := n - (w + 1)
  have hnh : n - h ≤ w + 1 := by omega
  have ha_lt_w : a ≤ w + 1 := by omega
  have hb_lt_w : b ≤ w + 1 := by omega
  let sitesA : Finset (Fin a) := Finset.univ.filter (fun i : Fin a => h < i.val)
  let sitesB : Finset (Fin b) := Finset.univ.filter (fun i : Fin b => h < i.val)
  obtain ⟨poolA, ownerA, hcardA, huniqA⟩ := PW.main_proof a h t ha hht hta h2a sitesA
  obtain ⟨poolB, ownerB, hcardB, huniqB⟩ := PW.main_proof b h t hb hht htb h2b sitesB
  have hsitesA_card : Fintype.card (↥sitesA) = a - h - 1 := by
    rw [Fintype.card_coe]
    exact card_sites_gt a h (by omega)
  have hsitesB_card : Fintype.card (↥sitesB) = b - h - 1 := by
    rw [Fintype.card_coe]
    exact card_sites_gt b h (by omega)
  have hpoolA_ge : (a - h - 1) * 2 ^ (a - t - 3) ≤ Fintype.card (↥poolA) := by
    rw [← hsitesA_card]
    exact card_pool_ge ownerA (2 ^ (a - t - 3)) hcardA
  have hpoolB_ge : (b - h - 1) * 2 ^ (b - t - 3) ≤ Fintype.card (↥poolB) := by
    rw [← hsitesB_card]
    exact card_pool_ge ownerB (2 ^ (b - t - 3)) hcardB
  let M := Fintype.card (↥poolA × ↥poolB)
  let e : Fin M ≃ ↥poolA × ↥poolB := (Fintype.equivFin (↥poolA × ↥poolB)).symm
  let loc : ℕ → Fin n := fun k => ⟨k % n, Nat.mod_lt _ hn⟩
  let win : Fin n → (Fin n → Bool) → (Fin (w + 1) → Bool) :=
    fun r z j => z (loc (r.val + j.val))
  let code : Fin M → (Fin n → Bool) := fun i => concatWord a b (e i).1.val (e i).2.val
  let leftRow : Fin M → Fin n := fun i => ⟨(ownerA (e i).1).val.val, by
    have := (ownerA (e i).1).val.isLt
    omega⟩
  let rightRow : Fin M → Fin n := fun i => ⟨a + (ownerB (e i).2).val.val, by
    have := (ownerB (e i).2).val.isLt
    omega⟩
  let left : Fin M → (Fin n × (Fin (w + 1) → Bool)) := fun i => (leftRow i, win (leftRow i) (code i))
  let right : Fin M → (Fin n × (Fin (w + 1) → Bool)) := fun i => (rightRow i, win (rightRow i) (code i))
  have hleftRow_gt : ∀ i : Fin M, h < (leftRow i).val := by
    intro i
    have hmem := (ownerA (e i).1).property
    simp only [sitesA, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem
  have hleftRow_lt : ∀ i : Fin M, (leftRow i).val < a := fun i => (ownerA (e i).1).val.isLt
  have hrightRow_gt : ∀ i : Fin M, a + h < (rightRow i).val := by
    intro i
    have hmem := (ownerB (e i).2).property
    simp only [sitesB, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    change a + h < a + (ownerB (e i).2).val.val
    omega
  have hrightRow_ge : ∀ i : Fin M, a ≤ (rightRow i).val := by
    intro i
    change a ≤ a + (ownerB (e i).2).val.val
    omega
  have hleft_ident : ∀ i j : Fin M, win (leftRow j) (code i) = win (leftRow j) (code j) → i = j := by
    intro i j hw
    apply e.injective
    apply Prod.ext
    · refine (huniqA (e j).1 (e i).1 ?_).symm
      intro k
      let p := (ownerA (e j).1).val.val
      have hp_gt : h < p := hleftRow_gt j
      have hp_lt : p < a := hleftRow_lt j
      by_cases hlt : p + k.val < a
      · have hk_w : k.val < w + 1 := by omega
        have hstep := congrFun hw ⟨k.val, hk_w⟩
        have hloc_n : loc ((leftRow j).val + k.val) = ⟨p + k.val, by omega⟩ := by
          apply Fin.ext
          change (p + k.val) % (a + b) = p + k.val
          exact Nat.mod_eq_of_lt (by omega)
        have hloc_a : (⟨(p + k.val) % a, Nat.mod_lt _ ha⟩ : Fin a) = ⟨p + k.val, hlt⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hlt
        dsimp only [win, code] at hstep
        rw [hloc_n, concatWord_lt a b _ _ _ (by omega), concatWord_lt a b _ _ _ (by omega)] at hstep
        dsimp only
        rw [hloc_a]
        exact hstep.symm
      · have hk_w : k.val + b < w + 1 := by omega
        have hstep := congrFun hw ⟨k.val + b, hk_w⟩
        have hrem_lt : p + k.val - a < a := by omega
        have hloc_n : loc ((leftRow j).val + (k.val + b)) = ⟨p + k.val - a, by omega⟩ := by
          apply Fin.ext
          change (p + (k.val + b)) % (a + b) = p + k.val - a
          have hsum : p + (k.val + b) = (p + k.val - a) + (a + b) := by omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hloc_a : (⟨(p + k.val) % a, Nat.mod_lt _ ha⟩ : Fin a) = ⟨p + k.val - a, hrem_lt⟩ := by
          apply Fin.ext
          change (p + k.val) % a = p + k.val - a
          have hsum : (p + k.val) % a = ((p + k.val - a) + a) % a := congrArg (· % a) (by omega)
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hrem_lt]
        dsimp only [win, code] at hstep
        rw [hloc_n, concatWord_lt a b _ _ _ (by omega), concatWord_lt a b _ _ _ (by omega)] at hstep
        dsimp only
        rw [hloc_a]
        exact hstep.symm
    · apply Subtype.ext
      funext v
      let p := (ownerA (e j).1).val.val
      have hp_gt : h < p := hleftRow_gt j
      have hp_lt : p < a := hleftRow_lt j
      have hj_w : a - p + v.val < w + 1 := by omega
      have hstep := congrFun hw ⟨a - p + v.val, hj_w⟩
      have hloc_n : loc ((leftRow j).val + (a - p + v.val)) = ⟨a + v.val, by omega⟩ := by
        apply Fin.ext
        change (p + (a - p + v.val)) % (a + b) = a + v.val
        have hsum : p + (a - p + v.val) = a + v.val := by omega
        rw [hsum, Nat.mod_eq_of_lt (by omega)]
      dsimp only [win, code] at hstep
      rw [hloc_n, concatWord_ge a b _ _ _ (by omega), concatWord_ge a b _ _ _ (by omega)] at hstep
      exact hstep
  have hright_ident : ∀ i j : Fin M, win (rightRow j) (code i) = win (rightRow j) (code j) → i = j := by
    intro i j hw
    apply e.injective
    apply Prod.ext
    · apply Subtype.ext
      funext u
      let q := (ownerB (e j).2).val.val
      have hq_gt : h < q := by
        have := hrightRow_gt j
        change a + h < a + q at this
        omega
      have hq_lt : q < b := (ownerB (e j).2).val.isLt
      have hj_w : b - q + u.val < w + 1 := by omega
      have hstep := congrFun hw ⟨b - q + u.val, hj_w⟩
      have hloc_n : loc ((rightRow j).val + (b - q + u.val)) = ⟨u.val, by omega⟩ := by
        apply Fin.ext
        change (a + q + (b - q + u.val)) % (a + b) = u.val
        have hsum : a + q + (b - q + u.val) = u.val + (a + b) := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      dsimp only [win, code] at hstep
      rw [hloc_n, concatWord_lt a b _ _ _ (by omega), concatWord_lt a b _ _ _ (by omega)] at hstep
      exact hstep
    · refine (huniqB (e j).2 (e i).2 ?_).symm
      intro k
      let q := (ownerB (e j).2).val.val
      have hq_gt : h < q := by
        have := hrightRow_gt j
        change a + h < a + q at this
        omega
      have hq_lt : q < b := (ownerB (e j).2).val.isLt
      by_cases hlt : q + k.val < b
      · have hk_w : k.val < w + 1 := by omega
        have hstep := congrFun hw ⟨k.val, hk_w⟩
        have hloc_n : loc ((rightRow j).val + k.val) = ⟨a + (q + k.val), by omega⟩ := by
          apply Fin.ext
          change (a + q + k.val) % (a + b) = a + (q + k.val)
          have hsum : a + q + k.val = a + (q + k.val) := by omega
          rw [hsum, Nat.mod_eq_of_lt (by omega)]
        have hloc_b : (⟨(q + k.val) % b, Nat.mod_lt _ hb⟩ : Fin b) = ⟨q + k.val, hlt⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hlt
        dsimp only [win, code] at hstep
        rw [hloc_n, concatWord_ge a b _ _ _ (by omega), concatWord_ge a b _ _ _ (by omega)] at hstep
        dsimp only
        rw [hloc_b]
        exact hstep.symm
      · have hk_w : k.val + a < w + 1 := by omega
        have hstep := congrFun hw ⟨k.val + a, hk_w⟩
        have hrem_lt : q + k.val - b < b := by omega
        have hloc_n : loc ((rightRow j).val + (k.val + a)) = ⟨a + (q + k.val - b), by omega⟩ := by
          apply Fin.ext
          change (a + q + (k.val + a)) % (a + b) = a + (q + k.val - b)
          have hsum : a + q + (k.val + a) = (a + (q + k.val - b)) + (a + b) := by omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hloc_b : (⟨(q + k.val) % b, Nat.mod_lt _ hb⟩ : Fin b) = ⟨q + k.val - b, hrem_lt⟩ := by
          apply Fin.ext
          change (q + k.val) % b = q + k.val - b
          have hsum : (q + k.val) % b = ((q + k.val - b) + b) % b := congrArg (· % b) (by omega)
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hrem_lt]
        dsimp only [win, code] at hstep
        rw [hloc_n, concatWord_ge a b _ _ _ (by omega), concatWord_ge a b _ _ _ (by omega)] at hstep
        dsimp only
        rw [hloc_b]
        exact hstep.symm
  have hcode_inj : Function.Injective code := by
    intro i j hij
    apply e.injective
    have hp := @concatWord_injective a b ((e i).1.val, (e i).2.val) ((e j).1.val, (e j).2.val) hij
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hp)) (Subtype.ext (congrArg Prod.snd hp))
  have hleft_inj : Function.Injective left := by
    intro i j hij
    have hrow : leftRow i = leftRow j := congrArg Prod.fst hij
    have hpat : win (leftRow i) (code i) = win (leftRow j) (code j) := congrArg Prod.snd hij
    rw [hrow] at hpat
    exact hleft_ident i j hpat
  have hright_inj : Function.Injective right := by
    intro i j hij
    have hrow : rightRow i = rightRow j := congrArg Prod.fst hij
    have hpat : win (rightRow i) (code i) = win (rightRow j) (code j) := congrArg Prod.snd hij
    rw [hrow] at hpat
    exact hright_ident i j hpat
  let base : (Fin n × (Fin (w + 1) → Bool)) → Bool := fun slot =>
    if slot.1.val = 0 then
      decide ((fun u : Fin a => slot.2 ⟨u.val, by omega⟩) ∈ poolA)
    else if slot.1.val = a then
      decide ((fun v : Fin b => slot.2 ⟨v.val, by omega⟩) ∈ poolB)
    else
      decide (slot ∉ Finset.univ.image left ∧ slot ∉ Finset.univ.image right)
  refine ⟨M, code, base, left, right, ?_, hcode_inj, hleft_inj, hright_inj, ?_, ?_⟩
  · calc
      (a - h - 1) * 2 ^ (a - t - 3) * ((b - h - 1) * 2 ^ (b - t - 3))
          ≤ Fintype.card (↥poolA) * Fintype.card (↥poolB) :=
        Nat.mul_le_mul hpoolA_ge hpoolB_ge
      _ = M := by simp [M, Fintype.card_prod]
  · intro i
    have h1 : (left i).1.val < a := hleftRow_lt i
    have h2' : a ≤ (right i).1.val := hrightRow_ge i
    have h1_ne0 : (left i).1.val ≠ 0 := by
      have hgt : h < (left i).1.val := hleftRow_gt i
      omega
    have h1_nea : (left i).1.val ≠ a := by omega
    have h2_ne0 : (right i).1.val ≠ 0 := by omega
    have h2_nea : (right i).1.val ≠ a := by
      have hgt := hrightRow_gt i
      change a + h < (right i).1.val at hgt
      omega
    refine ⟨h1, h2', ?_, ?_⟩
    · dsimp only [base]
      rw [if_neg h1_ne0, if_neg h1_nea]
      simp [Finset.mem_image]
    · dsimp only [base]
      rw [if_neg h2_ne0, if_neg h2_nea]
      simp [Finset.mem_image]
  · intro A B
    ext x
    rw [Finset.mem_filter, Finset.mem_image]
    simp only [Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · intro hx
      have h0 := hx ⟨0, hn⟩
      have h0_notL : (⟨0, hn⟩, win ⟨0, hn⟩ x) ∉ A.image left := by
        simp only [Finset.mem_image, not_exists, not_and]
        intro j _ hj
        have := congrArg (fun s => s.1.val) hj
        dsimp [left] at this
        have := hleftRow_gt j
        omega
      have h0_notR : (⟨0, hn⟩, win ⟨0, hn⟩ x) ∉ B.image right := by
        simp only [Finset.mem_image, not_exists, not_and]
        intro j _ hj
        have := congrArg (fun s => s.1.val) hj
        dsimp [right] at this
        have := hrightRow_ge j
        omega
      change base (⟨0, hn⟩, win ⟨0, hn⟩ x) || decide ((⟨0, hn⟩, win ⟨0, hn⟩ x) ∈ A.image left) ||
          decide ((⟨0, hn⟩, win ⟨0, hn⟩ x) ∈ B.image right) = true at h0
      simp [h0_notL, h0_notR] at h0
      dsimp only [base] at h0
      rw [if_pos rfl, decide_eq_true_eq] at h0
      have hwin0 : (fun u : Fin a => win ⟨0, hn⟩ x ⟨u.val, by omega⟩) =
          (fun u : Fin a => x ⟨u.val, by omega⟩) := by
        funext u
        dsimp only [win, loc]
        congr 1
        apply Fin.ext
        change (0 + u.val) % (a + b) = u.val
        rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      rw [hwin0] at h0
      have ha_lt : a < n := by omega
      have ha_ok := hx ⟨a, ha_lt⟩
      have ha_notL : (⟨a, ha_lt⟩, win ⟨a, ha_lt⟩ x) ∉ A.image left := by
        simp only [Finset.mem_image, not_exists, not_and]
        intro j _ hj
        have := congrArg (fun s => s.1.val) hj
        dsimp [left] at this
        have := hleftRow_lt j
        omega
      have ha_notR : (⟨a, ha_lt⟩, win ⟨a, ha_lt⟩ x) ∉ B.image right := by
        simp only [Finset.mem_image, not_exists, not_and]
        intro j _ hj
        have := congrArg (fun s => s.1.val) hj
        dsimp [right] at this
        have := hrightRow_gt j
        omega
      change base (⟨a, ha_lt⟩, win ⟨a, ha_lt⟩ x) || decide ((⟨a, ha_lt⟩, win ⟨a, ha_lt⟩ x) ∈ A.image left) ||
          decide ((⟨a, ha_lt⟩, win ⟨a, ha_lt⟩ x) ∈ B.image right) = true at ha_ok
      simp [ha_notL, ha_notR] at ha_ok
      dsimp only [base] at ha_ok
      have ha_ne0 : a ≠ 0 := by omega
      rw [if_neg ha_ne0, if_pos rfl, decide_eq_true_eq] at ha_ok
      have hwina : (fun v : Fin b => win ⟨a, ha_lt⟩ x ⟨v.val, by omega⟩) =
          (fun v : Fin b => x ⟨a + v.val, by omega⟩) := by
        funext v
        dsimp only [win, loc]
        congr 1
        apply Fin.ext
        change (a + v.val) % (a + b) = a + v.val
        exact Nat.mod_eq_of_lt (by omega)
      rw [hwina] at ha_ok
      let xL : ↥poolA := ⟨fun u : Fin a => x ⟨u.val, by omega⟩, h0⟩
      let xR : ↥poolB := ⟨fun v : Fin b => x ⟨a + v.val, by omega⟩, ha_ok⟩
      let i : Fin M := e.symm (xL, xR)
      have hcode_x : code i = x := by
        dsimp only [code, i]
        rw [Equiv.apply_symm_apply]
        exact concatWord_eq_self a b x
      refine ⟨i, ⟨?_, ?_⟩, hcode_x⟩
      · have hL := hx (leftRow i)
        change base (leftRow i, win (leftRow i) x) ||
            decide ((leftRow i, win (leftRow i) x) ∈ A.image left) ||
            decide ((leftRow i, win (leftRow i) x) ∈ B.image right) = true at hL
        rw [← hcode_x] at hL
        have hbase_f : base (left i) = false := by
          dsimp only [base]
          have h1 : h < (left i).1.val := hleftRow_gt i
          have h2' : (left i).1.val < a := hleftRow_lt i
          rw [if_neg (by omega), if_neg (by omega)]
          simp [Finset.mem_image]
        have hnotR : left i ∉ B.image right := by
          simp only [Finset.mem_image, not_exists, not_and]
          intro j _ hj
          have hval : (rightRow j).val = (leftRow i).val := congrArg (fun s => s.1.val) hj
          have h1 := hleftRow_lt i
          have h2' := hrightRow_ge j
          omega
        change base (left i) || decide (left i ∈ A.image left) || decide (left i ∈ B.image right) = true at hL
        simp [hbase_f, hnotR] at hL
        rcases hL with ⟨j, hjA, hji⟩
        exact (hleft_inj hji) ▸ hjA
      · have hR := hx (rightRow i)
        change base (rightRow i, win (rightRow i) x) ||
            decide ((rightRow i, win (rightRow i) x) ∈ A.image left) ||
            decide ((rightRow i, win (rightRow i) x) ∈ B.image right) = true at hR
        rw [← hcode_x] at hR
        have hbase_f : base (right i) = false := by
          dsimp only [base]
          have h1 : a + h < (right i).1.val := hrightRow_gt i
          rw [if_neg (by omega), if_neg (by omega)]
          simp [Finset.mem_image]
        have hnotL : right i ∉ A.image left := by
          simp only [Finset.mem_image, not_exists, not_and]
          intro j _ hj
          have hval : (leftRow j).val = (rightRow i).val := congrArg (fun s => s.1.val) hj
          have h1 := hleftRow_lt j
          have h2' := hrightRow_ge i
          omega
        change base (right i) || decide (right i ∈ A.image left) || decide (right i ∈ B.image right) = true at hR
        simp [hbase_f, hnotL] at hR
        rcases hR with ⟨j, hjB, hji⟩
        exact (hright_inj hji) ▸ hjB
    · rintro ⟨i, ⟨hiA, hiB⟩, rfl⟩
      intro r
      change base (r, win r (code i)) || decide ((r, win r (code i)) ∈ A.image left) ||
          decide ((r, win r (code i)) ∈ B.image right) = true
      by_cases hr0 : r.val = 0
      · have hr_eq : r = ⟨0, hn⟩ := Fin.ext hr0
        subst hr_eq
        have hbase_t : base (⟨0, hn⟩, win ⟨0, hn⟩ (code i)) = true := by
          dsimp only [base]
          rw [if_pos rfl, decide_eq_true_eq]
          have hwin0 : (fun u : Fin a => win ⟨0, hn⟩ (code i) ⟨u.val, by omega⟩) = (e i).1.val := by
            funext u
            dsimp only [win, loc, code]
            have hloc : (⟨(0 + u.val) % (a + b), Nat.mod_lt _ hn⟩ : Fin n) = ⟨u.val, by omega⟩ := by
              apply Fin.ext
              change (0 + u.val) % (a + b) = u.val
              rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
            rw [hloc, concatWord_left]
          rw [hwin0]
          exact (e i).1.property
        rw [hbase_t]
        rfl
      · by_cases hra : r.val = a
        · have ha_lt : a < n := by omega
          have hr_eq : r = ⟨a, ha_lt⟩ := Fin.ext hra
          subst hr_eq
          have hbase_t : base (⟨a, by omega⟩, win ⟨a, by omega⟩ (code i)) = true := by
            dsimp only [base]
            rw [if_neg hr0, if_pos rfl, decide_eq_true_eq]
            have hwina : (fun v : Fin b => win ⟨a, by omega⟩ (code i) ⟨v.val, by omega⟩) = (e i).2.val := by
              funext v
              dsimp only [win, loc, code]
              have hloc : (⟨(a + v.val) % (a + b), Nat.mod_lt _ hn⟩ : Fin n) = ⟨a + v.val, by omega⟩ := by
                apply Fin.ext
                exact Nat.mod_eq_of_lt (by omega)
              rw [hloc, concatWord_right]
            rw [hwina]
            exact (e i).2.property
          rw [hbase_t]
          rfl
        · by_cases hmemL : (r, win r (code i)) ∈ Finset.univ.image left
          · rcases Finset.mem_image.mp hmemL with ⟨j, _, hj⟩
            have hrow : leftRow j = r := congrArg Prod.fst hj
            have hpat : win (leftRow j) (code j) = win r (code i) := congrArg Prod.snd hj
            rw [hrow] at hpat
            have hij : i = j := hleft_ident i j (by rw [hrow]; exact hpat.symm)
            subst hij
            have hmemA : (r, win r (code i)) ∈ A.image left := by
              rw [← hj]
              exact Finset.mem_image_of_mem left hiA
            rw [decide_eq_true hmemA]
            simp
          · by_cases hmemR : (r, win r (code i)) ∈ Finset.univ.image right
            · rcases Finset.mem_image.mp hmemR with ⟨j, _, hj⟩
              have hrow : rightRow j = r := congrArg Prod.fst hj
              have hpat : win (rightRow j) (code j) = win r (code i) := congrArg Prod.snd hj
              rw [hrow] at hpat
              have hij : i = j := hright_ident i j (by rw [hrow]; exact hpat.symm)
              subst hij
              have hmemB : (r, win r (code i)) ∈ B.image right := by
                rw [← hj]
                exact Finset.mem_image_of_mem right hiB
              rw [decide_eq_true hmemB]
              simp
            · have hbase_t : base (r, win r (code i)) = true := by
                dsimp only [base]
                rw [if_neg hr0, if_neg hra, decide_eq_true_eq]
                exact ⟨hmemL, hmemR⟩
              rw [hbase_t]
              rfl

theorem lib845 : (∀ (a b w t : Nat) (hn : 0 < a+b),
  let n := a+b
  let h := n-(w+1)
  h ≤ t → t+3 ≤ min a b → 2*max a b ≤ 2^t →
  let Word := Fin n → Bool
  let Pat := Fin (w+1) → Bool
  let Slot := Fin n × Pat
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let solutions := fun (tab : Slot → Bool) =>
    (Finset.univ : Finset Word).filter (fun x =>
      ∀ i : Fin n, tab (i,fun j => x (loc (i.val+j.val))) = true)
  ∃ (M : Nat) (code : Fin M → Word) (base : Slot → Bool) (left right : Fin M → Slot),
    (a-h-1)*2^(a-t-3)*((b-h-1)*2^(b-t-3)) ≤ M ∧
    Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
    (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
      base (left i) = false ∧ base (right i) = false) ∧
    ∀ A B : Finset (Fin M), solutions (fun slot =>
      base slot || decide (slot ∈ A.image left) || decide (slot ∈ B.image right)) =
        (A ∩ B).image code) :=
  main_theorem

end Lib845

open Finset PEqualNP.CircuitLowerBounds.Helpers

theorem ceil_mul (N p : ℕ) (hp : 0 < p) : N ≤ p * ((N + p - 1) / p) := by
  have h1 := Nat.div_add_mod (N + p - 1) p
  have h2 := Nat.mod_lt (N + p - 1) hp
  omega

theorem fold_rest {n B : ℕ} {Row : Type} (cc : Fin n → Row → Fin B → Bool) (tb : Fin n → Row)
    (l : List (Fin n)) (a b : Bool) (m : Fin B → Bool) (g : Bool × Bool × (Fin B → Bool) → Fin n → Bool × Bool × (Fin B → Bool))
    (hg : ∀ st i, i ∈ l → g st i = (st.1, st.2.1, fun k => st.2.2 k && cc i (tb i) k)) :
    l.foldl g (a, b, m) = (a, b, fun k => m k && decide (∀ i ∈ l, cc i (tb i) k = true)) := by
  induction l generalizing m with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, hg _ _ (by simp)]
    rw [ih _ (fun st i hi => hg st i (by simp [hi]))]
    simp only [Prod.mk.injEq, true_and]
    funext k
    simp only [List.mem_cons, forall_eq_or_imp]
    cases m k <;> cases cc j (tb j) k <;> simp

theorem foldl_conj {α β γ : Type} (E : α ≃ β) (g : α → γ → α) (l : List γ) (a : α) :
    l.foldl (fun s x => E (g (E.symm s) x)) (E a) = E (l.foldl g a) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih]

theorem or_pos (x y : ℕ) : (decide (0 < x) || decide (0 < y)) = decide (0 < x + y) := by
  by_cases hx : 0 < x <;> by_cases hy : 0 < y <;> simp [hx, hy] <;> omega

theorem xor_odd (x y : ℕ) : xor (decide (x % 2 = 1)) (decide (y % 2 = 1)) = decide ((x + y) % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rcases Nat.mod_two_eq_zero_or_one y with h' | h' <;>
    simp [Nat.add_mod, h, h']

theorem upper {Row : Type} (n p : ℕ) (hn : 0 < n) (hp : 0 < p) (c : Fin n → Row → (Fin n → Bool) → Bool) :
    ∃ (start : Fin (2 ^ (2 + (2 ^ n + p - 1) / p)))
      (step : Fin p → Fin n → Fin (2 ^ (2 + (2 ^ n + p - 1) / p)) → Row → Fin (2 ^ (2 + (2 ^ n + p - 1) / p)))
      (answer : Fin (2 ^ (2 + (2 ^ n + p - 1) / p)) → Bool × Bool), ∀ table : Fin n → Row,
      answer ((List.finRange p).foldl (fun prev passId =>
        (List.finRange n).foldl (fun state site => step passId site state (table site)) prev) start) =
        (decide (0 < (univ.filter (fun x => ∀ i, c i (table i) x = true)).card),
          (univ.filter (fun x => ∀ i, c i (table i) x = true)).card.testBit 0) := by
  generalize hN : 2 ^ n = N
  generalize hB : (N + p - 1) / p = B
  have hNB : N ≤ p * B := hB ▸ ceil_mul N p hp
  have hN1 : 0 < N := by rw [← hN]; positivity
  have hcard : Fintype.card (Bool × Bool × (Fin B → Bool)) = 2 ^ (2 + B) := by
    simp [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, pow_add]; ring
  let E : (Bool × Bool × (Fin B → Bool)) ≃ Fin (2 ^ (2 + B)) := Fintype.equivFinOfCardEq hcard
  let W : (Fin n → Bool) ≃ Fin N := Fintype.equivFinOfCardEq (by simp [← hN])
  let w : ℕ → Fin B → (Fin n → Bool) := fun q k =>
    if h : q * B + k.val < N then W.symm ⟨q * B + k.val, h⟩ else fun _ => false
  let cnt : ℕ → (Fin B → Bool) → ℕ := fun q m =>
    (univ.filter (fun k : Fin B => m k = true ∧ q * B + k.val < N)).card
  let f : ℕ → Fin n → (Bool × Bool × (Fin B → Bool)) → Row → (Bool × Bool × (Fin B → Bool)) :=
    fun q i st r => if i.val = 0 then
      (st.1 || decide (0 < cnt (q - 1) st.2.2), xor st.2.1 (decide (cnt (q - 1) st.2.2 % 2 = 1)),
        fun k => c i r (w q k))
    else (st.1, st.2.1, fun k => st.2.2 k && c i r (w q k))
  refine ⟨E (false, false, fun _ => false), fun q i s r => E (f q.val i (E.symm s) r),
    fun s => ((E.symm s).1 || decide (0 < cnt (p - 1) (E.symm s).2.2),
      xor (E.symm s).2.1 (decide (cnt (p - 1) (E.symm s).2.2 % 2 = 1))), ?_⟩
  intro table
  let sol : (Fin n → Bool) → Prop := fun x => ∀ i, c i (table i) x = true
  let mask : ℕ → Fin B → Bool := fun q k => decide (sol (w q k))
  let pass : ℕ → (Bool × Bool × (Fin B → Bool)) → (Bool × Bool × (Fin B → Bool)) := fun q st =>
    (List.finRange n).foldl (fun st site => f q site st (table site)) st
  have hpass : ∀ q a b m, pass q (a, b, m) = (a || decide (0 < cnt (q - 1) m),
      xor b (decide (cnt (q - 1) m % 2 = 1)), mask q) := by
    intro q a b m
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [pass]
    rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
    have h0 : f q 0 (a, b, m) (table 0) = (a || decide (0 < cnt (q - 1) m),
        xor b (decide (cnt (q - 1) m % 2 = 1)), fun k => c 0 (table 0) (w q k)) := by
      simp [f]
    rw [h0, fold_rest (fun i r k => c i.succ r (w q k)) (fun i => table i.succ) (List.finRange n')]
    · simp only [Prod.mk.injEq, true_and]
      funext k
      simp only [mask, sol, List.mem_finRange, true_implies]
      cases h : c 0 (table 0) (w q k) <;> simp [Fin.forall_fin_succ, h]
    · intro st i _
      simp [f, Fin.succ_ne_zero]
  have hD : ∀ P, (List.range (P + 1)).foldl (fun st q => pass q st) (false, false, fun _ => false) =
      (decide (0 < ∑ q ∈ range P, cnt q (mask q)), decide ((∑ q ∈ range P, cnt q (mask q)) % 2 = 1),
        mask P) := by
    intro P
    induction P with
    | zero =>
      simp only [List.range_one, List.foldl_cons, List.foldl_nil, hpass]
      simp [cnt]
    | succ P ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, hpass,
        Finset.sum_range_succ, or_pos, xor_odd]
      simp
  have hcount : (univ.filter sol).card = ∑ q ∈ range p, cnt q (mask q) := by
    have e1 : (univ.filter sol).card = (univ.filter (fun j : Fin N => sol (W.symm j))).card :=
      Finset.card_equiv W (by intro x; simp)
    have hB0 : 0 < B := by
      rcases Nat.eq_zero_or_pos B with h | h
      · rw [h] at hNB; omega
      · exact h
    rw [e1, Finset.card_eq_sum_card_fiberwise (f := fun j : Fin N => j.val / B) (t := range p)]
    · apply Finset.sum_congr rfl
      intro q hq
      symm
      apply Finset.card_bij (fun k hk => (⟨q * B + k.val, (Finset.mem_filter.mp hk).2.2⟩ : Fin N))
      · intro k hk
        simp only [cnt, mask, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hk ⊢
        refine ⟨?_, ?_⟩
        · have := hk.1
          simp only [w, dif_pos hk.2] at this
          exact this
        · have := k.isLt
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB0, Nat.div_eq_of_lt this]; simp
      · intro k1 _ k2 _ h
        simp only [Fin.mk.injEq] at h
        exact Fin.ext (by omega)
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hj2 : q * B + j.val % B = j.val := by
          rw [← hj.2]; have := Nat.div_add_mod j.val B; rw [Nat.mul_comm] at this; exact this
        have hlt : q * B + j.val % B < N := by rw [hj2]; exact j.isLt
        refine ⟨⟨j.val % B, Nat.mod_lt _ hB0⟩, ?_, ?_⟩
        · simp only [cnt, mask, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
          refine ⟨?_, hlt⟩
          simp only [w, dif_pos hlt]
          have : (⟨q * B + j.val % B, hlt⟩ : Fin N) = j := Fin.ext hj2
          rw [this]; exact hj.1
        · exact Fin.ext hj2
    · intro j _
      simp only [Finset.coe_range, Set.mem_Iio]
      rw [Nat.div_lt_iff_lt_mul hB0]
      have := j.isLt
      nlinarith
  have hrun : (List.finRange p).foldl (fun prev passId =>
      (List.finRange n).foldl (fun state site => E (f passId.val site (E.symm state) (table site))) prev)
        (E (false, false, fun _ => false)) =
      E ((List.range p).foldl (fun st q => pass q st) (false, false, fun _ => false)) := by
    have h1 : ∀ (q : ℕ) (s : Fin (2 ^ (2 + B))),
        (List.finRange n).foldl (fun state site => E (f q site (E.symm state) (table site))) s =
          E (pass q (E.symm s)) := by
      intro q s
      have := foldl_conj E (fun st site => f q site st (table site)) (List.finRange n) (E.symm s)
      simp only [Equiv.apply_symm_apply] at this
      exact this
    simp only [h1]
    have h2 := foldl_conj E (fun st (q : Fin p) => pass q.val st) (List.finRange p) (false, false, fun _ => false)
    rw [h2, ← List.map_coe_finRange_eq_range, List.foldl_map]
  simp only
  rw [hrun, Equiv.symm_apply_apply]
  obtain ⟨P, rfl⟩ : ∃ P, p = P + 1 := ⟨p - 1, by omega⟩
  rw [hD P]
  simp only [Nat.add_sub_cancel]
  rw [or_pos, xor_odd, ← Finset.sum_range_succ, ← hcount, Nat.testBit_zero]

theorem lindsey_w (M : ℕ) (A B : Finset (Fin M → Bool)) (ε : (Fin M → Bool) → ℤ)
    (hε : ∀ y, ε y * ε y = 1) :
    (∑ x ∈ A, ∑ y ∈ B, ipSign M x y * ε y) ^ 2 ≤ (A.card : ℤ) * (B.card : ℤ) * 2 ^ M := by
  have h1 : (∑ x ∈ A, ∑ y ∈ B, ipSign M x y * ε y) ^ 2 ≤
      (A.card : ℤ) * ∑ x ∈ A, (∑ y ∈ B, ipSign M x y * ε y) ^ 2 := sq_sum_le_card_mul_sum_sq
  have h2 : ∑ x ∈ A, (∑ y ∈ B, ipSign M x y * ε y) ^ 2 ≤
      ∑ x : Fin M → Bool, (∑ y ∈ B, ipSign M x y * ε y) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ A) (fun _ _ _ => sq_nonneg _)
  have h3 : ∑ x : Fin M → Bool, (∑ y ∈ B, ipSign M x y * ε y) ^ 2 = (B.card : ℤ) * 2 ^ M := by
    simp_rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    have : ∀ y ∈ B, ∑ x : Fin M → Bool, ∑ y' ∈ B, ipSign M x y * ε y * (ipSign M x y' * ε y') = 2 ^ M := by
      intro y hy
      rw [Finset.sum_comm]
      have e : ∀ y', ∑ x : Fin M → Bool, ipSign M x y * ε y * (ipSign M x y' * ε y') =
          ε y * ε y' * ∑ x : Fin M → Bool, ipSign M x y * ipSign M x y' := by
        intro y'
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      simp_rw [e, ipSign_orth]
      simp [hy, hε]
    rw [Finset.sum_congr rfl this]
    simp
  calc (∑ x ∈ A, ∑ y ∈ B, ipSign M x y * ε y) ^ 2
      ≤ (A.card : ℤ) * ∑ x ∈ A, (∑ y ∈ B, ipSign M x y * ε y) ^ 2 := h1
    _ ≤ (A.card : ℤ) * ((B.card : ℤ) * 2 ^ M) := by
        apply mul_le_mul_of_nonneg_left (h2.trans h3.le) (by positivity)
    _ = (A.card : ℤ) * (B.card : ℤ) * 2 ^ M := by ring

def sgn (b : Bool) : ℤ := if b then -1 else 1

theorem sgn_sq (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

def P {X Y : Type} {S : ℕ} (s0 : Fin S) (α : ℕ → Fin S → X → Fin S) (β : ℕ → Fin S → Y → Fin S)
    (x : X) (y : Y) : ℕ → Fin S
  | 0 => s0
  | q + 1 => β q (α q (P s0 α β x y q) x) y

def prev {S p : ℕ} (s0 : Fin S) (t : (Fin p → Fin S) × (Fin (p - 1) → Fin S)) (q : ℕ) : Fin S :=
  if h : q = 0 then s0 else if h' : q - 1 < p - 1 then t.2 ⟨q - 1, h'⟩ else s0

theorem proto {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (S p : ℕ) (hp : 0 < p) (s0 : Fin S)
    (α : ℕ → Fin S → X → Fin S) (β : ℕ → Fin S → Y → Fin S) (g : Fin S → Bool) (wt : X → Y → ℤ) (K : ℤ)
    (Lin : ∀ (A : Finset X) (B : Finset Y) (ε : Y → ℤ), (∀ y, ε y * ε y = 1) →
      (∑ x ∈ A, ∑ y ∈ B, wt x y * ε y) ^ 2 ≤ (A.card : ℤ) * (B.card : ℤ) * K) :
    (∑ x, ∑ y, wt x y * sgn (g (P s0 α β x y p))) ^ 2 ≤
      (S : ℤ) ^ (2 * p - 1) * (Fintype.card X : ℤ) * (Fintype.card Y : ℤ) * K := by
  classical
  let T := (Fin p → Fin S) × (Fin (p - 1) → Fin S)
  let tau : X × Y → T := fun xy =>
    (fun q => α q.val (P s0 α β xy.1 xy.2 q.val) xy.1,
     fun q => P s0 α β xy.1 xy.2 (q.val + 1))
  let Ac : T → X → Prop := fun t x => ∀ q : Fin p, t.1 q = α q.val (prev s0 t q.val) x
  let Bc : T → Y → Prop := fun t y => ∀ q : Fin (p - 1), t.2 q = β q.val (t.1 ⟨q.val, by omega⟩) y
  have hiff : ∀ x y t, tau (x, y) = t ↔ (Ac t x ∧ Bc t y) := by
    intro x y t
    constructor
    · rintro rfl
      refine ⟨?_, ?_⟩
      · intro q
        simp only [tau]
        congr 1
        unfold prev
        by_cases h0 : q.val = 0
        · simp [h0, P]
        · have h1 : q.val - 1 < p - 1 := by omega
          simp only [h0, h1, dite_false, dite_true]
          congr 1
          omega
      · intro q
        simp only [tau, P]
    · rintro ⟨ha, hb⟩
      have key : ∀ q : ℕ, (hq : q < p) → t.1 ⟨q, hq⟩ = α q (P s0 α β x y q) x ∧
          (∀ hq' : q < p - 1, t.2 ⟨q, hq'⟩ = P s0 α β x y (q + 1)) := by
        intro q
        induction q with
        | zero =>
          intro hq
          have e1 : t.1 ⟨0, hq⟩ = α 0 (P s0 α β x y 0) x := by
            rw [ha ⟨0, hq⟩]; simp [prev, P]
          refine ⟨e1, ?_⟩
          intro hq'
          rw [hb ⟨0, hq'⟩, e1]
          rfl
        | succ q ih =>
          intro hq
          have ih' := (ih (by omega)).2 (by omega)
          have e1 : t.1 ⟨q + 1, hq⟩ = α (q + 1) (P s0 α β x y (q + 1)) x := by
            rw [ha ⟨q + 1, hq⟩]
            have : prev s0 t (q + 1) = t.2 ⟨q, by omega⟩ := by
              simp [prev, show q < p - 1 by omega]
            simp only [this, ih']
          refine ⟨e1, ?_⟩
          intro hq'
          rw [hb ⟨q + 1, hq'⟩, e1]
          rfl
      apply Prod.ext
      · funext q
        exact ((key q.val q.isLt).1).symm
      · funext q
        exact ((key q.val (by omega)).2 q.isLt).symm
  have hPp : ∀ x y, P s0 α β x y p = β (p - 1) (α (p - 1) (P s0 α β x y (p - 1)) x) y := by
    intro x y
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rfl
  let A : T → Finset X := fun t => univ.filter (Ac t)
  let B : T → Finset Y := fun t => univ.filter (Bc t)
  let ε : T → Y → ℤ := fun t y => sgn (g (β (p - 1) (t.1 ⟨p - 1, by omega⟩) y))
  have hfib : ∀ t, (univ : Finset (X × Y)).filter (fun xy => tau xy = t) = A t ×ˢ B t := by
    intro t
    ext ⟨x, y⟩
    simp [A, B, hiff]
  have hsum : ∑ x, ∑ y, wt x y * sgn (g (P s0 α β x y p)) =
      ∑ t : T, ∑ x ∈ A t, ∑ y ∈ B t, wt x y * ε t y := by
    rw [← Fintype.sum_prod_type', ← Finset.sum_fiberwise (univ : Finset (X × Y)) tau]
    apply Finset.sum_congr rfl
    intro t _
    rw [hfib, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    have ht : tau (x, y) = t := (hiff x y t).2 ⟨(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2⟩
    simp only [ε, hPp, ← ht, tau]
  have hcardsum : ∑ t : T, ((A t).card : ℤ) * ((B t).card : ℤ) =
      (Fintype.card X : ℤ) * (Fintype.card Y : ℤ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := tau) (s := (univ : Finset (X × Y)))
      (t := (univ : Finset T)) (by intro _ _; simp)
    simp only [hfib, Finset.card_product, Finset.card_univ, Fintype.card_prod] at this
    rw [← Nat.cast_mul, this]
    push_cast
    rfl
  have hT : (Fintype.card T : ℤ) = (S : ℤ) ^ (2 * p - 1) := by
    simp only [T, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [← pow_add]
    congr 1
    omega
  rw [hsum]
  calc (∑ t : T, ∑ x ∈ A t, ∑ y ∈ B t, wt x y * ε t y) ^ 2
      ≤ (Fintype.card T : ℤ) * ∑ t : T, (∑ x ∈ A t, ∑ y ∈ B t, wt x y * ε t y) ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset T))
          (f := fun t => ∑ x ∈ A t, ∑ y ∈ B t, wt x y * ε t y)
        simpa using this
    _ ≤ (Fintype.card T : ℤ) * ∑ t : T, ((A t).card : ℤ) * ((B t).card : ℤ) * K := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro t _
        exact Lin (A t) (B t) (ε t) (fun y => sgn_sq _)
    _ = (S : ℤ) ^ (2 * p - 1) * (Fintype.card X : ℤ) * (Fintype.card Y : ℤ) * K := by
        rw [← Finset.sum_mul, hcardsum, hT]; ring

theorem drop_ge {n : ℕ} (a : ℕ) (l : List (Fin n)) (hl : l.Pairwise (· < ·)) :
    ∀ i ∈ l.dropWhile (fun i => decide (i.val < a)), a ≤ i.val := by
  induction l with
  | nil => simp
  | cons j l ih =>
    intro i hi
    rw [List.pairwise_cons] at hl
    by_cases hj : j.val < a
    · rw [List.dropWhile_cons_of_pos (by simpa using hj)] at hi
      exact ih hl.2 i hi
    · rw [List.dropWhile_cons_of_neg (by simpa using hj)] at hi
      rcases List.mem_cons.mp hi with h | h
      · subst h; omega
      · have := hl.1 i h
        have : j.val < i.val := this
        omega

theorem foldl_congr' {σ γ : Type} (l : List γ) (f g : σ → γ → σ) (h : ∀ i ∈ l, ∀ s, f s i = g s i) (s : σ) :
    l.foldl f s = l.foldl g s := by
  induction l generalizing s with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [h j (by simp) s]
    exact ih (fun i hi => h i (by simp [hi])) _

theorem list_corr {γ : Type} (l : List γ) (q : γ → Bool) :
    (l.map (fun c => if q c then (1 : ℤ) else -1)).sum = 2 * ((l.filter q).length : ℤ) - l.length := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.filter_cons, List.length_cons]
    cases q j <;> simp <;> ring

theorem sgn_mul (b o : Bool) : sgn b * sgn o = if (o == b) = true then 1 else -1 := by
  cases b <;> cases o <;> simp [sgn]

theorem ip_sgn (M : ℕ) (x y : Fin M → Bool) :
    ipSign M x y = sgn ((univ.filter (fun i : Fin M => x i = true ∧ y i = true)).card.testBit 0) := by
  unfold ipSign sgn
  rw [Nat.testBit_zero]
  rcases Nat.even_or_odd (univ.filter (fun i : Fin M => x i = true ∧ y i = true)).card with h | h
  · rw [h.neg_one_pow]; simp [Nat.even_iff.mp h]
  · rw [h.neg_one_pow]; simp [Nat.odd_iff.mp h]

theorem lower {Pat : Type} [DecidableEq Pat] (a b M p S R u v : ℕ) (hp : 0 < p) (hR : 0 < R) (hv : 0 < v)
    (code : Fin M → (Fin (a + b) → Bool)) (base : Fin (a + b) × Pat → Bool)
    (left right : Fin M → Fin (a + b) × Pat)
    (hcode : Function.Injective code)
    (hlr : ∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val)
    (sols : (Fin (a + b) × Pat → Bool) → Finset (Fin (a + b) → Bool))
    (hsol : ∀ A B : Finset (Fin M), sols (fun slot => base slot || decide (slot ∈ A.image left) ||
      decide (slot ∈ B.image right)) = (A ∩ B).image code)
    (init : Fin R → Fin S) (update : Fin R → Fin p → Fin (a + b) → Fin S → (Pat → Bool) → Fin S)
    (output : Fin R → Fin S → Bool)
    (hyp : ∀ table : Fin (a + b) → Pat → Bool, (v + u) * R ≤ 2 * v * ((List.finRange R).filter (fun coin =>
      output coin ((List.finRange p).foldl (fun prev passId =>
        (List.finRange (a + b)).foldl (fun state site => update coin passId site state (table site)) prev)
          (init coin)) == (sols (fun slot => table slot.1 slot.2)).card.testBit 0)).length) :
    u ^ 2 * 2 ^ M ≤ v ^ 2 * S ^ (2 * p - 1) := by
  let Xs : (Fin M → Bool) → Finset (Fin M) := fun x => univ.filter (fun i => x i = true)
  let T : (Fin M → Bool) → (Fin M → Bool) → Fin (a + b) → Pat → Bool := fun x y i pat =>
    base (i, pat) || decide ((i, pat) ∈ (Xs x).image left) || decide ((i, pat) ∈ (Xs y).image right)
  have hpar : ∀ x y, (sols (fun slot => T x y slot.1 slot.2)).card =
      (univ.filter (fun i : Fin M => x i = true ∧ y i = true)).card := by
    intro x y
    have := hsol (Xs x) (Xs y)
    simp only [T]
    rw [this, Finset.card_image_of_injective _ hcode]
    congr 1
    ext i
    simp [Xs]
  have hT1 : ∀ (i : Fin (a + b)), i.val < a → ∀ x y y', T x y i = T x y' i := by
    intro i hi x y y'
    funext pat
    have h1 : ∀ z, decide ((i, pat) ∈ (Xs z).image right) = false := by
      intro z
      simp only [decide_eq_false_iff_not, Finset.mem_image, not_exists, not_and]
      intro j _ hj
      have := (hlr j).2
      rw [hj] at this
      simp at this; omega
    simp only [T, h1]
  have hT2 : ∀ (i : Fin (a + b)), a ≤ i.val → ∀ x x' y, T x y i = T x' y i := by
    intro i hi x x' y
    funext pat
    have h1 : ∀ z, decide ((i, pat) ∈ (Xs z).image left) = false := by
      intro z
      simp only [decide_eq_false_iff_not, Finset.mem_image, not_exists, not_and]
      intro j _ hj
      have := (hlr j).1
      rw [hj] at this
      simp at this; omega
    simp only [T, h1]
  let takeL := (List.finRange (a + b)).takeWhile (fun i => decide (i.val < a))
  let dropL := (List.finRange (a + b)).dropWhile (fun i => decide (i.val < a))
  let al : Fin R → ℕ → Fin S → (Fin M → Bool) → Fin S := fun c q s x =>
    if h : q < p then takeL.foldl (fun st site => update c ⟨q, h⟩ site st (T x (fun _ => false) site)) s else s
  let be : Fin R → ℕ → Fin S → (Fin M → Bool) → Fin S := fun c q s y =>
    if h : q < p then dropL.foldl (fun st site => update c ⟨q, h⟩ site st (T (fun _ => false) y site)) s else s
  have hrun : ∀ c x y, (List.finRange p).foldl (fun prev passId =>
        (List.finRange (a + b)).foldl (fun state site => update c passId site state (T x y site)) prev)
          (init c) = P (init c) (al c) (be c) x y p := by
    intro c x y
    have hpass : ∀ (q : Fin p) s, (List.finRange (a + b)).foldl
        (fun state site => update c q site state (T x y site)) s = be c q.val (al c q.val s x) y := by
      intro q s
      rw [← List.takeWhile_append_dropWhile (p := fun i : Fin (a + b) => decide (i.val < a))
        (l := List.finRange (a + b)), List.foldl_append]
      simp only [al, be, dif_pos q.isLt, Fin.eta]
      have e1 := foldl_congr' takeL (fun state site => update c q site state (T x y site))
        (fun st site => update c q site st (T x (fun _ => false) site)) (by
          intro i hi s'
          have := List.mem_takeWhile_imp hi
          simp only [decide_eq_true_eq] at this
          rw [hT1 i this x y (fun _ => false)]) s
      have e2 := fun s' => foldl_congr' dropL (fun state site => update c q site state (T x y site))
        (fun st site => update c q site st (T (fun _ => false) y site)) (by
          intro i hi s''
          rw [hT2 i (drop_ge a _ (List.pairwise_lt_finRange _) i hi) x (fun _ => false) y]) s'
      simp only [takeL, dropL] at e1 e2
      rw [e1, e2]
    simp only [hpass]
    have : ∀ k, (List.range k).foldl (fun prev q => be c q (al c q prev x) y) (init c) =
        P (init c) (al c) (be c) x y k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [List.range_succ, List.foldl_append, ih]; rfl
    have hr := this p
    rw [← List.map_coe_finRange_eq_range, List.foldl_map] at hr
    exact hr
  have hcardX : (Fintype.card (Fin M → Bool) : ℤ) = 2 ^ M := by simp
  let C : Fin R → ℤ := fun c => ∑ x : Fin M → Bool, ∑ y : Fin M → Bool,
    ipSign M x y * sgn (output c (P (init c) (al c) (be c) x y p))
  have hC : ∀ c, C c ^ 2 ≤ (S : ℤ) ^ (2 * p - 1) * 2 ^ M * 2 ^ M * 2 ^ M := by
    intro c
    have := proto S p hp (init c) (al c) (be c) (output c) (ipSign M) (2 ^ M)
      (fun A B ε hε => lindsey_w M A B ε hε)
    rw [hcardX] at this
    exact this
  have hcor : ∀ x y, (u : ℤ) * R ≤
      v * ∑ c : Fin R, ipSign M x y * sgn (output c (P (init c) (al c) (be c) x y p)) := by
    intro x y
    have h := hyp (T x y)
    simp only [hrun] at h
    rw [hpar] at h
    rw [ip_sgn]
    simp_rw [sgn_mul]
    rw [Fin.sum_univ_def, list_corr, List.length_finRange]
    have h' : (((v + u) * R : ℕ) : ℤ) ≤ ((2 * v * (List.filter (fun c => output c
        (P (init c) (al c) (be c) x y p) == (univ.filter (fun i : Fin M => x i = true ∧ y i = true)).card.testBit 0)
        (List.finRange R)).length : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hsumC : (u : ℤ) * R * (2 ^ M * 2 ^ M) ≤ v * ∑ c, C c := by
    have e : ∑ c, C c = ∑ x : Fin M → Bool, ∑ y : Fin M → Bool, ∑ c : Fin R,
        ipSign M x y * sgn (output c (P (init c) (al c) (be c) x y p)) := by
      simp only [C]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    rw [e, Finset.mul_sum]
    calc (u : ℤ) * R * (2 ^ M * 2 ^ M) = ∑ x : Fin M → Bool, ∑ y : Fin M → Bool, (u : ℤ) * R := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [← hcardX]; push_cast; ring
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro y _
          exact hcor x y
  have hCS : (∑ c, C c) ^ 2 ≤ (R : ℤ) * ∑ c, C c ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin R))) (f := C)
    simpa using this
  have hCS2 : ∑ c, C c ^ 2 ≤ (R : ℤ) * ((S : ℤ) ^ (2 * p - 1) * 2 ^ M * 2 ^ M * 2 ^ M) := by
    calc ∑ c, C c ^ 2 ≤ ∑ _c : Fin R, ((S : ℤ) ^ (2 * p - 1) * 2 ^ M * 2 ^ M * 2 ^ M) :=
          Finset.sum_le_sum (fun c _ => hC c)
      _ = _ := by simp
  have hpos : 0 ≤ (u : ℤ) * R * (2 ^ M * 2 ^ M) := by positivity
  have big : ((u : ℤ) * R * (2 ^ M * 2 ^ M)) ^ 2 ≤
      (v : ℤ) ^ 2 * (R * (R * ((S : ℤ) ^ (2 * p - 1) * 2 ^ M * 2 ^ M * 2 ^ M))) := by
    calc ((u : ℤ) * R * (2 ^ M * 2 ^ M)) ^ 2 ≤ (v * ∑ c, C c) ^ 2 := pow_le_pow_left₀ hpos hsumC 2
      _ = (v : ℤ) ^ 2 * (∑ c, C c) ^ 2 := by ring
      _ ≤ (v : ℤ) ^ 2 * (R * ∑ c, C c ^ 2) := mul_le_mul_of_nonneg_left hCS (by positivity)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hCS2 (by positivity)
  have hZ : (0 : ℤ) < (R : ℤ) ^ 2 * (2 ^ M) ^ 3 := by
    have : (0 : ℤ) < R := by exact_mod_cast hR
    positivity
  have fin : ((u : ℤ) ^ 2 * 2 ^ M) * ((R : ℤ) ^ 2 * (2 ^ M) ^ 3) ≤
      ((v : ℤ) ^ 2 * (S : ℤ) ^ (2 * p - 1)) * ((R : ℤ) ^ 2 * (2 ^ M) ^ 3) := by
    have e1 : ((u : ℤ) ^ 2 * 2 ^ M) * ((R : ℤ) ^ 2 * (2 ^ M) ^ 3) = ((u : ℤ) * R * (2 ^ M * 2 ^ M)) ^ 2 := by ring
    have e2 : ((v : ℤ) ^ 2 * (S : ℤ) ^ (2 * p - 1)) * ((R : ℤ) ^ 2 * (2 ^ M) ^ 3) =
        (v : ℤ) ^ 2 * (R * (R * ((S : ℤ) ^ (2 * p - 1) * 2 ^ M * 2 ^ M * 2 ^ M))) := by ring
    rw [e1, e2]; exact big
  have := le_of_mul_le_mul_right fin hZ
  exact_mod_cast this

theorem exp_bound (k : ℕ) (hk : 6 ≤ k) : 2 * (2 * k + 5) ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]; omega

theorem arith (a b h : ℕ) (hab : a ≤ b) (hba : b ≤ a + 1) (ha : 16 ≤ a) (hh : h ≤ Nat.clog 2 (2 * b)) :
    Nat.clog 2 (2 * b) + 3 ≤ min a b ∧ 2 * max a b ≤ 2 ^ Nat.clog 2 (2 * b) ∧
    2 ^ (a + b - 13) ≤ (a - h - 1) * 2 ^ (a - Nat.clog 2 (2 * b) - 3) *
      ((b - h - 1) * 2 ^ (b - Nat.clog 2 (2 * b) - 3)) := by
  set t := Nat.clog 2 (2 * b) with ht
  have h2t : 2 * t + 3 ≤ a := by
    have hk := exp_bound ((a - 3) / 2) (by omega)
    have : t ≤ (a - 3) / 2 := Nat.clog_le_of_le_pow (by
      calc 2 * b ≤ 2 * (2 * ((a - 3) / 2) + 5) := by omega
        _ ≤ 2 ^ ((a - 3) / 2) := hk)
    omega
  have hup : 2 * b ≤ 2 ^ t := Nat.le_pow_clog (by norm_num) _
  have ht5 : 5 ≤ t := by
    by_contra hc
    have : 2 ^ t ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlow : 2 ^ t < 4 * b := by
    have := Nat.pow_pred_clog_lt_self 2 (x := 2 * b) (by omega)
    rw [← ht, Nat.pred_eq_sub_one] at this
    have e : 2 ^ t = 2 * 2 ^ (t - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  refine ⟨by rw [min_eq_left hab]; omega, by rw [max_eq_right hab]; exact hup, ?_⟩
  set X := a - t - 1
  set Y := b - t - 1
  have hX : b ≤ 2 * X := by omega
  have hY : b ≤ 2 * Y := by omega
  have hsq : 2 ^ (2 * t - 7) * 128 = 2 ^ t * 2 ^ t := by
    rw [← pow_add, show (128 : ℕ) = 2 ^ 7 by norm_num, ← pow_add]; congr 1; omega
  have hXY : 2 ^ (2 * t - 7) ≤ X * Y := by
    have h1 : 2 ^ t * 2 ^ t < 16 * (b * b) := by nlinarith
    have h2 : 4 * (b * b) ≤ 16 * (X * Y) := by nlinarith
    nlinarith
  have hsplit : 2 ^ (a + b - 13) = 2 ^ (a - t - 3) * 2 ^ (b - t - 3) * 2 ^ (2 * t - 7) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hXh : X ≤ a - h - 1 := by omega
  have hYh : Y ≤ b - h - 1 := by omega
  rw [hsplit]
  calc 2 ^ (a - t - 3) * 2 ^ (b - t - 3) * 2 ^ (2 * t - 7)
      ≤ 2 ^ (a - t - 3) * 2 ^ (b - t - 3) * (X * Y) := Nat.mul_le_mul_left _ hXY
    _ ≤ 2 ^ (a - t - 3) * 2 ^ (b - t - 3) * ((a - h - 1) * (b - h - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hXh hYh)
    _ = (a - h - 1) * 2 ^ (a - t - 3) * ((b - h - 1) * 2 ^ (b - t - 3)) := by ring

end PEqualNP.Outside.L_clb_115

theorem PEqualNP.Outside.L_clb_115 : ∀ (n w p : Nat) (hn : 0 < n), 32 ≤ n → 0 < p →
  n-(w+1) ≤ Nat.clog 2 (2*(n-n/2)) →
  let Pat := Fin (w+1) → Bool
  let Row := Pat → Bool
  let Tab := Fin n → Row
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let total := fun (table : Tab) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      ∀ i : Fin n, table i (fun j => x (loc (i.val+j.val))) = true)).card
  let run := fun (S : Nat) (start : Fin S)
      (step : Fin p → Fin n → Fin S → Row → Fin S) (table : Tab) =>
    (List.finRange p).foldl (fun prev passId =>
      (List.finRange n).foldl (fun state site => step passId site state (table site)) prev) start
  let H := 2^(n-13)
  let bits := 2+(2^n+p-1)/p
  (∃ (start : Fin (2^bits)) (step : Fin p → Fin n → Fin (2^bits) → Row → Fin (2^bits))
      (answer : Fin (2^bits) → Bool × Bool), ∀ table : Tab,
      answer (run (2^bits) start step table) =
        (decide (0 < total table), (total table).testBit 0)) ∧
    ∀ (S R u v : Nat), 0 < R → 0 < v → u ≤ v →
      ∀ (init : Fin R → Fin S) (update : Fin R → Fin p → Fin n → Fin S → Row → Fin S)
        (output : Fin R → Fin S → Bool),
        (∀ table : Tab, (v+u)*R ≤ 2*v*((List.finRange R).filter (fun coin =>
          output coin (run S (init coin) (update coin) table) == (total table).testBit 0)).length) →
        u^2 * 2^H ≤ v^2 * S^(2*p-1) := by
  intro n w p hn h32 hp hcl
  intro Pat Row Tab loc total run H bits
  refine ⟨?_, ?_⟩
  · exact PEqualNP.Outside.L_clb_115.upper (Row := Row) n p hn hp
      (fun (i : Fin n) (r : Row) (x : Fin n → Bool) => r (fun j => x (loc (i.val + j.val))))
  · intro S R u v hR hv _ init update output hyp
    obtain ⟨a, b, rfl, hab, hba, ha, hb⟩ : ∃ a b, a + b = n ∧ a ≤ b ∧ b ≤ a + 1 ∧ 16 ≤ a ∧
        n - n / 2 = b := ⟨n / 2, n - n / 2, by omega, by omega, by omega, by omega, rfl⟩
    rw [hb] at hcl
    obtain ⟨h1, h2, h3⟩ := PEqualNP.Outside.L_clb_115.arith a b (a + b - (w + 1)) hab hba ha hcl
    have L := PEqualNP.Outside.L_clb_115.Lib845.lib845 a b w (Nat.clog 2 (2 * b)) hn hcl h1 h2
    obtain ⟨M, code, base, left, right, hM, hcode, _, _, hlr, hsol⟩ := L
    have key := PEqualNP.Outside.L_clb_115.lower a b M p S R u v hp hR hv code base left right hcode
      (fun i => ⟨(hlr i).1, (hlr i).2.1⟩)
      (fun tab => (Finset.univ : Finset (Fin (a + b) → Bool)).filter (fun x =>
        ∀ i : Fin (a + b), tab (i, fun j => x (loc (i.val + j.val))) = true)) hsol init update output hyp
    have hHM : H ≤ M := le_trans h3 hM
    calc u ^ 2 * 2 ^ H ≤ u ^ 2 * 2 ^ M := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hHM)
      _ ≤ v ^ 2 * S ^ (2 * p - 1) := key

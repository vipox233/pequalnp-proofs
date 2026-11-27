import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_288

def mix (k : ℕ) (x : ZMod k → Bool) (j : ZMod k) : Bool :=
  xor (xor (x (j - 1)) (x j)) (x (j + 1))

def chi (k : ℕ) (z : ZMod k → Bool) (j : ZMod k) : Bool :=
  xor (z j) (!(z (j + 1)) && z (j + 2))

def x0 (k : ℕ) (t : ZMod k) : Bool :=
  decide (if k % 6 = 1 then t.val % 6 < 3 else 2 ≤ t.val % 6 ∧ t.val % 6 ≤ 4)

lemma bool_mix_xor (a1 a2 a3 b1 b2 b3 : Bool)
    (h : xor (xor a1 a2) a3 = xor (xor b1 b2) b3) :
    xor (xor (xor a1 b1) (xor a2 b2)) (xor a3 b3) = false := by
  cases a1 <;> cases a2 <;> cases a3 <;> cases b1 <;> cases b2 <;> cases b3 <;> simp_all

lemma bool_per (a0 a1 a2 a3 : Bool)
    (h1 : xor (xor a0 a1) a2 = false) (h2 : xor (xor a1 a2) a3 = false) :
    a3 = a0 := by
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> simp_all

lemma bool_xor_eq_false (a b : Bool) (h : xor a b = false) : a = b := by
  cases a <;> cases b <;> simp_all

lemma bool_xor_cancel_right (a b k c : Bool)
    (h : xor (xor a k) c = xor (xor b k) c) : a = b := by
  cases a <;> cases b <;> cases k <;> cases c <;> simp_all

lemma bool_xor_cancel_left (k a b : Bool) (h : xor k a = xor k b) : a = b := by
  cases k <;> cases a <;> cases b <;> simp_all

lemma exists_three_mul (k : ℕ) [NeZero k] (hk : k % 6 = 1 ∨ k % 6 = 5) (x : ZMod k) :
    ∃ m : ℕ, (3 : ZMod k) * (m : ZMod k) = x := by
  have hu : ∃ u : ZMod k, (3 : ZMod k) * u = 1 := by
    rcases hk with h1 | h5
    · refine ⟨((4 * (k / 6) + 1 : ℕ) : ZMod k), ?_⟩
      have hnat : 3 * (4 * (k / 6) + 1) = 2 * k + 1 := by omega
      have hcast : ((3 * (4 * (k / 6) + 1) : ℕ) : ZMod k) = ((2 * k + 1 : ℕ) : ZMod k) :=
        congrArg Nat.cast hnat
      push_cast at hcast
      simpa using hcast
    · refine ⟨((2 * (k / 6) + 2 : ℕ) : ZMod k), ?_⟩
      have hnat : 3 * (2 * (k / 6) + 2) = k + 1 := by omega
      have hcast : ((3 * (2 * (k / 6) + 2) : ℕ) : ZMod k) = ((k + 1 : ℕ) : ZMod k) :=
        congrArg Nat.cast hnat
      push_cast at hcast
      simpa using hcast
  obtain ⟨u, h3u⟩ := hu
  refine ⟨(u * x).val, ?_⟩
  rw [ZMod.natCast_zmod_val, ← mul_assoc, h3u, one_mul]

lemma exists_two_mul (k : ℕ) [NeZero k] (hk : k % 6 = 1 ∨ k % 6 = 5) (x : ZMod k) :
    ∃ m : ℕ, (2 : ZMod k) * (m : ZMod k) = x := by
  have h2u : (2 : ZMod k) * (((k + 1) / 2 : ℕ) : ZMod k) = 1 := by
    have hnat : 2 * ((k + 1) / 2) = k + 1 := by omega
    have hcast : ((2 * ((k + 1) / 2) : ℕ) : ZMod k) = ((k + 1 : ℕ) : ZMod k) :=
      congrArg Nat.cast hnat
    push_cast at hcast
    simpa using hcast
  refine ⟨((((k + 1) / 2 : ℕ) : ZMod k) * x).val, ?_⟩
  rw [ZMod.natCast_zmod_val, ← mul_assoc, h2u, one_mul]

lemma mix_injective (k : ℕ) [NeZero k] (hk : k % 6 = 1 ∨ k % 6 = 5) :
    Function.Injective (mix k) := by
  intro x y hxy
  let d : ZMod k → Bool := fun j => xor (x j) (y j)
  have hd_mix : ∀ j : ZMod k, mix k d j = false := by
    intro j
    exact bool_mix_xor _ _ _ _ _ _ (congrFun hxy j)
  have hd_per : ∀ j : ZMod k, d (j + 3) = d j := by
    intro j
    have h1 := hd_mix (j + 1)
    have h2 := hd_mix (j + 2)
    dsimp only [mix] at h1 h2
    have e1 : (j + 1) - 1 = j := by ring
    have e2 : (j + 1) + 1 = j + 2 := by ring
    have e3 : (j + 2) - 1 = j + 1 := by ring
    have e4 : (j + 2) + 1 = j + 3 := by ring
    rw [e1, e2] at h1
    rw [e3, e4] at h2
    exact bool_per _ _ _ _ h1 h2
  have hd_mul : ∀ m : ℕ, d ((3 : ZMod k) * (m : ZMod k)) = d 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (3 : ZMod k) * ((m + 1 : ℕ) : ZMod k) = (3 : ZMod k) * (m : ZMod k) + 3 := by
        push_cast
        ring
      rw [e, hd_per, ih]
  have hd_const : ∀ j : ZMod k, d j = d 0 := by
    intro j
    obtain ⟨m, hm⟩ := exists_three_mul k hk j
    rw [← hm, hd_mul]
  have hd0 : d 0 = false := by
    have h0 := hd_mix 0
    dsimp only [mix] at h0
    rw [hd_const (0 - 1), hd_const (0 + 1)] at h0
    cases h : d 0 <;> simp_all
  funext j
  have hdj : d j = false := by rw [hd_const j, hd0]
  exact bool_xor_eq_false _ _ hdj

lemma chi_step (k : ℕ) (z : ZMod k → Bool) (j : ZMod k) :
    z j = xor (chi k z j) (!(chi k z (j + 1)) && z (j + 2)) := by
  dsimp only [chi]
  have e1 : (j + 1) + 1 = j + 2 := by ring
  have e2 : (j + 1) + 2 = j + 3 := by ring
  rw [e1, e2]
  cases z j <;> cases z (j + 1) <;> cases z (j + 2) <;> cases z (j + 3) <;> rfl

lemma chi_eq_zero_imp (k : ℕ) [NeZero k] (hk : k % 6 = 1 ∨ k % 6 = 5)
    (z : ZMod k → Bool) (hz : ∀ t, chi k z t = false) : ∀ j, z j = false := by
  have hz2 : ∀ j : ZMod k, z (j + 2) = z j := by
    intro j
    have h := chi_step k z j
    rw [hz j, hz (j + 1)] at h
    simpa using h.symm
  have hz_mul : ∀ m : ℕ, z ((2 : ZMod k) * (m : ZMod k)) = z 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (2 : ZMod k) * ((m + 1 : ℕ) : ZMod k) = (2 : ZMod k) * (m : ZMod k) + 2 := by
        push_cast
        ring
      rw [e, hz2, ih]
  have hz_const : ∀ j : ZMod k, z j = z 0 := by
    intro j
    obtain ⟨m, hm⟩ := exists_two_mul k hk j
    rw [← hm, hz_mul]
  have hz0 : z 0 = false := by
    have h0 := hz 0
    dsimp only [chi] at h0
    rw [hz_const (0 + 1), hz_const (0 + 2)] at h0
    cases h : z 0 <;> simp_all
  intro j
  rw [hz_const j, hz0]

lemma chi_injective (k : ℕ) [NeZero k] (hk : k % 6 = 1 ∨ k % 6 = 5) :
    Function.Injective (chi k) := by
  intro z w hzw
  funext j₀
  by_contra hne
  have hstep : ∀ j : ZMod k, z j ≠ w j → chi k z (j + 1) = false ∧ z (j + 2) ≠ w (j + 2) := by
    intro j hj
    have hz := chi_step k z j
    have hw := chi_step k w j
    rw [← hzw] at hw
    cases hc : chi k z (j + 1)
    · refine ⟨rfl, ?_⟩
      intro heq
      rw [hc, heq] at hz
      rw [hc] at hw
      exact hj (hz.trans hw.symm)
    · rw [hc] at hz hw
      simp at hz hw
      exact absurd (hz.trans hw.symm) hj
  have hind : ∀ m : ℕ,
      z (j₀ + (2 : ZMod k) * (m : ZMod k)) ≠ w (j₀ + (2 : ZMod k) * (m : ZMod k)) ∧
      chi k z (j₀ + (2 : ZMod k) * (m : ZMod k) + 1) = false := by
    intro m
    induction m with
    | zero =>
      simp only [Nat.cast_zero, mul_zero, add_zero]
      exact ⟨hne, (hstep j₀ hne).1⟩
    | succ m ih =>
      have e : j₀ + (2 : ZMod k) * ((m + 1 : ℕ) : ZMod k) =
          (j₀ + (2 : ZMod k) * (m : ZMod k)) + 2 := by
        push_cast
        ring
      rw [e]
      have hne' := (hstep _ ih.1).2
      exact ⟨hne', (hstep _ hne').1⟩
  have hcz_zero : ∀ t : ZMod k, chi k z t = false := by
    intro t
    obtain ⟨m, hm⟩ := exists_two_mul k hk (t - j₀ - 1)
    have ht : j₀ + (2 : ZMod k) * (m : ZMod k) + 1 = t := by
      rw [hm]
      ring
    rw [← ht]
    exact (hind m).2
  have hcw_zero : ∀ t : ZMod k, chi k w t = false := by
    intro t
    rw [← hzw]
    exact hcz_zero t
  have hz0 := chi_eq_zero_imp k hk z hcz_zero j₀
  have hw0 := chi_eq_zero_imp k hk w hcw_zero j₀
  exact hne (hz0.trans hw0.symm)

lemma val_add_one_eq (k : ℕ) [NeZero k] (j : ZMod k) :
    (j + 1).val = if j.val + 1 < k then j.val + 1 else 0 := by
  have hkpos : 0 < k := NeZero.pos k
  have hjlt : j.val < k := j.val_lt
  by_cases hlt : j.val + 1 < k
  · simp only [hlt, ite_true]
    have hcast : ((j.val + 1 : ℕ) : ZMod k) = j + 1 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [← hcast, ZMod.val_natCast_of_lt hlt]
  · simp only [hlt, ite_false]
    have heq : j.val + 1 = k := by omega
    have hcast : j + 1 = 0 := by
      have : ((j.val + 1 : ℕ) : ZMod k) = (k : ZMod k) := congrArg Nat.cast heq
      push_cast at this
      rw [ZMod.natCast_zmod_val, ZMod.natCast_self] at this
      exact this
    rw [hcast, ZMod.val_zero]

lemma val_sub_one_eq (k : ℕ) [NeZero k] (j : ZMod k) :
    (j - 1).val = if j.val = 0 then k - 1 else j.val - 1 := by
  have hkpos : 0 < k := NeZero.pos k
  have hjlt : j.val < k := j.val_lt
  by_cases h0 : j.val = 0
  · simp only [h0, ite_true]
    have hj0 : j = 0 := by
      rw [← ZMod.natCast_zmod_val j, h0, Nat.cast_zero]
    have hcast : ((k - 1 : ℕ) : ZMod k) = j - 1 := by
      rw [hj0, zero_sub]
      apply eq_neg_of_add_eq_zero_left
      have h1 : (k - 1) + 1 = k := by omega
      have h2 : (((k - 1) + 1 : ℕ) : ZMod k) = (k : ZMod k) := congrArg Nat.cast h1
      push_cast at h2
      simpa using h2
    rw [← hcast, ZMod.val_natCast_of_lt (by omega)]
  · simp only [h0, ite_false]
    have hcast : ((j.val - 1 : ℕ) : ZMod k) = j - 1 := by
      apply eq_sub_of_add_eq
      have h1 : (j.val - 1) + 1 = j.val := by omega
      have h2 : (((j.val - 1) + 1 : ℕ) : ZMod k) = (j.val : ZMod k) := congrArg Nat.cast h1
      push_cast at h2
      rwa [ZMod.natCast_zmod_val] at h2
    rw [← hcast, ZMod.val_natCast_of_lt (by omega)]

lemma x0_mod6_1 (k : ℕ) (hk : k % 6 = 1) (t : ZMod k) :
    x0 k t = decide (t.val % 6 < 3) := by
  simp [x0, hk]

lemma x0_mod6_5 (k : ℕ) (hk : k % 6 = 5) (t : ZMod k) :
    x0 k t = decide (2 ≤ t.val % 6 ∧ t.val % 6 ≤ 4) := by
  have hne : k % 6 ≠ 1 := by omega
  simp [x0, hne]

lemma mix_x0 (k : ℕ) [NeZero k] (hk : k % 6 = 1 ∨ k % 6 = 5) (j : ZMod k) :
    mix k (x0 k) j = decide (j.val = 0 ∨ j.val % 2 = 1) := by
  have hjlt : j.val < k := j.val_lt
  by_cases hk1 : k = 1
  · subst hk1
    have hj0 : j.val = 0 := by omega
    have hsub : (j - 1).val = 0 := by have := (j - 1).val_lt; omega
    have hadd : (j + 1).val = 0 := by have := (j + 1).val_lt; omega
    dsimp only [mix, x0]
    rw [hj0, hsub, hadd]
    decide
  · have hsub := val_sub_one_eq k j
    have hadd := val_add_one_eq k j
    rcases hk with h1 | h5
    · have hk7 : 7 ≤ k := by omega
      dsimp only [mix]
      rw [x0_mod6_1 k h1, x0_mod6_1 k h1, x0_mod6_1 k h1, hsub, hadd]
      by_cases h0 : j.val = 0
      · have hlt1 : 1 < k := by omega
        have hm1 : (k - 1) % 6 = 0 := by omega
        simp [h0, hlt1, hm1]
      · by_cases hlast : j.val + 1 < k
        · simp only [h0, hlast, ite_false, ite_true]
          have hmod : j.val % 6 < 6 := Nat.mod_lt _ (by omega)
          interval_cases hr : j.val % 6
          · have h1' : (j.val - 1) % 6 = 5 := by omega
            have h2' : (j.val + 1) % 6 = 1 := by omega
            have h3' : j.val % 2 = 0 := by omega
            simp [h1', h2', h0, h3']
          · have h1' : (j.val - 1) % 6 = 0 := by omega
            have h2' : (j.val + 1) % 6 = 2 := by omega
            have h3' : j.val % 2 = 1 := by omega
            simp [h1', h2', h3']
          · have h1' : (j.val - 1) % 6 = 1 := by omega
            have h2' : (j.val + 1) % 6 = 3 := by omega
            have h3' : j.val % 2 = 0 := by omega
            simp [h1', h2', h0, h3']
          · have h1' : (j.val - 1) % 6 = 2 := by omega
            have h2' : (j.val + 1) % 6 = 4 := by omega
            have h3' : j.val % 2 = 1 := by omega
            simp [h1', h2', h3']
          · have h1' : (j.val - 1) % 6 = 3 := by omega
            have h2' : (j.val + 1) % 6 = 5 := by omega
            have h3' : j.val % 2 = 0 := by omega
            simp [h1', h2', h0, h3']
          · have h1' : (j.val - 1) % 6 = 4 := by omega
            have h2' : (j.val + 1) % 6 = 0 := by omega
            have h3' : j.val % 2 = 1 := by omega
            simp [h1', h2', h3']
        · simp only [h0, hlast, ite_false]
          have h1' : (j.val - 1) % 6 = 5 := by omega
          have h2' : j.val % 6 = 0 := by omega
          have h3' : j.val % 2 = 0 := by omega
          simp [h1', h2', h0, h3']
    · have hk5 : 5 ≤ k := by omega
      dsimp only [mix]
      rw [x0_mod6_5 k h5, x0_mod6_5 k h5, x0_mod6_5 k h5, hsub, hadd]
      by_cases h0 : j.val = 0
      · have hlt1 : 1 < k := by omega
        have hm1 : (k - 1) % 6 = 4 := by omega
        simp [h0, hlt1, hm1]
      · by_cases hlast : j.val + 1 < k
        · simp only [h0, hlast, ite_false, ite_true]
          have hmod : j.val % 6 < 6 := Nat.mod_lt _ (by omega)
          interval_cases hr : j.val % 6
          · have h1' : (j.val - 1) % 6 = 5 := by omega
            have h2' : (j.val + 1) % 6 = 1 := by omega
            have h3' : j.val % 2 = 0 := by omega
            simp [h1', h2', h0, h3']
          · have h1' : (j.val - 1) % 6 = 0 := by omega
            have h2' : (j.val + 1) % 6 = 2 := by omega
            have h3' : j.val % 2 = 1 := by omega
            simp [h1', h2', h3']
          · have h1' : (j.val - 1) % 6 = 1 := by omega
            have h2' : (j.val + 1) % 6 = 3 := by omega
            have h3' : j.val % 2 = 0 := by omega
            simp [h1', h2', h0, h3']
          · have h1' : (j.val - 1) % 6 = 2 := by omega
            have h2' : (j.val + 1) % 6 = 4 := by omega
            have h3' : j.val % 2 = 1 := by omega
            simp [h1', h2', h3']
          · have h1' : (j.val - 1) % 6 = 3 := by omega
            have h2' : (j.val + 1) % 6 = 5 := by omega
            have h3' : j.val % 2 = 0 := by omega
            simp [h1', h2', h0, h3']
          · have h1' : (j.val - 1) % 6 = 4 := by omega
            have h2' : (j.val + 1) % 6 = 0 := by omega
            have h3' : j.val % 2 = 1 := by omega
            simp [h1', h2', h3']
        · simp only [h0, hlast, ite_false]
          have h1' : (j.val - 1) % 6 = 3 := by omega
          have h2' : j.val % 6 = 4 := by omega
          have h3' : j.val % 2 = 0 := by omega
          simp [h1', h2', h0, h3']

lemma chi_m0 (k : ℕ) [NeZero k] (hk : k % 2 = 1) (j : ZMod k) :
    chi k (fun t => decide (t.val = 0 ∨ t.val % 2 = 1)) j = decide (j = 0) := by
  have hjlt : j.val < k := j.val_lt
  have hjeq0 : (j = 0) ↔ (j.val = 0) := by
    constructor
    · intro h; subst h; exact ZMod.val_zero
    · intro h; rw [← ZMod.natCast_zmod_val j, h, Nat.cast_zero]
  by_cases hk1 : k = 1
  · subst hk1
    have hj0 : j.val = 0 := by omega
    have h1 : (j + 1).val = 0 := by have := (j + 1).val_lt; omega
    have h2 : (j + 2).val = 0 := by have := (j + 2).val_lt; omega
    dsimp only [chi]
    rw [hj0, h1, h2]
    have : j = 0 := hjeq0.mpr hj0
    subst this
    simp
  · have hk3 : 3 ≤ k := by omega
    have h1 : (j + 1).val = if j.val + 1 < k then j.val + 1 else 0 := val_add_one_eq k j
    have h2 : (j + 2).val = if (j + 1).val + 1 < k then (j + 1).val + 1 else 0 := by
      have : j + 2 = (j + 1) + 1 := by ring
      rw [this]
      exact val_add_one_eq k (j + 1)
    dsimp only [chi]
    by_cases hj0 : j.val = 0
    · have h1' : (j + 1).val = 1 := by
        have hlt1 : 1 < k := by omega
        simp [h1, hj0, hlt1]
      have h2' : (j + 2).val = 2 := by
        have hlt2 : 1 + 1 < k := by omega
        simp [h2, h1', hlt2]
      have hjz : j = 0 := hjeq0.mpr hj0
      rw [hj0, h1', h2', hjz]
      simp
    · have hjne : j ≠ 0 := fun h => hj0 (hjeq0.mp h)
      by_cases hlt2 : j.val + 2 < k
      · have h1' : (j + 1).val = j.val + 1 := by
          have hlt1 : j.val + 1 < k := by omega
          simp [h1, hlt1]
        have h2' : (j + 2).val = j.val + 2 := by
          simp [h2, h1', hlt2]
        rw [h1', h2']
        have hmod : j.val % 2 < 2 := Nat.mod_lt _ (by omega)
        interval_cases hr : j.val % 2
        · have r1 : (j.val + 1) % 2 = 1 := by omega
          have r2 : (j.val + 2) % 2 = 0 := by omega
          have n1 : j.val + 1 ≠ 0 := by omega
          have n2 : j.val + 2 ≠ 0 := by omega
          simp [hj0, hjne, hr, r1, r2, n1, n2]
        · have r1 : (j.val + 1) % 2 = 0 := by omega
          have r2 : (j.val + 2) % 2 = 1 := by omega
          have n1 : j.val + 1 ≠ 0 := by omega
          simp [hj0, hjne, hr, r1, r2, n1]
      · by_cases hlt1 : j.val + 1 < k
        · have h1' : (j + 1).val = j.val + 1 := by simp [h1, hlt1]
          have h2' : (j + 2).val = 0 := by
            have hn2 : ¬ (j.val + 1 + 1 < k) := by omega
            simp [h2, h1', hn2]
          have hr0 : j.val % 2 = 1 := by omega
          have hr1 : (j.val + 1) % 2 = 0 := by omega
          have n1 : j.val + 1 ≠ 0 := by omega
          rw [h1', h2']
          simp [hj0, hjne, hr0, hr1, n1]
        · have h1' : (j + 1).val = 0 := by simp [h1, hlt1]
          have h2' : (j + 2).val = 1 := by
            have h0lt : 0 + 1 < k := by omega
            simp [h2, h1', h0lt]
          have hr0 : j.val % 2 = 0 := by omega
          rw [h1', h2']
          simp [hj0, hjne, hr0]

lemma filter_range_succ (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range (n + 1)).filter P).card =
      ((Finset.range n).filter P).card + if P n then 1 else 0 := by
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · omega

lemma card_range_mod6_lt3 : ∀ q : ℕ,
    ((Finset.range (6 * q + 1)).filter (fun r => r % 6 < 3)).card = 3 * q + 1
  | 0 => by decide
  | q + 1 => by
    have ih := card_range_mod6_lt3 q
    have h6 : 6 * (q + 1) + 1 = ((((((6 * q + 1) + 1) + 1) + 1) + 1) + 1) + 1 := by omega
    rw [h6, filter_range_succ, filter_range_succ, filter_range_succ,
      filter_range_succ, filter_range_succ, filter_range_succ, ih]
    have r1 : (6 * q + 1) % 6 < 3 := by omega
    have r2 : (6 * q + 1 + 1) % 6 < 3 := by omega
    have r3 : ¬ (6 * q + 1 + 1 + 1) % 6 < 3 := by omega
    have r4 : ¬ (6 * q + 1 + 1 + 1 + 1) % 6 < 3 := by omega
    have r5 : ¬ (6 * q + 1 + 1 + 1 + 1 + 1) % 6 < 3 := by omega
    have r6 : (6 * q + 1 + 1 + 1 + 1 + 1 + 1) % 6 < 3 := by omega
    simp only [r1, r2, r3, r4, r5, r6, ite_true, ite_false]
    omega

lemma card_range_mod6_mid : ∀ q : ℕ,
    ((Finset.range (6 * q + 5)).filter (fun r => 2 ≤ r % 6 ∧ r % 6 ≤ 4)).card = 3 * q + 3
  | 0 => by decide
  | q + 1 => by
    have ih := card_range_mod6_mid q
    have h6 : 6 * (q + 1) + 5 = ((((((6 * q + 5) + 1) + 1) + 1) + 1) + 1) + 1 := by omega
    rw [h6, filter_range_succ, filter_range_succ, filter_range_succ,
      filter_range_succ, filter_range_succ, filter_range_succ, ih]
    have r1 : ¬ (2 ≤ (6 * q + 5) % 6 ∧ (6 * q + 5) % 6 ≤ 4) := by omega
    have r2 : ¬ (2 ≤ (6 * q + 5 + 1) % 6 ∧ (6 * q + 5 + 1) % 6 ≤ 4) := by omega
    have r3 : ¬ (2 ≤ (6 * q + 5 + 1 + 1) % 6 ∧ (6 * q + 5 + 1 + 1) % 6 ≤ 4) := by omega
    have r4 : 2 ≤ (6 * q + 5 + 1 + 1 + 1) % 6 ∧ (6 * q + 5 + 1 + 1 + 1) % 6 ≤ 4 := by omega
    have r5 : 2 ≤ (6 * q + 5 + 1 + 1 + 1 + 1) % 6 ∧ (6 * q + 5 + 1 + 1 + 1 + 1) % 6 ≤ 4 := by omega
    have r6 : 2 ≤ (6 * q + 5 + 1 + 1 + 1 + 1 + 1) % 6 ∧ (6 * q + 5 + 1 + 1 + 1 + 1 + 1) % 6 ≤ 4 := by omega
    simp [r1, r2, r3, r4, r5, r6]
    omega

lemma card_x0 (k : ℕ) [NeZero k] (hk : k % 6 = 1 ∨ k % 6 = 5) :
    (Finset.univ.filter (fun t : ZMod k => x0 k t = true)).card = (k + 1) / 2 := by
  let P : ℕ → Prop := fun r => if k % 6 = 1 then r % 6 < 3 else 2 ≤ r % 6 ∧ r % 6 ≤ 4
  have hcard_bij : (Finset.univ.filter (fun t : ZMod k => x0 k t = true)).card =
      ((Finset.range k).filter (fun r => P r)).card := by
    apply Finset.card_bij (fun t _ => t.val)
    · intro t ht
      rw [Finset.mem_filter] at ht ⊢
      refine ⟨Finset.mem_range.mpr t.val_lt, ?_⟩
      simpa [x0, P] using ht.2
    · intro t₁ _ t₂ _ h
      exact ZMod.val_injective k h
    · intro r hr
      rw [Finset.mem_filter, Finset.mem_range] at hr
      refine ⟨(r : ZMod k), ?_, ZMod.val_natCast_of_lt hr.1⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [x0, P, ZMod.val_natCast_of_lt hr.1] using hr.2
  rw [hcard_bij]
  rcases hk with h1 | h5
  · have hP : (Finset.range k).filter (fun r => P r) =
        (Finset.range (6 * (k / 6) + 1)).filter (fun r => r % 6 < 3) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, P, h1, ite_true]
      omega
    rw [hP, card_range_mod6_lt3]
    omega
  · have hne : k % 6 ≠ 1 := by omega
    have hP : (Finset.range k).filter (fun r => P r) =
        (Finset.range (6 * (k / 6) + 5)).filter (fun r => 2 ≤ r % 6 ∧ r % 6 ≤ 4) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, P, hne, ite_false]
      omega
    rw [hP, card_range_mod6_mid]
    omega

end PEqualNP.Outside.L_pcx_288

theorem PEqualNP.Outside.L_pcx_288 : (∀ (k : ℕ) [NeZero k], (k % 6 = 1 ∨ k % 6 = 5) →
  let I := ZMod k
  let Word := I → Bool
  let mix := fun (x : Word) (j : I) => xor (xor (x (j-1)) (x j)) (x (j+1))
  let chi := fun (z : Word) (j : I) => xor (z j) (!(z (j+1)) && z (j+2))
  let c : Word := fun j => (3^(k+1) % 2^k).testBit j.val
  let row := fun (key name : Word) (j : I) =>
    xor (xor (chi (mix (fun i => xor (key (i-1)) (name i))) j) (key j)) (c j)
  let zero : Word := fun _ => false
  let pulse := fun (s : I) (j : I) => decide (j = s)
  let mask := fun (i s : I) =>
    let u := (i-s).val % 6
    decide (if k % 6 = 1 then u < 3 else 2 ≤ u ∧ u ≤ 4)
  ∃ dec : Word → Word → Word,
    (∀ key name out, row key name = out ↔ dec key out = name) ∧ dec zero c = zero ∧
    ∀ i : I,
      (∀ s : I, dec zero (fun j => xor (c j) (pulse s j)) i = mask i s ∧
        dec (pulse s) c i = xor (mask i s) (pulse s (i-1))) ∧
      (Finset.univ.filter (fun s : I => mask i s = true)).card = (k+1)/2 ∧
      (Finset.univ.filter (fun s : I => xor (mask i s) (pulse s (i-1)) = true)).card =
        (if k % 6 = 1 then (k-1)/2 else (k+3)/2)) := by
  intro k _ hk I Word mix chi c row zero pulse mask
  have hmix_inj : Function.Injective mix := PEqualNP.Outside.L_pcx_288.mix_injective k hk
  have hchi_inj : Function.Injective chi := PEqualNP.Outside.L_pcx_288.chi_injective k hk
  have hrow_bij : ∀ key : Word, Function.Bijective (row key) := by
    intro key
    apply Finite.injective_iff_bijective.mp
    intro n₁ n₂ h
    have h1 : chi (mix (fun i => xor (key (i - 1)) (n₁ i))) =
        chi (mix (fun i => xor (key (i - 1)) (n₂ i))) := by
      funext j
      exact PEqualNP.Outside.L_pcx_288.bool_xor_cancel_right _ _ _ _ (congrFun h j)
    have h2 := hmix_inj (hchi_inj h1)
    funext i
    exact PEqualNP.Outside.L_pcx_288.bool_xor_cancel_left _ _ _ (congrFun h2 i)
  let dec : Word → Word → Word := fun key out => (Equiv.ofBijective (row key) (hrow_bij key)).symm out
  have hdec : ∀ key name out, row key name = out ↔ dec key out = name := by
    intro key name out
    exact ((Equiv.ofBijective (row key) (hrow_bij key)).symm_apply_eq.trans eq_comm).symm
  have hchi_mix_x0 : ∀ s : I, chi (mix (fun i => mask i s)) = pulse s := by
    intro s
    have hmix_s : mix (fun i => mask i s) =
        fun j => PEqualNP.Outside.L_pcx_288.mix k (PEqualNP.Outside.L_pcx_288.x0 k) (j - s) := by
      funext j
      dsimp only [mix, mask, PEqualNP.Outside.L_pcx_288.mix, PEqualNP.Outside.L_pcx_288.x0]
      have e1 : j - 1 - s = (j - s) - 1 := by ring
      have e2 : j + 1 - s = (j - s) + 1 := by ring
      rw [e1, e2]
    funext j
    rw [hmix_s]
    have hchi_s : chi (fun j => PEqualNP.Outside.L_pcx_288.mix k (PEqualNP.Outside.L_pcx_288.x0 k) (j - s)) j =
        PEqualNP.Outside.L_pcx_288.chi k
          (fun t => decide (t.val = 0 ∨ t.val % 2 = 1)) (j - s) := by
      dsimp only [chi, PEqualNP.Outside.L_pcx_288.chi]
      have e1 : j + 1 - s = (j - s) + 1 := by ring
      have e2 : j + 2 - s = (j - s) + 2 := by ring
      rw [e1, e2, PEqualNP.Outside.L_pcx_288.mix_x0 k hk,
        PEqualNP.Outside.L_pcx_288.mix_x0 k hk, PEqualNP.Outside.L_pcx_288.mix_x0 k hk]
    rw [hchi_s, PEqualNP.Outside.L_pcx_288.chi_m0 k (by omega)]
    dsimp only [pulse]
    have hs : j - s = 0 ↔ j = s := sub_eq_zero
    simp [hs]
  refine ⟨dec, hdec, ?_, ?_⟩
  · rw [← hdec]
    funext j
    simp [row, chi, mix, zero]
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · intro s
      constructor
      · have hfull : dec zero (fun j => xor (c j) (pulse s j)) = fun i => mask i s := by
          rw [← hdec]
          funext j
          dsimp only [row, zero]
          have h1 : (fun i => xor false (mask i s)) = fun i => mask i s := by
            funext t; simp
          rw [h1, hchi_mix_x0 s]
          cases c j <;> cases pulse s j <;> rfl
        exact congrFun hfull i
      · have hfull : dec (pulse s) c = fun i => xor (mask i s) (pulse s (i - 1)) := by
          rw [← hdec]
          funext j
          dsimp only [row]
          have h1 : (fun t => xor (pulse s (t - 1)) (xor (mask t s) (pulse s (t - 1)))) =
              fun t => mask t s := by
            funext t
            cases pulse s (t - 1) <;> cases mask t s <;> rfl
          rw [h1, hchi_mix_x0 s]
          cases pulse s j <;> cases c j <;> rfl
        exact congrFun hfull i
    · have hbij : (Finset.univ.filter (fun s : I => mask i s = true)).card =
          (Finset.univ.filter (fun t : ZMod k => PEqualNP.Outside.L_pcx_288.x0 k t = true)).card := by
        apply Finset.card_bij (fun s _ => i - s)
        · intro s hs
          rw [Finset.mem_filter] at hs ⊢
          exact ⟨Finset.mem_univ _, hs.2⟩
        · intro s₁ _ s₂ _ h
          exact sub_right_injective h
        · intro t ht
          rw [Finset.mem_filter] at ht
          refine ⟨i - t, ?_, by ring⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have e : i - (i - t) = t := by ring
          simpa [mask, PEqualNP.Outside.L_pcx_288.x0, e] using ht.2
      rw [hbij, PEqualNP.Outside.L_pcx_288.card_x0 k hk]
    · set A : Finset (ZMod k) :=
        Finset.univ.filter (fun t : ZMod k => PEqualNP.Outside.L_pcx_288.x0 k t = true)
      have hAcard : A.card = (k + 1) / 2 := PEqualNP.Outside.L_pcx_288.card_x0 k hk
      have hbij : (Finset.univ.filter (fun s : I => xor (mask i s) (pulse s (i - 1)) = true)).card =
          (Finset.univ.filter (fun t : ZMod k =>
            xor (PEqualNP.Outside.L_pcx_288.x0 k t) (decide (t = 1)) = true)).card := by
        apply Finset.card_bij (fun s _ => i - s)
        · intro s hs
          rw [Finset.mem_filter] at hs ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          have hp : pulse s (i - 1) = decide (i - s = 1) := by
            dsimp only [pulse]
            have : (i - 1 = s) ↔ (i - s = 1) := by
              constructor <;> intro h <;> linear_combination h
            simp [this]
          rw [← hp]
          exact hs.2
        · intro s₁ _ s₂ _ h
          exact sub_right_injective h
        · intro t ht
          rw [Finset.mem_filter] at ht
          refine ⟨i - t, ?_, by ring⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have e : i - (i - t) = t := by ring
          have hp : pulse (i - t) (i - 1) = decide (t = 1) := by
            dsimp only [pulse]
            have : (i - 1 = i - t) ↔ (t = 1) := by
              constructor <;> intro h <;> linear_combination h
            simp [this]
          rw [hp]
          simpa [mask, PEqualNP.Outside.L_pcx_288.x0, e] using ht.2
      rw [hbij]
      rcases hk with h1 | h5
      · simp only [h1, ite_true]
        have hx1 : PEqualNP.Outside.L_pcx_288.x0 k 1 = true := by
          rw [PEqualNP.Outside.L_pcx_288.x0_mod6_1 k h1]
          by_cases hk1 : k = 1
          · subst hk1; decide
          · have h1val : (1 : ZMod k).val = 1 := ZMod.val_one'' (by omega)
            rw [h1val]
            decide
        have h1A : (1 : ZMod k) ∈ A := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hx1⟩
        have heq : Finset.univ.filter (fun t : ZMod k =>
            xor (PEqualNP.Outside.L_pcx_288.x0 k t) (decide (t = 1)) = true) = A.erase 1 := by
          ext t
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          by_cases ht1 : t = 1
          · subst ht1; simp [hx1]
          · simp [ht1]
        rw [heq, Finset.card_erase_of_mem h1A, hAcard]
        omega
      · have hne : k % 6 ≠ 1 := by omega
        simp only [hne, ite_false]
        have hx1 : PEqualNP.Outside.L_pcx_288.x0 k 1 = false := by
          rw [PEqualNP.Outside.L_pcx_288.x0_mod6_5 k h5]
          have h1val : (1 : ZMod k).val = 1 := ZMod.val_one'' (by omega)
          rw [h1val]
          decide
        have h1notA : (1 : ZMod k) ∉ A := by
          rw [Finset.mem_filter]
          simp [hx1]
        have heq : Finset.univ.filter (fun t : ZMod k =>
            xor (PEqualNP.Outside.L_pcx_288.x0 k t) (decide (t = 1)) = true) = insert 1 A := by
          ext t
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          by_cases ht1 : t = 1
          · subst ht1; simp [hx1]
          · simp [ht1]
        rw [heq, Finset.card_insert_of_notMem h1notA, hAcard]
        omega

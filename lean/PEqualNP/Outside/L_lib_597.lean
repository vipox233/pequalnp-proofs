import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_597_aux

def walk {V G : Type*} (E : V → V → G → Prop) (m : ℕ) (v : ℕ → V) (s : ℕ → G) : Prop :=
  ∀ i < m, E (v i) (v (i + 1)) (s i)

def gain {G : Type*} [Group G] (m : ℕ) (s : ℕ → G) : G :=
  ((List.range m).map s).prod

lemma gain_zero {G : Type*} [Group G] (s : ℕ → G) : gain 0 s = 1 := by
  simp [gain]

lemma gain_succ {G : Type*} [Group G] (m : ℕ) (s : ℕ → G) :
    gain (m + 1) s = gain m s * s m := by
  simp [gain, List.range_succ, List.map_append, List.prod_append]

lemma gain_one {G : Type*} [Group G] (s : ℕ → G) : gain 1 s = s 0 := by
  simp [gain]

lemma gain_congr {G : Type*} [Group G] (m : ℕ) (s1 s2 : ℕ → G)
    (h : ∀ i < m, s1 i = s2 i) : gain m s1 = gain m s2 := by
  induction m with
  | zero => simp [gain]
  | succ m ih =>
    rw [gain_succ, gain_succ, ih (fun i hi => h i (by omega)), h m (by omega)]

lemma gain_add {G : Type*} [Group G] (a b : ℕ) (s : ℕ → G) :
    gain (a + b) s = gain a s * gain b (fun i => s (a + i)) := by
  induction b with
  | zero =>
    simp [gain_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, gain_succ, ih, gain_succ, mul_assoc]

lemma walk_subwalk {V G : Type*} {E : V → V → G → Prop} {m : ℕ} {v : ℕ → V} {s : ℕ → G}
    (hw : walk E m v s) (a b : ℕ) (hab : a ≤ b) (hbm : b ≤ m) :
    walk E (b - a) (fun i => v (a + i)) (fun i => s (a + i)) := by
  intro i hi
  dsimp only
  have h1 : a + i < m := by omega
  have h2 : a + (i + 1) = a + i + 1 := by omega
  rw [h2]
  exact hw (a + i) h1

lemma walk_concat {V G : Type*} [Group G] {E : V → V → G → Prop}
    {m1 m2 : ℕ} {v1 v2 : ℕ → V} {s1 s2 : ℕ → G}
    (hw1 : walk E m1 v1 s1) (hw2 : walk E m2 v2 s2) (hmid : v1 m1 = v2 0) :
    ∃ (v : ℕ → V) (s : ℕ → G),
      walk E (m1 + m2) v s ∧ v 0 = v1 0 ∧ v (m1 + m2) = v2 m2 ∧
      gain (m1 + m2) s = gain m1 s1 * gain m2 s2 := by
  let v : ℕ → V := fun i => if i < m1 then v1 i else v2 (i - m1)
  let s : ℕ → G := fun i => if i < m1 then s1 i else s2 (i - m1)
  refine ⟨v, s, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hlt : i + 1 < m1
    · have hi1 : i < m1 := by omega
      simp only [v, s, hi1, hlt, ↓reduceIte]
      exact hw1 i hi1
    · by_cases heq : i + 1 = m1
      · have hi1 : i < m1 := by omega
        have hnot : ¬ (i + 1 < m1) := by omega
        have hsub : i + 1 - m1 = 0 := by omega
        simp only [v, s, hi1, hnot, hsub, ↓reduceIte]
        rw [← hmid, ← heq]
        exact hw1 i hi1
      · have hi_ge : ¬ (i < m1) := by omega
        have hnot : ¬ (i + 1 < m1) := by omega
        have hsub : i + 1 - m1 = (i - m1) + 1 := by omega
        simp only [v, s, hi_ge, hnot, hsub, ↓reduceIte]
        exact hw2 (i - m1) (by omega)
  · by_cases h0 : 0 < m1
    · simp only [v, h0, ↓reduceIte]
    · have hm0 : m1 = 0 := by omega
      subst hm0
      simp only [v, lt_self_iff_false, ↓reduceIte, Nat.sub_zero, ← hmid]
  · simp only [v, show ¬ (m1 + m2 < m1) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  · rw [gain_add]
    have hg1 : gain m1 s = gain m1 s1 := gain_congr m1 s s1 fun i hi => by
      simp only [s, hi, ↓reduceIte]
    have hg2 : gain m2 (fun i => s (m1 + i)) = gain m2 s2 :=
      gain_congr m2 _ s2 fun i _ => by
        simp only [s, show ¬ (m1 + i < m1) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [hg1, hg2]

lemma walk_rev {V G : Type*} [Group G] {E : V → V → G → Prop}
    (hsym : ∀ u v g, E u v g → E v u g⁻¹)
    {m : ℕ} {v : ℕ → V} {s : ℕ → G} (hw : walk E m v s) :
    ∃ (vr : ℕ → V) (sr : ℕ → G),
      walk E m vr sr ∧ vr 0 = v m ∧ vr m = v 0 ∧ gain m sr = (gain m s)⁻¹ := by
  let vr : ℕ → V := fun i => v (m - i)
  let sr : ℕ → G := fun i => (s (m - 1 - i))⁻¹
  refine ⟨vr, sr, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [vr, sr]
    have hidx : m - 1 - i < m := by omega
    have hsucc : m - 1 - i + 1 = m - i := by omega
    have hsub : m - (i + 1) = m - 1 - i := by omega
    rw [hsub]
    have he := hw (m - 1 - i) hidx
    rw [hsucc] at he
    exact hsym _ _ _ he
  · simp [vr]
  · simp [vr]
  · have hrev_aux : ∀ k : ℕ, k ≤ m →
        gain k sr = (gain k (fun i => s (m - k + i)))⁻¹ := by
      intro k
      induction k with
      | zero =>
        intro _
        simp [gain_zero]
      | succ k ih =>
        intro hk
        rw [gain_succ, ih (by omega)]
        have hsplit : gain (k + 1) (fun i => s (m - (k + 1) + i)) =
            s (m - 1 - k) * gain k (fun i => s (m - k + i)) := by
          have h1 := gain_add 1 k (fun i => s (m - (k + 1) + i))
          rw [show 1 + k = k + 1 by omega] at h1
          rw [h1, gain_one]
          have hfirst : s (m - (k + 1) + 0) = s (m - 1 - k) := by congr 1; omega
          have hrest : gain k (fun i => s (m - (k + 1) + (1 + i))) =
              gain k (fun i => s (m - k + i)) := by
            refine gain_congr k _ _ fun i hi => ?_
            congr 1; omega
          rw [hfirst, hrest]
        rw [hsplit, mul_inv_rev]
    have hfull := hrev_aux m le_rfl
    rw [hfull]
    congr 1
    refine gain_congr m _ _ fun i _ => ?_
    simp

lemma walk_single {V G : Type*} [Group G] {E : V → V → G → Prop}
    {u w : V} {g : G} (he : E u w g) :
    ∃ (v : ℕ → V) (s : ℕ → G), walk E 1 v s ∧ v 0 = u ∧ v 1 = w ∧ gain 1 s = g := by
  refine ⟨fun i => if i = 0 then u else w, fun _ => g, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simpa using he
  · simp
  · simp
  · simp [gain_one]

lemma walk_nil {V G : Type*} [Group G] (E : V → V → G → Prop) (u : V) :
    ∃ (v : ℕ → V) (s : ℕ → G), walk E 0 v s ∧ v 0 = u ∧ v 0 = u ∧ gain 0 s = 1 :=
  ⟨fun _ => u, fun _ => 1, fun _ hi => absurd hi (Nat.not_lt_zero _), rfl, rfl, gain_zero _⟩

lemma walk_rotate {V G : Type*} [Group G] {E : V → V → G → Prop}
    {m : ℕ} {v : ℕ → V} {s : ℕ → G} (hw : walk E m v s) (hclosed : v 0 = v m)
    (i0 : ℕ) (hi0 : i0 < m) :
    ∃ (v' : ℕ → V) (s' : ℕ → G),
      walk E m v' s' ∧
      (∀ j ≤ m, v' j = v ((i0 + j) % m)) ∧
      v' 0 = v i0 ∧ v' m = v i0 ∧
      (gain m s' = 1 ↔ gain m s = 1) := by
  let v1 := fun j => v (i0 + j)
  let s1 := fun j => s (i0 + j)
  have hw1 : walk E (m - i0) v1 s1 := walk_subwalk hw i0 m (by omega) le_rfl
  have hw2 : walk E i0 v s := by
    intro j hj; exact hw j (by omega)
  have hmid : v1 (m - i0) = v 0 := by
    simp only [v1, show i0 + (m - i0) = m by omega, hclosed]
  let v' : ℕ → V := fun j => if j < m - i0 then v1 j else v (j - (m - i0))
  let s' : ℕ → G := fun j => if j < m - i0 then s1 j else s (j - (m - i0))
  have hm_eq : (m - i0) + i0 = m := by omega
  have hw' : walk E m v' s' := by
    intro j hj
    by_cases hlt : j + 1 < m - i0
    · have hj1 : j < m - i0 := by omega
      simp only [v', s', hj1, hlt, ↓reduceIte]
      exact hw1 j hj1
    · by_cases heq : j + 1 = m - i0
      · have hj1 : j < m - i0 := by omega
        have hnot : ¬ (j + 1 < m - i0) := by omega
        have hsub : j + 1 - (m - i0) = 0 := by omega
        simp only [v', s', hj1, hnot, hsub, ↓reduceIte]
        rw [← hmid, ← heq]
        exact hw1 j hj1
      · have hj_ge : ¬ (j < m - i0) := by omega
        have hnot : ¬ (j + 1 < m - i0) := by omega
        have hsub : j + 1 - (m - i0) = (j - (m - i0)) + 1 := by omega
        simp only [v', s', hj_ge, hnot, hsub, ↓reduceIte]
        exact hw2 (j - (m - i0)) (by omega)
  have hv'_mod : ∀ j ≤ m, v' j = v ((i0 + j) % m) := by
    intro j hj
    by_cases hlt : j < m - i0
    · simp only [v', v1, hlt, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega)]
    · simp only [v', hlt, ↓reduceIte]
      by_cases hjm : j = m
      · subst j
        have hsub : m - (m - i0) = i0 := by omega
        rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt hi0]
      · have hmod : (i0 + j) % m = j - (m - i0) := by
          have hadd : i0 + j = (j - (m - i0)) + m := by omega
          rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
  have hv'0 : v' 0 = v i0 := by
    rw [hv'_mod 0 (by omega), Nat.add_zero, Nat.mod_eq_of_lt hi0]
  have hv'm : v' m = v i0 := by
    rw [hv'_mod m le_rfl, Nat.add_mod_right, Nat.mod_eq_of_lt hi0]
  have hgain_orig : gain m s = gain i0 s * gain (m - i0) s1 := by
    have h1 := gain_add i0 (m - i0) s
    rw [show i0 + (m - i0) = m by omega] at h1
    exact h1
  have hgain_rot : gain m s' = gain (m - i0) s1 * gain i0 s := by
    have h1 := gain_add (m - i0) i0 s'
    rw [hm_eq] at h1
    rw [h1]
    have hg1 : gain (m - i0) s' = gain (m - i0) s1 :=
      gain_congr (m - i0) s' s1 fun j hj => by simp only [s', hj, ↓reduceIte]
    have hg2 : gain i0 (fun j => s' (m - i0 + j)) = gain i0 s :=
      gain_congr i0 _ s fun j _ => by
        simp only [s', show ¬ (m - i0 + j < m - i0) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [hg1, hg2]
  have hiff : gain m s' = 1 ↔ gain m s = 1 := by
    rw [hgain_rot, hgain_orig]
    constructor
    · intro h
      have hinv : gain (m - i0) s1 = (gain i0 s)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [hinv, mul_inv_cancel]
    · intro h
      have hinv : gain i0 s = (gain (m - i0) s1)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [hinv, mul_inv_cancel]
  exact ⟨v', s', hw', hv'_mod, hv'0, hv'm, hiff⟩

lemma short_chain_concat {V G : Type*} [Group G] {E : V → V → G → Prop}
    (R : ℕ) (k : ℕ) (P : ℕ → V) (g : ℕ → G)
    (hstep : ∀ i < k, ∃ m ≤ R, ∃ (v : ℕ → V) (s : ℕ → G),
      walk E m v s ∧ v 0 = P i ∧ v m = P (i + 1) ∧ gain m s = g i) :
    ∃ m ≤ k * R, ∃ (v : ℕ → V) (s : ℕ → G),
      walk E m v s ∧ v 0 = P 0 ∧ v m = P k ∧ gain m s = gain k g := by
  induction k with
  | zero =>
    refine ⟨0, by simp, fun _ => P 0, fun _ => 1, fun _ hi => absurd hi (Nat.not_lt_zero _),
      rfl, rfl, ?_⟩
    simp [gain_zero]
  | succ k ih =>
    rcases ih (fun i hi => hstep i (by omega)) with ⟨m1, hm1, v1, s1, hw1, hv10, hv1m, hg1⟩
    rcases hstep k (by omega) with ⟨m2, hm2, v2, s2, hw2, hv20, hv2m, hg2⟩
    rcases walk_concat hw1 hw2 (hv1m.trans hv20.symm) with ⟨v, s, hw, hv0, hvm, hgs⟩
    refine ⟨m1 + m2, ?_, v, s, hw, hv0.trans hv10, hvm.trans hv2m, ?_⟩
    · rw [Nat.succ_mul]; omega
    · rw [hgs, hg1, hg2, gain_succ]

lemma pins_chain_eval {V G : Type*} [Group G] {E : V → V → G → Prop}
    (R : ℕ) (T : Finset V) (y : V → G)
    (hT : ∀ m ≤ R, ∀ v s, walk E m v s → v 0 ∈ T → v m ∈ T → y (v m) = y (v 0) * gain m s)
    {m : ℕ} {v : ℕ → V} {s : ℕ → G} (hw : walk E m v s)
    (k : ℕ) (t : ℕ → ℕ) (ht0 : t 0 = 0) (ht_mono : ∀ j < k, t j ≤ t (j + 1))
    (ht_step : ∀ j < k, t (j + 1) - t j ≤ R) (ht_le : ∀ j ≤ k, t j ≤ m)
    (ht_mem : ∀ j ≤ k, v (t j) ∈ T) :
    ∀ j ≤ k, y (v (t j)) = y (v 0) * gain (t j) s := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [ht0, gain_zero, mul_one]
  | succ j ih =>
    intro hj
    have hprev := ih (by omega)
    have hle : t j ≤ t (j + 1) := ht_mono j (by omega)
    have hsub := walk_subwalk hw (t j) (t (j + 1)) hle (ht_le (j + 1) hj)
    have hstep_eq := hT (t (j + 1) - t j) (ht_step j (by omega))
      (fun i => v (t j + i)) (fun i => s (t j + i)) hsub
      (by simpa using ht_mem j (by omega))
      (by simpa [Nat.add_sub_of_le hle] using ht_mem (j + 1) hj)
    simp only [Nat.add_zero, Nat.add_sub_of_le hle] at hstep_eq
    rw [hstep_eq, hprev, mul_assoc, ← gain_add, Nat.add_sub_of_le hle]

end PEqualNP.Outside.L_lib_597_aux

open PEqualNP.Outside.L_lib_597_aux in
theorem PEqualNP.Outside.L_lib_597 :
    ∀ (n : ℕ) (G : Type) [Group G] [DecidableEq G]
  (E : Fin n → Fin n → G → Prop),
  (∀ u v g, E u v g → E v u g⁻¹) →
  let walk := fun (m : ℕ) (v : ℕ → Fin n) (s : ℕ → G) =>
    ∀ i < m, E (v i) (v (i+1)) (s i)
  let gain := fun (m : ℕ) (s : ℕ → G) => ((List.range m).map s).prod
  let pinsOK := fun (S : Finset (Fin n)) (z : Fin n → G) (R : ℕ) =>
    ∀ m ≤ R, ∀ v s, walk m v s → v 0 ∈ S → v m ∈ S →
      z (v m) = z (v 0) * gain m s
  let closedOK := fun radius : ℕ =>
    ∀ m ≤ radius, ∀ v s, walk m v s → v 0 = v m → gain m s = 1
  ∀ (S : Finset (Fin n)) (z : Fin n → G) (q R : ℕ),
    (∀ U : Finset (Fin n), U.card ≤ q → ∃ y : Fin n → G,
      (∀ i ∈ S, y i = z i) ∧ pinsOK (S ∪ U) y R) ↔
    pinsOK S z ((q+1)*R) ∧ closedOK (q*R) := by
  intro n G _ _ E hsym walk0 gain0 pinsOK closedOK S z q R
  have hwalk0 : walk0 = PEqualNP.Outside.L_lib_597_aux.walk E := rfl
  have hgain0 : gain0 = PEqualNP.Outside.L_lib_597_aux.gain := rfl
  constructor
  · intro hLHS
    constructor
    · intro m hm v s hw hv0 hvm
      let t : ℕ → ℕ := fun j => min (j * R) m
      let U : Finset (Fin n) := (Finset.range q).image (fun j => v (t (j + 1)))
      have hU_card : U.card ≤ q :=
        le_trans Finset.card_image_le (by simp)
      rcases hLHS U hU_card with ⟨y, hyS, hyPins⟩
      have hmem : ∀ j ≤ q + 1, v (t j) ∈ S ∪ U := by
        intro j hj
        by_cases hj0 : j = 0
        · subst hj0; simp only [t, zero_mul, Nat.zero_min]; exact Finset.mem_union_left U hv0
        · by_cases hjq : j = q + 1
          · subst hjq
            have htm : t (q + 1) = m := Nat.min_eq_right hm
            rw [htm]; exact Finset.mem_union_left U hvm
          · refine Finset.mem_union_right S ?_
            refine Finset.mem_image.mpr ⟨j - 1, Finset.mem_range.mpr (by omega), ?_⟩
            congr 2; omega
      have heval := pins_chain_eval R (S ∪ U) y hyPins hw (q + 1) t
        (by simp [t])
        (fun j _ => min_le_min_right m (Nat.mul_le_mul_right R (by omega)))
        (fun j _ => by
          simp only [t]
          have hmul : (j + 1) * R = j * R + R := by ring
          omega)
        (fun j _ => Nat.min_le_right _ _)
        hmem (q + 1) le_rfl
      have htm : t (q + 1) = m := Nat.min_eq_right hm
      rw [htm, hyS (v m) hvm, hyS (v 0) hv0] at heval
      exact heval
    · intro m hm v s hw hcl
      by_cases hq0 : q = 0
      · subst hq0
        have hm0 : m = 0 := by simpa using hm
        subst hm0
        exact gain_zero s
      · let t : ℕ → ℕ := fun j => min (j * R) m
        let U : Finset (Fin n) := (Finset.range q).image (fun j => v (t j))
        have hU_card : U.card ≤ q :=
          le_trans Finset.card_image_le (by simp)
        rcases hLHS U hU_card with ⟨y, _, hyPins⟩
        have hmem : ∀ j ≤ q, v (t j) ∈ S ∪ U := by
          intro j hj
          refine Finset.mem_union_right S ?_
          by_cases hjq : j = q
          · subst j
            have htm : t q = m := Nat.min_eq_right hm
            rw [htm, ← hcl]
            refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
            simp [t]
          · exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
        have heval := pins_chain_eval R (S ∪ U) y hyPins hw q t
          (by simp [t])
          (fun j _ => min_le_min_right m (Nat.mul_le_mul_right R (by omega)))
          (fun j _ => by
            simp only [t]
            have hmul : (j + 1) * R = j * R + R := by ring
            omega)
          (fun j _ => Nat.min_le_right _ _)
          hmem q le_rfl
        have htm : t q = m := Nat.min_eq_right hm
        rw [htm, ← hcl] at heval
        have h1 : y (v 0) * 1 = y (v 0) * gain0 m s := by
          rw [mul_one]; exact heval
        exact (mul_left_cancel h1).symm
  · rintro ⟨hPins, hClosed⟩ U hU
    classical
    let U' : Finset (Fin n) := U \ S
    have hU'_card : U'.card ≤ q := le_trans (Finset.card_le_card Finset.sdiff_subset) hU
    let Short : Fin n → Fin n → G → Prop := fun a b g =>
      ∃ m ≤ R, ∃ v s, walk0 m v s ∧ v 0 = a ∧ v m = b ∧ gain0 m s = g
    have hShort_sym : ∀ a b g, Short a b g → Short b a g⁻¹ := by
      rintro a b g ⟨m, hm, v, s, hw, hv0, hvm, hgs⟩
      rcases walk_rev hsym hw with ⟨vr, sr, hwr, hvr0, hvrm, hgr⟩
      exact ⟨m, hm, vr, sr, hwr, hvr0.trans hvm, hvrm.trans hv0, hgr.trans (congrArg Inv.inv hgs)⟩
    let Rep : Option {u : Fin n // u ∈ U'} → Fin n → Prop := fun p a =>
      match p with
      | none => a ∈ S
      | some u => a = u.1
    let adj : Option {u : Fin n // u ∈ U'} → Fin n → G := fun p a =>
      match p with
      | none => z a
      | some _ => 1
    let EH : Option {u : Fin n // u ∈ U'} → Option {u : Fin n // u ∈ U'} → G → Prop :=
      fun p1 p2 h =>
        ∃ a b g, Rep p1 a ∧ Rep p2 b ∧ Short a b g ∧ h = adj p1 a * g * (adj p2 b)⁻¹
    have hEH_sym : ∀ p1 p2 h, EH p1 p2 h → EH p2 p1 h⁻¹ := by
      rintro p1 p2 h ⟨a, b, g, hpa, hqb, hsh, rfl⟩
      refine ⟨b, a, g⁻¹, hqb, hpa, hShort_sym a b g hsh, ?_⟩
      group
    have hEH_closed : ∀ k : ℕ, ∀ P H_s,
        PEqualNP.Outside.L_lib_597_aux.walk EH k P H_s → P 0 = P k →
        PEqualNP.Outside.L_lib_597_aux.gain k H_s = 1 := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro P H_s hwP hclP
        by_contra hne1
        have hk_pos : 0 < k := by
          by_contra hk0
          have h0 : k = 0 := by omega
          subst h0
          exact hne1 (gain_zero H_s)
        have hnodup : ∀ i j : ℕ, i < j → j < k → P i ≠ P j := by
          intro i j hij hjk heq
          have hw_in := walk_subwalk hwP i j (by omega) (by omega)
          have hgin : PEqualNP.Outside.L_lib_597_aux.gain (j - i) (fun t => H_s (i + t)) = 1 :=
            ih (j - i) (by omega) _ _ hw_in (by simpa [Nat.add_sub_of_le (le_of_lt hij)] using heq)
          have hw_pre : PEqualNP.Outside.L_lib_597_aux.walk EH i P H_s :=
            fun t ht => hwP t (by omega)
          have hw_suf := walk_subwalk hwP j k (by omega) le_rfl
          have hmid : P i = P (j + 0) := by simpa using heq
          rcases walk_concat hw_pre hw_suf hmid with ⟨vout, sout, hwout, hvout0, hvoutm, hgout⟩
          have hout_cl : vout 0 = vout (i + (k - j)) := by
            rw [hvout0, hvoutm, Nat.add_sub_of_le (le_of_lt hjk), hclP]
          have hgout1 : PEqualNP.Outside.L_lib_597_aux.gain (i + (k - j)) sout = 1 :=
            ih (i + (k - j)) (by omega) vout sout hwout hout_cl
          rw [hgout] at hgout1
          have htot : PEqualNP.Outside.L_lib_597_aux.gain k H_s =
              PEqualNP.Outside.L_lib_597_aux.gain i H_s *
                PEqualNP.Outside.L_lib_597_aux.gain (j - i) (fun t => H_s (i + t)) *
                PEqualNP.Outside.L_lib_597_aux.gain (k - j) (fun t => H_s (j + t)) := by
            have h1 := gain_add i (k - i) H_s
            rw [show i + (k - i) = k by omega] at h1
            have h2 := gain_add (j - i) (k - j) (fun t => H_s (i + t))
            rw [show (j - i) + (k - j) = k - i by omega] at h2
            rw [h1, h2, ← mul_assoc]
            congr 1
            refine gain_congr (k - j) _ _ fun t _ => ?_
            congr 1; omega
          rw [htot, hgin, mul_one, hgout1] at hne1
          exact hne1 rfl
        have hinj : Function.Injective (fun i : Fin k => P i.val) := by
          intro a b hab
          by_contra hne
          have hval : a.val ≠ b.val := fun h => hne (Fin.ext h)
          rcases lt_or_gt_of_ne hval with hlt | hgt
          · exact hnodup a.val b.val hlt b.2 hab
          · exact hnodup b.val a.val hgt a.2 hab.symm
        by_cases hhas_none : ∃ i0 < k, P i0 = none
        · rcases hhas_none with ⟨i0, hi0, hPi0⟩
          rcases walk_rotate hwP hclP i0 hi0 with ⟨P', H_s', hwP', hP'_mod, hP'0, hP'k, hiff⟩
          have hk_le : k ≤ q + 1 := by
            have hcard_le : Fintype.card (Fin k) ≤ Fintype.card (Option {u : Fin n // u ∈ U'}) :=
              Fintype.card_le_of_injective _ hinj
            simp only [Fintype.card_fin, Fintype.card_option, Fintype.card_coe] at hcard_le
            omega
          have hP'0_none : P' 0 = none := hP'0.trans hPi0
          have hP'k_none : P' k = none := hP'k.trans hPi0
          have hP'_mid : ∀ j : ℕ, 0 < j → j < k → P' j ≠ none := by
            intro j hj0 hjk hnone
            rw [hP'_mod j (by omega)] at hnone
            have hmod_lt : (i0 + j) % k < k := Nat.mod_lt _ hk_pos
            have hmod_ne : (i0 + j) % k ≠ i0 := by
              intro heq
              have h1 : (i0 + j) % k = (i0 + 0) % k := by rw [heq, Nat.add_zero, Nat.mod_eq_of_lt hi0]
              by_cases hlt : i0 + j < k
              · rw [Nat.mod_eq_of_lt hlt, Nat.add_zero, Nat.mod_eq_of_lt hi0] at h1; omega
              · have hsub : (i0 + j) % k = i0 + j - k := by
                  have ha : i0 + j = (i0 + j - k) + k := by omega
                  conv_lhs => rw [ha]
                  rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                rw [hsub, Nat.add_zero, Nat.mod_eq_of_lt hi0] at h1; omega
            have hfin_eq : (⟨(i0 + j) % k, hmod_lt⟩ : Fin k) = ⟨i0, hi0⟩ :=
              hinj (hnone.trans hPi0.symm)
            exact hmod_ne (congrArg Fin.val hfin_eq)
          have hdata : ∀ j < k, ∃ a b g,
              Rep (P' j) a ∧ Rep (P' (j + 1)) b ∧ Short a b g ∧
                H_s' j = adj (P' j) a * g * (adj (P' (j + 1)) b)⁻¹ :=
            fun j hj => hwP' j hj
          choose a b g ha hb hsh hH using hdata
          let Vseq : ℕ → Fin n := fun j =>
            if h0 : j = 0 then a 0 hk_pos
            else if hk' : j = k then b (k - 1) (by omega)
            else if hlt : j < k then a j hlt
            else a 0 hk_pos
          let gseq : ℕ → G := fun j => if h : j < k then g j h else 1
          have hstep_short : ∀ j < k, Short (Vseq j) (Vseq (j + 1)) (gseq j) := by
            intro j hj
            have hleft : Vseq j = a j hj := by
              by_cases hj0 : j = 0
              · subst hj0; simp [Vseq]
              · simp [Vseq, hj0, show j ≠ k by omega, hj]
            have hright : Vseq (j + 1) = b j hj := by
              by_cases hjk : j + 1 = k
              · have hk0 : k ≠ 0 := by omega
                have hjk' : k - 1 = j := by omega
                simp only [Vseq, hjk, hk0, ↓reduceDIte]
                congr 1
              · have h1 : j + 1 ≠ 0 := by omega
                have hlt : j + 1 < k := by omega
                simp only [Vseq, h1, hjk, hlt, ↓reduceDIte]
                have hne_none := hP'_mid (j + 1) (by omega) hlt
                cases hPval : P' (j + 1) with
                | none => exact absurd hPval hne_none
                | some u =>
                  have ha' := ha (j + 1) hlt
                  have hb' := hb j hj
                  rw [hPval] at ha' hb'
                  exact ha'.trans hb'.symm
            rw [hleft, hright]
            simp only [gseq, hj, ↓reduceDIte]
            exact hsh j hj
          rcases short_chain_concat R k Vseq gseq hstep_short with
            ⟨m_tot, hm_tot, v_tot, s_tot, hw_tot, hv0_tot, hvm_tot, hgain_tot⟩
          have ha0S : Vseq 0 ∈ S := by
            simp only [Vseq, ↓reduceDIte]
            have h := ha 0 hk_pos
            rw [hP'0_none] at h
            exact h
          have hbkS : Vseq k ∈ S := by
            simp only [Vseq, show k ≠ 0 by omega, ↓reduceDIte]
            have h := hb (k - 1) (by omega)
            rw [show k - 1 + 1 = k by omega, hP'k_none] at h
            exact h
          have hpins_res : z (Vseq k) = z (Vseq 0) * PEqualNP.Outside.L_lib_597_aux.gain k gseq := by
            have h1 := hPins m_tot (le_trans hm_tot (Nat.mul_le_mul_right R hk_le)) v_tot s_tot
              hw_tot (by rwa [hv0_tot]) (by rwa [hvm_tot])
            rw [hv0_tot, hvm_tot, hgain0, hgain_tot] at h1
            exact h1
          have hH_prod : PEqualNP.Outside.L_lib_597_aux.gain k H_s' =
              z (Vseq 0) * PEqualNP.Outside.L_lib_597_aux.gain k gseq * (z (Vseq k))⁻¹ := by
            by_cases hk1 : k = 1
            · subst hk1
              rw [gain_one, gain_one, hH 0 (by omega)]
              have h0 : Vseq 0 = a 0 (by omega) := by simp [Vseq]
              have h1 : Vseq 1 = b 0 (by omega) := by simp [Vseq]
              have hg0 : gseq 0 = g 0 (by omega) := by simp [gseq]
              rw [h0, h1, hg0, hP'0_none, hP'k_none]
            · have hmid_adj : ∀ j : ℕ, 0 < j → j < k →
                  ∀ x : Fin n, adj (P' j) x = 1 := by
                intro j hj0 hjk x
                cases hPval : P' j with
                | none => exact absurd hPval (hP'_mid j hj0 hjk)
                | some _ => rfl
              have hsplit_first : PEqualNP.Outside.L_lib_597_aux.gain k H_s' =
                  H_s' 0 * PEqualNP.Outside.L_lib_597_aux.gain (k - 1) (fun i => H_s' (1 + i)) := by
                have h := gain_add 1 (k - 1) H_s'
                rw [show 1 + (k - 1) = k by omega, gain_one] at h
                exact h
              have hsplit_g : PEqualNP.Outside.L_lib_597_aux.gain k gseq =
                  gseq 0 * PEqualNP.Outside.L_lib_597_aux.gain (k - 1) (fun i => gseq (1 + i)) := by
                have h := gain_add 1 (k - 1) gseq
                rw [show 1 + (k - 1) = k by omega, gain_one] at h
                exact h
              have hH0 : H_s' 0 = z (Vseq 0) * gseq 0 := by
                rw [hH 0 hk_pos, hP'0_none, hmid_adj 1 (by omega) (by omega)]
                simp only [adj, inv_one, mul_one, Vseq, ↓reduceDIte, gseq, hk_pos]
              have htail : PEqualNP.Outside.L_lib_597_aux.gain (k - 1) (fun i => H_s' (1 + i)) =
                  PEqualNP.Outside.L_lib_597_aux.gain (k - 1) (fun i => gseq (1 + i)) * (z (Vseq k))⁻¹ := by
                have hk2 : 1 ≤ k - 1 := by omega
                have hlast : (k - 1) = (k - 2) + 1 := by omega
                rw [hlast, gain_succ, gain_succ]
                have hmid_eq : PEqualNP.Outside.L_lib_597_aux.gain (k - 2) (fun i => H_s' (1 + i)) =
                    PEqualNP.Outside.L_lib_597_aux.gain (k - 2) (fun i => gseq (1 + i)) := by
                  refine gain_congr (k - 2) _ _ fun i hi => ?_
                  rw [hH (1 + i) (by omega),
                    hmid_adj (1 + i) (by omega) (by omega),
                    hmid_adj (1 + i + 1) (by omega) (by omega)]
                  simp only [one_mul, inv_one, mul_one, gseq, show 1 + i < k by omega, ↓reduceDIte]
                have hend_eq : H_s' (1 + (k - 2)) = gseq (1 + (k - 2)) * (z (Vseq k))⁻¹ := by
                  have hidx : 1 + (k - 2) = k - 1 := by omega
                  have hbeq : b (1 + (k - 2)) (by omega) = b (k - 1) (by omega) := by
                    congr 1
                  rw [hH (1 + (k - 2)) (by omega),
                    hmid_adj (1 + (k - 2)) (by omega) (by omega),
                    show 1 + (k - 2) + 1 = k by omega, hP'k_none]
                  simp only [one_mul, adj, gseq, show 1 + (k - 2) < k by omega, ↓reduceDIte,
                    Vseq, show k ≠ 0 by omega]
                  rw [hbeq]
                rw [hmid_eq, hend_eq, mul_assoc]
              rw [hsplit_first, hsplit_g, hH0, htail]
              group
          rw [hH_prod, ← hpins_res, mul_inv_cancel] at hiff
          exact hne1 (hiff.mp rfl)
        · push Not at hhas_none
          have hk_le : k ≤ q := by
            let f : Fin k → {u : Fin n // u ∈ U'} := fun i =>
              match h : P i.val with
              | none => absurd h (hhas_none i.val i.2)
              | some u => u
            have hf_inj : Function.Injective f := by
              intro a b hab
              apply hinj
              cases ha : P a.val with
              | none => exact absurd ha (hhas_none a.val a.2)
              | some ua =>
                cases hb : P b.val with
                | none => exact absurd hb (hhas_none b.val b.2)
                | some ub =>
                  simp only [f] at hab
                  have ha' : (match h : P a.val with | none => absurd h (hhas_none a.val a.2) | some u => u) = ua := by
                    split <;> simp_all
                  have hb' : (match h : P b.val with | none => absurd h (hhas_none b.val b.2) | some u => u) = ub := by
                    split <;> simp_all
                  rw [ha', hb'] at hab
                  dsimp only
                  rw [ha, hb, hab]
            have hcard_le : Fintype.card (Fin k) ≤ Fintype.card {u : Fin n // u ∈ U'} :=
              Fintype.card_le_of_injective f hf_inj
            simp only [Fintype.card_fin, Fintype.card_coe] at hcard_le
            omega
          have hP_all : ∀ i ≤ k, P i ≠ none := by
            intro i hi
            by_cases hik : i = k
            · rw [hik, ← hclP]; exact hhas_none 0 hk_pos
            · exact hhas_none i (by omega)
          let Vseq : ℕ → Fin n := fun i =>
            match P i with
            | none => ⟨0, by
                have h0 := hhas_none 0 hk_pos
                cases hP0 : P 0 with
                | none => exact absurd hP0 h0
                | some u => exact Nat.pos_of_ne_zero (fun hn0 => Fin.elim0 (hn0 ▸ u.1))⟩
            | some u => u.1
          have hstep_short : ∀ i < k, Short (Vseq i) (Vseq (i + 1)) (H_s i) := by
            intro i hi
            rcases hwP i hi with ⟨a, b, g, ha, hb, hsh, hH⟩
            cases hPi : P i with
            | none => exact absurd hPi (hP_all i (by omega))
            | some ui =>
              cases hPi1 : P (i + 1) with
              | none => exact absurd hPi1 (hP_all (i + 1) (by omega))
              | some ui1 =>
                rw [hPi] at ha hH
                rw [hPi1] at hb hH
                simp only [Rep, adj, one_mul, inv_one, mul_one] at ha hb hH
                subst ha hb hH
                simp only [Vseq, hPi, hPi1]
                exact hsh
          rcases short_chain_concat R k Vseq H_s hstep_short with
            ⟨m_tot, hm_tot, v_tot, s_tot, hw_tot, hv0_tot, hvm_tot, hgain_tot⟩
          have hcl_tot : v_tot 0 = v_tot m_tot := by
            rw [hv0_tot, hvm_tot]
            simp only [Vseq, hclP]
          have h1 := hClosed m_tot (le_trans hm_tot (Nat.mul_le_mul_right R hk_le)) v_tot s_tot
            hw_tot hcl_tot
          rw [hgain0, hgain_tot] at h1
          exact hne1 h1
    let ReachH : Option {u : Fin n // u ∈ U'} → Option {u : Fin n // u ∈ U'} → Prop :=
      fun p1 p2 => ∃ k P H_s, PEqualNP.Outside.L_lib_597_aux.walk EH k P H_s ∧ P 0 = p1 ∧ P k = p2
    have hReach_refl : ∀ p, ReachH p p := fun p =>
      ⟨0, fun _ => p, fun _ => 1, fun _ hi => absurd hi (Nat.not_lt_zero _), rfl, rfl⟩
    have hReach_symm : ∀ p1 p2, ReachH p1 p2 → ReachH p2 p1 := by
      rintro p1 p2 ⟨k, P, H_s, hw, h0, hk⟩
      rcases walk_rev hEH_sym hw with ⟨Pr, H_sr, hwr, h0r, hkr, _⟩
      exact ⟨k, Pr, H_sr, hwr, h0r.trans hk, hkr.trans h0⟩
    have hReach_trans : ∀ p1 p2 p3, ReachH p1 p2 → ReachH p2 p3 → ReachH p1 p3 := by
      rintro p1 p2 p3 ⟨k1, P1, s1, hw1, h10, h1k⟩ ⟨k2, P2, s2, hw2, h20, h2k⟩
      rcases walk_concat hw1 hw2 (h1k.trans h20.symm) with ⟨P, s, hw, h0, hk, _⟩
      exact ⟨k1 + k2, P, s, hw, h0.trans h10, hk.trans h2k⟩
    have hgain_unique : ∀ p1 p2 k1 P1 s1 k2 P2 s2,
        PEqualNP.Outside.L_lib_597_aux.walk EH k1 P1 s1 → P1 0 = p1 → P1 k1 = p2 →
        PEqualNP.Outside.L_lib_597_aux.walk EH k2 P2 s2 → P2 0 = p1 → P2 k2 = p2 →
        PEqualNP.Outside.L_lib_597_aux.gain k1 s1 = PEqualNP.Outside.L_lib_597_aux.gain k2 s2 := by
      intro p1 p2 k1 P1 s1 k2 P2 s2 hw1 h10 h1k hw2 h20 h2k
      rcases walk_rev hEH_sym hw2 with ⟨P2r, s2r, hw2r, h2r0, h2rk, hg2r⟩
      rcases walk_concat hw1 hw2r (h1k.trans (h2r0.trans h2k).symm) with ⟨P, s, hw, h0, hk, hgs⟩
      have hcl : P 0 = P (k1 + k2) := by rw [h0, hk, h10, h2rk, h20]
      have h1 := hEH_closed (k1 + k2) P s hw hcl
      rw [hgs, hg2r] at h1
      exact mul_inv_eq_one.mp h1
    let idxOf : Option {u : Fin n // u ∈ U'} → ℕ := fun p =>
      match p with
      | none => 0
      | some u => u.1.val + 1
    have hidx_inj : Function.Injective idxOf := by
      intro p1 p2 h
      cases p1 with
      | none =>
        cases p2 with
        | none => rfl
        | some u => simp [idxOf] at h
      | some u1 =>
        cases p2 with
        | none => simp [idxOf] at h
        | some u2 =>
          simp only [idxOf] at h
          have : u1.1.val = u2.1.val := by omega
          exact congrArg some (Subtype.ext (Fin.ext this))
    let compOf : Option {u : Fin n // u ∈ U'} → Finset (Option {u : Fin n // u ∈ U'}) := fun p =>
      Finset.univ.filter (fun q => ReachH p q)
    have hcomp_ne : ∀ p, (compOf p).Nonempty := fun p =>
      ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hReach_refl p⟩⟩
    have hcomp_eq : ∀ p1 p2, ReachH p1 p2 → compOf p1 = compOf p2 := by
      intro p1 p2 hr
      ext x
      simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => hReach_trans p2 p1 x (hReach_symm p1 p2 hr) h,
        fun h => hReach_trans p1 p2 x hr h⟩
    let baseOf : Option {u : Fin n // u ∈ U'} → Option {u : Fin n // u ∈ U'} := fun p =>
      Classical.choose (Finset.mem_image.mp
        (Finset.min'_mem ((compOf p).image idxOf) (Finset.Nonempty.image (hcomp_ne p) idxOf)))
    have hbase_mem : ∀ p, baseOf p ∈ compOf p ∧
        idxOf (baseOf p) = ((compOf p).image idxOf).min' (Finset.Nonempty.image (hcomp_ne p) idxOf) :=
      fun p => Classical.choose_spec (Finset.mem_image.mp
        (Finset.min'_mem ((compOf p).image idxOf) (Finset.Nonempty.image (hcomp_ne p) idxOf)))
    have hbase_reach : ∀ p, ReachH (baseOf p) p := fun p =>
      hReach_symm p (baseOf p) (Finset.mem_filter.mp (hbase_mem p).1).2
    have hbase_eq : ∀ p1 p2, ReachH p1 p2 → baseOf p1 = baseOf p2 := by
      intro p1 p2 hr
      apply hidx_inj
      rw [(hbase_mem p1).2, (hbase_mem p2).2]
      have hc := hcomp_eq p1 p2 hr
      simp only [hc]
    have hbase_none : baseOf none = none := by
      apply hidx_inj
      rw [(hbase_mem none).2]
      apply le_antisymm
      · exact Finset.min'_le _ 0 (Finset.mem_image.mpr ⟨none,
          Finset.mem_filter.mpr ⟨Finset.mem_univ none, hReach_refl none⟩, rfl⟩)
      · exact Nat.zero_le _
    let yc : Option {u : Fin n // u ∈ U'} → G := fun p =>
      let h := hbase_reach p
      let k := Classical.choose h
      let P := Classical.choose (Classical.choose_spec h)
      let s := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
      PEqualNP.Outside.L_lib_597_aux.gain k s
    have hyc_eq : ∀ p k P s,
        PEqualNP.Outside.L_lib_597_aux.walk EH k P s → P 0 = baseOf p → P k = p →
        yc p = PEqualNP.Outside.L_lib_597_aux.gain k s := by
      intro p k P s hw h0 hk
      let h := hbase_reach p
      let k0 := Classical.choose h
      let P0 := Classical.choose (Classical.choose_spec h)
      let s0 := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
      have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))
      exact hgain_unique (baseOf p) p k0 P0 s0 k P s hspec.1 hspec.2.1 hspec.2.2 hw h0 hk
    have hyc_none : yc none = 1 := by
      rw [hyc_eq none 0 (fun _ => none) (fun _ => 1)
        (fun _ hi => absurd hi (Nat.not_lt_zero _)) hbase_none.symm rfl]
      exact gain_zero _
    have hyc_edge : ∀ p1 p2 h, EH p1 p2 h → yc p2 = yc p1 * h := by
      intro p1 p2 h he
      rcases walk_single he with ⟨Pe, se, hwe, h0e, h1e, hge⟩
      have hreach12 : ReachH p1 p2 := ⟨1, Pe, se, hwe, h0e, h1e⟩
      have hbeq : baseOf p1 = baseOf p2 := hbase_eq p1 p2 hreach12
      rcases hbase_reach p1 with ⟨k1, P1, s1, hw1, h10, h1k⟩
      rcases walk_concat hw1 hwe (h1k.trans h0e.symm) with ⟨P2, s2, hw2, h20, h2k, hg2⟩
      rw [hyc_eq p1 k1 P1 s1 hw1 h10 h1k,
        hyc_eq p2 (k1 + 1) P2 s2 hw2 (h20.trans (h10.trans hbeq)) (h2k.trans h1e),
        hg2, hge]
    let y : Fin n → G := fun i =>
      if i ∈ S then z i else if h : i ∈ U' then yc (some ⟨i, h⟩) else 1
    refine ⟨y, fun i hi => by simp [y, hi], ?_⟩
    intro m hm v s hw hv0 hvm
    have hShort : Short (v 0) (v m) (gain0 m s) := ⟨m, hm, v, s, hw, rfl, rfl, rfl⟩
    let toOpt : ∀ a : Fin n, a ∈ S ∪ U → Option {u : Fin n // u ∈ U'} := fun a ha =>
      if hS : a ∈ S then none
      else some ⟨a, Finset.mem_sdiff.mpr ⟨(Finset.mem_union.mp ha).resolve_left hS, hS⟩⟩
    have hRep : ∀ a (ha : a ∈ S ∪ U), Rep (toOpt a ha) a := by
      intro a ha
      by_cases hS : a ∈ S
      · simp [toOpt, hS, Rep]
      · simp [toOpt, hS, Rep]
    have hy_eq : ∀ a (ha : a ∈ S ∪ U), y a = yc (toOpt a ha) * adj (toOpt a ha) a := by
      intro a ha
      by_cases hS : a ∈ S
      · simp only [y, hS, ↓reduceIte, toOpt, ↓reduceDIte, hyc_none, adj, one_mul]
      · have hU'a : a ∈ U' := Finset.mem_sdiff.mpr ⟨(Finset.mem_union.mp ha).resolve_left hS, hS⟩
        simp only [y, hS, ↓reduceIte, hU'a, ↓reduceDIte, toOpt, adj, mul_one]
    let p0 := toOpt (v 0) hv0
    let pm := toOpt (v m) hvm
    have hEdge : EH p0 pm (adj p0 (v 0) * gain0 m s * (adj pm (v m))⁻¹) :=
      ⟨v 0, v m, gain0 m s, hRep (v 0) hv0, hRep (v m) hvm, hShort, rfl⟩
    have hstep := hyc_edge p0 pm _ hEdge
    rw [hy_eq (v m) hvm, hy_eq (v 0) hv0, hstep]
    dsimp only [p0, pm]
    group

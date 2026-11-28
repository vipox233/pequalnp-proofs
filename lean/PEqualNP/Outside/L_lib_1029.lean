import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1029

section ProofBody

private abbrev V (q : ℕ) : Type := Fin q → ZMod 2

private def dot {q : ℕ} (a x : V q) : ZMod 2 := ∑ i, a i * x i

private def chi {q : ℕ} (a x : V q) : ℚ := if dot a x = 0 then 1 else -1

private lemma zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

private lemma v_add_self {q : ℕ} (a : V q) : a + a = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  rcases zmod2_cases (a i) with h | h <;> rw [h] <;> decide

private lemma v_add_eq_zero_iff {q : ℕ} (a b : V q) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    funext i
    have hi : a i + b i = 0 := congrFun h i
    rcases zmod2_cases (a i) with ha | ha <;> rcases zmod2_cases (b i) with hb | hb <;>
      simp [ha, hb] at hi ⊢
  · rintro rfl; exact v_add_self a

private lemma dot_zero_left {q : ℕ} (x : V q) : dot (0 : V q) x = 0 := by
  simp [dot]

private lemma dot_add_left {q : ℕ} (a b x : V q) : dot (a + b) x = dot a x + dot b x := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma dot_add_right {q : ℕ} (a x y : V q) : dot a (x + y) = dot a x + dot a y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma chi_zero {q : ℕ} (x : V q) : chi (0 : V q) x = 1 := by
  simp [chi, dot_zero_left]

private lemma chi_mul_left {q : ℕ} (a b x : V q) : chi a x * chi b x = chi (a + b) x := by
  unfold chi
  rw [dot_add_left]
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases zmod2_cases (dot a x) with ha | ha <;> rcases zmod2_cases (dot b x) with hb | hb <;>
    simp [ha, hb, h11]

private lemma chi_mul_right {q : ℕ} (a x y : V q) : chi a (x + y) = chi a x * chi a y := by
  unfold chi
  rw [dot_add_right]
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases zmod2_cases (dot a x) with hx | hx <;> rcases zmod2_cases (dot a y) with hy | hy <;>
    simp [hx, hy, h11]

private lemma chi_sq {q : ℕ} (a x : V q) : chi a x * chi a x = 1 := by
  rw [chi_mul_left, v_add_self, chi_zero]

private lemma one_sub_chi {q : ℕ} (a x : V q) :
    1 - chi a x = if dot a x = 0 then 0 else 2 := by
  unfold chi
  split_ifs <;> norm_num

private lemma card_V (q : ℕ) : (Fintype.card (V q) : ℚ) = (2 : ℚ) ^ q := by
  have h : Fintype.card (V q) = 2 ^ q := by
    simp [V, ZMod.card]
  exact_mod_cast h

private lemma sum_chi {q : ℕ} (a : V q) :
    ∑ x : V q, chi a x = if a = 0 then (2 : ℚ) ^ q else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp only [chi_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ↓reduceIte]
    exact card_V q
  · simp only [ha, ↓reduceIte]
    have hex : ∃ i : Fin q, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    obtain ⟨i, hi⟩ := hex
    have hai : a i = 1 := by
      rcases zmod2_cases (a i) with h0 | h1
      · exact absurd h0 hi
      · exact h1
    let e : V q := Pi.single i (1 : ZMod 2)
    have hdot_e : dot a e = 1 := by
      unfold dot
      rw [Finset.sum_eq_single i]
      · simp [e, hai]
      · intro j _ hji
        simp [e, Pi.single_eq_of_ne hji]
      · intro hi'; exact absurd (Finset.mem_univ i) hi'
    have hchi_e : chi a e = -1 := by
      unfold chi
      rw [hdot_e]
      norm_num
    let eqv : V q ≃ V q :=
      { toFun := fun x => x + e
        invFun := fun x => x + e
        left_inv := fun x => by dsimp only; rw [add_assoc, v_add_self, add_zero]
        right_inv := fun x => by dsimp only; rw [add_assoc, v_add_self, add_zero] }
    have hsum : ∑ x : V q, chi a x = ∑ x : V q, chi a (x + e) :=
      (Fintype.sum_equiv eqv _ _ (fun _ => rfl)).symm
    have hneg : ∑ x : V q, chi a (x + e) = -(∑ x : V q, chi a x) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [chi_mul_right, hchi_e]
      ring
    linarith

private lemma sum_chi_mul {q : ℕ} (a b : V q) :
    ∑ x : V q, chi a x * chi b x = if a = b then (2 : ℚ) ^ q else 0 := by
  have h1 : ∑ x : V q, chi a x * chi b x = ∑ x : V q, chi (a + b) x :=
    Finset.sum_congr rfl fun x _ => chi_mul_left a b x
  rw [h1, sum_chi]
  simp only [v_add_eq_zero_iff]

private lemma main_proof : (let F := ZMod 2
∀ q : ℕ,
  let V := Fin q → F
  let dot := fun (a x : V) => ∑ i, a i * x i
  ∀ (M : V → ℕ), M 0 = 0 →
    let N := ∑ a, M a
    let parity := fun a : V => (if a = 0 then N else M a) % 2
    ∀ (L : ℕ) (c : Fin L → V), 2*L ≤ N+2 →
      (∀ x : V, (∑ a, if dot a x = 0 then 0 else M a) ≤
        2*(Finset.univ.filter (fun j => dot (c j) x ≠ 0)).card) →
      ∀ (k : ℕ) (b : Fin k → ℕ) (h : (i : Fin k) → Fin (b i) → V),
        (∀ i, Function.Injective (h i)) →
        (∀ i j, h i j ≠ 0 ∧ M (h i j) % 2 = 1) →
        (∀ i j j', j ≠ j' → M (h i j + h i j') % 2 = 1) →
        (∀ i i', i ≠ i' → ∀ j j',
          M (h i j + h i' j') % 2 = 0 ∧
          ∃ u, parity (u + (h i j + h i' j')) ≠ parity u) →
        (∑ i, (b i : ℚ) / ((b i : ℚ) + 1)) ≤ 2) := by
  intro F q Vq dotq M hM0 N parity L c h2L hdom k b h hinj hodd hsame hcross
  let K : V q → ℕ := fun a => (Finset.univ.filter (fun j : Fin L => c j = a)).card
  have hK_sum : ∑ a : V q, K a = L := by
    have hcard : (Finset.univ : Finset (Fin L)).card =
        ∑ a : V q, (Finset.univ.filter (fun j : Fin L => c j = a)).card := by
      have hbi : (Finset.univ : Finset (Fin L)) =
          Finset.univ.biUnion (fun a : V q => Finset.univ.filter (fun j : Fin L => c j = a)) := by
        ext j; simp
      conv_lhs => rw [hbi]
      rw [Finset.card_biUnion]
      intro a _ a' _ haa'
      simp only [Function.onFun, Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
      exact haa' (hj1.symm.trans hj2)
    simpa [K] using hcard.symm
  have hchi_c : ∀ x : V q, ∑ j : Fin L, chi (c j) x = ∑ a : V q, (K a : ℚ) * chi a x := by
    intro x
    have h1 : ∑ j : Fin L, chi (c j) x =
        ∑ a : V q, ∑ j ∈ Finset.univ.filter (fun j : Fin L => c j = a), chi (c j) x := by
      have hbi : (Finset.univ : Finset (Fin L)) =
          Finset.univ.biUnion (fun a : V q => Finset.univ.filter (fun j : Fin L => c j = a)) := by
        ext j; simp
      conv_lhs => rw [hbi]
      rw [Finset.sum_biUnion]
      intro a _ a' _ haa'
      simp only [Function.onFun, Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
      exact haa' (hj1.symm.trans hj2)
    rw [h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : ∑ j ∈ Finset.univ.filter (fun j : Fin L => c j = a), chi (c j) x =
        ∑ _j ∈ Finset.univ.filter (fun j : Fin L => c j = a), chi a x :=
      Finset.sum_congr rfl fun j hj => by
        rw [(Finset.mem_filter.mp hj).2]
    rw [h2, Finset.sum_const, nsmul_eq_mul]
  let W : V q → ℚ := fun x =>
    2 * ((2 : ℚ) * ((Finset.univ.filter (fun j : Fin L => dot (c j) x ≠ 0)).card : ℚ) -
      ((∑ a : V q, if dot a x = 0 then 0 else M a : ℕ) : ℚ))
  have hW_nonneg : ∀ x : V q, 0 ≤ W x := by
    intro x
    have hx : (∑ a : V q, if dot a x = 0 then 0 else M a) ≤
        2 * (Finset.univ.filter (fun j : Fin L => dot (c j) x ≠ 0)).card := hdom x
    have hxQ : ((∑ a : V q, if dot a x = 0 then 0 else M a : ℕ) : ℚ) ≤
        2 * ((Finset.univ.filter (fun j : Fin L => dot (c j) x ≠ 0)).card : ℚ) := by
      exact_mod_cast hx
    dsimp only [W]
    linarith
  let w : V q → ℤ := fun a =>
    if a = 0 then 2 * (L : ℤ) - (N : ℤ) - 2 * (K 0 : ℤ) else (M a : ℤ) - 2 * (K a : ℤ)
  have hW_walsh : ∀ x : V q, W x = ∑ a : V q, (w a : ℚ) * chi a x := by
    intro x
    have hM_id : 2 * ((∑ a : V q, if dot a x = 0 then 0 else M a : ℕ) : ℚ) =
        (N : ℚ) - ∑ a : V q, (M a : ℚ) * chi a x := by
      have hN_eq : (N : ℚ) = ∑ a : V q, (M a : ℚ) := by
        change ((∑ a : V q, M a : ℕ) : ℚ) = _
        push_cast; rfl
      rw [hN_eq, ← Finset.sum_sub_distrib]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hsub : (M a : ℚ) - (M a : ℚ) * chi a x = (M a : ℚ) * (1 - chi a x) := by ring
      rw [hsub, one_sub_chi]
      split_ifs <;> ring
    have hC_id : 2 * ((Finset.univ.filter (fun j : Fin L => dot (c j) x ≠ 0)).card : ℚ) =
        (L : ℚ) - ∑ a : V q, (K a : ℚ) * chi a x := by
      rw [← hchi_c x]
      have hL_eq : (L : ℚ) = ∑ _j : Fin L, (1 : ℚ) := by simp
      rw [hL_eq, ← Finset.sum_sub_distrib]
      have hfilt : 2 * ((Finset.univ.filter (fun j : Fin L => dot (c j) x ≠ 0)).card : ℚ) =
          ∑ j : Fin L, (if dot (c j) x = 0 then (0 : ℚ) else 2) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
          mul_comm]
      rw [hfilt]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (one_sub_chi (c j) x).symm
    have hW_eq : W x = (2 * (L : ℚ) - (N : ℚ)) + ∑ a : V q, ((M a : ℚ) - 2 * (K a : ℚ)) * chi a x := by
      have h1 : W x = 2 * (2 * ((Finset.univ.filter (fun j : Fin L => dot (c j) x ≠ 0)).card : ℚ)) -
          2 * ((∑ a : V q, if dot a x = 0 then 0 else M a : ℕ) : ℚ) := by
        dsimp only [W]; ring
      rw [h1, hC_id, hM_id]
      have hsum_sub : ∑ a : V q, ((M a : ℚ) - 2 * (K a : ℚ)) * chi a x =
          (∑ a : V q, (M a : ℚ) * chi a x) - 2 * (∑ a : V q, (K a : ℚ) * chi a x) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => by ring
      rw [hsum_sub]; ring
    rw [hW_eq]
    have hsplit_r : ∑ a : V q, (w a : ℚ) * chi a x =
        (w 0 : ℚ) * chi 0 x + ∑ a ∈ Finset.univ.erase (0 : V q), (w a : ℚ) * chi a x :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : V q))).symm
    have hsplit_l : ∑ a : V q, ((M a : ℚ) - 2 * (K a : ℚ)) * chi a x =
        ((M 0 : ℚ) - 2 * (K 0 : ℚ)) * chi 0 x +
        ∑ a ∈ Finset.univ.erase (0 : V q), ((M a : ℚ) - 2 * (K a : ℚ)) * chi a x :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : V q))).symm
    rw [hsplit_l, hsplit_r]
    have hrest : ∑ a ∈ Finset.univ.erase (0 : V q), ((M a : ℚ) - 2 * (K a : ℚ)) * chi a x =
        ∑ a ∈ Finset.univ.erase (0 : V q), (w a : ℚ) * chi a x := by
      refine Finset.sum_congr rfl fun a ha => ?_
      have hne : a ≠ 0 := (Finset.mem_erase.mp ha).1
      simp only [w, hne, ↓reduceIte]
      push_cast; rfl
    rw [hrest, chi_zero, mul_one, mul_one, hM0]
    simp only [w, ↓reduceIte, Nat.cast_zero, zero_sub]
    push_cast; ring
  have h2q_pos : (0 : ℚ) < (2 : ℚ) ^ q := by positivity
  have hwalsh_coeff : ∀ a : V q, ∑ x : V q, W x * chi a x = (2 : ℚ) ^ q * (w a : ℚ) := by
    intro a
    calc ∑ x : V q, W x * chi a x
        = ∑ x : V q, (∑ b : V q, (w b : ℚ) * chi b x) * chi a x :=
          Finset.sum_congr rfl fun x _ => by rw [hW_walsh x]
      _ = ∑ x : V q, ∑ b : V q, (w b : ℚ) * (chi b x * chi a x) :=
          Finset.sum_congr rfl fun x _ => by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ b : V q, (w b : ℚ) * ∑ x : V q, chi b x * chi a x := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
      _ = ∑ b : V q, (w b : ℚ) * (if b = a then (2 : ℚ) ^ q else 0) :=
          Finset.sum_congr rfl fun b _ => by rw [sum_chi_mul b a]
      _ = (2 : ℚ) ^ q * (w a : ℚ) := by
          rw [Finset.sum_eq_single a]
          · simp [mul_comm]
          · intro b _ hba; simp [hba]
          · intro ha; exact absurd (Finset.mem_univ a) ha
  have hw0_nonneg : 0 ≤ w 0 := by
    have hsum_nn : 0 ≤ ∑ x : V q, W x * chi 0 x :=
      Finset.sum_nonneg fun x _ => by rw [chi_zero, mul_one]; exact hW_nonneg x
    rw [hwalsh_coeff 0] at hsum_nn
    have hQ : (0 : ℚ) ≤ (w 0 : ℚ) := nonneg_of_mul_nonneg_right hsum_nn h2q_pos
    exact_mod_cast hQ
  have hw0_le2 : w 0 ≤ 2 := by
    simp only [w, ↓reduceIte]
    omega
  have hw_abs_le : ∀ d : V q, -w 0 ≤ w d ∧ w d ≤ w 0 := by
    intro d
    have hle : ∑ x : V q, W x * chi d x ≤ ∑ x : V q, W x * chi 0 x := by
      refine Finset.sum_le_sum fun x _ => ?_
      rw [chi_zero, mul_one]
      have hcd : chi d x ≤ 1 := by unfold chi; split_ifs <;> norm_num
      nlinarith [hW_nonneg x]
    have hge : -(∑ x : V q, W x * chi 0 x) ≤ ∑ x : V q, W x * chi d x := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [chi_zero, mul_one]
      have hcd : -1 ≤ chi d x := by unfold chi; split_ifs <;> norm_num
      nlinarith [hW_nonneg x]
    rw [hwalsh_coeff d, hwalsh_coeff 0] at hle hge
    have hleQ : (w d : ℚ) ≤ (w 0 : ℚ) := by nlinarith
    have hgeQ : -(w 0 : ℚ) ≤ (w d : ℚ) := by nlinarith
    exact ⟨by exact_mod_cast hgeQ, by exact_mod_cast hleQ⟩
  have hw_parity : ∀ a : V q, (parity a = 0 ↔ ∃ t : ℤ, w a = 2 * t) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      simp only [parity, w, ↓reduceIte]
      constructor
      · intro hN
        refine ⟨(L : ℤ) - ((N / 2 : ℕ) : ℤ) - (K 0 : ℤ), ?_⟩
        omega
      · rintro ⟨t, ht⟩
        omega
    · simp only [parity, w, ha, ↓reduceIte]
      constructor
      · intro hM
        refine ⟨((M a / 2 : ℕ) : ℤ) - (K a : ℤ), ?_⟩
        omega
      · rintro ⟨t, ht⟩
        omega
  have hfull_mass_parity : ∀ d : V q, (w d = w 0 ∨ w d = -w 0) →
      ∀ u : V q, parity (u + d) = parity u := by
    intro d hfull u
    have hrel : ∃ s : ℚ, (s = 1 ∨ s = -1) ∧ (w d : ℚ) = s * (w 0 : ℚ) := by
      rcases hfull with hpos | hneg
      · exact ⟨1, Or.inl rfl, by rw [hpos]; ring⟩
      · exact ⟨-1, Or.inr rfl, by rw [hneg]; push_cast; ring⟩
    obtain ⟨s, hs, hwd_eq⟩ := hrel
    have hzero_sum : ∑ x : V q, W x * (1 - s * chi d x) = 0 := by
      have hexp : ∑ x : V q, W x * (1 - s * chi d x) =
          (∑ x : V q, W x * chi 0 x) - s * (∑ x : V q, W x * chi d x) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [chi_zero]; ring
      rw [hexp, hwalsh_coeff 0, hwalsh_coeff d, hwd_eq]
      rcases hs with rfl | rfl <;> ring
    have hterm_nn : ∀ x ∈ (Finset.univ : Finset (V q)), 0 ≤ W x * (1 - s * chi d x) := by
      intro x _
      have h1 : 0 ≤ 1 - s * chi d x := by
        unfold chi
        rcases hs with rfl | rfl <;> split_ifs <;> norm_num
      exact mul_nonneg (hW_nonneg x) h1
    have hterm_zero : ∀ x : V q, W x * (1 - s * chi d x) = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nn).mp hzero_sum x (Finset.mem_univ x)
    have hshift : ∀ x : V q, W x * chi d x = s * W x := by
      intro x
      have hx := hterm_zero x
      rcases hs with rfl | rfl <;> linarith
    have hwu_eq : (w (u + d) : ℚ) = s * (w u : ℚ) := by
      have h1 : (2 : ℚ) ^ q * (w (u + d) : ℚ) = (2 : ℚ) ^ q * (s * (w u : ℚ)) := by
        calc (2 : ℚ) ^ q * (w (u + d) : ℚ)
            = ∑ x : V q, W x * chi (u + d) x := (hwalsh_coeff (u + d)).symm
          _ = ∑ x : V q, (W x * chi d x) * chi u x :=
              Finset.sum_congr rfl fun x _ => by rw [← chi_mul_left]; ring
          _ = ∑ x : V q, (s * W x) * chi u x :=
              Finset.sum_congr rfl fun x _ => by rw [hshift x]
          _ = s * ∑ x : V q, W x * chi u x := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x _ => by ring
          _ = (2 : ℚ) ^ q * (s * (w u : ℚ)) := by rw [hwalsh_coeff u]; ring
      exact mul_left_cancel₀ (ne_of_gt h2q_pos) h1
    have hwu_int : w (u + d) = w u ∨ w (u + d) = -w u := by
      rcases hs with rfl | rfl
      · left; rw [one_mul] at hwu_eq; exact_mod_cast hwu_eq
      · right
        have h' : (w (u + d) : ℚ) = ((-w u : ℤ) : ℚ) := by push_cast; linarith
        exact_mod_cast h'
    have hpar_iff : parity (u + d) = 0 ↔ parity u = 0 := by
      rw [hw_parity (u + d), hw_parity u]
      rcases hwu_int with heq | hneg
      · rw [heq]
      · rw [hneg]
        exact ⟨fun ⟨t, ht⟩ => ⟨-t, by omega⟩, fun ⟨t, ht⟩ => ⟨-t, by omega⟩⟩
    have hp1 : parity (u + d) < 2 := Nat.mod_lt _ (by omega)
    have hp2 : parity u < 2 := Nat.mod_lt _ (by omega)
    by_cases h0 : parity u = 0
    · rw [h0, hpar_iff.mpr h0]
    · have h0' : parity (u + d) ≠ 0 := mt hpar_iff.mp h0
      omega
  have hw_odd_unit : ∀ a : V q, a ≠ 0 → M a % 2 = 1 → w a = 1 ∨ w a = -1 := by
    intro a ha hMa
    have hbd := hw_abs_le a
    have hwa : w a = (M a : ℤ) - 2 * (K a : ℤ) := by simp [w, ha]
    omega
  have hw_hij : ∀ (i : Fin k) (j : Fin (b i)), w (h i j) = 1 ∨ w (h i j) = -1 :=
    fun i j => hw_odd_unit (h i j) (hodd i j).1 (hodd i j).2
  have hw_same : ∀ (i : Fin k) (j j' : Fin (b i)), j ≠ j' →
      w (h i j + h i j') = 1 ∨ w (h i j + h i j') = -1 := by
    intro i j j' hne
    have hne0 : h i j + h i j' ≠ 0 := by
      intro h0
      exact hne (hinj i ((v_add_eq_zero_iff _ _).mp h0))
    exact hw_odd_unit _ hne0 (hsame i j j' hne)
  have hw_cross : ∀ (i i' : Fin k), i ≠ i' → ∀ (j : Fin (b i)) (j' : Fin (b i')),
      w (h i j + h i' j') = 0 := by
    intro i i' hii' j j'
    set d : V q := h i j + h i' j' with hddef
    obtain ⟨hMd, u, hpu⟩ := hcross i i' hii' j j'
    rw [← hddef] at hMd hpu
    have hd0 : d ≠ 0 := by
      intro h0
      rw [h0, add_zero] at hpu
      exact hpu rfl
    have hbd := hw_abs_le d
    have hwd : w d = (M d : ℤ) - 2 * (K d : ℤ) := by simp [w, hd0]
    by_contra hnz
    have hfull : w d = w 0 ∨ w d = -w 0 := by omega
    exact hpu (hfull_mass_parity d hfull u)
  let s : (i : Fin k) → Fin (b i) → ℚ := fun i j => (w (h i j) : ℚ)
  have hs_sq : ∀ i j, s i j * s i j = 1 := by
    intro i j
    rcases hw_hij i j with h1 | h1 <;> simp [s, h1]
  have hs_abs : ∀ i j, s i j = 1 ∨ s i j = -1 := by
    intro i j
    rcases hw_hij i j with h1 | h1
    · left; simp [s, h1]
    · right; simp [s, h1]
  let f : Fin k → V q → ℚ := fun i x => ∑ j : Fin (b i), s i j * chi (h i j) x
  have hinner_one : ∀ i : Fin k, ∑ x : V q, W x * f i x = (2 : ℚ) ^ q * (b i : ℚ) := by
    intro i
    calc ∑ x : V q, W x * f i x
        = ∑ x : V q, ∑ j : Fin (b i), s i j * (W x * chi (h i j) x) :=
          Finset.sum_congr rfl fun x _ => by
            dsimp only [f]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j : Fin (b i), s i j * ∑ x : V q, W x * chi (h i j) x := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
      _ = ∑ j : Fin (b i), (2 : ℚ) ^ q := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hwalsh_coeff (h i j)]
          have hsq := hs_sq i j
          dsimp only [s] at hsq
          nlinarith
      _ = (2 : ℚ) ^ q * (b i : ℚ) := by
          simp [mul_comm]
  have hinner_cross : ∀ i i' : Fin k, i ≠ i' → ∑ x : V q, W x * f i x * f i' x = 0 := by
    intro i i' hii'
    have hexp : ∑ x : V q, W x * f i x * f i' x =
        ∑ j : Fin (b i), ∑ j' : Fin (b i'),
          s i j * s i' j' * ∑ x : V q, W x * chi (h i j + h i' j') x := by
      calc ∑ x : V q, W x * f i x * f i' x
          = ∑ x : V q, ∑ j : Fin (b i), ∑ j' : Fin (b i'),
              s i j * s i' j' * (W x * chi (h i j + h i' j') x) :=
            Finset.sum_congr rfl fun x _ => by
              dsimp only [f]
              have h1 : W x * (∑ j : Fin (b i), s i j * chi (h i j) x) =
                  ∑ j : Fin (b i), W x * (s i j * chi (h i j) x) := Finset.mul_sum _ _ _
              rw [h1, Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j' _ => ?_
              rw [← chi_mul_left]; ring
        _ = ∑ j : Fin (b i), ∑ x : V q, ∑ j' : Fin (b i'),
              s i j * s i' j' * (W x * chi (h i j + h i' j') x) := Finset.sum_comm
        _ = ∑ j : Fin (b i), ∑ j' : Fin (b i'), ∑ x : V q,
              s i j * s i' j' * (W x * chi (h i j + h i' j') x) :=
            Finset.sum_congr rfl fun j _ => Finset.sum_comm
        _ = ∑ j : Fin (b i), ∑ j' : Fin (b i'),
              s i j * s i' j' * ∑ x : V q, W x * chi (h i j + h i' j') x :=
            Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by rw [Finset.mul_sum]
    rw [hexp]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' _ => ?_
    rw [hwalsh_coeff, hw_cross i i' hii' j j']
    simp
  have hnorm_le : ∀ i : Fin k,
      ∑ x : V q, W x * f i x * f i x ≤ (2 : ℚ) ^ q * ((b i : ℚ) * ((b i : ℚ) + 1)) := by
    intro i
    have hexp : ∑ x : V q, W x * f i x * f i x =
        ∑ j : Fin (b i), ∑ j' : Fin (b i),
          s i j * s i j' * ((2 : ℚ) ^ q * (w (h i j + h i j') : ℚ)) := by
      calc ∑ x : V q, W x * f i x * f i x
          = ∑ x : V q, ∑ j : Fin (b i), ∑ j' : Fin (b i),
              s i j * s i j' * (W x * chi (h i j + h i j') x) :=
            Finset.sum_congr rfl fun x _ => by
              dsimp only [f]
              have h1 : W x * (∑ j : Fin (b i), s i j * chi (h i j) x) =
                  ∑ j : Fin (b i), W x * (s i j * chi (h i j) x) := Finset.mul_sum _ _ _
              rw [h1, Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j' _ => ?_
              rw [← chi_mul_left]; ring
        _ = ∑ j : Fin (b i), ∑ x : V q, ∑ j' : Fin (b i),
              s i j * s i j' * (W x * chi (h i j + h i j') x) := Finset.sum_comm
        _ = ∑ j : Fin (b i), ∑ j' : Fin (b i), ∑ x : V q,
              s i j * s i j' * (W x * chi (h i j + h i j') x) :=
            Finset.sum_congr rfl fun j _ => Finset.sum_comm
        _ = ∑ j : Fin (b i), ∑ j' : Fin (b i),
              s i j * s i j' * ((2 : ℚ) ^ q * (w (h i j + h i j') : ℚ)) :=
            Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by
              rw [← Finset.mul_sum, hwalsh_coeff]
    rw [hexp]
    have hbound : ∑ j : Fin (b i), ∑ j' : Fin (b i),
          s i j * s i j' * ((2 : ℚ) ^ q * (w (h i j + h i j') : ℚ)) ≤
        ∑ j : Fin (b i), ∑ j' : Fin (b i),
          (if j = j' then (2 : ℚ) ^ q * 2 else (2 : ℚ) ^ q) := by
      refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => ?_
      by_cases hjj : j = j'
      · subst hjj
        simp only [↓reduceIte]
        have h0 : h i j + h i j = 0 := v_add_self (h i j)
        rw [h0]
        have hsq := hs_sq i j
        have hw0Q : (w 0 : ℚ) ≤ 2 := by exact_mod_cast hw0_le2
        rw [hsq, one_mul]
        nlinarith
      · simp only [hjj, ↓reduceIte]
        have h1 := hs_abs i j
        have h2 := hs_abs i j'
        have h3 := hw_same i j j' hjj
        have hprod : s i j * s i j' * (w (h i j + h i j') : ℚ) ≤ 1 := by
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
            simp [h1, h2, h3]
        nlinarith
    have hrhs : ∑ j : Fin (b i), ∑ j' : Fin (b i),
          (if j = j' then (2 : ℚ) ^ q * 2 else (2 : ℚ) ^ q) =
        (2 : ℚ) ^ q * ((b i : ℚ) * ((b i : ℚ) + 1)) := by
      have hterm : ∀ j : Fin (b i),
          ∑ j' : Fin (b i), (if j = j' then (2 : ℚ) ^ q * 2 else (2 : ℚ) ^ q) =
          (2 : ℚ) ^ q * ((b i : ℚ) + 1) := by
        intro j
        have hrew : ∑ j' : Fin (b i), (if j = j' then (2 : ℚ) ^ q * 2 else (2 : ℚ) ^ q) =
            ∑ j' : Fin (b i), ((2 : ℚ) ^ q + if j' = j then (2 : ℚ) ^ q else 0) := by
          refine Finset.sum_congr rfl fun j' _ => ?_
          by_cases hjj : j' = j
          · subst hjj; simp; ring
          · have hne : j ≠ j' := Ne.symm hjj
            simp [hjj, hne]
        rw [hrew, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        ring
      calc ∑ j : Fin (b i), ∑ j' : Fin (b i),
              (if j = j' then (2 : ℚ) ^ q * 2 else (2 : ℚ) ^ q)
          = ∑ _j : Fin (b i), (2 : ℚ) ^ q * ((b i : ℚ) + 1) :=
            Finset.sum_congr rfl fun j _ => hterm j
        _ = (2 : ℚ) ^ q * ((b i : ℚ) * ((b i : ℚ) + 1)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    exact hbound.trans_eq hrhs
  let α : Fin k → ℚ := fun i => 1 / ((b i : ℚ) + 1)
  have hnonneg : 0 ≤ ∑ x : V q, W x * (1 - ∑ i : Fin k, α i * f i x) ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hW_nonneg x) (sq_nonneg _)
  have hexpand : ∑ x : V q, W x * (1 - ∑ i : Fin k, α i * f i x) ^ 2 =
      (∑ x : V q, W x * chi 0 x) -
      2 * (∑ i : Fin k, α i * ∑ x : V q, W x * f i x) +
      ∑ i : Fin k, α i * α i * ∑ x : V q, W x * f i x * f i x := by
    have hsq_step : ∀ x : V q,
        W x * (1 - ∑ i : Fin k, α i * f i x) ^ 2 =
        W x * chi 0 x - 2 * (∑ i : Fin k, α i * (W x * f i x)) +
        ∑ i : Fin k, ∑ i' : Fin k, α i * α i' * (W x * f i x * f i' x) := by
      intro x
      rw [chi_zero, mul_one]
      have h1 : (∑ i : Fin k, α i * f i x) ^ 2 =
          ∑ i : Fin k, ∑ i' : Fin k, α i * α i' * (f i x * f i' x) := by
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i' _ => by ring
      have h2 : W x * (∑ i : Fin k, α i * f i x) = ∑ i : Fin k, α i * (W x * f i x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      have h3 : W x * (∑ i : Fin k, α i * f i x) ^ 2 =
          ∑ i : Fin k, ∑ i' : Fin k, α i * α i' * (W x * f i x * f i' x) := by
        rw [h1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i' _ => by ring
      linarith [show W x * (1 - ∑ i : Fin k, α i * f i x) ^ 2 =
        W x - 2 * (W x * ∑ i : Fin k, α i * f i x) + W x * (∑ i : Fin k, α i * f i x) ^ 2 by ring]
    have hsum1 : ∑ x : V q, W x * (1 - ∑ i : Fin k, α i * f i x) ^ 2 =
        (∑ x : V q, W x * chi 0 x) -
        2 * (∑ x : V q, ∑ i : Fin k, α i * (W x * f i x)) +
        ∑ x : V q, ∑ i : Fin k, ∑ i' : Fin k, α i * α i' * (W x * f i x * f i' x) := by
      rw [Finset.sum_congr rfl fun x _ => hsq_step x]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsum1]
    have hmid : ∑ x : V q, ∑ i : Fin k, α i * (W x * f i x) =
        ∑ i : Fin k, α i * ∑ x : V q, W x * f i x := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    have hlast : ∑ x : V q, ∑ i : Fin k, ∑ i' : Fin k, α i * α i' * (W x * f i x * f i' x) =
        ∑ i : Fin k, α i * α i * ∑ x : V q, W x * f i x * f i x := by
      calc ∑ x : V q, ∑ i : Fin k, ∑ i' : Fin k, α i * α i' * (W x * f i x * f i' x)
          = ∑ i : Fin k, ∑ x : V q, ∑ i' : Fin k, α i * α i' * (W x * f i x * f i' x) :=
            Finset.sum_comm
        _ = ∑ i : Fin k, ∑ i' : Fin k, ∑ x : V q, α i * α i' * (W x * f i x * f i' x) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ i : Fin k, ∑ i' : Fin k, α i * α i' * ∑ x : V q, W x * f i x * f i' x :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by rw [Finset.mul_sum]
        _ = ∑ i : Fin k, α i * α i * ∑ x : V q, W x * f i x * f i x := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_eq_single i]
            · intro i' _ hi'i
              rw [hinner_cross i i' hi'i.symm, mul_zero]
            · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hmid, hlast]
  have hle_rhs : ∑ x : V q, W x * (1 - ∑ i : Fin k, α i * f i x) ^ 2 ≤
      (2 : ℚ) ^ q * (2 - ∑ i : Fin k, (b i : ℚ) / ((b i : ℚ) + 1)) := by
    rw [hexpand, hwalsh_coeff 0]
    have hw0Q : (w 0 : ℚ) ≤ 2 := by exact_mod_cast hw0_le2
    have hlin : ∑ i : Fin k, α i * ∑ x : V q, W x * f i x =
        (2 : ℚ) ^ q * ∑ i : Fin k, (b i : ℚ) / ((b i : ℚ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hinner_one i]
      dsimp only [α]
      ring
    have hquad : ∑ i : Fin k, α i * α i * ∑ x : V q, W x * f i x * f i x ≤
        (2 : ℚ) ^ q * ∑ i : Fin k, (b i : ℚ) / ((b i : ℚ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hpos : (0 : ℚ) < (b i : ℚ) + 1 := by positivity
      have hne : (b i : ℚ) + 1 ≠ 0 := ne_of_gt hpos
      have hαsq : 0 ≤ α i * α i := mul_self_nonneg (α i)
      calc α i * α i * ∑ x : V q, W x * f i x * f i x
          ≤ α i * α i * ((2 : ℚ) ^ q * ((b i : ℚ) * ((b i : ℚ) + 1))) :=
            mul_le_mul_of_nonneg_left (hnorm_le i) hαsq
        _ = (2 : ℚ) ^ q * ((b i : ℚ) / ((b i : ℚ) + 1)) := by
            dsimp only [α]
            field_simp [hne]
    rw [hlin]
    nlinarith
  have hfinal : 0 ≤ (2 : ℚ) ^ q * (2 - ∑ i : Fin k, (b i : ℚ) / ((b i : ℚ) + 1)) :=
    hnonneg.trans hle_rhs
  have hsub_nn : 0 ≤ 2 - ∑ i : Fin k, (b i : ℚ) / ((b i : ℚ) + 1) :=
    nonneg_of_mul_nonneg_right hfinal h2q_pos
  linarith

end ProofBody

end PEqualNP.Outside.L_lib_1029

theorem PEqualNP.Outside.L_lib_1029 : (let F := ZMod 2
∀ q : ℕ,
  let V := Fin q → F
  let dot := fun (a x : V) => ∑ i, a i * x i
  ∀ (M : V → ℕ), M 0 = 0 →
    let N := ∑ a, M a
    let parity := fun a : V => (if a = 0 then N else M a) % 2
    ∀ (L : ℕ) (c : Fin L → V), 2*L ≤ N+2 →
      (∀ x : V, (∑ a, if dot a x = 0 then 0 else M a) ≤
        2*(Finset.univ.filter (fun j => dot (c j) x ≠ 0)).card) →
      ∀ (k : ℕ) (b : Fin k → ℕ) (h : (i : Fin k) → Fin (b i) → V),
        (∀ i, Function.Injective (h i)) →
        (∀ i j, h i j ≠ 0 ∧ M (h i j) % 2 = 1) →
        (∀ i j j', j ≠ j' → M (h i j + h i j') % 2 = 1) →
        (∀ i i', i ≠ i' → ∀ j j',
          M (h i j + h i' j') % 2 = 0 ∧
          ∃ u, parity (u + (h i j + h i' j')) ≠ parity u) →
        (∑ i, (b i : ℚ) / ((b i : ℚ) + 1)) ≤ 2) :=
  PEqualNP.Outside.L_lib_1029.main_proof

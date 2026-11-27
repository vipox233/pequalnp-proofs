import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_505_aux

open Finset

def wt {s : ℕ} (v : Fin s → ZMod 2) : ℕ :=
  ((Finset.univ : Finset (Fin s)).filter (fun i => v i ≠ 0)).card

theorem ceil_div_pow_succ (d k : ℕ) (hd : 0 < d) :
    ((d + 1) / 2 + 2 ^ k - 1) / 2 ^ k = (d + 2 ^ (k + 1) - 1) / 2 ^ (k + 1) := by
  have h2k : 0 < 2 ^ k := Nat.two_pow_pos k
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
  rw [hpow, ← Nat.div_div_eq_div_mul]
  congr 1
  have hnum : d + 2 * 2 ^ k - 1 = (d + 1) + 2 * (2 ^ k - 1) := by omega
  rw [hnum, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
  omega

theorem zmod2_add_weight_bit (a b : ZMod 2) (hb : b ≠ 0) :
    (if a ≠ 0 then 1 else 0) + (if a + b ≠ 0 then 1 else 0) = 1 := by
  revert a b hb
  decide

theorem zmod2_zero_weight_bit (a b : ZMod 2) (hb : b = 0) :
    (if a ≠ 0 then 1 else 0) + (if a + b ≠ 0 then 1 else 0) =
      2 * (if a ≠ 0 then 1 else 0) := by
  revert a b hb
  decide

theorem wt_add_wt_puncture {s : ℕ} (v c : Fin s → ZMod 2) :
    wt v + wt (v + c) =
      2 * ((Finset.univ.filter (fun i : Fin s => c i = 0)).filter (fun i => v i ≠ 0)).card + wt c := by
  unfold wt
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin s => c i = 0)]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin s => c i = 0),
      ((if v i ≠ 0 then 1 else 0) + (if (v + c) i ≠ 0 then 1 else 0)) =
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin s => c i = 0), (if v i ≠ 0 then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hci : c i = 0 := (Finset.mem_filter.1 hi).2
    exact zmod2_zero_weight_bit (v i) (c i) hci
  have h2 : ∑ i ∈ Finset.univ.filter (fun i : Fin s => ¬ c i = 0),
      ((if v i ≠ 0 then 1 else 0) + (if (v + c) i ≠ 0 then 1 else 0)) =
      ∑ i : Fin s, if c i ≠ 0 then 1 else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hci : c i ≠ 0 := (Finset.mem_filter.1 hi).2
    exact zmod2_add_weight_bit (v i) (c i) hci
  rw [h1, h2]

def insertZeroLin {m : ℕ} (k0 : Fin (m + 1)) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin (m + 1) → ZMod 2) where
  toFun := fun u => Fin.insertNth k0 (0 : ZMod 2) u
  map_add' := fun u v => by
    ext i
    refine Fin.succAboveCases k0 (by simp) (fun j => by simp) i
  map_smul' := fun c u => by
    ext i
    refine Fin.succAboveCases k0 (by simp) (fun j => by simp) i

theorem insertZeroLin_injective {m : ℕ} (k0 : Fin (m + 1)) :
    Function.Injective (insertZeroLin k0) := by
  intro u v h
  ext j
  have hj := congrFun h (k0.succAbove j)
  simpa [insertZeroLin] using hj

theorem insertZeroLin_at_k0 {m : ℕ} (k0 : Fin (m + 1)) (u : Fin m → ZMod 2) :
    insertZeroLin k0 u k0 = 0 := by
  simp [insertZeroLin]

theorem main : ∀ (m s d : ℕ), 0 < d →
    ∀ E : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2),
      (∀ w, w ≠ 0 → d ≤ wt (E w)) →
      (∑ i : Fin m, (d + 2 ^ i.val - 1) / 2 ^ i.val) ≤ s := by
  intro m
  induction m with
  | zero =>
    intro s d _ _ _
    simp
  | succ m ih =>
    intro s d hd E hE
    have hne : ((Finset.univ : Finset (Fin (m + 1) → ZMod 2)).erase 0).Nonempty := by
      refine ⟨fun _ => 1, Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩⟩
      intro h0
      have h1 := congrFun h0 ⟨0, Nat.zero_lt_succ m⟩
      exact one_ne_zero h1
    obtain ⟨w0, hw0_mem, hw0_min⟩ :=
      Finset.exists_min_image ((Finset.univ : Finset (Fin (m + 1) → ZMod 2)).erase 0)
        (fun w => wt (E w)) hne
    have hw0_ne : w0 ≠ 0 := (Finset.mem_erase.1 hw0_mem).1
    set w := wt (E w0) with hw_def
    have hdw : d ≤ w := hE w0 hw0_ne
    have hws : w ≤ s := by
      have h1 := Finset.card_le_card
        (Finset.filter_subset (fun i : Fin s => E w0 i ≠ 0) (Finset.univ : Finset (Fin s)))
      rw [Finset.card_univ, Fintype.card_fin] at h1
      exact h1
    obtain ⟨k0, hk0⟩ : ∃ k0 : Fin (m + 1), w0 k0 ≠ 0 := by
      by_contra hc
      apply hw0_ne
      ext i
      by_contra hni
      exact hc ⟨i, hni⟩
    let S0 : Finset (Fin s) := Finset.univ.filter (fun i : Fin s => E w0 i = 0)
    have hS0_card : S0.card = s - w := by
      have hadd : S0.card + w = s := by
        unfold S0
        rw [hw_def, wt, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
        have h1 : ∀ i : Fin s, (if E w0 i = 0 then 1 else 0) + (if E w0 i ≠ 0 then 1 else 0) = 1 := by
          intro i
          by_cases h : E w0 i = 0 <;> simp [h]
        rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, mul_one]
      omega
    have hcard_coe : Fintype.card {i : Fin s // i ∈ S0} = s - w := by
      rw [Fintype.card_coe, hS0_card]
    let e : Fin (s - w) ≃ {i : Fin s // i ∈ S0} := (Fintype.equivFinOfCardEq hcard_coe).symm
    let proj : (Fin s → ZMod 2) →ₗ[ZMod 2] (Fin (s - w) → ZMod 2) :=
      { toFun := fun v j => v (e j).1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let E' : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin (s - w) → ZMod 2) :=
      proj.comp (E.comp (insertZeroLin k0))
    have hE'wt : ∀ u : Fin m → ZMod 2,
        wt (E' u) = (S0.filter (fun i => E (insertZeroLin k0 u) i ≠ 0)).card := by
      intro u
      unfold wt
      refine Finset.card_bij (fun j _ => (e j).1) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact ⟨(e j).2, hj⟩
      · intro j1 _ j2 _ h12
        exact e.injective (Subtype.ext h12)
      · intro i hi
        simp only [Finset.mem_filter] at hi
        refine ⟨e.symm ⟨i, hi.1⟩, ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [E', proj] using hi.2
    have hE'min : ∀ u : Fin m → ZMod 2, u ≠ 0 → (d + 1) / 2 ≤ wt (E' u) := by
      intro u hu
      have hphi_ne : insertZeroLin k0 u ≠ 0 := by
        intro h0
        apply hu
        apply insertZeroLin_injective k0
        simpa using h0
      have hsum_ne : insertZeroLin k0 u + w0 ≠ 0 := by
        intro h0
        have hk := congrFun h0 k0
        simp [insertZeroLin_at_k0] at hk
        exact hk0 hk
      have hm1 : w ≤ wt (E (insertZeroLin k0 u)) :=
        hw0_min (insertZeroLin k0 u) (Finset.mem_erase.2 ⟨hphi_ne, Finset.mem_univ _⟩)
      have hm2 : w ≤ wt (E (insertZeroLin k0 u + w0)) :=
        hw0_min (insertZeroLin k0 u + w0) (Finset.mem_erase.2 ⟨hsum_ne, Finset.mem_univ _⟩)
      rw [map_add] at hm2
      have hrel := wt_add_wt_puncture (E (insertZeroLin k0 u)) (E w0)
      rw [← hE'wt u] at hrel
      omega
    have hih := ih (s - w) ((d + 1) / 2) (by omega) E' hE'min
    rw [Fin.sum_univ_succ]
    have h0term : (d + 2 ^ (0 : Fin (m + 1)).val - 1) / 2 ^ (0 : Fin (m + 1)).val = d := by
      simp
    rw [h0term]
    have htail :
        ∑ i : Fin m, (d + 2 ^ i.succ.val - 1) / 2 ^ i.succ.val =
        ∑ i : Fin m, ((d + 1) / 2 + 2 ^ i.val - 1) / 2 ^ i.val := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact (ceil_div_pow_succ d i.val hd).symm
    rw [htail]
    omega

end PEqualNP.Outside.L_lib_505_aux

theorem PEqualNP.Outside.L_lib_505 :
∀ m s d : ℕ, 0 < d →
  ∀ E : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2),
    (∀ w, w ≠ 0 → d ≤ ((Finset.univ : Finset (Fin s)).filter (fun i => E w i ≠ 0)).card) →
    (∑ i : Fin m, (d + 2^i.val - 1) / 2^i.val) ≤ s := by
  intro m s d hd E hE
  exact PEqualNP.Outside.L_lib_505_aux.main m s d hd E hE

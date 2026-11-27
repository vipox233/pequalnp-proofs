import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_533

theorem gibbs (m : ℕ) (p q : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : (∑ i, p i) = 1)
    (hq : ∀ i, 0 < q i) :
    (∑ i, -(p i) * Real.log (p i)) ≤ (∑ i, -(p i) * Real.log (q i)) + Real.log (∑ i, q i) := by
  obtain ⟨i0, -, -⟩ : ∃ i ∈ (Finset.univ : Finset (Fin m)), p i ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  have hZ : 0 < ∑ i, q i := Finset.sum_pos (fun i _ => hq i) ⟨i0, Finset.mem_univ _⟩
  have key : ∀ i, -(p i) * Real.log (p i) ≤
      -(p i) * Real.log (q i) + p i * Real.log (∑ j, q j) + (q i / (∑ j, q j) - p i) := by
    intro i
    rcases eq_or_lt_of_le (hp i) with h0 | hpos
    · rw [← h0]
      have h5 : 0 ≤ q i / (∑ j, q j) := div_nonneg (hq i).le hZ.le
      simpa using h5
    · have hx : 0 < q i / ((∑ j, q j) * p i) := div_pos (hq i) (mul_pos hZ hpos)
      have h1 := Real.log_le_sub_one_of_pos hx
      rw [Real.log_div (hq i).ne' (mul_pos hZ hpos).ne', Real.log_mul hZ.ne' hpos.ne'] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
      have h3 : p i * (q i / ((∑ j, q j) * p i) - 1) = q i / (∑ j, q j) - p i := by
        field_simp
      rw [h3] at h2
      linarith
  calc (∑ i, -(p i) * Real.log (p i))
      ≤ ∑ i, (-(p i) * Real.log (q i) + p i * Real.log (∑ j, q j) + (q i / (∑ j, q j) - p i)) :=
        Finset.sum_le_sum (fun i _ => key i)
    _ = (∑ i, -(p i) * Real.log (q i)) + Real.log (∑ i, q i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_mul, ← Finset.sum_div, hsum, div_self hZ.ne']
        ring

theorem card_len (S : Finset (List Bool)) (k : ℕ) :
    (S.filter (fun w => w.length = k)).card ≤ 2 ^ k := by
  have h := Finset.card_le_card_of_injOn (s := S.filter (fun w => w.length = k))
    (t := (Finset.univ : Finset (Fin k → Bool)))
    (fun w => fun j : Fin k => w.getD j.val false) (fun _ _ => Finset.mem_univ _)
    (by
      intro w hw w' hw' heq
      have hl : w.length = k := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
      have hl' : w'.length = k := (Finset.mem_filter.mp (Finset.mem_coe.mp hw')).2
      apply List.ext_getElem (hl.trans hl'.symm)
      intro j h1 h2
      have h6 := congrFun heq ⟨j, hl ▸ h1⟩
      simpa [List.getD_eq_getElem, h1, h2] using h6)
  simpa using h

theorem zbound (m : ℕ) (c : Fin m → List Bool) (hc : Function.Injective c) (a : ℝ)
    (ha0 : 0 ≤ a) (ha : 2 * a < 1) :
    (∑ i, a ^ (c i).length) ≤ 1 / (1 - 2 * a) := by
  have h1 : (∑ i, a ^ (c i).length) = ∑ w ∈ Finset.univ.image c, a ^ w.length := by
    rw [Finset.sum_image (fun x _ y _ h => hc h)]
  obtain ⟨N, hN⟩ : ∃ N, ∀ w ∈ Finset.univ.image c, w.length < N :=
    ⟨(Finset.univ.image c).sup List.length + 1,
      fun w hw => Nat.lt_succ_of_le (Finset.le_sup (f := List.length) hw)⟩
  have h2 : (∑ w ∈ Finset.univ.image c, a ^ w.length) =
      ∑ k ∈ Finset.range N, ∑ w ∈ (Finset.univ.image c).filter (fun w => w.length = k),
        a ^ w.length :=
    (Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_range.mpr (hN w hw)) _).symm
  have h3 : ∀ k ∈ Finset.range N,
      (∑ w ∈ (Finset.univ.image c).filter (fun w => w.length = k), a ^ w.length) ≤
        (2 * a) ^ k := by
    intro k _
    have h7 : (∑ w ∈ (Finset.univ.image c).filter (fun w => w.length = k), a ^ w.length) =
        ∑ w ∈ (Finset.univ.image c).filter (fun w => w.length = k), a ^ k :=
      Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2])
    rw [h7, Finset.sum_const, nsmul_eq_mul, mul_pow]
    have hc' := card_len (Finset.univ.image c) k
    have hc2 : (((Finset.univ.image c).filter (fun w => w.length = k)).card : ℝ) ≤ 2 ^ k := by
      exact_mod_cast hc'
    exact mul_le_mul_of_nonneg_right hc2 (pow_nonneg ha0 k)
  have h4 : (∑ k ∈ Finset.range N, (2 * a) ^ k) ≤ 1 / (1 - 2 * a) := by
    have hpos : 0 < 1 - 2 * a := by linarith
    rw [le_div_iff₀ hpos]
    have h8 := mul_neg_geom_sum (2 * a) N
    have hx : 0 ≤ (2 * a) ^ N := pow_nonneg (by linarith) N
    linarith
  rw [h1, h2]
  exact (Finset.sum_le_sum h3).trans h4

theorem main (m : ℕ) (p : Fin m → ℝ) (c : Fin m → List Bool)
    (hp : ∀ i, 0 ≤ p i) (hsum : (∑ i, p i) = 1) (hc : Function.Injective c) :
    (∑ i, -(p i)*Real.log (p i)) ≤
      (∑ i, p i * ((c i).length : ℝ))*Real.log 2 +
      ((∑ i, p i * ((c i).length : ℝ))+1)*Real.log ((∑ i, p i * ((c i).length : ℝ))+1) -
      (∑ i, p i * ((c i).length : ℝ))*Real.log (∑ i, p i * ((c i).length : ℝ)) := by
  have hL0 : 0 ≤ ∑ i, p i * ((c i).length : ℝ) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (Nat.cast_nonneg _))
  generalize hLdef : (∑ i, p i * ((c i).length : ℝ)) = L at hL0 ⊢
  rcases eq_or_lt_of_le hL0 with hz | hLpos
  · subst hz
    have hterm : ∀ i, p i * ((c i).length : ℝ) = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (hp i) (Nat.cast_nonneg _))).mp hLdef i (Finset.mem_univ i)
    have hnil : ∀ i, c i ≠ [] → p i = 0 := by
      intro i hci
      rcases mul_eq_zero.mp (hterm i) with h | h
      · exact h
      · exact absurd (List.length_eq_zero_iff.mp (by exact_mod_cast h)) hci
    have h01 : ∀ i, p i = 0 ∨ p i = 1 := by
      intro i
      by_cases hci : c i = []
      · right
        have h9 : (∑ j, p j) = p i := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            exact hnil j (fun h => hji (hc (h.trans hci.symm)))
          · intro h; exact absurd (Finset.mem_univ i) h
        rw [← h9, hsum]
      · left; exact hnil i hci
    have hH : (∑ i, -(p i)*Real.log (p i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases h01 i with h | h <;> rw [h] <;> simp
    rw [hH]; simp
  · have hne : L + 1 ≠ 0 := by positivity
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = L / (2 * (L + 1)) := ⟨_, rfl⟩
    have hapos : 0 < a := by rw [ha]; positivity
    have h2a : 2 * a = L / (L + 1) := by rw [ha]; field_simp
    have h2a1 : 2 * a < 1 := by rw [h2a, div_lt_one (by linarith)]; linarith
    have hg := gibbs m p (fun i => a ^ (c i).length) hp hsum (fun i => pow_pos hapos _)
    beta_reduce at hg
    have hz := zbound m c hc a hapos.le h2a1
    have hz2 : 1 / (1 - 2 * a) = L + 1 := by rw [h2a]; field_simp; ring
    obtain ⟨i0, -, -⟩ : ∃ i ∈ (Finset.univ : Finset (Fin m)), p i ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
    have hZpos : 0 < ∑ i, a ^ (c i).length :=
      Finset.sum_pos (fun i _ => pow_pos hapos _) ⟨i0, Finset.mem_univ _⟩
    have hlogZ : Real.log (∑ i, a ^ (c i).length) ≤ Real.log (L + 1) := by
      apply Real.log_le_log hZpos
      rw [← hz2]; exact hz
    have hloga : Real.log a = Real.log L - (Real.log 2 + Real.log (L + 1)) := by
      rw [ha, Real.log_div hLpos.ne' (by positivity), Real.log_mul (by norm_num) hne]
    have hsum2 : (∑ i, -(p i) * Real.log (a ^ (c i).length)) = -L * Real.log a := by
      have h10 : ∀ i, -(p i) * Real.log (a ^ (c i).length) =
          -(Real.log a) * (p i * ((c i).length : ℝ)) := by
        intro i; rw [Real.log_pow]; ring
      rw [Finset.sum_congr rfl (fun i _ => h10 i), ← Finset.mul_sum, hLdef]; ring
    rw [hsum2, hloga] at hg
    linarith

end PEqualNP.Outside.L_lib_533

theorem PEqualNP.Outside.L_lib_533 : ∀ (m : ℕ) (p : Fin m → ℝ) (c : Fin m → List Bool),
  (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 → Function.Injective c →
  let L := ∑ i, p i * ((c i).length : ℝ)
  let H := ∑ i, -(p i)*Real.log (p i)
  H ≤ L*Real.log 2 + (L+1)*Real.log (L+1) - L*Real.log L := by
  intro m p c hp hsum hc
  exact PEqualNP.Outside.L_lib_533.main m p c hp hsum hc

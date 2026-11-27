import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_842

open Finset

theorem interm : ∀ (q : ℕ) (lo hi : Fin q → ℕ) (T : ℕ), (∀ j, lo j ≤ hi j) →
    ∑ j, lo j ≤ T → T ≤ ∑ j, hi j →
    ∃ x : Fin q → ℕ, (∀ j, lo j ≤ x j ∧ x j ≤ hi j) ∧ ∑ j, x j = T := by
  intro q
  induction q with
  | zero =>
    intro lo hi T _ _ h2
    refine ⟨fun _ => 0, fun j => j.elim0, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h2 ⊢
    omega
  | succ q ih =>
    intro lo hi T hle h1 h2
    rw [Fin.sum_univ_succ] at h1 h2
    have hAB : ∑ i : Fin q, lo i.succ ≤ ∑ i : Fin q, hi i.succ :=
      Finset.sum_le_sum (fun i _ => hle i.succ)
    have h0 := hle 0
    obtain ⟨y, hy, hys⟩ := ih (fun i => lo i.succ) (fun i => hi i.succ)
      (T - max (lo 0) (T - ∑ i : Fin q, hi i.succ)) (fun i => hle i.succ) (by omega) (by omega)
    refine ⟨Fin.cons (max (lo 0) (T - ∑ i : Fin q, hi i.succ)) y, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero]; omega
      · simp only [Fin.cons_succ]; exact hy i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hys]; omega

theorem split (q E : ℕ) : ∀ (k : ℕ) (v : Fin q → ℕ), ∑ j, v j = E * k →
    ∃ g : Fin k → Fin q → ℕ, (∀ w, ∑ j, g w j = E) ∧ ∀ j, ∑ w, g w j = v j := by
  intro k
  induction k with
  | zero =>
    intro v hv
    refine ⟨fun w => w.elim0, fun w => w.elim0, fun j => ?_⟩
    rw [mul_zero, Finset.sum_eq_zero_iff] at hv
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact (hv j (Finset.mem_univ j)).symm
  | succ k ih =>
    intro v hv
    obtain ⟨a, ha, has⟩ := interm q (fun _ => 0) v E (fun _ => Nat.zero_le _) (by simp)
      (by rw [hv]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos k))
    have hsub : ∑ j, (v j - a j) + ∑ j, a j = ∑ j, v j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (ha j).2)
    obtain ⟨g, hg1, hg2⟩ := ih (fun j => v j - a j) (by
      have e : E * (k+1) = E * k + E := by ring
      rw [hv, e, has] at hsub
      exact Nat.add_right_cancel hsub)
    refine ⟨Fin.cons a g, ?_, ?_⟩
    · intro w
      refine Fin.cases ?_ (fun i => ?_) w
      · simpa using has
      · simpa using hg1 i
    · intro j
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hg2 j]
      have := (ha j).2
      omega

theorem shift (b : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ range (b+1), 2^(b+1-1-i) * f i = 2 * ∑ i ∈ range b, 2^(b-1-i) * f i + f b := by
  rw [sum_range_succ, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    rw [show b+1-1-i = (b-1-i)+1 by omega, pow_succ]
    ring
  · simp

theorem tele (u : ℕ → ℕ) (h0 : u 0 = 1) : ∀ b, (∀ i < b, u (i+1) ≤ 2*u i) →
    u b ≤ 2^b ∧ ∑ i ∈ range b, 2^(b-1-i) * (2*u i - u (i+1)) = 2^b - u b := by
  intro b
  induction b with
  | zero => intro _; simp [h0]
  | succ b ih =>
    intro hs
    obtain ⟨h1, h2⟩ := ih (fun i hi => hs i (by omega))
    have h3 := hs b (by omega)
    refine ⟨by rw [pow_succ]; omega, ?_⟩
    rw [shift b (fun i => 2*u i - u (i+1))]
    rw [h2, pow_succ]
    omega

theorem sumA (E q : ℕ) (u : ℕ → ℕ) (h0 : u 0 = 1) (c : ℕ → Fin q → ℕ) (b : ℕ)
    (hs : ∀ i < b, u (i+1) ≤ 2*u i) (hc : ∀ i < b, ∑ j, c i j = E * (2*u i - u (i+1))) :
    ∑ j, ∑ i ∈ range b, 2^(b-1-i) * c i j = E * (2^b - u b) := by
  rw [Finset.sum_comm, ← (tele u h0 b hs).2, mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [← mul_sum, hc i hi]
  ring

theorem div2 (m p b : ℕ) (hb : b < p) : 2 * (m / 2^(p-b)) ≤ m / 2^(p-(b+1)) := by
  rw [show p - b = (p-(b+1)) + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

theorem nec (p E q : ℕ) (hE : 0 < E) (M : Fin q → ℕ) (u : ℕ → ℕ) (h0 : u 0 = 1)
    (hs : ∀ b < p, u (b+1) ≤ 2*u b) (c : ℕ → Fin q → ℕ)
    (hc : ∀ i < p, ∑ j, c i j = E * (2*u i - u (i+1)))
    (hM : ∀ j, ∑ i ∈ range p, 2^(p-1-i) * c i j = M j) :
    ∀ b ≤ p, 2^b - (∑ j, M j / 2^(p-b)) / E ≤ u b := by
  intro b hb
  have hA : ∀ j, ∑ i ∈ range b, 2^(b-1-i) * c i j ≤ M j / 2^(p-b) := by
    intro j
    rw [Nat.le_div_iff_mul_le (by positivity), ← hM j, sum_mul]
    calc ∑ i ∈ range b, 2^(b-1-i) * c i j * 2^(p-b)
        = ∑ i ∈ range b, 2^(p-1-i) * c i j := by
          apply sum_congr rfl; intro i hi; rw [mem_range] at hi
          rw [show p-1-i = (b-1-i) + (p-b) by omega, pow_add]; ring
      _ ≤ ∑ i ∈ range p, 2^(p-1-i) * c i j :=
          sum_le_sum_of_subset (Finset.range_mono hb)
  have hsum := sumA E q u h0 c b (fun i hi => hs i (by omega)) (fun i hi => hc i (by omega))
  have hle : E * (2^b - u b) ≤ ∑ j, M j / 2^(p-b) := by
    rw [← hsum]; exact sum_le_sum (fun j _ => hA j)
  have : 2^b - u b ≤ (∑ j, M j / 2^(p-b)) / E :=
    (Nat.le_div_iff_mul_le hE).2 (by rw [mul_comm]; exact hle)
  omega

theorem suff (p E q : ℕ) (hE : 0 < E) (M : Fin q → ℕ) (hMs : ∑ j, M j = (2^p-1)*E)
    (u : ℕ → ℕ) (h0 : u 0 = 1) (hp1 : u p = 1)
    (hs : ∀ b < p, u (b+1) ≤ 2*u b)
    (hb : ∀ b ≤ p, 2^b - (∑ j, M j / 2^(p-b)) / E ≤ u b) :
    ∃ c : ℕ → Fin q → ℕ, (∀ i < p, ∑ j, c i j = E * (2*u i - u (i+1))) ∧
      ∀ j, ∑ i ∈ range p, 2^(p-1-i) * c i j = M j := by
  have hcap : ∀ b ≤ p, E * (2^b - u b) ≤ ∑ j, M j / 2^(p-b) := by
    intro b hbp
    have h1 := hb b hbp
    have h2 := Nat.mul_div_le (∑ j, M j / 2^(p-b)) E
    have h3 : 2^b - u b ≤ (∑ j, M j / 2^(p-b)) / E := by
      generalize (∑ j, M j / 2^(p-b)) / E = Y at h1 ⊢
      omega
    calc E * (2^b - u b) ≤ E * ((∑ j, M j / 2^(p-b)) / E) := Nat.mul_le_mul_left _ h3
      _ ≤ _ := h2
  have key : ∀ b ≤ p, ∃ c : ℕ → Fin q → ℕ, (∀ i < b, ∑ j, c i j = E * (2*u i - u (i+1))) ∧
      ∀ j, ∑ i ∈ range b, 2^(b-1-i) * c i j ≤ M j / 2^(p-b) := by
    intro b
    induction b with
    | zero =>
      intro _
      exact ⟨fun _ _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _), fun j => by simp⟩
    | succ b ih =>
      intro hbp
      obtain ⟨c, hc1, hc2⟩ := ih (by omega)
      have ht := tele u h0 b (fun i hi => hs i (by omega))
      have hs' := hs b (by omega)
      have hsA := sumA E q u h0 c b (fun i hi => hs i (by omega)) hc1
      obtain ⟨A, hAdef⟩ : ∃ A : Fin q → ℕ, ∀ j, A j = ∑ i ∈ range b, 2^(b-1-i) * c i j :=
        ⟨_, fun j => rfl⟩
      have hsA' : ∑ j, A j = E * (2^b - u b) := by simp only [hAdef]; exact hsA
      have hsA2 : ∑ j, 2 * A j = 2 * (E * (2^b - u b)) := by rw [← mul_sum, hsA']
      obtain ⟨x, hx, hxs⟩ := interm q (fun j => 2 * A j)
        (fun j => M j / 2^(p-(b+1))) (E * (2^(b+1) - u (b+1)))
        (fun j => le_trans (Nat.mul_le_mul_left 2 (hAdef j ▸ hc2 j)) (div2 _ p b (by omega)))
        (by
          rw [hsA2]
          calc 2 * (E * (2^b - u b)) = E * (2 * (2^b - u b)) := by ring
            _ ≤ E * (2^(b+1) - u (b+1)) := Nat.mul_le_mul_left _ (by rw [pow_succ]; omega))
        (hcap (b+1) hbp)
      have hrow : ∑ j, (x j - 2 * A j) = E * (2*u b - u (b+1)) := by
        have e1 : ∑ j, (x j - 2 * A j) + ∑ j, 2 * A j = ∑ j, x j := by
          rw [← sum_add_distrib]; exact sum_congr rfl (fun j _ => Nat.sub_add_cancel (hx j).1)
        rw [hsA2, hxs] at e1
        have e2 : 2^(b+1) - u (b+1) = 2 * (2^b - u b) + (2*u b - u (b+1)) := by
          rw [pow_succ]; omega
        have e3 : E * (2 * (2^b - u b)) = 2 * (E * (2^b - u b)) := by ring
        rw [e2, mul_add, e3, add_comm (2 * (E * (2^b - u b)))] at e1
        exact Nat.add_right_cancel e1
      refine ⟨fun i j => if i = b then x j - 2 * A j else c i j, ?_, ?_⟩
      · intro i hi
        by_cases hib : i = b
        · subst hib
          simpa using hrow
        · simp only [hib, if_false]
          exact hc1 i (by omega)
      · intro j
        rw [shift b (fun i => if i = b then x j - 2 * A j else c i j)]
        have e : ∑ i ∈ range b, 2^(b-1-i) * (if i = b then x j - 2 * A j else c i j) = A j := by
          rw [hAdef]; apply sum_congr rfl; intro i hi; rw [mem_range] at hi
          rw [if_neg (by omega)]
        rw [e, if_pos rfl]
        have := hx j
        omega
  obtain ⟨c, hc1, hc2⟩ := key p le_rfl
  refine ⟨c, hc1, ?_⟩
  have hsum := sumA E q u h0 c p hs hc1
  rw [hp1] at hsum
  have hle : ∀ j ∈ univ, ∑ i ∈ range p, 2^(p-1-i) * c i j ≤ M j := by
    intro j _
    have := hc2 j
    rw [Nat.sub_self, pow_zero, Nat.div_one] at this
    exact this
  have heq := (sum_eq_sum_iff_of_le hle).1 (by rw [hsum, hMs, mul_comm])
  exact fun j => heq j (mem_univ j)

theorem fits_to (p E q : ℕ) (M : Fin q → ℕ) (u : ℕ → ℕ)
    (h : (i : Fin p) → Fin (2*u i.val-u (i.val+1)) → Fin q → ℕ)
    (h1 : ∀ i w, (∑ j, h i w j) = E)
    (h2 : ∀ j, (∑ i : Fin p, 2^(p-1-i.val) * ∑ w, h i w j) = M j) :
    ∃ c : ℕ → Fin q → ℕ, (∀ i < p, ∑ j, c i j = E * (2*u i - u (i+1))) ∧
      ∀ j, ∑ i ∈ range p, 2^(p-1-i) * c i j = M j := by
  refine ⟨fun i j => if hi : i < p then ∑ w, h ⟨i, hi⟩ w j else 0, ?_, ?_⟩
  · intro i hi
    simp only [dif_pos hi]
    rw [sum_comm]
    simp only [h1, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    exact mul_comm _ _
  · intro j
    rw [← h2 j, ← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    beta_reduce
    rw [dif_pos i.isLt]

theorem to_fits (p E q : ℕ) (M : Fin q → ℕ) (u : ℕ → ℕ) (c : ℕ → Fin q → ℕ)
    (hc : ∀ i < p, ∑ j, c i j = E * (2*u i - u (i+1)))
    (hM : ∀ j, ∑ i ∈ range p, 2^(p-1-i) * c i j = M j) :
    ∃ h : (i : Fin p) → Fin (2*u i.val-u (i.val+1)) → Fin q → ℕ,
      (∀ i w, (∑ j, h i w j) = E) ∧
      ∀ j, (∑ i : Fin p, 2^(p-1-i.val) * ∑ w, h i w j) = M j := by
  have := fun i : Fin p => split q E (2*u i.val - u (i.val+1)) (c i.val) (hc i.val i.isLt)
  choose g hg1 hg2 using this
  refine ⟨g, hg1, fun j => ?_⟩
  rw [← hM j, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  rw [hg2]

theorem best0 (p E q : ℕ) (hE : 0 < E) (M : Fin q → ℕ) (hMs : ∑ j, M j = (2^p-1)*E) :
    2^0 - (∑ j, M j / 2^(p-0))/E = 1 := by
  have hlt : ∑ j, M j / 2^(p-0) < E := by
    have h1 : 2^p * ∑ j, M j / 2^(p-0) ≤ ∑ j, M j := by
      rw [mul_sum]; exact sum_le_sum (fun j _ => by rw [Nat.sub_zero]; exact Nat.mul_div_le _ _)
    have h2 : 1 ≤ 2^p := Nat.one_le_two_pow
    by_contra hc
    push_neg at hc
    have h4 := Nat.mul_le_mul_left (2^p) hc
    rw [hMs] at h1
    have h3 : (2^p - 1) * E < 2^p * E := Nat.mul_lt_mul_of_pos_right (by omega) hE
    exact absurd (h4.trans h1) (not_le.2 h3)
  rw [Nat.div_eq_of_lt hlt]
  simp

theorem bestp (p E q : ℕ) (hE : 0 < E) (M : Fin q → ℕ) (hMs : ∑ j, M j = (2^p-1)*E) :
    2^p - (∑ j, M j / 2^(p-p))/E = 1 := by
  simp only [Nat.sub_self, pow_zero, Nat.div_one]
  rw [hMs, Nat.mul_div_cancel _ hE]
  have : 1 ≤ 2^p := Nat.one_le_two_pow
  omega

theorem beststep (p E q : ℕ) (M : Fin q → ℕ) (b : ℕ) (hb : b < p) :
    2^(b+1) - (∑ j, M j / 2^(p-(b+1)))/E ≤ 2 * (2^b - (∑ j, M j / 2^(p-b))/E) := by
  have h1 : 2 * ∑ j, M j / 2^(p-b) ≤ ∑ j, M j / 2^(p-(b+1)) := by
    rw [mul_sum]; exact sum_le_sum (fun j _ => div2 _ p b hb)
  have h2 : 2 * ((∑ j, M j / 2^(p-b))/E) ≤ (∑ j, M j / 2^(p-(b+1)))/E :=
    (Nat.mul_div_le_mul_div_assoc _ _ _).trans (Nat.div_le_div_right h1)
  rw [pow_succ]
  omega

end PEqualNP.Outside.L_lib_842

open PEqualNP.Outside.L_lib_842 in
theorem PEqualNP.Outside.L_lib_842 : 
∀ (p E q : ℕ), 0 < p → 0 < E → ∀ M : Fin q → ℕ,
  (∑ j, M j) = (2^p-1)*E →
  let cap := fun b : ℕ => ∑ j, M j / 2^(p-b)
  let best := fun b : ℕ => 2^b-cap b/E
  let shape := fun u : ℕ → ℕ =>
    u 0 = 1 ∧ u p = 1 ∧ ∀ b < p, u (b+1) ≤ 2*u b
  let fits := fun u : ℕ → ℕ =>
    ∃ h : (i : Fin p) → Fin (2*u i.val-u (i.val+1)) → Fin q → ℕ,
      (∀ i w, (∑ j, h i w j) = E) ∧
      ∀ j, (∑ i : Fin p, 2^(p-1-i.val) * ∑ w, h i w j) = M j
  (∀ u, shape u → (fits u ↔ ∀ b ≤ p, best b ≤ u b)) ∧ shape best ∧ fits best := by
  intro p E q hp hE M hMs
  dsimp only
  refine ⟨fun u hu => ⟨fun ⟨h, h1, h2⟩ => ?_, fun hb => ?_⟩, ⟨best0 p E q hE M hMs, bestp p E q hE M hMs,
    fun b hb => beststep p E q M b hb⟩, ?_⟩
  · obtain ⟨c, hc1, hc2⟩ := fits_to p E q M u h h1 h2
    exact nec p E q hE M u hu.1 hu.2.2 c hc1 hc2
  · obtain ⟨c, hc1, hc2⟩ := suff p E q hE M hMs u hu.1 hu.2.1 hu.2.2 hb
    exact to_fits p E q M u c hc1 hc2
  · obtain ⟨c, hc1, hc2⟩ := suff p E q hE M hMs _ (best0 p E q hE M hMs) (bestp p E q hE M hMs)
      (fun b hb => beststep p E q M b hb) (fun b _ => le_rfl)
    exact to_fits p E q M _ c hc1 hc2

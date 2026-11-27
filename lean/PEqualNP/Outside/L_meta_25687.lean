import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25687_aux

private abbrev V := Fin 2 → ZMod 2

private def sw (v : V) : V := ![v 1, v 0]

private lemma add_self_z2 (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma add_self_V (v : V) : v + v = 0 := by
  ext i
  exact add_self_z2 (v i)

private lemma eq_of_add_eq_zero_V {u v : V} (h : u + v = 0) : u = v := by
  have hv := add_self_V v
  calc
    u = u + (v + v) := by rw [hv, add_zero]
    _ = (u + v) + v := by rw [add_assoc]
    _ = v := by rw [h, zero_add]

private lemma sw_sw (v : V) : sw (sw v) = v := by
  ext i
  fin_cases i <;> rfl

private lemma sw_add (u v : V) : sw (u + v) = sw u + sw v := by
  ext i
  fin_cases i <;> rfl

private lemma dot_add_left_V (u v w : V) :
    dotProduct (u + v) w = dotProduct u w + dotProduct v w := by
  simp only [dotProduct, Fin.sum_univ_two, Pi.add_apply]
  ring

private lemma dot_add_right_V (u v w : V) :
    dotProduct u (v + w) = dotProduct u v + dotProduct u w := by
  simp only [dotProduct, Fin.sum_univ_two, Pi.add_apply]
  ring

private lemma dot_sw_self (v : V) : dotProduct v (sw v) = 0 := by
  simp only [dotProduct, sw, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  generalize v 0 = a
  generalize v 1 = b
  fin_cases a <;> fin_cases b <;> decide

private lemma dot_sw_left_self (v : V) : dotProduct (sw v) v = 0 := by
  have h := dot_sw_self (sw v)
  rwa [sw_sw] at h

private lemma xor_decide_eq (a b : ZMod 2) :
    Bool.xor (decide (a = 1)) (decide (b = 1)) = decide (a + b = 1) := by
  fin_cases a <;> fin_cases b <;> decide

private lemma decide_eq_one_false_iff (z : ZMod 2) :
    decide (z = 1) = false ↔ z = 0 := by
  revert z
  decide

private lemma xor4_iff (x1 x2 y1 y2 : V) (f1 f2 g1 g2 : ZMod 2) :
    Bool.xor
      (Bool.xor (decide (dotProduct x1 y1 + f1 + g1 = 1))
                (decide (dotProduct x2 y2 + f2 + g2 = 1)))
      (Bool.xor (decide (dotProduct x1 y2 + f1 + g2 = 1))
                (decide (dotProduct x2 y1 + f2 + g1 = 1))) = false ↔
    dotProduct (x1 + x2) (y1 + y2) = 0 := by
  rw [xor_decide_eq, xor_decide_eq, xor_decide_eq]
  have hsum :
      (dotProduct x1 y1 + f1 + g1) + (dotProduct x2 y2 + f2 + g2) +
        ((dotProduct x1 y2 + f1 + g2) + (dotProduct x2 y1 + f2 + g1)) =
      dotProduct (x1 + x2) (y1 + y2) := by
    have hf1 := add_self_z2 f1
    have hf2 := add_self_z2 f2
    have hg1 := add_self_z2 g1
    have hg2 := add_self_z2 g2
    simp only [dotProduct, Fin.sum_univ_two, Pi.add_apply]
    linear_combination hf1 + hf2 + hg1 + hg2
  rw [hsum]
  exact decide_eq_one_false_iff _

private lemma line_dot_zero_aux :
    ∀ a0 a1 u0 u1 w0 w1 : ZMod 2,
      ¬ (a0 = 0 ∧ a1 = 0) →
      a0 * u0 + a1 * u1 = 0 →
      a1 * w0 + a0 * w1 = 0 →
      u0 * w0 + u1 * w1 = 0 := by
  decide

private lemma line_dot_zero (a du dw : V) (ha : a ≠ 0)
    (h1 : dotProduct a du = 0) (h2 : dotProduct (sw a) dw = 0) :
    dotProduct du dw = 0 := by
  have ha' : ¬ (a 0 = 0 ∧ a 1 = 0) := by
    intro ⟨h0, h1⟩
    apply ha
    ext i
    fin_cases i
    · exact h0
    · exact h1
  simp only [dotProduct, sw, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2 ⊢
  exact line_dot_zero_aux (a 0) (a 1) (du 0) (du 1) (dw 0) (dw 1) ha' h1 h2

private lemma ortho_basis_zero_aux :
    ∀ a0 a1 b0 b1 e0 e1 : ZMod 2,
      ¬ (a0 = 0 ∧ a1 = 0) →
      ¬ (b0 = 0 ∧ b1 = 0) →
      ¬ (a0 = b0 ∧ a1 = b1) →
      a0 * e0 + a1 * e1 = 0 →
      b0 * e0 + b1 * e1 = 0 →
      e0 = 0 ∧ e1 = 0 := by
  decide

private lemma ortho_basis_zero (u1 u2 e : V)
    (h1 : u1 ≠ 0) (h2 : u2 ≠ 0) (hne : u1 ≠ u2)
    (he1 : dotProduct u1 e = 0) (he2 : dotProduct u2 e = 0) :
    e = 0 := by
  have h1' : ¬ (u1 0 = 0 ∧ u1 1 = 0) := by
    intro ⟨p, q⟩; apply h1; ext i; fin_cases i; exact p; exact q
  have h2' : ¬ (u2 0 = 0 ∧ u2 1 = 0) := by
    intro ⟨p, q⟩; apply h2; ext i; fin_cases i; exact p; exact q
  have hne' : ¬ (u1 0 = u2 0 ∧ u1 1 = u2 1) := by
    intro ⟨p, q⟩; apply hne; ext i; fin_cases i; exact p; exact q
  simp only [dotProduct, Fin.sum_univ_two] at he1 he2
  obtain ⟨e0, e1⟩ := ortho_basis_zero_aux (u1 0) (u1 1) (u2 0) (u2 1) (e 0) (e 1)
    h1' h2' hne' he1 he2
  ext i
  fin_cases i
  · exact e0
  · exact e1

private lemma basis_iso_dichotomy_aux :
    ∀ u10 u11 u20 u21 w10 w11 w20 w21 : ZMod 2,
      ¬ (u10 = 0 ∧ u11 = 0) →
      ¬ (u20 = 0 ∧ u21 = 0) →
      ¬ (u10 = u20 ∧ u11 = u21) →
      u10 * w10 + u11 * w11 = 0 →
      u20 * w20 + u21 * w21 = 0 →
      (u10 + u20) * (w10 + w20) + (u11 + u21) * (w11 + w21) = 0 →
      ((w10 = 0 ∧ w11 = 0) ∧ (w20 = 0 ∧ w21 = 0)) ∨
      ((w10 = u11 ∧ w11 = u10) ∧ (w20 = u21 ∧ w21 = u20)) := by
  decide

private lemma basis_iso_dichotomy (u1 u2 w1 w2 : V)
    (h1 : u1 ≠ 0) (h2 : u2 ≠ 0) (hne : u1 ≠ u2)
    (hd1 : dotProduct u1 w1 = 0)
    (hd2 : dotProduct u2 w2 = 0)
    (hd12 : dotProduct (u1 + u2) (w1 + w2) = 0) :
    (w1 = 0 ∧ w2 = 0) ∨ (w1 = sw u1 ∧ w2 = sw u2) := by
  have h1' : ¬ (u1 0 = 0 ∧ u1 1 = 0) := by
    intro ⟨p, q⟩; apply h1; ext i; fin_cases i; exact p; exact q
  have h2' : ¬ (u2 0 = 0 ∧ u2 1 = 0) := by
    intro ⟨p, q⟩; apply h2; ext i; fin_cases i; exact p; exact q
  have hne' : ¬ (u1 0 = u2 0 ∧ u1 1 = u2 1) := by
    intro ⟨p, q⟩; apply hne; ext i; fin_cases i; exact p; exact q
  simp only [dotProduct, Fin.sum_univ_two, Pi.add_apply] at hd1 hd2 hd12
  rcases basis_iso_dichotomy_aux (u1 0) (u1 1) (u2 0) (u2 1) (w1 0) (w1 1) (w2 0) (w2 1)
      h1' h2' hne' hd1 hd2 hd12 with ⟨⟨a, b⟩, ⟨c, d⟩⟩ | ⟨⟨a, b⟩, ⟨c, d⟩⟩
  · left
    exact ⟨by ext i; fin_cases i; exact a; exact b,
           by ext i; fin_cases i; exact c; exact d⟩
  · right
    exact ⟨by ext i; fin_cases i; exact a; exact b,
           by ext i; fin_cases i; exact c; exact d⟩

private lemma three_distinct_ortho_zero (x a b c e : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : dotProduct (x + a) e = 0)
    (hb : dotProduct (x + b) e = 0)
    (hc : dotProduct (x + c) e = 0) : e = 0 := by
  have hdiff : ∀ p q : V, p ≠ q → x + p ≠ x + q := by
    intro p q hpq heq
    apply hpq
    have := congrArg (fun v => x + v) heq
    rw [← add_assoc, ← add_assoc, add_self_V, zero_add, zero_add] at this
    exact this
  have hne0 : ∀ p : V, x ≠ p → x + p ≠ 0 := by
    intro p hxp h0
    exact hxp (eq_of_add_eq_zero_V h0)
  by_cases hxa : x = a
  · exact ortho_basis_zero (x + b) (x + c) e
      (hne0 b (by rwa [hxa])) (hne0 c (by rwa [hxa])) (hdiff b c hbc) hb hc
  · by_cases hxb : x = b
    · exact ortho_basis_zero (x + a) (x + c) e
        (hne0 a hxa) (hne0 c (by rwa [hxb])) (hdiff a c hac) ha hc
    · exact ortho_basis_zero (x + a) (x + b) e
        (hne0 a hxa) (hne0 b hxb) (hdiff a b hab) ha hb

private lemma classify_iso (S : Finset (V × V))
    (hS : ∀ p ∈ S, ∀ q ∈ S, dotProduct (p.1 + q.1) (p.2 + q.2) = 0) :
    (∃ v : V, ∀ p ∈ S, p.1 = v) ∨
    (∃ w : V, ∀ p ∈ S, p.2 = w) ∨
    (∃ (a : V) (s h : ZMod 2), a ≠ 0 ∧
      ∀ p ∈ S, dotProduct a p.1 = s ∧ dotProduct (sw a) p.2 = h) ∨
    (∃ b : V, ∀ p ∈ S, p.2 = sw p.1 + b) := by
  by_cases hempty : S = ∅
  · left
    exact ⟨0, fun p hp => by simp [hempty] at hp⟩
  obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  by_cases hrow : ∀ p ∈ S, p.1 = p0.1
  · left
    exact ⟨p0.1, hrow⟩
  by_cases hcol : ∀ p ∈ S, p.2 = p0.2
  · right; left
    exact ⟨p0.2, hcol⟩
  push_neg at hrow
  obtain ⟨p1, hp1, hp1_ne⟩ := hrow
  by_cases hline : ∀ p ∈ S, p.1 = p0.1 ∨ p.1 = p1.1
  · right; right; left
    let du : V := p1.1 + p0.1
    have hdu_ne : du ≠ 0 := fun h0 => hp1_ne (eq_of_add_eq_zero_V h0)
    have hsw_ne : sw du ≠ 0 := by
      intro h0
      apply hdu_ne
      have := congrArg sw h0
      rw [sw_sw] at this
      exact this.trans (by ext i; fin_cases i <;> rfl)
    refine ⟨sw du, dotProduct (sw du) p0.1, dotProduct du p0.2, hsw_ne, ?_⟩
    intro p hp
    rw [sw_sw]
    constructor
    · rcases hline p hp with h | h
      · rw [h]
      · rw [h]
        have hp1_eq : p1.1 = du + p0.1 := by
          dsimp only [du]
          rw [add_assoc, add_self_V, add_zero]
        rw [hp1_eq, dot_add_right_V, dot_sw_left_self, zero_add]
    · have hdiff0 : dotProduct du (p.2 + p0.2) = 0 := by
        rcases hline p hp with h | h
        · have h1 := hS p hp p1 hp1
          have h2 := hS p0 hp0 p1 hp1
          rw [h, add_comm p0.1 p1.1] at h1
          rw [add_comm p0.1 p1.1] at h2
          have hsum : dotProduct du (p.2 + p1.2) + dotProduct du (p0.2 + p1.2) = 0 := by
            rw [h1, h2, add_zero]
          have hvec : (p.2 + p1.2) + (p0.2 + p1.2) = p.2 + p0.2 := by
            ext i
            have := add_self_z2 (p1.2 i)
            simp only [Pi.add_apply]
            linear_combination this
          rw [← dot_add_right_V, hvec] at hsum
          exact hsum
        · have h1 := hS p hp p0 hp0
          rwa [h] at h1
      rw [dot_add_right_V] at hdiff0
      have hself := add_self_z2 (dotProduct du p0.2)
      linear_combination hdiff0 - hself
  · push_neg at hline
    obtain ⟨p2, hp2, hp2_ne0, hp2_ne1⟩ := hline
    let u1 : V := p1.1 + p0.1
    let u2 : V := p2.1 + p0.1
    let w1 : V := p1.2 + p0.2
    let w2 : V := p2.2 + p0.2
    have hu1 : u1 ≠ 0 := fun h0 => hp1_ne (eq_of_add_eq_zero_V h0)
    have hu2 : u2 ≠ 0 := fun h0 => hp2_ne0 (eq_of_add_eq_zero_V h0)
    have hu12 : u1 ≠ u2 := by
      intro heq
      apply hp2_ne1
      have := congrArg (fun v => v + p0.1) heq
      dsimp only [u1, u2] at this
      rw [add_assoc, add_assoc, add_self_V, add_zero, add_zero] at this
      exact this.symm
    have hd1 : dotProduct u1 w1 = 0 := hS p1 hp1 p0 hp0
    have hd2 : dotProduct u2 w2 = 0 := hS p2 hp2 p0 hp0
    have hu_sum : u1 + u2 = p1.1 + p2.1 := by
      ext i
      have := add_self_z2 (p0.1 i)
      simp only [u1, u2, Pi.add_apply]
      linear_combination this
    have hw_sum : w1 + w2 = p1.2 + p2.2 := by
      ext i
      have := add_self_z2 (p0.2 i)
      simp only [w1, w2, Pi.add_apply]
      linear_combination this
    have hd12 : dotProduct (u1 + u2) (w1 + w2) = 0 := by
      rw [hu_sum, hw_sum]
      exact hS p1 hp1 p2 hp2
    rcases basis_iso_dichotomy u1 u2 w1 w2 hu1 hu2 hu12 hd1 hd2 hd12 with
        ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
    · right; left
      refine ⟨p0.2, fun p hp => ?_⟩
      have hp1_2 : p1.2 = p0.2 := eq_of_add_eq_zero_V hw1
      have hp2_2 : p2.2 = p0.2 := eq_of_add_eq_zero_V hw2
      have he : p.2 + p0.2 = 0 := by
        refine three_distinct_ortho_zero p.1 p0.1 p1.1 p2.1 (p.2 + p0.2)
          hp1_ne.symm hp2_ne0.symm hp2_ne1.symm ?_ ?_ ?_
        · exact hS p hp p0 hp0
        · have h := hS p hp p1 hp1; rwa [hp1_2] at h
        · have h := hS p hp p2 hp2; rwa [hp2_2] at h
      exact eq_of_add_eq_zero_V he
    · right; right; right
      let b : V := p0.2 + sw p0.1
      have hq0 : p0.2 = sw p0.1 + b := by
        dsimp only [b]
        rw [add_comm (sw p0.1), add_assoc, add_self_V, add_zero]
      have hq1 : p1.2 = sw p1.1 + b := by
        have h1 : p1.2 = w1 + p0.2 := by
          dsimp only [w1]; rw [add_assoc, add_self_V, add_zero]
        rw [h1, hw1, hq0]
        dsimp only [u1]
        rw [sw_add]
        ext i
        have := add_self_z2 (sw p0.1 i)
        simp only [Pi.add_apply]
        linear_combination this
      have hq2 : p2.2 = sw p2.1 + b := by
        have h2 : p2.2 = w2 + p0.2 := by
          dsimp only [w2]; rw [add_assoc, add_self_V, add_zero]
        rw [h2, hw2, hq0]
        dsimp only [u2]
        rw [sw_add]
        ext i
        have := add_self_z2 (sw p0.1 i)
        simp only [Pi.add_apply]
        linear_combination this
      refine ⟨b, fun p hp => ?_⟩
      have hstep : ∀ q ∈ S, q.2 = sw q.1 + b →
          dotProduct (p.1 + q.1) (p.2 + (sw p.1 + b)) = 0 := by
        intro q hq hqb
        have hdot := hS p hp q hq
        have hvec : p.2 + (sw p.1 + b) = (p.2 + q.2) + sw (p.1 + q.1) := by
          rw [hqb, sw_add]
          ext i
          have h1 := add_self_z2 (sw q.1 i)
          simp only [Pi.add_apply]
          linear_combination -h1
        rw [hvec, dot_add_right_V, hdot, dot_sw_self, add_zero]
      have he : p.2 + (sw p.1 + b) = 0 :=
        three_distinct_ortho_zero p.1 p0.1 p1.1 p2.1 (p.2 + (sw p.1 + b))
          hp1_ne.symm hp2_ne0.symm hp2_ne1.symm
          (hstep p0 hp0 hq0) (hstep p1 hp1 hq1) (hstep p2 hp2 hq2)
      exact eq_of_add_eq_zero_V he

private lemma extend_bij {n : ℕ} (A B : Finset (Fin n))
    (e : {i : Fin n // i ∈ A} ≃ {j : Fin n // j ∈ B}) :
    ∃ π : Equiv.Perm (Fin n), ∀ (i : Fin n) (hi : i ∈ A), π i = (e ⟨i, hi⟩).val := by
  have hcard_AB : Fintype.card {i : Fin n // i ∈ A} = Fintype.card {j : Fin n // j ∈ B} :=
    Fintype.card_congr e
  have hcard_compl :
      Fintype.card {i : Fin n // ¬ i ∈ A} = Fintype.card {j : Fin n // ¬ j ∈ B} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard_AB]
  let e' : {i : Fin n // ¬ i ∈ A} ≃ {j : Fin n // ¬ j ∈ B} :=
    Fintype.equivOfCardEq hcard_compl
  let π : Equiv.Perm (Fin n) :=
    (Equiv.sumCompl (· ∈ A)).symm.trans ((Equiv.sumCongr e e').trans (Equiv.sumCompl (· ∈ B)))
  refine ⟨π, fun i hi => ?_⟩
  simp [π, Equiv.sumCompl_symm_apply_of_pos hi]

end PEqualNP.Outside.L_meta_25687_aux

theorem PEqualNP.Outside.L_meta_25687 : (∀ (n t : ℕ),
  let V := Fin 2 → ZMod 2
  let swap := fun (v : V) => ![v 1, v 0]
  ∀ (x y : Fin n → V) (f g : Fin n → ZMod 2),
    let G := fun row col => decide (dotProduct (x row) (y col) + f row + g col = 1)
    let mult := fun (bank : Fin n → V) (point : V) =>
      ((Finset.univ : Finset (Fin n)).filter (fun name => bank name = point)).card
    let line := fun (bank : Fin n → V) (normal : V) (bit : ZMod 2) =>
      ((Finset.univ : Finset (Fin n)).filter (fun label => dotProduct normal (bank label) = bit)).card
    (∃ (π : Equiv.Perm (Fin n)) (K : Finset (Fin n)), n ≤ K.card + t ∧
      ∀ i ∈ K, ∀ j ∈ K,
        Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) = false) ↔
    (∃ v : V, n ≤ t + mult x v) ∨ (∃ w : V, n ≤ t + mult y w) ∨
    (∃ (a : V) (s h : ZMod 2), a ≠ 0 ∧ n ≤ t + min (line x a s) (line y (swap a) h)) ∨
    (∃ b : V, n ≤ t + ∑ z : V, min (mult x z) (mult y (swap z + b)))) := by
  intro n t V swap x y f g G mult line
  constructor
  · rintro ⟨π, K, hcard, hxor⟩
    have hdot : ∀ i ∈ K, ∀ j ∈ K, dotProduct (x i + x j) (y (π i) + y (π j)) = 0 := by
      intro i hi j hj
      exact (PEqualNP.Outside.L_meta_25687_aux.xor4_iff (x i) (x j) (y (π i)) (y (π j))
        (f i) (f j) (g (π i)) (g (π j))).mp (hxor i hi j hj)
    let S : Finset (V × V) := K.image (fun i => (x i, y (π i)))
    have hS : ∀ p ∈ S, ∀ q ∈ S, dotProduct (p.1 + q.1) (p.2 + q.2) = 0 := by
      intro p hp q hq
      rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
      rcases Finset.mem_image.mp hq with ⟨j, hj, rfl⟩
      exact hdot i hi j hj
    rcases PEqualNP.Outside.L_meta_25687_aux.classify_iso S hS with
        ⟨v, hv⟩ | ⟨w, hw⟩ | ⟨a, s, h, ha, hline⟩ | ⟨b, hb⟩
    · left
      refine ⟨v, ?_⟩
      have hsub : K ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => x i = v) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hv (x i, y (π i)) (Finset.mem_image_of_mem _ hi)
      have hle : K.card ≤ mult x v := Finset.card_le_card hsub
      omega
    · right; left
      refine ⟨w, ?_⟩
      have hsub : K.image π ⊆ (Finset.univ : Finset (Fin n)).filter (fun j => y j = w) := by
        intro j hj
        rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hw (x i, y (π i)) (Finset.mem_image_of_mem _ hi)
      have hle : K.card ≤ mult y w := by
        calc
          K.card = (K.image π).card := (Finset.card_image_of_injective K π.injective).symm
          _ ≤ mult y w := Finset.card_le_card hsub
      omega
    · right; right; left
      refine ⟨a, s, h, ha, ?_⟩
      have hsub1 : K ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => dotProduct a (x i) = s) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hline (x i, y (π i)) (Finset.mem_image_of_mem _ hi)).1
      have hsub2 : K.image π ⊆
          (Finset.univ : Finset (Fin n)).filter (fun j => dotProduct (swap a) (y j) = h) := by
        intro j hj
        rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hline (x i, y (π i)) (Finset.mem_image_of_mem _ hi)).2
      have hle1 : K.card ≤ line x a s := Finset.card_le_card hsub1
      have hle2 : K.card ≤ line y (swap a) h := by
        calc
          K.card = (K.image π).card := (Finset.card_image_of_injective K π.injective).symm
          _ ≤ line y (swap a) h := Finset.card_le_card hsub2
      have hle : K.card ≤ min (line x a s) (line y (swap a) h) := le_min hle1 hle2
      omega
    · right; right; right
      refine ⟨b, ?_⟩
      have hpart : K.card = ∑ z : V, (K.filter (fun i => x i = z)).card := by
        have := Finset.card_eq_sum_card_fiberwise (f := x) (s := K) (t := (Finset.univ : Finset V))
          (fun _ _ => Finset.mem_univ _)
        exact this
      have hle : K.card ≤ ∑ z : V, min (mult x z) (mult y (swap z + b)) := by
        rw [hpart]
        refine Finset.sum_le_sum fun z _ => ?_
        have hsub1 : K.filter (fun i => x i = z) ⊆
            (Finset.univ : Finset (Fin n)).filter (fun i => x i = z) := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact hi.2
        have hsub2 : (K.filter (fun i => x i = z)).image π ⊆
            (Finset.univ : Finset (Fin n)).filter (fun j => y j = swap z + b) := by
          intro j hj
          rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          have hbi : y (π i) = swap (x i) + b :=
            hb (x i, y (π i)) (Finset.mem_image_of_mem _ hi.1)
          rw [hbi, hi.2]
        have hle1 : (K.filter (fun i => x i = z)).card ≤ mult x z := Finset.card_le_card hsub1
        have hle2 : (K.filter (fun i => x i = z)).card ≤ mult y (swap z + b) := by
          calc
            (K.filter (fun i => x i = z)).card = ((K.filter (fun i => x i = z)).image π).card :=
              (Finset.card_image_of_injective _ π.injective).symm
            _ ≤ mult y (swap z + b) := Finset.card_le_card hsub2
        exact le_min hle1 hle2
      omega
  · rintro (⟨v, hv⟩ | ⟨w, hw⟩ | ⟨a, s, h, ha, hline⟩ | ⟨b, hb⟩)
    · refine ⟨Equiv.refl (Fin n), (Finset.univ : Finset (Fin n)).filter (fun i => x i = v),
        by dsimp only [mult] at hv; omega, ?_⟩
      intro i hi j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      refine (PEqualNP.Outside.L_meta_25687_aux.xor4_iff (x i) (x j) (y i) (y j)
        (f i) (f j) (g i) (g j)).mpr ?_
      rw [hi, hj, PEqualNP.Outside.L_meta_25687_aux.add_self_V, zero_dotProduct]
    · refine ⟨Equiv.refl (Fin n), (Finset.univ : Finset (Fin n)).filter (fun i => y i = w),
        by dsimp only [mult] at hw; omega, ?_⟩
      intro i hi j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      refine (PEqualNP.Outside.L_meta_25687_aux.xor4_iff (x i) (x j) (y i) (y j)
        (f i) (f j) (g i) (g j)).mpr ?_
      rw [hi, hj, PEqualNP.Outside.L_meta_25687_aux.add_self_V, dotProduct_zero]
    · let A0 : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun i => dotProduct a (x i) = s)
      let B0 : Finset (Fin n) :=
        (Finset.univ : Finset (Fin n)).filter (fun j => dotProduct (swap a) (y j) = h)
      obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_left A0.card B0.card)
      obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_right A0.card B0.card)
      have hcard_eq : Fintype.card {i : Fin n // i ∈ A} = Fintype.card {j : Fin n // j ∈ B} := by
        simp [Fintype.card_coe, hAcard, hBcard]
      let e : {i : Fin n // i ∈ A} ≃ {j : Fin n // j ∈ B} := Fintype.equivOfCardEq hcard_eq
      obtain ⟨π, hπ⟩ := PEqualNP.Outside.L_meta_25687_aux.extend_bij A B e
      have hA_ge : n ≤ A.card + t := by
        have h1 : A0.card = line x a s := rfl
        have h2 : B0.card = line y (swap a) h := rfl
        omega
      refine ⟨π, A, hA_ge, ?_⟩
      intro i hi j hj
      refine (PEqualNP.Outside.L_meta_25687_aux.xor4_iff (x i) (x j) (y (π i)) (y (π j))
        (f i) (f j) (g (π i)) (g (π j))).mpr ?_
      have hiA : dotProduct a (x i) = s := (Finset.mem_filter.mp (hAsub hi)).2
      have hjA : dotProduct a (x j) = s := (Finset.mem_filter.mp (hAsub hj)).2
      have hπi : π i ∈ B := by rw [hπ i hi]; exact (e ⟨i, hi⟩).property
      have hπj : π j ∈ B := by rw [hπ j hj]; exact (e ⟨j, hj⟩).property
      have hiB : dotProduct (PEqualNP.Outside.L_meta_25687_aux.sw a) (y (π i)) = h :=
        (Finset.mem_filter.mp (hBsub hπi)).2
      have hjB : dotProduct (PEqualNP.Outside.L_meta_25687_aux.sw a) (y (π j)) = h :=
        (Finset.mem_filter.mp (hBsub hπj)).2
      refine PEqualNP.Outside.L_meta_25687_aux.line_dot_zero a (x i + x j) (y (π i) + y (π j)) ha ?_ ?_
      · rw [PEqualNP.Outside.L_meta_25687_aux.dot_add_right_V, hiA, hjA,
          PEqualNP.Outside.L_meta_25687_aux.add_self_z2]
      · rw [PEqualNP.Outside.L_meta_25687_aux.dot_add_right_V, hiB, hjB,
          PEqualNP.Outside.L_meta_25687_aux.add_self_z2]
    · have hsw_eq : ∀ v : V, swap v = PEqualNP.Outside.L_meta_25687_aux.sw v := fun _ => rfl
      let A0 : V → Finset (Fin n) := fun z =>
        (Finset.univ : Finset (Fin n)).filter (fun i => x i = z)
      let B0 : V → Finset (Fin n) := fun z =>
        (Finset.univ : Finset (Fin n)).filter (fun j => y j = swap z + b)
      have hchoose : ∀ z : V, ∃ (Az Bz : Finset (Fin n)),
          Az ⊆ A0 z ∧ Bz ⊆ B0 z ∧
          Az.card = min (A0 z).card (B0 z).card ∧
          Bz.card = min (A0 z).card (B0 z).card := by
        intro z
        obtain ⟨Az, hAz, hAzc⟩ := Finset.exists_subset_card_eq (Nat.min_le_left (A0 z).card (B0 z).card)
        obtain ⟨Bz, hBz, hBzc⟩ := Finset.exists_subset_card_eq (Nat.min_le_right (A0 z).card (B0 z).card)
        exact ⟨Az, Bz, hAz, hBz, hAzc, hBzc⟩
      choose A B hAsub hBsub hAcard hBcard using hchoose
      have hA_val : ∀ (z : V) (i : Fin n), i ∈ A z → x i = z :=
        fun z i hi => (Finset.mem_filter.mp (hAsub z hi)).2
      have hB_val : ∀ (z : V) (j : Fin n), j ∈ B z → y j = swap z + b :=
        fun z j hj => (Finset.mem_filter.mp (hBsub z hj)).2
      have hA_disj : Set.PairwiseDisjoint (Finset.univ : Finset V) A := by
        intro z1 _ z2 _ hne
        change Disjoint (A z1) (A z2)
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        exact hne ((hA_val z1 i hi1).symm.trans (hA_val z2 i hi2))
      let ez : ∀ z : V, {i : Fin n // i ∈ A z} ≃ {j : Fin n // j ∈ B z} := fun z =>
        Fintype.equivOfCardEq (by simp [Fintype.card_coe, hAcard z, hBcard z])
      let K : Finset (Fin n) := Finset.univ.biUnion A
      let L : Finset (Fin n) := Finset.univ.biUnion B
      have hK_mem : ∀ (i : Fin n), i ∈ K → i ∈ A (x i) := by
        intro i hi
        rcases Finset.mem_biUnion.mp hi with ⟨z, _, hiz⟩
        have hxz : x i = z := hA_val z i hiz
        rwa [hxz]
      have hL_mem : ∀ (j : Fin n), j ∈ L → j ∈ B (swap (y j + b)) := by
        intro j hj
        rcases Finset.mem_biUnion.mp hj with ⟨z, _, hjz⟩
        have hyz : y j = swap z + b := hB_val z j hjz
        have hz_eq : swap (y j + b) = z := by
          rw [hyz, add_assoc, PEqualNP.Outside.L_meta_25687_aux.add_self_V, add_zero, hsw_eq, hsw_eq,
            PEqualNP.Outside.L_meta_25687_aux.sw_sw]
        rwa [hz_eq]
      let e : {i : Fin n // i ∈ K} ≃ {j : Fin n // j ∈ L} :=
        { toFun := fun ⟨i, hi⟩ =>
            ⟨(ez (x i) ⟨i, hK_mem i hi⟩).val,
             Finset.mem_biUnion.mpr ⟨x i, Finset.mem_univ _, (ez (x i) ⟨i, hK_mem i hi⟩).property⟩⟩
          invFun := fun ⟨j, hj⟩ =>
            ⟨((ez (swap (y j + b))).symm ⟨j, hL_mem j hj⟩).val,
             Finset.mem_biUnion.mpr ⟨swap (y j + b), Finset.mem_univ _,
               ((ez (swap (y j + b))).symm ⟨j, hL_mem j hj⟩).property⟩⟩
          left_inv := fun ⟨i, hi⟩ => by
            apply Subtype.ext
            dsimp only
            set j := (ez (x i) ⟨i, hK_mem i hi⟩).val
            have hj_B : j ∈ B (x i) := (ez (x i) ⟨i, hK_mem i hi⟩).property
            have hyj : y j = swap (x i) + b := hB_val (x i) j hj_B
            have hidx : swap (y j + b) = x i := by
              rw [hyj, add_assoc, PEqualNP.Outside.L_meta_25687_aux.add_self_V, add_zero, hsw_eq, hsw_eq,
                PEqualNP.Outside.L_meta_25687_aux.sw_sw]
            have hpair : ∀ (z : V) (hz : z = x i) (hjz : j ∈ B z),
                ((ez z).symm ⟨j, hjz⟩).val = i := by
              intro z hz hjz
              subst hz
              have heq : (⟨j, hjz⟩ : {u : Fin n // u ∈ B (x i)}) = ez (x i) ⟨i, hK_mem i hi⟩ :=
                Subtype.ext rfl
              rw [heq, Equiv.symm_apply_apply]
            exact hpair _ hidx _
          right_inv := fun ⟨j, hj⟩ => by
            apply Subtype.ext
            dsimp only
            set z := swap (y j + b)
            set i := ((ez z).symm ⟨j, hL_mem j hj⟩).val
            have hi_A : i ∈ A z := ((ez z).symm ⟨j, hL_mem j hj⟩).property
            have hxi : x i = z := hA_val z i hi_A
            have hpair : ∀ (z' : V) (hz' : z' = z) (hiz' : i ∈ A z'),
                (ez z' ⟨i, hiz'⟩).val = j := by
              intro z' hz' hiz'
              subst hz'
              have heq : (⟨i, hiz'⟩ : {u : Fin n // u ∈ A z}) = (ez z).symm ⟨j, hL_mem j hj⟩ :=
                Subtype.ext rfl
              rw [heq, Equiv.apply_symm_apply]
            exact hpair _ hxi _ }
      obtain ⟨π, hπ⟩ := PEqualNP.Outside.L_meta_25687_aux.extend_bij K L e
      have hKcard : K.card = ∑ z : V, min (mult x z) (mult y (swap z + b)) := by
        rw [Finset.card_biUnion hA_disj]
        refine Finset.sum_congr rfl fun z _ => ?_
        exact hAcard z
      refine ⟨π, K, by omega, ?_⟩
      intro i hi j hj
      refine (PEqualNP.Outside.L_meta_25687_aux.xor4_iff (x i) (x j) (y (π i)) (y (π j))
        (f i) (f j) (g (π i)) (g (π j))).mpr ?_
      have hπi_B : π i ∈ B (x i) := by
        rw [hπ i hi]
        exact (ez (x i) ⟨i, hK_mem i hi⟩).property
      have hπj_B : π j ∈ B (x j) := by
        rw [hπ j hj]
        exact (ez (x j) ⟨j, hK_mem j hj⟩).property
      have hyi : y (π i) = swap (x i) + b := hB_val (x i) (π i) hπi_B
      have hyj : y (π j) = swap (x j) + b := hB_val (x j) (π j) hπj_B
      have hydiff : y (π i) + y (π j) = PEqualNP.Outside.L_meta_25687_aux.sw (x i + x j) := by
        rw [hyi, hyj, hsw_eq, hsw_eq, PEqualNP.Outside.L_meta_25687_aux.sw_add]
        ext k
        change (PEqualNP.Outside.L_meta_25687_aux.sw (x i) k + b k) +
            (PEqualNP.Outside.L_meta_25687_aux.sw (x j) k + b k) =
          PEqualNP.Outside.L_meta_25687_aux.sw (x i) k +
            PEqualNP.Outside.L_meta_25687_aux.sw (x j) k
        have := PEqualNP.Outside.L_meta_25687_aux.add_self_z2 (b k)
        linear_combination this
      rw [hydiff]
      exact PEqualNP.Outside.L_meta_25687_aux.dot_sw_self (x i + x j)

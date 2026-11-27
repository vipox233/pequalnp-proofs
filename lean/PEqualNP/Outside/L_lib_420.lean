import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_420_aux

def sgn (b : ZMod 2) : ℤ :=
  if b = 0 then 1 else -1

lemma z2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

lemma z2_ne_zero (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  revert x h; decide

lemma z2_add_eq_zero_iff (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  revert x y; decide

lemma z2_add_ne_zero (x y : ZMod 2) (h : x ≠ y) : x + y = 1 := by
  revert x y h; decide

lemma sgn_add (b c : ZMod 2) : sgn (b + c) = sgn b * sgn c := by
  revert b c; decide

lemma sgn_add_one (b : ZMod 2) : sgn (b + 1) = -sgn b := by
  revert b; decide

lemma z2_term_id (p1 p2 q1 q2 q3 q4 : ZMod 2) :
    (q1 + p1) + (q3 + (p1 + p2)) = (q2 + q4 + p2) + (q3 + q2 + q1 + q4) := by
  revert p1 p2 q1 q2 q3 q4; decide

lemma z2_rad_id (qd0d qd0 qd q0 p1 p2 : ZMod 2) (h : qd0d + qd0 + qd + q0 = 0) :
    qd0d + q0 + (p1 + p2) = (qd + q0 + p1) + (qd0 + q0 + p2) := by
  revert qd0d qd0 qd q0 p1 p2 h; decide

lemma vec_add_self {n : ℕ} (u : Fin n → ZMod 2) : u + u = 0 :=
  funext fun i => z2_add_self (u i)

lemma vec_add_cancel_right {n : ℕ} (u v : Fin n → ZMod 2) : u + v + v = u := by
  rw [add_assoc, vec_add_self, add_zero]

lemma vec_add_cancel_left {n : ℕ} (u v : Fin n → ZMod 2) : u + (u + v) = v := by
  rw [← add_assoc, vec_add_self, zero_add]

lemma dot_add_right {n : ℕ} (a x y : Fin n → ZMod 2) :
    dotProduct a (x + y) = dotProduct a x + dotProduct a y := by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

lemma card_vec (n : ℕ) : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2 ^ n := by
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma sum_translate {n : ℕ} (c : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ℤ) :
    (∑ y : Fin n → ZMod 2, f y) = ∑ d : Fin n → ZMod 2, f (d + c) := by
  symm
  refine Finset.sum_bij (fun d _ => d + c) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro d1 _ d2 _ h
    simpa [vec_add_cancel_right] using congrArg (fun z => z + c) h
  · intro y _
    exact ⟨y + c, Finset.mem_univ _, vec_add_cancel_right y c⟩

lemma main (n : ℕ) (q : (Fin n → ZMod 2) → ZMod 2)
    (hpol : ∀ u v w : Fin n → ZMod 2,
      (q (u + (v + w)) + q u + q (v + w) + q 0) =
        (q (u + v) + q u + q v + q 0) + (q (u + w) + q u + q w + q 0))
    (a : Fin n → ZMod 2) :
    let V := Fin n → ZMod 2
    let polar := fun (u v : V) => q (u + v) + q u + q v + q 0
    let radical := Finset.univ.filter (fun d : V => ∀ x : V, polar d x = 0)
    (∑ x : V, sgn (q x + dotProduct a x)) ^ 2 =
      if ∀ d ∈ radical, q d + q 0 = dotProduct a d
      then (2 : ℤ) ^ n * (radical.card : ℤ) else 0 := by
  classical
  intro V polar radical
  have hpol_lin : ∀ u v w : V, polar u (v + w) = polar u v + polar u w := hpol
  have hpol_symm : ∀ u v : V, polar u v = polar v u := fun u v => by
    dsimp only [polar]
    rw [add_comm u v]
    abel
  have hsq :
      (∑ x : V, sgn (q x + dotProduct a x)) ^ 2 =
        ∑ d : V, sgn (q d + q 0 + dotProduct a d) * ∑ x : V, sgn (polar d x) := by
    rw [sq, Finset.sum_mul]
    calc
      ∑ x : V, sgn (q x + dotProduct a x) * ∑ y : V, sgn (q y + dotProduct a y)
        = ∑ x : V, ∑ y : V, sgn (q x + dotProduct a x) * sgn (q y + dotProduct a y) := by
            refine Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _
      _ = ∑ x : V, ∑ d : V,
            sgn (q x + dotProduct a x) * sgn (q (d + x) + dotProduct a (d + x)) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            exact sum_translate x (fun y => sgn (q x + dotProduct a x) * sgn (q y + dotProduct a y))
      _ = ∑ d : V, ∑ x : V,
            sgn (q x + dotProduct a x) * sgn (q (d + x) + dotProduct a (d + x)) := Finset.sum_comm
      _ = ∑ d : V, ∑ x : V, sgn (q d + q 0 + dotProduct a d) * sgn (polar d x) := by
            refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun x _ => ?_
            rw [← sgn_add, ← sgn_add, dot_add_right, add_comm (dotProduct a d) (dotProduct a x)]
            congr 1
            exact z2_term_id (dotProduct a x) (dotProduct a d) (q x) (q d) (q (d + x)) (q 0)
      _ = ∑ d : V, sgn (q d + q 0 + dotProduct a d) * ∑ x : V, sgn (polar d x) := by
            refine Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm
  have hchar : ∀ d : V,
      (∑ x : V, sgn (polar d x)) = if d ∈ radical then (2 : ℤ) ^ n else 0 := by
    intro d
    split_ifs with hd
    · have hall : ∀ x : V, polar d x = 0 := (Finset.mem_filter.1 hd).2
      have hs1 : (∑ x : V, sgn (polar d x)) = ∑ _x : V, (1 : ℤ) :=
        Finset.sum_congr rfl fun x _ => by rw [hall x]; rfl
      rw [hs1, Finset.sum_const, nsmul_eq_mul, mul_one, card_vec]
      norm_cast
    · have hex : ∃ x0 : V, polar d x0 ≠ 0 := by
        by_contra hnone
        push Not at hnone
        exact hd (Finset.mem_filter.2 ⟨Finset.mem_univ d, hnone⟩)
      obtain ⟨x0, hx0⟩ := hex
      have hx1 : polar d x0 = 1 := z2_ne_zero _ hx0
      have hshift :
          (∑ x : V, sgn (polar d x)) = ∑ x : V, sgn (polar d (x + x0)) :=
        sum_translate x0 (fun x => sgn (polar d x))
      have hflip :
          (∑ x : V, sgn (polar d (x + x0))) = -∑ x : V, sgn (polar d x) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hlin : polar d (x + x0) = polar d x + polar d x0 := hpol d x x0
        rw [hlin, hx1, sgn_add_one]
      have hneg : (∑ x : V, sgn (polar d x)) = -∑ x : V, sgn (polar d x) :=
        hshift.trans hflip
      omega
  have hred :
      (∑ x : V, sgn (q x + dotProduct a x)) ^ 2 =
        (2 : ℤ) ^ n * ∑ d ∈ radical, sgn (q d + q 0 + dotProduct a d) := by
    rw [hsq]
    calc
      ∑ d : V, sgn (q d + q 0 + dotProduct a d) * ∑ x : V, sgn (polar d x)
        = ∑ d : V, if d ∈ radical then sgn (q d + q 0 + dotProduct a d) * (2 : ℤ) ^ n else 0 := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [hchar d]
            split_ifs <;> simp
      _ = ∑ d ∈ radical, sgn (q d + q 0 + dotProduct a d) * (2 : ℤ) ^ n := by
            rw [← Finset.sum_filter]
            congr 1
            ext d
            simp
      _ = (2 : ℤ) ^ n * ∑ d ∈ radical, sgn (q d + q 0 + dotProduct a d) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun d _ => mul_comm _ _
  rw [hred]
  split_ifs with hmatch
  · congr 1
    have hs1 : (∑ d ∈ radical, sgn (q d + q 0 + dotProduct a d)) = ∑ _d ∈ radical, (1 : ℤ) :=
      Finset.sum_congr rfl fun d hd => by
        rw [hmatch d hd, z2_add_self]
        rfl
    rw [hs1, Finset.sum_const, nsmul_eq_mul, mul_one]
  · have hex : ∃ d0 ∈ radical, q d0 + q 0 ≠ dotProduct a d0 := by
      by_contra hnone
      push Not at hnone
      exact hmatch hnone
    obtain ⟨d0, hd0, hne⟩ := hex
    have hd0_pol : ∀ x : V, polar d0 x = 0 := (Finset.mem_filter.1 hd0).2
    have hval1 : q d0 + q 0 + dotProduct a d0 = 1 := z2_ne_zero _ (by
      intro hz
      exact hne ((z2_add_eq_zero_iff _ _).1 hz))
    have hrad_add : ∀ d ∈ radical, d + d0 ∈ radical := by
      intro d hd
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun x => ?_⟩
      rw [hpol_symm, hpol_lin x d d0, hpol_symm x d, hpol_symm x d0,
        (Finset.mem_filter.1 hd).2 x, hd0_pol x, add_zero]
    have hsum_zero : ∑ d ∈ radical, sgn (q d + q 0 + dotProduct a d) = 0 := by
      have hbij :
          (∑ d ∈ radical, sgn (q d + q 0 + dotProduct a d)) =
            ∑ d ∈ radical, sgn (q (d + d0) + q 0 + dotProduct a (d + d0)) := by
        symm
        refine Finset.sum_bij (fun d _ => d + d0) hrad_add ?_ ?_ (fun _ _ => rfl)
        · intro d1 _ d2 _ h
          simpa [vec_add_cancel_right] using congrArg (fun z => z + d0) h
        · intro d hd
          exact ⟨d + d0, hrad_add d hd, vec_add_cancel_right d d0⟩
      have hneg :
          (∑ d ∈ radical, sgn (q (d + d0) + q 0 + dotProduct a (d + d0))) =
            -∑ d ∈ radical, sgn (q d + q 0 + dotProduct a d) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        have hp : q (d + d0) + q d0 + q d + q 0 = 0 := by
          simpa [polar, add_comm d d0] using hd0_pol d
        rw [dot_add_right, z2_rad_id (q (d + d0)) (q d0) (q d) (q 0) (dotProduct a d) (dotProduct a d0) hp,
          hval1, sgn_add_one]
      have htot := hbij.trans hneg
      omega
    rw [hsum_zero, mul_zero]

end PEqualNP.Outside.L_lib_420_aux

theorem PEqualNP.Outside.L_lib_420 :
∀ n : ℕ,
  let V := Fin n → ZMod 2
  let s := fun (bit : ZMod 2) => if bit = 0 then (1 : ℤ) else -1
  ∀ q : V → ZMod 2,
    let polar := fun (u v : V) => q (u+v) + q u + q v + q 0
    (∀ u v w : V, polar u (v+w) = polar u v + polar u w) →
    let radical := Finset.univ.filter (fun d : V => ∀ x : V, polar d x = 0)
    ∀ a : V,
      (∑ x : V, s (q x + dotProduct a x))^2 =
        if ∀ d ∈ radical, q d + q 0 = dotProduct a d
        then (2:ℤ)^n * (radical.card : ℤ) else 0 := by
  intro n V s q polar hpol radical a
  exact PEqualNP.Outside.L_lib_420_aux.main n q hpol a

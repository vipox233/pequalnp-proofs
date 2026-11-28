import Mathlib
import PEqualNP.Defs

-- A nonzero linear map g = (A, B, C) to one extra masked-product block: offsets p, q exist such that on every
-- fibre of the r masked products the extra bit C + (A + p)(B + q) takes both values.
--
-- A point is written pt x y z (first operands, second operands, masks); its outputs are z + x*y.
-- (1) A nonzero linear form takes both values on every fibre: move one operand vector, or, if the form
--     sees no operand, set both operands to a vector u and add u to the masks.
-- (2) If A = 0, B = 0 or A = B, one offset pair makes the extra bit equal to C, and another makes it a
--     nonzero one of A, B; use the first if C is not zero and the second otherwise.
-- (3) Otherwise translate by the mask vector b: fibre b with offsets (p, q) is fibre 0 with offsets
--     (p + A(0,0,b), q + B(0,0,b)), up to the constant C(0,0,b). On fibre 0 at most one offset pair is bad,
--     because the difference of the extra bits for two pairs is a nonzero linear form plus a constant.
--     If the mask parts of A and B are independent (two mask vectors u1, u2 with nonzero determinant), no
--     pair is bad: on the 16 points with operands s1 u1 + s2 u2 and t1 u1 + t2 u2 the values of the extra
--     bit add up to that determinant, so they are not all equal. If they are dependent, the translations
--     reach at most one nonzero pair (l0, m0), and among the four offset pairs one avoids the bad pair
--     together with its translate.

namespace PEqualNP.Outside.L_pcx_414

abbrev K := ZMod 2
abbrev X (r : ℕ) := Fin r → Fin 3 → K

/-- The outputs of the `r` masked products. -/
def tgt {r : ℕ} (w : X r) : Fin r → K := fun i => w i 2 + w i 0 * w i 1

/-- The point with first operands `x`, second operands `y` and masks `z`. -/
def pt {r : ℕ} (x y z : Fin r → K) : X r := fun i => ![x i, y i, z i]

theorem z_ne (A : K) (h : A ≠ 1) : A = 0 := by revert A; decide
theorem z_ne0 (A : K) (h : A ≠ 0) : A = 1 := by revert A; decide
theorem z_cases (A : K) : A = 0 ∨ A = 1 := by revert A; decide
theorem z_flip (v e : K) (h : v ≠ e) : v = e + 1 := by revert v e; decide
theorem z_eq_of_add (a b : K) (h : a + b = 0) : a = b := by revert a b; decide
theorem z_01 (t : K) : 0 + t ≠ 1 + t := by revert t; decide
theorem z_cancel (a l : K) (h : a + l = a) : l = 0 := by revert a l; decide
theorem z_cancel2 (a l l0 : K) (h : a + l + l0 = a) : l = l0 := by revert a l l0; decide
theorem z_pick (l0 m0 : K) : ∃ l1 m1 : K, ¬ (l1 = 0 ∧ m1 = 0) ∧ ¬ (l1 = l0 ∧ m1 = m0) := by
  revert l0 m0; decide
theorem z_par (l0 m0 l m : K) (h0 : l0 ≠ 0 ∨ m0 ≠ 0) (hd : l0 * m + l * m0 = 0) :
    (l = 0 ∧ m = 0) ∨ (l = l0 ∧ m = m0) := by
  revert l0 m0 l m; decide
theorem z_d (a b c p q p' q' : K) :
    c + (a + p) * (b + q) + (c + (a + p') * (b + q')) =
      (q + q') * a + (p + p') * b + (p * q + p' * q') := by
  revert a b c p q p' q'; decide
theorem zN1 (e t : K) : (e + t) * 1 + t = e := by revert e t; decide
theorem zN3 (e t : K) : (e + t) * 0 + (e + t) * 0 + (e + t) * 1 + t = e := by revert e t; decide
theorem zT1 (β s u : K) : β + s * u + s * u * (s * u) = β := by revert β s u; decide
theorem zT2 (s1 t1 s2 t2 x y : K) :
    s1 * t1 * x + s2 * t2 * y + (s1 * t2 + s2 * t1) * (x * y) + (s1 * x + s2 * y) * (t1 * x + t2 * y)
      = 0 := by
  revert s1 t1 s2 t2 x y; decide
theorem zA1 (e : K) : 0 + (0 + 1) * (e + 0) = e := by revert e; decide
theorem zA2 (e t : K) : e + (0 + 0) * (t + 0) = e := by revert e t; decide
theorem zA3 (e : K) : 0 + (e + 0) * (0 + 1) = e := by revert e; decide
theorem zA4 (e t : K) : e + (t + 0) * (0 + 0) = e := by revert e t; decide
theorem zA5 (e : K) : 0 + (e + 0) * (e + 0) = e := by revert e; decide
theorem zA6 (e t : K) : e + (t + 0) * (t + 1) = e := by revert e t; decide

/-- A nonzero linear form takes both values on every fibre. -/
theorem NC {r : ℕ} (l : X r →ₗ[K] K) (hl : l ≠ 0) (b : Fin r → K) (e : K) :
    ∃ w : X r, tgt w = b ∧ l w = e := by
  obtain ⟨s, hs⟩ : ∃ s : K, s = e + l (pt 0 0 b) := ⟨_, rfl⟩
  by_cases h1 : ∃ u : Fin r → K, l (pt u 0 0) = 1
  · obtain ⟨u, hu⟩ := h1
    refine ⟨pt (s • u) 0 b, ?_, ?_⟩
    · funext i; simp [tgt, pt]
    · have e1 : pt (s • u) 0 b = s • pt u 0 0 + pt 0 0 b := by
        funext i c; fin_cases c <;> simp [pt]
      rw [e1, map_add, map_smul, hu, smul_eq_mul, hs]
      exact zN1 e _
  · by_cases h2 : ∃ u : Fin r → K, l (pt 0 u 0) = 1
    · obtain ⟨u, hu⟩ := h2
      refine ⟨pt 0 (s • u) b, ?_, ?_⟩
      · funext i; simp [tgt, pt]
      · have e1 : pt 0 (s • u) b = s • pt 0 u 0 + pt 0 0 b := by
          funext i c; fin_cases c <;> simp [pt]
        rw [e1, map_add, map_smul, hu, smul_eq_mul, hs]
        exact zN1 e _
    · have h1' : ∀ u : Fin r → K, l (pt u 0 0) = 0 := fun u => z_ne _ (fun hc => h1 ⟨u, hc⟩)
      have h2' : ∀ u : Fin r → K, l (pt 0 u 0) = 0 := fun u => z_ne _ (fun hc => h2 ⟨u, hc⟩)
      obtain ⟨w0, hw0⟩ : ∃ w0 : X r, l w0 ≠ 0 := by
        by_contra hcon
        apply hl
        apply LinearMap.ext
        intro w
        by_contra hw
        exact hcon ⟨w, hw⟩
      obtain ⟨u, hu⟩ : ∃ u : Fin r → K, u = fun i => w0 i 2 := ⟨_, rfl⟩
      have hsplit : w0 = pt (fun i => w0 i 0) 0 0 + pt 0 (fun i => w0 i 1) 0 + pt 0 0 u := by
        rw [hu]
        funext i c; fin_cases c <;> simp [pt]
      have hz : l (pt 0 0 u) = 1 := by
        apply z_ne0
        intro hc
        apply hw0
        rw [hsplit, map_add, map_add, h1', h2', hc]
        rfl
      refine ⟨pt (s • u) (s • u) (b + s • u), ?_, ?_⟩
      · funext i
        show b i + s * u i + s * u i * (s * u i) = b i
        exact zT1 _ _ _
      · have e1 : pt (s • u) (s • u) (b + s • u)
            = s • pt u 0 0 + s • pt 0 u 0 + s • pt 0 0 u + pt 0 0 b := by
          funext i c; fin_cases c <;> simp [pt, add_comm]
        rw [e1, map_add, map_add, map_add, map_smul, map_smul, map_smul, h1', h2', hz, smul_eq_mul,
          hs]
        exact zN3 e _

/-- The offsets `p`, `q` are good on the zero fibre. -/
def G0 {r : ℕ} (g : X r →ₗ[K] (Fin 3 → K)) (p q : K) : Prop :=
  ∀ e : K, ∃ w : X r, tgt w = 0 ∧ (g w) 2 + ((g w) 0 + p) * ((g w) 1 + q) = e

/-- Fibre `b` with offsets `(p, q)` is the zero fibre with translated offsets. -/
theorem trans {r : ℕ} (g : X r →ₗ[K] (Fin 3 → K)) (p q : K) (b : Fin r → K)
    (h : G0 g (p + (g (pt 0 0 b)) 0) (q + (g (pt 0 0 b)) 1)) (e : K) :
    ∃ w : X r, tgt w = b ∧ (g w) 2 + ((g w) 0 + p) * ((g w) 1 + q) = e := by
  have h2 : (2 : K) = 0 := by decide
  obtain ⟨w0, hw0, he0⟩ := h (e + (g (pt 0 0 b)) 2)
  refine ⟨w0 + pt 0 0 b, ?_, ?_⟩
  · funext i
    have h0 : w0 i 2 + w0 i 0 * w0 i 1 = 0 := congrFun hw0 i
    show (w0 i 2 + b i) + (w0 i 0 + 0) * (w0 i 1 + 0) = b i
    linear_combination h0
  · rw [map_add]
    show (g w0) 2 + (g (pt 0 0 b)) 2
      + ((g w0) 0 + (g (pt 0 0 b)) 0 + p) * ((g w0) 1 + (g (pt 0 0 b)) 1 + q) = e
    linear_combination he0 + (g (pt 0 0 b)) 2 * h2

/-- With `A`, `B` independent, at most one offset pair is bad on the zero fibre. -/
theorem uniq {r : ℕ} (g : X r →ₗ[K] (Fin 3 → K)) (A B : X r →ₗ[K] K)
    (hA0 : ∀ w, A w = (g w) 0) (hB1 : ∀ w, B w = (g w) 1) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B)
    (p q p' q' : K) (h1 : ¬ G0 g p q) (h2 : ¬ G0 g p' q') : p = p' ∧ q = q' := by
  obtain ⟨e, he⟩ := not_forall.1 h1
  obtain ⟨e', he'⟩ := not_forall.1 h2
  have hv : ∀ w : X r, tgt w = 0 → (g w) 2 + ((g w) 0 + p) * ((g w) 1 + q) = e + 1 :=
    fun w hw => z_flip _ _ (fun hc => he ⟨w, hw, hc⟩)
  have hv' : ∀ w : X r, tgt w = 0 → (g w) 2 + ((g w) 0 + p') * ((g w) 1 + q') = e' + 1 :=
    fun w hw => z_flip _ _ (fun hc => he' ⟨w, hw, hc⟩)
  have hl : (q + q') • A + (p + p') • B = 0 := by
    by_contra hne
    obtain ⟨w1, hw1, e1⟩ := NC _ hne 0 0
    obtain ⟨w2, hw2, e2⟩ := NC _ hne 0 1
    have e1' : (q + q') * (g w1) 0 + (p + p') * (g w1) 1 = 0 := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hA0, hB1] at e1
      exact e1
    have e2' : (q + q') * (g w2) 0 + (p + p') * (g w2) 1 = 1 := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hA0, hB1] at e2
      exact e2
    have d1 := z_d ((g w1) 0) ((g w1) 1) ((g w1) 2) p q p' q'
    rw [hv w1 hw1, hv' w1 hw1, e1'] at d1
    have d2 := z_d ((g w2) 0) ((g w2) 1) ((g w2) 2) p q p' q'
    rw [hv w2 hw2, hv' w2 hw2, e2'] at d2
    exact z_01 _ (d1.symm.trans d2)
  have key : q + q' = 0 ∧ p + p' = 0 := by
    rcases z_cases (q + q') with hs | hs <;> rcases z_cases (p + p') with ht | ht
    · exact ⟨hs, ht⟩
    · exfalso
      rw [hs, ht] at hl
      exact hB (by simpa using hl)
    · exfalso
      rw [hs, ht] at hl
      exact hA (by simpa using hl)
    · exfalso
      rw [hs, ht] at hl
      apply hAB
      apply LinearMap.ext
      intro w
      have hw := LinearMap.congr_fun hl w
      simp only [LinearMap.add_apply, one_smul, LinearMap.zero_apply] at hw
      exact z_eq_of_add _ _ hw
  exact ⟨z_eq_of_add _ _ key.2, z_eq_of_add _ _ key.1⟩

/-- The sixteen values add up to the determinant, so they are not all equal. -/
theorem quartic_arith (a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 c1 c2 c3 c4 c5 c6 c7 p q e : K)
    (hdet : a5 * b6 + a6 * b5 = 1)
    (hall : ∀ s1 t1 s2 t2 : K,
      (s1 * c1 + s2 * c2 + t1 * c3 + t2 * c4 + (s1 * t1) * c5 + (s2 * t2) * c6 + (s1 * t2 + s2 * t1) * c7)
      + ((s1 * a1 + s2 * a2 + t1 * a3 + t2 * a4 + (s1 * t1) * a5 + (s2 * t2) * a6 + (s1 * t2 + s2 * t1) * a7) + p)
        * ((s1 * b1 + s2 * b2 + t1 * b3 + t2 * b4 + (s1 * t1) * b5 + (s2 * t2) * b6 + (s1 * t2 + s2 * t1) * b7) + q) = e + 1) : False := by
  have h2 : (2 : K) = 0 := by decide
  have h0000 := hall 0 0 0 0
  have h0001 := hall 0 0 0 1
  have h0010 := hall 0 0 1 0
  have h0011 := hall 0 0 1 1
  have h0100 := hall 0 1 0 0
  have h0101 := hall 0 1 0 1
  have h0110 := hall 0 1 1 0
  have h0111 := hall 0 1 1 1
  have h1000 := hall 1 0 0 0
  have h1001 := hall 1 0 0 1
  have h1010 := hall 1 0 1 0
  have h1011 := hall 1 0 1 1
  have h1100 := hall 1 1 0 0
  have h1101 := hall 1 1 0 1
  have h1110 := hall 1 1 1 0
  have h1111 := hall 1 1 1 1
  have h1 : (1 : K) = 0 := by
    linear_combination h0000 + h0001 + h0010 + h0011 + h0100 + h0101 + h0110 + h0111 + h1000 + h1001 + h1010 + h1011 + h1100 + h1101 + h1110 + h1111 - hdet
      + (8 * (e + 1) - (4 * a1 * b1 + 2 * a1 * b2 + 2 * a1 * b3 + 2 * a1 * b4 + 2 * a1 * b5 + 1 * a1 * b6 + 3 * a1 * b7 + 4 * a1 * q + 2 * a2 * b1 + 4 * a2 * b2 + 2 * a2 * b3 + 2 * a2 * b4 + 1 * a2 * b5 + 2 * a2 * b6 + 3 * a2 * b7 + 4 * a2 * q + 2 * a3 * b1 + 2 * a3 * b2 + 4 * a3 * b3 + 2 * a3 * b4 + 2 * a3 * b5 + 1 * a3 * b6 + 3 * a3 * b7 + 4 * a3 * q + 2 * a4 * b1 + 2 * a4 * b2 + 2 * a4 * b3 + 4 * a4 * b4 + 1 * a4 * b5 + 2 * a4 * b6 + 3 * a4 * b7 + 4 * a4 * q + 2 * a5 * b1 + 1 * a5 * b2 + 2 * a5 * b3 + 1 * a5 * b4 + 2 * a5 * b5 + 2 * a5 * b7 + 2 * a5 * q + 1 * a6 * b1 + 2 * a6 * b2 + 1 * a6 * b3 + 2 * a6 * b4 + 2 * a6 * b6 + 2 * a6 * b7 + 2 * a6 * q + 3 * a7 * b1 + 3 * a7 * b2 + 3 * a7 * b3 + 3 * a7 * b4 + 2 * a7 * b5 + 2 * a7 * b6 + 5 * a7 * b7 + 4 * a7 * q + 4 * b1 * p + 4 * b2 * p + 4 * b3 * p + 4 * b4 * p + 2 * b5 * p + 2 * b6 * p + 4 * b7 * p + 4 * c1 + 4 * c2 + 4 * c3 + 4 * c4 + 2 * c5 + 2 * c6 + 4 * c7 + 8 * p * q)) * h2
  exact one_ne_zero h1

/-- With independent mask parts of `A` and `B`, every offset pair is good on the zero fibre. -/
theorem quartic {r : ℕ} (g : X r →ₗ[K] (Fin 3 → K)) (u1 u2 : Fin r → K)
    (hdet : (g (pt 0 0 u1)) 0 * (g (pt 0 0 u2)) 1 + (g (pt 0 0 u2)) 0 * (g (pt 0 0 u1)) 1 = 1)
    (p q : K) : G0 g p q := by
  intro e
  have hpt : ∀ s1 t1 s2 t2 : K, ∃ w : X r, tgt w = 0 ∧ ∀ c : Fin 3, (g w) c =
      s1 * (g (pt u1 0 0)) c + s2 * (g (pt u2 0 0)) c + t1 * (g (pt 0 u1 0)) c
        + t2 * (g (pt 0 u2 0)) c + (s1 * t1) * (g (pt 0 0 u1)) c + (s2 * t2) * (g (pt 0 0 u2)) c
        + (s1 * t2 + s2 * t1) * (g (pt 0 0 (u1 * u2))) c := by
    intro s1 t1 s2 t2
    refine ⟨pt (s1 • u1 + s2 • u2) (t1 • u1 + t2 • u2)
      ((s1 * t1) • u1 + (s2 * t2) • u2 + (s1 * t2 + s2 * t1) • (u1 * u2)), ?_, ?_⟩
    · funext i
      show s1 * t1 * u1 i + s2 * t2 * u2 i + (s1 * t2 + s2 * t1) * (u1 i * u2 i)
        + (s1 * u1 i + s2 * u2 i) * (t1 * u1 i + t2 * u2 i) = 0
      exact zT2 _ _ _ _ _ _
    · intro c
      have e1 : pt (s1 • u1 + s2 • u2) (t1 • u1 + t2 • u2)
          ((s1 * t1) • u1 + (s2 * t2) • u2 + (s1 * t2 + s2 * t1) • (u1 * u2))
          = s1 • pt u1 0 0 + s2 • pt u2 0 0 + t1 • pt 0 u1 0 + t2 • pt 0 u2 0
            + (s1 * t1) • pt 0 0 u1 + (s2 * t2) • pt 0 0 u2
            + (s1 * t2 + s2 * t1) • pt 0 0 (u1 * u2) := by
        funext i c'; fin_cases c' <;> simp [pt]
      rw [e1]
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_contra hcon
  apply quartic_arith ((g (pt u1 0 0)) 0) ((g (pt u2 0 0)) 0) ((g (pt 0 u1 0)) 0) ((g (pt 0 u2 0)) 0)
    ((g (pt 0 0 u1)) 0) ((g (pt 0 0 u2)) 0) ((g (pt 0 0 (u1 * u2))) 0)
    ((g (pt u1 0 0)) 1) ((g (pt u2 0 0)) 1) ((g (pt 0 u1 0)) 1) ((g (pt 0 u2 0)) 1)
    ((g (pt 0 0 u1)) 1) ((g (pt 0 0 u2)) 1) ((g (pt 0 0 (u1 * u2))) 1)
    ((g (pt u1 0 0)) 2) ((g (pt u2 0 0)) 2) ((g (pt 0 u1 0)) 2) ((g (pt 0 u2 0)) 2)
    ((g (pt 0 0 u1)) 2) ((g (pt 0 0 u2)) 2) ((g (pt 0 0 (u1 * u2))) 2) p q e hdet
  intro s1 t1 s2 t2
  obtain ⟨w, hw, hgw⟩ := hpt s1 t1 s2 t2
  have hv := z_flip _ e (fun hc => hcon ⟨w, hw, hc⟩)
  rw [hgw 0, hgw 1, hgw 2] at hv
  exact hv

theorem main {r : ℕ} (g : X r →ₗ[K] (Fin 3 → K)) (hg : g ≠ 0) :
    ∃ p q : K, ∀ (b : Fin r → K) (e : K), ∃ w : X r, tgt w = b ∧
      (g w) 2 + ((g w) 0 + p) * ((g w) 1 + q) = e := by
  obtain ⟨A, hA0⟩ : ∃ A : X r →ₗ[K] K, ∀ w, A w = (g w) 0 :=
    ⟨(LinearMap.proj 0).comp g, fun w => rfl⟩
  obtain ⟨B, hB1⟩ : ∃ B : X r →ₗ[K] K, ∀ w, B w = (g w) 1 :=
    ⟨(LinearMap.proj 1).comp g, fun w => rfl⟩
  obtain ⟨C, hC2⟩ : ∃ C : X r →ₗ[K] K, ∀ w, C w = (g w) 2 :=
    ⟨(LinearMap.proj 2).comp g, fun w => rfl⟩
  have hz0 : A = 0 → ∀ w, (g w) 0 = 0 := by
    intro h w
    have e := hA0 w
    rw [h] at e
    exact e.symm
  have hz1 : B = 0 → ∀ w, (g w) 1 = 0 := by
    intro h w
    have e := hB1 w
    rw [h] at e
    exact e.symm
  have hz2 : C = 0 → ∀ w, (g w) 2 = 0 := by
    intro h w
    have e := hC2 w
    rw [h] at e
    exact e.symm
  by_cases hA : A = 0
  · by_cases hC : C = 0
    · have hB : B ≠ 0 := by
        intro hB
        apply hg
        apply LinearMap.ext
        intro w
        funext c
        fin_cases c
        · exact hz0 hA w
        · exact hz1 hB w
        · exact hz2 hC w
      refine ⟨1, 0, fun b e => ?_⟩
      obtain ⟨w, hw, he⟩ := NC B hB b e
      refine ⟨w, hw, ?_⟩
      rw [hz0 hA w, hz2 hC w, ← hB1, he]
      exact zA1 e
    · refine ⟨0, 0, fun b e => ?_⟩
      obtain ⟨w, hw, he⟩ := NC C hC b e
      refine ⟨w, hw, ?_⟩
      rw [hz0 hA w, ← hC2, he]
      exact zA2 e _
  · by_cases hB : B = 0
    · by_cases hC : C = 0
      · refine ⟨0, 1, fun b e => ?_⟩
        obtain ⟨w, hw, he⟩ := NC A hA b e
        refine ⟨w, hw, ?_⟩
        rw [hz1 hB w, hz2 hC w, ← hA0, he]
        exact zA3 e
      · refine ⟨0, 0, fun b e => ?_⟩
        obtain ⟨w, hw, he⟩ := NC C hC b e
        refine ⟨w, hw, ?_⟩
        rw [hz1 hB w, ← hC2, he]
        exact zA4 e _
    · by_cases hAB : A = B
      · have hab : ∀ w, (g w) 1 = (g w) 0 := by
          intro w
          rw [← hA0, ← hB1, hAB]
        by_cases hC : C = 0
        · refine ⟨0, 0, fun b e => ?_⟩
          obtain ⟨w, hw, he⟩ := NC A hA b e
          refine ⟨w, hw, ?_⟩
          rw [hab w, hz2 hC w, ← hA0, he]
          exact zA5 e
        · refine ⟨0, 1, fun b e => ?_⟩
          obtain ⟨w, hw, he⟩ := NC C hC b e
          refine ⟨w, hw, ?_⟩
          rw [hab w, ← hC2, he]
          exact zA6 e _
      · have hu := uniq g A B hA0 hB1 hA hB hAB
        by_cases hd : ∃ u1 u2 : Fin r → K,
            (g (pt 0 0 u1)) 0 * (g (pt 0 0 u2)) 1 + (g (pt 0 0 u2)) 0 * (g (pt 0 0 u1)) 1 = 1
        · obtain ⟨u1, u2, hdet⟩ := hd
          exact ⟨0, 0, fun b e => trans g 0 0 b (quartic g u1 u2 hdet _ _) e⟩
        · have hd0 : ∀ u1 u2 : Fin r → K,
              (g (pt 0 0 u1)) 0 * (g (pt 0 0 u2)) 1 + (g (pt 0 0 u2)) 0 * (g (pt 0 0 u1)) 1 = 0 :=
            fun u1 u2 => z_ne _ (fun hc => hd ⟨u1, u2, hc⟩)
          obtain ⟨l0, m0, hlm⟩ : ∃ l0 m0 : K, ∀ u : Fin r → K,
              ((g (pt 0 0 u)) 0 = 0 ∧ (g (pt 0 0 u)) 1 = 0) ∨
              ((g (pt 0 0 u)) 0 = l0 ∧ (g (pt 0 0 u)) 1 = m0) := by
            by_cases hne : ∃ u0 : Fin r → K, (g (pt 0 0 u0)) 0 ≠ 0 ∨ (g (pt 0 0 u0)) 1 ≠ 0
            · obtain ⟨u0, h0⟩ := hne
              exact ⟨_, _, fun u => z_par _ _ _ _ h0 (hd0 u0 u)⟩
            · refine ⟨0, 0, fun u => Or.inl ⟨?_, ?_⟩⟩
              · by_contra hc
                exact hne ⟨u, Or.inl hc⟩
              · by_contra hc
                exact hne ⟨u, Or.inr hc⟩
          obtain ⟨p, q, hp1, hp2⟩ : ∃ p q : K, G0 g p q ∧ G0 g (p + l0) (q + m0) := by
            by_cases hb : ∃ p0 q0 : K, ¬ G0 g p0 q0
            · obtain ⟨p0, q0, hbad⟩ := hb
              obtain ⟨l1, m1, h1, h2⟩ := z_pick l0 m0
              refine ⟨p0 + l1, q0 + m1, ?_, ?_⟩
              · by_contra hn
                have hh := hu _ _ _ _ hn hbad
                exact h1 ⟨z_cancel _ _ hh.1, z_cancel _ _ hh.2⟩
              · by_contra hn
                have hh := hu _ _ _ _ hn hbad
                exact h2 ⟨z_cancel2 _ _ _ hh.1, z_cancel2 _ _ _ hh.2⟩
            · have hall : ∀ p q : K, G0 g p q := by
                intro p q
                by_contra hn
                exact hb ⟨p, q, hn⟩
              exact ⟨0, 0, hall _ _, hall _ _⟩
          refine ⟨p, q, fun b e => trans g p q b ?_ e⟩
          rcases hlm b with ⟨h0, h1⟩ | ⟨h0, h1⟩
          · rw [h0, h1, add_zero, add_zero]
            exact hp1
          · rw [h0, h1]
            exact hp2

end PEqualNP.Outside.L_pcx_414

theorem PEqualNP.Outside.L_pcx_414 : ∀ r : ℕ,
  let F := ZMod 2
  let X := Fin r → Fin 3 → F
  let target := fun (w : X) (i : Fin r) => w i 2 + w i 0 * w i 1
  ∀ (g : X →ₗ[F] (Fin 3 → F)) (_ : g ≠ 0),
    ∃ p q : F, ∀ (b : Fin r → F) (e : F), ∃ w : X,
      target w = b ∧ (g w) 2 + ((g w) 0+p)*((g w) 1+q) = e := by
  intro r
  dsimp only
  intro g hg
  obtain ⟨p, q, h⟩ := PEqualNP.Outside.L_pcx_414.main g hg
  refine ⟨p, q, fun b e => ?_⟩
  obtain ⟨w, hw, he⟩ := h b e
  exact ⟨w, hw, he⟩

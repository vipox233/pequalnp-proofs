import Mathlib
import PEqualNP.Defs

-- Credit: the even-rank lemmas for alternating forms (symm_zero_diag_sum, radSub,
-- even_codim_rad, even_finrank_range_alt) are copied from the merged proof
-- lean/PEqualNP/Outside/L_meta_25745.lean on upstream/main.

namespace PEqualNP.Outside.L_lib_922

open Matrix

lemma z2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

lemma z2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a h; decide

lemma z2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b h; decide

lemma symm_zero_diag_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (M : ι → ι → ZMod 2) (hdiag : ∀ i, M i i = 0) (hsymm : ∀ i j, M i j = M j i) :
    ∑ i ∈ s, ∑ j ∈ s, M i j = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hinner : ∀ i ∈ s, ∑ j ∈ insert a s, M i j = M i a + ∑ j ∈ s, M i j := by
      intro i _
      rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha, Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ih, hdiag a,
      zero_add, add_zero]
    have hswap : ∑ i ∈ s, M i a = ∑ j ∈ s, M a j := by
      apply Finset.sum_congr rfl
      intro i _
      exact hsymm i a
    rw [hswap]
    exact z2_add_self _

def radSub {r : ℕ}
    (B : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (U : Submodule (ZMod 2) (Fin r → ZMod 2)) : Submodule (ZMod 2) (Fin r → ZMod 2) :=
  { carrier := {u | u ∈ U ∧ ∀ v ∈ U, B u v = 0}, add_mem' := by
      intro a b ha hb
      refine ⟨U.add_mem ha.1 hb.1, fun v hv => ?_⟩
      rw [map_add, LinearMap.add_apply, ha.2 v hv, hb.2 v hv, add_zero]
    zero_mem' := ⟨U.zero_mem, fun _ _ => by simp⟩
    smul_mem' := by
      intro s a ha
      refine ⟨U.smul_mem s ha.1, fun v hv => ?_⟩
      rw [map_smul, LinearMap.smul_apply, ha.2 v hv, smul_zero] }

lemma even_codim_rad {r : ℕ}
    (B : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (halt : ∀ v, B v v = 0)
    (hsymm : ∀ u v, B u v = B v u)
    (W : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    Even (Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) (radSub B W)) := by
  classical
  let radOf := radSub B
  have hstrong : ∀ k : ℕ, ∀ U : Submodule (ZMod 2) (Fin r → ZMod 2),
      Module.finrank (ZMod 2) U = k →
      Even (Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) (radOf U)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro U hk
      by_cases htriv : ∀ u ∈ U, ∀ v ∈ U, B u v = 0
      · have heq : radOf U = U := by
          ext u
          exact ⟨fun h => h.1, fun hu => ⟨hu, htriv u hu⟩⟩
        rw [heq, Nat.sub_self]
        exact ⟨0, rfl⟩
      · push Not at htriv
        obtain ⟨u, huU, v, hvU, huv_ne⟩ := htriv
        have huv : B u v = 1 := z2_eq_one_of_ne_zero huv_ne
        have hvu : B v u = 1 := by rw [hsymm, huv]
        let φ : U →ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
          { toFun := fun w => (B u w.1, B v w.1)
            map_add' := fun a b => by
              apply Prod.ext <;> simp only [Submodule.coe_add, map_add, Prod.fst_add, Prod.snd_add]
            map_smul' := fun s a => by
              apply Prod.ext <;> simp only [SetLike.val_smul, map_smul, Prod.smul_fst,
                Prod.smul_snd, RingHom.id_apply] }
        have hφ_surj : Function.Surjective φ := by
          intro ⟨a, b⟩
          refine ⟨a • ⟨v, hvU⟩ + b • ⟨u, huU⟩, ?_⟩
          apply Prod.ext
          · change B u (a • v + b • u) = a
            rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, huv, halt u,
              mul_one, mul_zero, add_zero]
          · change B v (a • v + b • u) = b
            rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hvu, halt v,
              mul_zero, mul_one, zero_add]
        have hrange_φ : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
        have hrank_φ : Module.finrank (ZMod 2) (LinearMap.range φ) = 2 := by
          rw [hrange_φ, finrank_top, Module.finrank_prod, Module.finrank_self]
        have hrn := LinearMap.finrank_range_add_finrank_ker φ
        rw [hrank_φ] at hrn
        let U' : Submodule (ZMod 2) (Fin r → ZMod 2) :=
          { carrier := {w | w ∈ U ∧ B u w = 0 ∧ B v w = 0}, add_mem' := by
              intro a b ha hb
              refine ⟨U.add_mem ha.1 hb.1, ?_, ?_⟩
              · rw [map_add, ha.2.1, hb.2.1, add_zero]
              · rw [map_add, ha.2.2, hb.2.2, add_zero]
            zero_mem' := ⟨U.zero_mem, by simp, by simp⟩
            smul_mem' := by
              intro s a ha
              refine ⟨U.smul_mem s ha.1, ?_, ?_⟩
              · rw [map_smul, ha.2.1, smul_zero]
              · rw [map_smul, ha.2.2, smul_zero] }
        let eker : LinearMap.ker φ ≃ₗ[ZMod 2] U' :=
          { toFun := fun w => ⟨w.1.1, w.1.2, by
              have hw : φ w.1 = 0 := w.2
              exact ⟨congrArg Prod.fst hw, congrArg Prod.snd hw⟩⟩
            invFun := fun w => ⟨⟨w.1, w.2.1⟩, by
              change φ ⟨w.1, w.2.1⟩ = 0
              exact Prod.ext w.2.2.1 w.2.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        have hdimU' : Module.finrank (ZMod 2) U' = Module.finrank (ZMod 2) (LinearMap.ker φ) :=
          eker.finrank_eq.symm
        have hrad_eq : radOf U' = radOf U := by
          ext x
          constructor
          · intro hx
            refine ⟨hx.1.1, fun w hw => ?_⟩
            let w' := w + B u w • v + B v w • u
            have hw'U : w' ∈ U :=
              U.add_mem (U.add_mem hw (U.smul_mem _ hvU)) (U.smul_mem _ huU)
            have hBuw' : B u w' = 0 := by
              dsimp only [w']
              rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
                huv, halt u, mul_one, mul_zero, add_zero]
              exact z2_add_self _
            have hBvw' : B v w' = 0 := by
              dsimp only [w']
              rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
                hvu, halt v, mul_one, mul_zero, add_zero]
              exact z2_add_self _
            have hBxw' : B x w' = 0 := hx.2 w' ⟨hw'U, hBuw', hBvw'⟩
            have hBxu : B x u = 0 := by rw [hsymm]; exact hx.1.2.1
            have hBxv : B x v = 0 := by rw [hsymm]; exact hx.1.2.2
            dsimp only [w'] at hBxw'
            rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
              hBxv, hBxu, mul_zero, mul_zero, add_zero, add_zero] at hBxw'
            exact hBxw'
          · intro hx
            refine ⟨⟨hx.1, ?_, ?_⟩, fun w hw => hx.2 w hw.1⟩
            · rw [hsymm]; exact hx.2 u huU
            · rw [hsymm]; exact hx.2 v hvU
        have hle_rad : Module.finrank (ZMod 2) (radOf U') ≤ Module.finrank (ZMod 2) U' :=
          Submodule.finrank_mono (fun _ hx => hx.1)
        have hU'_lt : Module.finrank (ZMod 2) U' < k := by omega
        have hev' := ih (Module.finrank (ZMod 2) U') hU'_lt U' rfl
        rw [hrad_eq] at hev' hle_rad
        rcases hev' with ⟨t, ht⟩
        refine ⟨t + 1, ?_⟩
        omega
  exact hstrong (Module.finrank (ZMod 2) W) W rfl

lemma even_finrank_range_alt {r : ℕ}
    (A : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (halt : ∀ v, dotProduct v (A v) = 0) :
    Even (Module.finrank (ZMod 2) (LinearMap.range A)) := by
  have hsymm : ∀ u v, dotProduct u (A v) = dotProduct v (A u) := by
    intro u v
    have h := halt (u + v)
    rw [map_add, add_dotProduct, dotProduct_add, dotProduct_add, halt u, halt v,
      zero_add, add_zero] at h
    exact z2_eq_of_add_eq_zero h
  let B : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun u =>
        { toFun := fun v => dotProduct u (A v)
          map_add' := fun v₁ v₂ => by rw [map_add, dotProduct_add]
          map_smul' := fun s v => by rw [map_smul, dotProduct_smul, RingHom.id_apply] }
      map_add' := fun u₁ u₂ => by
        apply LinearMap.ext; intro v; exact add_dotProduct u₁ u₂ (A v)
      map_smul' := fun s u => by
        apply LinearMap.ext; intro v; exact smul_dotProduct s u (A v) }
  have hrad : radSub B ⊤ = LinearMap.ker A := by
    ext u
    change (u ∈ (⊤ : Submodule (ZMod 2) (Fin r → ZMod 2)) ∧
      ∀ v ∈ (⊤ : Submodule (ZMod 2) (Fin r → ZMod 2)), dotProduct u (A v) = 0) ↔ A u = 0
    constructor
    · intro h
      funext a
      have ha := h.2 (Pi.single a 1) Submodule.mem_top
      rw [hsymm, single_dotProduct, one_mul] at ha
      exact ha
    · intro h
      refine ⟨Submodule.mem_top, fun v _ => ?_⟩
      rw [hsymm, h, dotProduct_zero]
  have hev := even_codim_rad B halt hsymm ⊤
  rw [hrad, finrank_top] at hev
  have hrn := LinearMap.finrank_range_add_finrank_ker A
  have hsub : Module.finrank (ZMod 2) (Fin r → ZMod 2) - Module.finrank (ZMod 2) (LinearMap.ker A) =
      Module.finrank (ZMod 2) (LinearMap.range A) := by omega
  rwa [hsub] at hev

lemma q_anti {x w : ℕ} (h : w ≤ x) : (1:ℚ) / 2 ^ x ≤ 1 / 2 ^ w :=
  one_div_pow_le_one_div_pow_of_le (by norm_num) h

lemma q_succ (x : ℕ) : (1:ℚ) / 2 ^ (x + 1) = (1 / 2 ^ x) / 2 := by
  rw [pow_succ]; field_simp

lemma q_pos (x : ℕ) : 0 < (1:ℚ) / 2 ^ x := by positivity

lemma q_le_half {x : ℕ} (h : 1 ≤ x) : (1:ℚ) / 2 ^ x ≤ 1 / 2 :=
  calc (1:ℚ) / 2 ^ x ≤ 1 / 2 ^ 1 := q_anti h
    _ = 1 / 2 := by norm_num

lemma q_le_quarter {x : ℕ} (h : 2 ≤ x) : (1:ℚ) / 2 ^ x ≤ 1 / 4 :=
  calc (1:ℚ) / 2 ^ x ≤ 1 / 2 ^ 2 := q_anti h
    _ = 1 / 4 := by norm_num

lemma qB {x w : ℕ} (h : w ≤ x + 1) (hx : 1 ≤ x) : (1:ℚ) / 2 ^ x ≤ 1 / 2 ^ w + 1 / 4 := by
  rcases Nat.lt_or_ge x w with hlt | hge
  · have hw : w = x + 1 := by omega
    subst hw
    rw [q_succ]
    have := q_le_half hx
    linarith
  · have := q_anti hge
    linarith

lemma comb (h0 h1 h2 h3 w1 w2 w3 : ℕ) (c01 : w1 ≤ h0 + h1) (c02 : w2 ≤ h0 + h2)
    (c03 : w3 ≤ h0 + h3) (c12 : w3 ≤ h1 + h2) (c13 : w2 ≤ h1 + h3) (c23 : w1 ≤ h2 + h3)
    (m1 : h0 ≤ h1) (m2 : h0 ≤ h2) (m3 : h0 ≤ h3)
    (hex : ¬ (h0 = 1 ∧ h1 = 1 ∧ h2 = 1 ∧ h3 = 1 ∧ w1 = 2 ∧ w2 = 2 ∧ w3 = 2)) :
    (1:ℚ) / 2 ^ h0 + 1 / 2 ^ h1 + 1 / 2 ^ h2 + 1 / 2 ^ h3 ≤
      1 + 1 / 2 ^ w1 + 1 / 2 ^ w2 + 1 / 2 ^ w3 := by
  have p1 := q_pos w1
  have p2 := q_pos w2
  have p3 := q_pos w3
  rcases Nat.lt_or_ge h0 1 with hz | hone
  · have e : h0 = 0 := by omega
    subst e
    have := q_anti (show w1 ≤ h1 by omega)
    have := q_anti (show w2 ≤ h2 by omega)
    have := q_anti (show w3 ≤ h3 by omega)
    rw [pow_zero, div_one]
    linarith
  rcases Nat.lt_or_ge h0 2 with ho | htwo
  · have e : h0 = 1 := by omega
    subst e
    have e0 : (1:ℚ) / 2 ^ 1 = 1 / 2 := by norm_num
    rw [e0]
    by_cases d1 : w1 ≤ h1
    · have := q_anti d1
      have := qB (show w2 ≤ h2 + 1 by omega) (by omega)
      have := qB (show w3 ≤ h3 + 1 by omega) (by omega)
      linarith
    by_cases d2 : w2 ≤ h2
    · have := q_anti d2
      have := qB (show w1 ≤ h1 + 1 by omega) (by omega)
      have := qB (show w3 ≤ h3 + 1 by omega) (by omega)
      linarith
    by_cases d3 : w3 ≤ h3
    · have := q_anti d3
      have := qB (show w1 ≤ h1 + 1 by omega) (by omega)
      have := qB (show w2 ≤ h2 + 1 by omega) (by omega)
      linarith
    have hw1 : w1 = h1 + 1 := by omega
    have hw2 : w2 = h2 + 1 := by omega
    have hw3 : w3 = h3 + 1 := by omega
    subst hw1 hw2 hw3
    rw [q_succ, q_succ, q_succ]
    have t1 := q_le_half (show 1 ≤ h1 by omega)
    have t2 := q_le_half (show 1 ≤ h2 by omega)
    have t3 := q_le_half (show 1 ≤ h3 by omega)
    have hc : (2 ≤ h1 ∧ 2 ≤ h2) ∨ (2 ≤ h1 ∧ 2 ≤ h3) ∨ (2 ≤ h2 ∧ 2 ≤ h3) := by omega
    rcases hc with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · have := q_le_quarter a
      have := q_le_quarter b
      linarith
    · have := q_le_quarter a
      have := q_le_quarter b
      linarith
    · have := q_le_quarter a
      have := q_le_quarter b
      linarith
  · have := q_le_quarter htwo
    have := q_le_quarter (show 2 ≤ h1 by omega)
    have := q_le_quarter (show 2 ≤ h2 by omega)
    have := q_le_quarter (show 2 ≤ h3 by omega)
    linarith

def e1 : Fin 2 → ZMod 2 := fun i => if i = 0 then 1 else 0

def e2 : Fin 2 → ZMod 2 := fun i => if i = 0 then 0 else 1

lemma univE : (Finset.univ : Finset (Fin 2 → ZMod 2)) = {0, e1, e2, e1 + e2} := by
  decide

lemma sumE (f : (Fin 2 → ZMod 2) → ℚ) : ∑ a, f a = f 0 + f e1 + f e2 + f (e1 + e2) := by
  rw [univE, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

lemma idA (x y : Fin 2 → ZMod 2) : x + (x + y) = y := by
  funext i
  simp only [Pi.add_apply]
  exact (by decide : ∀ p q : ZMod 2, p + (p + q) = q) _ _

lemma idB (x y z : Fin 2 → ZMod 2) : (x + y) + (x + z) = y + z := by
  funext i
  simp only [Pi.add_apply]
  exact (by decide : ∀ p q r : ZMod 2, (p + q) + (p + r) = q + r) _ _ _

lemma idC (x y : Fin 2 → ZMod 2) : y + (x + y) = x := by
  funext i
  simp only [Pi.add_apply]
  exact (by decide : ∀ p q : ZMod 2, q + (p + q) = p) _ _

lemma final (G W : (Fin 2 → ZMod 2) → ℕ) (hW0 : W 0 = 0)
    (hpw : ∀ a a', W (a + a') ≤ G a + G a')
    (hex : ∀ b, G b = 1 → G (b + e1) = 1 → G (b + e2) = 1 → G (b + (e1 + e2)) = 1 →
      W e1 = 2 → W e2 = 2 → W (e1 + e2) = 2 → False) :
    ∑ a, (1:ℚ) / 2 ^ (G a) ≤ ∑ a, (1:ℚ) / 2 ^ (W a) := by
  obtain ⟨b, -, hb⟩ := Finset.exists_min_image Finset.univ G Finset.univ_nonempty
  have hL : ∑ a, (1:ℚ) / 2 ^ (G a) = ∑ a, (1:ℚ) / 2 ^ (G (b + a)) :=
    (Equiv.sum_comp (Equiv.addLeft b) (fun a => (1:ℚ) / 2 ^ (G a))).symm
  rw [hL, sumE, sumE, add_zero, hW0, pow_zero, div_one]
  have c01 := hpw b (b + e1)
  have c02 := hpw b (b + e2)
  have c03 := hpw b (b + (e1 + e2))
  have c12 := hpw (b + e1) (b + e2)
  have c13 := hpw (b + e1) (b + (e1 + e2))
  have c23 := hpw (b + e2) (b + (e1 + e2))
  rw [idA] at c01 c02 c03
  rw [idB] at c12 c13 c23
  rw [idA] at c13
  rw [idC] at c23
  refine comb _ _ _ _ _ _ _ c01 c02 c03 c12 c13 c23 (hb _ (Finset.mem_univ _))
    (hb _ (Finset.mem_univ _)) (hb _ (Finset.mem_univ _)) ?_
  rintro ⟨q0, q1, q2, q3, v1, v2, v3⟩
  exact hex b q0 q1 q2 q3 v1 v2 v3

section LA

variable {m n : ℕ}

def bas (n : ℕ) (i : Fin n) : Fin n → ZMod 2 := fun j => if i = j then 1 else 0

def Pm (P : (Fin n → ZMod 2) →ₗ[ZMod 2] ((Fin m × Bool) → ZMod 2)) :
    Matrix (Fin m × Bool) (Fin n) (ZMod 2) := Matrix.of fun x i => P (bas n i) x

def Qm (P : (Fin n → ZMod 2) →ₗ[ZMod 2] ((Fin m × Bool) → ZMod 2)) :
    Matrix (Fin m × Bool) (Fin n) (ZMod 2) := Matrix.of fun x i => P (bas n i) (x.1, !x.2)

def cv (C : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) (a : Fin 2 → ZMod 2) :
    Fin m × Bool → ZMod 2 := fun x => C a x.1

def om (C : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (P : (Fin n → ZMod 2) →ₗ[ZMod 2] ((Fin m × Bool) → ZMod 2)) (a : Fin 2 → ZMod 2) :
    Matrix (Fin n) (Fin n) (ZMod 2) := Matrix.of fun i j : Fin n =>
  ∑ t : Fin m, C a t * (P (bas n i) (t, false) * P (bas n j) (t, true) +
    P (bas n i) (t, true) * P (bas n j) (t, false))

def wtf (C : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) (a : Fin 2 → ZMod 2) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter (fun t => C a t ≠ 0)).card

variable (C : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
  (P : (Fin n → ZMod 2) →ₗ[ZMod 2] ((Fin m × Bool) → ZMod 2))

lemma Pm_mulVec (v : Fin n → ZMod 2) : (Pm P) *ᵥ v = P v := by
  conv_rhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  funext x
  simp only [Matrix.mulVec, dotProduct, Pm, Matrix.of_apply, Finset.sum_apply, map_smul,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma Qm_mulVec (v : Fin n → ZMod 2) : (Qm P) *ᵥ v = fun x => P v (x.1, !x.2) := by
  conv_rhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  funext x
  simp only [Matrix.mulVec, dotProduct, Qm, Matrix.of_apply, Finset.sum_apply, map_smul,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

variable {P} in
lemma Pm_rank (hP : Function.Surjective P) : (Pm P).rank = Fintype.card (Fin m × Bool) := by
  apply Matrix.mulVec_surjective_iff_rank_eq_card.mp
  intro y
  obtain ⟨v, hv⟩ := hP y
  exact ⟨v, by rw [Pm_mulVec, hv]⟩

variable {P} in
lemma Qm_rank (hP : Function.Surjective P) : (Qm P).rank = Fintype.card (Fin m × Bool) := by
  apply Matrix.mulVec_surjective_iff_rank_eq_card.mp
  intro y
  obtain ⟨v, hv⟩ := hP (fun x => y (x.1, !x.2))
  refine ⟨v, ?_⟩
  rw [Qm_mulVec, hv]
  funext x
  simp

variable {P} in
lemma PmT_inj (hP : Function.Surjective P) : Function.Injective (Pm P)ᵀ.mulVec := by
  have hr : (Pm P)ᵀ.rank = Fintype.card (Fin m × Bool) := by
    rw [Matrix.rank_transpose, Pm_rank hP]
  have hrn := LinearMap.finrank_range_add_finrank_ker ((Pm P)ᵀ.mulVecLin)
  rw [Matrix.rank] at hr
  rw [hr, Module.finrank_fintype_fun_eq_card] at hrn
  have hk : LinearMap.ker (Pm P)ᵀ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have := LinearMap.ker_eq_bot.mp hk
  exact fun a b h => this h

lemma om_eq (a : Fin 2 → ZMod 2) :
    om C P a = (Pm P)ᵀ * (Matrix.diagonal (cv C a) * Qm P) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [om, Matrix.of_apply, Matrix.transpose_apply, Matrix.diagonal_mul, Pm, Qm, cv,
    Fintype.sum_prod_type, Fintype.sum_bool, Bool.not_true, Bool.not_false]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  ring

lemma om_add (a b : Fin 2 → ZMod 2) : om C P (a + b) = om C P a + om C P b := by
  ext i j
  simp only [om, Matrix.of_apply, Matrix.add_apply, map_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

lemma om_diag (a : Fin 2 → ZMod 2) (i : Fin n) : om C P a i i = 0 := by
  simp only [om, Matrix.of_apply]
  apply Finset.sum_eq_zero
  intro t _
  rw [(by decide : ∀ u v : ZMod 2, u * v + v * u = 0), mul_zero]

lemma om_symm (a : Fin 2 → ZMod 2) (i j : Fin n) : om C P a i j = om C P a j i := by
  simp only [om, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun t _ => by ring)

lemma even_rank (A : Matrix (Fin n) (Fin n) (ZMod 2)) (hd : ∀ i, A i i = 0)
    (hs : ∀ i j, A i j = A j i) : Even A.rank := by
  apply even_finrank_range_alt A.mulVecLin
  intro v
  rw [Matrix.mulVecLin_apply]
  have h := symm_zero_diag_sum Finset.univ (fun i j => v i * A i j * v j)
    (fun i => by show v i * A i i * v i = 0; rw [hd]; ring)
    (fun i j => by show v i * A i j * v j = v j * A j i * v i; rw [hs i j]; ring)
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [← h]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma rank_add_le' (A B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

variable {P} in
lemma rank_om (hP : Function.Surjective P) (a : Fin 2 → ZMod 2) :
    (om C P a).rank = 2 * wtf C a := by
  rw [om_eq]
  have h1 := Matrix.rank_mul_ge (Pm P)ᵀ (Matrix.diagonal (cv C a) * Qm P)
  have h2 := Matrix.rank_mul_ge (Matrix.diagonal (cv C a)) (Qm P)
  have h3 := Matrix.rank_mul_le_right (Pm P)ᵀ (Matrix.diagonal (cv C a) * Qm P)
  have h4 := Matrix.rank_mul_le_left (Matrix.diagonal (cv C a)) (Qm P)
  have hd : (Matrix.diagonal (cv C a)).rank = 2 * wtf C a := by
    rw [Matrix.rank_diagonal, Fintype.card_subtype]
    have hf : (Finset.univ.filter fun x : Fin m × Bool => cv C a x ≠ 0) =
        ((Finset.univ : Finset (Fin m)).filter (fun t => C a t ≠ 0)) ×ˢ
          (Finset.univ : Finset Bool) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true]
      exact Iff.rfl
    rw [hf, Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]
    rfl
  rw [Matrix.rank_transpose, Pm_rank hP] at h1
  rw [Qm_rank hP] at h2
  omega

lemma range_om (a : Fin 2 → ZMod 2) (x : Fin n → ZMod 2)
    (hx : x ∈ LinearMap.range (om C P a).mulVecLin) :
    ∃ y, x = (Pm P)ᵀ *ᵥ y ∧ ∀ t b, C a t = 0 → y (t, b) = 0 := by
  obtain ⟨v, rfl⟩ := hx
  refine ⟨Matrix.diagonal (cv C a) *ᵥ (Qm P *ᵥ v), ?_, ?_⟩
  · rw [Matrix.mulVecLin_apply, om_eq]
    simp only [Matrix.mulVec_mulVec]
  · intro t b h
    rw [Matrix.mulVec_diagonal]
    simp only [cv]
    rw [h, zero_mul]

lemma incl (X Y : Matrix (Fin n) (Fin n) (ZMod 2)) (hX : X.rank = 2) (hXY : (X + Y).rank = 2)
    (hY : Y.rank = 4) : LinearMap.range X.mulVecLin ≤ LinearMap.range Y.mulVecLin := by
  have hle : LinearMap.range Y.mulVecLin ≤
      LinearMap.range X.mulVecLin ⊔ LinearMap.range (X + Y).mulVecLin := by
    rintro _ ⟨v, rfl⟩
    have e : Y *ᵥ v = X *ᵥ v + (X + Y) *ᵥ v := by
      rw [Matrix.add_mulVec]
      funext i
      simp only [Pi.add_apply]
      exact (by decide : ∀ p q : ZMod 2, q = p + (p + q)) _ _
    rw [Matrix.mulVecLin_apply, e]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    have := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range X.mulVecLin)
      (LinearMap.range (X + Y).mulVecLin)
    unfold Matrix.rank at hX hXY hY
    omega)
  calc LinearMap.range X.mulVecLin ≤
      LinearMap.range X.mulVecLin ⊔ LinearMap.range (X + Y).mulVecLin := le_sup_left
    _ = LinearMap.range Y.mulVecLin := heq.symm

variable {P} in
lemma no_exc (hP : Function.Surjective P) (K' : Matrix (Fin n) (Fin n) (ZMod 2))
    (a1 a2 : Fin 2 → ZMod 2) (h0 : K'.rank = 2) (h1 : (K' + om C P a1).rank = 2)
    (h2 : (K' + om C P a2).rank = 2) (h3 : (K' + om C P (a1 + a2)).rank = 2)
    (w1 : (om C P a1).rank = 4) (w2 : (om C P a2).rank = 4)
    (w3 : (om C P (a1 + a2)).rank = 4) : False := by
  have i1 := incl _ _ h0 h1 w1
  have i2 := incl _ _ h0 h2 w2
  have i3 := incl _ _ h0 h3 w3
  have hbot : LinearMap.range K'.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y1, e1', s1⟩ := range_om C P a1 x (i1 hx)
    obtain ⟨y2, e2', s2⟩ := range_om C P a2 x (i2 hx)
    obtain ⟨y3, e3', s3⟩ := range_om C P (a1 + a2) x (i3 hx)
    have hinj := PmT_inj hP
    have y12 : y1 = y2 := hinj (e1'.symm.trans e2')
    have y13 : y1 = y3 := hinj (e1'.symm.trans e3')
    have hy : y1 = 0 := by
      funext ⟨t, b⟩
      by_cases c1 : C a1 t = 0
      · exact s1 t b c1
      by_cases c2 : C a2 t = 0
      · rw [y12]; exact s2 t b c2
      rw [y13]
      apply s3 t b
      rw [map_add, Pi.add_apply, z2_eq_one_of_ne_zero c1, z2_eq_one_of_ne_zero c2]
      decide
    rw [Submodule.mem_bot, e1', hy, Matrix.mulVec_zero]
  have : K'.rank = 0 := by
    unfold Matrix.rank
    rw [hbot, finrank_bot]
  omega

variable {P} in
theorem main (hP : Function.Surjective P) :
    (∀ K : Matrix (Fin n) (Fin n) (ZMod 2), (∀ i, K i i = 0) → (∀ i j, K i j = K j i) →
      ∑ a : Fin 2 → ZMod 2, (1 : ℚ) / 2 ^ ((K + om C P a).rank / 2) ≤
        ∑ a : Fin 2 → ZMod 2, (1 : ℚ) / 2 ^ (wtf C a)) ∧
    ∑ a : Fin 2 → ZMod 2, (1 : ℚ) / 2 ^ (((0 : Matrix (Fin n) (Fin n) (ZMod 2)) + om C P a).rank / 2) =
      ∑ a : Fin 2 → ZMod 2, (1 : ℚ) / 2 ^ (wtf C a) := by
  refine ⟨fun K hd hs => ?_, ?_⟩
  · have hev : ∀ a, Even (K + om C P a).rank := fun a =>
      even_rank _ (fun i => by rw [Matrix.add_apply, hd, om_diag, add_zero])
        (fun i j => by rw [Matrix.add_apply, Matrix.add_apply, hs, om_symm])
    have hsum : ∀ a a', om C P (a + a') = (K + om C P a) + (K + om C P a') := by
      intro a a'
      rw [om_add]
      ext i j
      simp only [Matrix.add_apply]
      exact (by decide : ∀ x y z : ZMod 2, y + z = x + y + (x + z)) _ _ _
    refine final (fun a => (K + om C P a).rank / 2) (wtf C) ?_ ?_ ?_
    · simp [wtf]
    · intro a a'
      have h2 := rank_add_le' (K + om C P a) (K + om C P a')
      rw [← hsum, rank_om C hP] at h2
      obtain ⟨k1, hk1⟩ := hev a
      obtain ⟨k2, hk2⟩ := hev a'
      omega
    · intro b q0 q1 q2 q3 v1 v2 v3
      have r : ∀ a, (K + om C P a).rank / 2 = 1 → (K + om C P a).rank = 2 := by
        intro a ha
        obtain ⟨k, hk⟩ := hev a
        omega
      have s : ∀ a, (K + om C P b + om C P a) = K + om C P (b + a) := by
        intro a
        rw [add_assoc, ← om_add]
      apply no_exc C hP (K + om C P b) e1 e2 (r b q0)
      · rw [s]; exact r _ q1
      · rw [s]; exact r _ q2
      · rw [s]; exact r _ q3
      · rw [rank_om C hP, v1]
      · rw [rank_om C hP, v2]
      · rw [rank_om C hP, v3]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [zero_add, rank_om C hP, Nat.mul_div_cancel_left _ (by norm_num)]

end LA

end PEqualNP.Outside.L_lib_922

open PEqualNP.Outside.L_lib_922 in
theorem PEqualNP.Outside.L_lib_922 : ∀ m n : ℕ,
  let F := ZMod 2
  let V := Fin n → F
  let E := Fin 2 → F
  let D := (Fin m × Bool) → F
  let M := Matrix (Fin n) (Fin n) F
  let basis := fun (i j : Fin n) => if i = j then (1 : F) else 0
  ∀ (C : E →ₗ[F] (Fin m → F)) (P : V →ₗ[F] D), Function.Injective C →
    Function.Surjective P →
    let wt := fun (a : E) => ((Finset.univ : Finset (Fin m)).filter (fun t => C a t ≠ 0)).card
    let omega := fun (a : E) => Matrix.of (fun i j : Fin n =>
      ∑ t : Fin m, C a t * (P (basis i) (t,false) * P (basis j) (t,true) +
        P (basis i) (t,true) * P (basis j) (t,false)))
    let score := fun (K : M) => ∑ a : E, (1 : ℚ) / 2^((K + omega a).rank / 2)
    let target := ∑ a : E, (1 : ℚ) / 2^(wt a)
    (∀ K : M, (∀ i, K i i = 0) → (∀ i j, K i j = K j i) → score K ≤ target) ∧
      score 0 = target := by
  intro m n F V E D M basis C P hC hP wt omega score target
  exact main C hP

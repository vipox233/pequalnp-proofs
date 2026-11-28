import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1043

open Finset Matrix

def dl {n : ℕ} (i j : Fin n) : ℝ := if i = j then 1 else 0

section moments
variable {z n : ℕ} (e : Fin z → Fin n → ℝ) (he : ∀ s i, e s i * e s i = 1)
  (H : ∀ I : Finset (Fin n), I.Nonempty → I.card ≤ 4 → (∑ s, ∏ i ∈ I, e s i) = 0)
include H

theorem S2 {i j : Fin n} (hij : i ≠ j) : ∑ s, e s i * e s j = 0 := by
  have := H {i, j} (by simp) (by rw [card_pair hij]; norm_num)
  simpa [prod_pair hij] using this

theorem S4 {i j k l : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) : ∑ s, e s i * e s j * e s k * e s l = 0 := by
  have := H {i, j, k, l} (by simp) card_le_four
  simp only [prod_insert (show i ∉ ({j, k, l} : Finset _) by simp [hij, hik, hil]),
    prod_insert (show j ∉ ({k, l} : Finset _) by simp [hjk, hjl]), prod_pair hkl] at this
  simpa [mul_assoc] using this

include he

theorem E4 (i j k l : Fin n) : ∑ s, e s i * e s j * e s k * e s l =
    z * (dl i j * dl k l + dl i k * dl j l + dl i l * dl j k - 2 * (dl i j * dl j k * dl k l)) := by
  rcases eq_or_ne i j with rfl | hij
  · rcases eq_or_ne k l with rfl | hkl
    · have h : ∀ s, e s i * e s i * e s k * e s k = 1 := fun s => by
        linear_combination (e s k * e s k) * he s i + he s k
      rw [sum_congr rfl fun s _ => h s]
      clear h; clear H he; simp only [dl]; split_ifs <;> (try subst_vars) <;> first | contradiction | norm_num
    · have h : ∀ s, e s i * e s i * e s k * e s l = e s k * e s l := fun s => by
        linear_combination (e s k * e s l) * he s i
      rw [sum_congr rfl fun s _ => h s, S2 e H hkl]
      clear h; clear H he; simp only [dl]; split_ifs <;> (try subst_vars) <;> first | contradiction | norm_num
  · rcases eq_or_ne k l with rfl | hkl
    · have h : ∀ s, e s i * e s j * e s k * e s k = e s i * e s j := fun s => by
        linear_combination (e s i * e s j) * he s k
      rw [sum_congr rfl fun s _ => h s, S2 e H hij]
      clear h; clear H he; simp only [dl]; split_ifs <;> (try subst_vars) <;> first | contradiction | norm_num
    · rcases eq_or_ne i k with rfl | hik
      · rcases eq_or_ne j l with rfl | hjl
        · have h : ∀ s, e s i * e s j * e s i * e s j = 1 := fun s => by
            linear_combination (e s j * e s j) * he s i + he s j
          rw [sum_congr rfl fun s _ => h s]
          clear h; clear H he; simp only [dl]; split_ifs <;> (try subst_vars) <;> first | contradiction | norm_num
        · have h : ∀ s, e s i * e s j * e s i * e s l = e s j * e s l := fun s => by
            linear_combination (e s j * e s l) * he s i
          rw [sum_congr rfl fun s _ => h s, S2 e H hjl]
          clear h; clear H he; simp only [dl]; split_ifs <;> (try subst_vars) <;> first | contradiction | norm_num
      · rcases eq_or_ne i l with rfl | hil
        · rcases eq_or_ne j k with rfl | hjk
          · have h : ∀ s, e s i * e s j * e s j * e s i = 1 := fun s => by
              linear_combination (e s j * e s j) * he s i + he s j
            rw [sum_congr rfl fun s _ => h s]
            clear h; clear H he; simp only [dl]; split_ifs <;> (try subst_vars) <;> first | contradiction | norm_num
          · have h : ∀ s, e s i * e s j * e s k * e s i = e s j * e s k := fun s => by
              linear_combination (e s j * e s k) * he s i
            rw [sum_congr rfl fun s _ => h s, S2 e H hjk]
            clear h; clear H he; simp only [dl]; split_ifs <;> (try subst_vars) <;> first | contradiction | norm_num
        · rcases eq_or_ne j k with rfl | hjk
          · have h : ∀ s, e s i * e s j * e s j * e s l = e s i * e s l := fun s => by
              linear_combination (e s i * e s l) * he s j
            rw [sum_congr rfl fun s _ => h s, S2 e H hil]
            clear h; clear H he; simp only [dl]; split_ifs <;> (try subst_vars) <;> first | contradiction | norm_num
          · rcases eq_or_ne j l with rfl | hjl
            · have h : ∀ s, e s i * e s j * e s k * e s j = e s i * e s k := fun s => by
                linear_combination (e s i * e s k) * he s j
              rw [sum_congr rfl fun s _ => h s, S2 e H hik]
              clear h; clear H he; simp only [dl]; split_ifs <;> (try subst_vars) <;> first | contradiction | norm_num
            · rw [S4 e H hij hik hil hjk hjl hkl]
              clear H he; simp only [dl]; split_ifs <;> (try subst_vars) <;> first | contradiction | norm_num

theorem E2 (i j : Fin n) : ∑ s, e s i * e s j = z * dl i j := by
  rcases eq_or_ne i j with rfl | hij
  · simp [he, dl]
  · rw [S2 e H hij]; simp [dl, hij]

theorem M2 (v : Fin n → ℝ) : ∑ s, (∑ i, v i * e s i) ^ 2 = z * ∑ i, v i ^ 2 := by
  have h1 : ∀ s, (∑ i, v i * e s i) ^ 2 = ∑ i, ∑ j, v i * v j * (e s i * e s j) := by
    intro s; rw [sq, sum_mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [sum_congr rfl fun s _ => h1 s, sum_comm]
  rw [sum_congr rfl fun i _ => sum_comm]
  simp only [← mul_sum, E2 e he H]
  simp [dl, mul_sum, sq]
  exact sum_congr rfl fun i _ => by ring

theorem M4 (v : Fin n → ℝ) : ∑ s, (∑ i, v i * e s i) ^ 4 =
    z * (3 * (∑ i, v i ^ 2) ^ 2 - 2 * ∑ i, v i ^ 4) := by
  have h2 : ∀ s, (∑ i, v i * e s i) ^ 2 =
      ∑ p : Fin n × Fin n, v p.1 * v p.2 * (e s p.1 * e s p.2) := by
    intro s; rw [sq, sum_mul_sum, Fintype.sum_prod_type]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have h4 : ∀ s, (∑ i, v i * e s i) ^ 4 = ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
      v p.1 * v p.2 * v q.1 * v q.2 * (e s p.1 * e s p.2 * e s q.1 * e s q.2) := by
    intro s; rw [show 4 = 2 * 2 by rfl, pow_mul, h2, sq, sum_mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [sum_congr rfl fun s _ => h4 s, sum_comm]
  rw [sum_congr rfl fun p _ => sum_comm]
  simp only [← mul_sum, E4 e he H]
  simp only [Fintype.sum_prod_type]
  simp [dl, mul_sum, sum_add_distrib, sum_sub_distrib, mul_add, mul_sub, sq, mul_ite]
  have e1 : ∀ x, ∑ y, v x * v x * v y * v y * (z : ℝ) = z * (v x * v x) * ∑ y, v y * v y := by
    intro x; rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
  have e2 : ∀ x, ∑ y, v x * v y * v x * v y * (z : ℝ) = z * (v x * v x) * ∑ y, v y * v y := by
    intro x; rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
  have e3 : ∀ x, ∑ y, v x * v y * v y * v x * (z : ℝ) = z * (v x * v x) * ∑ y, v y * v y := by
    intro x; rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
  simp only [e1, e2, e3]
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

theorem key (v a : Fin n → ℝ) : ∑ i, v i * (2 * z * a i / (1 + 3 * ∑ j, a j ^ 2)) ≤
    ∑ s, |∑ i, v i * e s i| := by
  have hN : 0 ≤ ∑ j, a j ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 < 1 + 3 * ∑ j, a j ^ 2 := by linarith
  have hW : 0 ≤ ∑ i, v i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  rcases hW.eq_or_lt with hW0 | hWpos
  · have hv : ∀ i, v i = 0 := by
      intro i
      have := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).1 hW0.symm i (mem_univ _)
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    simp [hv]
  · set W := ∑ i, v i ^ 2 with hWdef
    set N := ∑ j, a j ^ 2 with hNdef
    set t := Real.sqrt (3 * W) with htdef
    have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
    have ht2 : t ^ 2 = 3 * W := Real.sq_sqrt (by linarith)
    have pw : ∀ s, 3 * t ^ 2 * (∑ i, v i * e s i) ^ 2 ≤
        2 * t ^ 3 * |∑ i, v i * e s i| + (∑ i, v i * e s i) ^ 4 := by
      intro s
      set Y := ∑ i, v i * e s i
      have hu := abs_nonneg Y
      have h1 : Y ^ 2 = |Y| ^ 2 := (sq_abs _).symm
      have h2 : Y ^ 4 = |Y| ^ 4 := by
        rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, h1]
      rw [h1, h2]
      have : 0 ≤ |Y| * ((|Y| - t) ^ 2 * (|Y| + 2 * t)) := by positivity
      nlinarith [this]
    have sumpw := sum_le_sum fun s (_ : s ∈ univ) => pw s
    rw [← mul_sum, sum_add_distrib, ← mul_sum, M2 e he H v, M4 e he H v] at sumpw
    have v4 : 0 ≤ ∑ i, v i ^ 4 := sum_nonneg (fun i _ => by positivity)
    have hz : (0 : ℝ) ≤ z := Nat.cast_nonneg z
    have hWt : W = t ^ 2 / 3 := by linarith
    rw [← hWdef, hWt] at sumpw
    have hA0 : 2 * t ^ 3 * ((z : ℝ) * t / 3) ≤ 2 * t ^ 3 * ∑ s, |∑ i, v i * e s i| := by
      nlinarith [mul_nonneg hz v4]
    have hA : (z : ℝ) * t / 3 ≤ ∑ s, |∑ i, v i * e s i| :=
      le_of_mul_le_mul_left hA0 (by positivity)
    have cs := sum_le_sum fun i (_ : i ∈ univ) =>
      (show 2 * t * (v i * a i) ≤ v i ^ 2 + t ^ 2 * a i ^ 2 by nlinarith [sq_nonneg (v i - t * a i)])
    rw [← mul_sum, sum_add_distrib, ← mul_sum] at cs
    have hP : 6 * ∑ i, v i * a i ≤ t * (1 + 3 * N) := by
      have : t * (6 * ∑ i, v i * a i) ≤ t * (t * (1 + 3 * N)) := by nlinarith
      exact le_of_mul_le_mul_left this ht
    have hL : ∑ i, v i * (2 * z * a i / (1 + 3 * N)) =
        ∑ i, (2 * z / (1 + 3 * N)) * (v i * a i) := sum_congr rfl fun i _ => by ring
    rw [hL, ← mul_sum, div_mul_eq_mul_div, div_le_iff₀ hD]
    nlinarith [mul_le_mul_of_nonneg_left hP hz]

theorem exists_real (a : Fin n → ℝ) : ∃ g : Fin z → ℝ, (∀ s, |g s| ≤ 1) ∧
    ∀ i, ∑ s, g s * e s i = 2 * z * a i / (1 + 3 * ∑ j, a j ^ 2) := by
  let Mt : Matrix (Fin n) (Fin z) ℝ := Matrix.of fun i s => e s i
  let L := Matrix.mulVecLin Mt
  let K := L '' Set.Icc (-1 : Fin z → ℝ) 1
  by_contra hno
  have hb : (fun i => 2 * z * a i / (1 + 3 * ∑ j, a j ^ 2)) ∉ K := by
    rintro ⟨g, hg, hgb⟩
    apply hno
    refine ⟨g, fun s => abs_le.2 ⟨hg.1 s, hg.2 s⟩, fun i => ?_⟩
    have := congrFun hgb i
    simp only [L, Mt, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply] at this
    rw [← this]; exact sum_congr rfl fun s _ => mul_comm _ _
  have hKc : IsCompact K := isCompact_Icc.image L.continuous_of_finiteDimensional
  obtain ⟨f, u, hfu, hK⟩ :=
    geometric_hahn_banach_point_closed ((convex_Icc _ _).linear_image L) hKc.isClosed hb
  let w : Fin n → ℝ := fun i => f (fun j => if i = j then 1 else 0)
  have hf : ∀ x, f x = ∑ i, x i * w i := fun x => by
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) x
    simpa [smul_eq_mul, w] using this
  let g : Fin z → ℝ := fun s => if 0 ≤ ∑ i, w i * e s i then -1 else 1
  have hgK : L g ∈ K := ⟨g, ⟨fun s => by simp only [g]; split_ifs <;> norm_num,
    fun s => by simp only [g]; split_ifs <;> norm_num⟩, rfl⟩
  have h1 := hK _ hgK
  rw [hf] at h1 hfu
  have h2 : ∑ i, (L g) i * w i = - ∑ s, |∑ i, w i * e s i| := by
    simp only [L, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Mt, Matrix.of_apply, sum_mul]
    rw [sum_comm, ← sum_neg_distrib]; refine sum_congr rfl fun s _ => ?_
    have : ∑ i, e s i * g s * w i = g s * ∑ i, w i * e s i := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    rw [this]; simp only [g]; split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.1 h)]; ring
  have key' := key e he H (fun i => - w i) a
  have e1 : ∀ s, |∑ i, -w i * e s i| = |∑ i, w i * e s i| := fun s => by
    rw [← abs_neg, ← sum_neg_distrib]; simp [neg_mul]
  simp only [e1] at key'
  have e2 : ∑ i, -w i * (2 * z * a i / (1 + 3 * ∑ j, a j ^ 2)) =
      - ∑ i, (2 * z * a i / (1 + 3 * ∑ j, a j ^ 2)) * w i := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun i _ => by ring
  rw [e2] at key'
  linarith

end moments

section vertex
variable {z n : ℕ} (e : Fin z → Fin n → ℝ) (b : Fin n → ℝ)

open Classical in
theorem vertex (g0 : Fin z → ℝ) (hb0 : ∀ s, |g0 s| ≤ 1) (he0 : ∀ i, ∑ s, g0 s * e s i = b i) :
    ∃ g : Fin z → ℝ, (∀ s, |g s| ≤ 1) ∧ (∀ i, ∑ s, g s * e s i = b i) ∧
      ∀ d : Fin z → ℝ, (∀ s, |g s| = 1 → d s = 0) → (∀ i, ∑ s, d s * e s i = 0) → d = 0 := by
  suffices h : ∀ m, ∀ g : Fin z → ℝ, (∀ s, |g s| ≤ 1) → (∀ i, ∑ s, g s * e s i = b i) →
      z - (univ.filter fun s => |g s| = 1).card = m →
      ∃ g : Fin z → ℝ, (∀ s, |g s| ≤ 1) ∧ (∀ i, ∑ s, g s * e s i = b i) ∧
      ∀ d : Fin z → ℝ, (∀ s, |g s| = 1 → d s = 0) → (∀ i, ∑ s, d s * e s i = 0) → d = 0 from
    h _ g0 hb0 he0 rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro g hgb hge hm
  by_cases hgood : ∀ d : Fin z → ℝ, (∀ s, |g s| = 1 → d s = 0) → (∀ i, ∑ s, d s * e s i = 0) → d = 0
  · exact ⟨g, hgb, hge, hgood⟩
  push Not at hgood
  obtain ⟨d, hdT, hdM, hd0⟩ := hgood
  obtain ⟨s1, hs1⟩ := Function.ne_iff.1 hd0
  let J := univ.filter fun s => d s ≠ 0
  let τ : Fin z → ℝ := fun s => if 0 < d s then (1 - g s) / d s else (-1 - g s) / d s
  obtain ⟨s0, hs0J, hmin⟩ := J.exists_min_image τ ⟨s1, by simp only [J, mem_filter, mem_univ, true_and]; simpa using hs1⟩
  have hs0 : d s0 ≠ 0 := by simpa [J] using hs0J
  have hlt : ∀ s, d s ≠ 0 → |g s| < 1 := fun s hs =>
    lt_of_le_of_ne (hgb s) (fun h => hs (hdT s h))
  have hτ : ∀ s, d s ≠ 0 → 0 ≤ τ s := by
    intro s hs
    have := abs_lt.1 (hlt s hs)
    simp only [τ]; split_ifs with h
    · exact div_nonneg (by linarith) h.le
    · exact div_nonneg_of_nonpos (by linarith) (not_lt.1 h)
  set t := τ s0
  have ht : 0 ≤ t := hτ s0 hs0
  let g' : Fin z → ℝ := fun s => g s + t * d s
  have hg'b : ∀ s, |g' s| ≤ 1 := by
    intro s
    by_cases hs : d s = 0
    · simp [g', hs, hgb s]
    have hts : t ≤ τ s := hmin s (by simp [J, hs])
    have hgs := abs_le.1 (hgb s)
    apply abs_le.2
    simp only [τ, g'] at hts ⊢
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · simp only [not_lt.2 hneg.le, ↓reduceIte] at hts
      rw [le_div_iff_of_neg hneg] at hts
      constructor <;> nlinarith
    · simp only [hpos, ↓reduceIte] at hts
      rw [le_div_iff₀ hpos] at hts
      constructor <;> nlinarith
  have hg'e : ∀ i, ∑ s, g' s * e s i = b i := by
    intro i
    have : ∑ s, g' s * e s i = ∑ s, g s * e s i + t * ∑ s, d s * e s i := by
      rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun s _ => by simp only [g']; ring
    rw [this, hge i, hdM i, mul_zero, add_zero]
  have hsub : (univ.filter fun s => |g s| = 1) ⊂ (univ.filter fun s => |g' s| = 1) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨s0, ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and, g', t]
        simp only [τ]; split_ifs <;> field_simp <;> norm_num
      · simp only [mem_filter, mem_univ, true_and]
        exact fun h => hs0 (hdT s0 h)
    · intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs ⊢
      simp [g', hdT s hs, hs]
  have hc := card_lt_card hsub
  have hle : (univ.filter fun s => |g' s| = 1).card ≤ z := by
    simpa using card_le_univ (univ.filter fun s => |g' s| = 1)
  exact ih _ (by omega) g' hg'b hg'e rfl

end vertex

theorem rat_sol {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k] (A : Matrix m k ℚ)
    (y : m → ℚ) (x : k → ℝ) (hx : (A.map (Rat.castHom ℝ)) *ᵥ x = fun r => (y r : ℝ))
    (hinj : ∀ d : k → ℝ, (A.map (Rat.castHom ℝ)) *ᵥ d = 0 → d = 0) :
    ∃ q : k → ℚ, ∀ j, x j = q j := by
  set f := Rat.castHom ℝ
  set Ar := A.map f
  set G := Aᵀ * A
  have hG : G.map f = Arᵀ * Ar := by simp only [G, Ar, Matrix.map_mul, Matrix.transpose_map]
  have hdet : (G.map f).det ≠ 0 := by
    intro h0
    obtain ⟨d, hd0, hd⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hd0; apply hinj
    rw [hG, ← Matrix.mulVec_mulVec] at hd
    have h3 : (Ar *ᵥ d) ⬝ᵥ (Ar *ᵥ d) = 0 := by
      have : d ⬝ᵥ (Arᵀ *ᵥ (Ar *ᵥ d)) = 0 := by rw [hd, dotProduct_zero]
      rwa [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at this
    exact dotProduct_self_eq_zero.1 h3
  have h1 : (G.map f).adjugate *ᵥ ((G.map f) *ᵥ x) = (G.map f).det • x := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 : (G.map f) *ᵥ x = Arᵀ *ᵥ (fun r => (y r : ℝ)) := by
    rw [hG, ← Matrix.mulVec_mulVec, hx]
  refine ⟨G.det⁻¹ • (G.adjugate *ᵥ (Aᵀ *ᵥ y)), fun j => ?_⟩
  have h3 : x j = (G.map f).det⁻¹ * ((G.map f).adjugate *ᵥ (Arᵀ *ᵥ (fun r => (y r : ℝ)))) j := by
    rw [← h2, h1, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hdet]
  rw [h3]
  show _ = f ((G.det⁻¹ • (G.adjugate *ᵥ (Aᵀ *ᵥ y))) j)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, RingHom.map_det, RingHom.map_mulVec,
    RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply f G.adjugate, RingHom.map_adjugate,
    RingHom.mapMatrix_apply]
  congr 3
  funext r
  rw [Function.comp_apply, RingHom.map_mulVec, Matrix.transpose_map]
  rfl

end PEqualNP.Outside.L_lib_1043

open PEqualNP.Outside.L_lib_1043 Matrix Finset in
theorem PEqualNP.Outside.L_lib_1043 : ∀ (n z : Nat), 0 < z → ∀ σ : Fin z → Fin n → Bool,
  let sign := fun (s : Fin z) (i : Fin n) => if σ s i then (1 : ℚ) else -1
  (∀ I : Finset (Fin n), I.Nonempty → I.card ≤ 4 →
    (∑ s : Fin z, ∏ i ∈ I, sign s i) = 0) →
  ∀ a : Fin n → ℚ,
    let normSq := ∑ i : Fin n, (a i)^2
    ∃ f : Fin z → ℚ, (∀ s, -1 ≤ f s ∧ f s ≤ 1) ∧
      ∀ i, (1+3*normSq)*(∑ s : Fin z, f s * sign s i) = 2*(z : ℚ)*a i := by
  intro n z _ σ sign hH a normSq
  classical
  let e : Fin z → Fin n → ℝ := fun s i => ((sign s i : ℚ) : ℝ)
  have he : ∀ s i, e s i * e s i = 1 := by
    intro s i; simp only [e, sign]; split_ifs <;> norm_num
  have H : ∀ I : Finset (Fin n), I.Nonempty → I.card ≤ 4 → (∑ s, ∏ i ∈ I, e s i) = 0 := by
    intro I h1 h2
    have := congrArg (fun q : ℚ => (q : ℝ)) (hH I h1 h2)
    simpa [e] using this
  let ar : Fin n → ℝ := fun i => (a i : ℝ)
  obtain ⟨g0, hg0b, hg0e⟩ := exists_real e he H ar
  obtain ⟨g, hgb, hge, hgood⟩ := vertex e _ g0 hg0b hg0e
  let A : Matrix (Fin n ⊕ Fin z) (Fin z) ℚ := Matrix.of fun r s =>
    Sum.elim (fun i => sign s i) (fun t => if |g t| = 1 ∧ s = t then 1 else 0) r
  let y : Fin n ⊕ Fin z → ℚ := Sum.elim (fun i => 2 * z * a i / (1 + 3 * normSq))
    (fun t => if |g t| = 1 then (if 0 < g t then 1 else -1) else 0)
  have hx : (A.map (Rat.castHom ℝ)) *ᵥ g = fun r => (y r : ℝ) := by
    funext r
    cases r with
    | inl i =>
      have h := hge i
      simp only [A, y, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply,
        Sum.elim_inl, Rat.coe_castHom]
      rw [sum_congr rfl fun s _ => mul_comm _ _]
      rw [h]; simp only [ar, normSq]; push_cast; rfl
    | inr t =>
      simp only [A, y, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply,
        Sum.elim_inr, Rat.coe_castHom]
      by_cases ht : |g t| = 1
      · simp only [ht, true_and, if_true]
        rw [sum_eq_single t (fun s _ hs => by simp [hs]) (by simp)]
        rcases (abs_eq zero_le_one).1 ht with h | h <;> norm_num [h]
      · simp [ht]
  have hinj : ∀ d : Fin z → ℝ, (A.map (Rat.castHom ℝ)) *ᵥ d = 0 → d = 0 := by
    intro d hd
    apply hgood d
    · intro s hs
      have := congrFun hd (Sum.inr s)
      simpa [A, Matrix.mulVec, dotProduct, hs, apply_ite (Rat.castHom ℝ), apply_ite ((Rat.cast : ℚ → ℝ)), ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this
    · intro i
      have := congrFun hd (Sum.inl i)
      simp only [A, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply,
        Sum.elim_inl, Rat.coe_castHom, Pi.zero_apply] at this
      rw [← this]; exact sum_congr rfl fun s _ => mul_comm _ _
  obtain ⟨q, hq⟩ := rat_sol A y g hx hinj
  refine ⟨q, fun s => ?_, fun i => ?_⟩
  · have := abs_le.1 (hgb s)
    rw [hq s] at this
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  · have h := hge i
    simp only [hq] at h
    have hD : (0 : ℝ) < 1 + 3 * ∑ j, ar j ^ 2 := by positivity
    have hr : ((1 + 3 * normSq : ℚ) : ℝ) * ((∑ s, q s * sign s i : ℚ) : ℝ) =
        ((2 * (z : ℚ) * a i : ℚ) : ℝ) := by
      have e3 : ((∑ s, q s * sign s i : ℚ) : ℝ) = ∑ s, (q s : ℝ) * e s i := by
        push_cast; rfl
      have e4 : ((1 + 3 * normSq : ℚ) : ℝ) = 1 + 3 * ∑ j, ar j ^ 2 := by
        simp only [normSq, ar]; push_cast; rfl
      rw [e3, e4, h]
      field_simp
      simp only [ar]; push_cast; ring
    exact_mod_cast hr

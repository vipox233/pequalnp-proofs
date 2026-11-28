import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_375_aux

open scoped BigOperators

def histDef {n : ℕ} (M : Bool → Fin n → Fin n) (pin : Bool × Fin n → Option Bool)
    (d : Fin (n + 1) × Fin (n + 1)) : ℕ :=
  ((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
    (∀ u, pin u = none ∨ pin u = some (x u)) ∧
    ∀ h : Bool, (Finset.univ.filter (fun i : Fin n =>
      x (false, i) ≠ x (true, M h i))).card = (if h then d.2 else d.1).val)).card

def ringDef (n : ℕ) [NeZero n] (h : Bool) (i : Fin n) : Fin n :=
  if h then i + 1 else i

def classesDef {n : ℕ} (M : Bool → Fin n → Fin n) : ℕ :=
  ((Finset.univ : Finset (Bool × Fin n → Option Bool)).image (histDef M)).card

def delta0 (d : ℕ × ℕ) : ℕ := if d = (0, 0) then 1 else 0

def conv (f g : ℕ × ℕ → ℕ) (d : ℕ × ℕ) : ℕ :=
  ∑ a ∈ Finset.range (d.1 + 1), ∑ b ∈ Finset.range (d.2 + 1),
    f (a, b) * g (d.1 - a, d.2 - b)

lemma conv_delta0_left (f : ℕ × ℕ → ℕ) : conv delta0 f = f := by
  funext ⟨d1, d2⟩
  unfold conv delta0
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      have : (0, b) ≠ (0, 0) := by intro h; exact hb (congrArg Prod.snd h)
      simp [this]
    · intro h; exfalso; exact h (Finset.mem_range.mpr (Nat.succ_pos _))
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    have : (a, b) ≠ (0, 0) := by intro h; exact ha (congrArg Prod.fst h)
    simp [this]
  · intro h; exfalso; exact h (Finset.mem_range.mpr (Nat.succ_pos _))

lemma sum_range_rev (d : ℕ) (F : ℕ → ℕ) :
    (∑ a ∈ Finset.range (d + 1), F a) = ∑ a ∈ Finset.range (d + 1), F (d - a) := by
  apply Finset.sum_nbij (fun a => d - a)
  · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
  · intro a1 ha1 a2 ha2 heq
    have h1 : a1 < d + 1 := Finset.mem_range.mp ha1
    have h2 : a2 < d + 1 := Finset.mem_range.mp ha2
    dsimp at heq; omega
  · intro b hb
    have h1 : b < d + 1 := Finset.mem_range.mp hb
    refine ⟨d - b, Finset.mem_range.mpr (by omega), ?_⟩
    dsimp; omega
  · intro a ha
    have h1 : a < d + 1 := Finset.mem_range.mp ha
    congr 1; omega

lemma conv_comm (f g : ℕ × ℕ → ℕ) : conv f g = conv g f := by
  funext ⟨d1, d2⟩
  unfold conv
  rw [sum_range_rev d1]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_range_rev d2]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Finset.mem_range] at ha hb
  rw [show d1 - (d1 - a) = a by omega, show d2 - (d2 - b) = b by omega]
  exact Nat.mul_comm _ _

lemma conv_delta0_right (f : ℕ × ℕ → ℕ) : conv f delta0 = f := by
  rw [conv_comm, conv_delta0_left]

lemma sum_range_triple (d : ℕ) (F : ℕ → ℕ → ℕ → ℕ) :
    (∑ a ∈ Finset.range (d + 1), ∑ b ∈ Finset.range (a + 1), F b (a - b) (d - a)) =
    ∑ b ∈ Finset.range (d + 1), ∑ c ∈ Finset.range (d - b + 1), F b c (d - b - c) := by
  have h1 : (∑ a ∈ Finset.range (d + 1), ∑ b ∈ Finset.range (a + 1), F b (a - b) (d - a)) =
      ∑ t ∈ (Finset.range (d + 1) ×ˢ Finset.range (d + 1)).filter (fun t => t.1 + t.2 ≤ d),
        F t.1 t.2 (d - t.1 - t.2) := by
    rw [Finset.sum_sigma']
    apply Finset.sum_nbij (fun s => (s.2, s.1 - s.2))
    · intro ⟨a, b⟩ h
      simp only [Finset.mem_sigma, Finset.mem_range] at h
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 heq
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at h1 h2
      dsimp at heq
      have hb : b1 = b2 := (Prod.mk.inj heq).1
      have ha : a1 = a2 := by have := (Prod.mk.inj heq).2; omega
      subst hb; subst ha; rfl
    · intro ⟨b, c⟩ h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
      refine ⟨⟨b + c, b⟩, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range]; omega
      · dsimp; ext <;> omega
    · intro ⟨a, b⟩ h
      simp only [Finset.mem_sigma, Finset.mem_range] at h
      dsimp; congr 1; omega
  have h2 : (∑ b ∈ Finset.range (d + 1), ∑ c ∈ Finset.range (d - b + 1), F b c (d - b - c)) =
      ∑ t ∈ (Finset.range (d + 1) ×ˢ Finset.range (d + 1)).filter (fun t => t.1 + t.2 ≤ d),
        F t.1 t.2 (d - t.1 - t.2) := by
    rw [Finset.sum_sigma']
    apply Finset.sum_nbij (fun s => (s.1, s.2))
    · intro ⟨b, c⟩ h
      simp only [Finset.mem_sigma, Finset.mem_range] at h
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro ⟨b1, c1⟩ _ ⟨b2, c2⟩ _ heq
      dsimp at heq
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩; rfl
    · intro ⟨b, c⟩ h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
      refine ⟨⟨b, c⟩, ?_, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range]; omega
    · intro _ _; rfl
  exact h1.trans h2.symm

lemma conv_assoc (f g h : ℕ × ℕ → ℕ) : conv (conv f g) h = conv f (conv g h) := by
  funext ⟨d1, d2⟩
  unfold conv
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  trans (∑ a ∈ Finset.range (d1 + 1), ∑ x ∈ Finset.range (a + 1),
      ∑ b ∈ Finset.range (d2 + 1), ∑ y ∈ Finset.range (b + 1),
        f (x, y) * g (a - x, b - y) * h (d1 - a, d2 - b))
  · apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm]
  rw [sum_range_triple d1 (fun x1 x2 x3 => ∑ b ∈ Finset.range (d2 + 1), ∑ y ∈ Finset.range (b + 1),
      f (x1, y) * g (x2, b - y) * h (x3, d2 - b))]
  apply Finset.sum_congr rfl; intro x1 _
  have hinner : ∀ x2 x3 : ℕ,
      (∑ b ∈ Finset.range (d2 + 1), ∑ y ∈ Finset.range (b + 1),
        f (x1, y) * g (x2, b - y) * h (x3, d2 - b)) =
      ∑ y1 ∈ Finset.range (d2 + 1), ∑ y2 ∈ Finset.range (d2 - y1 + 1),
        f (x1, y1) * (g (x2, y2) * h (x3, d2 - y1 - y2)) := by
    intro x2 x3
    rw [sum_range_triple d2 (fun y1 y2 y3 => f (x1, y1) * g (x2, y2) * h (x3, y3))]
    apply Finset.sum_congr rfl; intro y1 _
    apply Finset.sum_congr rfl; intro y2 _
    ring
  trans (∑ x2 ∈ Finset.range (d1 - x1 + 1), ∑ y1 ∈ Finset.range (d2 + 1),
      ∑ y2 ∈ Finset.range (d2 - y1 + 1), f (x1, y1) * (g (x2, y2) * h (d1 - x1 - x2, d2 - y1 - y2)))
  · apply Finset.sum_congr rfl; intro x2 _
    exact hinner x2 (d1 - x1 - x2)
  · rw [Finset.sum_comm]

def convList (L : List (ℕ × ℕ → ℕ)) : ℕ × ℕ → ℕ :=
  L.foldr conv delta0

lemma convList_perm {L1 L2 : List (ℕ × ℕ → ℕ)} (h : L1.Perm L2) :
    convList L1 = convList L2 := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [convList, List.foldr_cons]; exact congrArg (conv x) ih
  | swap x y l =>
    simp only [convList, List.foldr_cons]
    rw [← conv_assoc, conv_comm y x, conv_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

def segHist (r b : ℕ) (par : Bool) (d : ℕ × ℕ) : ℕ :=
  if (d.1 + d.2) % 2 = (if par then 1 else 0) then Nat.choose r d.1 * Nat.choose b d.2 else 0

lemma segHist_one_zero (d1 : ℕ) : segHist 1 1 false (d1, 0) = if d1 = 0 then 1 else 0 := by
  unfold segHist
  rcases d1 with _ | _ | d1
  · decide
  · decide
  · simp [Nat.choose_eq_zero_of_lt (show 1 < d1 + 2 by omega)]

lemma conv_zero_snd (f g : ℕ × ℕ → ℕ) (d1 : ℕ) :
    conv f g (d1, 0) = ∑ a ∈ Finset.range (d1 + 1), f (a, 0) * g (d1 - a, 0) := by
  unfold conv
  apply Finset.sum_congr rfl
  intro a _
  simp

lemma eval_poly_conv (f g : ℕ × ℕ → ℕ) (n1 n2 : ℕ)
    (hf : ∀ a, n1 < a → f (a, 0) = 0) (hg : ∀ b, n2 < b → g (b, 0) = 0) (z : ℂ) :
    (∑ d ∈ Finset.range (n1 + n2 + 1), (conv f g (d, 0) : ℂ) * z ^ d) =
    (∑ a ∈ Finset.range (n1 + 1), (f (a, 0) : ℂ) * z ^ a) *
    (∑ b ∈ Finset.range (n2 + 1), (g (b, 0) : ℂ) * z ^ b) := by
  rw [Finset.sum_mul_sum]
  simp_rw [conv_zero_snd, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
  symm
  rw [← Finset.sum_product']
  have hsub : ∀ p ∈ Finset.range (n1 + 1) ×ˢ Finset.range (n2 + 1),
      p.1 + p.2 ∈ Finset.range (n1 + n2 + 1) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hsub]
  apply Finset.sum_congr rfl
  intro d _
  have hring : (∑ p ∈ (Finset.range (n1 + 1) ×ˢ Finset.range (n2 + 1)).filter (fun p => p.1 + p.2 = d),
      (f (p.1, 0) : ℂ) * z ^ p.1 * ((g (p.2, 0) : ℂ) * z ^ p.2)) =
      ∑ p ∈ (Finset.range (n1 + 1) ×ˢ Finset.range (n2 + 1)).filter (fun p => p.1 + p.2 = d),
      (f (p.1, 0) : ℂ) * (g (p.2, 0) : ℂ) * z ^ (p.1 + p.2) := by
    apply Finset.sum_congr rfl; intro p _; rw [pow_add]; ring
  rw [hring]
  symm
  trans (∑ a ∈ (Finset.range (d + 1)).filter (fun a => a ≤ n1 ∧ d - a ≤ n2),
      (f (a, 0) : ℂ) * (g (d - a, 0) : ℂ) * z ^ d)
  · symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a ha hnot
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hnot
    by_cases h1 : a ≤ n1
    · have h2 : ¬ d - a ≤ n2 := fun h2 => hnot ha h1 h2
      simp [hg (d - a) (by omega)]
    · simp [hf a (by omega)]
  · apply Finset.sum_nbij (fun a => (a, d - a))
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro a1 _ a2 _ heq; exact (Prod.mk.inj heq).1
    · intro ⟨a, b⟩ hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
      refine ⟨a, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]; omega
      · dsimp; ext <;> omega
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      rw [show a + (d - a) = d by omega]

lemma eval_segHist_zero (L : ℕ) (z : ℂ) :
    (∑ d ∈ Finset.range (L + 1), (segHist L L false (d, 0) : ℂ) * z ^ d) =
    ((1 + z) ^ L + (1 - z) ^ L) / 2 := by
  have h1 : (1 + z) ^ L = ∑ d ∈ Finset.range (L + 1), (Nat.choose L d : ℂ) * z ^ d := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro d _
    simp [mul_comm]
  have h2 : (1 - z) ^ L = ∑ d ∈ Finset.range (L + 1), (Nat.choose L d : ℂ) * (-z) ^ d := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro d _
    simp [mul_comm]
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  unfold segHist
  simp only [Nat.add_zero, Bool.false_eq_true, ↓reduceIte, Nat.choose_zero_right, mul_one]
  by_cases he : d % 2 = 0
  · rw [if_pos he]
    have hev : Even d := Nat.even_iff.mpr he
    rw [hev.neg_pow]
    ring
  · rw [if_neg he]
    have hodd : Odd d := Nat.odd_iff.mpr (by omega)
    rw [hodd.neg_pow]
    ring

noncomputable def segPoly (L : ℕ) : Polynomial ℂ :=
  ((1 + Polynomial.X) ^ L + (1 - Polynomial.X) ^ L) * Polynomial.C (2⁻¹ : ℂ)

lemma eval_segPoly (L : ℕ) (z : ℂ) :
    (segPoly L).eval z = ((1 + z) ^ L + (1 - z) ^ L) / 2 := by
  simp [segPoly, div_eq_mul_inv]

lemma segPoly_ne_zero (L : ℕ) : segPoly L ≠ 0 := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  rw [eval_segPoly] at h0
  norm_num at h0

lemma poly_zero_distinct (S T : Finset ℕ) (hS : ∀ L ∈ S, 2 ≤ L) (hT : ∀ L ∈ T, 2 ≤ L)
    (heq : ∀ z : ℂ,
      (∏ L ∈ S, ((1 + z) ^ L + (1 - z) ^ L) / 2) =
      (∏ L ∈ T, ((1 + z) ^ L + (1 - z) ^ L) / 2)) : S = T := by
  have hpoly : (∏ L ∈ S, segPoly L) = ∏ L ∈ T, segPoly L := by
    apply Polynomial.funext
    intro z
    simp only [Polynomial.eval_prod, eval_segPoly]
    exact heq z
  have hdisjST : Disjoint (S \ T) (S ∩ T) :=
    Finset.sdiff_disjoint.mono_right Finset.inter_subset_right
  have hdisjTS : Disjoint (T \ S) (T ∩ S) :=
    Finset.sdiff_disjoint.mono_right Finset.inter_subset_right
  have hsplitS : (∏ L ∈ S, segPoly L) = (∏ L ∈ S \ T, segPoly L) * (∏ L ∈ S ∩ T, segPoly L) := by
    rw [← Finset.prod_union hdisjST, Finset.sdiff_union_inter]
  have hsplitT : (∏ L ∈ T, segPoly L) = (∏ L ∈ T \ S, segPoly L) * (∏ L ∈ S ∩ T, segPoly L) := by
    rw [Finset.inter_comm S T, ← Finset.prod_union hdisjTS, Finset.sdiff_union_inter]
  rw [hsplitS, hsplitT] at hpoly
  have hcommon_ne : (∏ L ∈ S ∩ T, segPoly L) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun L _ => segPoly_ne_zero L)
  have hcancel : (∏ L ∈ S \ T, segPoly L) = ∏ L ∈ T \ S, segPoly L :=
    mul_right_cancel₀ hcommon_ne hpoly
  by_contra hne
  have hsym : (symmDiff S T).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hne (symmDiff_eq_bot.mp h)
  let M := (symmDiff S T).max' hsym
  have hM_mem : M ∈ symmDiff S T := Finset.max'_mem _ hsym
  have hM_ge : 2 ≤ M := by
    rcases Finset.mem_symmDiff.mp hM_mem with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hS M h1
    · exact hT M h1
  let θ : ℝ := Real.pi / (M : ℝ)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hθpos : 0 < θ := div_pos Real.pi_pos hMpos
  have hθlt : θ < Real.pi := by
    dsimp [θ]
    rw [div_lt_iff₀ hMpos]
    have hM2 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (show 1 < M by omega)
    nlinarith [Real.pi_pos]
  let u : ℂ := Complex.exp (θ * Complex.I)
  have hu_ne : u + 1 ≠ 0 := by
    intro h
    have him : (u + 1).im = 0 := congrArg Complex.im h
    simp only [u, Complex.add_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, add_zero] at him
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
    linarith
  let z : ℂ := (u - 1) / (u + 1)
  have h1pz : 1 + z = 2 * u / (u + 1) := by
    dsimp [z]; field_simp [hu_ne]; ring
  have h1mz : 1 - z = 2 / (u + 1) := by
    dsimp [z]; field_simp [hu_ne]; ring
  have hfactor : ∀ L : ℕ, (segPoly L).eval z = (2 / (u + 1)) ^ L * (u ^ L + 1) / 2 := by
    intro L
    rw [eval_segPoly, h1pz, h1mz]
    have : (2 * u / (u + 1)) ^ L = (2 / (u + 1)) ^ L * u ^ L := by
      rw [← mul_pow]; congr 1; ring
    rw [this]; ring
  have hzeroM : (segPoly M).eval z = 0 := by
    rw [hfactor M]
    have huM : u ^ M = -1 := by
      dsimp [u]
      rw [← Complex.exp_nat_mul]
      have harg : (M : ℂ) * ((θ : ℂ) * Complex.I) = Real.pi * Complex.I := by
        dsimp [θ]
        have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
        push_cast
        field_simp [hMc]
      rw [harg, Complex.exp_pi_mul_I]
    rw [huM]; ring
  have hnz : ∀ L : ℕ, 1 ≤ L → L < M → (segPoly L).eval z ≠ 0 := by
    intro L hL1 hLM
    rw [hfactor L]
    have h2u : (2 / (u + 1)) ^ L ≠ 0 := pow_ne_zero L (div_ne_zero two_ne_zero hu_ne)
    have huL : u ^ L + 1 ≠ 0 := by
      intro h
      have him : (u ^ L + 1).im = 0 := congrArg Complex.im h
      have huLeq : u ^ L = Complex.exp ((((L : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
        dsimp [u]
        rw [← Complex.exp_nat_mul]
        congr 1; push_cast; ring
      rw [huLeq] at him
      simp only [Complex.add_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, add_zero] at him
      have hpos : 0 < (L : ℝ) * θ := mul_pos (by exact_mod_cast (show 0 < L by omega)) hθpos
      have hlt : (L : ℝ) * θ < Real.pi := by
        dsimp [θ]
        rw [mul_div_assoc', div_lt_iff₀ hMpos]
        have hLM' : (L : ℝ) < (M : ℝ) := by exact_mod_cast hLM
        nlinarith [Real.pi_pos]
      have hsin : 0 < Real.sin ((L : ℝ) * θ) := Real.sin_pos_of_pos_of_lt_pi hpos hlt
      linarith
    exact div_ne_zero (mul_ne_zero h2u huL) two_ne_zero
  have heval := congrArg (Polynomial.eval z) hcancel
  simp only [Polynomial.eval_prod] at heval
  rcases Finset.mem_symmDiff.mp hM_mem with ⟨hMS, hMT⟩ | ⟨hMT, hMS⟩
  · have hLHS : (∏ L ∈ S \ T, (segPoly L).eval z) = 0 :=
      Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hMS, hMT⟩) hzeroM
    have hRHS : (∏ L ∈ T \ S, (segPoly L).eval z) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro L hL
      have hLT : L ∈ T := (Finset.mem_sdiff.mp hL).1
      have hLsym : L ∈ symmDiff S T := Finset.mem_symmDiff.mpr (Or.inr (Finset.mem_sdiff.mp hL))
      have hLle : L ≤ M := Finset.le_max' _ L hLsym
      have hLne : L ≠ M := fun h => hMT (h ▸ hLT)
      exact hnz L (by have := hT L hLT; omega) (by omega)
    exact hRHS (heval.symm.trans hLHS)
  · have hRHS : (∏ L ∈ T \ S, (segPoly L).eval z) = 0 :=
      Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hMT, hMS⟩) hzeroM
    have hLHS : (∏ L ∈ S \ T, (segPoly L).eval z) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro L hL
      have hLS : L ∈ S := (Finset.mem_sdiff.mp hL).1
      have hLsym : L ∈ symmDiff S T := Finset.mem_symmDiff.mpr (Or.inl (Finset.mem_sdiff.mp hL))
      have hLle : L ≤ M := Finset.le_max' _ L hLsym
      have hLne : L ≠ M := fun h => hMS (h ▸ hLS)
      exact hnz L (by have := hS L hLS; omega) (by omega)
    exact hLHS (heval.trans hRHS)

def Part4 (m : ℕ) : Finset (Fin 4 × Fin m → Fin (m + 1)) :=
  Finset.univ.filter (fun c => ∑ p : Fin 4 × Fin m, (p.2.val + 1) * (c p).val = m)

lemma exp_quad_le (y : ℝ) (hy : 0 ≤ y) : 1 + y + y ^ 2 / 2 ≤ Real.exp y := by
  have h := Real.sum_le_exp_of_nonneg hy 3
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma sum_inv_sqrt_le (B : ℕ) :
    (∑ l ∈ Finset.range B, (1 : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)) ≤ 2 * Real.sqrt (B : ℝ) := by
  induction B with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hsq : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hk1
    have hle : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)
    have hdiff : (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) *
        (Real.sqrt ((k + 1 : ℕ) : ℝ) + Real.sqrt (k : ℝ)) = 1 := by
      have : (Real.sqrt ((k + 1 : ℕ) : ℝ)) ^ 2 - (Real.sqrt (k : ℝ)) ^ 2 = 1 := by
        rw [Real.sq_sqrt hk1.le, Real.sq_sqrt hk]; push_cast; ring
      linarith
    have hstep : 1 / Real.sqrt ((k + 1 : ℕ) : ℝ) ≤
        2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) := by
      rw [div_le_iff₀ hsq]
      nlinarith
    linarith

lemma part4_card_le (m : ℕ) : (Part4 m).card ≤ 2 ^ (70 * (Nat.sqrt m + 1)) := by
  let B : ℕ := Nat.sqrt m + 1
  have hBpos : (0 : ℝ) < (B : ℝ) := by positivity
  have hmle : (m : ℝ) ≤ (B : ℝ) * (B : ℝ) := by
    have h : m < B * B := Nat.lt_succ_sqrt m
    exact_mod_cast h.le
  let x : ℝ := Real.exp (-1 / (B : ℝ))
  have hxpos : 0 < x := Real.exp_pos _
  have hxlt1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by norm_num) hBpos
  have hsum_eq : ((Part4 m).card : ℝ) * x ^ m ≤
      ∏ p : Fin 4 × Fin m, ∑ r : Fin (m + 1), (x ^ (p.2.val + 1)) ^ r.val := by
    rw [Fintype.prod_sum]
    have hterm : ∀ c ∈ Part4 m, x ^ m = ∏ p : Fin 4 × Fin m, (x ^ (p.2.val + 1)) ^ (c p).val := by
      intro c hc
      have hsum : ∑ p : Fin 4 × Fin m, (p.2.val + 1) * (c p).val = m := (Finset.mem_filter.mp hc).2
      simp_rw [← pow_mul]
      rw [Finset.prod_pow_eq_pow_sum, hsum]
    calc ((Part4 m).card : ℝ) * x ^ m
        = ∑ c ∈ Part4 m, x ^ m := by simp
      _ = ∑ c ∈ Part4 m, ∏ p : Fin 4 × Fin m, (x ^ (p.2.val + 1)) ^ (c p).val :=
          Finset.sum_congr rfl hterm
      _ ≤ ∑ c ∈ (Finset.univ : Finset (Fin 4 × Fin m → Fin (m + 1))),
            ∏ p : Fin 4 × Fin m, (x ^ (p.2.val + 1)) ^ (c p).val :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Finset.prod_nonneg (fun _ _ => pow_nonneg (pow_nonneg hxpos.le _) _))
  have hgeom : ∀ (y : ℝ), 0 ≤ y → y < 1 →
      (∑ r : Fin (m + 1), y ^ r.val) ≤ (1 - y)⁻¹ := by
    intro y hy0 hy1
    rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hy1.ne]
    have h1my : 0 < 1 - y := sub_pos.mpr hy1
    rw [← neg_sub 1 (y ^ (m + 1)), ← neg_sub 1 y, neg_div_neg_eq, div_le_iff₀ h1my,
        inv_mul_cancel₀ h1my.ne']
    have : 0 ≤ y ^ (m + 1) := pow_nonneg hy0 _
    linarith
  have hprod_le : (∏ p : Fin 4 × Fin m, ∑ r : Fin (m + 1), (x ^ (p.2.val + 1)) ^ r.val) ≤
      (∏ l ∈ Finset.range m, (1 - x ^ (l + 1))⁻¹) ^ 4 := by
    calc (∏ p : Fin 4 × Fin m, ∑ r : Fin (m + 1), (x ^ (p.2.val + 1)) ^ r.val)
        ≤ ∏ p : Fin 4 × Fin m, (1 - x ^ (p.2.val + 1))⁻¹ := by
          gcongr with p _
          exact hgeom (x ^ (p.2.val + 1)) (pow_nonneg hxpos.le _)
            (pow_lt_one₀ hxpos.le hxlt1 (Nat.succ_ne_zero _))
      _ = ∏ _ : Fin 4, ∏ l : Fin m, (1 - x ^ (l.val + 1))⁻¹ := by
          rw [Fintype.prod_prod_type]
      _ = (∏ l ∈ Finset.range m, (1 - x ^ (l + 1))⁻¹) ^ 4 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              Fin.prod_univ_eq_prod_range (fun l => (1 - x ^ (l + 1))⁻¹)]
  have h1mx : ∀ l : ℕ, 0 < 1 - x ^ (l + 1) := fun l =>
    sub_pos.mpr (pow_lt_one₀ hxpos.le hxlt1 (Nat.succ_ne_zero _))
  have hx_pow : ∀ l : ℕ, x ^ l = Real.exp (-((l : ℝ) / (B : ℝ))) := by
    intro l
    dsimp [x]
    rw [← Real.exp_nat_mul]
    congr 1; ring
  have hsmall : ∀ l : ℕ, l < B →
      (1 - x ^ (l + 1))⁻¹ ≤ Real.exp (2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)) := by
    intro l hl
    let t : ℝ := ((l + 1 : ℕ) : ℝ) / (B : ℝ)
    have htpos : 0 < t := by positivity
    have htle : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one hBpos]
      exact_mod_cast hl
    have hexp_t : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have h1mt : t / 2 ≤ 1 - x ^ (l + 1) := by
      rw [hx_pow]
      have hneg : Real.exp (-t) ≤ (1 + t)⁻¹ := by
        rw [Real.exp_neg]
        exact inv_anti₀ (by linarith) hexp_t
      have h1 : t / (1 + t) ≤ 1 - Real.exp (-t) := by
        have : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp [show 1 + t ≠ 0 by linarith]; ring
        linarith
      have h2 : t / 2 ≤ t / (1 + t) := by
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]
        nlinarith
      linarith
    have hinv : (1 - x ^ (l + 1))⁻¹ ≤ 2 / t := by
      have : (1 - x ^ (l + 1))⁻¹ ≤ (t / 2)⁻¹ := inv_anti₀ (by linarith) h1mt
      simpa [inv_div] using this
    let u : ℝ := Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)
    have hupos : 0 ≤ u := by positivity
    have hu2 : u ^ 2 = 1 / t := by
      dsimp [u, t]
      rw [div_pow, Real.sq_sqrt hBpos.le, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((l + 1 : ℕ) : ℝ))]
      field_simp
    have h2u : 2 / t ≤ Real.exp (2 * u) := by
      have hq := exp_quad_le (2 * u) (by linarith)
      have : 2 / t = (2 * u) ^ 2 / 2 := by rw [mul_pow, hu2]; ring
      linarith
    exact hinv.trans (by simpa [u, mul_div_assoc] using h2u)
  have hlarge : ∀ l : ℕ, B ≤ l →
      (1 - x ^ (l + 1))⁻¹ ≤ Real.exp (2 * x ^ (l + 1)) := by
    intro l hl
    have hle1 : 1 ≤ ((l + 1 : ℕ) : ℝ) / (B : ℝ) := by
      rw [le_div_iff₀ hBpos, one_mul]
      exact_mod_cast (show B ≤ l + 1 by omega)
    have hylt : x ^ (l + 1) ≤ 1 / 2 := by
      rw [hx_pow]
      have h1 : Real.exp (-(((l + 1 : ℕ) : ℝ) / (B : ℝ))) ≤ Real.exp (-1) :=
        Real.exp_le_exp.mpr (by linarith)
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h3 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ (by norm_num) h2
      linarith
    have hinv : (1 - x ^ (l + 1))⁻¹ ≤ 1 + 2 * x ^ (l + 1) := by
      have hpos : 0 < 1 - x ^ (l + 1) := by linarith
      have hy0 : 0 ≤ x ^ (l + 1) := pow_nonneg hxpos.le _
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith
    exact hinv.trans (by linarith [Real.add_one_le_exp (2 * x ^ (l + 1))])
  have hprod_exp : (∏ l ∈ Finset.range m, (1 - x ^ (l + 1))⁻¹) ≤ Real.exp (8 * (B : ℝ)) := by
    let f_bound (l : ℕ) : ℝ :=
      if l < B then 2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ) else 2 * x ^ (l + 1)
    have hstep : (∏ l ∈ Finset.range m, (1 - x ^ (l + 1))⁻¹) ≤
        ∏ l ∈ Finset.range m, Real.exp (f_bound l) := by
      gcongr with l _
      · exact fun l _ => (inv_pos.mpr (h1mx l)).le
      · show (1 - x ^ (l + 1))⁻¹ ≤ Real.exp (if l < B then 2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ) else 2 * x ^ (l + 1))
        split_ifs with h
        · exact hsmall l h
        · exact hlarge l (by omega)
    rw [← Real.exp_sum] at hstep
    apply hstep.trans
    apply Real.exp_le_exp.mpr
    have hsplit : (∑ l ∈ Finset.range m, f_bound l) ≤
        (∑ l ∈ Finset.range B, 2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)) +
        (∑ l ∈ Finset.range m, 2 * x ^ (l + 1)) := by
      have h1 : (∑ l ∈ Finset.range m, f_bound l) =
          (∑ l ∈ (Finset.range m).filter (· < B), 2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)) +
          (∑ l ∈ (Finset.range m).filter (fun l => ¬ l < B), 2 * x ^ (l + 1)) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range m) (· < B) f_bound]
        congr 1
        · apply Finset.sum_congr rfl; intro l hl; simp [f_bound, (Finset.mem_filter.mp hl).2]
        · apply Finset.sum_congr rfl; intro l hl; simp [f_bound, (Finset.mem_filter.mp hl).2]
      rw [h1]
      apply add_le_add
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro l hl; exact Finset.mem_range.mpr (Finset.mem_filter.mp hl).2
        · intro l _ _; positivity
      · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        · intro l _ _; positivity
    have hsum1 : (∑ l ∈ Finset.range B, 2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)) ≤ 4 * (B : ℝ) := by
      have : (∑ l ∈ Finset.range B, 2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)) =
          2 * Real.sqrt (B : ℝ) * ∑ l ∈ Finset.range B, 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
      rw [this]
      have hsq := sum_inv_sqrt_le B
      have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (B : ℝ))
      have hsqB : Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) = (B : ℝ) := Real.mul_self_sqrt hBpos.le
      nlinarith
    have hsum2 : (∑ l ∈ Finset.range m, 2 * x ^ (l + 1)) ≤ 4 * (B : ℝ) := by
      have : (∑ l ∈ Finset.range m, 2 * x ^ (l + 1)) = 2 * x * ∑ l ∈ Finset.range m, x ^ l := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
      rw [this, geom_sum_eq hxlt1.ne]
      have h1mx_pos : 0 < 1 - x := sub_pos.mpr hxlt1
      have h1mx_ge : 1 / (2 * (B : ℝ)) ≤ 1 - x := by
        have ht : 1 / (B : ℝ) ≤ 1 := by rw [div_le_one hBpos]; exact_mod_cast (show 1 ≤ B by omega)
        have h1 : 1 + 1 / (B : ℝ) ≤ Real.exp (1 / (B : ℝ)) := by linarith [Real.add_one_le_exp (1 / (B : ℝ))]
        have h2 : x ≤ (1 + 1 / (B : ℝ))⁻¹ := by
          dsimp [x]; rw [show -1 / (B : ℝ) = -(1 / (B : ℝ)) by ring, Real.exp_neg]
          exact inv_anti₀ (by positivity) h1
        have h3 : 1 - (1 + 1 / (B : ℝ))⁻¹ = (1 / (B : ℝ)) / (1 + 1 / (B : ℝ)) := by
          field_simp [hBpos.ne', show (B : ℝ) + 1 ≠ 0 by positivity]; ring
        have h4 : 1 / (2 * (B : ℝ)) ≤ (1 / (B : ℝ)) / (1 + 1 / (B : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h2B : 1 / (B : ℝ) * (2 * (B : ℝ)) = 2 := by field_simp [hBpos.ne']
          linarith
        linarith
      have hfrac : (x ^ m - 1) / (x - 1) ≤ (1 - x)⁻¹ := by
        rw [← neg_sub 1 (x ^ m), ← neg_sub 1 x, neg_div_neg_eq, div_le_iff₀ h1mx_pos,
            inv_mul_cancel₀ h1mx_pos.ne']
        have : 0 ≤ x ^ m := pow_nonneg hxpos.le m
        linarith
      have hinv : (1 - x)⁻¹ ≤ 2 * (B : ℝ) := by
        have := inv_anti₀ (by positivity) h1mx_ge
        simpa using this
      nlinarith
    linarith
  have hcard_real : ((Part4 m).card : ℝ) ≤ Real.exp (33 * (B : ℝ)) := by
    have hxm_pos : 0 < x ^ m := pow_pos hxpos m
    have h1 := hsum_eq.trans (hprod_le.trans (pow_le_pow_left₀
      (Finset.prod_nonneg (fun l _ => (inv_pos.mpr (h1mx l)).le)) hprod_exp 4))
    have h2 : ((Part4 m).card : ℝ) ≤ Real.exp (8 * (B : ℝ)) ^ 4 * (x ^ m)⁻¹ := by
      exact (le_mul_inv_iff₀ hxm_pos).mpr h1
    have h3 : Real.exp (8 * (B : ℝ)) ^ 4 = Real.exp (32 * (B : ℝ)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h4 : (x ^ m)⁻¹ ≤ Real.exp (B : ℝ) := by
      rw [hx_pow, ← Real.exp_neg, neg_neg]
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ hBpos]
      exact hmle
    calc ((Part4 m).card : ℝ)
        ≤ Real.exp (32 * (B : ℝ)) * Real.exp (B : ℝ) := by
          rw [← h3]
          exact h2.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
      _ = Real.exp (33 * (B : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  have h2pow : Real.exp (33 * (B : ℝ)) ≤ ((2 ^ (70 * B) : ℕ) : ℝ) := by
    have he4 : Real.exp 1 ≤ (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h1 : Real.exp (33 * (B : ℝ)) = Real.exp 1 ^ (33 * B) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h1]
    calc Real.exp 1 ^ (33 * B)
        ≤ (4 : ℝ) ^ (33 * B) := pow_le_pow_left₀ (Real.exp_pos 1).le he4 _
      _ = (2 : ℝ) ^ (66 * B) := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (70 * B) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = ((2 ^ (70 * B) : ℕ) : ℝ) := by norm_cast
  exact_mod_cast hcard_real.trans h2pow

def pathVert (m : ℕ) (c0 c1 : Bool) (y : Fin (m - 1) → Bool) (j : ℕ) : Bool :=
  if h0 : j = 0 then c0 else if h : j < m then y ⟨j - 1, by omega⟩ else c1

def pathEdge (m : ℕ) (c0 c1 : Bool) (y : Fin (m - 1) → Bool) (j : Fin m) : Bool :=
  decide (pathVert m c0 c1 y j.val ≠ pathVert m c0 c1 y (j.val + 1))

lemma xor_bool_eq_decide_ne (a b : Bool) : xor a b = decide (a ≠ b) := by
  cases a <;> cases b <;> decide

lemma pathVert_prefix_parity (m : ℕ) (hm : 1 ≤ m) (c0 c1 : Bool) (y : Fin (m - 1) → Bool) :
    ∀ k ≤ m, xor c0 (pathVert m c0 c1 y k) =
      decide ((Finset.univ.filter (fun j : Fin m => j.val < k ∧ pathEdge m c0 c1 y j = true)).card % 2 = 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [pathVert]
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    have hsplit : (Finset.univ.filter (fun j : Fin m => j.val < k + 1 ∧ pathEdge m c0 c1 y j = true)) =
        (if pathEdge m c0 c1 y ⟨k, by omega⟩ = true then
          insert ⟨k, by omega⟩ (Finset.univ.filter (fun j : Fin m => j.val < k ∧ pathEdge m c0 c1 y j = true))
        else Finset.univ.filter (fun j : Fin m => j.val < k ∧ pathEdge m c0 c1 y j = true)) := by
      ext j
      split_ifs with he
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        constructor
        · intro ⟨hjk, hje⟩
          by_cases h : j.val = k
          · exact Or.inl h
          · exact Or.inr ⟨by omega, hje⟩
        · rintro (h | ⟨hjk, hje⟩)
          · refine ⟨by omega, ?_⟩
            have hj : j = ⟨k, by omega⟩ := Fin.ext h
            rw [hj]; exact he
          · exact ⟨by omega, hje⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ⟨hjk, hje⟩
          by_cases h : j.val = k
          · exfalso; apply he; have hj : j = ⟨k, by omega⟩ := Fin.ext h; rwa [← hj]
          · exact ⟨by omega, hje⟩
        · intro ⟨hjk, hje⟩; exact ⟨by omega, hje⟩
    have hnotmem : (⟨k, by omega⟩ : Fin m) ∉
        Finset.univ.filter (fun j : Fin m => j.val < k ∧ pathEdge m c0 c1 y j = true) := by
      simp
    rw [hsplit]
    have hstep : xor c0 (pathVert m c0 c1 y (k + 1)) =
        xor (xor c0 (pathVert m c0 c1 y k)) (pathEdge m c0 c1 y ⟨k, by omega⟩) := by
      unfold pathEdge
      rw [← xor_bool_eq_decide_ne]
      generalize pathVert m c0 c1 y k = v1
      generalize pathVert m c0 c1 y (k + 1) = v2
      cases c0 <;> cases v1 <;> cases v2 <;> decide
    rw [hstep, ihk]
    split_ifs with he
    · rw [he, Finset.card_insert_of_notMem hnotmem]
      generalize (Finset.univ.filter (fun j : Fin m => j.val < k ∧ pathEdge m c0 c1 y j = true)).card = c
      rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
      · simp [Nat.add_mod, h0]
      · simp [Nat.add_mod, h1]
    · have hfalse : pathEdge m c0 c1 y ⟨k, by omega⟩ = false := Bool.eq_false_iff.mpr he
      rw [hfalse]
      simp

lemma path_count (m : ℕ) (hm : 1 ≤ m) (cs : Fin m → Bool) (c0 c1 : Bool) (d1 d2 : ℕ) :
    ((Finset.univ : Finset (Fin (m - 1) → Bool)).filter (fun y =>
      (Finset.univ.filter (fun j : Fin m => cs j = false ∧ pathEdge m c0 c1 y j = true)).card = d1 ∧
      (Finset.univ.filter (fun j : Fin m => cs j = true ∧ pathEdge m c0 c1 y j = true)).card = d2)).card =
    segHist (Finset.univ.filter (fun j : Fin m => cs j = false)).card
            (Finset.univ.filter (fun j : Fin m => cs j = true)).card
            (xor c0 c1) (d1, d2) := by
  let R : Finset (Fin m) := Finset.univ.filter (fun j => cs j = false)
  let B : Finset (Fin m) := Finset.univ.filter (fun j => cs j = true)
  let E_set : Finset (Fin m → Bool) := Finset.univ.filter (fun e =>
    (Finset.univ.filter (fun j : Fin m => cs j = false ∧ e j = true)).card = d1 ∧
    (Finset.univ.filter (fun j : Fin m => cs j = true ∧ e j = true)).card = d2 ∧
    (Finset.univ.filter (fun j : Fin m => e j = true)).card % 2 = if xor c0 c1 then 1 else 0)
  have hbij1 : ((Finset.univ : Finset (Fin (m - 1) → Bool)).filter (fun y =>
      (Finset.univ.filter (fun j : Fin m => cs j = false ∧ pathEdge m c0 c1 y j = true)).card = d1 ∧
      (Finset.univ.filter (fun j : Fin m => cs j = true ∧ pathEdge m c0 c1 y j = true)).card = d2)).card =
      E_set.card := by
    apply Finset.card_nbij (fun y => pathEdge m c0 c1 y)
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [E_set, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hy.1, hy.2, ?_⟩
      have hp := pathVert_prefix_parity m hm c0 c1 y m le_rfl
      have hvm : pathVert m c0 c1 y m = c1 := by
        unfold pathVert; simp [show m ≠ 0 by omega]
      rw [hvm] at hp
      have hfilt : (Finset.univ.filter (fun j : Fin m => j.val < m ∧ pathEdge m c0 c1 y j = true)) =
          Finset.univ.filter (fun j : Fin m => pathEdge m c0 c1 y j = true) := by
        ext j; simp [j.isLt]
      rw [hfilt] at hp
      cases hx : xor c0 c1
      · rw [hx] at hp; simp at hp ⊢; omega
      · rw [hx] at hp; simpa using hp.symm
    · intro y1 _ y2 _ heq
      dsimp at heq
      funext t
      have h1 := pathVert_prefix_parity m hm c0 c1 y1 (t.val + 1) (by omega)
      have h2 := pathVert_prefix_parity m hm c0 c1 y2 (t.val + 1) (by omega)
      have hv1 : pathVert m c0 c1 y1 (t.val + 1) = y1 t := by
        unfold pathVert; simp [show t.val + 1 < m by omega]
      have hv2 : pathVert m c0 c1 y2 (t.val + 1) = y2 t := by
        unfold pathVert; simp [show t.val + 1 < m by omega]
      rw [hv1] at h1; rw [hv2, ← heq] at h2
      have hxor : xor c0 (y1 t) = xor c0 (y2 t) := h1.trans h2.symm
      cases c0 <;> cases hy1 : y1 t <;> cases hy2 : y2 t <;> simp_all
    · intro e he
      simp only [E_set, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at he
      let y : Fin (m - 1) → Bool := fun t =>
        xor c0 (decide ((Finset.univ.filter (fun j : Fin m => j.val < t.val + 1 ∧ e j = true)).card % 2 = 1))
      have he_eq : pathEdge m c0 c1 y = e := by
        have hvert : ∀ k ≤ m, pathVert m c0 c1 y k =
            xor c0 (decide ((Finset.univ.filter (fun j : Fin m => j.val < k ∧ e j = true)).card % 2 = 1)) := by
          intro k hk
          by_cases hk0 : k = 0
          · subst hk0; simp [pathVert]
          · by_cases hkm : k < m
            · unfold pathVert
              simp only [hk0, ↓reduceDIte, hkm, y]
              have hsub : Finset.univ.filter (fun j : Fin m => j.val < k - 1 + 1 ∧ e j = true) =
                  Finset.univ.filter (fun j : Fin m => j.val < k ∧ e j = true) := by
                ext j; simp [show k - 1 + 1 = k by omega]
              rw [hsub]
            · have hkeq : k = m := by omega
              rw [hkeq]
              unfold pathVert
              have hm0 : m ≠ 0 := by omega
              simp only [hm0, ↓reduceDIte, lt_irrefl]
              have hfilt : (Finset.univ.filter (fun j : Fin m => j.val < m ∧ e j = true)) =
                  Finset.univ.filter (fun j : Fin m => e j = true) := by ext j; simp [j.isLt]
              rw [hfilt, he.2.2]
              cases c0 <;> cases c1 <;> decide
        funext j
        unfold pathEdge
        rw [hvert j.val (by omega), hvert (j.val + 1) (by omega), ← xor_bool_eq_decide_ne]
        have hsplit : (Finset.univ.filter (fun i : Fin m => i.val < j.val + 1 ∧ e i = true)) =
            (if e j = true then
              insert j (Finset.univ.filter (fun i : Fin m => i.val < j.val ∧ e i = true))
            else Finset.univ.filter (fun i : Fin m => i.val < j.val ∧ e i = true)) := by
          ext i
          split_ifs with hej
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
            constructor
            · intro ⟨hij, hie⟩
              by_cases h : i.val = j.val
              · exact Or.inl h
              · exact Or.inr ⟨by omega, hie⟩
            · rintro (h | ⟨hij, hie⟩)
              · refine ⟨by omega, ?_⟩; rw [Fin.ext h]; exact hej
              · exact ⟨by omega, hie⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro ⟨hij, hie⟩
              by_cases h : i.val = j.val
              · exfalso; apply hej; rw [← Fin.ext h]; exact hie
              · exact ⟨by omega, hie⟩
            · intro ⟨hij, hie⟩; exact ⟨by omega, hie⟩
        have hnotmem : j ∉ Finset.univ.filter (fun i : Fin m => i.val < j.val ∧ e i = true) := by simp
        rw [hsplit]
        split_ifs with hej
        · rw [hej, Finset.card_insert_of_notMem hnotmem]
          generalize (Finset.univ.filter (fun i : Fin m => i.val < j.val ∧ e i = true)).card = c
          rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
          · cases c0 <;> simp [Nat.add_mod, h0]
          · cases c0 <;> simp [Nat.add_mod, h1]
        · have hf : e j = false := Bool.eq_false_iff.mpr hej
          rw [hf]
          cases c0 <;> simp
      refine ⟨y, ?_, he_eq⟩
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, he_eq]
      exact ⟨he.1, he.2.1⟩
  rw [hbij1]
  unfold segHist
  have hpart : ∀ e : Fin m → Bool,
      (Finset.univ.filter (fun j : Fin m => e j = true)).card =
      (Finset.univ.filter (fun j : Fin m => cs j = false ∧ e j = true)).card +
      (Finset.univ.filter (fun j : Fin m => cs j = true ∧ e j = true)).card := by
    intro e
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      cases cs j <;> simp
    · rw [Finset.disjoint_left]; intro j h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rw [h1.1] at h2; exact Bool.noConfusion h2.1
  by_cases hpar : (d1 + d2) % 2 = if xor c0 c1 then 1 else 0
  · rw [if_pos hpar]
    have hbij2 : E_set.card = (R.powersetCard d1 ×ˢ B.powersetCard d2).card := by
      apply Finset.card_nbij (fun e =>
        (Finset.univ.filter (fun j : Fin m => cs j = false ∧ e j = true),
         Finset.univ.filter (fun j : Fin m => cs j = true ∧ e j = true)))
      · intro e he
        simp only [E_set, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at he
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard, R, B]
        refine ⟨⟨fun j hj => ?_, he.1⟩, ⟨fun j hj => ?_, he.2.1⟩⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; exact hj.1
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; exact hj.1
      · intro e1 _ e2 _ heq
        rcases Prod.mk.inj heq with ⟨h1, h2⟩
        funext j
        cases hc : cs j
        · have := Finset.ext_iff.mp h1 j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hc] at this
          cases he1 : e1 j <;> cases he2 : e2 j <;> simp_all
        · have := Finset.ext_iff.mp h2 j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hc] at this
          cases he1 : e1 j <;> cases he2 : e2 j <;> simp_all
      · intro ⟨Ar, Ab⟩ hAB
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard, R, B] at hAB
        let e : Fin m → Bool := fun j => decide (j ∈ Ar ∨ j ∈ Ab)
        have hAr : Finset.univ.filter (fun j : Fin m => cs j = false ∧ e j = true) = Ar := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, decide_eq_true_eq]
          constructor
          · rintro ⟨hc, h | h⟩
            · exact h
            · have := hAB.2.1 h; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
              rw [hc] at this; exact absurd this (by decide)
          · intro hj
            have := hAB.1.1 hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
            exact ⟨this, Or.inl hj⟩
        have hAb : Finset.univ.filter (fun j : Fin m => cs j = true ∧ e j = true) = Ab := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, decide_eq_true_eq]
          constructor
          · rintro ⟨hc, h | h⟩
            · have := hAB.1.1 h; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
              rw [hc] at this; exact absurd this (by decide)
            · exact h
          · intro hj
            have := hAB.2.1 hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
            exact ⟨this, Or.inr hj⟩
        refine ⟨e, ?_, by simp [hAr, hAb]⟩
        simp only [E_set, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨by rw [hAr]; exact hAB.1.2, by rw [hAb]; exact hAB.2.2, ?_⟩
        rw [hpart e, hAr, hAb, hAB.1.2, hAB.2.2]; exact hpar
    rw [hbij2, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard]
  · rw [if_neg hpar]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e _ ⟨h1, h2, h3⟩
    rw [hpart e, h1, h2] at h3
    exact hpar h3

lemma tuple_conv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → Type*) [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (w1 w2 : ∀ i, α i → ℕ) (L : List ι) (hL : L.Nodup) (hfull : ∀ i, i ∈ L) :
    ∀ d : ℕ × ℕ,
      ((Finset.univ : Finset (∀ i, α i)).filter (fun y =>
        (∑ i, w1 i (y i)) = d.1 ∧ (∑ i, w2 i (y i)) = d.2)).card =
      convList (L.map fun i => fun p : ℕ × ℕ =>
        ((Finset.univ : Finset (α i)).filter (fun a => w1 i a = p.1 ∧ w2 i a = p.2)).card) d := by
  have hgen : ∀ (S : List ι), S.Nodup → ∀ d : ℕ × ℕ,
      ((Finset.univ : Finset (∀ i : {x // x ∈ S}, α i.1)).filter (fun y =>
        (∑ i : {x // x ∈ S}, w1 i.1 (y i)) = d.1 ∧ (∑ i : {x // x ∈ S}, w2 i.1 (y i)) = d.2)).card =
      convList (S.map fun i => fun p : ℕ × ℕ =>
        ((Finset.univ : Finset (α i)).filter (fun a => w1 i a = p.1 ∧ w2 i a = p.2)).card) d := by
    intro S
    induction S with
    | nil =>
      intro _ ⟨d1, d2⟩
      simp only [List.map_nil, convList, List.foldr_nil, delta0]
      have huniq : ∀ y : (∀ i : {x // x ∈ ([] : List ι)}, α i.1),
          (∑ i : {x // x ∈ ([] : List ι)}, w1 i.1 (y i)) = 0 ∧
          (∑ i : {x // x ∈ ([] : List ι)}, w2 i.1 (y i)) = 0 := by
        intro y; simp
      by_cases h0 : (d1, d2) = (0, 0)
      · rcases Prod.mk.inj h0 with ⟨rfl, rfl⟩
        simp only [↓reduceIte]
        have : (Finset.univ.filter (fun y : ∀ i : {x // x ∈ ([] : List ι)}, α i.1 =>
            (∑ i, w1 i.1 (y i)) = 0 ∧ (∑ i, w2 i.1 (y i)) = 0)) = Finset.univ := by
          ext y; simp
        rw [this, Finset.card_univ, Fintype.card_pi]
        simp
      · rw [if_neg h0, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro y _ ⟨h1, h2⟩
        obtain ⟨z1, z2⟩ := huniq y
        exact h0 (Prod.ext (z1.symm.trans h1).symm (z2.symm.trans h2).symm)
    | cons a tl ih =>
      intro hnd ⟨d1, d2⟩
      rw [List.nodup_cons] at hnd
      rcases hnd with ⟨ha_not, htl_nd⟩
      simp only [List.map_cons, convList, List.foldr_cons]
      unfold conv
      let eSub : (∀ i : {x // x ∈ a :: tl}, α i.1) ≃ α a × (∀ i : {x // x ∈ tl}, α i.1) :=
        { toFun := fun y => (y ⟨a, List.mem_cons_self⟩, fun i => y ⟨i.1, List.mem_cons_of_mem a i.2⟩)
          invFun := fun p i =>
            if h : i.1 = a then cast (congrArg α h.symm) p.1
            else p.2 ⟨i.1, (List.mem_cons.mp i.2).resolve_left h⟩
          left_inv := fun y => by
            funext ⟨x, hx⟩
            by_cases h : x = a
            · subst h; simp
            · simp [h]
          right_inv := fun ⟨ya, ytl⟩ => by
            apply Prod.ext
            · simp
            · funext ⟨x, hx⟩
              have hne : x ≠ a := fun h => ha_not (h ▸ hx)
              simp [hne] }
      have hsum1 : ∀ y : (∀ i : {x // x ∈ a :: tl}, α i.1),
          (∑ i : {x // x ∈ a :: tl}, w1 i.1 (y i)) =
          w1 a (eSub y).1 + ∑ i : {x // x ∈ tl}, w1 i.1 ((eSub y).2 i) := by
        intro y
        let a0 : {x // x ∈ a :: tl} := ⟨a, List.mem_cons_self⟩
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0)]
        congr 1
        symm
        apply Finset.sum_nbij (fun j : {x // x ∈ tl} => (⟨j.1, List.mem_cons_of_mem a j.2⟩ : {x // x ∈ a :: tl}))
        · intro j _
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Subtype.ext_iff, a0]
          exact fun h => ha_not (h ▸ j.2)
        · intro j1 _ j2 _ heq; dsimp at heq; exact Subtype.ext (Subtype.mk.inj heq)
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Subtype.ext_iff, a0] at hi
          exact ⟨⟨i.1, (List.mem_cons.mp i.2).resolve_left hi⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
        · intro _ _; rfl
      have hsum2 : ∀ y : (∀ i : {x // x ∈ a :: tl}, α i.1),
          (∑ i : {x // x ∈ a :: tl}, w2 i.1 (y i)) =
          w2 a (eSub y).1 + ∑ i : {x // x ∈ tl}, w2 i.1 ((eSub y).2 i) := by
        intro y
        let a0 : {x // x ∈ a :: tl} := ⟨a, List.mem_cons_self⟩
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0)]
        congr 1
        symm
        apply Finset.sum_nbij (fun j : {x // x ∈ tl} => (⟨j.1, List.mem_cons_of_mem a j.2⟩ : {x // x ∈ a :: tl}))
        · intro j _
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Subtype.ext_iff, a0]
          exact fun h => ha_not (h ▸ j.2)
        · intro j1 _ j2 _ heq; dsimp at heq; exact Subtype.ext (Subtype.mk.inj heq)
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Subtype.ext_iff, a0] at hi
          exact ⟨⟨i.1, (List.mem_cons.mp i.2).resolve_left hi⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
        · intro _ _; rfl
      have hrew : ((Finset.univ : Finset (∀ i : {x // x ∈ a :: tl}, α i.1)).filter (fun y =>
          (∑ i : {x // x ∈ a :: tl}, w1 i.1 (y i)) = d1 ∧
          (∑ i : {x // x ∈ a :: tl}, w2 i.1 (y i)) = d2)).card =
          ((Finset.univ : Finset (α a × (∀ i : {x // x ∈ tl}, α i.1))).filter (fun p =>
            w1 a p.1 + (∑ i : {x // x ∈ tl}, w1 i.1 (p.2 i)) = d1 ∧
            w2 a p.1 + (∑ i : {x // x ∈ tl}, w2 i.1 (p.2 i)) = d2)).card := by
        apply Finset.card_nbij (fun y => eSub y)
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
          rw [← hsum1 y, ← hsum2 y]; exact hy
        · intro y1 _ y2 _ heq; exact eSub.injective heq
        · intro p hp
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          refine ⟨eSub.symm p, ?_, eSub.apply_symm_apply p⟩
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hsum1, hsum2, eSub.apply_symm_apply]; exact hp
      rw [hrew]
      have hfib : ((Finset.univ : Finset (α a × (∀ i : {x // x ∈ tl}, α i.1))).filter (fun p =>
            w1 a p.1 + (∑ i : {x // x ∈ tl}, w1 i.1 (p.2 i)) = d1 ∧
            w2 a p.1 + (∑ i : {x // x ∈ tl}, w2 i.1 (p.2 i)) = d2)).card =
          ∑ x ∈ Finset.range (d1 + 1), ∑ y ∈ Finset.range (d2 + 1),
            ((Finset.univ : Finset (α a)).filter (fun z => w1 a z = x ∧ w2 a z = y)).card *
            ((Finset.univ : Finset (∀ i : {x // x ∈ tl}, α i.1)).filter (fun z =>
              (∑ i, w1 i.1 (z i)) = d1 - x ∧ (∑ i, w2 i.1 (z i)) = d2 - y)).card := by
        have hmap : ∀ p ∈ (Finset.univ : Finset (α a × (∀ i : {x // x ∈ tl}, α i.1))).filter (fun p =>
            w1 a p.1 + (∑ i : {x // x ∈ tl}, w1 i.1 (p.2 i)) = d1 ∧
            w2 a p.1 + (∑ i : {x // x ∈ tl}, w2 i.1 (p.2 i)) = d2),
            (w1 a p.1, w2 a p.1) ∈ Finset.range (d1 + 1) ×ˢ Finset.range (d2 + 1) := by
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          simp only [Finset.mem_product, Finset.mem_range]; omega
        rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to hmap, Finset.sum_product]
        apply Finset.sum_congr rfl; intro x hx
        apply Finset.sum_congr rfl; intro y hy
        simp only [Finset.mem_range] at hx hy
        rw [← Finset.card_eq_sum_ones, ← Finset.card_product]
        congr 1; ext ⟨p1, p2⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Prod.mk.injEq]
        omega
      rw [hfib]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      rw [ih htl_nd (d1 - x, d2 - y)]
      rfl
  intro d
  rw [← hgen L hL d]
  let eFull : (∀ i : ι, α i) ≃ (∀ i : {x // x ∈ L}, α i.1) :=
    { toFun := fun y i => y i.1
      invFun := fun y i => y ⟨i, hfull i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply Finset.card_nbij (fun y => eFull y)
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    constructor
    · rw [← hy.1]; symm
      exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv hfull).symm _ _ (fun _ => rfl)
    · rw [← hy.2]; symm
      exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv hfull).symm _ _ (fun _ => rfl)
  · intro y1 _ y2 _ heq; exact eFull.injective heq
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨eFull.symm y, ?_, eFull.apply_symm_apply y⟩
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rw [← hy.1]
      exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv hfull).symm _ _ (fun _ => rfl)
    · rw [← hy.2]
      exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv hfull).symm _ _ (fun _ => rfl)

lemma hist_eq_convList {n : ℕ} (M : Bool → Fin n → Fin n) (pin : Bool × Fin n → Option Bool)
    (K : ℕ) (m : Fin K → ℕ) (hm : ∀ idx, 1 ≤ m idx)
    (verts : ∀ idx, Fin (m idx + 1) → Bool × Fin n)
    (ecols : ∀ idx, Fin (m idx) → Bool)
    (eidx : ∀ idx, Fin (m idx) → Fin n)
    (c0 c1 : Fin K → Bool)
    (hpin0 : ∀ idx, pin (verts idx 0) = some (c0 idx))
    (hpin1 : ∀ idx, pin (verts idx (Fin.last (m idx))) = some (c1 idx))
    (hedge : ∀ idx (j : Fin (m idx)),
      (verts idx j.castSucc = (false, eidx idx j) ∧ verts idx j.succ = (true, M (ecols idx j) (eidx idx j))) ∨
      (verts idx j.castSucc = (true, M (ecols idx j) (eidx idx j)) ∧ verts idx j.succ = (false, eidx idx j)))
    (eVert : (Σ idx : Fin K, Fin (m idx - 1)) ≃ {u : Bool × Fin n // pin u = none})
    (heVert : ∀ p, (eVert p).1 = verts p.1 ⟨p.2.val + 1, by have := hm p.1; omega⟩)
    (eEdge : (Σ idx : Fin K, Fin (m idx)) ≃ Bool × Fin n)
    (heEdge : ∀ p, eEdge p = (ecols p.1 p.2, eidx p.1 p.2)) :
    ∀ d : Fin (n + 1) × Fin (n + 1),
      histDef M pin d = convList ((List.finRange K).map fun idx =>
        segHist (Finset.univ.filter (fun j : Fin (m idx) => ecols idx j = false)).card
                (Finset.univ.filter (fun j : Fin (m idx) => ecols idx j = true)).card
                (xor (c0 idx) (c1 idx))) (d.1.val, d.2.val) := by
  intro d
  let assign (y : ∀ idx : Fin K, Fin (m idx - 1) → Bool) (u : Bool × Fin n) : Bool :=
    if h : pin u = none then let p := eVert.symm ⟨u, h⟩; y p.1 p.2 else (pin u).getD false
  have hcons : ∀ y u, pin u = none ∨ pin u = some (assign y u) := by
    intro y u
    cases h : pin u with
    | none => exact Or.inl rfl
    | some b => exact Or.inr (by unfold assign; simp [h])
  have hverts : ∀ y idx (j : ℕ) (hj : j ≤ m idx),
      assign y (verts idx ⟨j, by omega⟩) = pathVert (m idx) (c0 idx) (c1 idx) (y idx) j := by
    intro y idx j hj
    by_cases hj0 : j = 0
    · subst hj0
      have hp := hpin0 idx
      unfold assign pathVert
      simp [hp]
    · by_cases hjm : j < m idx
      · let t : Fin (m idx - 1) := ⟨j - 1, by omega⟩
        have hv : verts idx ⟨j, by omega⟩ = (eVert ⟨idx, t⟩).1 := by
          rw [heVert]; congr 1; ext; dsimp [t]; omega
        have hp : pin (verts idx ⟨j, by omega⟩) = none := by
          rw [hv]; exact (eVert ⟨idx, t⟩).2
        unfold assign pathVert
        simp only [hp, ↓reduceDIte, hj0, hjm]
        have hsub : (⟨verts idx ⟨j, by omega⟩, hp⟩ : {u // pin u = none}) = eVert ⟨idx, t⟩ :=
          Subtype.ext hv
        rw [hsub, Equiv.symm_apply_apply]
      · have hjeq : j = m idx := by omega
        subst hjeq
        have hp := hpin1 idx
        have hlast : (⟨m idx, by omega⟩ : Fin (m idx + 1)) = Fin.last (m idx) := rfl
        rw [hlast]
        unfold assign pathVert
        simp [hp, hj0]
  have hcount : ∀ y (h : Bool),
      (Finset.univ.filter (fun i : Fin n => assign y (false, i) ≠ assign y (true, M h i))).card =
      ∑ idx : Fin K, (Finset.univ.filter (fun j : Fin (m idx) =>
        ecols idx j = h ∧ pathEdge (m idx) (c0 idx) (c1 idx) (y idx) j = true)).card := by
    intro y h
    rw [← Finset.card_sigma]
    apply Finset.card_nbij (fun i => eEdge.symm (h, i))
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
      set p := eEdge.symm (h, i)
      have hp : (ecols p.1 p.2, eidx p.1 p.2) = (h, i) := by
        rw [← heEdge p, Equiv.apply_symm_apply]
      rcases Prod.mk.inj hp with ⟨hcol, hidx⟩
      refine ⟨hcol, ?_⟩
      unfold pathEdge
      rw [← hverts y p.1 p.2.val (by omega), ← hverts y p.1 (p.2.val + 1) (by omega), decide_eq_true_eq]
      have hcs : (⟨p.2.val, by omega⟩ : Fin (m p.1 + 1)) = p.2.castSucc := rfl
      have hsc : (⟨p.2.val + 1, by omega⟩ : Fin (m p.1 + 1)) = p.2.succ := rfl
      rw [hcs, hsc]
      rcases hedge p.1 p.2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb, hcol, hidx]; exact hi
      · rw [ha, hb, hcol, hidx]; exact Ne.symm hi
    · intro i1 _ i2 _ heq
      have := congrArg eEdge heq
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact (Prod.mk.inj this).2
    · intro ⟨idx, j⟩ hp
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp
      refine ⟨eidx idx j, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        have hpe := hp.2
        unfold pathEdge at hpe
        rw [← hverts y idx j.val (by omega), ← hverts y idx (j.val + 1) (by omega), decide_eq_true_eq] at hpe
        have hcs : (⟨j.val, by omega⟩ : Fin (m idx + 1)) = j.castSucc := rfl
        have hsc : (⟨j.val + 1, by omega⟩ : Fin (m idx + 1)) = j.succ := rfl
        rw [hcs, hsc] at hpe
        rcases hedge idx j with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [ha, hb, hp.1] at hpe; exact hpe
        · rw [ha, hb, hp.1] at hpe; exact Ne.symm hpe
      · apply eEdge.injective
        rw [Equiv.apply_symm_apply, heEdge, hp.1]
  have hbij : histDef M pin d =
      ((Finset.univ : Finset (∀ idx : Fin K, Fin (m idx - 1) → Bool)).filter (fun y =>
        (∑ idx : Fin K, (Finset.univ.filter (fun j : Fin (m idx) =>
          ecols idx j = false ∧ pathEdge (m idx) (c0 idx) (c1 idx) (y idx) j = true)).card) = d.1.val ∧
        (∑ idx : Fin K, (Finset.univ.filter (fun j : Fin (m idx) =>
          ecols idx j = true ∧ pathEdge (m idx) (c0 idx) (c1 idx) (y idx) j = true)).card) = d.2.val)).card := by
    symm
    apply Finset.card_nbij assign
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      refine ⟨hcons y, ?_⟩
      intro h; cases h
      · simpa [hcount y false] using hy.1
      · simpa [hcount y true] using hy.2
    · intro y1 _ y2 _ heq
      funext idx t
      have h1 := hverts y1 idx (t.val + 1) (by have := hm idx; omega)
      have h2 := hverts y2 idx (t.val + 1) (by have := hm idx; omega)
      have hv1 : pathVert (m idx) (c0 idx) (c1 idx) (y1 idx) (t.val + 1) = y1 idx t := by
        unfold pathVert; simp [show t.val + 1 < m idx by omega]
      have hv2 : pathVert (m idx) (c0 idx) (c1 idx) (y2 idx) (t.val + 1) = y2 idx t := by
        unfold pathVert; simp [show t.val + 1 < m idx by omega]
      rw [hv1] at h1; rw [hv2] at h2
      have hxy := congrFun heq (verts idx ⟨t.val + 1, by have := hm idx; omega⟩)
      exact h1.symm.trans (hxy.trans h2)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      let y : ∀ idx : Fin K, Fin (m idx - 1) → Bool :=
        fun idx t => x (verts idx ⟨t.val + 1, by have := hm idx; omega⟩)
      have hax : assign y = x := by
        funext u
        unfold assign
        by_cases h : pin u = none
        · simp only [h, ↓reduceDIte, y]
          have hsub := heVert (eVert.symm ⟨u, h⟩)
          rw [Equiv.apply_symm_apply] at hsub
          rw [← hsub]
        · simp only [h, ↓reduceDIte]
          rcases hx.1 u with hnone | hsome
          · exact absurd hnone h
          · rw [hsome]; rfl
      refine ⟨y, ?_, hax⟩
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      have hf := hx.2 false; have ht := hx.2 true
      rw [← hax] at hf ht
      rw [← hcount y false, ← hcount y true]
      exact ⟨by simpa using hf, by simpa using ht⟩
  rw [hbij]
  have htc := tuple_conv (fun idx : Fin K => Fin (m idx - 1) → Bool)
    (fun idx y => (Finset.univ.filter (fun j : Fin (m idx) =>
      ecols idx j = false ∧ pathEdge (m idx) (c0 idx) (c1 idx) y j = true)).card)
    (fun idx y => (Finset.univ.filter (fun j : Fin (m idx) =>
      ecols idx j = true ∧ pathEdge (m idx) (c0 idx) (c1 idx) y j = true)).card)
    (List.finRange K) (List.nodup_finRange K) (fun idx => List.mem_finRange idx) (d.1.val, d.2.val)
  rw [htc]
  congr 1
  apply List.map_congr_left
  intro idx _
  funext ⟨a, b⟩
  exact path_count (m idx) (hm idx) (ecols idx) (c0 idx) (c1 idx) a b

lemma perm_mem_periodicPts {n : ℕ} (τ : Equiv.Perm (Fin n)) (i0 : Fin n) :
    i0 ∈ Function.periodicPts τ := by
  have hlt : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by simp
  obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun t : Fin (n + 1) => (τ^[t.val]) i0) hlt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · refine ⟨b.val - a.val, by omega, ?_⟩
    apply (τ.injective.iterate a.val)
    rw [← Function.iterate_add_apply, show a.val + (b.val - a.val) = b.val by omega, heq]
  · refine ⟨a.val - b.val, by omega, ?_⟩
    apply (τ.injective.iterate b.val)
    rw [← Function.iterate_add_apply, show b.val + (a.val - b.val) = a.val by omega, heq]

lemma free_cycles_elim {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (pin : Bool × Fin n → Option Bool) :
    let τ : Equiv.Perm (Fin n) := (M true).trans (M false).symm
    ∃ (pin1 : Bool × Fin n → Option Bool) (f : ℕ), f ≤ n ∧
      (∀ d, histDef (fun h i => M h i) pin d = 2 ^ f * histDef (fun h i => M h i) pin1 d) ∧
      ∀ i : Fin n, ∃ t : ℕ, pin1 (false, (τ^[t]) i) ≠ none ∨ pin1 (true, M true ((τ^[t]) i)) ≠ none := by
  classical
  intro τ
  let freeSet (p : Bool × Fin n → Option Bool) : Finset (Fin n) :=
    Finset.univ.filter (fun i => ∀ t : ℕ, p (false, (τ^[t]) i) = none ∧ p (true, M true ((τ^[t]) i)) = none)
  have haux : ∀ k : ℕ, ∀ p : Bool × Fin n → Option Bool, (freeSet p).card ≤ k →
      ∃ (p1 : Bool × Fin n → Option Bool) (f : ℕ), f ≤ k ∧
        (∀ d, histDef (fun h i => M h i) p d = 2 ^ f * histDef (fun h i => M h i) p1 d) ∧
        (freeSet p1).card = 0 := by
    intro k
    induction k with
    | zero =>
      intro p hp
      exact ⟨p, 0, le_rfl, fun _ => by simp, Nat.eq_zero_of_le_zero hp⟩
    | succ k ih =>
      intro p hp
      by_cases hemp : freeSet p = ∅
      · exact ⟨p, 0, Nat.zero_le _, fun _ => by simp, by simp [hemp]⟩
      · obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        have hi0_free : ∀ t : ℕ, p (false, (τ^[t]) i0) = none ∧ p (true, M true ((τ^[t]) i0)) = none :=
          (Finset.mem_filter.mp hi0).2
        let pF := Function.update p (false, i0) (some false)
        let pT := Function.update p (false, i0) (some true)
        let inOrb (i : Fin n) : Prop := ∃ t : ℕ, (τ^[t]) i0 = i
        haveI : DecidablePred inOrb := Classical.decPred _
        have horb_step : ∀ i : Fin n, inOrb i ↔ inOrb (τ i) := by
          intro i
          constructor
          · rintro ⟨t, rfl⟩; exact ⟨t + 1, by rw [Function.iterate_succ_apply']⟩
          · rintro ⟨t, ht⟩
            have hfin : ∃ m : ℕ, 0 < m ∧ (τ^[m]) i0 = i0 := by
              have hper : i0 ∈ Function.periodicPts τ := perm_mem_periodicPts τ i0
              exact ⟨Function.minimalPeriod τ i0, Function.minimalPeriod_pos_of_mem_periodicPts hper,
                Function.iterate_minimalPeriod⟩
            obtain ⟨m, hmpos, hm⟩ := hfin
            cases t with
            | zero =>
              refine ⟨m - 1, ?_⟩
              apply τ.injective
              rw [← Function.iterate_succ_apply' τ, show (m - 1).succ = m by omega, hm, ← ht]
              rfl
            | succ t' =>
              exact ⟨t', τ.injective (by rw [← Function.iterate_succ_apply' τ, ht])⟩
        let flip (x : Bool × Fin n → Bool) (u : Bool × Fin n) : Bool :=
          if (u.1 = false ∧ inOrb u.2) ∨ (u.1 = true ∧ inOrb ((M true).symm u.2)) then !x u else x u
        have hflip_inv : ∀ x, flip (flip x) = x := by
          intro x; funext u; unfold flip; split_ifs <;> simp
        have hflip_edge : ∀ x (h : Bool) (i : Fin n),
            (flip x (false, i) ≠ flip x (true, M h i)) ↔ (x (false, i) ≠ x (true, M h i)) := by
          intro x h i
          have hsame : inOrb i ↔ inOrb ((M true).symm (M h i)) := by
            cases h
            · have : (M true).symm (M false i) = τ.symm i := by
                apply τ.injective; simp [τ]
              rw [this, horb_step (τ.symm i), Equiv.apply_symm_apply]
            · simp
          unfold flip
          by_cases ho : inOrb i
          · have ho' : inOrb ((M true).symm (M h i)) := hsame.mp ho
            simp [ho, ho']
          · have ho' : ¬ inOrb ((M true).symm (M h i)) := fun h' => ho (hsame.mpr h')
            simp [ho, ho']
        have hstep_eq : ∀ d, histDef (fun h i => M h i) p d = 2 * histDef (fun h i => M h i) pF d := by
          intro d
          have hpart : histDef (fun h i => M h i) p d =
              histDef (fun h i => M h i) pF d + histDef (fun h i => M h i) pT d := by
            unfold histDef
            rw [← Finset.card_union_of_disjoint]
            · congr 1; ext x
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, pF, pT]
              constructor
              · intro ⟨hc, hd⟩
                cases hx0 : x (false, i0)
                · left; refine ⟨fun u => ?_, hd⟩
                  by_cases hu : u = (false, i0)
                  · subst hu; simp [hx0]
                  · simp [Function.update_of_ne hu, hc u]
                · right; refine ⟨fun u => ?_, hd⟩
                  by_cases hu : u = (false, i0)
                  · subst hu; simp [hx0]
                  · simp [Function.update_of_ne hu, hc u]
              · rintro (⟨hc, hd⟩ | ⟨hc, hd⟩)
                · refine ⟨fun u => ?_, hd⟩
                  by_cases hu : u = (false, i0)
                  · subst hu; exact Or.inl (hi0_free 0).1
                  · simpa [Function.update_of_ne hu] using hc u
                · refine ⟨fun u => ?_, hd⟩
                  by_cases hu : u = (false, i0)
                  · subst hu; exact Or.inl (hi0_free 0).1
                  · simpa [Function.update_of_ne hu] using hc u
            · rw [Finset.disjoint_left]; intro x h1 h2
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, pF, pT] at h1 h2
              have a1 := h1.1 (false, i0); have a2 := h2.1 (false, i0)
              simp only [Function.update_self, reduceCtorEq, Option.some.injEq, false_or] at a1 a2
              rw [← a1] at a2; exact Bool.noConfusion a2
          have hFT : histDef (fun h i => M h i) pT d = histDef (fun h i => M h i) pF d := by
            unfold histDef
            apply Finset.card_nbij flip
            · intro x hx
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              refine ⟨fun u => ?_, fun h => ?_⟩
              · by_cases hu : u = (false, i0)
                · subst hu
                  have hx0 : x (false, i0) = true := by
                    have := hx.1 (false, i0)
                    simp only [pT, Function.update_self, reduceCtorEq, Option.some.injEq, false_or] at this
                    exact this.symm
                  have hin : inOrb i0 := ⟨0, rfl⟩
                  simp [pF, flip, hin, hx0]
                · dsimp only [pF]; rw [Function.update_of_ne hu]
                  have hxu := hx.1 u; dsimp only [pT] at hxu; rw [Function.update_of_ne hu] at hxu
                  rcases hxu with hnone | hsome
                  · exact Or.inl hnone
                  · right
                    have hnot : ¬ ((u.1 = false ∧ inOrb u.2) ∨ (u.1 = true ∧ inOrb ((M true).symm u.2))) := by
                      rintro (⟨h1, t, ht⟩ | ⟨h1, t, ht⟩)
                      · have : u = (false, (τ^[t]) i0) := Prod.ext h1 ht.symm
                        rw [this, (hi0_free t).1] at hsome; cases hsome
                      · have : u = (true, M true ((τ^[t]) i0)) := by
                          apply Prod.ext h1; rw [ht, Equiv.apply_symm_apply]
                        rw [this, (hi0_free t).2] at hsome; cases hsome
                    simpa [flip, hnot] using hsome
              · rw [← hx.2 h]; congr 1; ext i; simp [hflip_edge]
            · intro x1 _ x2 _ heq; rw [← hflip_inv x1, ← hflip_inv x2, heq]
            · intro x hx
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
              refine ⟨flip x, ?_, hflip_inv x⟩
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨fun u => ?_, fun h => ?_⟩
              · by_cases hu : u = (false, i0)
                · subst hu
                  have hx0 : x (false, i0) = false := by
                    have := hx.1 (false, i0)
                    simp only [pF, Function.update_self, reduceCtorEq, Option.some.injEq, false_or] at this
                    exact this.symm
                  have hin : inOrb i0 := ⟨0, rfl⟩
                  simp [pT, flip, hin, hx0]
                · dsimp only [pT]; rw [Function.update_of_ne hu]
                  have hxu := hx.1 u; dsimp only [pF] at hxu; rw [Function.update_of_ne hu] at hxu
                  rcases hxu with hnone | hsome
                  · exact Or.inl hnone
                  · right
                    have hnot : ¬ ((u.1 = false ∧ inOrb u.2) ∨ (u.1 = true ∧ inOrb ((M true).symm u.2))) := by
                      rintro (⟨h1, t, ht⟩ | ⟨h1, t, ht⟩)
                      · have : u = (false, (τ^[t]) i0) := Prod.ext h1 ht.symm
                        rw [this, (hi0_free t).1] at hsome; cases hsome
                      · have : u = (true, M true ((τ^[t]) i0)) := by
                          apply Prod.ext h1; rw [ht, Equiv.apply_symm_apply]
                        rw [this, (hi0_free t).2] at hsome; cases hsome
                    simpa [flip, hnot] using hsome
              · rw [← hx.2 h]; congr 1; ext i; simp [hflip_edge]
          rw [hpart, hFT]; ring
        have hsub : freeSet pF ⊂ freeSet p := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨fun i hi => ?_, fun heq => ?_⟩
          · simp only [freeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            intro t
            have h1 := (hi t).1; have h2 := (hi t).2
            constructor
            · by_cases hu : (false, (τ^[t]) i) = (false, i0)
              · simp [pF, hu] at h1
              · simpa [pF, Function.update_of_ne hu] using h1
            · have hu : (true, M true ((τ^[t]) i)) ≠ (false, i0) := by simp
              simpa [pF, Function.update_of_ne hu] using h2
          · have hi0' : i0 ∈ freeSet pF := heq ▸ hi0
            have h0 := ((Finset.mem_filter.mp hi0').2 0).1
            simp [pF] at h0
        have hcard_lt : (freeSet pF).card ≤ k := by
          have := Finset.card_lt_card hsub; omega
        obtain ⟨p1, f, hf, hhist, hzero⟩ := ih pF hcard_lt
        refine ⟨p1, f + 1, by omega, fun d => ?_, hzero⟩
        rw [hstep_eq d, hhist d, pow_succ]; ring
  have hle : (freeSet pin).card ≤ n := by
    calc (freeSet pin).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  obtain ⟨p1, f, hf, hhist, hzero⟩ := haux n pin hle
  refine ⟨p1, f, hf, hhist, fun i => ?_⟩
  by_contra hnot
  push_neg at hnot
  have hi : i ∈ freeSet p1 := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnot⟩
  have hpos : 0 < (freeSet p1).card := Finset.card_pos.mpr ⟨i, hi⟩
  omega

lemma alt_counts (m : ℕ) (hm : 1 ≤ m) (s0 : Bool) :
    let ecols : Fin m → Bool := fun j => if j.val % 2 = 0 then s0 else !s0
    let r := (Finset.univ.filter (fun j : Fin m => ecols j = false)).card
    let b := (Finset.univ.filter (fun j : Fin m => ecols j = true)).card
    r + b = m ∧
    (if m % 2 = 0 then r = m / 2 ∧ b = m / 2
     else if s0 = false then r = m / 2 + 1 ∧ b = m / 2
     else r = m / 2 ∧ b = m / 2 + 1) := by
  induction m with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk; cases s0 <;> decide
    · have hk1 : 1 ≤ k := by omega
      obtain ⟨hsum, hcase⟩ := ih hk1
      dsimp only at hsum hcase ⊢
      let ecols : Fin (k + 1) → Bool := fun j => if j.val % 2 = 0 then s0 else !s0
      let ecols' : Fin k → Bool := fun j => if j.val % 2 = 0 then s0 else !s0
      have hstep : ∀ c : Bool,
          (Finset.univ.filter (fun j : Fin (k + 1) => ecols j = c)).card =
          (Finset.univ.filter (fun j : Fin k => ecols' j = c)).card +
          if ecols (Fin.last k) = c then 1 else 0 := by
        intro c
        rw [Finset.card_filter, Fin.sum_univ_castSucc, Finset.card_filter]
        rfl
      have hf := hstep false
      have ht := hstep true
      have hlast : ecols (Fin.last k) = if k % 2 = 0 then s0 else !s0 := rfl
      rw [hlast] at hf ht
      have hr_def : (Finset.univ.filter (fun j : Fin (k + 1) => (if j.val % 2 = 0 then s0 else !s0) = false)).card =
          (Finset.univ.filter (fun j : Fin (k + 1) => ecols j = false)).card := rfl
      have hb_def : (Finset.univ.filter (fun j : Fin (k + 1) => (if j.val % 2 = 0 then s0 else !s0) = true)).card =
          (Finset.univ.filter (fun j : Fin (k + 1) => ecols j = true)).card := rfl
      rw [hr_def, hb_def, hf, ht]
      change (Finset.univ.filter (fun j : Fin k => ecols' j = false)).card +
        (Finset.univ.filter (fun j : Fin k => ecols' j = true)).card = k at hsum
      change (if k % 2 = 0 then
          (Finset.univ.filter (fun j : Fin k => ecols' j = false)).card = k / 2 ∧
          (Finset.univ.filter (fun j : Fin k => ecols' j = true)).card = k / 2
         else if s0 = false then
          (Finset.univ.filter (fun j : Fin k => ecols' j = false)).card = k / 2 + 1 ∧
          (Finset.univ.filter (fun j : Fin k => ecols' j = true)).card = k / 2
         else
          (Finset.univ.filter (fun j : Fin k => ecols' j = false)).card = k / 2 ∧
          (Finset.univ.filter (fun j : Fin k => ecols' j = true)).card = k / 2 + 1) at hcase
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
      · have h0' : (k + 1) % 2 = 1 := by omega
        simp only [h0, h0', ↓reduceIte, show ¬ (1 : ℕ) = 0 by decide] at hcase ⊢
        cases s0 <;> simp at hcase ⊢ <;> omega
      · have h1' : (k + 1) % 2 = 0 := by omega
        simp only [h1, h1', ↓reduceIte, show ¬ (1 : ℕ) = 0 by decide] at hcase ⊢
        cases s0 <;> simp at hcase ⊢ <;> omega

lemma cycle_decomp {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    ∃ cycs : List (List (Fin n)),
      (∀ c ∈ cycs, 0 < c.length ∧ c.Nodup ∧
        ∀ r : Fin c.length, τ (c.get r) = c.get ⟨(r.val + 1) % c.length, Nat.mod_lt _ (by have := r.isLt; omega)⟩) ∧
      cycs.flatten.Nodup ∧
      ∀ i : Fin n, i ∈ cycs.flatten := by
  classical
  have haux : ∀ k : ℕ, ∀ S : Finset (Fin n), S.card ≤ k →
      (∀ i ∈ S, τ i ∈ S) → (∀ i ∈ S, τ.symm i ∈ S) →
      ∃ cycs : List (List (Fin n)),
        (∀ c ∈ cycs, 0 < c.length ∧ c.Nodup ∧
          ∀ r : Fin c.length, τ (c.get r) = c.get ⟨(r.val + 1) % c.length, Nat.mod_lt _ (by have := r.isLt; omega)⟩) ∧
        cycs.flatten.Nodup ∧
        ∀ i : Fin n, i ∈ cycs.flatten ↔ i ∈ S := by
    intro k
    induction k with
    | zero =>
      intro S hS _ _
      have hE : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hS)
      exact ⟨[], by simp, List.nodup_nil, fun i => by simp [hE]⟩
    | succ k ih =>
      intro S hS hcl hcl'
      by_cases hemp : S = ∅
      · exact ⟨[], by simp, List.nodup_nil, fun i => by simp [hemp]⟩
      · obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        have hper : i0 ∈ Function.periodicPts τ := perm_mem_periodicPts τ i0
        let L := Function.minimalPeriod τ i0
        have hLpos : 0 < L := Function.minimalPeriod_pos_of_mem_periodicPts hper
        have hLper : (τ^[L]) i0 = i0 := Function.iterate_minimalPeriod
        let c : List (Fin n) := List.ofFn (fun r : Fin L => (τ^[r.val]) i0)
        have hclen : c.length = L := List.length_ofFn
        have hcnd : c.Nodup := by
          rw [List.nodup_iff_injective_get]
          intro r1 r2 heq
          simp only [c, List.get_eq_getElem, List.getElem_ofFn] at heq
          have h1 : r1.val < L := by omega
          have h2 : r2.val < L := by omega
          by_contra hne
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
          · have hdiff : (τ^[r2.val - r1.val]) i0 = i0 := by
              have hiter : (τ^[r1.val]) ((τ^[r2.val - r1.val]) i0) = (τ^[r1.val]) i0 := by
                rw [← Function.iterate_add_apply, show r1.val + (r2.val - r1.val) = r2.val by omega, heq]
              exact (τ.injective.iterate r1.val) hiter
            have hle := Function.IsPeriodicPt.minimalPeriod_le (by omega : 0 < r2.val - r1.val) hdiff
            omega
          · have hdiff : (τ^[r1.val - r2.val]) i0 = i0 := by
              have hiter : (τ^[r2.val]) ((τ^[r1.val - r2.val]) i0) = (τ^[r2.val]) i0 := by
                rw [← Function.iterate_add_apply, show r2.val + (r1.val - r2.val) = r1.val by omega, heq]
              exact (τ.injective.iterate r2.val) hiter
            have hle := Function.IsPeriodicPt.minimalPeriod_le (by omega : 0 < r1.val - r2.val) hdiff
            omega
        have hcstep : ∀ r : Fin c.length,
            τ (c.get r) = c.get ⟨(r.val + 1) % c.length, Nat.mod_lt _ (by have := r.isLt; omega)⟩ := by
          intro r
          have hrL : r.val < L := by rw [← hclen]; exact r.isLt
          simp only [c, List.get_eq_getElem, List.getElem_ofFn, List.length_ofFn]
          rw [← Function.iterate_succ_apply' τ]
          by_cases hlast : r.val + 1 < L
          · rw [Nat.mod_eq_of_lt hlast]
          · have hEq : r.val + 1 = L := by omega
            have hmod0 : (r.val + 1) % L = 0 := by rw [hEq, Nat.mod_self]
            have hsucc : r.val.succ = L := by omega
            rw [hsucc, hLper]
            simp [hmod0]
        have hcsub : ∀ x ∈ c, x ∈ S := by
          intro x hx
          rw [List.mem_ofFn] at hx
          obtain ⟨r, rfl⟩ := hx
          have hiterS : ∀ t : ℕ, (τ^[t]) i0 ∈ S := by
            intro t; induction t with
            | zero => exact hi0
            | succ t iht => rw [Function.iterate_succ_apply' τ]; exact hcl _ iht
          exact hiterS r.val
        have hc_closed : ∀ x, x ∈ c → τ x ∈ c := by
          intro x hx
          obtain ⟨r, rfl⟩ := List.get_of_mem hx
          rw [hcstep r]; exact List.get_mem _ _
        have hc_closed' : ∀ x, x ∈ c → τ.symm x ∈ c := by
          intro x hx
          rw [List.mem_ofFn] at hx
          obtain ⟨r, rfl⟩ := hx
          rw [List.mem_ofFn]
          by_cases hr0 : r.val = 0
          · refine ⟨⟨L - 1, by omega⟩, ?_⟩
            apply τ.injective
            rw [Equiv.apply_symm_apply, ← Function.iterate_succ_apply' τ,
                show (L - 1).succ = L by omega, hLper, hr0]; rfl
          · refine ⟨⟨r.val - 1, by omega⟩, ?_⟩
            apply τ.injective
            rw [Equiv.apply_symm_apply, ← Function.iterate_succ_apply' τ,
                show (r.val - 1).succ = r.val by omega]
        let S' := S \ c.toFinset
        have hS'lt : S'.card ≤ k := by
          have hi0c : i0 ∈ c.toFinset := by
            rw [List.mem_toFinset, List.mem_ofFn]
            exact ⟨⟨0, hLpos⟩, rfl⟩
          have hss : S' ⊂ S := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨Finset.sdiff_subset, fun h => ?_⟩
            have : i0 ∈ S' := h ▸ hi0
            exact (Finset.mem_sdiff.mp this).2 hi0c
          have := Finset.card_lt_card hss; omega
        have hS'cl : ∀ i ∈ S', τ i ∈ S' := by
          intro i hi
          rcases Finset.mem_sdiff.mp hi with ⟨hiS, hic⟩
          refine Finset.mem_sdiff.mpr ⟨hcl i hiS, fun h => hic ?_⟩
          rw [List.mem_toFinset] at h ⊢
          have := hc_closed' _ h
          simpa using this
        have hS'cl' : ∀ i ∈ S', τ.symm i ∈ S' := by
          intro i hi
          rcases Finset.mem_sdiff.mp hi with ⟨hiS, hic⟩
          refine Finset.mem_sdiff.mpr ⟨hcl' i hiS, fun h => hic ?_⟩
          rw [List.mem_toFinset] at h ⊢
          have := hc_closed _ h
          simpa using this
        obtain ⟨cycs, hcycs, hnd, hmem⟩ := ih S' hS'lt hS'cl hS'cl'
        refine ⟨c :: cycs, ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨by omega, hcnd, hcstep⟩
          · exact hcycs x hx
        · rw [List.flatten_cons, List.nodup_append]
          refine ⟨hcnd, hnd, fun a ha b hb hab => ?_⟩
          subst hab
          have := (hmem a).mp hb
          exact (Finset.mem_sdiff.mp this).2 (List.mem_toFinset.mpr ha)
        · intro i
          rw [List.flatten_cons, List.mem_append, hmem i, Finset.mem_sdiff, List.mem_toFinset]
          by_cases hic : i ∈ c
          · exact ⟨fun _ => hcsub i hic, fun _ => Or.inl hic⟩
          · simp [hic]
  obtain ⟨cycs, hcycs, hnd, hmem⟩ := haux n Finset.univ (by simp) (fun _ _ => Finset.mem_univ _)
    (fun _ _ => Finset.mem_univ _)
  exact ⟨cycs, hcycs, hnd, fun i => (hmem i).mpr (Finset.mem_univ i)⟩

lemma foldl_xor_init (a : Bool) (l : List Bool) :
    l.foldl xor a = xor a (l.foldl xor false) := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih (xor a x), ih x]
    cases a <;> cases x <;> cases xs.foldl xor false <;> decide

lemma foldl_xor_cons (a b : Bool) (l : List Bool) :
    (b :: l).foldl xor a = xor b (l.foldl xor a) := by
  simp only [List.foldl_cons]
  rw [foldl_xor_init (xor a b) l, foldl_xor_init a l]
  cases a <;> cases b <;> cases l.foldl xor false <;> decide

lemma foldl_xor_append (l1 l2 : List Bool) (a : Bool) :
    (l1 ++ l2).foldl xor a = xor (l1.foldl xor false) (l2.foldl xor a) := by
  induction l1 generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, foldl_xor_cons, ih]
    cases x <;> cases xs.foldl xor false <;> cases l2.foldl xor a <;> decide

lemma split_interval (N : ℕ) (isPin : ℕ → Bool) (h0 : isPin 0 = true) (hN : 0 < N) :
    ∃ segs : List (ℕ × ℕ),
      (∀ s ∈ segs, s.1 < s.2 ∧ s.2 ≤ N ∧ isPin s.1 = true ∧
        (s.2 < N → isPin s.2 = true) ∧ ∀ t, s.1 < t → t < s.2 → isPin t = false) ∧
      (∀ t < N, ∃! k : Fin segs.length, (segs.get k).1 ≤ t ∧ t < (segs.get k).2) ∧
      (∀ val : ℕ → Bool, (segs.map (fun s => xor (val s.1) (val s.2))).foldl xor false = xor (val 0) (val N)) := by
  have haux : ∀ d a : ℕ, a + d = N → a < N → isPin a = true →
      ∃ segs : List (ℕ × ℕ),
        (∀ s ∈ segs, a ≤ s.1 ∧ s.1 < s.2 ∧ s.2 ≤ N ∧ isPin s.1 = true ∧
          (s.2 < N → isPin s.2 = true) ∧ ∀ t, s.1 < t → t < s.2 → isPin t = false) ∧
        (∀ t, a ≤ t → t < N → ∃! k : Fin segs.length, (segs.get k).1 ≤ t ∧ t < (segs.get k).2) ∧
        (∀ val : ℕ → Bool, (segs.map (fun s => xor (val s.1) (val s.2))).foldl xor false = xor (val a) (val N)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro a had haN hpa
      let nextSet : Finset ℕ := (Finset.Ioo a N).filter (fun t => isPin t = true)
      by_cases hne : nextSet.Nonempty
      · let b := nextSet.min' hne
        have hb_mem : b ∈ nextSet := Finset.min'_mem nextSet hne
        have hb_Ioo : a < b ∧ b < N := Finset.mem_Ioo.mp (Finset.mem_filter.mp hb_mem).1
        have hpb : isPin b = true := (Finset.mem_filter.mp hb_mem).2
        have hbetween : ∀ t, a < t → t < b → isPin t = false := by
          intro t hat htb
          by_contra hf
          have ht : isPin t = true := Bool.eq_true_of_not_eq_false hf
          have htm : t ∈ nextSet := Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hat, by omega⟩, ht⟩
          have hle := Finset.min'_le nextSet t htm
          omega
        obtain ⟨tl, htl_ok, htl_cov, htl_xor⟩ := ih (N - b) (by omega) b (by omega) hb_Ioo.2 hpb
        refine ⟨(a, b) :: tl, ?_, ?_, ?_⟩
        · intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · exact ⟨le_rfl, hb_Ioo.1, hb_Ioo.2.le, hpa, fun _ => hpb, hbetween⟩
          · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := htl_ok s hs
            exact ⟨by omega, h2, h3, h4, h5, h6⟩
        · intro t hat htN
          by_cases htb : t < b
          · refine ⟨⟨0, Nat.zero_lt_succ _⟩, ⟨hat, htb⟩, ?_⟩
            intro k hk
            rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
            · rfl
            · have hk1 := (htl_ok (tl.get k') (List.get_mem _ _)).1
              have hk' : (tl.get k').1 ≤ t ∧ t < (tl.get k').2 := by
                simpa [List.get_eq_getElem] using hk
              omega
          · obtain ⟨k', hk', hunk'⟩ := htl_cov t (by omega) htN
            refine ⟨k'.succ, ?_, ?_⟩
            · simpa [List.get_eq_getElem] using hk'
            · intro k hk
              rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
              · have hk0 : a ≤ t ∧ t < b := by simpa [List.get_eq_getElem] using hk
                omega
              · congr 1; apply hunk'; simpa [List.get_eq_getElem] using hk
        · intro val
          simp only [List.map_cons, foldl_xor_cons, htl_xor val]
          cases val a <;> cases val b <;> cases val N <;> decide
      · have hbetween : ∀ t, a < t → t < N → isPin t = false := by
          intro t hat htN
          by_contra hf
          have ht : isPin t = true := Bool.eq_true_of_not_eq_false hf
          exact hne ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hat, htN⟩, ht⟩⟩
        refine ⟨[(a, N)], ?_, ?_, ?_⟩
        · intro s hs
          simp only [List.mem_singleton] at hs; subst hs
          exact ⟨le_rfl, haN, le_rfl, hpa, fun h => absurd h (lt_irrefl N), hbetween⟩
        · intro t hat htN
          refine ⟨⟨0, Nat.zero_lt_one⟩, ⟨hat, htN⟩, fun k _ => ?_⟩
          have hk : k.val = 0 := Nat.lt_one_iff.mp k.isLt
          exact Fin.ext hk
        · intro val; simp
  obtain ⟨segs, hok, hcov, hxor⟩ := haux N 0 (Nat.zero_add N) hN h0
  exact ⟨segs, fun s hs => (hok s hs).2, fun t ht => hcov t (Nat.zero_le t) ht, hxor⟩

def interleave {α : Type*} : List α → List α → List α
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => x :: y :: interleave xs ys

lemma interleave_perm {α : Type*} : ∀ xs ys : List α, (interleave xs ys).Perm (xs ++ ys)
  | [], ys => by simp [interleave]
  | x :: xs, [] => by simp [interleave]
  | x :: xs, y :: ys => by
    simp only [interleave, List.cons_append]
    apply List.Perm.cons x
    have h1 := interleave_perm xs ys
    have h2 : (y :: interleave xs ys).Perm (y :: (xs ++ ys)) := h1.cons y
    exact h2.trans List.perm_middle.symm

lemma mod_two_mul_div (t L : ℕ) (hL : 0 < L) :
    t % (2 * L) / 2 = (t / 2) % L := by
  have h1 : t = 2 * (t / 2) + t % 2 := (Nat.div_add_mod t 2).symm
  have hq := Nat.div_add_mod (t / 2) L
  have hm : t % 2 < 2 := Nat.mod_lt t (by omega)
  have hlt : 2 * ((t / 2) % L) + t % 2 < 2 * L := by have := Nat.mod_lt (t / 2) hL; omega
  have heq : t = (2 * L) * (t / 2 / L) + (2 * ((t / 2) % L) + t % 2) := by
    calc t = 2 * (t / 2) + t % 2 := h1
      _ = 2 * (L * (t / 2 / L) + (t / 2) % L) + t % 2 := by rw [hq]
      _ = (2 * L) * (t / 2 / L) + (2 * ((t / 2) % L) + t % 2) := by ring
  have hmod : t % (2 * L) = 2 * ((t / 2) % L) + t % 2 := by
    conv_lhs => rw [heq]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  rw [hmod]; omega

lemma extract_segs {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (pin : Bool × Fin n → Option Bool)
    (hpinned : ∀ i : Fin n, ∃ t : ℕ,
      pin (false, (((M true).trans (M false).symm)^[t]) i) ≠ none ∨
      pin (true, M true ((((M true).trans (M false).symm)^[t]) i)) ≠ none) :
    ∃ segs : List (ℕ × ℕ × Bool),
      (∀ d : Fin (n + 1) × Fin (n + 1),
        histDef (fun h i => M h i) pin d =
        convList (segs.map fun s => segHist s.1 s.2.1 s.2.2) (d.1.val, d.2.val)) ∧
      (∀ s ∈ segs, (s.1 = s.2.1 ∧ 0 < s.1) ∨ s.1 = s.2.1 + 1 ∨ s.2.1 = s.1 + 1) ∧
      (segs.map (·.1)).sum = n ∧ (segs.map (·.2.1)).sum = n ∧
      (segs.map (·.2.2)).foldl xor false = false := by
  classical
  let τ : Equiv.Perm (Fin n) := (M true).trans (M false).symm
  obtain ⟨cycs, hcycs, hflat_nd, hflat_mem⟩ := cycle_decomp τ
  have hcyc_pos : ∀ c : Fin cycs.length, 0 < (cycs.get c).length := fun c =>
    (hcycs _ (List.get_mem _ _)).1
  have hcyc_step : ∀ c : Fin cycs.length, ∀ r : Fin (cycs.get c).length,
      τ ((cycs.get c).get r) =
      (cycs.get c).get ⟨(r.val + 1) % (cycs.get c).length, Nat.mod_lt _ (hcyc_pos c)⟩ := fun c =>
    (hcycs _ (List.get_mem _ _)).2.2
  have hcyc_iter : ∀ c : Fin cycs.length, ∀ t : ℕ,
      (τ^[t]) ((cycs.get c).get ⟨0, hcyc_pos c⟩) =
      (cycs.get c).get ⟨t % (cycs.get c).length, Nat.mod_lt _ (hcyc_pos c)⟩ := by
    intro c t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply' τ, ih, hcyc_step c]
      congr 1; ext; simp [Nat.add_mod]
  let cVert (c : Fin cycs.length) (t : ℕ) : Bool × Fin n :=
    let L := (cycs.get c).length
    let i := (cycs.get c).get ⟨(t / 2) % L, Nat.mod_lt _ (hcyc_pos c)⟩
    if t % 2 = 0 then (false, i) else (true, M true i)
  let cEdge (c : Fin cycs.length) (t : ℕ) : Bool × Fin n :=
    let L := (cycs.get c).length
    if t % 2 = 0 then (true, (cycs.get c).get ⟨(t / 2) % L, Nat.mod_lt _ (hcyc_pos c)⟩)
    else (false, (cycs.get c).get ⟨(t / 2 + 1) % L, Nat.mod_lt _ (hcyc_pos c)⟩)
  have hcVert_mod : ∀ c t, cVert c (t % (2 * (cycs.get c).length)) = cVert c t := by
    intro c t
    have hL := hcyc_pos c
    dsimp only [cVert]
    have h1 : t % (2 * (cycs.get c).length) % 2 = t % 2 := Nat.mod_mod_of_dvd t (dvd_mul_right 2 _)
    have h2 : t % (2 * (cycs.get c).length) / 2 % (cycs.get c).length = t / 2 % (cycs.get c).length := by
      rw [mod_two_mul_div t _ hL, Nat.mod_mod]
    have hfin : (⟨t % (2 * (cycs.get c).length) / 2 % (cycs.get c).length, Nat.mod_lt _ hL⟩ : Fin (cycs.get c).length) =
        ⟨t / 2 % (cycs.get c).length, Nat.mod_lt _ hL⟩ := Fin.ext h2
    rw [h1, hfin]
  have hcEdge_mod : ∀ c t, cEdge c (t % (2 * (cycs.get c).length)) = cEdge c t := by
    intro c t
    have hL := hcyc_pos c
    dsimp only [cEdge]
    have h1 : t % (2 * (cycs.get c).length) % 2 = t % 2 := Nat.mod_mod_of_dvd t (dvd_mul_right 2 _)
    have h2 : t % (2 * (cycs.get c).length) / 2 = (t / 2) % (cycs.get c).length := mod_two_mul_div t _ hL
    have hfin1 : (⟨t % (2 * (cycs.get c).length) / 2 % (cycs.get c).length, Nat.mod_lt _ hL⟩ : Fin (cycs.get c).length) =
        ⟨t / 2 % (cycs.get c).length, Nat.mod_lt _ hL⟩ := Fin.ext (by dsimp only; rw [h2, Nat.mod_mod])
    have hfin2 : (⟨(t % (2 * (cycs.get c).length) / 2 + 1) % (cycs.get c).length, Nat.mod_lt _ hL⟩ : Fin (cycs.get c).length) =
        ⟨(t / 2 + 1) % (cycs.get c).length, Nat.mod_lt _ hL⟩ := Fin.ext (by dsimp only; rw [h2, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod])
    rw [h1, hfin1, hfin2]
  have hcEdge_adj : ∀ c t,
      let e := cEdge c t
      (cVert c t = (false, e.2) ∧ cVert c (t + 1) = (true, M e.1 e.2)) ∨
      (cVert c t = (true, M e.1 e.2) ∧ cVert c (t + 1) = (false, e.2)) := by
    intro c t
    have hL := hcyc_pos c
    dsimp only [cVert, cEdge]
    rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
    · left
      have h1' : (t + 1) % 2 = 1 := by omega
      have hd : (t + 1) / 2 = t / 2 := by omega
      have hfin : (⟨(t + 1) / 2 % (cycs.get c).length, Nat.mod_lt _ hL⟩ : Fin (cycs.get c).length) =
          ⟨t / 2 % (cycs.get c).length, Nat.mod_lt _ hL⟩ := Fin.ext (by dsimp only; rw [hd])
      simp only [h0, ↓reduceIte, h1', show ¬ (1 : ℕ) = 0 by decide]
      exact ⟨trivial, by rw [hfin]⟩
    · right
      have h0' : (t + 1) % 2 = 0 := by omega
      have hd : (t + 1) / 2 = t / 2 + 1 := by omega
      have hfin : (⟨(t + 1) / 2 % (cycs.get c).length, Nat.mod_lt _ hL⟩ : Fin (cycs.get c).length) =
          ⟨(t / 2 + 1) % (cycs.get c).length, Nat.mod_lt _ hL⟩ := Fin.ext (by dsimp only; rw [hd])
      simp only [h1, show ¬ (1 : ℕ) = 0 by decide, h0', ↓reduceIte, hfin, and_true]
      congr 1
      have hst := hcyc_step c ⟨(t / 2) % (cycs.get c).length, Nat.mod_lt _ hL⟩
      have hfin2 : (⟨((t / 2) % (cycs.get c).length + 1) % (cycs.get c).length, Nat.mod_lt _ hL⟩ : Fin (cycs.get c).length) =
          ⟨(t / 2 + 1) % (cycs.get c).length, Nat.mod_lt _ hL⟩ := Fin.ext (by simp [Nat.add_mod])
      rw [hfin2] at hst
      have hst' : M false ((cycs.get c).get ⟨(t / 2 + 1) % (cycs.get c).length, Nat.mod_lt _ hL⟩) =
          M true ((cycs.get c).get ⟨(t / 2) % (cycs.get c).length, Nat.mod_lt _ hL⟩) := by
        rw [← hst]; simp [τ]
      exact hst'.symm
  have hcyc_pin : ∀ c : Fin cycs.length, ∃ r0 < 2 * (cycs.get c).length, (pin (cVert c r0)).isSome = true := by
    intro c
    have hL := hcyc_pos c
    obtain ⟨t, ht⟩ := hpinned ((cycs.get c).get ⟨0, hL⟩)
    rw [hcyc_iter c t] at ht
    let r := t % (cycs.get c).length
    have hr : r < (cycs.get c).length := Nat.mod_lt _ hL
    rcases ht with h | h
    · refine ⟨2 * r, by omega, ?_⟩
      have hv : cVert c (2 * r) = (false, (cycs.get c).get ⟨r, hr⟩) := by
        dsimp only [cVert]
        have hfin : (⟨2 * r / 2 % (cycs.get c).length, Nat.mod_lt _ hL⟩ : Fin (cycs.get c).length) = ⟨r, hr⟩ :=
          Fin.ext (by dsimp only; rw [Nat.mul_div_right r (by omega), Nat.mod_eq_of_lt hr])
        simp only [Nat.mul_mod_right, ↓reduceIte, hfin]
      rw [hv]; exact Option.isSome_iff_ne_none.mpr h
    · refine ⟨2 * r + 1, by omega, ?_⟩
      have hv : cVert c (2 * r + 1) = (true, M true ((cycs.get c).get ⟨r, hr⟩)) := by
        dsimp only [cVert]
        have hm1 : (2 * r + 1) % 2 = 1 := by omega
        have hfin : (⟨(2 * r + 1) / 2 % (cycs.get c).length, Nat.mod_lt _ hL⟩ : Fin (cycs.get c).length) = ⟨r, hr⟩ :=
          Fin.ext (by dsimp only; rw [show (2 * r + 1) / 2 = r by omega, Nat.mod_eq_of_lt hr])
        simp only [hm1, show ¬ (1 : ℕ) = 0 by decide, ↓reduceIte, hfin]
      rw [hv]; exact Option.isSome_iff_ne_none.mpr h
  choose r0 hr0_lt hr0_pin using hcyc_pin
  have hsplit : ∀ c : Fin cycs.length,
      ∃ l : List (ℕ × ℕ),
        (∀ s ∈ l, s.1 < s.2 ∧ s.2 ≤ 2 * (cycs.get c).length ∧
          (pin (cVert c ((r0 c + s.1) % (2 * (cycs.get c).length)))).isSome = true ∧
          (s.2 < 2 * (cycs.get c).length → (pin (cVert c ((r0 c + s.2) % (2 * (cycs.get c).length)))).isSome = true) ∧
          ∀ t, s.1 < t → t < s.2 → (pin (cVert c ((r0 c + t) % (2 * (cycs.get c).length)))).isSome = false) ∧
        (∀ t < 2 * (cycs.get c).length, ∃! k : Fin l.length, (l.get k).1 ≤ t ∧ t < (l.get k).2) ∧
        (∀ val : ℕ → Bool, (l.map (fun s => xor (val s.1) (val s.2))).foldl xor false = xor (val 0) (val (2 * (cycs.get c).length))) := by
    intro c
    apply split_interval (2 * (cycs.get c).length)
      (fun t => (pin (cVert c ((r0 c + t) % (2 * (cycs.get c).length)))).isSome)
    · rw [Nat.add_zero, Nat.mod_eq_of_lt (hr0_lt c)]; exact hr0_pin c
    · have := hcyc_pos c; omega
  choose raw hraw_ok hraw_cov hraw_xor using hsplit

  let allIdx : List (Σ c : Fin cycs.length, Fin (raw c).length) :=
    (List.finRange cycs.length).flatMap (fun c => (List.finRange (raw c).length).map (fun k => ⟨c, k⟩))
  let K := allIdx.length
  let getIdx (idx : Fin K) : Σ c : Fin cycs.length, Fin (raw c).length := allIdx.get idx
  let segA (idx : Fin K) : ℕ := ((raw (getIdx idx).1).get (getIdx idx).2).1
  let segB (idx : Fin K) : ℕ := ((raw (getIdx idx).1).get (getIdx idx).2).2
  let m (idx : Fin K) : ℕ := segB idx - segA idx
  have hm : ∀ idx : Fin K, 1 ≤ m idx := by
    intro idx
    have h := (hraw_ok (getIdx idx).1 _ (List.get_mem _ (getIdx idx).2)).1
    dsimp only [m, segA, segB]; omega
  let verts (idx : Fin K) (j : Fin (m idx + 1)) : Bool × Fin n :=
    let c := (getIdx idx).1
    cVert c ((r0 c + segA idx + j.val) % (2 * (cycs.get c).length))
  let ecols (idx : Fin K) (j : Fin (m idx)) : Bool :=
    let c := (getIdx idx).1
    (cEdge c ((r0 c + segA idx + j.val) % (2 * (cycs.get c).length))).1
  let eidx (idx : Fin K) (j : Fin (m idx)) : Fin n :=
    let c := (getIdx idx).1
    (cEdge c ((r0 c + segA idx + j.val) % (2 * (cycs.get c).length))).2
  let c0 (idx : Fin K) : Bool := (pin (verts idx 0)).getD false
  let c1 (idx : Fin K) : Bool := (pin (verts idx (Fin.last (m idx)))).getD false
  have hpin0 : ∀ idx : Fin K, pin (verts idx 0) = some (c0 idx) := by
    intro idx
    have h := (hraw_ok (getIdx idx).1 _ (List.get_mem _ (getIdx idx).2)).2.2.1
    have hv : verts idx 0 = cVert (getIdx idx).1 ((r0 (getIdx idx).1 + segA idx) % (2 * (cycs.get (getIdx idx).1).length)) := by
      dsimp only [verts, Fin.val_zero, Nat.add_zero]
    rw [hv]
    cases hp : pin (cVert (getIdx idx).1 ((r0 (getIdx idx).1 + segA idx) % (2 * (cycs.get (getIdx idx).1).length))) with
    | none => rw [hp] at h; simp at h
    | some b => dsimp only [c0]; rw [hv, hp]; rfl
  have hpin1 : ∀ idx : Fin K, pin (verts idx (Fin.last (m idx))) = some (c1 idx) := by
    intro idx
    have hok := hraw_ok (getIdx idx).1 _ (List.get_mem _ (getIdx idx).2)
    have hlast : r0 (getIdx idx).1 + segA idx + m idx = r0 (getIdx idx).1 + segB idx := by
      have hlt := hok.1; dsimp only [m, segA, segB] at hlt ⊢; omega
    have hv : verts idx (Fin.last (m idx)) =
        cVert (getIdx idx).1 ((r0 (getIdx idx).1 + segB idx) % (2 * (cycs.get (getIdx idx).1).length)) := by
      dsimp [verts]; simp [hlast]
    have his : (pin (verts idx (Fin.last (m idx)))).isSome = true := by
      rw [hv]
      by_cases hlt : segB idx < 2 * (cycs.get (getIdx idx).1).length
      · exact hok.2.2.2.1 hlt
      · have heq : segB idx = 2 * (cycs.get (getIdx idx).1).length := by
          have hle := hok.2.1; dsimp only [segB] at hlt hle ⊢; omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (hr0_lt _)]
        exact hr0_pin _
    cases hp : pin (verts idx (Fin.last (m idx))) with
    | none => rw [hp] at his; simp at his
    | some b => simp [c1, hp]
  have hedge : ∀ idx (j : Fin (m idx)),
      (verts idx j.castSucc = (false, eidx idx j) ∧ verts idx j.succ = (true, M (ecols idx j) (eidx idx j))) ∨
      (verts idx j.castSucc = (true, M (ecols idx j) (eidx idx j)) ∧ verts idx j.succ = (false, eidx idx j)) := by
    intro idx j
    let c := (getIdx idx).1
    let t := r0 c + segA idx + j.val
    have hv0 : verts idx j.castSucc = cVert c t := hcVert_mod c t
    have hv1 : verts idx j.succ = cVert c (t + 1) := by
      dsimp [verts]; rw [show r0 c + segA idx + (j.val + 1) = t + 1 by omega]; exact hcVert_mod c (t + 1)
    have he0 : (ecols idx j, eidx idx j) = cEdge c t :=
      congrArg (fun p => (p.1, p.2)) (hcEdge_mod c t)
    rw [hv0, hv1]
    have h1 := hcEdge_adj c t
    rw [← he0] at h1
    exact h1

  have hflat_bij : ∀ i : Fin n, ∃! p : Σ c : Fin cycs.length, Fin (cycs.get c).length,
      (cycs.get p.1).get p.2 = i := by
    intro i
    have hm := hflat_mem i
    rw [List.mem_flatten] at hm
    obtain ⟨l, hl, hil⟩ := hm
    obtain ⟨c, rfl⟩ := List.get_of_mem hl
    obtain ⟨r, rfl⟩ := List.get_of_mem hil
    refine ⟨⟨c, r⟩, rfl, ?_⟩
    rintro ⟨c', r'⟩ heq
    have hnd := hflat_nd
    by_contra hne

    have hget_inj : ∀ (p1 p2 : Σ c : Fin cycs.length, Fin (cycs.get c).length),
        (cycs.get p1.1).get p1.2 = (cycs.get p2.1).get p2.2 → p1 = p2 := by
      intro p1 p2 hp
      by_cases hc : p1.1 = p2.1
      · rcases p1 with ⟨c1, r1⟩; rcases p2 with ⟨c2, r2⟩
        dsimp at hc hp; subst hc
        have hndc := (hcycs _ (List.get_mem _ c1)).2.1
        rw [List.nodup_iff_injective_get] at hndc
        exact Sigma.ext rfl (heq_of_eq (hndc hp))
      · exfalso
        have hpw := List.nodup_flatten.mp hnd
        have hdisj := hpw.2
        have hmem_pair : ∀ (a b : Fin cycs.length), a ≠ b → List.Disjoint (cycs.get a) (cycs.get b) := by
          intro a b hab
          have hidx := List.pairwise_iff_get.mp hdisj
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hlt
          · exact hidx a b hlt
          · exact (hidx b a hlt).symm
        exact hmem_pair p1.1 p2.1 hc (List.get_mem _ p1.2) (hp ▸ List.get_mem _ p2.2)
    exact hne (hget_inj ⟨c', r'⟩ ⟨c, r⟩ heq)

  have hallIdx_nd : allIdx.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun c _ => (List.nodup_finRange _).map (fun _ _ h => by cases h; rfl), ?_⟩
    exact (List.nodup_finRange _).imp (fun {c1 c2} hne => by
      intro p hp1 hp2
      simp only [List.mem_map] at hp1 hp2
      rcases hp1 with ⟨_, _, rfl⟩; rcases hp2 with ⟨_, _, h⟩
      exact hne (congrArg Sigma.fst h).symm)
  have hallIdx_mem : ∀ p : Σ c : Fin cycs.length, Fin (raw c).length, p ∈ allIdx := by
    intro ⟨c, k⟩
    simp only [allIdx, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
    exact ⟨c, k, rfl⟩
  have hgetIdx_bij : ∀ p : Σ c : Fin cycs.length, Fin (raw c).length, ∃! idx : Fin K, getIdx idx = p := by
    intro p
    obtain ⟨idx, hidx⟩ := List.get_of_mem (hallIdx_mem p)
    refine ⟨idx, hidx, fun idx' hidx' => ?_⟩
    exact (List.nodup_iff_injective_get.mp hallIdx_nd) (hidx'.trans hidx.symm)

  have hrot_inj : ∀ c a b, a < 2 * (cycs.get c).length → b < 2 * (cycs.get c).length →
      (r0 c + a) % (2 * (cycs.get c).length) = (r0 c + b) % (2 * (cycs.get c).length) → a = b := by
    intro c a b ha hb h1
    have h3 : r0 c < 2 * (cycs.get c).length := hr0_lt c
    by_cases ha' : r0 c + a < 2 * (cycs.get c).length <;> by_cases hb' : r0 c + b < 2 * (cycs.get c).length
    · rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h1; omega
    · rw [Nat.mod_eq_of_lt ha', show (r0 c + b) % (2 * (cycs.get c).length) = r0 c + b - 2 * (cycs.get c).length by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]] at h1; omega
    · rw [Nat.mod_eq_of_lt hb', show (r0 c + a) % (2 * (cycs.get c).length) = r0 c + a - 2 * (cycs.get c).length by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]] at h1; omega
    · rw [show (r0 c + a) % (2 * (cycs.get c).length) = r0 c + a - 2 * (cycs.get c).length by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)],
          show (r0 c + b) % (2 * (cycs.get c).length) = r0 c + b - 2 * (cycs.get c).length by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]] at h1; omega
  have hcEdge_inj : ∀ c1 c2 t1 t2, t1 < 2 * (cycs.get c1).length → t2 < 2 * (cycs.get c2).length →
      cEdge c1 t1 = cEdge c2 t2 → c1 = c2 ∧ t1 = t2 := by
    intro c1 c2 t1 t2 ht1 ht2 heq
    have hcol : (cEdge c1 t1).1 = (cEdge c2 t2).1 := congrArg Prod.fst heq
    have hidx : (cEdge c1 t1).2 = (cEdge c2 t2).2 := congrArg Prod.snd heq
    dsimp [cEdge] at hcol hidx
    rcases Nat.mod_two_eq_zero_or_one t1 with a0 | a1 <;> rcases Nat.mod_two_eq_zero_or_one t2 with b0 | b1
    · simp only [a0, b0, ↓reduceIte] at hidx
      obtain ⟨_, _, huniq⟩ := hflat_bij ((cycs.get c1).get ⟨t1 / 2 % (cycs.get c1).length, Nat.mod_lt _ (hcyc_pos c1)⟩)
      have h1 := huniq ⟨c1, ⟨t1 / 2 % (cycs.get c1).length, Nat.mod_lt _ (hcyc_pos c1)⟩⟩ rfl
      have h2 := huniq ⟨c2, ⟨t2 / 2 % (cycs.get c2).length, Nat.mod_lt _ (hcyc_pos c2)⟩⟩ hidx.symm
      have hp : (⟨c1, ⟨t1 / 2 % (cycs.get c1).length, Nat.mod_lt _ (hcyc_pos c1)⟩⟩ : Σ c : Fin cycs.length, Fin (cycs.get c).length) =
          ⟨c2, ⟨t2 / 2 % (cycs.get c2).length, Nat.mod_lt _ (hcyc_pos c2)⟩⟩ := h1.trans h2.symm
      have hce : c1 = c2 := congrArg Sigma.fst hp
      refine ⟨hce, ?_⟩
      subst hce
      have hr : t1 / 2 % (cycs.get c1).length = t2 / 2 % (cycs.get c1).length :=
        congrArg Fin.val (eq_of_heq (Sigma.mk.inj hp).2)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hr
      omega
    · simp [a0, b1] at hcol
    · simp [a1, b0] at hcol
    · simp only [a1, b1, show ¬ (1 : ℕ) = 0 by decide, ↓reduceIte] at hidx
      obtain ⟨_, _, huniq⟩ := hflat_bij ((cycs.get c1).get ⟨(t1 / 2 + 1) % (cycs.get c1).length, Nat.mod_lt _ (hcyc_pos c1)⟩)
      have h1 := huniq ⟨c1, ⟨(t1 / 2 + 1) % (cycs.get c1).length, Nat.mod_lt _ (hcyc_pos c1)⟩⟩ rfl
      have h2 := huniq ⟨c2, ⟨(t2 / 2 + 1) % (cycs.get c2).length, Nat.mod_lt _ (hcyc_pos c2)⟩⟩ hidx.symm
      have hp : (⟨c1, ⟨(t1 / 2 + 1) % (cycs.get c1).length, Nat.mod_lt _ (hcyc_pos c1)⟩⟩ : Σ c : Fin cycs.length, Fin (cycs.get c).length) =
          ⟨c2, ⟨(t2 / 2 + 1) % (cycs.get c2).length, Nat.mod_lt _ (hcyc_pos c2)⟩⟩ := h1.trans h2.symm
      have hce : c1 = c2 := congrArg Sigma.fst hp
      refine ⟨hce, ?_⟩
      subst hce
      have hr : (t1 / 2 + 1) % (cycs.get c1).length = (t2 / 2 + 1) % (cycs.get c1).length :=
        congrArg Fin.val (eq_of_heq (Sigma.mk.inj hp).2)
      have hL := hcyc_pos c1
      have hdiv : t1 / 2 = t2 / 2 := by
        by_cases x1 : t1 / 2 + 1 < (cycs.get c1).length <;> by_cases x2 : t2 / 2 + 1 < (cycs.get c1).length
        · rw [Nat.mod_eq_of_lt x1, Nat.mod_eq_of_lt x2] at hr; omega
        · have hx2 : t2 / 2 + 1 = (cycs.get c1).length := by omega
          rw [Nat.mod_eq_of_lt x1, hx2, Nat.mod_self] at hr; omega
        · have hx1 : t1 / 2 + 1 = (cycs.get c1).length := by omega
          rw [Nat.mod_eq_of_lt x2, hx1, Nat.mod_self] at hr; omega
        · omega
      omega
  have hcVert_inj : ∀ c1 c2 t1 t2, t1 < 2 * (cycs.get c1).length → t2 < 2 * (cycs.get c2).length →
      cVert c1 t1 = cVert c2 t2 → c1 = c2 ∧ t1 = t2 := by
    intro c1 c2 t1 t2 ht1 ht2 heq
    have hcol : (cVert c1 t1).1 = (cVert c2 t2).1 := congrArg Prod.fst heq
    have hidx : (cVert c1 t1).2 = (cVert c2 t2).2 := congrArg Prod.snd heq
    dsimp [cVert] at hcol hidx
    rcases Nat.mod_two_eq_zero_or_one t1 with a0 | a1 <;> rcases Nat.mod_two_eq_zero_or_one t2 with b0 | b1
    · simp only [a0, b0, ↓reduceIte] at hidx
      obtain ⟨_, _, huniq⟩ := hflat_bij ((cycs.get c1).get ⟨t1 / 2 % (cycs.get c1).length, Nat.mod_lt _ (hcyc_pos c1)⟩)
      have h1 := huniq ⟨c1, ⟨t1 / 2 % (cycs.get c1).length, Nat.mod_lt _ (hcyc_pos c1)⟩⟩ rfl
      have h2 := huniq ⟨c2, ⟨t2 / 2 % (cycs.get c2).length, Nat.mod_lt _ (hcyc_pos c2)⟩⟩ hidx.symm
      have hp : (⟨c1, ⟨t1 / 2 % (cycs.get c1).length, Nat.mod_lt _ (hcyc_pos c1)⟩⟩ : Σ c : Fin cycs.length, Fin (cycs.get c).length) =
          ⟨c2, ⟨t2 / 2 % (cycs.get c2).length, Nat.mod_lt _ (hcyc_pos c2)⟩⟩ := h1.trans h2.symm
      have hce : c1 = c2 := congrArg Sigma.fst hp
      refine ⟨hce, ?_⟩
      subst hce
      have hr : t1 / 2 % (cycs.get c1).length = t2 / 2 % (cycs.get c1).length :=
        congrArg Fin.val (eq_of_heq (Sigma.mk.inj hp).2)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hr
      omega
    · simp [a0, b1] at hcol
    · simp [a1, b0] at hcol
    · simp only [a1, b1, show ¬ (1 : ℕ) = 0 by decide, ↓reduceIte] at hidx
      have hidx' := (M true).injective hidx
      obtain ⟨_, _, huniq⟩ := hflat_bij ((cycs.get c1).get ⟨t1 / 2 % (cycs.get c1).length, Nat.mod_lt _ (hcyc_pos c1)⟩)
      have h1 := huniq ⟨c1, ⟨t1 / 2 % (cycs.get c1).length, Nat.mod_lt _ (hcyc_pos c1)⟩⟩ rfl
      have h2 := huniq ⟨c2, ⟨t2 / 2 % (cycs.get c2).length, Nat.mod_lt _ (hcyc_pos c2)⟩⟩ hidx'.symm
      have hp : (⟨c1, ⟨t1 / 2 % (cycs.get c1).length, Nat.mod_lt _ (hcyc_pos c1)⟩⟩ : Σ c : Fin cycs.length, Fin (cycs.get c).length) =
          ⟨c2, ⟨t2 / 2 % (cycs.get c2).length, Nat.mod_lt _ (hcyc_pos c2)⟩⟩ := h1.trans h2.symm
      have hce : c1 = c2 := congrArg Sigma.fst hp
      refine ⟨hce, ?_⟩
      subst hce
      have hr : t1 / 2 % (cycs.get c1).length = t2 / 2 % (cycs.get c1).length :=
        congrArg Fin.val (eq_of_heq (Sigma.mk.inj hp).2)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hr
      omega
  have heEdge_bij : Function.Bijective (fun p : Σ idx : Fin K, Fin (m idx) => (ecols p.1 p.2, eidx p.1 p.2)) := by
    constructor
    · rintro ⟨idx1, j1⟩ ⟨idx2, j2⟩ heq
      have hok1 := hraw_ok (getIdx idx1).1 _ (List.get_mem _ (getIdx idx1).2)
      have hok2 := hraw_ok (getIdx idx2).1 _ (List.get_mem _ (getIdx idx2).2)
      have ⟨hce, hte⟩ := hcEdge_inj (getIdx idx1).1 (getIdx idx2).1
        ((r0 (getIdx idx1).1 + segA idx1 + j1.val) % (2 * (cycs.get (getIdx idx1).1).length))
        ((r0 (getIdx idx2).1 + segA idx2 + j2.val) % (2 * (cycs.get (getIdx idx2).1).length))
        (Nat.mod_lt _ (by have := hcyc_pos (getIdx idx1).1; omega))
        (Nat.mod_lt _ (by have := hcyc_pos (getIdx idx2).1; omega))
        heq
      have ht1 : segA idx1 + j1.val < 2 * (cycs.get (getIdx idx1).1).length := by
        have hj1 := j1.isLt; have hB1 := hok1.2.1; dsimp only [m, segA, segB] at hj1 hB1 ⊢; omega
      have ht2 : segA idx2 + j2.val < 2 * (cycs.get (getIdx idx2).1).length := by
        have hj2 := j2.isLt; have hB2 := hok2.2.1; dsimp only [m, segA, segB] at hj2 hB2 ⊢; omega
      have hte' : (r0 (getIdx idx1).1 + (segA idx1 + j1.val)) % (2 * (cycs.get (getIdx idx1).1).length) =
          (r0 (getIdx idx2).1 + (segA idx2 + j2.val)) % (2 * (cycs.get (getIdx idx2).1).length) := by
        simpa only [Nat.add_assoc] using hte
      have hsum_eq : segA idx1 + j1.val = segA idx2 + j2.val := by
        revert ht2 hte'; generalize (getIdx idx2).1 = c2 at hce ⊢; subst hce; intro ht2 hte'
        exact hrot_inj _ _ _ ht1 ht2 hte'
      have hidx_eq : idx1 = idx2 := by
        apply (List.nodup_iff_injective_get.mp hallIdx_nd)
        change getIdx idx1 = getIdx idx2
        have hheq : ∀ (c1 c2 : Fin cycs.length) (k1 : Fin (raw c1).length) (k2 : Fin (raw c2).length),
            c1 = c2 → ∀ t < 2 * (cycs.get c1).length,
            (((raw c1).get k1).1 ≤ t ∧ t < ((raw c1).get k1).2) →
            (((raw c2).get k2).1 ≤ t ∧ t < ((raw c2).get k2).2) → HEq k1 k2 := by
          rintro c1 _ k1 k2 rfl t ht h1 h2
          obtain ⟨_, _, huniq⟩ := hraw_cov c1 t ht
          exact heq_of_eq ((huniq k1 h1).trans (huniq k2 h2).symm)
        have hm1 : ((raw (getIdx idx1).1).get (getIdx idx1).2).1 ≤ segA idx1 + j1.val ∧
            segA idx1 + j1.val < ((raw (getIdx idx1).1).get (getIdx idx1).2).2 := by
          have hj1 := j1.isLt; dsimp only [m, segA, segB] at hj1 ⊢; omega
        have hm2 : ((raw (getIdx idx2).1).get (getIdx idx2).2).1 ≤ segA idx1 + j1.val ∧
            segA idx1 + j1.val < ((raw (getIdx idx2).1).get (getIdx idx2).2).2 := by
          have hj2 := j2.isLt; rw [hsum_eq]; dsimp only [m, segA, segB] at hj2 ⊢; omega
        exact Sigma.ext hce (hheq _ _ _ _ hce _ ht1 hm1 hm2)
      subst hidx_eq
      exact Sigma.ext rfl (heq_of_eq (Fin.ext (Nat.add_left_cancel hsum_eq)))
    · rintro ⟨h, i⟩
      obtain ⟨⟨c, r⟩, hcr, _⟩ := hflat_bij i
      have hL := hcyc_pos c
      let L := (cycs.get c).length
      have hL' : 0 < L := hL
      let t_raw : ℕ := if h then 2 * r.val else 2 * ((r.val + L - 1) % L) + 1
      have ht_raw_lt : t_raw < 2 * L := by
        dsimp only [t_raw]; split_ifs
        · have := r.isLt; omega
        · have := Nat.mod_lt (r.val + L - 1) hL'; omega
      have hcE : cEdge c t_raw = (h, i) := by
        dsimp only [cEdge, t_raw]; cases h
        · have hm1 : (2 * ((r.val + L - 1) % L) + 1) % 2 = 1 := by omega
          have hd1 : (2 * ((r.val + L - 1) % L) + 1) / 2 = (r.val + L - 1) % L := by omega
          simp only [Bool.false_eq_true, ↓reduceIte, hm1, show ¬ (1 : ℕ) = 0 by decide]
          congr 1
          have hfin : (⟨((2 * ((r.val + L - 1) % L) + 1) / 2 + 1) % L, Nat.mod_lt _ hL⟩ : Fin L) = r := by
            apply Fin.ext
            dsimp only
            rw [hd1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
                show r.val + L - 1 + 1 = r.val + L by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]
          exact (congrArg (cycs.get c).get hfin).trans hcr
        · have hfin : (⟨2 * r.val / 2 % L, Nat.mod_lt _ hL⟩ : Fin L) = r :=
            Fin.ext (by dsimp only; rw [Nat.mul_div_right r.val (by omega), Nat.mod_eq_of_lt r.isLt])
          simp only [↓reduceIte, Nat.mul_mod_right]
          exact Prod.ext rfl ((congrArg (cycs.get c).get hfin).trans hcr)
      let t_rot : ℕ := (t_raw + 2 * L - r0 c) % (2 * L)
      have ht_rot_lt : t_rot < 2 * L := Nat.mod_lt _ (by omega)
      have hrot_eq : (r0 c + t_rot) % (2 * L) = t_raw := by
        dsimp [t_rot]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show r0 c + (t_raw + 2 * L - r0 c) = t_raw + 2 * L by have := hr0_lt c; omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt ht_raw_lt]
      obtain ⟨k, hk, _⟩ := hraw_cov c t_rot ht_rot_lt
      obtain ⟨idx, hidx, _⟩ := hgetIdx_bij ⟨c, k⟩
      have hA : segA idx = ((raw c).get k).1 := by dsimp [segA]; rw [hidx]
      have hB : segB idx = ((raw c).get k).2 := by dsimp [segB]; rw [hidx]
      let j : Fin (m idx) := ⟨t_rot - segA idx, by dsimp [m]; omega⟩
      refine ⟨⟨idx, j⟩, ?_⟩
      dsimp only [ecols, eidx, j]
      have h1 : (getIdx idx).1 = c := congrArg Sigma.fst hidx
      have ht1 : r0 (getIdx idx).1 + segA idx + (t_rot - segA idx) = r0 (getIdx idx).1 + t_rot := by omega
      rw [ht1]
      revert h1; generalize (getIdx idx).1 = c1; intro h1; subst c1
      change cEdge c ((r0 c + t_rot) % (2 * L)) = (h, i)
      rw [hrot_eq]; exact hcE

  have heVert_bij : Function.Bijective (fun p : Σ idx : Fin K, Fin (m idx - 1) =>
      (⟨verts p.1 ⟨p.2.val + 1, by have := hm p.1; omega⟩, by
        have hok := hraw_ok (getIdx p.1).1 _ (List.get_mem _ (getIdx p.1).2)
        have h1 := hok.2.2.2.2 (segA p.1 + (p.2.val + 1)) (by dsimp only [segA]; omega)
          (by have hp2 := p.2.isLt; have hmp := hm p.1; dsimp only [m, segA, segB] at hp2 hmp ⊢; omega)
        have hv : verts p.1 ⟨p.2.val + 1, by have := hm p.1; omega⟩ =
            cVert (getIdx p.1).1 ((r0 (getIdx p.1).1 + (segA p.1 + (p.2.val + 1))) % (2 * (cycs.get (getIdx p.1).1).length)) := by
          dsimp [verts]; rw [Nat.add_assoc]
        rw [hv]; exact Option.not_isSome_iff_eq_none.mp (by rw [h1]; decide)⟩ : {u : Bool × Fin n // pin u = none})) := by
    constructor
    · rintro ⟨idx1, t1⟩ ⟨idx2, t2⟩ heq
      have hv_eq : verts idx1 ⟨t1.val + 1, by have := hm idx1; omega⟩ =
          verts idx2 ⟨t2.val + 1, by have := hm idx2; omega⟩ := congrArg Subtype.val heq
      have hok1 := hraw_ok (getIdx idx1).1 _ (List.get_mem _ (getIdx idx1).2)
      have hok2 := hraw_ok (getIdx idx2).1 _ (List.get_mem _ (getIdx idx2).2)
      have ⟨hce, hte⟩ := hcVert_inj (getIdx idx1).1 (getIdx idx2).1
        ((r0 (getIdx idx1).1 + segA idx1 + (t1.val + 1)) % (2 * (cycs.get (getIdx idx1).1).length))
        ((r0 (getIdx idx2).1 + segA idx2 + (t2.val + 1)) % (2 * (cycs.get (getIdx idx2).1).length))
        (Nat.mod_lt _ (by have := hcyc_pos (getIdx idx1).1; omega))
        (Nat.mod_lt _ (by have := hcyc_pos (getIdx idx2).1; omega))
        hv_eq
      have ht1 : segA idx1 + (t1.val + 1) < 2 * (cycs.get (getIdx idx1).1).length := by
        have ht1' := t1.isLt; have hm1 := hm idx1; have hB1 := hok1.2.1; dsimp only [m, segA, segB] at ht1' hm1 hB1 ⊢; omega
      have ht2 : segA idx2 + (t2.val + 1) < 2 * (cycs.get (getIdx idx2).1).length := by
        have ht2' := t2.isLt; have hm2 := hm idx2; have hB2 := hok2.2.1; dsimp only [m, segA, segB] at ht2' hm2 hB2 ⊢; omega
      have hte' : (r0 (getIdx idx1).1 + (segA idx1 + (t1.val + 1))) % (2 * (cycs.get (getIdx idx1).1).length) =
          (r0 (getIdx idx2).1 + (segA idx2 + (t2.val + 1))) % (2 * (cycs.get (getIdx idx2).1).length) := by
        simpa only [Nat.add_assoc] using hte
      have hsum_eq : segA idx1 + (t1.val + 1) = segA idx2 + (t2.val + 1) := by
        revert ht2 hte'; generalize (getIdx idx2).1 = c2 at hce ⊢; subst hce; intro ht2 hte'
        exact hrot_inj _ _ _ ht1 ht2 hte'
      have hidx_eq : idx1 = idx2 := by
        apply (List.nodup_iff_injective_get.mp hallIdx_nd)
        change getIdx idx1 = getIdx idx2
        have hheq : ∀ (c1 c2 : Fin cycs.length) (k1 : Fin (raw c1).length) (k2 : Fin (raw c2).length),
            c1 = c2 → ∀ t < 2 * (cycs.get c1).length,
            (((raw c1).get k1).1 ≤ t ∧ t < ((raw c1).get k1).2) →
            (((raw c2).get k2).1 ≤ t ∧ t < ((raw c2).get k2).2) → HEq k1 k2 := by
          rintro c1 _ k1 k2 rfl t ht h1 h2
          obtain ⟨_, _, huniq⟩ := hraw_cov c1 t ht
          exact heq_of_eq ((huniq k1 h1).trans (huniq k2 h2).symm)
        have hm1 : ((raw (getIdx idx1).1).get (getIdx idx1).2).1 ≤ segA idx1 + (t1.val + 1) ∧
            segA idx1 + (t1.val + 1) < ((raw (getIdx idx1).1).get (getIdx idx1).2).2 := by
          have ht1' := t1.isLt; have hmi := hm idx1; dsimp only [m, segA, segB] at ht1' hmi ⊢; omega
        have hm2 : ((raw (getIdx idx2).1).get (getIdx idx2).2).1 ≤ segA idx1 + (t1.val + 1) ∧
            segA idx1 + (t1.val + 1) < ((raw (getIdx idx2).1).get (getIdx idx2).2).2 := by
          have ht2' := t2.isLt; have hmi := hm idx2; rw [hsum_eq]; dsimp only [m, segA, segB] at ht2' hmi ⊢; omega
        exact Sigma.ext hce (hheq _ _ _ _ hce _ ht1 hm1 hm2)
      subst hidx_eq
      have ht_eq : t1.val = t2.val := by omega
      exact Sigma.ext rfl (heq_of_eq (Fin.ext ht_eq))
    · rintro ⟨⟨b, i⟩, hpin_none⟩
      let i_cyc : Fin n := if b then (M true).symm i else i
      obtain ⟨⟨c, r⟩, hcr, _⟩ := hflat_bij i_cyc
      have hL := hcyc_pos c
      let L := (cycs.get c).length
      let t_raw : ℕ := if b then 2 * r.val + 1 else 2 * r.val
      have ht_raw_lt : t_raw < 2 * L := by have := r.isLt; dsimp [t_raw]; split_ifs <;> omega
      have hcV : cVert c t_raw = (b, i) := by
        dsimp only [cVert, t_raw, i_cyc] at hcr ⊢
        cases b
        · have hfin : (⟨2 * r.val / 2 % L, Nat.mod_lt _ hL⟩ : Fin L) = r :=
            Fin.ext (by dsimp only; rw [Nat.mul_div_right r.val (by omega), Nat.mod_eq_of_lt r.isLt])
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_mod_right]
          exact Prod.ext rfl ((congrArg (cycs.get c).get hfin).trans (by simpa using hcr))
        · have hm1 : (2 * r.val + 1) % 2 = 1 := by omega
          have hfin : (⟨(2 * r.val + 1) / 2 % L, Nat.mod_lt _ hL⟩ : Fin L) = r :=
            Fin.ext (by dsimp only; rw [show (2 * r.val + 1) / 2 = r.val by omega, Nat.mod_eq_of_lt r.isLt])
          simp only [↓reduceIte, hm1, show ¬ (1 : ℕ) = 0 by decide]
          have hget : (cycs.get c).get ⟨(2 * r.val + 1) / 2 % L, Nat.mod_lt _ hL⟩ = (M true).symm i :=
            (congrArg (cycs.get c).get hfin).trans (by simpa using hcr)
          exact Prod.ext rfl (by rw [hget, Equiv.apply_symm_apply])
      let t_rot : ℕ := (t_raw + 2 * L - r0 c) % (2 * L)
      have ht_rot_lt : t_rot < 2 * L := Nat.mod_lt _ (by omega)
      have hrot_eq : (r0 c + t_rot) % (2 * L) = t_raw := by
        dsimp [t_rot]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show r0 c + (t_raw + 2 * L - r0 c) = t_raw + 2 * L by have := hr0_lt c; omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt ht_raw_lt]
      obtain ⟨k, hk, _⟩ := hraw_cov c t_rot ht_rot_lt
      obtain ⟨idx, hidx, _⟩ := hgetIdx_bij ⟨c, k⟩
      have hA : segA idx = ((raw c).get k).1 := by dsimp [segA]; rw [hidx]
      have hB : segB idx = ((raw c).get k).2 := by dsimp [segB]; rw [hidx]
      have hgt : segA idx < t_rot := by
        by_contra hle
        have heqA : t_rot = segA idx := by omega
        have hok := hraw_ok c _ (List.get_mem _ k)
        have hp := hok.2.2.1
        rw [← hA, ← heqA, hrot_eq, hcV, hpin_none] at hp
        simp at hp
      let t : Fin (m idx - 1) := ⟨t_rot - segA idx - 1, by dsimp [m]; omega⟩
      refine ⟨⟨idx, t⟩, Subtype.ext ?_⟩
      dsimp only [verts, t]
      have h1 : (getIdx idx).1 = c := congrArg Sigma.fst hidx
      have ht1 : r0 (getIdx idx).1 + segA idx + (t_rot - segA idx - 1 + 1) = r0 (getIdx idx).1 + t_rot := by omega
      rw [ht1]
      revert h1; generalize (getIdx idx).1 = c1; intro h1; subst c1
      change cVert c ((r0 c + t_rot) % (2 * L)) = (b, i)
      rw [hrot_eq]; exact hcV
  let eEdge := Equiv.ofBijective _ heEdge_bij
  let eVert := Equiv.ofBijective _ heVert_bij
  let rCnt (idx : Fin K) : ℕ := (Finset.univ.filter (fun j : Fin (m idx) => ecols idx j = false)).card
  let bCnt (idx : Fin K) : ℕ := (Finset.univ.filter (fun j : Fin (m idx) => ecols idx j = true)).card
  let segs : List (ℕ × ℕ × Bool) := (List.finRange K).map fun idx => (rCnt idx, bCnt idx, xor (c0 idx) (c1 idx))
  refine ⟨segs, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    have hh := hist_eq_convList (fun h i => M h i) pin K m hm verts ecols eidx c0 c1 hpin0 hpin1 hedge
      eVert (fun _ => rfl) eEdge (fun _ => rfl) d
    rw [hh]
    simp [segs, List.map_map, Function.comp_def, rCnt, bCnt]
  · intro s hs
    simp only [segs, List.mem_map, List.mem_finRange, true_and] at hs
    obtain ⟨idx, rfl⟩ := hs
    let c := (getIdx idx).1
    let s0 : Bool := decide ((r0 c + segA idx) % 2 = 0)
    have hce_fst : ∀ c t, (cEdge c t).1 = if t % 2 = 0 then true else false := by
      intro c t; dsimp only [cEdge]; split_ifs <;> rfl
    have hec : ∀ j : Fin (m idx), ecols idx j = if j.val % 2 = 0 then s0 else !s0 := by
      intro j
      have hmod : (r0 c + segA idx + j.val) % (2 * (cycs.get c).length) % 2 = (r0 c + segA idx + j.val) % 2 :=
        Nat.mod_mod_of_dvd _ (dvd_mul_right 2 _)
      dsimp only [ecols, s0]
      rw [hce_fst, hmod]
      rcases Nat.mod_two_eq_zero_or_one (r0 c + segA idx) with h0 | h1
      · rcases Nat.mod_two_eq_zero_or_one j.val with j0 | j1
        · simp [Nat.add_mod, h0, j0]
        · simp [Nat.add_mod, h0, j1]
      · rcases Nat.mod_two_eq_zero_or_one j.val with j0 | j1
        · simp [Nat.add_mod, h1, j0]
        · simp [Nat.add_mod, h1, j1]
    obtain ⟨hac_sum, hac_case⟩ := alt_counts (m idx) (hm idx) s0
    dsimp only at hac_sum hac_case
    have hr_eq : rCnt idx = (Finset.univ.filter (fun j : Fin (m idx) => (if j.val % 2 = 0 then s0 else !s0) = false)).card := by
      dsimp [rCnt]; congr 1; ext j; simp [hec j]
    have hb_eq : bCnt idx = (Finset.univ.filter (fun j : Fin (m idx) => (if j.val % 2 = 0 then s0 else !s0) = true)).card := by
      dsimp [bCnt]; congr 1; ext j; simp [hec j]
    rw [hr_eq, hb_eq]
    have h1 := hm idx
    rcases Nat.mod_two_eq_zero_or_one (m idx) with h0 | h2
    · simp only [h0, ↓reduceIte] at hac_case
      rcases hac_case with ⟨hL, hR⟩
      rw [hL, hR]; left; exact ⟨rfl, by omega⟩
    · simp only [h2, show ¬ (1 : ℕ) = 0 by decide, ↓reduceIte] at hac_case
      by_cases hs0 : s0 = false
      · rw [hs0] at hac_case ⊢
        simp only [↓reduceIte] at hac_case
        rcases hac_case with ⟨hL, hR⟩
        rw [hL, hR]; right; left; dsimp only
      · have hs0' : s0 = true := Bool.eq_true_of_not_eq_false hs0
        rw [hs0'] at hac_case ⊢
        simp only [Bool.true_eq_false, ↓reduceIte] at hac_case
        rcases hac_case with ⟨hL, hR⟩
        rw [hL, hR]; right; right; dsimp only
  ·
    have hsum : (segs.map (·.1)).sum = ∑ idx : Fin K, rCnt idx := by
      simp [segs, List.map_map, Function.comp_def, Fin.sum_univ_def]
    rw [hsum]
    have hcard : (∑ idx : Fin K, rCnt idx) = (Finset.univ.filter (fun p : Bool × Fin n => p.1 = false)).card := by
      dsimp [rCnt]
      rw [← Finset.card_sigma]
      apply Finset.card_nbij (fun p => eEdge p)
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp ⊢
        exact hp
      · intro p1 _ p2 _ heq; exact eEdge.injective heq
      · intro ⟨h, i⟩ hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        refine ⟨eEdge.symm (h, i), ?_, Equiv.apply_symm_apply eEdge (h, i)⟩
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
        have := Equiv.apply_symm_apply eEdge (h, i)
        have h1 : (eEdge (eEdge.symm (h, i))).1 = h := congrArg Prod.fst this
        exact h1.trans hp
    rw [hcard]
    have : (Finset.univ.filter (fun p : Bool × Fin n => p.1 = false)).card = Fintype.card (Fin n) := by
      apply Finset.card_nbij (fun p => p.2)
      · intro _ _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
      · intro p1 h1 p2 h2 heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact Prod.ext (h1.trans h2.symm) heq
      · intro i _; exact ⟨(false, i), by simp, rfl⟩
    rw [this, Fintype.card_fin]
  ·
    have hsum : (segs.map (·.2.1)).sum = ∑ idx : Fin K, bCnt idx := by
      simp [segs, List.map_map, Function.comp_def, Fin.sum_univ_def]
    rw [hsum]
    have hcard : (∑ idx : Fin K, bCnt idx) = (Finset.univ.filter (fun p : Bool × Fin n => p.1 = true)).card := by
      dsimp [bCnt]
      rw [← Finset.card_sigma]
      apply Finset.card_nbij (fun p => eEdge p)
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp ⊢
        exact hp
      · intro p1 _ p2 _ heq; exact eEdge.injective heq
      · intro ⟨h, i⟩ hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        refine ⟨eEdge.symm (h, i), ?_, Equiv.apply_symm_apply eEdge (h, i)⟩
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
        have := Equiv.apply_symm_apply eEdge (h, i)
        have h1 : (eEdge (eEdge.symm (h, i))).1 = h := congrArg Prod.fst this
        exact h1.trans hp
    rw [hcard]
    have : (Finset.univ.filter (fun p : Bool × Fin n => p.1 = true)).card = Fintype.card (Fin n) := by
      apply Finset.card_nbij (fun p => p.2)
      · intro _ _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
      · intro p1 h1 p2 h2 heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact Prod.ext (h1.trans h2.symm) heq
      · intro i _; exact ⟨(true, i), by simp, rfl⟩
    rw [this, Fintype.card_fin]
  ·
    have hmap : segs.map (·.2.2) =
        (List.finRange cycs.length).flatMap (fun c =>
          (raw c).map (fun s => xor ((pin (cVert c ((r0 c + s.1) % (2 * (cycs.get c).length)))).getD false)
            ((pin (cVert c ((r0 c + s.2) % (2 * (cycs.get c).length)))).getD false))) := by
      have h1 : (List.finRange K).map (fun idx => xor (c0 idx) (c1 idx)) =
          allIdx.map (fun p => xor ((pin (cVert p.1 ((r0 p.1 + ((raw p.1).get p.2).1) % (2 * (cycs.get p.1).length)))).getD false)
            ((pin (cVert p.1 ((r0 p.1 + ((raw p.1).get p.2).2) % (2 * (cycs.get p.1).length)))).getD false)) := by
        apply List.ext_getElem
        · simp [K]
        · intro i h1 h2
          simp only [List.getElem_map, List.getElem_finRange]
          have h2' : i < K := by simpa [K] using h2
          let idx : Fin K := ⟨i, h2'⟩
          have hok := hraw_ok (getIdx idx).1 _ (List.get_mem _ (getIdx idx).2)
          have hlt := hok.1
          have hlast : r0 (getIdx idx).1 + segA idx + m idx = r0 (getIdx idx).1 + segB idx := by
            dsimp only [m, segA, segB] at hlt ⊢; omega
          change xor ((pin (verts idx 0)).getD false) ((pin (verts idx (Fin.last (m idx)))).getD false) = _
          dsimp only [verts, Fin.last, Fin.val_zero]
          rw [Nat.add_zero, hlast]
          rfl
      have hcomp : segs.map (·.2.2) = (List.finRange K).map (fun idx => xor (c0 idx) (c1 idx)) := by
        dsimp only [segs]; rw [List.map_map]; rfl
      rw [hcomp, h1]
      dsimp only [allIdx]
      rw [List.map_flatMap]
      congr 1; funext c
      rw [List.map_map]
      apply List.ext_getElem
      · simp
      · intro i h1 h2; simp
    rw [hmap]
    have hflat_xor : ∀ (L : List (Fin cycs.length)),
        (L.flatMap (fun c =>
          (raw c).map (fun s => xor ((pin (cVert c ((r0 c + s.1) % (2 * (cycs.get c).length)))).getD false)
            ((pin (cVert c ((r0 c + s.2) % (2 * (cycs.get c).length)))).getD false)))).foldl xor false = false := by
      intro L
      induction L with
      | nil => rfl
      | cons c tl ih =>
        rw [List.flatMap_cons, foldl_xor_append, ih]
        have hc := hraw_xor c (fun t => (pin (cVert c ((r0 c + t) % (2 * (cycs.get c).length)))).getD false)
        rw [hc, Nat.add_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (hr0_lt c)]
        simp
    exact hflat_xor (List.finRange cycs.length)

lemma foldl_xor_perm {l1 l2 : List Bool} (h : l1.Perm l2) (a : Bool) :
    l1.foldl xor a = l2.foldl xor a := by
  induction h generalizing a with
  | nil => rfl
  | cons x _ ih => simp only [List.foldl_cons]; exact ih (xor a x)
  | swap x y l =>
    simp only [List.foldl_cons]
    have : xor (xor a y) x = xor (xor a x) y := by cases a <;> cases x <;> cases y <;> decide
    rw [this]
  | trans _ _ ih1 ih2 => exact (ih1 a).trans (ih2 a)

lemma interleave_spec : ∀ (xs ys : List (ℕ × ℕ × Bool)), xs.length = ys.length →
    (∀ s ∈ xs, s.2.1 = s.1 + 1) → (∀ s ∈ ys, s.1 = s.2.1 + 1) →
    let zs := interleave xs ys
    zs.length = 2 * xs.length ∧
    ∀ i (hi : i < zs.length),
      (((zs.take i).map (fun u => u.1 + u.2.1)).sum % 2 = i % 2) ∧
      (if i % 2 = 0 then zs[i].2.1 = zs[i].1 + 1 else zs[i].1 = zs[i].2.1 + 1)
  | [], [], _, _, _ => ⟨rfl, fun i hi => by simp [interleave] at hi⟩
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, hxs, hys => by
    have hlen' : xs.length = ys.length := by simpa using hlen
    have hx : x.2.1 = x.1 + 1 := hxs x List.mem_cons_self
    have hy : y.1 = y.2.1 + 1 := hys y List.mem_cons_self
    obtain ⟨ih_len, ih_spec⟩ := interleave_spec xs ys hlen'
      (fun s hs => hxs s (List.mem_cons_of_mem _ hs))
      (fun s hs => hys s (List.mem_cons_of_mem _ hs))
    refine ⟨by simp [interleave, ih_len]; omega, ?_⟩
    intro i hi
    match i with
    | 0 => simp [interleave, hx]
    | 1 =>
      simp only [interleave, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero, List.getElem_cons_succ, List.getElem_cons_zero]
      exact ⟨by omega, by simp [hy]⟩
    | j + 2 =>
      have hj : j < (interleave xs ys).length := by simp [interleave] at hi; omega
      obtain ⟨hsum, hpar⟩ := ih_spec j hj
      simp only [interleave, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.getElem_cons_succ]
      constructor
      · omega
      · have hmod : (j + 2) % 2 = j % 2 := by omega
        simpa [hmod] using hpar

lemma segs_partition_perm (segs : List (ℕ × ℕ × Bool))
    (hvalid : ∀ s ∈ segs, (s.1 = s.2.1 ∧ 0 < s.1) ∨ s.1 = s.2.1 + 1 ∨ s.2.1 = s.1 + 1) :
    let evens := segs.filter (fun s => decide (s.1 = s.2.1))
    let blueOdds := segs.filter (fun s => decide (s.2.1 = s.1 + 1))
    let redOdds := segs.filter (fun s => decide (s.1 = s.2.1 + 1))
    segs.Perm (evens ++ blueOdds ++ redOdds) ∧
    (segs.map (·.1)).sum + blueOdds.length = (segs.map (·.2.1)).sum + redOdds.length := by
  induction segs with
  | nil => simp
  | cons s tl ih =>
    have hs := hvalid s List.mem_cons_self
    obtain ⟨hp, hsum⟩ := ih (fun u hu => hvalid u (List.mem_cons_of_mem _ hu))
    dsimp only at hp hsum ⊢
    rcases hs with ⟨heq, _⟩ | hred | hblue
    · have h1 : decide (s.1 = s.2.1) = true := decide_eq_true heq
      have h2 : decide (s.2.1 = s.1 + 1) = false := decide_eq_false (by omega)
      have h3 : decide (s.1 = s.2.1 + 1) = false := decide_eq_false (by omega)
      simp only [List.filter_cons, h1, h2, h3, Bool.false_eq_true, ↓reduceIte, List.cons_append,
        List.map_cons, List.sum_cons]
      exact ⟨hp.cons s, by omega⟩
    · have h1 : decide (s.1 = s.2.1) = false := decide_eq_false (by omega)
      have h2 : decide (s.2.1 = s.1 + 1) = false := decide_eq_false (by omega)
      have h3 : decide (s.1 = s.2.1 + 1) = true := decide_eq_true hred
      simp only [List.filter_cons, h1, h2, h3, Bool.false_eq_true, ↓reduceIte, List.length_cons,
        List.map_cons, List.sum_cons]
      refine ⟨(hp.cons s).trans ?_, by omega⟩
      exact List.perm_middle.symm
    · have h1 : decide (s.1 = s.2.1) = false := decide_eq_false (by omega)
      have h2 : decide (s.2.1 = s.1 + 1) = true := decide_eq_true hblue
      have h3 : decide (s.1 = s.2.1 + 1) = false := decide_eq_false (by omega)
      simp only [List.filter_cons, h1, h2, h3, Bool.false_eq_true, ↓reduceIte, List.length_cons,
        List.map_cons, List.sum_cons]
      refine ⟨(hp.cons s).trans ?_, by omega⟩
      rw [List.append_assoc, List.append_assoc, List.cons_append]
      exact (List.perm_middle (l₁ := tl.filter (fun s => decide (s.1 = s.2.1)))
        (a := s) (l₂ := tl.filter (fun s => decide (s.2.1 = s.1 + 1)) ++ tl.filter (fun s => decide (s.1 = s.2.1 + 1)))).symm

lemma layout_ring {n : ℕ} [NeZero n] (segs : List (ℕ × ℕ × Bool))
    (hvalid : ∀ s ∈ segs, (s.1 = s.2.1 ∧ 0 < s.1) ∨ s.1 = s.2.1 + 1 ∨ s.2.1 = s.1 + 1)
    (hsumR : (segs.map (·.1)).sum = n)
    (hsumB : (segs.map (·.2.1)).sum = n)
    (hxor : (segs.map (·.2.2)).foldl xor false = false) :
    ∃ pin : Bool × Fin n → Option Bool,
      ∀ d : Fin (n + 1) × Fin (n + 1),
        histDef (ringDef n) pin d =
        convList (segs.map fun s => segHist s.1 s.2.1 s.2.2) (d.1.val, d.2.val) := by
  classical
  have hn : 0 < n := NeZero.pos n
  let evens := segs.filter (fun s => decide (s.1 = s.2.1))
  let blueOdds := segs.filter (fun s => decide (s.2.1 = s.1 + 1))
  let redOdds := segs.filter (fun s => decide (s.1 = s.2.1 + 1))
  obtain ⟨hpart_perm, hpart_sum⟩ := segs_partition_perm segs hvalid
  have hbr_len : blueOdds.length = redOdds.length := by dsimp only [blueOdds, redOdds]; omega
  let odds := interleave blueOdds redOdds
  let ordered := evens ++ odds
  have hord_perm : ordered.Perm segs := by
    have h1 : ordered.Perm (evens ++ (blueOdds ++ redOdds)) :=
      List.Perm.append_left evens (interleave_perm blueOdds redOdds)
    rw [← List.append_assoc] at h1
    exact h1.trans hpart_perm.symm
  have hord_valid : ∀ s ∈ ordered, (s.1 = s.2.1 ∧ 0 < s.1) ∨ s.1 = s.2.1 + 1 ∨ s.2.1 = s.1 + 1 :=
    fun s hs => hvalid s (hord_perm.subset hs)
  have hord_sumR : (ordered.map (·.1)).sum = n := by
    rw [(hord_perm.map (·.1)).sum_eq, hsumR]
  have hord_sumB : (ordered.map (·.2.1)).sum = n := by
    rw [(hord_perm.map (·.2.1)).sum_eq, hsumB]
  have hord_sum2 : (ordered.map (fun s => s.1 + s.2.1)).sum = 2 * n := by
    have hadd : ∀ l : List (ℕ × ℕ × Bool), (l.map (fun s => s.1 + s.2.1)).sum =
        (l.map (·.1)).sum + (l.map (·.2.1)).sum := by
      intro l; induction l with
      | nil => rfl
      | cons s tl ih => simp [ih]; omega
    rw [hadd, hord_sumR, hord_sumB]; omega
  have hord_xor : (ordered.map (·.2.2)).foldl xor false = false := by
    rw [foldl_xor_perm (hord_perm.map (·.2.2)) false, hxor]
  let K := ordered.length
  have hKpos : 0 < K := by
    by_contra h0
    have hemp : ordered = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hemp] at hord_sum2; simp at hord_sum2; omega
  let m (idx : Fin K) : ℕ := (ordered.get idx).1 + (ordered.get idx).2.1
  have hm : ∀ idx : Fin K, 1 ≤ m idx := by
    intro idx
    have hv := hord_valid _ (List.get_mem _ idx)
    dsimp only [m]; omega
  let startPos (i : ℕ) : ℕ := ((ordered.take i).map (fun s => s.1 + s.2.1)).sum
  let startCol (i : ℕ) : Bool := ((ordered.take i).map (·.2.2)).foldl xor false
  have hstartPos_zero : startPos 0 = 0 := rfl
  have hstartPos_K : startPos K = 2 * n := by
    dsimp only [startPos, K]; rw [List.take_length]; exact hord_sum2
  have hstartCol_zero : startCol 0 = false := rfl
  have hstartCol_K : startCol K = false := by
    dsimp only [startCol, K]; rw [List.take_length]; exact hord_xor
  have htake_succ : ∀ idx : Fin K, ordered.take (idx.val + 1) = ordered.take idx.val ++ [ordered.get idx] := by
    intro idx; exact List.take_add_one (l := ordered) (i := idx.val) ▸ by
      simp [List.getElem?_eq_getElem idx.isLt]
  have hstartPos_step : ∀ idx : Fin K, startPos (idx.val + 1) = startPos idx.val + m idx := by
    intro idx
    dsimp only [startPos, m]
    rw [htake_succ idx, List.map_append, List.sum_append]
    simp
  have hstartCol_step : ∀ idx : Fin K, startCol (idx.val + 1) = xor (startCol idx.val) (ordered.get idx).2.2 := by
    intro idx
    dsimp only [startCol]
    rw [htake_succ idx, List.map_append, foldl_xor_append]
    simp only [List.map_singleton, List.foldl_cons, List.foldl_nil, Bool.false_xor]
  have hstartPos_mono : ∀ i j, i < j → j ≤ K → startPos i < startPos j := by
    intro i j hij hjK
    induction j with
    | zero => omega
    | succ j ih =>
      have hj : j < K := by omega
      have hstep := hstartPos_step ⟨j, hj⟩
      dsimp only at hstep
      have hm_j := hm ⟨j, hj⟩
      by_cases heq : i = j
      · subst heq; omega
      · have := ih (by omega) (by omega); omega
  have hstartPos_le : ∀ i j, i ≤ j → j ≤ K → startPos i ≤ startPos j := by
    intro i j hij hjK
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact (hstartPos_mono i j hlt hjK).le
  have hstartPos_lt : ∀ idx : Fin K, startPos idx.val < 2 * n := by
    intro idx; rw [← hstartPos_K]; exact hstartPos_mono idx.val K idx.isLt le_rfl

  have hevens_even : ∀ i ≤ evens.length, ((evens.take i).map (fun s => s.1 + s.2.1)).sum % 2 = 0 := by
    intro i _
    have hall : ∀ l : List (ℕ × ℕ × Bool), (∀ s ∈ l, s.1 = s.2.1) →
        (l.map (fun s => s.1 + s.2.1)).sum % 2 = 0 := by
      intro l hl
      induction l with
      | nil => rfl
      | cons s tl ih =>
        have hs := hl s List.mem_cons_self
        have htl := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))
        simp only [List.map_cons, List.sum_cons]; omega
    apply hall
    intro s hs
    have hmem := List.mem_of_mem_take hs
    have hf := (List.mem_filter.mp hmem).2
    exact of_decide_eq_true hf
  obtain ⟨hodds_len, hodds_spec⟩ := interleave_spec blueOdds redOdds hbr_len
    (fun s hs => of_decide_eq_true (List.mem_filter.mp hs).2)
    (fun s hs => of_decide_eq_true (List.mem_filter.mp hs).2)

  let rVert (t : ℕ) : Bool × Fin n :=
    if t % 2 = 0 then (false, ⟨(t / 2) % n, Nat.mod_lt _ hn⟩)
    else (true, ⟨(t / 2 + 1) % n, Nat.mod_lt _ hn⟩)
  let rEdge (t : ℕ) : Bool × Fin n :=
    if t % 2 = 0 then (true, ⟨(t / 2) % n, Nat.mod_lt _ hn⟩)
    else (false, ⟨(t / 2 + 1) % n, Nat.mod_lt _ hn⟩)
  have hrVert_mod : ∀ t, rVert (t % (2 * n)) = rVert t := by
    intro t
    dsimp only [rVert]
    have h1 : t % (2 * n) % 2 = t % 2 := Nat.mod_mod_of_dvd t (dvd_mul_right 2 n)
    have h2 : t % (2 * n) / 2 = (t / 2) % n := mod_two_mul_div t n hn
    have hfin1 : (⟨t % (2 * n) / 2 % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨t / 2 % n, Nat.mod_lt _ hn⟩ :=
      Fin.ext (by dsimp only; rw [h2, Nat.mod_mod])
    have hfin2 : (⟨(t % (2 * n) / 2 + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨(t / 2 + 1) % n, Nat.mod_lt _ hn⟩ :=
      Fin.ext (by dsimp only; rw [h2, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod])
    rw [h1, hfin1, hfin2]
  have hrEdge_adj : ∀ t,
      let e := rEdge t
      (rVert t = (false, e.2) ∧ rVert (t + 1) = (true, ringDef n e.1 e.2)) ∨
      (rVert t = (true, ringDef n e.1 e.2) ∧ rVert (t + 1) = (false, e.2)) := by
    intro t
    dsimp only [rVert, rEdge, ringDef]
    rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
    · left
      have h1' : (t + 1) % 2 = 1 := by omega
      have hd : (t + 1) / 2 = t / 2 := by omega
      simp only [h0, ↓reduceIte, h1', show ¬ (1 : ℕ) = 0 by decide]
      refine ⟨trivial, ?_⟩
      congr 1; apply Fin.ext; rw [Fin.val_add, Fin.val_one']; dsimp only
      rw [hd]
      by_cases hn1 : n = 1
      · subst hn1; omega
      · rw [Nat.mod_eq_of_lt (show 1 < n by omega)]; simp [Nat.add_mod]
    · right
      have h0' : (t + 1) % 2 = 0 := by omega
      have hd : (t + 1) / 2 = t / 2 + 1 := by omega
      simp only [h1, show ¬ (1 : ℕ) = 0 by decide, h0', ↓reduceIte, Bool.false_eq_true]
      refine ⟨trivial, ?_⟩
      congr 1; apply Fin.ext; dsimp only; rw [hd]
  have hrVert_bij : Function.Bijective (fun t : Fin (2 * n) => rVert t.val) := by
    constructor
    · intro t1 t2 heq
      dsimp only [rVert] at heq
      rcases Nat.mod_two_eq_zero_or_one t1.val with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one t2.val with h2 | h2
      · simp only [h1, h2, ↓reduceIte] at heq
        have hv : t1.val / 2 % n = t2.val / 2 % n := congrArg (fun p => p.2.val) heq
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
        exact Fin.ext (by omega)
      · simp only [h1, h2, ↓reduceIte, show ¬ (1 : ℕ) = 0 by decide] at heq; simp at heq
      · simp only [h1, h2, ↓reduceIte, show ¬ (1 : ℕ) = 0 by decide] at heq; simp at heq
      · simp only [h1, h2, ↓reduceIte, show ¬ (1 : ℕ) = 0 by decide] at heq
        have hv : (t1.val / 2 + 1) % n = (t2.val / 2 + 1) % n := congrArg (fun p => p.2.val) heq
        have hlt1 : t1.val / 2 < n := by omega
        have hlt2 : t2.val / 2 < n := by omega
        have heq_div : t1.val / 2 = t2.val / 2 := by
          by_cases h1n : t1.val / 2 + 1 < n <;> by_cases h2n : t2.val / 2 + 1 < n
          · rw [Nat.mod_eq_of_lt h1n, Nat.mod_eq_of_lt h2n] at hv; omega
          · have h2eq : t2.val / 2 + 1 = n := by omega
            rw [Nat.mod_eq_of_lt h1n, h2eq, Nat.mod_self] at hv; omega
          · have h1eq : t1.val / 2 + 1 = n := by omega
            rw [h1eq, Nat.mod_self, Nat.mod_eq_of_lt h2n] at hv; omega
          · omega
        exact Fin.ext (by omega)
    · rintro ⟨b, i⟩
      cases b
      · refine ⟨⟨2 * i.val, by omega⟩, ?_⟩
        dsimp only [rVert]
        simp only [Nat.mul_mod_right, ↓reduceIte]
        congr 1; apply Fin.ext; dsimp only
        rw [Nat.mul_div_right i.val (by omega), Nat.mod_eq_of_lt i.isLt]
      · let j := (i.val + n - 1) % n
        have hj : j < n := Nat.mod_lt _ hn
        refine ⟨⟨2 * j + 1, by omega⟩, ?_⟩
        dsimp only [rVert]
        have hm1 : (2 * j + 1) % 2 = 1 := by omega
        have hd1 : (2 * j + 1) / 2 = j := by omega
        simp only [hm1, show ¬ (1 : ℕ) = 0 by decide, ↓reduceIte]
        congr 1; apply Fin.ext; dsimp only
        rw [hd1]; dsimp only [j]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show i.val + n - 1 + 1 = i.val + n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  have hrEdge_bij : Function.Bijective (fun t : Fin (2 * n) => rEdge t.val) := by
    constructor
    · intro t1 t2 heq
      dsimp only [rEdge] at heq
      rcases Nat.mod_two_eq_zero_or_one t1.val with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one t2.val with h2 | h2
      · simp only [h1, h2, ↓reduceIte] at heq
        have hv : t1.val / 2 % n = t2.val / 2 % n := congrArg (fun p => p.2.val) heq
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
        exact Fin.ext (by omega)
      · simp only [h1, h2, ↓reduceIte, show ¬ (1 : ℕ) = 0 by decide] at heq; simp at heq
      · simp only [h1, h2, ↓reduceIte, show ¬ (1 : ℕ) = 0 by decide] at heq; simp at heq
      · simp only [h1, h2, ↓reduceIte, show ¬ (1 : ℕ) = 0 by decide] at heq
        have hv : (t1.val / 2 + 1) % n = (t2.val / 2 + 1) % n := congrArg (fun p => p.2.val) heq
        have hlt1 : t1.val / 2 < n := by omega
        have hlt2 : t2.val / 2 < n := by omega
        have heq_div : t1.val / 2 = t2.val / 2 := by
          by_cases h1n : t1.val / 2 + 1 < n <;> by_cases h2n : t2.val / 2 + 1 < n
          · rw [Nat.mod_eq_of_lt h1n, Nat.mod_eq_of_lt h2n] at hv; omega
          · have h2eq : t2.val / 2 + 1 = n := by omega
            rw [Nat.mod_eq_of_lt h1n, h2eq, Nat.mod_self] at hv; omega
          · have h1eq : t1.val / 2 + 1 = n := by omega
            rw [h1eq, Nat.mod_self, Nat.mod_eq_of_lt h2n] at hv; omega
          · omega
        exact Fin.ext (by omega)
    · rintro ⟨b, i⟩
      cases b
      · let j := (i.val + n - 1) % n
        have hj : j < n := Nat.mod_lt _ hn
        refine ⟨⟨2 * j + 1, by omega⟩, ?_⟩
        dsimp only [rEdge]
        have hm1 : (2 * j + 1) % 2 = 1 := by omega
        have hd1 : (2 * j + 1) / 2 = j := by omega
        simp only [hm1, show ¬ (1 : ℕ) = 0 by decide, ↓reduceIte]
        congr 1; apply Fin.ext; dsimp only
        rw [hd1]; dsimp only [j]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show i.val + n - 1 + 1 = i.val + n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      · refine ⟨⟨2 * i.val, by omega⟩, ?_⟩
        dsimp only [rEdge]
        simp only [Nat.mul_mod_right, ↓reduceIte]
        congr 1; apply Fin.ext; dsimp only
        rw [Nat.mul_div_right i.val (by omega), Nat.mod_eq_of_lt i.isLt]
  let rVertEquiv : Fin (2 * n) ≃ Bool × Fin n := Equiv.ofBijective _ hrVert_bij
  let rEdgeEquiv : Fin (2 * n) ≃ Bool × Fin n := Equiv.ofBijective _ hrEdge_bij

  have hseg_cov : ∀ t < 2 * n, ∃! idx : Fin K, startPos idx.val ≤ t ∧ t < startPos (idx.val + 1) := by
    intro t ht
    have hex : ∃ idx : Fin K, startPos idx.val ≤ t ∧ t < startPos (idx.val + 1) := by
      have haux : ∀ j ≤ K, t < startPos j → ∃ i < j, startPos i ≤ t ∧ t < startPos (i + 1) := by
        intro j
        induction j with
        | zero => intro _ hlt; rw [hstartPos_zero] at hlt; omega
        | succ j ih =>
          intro hj hlt
          by_cases hle : startPos j ≤ t
          · exact ⟨j, Nat.lt_succ_self j, hle, hlt⟩
          · obtain ⟨i, hij, hi1, hi2⟩ := ih (by omega) (by omega)
            exact ⟨i, by omega, hi1, hi2⟩
      obtain ⟨i, hiK, hi1, hi2⟩ := haux K le_rfl (by rw [hstartPos_K]; exact ht)
      exact ⟨⟨i, hiK⟩, hi1, hi2⟩
    obtain ⟨idx, h1, h2⟩ := hex
    refine ⟨idx, ⟨h1, h2⟩, ?_⟩
    intro idx' ⟨h1', h2'⟩
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have := hstartPos_le (idx'.val + 1) idx.val (by omega) idx.isLt.le; omega
    · have := hstartPos_le (idx.val + 1) idx'.val (by omega) idx'.isLt.le; omega

  let pinAt (t : ℕ) : Option Bool :=
    ((List.finRange K).find? (fun idx => decide (startPos idx.val = t))).map (fun idx => startCol idx.val)
  let pin (u : Bool × Fin n) : Option Bool := pinAt (rVertEquiv.symm u).val
  have hpinAt_some : ∀ idx : Fin K, pinAt (startPos idx.val) = some (startCol idx.val) := by
    intro idx
    dsimp only [pinAt]
    have hfind : (List.finRange K).find? (fun j => decide (startPos j.val = startPos idx.val)) = some idx := by
      rcases h : (List.finRange K).find? (fun j => decide (startPos j.val = startPos idx.val)) with _ | j
      · exfalso
        have hnone := List.find?_eq_none.mp h idx (List.mem_finRange idx)
        simp at hnone
      · have hj : startPos j.val = startPos idx.val := by simpa using List.find?_some h
        have hjeq : j = idx := by
          by_contra hne
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
          · have := hstartPos_mono j.val idx.val hlt idx.isLt.le; omega
          · have := hstartPos_mono idx.val j.val hlt j.isLt.le; omega
        rw [h, hjeq]
    rw [hfind]; rfl
  have hpinAt_none : ∀ t, (∀ idx : Fin K, startPos idx.val ≠ t) → pinAt t = none := by
    intro t ht
    dsimp only [pinAt]
    have hfind : (List.finRange K).find? (fun j => decide (startPos j.val = t)) = none := by
      rw [List.find?_eq_none]
      intro j _; simp [ht j]
    rw [hfind]; rfl
  have hpin_rVert : ∀ t (ht : t < 2 * n), pin (rVert t) = pinAt t := by
    intro t ht
    dsimp only [pin]
    have hsym : rVertEquiv.symm (rVert t) = ⟨t, ht⟩ := rVertEquiv.symm_apply_apply ⟨t, ht⟩
    rw [hsym]

  let verts (idx : Fin K) (j : Fin (m idx + 1)) : Bool × Fin n := rVert (startPos idx.val + j.val)
  let ecols (idx : Fin K) (j : Fin (m idx)) : Bool := (rEdge (startPos idx.val + j.val)).1
  let eidx (idx : Fin K) (j : Fin (m idx)) : Fin n := (rEdge (startPos idx.val + j.val)).2
  let c0 (idx : Fin K) : Bool := startCol idx.val
  let c1 (idx : Fin K) : Bool := startCol (idx.val + 1)
  have hpin0 : ∀ idx : Fin K, pin (verts idx 0) = some (c0 idx) := by
    intro idx
    dsimp only [verts, Fin.val_zero, Nat.add_zero, c0]
    rw [hpin_rVert _ (hstartPos_lt idx), hpinAt_some idx]
  have hpin1 : ∀ idx : Fin K, pin (verts idx (Fin.last (m idx))) = some (c1 idx) := by
    intro idx
    dsimp only [verts, Fin.last, c1]
    rw [← hstartPos_step idx]
    by_cases hlt : idx.val + 1 < K
    · let idx' : Fin K := ⟨idx.val + 1, hlt⟩
      rw [hpin_rVert _ (hstartPos_lt idx')]
      exact hpinAt_some idx'
    · have heqK : idx.val + 1 = K := by omega
      rw [heqK, hstartPos_K, hstartCol_K, ← hrVert_mod (2 * n), Nat.mod_self,
          hpin_rVert 0 (by omega)]
      have h0 := hpinAt_some ⟨0, hKpos⟩
      simpa [hstartPos_zero, hstartCol_zero] using h0
  have hedge : ∀ idx (j : Fin (m idx)),
      (verts idx j.castSucc = (false, eidx idx j) ∧ verts idx j.succ = (true, ringDef n (ecols idx j) (eidx idx j))) ∨
      (verts idx j.castSucc = (true, ringDef n (ecols idx j) (eidx idx j)) ∧ verts idx j.succ = (false, eidx idx j)) := by
    intro idx j
    have := hrEdge_adj (startPos idx.val + j.val)
    simpa [verts, ecols, eidx, Nat.add_assoc] using this
  have heEdge_bij : Function.Bijective (fun p : Σ idx : Fin K, Fin (m idx) => (ecols p.1 p.2, eidx p.1 p.2)) := by
    have hlt_2n : ∀ p : Σ idx : Fin K, Fin (m idx), startPos p.1.val + p.2.val < 2 * n := by
      rintro ⟨idx, j⟩; dsimp only
      have h1 := hstartPos_step idx
      have h2 := hstartPos_le (idx.val + 1) K (by omega) le_rfl
      rw [hstartPos_K, h1] at h2
      have hj := j.isLt; omega
    constructor
    · rintro ⟨idx1, j1⟩ ⟨idx2, j2⟩ heq
      have ht : (⟨startPos idx1.val + j1.val, hlt_2n ⟨idx1, j1⟩⟩ : Fin (2 * n)) =
          ⟨startPos idx2.val + j2.val, hlt_2n ⟨idx2, j2⟩⟩ := rEdgeEquiv.injective heq
      have hsum : startPos idx1.val + j1.val = startPos idx2.val + j2.val := congrArg Fin.val ht
      obtain ⟨_, _, huniq⟩ := hseg_cov (startPos idx1.val + j1.val) (hlt_2n ⟨idx1, j1⟩)
      have hm1 : startPos idx1.val ≤ startPos idx1.val + j1.val ∧ startPos idx1.val + j1.val < startPos (idx1.val + 1) := by
        rw [hstartPos_step idx1]; have := j1.isLt; omega
      have hm2 : startPos idx2.val ≤ startPos idx1.val + j1.val ∧ startPos idx1.val + j1.val < startPos (idx2.val + 1) := by
        rw [hsum, hstartPos_step idx2]; have := j2.isLt; omega
      have hidx : idx1 = idx2 := (huniq idx1 hm1).trans (huniq idx2 hm2).symm
      subst hidx
      exact Sigma.ext rfl (heq_of_eq (Fin.ext (Nat.add_left_cancel hsum)))
    · intro e
      let t := rEdgeEquiv.symm e
      obtain ⟨idx, ⟨h1, h2⟩, _⟩ := hseg_cov t.val t.isLt
      rw [hstartPos_step idx] at h2
      refine ⟨⟨idx, ⟨t.val - startPos idx.val, by omega⟩⟩, ?_⟩
      change rEdge (startPos idx.val + (t.val - startPos idx.val)) = e
      rw [show startPos idx.val + (t.val - startPos idx.val) = t.val by omega]
      exact rEdgeEquiv.apply_symm_apply e
  have heVert_bij : Function.Bijective (fun p : Σ idx : Fin K, Fin (m idx - 1) =>
      (⟨verts p.1 ⟨p.2.val + 1, by have := hm p.1; omega⟩, by
        have hlt : startPos p.1.val + (p.2.val + 1) < 2 * n := by
          have h1 := hstartPos_step p.1
          have h2 := hstartPos_le (p.1.val + 1) K (by omega) le_rfl
          rw [hstartPos_K] at h2
          have hj := p.2.isLt; have hmp := hm p.1; omega
        change pin (rVert (startPos p.1.val + (p.2.val + 1))) = none
        rw [hpin_rVert _ hlt]
        apply hpinAt_none
        intro idx' heq
        have hstep := hstartPos_step p.1
        have hp2 := p.2.isLt; have hmp := hm p.1
        rcases lt_trichotomy idx'.val p.1.val with hlt' | heq' | hgt'
        · have := hstartPos_mono idx'.val p.1.val hlt' p.1.isLt.le; omega
        · rw [heq'] at heq; omega
        · have := hstartPos_le (p.1.val + 1) idx'.val (by omega) idx'.isLt.le; omega⟩ : {u : Bool × Fin n // pin u = none})) := by
    have hlt_2n : ∀ p : Σ idx : Fin K, Fin (m idx - 1), startPos p.1.val + (p.2.val + 1) < 2 * n := by
      rintro ⟨idx, j⟩; dsimp only
      have h1 := hstartPos_step idx
      have h2 := hstartPos_le (idx.val + 1) K (by omega) le_rfl
      rw [hstartPos_K, h1] at h2
      have hj := j.isLt; have hmi := hm idx; omega
    constructor
    · rintro ⟨idx1, j1⟩ ⟨idx2, j2⟩ heq
      have hv : rVert (startPos idx1.val + (j1.val + 1)) = rVert (startPos idx2.val + (j2.val + 1)) :=
        congrArg Subtype.val heq
      have ht : (⟨startPos idx1.val + (j1.val + 1), hlt_2n ⟨idx1, j1⟩⟩ : Fin (2 * n)) =
          ⟨startPos idx2.val + (j2.val + 1), hlt_2n ⟨idx2, j2⟩⟩ := rVertEquiv.injective hv
      have hsum : startPos idx1.val + (j1.val + 1) = startPos idx2.val + (j2.val + 1) := congrArg Fin.val ht
      obtain ⟨_, _, huniq⟩ := hseg_cov (startPos idx1.val + (j1.val + 1)) (hlt_2n ⟨idx1, j1⟩)
      have hm1 : startPos idx1.val ≤ startPos idx1.val + (j1.val + 1) ∧ startPos idx1.val + (j1.val + 1) < startPos (idx1.val + 1) := by
        rw [hstartPos_step idx1]; have hj1 := j1.isLt; have hmi := hm idx1; omega
      have hm2 : startPos idx2.val ≤ startPos idx1.val + (j1.val + 1) ∧ startPos idx1.val + (j1.val + 1) < startPos (idx2.val + 1) := by
        rw [hsum, hstartPos_step idx2]; have hj2 := j2.isLt; have hmi := hm idx2; omega
      have hidx : idx1 = idx2 := (huniq idx1 hm1).trans (huniq idx2 hm2).symm
      subst hidx
      have hj_eq : j1.val = j2.val := by omega
      exact Sigma.ext rfl (heq_of_eq (Fin.ext hj_eq))
    · rintro ⟨u, hu⟩
      let t := rVertEquiv.symm u
      obtain ⟨idx, ⟨h1, h2⟩, _⟩ := hseg_cov t.val t.isLt
      have hgt : startPos idx.val < t.val := by
        by_contra hle
        have heq : t.val = startPos idx.val := by omega
        have hp : pin u = some (startCol idx.val) := by
          have : u = rVert t.val := (rVertEquiv.apply_symm_apply u).symm
          rw [this, hpin_rVert t.val t.isLt, heq, hpinAt_some idx]
        rw [hu] at hp; simp at hp
      rw [hstartPos_step idx] at h2
      refine ⟨⟨idx, ⟨t.val - startPos idx.val - 1, by omega⟩⟩, Subtype.ext ?_⟩
      change rVert (startPos idx.val + (t.val - startPos idx.val - 1 + 1)) = u
      rw [show startPos idx.val + (t.val - startPos idx.val - 1 + 1) = t.val by omega]
      exact rVertEquiv.apply_symm_apply u
  let eEdge := Equiv.ofBijective _ heEdge_bij
  let eVert := Equiv.ofBijective _ heVert_bij
  refine ⟨pin, fun d => ?_⟩
  have hh := hist_eq_convList (ringDef n) pin K m hm verts ecols eidx c0 c1 hpin0 hpin1 hedge
    eVert (fun _ => rfl) eEdge (fun _ => rfl) d
  rw [hh]
  have hlist_eq : (List.finRange K).map (fun idx =>
      segHist (Finset.univ.filter (fun j : Fin (m idx) => ecols idx j = false)).card
              (Finset.univ.filter (fun j : Fin (m idx) => ecols idx j = true)).card
              (xor (c0 idx) (c1 idx))) =
      ordered.map (fun s => segHist s.1 s.2.1 s.2.2) := by
    apply List.ext_getElem
    · simp [K]
    · intro i h1 h2
      have hiK : i < K := by simpa [K] using h2
      let idx : Fin K := ⟨i, hiK⟩
      let s := ordered.get idx
      have hget_fin : ∀ (p : Fin K → (ℕ × ℕ → ℕ)), ((List.finRange K).map p)[i]'(by simpa [K] using h1) = p idx := by
        intro p; simp [idx]
      rw [hget_fin, List.getElem_map]
      have hxor_i : xor (c0 idx) (c1 idx) = s.2.2 := by
        dsimp only [c0, c1]; rw [hstartCol_step idx]
        cases startCol idx.val <;> cases s.2.2 <;> decide
      let s0 : Bool := decide (startPos idx.val % 2 = 0)
      have hrE_fst : ∀ t, (rEdge t).1 = if t % 2 = 0 then true else false := by
        intro t; dsimp only [rEdge]; split_ifs <;> rfl
      have hec : ∀ j : Fin (m idx), ecols idx j = if j.val % 2 = 0 then s0 else !s0 := by
        intro j
        dsimp only [ecols, s0]
        rw [hrE_fst]
        rcases Nat.mod_two_eq_zero_or_one (startPos idx.val) with h0 | h1
        · rcases Nat.mod_two_eq_zero_or_one j.val with j0 | j1
          · simp [Nat.add_mod, h0, j0]
          · simp [Nat.add_mod, h0, j1]
        · rcases Nat.mod_two_eq_zero_or_one j.val with j0 | j1
          · simp [Nat.add_mod, h1, j0]
          · simp [Nat.add_mod, h1, j1]
      have hac := alt_counts (m idx) (hm idx) s0
      dsimp only at hac
      have hr_eq : (Finset.univ.filter (fun j : Fin (m idx) => ecols idx j = false)).card =
          (Finset.univ.filter (fun j : Fin (m idx) => (if j.val % 2 = 0 then s0 else !s0) = false)).card := by
        congr 1; ext j; simp [hec j]
      have hb_eq : (Finset.univ.filter (fun j : Fin (m idx) => ecols idx j = true)).card =
          (Finset.univ.filter (fun j : Fin (m idx) => (if j.val % 2 = 0 then s0 else !s0) = true)).card := by
        congr 1; ext j; simp [hec j]
      have hgoal : segHist (Finset.univ.filter (fun j : Fin (m idx) => ecols idx j = false)).card
                     (Finset.univ.filter (fun j : Fin (m idx) => ecols idx j = true)).card
                     (xor (c0 idx) (c1 idx)) = segHist s.1 s.2.1 s.2.2 := by
        rw [hr_eq, hb_eq, hxor_i]
        have hm_eq : m idx = s.1 + s.2.1 := rfl
        rcases hac with ⟨_, hac_case⟩
        by_cases hlt_ev : i < evens.length
        · have hs_mem : s ∈ evens := by
            have : ordered[i] = evens[i] := List.getElem_append_left hlt_ev
            change ordered[i] ∈ evens; rw [this]; exact List.getElem_mem hlt_ev
          have hrb : s.1 = s.2.1 := of_decide_eq_true (List.mem_filter.mp hs_mem).2
          have hmod0 : m idx % 2 = 0 := by rw [hm_eq]; omega
          simp only [hmod0, ↓reduceIte] at hac_case
          rcases hac_case with ⟨hL, hR⟩
          rw [hL, hR, hm_eq]
          congr 1 <;> omega
        · let j := i - evens.length
          have hj : j < odds.length := by
            have : K = evens.length + odds.length := List.length_append
            omega
          obtain ⟨hsp_odds, hpar_odds⟩ := hodds_spec j hj
          change ((odds.take j).map (fun u => u.1 + u.2.1)).sum % 2 = j % 2 at hsp_odds
          have hs_eq : s = odds[j] := by
            change ordered[i] = odds[j]
            exact List.getElem_append_right (by omega)
          have hsp_mod : startPos idx.val % 2 = j % 2 := by
            dsimp only [startPos, idx]
            have htake : ordered.take i = evens ++ odds.take j := by
              dsimp only [ordered]
              rw [List.take_append, List.take_of_length_le (by omega)]
            rw [htake, List.map_append, List.sum_append]
            have hev0 := hevens_even evens.length le_rfl
            rw [List.take_length] at hev0
            omega
          rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
          · simp only [hj0, ↓reduceIte] at hpar_odds
            rw [← hs_eq] at hpar_odds
            have hm1 : m idx % 2 = 1 := by rw [hm_eq]; omega
            have hs0 : s0 = true := by dsimp only [s0]; simp [hsp_mod, hj0]
            rw [hs0] at hac_case ⊢
            simp only [hm1, show ¬ (1 : ℕ) = 0 by decide, ↓reduceIte, Bool.true_eq_false] at hac_case
            rcases hac_case with ⟨hL, hR⟩
            rw [hL, hR, hm_eq]
            congr 1 <;> omega
          · simp only [hj1, show ¬ (1 : ℕ) = 0 by decide, ↓reduceIte] at hpar_odds
            rw [← hs_eq] at hpar_odds
            have hm1 : m idx % 2 = 1 := by rw [hm_eq]; omega
            have hs0 : s0 = false := by dsimp only [s0]; simp [hsp_mod, hj1]
            rw [hs0] at hac_case ⊢
            simp only [hm1, show ¬ (1 : ℕ) = 0 by decide, ↓reduceIte] at hac_case
            rcases hac_case with ⟨hL, hR⟩
            rw [hL, hR, hm_eq]
            congr 1 <;> omega
      simpa only [s, List.get_eq_getElem] using hgoal
  rw [hlist_eq]
  exact congrFun (convList_perm (hord_perm.map _)) (d.1.val, d.2.val)

def ringPerm (n : ℕ) [NeZero n] : Bool → Equiv.Perm (Fin n)
  | false => Equiv.refl (Fin n)
  | true => Equiv.addRight (1 : Fin n)

lemma ringPerm_apply (n : ℕ) [NeZero n] (h : Bool) (i : Fin n) :
    ringPerm n h i = ringDef n h i := by
  cases h <;> rfl

lemma convList_support (ls : List ℕ) :
    ∀ a, ls.sum < a → convList (ls.map fun L => segHist L L false) (a, 0) = 0 := by
  induction ls with
  | nil =>
    intro a ha
    simp only [List.sum_nil] at ha
    change delta0 (a, 0) = 0
    unfold delta0
    simp [show a ≠ 0 by omega]
  | cons L tl ih =>
    intro a ha
    simp only [List.sum_cons] at ha
    change conv (segHist L L false) (convList (tl.map fun L => segHist L L false)) (a, 0) = 0
    rw [conv_zero_snd]
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_range] at hx
    by_cases hxL : x ≤ L
    · have hgt : tl.sum < a - x := by omega
      rw [ih (a - x) hgt, mul_zero]
    · have : segHist L L false (x, 0) = 0 := by
        unfold segHist; split_ifs <;> simp [Nat.choose_eq_zero_of_lt (show L < x by omega)]
      rw [this, zero_mul]

lemma eval_poly_convList (ls : List ℕ) (z : ℂ) :
    (∑ d ∈ Finset.range (ls.sum + 1), (convList (ls.map fun L => segHist L L false) (d, 0) : ℂ) * z ^ d) =
    (ls.map fun L => ((1 + z) ^ L + (1 - z) ^ L) / 2).prod := by
  induction ls with
  | nil => simp [convList, delta0]
  | cons L tl ih =>
    simp only [List.sum_cons, List.map_cons, List.prod_cons]
    have hcons : convList (segHist L L false :: tl.map fun L => segHist L L false) =
        conv (segHist L L false) (convList (tl.map fun L => segHist L L false)) := rfl
    rw [hcons]
    have hL : ∀ a, L < a → segHist L L false (a, 0) = 0 := by
      intro a ha; unfold segHist; split_ifs <;> simp [Nat.choose_eq_zero_of_lt ha]
    rw [eval_poly_conv _ _ L tl.sum hL (convList_support tl) z, eval_segHist_zero L z, ih]

lemma list_sum_flatMap {α : Type*} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a tl ih => simp [List.flatMap_cons, List.sum_append, ih]

lemma list_prod_flatMap {α : Type*} (l : List α) (f : α → List ℂ) :
    (l.flatMap f).prod = (l.map (fun a => (f a).prod)).prod := by
  induction l with
  | nil => rfl
  | cons a tl ih => simp [List.flatMap_cons, List.prod_append, ih]

lemma sum_j_add_two (t : ℕ) : 2 * (∑ j : Fin t, (j.val + 2)) = t * (t + 3) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    linarith

lemma foldl_xor_all_false (l : List Bool) (h : ∀ b ∈ l, b = false) :
    l.foldl xor false = false := by
  induction l with
  | nil => rfl
  | cons b tl ih =>
    have hb := h b List.mem_cons_self
    subst hb
    simpa using ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

end PEqualNP.Outside.L_pcx_375_aux

theorem PEqualNP.Outside.L_pcx_375 : (∃ C : ℕ, 0 < C ∧ ∀ k : ℕ,
  let n := k+1
  let I := Fin n
  let V := Bool × I
  let P := V → Option Bool
  let J := Fin (n+1)
  let hist := fun (M : Bool → I → I) (pin : P) (d : J × J) =>
    ((Finset.univ : Finset (V → Bool)).filter (fun x =>
      (∀ u, pin u = none ∨ pin u = some (x u)) ∧
      ∀ h : Bool, (Finset.univ.filter (fun i : I =>
        x (false,i) ≠ x (true,M h i))).card = (if h then d.2 else d.1).val)).card
  let ring := fun (h : Bool) (i : I) => if h then i+1 else i
  let classes := fun M : Bool → I → I => ((Finset.univ : Finset P).image (hist M)).card
  (∀ t : ℕ, t*(t+3) ≤ 2*n → 2^t ≤ classes ring) ∧
    classes ring ≤ 2^(C*(1+Nat.sqrt n)) ∧
    ∀ M : Bool → Equiv.Perm I,
      let pair := fun (h : Bool) (i : I) => M h i
      classes pair ≤ (n+1)*classes ring ∧
      ∀ pin : P, ∃ (pin' : P) (f : ℕ), f ≤ n ∧
        ∀ d, hist pair pin d = 2^f * hist ring pin' d) := by
  classical
  open PEqualNP.Outside.L_pcx_375_aux in
  refine ⟨150, by omega, fun k => ?_⟩
  let n := k + 1
  haveI : NeZero n := ⟨Nat.succ_ne_zero k⟩
  have hn : 0 < n := Nat.succ_pos k
  refine ⟨?_, ?_, ?_⟩
  ·
    intro t ht
    have hsum_le : (∑ j : Fin t, (j.val + 2)) ≤ n := by
      have := PEqualNP.Outside.L_pcx_375_aux.sum_j_add_two t; omega
    let rem : ℕ := n - ∑ j : Fin t, (j.val + 2)
    let lenList (S : Finset (Fin t)) : List ℕ :=
      ((List.finRange t).flatMap (fun j => if j ∈ S then [j.val + 2] else List.replicate (j.val + 2) 1)) ++
      List.replicate rem 1
    have hlen_sum : ∀ S : Finset (Fin t), (lenList S).sum = n := by
      intro S
      dsimp only [lenList]
      rw [List.sum_append, List.sum_replicate, smul_eq_mul, mul_one]
      have hflat : (((List.finRange t).flatMap (fun j => if j ∈ S then [j.val + 2] else List.replicate (j.val + 2) 1)).sum) =
          ∑ j : Fin t, (j.val + 2) := by
        rw [PEqualNP.Outside.L_pcx_375_aux.list_sum_flatMap, Fin.sum_univ_def]
        congr 1; apply List.map_congr_left
        intro j _; split_ifs <;> simp
      rw [hflat]; omega
    have hpin_ex : ∀ S : Finset (Fin t), ∃ pin : Bool × Fin n → Option Bool,
        ∀ d : Fin (n + 1) × Fin (n + 1),
          PEqualNP.Outside.L_pcx_375_aux.histDef (PEqualNP.Outside.L_pcx_375_aux.ringDef n) pin d =
          PEqualNP.Outside.L_pcx_375_aux.convList ((lenList S).map fun L => PEqualNP.Outside.L_pcx_375_aux.segHist L L false) (d.1.val, d.2.val) := by
      intro S
      let segs : List (ℕ × ℕ × Bool) := (lenList S).map (fun L => (L, L, false))
      obtain ⟨pin, hpin⟩ := PEqualNP.Outside.L_pcx_375_aux.layout_ring (n := n) segs
        (by
          intro s hs
          simp only [segs, List.mem_map] at hs
          obtain ⟨L, hL, rfl⟩ := hs
          left; refine ⟨rfl, ?_⟩
          dsimp only [lenList] at hL
          rw [List.mem_append] at hL
          rcases hL with h1 | h2
          · rw [List.mem_flatMap] at h1
            obtain ⟨j, _, hj⟩ := h1
            split_ifs at hj
            · simp at hj; omega
            · rw [List.mem_replicate] at hj; omega
          · rw [List.mem_replicate] at h2; omega)
        (by simp [segs, List.map_map, Function.comp_def, hlen_sum S])
        (by simp [segs, List.map_map, Function.comp_def, hlen_sum S])
        (PEqualNP.Outside.L_pcx_375_aux.foldl_xor_all_false _ (by intro b hb; simp [segs] at hb; exact hb.2))
      refine ⟨pin, fun d => ?_⟩
      rw [hpin d]
      simp [segs, List.map_map, Function.comp_def]
    choose pinOf hpinOf using hpin_ex
    have hinj : Function.Injective (fun S : Finset (Fin t) =>
        PEqualNP.Outside.L_pcx_375_aux.histDef (PEqualNP.Outside.L_pcx_375_aux.ringDef n) (pinOf S)) := by
      intro S T hST
      have heval_eq : ∀ z : ℂ,
          (∏ L ∈ S.image (fun j : Fin t => j.val + 2), ((1 + z) ^ L + (1 - z) ^ L) / 2) =
          (∏ L ∈ T.image (fun j : Fin t => j.val + 2), ((1 + z) ^ L + (1 - z) ^ L) / 2) := by
        intro z
        have hpoly_eq : ∀ U : Finset (Fin t),
            (∑ d : Fin (n + 1),
              (PEqualNP.Outside.L_pcx_375_aux.histDef (PEqualNP.Outside.L_pcx_375_aux.ringDef n) (pinOf U)
                (d, ⟨0, Nat.zero_lt_succ n⟩) : ℂ) * z ^ d.val) =
            (∏ L ∈ U.image (fun j : Fin t => j.val + 2), ((1 + z) ^ L + (1 - z) ^ L) / 2) := by
          intro U
          have h1 : (∑ d : Fin (n + 1),
              (PEqualNP.Outside.L_pcx_375_aux.histDef (PEqualNP.Outside.L_pcx_375_aux.ringDef n) (pinOf U)
                (d, ⟨0, Nat.zero_lt_succ n⟩) : ℂ) * z ^ d.val) =
              ∑ d ∈ Finset.range ((lenList U).sum + 1),
                (PEqualNP.Outside.L_pcx_375_aux.convList ((lenList U).map fun L =>
                  PEqualNP.Outside.L_pcx_375_aux.segHist L L false) (d, 0) : ℂ) * z ^ d := by
            rw [hlen_sum U, ← Fin.sum_univ_eq_sum_range]
            apply Finset.sum_congr rfl
            intro d _
            rw [hpinOf U (d, ⟨0, Nat.zero_lt_succ n⟩)]
          rw [h1, PEqualNP.Outside.L_pcx_375_aux.eval_poly_convList (lenList U) z]
          dsimp only [lenList]
          rw [List.map_append, List.prod_append]
          have hrep1 : ∀ m : ℕ, ((List.replicate m 1).map (fun L => ((1 + z) ^ L + (1 - z) ^ L) / 2)).prod = 1 := by
            intro m; rw [List.map_replicate, List.prod_replicate]
            have : ((1 + z) ^ 1 + (1 - z) ^ 1) / 2 = 1 := by ring
            rw [this, one_pow]
          rw [hrep1 rem, mul_one, List.map_flatMap, PEqualNP.Outside.L_pcx_375_aux.list_prod_flatMap]
          have hfin_prod : (((List.finRange t).map (fun j =>
              ((if j ∈ U then [j.val + 2] else List.replicate (j.val + 2) 1).map
                (fun L => ((1 + z) ^ L + (1 - z) ^ L) / 2)).prod)).prod) =
              ∏ j : Fin t, if j ∈ U then ((1 + z) ^ (j.val + 2) + (1 - z) ^ (j.val + 2)) / 2 else 1 := by
            rw [Fin.prod_univ_def]
            congr 1; apply List.map_congr_left
            intro j _
            split_ifs
            · simp
            · exact hrep1 (j.val + 2)
          rw [hfin_prod, ← Finset.prod_filter]
          have hfilt : (Finset.univ.filter (fun j : Fin t => j ∈ U)) = U := by ext j; simp
          rw [hfilt, Finset.prod_image (fun a _ b _ hab => Fin.ext (Nat.add_right_cancel hab))]
        rw [← hpoly_eq S, ← hpoly_eq T]
        apply Finset.sum_congr rfl
        intro d _
        exact congrArg (fun x : ℕ => (x : ℂ) * z ^ d.val) (congrFun hST (d, ⟨0, Nat.zero_lt_succ n⟩))
      have himg_eq := PEqualNP.Outside.L_pcx_375_aux.poly_zero_distinct
        (S.image (fun j : Fin t => j.val + 2))
        (T.image (fun j : Fin t => j.val + 2))
        (by intro L hL; simp at hL; obtain ⟨j, _, rfl⟩ := hL; omega)
        (by intro L hL; simp at hL; obtain ⟨j, _, rfl⟩ := hL; omega)
        heval_eq
      ext j
      constructor
      · intro hj
        have hmem : j.val + 2 ∈ T.image (fun i : Fin t => i.val + 2) := by
          rw [← himg_eq]; exact Finset.mem_image_of_mem _ hj
        simp only [Finset.mem_image] at hmem
        obtain ⟨i, hi, hij⟩ := hmem
        have : i = j := Fin.ext (by omega)
        rwa [← this]
      · intro hj
        have hmem : j.val + 2 ∈ S.image (fun i : Fin t => i.val + 2) := by
          rw [himg_eq]; exact Finset.mem_image_of_mem _ hj
        simp only [Finset.mem_image] at hmem
        obtain ⟨i, hi, hij⟩ := hmem
        have : i = j := Fin.ext (by omega)
        rwa [← this]
    have hcard : (Finset.univ : Finset (Finset (Fin t))).card ≤
        ((Finset.univ : Finset (Bool × Fin n → Option Bool)).image
          (PEqualNP.Outside.L_pcx_375_aux.histDef (PEqualNP.Outside.L_pcx_375_aux.ringDef n))).card := by
      calc (Finset.univ : Finset (Finset (Fin t))).card
          = ((Finset.univ : Finset (Finset (Fin t))).image (fun S =>
              PEqualNP.Outside.L_pcx_375_aux.histDef (PEqualNP.Outside.L_pcx_375_aux.ringDef n) (pinOf S))).card :=
            (Finset.card_image_of_injective _ hinj).symm
        _ ≤ _ := Finset.card_le_card (by
            intro h hh
            simp only [Finset.mem_image, Finset.mem_univ, true_and] at hh ⊢
            obtain ⟨S, rfl⟩ := hh
            exact ⟨pinOf S, rfl⟩)
    have hlhs : (Finset.univ : Finset (Finset (Fin t))).card = 2 ^ t := by
      rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    exact hlhs ▸ hcard
  ·
    let decodeSeg (p : Fin 4 × Fin (2 * n)) : ℕ × ℕ × Bool :=
      let m := p.2.val + 1
      let par := decide (p.1.val % 2 = 1)
      if m % 2 = 0 then (m / 2, m / 2, par)
      else if p.1.val / 2 = 1 then (m / 2, m / 2 + 1, par)
      else (m / 2 + 1, m / 2, par)
    let encodeSegAll (s : ℕ × ℕ × Bool) : Option (Fin 4 × Fin (2 * n)) :=
      if h : 1 ≤ s.1 + s.2.1 ∧ s.1 + s.2.1 ≤ 2 * n then
        some (⟨(if s.2.1 > s.1 then 2 else 0) + (if s.2.2 then 1 else 0), by split_ifs <;> omega⟩,
              ⟨s.1 + s.2.1 - 1, by omega⟩)
      else none
    have hdec_enc_all : ∀ s : ℕ × ℕ × Bool,
        ((s.1 = s.2.1 ∧ 0 < s.1) ∨ s.1 = s.2.1 + 1 ∨ s.2.1 = s.1 + 1) →
        s.1 + s.2.1 ≤ 2 * n →
        ∃ p : Fin 4 × Fin (2 * n), encodeSegAll s = some p ∧ decodeSeg p = s ∧ p.2.val + 1 = s.1 + s.2.1 := by
      intro s hv hle
      have hpos : 1 ≤ s.1 + s.2.1 := by omega
      let p : Fin 4 × Fin (2 * n) :=
        (⟨(if s.2.1 > s.1 then 2 else 0) + (if s.2.2 then 1 else 0), by split_ifs <;> omega⟩,
         ⟨s.1 + s.2.1 - 1, by omega⟩)
      refine ⟨p, ?_, ?_, by dsimp only [p]; omega⟩
      · dsimp only [encodeSegAll, p]; simp [hpos, hle]
      · rcases s with ⟨r, b, par⟩
        dsimp only [decodeSeg, p] at hv hle hpos ⊢
        rcases hv with ⟨h1, h2⟩ | hred | hblue
        · have hnot : ¬ b > r := by omega
          have hmod : (r + b - 1 + 1) % 2 = 0 := by omega
          simp only [hnot, ↓reduceIte, Nat.zero_add, hmod]
          cases par <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
            exact Prod.ext (by dsimp only; omega) (Prod.ext (by dsimp only; omega) (by dsimp only; decide))
        · have hnot : ¬ b > r := by omega
          have hmod : (r + b - 1 + 1) % 2 = 1 := by omega
          simp only [hnot, ↓reduceIte, Nat.zero_add, hmod, show ¬ (1 : ℕ) = 0 by decide]
          cases par <;> simp only [Bool.false_eq_true, ↓reduceIte, show (0 : ℕ) / 2 = 0 by decide,
            show (1 : ℕ) / 2 = 0 by decide, show ¬ (0 : ℕ) = 1 by decide] <;>
            exact Prod.ext (by dsimp only; omega) (Prod.ext (by dsimp only; omega) (by dsimp only; decide))
        · have hgt : b > r := by omega
          have hmod : (r + b - 1 + 1) % 2 = 1 := by omega
          simp only [hgt, ↓reduceIte, hmod, show ¬ (1 : ℕ) = 0 by decide]
          cases par <;> simp only [Bool.false_eq_true, ↓reduceIte, show (2 + 0 : ℕ) / 2 = 1 by decide,
            show (2 + 1 : ℕ) / 2 = 1 by decide] <;>
            exact Prod.ext (by dsimp only; omega) (Prod.ext (by dsimp only; omega) (by dsimp only; decide))
    have hring_ex : ∀ pin : Bool × Fin n → Option Bool, pin ≠ (fun _ => none) →
        ∃ c ∈ PEqualNP.Outside.L_pcx_375_aux.Part4 (2 * n),
          ∃ segs : List (ℕ × ℕ × Bool),
            (∀ d, PEqualNP.Outside.L_pcx_375_aux.histDef (PEqualNP.Outside.L_pcx_375_aux.ringDef n) pin d =
              PEqualNP.Outside.L_pcx_375_aux.convList (segs.map fun s =>
                PEqualNP.Outside.L_pcx_375_aux.segHist s.1 s.2.1 s.2.2) (d.1.val, d.2.val)) ∧
            (∀ s ∈ segs, (s.1 = s.2.1 ∧ 0 < s.1) ∨ s.1 = s.2.1 + 1 ∨ s.2.1 = s.1 + 1) ∧
            (∀ s ∈ segs, s.1 + s.2.1 ≤ 2 * n) ∧
            (∀ p : Fin 4 × Fin (2 * n), (c p).val = (segs.filter (fun s => decide (encodeSegAll s = some p))).length) := by
      intro pin hne
      have hex_u : ∃ u, pin u ≠ none := by
        by_contra hall; apply hne; funext u; by_contra hu; exact hall ⟨u, hu⟩
      obtain ⟨⟨b0, i0⟩, hu0⟩ := hex_u
      let M := PEqualNP.Outside.L_pcx_375_aux.ringPerm n
      have htau_iter : ∀ (i : Fin n) (t : ℕ), ((((M true).trans (M false).symm)^[t]) i).val = (i.val + t) % n := by
        intro i t
        induction t with
        | zero => simp [Nat.mod_eq_of_lt i.isLt]
        | succ t ih =>
          rw [Function.iterate_succ_apply']
          change ((((M true).trans (M false).symm)^[t]) i + (1 : Fin n)).val = _
          rw [Fin.val_add, ih]
          by_cases hn1 : n = 1
          · simp [hn1, Nat.mod_one]
          · rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < n by omega), Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            congr 1
      have hpinned : ∀ i : Fin n, ∃ t : ℕ,
          pin (false, (((M true).trans (M false).symm)^[t]) i) ≠ none ∨
          pin (true, M true ((((M true).trans (M false).symm)^[t]) i)) ≠ none := by
        intro i
        cases b0
        · refine ⟨(i0.val + n - i.val) % n, Or.inl ?_⟩
          have heq : (((M true).trans (M false).symm)^[(i0.val + n - i.val) % n]) i = i0 := by
            apply Fin.ext; rw [htau_iter]
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
                show i.val + (i0.val + n - i.val) = i0.val + n by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt i0.isLt]
          rwa [heq]
        · let j0 : Fin n := i0 - 1
          refine ⟨(j0.val + n - i.val) % n, Or.inr ?_⟩
          have heq : (((M true).trans (M false).symm)^[(j0.val + n - i.val) % n]) i = j0 := by
            apply Fin.ext; rw [htau_iter]
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
                show i.val + (j0.val + n - i.val) = j0.val + n by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt j0.isLt]
          rw [heq]
          change pin (true, j0 + 1) ≠ none
          have : j0 + 1 = i0 := sub_add_cancel i0 1
          rwa [this]
      obtain ⟨segs, hhist, hvalid, hsumR, hsumB, _⟩ := PEqualNP.Outside.L_pcx_375_aux.extract_segs M pin hpinned
      have hMring : (fun h i => M h i) = PEqualNP.Outside.L_pcx_375_aux.ringDef n := by
        funext h i; exact PEqualNP.Outside.L_pcx_375_aux.ringPerm_apply n h i
      rw [hMring] at hhist
      have hsum2 : (segs.map (fun s => s.1 + s.2.1)).sum = 2 * n := by
        have hadd : ∀ l : List (ℕ × ℕ × Bool), (l.map (fun s => s.1 + s.2.1)).sum =
            (l.map (·.1)).sum + (l.map (·.2.1)).sum := by
          intro l; induction l with | nil => rfl | cons s tl ih => simp [ih]; omega
        rw [hadd, hsumR, hsumB]; omega
      have hle_all : ∀ s ∈ segs, s.1 + s.2.1 ≤ 2 * n := by
        intro s hs; rw [← hsum2]; exact List.le_sum_of_mem (List.mem_map.mpr ⟨s, hs, rfl⟩)
      have hlen_le : segs.length ≤ 2 * n := by
        have haux : ∀ l : List (ℕ × ℕ × Bool), (∀ s ∈ l, 1 ≤ s.1 + s.2.1) →
            l.length ≤ (l.map (fun s => s.1 + s.2.1)).sum := by
          intro l hl; induction l with
          | nil => simp
          | cons s tl ih =>
            have hs := hl s List.mem_cons_self
            have htl := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))
            simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
        rw [← hsum2]
        exact haux segs (fun s hs => by have := hvalid s hs; omega)
      let c : Fin 4 × Fin (2 * n) → Fin (2 * n + 1) := fun p =>
        ⟨(segs.filter (fun s => decide (encodeSegAll s = some p))).length,
          Nat.lt_succ_of_le ((List.length_filter_le _ _).trans hlen_le)⟩
      have hc_mem : c ∈ PEqualNP.Outside.L_pcx_375_aux.Part4 (2 * n) := by
        unfold PEqualNP.Outside.L_pcx_375_aux.Part4
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hsum_eq : ∀ l : List (ℕ × ℕ × Bool),
            (∀ s ∈ l, ((s.1 = s.2.1 ∧ 0 < s.1) ∨ s.1 = s.2.1 + 1 ∨ s.2.1 = s.1 + 1) ∧ s.1 + s.2.1 ≤ 2 * n) →
            (∑ p : Fin 4 × Fin (2 * n), (l.filter (fun s => decide (encodeSegAll s = some p))).length * (p.2.val + 1)) =
            (l.map (fun s => s.1 + s.2.1)).sum := by
          intro l hl
          induction l with
          | nil => simp
          | cons s tl ih =>
            have hs := hl s List.mem_cons_self
            have htl := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))
            obtain ⟨p0, hp0_enc, _, hp0_len⟩ := hdec_enc_all s hs.1 hs.2
            have hstep : ∀ p : Fin 4 × Fin (2 * n),
                ((s :: tl).filter (fun u => decide (encodeSegAll u = some p))).length * (p.2.val + 1) =
                (tl.filter (fun u => decide (encodeSegAll u = some p))).length * (p.2.val + 1) +
                if p = p0 then s.1 + s.2.1 else 0 := by
              intro p
              simp only [List.filter_cons, hp0_enc, Option.some.injEq]
              by_cases hp : p = p0
              · subst hp; simp [hp0_len]; ring
              · have hne : p0 ≠ p := Ne.symm hp
                simp [hp, hne]
            simp_rw [hstep]
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
            simp [htl]; omega
        have hcomm : (∑ p : Fin 4 × Fin (2 * n), (p.2.val + 1) * (c p).val) =
            ∑ p : Fin 4 × Fin (2 * n), (segs.filter (fun s => decide (encodeSegAll s = some p))).length * (p.2.val + 1) := by
          apply Finset.sum_congr rfl; intro p _; exact mul_comm _ _
        rw [hcomm, hsum_eq segs (fun s hs => ⟨hvalid s hs, hle_all s hs⟩), hsum2]
      exact ⟨c, hc_mem, segs, hhist, hvalid, hle_all, fun _ => rfl⟩

    let imgRing := (Finset.univ : Finset (Bool × Fin n → Option Bool)).image
      (PEqualNP.Outside.L_pcx_375_aux.histDef (PEqualNP.Outside.L_pcx_375_aux.ringDef n))
    have hmap_ex : ∀ h ∈ imgRing,
        ∃ o : Option {c // c ∈ PEqualNP.Outside.L_pcx_375_aux.Part4 (2 * n)},
          (o = none ∧ h = PEqualNP.Outside.L_pcx_375_aux.histDef (PEqualNP.Outside.L_pcx_375_aux.ringDef n) (fun _ => none)) ∨
          (∃ (c : {c // c ∈ PEqualNP.Outside.L_pcx_375_aux.Part4 (2 * n)}) (segs : List (ℕ × ℕ × Bool)),
            o = some c ∧
            (∀ d, h d = PEqualNP.Outside.L_pcx_375_aux.convList (segs.map fun s =>
              PEqualNP.Outside.L_pcx_375_aux.segHist s.1 s.2.1 s.2.2) (d.1.val, d.2.val)) ∧
            (∀ s ∈ segs, (s.1 = s.2.1 ∧ 0 < s.1) ∨ s.1 = s.2.1 + 1 ∨ s.2.1 = s.1 + 1) ∧
            (∀ s ∈ segs, s.1 + s.2.1 ≤ 2 * n) ∧
            (∀ p : Fin 4 × Fin (2 * n), (c.1 p).val = (segs.filter (fun s => decide (encodeSegAll s = some p))).length)) := by
      intro h hh
      obtain ⟨pin, _, rfl⟩ := Finset.mem_image.mp hh
      by_cases hp : pin = fun _ => none
      · subst hp; exact ⟨none, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨c, hc, segs, hhist, hvalid, hle, hcnt⟩ := hring_ex pin hp
        exact ⟨some ⟨c, hc⟩, Or.inr ⟨⟨c, hc⟩, segs, rfl, hhist, hvalid, hle, hcnt⟩⟩
    let fMap (h : (Fin (n + 1) × Fin (n + 1)) → ℕ) : Option {c // c ∈ PEqualNP.Outside.L_pcx_375_aux.Part4 (2 * n)} :=
      if hh : h ∈ imgRing then (hmap_ex h hh).choose else none
    have hfMap_inj : Set.InjOn fMap (imgRing : Set ((Fin (n + 1) × Fin (n + 1)) → ℕ)) := by
      intro h1 hh1 h2 hh2 heq
      have h1_mem : h1 ∈ imgRing := hh1
      have h2_mem : h2 ∈ imgRing := hh2
      have hs1 := (hmap_ex h1 h1_mem).choose_spec
      have hs2 := (hmap_ex h2 h2_mem).choose_spec
      have hfeq : (hmap_ex h1 h1_mem).choose = (hmap_ex h2 h2_mem).choose := by
        simpa [fMap, h1_mem, h2_mem] using heq
      rcases hs1 with ⟨hn1, he1⟩ | ⟨c1, segs1, ho1, hh1', hv1, hl1, hc1⟩ <;>
        rcases hs2 with ⟨hn2, he2⟩ | ⟨c2, segs2, ho2, hh2', hv2, hl2, hc2⟩
      · exact he1.trans he2.symm
      · rw [hn1, ho2] at hfeq; simp at hfeq
      · rw [ho1, hn2] at hfeq; simp at hfeq
      · rw [ho1, ho2] at hfeq
        have hc_eq : c1 = c2 := Option.some.inj hfeq
        subst hc_eq
        have hperm : segs1.Perm segs2 := by
          rw [List.perm_iff_count]
          intro s
          have hcnt_eq : ∀ (segs : List (ℕ × ℕ × Bool)) (hv : ∀ u ∈ segs, (u.1 = u.2.1 ∧ 0 < u.1) ∨ u.1 = u.2.1 + 1 ∨ u.2.1 = u.1 + 1)
              (hl : ∀ u ∈ segs, u.1 + u.2.1 ≤ 2 * n) (p : Fin 4 × Fin (2 * n)),
              encodeSegAll s = some p → decodeSeg p = s →
              segs.count s = (segs.filter (fun u => decide (encodeSegAll u = some p))).length := by
            intro segs hv hl p hp hdec
            rw [List.count_eq_length_filter]
            congr 1
            apply List.filter_congr
            intro u hu
            obtain ⟨pu, hpu, hdecu, _⟩ := hdec_enc_all u (hv u hu) (hl u hu)
            rw [Bool.eq_iff_iff]
            simp only [beq_iff_eq, decide_eq_true_eq, hpu, Option.some.injEq]
            constructor
            · rintro rfl; rw [hp] at hpu; exact Option.some.inj hpu.symm
            · rintro rfl; exact hdecu.symm.trans hdec
          by_cases hs1' : s ∈ segs1
          · obtain ⟨p, hp, hdec, _⟩ := hdec_enc_all s (hv1 s hs1') (hl1 s hs1')
            rw [hcnt_eq segs1 hv1 hl1 p hp hdec, hcnt_eq segs2 hv2 hl2 p hp hdec, ← hc1 p, ← hc2 p]
          · by_cases hs2' : s ∈ segs2
            · obtain ⟨p, hp, hdec, _⟩ := hdec_enc_all s (hv2 s hs2') (hl2 s hs2')
              rw [hcnt_eq segs1 hv1 hl1 p hp hdec, hcnt_eq segs2 hv2 hl2 p hp hdec, ← hc1 p, ← hc2 p]
            · rw [List.count_eq_zero_of_not_mem hs1', List.count_eq_zero_of_not_mem hs2']
        funext d
        rw [hh1' d, hh2' d]
        exact congrFun (PEqualNP.Outside.L_pcx_375_aux.convList_perm (hperm.map _)) (d.1.val, d.2.val)
    have hcard_le : imgRing.card ≤ 1 + (PEqualNP.Outside.L_pcx_375_aux.Part4 (2 * n)).card := by
      have h1 : imgRing.card ≤ Fintype.card (Option {c // c ∈ PEqualNP.Outside.L_pcx_375_aux.Part4 (2 * n)}) :=
        Finset.card_le_card_of_injOn fMap (fun _ _ => Finset.mem_univ _) hfMap_inj
      simpa [Fintype.card_option, Fintype.card_coe, add_comm] using h1
    have hpart4 := PEqualNP.Outside.L_pcx_375_aux.part4_card_le (2 * n)
    have hsqrt_le : Nat.sqrt (2 * n) ≤ 2 * Nat.sqrt n + 1 := by
      have hsq : n < (Nat.sqrt n + 1) ^ 2 := by
        have := Nat.lt_succ_sqrt n; nlinarith
      have h2sq : 2 * n < (2 * Nat.sqrt n + 2) ^ 2 := by nlinarith
      have hlt : Nat.sqrt (2 * n) < 2 * Nat.sqrt n + 2 := by
        rw [Nat.sqrt_lt]; nlinarith
      omega
    have hexp_le : 70 * (Nat.sqrt (2 * n) + 1) + 1 ≤ 150 * (1 + Nat.sqrt n) := by omega
    have hpow_bound : 1 + 2 ^ (70 * (Nat.sqrt (2 * n) + 1)) ≤ 2 ^ (150 * (1 + Nat.sqrt n)) := by
      have h1 : 1 ≤ 2 ^ (70 * (Nat.sqrt (2 * n) + 1)) := Nat.one_le_pow _ _ (by omega)
      calc 1 + 2 ^ (70 * (Nat.sqrt (2 * n) + 1))
          ≤ 2 ^ (70 * (Nat.sqrt (2 * n) + 1)) + 2 ^ (70 * (Nat.sqrt (2 * n) + 1)) := by omega
        _ = 2 ^ (70 * (Nat.sqrt (2 * n) + 1) + 1) := by rw [Nat.pow_succ]; omega
        _ ≤ 2 ^ (150 * (1 + Nat.sqrt n)) := Nat.pow_le_pow_right (by omega) hexp_le
    exact hcard_le.trans ((Nat.add_le_add_left hpart4 1).trans hpow_bound)
  ·
    intro M
    have hpart4 : ∀ pin : Bool × Fin n → Option Bool, ∃ (pin' : Bool × Fin n → Option Bool) (f : ℕ), f ≤ n ∧
        ∀ d : Fin (n + 1) × Fin (n + 1),
          PEqualNP.Outside.L_pcx_375_aux.histDef (fun h i => M h i) pin d =
          2 ^ f * PEqualNP.Outside.L_pcx_375_aux.histDef (PEqualNP.Outside.L_pcx_375_aux.ringDef n) pin' d := by
      intro pin
      obtain ⟨pin1, f, hf, hhist1, hpinned⟩ := PEqualNP.Outside.L_pcx_375_aux.free_cycles_elim M pin
      obtain ⟨segs, hhist2, hvalid, hsumR, hsumB, hxor⟩ := PEqualNP.Outside.L_pcx_375_aux.extract_segs M pin1 hpinned
      obtain ⟨pin', hhist3⟩ := PEqualNP.Outside.L_pcx_375_aux.layout_ring (n := n) segs hvalid hsumR hsumB hxor
      refine ⟨pin', f, hf, fun d => ?_⟩
      rw [hhist1 d, hhist2 d, hhist3 d]
    refine ⟨?_, hpart4⟩

    let imgPair := (Finset.univ : Finset (Bool × Fin n → Option Bool)).image
      (PEqualNP.Outside.L_pcx_375_aux.histDef (fun h i => M h i))
    let imgRing := (Finset.univ : Finset (Bool × Fin n → Option Bool)).image
      (PEqualNP.Outside.L_pcx_375_aux.histDef (PEqualNP.Outside.L_pcx_375_aux.ringDef n))
    have hpair_ex : ∀ h ∈ imgPair,
        ∃ p ∈ (Finset.univ : Finset (Fin (n + 1))) ×ˢ imgRing,
          ∀ d, h d = 2 ^ p.1.val * p.2 d := by
      intro h hh
      obtain ⟨pin, _, rfl⟩ := Finset.mem_image.mp hh
      obtain ⟨pin', f, hf, heq⟩ := hpart4 pin
      refine ⟨(⟨f, Nat.lt_succ_of_le hf⟩,
        PEqualNP.Outside.L_pcx_375_aux.histDef (PEqualNP.Outside.L_pcx_375_aux.ringDef n) pin'), ?_, heq⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    let gMap (h : (Fin (n + 1) × Fin (n + 1)) → ℕ) : Fin (n + 1) × ((Fin (n + 1) × Fin (n + 1)) → ℕ) :=
      if hh : h ∈ imgPair then (hpair_ex h hh).choose else (⟨0, Nat.zero_lt_succ n⟩, fun _ => 0)
    have hcard : imgPair.card ≤ ((Finset.univ : Finset (Fin (n + 1))) ×ˢ imgRing).card := by
      apply Finset.card_le_card_of_injOn gMap
      · intro h hh
        have hmem : h ∈ imgPair := hh
        simp only [gMap, hmem, ↓reduceDIte]
        exact (hpair_ex h hmem).choose_spec.1
      · intro h1 hh1 h2 hh2 heq
        have h1m : h1 ∈ imgPair := hh1
        have h2m : h2 ∈ imgPair := hh2
        have hs1 := (hpair_ex h1 h1m).choose_spec.2
        have hs2 := (hpair_ex h2 h2m).choose_spec.2
        have hgeq : (hpair_ex h1 h1m).choose = (hpair_ex h2 h2m).choose := by
          simpa [gMap, h1m, h2m] using heq
        funext d
        rw [hs1 d, hs2 d, hgeq]
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hcard
    exact hcard

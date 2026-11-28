import PEqualNP.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace PEqualNP.Outside.L_lib_928_aux

open Finset

def sgn (b : Bool) : ℝ := if b then -1 else 1

theorem sgn_xor (b1 b2 : Bool) : sgn (xor b1 b2) = sgn b1 * sgn b2 := by
  cases b1 <;> cases b2 <;> norm_num [sgn]

theorem sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> norm_num [sgn]

theorem abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> norm_num [sgn]

theorem sgn_parity {m : ℕ} (g : Fin m → Bool) :
    sgn (((Finset.univ : Finset (Fin m)).filter (fun i => g i)).card % 2 == 1)
      = ∏ i : Fin m, sgn (g i) := by
  have key : ∀ s : Finset (Fin m),
      sgn ((s.filter (fun i => g i)).card % 2 == 1) = ∏ i ∈ s, sgn (g i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [sgn]
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.filter_insert]
      by_cases hg : g i = true
      · rw [if_pos hg, Finset.card_insert_of_notMem (fun h => hi (mem_of_mem_filter _ h)), hg]
        rw [← ih]
        simp only [sgn]
        have : ((s.filter (fun i => g i)).card + 1) % 2 = 1 ↔ ¬ ((s.filter (fun i => g i)).card % 2 = 1) := by
          omega
        by_cases h1 : (s.filter (fun i => g i)).card % 2 = 1
        · have h2 : ¬ ((s.filter (fun i => g i)).card + 1) % 2 = 1 := by omega
          simp [h1, h2]
        · have h2 : ((s.filter (fun i => g i)).card + 1) % 2 = 1 := by omega
          simp [h1, h2]
      · rw [if_neg hg, Bool.eq_false_iff.mpr hg]
        rw [← ih]
        simp [sgn]
  exact key Finset.univ

theorem sum_add_div_two {α : Type*} (s : Finset α) (f g : α → ℝ) :
    ∑ i ∈ s, (f i + g i) / 2 = ((∑ i ∈ s, f i) + (∑ i ∈ s, g i)) / 2 := by
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib]

theorem sum_sgn_eq {α : Type*} (S : Finset α) (t : α → Bool) :
    ∑ x ∈ S, sgn (t x) = (S.card : ℝ) - 2 * ((S.filter (fun x => t x)).card : ℝ) := by
  have h1 : ∀ x ∈ S, sgn (t x) = 1 - 2 * (if t x then (1 : ℝ) else 0) := by
    intro x _; cases t x <;> norm_num [sgn]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, Finset.sum_boole]

theorem acc_le_bias {α : Type*} (S : Finset α) (t : α → Bool) (ans : Bool) :
    ((S.filter (fun x => ans = t x)).card : ℝ) ≤ ((S.card : ℝ) + |∑ x ∈ S, sgn (t x)|) / 2 := by
  have h1 : sgn ans * ∑ x ∈ S, sgn (t x) = 2 * ((S.filter (fun x => ans = t x)).card : ℝ) - (S.card : ℝ) := by
    rw [Finset.mul_sum]
    have h2 : ∀ x ∈ S, sgn ans * sgn (t x) = 2 * (if ans = t x then (1 : ℝ) else 0) - 1 := by
      intro x _; cases ans <;> cases t x <;> norm_num [sgn]
    rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have hle : sgn ans * ∑ x ∈ S, sgn (t x) ≤ |∑ x ∈ S, sgn (t x)| := by
    calc sgn ans * ∑ x ∈ S, sgn (t x) ≤ |sgn ans * ∑ x ∈ S, sgn (t x)| := le_abs_self _
      _ = |sgn ans| * |∑ x ∈ S, sgn (t x)| := abs_mul _ _
      _ = |∑ x ∈ S, sgn (t x)| := by rw [abs_sgn, one_mul]
  linarith

theorem max_ones_eq {α : Type*} [Fintype α] (t : α → Bool) :
    (max ((Finset.univ.filter (fun x => t x)).card)
      (Fintype.card α - (Finset.univ.filter (fun x => t x)).card) : ℝ)
      = ((Fintype.card α : ℝ) + |∑ x : α, sgn (t x)|) / 2 := by
  set c := (Finset.univ.filter (fun x => t x)).card
  have hle : c ≤ Fintype.card α := by simpa using Finset.card_le_univ (Finset.univ.filter (fun x => t x))
  have hs := sum_sgn_eq Finset.univ t
  simp only [Finset.card_univ] at hs
  rw [hs]
  by_cases h : 2 * c ≤ Fintype.card α
  · have hmax : max c (Fintype.card α - c) = Fintype.card α - c := max_eq_right (by omega)
    have hmaxr : max (c : ℝ) ((Fintype.card α : ℝ) - c) = (Fintype.card α : ℝ) - c := by
      have : (c : ℝ) ≤ (Fintype.card α : ℝ) - (c : ℝ) := by
        have : (2 : ℝ) * (c : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast h
        linarith
      exact max_eq_right this
    rw [hmaxr]
    have hnn : (0 : ℝ) ≤ (Fintype.card α : ℝ) - 2 * (c : ℝ) := by
      have : (2 : ℝ) * (c : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast h
      linarith
    rw [abs_of_nonneg hnn]
    ring
  · have hmaxr : max (c : ℝ) ((Fintype.card α : ℝ) - c) = (c : ℝ) := by
      have : (Fintype.card α : ℝ) - (c : ℝ) ≤ (c : ℝ) := by
        have : (Fintype.card α : ℝ) ≤ (2 : ℝ) * (c : ℝ) := by exact_mod_cast (show Fintype.card α ≤ 2 * c by omega)
        linarith
      exact max_eq_left this
    rw [hmaxr]
    have hnp : (Fintype.card α : ℝ) - 2 * (c : ℝ) ≤ 0 := by
      have : (Fintype.card α : ℝ) ≤ (2 : ℝ) * (c : ℝ) := by exact_mod_cast (show Fintype.card α ≤ 2 * c by omega)
      linarith
    rw [abs_of_nonpos hnp]
    ring

theorem prod_le_prod_nn {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 := hf a (mem_insert_self a s)
    have h2 := hfg a (mem_insert_self a s)
    have h3 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => hf i (mem_insert_of_mem hi))
    have h4 := ih (fun i hi => hf i (mem_insert_of_mem hi)) (fun i hi => hfg i (mem_insert_of_mem hi))
    exact mul_le_mul h2 h4 h3 (h1.trans h2)

theorem pow_tangent {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ h : ℕ, 1 ≤ h → b ^ h + (h : ℝ) * b ^ (h - 1) * (a - b) ≤ a ^ h := by
  intro h hh
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hh
  have hgeom : a ^ (k + 1) - b ^ (k + 1) = (a - b) * ∑ i ∈ Finset.range (k + 1), a ^ i * b ^ (k - i) := by
    rw [mul_comm]
    simpa using (geom_sum₂_mul a b (k + 1)).symm
  have hsum : (a - b) * ((k + 1 : ℕ) : ℝ) * b ^ k ≤ (a - b) * ∑ i ∈ Finset.range (k + 1), a ^ i * b ^ (k - i) := by
    by_cases hab : b ≤ a
    · have hle : ((k + 1 : ℕ) : ℝ) * b ^ k ≤ ∑ i ∈ Finset.range (k + 1), a ^ i * b ^ (k - i) := by
        calc ((k + 1 : ℕ) : ℝ) * b ^ k = ∑ _i ∈ Finset.range (k + 1), b ^ k := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ ∑ i ∈ Finset.range (k + 1), a ^ i * b ^ (k - i) := by
              refine Finset.sum_le_sum (fun i hi => ?_)
              have hi' : i ≤ k := Nat.le_of_lt_succ (mem_range.mp hi)
              calc b ^ k = b ^ i * b ^ (k - i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
                _ ≤ a ^ i * b ^ (k - i) := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hab i) (by positivity)
      have h1 := mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hab)
      linarith
    · push_neg at hab
      have hge : ∑ i ∈ Finset.range (k + 1), a ^ i * b ^ (k - i) ≤ ((k + 1 : ℕ) : ℝ) * b ^ k := by
        calc ∑ i ∈ Finset.range (k + 1), a ^ i * b ^ (k - i)
            ≤ ∑ _i ∈ Finset.range (k + 1), b ^ k := by
              refine Finset.sum_le_sum (fun i hi => ?_)
              have hi' : i ≤ k := Nat.le_of_lt_succ (mem_range.mp hi)
              calc a ^ i * b ^ (k - i) ≤ b ^ i * b ^ (k - i) :=
                    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab.le i) (by positivity)
                _ = b ^ k := by rw [← pow_add, Nat.add_sub_cancel' hi']
          _ = ((k + 1 : ℕ) : ℝ) * b ^ k := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have h1 := mul_le_mul_of_nonpos_left hge (sub_nonpos.mpr hab.le)
      linarith
  simp only [Nat.add_sub_cancel]
  push_cast at hsum ⊢
  linarith

theorem pow_mean_le {α : Type*} (T : Finset α) (hT : T.Nonempty) (g : α → ℝ)
    (hg : ∀ t ∈ T, 0 ≤ g t) (h : ℕ) (hh : 1 ≤ h) :
    ((∑ t ∈ T, g t) / (T.card : ℝ)) ^ h ≤ (∑ t ∈ T, (g t) ^ h) / (T.card : ℝ) := by
  have hcard : (0 : ℝ) < (T.card : ℝ) := by exact_mod_cast hT.card_pos
  set b := (∑ t ∈ T, g t) / (T.card : ℝ)
  have hb : 0 ≤ b := div_nonneg (Finset.sum_nonneg hg) hcard.le
  have h1 : ∑ t ∈ T, (b ^ h + (h : ℝ) * b ^ (h - 1) * (g t - b)) ≤ ∑ t ∈ T, (g t) ^ h :=
    Finset.sum_le_sum (fun t ht => pow_tangent (hg t ht) hb h hh)
  have h2 : ∑ t ∈ T, (b ^ h + (h : ℝ) * b ^ (h - 1) * (g t - b)) = (T.card : ℝ) * b ^ h := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have hzero : (∑ t ∈ T, g t) - (T.card : ℝ) * b = 0 := by
      simp only [b]; field_simp; ring
    rw [hzero, mul_zero, add_zero]
  rw [h2] at h1
  rw [le_div_iff₀ hcard]
  linarith

theorem kraft_ineq {α : Type*} [Fintype α] [DecidableEq α] (send : α → List Bool)
    (hpf : ∀ x x' tail, send x ++ tail = send x' → tail = []) :
    ∑ c ∈ Finset.univ.image send, (1 / 2 : ℝ) ^ c.length ≤ 1 := by
  classical
  set img := Finset.univ.image send
  set M := img.sup List.length
  let Ext : List Bool → Finset (Fin M → Bool) := fun c =>
    Finset.univ.filter (fun v => (List.ofFn v).take c.length = c)
  have hcard : ∀ c ∈ img, (Ext c).card = 2 ^ (M - c.length) := by
    intro c hc
    have hle : c.length ≤ M := Finset.le_sup (f := List.length) hc
    let φ : (Fin (M - c.length) → Bool) → (Fin M → Bool) := fun u i =>
      if hi : i.val < c.length then c[i.val]'hi else u ⟨i.val - c.length, by omega⟩
    have hinj : Function.Injective φ := by
      intro u1 u2 heq
      ext j
      have h1 := congrFun heq ⟨c.length + j.val, by omega⟩
      simp only [φ, show ¬ (c.length + j.val < c.length) by omega, dite_false,
        Nat.add_sub_cancel_left] at h1
      exact h1
    have himg : Finset.univ.image φ = Ext c := by
      ext v
      simp only [mem_image, mem_univ, true_and, Ext, mem_filter]
      constructor
      · rintro ⟨u, rfl⟩
        apply List.ext_getElem
        · simp [hle]
        · intro i hi1 hi2
          simp only [List.getElem_take, List.getElem_ofFn, φ, dif_pos hi2]
      · intro hv
        refine ⟨fun j => v ⟨c.length + j.val, by omega⟩, ?_⟩
        ext i
        simp only [φ]
        split_ifs with hi
        · have h1 := congrArg (fun l : List Bool => l[i.val]?) hv
          have h2 : i.val < ((List.ofFn v).take c.length).length := by simp [hle, hi]
          rw [List.getElem?_eq_getElem h2, List.getElem?_eq_getElem hi] at h1
          simp only [List.getElem_take, List.getElem_ofFn, Option.some.injEq] at h1
          exact h1.symm
        · congr 1; apply Fin.ext; dsimp; omega
    rw [← himg, Finset.card_image_of_injective _ hinj, card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  have hdisj : Set.PairwiseDisjoint (img : Set (List Bool)) Ext := by
    intro c1 hc1 c2 hc2 hne
    show Disjoint (Ext c1) (Ext c2)
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Ext, mem_filter, mem_univ, true_and] at hv1 hv2
    obtain ⟨x1, _, rfl⟩ := mem_image.mp (Finset.mem_coe.mp hc1)
    obtain ⟨x2, _, rfl⟩ := mem_image.mp (Finset.mem_coe.mp hc2)
    have hpref : ∀ (l1 l2 : List Bool), (List.ofFn v).take l1.length = l1 →
        (List.ofFn v).take l2.length = l2 → l1.length ≤ l2.length →
        ∃ tail, l1 ++ tail = l2 := by
      intro l1 l2 h1 h2 hle
      refine ⟨l2.drop l1.length, ?_⟩
      have : l1 = l2.take l1.length := by
        rw [← h2, List.take_take, min_eq_left hle, h1]
      exact (congrArg (· ++ l2.drop l1.length) this).trans (List.take_append_drop l1.length l2)
    rcases le_total (send x1).length (send x2).length with hle | hle
    · obtain ⟨tail, htail⟩ := hpref _ _ hv1 hv2 hle
      have ht0 := hpf x1 x2 tail htail
      rw [ht0, List.append_nil] at htail
      exact hne htail
    · obtain ⟨tail, htail⟩ := hpref _ _ hv2 hv1 hle
      have ht0 := hpf x2 x1 tail htail
      rw [ht0, List.append_nil] at htail
      exact hne htail.symm
  have hsum_nat : ∑ c ∈ img, 2 ^ (M - c.length) ≤ 2 ^ M := by
    calc ∑ c ∈ img, 2 ^ (M - c.length) = ∑ c ∈ img, (Ext c).card :=
          Finset.sum_congr rfl (fun c hc => (hcard c hc).symm)
      _ = (img.biUnion Ext).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (Finset.univ : Finset (Fin M → Bool)).card := Finset.card_le_univ _
      _ = 2 ^ M := by simp
  have h2M : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  rw [← mul_le_mul_iff_left₀ h2M, one_mul, Finset.sum_mul]
  have hterm : ∀ c ∈ img, (1 / 2 : ℝ) ^ c.length * (2 : ℝ) ^ M = ((2 ^ (M - c.length) : ℕ) : ℝ) := by
    intro c hc
    have hle : c.length ≤ M := Finset.le_sup (f := List.length) hc
    rw [one_div, inv_pow, inv_mul_eq_div, Nat.cast_pow, Nat.cast_ofNat,
      div_eq_iff (by positivity : (2 : ℝ) ^ c.length ≠ 0), ← pow_add, Nat.sub_add_cancel hle]
  rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum]
  exact_mod_cast hsum_nat

theorem gibbs_kraft (img : Finset (List Bool)) (w : List Bool → ℝ)
    (hwpos : ∀ c ∈ img, 0 < w c) (hwsum : ∑ c ∈ img, w c = 1)
    (hkraft : ∑ c ∈ img, (1 / 2 : ℝ) ^ c.length ≤ 1) :
    ∑ c ∈ img, w c * (Real.log (1 / w c) / Real.log 2) ≤ ∑ c ∈ img, w c * (c.length : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hstep : ∀ c ∈ img, w c * (Real.log (1 / w c) - (c.length : ℝ) * Real.log 2)
      ≤ (1 / 2 : ℝ) ^ c.length - w c := by
    intro c hc
    have hwc : 0 < w c := hwpos c hc
    have hpos : 0 < (1 / 2 : ℝ) ^ c.length / w c := by positivity
    have hlog := Real.log_le_sub_one_of_pos hpos
    have heq : Real.log ((1 / 2 : ℝ) ^ c.length / w c) =
        Real.log (1 / w c) - (c.length : ℝ) * Real.log 2 := by
      rw [Real.log_div (by positivity) hwc.ne', Real.log_pow, Real.log_div one_ne_zero two_ne_zero,
        Real.log_one, zero_sub, Real.log_div one_ne_zero hwc.ne', Real.log_one, zero_sub]
      ring
    rw [heq] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hwc.le
    have hrhs : w c * ((1 / 2 : ℝ) ^ c.length / w c - 1) = (1 / 2 : ℝ) ^ c.length - w c := by
      field_simp
    linarith
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_sub_distrib, hwsum] at hsum
  have hle0 : ∑ c ∈ img, w c * (Real.log (1 / w c) - (c.length : ℝ) * Real.log 2) ≤ 0 := by
    linarith
  have hexp : ∑ c ∈ img, w c * (Real.log (1 / w c) - (c.length : ℝ) * Real.log 2)
      = (∑ c ∈ img, w c * Real.log (1 / w c)) - (∑ c ∈ img, w c * (c.length : ℝ)) * Real.log 2 := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  rw [hexp] at hle0
  have hdiv : ∑ c ∈ img, w c * (Real.log (1 / w c) / Real.log 2) =
      (∑ c ∈ img, w c * Real.log (1 / w c)) / Real.log 2 := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  rw [hdiv, div_le_iff₀ hlog2]
  linarith

theorem sq_le_two_pow : ∀ t : ℕ, 4 ≤ t → t * t ≤ 2 ^ t := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases h4 : t < 4
    · have : t = 3 := by omega
      subst this; norm_num
    · have hih := ih (by omega)
      have : 2 * t + 1 ≤ t * t := by nlinarith
      calc (t + 1) * (t + 1) = t * t + (2 * t + 1) := by ring
        _ ≤ t * t + t * t := by omega
        _ ≤ 2 ^ t + 2 ^ t := by omega
        _ = 2 ^ (t + 1) := by ring

theorem exists_poly_le_two_pow (C K : ℕ) (hC : 1 ≤ C) (hK : 1 ≤ K) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ((C * m : ℕ) : ℝ) ^ K ≤ (2 : ℝ) ^ m := by
  set t := 2 * (C * K + K + 4)
  set m₀ := 2 ^ t
  have ht4 : 4 ≤ t := by omega
  have hsq : t * t ≤ 2 ^ t := sq_le_two_pow t ht4
  have hCpow : C ≤ 2 ^ C := Nat.lt_two_pow_self.le
  have hbase : (C * m₀) ^ K ≤ 2 ^ m₀ := by
    have h1 : (C * m₀) ^ K ≤ (2 ^ C * 2 ^ t) ^ K :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_right m₀ hCpow) K
    have h2 : (2 ^ C * 2 ^ t) ^ K = 2 ^ (C * K + t * K) := by
      rw [← pow_add, ← pow_mul, add_mul]
    have h3 : C * K + t * K ≤ 2 ^ t := by
      have h1 : C * K ≤ t := by omega
      have h2 : K + 1 ≤ t := by omega
      have hle1 : C * K + t * K ≤ t * t := by nlinarith
      omega
    exact h1.trans (h2 ▸ Nat.pow_le_pow_right (by norm_num) h3)
  have hm0_ge : 2 * K ≤ m₀ := by
    have ht_def : t = 2 * (C * K + K + 4) := rfl
    have hle1 : 2 * K ≤ t * t := by nlinarith
    omega
  refine ⟨m₀, by positivity, ?_⟩
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact_mod_cast hbase
  | succ m hm ih =>
    have hm2K : 2 * K ≤ m := le_trans hm0_ge hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hratio : ((m + 1 : ℕ) : ℝ) ^ K ≤ 2 * (m : ℝ) ^ K := by
      have hdiv : ((m + 1 : ℕ) : ℝ) / (m : ℝ) = 1 + 1 / (m : ℝ) := by
        push_cast; field_simp
      have hstep : (1 + 1 / (m : ℝ)) ^ K ≤ 2 := by
        have h1 : (1 + 1 / (m : ℝ)) ^ K ≤ (Real.exp (1 / (m : ℝ))) ^ K :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / (m : ℝ))]) K
        rw [← Real.exp_nat_mul] at h1
        have h2 : (K : ℝ) * (1 / (m : ℝ)) ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ hmpos (by norm_num : (0 : ℝ) < 2)]
          have : (2 * K : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2K
          linarith
        have h3 : Real.exp ((K : ℝ) * (1 / (m : ℝ))) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr h2
        have h4 : Real.exp (1 / 2) ≤ 2 := by
          have hsqe : (Real.exp (1 / 2)) ^ 2 < 4 := by
            rw [← Real.exp_nat_mul]
            have : ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
            rw [this]
            linarith [Real.exp_one_lt_d9]
          nlinarith [Real.exp_pos (1 / 2)]
        exact h1.trans (h3.trans h4)
      have hmul := mul_le_mul_of_nonneg_right hstep (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ K)
      rw [← hdiv, div_pow, div_mul_cancel₀ _ (by positivity : (m : ℝ) ^ K ≠ 0)] at hmul
      exact hmul
    have hCpos : (0 : ℝ) ≤ (C : ℝ) ^ K := by positivity
    calc ((C * (m + 1) : ℕ) : ℝ) ^ K = (C : ℝ) ^ K * ((m + 1 : ℕ) : ℝ) ^ K := by
          push_cast; rw [mul_pow]
      _ ≤ (C : ℝ) ^ K * (2 * (m : ℝ) ^ K) := mul_le_mul_of_nonneg_left hratio hCpos
      _ = 2 * ((C * m : ℕ) : ℝ) ^ K := by push_cast; rw [mul_pow]; ring
      _ ≤ 2 * (2 : ℝ) ^ m := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 : ℝ) ^ (m + 1) := by rw [pow_succ']

def encFin (a : ℕ) (u : Fin (2 ^ a)) : List Bool :=
  List.ofFn (fun j : Fin a => u.val.testBit j.val)

theorem encFin_len (a : ℕ) (u : Fin (2 ^ a)) : (encFin a u).length = a := by
  simp [encFin]

theorem encFin_inj (a : ℕ) : Function.Injective (encFin a) := by
  intro u v h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < a
  · have h1 := congrArg (fun l : List Bool => l[j]?) h
    simp only [encFin, List.getElem?_ofFn, dif_pos hj, Option.some.injEq] at h1
    exact h1
  · have hu : u.val < 2 ^ j := lt_of_lt_of_le u.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hv : v.val < 2 ^ j := lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow hu, Nat.testBit_lt_two_pow hv]

def encX (a m : ℕ) (x : Fin m → Fin (2 ^ a)) : List Bool :=
  (List.ofFn (fun i : Fin m => encFin a (x i))).flatten

theorem encX_len (a m : ℕ) (x : Fin m → Fin (2 ^ a)) : (encX a m x).length = a * m := by
  simp only [encX, List.length_flatten, List.map_ofFn]
  have hfun : (List.length ∘ fun i : Fin m => encFin a (x i)) = fun _ => a := by
    ext i; exact encFin_len a (x i)
  rw [hfun, List.ofFn_const, List.sum_replicate, smul_eq_mul, mul_comm]

theorem encX_inj (a m : ℕ) : Function.Injective (encX a m) := by
  intro x y h
  ext i
  have hlen : ∀ (z : Fin m → Fin (2 ^ a)) (t : Fin m),
      ((encX a m z).drop (t.val * a)).take a = encFin a (z t) := by
    intro z t
    have hsplit : List.ofFn (fun j : Fin m => encFin a (z j)) =
        (List.ofFn (fun j : Fin m => encFin a (z j))).take t.val ++
        [encFin a (z t)] ++
        (List.ofFn (fun j : Fin m => encFin a (z j))).drop (t.val + 1) := by
      have h1 := List.take_append_drop t.val (List.ofFn (fun j : Fin m => encFin a (z j)))
      have h2 : (List.ofFn (fun j : Fin m => encFin a (z j))).drop t.val =
          encFin a (z t) :: (List.ofFn (fun j : Fin m => encFin a (z j))).drop (t.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simp [t.isLt])]
        simp
      rw [h2] at h1
      simpa [List.append_assoc] using h1.symm
    have hpre_len : ((List.ofFn (fun j : Fin m => encFin a (z j))).take t.val).flatten.length = t.val * a := by
      rw [List.length_flatten, List.map_take, List.map_ofFn]
      have hfun : (List.length ∘ fun j : Fin m => encFin a (z j)) = fun _ => a := by
        ext j; exact encFin_len a (z j)
      rw [hfun, List.ofFn_const, List.take_replicate, min_eq_left t.isLt.le, List.sum_replicate, smul_eq_mul]
    simp only [encX]
    conv_lhs => rw [hsplit]
    rw [List.flatten_append, List.flatten_append, List.flatten_singleton,
      List.append_assoc, List.drop_left' hpre_len, List.take_left' (encFin_len a (z t))]
  have heq : encFin a (x i) = encFin a (y i) := by
    rw [← hlen x i, ← hlen y i, h]
  exact congrArg Fin.val (encFin_inj a heq)

set_option maxHeartbeats 1600000 in
theorem main : ∀ (a k : Nat), 0 < a → 0 < k →
  ∃ m₀ : Nat, 0 < m₀ ∧ ∀ m : Nat, m₀ ≤ m →
    let A := Fin (2^a)
    let B := Fin k
    let X := Fin m → A
    let Y := Fin m → B
    ∀ f : Fin m → A → B → Bool,
    (∀ i u v, u ≠ v →
      (∃ j, f i u j = f i v j) ∧ (∃ j, f i u j ≠ f i v j)) →
    ∀ (left : X → Bool) (right : Y → Bool),
      let truth := fun (x : X) (y : Y) =>
        xor (xor (left x) (right y))
          (((Finset.univ : Finset (Fin m)).filter (fun i => f i (x i) (y i))).card % 2 == 1)
      let nx := (2^a)^m
      let pairs := (Finset.univ : Finset (X × Y))
      let ones := fun (y : Y) => ((Finset.univ : Finset X).filter (fun x => truth x y)).card
      let base : ℚ := ((∑ y : Y, max (ones y) (nx - ones y) : Nat) : ℚ) / pairs.card
      ∀ θ : ℚ, 0 ≤ θ → θ ≤ 1 →
        let costs : Set ℚ := {c | ∃ (r : Nat) (send : Fin r → X → List Bool)
          (read : Fin r → List Bool → Y → Bool),
          0 < r ∧
          (∀ z x x' tail, send z x ++ tail = send z x' → tail = []) ∧
          (base + (1-base)*θ) * (r : ℚ)*pairs.card ≤
            ((∑ z : Fin r, (pairs.filter
              (fun xy => read z (send z xy.1) xy.2 = truth xy.1 xy.2)).card : Nat) : ℚ) ∧
          c = ((∑ z : Fin r, ∑ x : X, (send z x).length : Nat) : ℚ) / ((r : ℚ)*nx)}
        IsLeast costs (θ*(a*m : Nat)) := by
  intro a k ha hk
  classical
  have hk2 : 2 ≤ k ∨ k = 1 := by omega
  by_cases hk1 : k = 1
  · subst hk1
    refine ⟨1, by norm_num, fun m hm => ?_⟩
    intro A B X Y f hf
    exfalso
    have h2a : 2 ≤ 2 ^ a := by
      have : 2 ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
      simpa using this
    obtain ⟨⟨j1, hj1⟩, ⟨j2, hj2⟩⟩ :=
      hf ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨1, by omega⟩ (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    have : j1 = j2 := Subsingleton.elim j1 j2
    exact hj2 (this ▸ hj1)
  have hk_ge2 : 2 ≤ k := by omega
  set Q : ℕ := 4 * k
  set ρ : ℝ := ((k - 2 : ℕ) : ℝ) / (k : ℝ)
  have hρ_nn : 0 ≤ ρ := by positivity
  have hρ_lt1 : ρ < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < (k : ℝ))]
    have : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by rw [Nat.cast_sub hk_ge2]; norm_num
    linarith
  have hδpos : (0 : ℝ) < 1 / (4 * (Q : ℝ) * ((2 ^ a : ℕ) : ℝ)) := by positivity
  obtain ⟨h0, hh0⟩ := exists_pow_lt_of_lt_one hδpos hρ_lt1
  set h : ℕ := h0 + 1
  have hh_pos : 1 ≤ h := Nat.succ_pos _
  have hρh_lt : ρ ^ h < 1 / (4 * (Q : ℝ) * ((2 ^ a : ℕ) : ℝ)) := by
    calc ρ ^ h = ρ ^ h0 * ρ := pow_succ ρ h0
      _ ≤ ρ ^ h0 * 1 := mul_le_mul_of_nonneg_left hρ_lt1.le (by positivity)
      _ = ρ ^ h0 := mul_one _
      _ < 1 / (4 * (Q : ℝ) * ((2 ^ a : ℕ) : ℝ)) := hh0
  have h1ρ_le : (1 + (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h) ^ (2 * Q) ≤ ((2 ^ a : ℕ) : ℝ) := by
    set x := (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h
    have hx_nn : 0 ≤ x := by
      have : (1 : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow a 2 (by norm_num)
      exact mul_nonneg (by linarith) (by positivity)
    have hx_le : x ≤ 1 / (4 * (Q : ℝ)) := by
      have h1 : (((2 ^ a : ℕ) : ℝ) - 1) ≤ ((2 ^ a : ℕ) : ℝ) := by linarith
      calc x ≤ ((2 ^ a : ℕ) : ℝ) * ρ ^ h := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ ((2 ^ a : ℕ) : ℝ) * (1 / (4 * (Q : ℝ) * ((2 ^ a : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hρh_lt.le (by positivity)
        _ = 1 / (4 * (Q : ℝ)) := by field_simp
    have hstep1 : (1 + x) ^ (2 * Q) ≤ (Real.exp x) ^ (2 * Q) :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) (2 * Q)
    rw [← Real.exp_nat_mul] at hstep1
    have hstep2 : ((2 * Q : ℕ) : ℝ) * x ≤ 1 / 2 := by
      have hQ0 : (Q : ℝ) ≠ 0 := by positivity
      calc ((2 * Q : ℕ) : ℝ) * x ≤ ((2 * Q : ℕ) : ℝ) * (1 / (4 * (Q : ℝ))) :=
            mul_le_mul_of_nonneg_left hx_le (by positivity)
        _ = 1 / 2 := by push_cast; field_simp; ring
    have hstep3 : Real.exp (1 / 2) ≤ 2 := by
      have hsqe : (Real.exp (1 / 2)) ^ 2 < 4 := by
        rw [← Real.exp_nat_mul]
        have : ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
        rw [this]
        linarith [Real.exp_one_lt_d9]
      nlinarith [Real.exp_pos (1 / 2), sq_nonneg (Real.exp (1 / 2))]
    have h2a : (2 : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := by
      have : 2 ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
      exact_mod_cast this
    exact hstep1.trans ((Real.exp_le_exp.mpr hstep2).trans (hstep3.trans h2a))
  have h8hQ : 1 ≤ 8 * h * Q := by
    have hQ1 : 1 ≤ Q := by omega
    nlinarith
  obtain ⟨m1, hm1_pos, hm1⟩ := exists_poly_le_two_pow (8 * a) (8 * h * Q) (by omega) h8hQ
  set m₀ := max m1 (Q + 2)
  refine ⟨m₀, by omega, fun m hm => ?_⟩
  have hm_ge_m1 : m1 ≤ m := le_trans (le_max_left _ _) hm
  have hm_ge_Q2 : Q + 2 ≤ m := le_trans (le_max_right _ _) hm
  have hm_pos : 0 < m := by omega
  intro A B X Y f hf left right truth nx pairs ones base θ hθ0 hθ1 costs
  have hcardX : Fintype.card X = nx := by simp [X, A, nx]
  have hcardY : Fintype.card Y = k ^ m := by simp [Y, B]
  have hcardP : pairs.card = nx * k ^ m := by
    simp only [pairs, card_univ, Fintype.card_prod, hcardX, hcardY]
  have hnx_pos : 0 < nx := by positivity
  have hny_pos : 0 < k ^ m := by positivity
  have hP_pos : 0 < pairs.card := by rw [hcardP]; positivity
  have hmem : θ * (a * m : ℕ) ∈ costs := by
    set q := θ.den
    set p := θ.num.toNat
    have hq_pos : 0 < q := θ.pos
    have hp_le_q : p ≤ q := by
      have hnum_nn : 0 ≤ θ.num := Rat.num_nonneg.mpr hθ0
      have hq_pos_q : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq_pos
      have hnum_le_q : (θ.num : ℚ) ≤ (q : ℚ) := by
        have h1 := hθ1
        rw [← Rat.num_div_den θ, div_le_one hq_pos_q] at h1
        exact h1
      have hnum_le : θ.num ≤ (q : ℤ) := by exact_mod_cast hnum_le_q
      omega
    have hθ_eq : θ = (p : ℚ) / (q : ℚ) := by
      have hnum_nn : 0 ≤ θ.num := Rat.num_nonneg.mpr hθ0
      have hp_int : (p : ℤ) = θ.num := Int.toNat_of_nonneg hnum_nn
      rw [← Rat.num_div_den θ, ← hp_int]
      simp [q]
    let decX : List Bool → X := fun l =>
      if h : ∃ x : X, encX a m x = l then h.choose else fun _ => ⟨0, by positivity⟩
    have hdec : ∀ x : X, decX (encX a m x) = x := by
      intro x
      have hex : ∃ x' : X, encX a m x' = encX a m x := ⟨x, rfl⟩
      simp only [decX, dif_pos hex]
      exact encX_inj a m hex.choose_spec
    let send : Fin q → X → List Bool := fun z x => if z.val < p then encX a m x else []
    let read : Fin q → List Bool → Y → Bool := fun z l y =>
      if z.val < p then truth (decX l) y else decide (nx - ones y ≤ ones y)
    refine ⟨q, send, read, hq_pos, ?_, ?_, ?_⟩
    · intro z x x' tail htail
      simp only [send] at htail
      split_ifs at htail with hz
      · have hlen := congrArg List.length htail
        simp only [List.length_append, encX_len] at hlen
        exact List.eq_nil_of_length_eq_zero (by omega)
      · simpa using htail
    · have hseed : ∀ z : Fin q,
          (pairs.filter (fun xy => read z (send z xy.1) xy.2 = truth xy.1 xy.2)).card =
          if z.val < p then pairs.card else ∑ y : Y, max (ones y) (nx - ones y) := by
        intro z
        by_cases hz : z.val < p
        · rw [if_pos hz]
          have hall : pairs.filter (fun xy => read z (send z xy.1) xy.2 = truth xy.1 xy.2) = pairs := by
            ext xy
            simp only [mem_filter, and_iff_left_iff_imp]
            intro _; simp [read, send, hz, hdec]
          rw [hall]
        · rw [if_neg hz]
          have hfib : (pairs.filter (fun xy => decide (nx - ones xy.2 ≤ ones xy.2) = truth xy.1 xy.2)).card
              = ∑ y : Y, ((Finset.univ : Finset X).filter
                  (fun x => decide (nx - ones y ≤ ones y) = truth x y)).card := by
            rw [Finset.card_filter]
            change ∑ xy : X × Y, _ = _
            rw [Fintype.sum_prod_type_right]
            refine Finset.sum_congr rfl (fun y _ => ?_)
            rw [Finset.card_filter]
          have hsimp : pairs.filter (fun xy => read z (send z xy.1) xy.2 = truth xy.1 xy.2) =
              pairs.filter (fun xy => decide (nx - ones xy.2 ≤ ones xy.2) = truth xy.1 xy.2) := by
            ext xy; simp [read, hz]
          rw [hsimp, hfib]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          by_cases h1 : nx - ones y ≤ ones y
          · rw [max_eq_left h1]
            simp [ones, h1]
          · rw [max_eq_right (by omega)]
            have hsp := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X))
              (fun x => truth x y = true)
            have hnot : (Finset.univ : Finset X).filter (fun x => decide (nx - ones y ≤ ones y) = truth x y)
                = (Finset.univ : Finset X).filter (fun x => ¬ truth x y = true) := by
              ext x; simp [h1]
            rw [hnot]
            simp only [card_univ, hcardX] at hsp
            change _ = nx - (Finset.univ.filter (fun x => truth x y = true)).card
            omega
      simp only [hseed, Finset.sum_ite]
      have hcp : (Finset.univ.filter (fun z : Fin q => z.val < p)).card = p := by
        let f_emb : Fin p → Fin q := fun i => ⟨i.val, by omega⟩
        have hbij : (Finset.univ.filter (fun z : Fin q => z.val < p)) =
            (Finset.univ : Finset (Fin p)).image f_emb := by
          ext z; simp only [mem_filter, mem_univ, true_and, mem_image, f_emb]
          constructor
          · intro hz; exact ⟨⟨z.val, hz⟩, Fin.ext rfl⟩
          · rintro ⟨i, rfl⟩; exact i.isLt
        rw [hbij, Finset.card_image_of_injective (Finset.univ : Finset (Fin p))
          (show Function.Injective f_emb from fun i j h => Fin.ext (by simpa [f_emb] using congrArg Fin.val h))]
        simp
      have hcq : (Finset.univ.filter (fun z : Fin q => ¬ z.val < p)).card = q - p := by
        have hsp := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin q)))
          (fun z => z.val < p)
        simp only [card_univ, Fintype.card_fin, hcp] at hsp
        omega
      simp only [Finset.sum_const, hcp, hcq, smul_eq_mul]
      have hP0 : (pairs.card : ℚ) ≠ 0 := by exact_mod_cast hP_pos.ne'
      have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq_pos.ne'
      rw [hθ_eq]
      simp only [base]
      push_cast [Nat.cast_sub hp_le_q]
      exact le_of_eq (by field_simp; ring)
    · have hlen : ∀ z : Fin q, ∑ x : X, (send z x).length = if z.val < p then a * m * nx else 0 := by
        intro z
        by_cases hz : z.val < p
        · simp only [send, if_pos hz, encX_len, Finset.sum_const, card_univ, hcardX, smul_eq_mul, mul_comm]
        · simp [send, hz]
      simp only [hlen, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
      have hcp : (Finset.univ.filter (fun z : Fin q => z.val < p)).card = p := by
        let f_emb : Fin p → Fin q := fun i => ⟨i.val, by omega⟩
        have hbij : (Finset.univ.filter (fun z : Fin q => z.val < p)) =
            (Finset.univ : Finset (Fin p)).image f_emb := by
          ext z; simp only [mem_filter, mem_univ, true_and, mem_image, f_emb]
          constructor
          · intro hz; exact ⟨⟨z.val, hz⟩, Fin.ext rfl⟩
          · rintro ⟨i, rfl⟩; exact i.isLt
        rw [hbij, Finset.card_image_of_injective (Finset.univ : Finset (Fin p))
          (show Function.Injective f_emb from fun i j h => Fin.ext (by simpa [f_emb] using congrArg Fin.val h))]
        simp
      rw [hcp, hθ_eq]
      have hnx0 : (nx : ℚ) ≠ 0 := by exact_mod_cast hnx_pos.ne'
      have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq_pos.ne'
      push_cast
      field_simp
  refine ⟨hmem, ?_⟩
  intro c hc
  obtain ⟨r, send, read, hr_pos, hpf, hacc, hceq⟩ := hc
  let Bfn : Finset X → ℝ := fun S => (∑ y : Y, |∑ x ∈ S, sgn (truth x y)|) / ((pairs.card : ℕ) : ℝ)
  have hB_nn : ∀ S, 0 ≤ Bfn S := fun S => div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)
  have hB_triv : ∀ S, Bfn S ≤ (S.card : ℝ) / (nx : ℝ) := by
    intro S
    have h1 : ∑ y : Y, |∑ x ∈ S, sgn (truth x y)| ≤ (k ^ m : ℝ) * (S.card : ℝ) := by
      calc ∑ y : Y, |∑ x ∈ S, sgn (truth x y)|
          ≤ ∑ _y : Y, (S.card : ℝ) := Finset.sum_le_sum (fun y _ => by
            calc |∑ x ∈ S, sgn (truth x y)| ≤ ∑ x ∈ S, |sgn (truth x y)| := Finset.abs_sum_le_sum_abs _ _
              _ = (S.card : ℝ) := by simp [abs_sgn])
        _ = (k ^ m : ℝ) * (S.card : ℝ) := by simp [hcardY]
    simp only [Bfn, hcardP]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hcorr : ∀ x x' : X, |∑ y : Y, sgn (truth x y) * sgn (truth x' y)|
      ≤ (k : ℝ) ^ m * ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card) := by
    intro x x'
    have hterm : ∀ y : Y, sgn (truth x y) * sgn (truth x' y) =
        sgn (left x) * sgn (left x') * ∏ i : Fin m, (if f i (x i) (y i) = f i (x' i) (y i) then (1 : ℝ) else -1) := by
      intro y
      simp only [truth, sgn_xor, sgn_parity]
      have h1 : sgn (right y) * sgn (right y) = 1 := sgn_sq _
      have h2 : (∏ i : Fin m, sgn (f i (x i) (y i))) * (∏ i : Fin m, sgn (f i (x' i) (y i)))
          = ∏ i : Fin m, (if f i (x i) (y i) = f i (x' i) (y i) then (1 : ℝ) else -1) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        cases f i (x i) (y i) <;> cases f i (x' i) (y i) <;> norm_num [sgn]
      calc sgn (left x) * sgn (right y) * (∏ i, sgn (f i (x i) (y i))) *
            (sgn (left x') * sgn (right y) * ∏ i, sgn (f i (x' i) (y i)))
          = sgn (left x) * sgn (left x') * (sgn (right y) * sgn (right y)) *
            ((∏ i, sgn (f i (x i) (y i))) * (∏ i, sgn (f i (x' i) (y i)))) := by ring
        _ = sgn (left x) * sgn (left x') * ∏ i, (if f i (x i) (y i) = f i (x' i) (y i) then 1 else -1) := by
          rw [h1, mul_one, h2]
    simp only [hterm, ← Finset.mul_sum, abs_mul, abs_sgn, one_mul]
    rw [← Fintype.prod_sum (fun i j => if f i (x i) j = f i (x' i) j then (1 : ℝ) else -1),
      Finset.abs_prod]
    have hcoord : ∀ i : Fin m,
        |∑ j : Fin k, (if f i (x i) j = f i (x' i) j then (1 : ℝ) else -1)|
        ≤ (k : ℝ) * (if x i ≠ x' i then ρ else 1) := by
      intro i
      by_cases hxi : x i = x' i
      · simp [hxi, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
      · rw [if_pos hxi]
        obtain ⟨⟨j1, hj1⟩, ⟨j2, hj2⟩⟩ := hf i (x i) (x' i) hxi
        set c := (Finset.univ.filter (fun j : Fin k => f i (x i) j = f i (x' i) j)).card
        have hc_ge1 : 1 ≤ c := Finset.card_pos.mpr ⟨j1, by simp [hj1]⟩
        have hc_le : c ≤ k - 1 := by
          have hsub : Finset.univ.filter (fun j : Fin k => f i (x i) j = f i (x' i) j)
              ⊆ Finset.univ.erase j2 := by
            intro j hj
            rw [mem_filter] at hj
            exact mem_erase.mpr ⟨fun heq => hj2 (heq ▸ hj.2), mem_univ j⟩
          have := Finset.card_le_card hsub
          rw [card_erase_of_mem (mem_univ j2), card_univ, Fintype.card_fin] at this
          exact this
        have hsum_eq : ∑ j : Fin k, (if f i (x i) j = f i (x' i) j then (1 : ℝ) else -1)
            = 2 * (c : ℝ) - (k : ℝ) := by
          have h1 : ∀ j : Fin k, (if f i (x i) j = f i (x' i) j then (1 : ℝ) else -1)
              = 2 * (if f i (x i) j = f i (x' i) j then (1 : ℝ) else 0) - 1 := by
            intro j; split_ifs <;> norm_num
          simp only [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
            Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, c]
        rw [hsum_eq]
        have hkρ : (k : ℝ) * ρ = (k : ℝ) - 2 := by
          simp only [ρ]; rw [mul_div_cancel₀ _ (by positivity : (k : ℝ) ≠ 0), Nat.cast_sub hk_ge2]; norm_num
        rw [hkρ, abs_le]
        have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_ge1
        have hc2 : (c : ℝ) ≤ (k : ℝ) - 1 := by
          have : c + 1 ≤ k := by omega
          have : (c : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast this
          linarith
        constructor <;> linarith
    calc ∏ i : Fin m, |∑ j : Fin k, (if f i (x i) j = f i (x' i) j then (1 : ℝ) else -1)|
        ≤ ∏ i : Fin m, ((k : ℝ) * (if x i ≠ x' i then ρ else 1)) :=
          prod_le_prod_nn _ _ _ (fun _ _ => abs_nonneg _) (fun i _ => hcoord i)
      _ = (k : ℝ) ^ m * ∏ i : Fin m, (if x i ≠ x' i then ρ else 1) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, card_univ, Fintype.card_fin]
      _ = (k : ℝ) ^ m * ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card) := by
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have hbias_sq : ∀ S : Finset X, S.Nonempty →
      (Bfn S / ((S.card : ℝ) / (nx : ℝ))) ^ 2 ≤
      (∑ x ∈ S, ∑ x' ∈ S, ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card)) / ((S.card : ℝ) ^ 2) := by
    intro S hS
    have hSpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
    have hny : (0 : ℝ) < (k : ℝ) ^ m := by positivity
    have hnxr : (0 : ℝ) < (nx : ℝ) := by exact_mod_cast hnx_pos
    have hsimp : Bfn S / ((S.card : ℝ) / (nx : ℝ)) =
        (∑ y : Y, |∑ x ∈ S, sgn (truth x y)|) / ((k : ℝ) ^ m * (S.card : ℝ)) := by
      simp only [Bfn, hcardP]
      push_cast
      field_simp
    rw [hsimp, div_pow]
    have hcs : (∑ y : Y, |∑ x ∈ S, sgn (truth x y)|) ^ 2 ≤
        (k : ℝ) ^ m * ∑ y : Y, (∑ x ∈ S, sgn (truth x y)) ^ 2 := by
      let g : Y → ℝ := fun y => |∑ x ∈ S, sgn (truth x y)|
      have h0 : 0 ≤ ∑ y : Y, ∑ y' : Y, (g y - g y') ^ 2 :=
        Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      have hA : ∑ y : Y, ∑ y' : Y, (g y - g y') ^ 2 =
          (∑ y : Y, ∑ _y' : Y, g y ^ 2) - (∑ y : Y, ∑ y' : Y, 2 * g y * g y') +
          (∑ _y : Y, ∑ y' : Y, g y' ^ 2) := by
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have h1 : ∑ y : Y, ∑ _y' : Y, g y ^ 2 = (Fintype.card Y : ℝ) * ∑ y : Y, g y ^ 2 := by
        simp only [Finset.sum_const, card_univ, nsmul_eq_mul, Finset.mul_sum]
      have h2 : ∑ _y : Y, ∑ y' : Y, g y' ^ 2 = (Fintype.card Y : ℝ) * ∑ y : Y, g y ^ 2 := by
        simp only [Finset.sum_const, card_univ, nsmul_eq_mul]
      have h3 : ∑ y : Y, ∑ y' : Y, 2 * g y * g y' = 2 * (∑ y : Y, g y) ^ 2 := by
        rw [sq, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y' _ => by ring)
      have hsq : ∑ y : Y, g y ^ 2 = ∑ y : Y, (∑ x ∈ S, sgn (truth x y)) ^ 2 :=
        Finset.sum_congr rfl (fun y _ => sq_abs _)
      have hcardYr : (Fintype.card Y : ℝ) = (k : ℝ) ^ m := by
        rw [hcardY]; push_cast; rfl
      rw [hA, h1, h2, h3, hsq, hcardYr] at h0
      linarith
    have hexp : ∑ y : Y, (∑ x ∈ S, sgn (truth x y)) ^ 2 =
        ∑ x ∈ S, ∑ x' ∈ S, ∑ y : Y, sgn (truth x y) * sgn (truth x' y) := by
      simp only [sq, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x' _ => Finset.sum_congr rfl (fun y _ => mul_comm _ _))
    have hbound : ∑ y : Y, (∑ x ∈ S, sgn (truth x y)) ^ 2 ≤
        (k : ℝ) ^ m * ∑ x ∈ S, ∑ x' ∈ S, ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card) := by
      rw [hexp, Finset.mul_sum]
      refine Finset.sum_le_sum (fun x _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun x' _ => (le_abs_self _).trans (hcorr x x'))
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hcs' : (∑ y : Y, |∑ x ∈ S, sgn (truth x y)|) ^ 2 ≤
        ((k : ℝ) ^ m) * ((k : ℝ) ^ m * ∑ x ∈ S, ∑ x' ∈ S, ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card)) := by
      calc (∑ y : Y, |∑ x ∈ S, sgn (truth x y)|) ^ 2
          ≤ (k : ℝ) ^ m * ∑ y : Y, (∑ x ∈ S, sgn (truth x y)) ^ 2 := hcs
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound hny.le
    nlinarith [sq_nonneg (S.card : ℝ)]
  have hgap : ∀ S : Finset X, 2 ≤ S.card → Bfn S / ((S.card : ℝ) / (nx : ℝ)) ≤ 1 - 1 / (Q : ℝ) := by
    intro S hS2
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    have hSpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
    have h1 := hbias_sq S hS
    have h2 : ∑ x ∈ S, ∑ x' ∈ S, ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card)
        ≤ (S.card : ℝ) + ((S.card : ℝ) ^ 2 - (S.card : ℝ)) * ρ := by
      have hinner : ∀ x ∈ S, ∑ x' ∈ S, ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card)
          ≤ 1 + ((S.card : ℝ) - 1) * ρ := by
        intro x hx
        rw [← Finset.add_sum_erase S _ hx]
        have hdiag : ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x i)).card) = 1 := by simp
        rw [hdiag]
        have hoff : ∑ x' ∈ S.erase x, ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card)
            ≤ ((S.card : ℝ) - 1) * ρ := by
          calc ∑ x' ∈ S.erase x, ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card)
              ≤ ∑ _x' ∈ S.erase x, ρ := Finset.sum_le_sum (fun x' hx' => by
                have hne : x ≠ x' := (mem_erase.mp hx').1.symm
                have hpos : 1 ≤ (Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card := by
                  obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
                    by_contra hall; push_neg at hall; exact hne (funext hall)
                  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
                simpa using pow_le_pow_of_le_one hρ_nn hρ_lt1.le hpos)
            _ = ((S.erase x).card : ℝ) * ρ := by rw [Finset.sum_const, nsmul_eq_mul]
            _ = ((S.card : ℝ) - 1) * ρ := by
                rw [card_erase_of_mem hx, Nat.cast_sub (by omega)]; norm_num
        linarith
      calc ∑ x ∈ S, ∑ x' ∈ S, ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card)
          ≤ ∑ _x ∈ S, (1 + ((S.card : ℝ) - 1) * ρ) := Finset.sum_le_sum hinner
        _ = (S.card : ℝ) * (1 + ((S.card : ℝ) - 1) * ρ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = (S.card : ℝ) + ((S.card : ℝ) ^ 2 - (S.card : ℝ)) * ρ := by ring
    have h3 : ((S.card : ℝ) + ((S.card : ℝ) ^ 2 - (S.card : ℝ)) * ρ) / ((S.card : ℝ) ^ 2)
        ≤ (1 + ρ) / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      have hS2r : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hS2
      nlinarith [mul_nonneg (sub_nonneg.mpr hS2r) (sub_nonneg.mpr hρ_lt1.le)]
    have h4 : (1 + ρ) / 2 ≤ (1 - 1 / (Q : ℝ)) ^ 2 := by
      have hkρ : ρ = 1 - 2 / (k : ℝ) := by
        simp only [ρ, Nat.cast_sub hk_ge2]; push_cast; field_simp
      rw [hkρ]
      have hQeq : (Q : ℝ) = 4 * (k : ℝ) := by simp [Q]
      rw [hQeq]
      have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
      have : (1 - 1 / (4 * (k : ℝ))) ^ 2 - (1 + (1 - 2 / (k : ℝ))) / 2 =
          1 / (2 * (k : ℝ)) + 1 / (16 * (k : ℝ) ^ 2) := by field_simp; ring
      have : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)) + 1 / (16 * (k : ℝ) ^ 2) := by positivity
      linarith
    have hsq_le : (Bfn S / ((S.card : ℝ) / (nx : ℝ))) ^ 2 ≤ (1 - 1 / (Q : ℝ)) ^ 2 :=
      h1.trans ((div_le_div_of_nonneg_right h2 (by positivity)).trans (h3.trans h4))
    have hnn1 : 0 ≤ Bfn S / ((S.card : ℝ) / (nx : ℝ)) := div_nonneg (hB_nn S) (by positivity)
    have hnn2 : 0 ≤ 1 - 1 / (Q : ℝ) := by
      have : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (show 1 ≤ Q by omega)
      have : 1 / (Q : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact this
      linarith
    nlinarith
  have hlarge : ∀ S : Finset X, nx < S.card ^ Q →
      Bfn S / ((S.card : ℝ) / (nx : ℝ)) ≤ 1 / (8 * ((a * m : ℕ) : ℝ) ^ 2) := by
    intro S hSQ
    have hS : S.Nonempty := Finset.card_pos.mp (by
      by_contra h0; have : S.card = 0 := by omega
      rw [this, zero_pow (by omega)] at hSQ; omega)
    have hSpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
    have h1 := hbias_sq S hS
    have h2 : ((∑ x ∈ S, ∑ x' ∈ S, ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card))
        / ((S.card : ℝ) ^ 2)) ^ h
        ≤ (∑ x ∈ S, ∑ x' ∈ S, (ρ ^ h) ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card))
          / ((S.card : ℝ) ^ 2) := by
      have hpm := pow_mean_le (S ×ˢ S) (hS.product hS)
        (fun p => ρ ^ ((Finset.univ.filter (fun i : Fin m => p.1 i ≠ p.2 i)).card))
        (fun _ _ => by positivity) h hh_pos
      simp only [Finset.card_product, Nat.cast_mul, Finset.sum_product] at hpm
      simp only [← sq] at hpm
      refine hpm.trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => ?_))
      rw [← pow_mul, mul_comm, pow_mul]
    have h3 : ∑ x ∈ S, ∑ x' ∈ S, (ρ ^ h) ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card)
        ≤ (S.card : ℝ) * (1 + (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h) ^ m := by
      have hinner : ∀ x : X, ∑ x' : X, (ρ ^ h) ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card)
          = (1 + (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h) ^ m := by
        intro x
        have hprod : ∀ x' : X, (ρ ^ h) ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card)
            = ∏ i : Fin m, (if x i = x' i then (1 : ℝ) else ρ ^ h) := by
          intro x'
          rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
        simp only [hprod]
        rw [← Fintype.prod_sum (fun i u => if x i = u then (1 : ℝ) else ρ ^ h)]
        have h1coord : ∀ i : Fin m, ∑ u : A, (if x i = u then (1 : ℝ) else ρ ^ h)
            = 1 + (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h := by
          intro i
          rw [← Finset.add_sum_erase Finset.univ _ (mem_univ (x i)), if_pos rfl]
          have hoff : ∑ u ∈ Finset.univ.erase (x i), (if x i = u then (1 : ℝ) else ρ ^ h)
              = (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h := by
            have hcon : ∀ u ∈ Finset.univ.erase (x i), (if x i = u then (1 : ℝ) else ρ ^ h) = ρ ^ h :=
              fun u hu => if_neg (mem_erase.mp hu).1.symm
            rw [Finset.sum_congr rfl hcon, Finset.sum_const, card_erase_of_mem (mem_univ _),
              card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (Nat.one_le_pow a 2 (by norm_num))]
            norm_num
          rw [hoff]
        simp only [h1coord, Finset.prod_const, card_univ, Fintype.card_fin]
      calc ∑ x ∈ S, ∑ x' ∈ S, (ρ ^ h) ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card)
          ≤ ∑ x ∈ S, ∑ x' : X, (ρ ^ h) ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card) :=
            Finset.sum_le_sum (fun x _ => Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity))
        _ = (S.card : ℝ) * (1 + (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h) ^ m := by
            simp only [hinner, Finset.sum_const, nsmul_eq_mul]
    have h4 : (Bfn S / ((S.card : ℝ) / (nx : ℝ))) ^ (2 * h)
        ≤ (1 + (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h) ^ m / (S.card : ℝ) := by
      rw [pow_mul]
      calc ((Bfn S / ((S.card : ℝ) / (nx : ℝ))) ^ 2) ^ h
          ≤ ((∑ x ∈ S, ∑ x' ∈ S, ρ ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card))
              / ((S.card : ℝ) ^ 2)) ^ h :=
            pow_le_pow_left₀ (sq_nonneg _) h1 h
        _ ≤ (∑ x ∈ S, ∑ x' ∈ S, (ρ ^ h) ^ ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card))
              / ((S.card : ℝ) ^ 2) := h2
        _ ≤ ((S.card : ℝ) * (1 + (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h) ^ m) / ((S.card : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right h3 (by positivity)
        _ = (1 + (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h) ^ m / (S.card : ℝ) := by field_simp
    have h5 : (Bfn S / ((S.card : ℝ) / (nx : ℝ))) ^ (4 * h * Q) ≤ (1 / 2 : ℝ) ^ m := by
      have hexp4 : 4 * h * Q = (2 * h) * (2 * Q) := by ring
      rw [hexp4, pow_mul]
      have hstep1 := pow_le_pow_left₀ (by positivity) h4 (2 * Q)
      conv_rhs at hstep1 => rw [div_pow, ← pow_mul, mul_comm m (2 * Q), pow_mul]
      have hnum : ((1 + (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h) ^ (2 * Q)) ^ m ≤ (nx : ℝ) := by
        have hnx_eq : (nx : ℝ) = (((2 ^ a : ℕ) : ℝ)) ^ m := by simp only [nx, Nat.cast_pow]
        have h1ρ_nn : 0 ≤ (1 + (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h) ^ (2 * Q) := by
          have : (1 : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow a 2 (by norm_num)
          exact pow_nonneg (by nlinarith [pow_nonneg hρ_nn h]) _
        rw [hnx_eq]
        exact pow_le_pow_left₀ h1ρ_nn h1ρ_le m
      have hden : ((nx : ℝ) ^ 2) ≤ (S.card : ℝ) ^ (2 * Q) := by
        have hSQr : (nx : ℝ) ≤ (S.card : ℝ) ^ Q := by exact_mod_cast hSQ.le
        rw [mul_comm 2 Q, pow_mul]
        exact pow_le_pow_left₀ (by positivity) hSQr 2
      have h2m : (2 : ℝ) ^ m ≤ (nx : ℝ) := by
        have : 2 ^ m ≤ (2 ^ a) ^ m := Nat.pow_le_pow_left (by
          have : 2 ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha; simpa using this) m
        exact_mod_cast this
      calc ((Bfn S / ((S.card : ℝ) / (nx : ℝ))) ^ (2 * h)) ^ (2 * Q)
          ≤ ((1 + (((2 ^ a : ℕ) : ℝ) - 1) * ρ ^ h) ^ (2 * Q)) ^ m / (S.card : ℝ) ^ (2 * Q) := hstep1
        _ ≤ (nx : ℝ) / ((nx : ℝ) ^ 2) := div_le_div₀ (by positivity) hnum (by positivity) hden
        _ = 1 / (nx : ℝ) := by field_simp
        _ ≤ 1 / (2 : ℝ) ^ m := one_div_le_one_div_of_le (by positivity) h2m
        _ = (1 / 2 : ℝ) ^ m := by rw [one_div_pow]
    have h6 : (1 / 2 : ℝ) ^ m ≤ (1 / (8 * ((a * m : ℕ) : ℝ) ^ 2)) ^ (4 * h * Q) := by
      have hpoly := hm1 m hm_ge_m1
      have hle_sq : (8 * ((a * m : ℕ) : ℝ) ^ 2) ^ (4 * h * Q) ≤ ((8 * a * m : ℕ) : ℝ) ^ (8 * h * Q) := by
        have hbase : 8 * ((a * m : ℕ) : ℝ) ^ 2 ≤ ((8 * a * m : ℕ) : ℝ) ^ 2 := by
          push_cast; nlinarith
        have hexp : 8 * h * Q = 2 * (4 * h * Q) := by ring
        conv_rhs => rw [hexp, pow_mul]
        exact pow_le_pow_left₀ (by positivity) hbase (4 * h * Q)
      have hle2m : (8 * ((a * m : ℕ) : ℝ) ^ 2) ^ (4 * h * Q) ≤ (2 : ℝ) ^ m := hle_sq.trans hpoly
      rw [one_div_pow, one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) hle2m
    have h7 := h5.trans h6
    have hnn : 0 ≤ Bfn S / ((S.card : ℝ) / (nx : ℝ)) := div_nonneg (hB_nn S) (by positivity)
    have hpow_pos : 0 < 4 * h * Q := by positivity
    by_contra hgt
    push_neg at hgt
    have := pow_lt_pow_left₀ hgt (by positivity) hpow_pos.ne'
    linarith
  have hBX_le : Bfn Finset.univ ≤ 1 / (8 * ((a * m : ℕ) : ℝ) ^ 2) := by
    have hSQ : nx < (Finset.univ : Finset X).card ^ Q := by
      simp only [card_univ, hcardX]
      have h2nx : 2 ≤ nx := by
        have : 2 ^ 1 ≤ (2 ^ a) ^ m := by
          rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
        simpa using this
      calc nx = nx ^ 1 := (pow_one nx).symm
        _ < nx ^ Q := Nat.pow_lt_pow_right h2nx (by omega)
    have := hlarge Finset.univ hSQ
    simp only [card_univ, hcardX, div_self (by positivity : (nx : ℝ) ≠ 0), div_one] at this
    exact this
  have ham_ge1 : (1 : ℝ) ≤ ((a * m : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ a * m by nlinarith)
  have hBX_lt1 : Bfn Finset.univ ≤ 1 / 8 := by
    calc Bfn Finset.univ ≤ 1 / (8 * ((a * m : ℕ) : ℝ) ^ 2) := hBX_le
      _ ≤ 1 / 8 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hbase_eq : (base : ℝ) = (1 + Bfn Finset.univ) / 2 := by
    simp only [base, Bfn]
    push_cast
    have hsum : ∑ y : Y, ((max (ones y) (nx - ones y) : ℕ) : ℝ) =
        ((pairs.card : ℕ) : ℝ) / 2 + (∑ y : Y, |∑ x : X, sgn (truth x y)|) / 2 := by
      have h1 : ∀ y : Y, ((max (ones y) (nx - ones y) : ℕ) : ℝ) =
          ((nx : ℝ) + |∑ x : X, sgn (truth x y)|) / 2 := by
        intro y
        have hle : ones y ≤ nx := by rw [← hcardX]; exact Finset.card_le_univ _
        rw [Nat.cast_max, Nat.cast_sub hle, ← hcardX]
        dsimp only [ones]
        exact max_ones_eq (fun x => truth x y)
      calc ∑ y : Y, ((max (ones y) (nx - ones y) : ℕ) : ℝ)
          = ∑ y : Y, (((nx : ℝ) + |∑ x : X, sgn (truth x y)|) / 2) := Finset.sum_congr rfl (fun y _ => h1 y)
        _ = (∑ _y : Y, (nx : ℝ)) / 2 + (∑ y : Y, |∑ x : X, sgn (truth x y)|) / 2 := by
              rw [sum_add_div_two, add_div]
        _ = ((pairs.card : ℕ) : ℝ) / 2 + (∑ y : Y, |∑ x : X, sgn (truth x y)|) / 2 := by
              have hleft : ∑ _y : Y, (nx : ℝ) = ((pairs.card : ℕ) : ℝ) := by
                simp only [Finset.sum_const, card_univ, hcardY, nsmul_eq_mul, hcardP, Nat.cast_mul]
                ring
              rw [hleft]
    have hsum' : ∑ y : Y, max ((ones y : ℕ) : ℝ) (((nx - ones y : ℕ) : ℝ)) =
        ((pairs.card : ℕ) : ℝ) / 2 + (∑ y : Y, |∑ x : X, sgn (truth x y)|) / 2 := by
      simpa only [Nat.cast_max] using hsum
    rw [hsum']
    have hP0 : ((pairs.card : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hP_pos.ne'
    field_simp
  have hdet : ∀ z : Fin r,
      ((pairs.filter (fun xy => read z (send z xy.1) xy.2 = truth xy.1 xy.2)).card : ℝ)
        - (base : ℝ) * (pairs.card : ℝ)
      ≤ (1 - (base : ℝ)) * (pairs.card : ℝ) *
        ((∑ x : X, (send z x).length : ℕ) : ℝ) / (((a * m : ℕ) : ℝ) * (nx : ℝ)) := by
    intro z
    set img := Finset.univ.image (send z)
    let cls : List Bool → Finset X := fun w => Finset.univ.filter (fun x => send z x = w)
    let wt : List Bool → ℝ := fun w => ((cls w).card : ℝ) / (nx : ℝ)
    have hcls_ne : ∀ w ∈ img, (cls w).Nonempty := by
      intro w hw; obtain ⟨x, _, rfl⟩ := mem_image.mp hw; exact ⟨x, by simp [cls]⟩
    have hwt_pos : ∀ w ∈ img, 0 < wt w := fun w hw =>
      div_pos (by exact_mod_cast (hcls_ne w hw).card_pos) (by exact_mod_cast hnx_pos)
    have hsum_cls : ∑ w ∈ img, (cls w).card = nx := by
      rw [← hcardX, ← Finset.card_univ]
      exact (Finset.card_eq_sum_card_fiberwise (f := send z) (s := Finset.univ) (t := img)
        (fun x _ => mem_image_of_mem _ (mem_univ x))).symm
    have hwt_sum : ∑ w ∈ img, wt w = 1 := by
      calc ∑ w ∈ img, wt w = (∑ w ∈ img, ((cls w).card : ℝ)) / (nx : ℝ) := by
            simp only [wt, div_eq_mul_inv, ← Finset.sum_mul]
        _ = ((∑ w ∈ img, (cls w).card : ℕ) : ℝ) / (nx : ℝ) := by rw [Nat.cast_sum]
        _ = (nx : ℝ) / (nx : ℝ) := by rw [hsum_cls]
        _ = 1 := div_self (by positivity)
    have hacc_z : ((pairs.filter (fun xy => read z (send z xy.1) xy.2 = truth xy.1 xy.2)).card : ℝ)
        ≤ (pairs.card : ℝ) * (1 + ∑ w ∈ img, Bfn (cls w)) / 2 := by
      have hsplit : (pairs.filter (fun xy => read z (send z xy.1) xy.2 = truth xy.1 xy.2)).card =
          ∑ y : Y, ∑ w ∈ img, ((cls w).filter (fun x => read z w y = truth x y)).card := by
        rw [Finset.card_filter]
        change ∑ xy : X × Y, _ = _
        rw [Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← Finset.sum_fiberwise_of_maps_to (g := send z) (t := img) (fun x _ => mem_image_of_mem _ (mem_univ x))]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl (fun x hx => ?_)
        have hwx : send z x = w := (mem_filter.mp hx).2
        simp [hwx]
      rw [hsplit]
      push_cast
      have hle : ∑ y : Y, ∑ w ∈ img, (((cls w).filter (fun x => read z w y = truth x y)).card : ℝ)
          ≤ ∑ y : Y, ∑ w ∈ img, (((cls w).card : ℝ) + |∑ x ∈ cls w, sgn (truth x y)|) / 2 :=
        Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun w _ => acc_le_bias (cls w) (fun x => truth x y) (read z w y)))
      refine hle.trans (le_of_eq ?_)
      have hleft : ∑ y : Y, ∑ w ∈ img, ((cls w).card : ℝ) = (pairs.card : ℝ) := by
        have hinner : ∑ w ∈ img, ((cls w).card : ℝ) = (nx : ℝ) := by
          rw [← Nat.cast_sum, hsum_cls]
        simp only [hinner, Finset.sum_const, card_univ, hcardY, nsmul_eq_mul, hcardP, Nat.cast_mul]
        ring
      have hright : ∑ y : Y, ∑ w ∈ img, |∑ x ∈ cls w, sgn (truth x y)| =
          (pairs.card : ℝ) * ∑ w ∈ img, Bfn (cls w) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        simp only [Bfn]
        exact (mul_div_cancel₀ _ (by exact_mod_cast hP_pos.ne' : ((pairs.card : ℕ) : ℝ) ≠ 0)).symm
      calc ∑ y : Y, ∑ w ∈ img, (((cls w).card : ℝ) + |∑ x ∈ cls w, sgn (truth x y)|) / 2
          = ((∑ y : Y, ∑ w ∈ img, ((cls w).card : ℝ)) +
              (∑ y : Y, ∑ w ∈ img, |∑ x ∈ cls w, sgn (truth x y)|)) / 2 := by
              simp_rw [sum_add_div_two]
        _ = ((pairs.card : ℝ) + (pairs.card : ℝ) * ∑ w ∈ img, Bfn (cls w)) / 2 := by
              rw [hleft, hright]
        _ = (pairs.card : ℝ) * (1 + ∑ w ∈ img, Bfn (cls w)) / 2 := by ring
    have hL_eq : ((∑ x : X, (send z x).length : ℕ) : ℝ) / (((a * m : ℕ) : ℝ) * (nx : ℝ))
        = (∑ w ∈ img, wt w * (w.length : ℝ)) / ((a * m : ℕ) : ℝ) := by
      have h1 : ∑ x : X, (send z x).length = ∑ w ∈ img, (cls w).card * w.length := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := send z) (t := img) (fun x _ => mem_image_of_mem _ (mem_univ x))]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        have hcon : ∀ x ∈ cls w, (send z x).length = w.length := fun x hx => by rw [(mem_filter.mp hx).2]
        rw [Finset.sum_congr rfl hcon, Finset.sum_const, smul_eq_mul]
      have h2 : ∑ w ∈ img, wt w * (w.length : ℝ) = (∑ w ∈ img, ((cls w).card : ℝ) * (w.length : ℝ)) / (nx : ℝ) := by
        simp only [wt, div_eq_mul_inv, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        ring
      rw [h1, h2, div_div, mul_comm (nx : ℝ) ((a * m : ℕ) : ℝ)]
      congr 1
      simp only [Nat.cast_sum, Nat.cast_mul]
    have hred : (∑ w ∈ img, Bfn (cls w)) - Bfn Finset.univ
        ≤ (1 - Bfn Finset.univ) * ((∑ w ∈ img, wt w * (w.length : ℝ)) / ((a * m : ℕ) : ℝ)) := by
      by_cases hbig : ∃ w0 ∈ img, 1 - 1 / (2 * ((a * m : ℕ) : ℝ)) < wt w0
      · obtain ⟨w0, hw0, hwt0⟩ := hbig
        by_cases hcard1 : img.card = 1
        · obtain ⟨w1, hw1⟩ := Finset.card_eq_one.mp hcard1
          have hcls1 : cls w1 = Finset.univ := by
            ext x
            simp only [cls, mem_filter, mem_univ, true_and, iff_true]
            have : send z x ∈ img := mem_image_of_mem _ (mem_univ x)
            rw [hw1, mem_singleton] at this
            exact this
          have hnn_sum : 0 ≤ ∑ w ∈ img, wt w * (w.length : ℝ) :=
            Finset.sum_nonneg (fun w hw => mul_nonneg (hwt_pos w hw).le (Nat.cast_nonneg _))
          rw [hw1, Finset.sum_singleton, hcls1, sub_self]
          exact mul_nonneg (by linarith) (div_nonneg (by rwa [← hw1]) (by positivity))
        · have hlen_ge1 : ∀ w ∈ img, 1 ≤ w.length := by
            intro w hw
            by_contra h0
            have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
            obtain ⟨x0, _, hx0⟩ := mem_image.mp hw
            have hall : ∀ x : X, send z x = [] := fun x =>
              hpf z x0 x (send z x) (by rw [hx0, hnil, List.nil_append])
            have himg1 : img = {[]} := by
              ext u; simp only [img, mem_image, mem_univ, true_and, mem_singleton]
              constructor
              · rintro ⟨x, rfl⟩; exact hall x
              · rintro rfl; exact ⟨x0, hall x0⟩
            exact hcard1 (by rw [himg1, card_singleton])
          have hL_ge : 1 / ((a * m : ℕ) : ℝ) ≤ (∑ w ∈ img, wt w * (w.length : ℝ)) / ((a * m : ℕ) : ℝ) := by
            rw [div_le_div_iff_of_pos_right (by positivity)]
            calc (1 : ℝ) = ∑ w ∈ img, wt w := hwt_sum.symm
              _ ≤ ∑ w ∈ img, wt w * (w.length : ℝ) := Finset.sum_le_sum (fun w hw => by
                have h1 : (1 : ℝ) ≤ (w.length : ℝ) := by exact_mod_cast hlen_ge1 w hw
                nlinarith [hwt_pos w hw])
          have hw0_large : nx < (cls w0).card ^ Q := by
            have hhalf : (nx : ℝ) / 2 < ((cls w0).card : ℝ) := by
              have h1 : 1 / 2 < wt w0 := by
                have : 1 / (2 * ((a * m : ℕ) : ℝ)) ≤ 1 / 2 := by
                  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
                linarith
              simp only [wt, lt_div_iff₀ (by positivity : (0 : ℝ) < (nx : ℝ))] at h1
              linarith
            have h2c : nx < 2 * (cls w0).card := by
              have : (nx : ℝ) < 2 * ((cls w0).card : ℝ) := by linarith
              exact_mod_cast this
            have h2Q : 2 ^ Q < nx := by
              have hlt : Q < a * m := by nlinarith
              calc 2 ^ Q < 2 ^ (a * m) := Nat.pow_lt_pow_right (by norm_num) hlt
                _ = nx := by simp only [nx, pow_mul]
            have h1 : nx ^ Q < (2 * (cls w0).card) ^ Q := Nat.pow_lt_pow_left h2c (by omega)
            rw [mul_pow] at h1
            have h2 : nx * 2 ^ Q < nx * nx := Nat.mul_lt_mul_of_pos_left h2Q hnx_pos
            have h3 : nx ^ 2 ≤ nx ^ Q := Nat.pow_le_pow_right hnx_pos (by omega)
            have h4 : nx * 2 ^ Q < 2 ^ Q * (cls w0).card ^ Q := by
              calc nx * 2 ^ Q < nx * nx := h2
                _ = nx ^ 2 := (sq nx).symm
                _ ≤ nx ^ Q := h3
                _ < 2 ^ Q * (cls w0).card ^ Q := h1
            exact Nat.lt_of_mul_lt_mul_left (by rwa [mul_comm] at h4)
          have hB0 : Bfn (cls w0) ≤ 1 / (8 * ((a * m : ℕ) : ℝ)) := by
            have h1 := hlarge (cls w0) hw0_large
            have hwt_le1 : wt w0 ≤ 1 := by
              have : (cls w0).card ≤ nx := by rw [← hcardX]; exact Finset.card_le_univ _
              simp only [wt, div_le_one (by positivity : (0 : ℝ) < (nx : ℝ))]
              exact_mod_cast this
            have h2 : Bfn (cls w0) ≤ wt w0 * (1 / (8 * ((a * m : ℕ) : ℝ) ^ 2)) := by
              rwa [div_le_iff₀ (hwt_pos w0 hw0), mul_comm] at h1
            calc Bfn (cls w0) ≤ 1 * (1 / (8 * ((a * m : ℕ) : ℝ) ^ 2)) :=
                  h2.trans (mul_le_mul_of_nonneg_right hwt_le1 (by positivity))
              _ ≤ 1 / (8 * ((a * m : ℕ) : ℝ)) := by
                  rw [one_mul, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
          have hBrest : ∑ w ∈ img.erase w0, Bfn (cls w) ≤ 1 / (2 * ((a * m : ℕ) : ℝ)) := by
            calc ∑ w ∈ img.erase w0, Bfn (cls w)
                ≤ ∑ w ∈ img.erase w0, wt w := Finset.sum_le_sum (fun w _ => hB_triv (cls w))
              _ = 1 - wt w0 := by
                  have := Finset.add_sum_erase img wt hw0
                  linarith
              _ ≤ 1 / (2 * ((a * m : ℕ) : ℝ)) := by linarith
          have hLHS : (∑ w ∈ img, Bfn (cls w)) - Bfn Finset.univ ≤ 5 / (8 * ((a * m : ℕ) : ℝ)) := by
            rw [← Finset.add_sum_erase img (fun w => Bfn (cls w)) hw0]
            have hnn := hB_nn Finset.univ
            have : 1 / (8 * ((a * m : ℕ) : ℝ)) + 1 / (2 * ((a * m : ℕ) : ℝ)) = 5 / (8 * ((a * m : ℕ) : ℝ)) := by
              field_simp; ring
            linarith
          have hRHS : 7 / (8 * ((a * m : ℕ) : ℝ)) ≤
              (1 - Bfn Finset.univ) * ((∑ w ∈ img, wt w * (w.length : ℝ)) / ((a * m : ℕ) : ℝ)) := by
            calc 7 / (8 * ((a * m : ℕ) : ℝ)) = (7 / 8) * (1 / ((a * m : ℕ) : ℝ)) := by ring
              _ ≤ (1 - Bfn Finset.univ) * ((∑ w ∈ img, wt w * (w.length : ℝ)) / ((a * m : ℕ) : ℝ)) :=
                mul_le_mul (by linarith) hL_ge (by positivity) (by linarith)
          have h57 : 5 / (8 * ((a * m : ℕ) : ℝ)) ≤ 7 / (8 * ((a * m : ℕ) : ℝ)) :=
            div_le_div_of_nonneg_right (by norm_num) (by positivity)
          linarith
      · push_neg at hbig
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hnx2 : (nx : ℝ) = (2 : ℝ) ^ (a * m) := by
          have : nx = 2 ^ (a * m) := by simp only [nx, pow_mul]
          rw [this]; push_cast; rfl
        have hpt : ∀ w ∈ img, Bfn (cls w) ≤ wt w * (Real.log (1 / wt w) / (Real.log 2 * ((a * m : ℕ) : ℝ))) := by
          intro w hw
          have hwt_p := hwt_pos w hw
          rw [mul_comm (wt w), ← div_le_iff₀ hwt_p]
          by_cases hs1 : (cls w).card = 1
          · have hwt1 : 1 / wt w = (2 : ℝ) ^ (a * m) := by
              have : wt w = 1 / (nx : ℝ) := by simp only [wt, hs1, Nat.cast_one]
              rw [this, one_div_one_div, hnx2]
            rw [hwt1, Real.log_pow]
            have h1 : ((a * m : ℕ) : ℝ) * Real.log 2 / (Real.log 2 * ((a * m : ℕ) : ℝ)) = 1 := by
              field_simp
            rw [h1]
            have := hB_triv (cls w)
            rwa [div_le_one hwt_p]
          · have hs2 : 2 ≤ (cls w).card := by have := (hcls_ne w hw).card_pos; omega
            by_cases hsmall : (cls w).card ^ Q ≤ nx
            · have hle1 := hgap (cls w) hs2
              have hlog_ge : 1 - 1 / (Q : ℝ) ≤ Real.log (1 / wt w) / (Real.log 2 * ((a * m : ℕ) : ℝ)) := by
                have hpow_ge : (2 : ℝ) ^ (a * m * (Q - 1)) ≤ (1 / wt w) ^ Q := by
                  have h1 : (nx : ℝ) ^ Q = (2 : ℝ) ^ (a * m * Q) := by
                    rw [hnx2, ← pow_mul]
                  have h2 : ((cls w).card : ℝ) ^ Q ≤ (2 : ℝ) ^ (a * m) := by
                    rw [← hnx2]; exact_mod_cast hsmall
                  have h3 : (1 / wt w) ^ Q = (nx : ℝ) ^ Q / ((cls w).card : ℝ) ^ Q := by
                    simp only [wt, one_div, inv_div, div_pow]
                  rw [h3, h1, le_div_iff₀ (by positivity)]
                  calc (2 : ℝ) ^ (a * m * (Q - 1)) * ((cls w).card : ℝ) ^ Q
                      ≤ (2 : ℝ) ^ (a * m * (Q - 1)) * (2 : ℝ) ^ (a * m) :=
                        mul_le_mul_of_nonneg_left h2 (by positivity)
                    _ = (2 : ℝ) ^ (a * m * (Q - 1) + a * m) := (pow_add _ _ _).symm
                    _ = (2 : ℝ) ^ (a * m * Q) := by
                        congr 1
                        have : Q - 1 + 1 = Q := by omega
                        calc a * m * (Q - 1) + a * m = a * m * (Q - 1 + 1) := by ring
                          _ = a * m * Q := by rw [this]
                have hlog_pow := Real.log_le_log (by positivity) hpow_ge
                rw [Real.log_pow, Real.log_pow] at hlog_pow
                rw [le_div_iff₀ (by positivity)]
                have hQpos : (0 : ℝ) < (Q : ℝ) := by positivity
                have hQsub : ((Q - 1 : ℕ) : ℝ) = (Q : ℝ) - 1 := by
                  rw [Nat.cast_sub (by omega : 1 ≤ Q)]; norm_num
                have hmulQ : (Q : ℝ) * ((1 - 1 / (Q : ℝ)) * (Real.log 2 * ((a * m : ℕ) : ℝ))) =
                    ((a * m * (Q - 1) : ℕ) : ℝ) * Real.log 2 := by
                  push_cast [hQsub]; field_simp
                nlinarith
              exact hle1.trans hlog_ge
            · push_neg at hsmall
              have hle1 := hlarge (cls w) hsmall
              have hlog_ge : 1 / (2 * ((a * m : ℕ) : ℝ) ^ 2) ≤
                  Real.log (1 / wt w) / (Real.log 2 * ((a * m : ℕ) : ℝ)) := by
                have h1 : 1 - wt w ≤ Real.log (1 / wt w) := by
                  have := Real.log_le_sub_one_of_pos hwt_p
                  rw [Real.log_div one_ne_zero hwt_p.ne', Real.log_one, zero_sub]
                  linarith
                have h2 : 1 / (2 * ((a * m : ℕ) : ℝ)) ≤ Real.log (1 / wt w) := by
                  have := hbig w hw
                  linarith
                have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
                rw [div_le_div_iff₀ (by positivity) (by positivity)]
                calc 1 * (Real.log 2 * ((a * m : ℕ) : ℝ)) ≤ 1 * (1 * ((a * m : ℕ) : ℝ)) := by nlinarith
                  _ = (1 / (2 * ((a * m : ℕ) : ℝ))) * (2 * ((a * m : ℕ) : ℝ) ^ 2) := by field_simp
                  _ ≤ Real.log (1 / wt w) * (2 * ((a * m : ℕ) : ℝ) ^ 2) :=
                    mul_le_mul_of_nonneg_right h2 (by positivity)
              have h82 : 1 / (8 * ((a * m : ℕ) : ℝ) ^ 2) ≤ 1 / (2 * ((a * m : ℕ) : ℝ) ^ 2) := by
                rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
              exact hle1.trans (h82.trans hlog_ge)
        set H := (∑ w ∈ img, wt w * (Real.log (1 / wt w) / Real.log 2)) / ((a * m : ℕ) : ℝ)
        have hBsum_le_H : ∑ w ∈ img, Bfn (cls w) ≤ H := by
          calc ∑ w ∈ img, Bfn (cls w)
              ≤ ∑ w ∈ img, wt w * (Real.log (1 / wt w) / (Real.log 2 * ((a * m : ℕ) : ℝ))) :=
                Finset.sum_le_sum hpt
            _ = H := by
                show ∑ w ∈ img, wt w * (Real.log (1 / wt w) / (Real.log 2 * ((a * m : ℕ) : ℝ))) =
                  (∑ w ∈ img, wt w * (Real.log (1 / wt w) / Real.log 2)) / ((a * m : ℕ) : ℝ)
                simp only [div_eq_mul_inv, Finset.sum_mul]
                refine Finset.sum_congr rfl (fun w _ => ?_)
                rw [mul_inv]
                ring
        have hH_le1 : H ≤ 1 := by
          rw [div_le_one (by positivity)]
          calc ∑ w ∈ img, wt w * (Real.log (1 / wt w) / Real.log 2)
              ≤ ∑ w ∈ img, wt w * ((a * m : ℕ) : ℝ) := Finset.sum_le_sum (fun w hw => by
                apply mul_le_mul_of_nonneg_left _ (hwt_pos w hw).le
                rw [div_le_iff₀ hlog2_pos]
                have h1 : 1 / wt w ≤ (2 : ℝ) ^ (a * m) := by
                  have hge1 : (1 : ℝ) ≤ ((cls w).card : ℝ) := by exact_mod_cast (hcls_ne w hw).card_pos
                  have hdiv : 1 / wt w = (nx : ℝ) / ((cls w).card : ℝ) := by
                    show 1 / (((cls w).card : ℝ) / (nx : ℝ)) = _
                    rw [one_div_div]
                  rw [hdiv, div_le_iff₀ (by positivity), hnx2]
                  nlinarith
                have hlog1 := Real.log_le_log (by positivity) h1
                rwa [Real.log_pow] at hlog1)
            _ = ((a * m : ℕ) : ℝ) := by rw [← Finset.sum_mul, hwt_sum, one_mul]
        have hH_le_L : H ≤ (∑ w ∈ img, wt w * (w.length : ℝ)) / ((a * m : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (gibbs_kraft img wt hwt_pos hwt_sum (kraft_ineq (send z) (hpf z))) (by positivity)
        have hBX_nn := hB_nn Finset.univ
        calc (∑ w ∈ img, Bfn (cls w)) - Bfn Finset.univ
            ≤ H - Bfn Finset.univ := by linarith
          _ ≤ H - Bfn Finset.univ * H := by nlinarith
          _ = (1 - Bfn Finset.univ) * H := by ring
          _ ≤ (1 - Bfn Finset.univ) * ((∑ w ∈ img, wt w * (w.length : ℝ)) / ((a * m : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hH_le_L (by linarith)
    rw [mul_div_assoc, hL_eq, hbase_eq]
    have hPnn : (0 : ℝ) ≤ (pairs.card : ℝ) := by positivity
    nlinarith
  have hsum_det := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hdet z)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum_det
  have hsum_det' :
      (∑ z : Fin r, ((pairs.filter (fun xy => read z (send z xy.1) xy.2 = truth xy.1 xy.2)).card : ℝ)) -
        (r : ℝ) * ((base : ℝ) * (pairs.card : ℝ)) ≤
      (1 - (base : ℝ)) * (pairs.card : ℝ) *
        (∑ z : Fin r, ((∑ x : X, (send z x).length : ℕ) : ℝ)) / (((a * m : ℕ) : ℝ) * (nx : ℝ)) := by
    refine hsum_det.trans_eq ?_
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hacc_r : ((base : ℝ) + (1 - (base : ℝ)) * (θ : ℝ)) * (r : ℝ) * (pairs.card : ℝ)
      ≤ ∑ z : Fin r, ((pairs.filter (fun xy => read z (send z xy.1) xy.2 = truth xy.1 xy.2)).card : ℝ) := by
    have h1 : (((base + (1 - base) * θ) * (r : ℚ) * pairs.card : ℚ) : ℝ) ≤
        (((∑ z : Fin r, (pairs.filter (fun xy => read z (send z xy.1) xy.2 = truth xy.1 xy.2)).card : ℕ) : ℚ) : ℝ) := by
      exact_mod_cast hacc
    simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_sub, Rat.cast_one, Rat.cast_natCast,
      Nat.cast_sum, Rat.cast_sum] at h1
    exact h1
  have hceq_r : (c : ℝ) = (∑ z : Fin r, ((∑ x : X, (send z x).length : ℕ) : ℝ)) / ((r : ℝ) * (nx : ℝ)) := by
    have h1 : (c : ℝ) = ((((∑ z : Fin r, ∑ x : X, (send z x).length : ℕ) : ℚ) / ((r : ℚ) * nx) : ℚ) : ℝ) := by
      rw [hceq]
    simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Nat.cast_sum, Rat.cast_sum] at h1
    simpa only [Nat.cast_sum] using h1
  have h1mb : (0 : ℝ) < 1 - (base : ℝ) := by rw [hbase_eq]; linarith
  have hden_pos : (0 : ℝ) < (1 - (base : ℝ)) * (r : ℝ) * (pairs.card : ℝ) := by
    have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr_pos
    have hP' : (0 : ℝ) < (pairs.card : ℝ) := by exact_mod_cast hP_pos
    positivity
  have hgoal_r : (θ : ℝ) * ((a * m : ℕ) : ℝ) ≤ (c : ℝ) := by
    have h1 : (1 - (base : ℝ)) * (r : ℝ) * (pairs.card : ℝ) * (θ : ℝ) ≤
        (1 - (base : ℝ)) * (pairs.card : ℝ) *
          (∑ z : Fin r, ((∑ x : X, (send z x).length : ℕ) : ℝ)) / (((a * m : ℕ) : ℝ) * (nx : ℝ)) := by
      have hexp : ((base : ℝ) + (1 - (base : ℝ)) * (θ : ℝ)) * (r : ℝ) * (pairs.card : ℝ) =
          (r : ℝ) * ((base : ℝ) * (pairs.card : ℝ)) + (1 - (base : ℝ)) * (r : ℝ) * (pairs.card : ℝ) * (θ : ℝ) := by
        ring
      linarith
    have h2 : (1 - (base : ℝ)) * (pairs.card : ℝ) *
          (∑ z : Fin r, ((∑ x : X, (send z x).length : ℕ) : ℝ)) / (((a * m : ℕ) : ℝ) * (nx : ℝ))
        = (1 - (base : ℝ)) * (r : ℝ) * (pairs.card : ℝ) * ((c : ℝ) / ((a * m : ℕ) : ℝ)) := by
      rw [hceq_r]
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr_pos.ne'
      have hnx0 : (nx : ℝ) ≠ 0 := by exact_mod_cast hnx_pos.ne'
      have ham0 : ((a * m : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [h2] at h1
    have h3 : (θ : ℝ) ≤ (c : ℝ) / ((a * m : ℕ) : ℝ) := le_of_mul_le_mul_left h1 hden_pos
    rwa [le_div_iff₀ (by positivity)] at h3
  have hgoal_q : ((θ * ((a * m : ℕ) : ℚ) : ℚ) : ℝ) ≤ (c : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_natCast] using hgoal_r
  exact Rat.cast_le.mp hgoal_q

end PEqualNP.Outside.L_lib_928_aux

theorem PEqualNP.Outside.L_lib_928 : ∀ (a k : Nat), 0 < a → 0 < k →
  ∃ m₀ : Nat, 0 < m₀ ∧ ∀ m : Nat, m₀ ≤ m →
    let A := Fin (2^a)
    let B := Fin k
    let X := Fin m → A
    let Y := Fin m → B
    ∀ f : Fin m → A → B → Bool,
    (∀ i u v, u ≠ v →
      (∃ j, f i u j = f i v j) ∧ (∃ j, f i u j ≠ f i v j)) →
    ∀ (left : X → Bool) (right : Y → Bool),
      let truth := fun (x : X) (y : Y) =>
        xor (xor (left x) (right y))
          (((Finset.univ : Finset (Fin m)).filter (fun i => f i (x i) (y i))).card % 2 == 1)
      let nx := (2^a)^m
      let pairs := (Finset.univ : Finset (X × Y))
      let ones := fun (y : Y) => ((Finset.univ : Finset X).filter (fun x => truth x y)).card
      let base : ℚ := ((∑ y : Y, max (ones y) (nx - ones y) : Nat) : ℚ) / pairs.card
      ∀ θ : ℚ, 0 ≤ θ → θ ≤ 1 →
        let costs : Set ℚ := {c | ∃ (r : Nat) (send : Fin r → X → List Bool)
          (read : Fin r → List Bool → Y → Bool),
          0 < r ∧
          (∀ z x x' tail, send z x ++ tail = send z x' → tail = []) ∧
          (base + (1-base)*θ) * (r : ℚ)*pairs.card ≤
            ((∑ z : Fin r, (pairs.filter
              (fun xy => read z (send z xy.1) xy.2 = truth xy.1 xy.2)).card : Nat) : ℚ) ∧
          c = ((∑ z : Fin r, ∑ x : X, (send z x).length : Nat) : ℚ) / ((r : ℚ)*nx)}
        IsLeast costs (θ*(a*m : Nat)) :=
  PEqualNP.Outside.L_lib_928_aux.main

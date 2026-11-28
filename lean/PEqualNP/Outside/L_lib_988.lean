import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_988

private theorem mixture_gain (p δ : ℚ) (hp : 0 < p) (hp' : p < 1)
    (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    let w := 1 / (1 + p + δ)
    0 < w ∧ w < 1 ∧
      w * (p + δ) = 1 - w ∧
      p / (1 + p) + δ / 6 ≤ 1 - w := by
  dsimp
  have h₁ : 0 < 1 + p := by linarith
  have h₂ : 0 < 1 + p + δ := by linarith
  have h₃ : (1 + p) * (1 + p + δ) ≤ 6 := by
    calc
      (1 + p) * (1 + p + δ) ≤ 2 * (1 + p + δ) :=
        mul_le_mul_of_nonneg_right (by linarith) h₂.le
      _ ≤ 6 := by linarith
  refine ⟨one_div_pos.mpr h₂, (div_lt_one h₂).mpr (by linarith), ?_, ?_⟩
  · field_simp
    <;> ring
  · have he : 1 - 1 / (1 + p + δ) - p / (1 + p) =
        δ / ((1 + p) * (1 + p + δ)) := by
      field_simp
      <;> ring
    have hd : δ / 6 ≤ δ / ((1 + p) * (1 + p + δ)) :=
      div_le_div_of_nonneg_left hδ.le (mul_pos h₁ h₂) h₃
    linarith

private theorem abs_pow_sub_le (p t : ℚ) (hp : |p| ≤ 1) (ht : |t| ≤ 1)
    (n : ℕ) : |t ^ n - p ^ n| ≤ n * |t - p| := by
  have hmax : max |t| |p| ≤ 1 := max_le ht hp
  have hnonneg : 0 ≤ max |t| |p| := (abs_nonneg _).trans (le_max_left _ _)
  calc
    _ ≤ |t-p| * n * max |t| |p| ^ (n - 1) := abs_pow_sub_pow_le t p n
    _ ≤ |t-p| * n * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ hnonneg hmax) (by positivity)
    _ = _ := by ring

private theorem combine_advantages (p δ e_s e_h bonus : ℚ)
    (hp : 0 < p) (hp' : p < 1) (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (he_s : 0 ≤ e_s) (he_h : 0 ≤ e_h) (hbonus : bonus + e_s + e_h ≤ δ / 6)
    (S H : ℚ) (near : Prop)
    (hs : -e_s ≤ S) (hs_near : near → p + δ - e_s ≤ S)
    (hh : -e_h ≤ H) (hh_far : ¬ near → 1 - e_h ≤ H) :
    let w := 1 / (1 + p + δ)
    p / (1 + p) + bonus ≤ w*S + (1-w)*H := by
  classical
  let w : ℚ := 1 / (1 + p + δ)
  change _ ≤ w*S + (1-w)*H
  obtain ⟨hw, hw', hb, hg⟩ := mixture_gain p δ hp hp' hδ hδ'
  change 0 < w at hw
  change w < 1 at hw'
  change w*(p+δ) = 1-w at hb
  change p/(1+p) + δ/6 ≤ 1-w at hg
  have hwc : 0 ≤ 1-w := by linarith
  have hcost₁ := mul_le_mul_of_nonneg_right hw'.le he_s
  have hcost₂ := mul_le_mul_of_nonneg_right (show 1-w ≤ 1 by linarith) he_h
  have hsum : 1-w - (e_s+e_h) ≤ w*S + (1-w)*H := by
    by_cases hn : near
    · have h₁ := mul_le_mul_of_nonneg_left (hs_near hn) hw.le
      have h₂ := mul_le_mul_of_nonneg_left hh hwc
      linarith [mul_sub w (p+δ) e_s, mul_neg (1-w) e_h]
    · have h₁ := mul_le_mul_of_nonneg_left hs hw.le
      have h₂ := mul_le_mul_of_nonneg_left (hh_far hn) hwc
      linarith [mul_sub (1-w) 1 e_h, mul_neg w e_s, mul_one (1-w)]
  linarith

private theorem xor_labels (a b c d : Bool) :
    xor (xor a b) c = xor (xor a b) d ↔ c = d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem toAssignedProtocol {W S T : Type} [Fintype S] [Nonempty S] [Fintype T]
    (f : W → W → Bool) (left right : W → Bool)
    (send : S → W → T) (read : S → T → W → Bool) (a : ℚ)
    (h : ∀ x y, (1 + a) * (Fintype.card S : ℚ) ≤
      2 * ((Finset.univ.filter
        (fun s => read s (send s x) y = f x y)).card : ℚ)) :
    ∃ (M z : ℕ) (send' : Fin z → W → Fin M)
      (read' : Fin z → Fin M → W → Bool),
      0 < z ∧ M = 2 * Fintype.card T ∧
      ∀ x y, (1 + a) * (z : ℚ) ≤
        2 * ((Finset.univ.filter
          (fun s => read' s (send' s x) y = xor (xor (left x) (right y)) (f x y))).card : ℚ) := by
  classical
  let es := Fintype.equivFin S
  let et := Fintype.equivFin (Bool × T)
  refine ⟨_, _, fun s x => et (left x, send (es.symm s) x),
    fun s t y => xor (xor (et.symm t).1 (right y)) (read (es.symm s) (et.symm t).2 y),
    Fintype.card_pos, by simp, ?_⟩
  intro x y
  convert h x y using 2
  congr 1
  apply Finset.card_bij (fun s _ => es.symm s)
  · intro s hs
    simpa [xor_labels] using hs
  · intro s _ t _ he
    exact es.symm.injective he
  · intro s hs
    refine ⟨es s, ?_, es.symm_apply_apply s⟩
    simpa [xor_labels] using hs

private def gate (c s a : ℚ) : ℚ := max 0 (min 1 (2 - |a - c| / s))

private theorem gate_nonneg (c s a : ℚ) : 0 ≤ gate c s a := le_max_left _ _

private theorem gate_le_one (c s a : ℚ) : gate c s a ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

private theorem gate_of_near (c s a : ℚ) (hs : 0 < s) (h : |a-c| ≤ s) :
    gate c s a = 1 := by
  unfold gate
  have h' : |a-c| / s ≤ 1 := (div_le_one hs).mpr h
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

private theorem near_of_gate_pos (c s a : ℚ) (hs : 0 < s) (h : 0 < gate c s a) :
    |a-c| < 2 * s := by
  have h' : 0 < 2 - |a-c| / s :=
    (lt_min_iff.mp ((lt_max_iff.mp h).resolve_left (lt_irrefl 0))).2
  exact (div_lt_iff₀ hs).mp (by linarith)

private theorem clip_lipschitz (a b : ℚ) :
    |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a-b| := by
  calc
    _ ≤ |min 1 a - min 1 b| := by
      simpa using abs_max_sub_max_le_max (0 : ℚ) (min 1 a) 0 (min 1 b)
    _ ≤ _ := by
      simpa using abs_min_sub_min_le_max (1 : ℚ) a 1 b

private theorem gate_lipschitz (c s a b : ℚ) (hs : 0 < s) :
    |gate c s a - gate c s b| ≤ |a-b| / s := by
  refine (clip_lipschitz _ _).trans ?_
  have he : 2 - |a-c| / s - (2 - |b-c| / s) = (|b-c| - |a-c|) / s := by ring
  rw [he, abs_div, abs_of_pos hs]
  apply div_le_div_of_nonneg_right _ hs.le
  calc
    |(|b-c| - |a-c|)| ≤ |(b-c)-(a-c)| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |a-b| := by rw [← abs_neg (a-b)]; congr 1; ring

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

private theorem bounded_sum_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_bound : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i, (X i ω - ∫ z, X i z ∂μ)|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * (Fintype.card ι : ℝ) * (1 / 4))) := by
  let Y : ι → Ω → ℝ := fun i ω => X i ω - ∫ z, X i z ∂μ
  have hY : iIndepFun Y μ := h_indep.comp
    (fun i t => t - ∫ z, X i z ∂μ) (fun i => measurable_id.sub_const _)
  have hYn : iIndepFun (fun i ω => -Y i ω) μ :=
    hY.comp (fun _ t => -t) (fun _ => measurable_id.neg)
  have hG (i : ι) : HasSubgaussianMGF (Y i) (1 / 4) μ := by
    have he : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = 1 / 4 := by
      apply NNReal.coe_injective
      norm_num
    rw [← he]
    exact hasSubgaussianMGF_of_mem_Icc (h_meas i).aemeasurable (ae_of_all _ (h_bound i))
  have hp := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY
    (s := Finset.univ) (fun i _ => hG i) hε
  have hn := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYn
    (s := Finset.univ) (fun i _ => (hG i).neg) hε
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    ← mul_assoc] at hp hn
  simp only [Finset.sum_neg_distrib] at hn
  change μ.real {ω | ε ≤ |∑ i, Y i ω|} ≤ _
  have hevent : {ω | ε ≤ |∑ i, Y i ω|} =
      {ω | ε ≤ ∑ i, Y i ω} ∪ {ω | ε ≤ -(∑ i, Y i ω)} := by
    ext ω
    simp [abs_eq_max_neg, le_max_iff]
  rw [hevent]
  linarith [measureReal_union_le (μ := μ) {ω | ε ≤ ∑ i, Y i ω}
    {ω | ε ≤ -(∑ i, Y i ω)}]

private theorem atypical_count {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (y : Fin m → Fin q) (t : ℝ) (ht : 0 ≤ t) :
    ((Finset.univ.filter (fun x : Fin m → Fin q =>
      t ≤ |((Finset.univ.filter (fun i => x i = y i)).card : ℝ) / m - 1 / q|)).card : ℝ) /
      (q : ℝ)^m ≤ 2 * Real.exp (-2 * m * t^2) := by
  classical
  letI : MeasurableSpace (Fin q) := ⊤
  letI : DiscreteMeasurableSpace (Fin q) := ⟨fun _ => trivial⟩
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let α := Fin m → Fin q
  let μ : Measure (Fin q) := uniformOn Set.univ
  let ν : Measure α := uniformOn Set.univ
  have hν : ν = Measure.pi (fun _ : Fin m => μ) := by
    simpa [ν, μ] using (uniformOn_pi (f := fun _ : Fin m => (Set.univ : Set (Fin q))))
  let X : Fin m → α → ℝ := fun i x => if x i = y i then 1 else 0
  let f : Fin m → Fin q → ℝ := fun i a => if a = y i then 1 else 0
  have hf (i : Fin m) : Measurable (f i) := Measurable.of_discrete
  have hX (i : Fin m) : Measurable (X i) := (hf i).comp (measurable_pi_apply i)
  have hind : iIndepFun X ν := by
    rw [hν]
    exact iIndepFun_pi (fun i => (hf i).aemeasurable)
  have hmean (i : Fin m) : (∫ x, X i x ∂ν) = 1 / (q : ℝ) := by
    rw [hν]
    change (∫ x, f i (x i) ∂Measure.pi (fun _ : Fin m => μ)) = _
    have hpres := measurePreserving_eval (fun _ : Fin m => μ) i
    have hmap := integral_map (μ := Measure.pi (fun _ : Fin m => μ))
      hpres.measurable.aemeasurable (hf i).aestronglyMeasurable
    rw [hpres.map_eq] at hmap
    rw [← hmap]
    have hfi : f i = ({y i} : Set (Fin q)).indicator (1 : Fin q → ℝ) := by
      funext a
      simp [f, Set.indicator_apply]
    rw [hfi, integral_indicator_one (measurableSet_singleton _)]
    simp [μ, measureReal_def, uniformOn_univ, Measure.count_singleton, ENNReal.toReal_div]
  have htail := bounded_sum_tail ν hind hX
    (fun i x => by by_cases h : x i = y i <;> simp [X,h]) ((m : ℝ) * t)
    (mul_nonneg (by positivity) ht)
  simp only [hmean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at htail
  have hx (x : α) : (∑ i, X i x) =
      ((Finset.univ.filter (fun i => x i = y i)).card : ℝ) := by
    simp [X]
  simp only [hx] at htail
  let B := Finset.univ.filter (fun x : α =>
    t ≤ |((Finset.univ.filter (fun i => x i = y i)).card : ℝ) / m - 1 / q|)
  have hs : (B : Set α) = {x : α | (m : ℝ) * t ≤
      |((Finset.univ.filter (fun i => x i = y i)).card : ℝ) - m * (1 / q)|} := by
    ext x
    have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
    change x ∈ (B : Set α) ↔ _
    simp only [B, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [div_sub' hm'.ne', abs_div, abs_of_pos hm', le_div_iff₀ hm', mul_comm t]
  rw [← hs] at htail
  have hc : ν.real (B : Set α) = (B.card : ℝ) / (q : ℝ)^m := by
    have h := uniformOn_apply_finset (s := (Finset.univ : Finset α)) (t := B)
    have h' := congrArg ENNReal.toReal h
    simpa [ν, α, measureReal_def, ENNReal.toReal_div, Fintype.card_fun] using h'
  rw [hc] at htail
  have he : -((m : ℝ) * t) ^ 2 / (2 * m * (1 / 4)) = -2 * m * t^2 := by
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
    ring
  simpa only [he] using htail

private theorem all_avoid_count {W I : Type*} [Fintype W] [Fintype I] [DecidableEq I]
    (bad : W → Prop) [DecidablePred bad] :
    (Finset.univ.filter (fun s : I → W => ∀ i, bad (s i))).card =
      (Finset.univ.filter bad).card ^ Fintype.card I := by
  classical
  rw [← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_fun]
  exact Fintype.card_congr
    { toFun := fun s i => ⟨s.1 i, s.2 i⟩
      invFun := fun s => ⟨fun i => (s i).1, fun i => (s i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem equal_distance_equal_count {W I : Type*} [Fintype W] [Fintype I] [DecidableEq I]
    [DecidableEq W] (dist : W → ℕ) (pick : (I → ℕ) → I)
    (u v : W) (huv : dist u = dist v) :
    (Finset.univ.filter (fun s : I → W => s (pick (dist ∘ s)) = u)).card =
      (Finset.univ.filter (fun s : I → W => s (pick (dist ∘ s)) = v)).card := by
  let swap := Equiv.swap u v
  have hdist (w : W) : dist (swap w) = dist w := by
    by_cases hu : w = u
    · subst w
      simpa [swap] using huv.symm
    by_cases hv : w = v
    · subst w
      simpa [swap] using huv
    simp [swap, Equiv.swap_apply_of_ne_of_ne hu hv]
  let e : (I → W) ≃ (I → W) := Equiv.piCongrRight (fun _ => swap)
  have happ (s : I → W) : dist ∘ e s = dist ∘ s := funext fun i => hdist (s i)
  apply Finset.card_bij (fun s _ => e s)
  · intro s hs
    have hs' := (Finset.mem_filter.mp hs).2
    simp [happ, e, swap, hs']
  · intro s _ t _ h
    exact e.injective h
  · intro t ht
    let s := e.symm t
    have he : e s = t := e.apply_symm_apply t
    have ht' := (Finset.mem_filter.mp ht).2
    have hsel := happ s
    rw [he] at hsel
    refine ⟨s, ?_, he⟩
    simp [← hsel, s, e, swap, ht']

private noncomputable def nearest {I : Type*} [Fintype I] [Nonempty I] (d : I → ℕ) : I :=
  Classical.choose (Finset.exists_min_image Finset.univ d Finset.univ_nonempty)

private theorem nearest_le {I : Type*} [Fintype I] [Nonempty I] (d : I → ℕ) (i : I) :
    d (nearest d) ≤ d i :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ d Finset.univ_nonempty)).2 i
    (Finset.mem_univ _)

private theorem selected_miss_count {W I : Type*} [Fintype W] [Fintype I] [DecidableEq I] [Nonempty I]
    (dist : W → ℕ) (r : ℕ) :
    (Finset.univ.filter (fun s : I → W => r < dist (s (nearest (dist ∘ s))))).card =
      (Finset.univ.filter (fun w => r < dist w)).card ^ Fintype.card I := by
  classical
  convert all_avoid_count (I := I) (fun w : W => r < dist w) using 1
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i
    exact h.trans_le (nearest_le (dist ∘ s) i)
  · intro h
    exact h _

private theorem nonneg_of_equal_fibers {S W D : Type*} [Fintype S] [Fintype W]
    [DecidableEq W] [DecidableEq D]
    (select : S → W) (distance : W → D) (f : W → ℚ)
    (hcount : ∀ u v, distance u = distance v →
      (Finset.univ.filter fun s => select s = u).card =
        (Finset.univ.filter fun s => select s = v).card)
    (hf : ∀ d, 0 ≤ ∑ w ∈ Finset.univ.filter (fun w => distance w = d), f w) :
    0 ≤ ∑ s, f (select s) := by
  classical
  let n (w : W) := (Finset.univ.filter fun s => select s = w).card
  have hs : (∑ s, f (select s)) = ∑ w, (n w : ℚ) * f w := by
    have he := Finset.sum_fiberwise' (Finset.univ : Finset S) select f
    simpa [n, Finset.sum_const, nsmul_eq_mul] using he.symm
  rw [hs, ← Finset.sum_fiberwise_of_maps_to (t := Finset.univ.image distance)
    (g := distance) (fun w _ => Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩)]
  refine Finset.sum_nonneg fun d hd => ?_
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hd
  have he :
      (∑ w ∈ Finset.univ.filter (fun w => distance w = d), (n w : ℚ) * f w) =
      (n u : ℚ) * ∑ w ∈ Finset.univ.filter (fun w => distance w = d), f w := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hdist := (Finset.mem_filter.mp hw).2.trans hu.symm
    rw [show n w = n u from hcount _ _ hdist]
  rw [he]
  exact mul_nonneg (Nat.cast_nonneg _) (hf d)

private def changes {m q : ℕ} (x u : Fin m → Fin q) : Finset (Fin m) :=
  Finset.univ.filter fun i => u i ≠ x i

private def changeEquiv {m q : ℕ} (x : Fin m → Fin q) :
    (Fin m → Fin q) ≃ (s : Finset (Fin m)) × ((i : s) → {a : Fin q // a ≠ x i}) where
  toFun u := ⟨changes x u, fun i => ⟨u i, (Finset.mem_filter.mp i.2).2⟩⟩
  invFun s i := if h : i ∈ s.1 then s.2 ⟨i, h⟩ else x i
  left_inv u := by
    funext i
    by_cases h : u i = x i
    · simpa [changes, h] using h.symm
    · simp [changes, h]
  right_inv p := by
    obtain ⟨s, f⟩ := p
    have hs : changes x (fun i => if h : i ∈ s then (f ⟨i, h⟩).1 else x i) = s := by
      ext i
      by_cases hi : i ∈ s
      · simp [changes, hi, (f ⟨i, hi⟩).2]
      · simp [changes, hi]
    apply Sigma.ext hs
    apply Function.hfunext (congrArg (fun t : Finset (Fin m) => ↥t) hs)
    intro i j hij
    have helper {a b : Finset (Fin m)} (hab : a = b) (i : a) (j : b)
        (h : HEq i j) : i.val = j.val := by
      subst b
      cases h
      rfl
    have hv := helper hs i j hij
    have hi : i.val ∈ s := hv.symm ▸ j.2
    simp only [dite_eq_left hi]
    have he {a b : Fin m} (h : a = b) (ha : a ∈ s) (hb : b ∈ s) :
        HEq (f ⟨a, ha⟩) (f ⟨b, hb⟩) := by
      subst b
      rfl
    exact he hv _ j.2

private def shell_equiv {m q d : ℕ} (x : Fin m → Fin q) :
    {u // (changes x u).card = d} ≃
      (s : {s : Finset (Fin m) // s.card = d}) ×
        ((i : s.1) → {a : Fin q // a ≠ x i}) := by
  classical
  let e := changeEquiv x
  exact (e.subtypeEquiv (p := fun u => (changes x u).card = d)
    (q := fun p => p.1.card = d) (fun _ => Iff.rfl)).trans
    { toFun := fun p => ⟨⟨p.1.1, p.2⟩, p.1.2⟩
      invFun := fun p => ⟨⟨p.1.1, p.2⟩, p.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem shell_card {m q d : ℕ} (x : Fin m → Fin q) :
    (Finset.univ.filter (fun u => (changes x u).card = d)).card =
      m.choose d * (q - 1)^d := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (shell_equiv x), Fintype.card_sigma]
  have h (i : Fin m) : Fintype.card {a : Fin q // a ≠ x i} = q - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  simp only [Fintype.card_pi, h, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have hsum (s : {s : Finset (Fin m) // s.card = d}) :
      (q - 1)^s.1.card = (q - 1)^d := by rw [s.2]
  simp only [hsum, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, Fintype.card_finset_len,
    Fintype.card_fin]

private def agreement {m q : ℕ} (x y : Fin m → Fin q) : ℚ :=
  ((Finset.univ.filter (fun i => x i = y i)).card : ℚ) / m

private theorem agreement_lipschitz {m q : ℕ} (x u y : Fin m → Fin q) :
    |agreement u y - agreement x y| ≤ ((changes x u).card : ℚ) / m := by
  classical
  let A := Finset.univ.filter (fun i => u i = y i)
  let B := Finset.univ.filter (fun i => x i = y i)
  let D := changes x u
  have hA : A ⊆ B ∪ D := by
    intro i hi
    have hu : u i = y i := (Finset.mem_filter.mp hi).2
    by_cases he : u i = x i
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm.trans hu⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  have hB : B ⊆ A ∪ D := by
    intro i hi
    have hx : x i = y i := (Finset.mem_filter.mp hi).2
    by_cases he : u i = x i
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.trans hx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  have ha : (A.card : ℚ) ≤ B.card + D.card := by
    exact_mod_cast (Finset.card_le_card hA).trans (Finset.card_union_le _ _)
  have hb : (B.card : ℚ) ≤ A.card + D.card := by
    exact_mod_cast (Finset.card_le_card hB).trans (Finset.card_union_le _ _)
  change |(A.card : ℚ) / m - (B.card : ℚ) / m| ≤ (D.card : ℚ) / m
  rw [← sub_div, abs_div, show |(m : ℚ)| = (m : ℚ) from abs_of_nonneg (Nat.cast_nonneg m)]
  refine div_le_div_of_nonneg_right (abs_le.mpr ⟨?_, ?_⟩) (Nat.cast_nonneg _)
  · linarith
  · linarith

private theorem collision_card_mul {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V] {a b : W} (h : a ≠ b) :
    (Finset.univ.filter (fun f : W → V => f a = f b)).card * Fintype.card V =
      Fintype.card (W → V) := by
  classical
  let e : ({f : W → V // f a = f b} × V) ≃ (W → V) :=
    { toFun := fun p => Function.update p.1.1 a p.2
      invFun := fun f => (⟨Function.update f a (f b), by simp [h.symm]⟩, f a)
      left_inv := by
        rintro ⟨⟨f, hf⟩, v⟩
        apply Prod.ext
        · apply Subtype.ext
          funext x
          by_cases hx : x = a
          · subst x
            simpa [h.symm] using hf.symm
          · simp [Function.update_of_ne hx]
        · simp
      right_inv := by
        intro f
        funext x
        by_cases hx : x = a
        · subst x
          simp
        · simp [Function.update_of_ne hx] }
  simpa [Fintype.card_prod, Fintype.card_subtype] using Fintype.card_congr e

private def collisions {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
    (B : Finset W) (x : W) : Finset (W → V) :=
  (B.erase x).biUnion (fun u => Finset.univ.filter (fun f => f x = f u))

private theorem mem_collisions {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
    (B : Finset W) (x : W) (f : W → V) :
    f ∈ collisions B x ↔ ∃ u ∈ B, u ≠ x ∧ f x = f u := by
  simp only [collisions, Finset.mem_biUnion, Finset.mem_erase,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, ⟨hu, hB⟩, hf⟩
    exact ⟨u, hB, hu, hf⟩
  · rintro ⟨u, hB, hu, hf⟩
    exact ⟨u, ⟨hu, hB⟩, hf⟩

private theorem collisions_card_mul_le {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V] (B : Finset W) (x : W) :
    (collisions (V := V) B x).card * Fintype.card V ≤
      B.card * Fintype.card (W → V) := by
  classical
  unfold collisions
  calc
    _ ≤ (∑ u ∈ B.erase x, (Finset.univ.filter (fun f : W → V => f x = f u)).card) *
        Fintype.card V := Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = (B.erase x).card * Fintype.card (W → V) := by
      rw [Finset.sum_mul]
      calc
        _ = ∑ _ ∈ B.erase x, Fintype.card (W → V) := by
          refine Finset.sum_congr rfl fun u hu => ?_
          exact collision_card_mul (Finset.ne_of_mem_erase hu).symm
        _ = _ := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.erase_subset _ _))

open scoped BigOperators

private def matchCount {m q : ℕ} (x y : Fin m → Fin q) : ℕ :=
  (Finset.univ.filter fun i => x i = y i).card

private def matchSign {m q : ℕ} (x y : Fin m → Fin q) : ℚ := (-1) ^ matchCount x y

private theorem prod_eq_sign_count {I : Type*} (s : Finset I) (P : I → Prop)
    [DecidablePred P] :
    (∏ i ∈ s, if P i then (-1 : ℚ) else 1) = (-1) ^ (s.filter P).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    by_cases h : P a
    · have hn : a ∉ s.filter P := fun h' => ha (Finset.mem_of_mem_filter a h')
      simp [Finset.filter_insert, ha, h, hn, ih, pow_succ]
    · simp [Finset.filter_insert, ha, h, ih]

private theorem matchSign_eq_prod {m q : ℕ} (x y : Fin m → Fin q) :
    matchSign x y = ∏ i, if x i = y i then -1 else 1 :=
  (prod_eq_sign_count Finset.univ _).symm

private theorem match_correlation {m q : ℕ} (x c y : Fin m → Fin q) :
    matchSign x y * matchSign c y =
      ∏ i, if (x i = y i ↔ c i = y i) then 1 else -1 := by
  rw [matchSign_eq_prod, matchSign_eq_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h₁ : x i = y i <;> by_cases h₂ : c i = y i <;> simp [h₁,h₂]

private def parity {m q : ℕ} (x y : Fin m → Fin q) : Bool := matchCount x y % 2 == 1

private theorem sign_of_parity {m q : ℕ} (x y : Fin m → Fin q) :
    matchSign x y = if parity x y then -1 else 1 := by
  unfold matchSign parity
  rw [neg_one_pow_eq_pow_mod_two]
  have h : matchCount x y % 2 = 0 ∨ matchCount x y % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

open scoped BigOperators

private def score (actual wanted : Bool) : ℚ := if actual = wanted then 1 else -1

private theorem score_bounds (a b : Bool) : |score a b| = 1 := by
  unfold score
  split_ifs <;> simp

private theorem score_fair (b : Bool) : (𝔼 a : Bool, score a b) = 0 := by
  rw [Fintype.expect_eq_sum_div_card]
  cases b <;> norm_num [Fintype.sum_bool, score]

private theorem score_correct_count {S : Type*} [Fintype S] [Nonempty S] (f : S → Bool)
    (b : Bool) :
    (𝔼 s, score (f s) b) =
      2 * ((Finset.univ.filter (fun s => f s = b)).card : ℚ) / Fintype.card S - 1 := by
  have he (s : S) : score (f s) b = 2 * (if f s = b then 1 else 0) - 1 := by
    unfold score
    split_ifs <;> norm_num
  simp_rw [he, Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const]
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_filter]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

private theorem mean_change_on_exception {S : Type*} [Fintype S] (bad : Finset S)
    (f g : S → ℚ) (hf : ∀ s, |f s| ≤ 1) (hg : ∀ s, |g s| ≤ 1)
    (h : ∀ s ∉ bad, f s = g s) :
    |(𝔼 s, f s) - (𝔼 s, g s)| ≤
      2 * (bad.card : ℚ) / Fintype.card S := by
  classical
  rw [← Finset.expect_sub_distrib, Fintype.expect_eq_sum_div_card, abs_div,
    abs_of_nonneg (by positivity : 0 ≤ (Fintype.card S : ℚ))]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ s, |f s - g s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, if s ∈ bad then (2 : ℚ) else 0 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s ∈ bad
      · rw [if_pos hs]
        calc
          _ ≤ |f s| + |g s| := by simpa using abs_sub_le (f s) 0 (g s)
          _ ≤ _ := by linarith [hf s, hg s]
      · simp [hs, h s hs]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

private theorem coin_parameters (p : ℚ) (h₀ : 0 ≤ p) (h₁ : p ≤ 1) :
    ∃ a b : ℕ, 0 < b ∧ a ≤ b ∧ (a : ℚ) / b = p := by
  have hn : 0 ≤ p.num := Rat.num_nonneg.mpr h₀
  have he : (p.num.toNat : ℚ) = (p.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hn
  have hf : (p.num.toNat : ℚ) / p.den = p := by rw [he, Rat.num_div_den]
  refine ⟨p.num.toNat, p.den, p.den_pos, ?_, hf⟩
  have hd : 0 < (p.den : ℚ) := by exact_mod_cast p.den_pos
  have h' : (p.num.toNat : ℚ) / p.den ≤ 1 := hf.trans_le h₁
  have h := (div_le_iff₀ hd).mp h'
  exact_mod_cast (show (p.num.toNat : ℚ) ≤ p.den from by simpa using h)

private theorem coin_average (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (u v : ℚ) :
    (𝔼 j : Fin b, if j.val < a then u else v) =
      (a : ℚ) / b * u + (1 - (a : ℚ) / b) * v := by
  have he (j : Fin b) : (if j.val < a then u else v) =
      (if j.val < a then u - v else 0) + v := by
    split_ifs <;> ring
  letI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  simp_rw [he, Finset.expect_add_distrib, Fintype.expect_const]
  rw [Fintype.expect_eq_sum_div_card, ← Finset.sum_filter]
  simp [Finset.sum_const, nsmul_eq_mul, Fin.card_filter_val_lt, min_eq_right hab]
  ring

private theorem average_eval {I : Type*} {V : I → Type*} [Fintype I] [DecidableEq I]
    [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
    (i : I) (f : V i → ℚ) : (𝔼 s : (∀ i, V i), f (s i)) = 𝔼 a, f a := by
  classical
  let e := Equiv.piSplitAt i V
  calc
    _ = 𝔼 p : V i × (∀ j : {j // j ≠ i}, V j), f p.1 :=
      Fintype.expect_equiv e (fun s => f (s i)) (fun p => f p.1) (fun _ => rfl)
    _ = _ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp [Fintype.expect_const]

private theorem mix_average {S T : Type*} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (f : S → ℚ) (g : T → ℚ) :
    (𝔼 z : Fin b × (S × T), if z.1.val < a then f z.2.1 else g z.2.2) =
      (a : ℚ) / b * (𝔼 s, f s) + (1 - (a : ℚ) / b) * (𝔼 t, g t) := by
  have he (i : Fin b) :
      (𝔼 st : S × T, if i.val < a then f st.1 else g st.2) =
        if i.val < a then (𝔼 s, f s) else (𝔼 t, g t) := by
    by_cases h : i.val < a
    · simp only [h, ↓reduceIte]
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp [Fintype.expect_const]
    · simp only [h, ↓reduceIte]
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp [Fintype.expect_const]
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp_rw [he]
  exact coin_average a b hb hab _ _

private theorem average_filter_error {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S] (good : Finset S)
    (hgood : good.Nonempty) (f : S → ℚ) (hf : ∀ s, |f s| ≤ 1) :
    |(𝔼 s, f s) - (𝔼 s ∈ good, f s)| ≤ 2 * (goodᶜ.card : ℚ) / Fintype.card S := by
  classical
  let a := 𝔼 s ∈ good, f s
  let g : S → ℚ := fun s => if s ∈ good then f s else a
  have hfa (s) : -1 ≤ f s ∧ f s ≤ 1 := abs_le.mp (hf s)
  have ha₁ : a ≤ 1 := by
    rw [← Finset.expect_const hgood (1 : ℚ)]
    exact Finset.expect_le_expect fun s _ => (hfa s).2
  have ha₂ : -1 ≤ a := by
    rw [← Finset.expect_const hgood (-1 : ℚ)]
    exact Finset.expect_le_expect fun s _ => (hfa s).1
  have hg (s) : |g s| ≤ 1 := by
    by_cases h : s ∈ good
    · simpa [g,h] using hf s
    · simpa [g,h] using (abs_le.mpr ⟨ha₂,ha₁⟩ : |a| ≤ 1)
  have hge : (𝔼 s, g s) = a := by
    have he (s : S) : g s = (if s ∈ good then f s - a else 0) + a := by
      by_cases h : s ∈ good <;> simp [g,h]
    simp_rw [he, Finset.expect_add_distrib, Fintype.expect_const, Fintype.expect_ite_mem,
      Finset.expect_sub_distrib, Finset.expect_const hgood a]
    change good.dens • (a - a) + a = a
    simp
  have he := mean_change_on_exception goodᶜ f g hf hg (fun s hs => by
    have h : s ∈ good := by simpa using hs
    simp [g,h])
  simpa [hge] using he

private theorem average_indicator {S : Type*} [Fintype S] (p : S → Prop) [DecidablePred p] :
    (𝔼 s : S, if p s then (1 : ℚ) else 0) =
      ((Finset.univ.filter p).card : ℚ) / Fintype.card S := by
  rw [Fintype.expect_eq_sum_div_card, ← Finset.sum_filter]
  simp [Finset.sum_const]

private theorem miss_exp (u : ℝ) (hu : u ≤ 1) (L : ℕ) :
    (1 - u)^L ≤ Real.exp (-L * u) := by
  have h := Real.add_one_le_exp (-u)
  have h' : 1 - u ≤ Real.exp (-u) := by linarith
  calc
    _ ≤ (Real.exp (-u))^L := pow_le_pow_left₀ (by linarith) h' _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

private theorem one_sub_exp_neg_lower (s : ℝ) (hs : 0 ≤ s) :
    s / (1+s) ≤ 1 - Real.exp (-s) := by
  have hp : 0 < 1+s := by linarith
  have he : 1+s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have ho : Real.exp (-s) ≤ 1 / (1+s) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hp he
  have hh : s / (1+s) = 1 - 1 / (1+s) := by field_simp; ring
  linarith

private theorem shell_lower (m q j : ℕ) (hm : 2*j ≤ m) :
    ((q - 1 : ℕ) : ℝ)^j / (2^j * j.factorial) * (m : ℝ)^j ≤
      (m.choose j : ℝ) * ((q - 1 : ℕ) : ℝ)^j := by
  have hnat : m ≤ 2 * (m + 1 - j) := by omega
  have hbase : (m : ℝ) ≤ 2 * ((m + 1 - j : ℕ) : ℝ) := by exact_mod_cast hnat
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ m) hbase j
  rw [mul_pow] at hpow
  have hden : 0 < (2 : ℝ)^j * (j.factorial : ℝ) := by positivity
  have hf : 0 < (j.factorial : ℝ) := by positivity
  have hchoose := Nat.pow_le_choose (α := ℝ) j m
  have hc : ((m + 1 - j : ℕ) : ℝ)^j ≤ (m.choose j : ℝ) * j.factorial :=
    (div_le_iff₀ hf).mp hchoose
  have hmid : (m : ℝ)^j ≤ (m.choose j : ℝ) * (2^j * j.factorial) := by
    calc
      _ ≤ (2 : ℝ)^j * ((m + 1 - j : ℕ) : ℝ)^j := hpow
      _ ≤ 2^j * ((m.choose j : ℝ) * j.factorial) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  calc
    _ ≤ ((q - 1 : ℕ) : ℝ)^j * ((m.choose j : ℝ) * (2^j * j.factorial)) :=
      mul_le_mul_of_nonneg_left hmid (by positivity)
    _ = _ := by ring

private theorem log_le_binary (m : ℕ) (hm : 0 < m) :
    Real.log (m : ℝ) ≤ (1 + m.log2 : ℝ) := by
  have hnat : m < 2 ^ (m.log2 + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide) _
  have hr : (m : ℝ) < (2 : ℝ) ^ (m.log2 + 1) := by exact_mod_cast hnat
  have hlog := Real.strictMonoOn_log (show (m : ℝ) ∈ Set.Ioi 0 by change 0 < (m : ℝ); exact_mod_cast hm)
    (show ((2 : ℝ) ^ (m.log2 + 1 : ℕ)) ∈ Set.Ioi 0 by exact pow_pos (by norm_num : (0 : ℝ) < 2) (m.log2 + 1)) hr
  rw [Real.log_pow] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    _ ≤ _ := hlog.le
    _ ≤ ((m.log2 + 1 : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left htwo (by positivity)
    _ = _ := by push_cast; ring

open scoped BigOperators

private noncomputable def hashRead {W V : Type*} [Fintype W] [DecidableEq V]
    (B : W → Finset W) (f : W → V) (coin : Bool) (parity : W → W → Bool)
    (msg : V) (y : W) : Bool := by
  classical
  exact if h : ∃! u, u ∈ B y ∧ f u = msg then parity (Classical.choose h) y else coin

private theorem hash_advantage {W V : Type*} [Fintype W] [Fintype V] [Nonempty V]
    [DecidableEq W] [DecidableEq V] (B : W → Finset W)
    (parity : W → W → Bool) (x y : W) :
    (if x ∈ B y then (1 : ℚ) else 0) - 2 * ((B y).card : ℚ) / Fintype.card V ≤
      𝔼 s : (W → V) × Bool, score (hashRead B s.1 s.2 parity (s.1 x) y) (parity x y) := by
  classical
  let bad := (collisions (V := V) (B y) x).product (Finset.univ : Finset Bool)
  let actual : (W → V) × Bool → ℚ :=
    fun s => score (hashRead B s.1 s.2 parity (s.1 x) y) (parity x y)
  let ideal : (W → V) × Bool → ℚ :=
    fun s => if x ∈ B y then 1 else score s.2 (parity x y)
  have hA (s) : |actual s| ≤ 1 := (score_bounds _ _).le
  have hI (s) : |ideal s| ≤ 1 := by
    by_cases h : x ∈ B y <;> simp [ideal,h,score_bounds]
  have hEq (s) (hs : s ∉ bad) : actual s = ideal s := by
    have hk : ∀ u, u ∈ B y → s.1 u = s.1 x → u = x := by
      intro u hu he
      by_contra hn
      apply hs
      exact Finset.mem_product.mpr
        ⟨(mem_collisions _ _ _).mpr ⟨u, hu, hn, he.symm⟩, Finset.mem_univ _⟩
    by_cases hx : x ∈ B y
    · have h : ∃! u, u ∈ B y ∧ s.1 u = s.1 x :=
        ⟨x, ⟨hx, rfl⟩, fun u hu => hk u hu.1 hu.2⟩
      have he : Classical.choose h = x := hk _
        (Classical.choose_spec h).1.1 (Classical.choose_spec h).1.2
      change score (hashRead B s.1 s.2 parity (s.1 x) y) (parity x y) = _
      have hread : hashRead B s.1 s.2 parity (s.1 x) y = parity x y := by
        unfold hashRead
        split
        · rename_i hh
          exact congrArg (fun u => parity u y) (hk _
            (Classical.choose_spec hh).1.1 (Classical.choose_spec hh).1.2)
        · contradiction
      simp [hread, ideal, hx, score]
    · have h : ¬∃! u, u ∈ B y ∧ s.1 u = s.1 x := by
        rintro ⟨u, ⟨hu, he⟩, _⟩
        exact hx (hk u hu he ▸ hu)
      simp [actual, ideal, hashRead, h, hx]
  have hi : (𝔼 s, ideal s) = if x ∈ B y then 1 else 0 := by
    by_cases h : x ∈ B y
    · simp [ideal,h,Fintype.expect_const]
    · simp only [ideal, h, ↓reduceIte]
      rw [← Finset.univ_product_univ, Finset.expect_product]
      change (𝔼 _f : W → V, (𝔼 b : Bool, score b (parity x y))) = 0
      simp only [score_fair, Finset.expect_const_zero]
  have hc : (bad.card : ℚ) / Fintype.card ((W → V) × Bool) ≤
      ((B y).card : ℚ) / Fintype.card V := by
    have hV : 0 < (Fintype.card V : ℚ) := by exact_mod_cast Fintype.card_pos
    have hW : 0 < (Fintype.card (W → V) : ℚ) := by exact_mod_cast Fintype.card_pos
    have hl : ((collisions (V := V) (B y) x).card : ℚ) * Fintype.card V ≤
        ((B y).card : ℚ) * Fintype.card (W → V) := by
      exact_mod_cast collisions_card_mul_le (V := V) (B y) x
    have hh := (div_le_div_iff₀ hW hV).mpr hl
    simpa [bad, Finset.card_product, Fintype.card_prod, Nat.cast_mul, mul_div_mul_right] using hh
  have he := mean_change_on_exception bad actual ideal hA hI hEq
  have ha := neg_abs_le ((𝔼 s, actual s) - (𝔼 s, ideal s))
  rw [hi] at he ha
  dsimp [actual] at he ha
  rw [mul_div_assoc] at he ⊢
  linarith

open scoped BigOperators

private noncomputable def realize {m q d : ℕ} (x : Fin m → Fin q)
    (e : Fin d ↪ Fin m) (a : ∀ j : Fin d, {v : Fin q // v ≠ x (e j)}) : Fin m → Fin q := by
  classical
  exact fun i => if h : ∃ j, e j = i then (a (Classical.choose h)).1 else x i

private theorem realize_apply {m q d : ℕ} (x : Fin m → Fin q)
    (e : Fin d ↪ Fin m) (a : ∀ j : Fin d, {v : Fin q // v ≠ x (e j)})
    (j : Fin d) : realize x e a (e j) = (a j).1 := by
  classical
  have h : ∃ j', e j' = e j := ⟨j, rfl⟩
  have he : Classical.choose h = j := e.injective (Classical.choose_spec h)
  unfold realize
  split
  · rename_i hh
    exact congrArg (fun k => (a k).val) (e.injective (Classical.choose_spec hh))
  · contradiction

private theorem changes_realize {m q d : ℕ} (x : Fin m → Fin q)
    (e : Fin d ↪ Fin m) (a : ∀ j : Fin d, {v : Fin q // v ≠ x (e j)}) :
    changes x (realize x e a) = Finset.univ.map e := by
  classical
  ext i
  simp only [changes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · intro h
    by_contra hi
    exact h (by simp [realize, hi])
  · rintro ⟨j, rfl⟩
    rw [realize_apply]
    exact (a j).2

private noncomputable def describeEquiv {m q d : ℕ} (x : Fin m → Fin q) :
    ((e : Fin d ↪ Fin m) × (∀ j : Fin d, {v : Fin q // v ≠ x (e j)})) ≃
      ((c : {u // (changes x u).card = d}) × (Fin d ≃ ↥(changes x c.val))) := by
  classical
  let encode (p : (e : Fin d ↪ Fin m) × (∀ j : Fin d, {v : Fin q // v ≠ x (e j)})) :
      (c : {u // (changes x u).card = d}) × (Fin d ≃ ↥(changes x c.val)) := by
    let c := realize x p.1 p.2
    have hc := changes_realize x p.1 p.2
    have hd : (changes x c).card = d := by simpa [c, hc]
    refine ⟨⟨c, hd⟩, Equiv.ofBijective (fun j => ⟨p.1 j, ?_⟩) ?_⟩
    · rw [hc]
      exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · constructor
      · intro i j hij
        exact p.1.injective (congrArg Subtype.val hij)
      · intro i
        have hi : i.val ∈ Finset.univ.map p.1 := hc ▸ i.2
        obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi
        exact ⟨j, Subtype.ext hj⟩
  let decode (p : (c : {u // (changes x u).card = d}) × (Fin d ≃ ↥(changes x c.val))) :
      (e : Fin d ↪ Fin m) × (∀ j : Fin d, {v : Fin q // v ≠ x (e j)}) := by
    let e : Fin d ↪ Fin m := ⟨fun j => (p.2 j).val, fun i j h => p.2.injective (Subtype.ext h)⟩
    exact ⟨e, fun j => ⟨p.1.val (e j), (Finset.mem_filter.mp (p.2 j).2).2⟩⟩
  refine ⟨encode, decode, ?_, ?_⟩
  · rintro ⟨e, a⟩
    have he : (decode (encode ⟨e, a⟩)).1 = e := by ext j; rfl
    apply Sigma.ext he
    apply Function.hfunext rfl
    intro i j h
    have hij := eq_of_heq h
    subst j
    have hh : ∀ (e' : Fin d ↪ Fin m) (h : e' = e) (u : {v : Fin q // v ≠ x (e' i)}),
        u.val = (a i).val → HEq u (a i) := by
      intro e' he' u hu
      subst e'
      exact heq_of_eq (Subtype.ext hu)
    apply hh _ he
    exact realize_apply x e a i
  · rintro ⟨⟨c, hc⟩, e⟩
    let p : (c : {u // (changes x u).card = d}) × (Fin d ≃ ↥(changes x c.val)) := ⟨⟨c, hc⟩, e⟩
    have hval : (encode (decode p)).1.val = c := by
      funext i
      by_cases hi : i ∈ changes x c
      · obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
        have hji : (e j).val = i := congrArg Subtype.val hj
        change realize x (decode p).1 (decode p).2 i = c i
        rw [← hji]
        exact realize_apply x (decode p).1 (decode p).2 j
      · have hni : ¬ ∃ j, (e j).val = i := by
          rintro ⟨j, hj⟩
          exact hi (hj ▸ (e j).2)
        have hcx : c i = x i := by simpa [changes] using hi
        change realize x (decode p).1 (decode p).2 i = c i
        unfold realize
        split
        · rename_i hh
          exact (hni hh).elim
        · exact hcx.symm
    apply Sigma.ext (Subtype.ext hval)
    have helper {u v : {u // (changes x u).card = d}} (h : u = v)
        (f : Fin d ≃ ↥(changes x u.val)) (g : Fin d ≃ ↥(changes x v.val))
        (hf : ∀ j, (f j).val = (g j).val) : HEq f g := by
      subst v
      exact heq_of_eq (Equiv.ext fun j => Subtype.ext (hf j))
    exact helper (Subtype.ext hval) _ _ (fun _ => rfl)

private def flipSign {m q : ℕ} (x y : Fin m → Fin q) (i : Fin m) (a : Fin q) : ℚ :=
  if (x i = y i ↔ a = y i) then 1 else -1

private theorem descriptor_sign {m q d : ℕ} (x y : Fin m → Fin q)
    (e : Fin d ↪ Fin m) (a : ∀ j : Fin d, {v : Fin q // v ≠ x (e j)}) :
    matchSign x y * matchSign (realize x e a) y =
      ∏ j, flipSign x y (e j) ((a j).val) := by
  classical
  rw [match_correlation]
  let F : Fin m → ℚ := fun i => flipSign x y i (realize x e a i)
  change ∏ i, F i = _
  have hoff : ∀ i ∈ Finset.univ, i ∉ Finset.univ.map e → F i = 1 := by
    intro i _ hi
    have hn : ¬∃ j, e j = i := by
      rintro ⟨j, hj⟩
      exact hi (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, hj⟩)
    simp [F, flipSign, realize, hn]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.map e)) hoff, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro j _
  simp [F, realize_apply]

private theorem flipSign_bounds {m q : ℕ} (x y : Fin m → Fin q) (i : Fin m) (a : Fin q) :
    |flipSign x y i a| = 1 := by
  unfold flipSign
  split_ifs <;> simp

private noncomputable def injectiveEquiv {m q d : ℕ} (x : Fin m → Fin q) :
    {s : Fin d → (i : Fin m) × {v : Fin q // v ≠ x i} //
      Function.Injective (fun j => (s j).fst)} ≃
        ((e : Fin d ↪ Fin m) × (∀ j : Fin d, {v : Fin q // v ≠ x (e j)})) where
  toFun s := ⟨⟨fun j => (s.val j).1, s.2⟩, fun j => (s.val j).2⟩
  invFun p := ⟨fun j => ⟨p.1 j, p.2 j⟩, p.1.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem shell_average_encoding {m q d : ℕ} (x : Fin m → Fin q) (f : (Fin m → Fin q) → ℚ) :
    (𝔼 p : ((e : Fin d ↪ Fin m) × (∀ j : Fin d, {v : Fin q // v ≠ x (e j)})),
      f (realize x p.1 p.2)) =
    𝔼 c : {u // (changes x u).card = d}, f c.val := by
  classical
  let P := {u // (changes x u).card = d}
  let e (c : P) : Fin d ≃ ↥(changes x c.val) :=
    Fintype.equivOfCardEq (by simp [c.2])
  let ef : ((c : P) × (Fin d ≃ ↥(changes x c.val))) ≃ ((_: P) × Equiv.Perm (Fin d)) :=
    Equiv.sigmaCongrRight fun c => Equiv.equivCongr (Equiv.refl _) (e c).symm
  let ep := ((describeEquiv x).trans ef).trans (Equiv.sigmaEquivProd P (Equiv.Perm (Fin d)))
  calc
    _ = 𝔼 p : P × Equiv.Perm (Fin d), f p.1.val :=
      Fintype.expect_equiv ep _ _ (fun _ => rfl)
    _ = _ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp [P]

private theorem average_single_flips_pow {m q d : ℕ} (x y : Fin m → Fin q) :
    (𝔼 s : Fin d → (i : Fin m) × {v : Fin q // v ≠ x i},
      ∏ j, flipSign x y (s j).1 (s j).2.val) =
    (𝔼 a : (i : Fin m) × {v : Fin q // v ≠ x i}, flipSign x y a.1 a.2.val)^d := by
  classical
  symm
  simpa using Finset.expect_pow Finset.univ
    (fun a : (i : Fin m) × {v : Fin q // v ≠ x i} => flipSign x y a.1 a.2.val) d

private theorem mean_flip_formula {m q : ℕ} (hm : 0 < m) (hq : 1 < q) (x y : Fin m → Fin q) :
    (𝔼 a : (i : Fin m) × {v : Fin q // v ≠ x i}, flipSign x y a.1 a.2.val) =
      1 - 2 * (agreement x y + (1 - agreement x y) / ((q - 1 : ℕ) : ℚ)) := by
  classical
  let A (i : Fin m) := {v : Fin q // v ≠ x i}
  have hcard (i : Fin m) : Fintype.card (A i) = q - 1 := by
    change Fintype.card {v : Fin q // v ≠ x i} = _
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  let e (i : Fin m) : Fin (q-1) ≃ A i :=
    Fintype.equivOfCardEq (by simp [hcard])
  let ep : ((i : Fin m) × A i) ≃ Fin m × Fin (q-1) :=
    (Equiv.sigmaCongrRight (fun i => (e i).symm)).trans (Equiv.sigmaEquivProd _ _)
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  letI : Nonempty (Fin (q-1)) := ⟨⟨0, by omega⟩⟩
  letI (i : Fin m) : Nonempty (A i) := ⟨e i ⟨0, by omega⟩⟩
  have hl (i : Fin m) : (𝔼 a : A i, flipSign x y i a.val) =
      if x i = y i then (-1 : ℚ) else 1-2/((q-1 : ℕ) : ℚ) := by
    by_cases hi : x i = y i
    · have he (a : A i) : a.val ≠ y i := by simpa [← hi] using a.2
      simp [flipSign, hi, he, Fintype.expect_const]
    · let b : A i := ⟨y i, Ne.symm hi⟩
      have he (a : A i) : flipSign x y i a.val = 1 - (if a = b then 2 else 0) := by
        by_cases ha : a = b
        · subst a
          norm_num [flipSign,hi,b]
        · have hn : a.val ≠ y i := fun h => ha (Subtype.ext h)
          simp [flipSign,hi,ha,hn]
      simp_rw [he, Finset.expect_sub_distrib, Fintype.expect_const]
      rw [Fintype.expect_eq_sum_div_card]
      simp [hi, hcard]
  calc
    _ = 𝔼 p : Fin m × Fin (q-1), flipSign x y p.1 ((e p.1 p.2).val) := by
      apply Fintype.expect_equiv ep
      intro a
      change _ = flipSign x y a.1 ((e a.1 ((e a.1).symm a.2)).val)
      rw [Equiv.apply_symm_apply]
    _ = 𝔼 i : Fin m, (𝔼 a : A i, flipSign x y i a.val) := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      apply Finset.expect_congr rfl
      intro i _
      exact Fintype.expect_equiv (e i) _ _ (fun _ => rfl)
    _ = _ := by
      simp_rw [hl]
      let α : ℚ := 1-2/((q-1 : ℕ) : ℚ)
      have he (i : Fin m) : (if x i = y i then (-1 : ℚ) else α) =
          α - (α+1) * (if x i = y i then 1 else 0) := by
        by_cases h : x i = y i <;> simp [h]
      change (𝔼 i : Fin m, if x i = y i then (-1 : ℚ) else α) = _
      simp_rw [he, Finset.expect_sub_distrib, Fintype.expect_const, ← Finset.mul_expect]
      rw [Fintype.expect_eq_sum_div_card, ← Finset.sum_filter]
      simp [Finset.sum_const, Fintype.card_fin, agreement, α] <;> ring

private theorem repetitions_card_mul {D A B : Type*} [Fintype D] [Fintype A] [Fintype B]
    [DecidableEq D] [DecidableEq A] [DecidableEq B]
    (proj : A → B) (X : Type*) [Fintype X] (e : A ≃ B × X)
    (he : ∀ a, (e a).1 = proj a) :
    (Finset.univ.filter (fun s : D → A => ¬ Function.Injective (proj ∘ s))).card *
      Fintype.card B ≤ Fintype.card D ^ 2 * Fintype.card (D → A) := by
  classical
  let P : Finset (D × D) := Finset.univ.filter fun p => p.1 ≠ p.2
  let C (p : D × D) : Finset (D → A) :=
    Finset.univ.filter fun s => proj (s p.1) = proj (s p.2)
  have hC (p : D × D) (hp : p ∈ P) :
      (C p).card * Fintype.card B = Fintype.card (D → A) := by
    let ef : (D → A) ≃ (D → B) × (D → X) :=
      { toFun := fun s => (fun i => (e (s i)).1, fun i => (e (s i)).2)
        invFun := fun f i => e.symm (f.1 i, f.2 i)
        left_inv := by intro s; funext i; exact e.symm_apply_apply (s i)
        right_inv := by intro f; ext i <;> simp }
    have hx : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    let eqv := ef.subtypeEquiv
      (p := fun s => proj (s p.1) = proj (s p.2))
      (q := fun f => f.1 p.1 = f.1 p.2)
      (fun s => by simpa [ef, he])
    let eqv' :
        {f : (D → B) × (D → X) // f.1 p.1 = f.1 p.2} ≃
          {f : D → B // f p.1 = f p.2} × (D → X) :=
      { toFun := fun f => (⟨f.1.1, f.2⟩, f.1.2)
        invFun := fun z => ⟨(z.1.1, z.2), z.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := Fintype.card_congr (eqv.trans eqv')
    rw [Fintype.card_prod, Fintype.card_subtype, Fintype.card_subtype] at hc
    unfold C
    rw [hc, mul_right_comm, collision_card_mul (V := B) hx, ← Fintype.card_prod,
      ← Fintype.card_congr ef]
  have hsub : Finset.univ.filter (fun s : D → A => ¬ Function.Injective (proj ∘ s)) ⊆
      P.biUnion C := by
    intro s hs
    have hi := (Finset.mem_filter.mp hs).2
    unfold Function.Injective at hi
    push Not at hi
    obtain ⟨a, b, hab, hne⟩ := hi
    exact Finset.mem_biUnion.mpr
      ⟨(a,b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩
  calc
    _ ≤ (∑ p ∈ P, (C p).card) * Fintype.card B :=
      Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
    _ = P.card * Fintype.card (D → A) := by
      rw [Finset.sum_mul]
      calc
        _ = ∑ _ ∈ P, Fintype.card (D → A) := Finset.sum_congr rfl hC
        _ = _ := by simp
    _ ≤ _ := by
      have hp : P.card ≤ Fintype.card D ^ 2 := by
        simpa [P, pow_two, Fintype.card_prod] using
          Finset.card_filter_le (Finset.univ : Finset (D × D)) (fun p => p.1 ≠ p.2)
      exact Nat.mul_le_mul_right _ hp

private theorem uniform_shell_correlation {m q d : ℕ} (hm : 0 < m) (hq : 1 < q)
    (hd : d ≤ m) (x y : Fin m → Fin q) :
    let lam := 1 - 2 * (agreement x y + (1 - agreement x y) / ((q - 1 : ℕ) : ℚ))
    |(𝔼 c : {u // (changes x u).card = d},
       matchSign x y * matchSign c.val y) - lam^d| ≤
       2 * (d : ℚ)^2 / m := by
  classical
  let A := (i : Fin m) × {v : Fin q // v ≠ x i}
  let S := Fin d → A
  let p : S → Prop := fun s => Function.Injective (fun j => (s j).1)
  let G : Finset S := Finset.univ.filter p
  let F : S → ℚ := fun s => ∏ j, flipSign x y (s j).1 (s j).2.val
  let e (i : Fin m) : Fin (q-1) ≃ {v : Fin q // v ≠ x i} :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq])
  let ep : A ≃ Fin m × Fin (q-1) :=
    (Equiv.sigmaCongrRight (fun i => (e i).symm)).trans (Equiv.sigmaEquivProd _ _)
  let a (i : Fin m) : {v : Fin q // v ≠ x i} := e i ⟨0, by omega⟩
  let s₀ : S := fun j => ⟨Fin.castLEEmb hd j, a (Fin.castLEEmb hd j)⟩
  letI : Nonempty S := ⟨s₀⟩
  have hG : G.Nonempty :=
    ⟨s₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Fin.castLEEmb hd).injective⟩⟩
  have hF (s : S) : |F s| ≤ 1 := by
    simp [F, Finset.abs_prod, flipSign_bounds]
  have hω : Gᶜ.card * m ≤ d^2 * Fintype.card S := by
    have he : Gᶜ = Finset.univ.filter (fun s : S => ¬ p s) := by
      ext s
      simp [G]
    rw [he]
    simpa [p, S, Function.comp_def] using repetitions_card_mul
      (D := Fin d) (fun a : A => a.1) (Fin (q-1)) ep (fun _ => rfl)
  have hm' : 0 < (m : ℚ) := by exact_mod_cast hm
  have hS : 0 < (Fintype.card S : ℚ) := by exact_mod_cast Fintype.card_pos
  have hω' : (Gᶜ.card : ℚ) / Fintype.card S ≤ (d : ℚ)^2 / m :=
    (div_le_div_iff₀ hS hm').mpr (by exact_mod_cast hω)
  have hB : |(𝔼 s, F s) - (𝔼 s ∈ G, F s)| ≤ 2*(d : ℚ)^2/m := by
    refine (average_filter_error G hG F hF).trans ?_
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hω' (by norm_num : 0 ≤ (2 : ℚ))
  have hp : (𝔼 s ∈ G, F s) = 𝔼 s : {s : S // p s}, F s.val := by
    rw [Finset.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, Fintype.card_subtype]
    rw [Finset.sum_subtype (p := p) G (fun s => by simp [G]) F]
  have ha := Fintype.expect_equiv (injectiveEquiv (d := d) x) (fun s : {s : S // p s} => F s.val)
    (fun a => matchSign x y * matchSign (realize x a.1 a.2) y)
    (fun s => (descriptor_sign x y (injectiveEquiv x s).1 (injectiveEquiv x s).2).symm)
  have henc := shell_average_encoding (d := d) x
    (fun c => matchSign x y * matchSign c y)
  rw [henc] at ha
  have hfull : (𝔼 s, F s) =
      (1 - 2 * (agreement x y + (1 - agreement x y) / ((q - 1 : ℕ) : ℚ)))^d :=
    (average_single_flips_pow (d := d) x y).trans (by rw [mean_flip_formula hm hq])
  rw [hp, ha, hfull, abs_sub_comm] at hB
  exact hB

open scoped BigOperators

private theorem assemble {W S H T : Type} [Fintype S] [Fintype H] [Fintype T]
    [Nonempty S] [Nonempty H]
    (f : W → W → Bool) (left right : W → Bool)
    (sendS : S → W → T) (readS : S → T → W → Bool)
    (sendH : H → W → T) (readH : H → T → W → Bool)
    (p δ e_s e_h bonus : ℚ)
    (hp : 0 < p) (hp' : p < 1) (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (he_s : 0 ≤ e_s) (he_h : 0 ≤ e_h) (hbonus : bonus + e_s + e_h ≤ δ / 6)
    (near : W → W → Prop)
    (hs : ∀ x y, -e_s ≤ (𝔼 s, score (readS s (sendS s x) y) (f x y)))
    (hs_near : ∀ x y, near x y →
      p + δ - e_s ≤ (𝔼 s, score (readS s (sendS s x) y) (f x y)))
    (hh : ∀ x y, -e_h ≤ (𝔼 s, score (readH s (sendH s x) y) (f x y)))
    (hh_far : ∀ x y, ¬ near x y →
      1 - e_h ≤ (𝔼 s, score (readH s (sendH s x) y) (f x y))) :
    ∃ (M z : ℕ) (send : Fin z → W → Fin M) (read : Fin z → Fin M → W → Bool),
      0 < z ∧ M = 2 * Fintype.card T ∧
      ∀ x y, (1 + (p / (1+p) + bonus)) * (z : ℚ) ≤
        2 * ((Finset.univ.filter
          (fun s => read s (send s x) y = xor (xor (left x) (right y)) (f x y))).card : ℚ) := by
  let w : ℚ := 1 / (1+p+δ)
  have hden : 0 < 1+p+δ := by linarith
  have hw₀ : 0 ≤ w := (one_div_pos.mpr hden).le
  have hw₁ : w ≤ 1 := (div_le_one hden).mpr (by linarith)
  obtain ⟨a, b, hb, hab, hw⟩ := coin_parameters w hw₀ hw₁
  let Z := Fin b × (S × H)
  letI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  let send : Z → W → T := fun s x =>
    if s.1.val < a then sendS s.2.1 x else sendH s.2.2 x
  let read : Z → T → W → Bool := fun s t y =>
    if s.1.val < a then readS s.2.1 t y else readH s.2.2 t y
  apply toAssignedProtocol f left right send read (p / (1+p) + bonus)
  intro x y
  have hpoint (s : Z) : score (read s (send s x) y) (f x y) =
      if s.1.val < a then score (readS s.2.1 (sendS s.2.1 x) y) (f x y)
      else score (readH s.2.2 (sendH s.2.2 x) y) (f x y) := by
    by_cases h : s.1.val < a <;> simp [send, read, h]
  have hm := mix_average a b hb hab
    (fun s => score (readS s (sendS s x) y) (f x y))
    (fun s => score (readH s (sendH s x) y) (f x y))
  have hg := combine_advantages p δ e_s e_h bonus hp hp' hδ hδ'
    he_s he_h hbonus _ _ (near x y) (hs x y) (hs_near x y) (hh x y) (hh_far x y)
  change p / (1+p) + bonus ≤ _ at hg
  have hmean : p / (1+p) + bonus ≤ 𝔼 s : Z, score (read s (send s x) y) (f x y) := by
    simp_rw [hpoint]
    rw [hm, hw]
    exact hg
  rw [score_correct_count] at hmean
  have hcard : 0 < (Fintype.card Z : ℚ) := by exact_mod_cast Fintype.card_pos
  exact (le_div_iff₀ hcard).mp (by linarith)

open scoped BigOperators

private theorem randomize_decoder {W S T : Type} [Fintype S] [Nonempty S] [Fintype T] [Fintype W]
    (send : S → W → T) (base : S → T → W → Bool)
    (accept : S → T → W → ℚ) (f : W → W → Bool)
    (h₀ : ∀ s t y, 0 ≤ accept s t y) (h₁ : ∀ s t y, accept s t y ≤ 1) :
    ∃ (Z : Type) (_ : Fintype Z) (_ : Nonempty Z) (send' : Z → W → T) (read' : Z → T → W → Bool),
      ∀ x y, (𝔼 s, score (read' s (send' s x) y) (f x y)) =
        𝔼 s, accept s (send s x) y * score (base s (send s x) y) (f x y) := by
  classical
  choose a b hb hab he using
    (fun p : S × T × W => coin_parameters (accept p.1 p.2.1 p.2.2)
      (h₀ p.1 p.2.1 p.2.2) (h₁ p.1 p.2.1 p.2.2))
  let J := (p : S × T × W) → Fin (b p)
  let Z := S × (J × Bool)
  letI (p : S × T × W) : Nonempty (Fin (b p)) := ⟨⟨0, hb p⟩⟩
  let read (s : Z) (t : T) (y : W) :=
    if (s.2.1 (s.1,t,y)).val < a (s.1,t,y) then base s.1 t y else s.2.2
  refine ⟨Z, inferInstance, inferInstance, fun s x => send s.1 x, read, ?_⟩
  intro x y
  rw [← Finset.univ_product_univ, Finset.expect_product]
  apply Finset.expect_congr rfl
  intro s _
  let t := send s x
  let p : S × T × W := (s,t,y)
  change (𝔼 jb : J × Bool, score (read (s,jb) t y) (f x y)) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  have hfun (j : J) :
      (𝔼 v : Bool, score (read (s,j,v) t y) (f x y)) =
        if (j p).val < a p then score (base s t y) (f x y) else 0 := by
    change (𝔼 v : Bool, score (if (j p).val < a p then base s t y else v) (f x y)) = _
    by_cases h : (j p).val < a p
    · simp only [h, ↓reduceIte]
      exact Fintype.expect_const (ι := Bool) _
    · simp only [h, ↓reduceIte]
      exact score_fair _
  simp_rw [hfun]
  let F : Fin (b p) → ℚ := fun j => if j.val < a p then score (base s t y) (f x y) else 0
  change (𝔼 j : J, F (j p)) = _
  rw [average_eval (V := fun p => Fin (b p)) p F]
  change (𝔼 j : Fin (b p), if j.val < a p then score (base s t y) (f x y) else 0) = _
  rw [coin_average _ _ (hb p) (hab p), he p, mul_zero, add_zero]

open scoped BigOperators

private theorem score_center {m q : ℕ} (x c y : Fin m → Fin q) :
    score (parity c y) (parity x y) = matchSign x y * matchSign c y := by
  rw [sign_of_parity, sign_of_parity]
  cases parity x y <;> cases parity c y <;> norm_num [score]

private theorem sparse_comparison {m q r L : ℕ} (hm : 0 < m) (hq : 1 < q)
    (hr : r ≤ m) (hL : 0 < L) (x y : Fin m → Fin q)
    (c₀ t : ℚ) (ht : 0 < t) :
    letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
    let W := Fin m → Fin q
    let G := gate c₀ t
    let d := fun c : W => (changes x c).card
    let choice := fun s : Fin L → W => s (nearest (d ∘ s))
    let lam := 1 - 2 * (agreement x y + (1 - agreement x y) / ((q - 1 : ℕ) : ℚ))
    G (agreement x y) * (𝔼 s, if d (choice s) ≤ r then lam^(d (choice s)) else 0) -
        (2*(r : ℚ)^2 / m + r / (m*t)) ≤
      𝔼 s, if d (choice s) ≤ r then
        G (agreement (choice s) y) * score (parity (choice s) y) (parity x y) else 0 := by
  classical
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  let W := Fin m → Fin q
  letI : Nonempty W := ⟨x⟩
  let G := gate c₀ t
  let d := fun c : W => (changes x c).card
  let choice := fun s : Fin L → W => s (nearest (d ∘ s))
  let lam := 1 - 2 * (agreement x y + (1 - agreement x y) / ((q - 1 : ℕ) : ℚ))
  let f : W → ℚ := fun c => score (parity c y) (parity x y)
  let a := G (agreement x y)
  let E := 2*(r : ℚ)^2 / m
  let E' := (r : ℚ)/(m*t)
  let pred : W → ℚ := fun c => if d c ≤ r then lam^(d c) else 0
  let mid : W → ℚ := fun c => if d c ≤ r then a * f c else 0
  let out : W → ℚ := fun c => if d c ≤ r then G (agreement c y) * f c else 0
  have h₁ : a * (𝔼 s, pred (choice s)) - E ≤ 𝔼 s, mid (choice s) := by
    let h : W → ℚ := fun c => mid c - a * pred c + E
    have hfiber (j : ℕ) : 0 ≤ ∑ c ∈ Finset.univ.filter (fun c : W => d c = j), h c := by
      let B := Finset.univ.filter (fun c : W => d c = j)
      by_cases hj : j ≤ r
      · have hjm := hj.trans hr
        have hp := uniform_shell_correlation (d := j) hm hq hjm x y
        dsimp only at hp
        simp only [← score_center] at hp
        have hav : (𝔼 c ∈ B, f c) = 𝔼 c : {u : W // d u = j}, f c.val := by
          rw [Finset.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, Fintype.card_subtype]
          rw [Finset.sum_subtype (p := fun c => d c = j) B (fun c => by simp [B]) f]
        have herr : (𝔼 c ∈ B, f c) - lam^j ≥ -E := by
          rw [hav]
          have hE : 2*(j : ℚ)^2 / m ≤ E := by
            dsimp [E]
            gcongr
          exact (abs_le.mp (hp.trans hE)).1
        have hsum : 0 ≤ (B.card : ℚ) * ((𝔼 c ∈ B, f c) - lam^j + E) :=
          mul_nonneg (Nat.cast_nonneg _) (by linarith)
        have hsum' : 0 ≤ (∑ c ∈ B, f c) - (B.card : ℚ) * lam^j + (B.card : ℚ)*E := by
          by_cases hb : B.card = 0
          · simp [Finset.card_eq_zero.mp hb]
          have hbc : (B.card : ℚ) ≠ 0 := by exact_mod_cast hb
          rw [Finset.expect_eq_sum_div_card, mul_add, mul_sub, mul_div_cancel₀ _ hbc] at hsum
          exact hsum
        have hmul := mul_nonneg (gate_nonneg c₀ t (agreement x y)) hsum'
        have hrem := mul_nonneg (sub_nonneg.mpr (gate_le_one c₀ t (agreement x y)))
          (show 0 ≤ (B.card : ℚ)*E by positivity)
        change 0 ≤ ∑ c ∈ B, h c
        have he (c : W) (hc : c ∈ B) : h c = a * f c - a * lam^j + E := by
          have hc' : d c = j := (Finset.mem_filter.mp hc).2
          simp [h, mid, pred, hc', hj]
        rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        change 0 ≤ a * (∑ c ∈ B, f c) - (B.card : ℚ) * (a * lam^j) + (B.card : ℚ) * E
        change 0 ≤ a * _ at hmul
        change 0 ≤ (1-a)*_ at hrem
        calc
          0 ≤ a * ((∑ c ∈ B, f c) - (B.card : ℚ) * lam^j + (B.card : ℚ)*E) +
              (1-a)*((B.card : ℚ)*E) := add_nonneg hmul hrem
          _ = _ := by ring
      · apply Finset.sum_nonneg
        intro c hc
        have hdc := (Finset.mem_filter.mp hc).2
        simp only [h, mid, pred, hdc, hj, ↓reduceIte, mul_zero, sub_self, zero_add]
        positivity
    have hh := nonneg_of_equal_fibers choice d h
      (fun u v huv => equal_distance_equal_count d nearest u v huv) hfiber
    have hf : 0 ≤ 𝔼 s : Fin L → W, h (choice s) := by
      rw [Fintype.expect_eq_sum_div_card]
      exact div_nonneg hh (Nat.cast_nonneg _)
    simp only [h, Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
      Fintype.expect_const] at hf
    linarith
  have h₂ : (𝔼 s, mid (choice s)) - E' ≤ 𝔼 s, out (choice s) := by
    rw [← Fintype.expect_const (ι := Fin L → W) E', ← Finset.expect_sub_distrib]
    apply Finset.expect_le_expect
    intro s _
    let c := choice s
    change mid c - E' ≤ out c
    by_cases hc : d c ≤ r
    · have hgate := (gate_lipschitz c₀ t (agreement c y) (agreement x y) ht).trans
        (div_le_div_of_nonneg_right (agreement_lipschitz x c y) ht.le)
      have herr : |G (agreement c y) - a| ≤ E' := by
        refine hgate.trans ?_
        rw [div_div]
        change ((changes x c).card : ℚ)/(m*t) ≤ (r : ℚ)/(m*t)
        exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      have hf' : |f c| = 1 := score_bounds _ _
      have he : |(G (agreement c y) - a) * f c| ≤ E' := by
        rw [abs_mul, hf', mul_one]
        exact herr
      have h' := (abs_le.mp he).1
      simp only [sub_mul] at h'
      simpa [mid, out, hc] using (show a*f c - E' ≤ G (agreement c y)*f c by linarith)
    · have he : 0 ≤ E' := by positivity
      simp [mid, out, hc, he]
  change a * (𝔼 s, pred (choice s)) - (E+E') ≤ 𝔼 s, out (choice s)
  linarith

private theorem ideal_advantage {S : Type*} [Fintype S] [Nonempty S] (d : S → ℕ)
    (r : ℕ) (hr : 0 < r) (p g lam B F E : ℚ)
    (hlam : 0 ≤ lam) (hlam₁ : lam ≤ 1) (hg : g ≤ lam^(r-1)*(1-lam)) (hg₀ : 0 ≤ g)
    (hpow : p - E ≤ lam^r) (hB : B ≤ 𝔼 s, if d s ≤ r-1 then (1 : ℚ) else 0)
    (hF : (𝔼 s, if r < d s then (1 : ℚ) else 0) ≤ F) :
    p - E + g*B - F ≤ 𝔼 s, if d s ≤ r then lam^(d s) else 0 := by
  classical
  have hpoint (s : S) : lam^r + g*(if d s ≤ r-1 then 1 else 0) -
      (if r < d s then 1 else 0) ≤ if d s ≤ r then lam^(d s) else 0 := by
    by_cases hs : d s ≤ r
    · have hlt : ¬ r < d s := not_lt_of_ge hs
      by_cases h : d s ≤ r-1
      · have hle := pow_le_pow_of_le_one hlam hlam₁ h
        have hsub : r-1+1 = r := by omega
        have he : lam^r + lam^(r-1)*(1-lam) = lam^(r-1) := by
          have heq : lam^r = lam^(r-1)*lam := (congrArg (lam ^ ·) hsub.symm).trans (pow_succ _ _)
          rw [heq]
          ring
        simp only [hs, hlt, h, ↓reduceIte, mul_one, sub_zero]
        linarith
      · have hle := pow_le_pow_of_le_one hlam hlam₁ hs
        simpa [hs, hlt, h] using hle
    · have hn : ¬ d s ≤ r-1 := by omega
      have ht : r < d s := Nat.lt_of_not_ge hs
      simpa [hs,hn,ht] using (sub_nonpos.mpr (pow_le_one₀ hlam hlam₁ (n := r)))
  have hh := Finset.expect_le_expect (s := (Finset.univ : Finset S)) (fun s _ => hpoint s)
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
    Fintype.expect_const] at hh
  have hmul := mul_le_mul_of_nonneg_left hB hg₀
  linarith

private theorem lam_approx (q : ℕ) (hq : 5 ≤ q) (a : ℚ) :
    |(1 - 2*(a + (1-a)/((q-1 : ℕ) : ℚ))) - (1 - 4/(q : ℚ))| ≤
      2*|a-1/(q : ℚ)| := by
  have hq' : (1 : ℚ) < q := by exact_mod_cast (show 1 < q by omega)
  have hq₂ : (2 : ℚ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hq₁ : (1 : ℚ) ≤ q := hq'.le
  have hsub : ((q-1 : ℕ) : ℚ) = (q : ℚ)-1 := by exact_mod_cast Nat.cast_sub (R := ℚ) (show 1 ≤ q by omega)
  rw [hsub]
  have he : 1 - 2*(a + (1-a)/((q : ℚ)-1)) - (1-4/(q : ℚ)) =
      -2 * (((q : ℚ)-2)/((q : ℚ)-1)) * (a-1/(q : ℚ)) := by
    have h₁ : (q : ℚ) ≠ 0 := by linarith
    have h₂ : (q : ℚ)-1 ≠ 0 := by linarith
    field_simp
    ring
  rw [he, abs_mul, abs_mul, show |(-2 : ℚ)| = 2 by norm_num]
  have h₀ : 0 ≤ ((q : ℚ)-2)/((q : ℚ)-1) := div_nonneg (by linarith) (by linarith)
  rw [abs_of_nonneg h₀]
  have hle : ((q : ℚ)-2)/((q : ℚ)-1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  calc
    _ ≤ (2*1)*|a-1/(q : ℚ)| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by norm_num)) (abs_nonneg _)
    _ = _ := by ring

private theorem sparse_protocol {m q r L : ℕ} (hm : 0 < m) (hq : 1 < q)
    (hr : r ≤ m) (hL : 0 < L) (c₀ t : ℚ) (ht : 0 < t) :
    letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
    let W := Fin m → Fin q
    ∃ (S : Type) (_ : Fintype S) (_ : Nonempty S) (send : S → W → Option (Fin L))
      (read : S → Option (Fin L) → W → Bool),
      ∀ x y,
        let d := fun c : W => (changes x c).card
        let choice := fun s : Fin L → W => s (nearest (d ∘ s))
        let lam := 1 - 2*(agreement x y + (1-agreement x y)/((q-1 : ℕ) : ℚ))
        gate c₀ t (agreement x y) * (𝔼 s, if d (choice s) ≤ r then lam^(d (choice s)) else 0) -
          (2*(r : ℚ)^2/m + r/(m*t)) ≤
          (𝔼 s, score (read s (send s x) y) (parity x y)) := by
  classical
  let W := Fin m → Fin q
  letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  letI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  let send : (Fin L → W) → W → Option (Fin L) := fun s x =>
    let d := fun c : W => (changes x c).card
    let i := nearest (d ∘ s)
    if d (s i) ≤ r then some i else none
  let base : (Fin L → W) → Option (Fin L) → W → Bool := fun s i y =>
    match i with
    | some j => parity (s j) y
    | none => false
  let accept : (Fin L → W) → Option (Fin L) → W → ℚ := fun s i y =>
    match i with
    | some j => gate c₀ t (agreement (s j) y)
    | none => 0
  have h₀ : ∀ s i y, 0 ≤ accept s i y := by
    intro s i y
    cases i <;> simp [accept, gate_nonneg]
  have h₁ : ∀ s i y, accept s i y ≤ 1 := by
    intro s i y
    cases i <;> simp [accept, gate_le_one]
  obtain ⟨S, hS, hn, send', read', hEq⟩ :=
    randomize_decoder send base accept parity h₀ h₁
  refine ⟨S, hS, hn, send', read', ?_⟩
  intro x y
  dsimp only
  rw [hEq]
  have he (s : Fin L → W) :
      accept s (send s x) y * score (base s (send s x) y) (parity x y) =
        let d := fun c : W => (changes x c).card
        let c := s (nearest (d ∘ s))
        if d c ≤ r then gate c₀ t (agreement c y) * score (parity c y) (parity x y) else 0 := by
    dsimp only [send]
    split_ifs <;> simp [accept, base]
  simp_rw [he]
  exact sparse_comparison hm hq hr hL x y c₀ t ht

private theorem sparse_estimates {m q r L k : ℕ} (hm : 0 < m) (hq : 5 ≤ q) (hr : 0 < r)
    (hrm : r ≤ m) (hL : 0 < L) (hk : 0 < k)
    (b A t : ℚ) (hb : 0 < b) (hA : 0 < A) (ht : 0 < t) :
    letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
    let W := Fin m → Fin q
    let rho := 1 - 4/(q : ℚ)
    let g := (rho/2)^(r-1)*(1-rho)/2
    let error := 2*(r : ℚ)^2/m + r/(m*(t/k)) + A*k/m
    4*t ≤ rho/2 → 4*t ≤ (1-rho)/2 → 2*r*t ≤ b*g/4 →
    (∀ x : W,
      let d := fun c : W => (changes x c).card
      let D := fun s : Fin L → W => d (s (nearest (d ∘ s)))
      b/(k : ℚ) ≤ (𝔼 s, if D s ≤ r-1 then (1 : ℚ) else 0) ∧
        (𝔼 s, if r < D s then (1 : ℚ) else 0) ≤ A*k/m) →
    ∃ (S : Type) (_ : Fintype S) (_ : Nonempty S) (send : S → W → Option (Fin L))
      (read : S → Option (Fin L) → W → Bool),
      (∀ x y, -error ≤ 𝔼 s, score (read s (send s x) y) (parity x y)) ∧
      ∀ x y, |agreement x y - 1/(q : ℚ)| ≤ t/k →
        rho^r + 3*b*g/(4*k) - error ≤ 𝔼 s, score (read s (send s x) y) (parity x y) := by
  classical
  let W := Fin m → Fin q
  let rho : ℚ := 1 - 4/(q : ℚ)
  let g : ℚ := (rho/2)^(r-1)*(1-rho)/2
  let err : ℚ := 2*(r : ℚ)^2/m + r/(m*(t/k)) + A*k/m
  change 4*t ≤ rho/2 → 4*t ≤ (1-rho)/2 → 2*r*t ≤ b*g/4 → _ → _
  intro htr₀ htr₁ htg hprob
  have hq' : (4 : ℚ) < q := by exact_mod_cast (show 4 < q by omega)
  have hq₀ : 0 < (q : ℚ) := by linarith
  have hρ₀ : 0 < rho := sub_pos.mpr ((div_lt_one hq₀).mpr hq')
  have hρ₁ : rho < 1 := by
    dsimp [rho]
    have h : (0 : ℚ) < 4/q := by positivity
    linarith
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hk' : 0 < (k : ℚ) := by exact_mod_cast hk
  have hk₁ : 1 ≤ (k : ℚ) := by exact_mod_cast (show 1 ≤ k by omega)
  have ht' : 0 < t / (k : ℚ) := by positivity
  letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  letI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  obtain ⟨S, hS, hn, send, read, hs⟩ :=
    sparse_protocol (q := q) hm (by omega) hrm hL (1/q) (t/k) ht'
  refine ⟨S,hS,hn,send,read,?_,?_⟩
  · intro x y
    specialize hs x y
    dsimp only at hs
    have hG : 0 ≤ gate (1/q) (t/k) (agreement x y) := gate_nonneg _ _ _
    have hn' : 0 ≤ gate (1/q) (t/k) (agreement x y) *
        (𝔼 s : Fin L → W, if (changes x (s (nearest ((fun c : W => (changes x c).card) ∘ s)))).card ≤ r
          then (1 - 2*(agreement x y + (1-agreement x y)/((q-1 : ℕ) : ℚ))) ^
            (changes x (s (nearest ((fun c : W => (changes x c).card) ∘ s)))).card else 0) := by
      rcases hG.eq_or_lt with h | h
      · rw [← h, zero_mul]
      apply mul_nonneg hG
      have hnear := near_of_gate_pos _ _ _ ht' h
      have hdist := lam_approx q hq (agreement x y)
      have hsmall : |agreement x y - 1/(q : ℚ)| ≤ 2*t := by
        have hh : t/(k : ℚ) ≤ t := by
          apply (div_le_iff₀ hk').mpr
          nlinarith
        linarith
      have hlam : 0 ≤ 1 - 2*(agreement x y + (1-agreement x y)/((q-1 : ℕ) : ℚ)) := by
        change |(1 - 2*(agreement x y + (1-agreement x y)/((q-1 : ℕ) : ℚ))) - rho| ≤ _ at hdist
        linarith [(abs_le.mp hdist).1]
      exact Finset.expect_nonneg fun s _ => by split_ifs <;> positivity
    have hE : 0 ≤ A*k/m := by positivity
    change -err ≤ _
    dsimp [err]
    linarith
  · intro x y hxy
    specialize hs x y
    have hgate := gate_of_near (1/q) (t/k) (agreement x y) ht' hxy
    dsimp only at hs
    rw [hgate, one_mul] at hs
    let lam := 1 - 2*(agreement x y + (1-agreement x y)/((q-1 : ℕ) : ℚ))
    have hdist : |lam-rho| ≤ 2*(t/k) := (lam_approx q hq _).trans (by gcongr)
    have htK : t/(k : ℚ) ≤ t := (div_le_iff₀ hk').mpr (by nlinarith)
    have hl₀ : rho/2 ≤ lam := by linarith [(abs_le.mp hdist).1]
    have hl₁ : lam ≤ (1+rho)/2 := by linarith [(abs_le.mp hdist).2]
    have hl₀' : 0 ≤ lam := by linarith
    have hl₁' : lam ≤ 1 := by linarith
    have hgap : g ≤ lam^(r-1)*(1-lam) := by
      dsimp [g]
      rw [mul_div_assoc]
      gcongr
      linarith
    have hpow := abs_pow_sub_le rho lam
      (by rw [abs_of_pos hρ₀]; exact hρ₁.le) (by rw [abs_of_nonneg hl₀']; exact hl₁') r
    have hpow' : rho^r - 2*r*t/k ≤ lam^r := by
      have h := (abs_le.mp hpow).1
      have hh := mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg r)
      have he : (r : ℚ) * (2 * (t/k)) = 2*r*t/k := by ring
      rw [he] at hh
      linarith
    obtain ⟨hB,hF⟩ := hprob x
    have hIdeal := ideal_advantage _ r hr (rho^r) g lam (b/k) (A*k/m) (2*r*t/k)
      hl₀' hl₁' hgap hg hpow' hB hF
    have hbonus : 2*(r : ℚ)*t/k ≤ b*g/(4*k) := by
      rw [show b*g/(4*(k : ℚ)) = b*g/4/k by ring]
      exact div_le_div_of_nonneg_right htg hk'.le
    change rho^r + 3*b*g/(4*k) - err ≤ _
    dsimp [err, lam] at hIdeal ⊢
    have he : 3*b*g/(4*(k : ℚ)) = g*(b/k) - b*g/(4*k) := by ring
    rw [he]
    linarith only [hs, hIdeal, hbonus]

open scoped BigOperators

private theorem exact_miss_prob {W : Type*} [Fintype W] [Nonempty W]
    {L : ℕ} (hL : 0 < L) (dist : W → ℕ) (d : ℕ) :
    letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
    let outcome := fun s : Fin L → W => dist (s (nearest (dist ∘ s)))
    (𝔼 s, if d < outcome s then (1 : ℚ) else 0) =
      (1 - ((Finset.univ.filter fun w => dist w ≤ d).card : ℚ) / Fintype.card W)^L := by
  classical
  letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  dsimp
  rw [average_indicator, selected_miss_count dist d, Fintype.card_fin, Fintype.card_fun]
  push_cast
  rw [Fintype.card_fin, ← div_pow]
  congr 1
  have hw : 0 < (Fintype.card W : ℚ) := by exact_mod_cast Fintype.card_pos
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset W))
    (p := fun w => dist w ≤ d)
  simp only [not_le, Finset.card_univ] at h
  have h' : ((Finset.univ.filter fun w => dist w ≤ d).card : ℚ) +
      ((Finset.univ.filter fun w => d < dist w).card : ℚ) = Fintype.card W := by exact_mod_cast h
  field_simp
  linarith

private theorem miss_upper {L : ℕ} (v a : ℝ) (hv : v ≤ 1)
    (ha : a ≤ L*v) :
    (1-v)^L ≤ Real.exp (-a) :=
  (miss_exp v hv L).trans (Real.exp_le_exp.mpr (by linarith))

private theorem hit_lower {L : ℕ} (v b k : ℝ) (hv : v ≤ 1)
    (hb : 0 ≤ b) (hb' : b ≤ 1) (hk : 1 ≤ k) (h : b/k ≤ L*v) :
    b/(2*k) ≤ 1-(1-v)^L := by
  have hk' : 0 < k := by linarith
  have hs : 0 ≤ b/k := by positivity
  have hb₁ : 1+b/k ≤ 2 := by
    have he : b/k ≤ 1 := (div_le_one hk').mpr (hb'.trans hk)
    linarith
  have hc := one_sub_exp_neg_lower (b/k) hs
  have he : b/(2*k) = (b/k)/2 := by ring
  rw [he]
  have hc' := div_le_div_of_nonneg_left hs (show 0 < 1 + b/k by linarith) hb₁
  linarith [miss_upper v (b/k) hv h]

private theorem hash_tail_exponent {m k C r : ℕ} (hm : 0 < m) (hk : 0 < k) (t : ℝ)
    (hC : 2*(C : ℝ)*t^2 ≥ r+1) (h : C*k^2*(1+m.log2) ≤ m) :
    Real.exp (-2*m*(t/k)^2) ≤ 1/(m : ℝ)^(r+1) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hc : (C : ℝ)*(k : ℝ)^2*(1+m.log2) ≤ m := by exact_mod_cast h
  have hmC : (C : ℝ)*(1+m.log2) ≤ m/(k : ℝ)^2 :=
    (le_div_iff₀ (pow_pos hk' _)).mpr (by linear_combination hc)
  have hl : (r+1 : ℝ)*Real.log m ≤ 2*m*(t/k)^2 := by
    have hlogs : Real.log (m : ℝ) ≤ (1+m.log2 : ℝ) := log_le_binary m hm
    calc
      _ ≤ (r+1 : ℝ)*(1+m.log2) := mul_le_mul_of_nonneg_left hlogs (by positivity)
      _ ≤ (2*(C : ℝ)*t^2)*(1+m.log2) := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = (2*t^2)*((C : ℝ)*(1+m.log2)) := by ring
      _ ≤ (2*t^2)*(m/(k : ℝ)^2) := mul_le_mul_of_nonneg_left hmC (by positivity)
      _ = _ := by rw [div_pow]; ring
  calc
    _ ≤ Real.exp (-((r+1 : ℕ) : ℝ)*Real.log m) := by
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    _ = _ := by
      rw [neg_mul, Real.exp_neg, ← Real.log_pow, Real.exp_log (pow_pos hm' _), one_div]

open scoped BigOperators

private noncomputable def shellConstant (q j : ℕ) : ℝ :=
  ((q - 1 : ℕ) : ℝ)^j / (2^j * j.factorial)

private theorem shellConstant_pos {q : ℕ} (hq : 1 < q) (j : ℕ) :
    0 < shellConstant q j := by
  unfold shellConstant
  have h : 0 < ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < q - 1 by omega)
  positivity

private theorem ball_lower {m q j : ℕ} (hm : 2*j ≤ m) (x : Fin m → Fin q) :
    shellConstant q j * (m : ℝ)^j ≤
      ((Finset.univ.filter (fun u => (changes x u).card ≤ j)).card : ℝ) := by
  have h := shell_lower m q j hm
  refine h.trans ?_
  have he := shell_card (d := j) x
  have hsub : (Finset.univ.filter (fun u => (changes x u).card = j)) ⊆
      (Finset.univ.filter (fun u => (changes x u).card ≤ j)) := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.le⟩
  have hc := Finset.card_le_card hsub
  rw [he] at hc
  exact_mod_cast hc

private theorem sampling_probabilities {m q r k L : ℕ} (hm : 0 < m) (hq : 1 < q)
    (hr : 0 < r) (hk : 0 < k) (hL : 0 < L) (hmr : 2*r ≤ m)
    (hLD : q^m ≤ L*k*m^(r-1)) (x : Fin m → Fin q)
    (b : ℚ) (hb : 0 < b) (hb' : (2*b : ℚ) ≤ 1)
    (hb'' : (2*b : ℝ) ≤ shellConstant q (r-1))
    (A : ℚ) (hA : 0 < A) (hA' : 1 / (A : ℝ) ≤ shellConstant q r) :
    letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
    let d := fun c : Fin m → Fin q => (changes x c).card
    let D := fun s : Fin L → (Fin m → Fin q) => d (s (nearest (d ∘ s)))
    b/(k : ℚ) ≤ (𝔼 s, if D s ≤ r-1 then (1 : ℚ) else 0) ∧
      (𝔼 s, if r < D s then (1 : ℚ) else 0) ≤ A*k/m := by
  classical
  let W := Fin m → Fin q
  letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  let d := fun c : W => (changes x c).card
  let D := fun s : Fin L → W => d (s (nearest (d ∘ s)))
  let R (j : ℕ) : ℝ := ((Finset.univ.filter (fun u : W => d u ≤ j)).card : ℝ) / (q : ℝ)^m
  letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  letI : Nonempty W := ⟨x⟩
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hq' : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqm : 0 < (q : ℝ)^m := pow_pos hq' _
  have hD : 0 < (k : ℝ)*(m : ℝ)^(r-1) := by positivity
  have hspan : (q : ℝ)^m / ((k : ℝ)*(m : ℝ)^(r-1)) ≤ L := by
    apply (div_le_iff₀ hD).mpr
    have h := (show (q : ℝ)^m ≤ (L : ℝ)*k*(m : ℝ)^(r-1) by exact_mod_cast hLD)
    simpa [mul_assoc] using h
  have hR (j : ℕ) : R j ≤ 1 := by
    apply (div_le_one hqm).mpr
    have hc := (Finset.card_filter_le (Finset.univ : Finset W) (fun u => d u ≤ j))
    have hcn : (Finset.univ.filter (fun u : W => d u ≤ j)).card ≤ q^m := by
      simpa [W, Fintype.card_fun] using hc
    exact_mod_cast hcn
  have hbL (j : ℕ) (hj : 2*j ≤ m) :
      shellConstant q j * (m : ℝ)^j / ((k : ℝ)*(m : ℝ)^(r-1)) ≤ (L : ℝ)*R j := by
    have hb₀ := ball_lower (q := q) hj x
    have h := mul_le_mul_of_nonneg_right hspan (show 0 ≤ R j by positivity)
    calc
      _ ≤ ((Finset.univ.filter (fun u : W => d u ≤ j)).card : ℝ) /
          ((k : ℝ)*(m : ℝ)^(r-1)) := div_le_div_of_nonneg_right hb₀ hD.le
      _ = ((q : ℝ)^m / ((k : ℝ)*(m : ℝ)^(r-1))) * R j := by
        dsimp [R]
        field_simp <;> ring
      _ ≤ _ := h
  have hmj : 2*(r-1) ≤ m := by omega
  have hfirst := hbL (r-1) hmj
  have hfirst' : (2*b : ℝ) / k ≤ (L : ℝ)*R (r-1) := by
    refine (div_le_div_of_nonneg_right hb'' hk'.le).trans ?_
    convert hfirst using 1
    field_simp
  have hsecond := hbL r hmr
  have hpow : (m : ℝ)^r = (m : ℝ)^(r-1)*m := by
    nth_rw 1 [show r = r-1+1 by omega]
    rw [pow_succ]
  have hsecond' : ((m : ℝ)/(A*k)) ≤ (L : ℝ)*R r := by
    have hmA : (1 / (A : ℝ)) * m / k ≤ shellConstant q r * m / k :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA' hm'.le) hk'.le
    have hA₀ : 0 < (A : ℝ) := by exact_mod_cast hA
    have he : (m : ℝ)/(A*k) = (1/(A : ℝ))*m/k := by field_simp
    rw [he]
    refine hmA.trans ?_
    convert hsecond using 1
    rw [hpow]
    field_simp <;> ring
  have hh := hit_lower (L := L) (R (r-1)) (2*b) k (hR _) (by positivity)
    (by exact_mod_cast hb') (by exact_mod_cast (show 1 ≤ k by omega)) hfirst'
  have heHit : (2*b : ℝ)/(2*k) = (b : ℝ)/k := by ring
  rw [heHit] at hh
  have hf := miss_upper (L := L) (R r) ((m : ℝ)/(A*k)) (hR _) hsecond'
  have hA₀ : 0 < (A : ℝ) := by exact_mod_cast hA
  have hpos : 0 < (m : ℝ)/(A*k) := by positivity
  have hexp : Real.exp (-((m : ℝ)/(A*k))) ≤ A*k/m := by
    rw [Real.exp_neg, ← one_div]
    have hc := Real.add_one_le_exp ((m : ℝ)/(A*k))
    have hle := one_div_le_one_div_of_le hpos (show (m : ℝ)/(A*k) ≤ Real.exp ((m : ℝ)/(A*k)) by linarith)
    simpa [one_div_div] using hle
  let miss (j : ℕ) : ℚ := 𝔼 s, if j < D s then 1 else 0
  have hs (j : ℕ) : (miss j : ℝ) = (1-R j)^L := by
    have hc := exact_miss_prob (W := W) hL d j
    have he : miss j = (1-((Finset.univ.filter fun u : W => d u ≤ j).card : ℚ) / (q : ℚ)^m)^L := by
      simpa [miss, D, W, Fintype.card_fun] using hc
    rw [he]
    push_cast
    rfl
  have hcom : (𝔼 s, if D s ≤ r-1 then (1 : ℚ) else 0) = 1-miss (r-1) := by
    have he (s : Fin L → W) : (if D s ≤ r-1 then (1 : ℚ) else 0) =
      1-(if r-1 < D s then 1 else 0) := by
      by_cases h : D s ≤ r-1
      · simp [h, Nat.not_lt.mpr h]
      · simp [h, Nat.lt_of_not_ge h]
    simp_rw [he, Finset.expect_sub_distrib, Fintype.expect_const]
    rfl
  change b/(k : ℚ) ≤ (𝔼 s, if D s ≤ r-1 then (1 : ℚ) else 0) ∧ miss r ≤ A*k/m
  rw [hcom]
  constructor
  · have hh' : (b : ℝ)/k ≤ 1-(miss (r-1) : ℝ) := by rw [hs]; exact hh
    exact_mod_cast hh'
  · have hf' : (miss r : ℝ) ≤ A*k/m := by rw [hs]; exact hf.trans hexp
    exact_mod_cast hf'

private theorem hash_estimates {m q r k L C : ℕ} (hm : 0 < m) (hq : 0 < q)
    (hr : 0 < r) (hk : 0 < k) (hL : 0 < L)
    (hLD : q^m ≤ L*k*m^(r-1)) (t : ℚ) (ht : 0 < t)
    (hCt : 2*(C : ℝ)*(t : ℝ)^2 ≥ r+1)
    (hC : C*k^2*(1+m.log2) ≤ m) :
    letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
    let W := Fin m → Fin q
    ∃ (S : Type) (_ : Fintype S) (_ : Nonempty S) (send : S → W → Option (Fin L))
      (read : S → Option (Fin L) → W → Bool),
      (∀ x y, - (4*(k : ℚ)/m^2) ≤ 𝔼 s, score (read s (send s x) y) (parity x y)) ∧
      (∀ x y, ¬ |agreement x y - 1/(q : ℚ)| ≤ t/k →
        1 - (4*(k : ℚ)/m^2) ≤ 𝔼 s, score (read s (send s x) y) (parity x y)) := by
  classical
  let W := Fin m → Fin q
  let B (y : W) : Finset W := Finset.univ.filter (fun x : W =>
    t/(k : ℚ) < |agreement x y - 1/(q : ℚ)|)
  let S := (W → Fin L) × Bool
  letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  let send (s : S) (x : W) : Option (Fin L) := some (s.1 x)
  let read (s : S) : Option (Fin L) → W → Bool := fun i y =>
    match i with
    | none => s.2
    | some j => hashRead B s.1 s.2 parity j y
  have hB (y : W) : ((B y).card : ℚ)/(L : ℚ) ≤ 2*(k : ℚ)/m^2 := by
    have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
    have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
    have hL' : 0 < (L : ℝ) := by exact_mod_cast hL
    have ht' : 0 ≤ (t : ℝ)/k := by positivity
    let D : Finset W := Finset.univ.filter (fun x : W =>
      (t : ℝ)/k ≤ |((Finset.univ.filter (fun i => x i = y i)).card : ℝ) / m - 1 / q|)
    have hsub : B y ⊆ D := by
      intro x hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have he := (Finset.mem_filter.mp hx).2
      have hqcast : ((t/(k : ℚ) : ℚ) : ℝ) ≤ (|agreement x y - 1/(q : ℚ)| : ℚ) := by
        exact_mod_cast he.le
      simpa [agreement, Rat.cast_abs] using hqcast
    have hD := atypical_count hm hq y ((t : ℝ)/k) ht'
    have hD' : (D.card : ℝ) / (q : ℝ)^m ≤ 2 / (m : ℝ)^(r+1) := by
      change (D.card : ℝ) / (q : ℝ)^m ≤ _ at hD ⊢
      have htail := hash_tail_exponent hm hk (t : ℝ) hCt hC
      rw [div_eq_mul_one_div (2 : ℝ)]
      exact hD.trans (mul_le_mul_of_nonneg_left htail (by norm_num))
    have hratio : (q : ℝ)^m / L ≤ (k : ℝ)*(m : ℝ)^(r-1) := by
      apply (div_le_iff₀ hL').mpr
      have h := (show (q : ℝ)^m ≤ (L : ℝ)*k*(m : ℝ)^(r-1) by exact_mod_cast hLD)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hbcard : ((B y).card : ℝ) ≤ D.card := by exact_mod_cast Finset.card_le_card hsub
    have hre : ((B y).card : ℝ)/L ≤ 2*(k : ℝ)/m^2 := by
      calc
        _ ≤ (D.card : ℝ)/L := div_le_div_of_nonneg_right hbcard hL'.le
        _ = ((D.card : ℝ)/(q : ℝ)^m) * ((q : ℝ)^m/L) := by field_simp
        _ ≤ (2/(m : ℝ)^(r+1)) * ((k : ℝ)*(m : ℝ)^(r-1)) :=
          mul_le_mul hD' hratio (by positivity) (by positivity)
        _ = _ := by
          have he : r+1 = (r-1)+2 := by omega
          rw [he,pow_add]
          field_simp <;> ring
    apply (Rat.cast_le (K := ℝ)).mp
    simpa using hre
  have hbound (x y : W) :
      (if x ∈ B y then (1 : ℚ) else 0) - 4*(k : ℚ)/m^2 ≤
      𝔼 s : S, score (read s (send s x) y) (parity x y) := by
    have hh := hash_advantage (V := Fin L) B parity x y
    simp only [Fintype.card_fin] at hh
    have he := mul_le_mul_of_nonneg_left (hB y) (by norm_num : 0 ≤ (2 : ℚ))
    change _ ≤ 𝔼 s : S, score (hashRead B s.1 s.2 parity (s.1 x) y) (parity x y)
    have he' : 2 * (((B y).card : ℚ)/L) ≤ 4*(k : ℚ)/m^2 := by
      convert he using 1 <;> ring
    rw [mul_div_assoc] at hh
    linarith only [hh, he']
  refine ⟨S, inferInstance, inferInstance, send, read, ?_, ?_⟩
  · intro x y
    have hh := hbound x y
    by_cases h : x ∈ B y <;> simp only [h, ↓reduceIte] at hh <;> linarith
  · intro x y hxy
    have he : x ∈ B y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hxy⟩
    simpa [he] using hbound x y

end PEqualNP.Outside.L_lib_988

open PEqualNP.Outside.L_lib_988

theorem PEqualNP.Outside.L_lib_988 : (∀ (q r : Nat), 5 ≤ q → 0 < r →
  let ρ : ℚ := 1 - 4 / (q : ℚ)
  let τ := ρ^r / (1 + ρ^r)
  ∃ C : Nat, 0 < C ∧ ∀ m k : Nat, 0 < m → 0 < k →
    C * k^2 * (1 + Nat.log2 m) ≤ m →
    let W := Fin m → Fin q
    ∀ left right : W → Bool,
      let truth := fun (x y : W) => xor (xor (left x) (right y))
        (((Finset.univ : Finset (Fin m)).filter (fun i => x i = y i)).card % 2 == 1)
      ∃ (M z : Nat) (send : Fin z → W → Fin M) (read : Fin z → Fin M → W → Bool),
        0 < z ∧ M * k * m^(r-1) ≤ C * q^m ∧
        ∀ x y, (1 + τ + 1 / ((C : ℚ) * (k : ℚ))) * (z : ℚ) ≤
          2 * (((Finset.univ : Finset (Fin z)).filter
            (fun seed => read seed (send seed x) y = truth x y)).card : ℚ)) := by
  classical
  intro q r hq hr
  dsimp only
  let rho : ℚ := 1 - 4/(q : ℚ)
  let g : ℚ := (rho/2)^(r-1)*(1-rho)/2
  have hq' : (4 : ℚ) < q := by exact_mod_cast (show 4 < q by omega)
  have hq₀ : 0 < (q : ℚ) := by linarith
  have hr₀ : 0 < rho := sub_pos.mpr ((div_lt_one hq₀).mpr hq')
  have hr₁ : rho < 1 := by
    dsimp [rho]
    have h : (0 : ℚ) < 4/q := by positivity
    linarith
  have hg : 0 < g := by dsimp [g]; positivity
  have hg₁ : g ≤ 1/2 := by
    dsimp [g]
    have hpow : (rho/2)^(r-1) ≤ 1 :=
      pow_le_one₀ (by positivity) (by linarith)
    have hh := mul_le_mul_of_nonneg_right hpow (show 0 ≤ 1-rho by linarith)
    linarith
  let a (j : ℕ) : ℚ := ((q-1 : ℕ) : ℚ)^j/(2^j * j.factorial)
  have ha (j : ℕ) : 0 < a j := by
    have h : 0 < ((q-1 : ℕ) : ℚ) := by exact_mod_cast (show 0 < q-1 by omega)
    dsimp [a]
    positivity
  have haR (j : ℕ) : (a j : ℝ) = shellConstant q j := by
    simp [a, shellConstant]
  let b : ℚ := min 1 (a (r-1))/2
  let A : ℚ := 1 / a r
  have hb : 0 < b := div_pos (lt_min (by norm_num) (ha _)) (by norm_num)
  have hb₁ : 2*b ≤ 1 := by
    dsimp [b]
    linarith [min_le_left (1 : ℚ) (a (r-1))]
  have hb₂ : (2*b : ℝ) ≤ shellConstant q (r-1) := by
    rw [← haR]
    exact_mod_cast (show 2*b ≤ a (r-1) by
      dsimp [b]
      linarith [min_le_right (1 : ℚ) (a (r-1))])
  have hA : 0 < A := one_div_pos.mpr (ha _)
  have hAR : (1 : ℝ) / (A : ℝ) = shellConstant q r := by
    rw [← haR]
    simp [A]
  let t : ℚ := min (rho/8) (min ((1-rho)/8) (b*g/(8*r)))
  have htr : 0 < (r : ℚ) := by exact_mod_cast hr
  have ht : 0 < t := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have ht₀ : 4*t ≤ rho/2 := by linarith [min_le_left (rho/8) (min ((1-rho)/8) (b*g/(8*r)))]
  have ht₁ : 4*t ≤ (1-rho)/2 := by
    linarith [(min_le_right (rho/8) _).trans (min_le_left ((1-rho)/8) (b*g/(8*r)))]
  have ht₂ : 2*r*t ≤ b*g/4 := by
    have he : t ≤ b*g/(8*r) := (min_le_right _ _).trans (min_le_right _ _)
    have hp : 0 < 8*(r : ℚ) := by positivity
    have hh := (le_div_iff₀ hp).mp he
    nlinarith
  let E : ℚ := A + 2*(r : ℚ)^2 + r/t
  have hE : 0 < E := by dsimp [E]; positivity
  let B : ℚ := max 6 (max (2*r) (max A (max ((r+1)/(2*t^2)) (8*(E+5)/(b*g)))))
  obtain ⟨C, hC⟩ := exists_nat_ge B
  have hC₆ : 6 ≤ C := by exact_mod_cast (le_trans (le_max_left _ _) hC : (6 : ℚ) ≤ C)
  have hCr : 2*r ≤ C := by
    exact_mod_cast (show (2 : ℚ)*r ≤ C from
      (le_max_left _ _).trans ((le_max_right _ _).trans hC))
  have hCA : A ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hC))
  have hCt : 2*(C : ℝ)*(t : ℝ)^2 ≥ r+1 := by
    have hbq : ((r+1 : ℚ)/(2*t^2)) ≤ C :=
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hC)))
    have h := (div_le_iff₀ (show 0 < 2*t^2 by positivity)).mp hbq
    exact_mod_cast (show (r+1 : ℚ) ≤ 2*(C : ℚ)*t^2 by linarith)
  have hC' : 0 < (C : ℚ) := by exact_mod_cast (show 0 < C by omega)
  have hCb : (E+5)/(C : ℚ) ≤ b*g/8 := by
    have hbq : 8*(E+5)/(b*g) ≤ C :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hC)))
    have he := (div_le_iff₀ (show 0 < b*g by positivity)).mp hbq
    apply (div_le_iff₀ hC').mpr
    nlinarith
  refine ⟨C, by omega, ?_⟩
  intro m k hm hk hmk left right
  let W := Fin m → Fin q
  let D := k*m^(r-1)
  let N := q^m
  let L := N/D+1
  letI : Nonempty (Fin q) := ⟨⟨0,by omega⟩⟩
  have hD : 0 < D := by dsimp [D]; positivity
  have hL : 0 < L := Nat.succ_pos _
  have hCk : C*k^2 ≤ m :=
    (Nat.le_mul_of_pos_right _ (by omega : 0 < 1+m.log2)).trans hmk
  have hCkm : C*k ≤ m := by
    apply le_trans _ hCk
    rw [pow_two, ← Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ hk
  have hm2r : 2*r ≤ m := hCr.trans ((Nat.le_mul_of_pos_right _ hk).trans hCkm)
  have hm' : 0 < (m : ℚ) := by exact_mod_cast hm
  have hk' : 0 < (k : ℚ) := by exact_mod_cast hk
  have hk₁ : 1 ≤ (k : ℚ) := by exact_mod_cast hk
  have hckq : (C : ℚ)*(k : ℚ)^2 ≤ m := by exact_mod_cast hCk
  have hm₁ : 1 ≤ (m : ℚ) := by exact_mod_cast hm
  have hNk : D ≤ N := by
    have hAkm : (A : ℚ) * k ≤ m :=
      (mul_le_mul_of_nonneg_right hCA hk'.le).trans (by exact_mod_cast hCkm)
    have hAkm' : (A : ℝ) * k ≤ m := by exact_mod_cast hAkm
    let x : W := fun _ => ⟨0,by omega⟩
    have hb := ball_lower (q := q) hm2r x
    have hball : ((Finset.univ.filter (fun u : W => (changes x u).card ≤ r)).card : ℝ) ≤ N := by
      have he := Finset.card_filter_le (Finset.univ : Finset W)
        (fun u => (changes x u).card ≤ r)
      have hnat : (Finset.univ.filter (fun u : W => (changes x u).card ≤ r)).card ≤ N := by
        simpa [W,N,Fintype.card_fun] using he
      exact_mod_cast hnat
    have hA' : 0 < (A : ℝ) := by exact_mod_cast hA
    have hpow : (m : ℝ)^r = (m : ℝ) * (m : ℝ)^(r-1) := by
      nth_rw 1 [show r = (r-1)+1 by omega]
      rw [pow_succ, mul_comm]
    have hge : (A : ℝ) * ((D : ℕ) : ℝ) ≤ (m : ℝ)^r := by
      rw [hpow]
      push_cast [D]
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_right hAkm' (show 0 ≤ (m : ℝ)^(r-1) by positivity)
    rw [← hAR] at hb
    have hN := hb.trans hball
    have hN' : (m : ℝ)^r ≤ (A : ℝ)*N := by
      rw [one_div_mul_eq_div] at hN
      simpa [mul_comm] using (div_le_iff₀ hA').mp hN
    have hresult : (D : ℝ) ≤ (N : ℝ) := le_of_mul_le_mul_left (hge.trans hN') hA'
    exact_mod_cast hresult
  have hLN : N ≤ L*D := by
    have hmod := Nat.mod_lt N hD
    have hsum := Nat.mod_add_div N D
    rw [Nat.mul_comm D (N/D)] at hsum
    dsimp [L]
    rw [Nat.add_mul, one_mul]
    omega
  have hLN' : L*D ≤ 2*N := by
    have h := Nat.div_mul_le_self N D
    dsimp [L]
    rw [Nat.add_mul,one_mul]
    omega
  have hLD : q^m ≤ L*k*m^(r-1) := by simpa [D,N,mul_assoc] using hLN
  have hprob := sampling_probabilities hm (show 1 < q by omega) hr hk hL hm2r hLD
  have hsprob := fun x : W => hprob x b hb hb₁ hb₂ A hA hAR.le
  obtain ⟨S,hS,hnS,sendS,readS,hs,hsn⟩ := sparse_estimates hm hq hr
    (by omega : r ≤ m) hL hk b A t hb hA ht ht₀ ht₁ ht₂ hsprob
  obtain ⟨H,hH,hnH,sendH,readH,hh,hhf⟩ := hash_estimates hm
    (by omega : 0 < q) hr hk hL hLD t ht hCt hmk
  let delta : ℚ := 3*b*g/(4*k)
  let errS : ℚ := 2*(r : ℚ)^2/m + r/(m*(t/k)) + A*k/m
  let errH : ℚ := 4*(k : ℚ)/m^2
  have heS : 0 ≤ errS := by dsimp [errS]; positivity
  have heH : 0 ≤ errH := by dsimp [errH]; positivity
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hbg : b*g ≤ 1/4 := by
    have he := mul_le_mul (show b ≤ 1/2 by linarith) hg₁ hg.le
      (show 0 ≤ (1/2 : ℚ) by norm_num)
    linarith
  have hd' : delta ≤ 1 := by
    dsimp [delta]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hel : errS ≤ E/(C*k) := by
    have hkm : (k : ℚ)/m ≤ 1/(C*k) := by
      apply (div_le_div_iff₀ hm' (by positivity)).mpr
      nlinarith
    have h1 : (1 : ℚ)/m ≤ k/m := div_le_div_of_nonneg_right hk₁ hm'.le
    have he : (r : ℚ)/(m*(t/k)) = (r/t)*(k/m) := by field_simp <;> ring
    have hbase : 2*(r : ℚ)^2/m ≤ (2*(r : ℚ)^2)*(k/m) := by
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2*(r : ℚ)^2 by positivity)
    calc
      _ ≤ E*(k/m) := by
        dsimp [errS, E]
        rw [he]
        linear_combination hbase
      _ ≤ E*(1/(C*k)) := mul_le_mul_of_nonneg_left hkm hE.le
      _ = _ := by ring
  have heh : errH ≤ 4/(C*k) := by
    apply (div_le_div_iff₀ (by positivity : 0 < (m : ℚ)^2) (by positivity : 0 < (C : ℚ)*k)).mpr
    have hm2 : (m : ℚ) ≤ (m : ℚ)^2 := by nlinarith
    have hmk2 := hckq.trans hm2
    have hh := mul_le_mul_of_nonneg_left hmk2 (show (0 : ℚ) ≤ 4 by norm_num)
    linear_combination hh
  have hbonus : 1/((C : ℚ)*k) + errS + errH ≤ delta/6 := by
    have hb := div_le_div_of_nonneg_right hCb hk'.le
    have he : (E+5)/((C : ℚ)*k) ≤ delta/6 := by
      rw [← div_div]
      exact hb.trans_eq (by dsimp [delta]; ring)
    have hs : 1/((C : ℚ)*k) + E/((C : ℚ)*k) + 4/((C : ℚ)*k) = (E+5)/((C : ℚ)*k) := by ring
    linarith
  obtain ⟨M,z,send,read,hz,hM,hcorrect⟩ := assemble parity left right sendS readS sendH readH
    (rho^r) delta errS errH (1/((C : ℚ)*k))
    (pow_pos hr₀ _) (pow_lt_one₀ hr₀.le hr₁ (by omega))
    hd hd' heS heH hbonus (fun x y => |agreement x y-1/(q : ℚ)| ≤ t/k) hs hsn hh hhf
  refine ⟨M,z,send,read,hz,?_ ,?_⟩
  · have hmsg : M = 2*(L+1) := by simpa using hM
    rw [hmsg]
    change 2*(L+1)*k*m^(r-1) ≤ C*N
    calc
      _ = 2*(L*D+D) := by dsimp [D]; ring
      _ ≤ 2*(2*N+N) := Nat.mul_le_mul_left _ (Nat.add_le_add hLN' hNk)
      _ ≤ _ := by
        rw [show 2*(2*N+N) = 6*N by ring]
        exact Nat.mul_le_mul_right _ hC₆
  · intro x y
    simpa [parity, matchCount, rho, add_assoc] using hcorrect x y

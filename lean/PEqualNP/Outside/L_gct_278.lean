import PEqualNP.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace PEqualNP.Outside.L_gct_278_aux

noncomputable section

def Craw (x y : Fin 4 → ℂ) : ℂ :=
  x 0 * (y 1 * y 2 + y 1 * y 3 + y 2 * y 3) +
  x 1 * (y 0 * y 2 + y 0 * y 3 + y 2 * y 3) +
  x 2 * (y 0 * y 1 + y 0 * y 3 + y 1 * y 3) +
  x 3 * (y 0 * y 1 + y 0 * y 2 + y 1 * y 2)

def Qraw (x y : Fin 4 → ℂ) : ℂ :=
  y 0 * x 1 * x 2 * x 3 +
  y 1 * x 0 * x 2 * x 3 +
  y 2 * x 0 * x 1 * x 3 +
  y 3 * x 0 * x 1 * x 2

def termVal (x y : Fin 4 → ℂ) (c : Fin 4 → Fin 3) (i : Fin 4) : ℂ :=
  match c i with
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => x i
  | ⟨2, _⟩ => y i

def coeffC (x y : Fin 4 → ℂ) (c : Fin 4 → Fin 3) : ℂ :=
  ∏ i : Fin 4, termVal x y c i

def cWeight (c : Fin 4 → Fin 3) (f : Fin 4 ↪ Fin 5) : ℕ :=
  ∑ i : Fin 4, (c i).val * (f i).val

lemma prod_three_expand (ζ : ℂ) (x y : Fin 4 → ℂ) (f : Fin 4 ↪ Fin 5) :
    (∏ i : Fin 4, (1 + x i * ζ ^ (f i).val + y i * ζ ^ (2 * (f i).val))) =
      ∑ c : Fin 4 → Fin 3, coeffC x y c * ζ ^ (cWeight c f) := by
  have hfac : ∀ i : Fin 4,
      (1 + x i * ζ ^ (f i).val + y i * ζ ^ (2 * (f i).val)) =
        ∑ d : Fin 3, (match d with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => x i | ⟨2, _⟩ => y i) *
          ζ ^ (d.val * (f i).val) := by
    intro i
    rw [Fin.sum_univ_three]
    simp only [Fin.isValue, Fin.val_zero, zero_mul, pow_zero, mul_one,
      Fin.val_one, one_mul, Fin.val_two]
  simp_rw [hfac]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold coeffC termVal cWeight
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

lemma zeta_sum_zero {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hne : ζ ≠ 1 := hζ.ne_one (by decide)
  have hfac : (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4) = 0 := by
    calc (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4) = ζ ^ 5 - 1 := by ring
      _ = 0 := by rw [h5, sub_self]
  exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)

lemma zeta_pow_mod {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ζ ^ n = ζ ^ (n % 5) := by
  have hdiv : n = 5 * (n / 5) + n % 5 := (Nat.div_add_mod n 5).symm
  conv_lhs => rw [hdiv, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

lemma shift_sum_zero {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (c : Fin 4 → Fin 3)
    (hnd : (∑ i : Fin 4, (c i).val) % 5 ≠ 0) :
    (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight c f)) = 0 := by
  let shift5 : Fin 5 ≃ Fin 5 :=
    { toFun := fun a => ⟨(a.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
      invFun := fun a => ⟨(a.val + 4) % 5, Nat.mod_lt _ (by decide)⟩
      left_inv := fun a => by ext; dsimp; omega
      right_inv := fun a => by ext; dsimp; omega }
  let σ : (Fin 4 ↪ Fin 5) ≃ (Fin 4 ↪ Fin 5) :=
    { toFun := fun f => f.trans shift5.toEmbedding
      invFun := fun f => f.trans shift5.symm.toEmbedding
      left_inv := fun f => by apply DFunLike.ext; intro i; exact shift5.left_inv (f i)
      right_inv := fun f => by apply DFunLike.ext; intro i; exact shift5.right_inv (f i) }
  have hshift : ∀ f : Fin 4 ↪ Fin 5,
      ζ ^ (cWeight c (σ f)) = ζ ^ (∑ i : Fin 4, (c i).val) * ζ ^ (cWeight c f) := by
    intro f
    rw [← pow_add]
    conv_lhs => rw [zeta_pow_mod hζ]
    conv_rhs => rw [zeta_pow_mod hζ]
    congr 1
    unfold cWeight
    have h1 : ∀ i : Fin 4, ((c i).val * (σ f i).val) % 5 =
        ((c i).val + (c i).val * (f i).val) % 5 := by
      intro i
      have hsi : (σ f i).val = ((f i).val + 1) % 5 := rfl
      rw [hsi, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      have : (c i).val * ((f i).val + 1) = (c i).val + (c i).val * (f i).val := by ring
      rw [this]
    rw [Finset.sum_nat_mod, Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.sum_nat_mod,
      Finset.sum_add_distrib]
  have hinv : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight c f)) =
      ζ ^ (∑ i : Fin 4, (c i).val) * (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight c f)) := by
    calc (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight c f))
        = ∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight c (σ f)) :=
          (Fintype.sum_equiv σ _ _ (fun _ => rfl)).symm
      _ = ∑ f : Fin 4 ↪ Fin 5, ζ ^ (∑ i : Fin 4, (c i).val) * ζ ^ (cWeight c f) :=
          Finset.sum_congr rfl (fun f _ => hshift f)
      _ = ζ ^ (∑ i : Fin 4, (c i).val) * (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight c f)) := by
          rw [← Finset.mul_sum]
  have hne : ζ ^ (∑ i : Fin 4, (c i).val) ≠ 1 := by
    rw [zeta_pow_mod hζ]
    have hlt : (∑ i : Fin 4, (c i).val) % 5 < 5 := Nat.mod_lt _ (by decide)
    exact hζ.pow_ne_one_of_pos_of_lt hnd hlt
  have h0 : (1 - ζ ^ (∑ i : Fin 4, (c i).val)) * (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight c f)) = 0 := by
    linear_combination hinv
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hne))

lemma card_emb_four_five : Fintype.card (Fin 4 ↪ Fin 5) = 120 := by
  let S3 := (Finset.univ : Finset (Fin 5 × Fin 5 × Fin 5)).filter
    (fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)
  have hS3 : S3.card = 60 := by decide
  rw [← Finset.card_univ, Finset.card_eq_sum_ones]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun f : Fin 4 ↪ Fin 5 => (f 0, f 1, f 2)) (t := S3)]
  · have hfib : ∀ t ∈ S3,
        (Finset.univ.filter (fun f : Fin 4 ↪ Fin 5 => (f 0, f 1, f 2) = t)).card = 2 := by
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨_, ht12, ht13, ht23⟩
      have hrem : (Finset.univ \ ({t.1, t.2.1, t.2.2} : Finset (Fin 5))).card = 2 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [ht23]
        · simp [ht12, ht13]
      rw [← hrem]
      refine Finset.card_bij (fun f _ => f 3) ?_ ?_ ?_
      · intro f hf
        have heq := (Finset.mem_filter.mp hf).2
        have h1 : f 0 = t.1 := congrArg Prod.fst heq
        have h2 : f 1 = t.2.1 := congrArg (fun p => p.2.1) heq
        have h3 : f 2 = t.2.2 := congrArg (fun p => p.2.2) heq
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h | h)
        · exact absurd (f.injective (h1.trans h.symm)) (by decide)
        · exact absurd (f.injective (h2.trans h.symm)) (by decide)
        · exact absurd (f.injective (h3.trans h.symm)) (by decide)
      · intro f1 hf1 f2 hf2 h3Eq
        have heq1 := (Finset.mem_filter.mp hf1).2
        have heq2 := (Finset.mem_filter.mp hf2).2
        apply DFunLike.ext; intro x
        fin_cases x
        · exact (congrArg Prod.fst heq1).trans (congrArg Prod.fst heq2).symm
        · exact (congrArg (fun p => p.2.1) heq1).trans (congrArg (fun p => p.2.1) heq2).symm
        · exact (congrArg (fun p => p.2.2) heq1).trans (congrArg (fun p => p.2.2) heq2).symm
        · exact h3Eq
      · intro z hz
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, not_or] at hz
        let g : Fin 4 → Fin 5 := fun | ⟨0, _⟩ => t.1 | ⟨1, _⟩ => t.2.1 | ⟨2, _⟩ => t.2.2 | ⟨3, _⟩ => z
        have hginj : Function.Injective g := by
          intro x1 x2 hg
          fin_cases x1 <;> fin_cases x2 <;> dsimp [g] at hg <;>
            first | rfl | exact absurd hg ht12 | exact absurd hg ht13 | exact absurd hg ht23 |
              exact absurd hg.symm ht12 | exact absurd hg.symm ht13 | exact absurd hg.symm ht23 |
              exact absurd hg hz.1 | exact absurd hg hz.2.1 | exact absurd hg hz.2.2 |
              exact absurd hg.symm hz.1 | exact absurd hg.symm hz.2.1 | exact absurd hg.symm hz.2.2
        exact ⟨⟨g, hginj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
    have hsum : (∑ t ∈ S3, ∑ _f ∈ Finset.univ.filter (fun f : Fin 4 ↪ Fin 5 => (f 0, f 1, f 2) = t), 1) =
        ∑ _t ∈ S3, 2 := by
      apply Finset.sum_congr rfl; intro t ht
      rw [Finset.sum_const, smul_eq_mul, mul_one, hfib t ht]
    rw [hsum, Finset.sum_const, hS3]; rfl
  · intro f _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      f.injective.ne (by decide), f.injective.ne (by decide), f.injective.ne (by decide)⟩

lemma sum_weight_12 {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (c : Fin 4 → Fin 3)
    (i0 j1 j2 k0 : Fin 4)
    (hi0 : c i0 = 1) (hj1 : c j1 = 2) (hj2 : c j2 = 2) (hk0 : c k0 = 0)
    (h12 : i0 ≠ j1) (h13 : i0 ≠ j2) (h14 : i0 ≠ k0)
    (h23 : j1 ≠ j2) (h24 : j1 ≠ k0) (h34 : j2 ≠ k0) :
    (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight c f)) = 20 := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {i0, j1, j2, k0} := by
    have hsub : ({i0, j1, j2, k0} : Finset (Fin 4)) ⊆ Finset.univ := Finset.subset_univ _
    have hcard : ({i0, j1, j2, k0} : Finset (Fin 4)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [h34]
      · simp [h23, h24]
      · simp [h12, h13, h14]
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hcard])).symm
  have hw : ∀ f : Fin 4 ↪ Fin 5,
      cWeight c f = (f i0).val + 2 * (f j1).val + 2 * (f j2).val := by
    intro f
    unfold cWeight
    rw [huniv, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · simp only [hi0, hj1, hj2, hk0, Fin.val_one, Fin.val_two, Fin.val_zero, one_mul, zero_mul, add_zero]
      ring
    · simp [h34]
    · simp [h23, h24]
    · simp [h12, h13, h14]
  simp_rw [hw]
  let S3 := (Finset.univ : Finset (Fin 5 × Fin 5 × Fin 5)).filter
    (fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)
  have hfib : (∑ f : Fin 4 ↪ Fin 5, ζ ^ ((f i0).val + 2 * (f j1).val + 2 * (f j2).val)) =
      ∑ t ∈ S3, ∑ f ∈ Finset.univ.filter (fun f : Fin 4 ↪ Fin 5 => (f i0, f j1, f j2) = t),
        ζ ^ (t.1.val + 2 * t.2.1.val + 2 * t.2.2.val) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun f : Fin 4 ↪ Fin 5 => (f i0, f j1, f j2))
      (t := S3)]
    · apply Finset.sum_congr rfl; intro t _
      apply Finset.sum_congr rfl; intro f hf
      have heq := (Finset.mem_filter.mp hf).2
      rw [← heq]
    · intro f _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        f.injective.ne h12, f.injective.ne h13, f.injective.ne h23⟩
  rw [hfib]
  have hfib_card : ∀ t ∈ S3,
      (Finset.univ.filter (fun f : Fin 4 ↪ Fin 5 => (f i0, f j1, f j2) = t)).card = 2 := by
    intro t ht
    rcases Finset.mem_filter.mp ht with ⟨_, ht12, ht13, ht23⟩
    have hrem : (Finset.univ \ ({t.1, t.2.1, t.2.2} : Finset (Fin 5))).card = 2 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [ht23]
      · simp [ht12, ht13]
    rw [← hrem]
    refine Finset.card_bij (fun f _ => f k0) ?_ ?_ ?_
    · intro f hf
      have heq := (Finset.mem_filter.mp hf).2
      have h1 : f i0 = t.1 := congrArg Prod.fst heq
      have h2 : f j1 = t.2.1 := congrArg (fun p => p.2.1) heq
      have h3 : f j2 = t.2.2 := congrArg (fun p => p.2.2) heq
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h | h)
      · exact h14 (f.injective (h1.trans h.symm))
      · exact h24 (f.injective (h2.trans h.symm))
      · exact h34 (f.injective (h3.trans h.symm))
    · intro f1 hf1 f2 hf2 hkEq
      have heq1 := (Finset.mem_filter.mp hf1).2
      have heq2 := (Finset.mem_filter.mp hf2).2
      apply DFunLike.ext; intro x
      have hx : x ∈ ({i0, j1, j2, k0} : Finset (Fin 4)) := by rw [← huniv]; exact Finset.mem_univ x
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (congrArg Prod.fst heq1).trans (congrArg Prod.fst heq2).symm
      · exact (congrArg (fun p => p.2.1) heq1).trans (congrArg (fun p => p.2.1) heq2).symm
      · exact (congrArg (fun p => p.2.2) heq1).trans (congrArg (fun p => p.2.2) heq2).symm
      · exact hkEq
    · intro z hz
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or] at hz
      let g : Fin 4 → Fin 5 := fun x =>
        if x = i0 then t.1 else if x = j1 then t.2.1 else if x = j2 then t.2.2 else z
      have hginj : Function.Injective g := by
        intro x1 x2 hg
        have hx1 : x1 ∈ ({i0, j1, j2, k0} : Finset (Fin 4)) := by rw [← huniv]; exact Finset.mem_univ _
        have hx2 : x2 ∈ ({i0, j1, j2, k0} : Finset (Fin 4)) := by rw [← huniv]; exact Finset.mem_univ _
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
        rcases hx1 with rfl | rfl | rfl | rfl <;> rcases hx2 with rfl | rfl | rfl | rfl <;>
          simp only [g, ite_true, h12, h13, h23, h12.symm, h13.symm, h14.symm,
            h23.symm, h24.symm, h34.symm, ite_false] at hg <;>
          first | rfl | exact absurd hg ht12 | exact absurd hg ht13 | exact absurd hg ht23 |
            exact absurd hg.symm ht12 | exact absurd hg.symm ht13 | exact absurd hg.symm ht23 |
            exact absurd hg.symm hz.1 | exact absurd hg.symm hz.2.1 | exact absurd hg.symm hz.2.2 |
            exact absurd hg hz.1 | exact absurd hg hz.2.1 | exact absurd hg hz.2.2
      refine ⟨⟨g, hginj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · ext <;> simp [g, h12.symm, h13.symm, h23.symm]
      · simp [g, h14.symm, h24.symm, h34.symm]
  have hsum2 : (∑ t ∈ S3, ∑ _f ∈ Finset.univ.filter (fun f : Fin 4 ↪ Fin 5 => (f i0, f j1, f j2) = t),
      ζ ^ (t.1.val + 2 * t.2.1.val + 2 * t.2.2.val)) =
      2 * ∑ t ∈ S3, ζ ^ (t.1.val + 2 * t.2.1.val + 2 * t.2.2.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t ht
    rw [Finset.sum_const, hfib_card t ht]
    simp
  rw [hsum2]
  have hS3 : (∑ t ∈ S3, ζ ^ (t.1.val + 2 * t.2.1.val + 2 * t.2.2.val)) = 10 := by
    have hmod5 : ∀ t : Fin 5 × Fin 5 × Fin 5,
        ζ ^ (t.1.val + 2 * t.2.1.val + 2 * t.2.2.val) =
          ζ ^ ((t.1.val + 2 * t.2.1.val + 2 * t.2.2.val) % 5) := fun t => zeta_pow_mod hζ _
    simp_rw [hmod5]
    have hcount : ∀ r : Fin 5,
        (S3.filter (fun t => (t.1.val + 2 * t.2.1.val + 2 * t.2.2.val) % 5 = r.val)).card =
          if r = 0 then 20 else 10 := by
      intro r; fin_cases r <;> decide
    have hfib5 : (∑ t ∈ S3, ζ ^ ((t.1.val + 2 * t.2.1.val + 2 * t.2.2.val) % 5)) =
        ∑ r : Fin 5, ((S3.filter (fun t => (t.1.val + 2 * t.2.1.val + 2 * t.2.2.val) % 5 = r.val)).card : ℂ) *
          ζ ^ r.val := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun t : Fin 5 × Fin 5 × Fin 5 =>
        (⟨(t.1.val + 2 * t.2.1.val + 2 * t.2.2.val) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5))
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      apply Finset.sum_congr rfl; intro r _
      have hfilt : S3.filter (fun t =>
          (⟨(t.1.val + 2 * t.2.1.val + 2 * t.2.2.val) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = r) =
          S3.filter (fun t => (t.1.val + 2 * t.2.1.val + 2 * t.2.2.val) % 5 = r.val) := by
        ext t; simp [Fin.ext_iff]
      rw [hfilt]
      have hconst : ∀ t ∈ S3.filter (fun t => (t.1.val + 2 * t.2.1.val + 2 * t.2.2.val) % 5 = r.val),
          ζ ^ ((t.1.val + 2 * t.2.1.val + 2 * t.2.2.val) % 5) = ζ ^ r.val := by
        intro t ht; rw [(Finset.mem_filter.mp ht).2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    rw [hfib5]
    simp_rw [hcount]
    rw [Fin.sum_univ_five]
    have hz := zeta_sum_zero hζ
    simp only [Fin.isValue, ite_true, Fin.one_eq_zero_iff, Fin.reduceEq, ite_false,
      Fin.val_zero, pow_zero, mul_one, Fin.val_one, pow_one, Fin.val_two]
    norm_num
    linear_combination 10 * hz
  rw [hS3]; norm_num

lemma sum_weight_31 {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (c : Fin 4 → Fin 3)
    (j0 i1 i2 i3 : Fin 4)
    (hj0 : c j0 = 2) (hi1 : c i1 = 1) (hi2 : c i2 = 1) (hi3 : c i3 = 1)
    (h01 : j0 ≠ i1) (h02 : j0 ≠ i2) (h03 : j0 ≠ i3)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) :
    (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight c f)) = -30 := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {j0, i1, i2, i3} := by
    have hsub : ({j0, i1, i2, i3} : Finset (Fin 4)) ⊆ Finset.univ := Finset.subset_univ _
    have hcard : ({j0, i1, i2, i3} : Finset (Fin 4)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [h23]
      · simp [h12, h13]
      · simp [h01, h02, h03]
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hcard])).symm
  have hw : ∀ f : Fin 4 ↪ Fin 5,
      cWeight c f = 2 * (f j0).val + (f i1).val + (f i2).val + (f i3).val := by
    intro f
    unfold cWeight
    rw [huniv, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · simp only [hj0, hi1, hi2, hi3, Fin.val_one, Fin.val_two, one_mul]
      ring
    · simp [h23]
    · simp [h12, h13]
    · simp [h01, h02, h03]
  simp_rw [hw]
  let S4 := (Finset.univ : Finset (Fin 5 × Fin 5 × Fin 5 × Fin 5)).filter
    (fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.1 ≠ t.2.2.2 ∧
      t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2)
  have hbij : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (2 * (f j0).val + (f i1).val + (f i2).val + (f i3).val)) =
      ∑ t ∈ S4, ζ ^ (2 * t.1.val + t.2.1.val + t.2.2.1.val + t.2.2.2.val) := by
    refine Finset.sum_bij (fun f _ => (f j0, f i1, f i2, f i3)) ?_ ?_ ?_ ?_
    · intro f _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        f.injective.ne h01, f.injective.ne h02, f.injective.ne h03,
        f.injective.ne h12, f.injective.ne h13, f.injective.ne h23⟩
    · intro f1 _ f2 _ hEq
      apply DFunLike.ext; intro x
      have hx : x ∈ ({j0, i1, i2, i3} : Finset (Fin 4)) := by rw [← huniv]; exact Finset.mem_univ _
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact congrArg Prod.fst hEq
      · exact congrArg (fun p => p.2.1) hEq
      · exact congrArg (fun p => p.2.2.1) hEq
      · exact congrArg (fun p => p.2.2.2) hEq
    · intro t ht
      rcases Finset.mem_filter.mp ht with ⟨_, ht01, ht02, ht03, ht12, ht13, ht23⟩
      let g : Fin 4 → Fin 5 := fun x =>
        if x = j0 then t.1 else if x = i1 then t.2.1 else if x = i2 then t.2.2.1 else t.2.2.2
      have hginj : Function.Injective g := by
        intro x1 x2 hg
        have hx1 : x1 ∈ ({j0, i1, i2, i3} : Finset (Fin 4)) := by rw [← huniv]; exact Finset.mem_univ _
        have hx2 : x2 ∈ ({j0, i1, i2, i3} : Finset (Fin 4)) := by rw [← huniv]; exact Finset.mem_univ _
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
        rcases hx1 with rfl | rfl | rfl | rfl <;> rcases hx2 with rfl | rfl | rfl | rfl <;>
          simp only [g, ite_true, h01, h02, h12, h01.symm, h02.symm, h03.symm,
            h12.symm, h13.symm, h23.symm, ite_false] at hg <;>
          first | rfl | exact absurd hg ht01 | exact absurd hg ht02 | exact absurd hg ht03 |
            exact absurd hg ht12 | exact absurd hg ht13 | exact absurd hg ht23 |
            exact absurd hg.symm ht01 | exact absurd hg.symm ht02 | exact absurd hg.symm ht03 |
            exact absurd hg.symm ht12 | exact absurd hg.symm ht13 | exact absurd hg.symm ht23
      refine ⟨⟨g, hginj⟩, Finset.mem_univ _, ?_⟩
      ext <;> simp [g, h01.symm, h02.symm, h03.symm, h12.symm, h13.symm, h23.symm]
    · intro _ _; rfl
  rw [hbij]
  have hmod5 : ∀ t : Fin 5 × Fin 5 × Fin 5 × Fin 5,
      ζ ^ (2 * t.1.val + t.2.1.val + t.2.2.1.val + t.2.2.2.val) =
        ζ ^ ((2 * t.1.val + t.2.1.val + t.2.2.1.val + t.2.2.2.val) % 5) := fun t => zeta_pow_mod hζ _
  simp_rw [hmod5]
  have hcount : ∀ r : Fin 5,
      (S4.filter (fun t => (2 * t.1.val + t.2.1.val + t.2.2.1.val + t.2.2.2.val) % 5 = r.val)).card =
        if r = 0 then 0 else 30 := by
    intro r; fin_cases r <;> decide
  have hfib5 : (∑ t ∈ S4, ζ ^ ((2 * t.1.val + t.2.1.val + t.2.2.1.val + t.2.2.2.val) % 5)) =
      ∑ r : Fin 5, ((S4.filter (fun t => (2 * t.1.val + t.2.1.val + t.2.2.1.val + t.2.2.2.val) % 5 = r.val)).card : ℂ) *
        ζ ^ r.val := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun t : Fin 5 × Fin 5 × Fin 5 × Fin 5 =>
      (⟨(2 * t.1.val + t.2.1.val + t.2.2.1.val + t.2.2.2.val) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5))
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl; intro r _
    have hfilt : S4.filter (fun t =>
        (⟨(2 * t.1.val + t.2.1.val + t.2.2.1.val + t.2.2.2.val) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = r) =
        S4.filter (fun t => (2 * t.1.val + t.2.1.val + t.2.2.1.val + t.2.2.2.val) % 5 = r.val) := by
      ext t; simp [Fin.ext_iff]
    rw [hfilt]
    have hconst : ∀ t ∈ S4.filter (fun t => (2 * t.1.val + t.2.1.val + t.2.2.1.val + t.2.2.2.val) % 5 = r.val),
        ζ ^ ((2 * t.1.val + t.2.1.val + t.2.2.1.val + t.2.2.2.val) % 5) = ζ ^ r.val := by
      intro t ht; rw [(Finset.mem_filter.mp ht).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rw [hfib5]
  simp_rw [hcount]
  rw [Fin.sum_univ_five]
  have hz := zeta_sum_zero hζ
  simp only [Fin.isValue, ite_true, Fin.one_eq_zero_iff, Fin.reduceEq, ite_false,
    Fin.val_zero, pow_zero, mul_one, Fin.val_one, pow_one, Fin.val_two]
  norm_num
  linear_combination 30 * hz

def mkC (a b c d : Fin 3) : Fin 4 → Fin 3 :=
  fun | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c | ⟨3, _⟩ => d

def goodList : List (Fin 4 → Fin 3) :=
  [ mkC 0 0 0 0,
    mkC 1 2 2 0, mkC 1 2 0 2, mkC 1 0 2 2,
    mkC 2 1 2 0, mkC 2 1 0 2, mkC 0 1 2 2,
    mkC 2 2 1 0, mkC 2 0 1 2, mkC 0 2 1 2,
    mkC 2 2 0 1, mkC 2 0 2 1, mkC 0 2 2 1,
    mkC 2 1 1 1, mkC 1 2 1 1, mkC 1 1 2 1, mkC 1 1 1 2 ]

lemma goodList_nodup : goodList.Nodup := by decide

lemma not_mem_goodList_mod_ne (c : Fin 4 → Fin 3) (hc : c ∉ goodList) :
    (∑ i : Fin 4, (c i).val) % 5 ≠ 0 := by
  have hdec : ∀ c : Fin 4 → Fin 3, c ∈ goodList ∨ (∑ i : Fin 4, (c i).val) % 5 ≠ 0 := by decide
  exact (hdec c).resolve_left hc

lemma perm_exact_formula {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (x y : Fin 4 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + x i * ζ ^ (f i).val + y i * ζ ^ (2 * (f i).val))) =
      120 + 20 * Craw x y - 30 * Qraw x y := by
  simp_rw [prod_three_expand]
  rw [Finset.sum_comm]
  have hpull : ∀ c : Fin 4 → Fin 3,
      (∑ f : Fin 4 ↪ Fin 5, coeffC x y c * ζ ^ (cWeight c f)) =
        coeffC x y c * ∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight c f) := fun c => by rw [← Finset.mul_sum]
  simp_rw [hpull]
  have hred : (∑ c : Fin 4 → Fin 3, coeffC x y c * ∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight c f)) =
      ∑ c ∈ goodList.toFinset, coeffC x y c * ∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight c f) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro c _ hc
    have hnot : c ∉ goodList := by simpa using hc
    rw [shift_sum_zero hζ c (not_mem_goodList_mod_ne c hnot), mul_zero]
  rw [hred, List.sum_toFinset _ goodList_nodup]
  have h0000 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 0 0 0 0) f)) = 120 := by
    have hw : ∀ f : Fin 4 ↪ Fin 5, cWeight (mkC 0 0 0 0) f = 0 := by
      intro f; unfold cWeight mkC; rw [Fin.sum_univ_four]; simp
    simp_rw [hw, pow_zero, Finset.sum_const, Finset.card_univ, card_emb_four_five]
    norm_num
  have h12_0 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 1 2 2 0) f)) = 20 :=
    sum_weight_12 hζ _ 0 1 2 3 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h12_1 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 1 2 0 2) f)) = 20 :=
    sum_weight_12 hζ _ 0 1 3 2 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h12_2 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 1 0 2 2) f)) = 20 :=
    sum_weight_12 hζ _ 0 2 3 1 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h12_3 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 2 1 2 0) f)) = 20 :=
    sum_weight_12 hζ _ 1 0 2 3 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h12_4 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 2 1 0 2) f)) = 20 :=
    sum_weight_12 hζ _ 1 0 3 2 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h12_5 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 0 1 2 2) f)) = 20 :=
    sum_weight_12 hζ _ 1 2 3 0 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h12_6 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 2 2 1 0) f)) = 20 :=
    sum_weight_12 hζ _ 2 0 1 3 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h12_7 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 2 0 1 2) f)) = 20 :=
    sum_weight_12 hζ _ 2 0 3 1 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h12_8 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 0 2 1 2) f)) = 20 :=
    sum_weight_12 hζ _ 2 1 3 0 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h12_9 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 2 2 0 1) f)) = 20 :=
    sum_weight_12 hζ _ 3 0 1 2 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h12_10 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 2 0 2 1) f)) = 20 :=
    sum_weight_12 hζ _ 3 0 2 1 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h12_11 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 0 2 2 1) f)) = 20 :=
    sum_weight_12 hζ _ 3 1 2 0 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h31_0 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 2 1 1 1) f)) = -30 :=
    sum_weight_31 hζ _ 0 1 2 3 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h31_1 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 1 2 1 1) f)) = -30 :=
    sum_weight_31 hζ _ 1 0 2 3 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h31_2 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 1 1 2 1) f)) = -30 :=
    sum_weight_31 hζ _ 2 0 1 3 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h31_3 : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (cWeight (mkC 1 1 1 2) f)) = -30 :=
    sum_weight_31 hζ _ 3 0 1 2 rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [goodList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    h0000, h12_0, h12_1, h12_2, h12_3, h12_4, h12_5, h12_6, h12_7, h12_8, h12_9, h12_10, h12_11,
    h31_0, h31_1, h31_2, h31_3]
  unfold coeffC termVal mkC Craw Qraw
  simp only [Fin.prod_univ_four]
  ring

def hadamard (u : Fin 3 → ℂ) : Fin 4 → ℂ :=
  fun | ⟨0, _⟩ => u 0 + u 1 + u 2
      | ⟨1, _⟩ => u 0 - u 1 - u 2
      | ⟨2, _⟩ => -u 0 + u 1 - u 2
      | ⟨3, _⟩ => -u 0 - u 1 + u 2

def invHadamard (x : Fin 4 → ℂ) : Fin 3 → ℂ :=
  fun | ⟨0, _⟩ => (x 0 + x 1) / 2
      | ⟨1, _⟩ => (x 0 + x 2) / 2
      | ⟨2, _⟩ => (x 0 + x 3) / 2

lemma hadamard_sum_zero (u : Fin 3 → ℂ) : (∑ i : Fin 4, hadamard u i) = 0 := by
  rw [Fin.sum_univ_four]
  dsimp [hadamard]
  ring

lemma invHadamard_hadamard (u : Fin 3 → ℂ) : invHadamard (hadamard u) = u := by
  ext i
  fin_cases i <;> dsimp [invHadamard, hadamard] <;> ring

lemma hadamard_invHadamard (x : Fin 4 → ℂ) (hx : (∑ i : Fin 4, x i) = 0) :
    hadamard (invHadamard x) = x := by
  rw [Fin.sum_univ_four] at hx
  ext i
  fin_cases i
  · dsimp [invHadamard, hadamard]; linear_combination hx / 2
  · dsimp [invHadamard, hadamard]; linear_combination -hx / 2
  · dsimp [invHadamard, hadamard]; linear_combination -hx / 2
  · dsimp [invHadamard, hadamard]; linear_combination -hx / 2

def C3 (u v : Fin 3 → ℂ) : ℂ :=
  u 0 * v 1 * v 2 + u 1 * v 2 * v 0 + u 2 * v 0 * v 1

def Q3 (u v : Fin 3 → ℂ) : ℂ :=
  u 0 * v 0 * (u 0 ^ 2 - u 1 ^ 2 - u 2 ^ 2) +
  u 1 * v 1 * (u 1 ^ 2 - u 2 ^ 2 - u 0 ^ 2) +
  u 2 * v 2 * (u 2 ^ 2 - u 0 ^ 2 - u 1 ^ 2)

lemma Craw_hadamard (u v : Fin 3 → ℂ) : Craw (hadamard u) (hadamard v) = 8 * C3 u v := by
  unfold Craw C3 hadamard
  dsimp
  ring

lemma Qraw_hadamard (u v : Fin 3 → ℂ) : Qraw (hadamard u) (hadamard v) = 4 * Q3 u v := by
  unfold Qraw Q3 hadamard
  dsimp
  ring

def dot3 (a b : Fin 3 → ℂ) : ℂ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

def cross3 (a b : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun | ⟨0, _⟩ => a 1 * b 2 - a 2 * b 1
      | ⟨1, _⟩ => a 2 * b 0 - a 0 * b 2
      | ⟨2, _⟩ => a 0 * b 1 - a 1 * b 0

def qVec (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun | ⟨0, _⟩ => v 1 * v 2
      | ⟨1, _⟩ => v 2 * v 0
      | ⟨2, _⟩ => v 0 * v 1

lemma C3_eq_dot3 (u v : Fin 3 → ℂ) : C3 u v = dot3 u (qVec v) := by
  unfold C3 dot3 qVec
  dsimp
  ring

lemma cross3_cross3 (a b p : Fin 3 → ℂ) :
    cross3 (cross3 a b) p = dot3 a p • b - dot3 b p • a := by
  ext i
  fin_cases i <;>
    simp only [cross3, dot3, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    ring

lemma cross3_ne_zero_of_li {a b : Fin 3 → ℂ}
    (hli : ∀ c1 c2 : ℂ, c1 • a + c2 • b = 0 → c1 = 0 ∧ c2 = 0) :
    cross3 a b ≠ 0 := by
  intro h0
  have hc0 : a 1 * b 2 - a 2 * b 1 = 0 := congrFun h0 0
  have hc1 : a 2 * b 0 - a 0 * b 2 = 0 := congrFun h0 1
  have hc2 : a 0 * b 1 - a 1 * b 0 = 0 := congrFun h0 2
  by_cases ha0 : a 0 ≠ 0
  · have hdep : (-b 0) • a + (a 0) • b = 0 := by
      ext i
      fin_cases i
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.zero_eta]; ring
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.mk_one]; linear_combination hc2
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.reduceFinMk]; linear_combination -hc1
    exact ha0 (hli (-b 0) (a 0) hdep).2
  · push Not at ha0
    by_cases ha1 : a 1 ≠ 0
    · have hdep : (-b 1) • a + (a 1) • b = 0 := by
        ext i
        fin_cases i
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.zero_eta]; linear_combination -hc2
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.mk_one]; ring
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.reduceFinMk]; linear_combination hc0
      exact ha1 (hli (-b 1) (a 1) hdep).2
    · push Not at ha1
      by_cases ha2 : a 2 ≠ 0
      · have hdep : (-b 2) • a + (a 2) • b = 0 := by
          ext i
          fin_cases i
          · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.zero_eta]; linear_combination hc1
          · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.mk_one]; linear_combination -hc0
          · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.reduceFinMk]; ring
        exact ha2 (hli (-b 2) (a 2) hdep).2
      · push Not at ha2
        have ha : a = 0 := by ext i; fin_cases i <;> assumption
        have hdep : (1 : ℂ) • a + (0 : ℂ) • b = 0 := by rw [ha]; simp
        exact one_ne_zero (hli 1 0 hdep).1

lemma cross3_eq_zero_of_parallel {a p r : Fin 3 → ℂ} (ha : a ≠ 0)
    (hp : cross3 a p = 0) (hr : cross3 a r = 0) :
    cross3 p r = 0 := by
  have hp0 : a 1 * p 2 = a 2 * p 1 := sub_eq_zero.mp (congrFun hp 0)
  have hp1 : a 2 * p 0 = a 0 * p 2 := sub_eq_zero.mp (congrFun hp 1)
  have hp2 : a 0 * p 1 = a 1 * p 0 := sub_eq_zero.mp (congrFun hp 2)
  have hr0 : a 1 * r 2 = a 2 * r 1 := sub_eq_zero.mp (congrFun hr 0)
  have hr1 : a 2 * r 0 = a 0 * r 2 := sub_eq_zero.mp (congrFun hr 1)
  have hr2 : a 0 * r 1 = a 1 * r 0 := sub_eq_zero.mp (congrFun hr 2)
  have hex : a 0 ≠ 0 ∨ a 1 ≠ 0 ∨ a 2 ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (by ext i; fin_cases i <;> tauto)
  rcases hex with h0 | h1 | h2
  · ext i; fin_cases i <;> dsimp [cross3]
    · apply mul_left_cancel₀ (mul_ne_zero h0 h0)
      rw [mul_zero]
      calc (a 0 * a 0) * (p 1 * r 2 - p 2 * r 1)
          = (a 0 * p 1) * (a 0 * r 2) - (a 0 * p 2) * (a 0 * r 1) := by ring
        _ = (a 1 * p 0) * (a 2 * r 0) - (a 2 * p 0) * (a 1 * r 0) := by rw [hp2, ← hr1, ← hp1, hr2]
        _ = 0 := by ring
    · apply mul_left_cancel₀ h0
      rw [mul_zero]
      calc a 0 * (p 2 * r 0 - p 0 * r 2) = (a 0 * p 2) * r 0 - p 0 * (a 0 * r 2) := by ring
        _ = (a 2 * p 0) * r 0 - p 0 * (a 2 * r 0) := by rw [← hp1, ← hr1]
        _ = 0 := by ring
    · apply mul_left_cancel₀ h0
      rw [mul_zero]
      calc a 0 * (p 0 * r 1 - p 1 * r 0) = p 0 * (a 0 * r 1) - (a 0 * p 1) * r 0 := by ring
        _ = p 0 * (a 1 * r 0) - (a 1 * p 0) * r 0 := by rw [hr2, hp2]
        _ = 0 := by ring
  · ext i; fin_cases i <;> dsimp [cross3]
    · apply mul_left_cancel₀ h1
      rw [mul_zero]
      calc a 1 * (p 1 * r 2 - p 2 * r 1) = p 1 * (a 1 * r 2) - (a 1 * p 2) * r 1 := by ring
        _ = p 1 * (a 2 * r 1) - (a 2 * p 1) * r 1 := by rw [hr0, hp0]
        _ = 0 := by ring
    · apply mul_left_cancel₀ (mul_ne_zero h1 h1)
      rw [mul_zero]
      calc (a 1 * a 1) * (p 2 * r 0 - p 0 * r 2)
          = (a 1 * p 2) * (a 1 * r 0) - (a 1 * p 0) * (a 1 * r 2) := by ring
        _ = (a 2 * p 1) * (a 0 * r 1) - (a 0 * p 1) * (a 2 * r 1) := by rw [hp0, ← hr2, ← hp2, hr0]
        _ = 0 := by ring
    · apply mul_left_cancel₀ h1
      rw [mul_zero]
      calc a 1 * (p 0 * r 1 - p 1 * r 0) = (a 1 * p 0) * r 1 - p 1 * (a 1 * r 0) := by ring
        _ = (a 0 * p 1) * r 1 - p 1 * (a 0 * r 1) := by rw [← hp2, ← hr2]
        _ = 0 := by ring
  · ext i; fin_cases i <;> dsimp [cross3]
    · apply mul_left_cancel₀ h2
      rw [mul_zero]
      calc a 2 * (p 1 * r 2 - p 2 * r 1) = (a 2 * p 1) * r 2 - p 2 * (a 2 * r 1) := by ring
        _ = (a 1 * p 2) * r 2 - p 2 * (a 1 * r 2) := by rw [← hp0, ← hr0]
        _ = 0 := by ring
    · apply mul_left_cancel₀ h2
      rw [mul_zero]
      calc a 2 * (p 2 * r 0 - p 0 * r 2) = p 2 * (a 2 * r 0) - (a 2 * p 0) * r 2 := by ring
        _ = p 2 * (a 0 * r 2) - (a 0 * p 2) * r 2 := by rw [hr1, hp1]
        _ = 0 := by ring
    · apply mul_left_cancel₀ (mul_ne_zero h2 h2)
      rw [mul_zero]
      calc (a 2 * a 2) * (p 0 * r 1 - p 1 * r 0)
          = (a 2 * p 0) * (a 2 * r 1) - (a 2 * p 1) * (a 2 * r 0) := by ring
        _ = (a 0 * p 2) * (a 1 * r 2) - (a 1 * p 2) * (a 0 * r 2) := by rw [hp1, ← hr0, ← hp0, hr1]
        _ = 0 := by ring

lemma cross3_qVec_apply (v w : Fin 3 → ℂ) (i : Fin 3) :
    cross3 (qVec v) (qVec w) i = -(v i * w i * cross3 v w i) := by
  fin_cases i <;> dsimp [cross3, qVec] <;> ring

lemma cross3_add_smul_left (v w : Fin 3 → ℂ) (t : ℂ) :
    cross3 (v + t • w) w = cross3 v w := by
  ext i
  fin_cases i <;>
    simp only [cross3, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

lemma cross3_anticomm (v w : Fin 3 → ℂ) (i : Fin 3) :
    cross3 w v i = -cross3 v w i := by
  fin_cases i <;> dsimp [cross3] <;> ring

lemma finrank_le_three_C3_Q3 (L' : Submodule ℂ ((Fin 3 → ℂ) × (Fin 3 → ℂ)))
    (hL' : ∀ p ∈ L', C3 p.1 p.2 = 0 ∧ Q3 p.1 p.2 = 0) :
    Module.finrank ℂ L' ≤ 3 := by
  by_contra hgt
  push Not at hgt
  let π2 : L' →ₗ[ℂ] (Fin 3 → ℂ) :=
    { toFun := fun p => p.1.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let U : Submodule ℂ (Fin 3 → ℂ) :=
    { carrier := {u | (u, 0) ∈ L'}, add_mem' := fun ha hb => by simpa using L'.add_mem ha hb
      zero_mem' := L'.zero_mem
      smul_mem' := fun c _ ha => by simpa using L'.smul_mem c ha }
  let V : Submodule ℂ (Fin 3 → ℂ) := LinearMap.range π2
  have hker_equiv : LinearMap.ker π2 ≃ₗ[ℂ] U :=
    { toFun := fun p => ⟨p.1.1.1, by
        have hv : p.1.1.2 = 0 := p.2
        have hmem : (p.1.1.1, p.1.1.2) ∈ L' := p.1.2
        rw [hv] at hmem
        exact hmem⟩
      invFun := fun u => ⟨⟨(u.1, 0), u.2⟩, rfl⟩
      left_inv := fun p => by
        apply Subtype.ext; apply Subtype.ext
        exact Prod.ext rfl (Eq.symm p.2)
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsum_dim : Module.finrank ℂ U + Module.finrank ℂ V = Module.finrank ℂ L' := by
    have hrn := LinearMap.finrank_range_add_finrank_ker π2
    rw [LinearEquiv.finrank_eq hker_equiv] at hrn
    dsimp only [V]
    omega
  have hU_le : Module.finrank ℂ U ≤ 3 := by
    calc Module.finrank ℂ U ≤ Module.finrank ℂ (Fin 3 → ℂ) := Submodule.finrank_le _
      _ = 3 := by simp
  have hV_le : Module.finrank ℂ V ≤ 3 := by
    calc Module.finrank ℂ V ≤ Module.finrank ℂ (Fin 3 → ℂ) := Submodule.finrank_le _
      _ = 3 := by simp
  have hUV_CQ : ∀ u ∈ U, ∀ v ∈ V, C3 u v = 0 ∧ Q3 u v = 0 := by
    intro u hu v hv
    rcases hv with ⟨⟨⟨w, v'⟩, hwv⟩, hvEq⟩
    change v' = v at hvEq
    subst hvEq
    have hmem : ∀ t : ℂ, (w + t • u, v') ∈ L' := by
      intro t
      have h1 := L'.add_mem hwv (L'.smul_mem t hu)
      simpa using h1
    have hC0 : C3 w v' = 0 := (hL' (w, v') hwv).1
    have hC1 : C3 (w + (1 : ℂ) • u) v' = 0 := (hL' _ (hmem 1)).1
    have hC : C3 u v' = 0 := by
      have hlin : C3 (w + (1 : ℂ) • u) v' = C3 w v' + C3 u v' := by
        unfold C3; simp only [Pi.add_apply, one_smul]; ring
      rw [hlin, hC0, zero_add] at hC1
      exact hC1
    have hQ0 : Q3 w v' = 0 := (hL' (w, v') hwv).2
    have hQ1 : Q3 (w + (1 : ℂ) • u) v' = 0 := (hL' _ (hmem 1)).2
    have hQm1 : Q3 (w + (-1 : ℂ) • u) v' = 0 := (hL' _ (hmem (-1))).2
    have hQ2 : Q3 (w + (2 : ℂ) • u) v' = 0 := (hL' _ (hmem 2)).2
    have hQ : Q3 u v' = 0 := by
      have hcomb : 6 * Q3 u v' = Q3 (w + (2 : ℂ) • u) v' - 3 * Q3 (w + (1 : ℂ) • u) v' +
          3 * Q3 w v' - Q3 (w + (-1 : ℂ) • u) v' := by
        unfold Q3; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [hQ2, hQ1, hQ0, hQm1] at hcomb
      have : (6 : ℂ) * Q3 u v' = 0 := by simpa using hcomb
      exact (mul_eq_zero.mp this).resolve_left (by norm_num)
    exact ⟨hC, hQ⟩
  let e0 : Fin 3 → ℂ := fun i => if i = 0 then 1 else 0
  let e1 : Fin 3 → ℂ := fun i => if i = 1 then 1 else 0
  let e2 : Fin 3 → ℂ := fun i => if i = 2 then 1 else 0
  let c0 : Fin 3 → ℂ := fun i => if i = 0 then 0 else 1
  let c1 : Fin 3 → ℂ := fun i => if i = 1 then 0 else 1
  let c2 : Fin 3 → ℂ := fun i => if i = 2 then 0 else 1
  by_cases hU3 : Module.finrank ℂ U = 3
  · have hUtop : U = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hU3]; simp)
    have hVpos : 0 < Module.finrank ℂ V := by omega
    have hVne : V ≠ ⊥ := by
      intro hbot; rw [hbot, finrank_bot] at hVpos; omega
    rcases Submodule.exists_mem_ne_zero_of_ne_bot hVne with ⟨v, hv, hv0⟩
    have hv0' : v 0 = 0 := by
      have hq := (hUV_CQ e0 (hUtop ▸ Submodule.mem_top) v hv).2
      simpa [Q3, e0] using hq
    have hv1' : v 1 = 0 := by
      have hq := (hUV_CQ e1 (hUtop ▸ Submodule.mem_top) v hv).2
      simpa [Q3, e1] using hq
    have hv2' : v 2 = 0 := by
      have hq := (hUV_CQ e2 (hUtop ▸ Submodule.mem_top) v hv).2
      simpa [Q3, e2] using hq
    exact hv0 (by ext i; fin_cases i <;> assumption)
  · by_cases hV3 : Module.finrank ℂ V = 3
    · have hVtop : V = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hV3]; simp)
      have hUpos : 0 < Module.finrank ℂ U := by omega
      have hUne : U ≠ ⊥ := by
        intro hbot; rw [hbot, finrank_bot] at hUpos; omega
      rcases Submodule.exists_mem_ne_zero_of_ne_bot hUne with ⟨u, hu, hu0⟩
      have hu0' : u 0 = 0 := by
        have hc := (hUV_CQ u hu c0 (hVtop ▸ Submodule.mem_top)).1
        simpa [C3, c0] using hc
      have hu1' : u 1 = 0 := by
        have hc := (hUV_CQ u hu c1 (hVtop ▸ Submodule.mem_top)).1
        simpa [C3, c1] using hc
      have hu2' : u 2 = 0 := by
        have hc := (hUV_CQ u hu c2 (hVtop ▸ Submodule.mem_top)).1
        simpa [C3, c2] using hc
      exact hu0 (by ext i; fin_cases i <;> assumption)
    · have hU2 : Module.finrank ℂ U = 2 := by omega
      have hV2 : Module.finrank ℂ V = 2 := by omega
      let bU : Module.Basis (Fin 2) ℂ U := Module.finBasisOfFinrankEq ℂ U hU2
      let bV : Module.Basis (Fin 2) ℂ V := Module.finBasisOfFinrankEq ℂ V hV2
      let uA : Fin 3 → ℂ := (bU 0).1
      let uB : Fin 3 → ℂ := (bU 1).1
      let vA : Fin 3 → ℂ := (bV 0).1
      let vB : Fin 3 → ℂ := (bV 1).1
      have ha_ne : cross3 uA uB ≠ 0 := by
        apply cross3_ne_zero_of_li
        intro c1 c2 hdep
        have hK : c1 • bU 0 + c2 • bU 1 = 0 := Subtype.ext (by simpa [uA, uB] using hdep)
        have hlin := Fintype.linearIndependent_iff.mp bU.linearIndependent ![c1, c2]
          (by rw [Fin.sum_univ_two]; simpa using hK)
        exact ⟨hlin 0, hlin 1⟩
      have hb_ne : cross3 vA vB ≠ 0 := by
        apply cross3_ne_zero_of_li
        intro c1 c2 hdep
        have hK : c1 • bV 0 + c2 • bV 1 = 0 := Subtype.ext (by simpa [vA, vB] using hdep)
        have hlin := Fintype.linearIndependent_iff.mp bV.linearIndependent ![c1, c2]
          (by rw [Fin.sum_univ_two]; simpa using hK)
        exact ⟨hlin 0, hlin 1⟩
      have hq_par : ∀ v ∈ V, cross3 (cross3 uA uB) (qVec v) = 0 := by
        intro v hv
        rw [cross3_cross3, ← C3_eq_dot3, ← C3_eq_dot3,
          (hUV_CQ uA (bU 0).2 v hv).1, (hUV_CQ uB (bU 1).2 v hv).1]
        simp
      have hpair_zero : ∀ v ∈ V, ∀ w ∈ V, ∀ i : Fin 3, v i * w i * cross3 v w i = 0 := by
        intro v hv w hw i
        have hcr := cross3_eq_zero_of_parallel ha_ne (hq_par v hv) (hq_par w hw)
        have hi := congrFun hcr i
        rw [cross3_qVec_apply] at hi
        exact neg_eq_zero.mp hi
      have hcoord_kill : ∀ i : Fin 3, cross3 vA vB i ≠ 0 → vA i = 0 ∧ vB i = 0 := by
        intro i hbi
        have h0 := hpair_zero vA (bV 0).2 vB (bV 1).2 i
        have h1 : (vA + (1 : ℂ) • vB) i * vB i * cross3 (vA + (1 : ℂ) • vB) vB i = 0 :=
          hpair_zero _ (V.add_mem (bV 0).2 (V.smul_mem 1 (bV 1).2)) vB (bV 1).2 i
        rw [cross3_add_smul_left] at h1
        have hvw : vA i * vB i = 0 := (mul_eq_zero.mp h0).resolve_right hbi
        have hsum0 : (vA i + vB i) * vB i = 0 := by
          have := (mul_eq_zero.mp h1).resolve_right hbi
          simpa using this
        have hvB0 : vB i = 0 := by
          have hsq : vB i * vB i = 0 := by linear_combination hsum0 - hvw
          exact mul_self_eq_zero.mp hsq
        have h2 : (vB + (1 : ℂ) • vA) i * vA i * cross3 (vB + (1 : ℂ) • vA) vA i = 0 :=
          hpair_zero _ (V.add_mem (bV 1).2 (V.smul_mem 1 (bV 0).2)) vA (bV 0).2 i
        rw [cross3_add_smul_left] at h2
        have hbi' : cross3 vB vA i ≠ 0 := by rw [cross3_anticomm]; exact neg_ne_zero.mpr hbi
        have hsum1 : (vB i + vA i) * vA i = 0 := by
          have := (mul_eq_zero.mp h2).resolve_right hbi'
          simpa using this
        have hvA0 : vA i = 0 := by
          rw [hvB0, zero_add] at hsum1
          exact mul_self_eq_zero.mp hsum1
        exact ⟨hvA0, hvB0⟩
      have hb_ex : cross3 vA vB 0 ≠ 0 ∨ cross3 vA vB 1 ≠ 0 ∨ cross3 vA vB 2 ≠ 0 := by
        by_contra h; push Not at h
        exact hb_ne (by ext i; fin_cases i <;> tauto)
      have hplane_eq : ∀ (S : Submodule ℂ (Fin 3 → ℂ)) (k : Fin 3),
          Module.finrank ℂ S = 2 → (∀ x ∈ S, x k = 0) →
          ∀ x : Fin 3 → ℂ, x k = 0 → x ∈ S := by
        intro S k hS2 hSk
        let ev : (Fin 3 → ℂ) →ₗ[ℂ] ℂ :=
          { toFun := fun x => x k
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        let P : Submodule ℂ (Fin 3 → ℂ) := LinearMap.ker ev
        have hSP : S ≤ P := fun x hx => hSk x hx
        have hP2 : Module.finrank ℂ P = 2 := by
          have hsurj : LinearMap.range ev = ⊤ := by
            rw [Submodule.eq_top_iff']
            intro c
            refine ⟨fun j => if j = k then c else 0, ?_⟩
            simp [ev]
          have hrn := LinearMap.finrank_range_add_finrank_ker ev
          rw [hsurj, finrank_top, Module.finrank_self] at hrn
          have h3 : Module.finrank ℂ (Fin 3 → ℂ) = 3 := by simp
          dsimp only [P]
          omega
        have hEq : S = P := Submodule.eq_of_le_of_finrank_eq hSP (by rw [hS2, hP2])
        intro x hx
        rw [hEq]; exact hx
      have hV_coord : ∀ k : Fin 3, vA k = 0 → vB k = 0 → ∀ v ∈ V, v k = 0 := by
        intro k hA hB v hv
        have hrepr := bV.sum_repr ⟨v, hv⟩
        have hval := congrArg (fun x : V => x.1 k) hrepr
        rw [Fin.sum_univ_two] at hval
        simp only [Submodule.coe_add, SetLike.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hval
        change _ * vA k + _ * vB k = v k at hval
        rw [hA, hB, mul_zero, mul_zero, add_zero] at hval
        exact hval.symm
      rcases hb_ex with hb0 | hb1 | hb2
      · rcases hcoord_kill 0 hb0 with ⟨hA, hB⟩
        have hV0 := hplane_eq V 0 hV2 (hV_coord 0 hA hB)
        have hU_sub : ∀ u ∈ U, u 0 = 0 := by
          intro u hu
          have hc := (hUV_CQ u hu c0 (hV0 c0 (by simp [c0]))).1
          simpa [C3, c0] using hc
        have hU0 := hplane_eq U 0 hU2 hU_sub
        have hq := (hUV_CQ e1 (hU0 e1 (by simp [e1])) e1 (hV0 e1 (by simp [e1]))).2
        simp [Q3, e1] at hq
      · rcases hcoord_kill 1 hb1 with ⟨hA, hB⟩
        have hV1 := hplane_eq V 1 hV2 (hV_coord 1 hA hB)
        have hU_sub : ∀ u ∈ U, u 1 = 0 := by
          intro u hu
          have hc := (hUV_CQ u hu c1 (hV1 c1 (by simp [c1]))).1
          simpa [C3, c1] using hc
        have hU1 := hplane_eq U 1 hU2 hU_sub
        have hq := (hUV_CQ e0 (hU1 e0 (by simp [e0])) e0 (hV1 e0 (by simp [e0]))).2
        simp [Q3, e0] at hq
      · rcases hcoord_kill 2 hb2 with ⟨hA, hB⟩
        have hV2' := hplane_eq V 2 hV2 (hV_coord 2 hA hB)
        have hU_sub : ∀ u ∈ U, u 2 = 0 := by
          intro u hu
          have hc := (hUV_CQ u hu c2 (hV2' c2 (by simp [c2]))).1
          simpa [C3, c2] using hc
        have hU2' := hplane_eq U 2 hU2 hU_sub
        have hq := (hUV_CQ e0 (hU2' e0 (by simp [e0])) e0 (hV2' e0 (by simp [e0]))).2
        simp [Q3, e0] at hq

end

end PEqualNP.Outside.L_gct_278_aux

theorem PEqualNP.Outside.L_gct_278 :
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ 5 →
      (∀ L : Submodule ℂ ((Fin 4 → ℂ) × (Fin 4 → ℂ)),
        (∀ x ∈ L, (∑ i, x.1 i) = 0 ∧ (∑ i, x.2 i) = 0 ∧
          (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
            (1 + x.1 i * ζ ^ (f i).val + x.2 i * ζ ^ (2 * (f i).val))) = 120) →
          Module.finrank ℂ L ≤ 3) ∧
      (∃ L : Submodule ℂ ((Fin 4 → ℂ) × (Fin 4 → ℂ)),
        Module.finrank ℂ L = 3 ∧
          ∀ x ∈ L, (∑ i, x.1 i) = 0 ∧ (∑ i, x.2 i) = 0 ∧
            (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
              (1 + x.1 i * ζ ^ (f i).val + x.2 i * ζ ^ (2 * (f i).val))) = 120) := by
  intro ζ hζ
  constructor
  · intro L hL
    let φ : ((Fin 4 → ℂ) × (Fin 4 → ℂ)) →ₗ[ℂ] ((Fin 3 → ℂ) × (Fin 3 → ℂ)) :=
      { toFun := fun p => (PEqualNP.Outside.L_gct_278_aux.invHadamard p.1,
          PEqualNP.Outside.L_gct_278_aux.invHadamard p.2)
        map_add' := fun p q => by
          ext i <;> fin_cases i <;>
            simp only [PEqualNP.Outside.L_gct_278_aux.invHadamard, Prod.fst_add, Prod.snd_add,
              Pi.add_apply] <;> ring
        map_smul' := fun c p => by
          ext i <;> fin_cases i <;>
            simp only [PEqualNP.Outside.L_gct_278_aux.invHadamard, Prod.smul_fst, Prod.smul_snd,
              Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring }
    let L' : Submodule ℂ ((Fin 3 → ℂ) × (Fin 3 → ℂ)) := L.map φ
    have hL'_CQ : ∀ q ∈ L', PEqualNP.Outside.L_gct_278_aux.C3 q.1 q.2 = 0 ∧
        PEqualNP.Outside.L_gct_278_aux.Q3 q.1 q.2 = 0 := by
      rintro q ⟨p, hpL, rfl⟩
      have h1 := hL p hpL
      have hneg := hL ((-1 : ℂ) • p) (L.smul_mem (-1) hpL)
      have hp1 : 120 + 20 * PEqualNP.Outside.L_gct_278_aux.Craw p.1 p.2 -
          30 * PEqualNP.Outside.L_gct_278_aux.Qraw p.1 p.2 = 120 := by
        rw [← PEqualNP.Outside.L_gct_278_aux.perm_exact_formula hζ]; exact h1.2.2
      have hpm1 : 120 + 20 * PEqualNP.Outside.L_gct_278_aux.Craw ((-1 : ℂ) • p.1) ((-1 : ℂ) • p.2) -
          30 * PEqualNP.Outside.L_gct_278_aux.Qraw ((-1 : ℂ) • p.1) ((-1 : ℂ) • p.2) = 120 := by
        rw [← PEqualNP.Outside.L_gct_278_aux.perm_exact_formula hζ]; exact hneg.2.2
      have hCneg : PEqualNP.Outside.L_gct_278_aux.Craw ((-1 : ℂ) • p.1) ((-1 : ℂ) • p.2) =
          -PEqualNP.Outside.L_gct_278_aux.Craw p.1 p.2 := by
        unfold PEqualNP.Outside.L_gct_278_aux.Craw; simp only [Pi.smul_apply, smul_eq_mul]; ring
      have hQneg : PEqualNP.Outside.L_gct_278_aux.Qraw ((-1 : ℂ) • p.1) ((-1 : ℂ) • p.2) =
          PEqualNP.Outside.L_gct_278_aux.Qraw p.1 p.2 := by
        unfold PEqualNP.Outside.L_gct_278_aux.Qraw; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [hCneg, hQneg] at hpm1
      have hCraw0 : PEqualNP.Outside.L_gct_278_aux.Craw p.1 p.2 = 0 := by
        have : (40 : ℂ) * PEqualNP.Outside.L_gct_278_aux.Craw p.1 p.2 = 0 := by
          linear_combination hp1 - hpm1
        exact (mul_eq_zero.mp this).resolve_left (by norm_num)
      have hQraw0 : PEqualNP.Outside.L_gct_278_aux.Qraw p.1 p.2 = 0 := by
        have : (-60 : ℂ) * PEqualNP.Outside.L_gct_278_aux.Qraw p.1 p.2 = 0 := by
          linear_combination hp1 + hpm1
        exact (mul_eq_zero.mp this).resolve_left (by norm_num)
      have hp1_eq := PEqualNP.Outside.L_gct_278_aux.hadamard_invHadamard p.1 h1.1
      have hp2_eq := PEqualNP.Outside.L_gct_278_aux.hadamard_invHadamard p.2 h1.2.1
      have hC3 : 8 * PEqualNP.Outside.L_gct_278_aux.C3 (φ p).1 (φ p).2 = 0 := by
        rw [← PEqualNP.Outside.L_gct_278_aux.Craw_hadamard]
        change PEqualNP.Outside.L_gct_278_aux.Craw
          (PEqualNP.Outside.L_gct_278_aux.hadamard (PEqualNP.Outside.L_gct_278_aux.invHadamard p.1))
          (PEqualNP.Outside.L_gct_278_aux.hadamard (PEqualNP.Outside.L_gct_278_aux.invHadamard p.2)) = 0
        rw [hp1_eq, hp2_eq, hCraw0]
      have hQ3 : 4 * PEqualNP.Outside.L_gct_278_aux.Q3 (φ p).1 (φ p).2 = 0 := by
        rw [← PEqualNP.Outside.L_gct_278_aux.Qraw_hadamard]
        change PEqualNP.Outside.L_gct_278_aux.Qraw
          (PEqualNP.Outside.L_gct_278_aux.hadamard (PEqualNP.Outside.L_gct_278_aux.invHadamard p.1))
          (PEqualNP.Outside.L_gct_278_aux.hadamard (PEqualNP.Outside.L_gct_278_aux.invHadamard p.2)) = 0
        rw [hp1_eq, hp2_eq, hQraw0]
      exact ⟨(mul_eq_zero.mp hC3).resolve_left (by norm_num),
        (mul_eq_zero.mp hQ3).resolve_left (by norm_num)⟩
    have hinj : ∀ p ∈ L, φ p = 0 → p = 0 := by
      intro p hpL h0
      have h1 := hL p hpL
      have hfst : PEqualNP.Outside.L_gct_278_aux.invHadamard p.1 = 0 := congrArg Prod.fst h0
      have hsnd : PEqualNP.Outside.L_gct_278_aux.invHadamard p.2 = 0 := congrArg Prod.snd h0
      have hp1 : p.1 = 0 := by
        rw [← PEqualNP.Outside.L_gct_278_aux.hadamard_invHadamard p.1 h1.1, hfst]
        ext i; fin_cases i <;> simp [PEqualNP.Outside.L_gct_278_aux.hadamard]
      have hp2 : p.2 = 0 := by
        rw [← PEqualNP.Outside.L_gct_278_aux.hadamard_invHadamard p.2 h1.2.1, hsnd]
        ext i; fin_cases i <;> simp [PEqualNP.Outside.L_gct_278_aux.hadamard]
      exact Prod.ext hp1 hp2
    have hfin : Module.finrank ℂ L = Module.finrank ℂ L' := by
      let φL : L →ₗ[ℂ] L' :=
        { toFun := fun x => ⟨φ x.1, ⟨x.1, x.2, rfl⟩⟩
          map_add' := fun x y => Subtype.ext (map_add φ x.1 y.1)
          map_smul' := fun c x => Subtype.ext (map_smul φ c x.1) }
      have hlin : L ≃ₗ[ℂ] L' := LinearEquiv.ofBijective φL
        ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ hEq => by
          have hsub : φ (x - y) = 0 := by
            rw [map_sub, sub_eq_zero]; exact congrArg Subtype.val hEq
          have hxy : x - y = 0 := hinj (x - y) (L.sub_mem hx hy) hsub
          exact Subtype.ext (sub_eq_zero.mp hxy),
         fun ⟨y, x, hx, hxy⟩ => ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
      exact LinearEquiv.finrank_eq hlin
    rw [hfin]
    exact PEqualNP.Outside.L_gct_278_aux.finrank_le_three_C3_Q3 L' hL'_CQ
  · let ψ : (Fin 3 → ℂ) →ₗ[ℂ] ((Fin 4 → ℂ) × (Fin 4 → ℂ)) :=
      { toFun := fun u => (PEqualNP.Outside.L_gct_278_aux.hadamard u, 0)
        map_add' := fun u v => by
          ext i
          · fin_cases i <;>
              simp only [PEqualNP.Outside.L_gct_278_aux.hadamard, Prod.fst_add, Pi.add_apply] <;> ring
          · simp
        map_smul' := fun c u => by
          ext i
          · fin_cases i <;>
              simp only [PEqualNP.Outside.L_gct_278_aux.hadamard, Prod.smul_fst, Pi.smul_apply,
                smul_eq_mul, RingHom.id_apply] <;> ring
          · simp }
    refine ⟨LinearMap.range ψ, ?_, ?_⟩
    · have hinj : Function.Injective ψ := by
        intro u1 u2 hEq
        have h1 := congrArg (fun p => PEqualNP.Outside.L_gct_278_aux.invHadamard p.1) hEq
        change PEqualNP.Outside.L_gct_278_aux.invHadamard (PEqualNP.Outside.L_gct_278_aux.hadamard u1) =
          PEqualNP.Outside.L_gct_278_aux.invHadamard (PEqualNP.Outside.L_gct_278_aux.hadamard u2) at h1
        rw [PEqualNP.Outside.L_gct_278_aux.invHadamard_hadamard,
          PEqualNP.Outside.L_gct_278_aux.invHadamard_hadamard] at h1
        exact h1
      rw [LinearMap.finrank_range_of_inj hinj]
      simp
    · rintro _ ⟨u, rfl⟩
      refine ⟨PEqualNP.Outside.L_gct_278_aux.hadamard_sum_zero u, by simp [ψ], ?_⟩
      rw [PEqualNP.Outside.L_gct_278_aux.perm_exact_formula hζ]
      simp [ψ, PEqualNP.Outside.L_gct_278_aux.Craw, PEqualNP.Outside.L_gct_278_aux.Qraw]

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_249

open Classical

abbrev K := ZMod 2

theorem card_sub (n : ℕ) (P : Submodule K (Fin n → K)) :
    Fintype.card P = 2 ^ Module.finrank K P := by
  rw [Module.card_eq_pow_finrank (K := K) (V := P)]
  simp [K, ZMod.card]

theorem mid_card (n : ℕ) (U V : Submodule K (Fin n → K)) (x z : Fin n → K) :
    (Finset.univ.filter (fun y : Fin n → K => y - x ∈ U ∧ z - y ∈ V)).card =
      if z - x ∈ U ⊔ V then 2 ^ Module.finrank K (U ⊓ V : Submodule K (Fin n → K)) else 0 := by
  classical
  split_ifs with h
  · obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h

    rw [← card_sub n (U ⊓ V), ← Fintype.card_coe]
    refine Fintype.card_congr ?_
    exact
      { toFun := fun y => ⟨y.1 - (x + u), by
          obtain ⟨hy1, hy2⟩ := (Finset.mem_filter.1 y.2).2
          refine ⟨?_, ?_⟩
          · have : y.1 - (x + u) = (y.1 - x) - u := by abel
            rw [this]; exact U.sub_mem hy1 hu
          · have : y.1 - (x + u) = v - (z - y.1) := by
              linear_combination -huv
            rw [this]; exact V.sub_mem hv hy2⟩
        invFun := fun w => ⟨w.1 + (x + u), by
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
          · have : w.1 + (x + u) - x = w.1 + u := by abel
            rw [this]; exact U.add_mem w.2.1 hu
          · have : z - (w.1 + (x + u)) = v - w.1 := by
              linear_combination -huv
            rw [this]; exact V.sub_mem hv w.2.2⟩
        left_inv := fun y => by ext1; simp
        right_inv := fun w => by ext1; simp }
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro y - ⟨h1, h2⟩
    exact h (by
      have : z - x = (y - x) + (z - y) := by abel
      rw [this]; exact Submodule.add_mem_sup h1 h2)

def tri (X : Type) : (Fin 3 → X) ≃ X × X × X where
  toFun v := (v 0, v 1, v 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv t := rfl

theorem count_eq (n a b c : ℕ) (A : (Fin n → K) →ₗ[K] (Fin a → K)) (B : (Fin n → K) →ₗ[K] (Fin b → K))
    (p : Fin a → K) (q : Fin b → K) (h : (Fin n → K) → (Fin c → K)) :
    (Finset.univ.filter (fun v : Fin 3 → (Fin n → K) =>
      A (v 0) + p = A (v 1) + p ∧ B (v 1) + q = B (v 2) + q ∧ h (v 2) = h (v 0))).card =
    2 ^ Module.finrank K (LinearMap.ker A ⊓ LinearMap.ker B : Submodule K (Fin n → K)) *
      ∑ x : Fin n → K, (Finset.univ.filter (fun z : Fin n → K =>
        z - x ∈ LinearMap.ker A ⊔ LinearMap.ker B ∧ h z = h x)).card := by
  set U := LinearMap.ker A
  set V := LinearMap.ker B
  rw [Finset.card_equiv (tri (Fin n → K)) (t := Finset.univ.filter (fun t : (Fin n → K) × (Fin n → K) × (Fin n → K) =>
      t.2.1 - t.1 ∈ U ∧ t.2.2 - t.2.1 ∈ V ∧ h t.2.2 = h t.1))]
  swap
  · intro v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, tri, add_left_inj, U, V,
      LinearMap.mem_ker, map_sub, sub_eq_zero]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1.symm, h2.symm, h3⟩
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases hz : h z = h x
  · have := mid_card n U V x z
    rw [Finset.card_filter] at this
    simp only [hz, and_true, this]
    split_ifs <;> simp
  · simp [hz]

noncomputable def cell (n c : ℕ) (W : Submodule K (Fin n → K)) (h : (Fin n → K) → (Fin c → K)) (x : Fin n → K) :
    Finset (Fin n → K) :=
  Finset.univ.filter (fun z => z - x ∈ W ∧ h z = h x)

theorem card_X (n : ℕ) : Fintype.card (Fin n → K) = 2 ^ n := by simp [K, ZMod.card]

theorem bound (n c : ℕ) (W : Submodule K (Fin n → K)) (h : (Fin n → K) → (Fin c → K)) :
    2 ^ n * 2 ^ (Module.finrank K W - c) ≤ ∑ x, (cell n c W h x).card ∧
    (∑ x, (cell n c W h x).card = 2 ^ n * 2 ^ (Module.finrank K W - c) ↔
      ∀ x, (cell n c W h x).card = 2 ^ (Module.finrank K W - c)) := by
  set s := Module.finrank K W
  set m := 2 ^ (s - c)
  have back : (∀ x, (cell n c W h x).card = m) → ∑ x, (cell n c W h x).card = 2 ^ n * m := by
    intro hx
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_const, Finset.card_univ, card_X, smul_eq_mul]
  have self_mem : ∀ x, x ∈ cell n c W h x := fun x => by simp [cell]
  rcases Nat.lt_or_ge c s with hcs | hcs
  ·
    let φ : (Fin n → K) → ((Fin n → K) ⧸ W) × (Fin c → K) := fun x => (W.mkQ x, h x)
    have hcell : ∀ x, cell n c W h x = Finset.univ.filter (fun z => φ z = φ x) := by
      intro x; ext z
      simp [cell, φ, Prod.ext_iff, Submodule.Quotient.eq]
    let f : ((Fin n → K) ⧸ W) × (Fin c → K) → ℕ := fun p => (Finset.univ.filter (fun x => φ x = p)).card
    have hS : ∑ x, (cell n c W h x).card = ∑ p, f p ^ 2 := by
      simp_rw [hcell]
      rw [← Finset.sum_fiberwise Finset.univ φ]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, smul_eq_mul, sq]
    have hF : ∑ p, f p = 2 ^ n := by
      have := Finset.sum_fiberwise Finset.univ φ (fun _ => (1 : ℕ))
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, card_X] at this
      exact this
    have hN : Fintype.card (((Fin n → K) ⧸ W) × (Fin c → K)) * m = 2 ^ n := by
      have h1 := Submodule.card_eq_card_quotient_mul_card W
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_X, card_sub] at h1
      rw [Fintype.card_prod, h1, card_X]
      simp only [m]
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hcs.le, mul_comm]
    have key : ((∑ x, (cell n c W h x).card : ℕ) : ℤ) = 2 ^ n * m + ∑ p, ((f p : ℤ) - m) ^ 2 := by
      have e : ∀ p, ((f p : ℤ) - m) ^ 2 = (f p : ℤ) ^ 2 - (2 * m) * f p + m ^ 2 := fun p => by ring
      simp_rw [e]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      have hS' : ((∑ x, (cell n c W h x).card : ℕ) : ℤ) = ∑ p, (f p : ℤ) ^ 2 := by rw [hS]; push_cast; rfl
      have hF' : (∑ p, (f p : ℤ)) = 2 ^ n := by exact_mod_cast hF
      have hN' : (Fintype.card (((Fin n → K) ⧸ W) × (Fin c → K)) : ℤ) * m = 2 ^ n := by exact_mod_cast hN
      rw [hS', hF']
      linear_combination (-(m : ℤ)) * hN'
    have nn : 0 ≤ ∑ p, ((f p : ℤ) - m) ^ 2 := Finset.sum_nonneg (fun p _ => sq_nonneg _)
    have h2 : ((2 ^ n * m : ℕ) : ℤ) ≤ ((∑ x, (cell n c W h x).card : ℕ) : ℤ) := by
      rw [key]; push_cast; linarith
    refine ⟨by exact_mod_cast h2, ⟨fun heq => ?_, back⟩⟩
    have z : ∑ p, ((f p : ℤ) - m) ^ 2 = 0 := by
      have : ((∑ x, (cell n c W h x).card : ℕ) : ℤ) = 2 ^ n * m := by exact_mod_cast heq
      linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun p _ => sq_nonneg _)] at z
    intro x
    have := z (φ x) (Finset.mem_univ _)
    rw [hcell x]
    have : (f (φ x) : ℤ) = m := by nlinarith [sq_nonneg ((f (φ x) : ℤ) - m)]
    exact_mod_cast this
  ·
    have hm : m = 1 := by simp [m, Nat.sub_eq_zero_of_le hcs]
    have one_le : ∀ x, 1 ≤ (cell n c W h x).card := fun x => Finset.card_pos.2 ⟨x, self_mem x⟩
    have hsum : ∑ _x : Fin n → K, (1 : ℕ) = 2 ^ n := by simp
    rw [hm, mul_one]
    refine ⟨hsum ▸ Finset.sum_le_sum (fun x _ => one_le x), ?_⟩
    rw [← hsum, eq_comm, Finset.sum_eq_sum_iff_of_le (fun x _ => one_le x)]
    simp [eq_comm]

theorem exists_ker (c : ℕ) (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] :
    ∃ f : W →ₗ[K] (Fin c → K), Module.finrank K (LinearMap.ker f) = Module.finrank K W - c := by
  set s := Module.finrank K W
  let e : W ≃ₗ[K] (Fin s → K) := (Module.finBasisOfFinrankEq K W rfl).equivFun
  rcases Nat.lt_or_ge s c with hsc | hcs
  · obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective
      (LinearMap.funLeft K K (Fin.castLE hsc.le)) (LinearMap.range_eq_top.2
        (LinearMap.funLeft_surjective_of_injective K K _ (Fin.castLE_injective hsc.le)))
    refine ⟨g ∘ₗ e.toLinearMap, ?_⟩
    have hinj : Function.Injective (g ∘ₗ e.toLinearMap) := by
      intro a b hab
      have := congrArg (LinearMap.funLeft K K (Fin.castLE hsc.le)) hab
      simp only [LinearMap.coe_comp, Function.comp_apply] at this
      rw [← LinearMap.comp_apply (LinearMap.funLeft K K (Fin.castLE hsc.le)) g,
        ← LinearMap.comp_apply (LinearMap.funLeft K K (Fin.castLE hsc.le)) g, hg] at this
      simpa using this
    rw [LinearMap.ker_eq_bot.2 hinj, finrank_bot]
    omega
  · let g := LinearMap.funLeft K K (Fin.castLE hcs)
    have hsurj : Function.Surjective (g ∘ₗ e.toLinearMap) :=
      (LinearMap.funLeft_surjective_of_injective K K _ (Fin.castLE_injective hcs)).comp e.surjective
    refine ⟨g ∘ₗ e.toLinearMap, ?_⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker (g ∘ₗ e.toLinearMap)
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h1
    rw [Module.finrank_fin_fun K] at h1
    omega

theorem exists_L (n c : ℕ) (W : Submodule K (Fin n → K)) :
    ∃ L : (Fin n → K) →ₗ[K] (Fin c → K), ∀ x, (cell n c W L x).card = 2 ^ (Module.finrank K W - c) := by
  obtain ⟨f, hf⟩ := exists_ker c W
  obtain ⟨L, hL⟩ := LinearMap.exists_extend f
  refine ⟨L, fun x => ?_⟩
  have hrank : Module.finrank K (W ⊓ LinearMap.ker L : Submodule K (Fin n → K)) = Module.finrank K W - c := by
    rw [← hf, ← hL, LinearMap.ker_comp, ← Submodule.map_comap_subtype]
    exact (Submodule.equivMapOfInjective W.subtype W.injective_subtype _).finrank_eq.symm
  rw [← hrank, ← card_sub n, ← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun z => ⟨z.1 - x, by
        obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 z.2).2
        exact ⟨h1, by simp [LinearMap.mem_ker, map_sub, h2]⟩⟩
      invFun := fun w => ⟨w.1 + x, by
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using w.2.1, ?_⟩
        have := LinearMap.mem_ker.1 (Submodule.mem_inf.1 w.2).2
        simp [map_add, this]⟩
      left_inv := fun z => by ext1; simp
      right_inv := fun w => by ext1; simp }

end PEqualNP.Outside.L_pcx_249

theorem PEqualNP.Outside.L_pcx_249 : (∀ (n a b c : ℕ),
  let K := ZMod 2
  let X := Fin n → K
  let Y := Fin c → K
  ∀ (A : X →ₗ[K] (Fin a → K)) (B : X →ₗ[K] (Fin b → K))
    (p : Fin a → K) (q : Fin b → K),
    let U := LinearMap.ker A
    let V := LinearMap.ker B
    let i := Module.finrank K (U ⊓ V : Submodule K X)
    let s := Module.finrank K (U ⊔ V : Submodule K X)
    let cells := fun (color : X → Y) (x : X) => @Finset.filter X
      (fun z : X => z - x ∈ U ⊔ V ∧ color z = color x) (Classical.decPred _) Finset.univ
    let count := fun h : X → Y => (Finset.univ.filter (fun v : Fin 3 → X =>
      A (v 0) + p = A (v 1) + p ∧ B (v 1) + q = B (v 2) + q ∧ h (v 2) = h (v 0))).card
    let optimum := 2^(n+i+(s-c))
    (∀ h : X → Y,
      count h = 2^i * ∑ x : X, (cells h x).card ∧ optimum ≤ count h ∧
      (count h = optimum ↔ ∀ x : X, (cells h x).card = 2^(s-c))) ∧
    ∃ L : X →ₗ[K] Y, count L = optimum) := by
  intro n a b c
  dsimp only
  intro A B p q
  have opt : 2 ^ (n + Module.finrank (ZMod 2) (LinearMap.ker A ⊓ LinearMap.ker B : Submodule (ZMod 2) (Fin n → ZMod 2)) +
      (Module.finrank (ZMod 2) (LinearMap.ker A ⊔ LinearMap.ker B : Submodule (ZMod 2) (Fin n → ZMod 2)) - c)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker A ⊓ LinearMap.ker B : Submodule (ZMod 2) (Fin n → ZMod 2)) *
      (2 ^ n * 2 ^ (Module.finrank (ZMod 2) (LinearMap.ker A ⊔ LinearMap.ker B : Submodule (ZMod 2) (Fin n → ZMod 2)) - c)) := by
    rw [pow_add, pow_add]; ring
  have hcell : ∀ (h : (Fin n → ZMod 2) → (Fin c → ZMod 2)) (x : Fin n → ZMod 2),
      (@Finset.filter (Fin n → ZMod 2) (fun z => z - x ∈ LinearMap.ker A ⊔ LinearMap.ker B ∧ h z = h x)
        (Classical.decPred _) Finset.univ) =
      PEqualNP.Outside.L_pcx_249.cell n c (LinearMap.ker A ⊔ LinearMap.ker B) h x := by
    intro h x; ext z; simp [PEqualNP.Outside.L_pcx_249.cell]
  have all : ∀ h : (Fin n → ZMod 2) → (Fin c → ZMod 2),
      (Finset.univ.filter (fun v : Fin 3 → (Fin n → ZMod 2) =>
        A (v 0) + p = A (v 1) + p ∧ B (v 1) + q = B (v 2) + q ∧ h (v 2) = h (v 0))).card =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker A ⊓ LinearMap.ker B : Submodule (ZMod 2) (Fin n → ZMod 2)) *
        ∑ x, (PEqualNP.Outside.L_pcx_249.cell n c (LinearMap.ker A ⊔ LinearMap.ker B) h x).card := by
    intro h
    rw [PEqualNP.Outside.L_pcx_249.count_eq n a b c A B p q h]
    congr 1
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨hle, hiff⟩ := PEqualNP.Outside.L_pcx_249.bound n c (LinearMap.ker A ⊔ LinearMap.ker B) h
    have hpos : 0 < 2 ^ Module.finrank (ZMod 2) (LinearMap.ker A ⊓ LinearMap.ker B : Submodule (ZMod 2) (Fin n → ZMod 2)) := by
      positivity
    simp only [hcell]
    refine ⟨all h, ?_, ?_⟩
    · rw [all h, opt]; exact Nat.mul_le_mul_left _ hle
    · rw [all h, opt, Nat.mul_left_cancel_iff hpos]; exact hiff
  · obtain ⟨L, hL⟩ := PEqualNP.Outside.L_pcx_249.exists_L n c (LinearMap.ker A ⊔ LinearMap.ker B)
    refine ⟨L, ?_⟩
    obtain ⟨hle, hiff⟩ := PEqualNP.Outside.L_pcx_249.bound n c (LinearMap.ker A ⊔ LinearMap.ker B) L
    rw [all L, opt, hiff.2 hL]

import PEqualNP.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace PEqualNP.Outside.L_gct_282_aux

noncomputable section

lemma zeta_pow_mod {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ζ ^ n = ζ ^ (n % 5) := by
  have hdiv : n = 5 * (n / 5) + n % 5 := (Nat.div_add_mod n 5).symm
  conv_lhs => rw [hdiv, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

lemma isPrimitiveRoot_pow_fin4 {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (k : Fin 4) :
    IsPrimitiveRoot (ζ ^ (k.val + 1)) 5 := by
  have hcop : Nat.Coprime (k.val + 1) 5 := by
    fin_cases k <;> decide
  exact hζ.pow_of_coprime (k.val + 1) hcop

lemma sum_pow_five_ind {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    (∑ k : Fin 5, (ζ ^ n) ^ k.val) = if n % 5 = 0 then (5 : ℂ) else 0 := by
  by_cases h0 : n % 5 = 0
  · rw [ite_eq_left_iff.mpr (fun h => absurd h0 h), zeta_pow_mod hζ n, h0, pow_zero]
    simp
  · rw [ite_eq_right_iff.mpr (fun h => absurd h h0)]
    have hne : ζ ^ n ≠ 1 := by
      rw [zeta_pow_mod hζ n]
      exact hζ.pow_ne_one_of_pos_of_lt h0 (Nat.mod_lt n (by decide))
    have h5 : (ζ ^ n) ^ 5 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hfac : (ζ ^ n - 1) * (∑ k : Fin 5, (ζ ^ n) ^ k.val) = 0 := by
      rw [Fin.sum_univ_five]
      have hring : (ζ ^ n - 1) *
          ((ζ ^ n) ^ (0 : Fin 5).val + (ζ ^ n) ^ (1 : Fin 5).val + (ζ ^ n) ^ (2 : Fin 5).val +
           (ζ ^ n) ^ (3 : Fin 5).val + (ζ ^ n) ^ (4 : Fin 5).val) = (ζ ^ n) ^ 5 - 1 := by
        change (ζ ^ n - 1) *
          ((ζ ^ n) ^ 0 + (ζ ^ n) ^ 1 + (ζ ^ n) ^ 2 + (ζ ^ n) ^ 3 + (ζ ^ n) ^ 4) = (ζ ^ n) ^ 5 - 1
        ring
      rw [hring, h5, sub_self]
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)

def mulPerm (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) : Equiv.Perm (Fin 5) :=
  let inv : ℕ := if k = 1 then 1 else if k = 2 then 3 else if k = 3 then 2 else 4
  { toFun := fun a => ⟨(k * a.val) % 5, Nat.mod_lt _ (by decide)⟩
    invFun := fun a => ⟨(inv * a.val) % 5, Nat.mod_lt _ (by decide)⟩
    left_inv := fun a => by
      ext
      rcases hk with rfl | rfl | rfl | rfl <;>
        (dsimp [inv]; have ha := a.isLt; omega)
    right_inv := fun a => by
      ext
      rcases hk with rfl | rfl | rfl | rfl <;>
        (dsimp [inv]; have ha := a.isLt; omega) }

lemma perm_to_emb_bijective :
    Function.Bijective (fun σ : Equiv.Perm (Fin 5) => Fin.castSuccEmb.trans σ.toEmbedding) := by
  constructor
  · intro σ₁ σ₂ hEq
    have h4 : ∀ i : Fin 4, σ₁ i.castSucc = σ₂ i.castSucc := fun i =>
      congrFun (congrArg DFunLike.coe hEq) i
    have h4eq : σ₁ 4 = σ₂ 4 := by
      by_contra hne
      rcases σ₂.surjective (σ₁ 4) with ⟨y, hy⟩
      by_cases hy4 : y.val < 4
      · have hyeq : y = (⟨y.val, hy4⟩ : Fin 4).castSucc := by ext; rfl
        rw [hyeq, ← h4] at hy
        have hEq4 : (⟨y.val, hy4⟩ : Fin 4).castSucc = 4 := σ₁.injective hy
        have : y.val = 4 := congrArg Fin.val hEq4
        omega
      · have : y = 4 := by ext; have := y.isLt; omega
        rw [this] at hy
        exact hne hy.symm
    ext x
    by_cases hx : x.val < 4
    · have hxeq : x = (⟨x.val, hx⟩ : Fin 4).castSucc := by ext; rfl
      rw [hxeq, h4]
    · have hx4 : x = 4 := by ext; have := x.isLt; omega
      rw [hx4, h4eq]
  · intro f
    let S : Finset (Fin 5) := Finset.univ \ Finset.univ.image f
    have hScard : S.card = 1 := by
      dsimp [S]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Finset.card_image_of_injective _ f.injective, Finset.card_univ,
        Fintype.card_fin, Fintype.card_fin]
    rcases Finset.card_eq_one.mp hScard with ⟨m, hm⟩
    have hmS : m ∈ S := by rw [hm]; exact Finset.mem_singleton_self m
    have hmNot : ∀ i : Fin 4, f i ≠ m := by
      intro i hi
      have hmem : m ∈ Finset.univ.image f := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
      exact (Finset.mem_sdiff.mp hmS).2 hmem
    let g : Fin 5 → Fin 5 := fun x => if h : x.val < 4 then f ⟨x.val, h⟩ else m
    have hginj : Function.Injective g := by
      intro x₁ x₂ hEq
      dsimp [g] at hEq
      split_ifs at hEq with h₁ h₂ h₂
      · exact Fin.ext (congrArg (fun a : Fin 4 => a.val) (f.injective hEq))
      · exact absurd hEq (hmNot _)
      · exact absurd hEq.symm (hmNot _)
      · ext; have := x₁.isLt; have := x₂.isLt; omega
    let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hginj)
    refine ⟨σ, ?_⟩
    apply DFunLike.ext; intro i
    show g i.castSucc = f i
    dsimp [g]
    exact ite_eq_left_iff.mpr (fun h => absurd i.isLt h)

def permEquivEmb : Equiv.Perm (Fin 5) ≃ (Fin 4 ↪ Fin 5) :=
  Equiv.ofBijective _ perm_to_emb_bijective

def embPrecomp (τ : Equiv.Perm (Fin 4)) : (Fin 4 ↪ Fin 5) ≃ (Fin 4 ↪ Fin 5) :=
  { toFun := fun f => τ.toEmbedding.trans f
    invFun := fun f => τ.symm.toEmbedding.trans f
    left_inv := fun f => by apply DFunLike.ext; intro i; simp
    right_inv := fun f => by apply DFunLike.ext; intro i; simp }

lemma sum_emb_comp (τ : Equiv.Perm (Fin 4)) (g : (Fin 4 ↪ Fin 5) → ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, g (τ.toEmbedding.trans f)) = ∑ f : Fin 4 ↪ Fin 5, g f :=
  Fintype.sum_equiv (embPrecomp τ) _ _ (fun _ => rfl)

lemma sum_emb_eq_sum_perm (g : (Fin 4 ↪ Fin 5) → ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, g f) =
      ∑ σ : Equiv.Perm (Fin 5), g (Fin.castSuccEmb.trans σ.toEmbedding) :=
  (Fintype.sum_equiv permEquivEmb _ _ (fun _ => rfl)).symm

lemma card_perm_five : (Fintype.card (Equiv.Perm (Fin 5)) : ℂ) = 120 := by
  rw [Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]

lemma shift_sum_zero {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (w : Fin 4 → ℕ)
    (hnd : (∑ i : Fin 4, w i) % 5 ≠ 0) :
    (∑ f : Fin 4 ↪ Fin 5, ζ ^ (∑ i : Fin 4, w i * (f i).val)) = 0 := by
  let shift5 : Equiv.Perm (Fin 5) :=
    { toFun := fun a => ⟨(a.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
      invFun := fun a => ⟨(a.val + 4) % 5, Nat.mod_lt _ (by decide)⟩
      left_inv := fun a => by ext; dsimp; have := a.isLt; omega
      right_inv := fun a => by ext; dsimp; have := a.isLt; omega }
  let τ : (Fin 4 ↪ Fin 5) ≃ (Fin 4 ↪ Fin 5) :=
    { toFun := fun f => f.trans shift5.toEmbedding
      invFun := fun f => f.trans shift5.symm.toEmbedding
      left_inv := fun f => by apply DFunLike.ext; intro i; exact shift5.left_inv (f i)
      right_inv := fun f => by apply DFunLike.ext; intro i; exact shift5.right_inv (f i) }
  have hshift : ∀ f : Fin 4 ↪ Fin 5,
      ζ ^ (∑ i : Fin 4, w i * (τ f i).val) =
        ζ ^ (∑ i : Fin 4, w i) * ζ ^ (∑ i : Fin 4, w i * (f i).val) := by
    intro f
    rw [← pow_add, zeta_pow_mod hζ, zeta_pow_mod hζ (n := _ + _)]
    congr 1
    have h1 : ∀ i : Fin 4, (w i * (τ f i).val) % 5 = (w i + w i * (f i).val) % 5 := by
      intro i
      have hsi : (τ f i).val = ((f i).val + 1) % 5 := rfl
      rw [hsi, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      have : w i * ((f i).val + 1) = w i + w i * (f i).val := by ring
      rw [this]
    rw [Finset.sum_nat_mod, Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.sum_nat_mod,
      Finset.sum_add_distrib]
  have hinv : (∑ f : Fin 4 ↪ Fin 5, ζ ^ (∑ i : Fin 4, w i * (f i).val)) =
      ζ ^ (∑ i : Fin 4, w i) * (∑ f : Fin 4 ↪ Fin 5, ζ ^ (∑ i : Fin 4, w i * (f i).val)) := by
    calc (∑ f : Fin 4 ↪ Fin 5, ζ ^ (∑ i : Fin 4, w i * (f i).val))
        = ∑ f : Fin 4 ↪ Fin 5, ζ ^ (∑ i : Fin 4, w i * (τ f i).val) :=
          (Fintype.sum_equiv τ _ _ (fun _ => rfl)).symm
      _ = ∑ f : Fin 4 ↪ Fin 5, ζ ^ (∑ i : Fin 4, w i) * ζ ^ (∑ i : Fin 4, w i * (f i).val) :=
          Finset.sum_congr rfl (fun f _ => hshift f)
      _ = ζ ^ (∑ i : Fin 4, w i) * (∑ f : Fin 4 ↪ Fin 5, ζ ^ (∑ i : Fin 4, w i * (f i).val)) := by
          rw [← Finset.mul_sum]
  have hne : ζ ^ (∑ i : Fin 4, w i) ≠ 1 := by
    rw [zeta_pow_mod hζ]
    exact hζ.pow_ne_one_of_pos_of_lt hnd (Nat.mod_lt _ (by decide))
  have h0 : (1 - ζ ^ (∑ i : Fin 4, w i)) *
      (∑ f : Fin 4 ↪ Fin 5, ζ ^ (∑ i : Fin 4, w i * (f i).val)) = 0 := by
    linear_combination hinv
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hne))

lemma shift_zero_single {ω : ℂ} (hω : IsPrimitiveRoot ω 5) (a0 a1 a2 a3 : ℕ)
    (hnd : (a0 + a1 + a2 + a3) % 5 ≠ 0) :
    (∑ f : Fin 4 ↪ Fin 5,
      ω ^ (a0 * (f 0).val + a1 * (f 1).val + a2 * (f 2).val + a3 * (f 3).val)) = 0 := by
  let w : Fin 4 → ℕ := ![a0, a1, a2, a3]
  have hsum : (∑ i : Fin 4, w i) = a0 + a1 + a2 + a3 := by
    rw [Fin.sum_univ_four]; rfl
  have hwf : ∀ f : Fin 4 ↪ Fin 5,
      (∑ i : Fin 4, w i * (f i).val) =
        a0 * (f 0).val + a1 * (f 1).val + a2 * (f 2).val + a3 * (f 3).val := by
    intro f; rw [Fin.sum_univ_four]; rfl
  have h0 := shift_sum_zero hω w (by rw [hsum]; exact hnd)
  simp_rw [hwf] at h0
  exact h0

lemma four_mul_sumW {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (w : Fin 4 → ℕ) :
    120 + 4 * (∑ f : Fin 4 ↪ Fin 5, ζ ^ (∑ i : Fin 4, w i * (f i).val)) =
      5 * (∑ σ : Equiv.Perm (Fin 5),
        if (∑ i : Fin 4, w i * (σ i.castSucc).val) % 5 = 0 then (1 : ℂ) else 0) := by
  rw [sum_emb_eq_sum_perm]
  let E : Equiv.Perm (Fin 5) → ℕ := fun σ => ∑ i : Fin 4, w i * (σ i.castSucc).val
  let S : ℂ := ∑ σ : Equiv.Perm (Fin 5), ζ ^ (E σ)
  have hscale : ∀ (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4),
      (∑ σ : Equiv.Perm (Fin 5), (ζ ^ (E σ)) ^ k) = S := by
    intro k hk
    let mP := mulPerm k hk
    let e : Equiv.Perm (Fin 5) ≃ Equiv.Perm (Fin 5) := Equiv.mulLeft mP
    calc (∑ σ : Equiv.Perm (Fin 5), (ζ ^ (E σ)) ^ k)
        = ∑ σ : Equiv.Perm (Fin 5), ζ ^ (E (e σ)) := by
          apply Finset.sum_congr rfl; intro σ _
          rw [← pow_mul, mul_comm, zeta_pow_mod hζ, zeta_pow_mod hζ (n := E (e σ))]
          congr 1
          dsimp only [E]
          have hterm : ∀ i : Fin 4,
              (w i * ((e σ) i.castSucc).val) % 5 = (k * (w i * (σ i.castSucc).val)) % 5 := by
            intro i
            have hm : ((e σ) i.castSucc).val = (k * (σ i.castSucc).val) % 5 := rfl
            rw [hm, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
            have : w i * (k * (σ i.castSucc).val) = k * (w i * (σ i.castSucc).val) := by ring
            rw [this]
          rw [Finset.sum_nat_mod, Finset.sum_congr rfl (fun i _ => hterm i),
            ← Finset.sum_nat_mod, ← Finset.mul_sum]
      _ = S := Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hdouble :
      (∑ σ : Equiv.Perm (Fin 5), ∑ k : Fin 5, (ζ ^ (E σ)) ^ k.val) = 120 + 4 * S := by
    rw [Finset.sum_comm, Fin.sum_univ_five]
    have h0 : (∑ σ : Equiv.Perm (Fin 5), (ζ ^ (E σ)) ^ (0 : Fin 5).val) = 120 := by
      simp only [Fin.val_zero, pow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one, card_perm_five]
    have h1 : (∑ σ : Equiv.Perm (Fin 5), (ζ ^ (E σ)) ^ (1 : Fin 5).val) = S :=
      hscale 1 (Or.inl rfl)
    have h2 : (∑ σ : Equiv.Perm (Fin 5), (ζ ^ (E σ)) ^ (2 : Fin 5).val) = S :=
      hscale 2 (Or.inr (Or.inl rfl))
    have h3 : (∑ σ : Equiv.Perm (Fin 5), (ζ ^ (E σ)) ^ (3 : Fin 5).val) = S :=
      hscale 3 (Or.inr (Or.inr (Or.inl rfl)))
    have h4 : (∑ σ : Equiv.Perm (Fin 5), (ζ ^ (E σ)) ^ (4 : Fin 5).val) = S :=
      hscale 4 (Or.inr (Or.inr (Or.inr rfl)))
    rw [h0, h1, h2, h3, h4]
    ring
  have hinner :
      (∑ σ : Equiv.Perm (Fin 5), ∑ k : Fin 5, (ζ ^ (E σ)) ^ k.val) =
      5 * (∑ σ : Equiv.Perm (Fin 5), if (E σ) % 5 = 0 then (1 : ℂ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro σ _
    rw [sum_pow_five_ind hζ]
    split_ifs <;> ring
  exact hdouble.symm.trans hinner

lemma sumW_pair_01 {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (∑ f : Fin 4 ↪ Fin 5, ζ ^ ((f 0).val + 4 * (f 1).val)) = -30 := by
  let w : Fin 4 → ℕ := ![1, 4, 0, 0]
  have heq : ∀ f : Fin 4 ↪ Fin 5,
      (∑ x : Fin 4, w x * (f x).val) = (f 0).val + 4 * (f 1).val := by
    intro f; rw [Fin.sum_univ_four]; dsimp [w]; ring
  have hfour := four_mul_sumW hζ w
  simp_rw [heq] at hfour
  have heq2 : ∀ σ : Equiv.Perm (Fin 5),
      (∑ x : Fin 4, w x * (σ x.castSucc).val) = (σ 0).val + 4 * (σ 1).val := by
    intro σ; rw [Fin.sum_univ_four]; dsimp [w]; change 1 * (σ 0).val + 4 * (σ 1).val + 0 * (σ 2).val + 0 * (σ 3).val = _; ring
  simp_rw [heq2] at hfour
  have hzero : ∀ σ : Equiv.Perm (Fin 5), ((σ 0).val + 4 * (σ 1).val) % 5 ≠ 0 := by
    intro σ hmod
    have hlt1 := (σ 0).isLt
    have hlt2 := (σ 1).isLt
    have hfeq : σ 0 = σ 1 := Fin.ext (by omega)
    exact (by decide : (0 : Fin 5) ≠ 1) (σ.injective hfeq)
  have hrhs : (∑ σ : Equiv.Perm (Fin 5),
      if ((σ 0).val + 4 * (σ 1).val) % 5 = 0 then (1 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro σ _
    exact ite_eq_right_iff.mpr (fun h => absurd h (hzero σ))
  rw [hrhs, mul_zero] at hfour
  linear_combination hfour / 4

lemma sumW_quartic_0 {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (∑ f : Fin 4 ↪ Fin 5, ζ ^ (2 * (f 0).val + (f 1).val + (f 2).val + (f 3).val)) = -30 := by
  let w : Fin 4 → ℕ := ![2, 1, 1, 1]
  have heq : ∀ f : Fin 4 ↪ Fin 5,
      (∑ x : Fin 4, w x * (f x).val) = 2 * (f 0).val + (f 1).val + (f 2).val + (f 3).val := by
    intro f; rw [Fin.sum_univ_four]; dsimp [w]; ring
  have hfour := four_mul_sumW hζ w
  simp_rw [heq] at hfour
  have heq2 : ∀ σ : Equiv.Perm (Fin 5),
      (∑ x : Fin 4, w x * (σ x.castSucc).val) =
        2 * (σ 0).val + (σ 1).val + (σ 2).val + (σ 3).val := by
    intro σ; rw [Fin.sum_univ_four]; dsimp [w]
    change 2 * (σ 0).val + 1 * (σ 1).val + 1 * (σ 2).val + 1 * (σ 3).val = _
    ring
  simp_rw [heq2] at hfour
  have hzero : ∀ σ : Equiv.Perm (Fin 5),
      (2 * (σ 0).val + (σ 1).val + (σ 2).val + (σ 3).val) % 5 ≠ 0 := by
    intro σ hmod
    have htot : (σ 0).val + (σ 1).val + (σ 2).val + (σ 3).val + (σ 4).val = 10 := by
      have h5 : (∑ x : Fin 5, (σ x).val) = 10 := by
        rw [Fintype.sum_equiv σ (fun x => (σ x).val) (fun x => x.val) (fun _ => rfl)]
        decide
      rw [← h5, Fin.sum_univ_five]
    have hlt1 := (σ 0).isLt
    have hlt2 := (σ 4).isLt
    have hfeq : σ 0 = σ 4 := Fin.ext (by omega)
    exact (by decide : (0 : Fin 5) ≠ 4) (σ.injective hfeq)
  have hrhs : (∑ σ : Equiv.Perm (Fin 5),
      if (2 * (σ 0).val + (σ 1).val + (σ 2).val + (σ 3).val) % 5 = 0 then (1 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro σ _
    exact ite_eq_right_iff.mpr (fun h => absurd h (hzero σ))
  rw [hrhs, mul_zero] at hfour
  linear_combination hfour / 4

lemma sumW_cubic_012 {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (∑ f : Fin 4 ↪ Fin 5, ζ ^ ((f 0).val + (f 1).val + 3 * (f 2).val)) = 20 := by
  let w : Fin 4 → ℕ := ![1, 1, 3, 0]
  have heq : ∀ f : Fin 4 ↪ Fin 5,
      (∑ x : Fin 4, w x * (f x).val) = (f 0).val + (f 1).val + 3 * (f 2).val := by
    intro f; rw [Fin.sum_univ_four]; dsimp [w]; ring
  have hfour := four_mul_sumW hζ w
  simp_rw [heq] at hfour
  have heq2 : ∀ σ : Equiv.Perm (Fin 5),
      (∑ x : Fin 4, w x * (σ x.castSucc).val) = (σ 0).val + (σ 1).val + 3 * (σ 2).val := by
    intro σ; rw [Fin.sum_univ_four]; dsimp [w]
    change 1 * (σ 0).val + 1 * (σ 1).val + 3 * (σ 2).val + 0 * (σ 3).val = _
    ring
  simp_rw [heq2] at hfour
  let c : Equiv.Perm (Fin 5) := Equiv.swap 1 3 * Equiv.swap 3 4
  have hc0 : c 0 = 0 := by decide
  have hc2 : c 2 = 2 := by decide
  have hc1 : c 1 = 3 := by decide
  have hc3 : c 3 = 4 := by decide
  let P : Equiv.Perm (Fin 5) → ℂ := fun σ =>
    if ((σ 0).val + (σ 1).val + 3 * (σ 2).val) % 5 = 0 then 1 else 0
  have htriple : ∀ σ : Equiv.Perm (Fin 5), P σ + P (σ * c) + P (σ * (c * c)) = 1 := by
    intro σ
    have h10 : (σ * c) 0 = σ 0 := by simp [Equiv.Perm.mul_apply, hc0]
    have h12 : (σ * c) 2 = σ 2 := by simp [Equiv.Perm.mul_apply, hc2]
    have h11 : (σ * c) 1 = σ 3 := by simp [Equiv.Perm.mul_apply, hc1]
    have h20 : (σ * (c * c)) 0 = σ 0 := by simp [Equiv.Perm.mul_apply, hc0]
    have h22 : (σ * (c * c)) 2 = σ 2 := by simp [Equiv.Perm.mul_apply, hc2]
    have h21 : (σ * (c * c)) 1 = σ 4 := by simp [Equiv.Perm.mul_apply, hc1, hc3]
    dsimp only [P]
    rw [h10, h12, h11, h20, h22, h21]
    have hiff : ∀ y : Fin 5,
        ((σ 0).val + y.val + 3 * (σ 2).val) % 5 = 0 ↔
          y = ⟨(2 * (σ 2).val + 4 * (σ 0).val) % 5, Nat.mod_lt _ (by decide)⟩ := by
      intro y
      have h0 := (σ 0).isLt; have h2 := (σ 2).isLt; have hy := y.isLt
      constructor
      · intro h; ext; dsimp; omega
      · intro h; have hv := congrArg Fin.val h; dsimp at hv; omega
    let x : Fin 5 := ⟨(2 * (σ 2).val + 4 * (σ 0).val) % 5, Nat.mod_lt _ (by decide)⟩
    have hx0 : x ≠ σ 0 := by
      intro h
      have hv := congrArg Fin.val h
      have h0 := (σ 0).isLt; have h2 := (σ 2).isLt
      have h02 : (σ 0).val ≠ (σ 2).val := fun h' =>
        (by decide : (0 : Fin 5) ≠ 2) (σ.injective (Fin.ext h'))
      dsimp [x] at hv; omega
    have hx2 : x ≠ σ 2 := by
      intro h
      have hv := congrArg Fin.val h
      have h0 := (σ 0).isLt; have h2 := (σ 2).isLt
      have h02 : (σ 0).val ≠ (σ 2).val := fun h' =>
        (by decide : (0 : Fin 5) ≠ 2) (σ.injective (Fin.ext h'))
      dsimp [x] at hv; omega
    rcases σ.surjective x with ⟨k, hk⟩
    have h13 : σ 1 ≠ σ 3 := fun h => (by decide : (1 : Fin 5) ≠ 3) (σ.injective h)
    have h14 : σ 1 ≠ σ 4 := fun h => (by decide : (1 : Fin 5) ≠ 4) (σ.injective h)
    have h34 : σ 3 ≠ σ 4 := fun h => (by decide : (3 : Fin 5) ≠ 4) (σ.injective h)
    simp_rw [hiff]
    change (if σ 1 = x then (1 : ℂ) else 0) + (if σ 3 = x then 1 else 0) +
      (if σ 4 = x then 1 else 0) = 1
    fin_cases k
    · exact absurd hk.symm hx0
    · rw [← hk]; simp [h13.symm, h14.symm]
    · exact absurd hk.symm hx2
    · rw [← hk]; simp [h13, h34.symm]
    · rw [← hk]; simp [h14, h34]
  have hsumP : 3 * (∑ σ : Equiv.Perm (Fin 5), P σ) = 120 := by
    have h1 : (∑ σ : Equiv.Perm (Fin 5), P (σ * c)) = ∑ σ : Equiv.Perm (Fin 5), P σ :=
      Fintype.sum_equiv (Equiv.mulRight c) _ _ (fun _ => rfl)
    have h2 : (∑ σ : Equiv.Perm (Fin 5), P (σ * (c * c))) = ∑ σ : Equiv.Perm (Fin 5), P σ :=
      Fintype.sum_equiv (Equiv.mulRight (c * c)) _ _ (fun _ => rfl)
    have hsum1 : (∑ σ : Equiv.Perm (Fin 5), (P σ + P (σ * c) + P (σ * (c * c)))) = 120 := by
      simp_rw [htriple]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_perm_five]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2] at hsum1
    linear_combination hsum1
  have h40 : (∑ σ : Equiv.Perm (Fin 5), P σ) = 40 := by linear_combination hsumP / 3
  change 120 + 4 * (∑ f : Fin 4 ↪ Fin 5, ζ ^ ((f 0).val + (f 1).val + 3 * (f 2).val)) =
    5 * (∑ σ : Equiv.Perm (Fin 5), P σ) at hfour
  rw [h40] at hfour
  linear_combination hfour / 4

lemma poly4_coeffs_zero (c0 c1 c2 c3 c4 : ℂ)
    (h : ∀ t : ℂ, c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4 = 120) :
    c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (4 * h1 - 4 * hm1 - h2 / 2 + hm2 / 2) / 6
  · linear_combination (-15 * h0 + 8 * h1 + 8 * hm1 - h2 / 2 - hm2 / 2) / 12
  · linear_combination (-h1 + hm1 + h2 / 2 - hm2 / 2) / 6
  · linear_combination (3 * h0 - 2 * h1 - 2 * hm1 + h2 / 2 + hm2 / 2) / 12

lemma prod_four_poly (A B : Fin 4 → ℂ) (t : ℂ) :
    (∏ i : Fin 4, (A i + t * B i)) =
      (A 0 * A 1 * A 2 * A 3) +
      (B 0 * A 1 * A 2 * A 3 + A 0 * B 1 * A 2 * A 3 +
       A 0 * A 1 * B 2 * A 3 + A 0 * A 1 * A 2 * B 3) * t +
      (B 0 * B 1 * A 2 * A 3 + B 0 * A 1 * B 2 * A 3 + B 0 * A 1 * A 2 * B 3 +
       A 0 * B 1 * B 2 * A 3 + A 0 * B 1 * A 2 * B 3 + A 0 * A 1 * B 2 * B 3) * t ^ 2 +
      (A 0 * B 1 * B 2 * B 3 + B 0 * A 1 * B 2 * B 3 +
       B 0 * B 1 * A 2 * B 3 + B 0 * B 1 * B 2 * A 3) * t ^ 3 +
      (B 0 * B 1 * B 2 * B 3) * t ^ 4 := by
  rw [Fin.prod_univ_four]
  ring

lemma sum_two_mode_poly (ω : ℂ) (m : ℕ) (u v : Fin 4 → ℂ)
    (hconst : ∀ t : ℂ,
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + t * u i * ω ^ (f i).val + v i * ω ^ (m * (f i).val))) = 120) :
    (∑ f : Fin 4 ↪ Fin 5,
      let A := fun i => 1 + v i * ω ^ (m * (f i).val)
      let B := fun i => u i * ω ^ (f i).val
      B 0 * A 1 * A 2 * A 3 + A 0 * B 1 * A 2 * A 3 +
      A 0 * A 1 * B 2 * A 3 + A 0 * A 1 * A 2 * B 3) = 0 ∧
    (∑ f : Fin 4 ↪ Fin 5,
      let A := fun i => 1 + v i * ω ^ (m * (f i).val)
      let B := fun i => u i * ω ^ (f i).val
      B 0 * B 1 * A 2 * A 3 + B 0 * A 1 * B 2 * A 3 + B 0 * A 1 * A 2 * B 3 +
      A 0 * B 1 * B 2 * A 3 + A 0 * B 1 * A 2 * B 3 + A 0 * A 1 * B 2 * B 3) = 0 ∧
    (∑ f : Fin 4 ↪ Fin 5,
      let A := fun i => 1 + v i * ω ^ (m * (f i).val)
      let B := fun i => u i * ω ^ (f i).val
      A 0 * B 1 * B 2 * B 3 + B 0 * A 1 * B 2 * B 3 +
      B 0 * B 1 * A 2 * B 3 + B 0 * B 1 * B 2 * A 3) = 0 := by
  have hpoly : ∀ t : ℂ,
      (∑ f : Fin 4 ↪ Fin 5,
        let A := fun i => 1 + v i * ω ^ (m * (f i).val)
        A 0 * A 1 * A 2 * A 3) +
      (∑ f : Fin 4 ↪ Fin 5,
        let A := fun i => 1 + v i * ω ^ (m * (f i).val)
        let B := fun i => u i * ω ^ (f i).val
        B 0 * A 1 * A 2 * A 3 + A 0 * B 1 * A 2 * A 3 +
        A 0 * A 1 * B 2 * A 3 + A 0 * A 1 * A 2 * B 3) * t +
      (∑ f : Fin 4 ↪ Fin 5,
        let A := fun i => 1 + v i * ω ^ (m * (f i).val)
        let B := fun i => u i * ω ^ (f i).val
        B 0 * B 1 * A 2 * A 3 + B 0 * A 1 * B 2 * A 3 + B 0 * A 1 * A 2 * B 3 +
        A 0 * B 1 * B 2 * A 3 + A 0 * B 1 * A 2 * B 3 + A 0 * A 1 * B 2 * B 3) * t ^ 2 +
      (∑ f : Fin 4 ↪ Fin 5,
        let A := fun i => 1 + v i * ω ^ (m * (f i).val)
        let B := fun i => u i * ω ^ (f i).val
        A 0 * B 1 * B 2 * B 3 + B 0 * A 1 * B 2 * B 3 +
        B 0 * B 1 * A 2 * B 3 + B 0 * B 1 * B 2 * A 3) * t ^ 3 +
      (∑ f : Fin 4 ↪ Fin 5,
        let B := fun i => u i * ω ^ (f i).val
        B 0 * B 1 * B 2 * B 3) * t ^ 4 = 120 := by
    intro t
    have ht := hconst t
    have hterm : ∀ f : Fin 4 ↪ Fin 5,
        (∏ i : Fin 4, (1 + t * u i * ω ^ (f i).val + v i * ω ^ (m * (f i).val))) =
          ∏ i : Fin 4, ((1 + v i * ω ^ (m * (f i).val)) + t * (u i * ω ^ (f i).val)) := by
      intro f; apply Finset.prod_congr rfl; intro i _; ring
    simp_rw [hterm, prod_four_poly, Finset.sum_add_distrib, ← Finset.sum_mul] at ht
    exact ht
  rcases poly4_coeffs_zero _ _ _ _ _ hpoly with ⟨h1, h2, h3, _⟩
  exact ⟨h1, h2, h3⟩

lemma pair_term_0 {ω : ℂ} (hω : IsPrimitiveRoot ω 5) (u0 w1 w2 w3 : ℂ) :
    (∑ f : Fin 4 ↪ Fin 5,
      (u0 * ω ^ (f 0).val) * (1 + w1 * ω ^ (4 * (f 1).val)) *
      (1 + w2 * ω ^ (4 * (f 2).val)) * (1 + w3 * ω ^ (4 * (f 3).val))) =
    (-30 : ℂ) * (u0 * (w1 + w2 + w3)) := by
  have hexp : ∀ f : Fin 4 ↪ Fin 5,
      (u0 * ω ^ (f 0).val) * (1 + w1 * ω ^ (4 * (f 1).val)) *
      (1 + w2 * ω ^ (4 * (f 2).val)) * (1 + w3 * ω ^ (4 * (f 3).val)) =
      u0 * ω ^ (1 * (f 0).val + 0 * (f 1).val + 0 * (f 2).val + 0 * (f 3).val) +
      (u0 * w1) * ω ^ ((f 0).val + 4 * (f 1).val) +
      (u0 * w2) * ω ^ ((f 0).val + 4 * (f 2).val) +
      (u0 * w3) * ω ^ ((f 0).val + 4 * (f 3).val) +
      (u0 * w1 * w2) * ω ^ (1 * (f 0).val + 4 * (f 1).val + 4 * (f 2).val + 0 * (f 3).val) +
      (u0 * w1 * w3) * ω ^ (1 * (f 0).val + 4 * (f 1).val + 0 * (f 2).val + 4 * (f 3).val) +
      (u0 * w2 * w3) * ω ^ (1 * (f 0).val + 0 * (f 1).val + 4 * (f 2).val + 4 * (f 3).val) +
      (u0 * w1 * w2 * w3) * ω ^ (1 * (f 0).val + 4 * (f 1).val + 4 * (f 2).val + 4 * (f 3).val) := by
    intro f; simp only [one_mul, zero_mul, add_zero, pow_add]; ring
  simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hp02 : (∑ f : Fin 4 ↪ Fin 5, ω ^ ((f 0).val + 4 * (f 2).val)) = -30 := by
    rw [← sumW_pair_01 hω, ← sum_emb_comp (Equiv.swap 1 2)]
    apply Finset.sum_congr rfl; intro f _; rfl
  have hp03 : (∑ f : Fin 4 ↪ Fin 5, ω ^ ((f 0).val + 4 * (f 3).val)) = -30 := by
    rw [← sumW_pair_01 hω, ← sum_emb_comp (Equiv.swap 1 3)]
    apply Finset.sum_congr rfl; intro f _; rfl
  rw [shift_zero_single hω 1 0 0 0 (by decide),
    sumW_pair_01 hω, hp02, hp03,
    shift_zero_single hω 1 4 4 0 (by decide),
    shift_zero_single hω 1 4 0 4 (by decide),
    shift_zero_single hω 1 0 4 4 (by decide),
    shift_zero_single hω 1 4 4 4 (by decide)]
  ring

lemma extract_pair {ω : ℂ} (hω : IsPrimitiveRoot ω 5) (u w : Fin 4 → ℂ)
    (hconst : ∀ t : ℂ,
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + t * u i * ω ^ (f i).val + w i * ω ^ (4 * (f i).val))) = 120) :
    u 0 * (w 1 + w 2 + w 3) + u 1 * (w 0 + w 2 + w 3) +
    u 2 * (w 0 + w 1 + w 3) + u 3 * (w 0 + w 1 + w 2) = 0 := by
  have hc1 := (sum_two_mode_poly ω 4 u w hconst).1
  simp only [Finset.sum_add_distrib] at hc1
  have t0 := pair_term_0 hω (u 0) (w 1) (w 2) (w 3)
  have t1 : (∑ f : Fin 4 ↪ Fin 5,
      (1 + w 0 * ω ^ (4 * (f 0).val)) * (u 1 * ω ^ (f 1).val) *
      (1 + w 2 * ω ^ (4 * (f 2).val)) * (1 + w 3 * ω ^ (4 * (f 3).val))) =
      (-30 : ℂ) * (u 1 * (w 0 + w 2 + w 3)) := by
    rw [← pair_term_0 hω (u 1) (w 0) (w 2) (w 3), ← sum_emb_comp (Equiv.swap 0 1)]
    apply Finset.sum_congr rfl; intro f _
    change (1 + w 0 * ω ^ (4 * (f 1).val)) * (u 1 * ω ^ (f 0).val) *
      (1 + w 2 * ω ^ (4 * (f 2).val)) * (1 + w 3 * ω ^ (4 * (f 3).val)) = _
    ring
  have t2 : (∑ f : Fin 4 ↪ Fin 5,
      (1 + w 0 * ω ^ (4 * (f 0).val)) * (1 + w 1 * ω ^ (4 * (f 1).val)) *
      (u 2 * ω ^ (f 2).val) * (1 + w 3 * ω ^ (4 * (f 3).val))) =
      (-30 : ℂ) * (u 2 * (w 0 + w 1 + w 3)) := by
    have hrhs : (-30 : ℂ) * (u 2 * (w 0 + w 1 + w 3)) = (-30 : ℂ) * (u 2 * (w 1 + w 0 + w 3)) := by ring
    rw [hrhs, ← pair_term_0 hω (u 2) (w 1) (w 0) (w 3), ← sum_emb_comp (Equiv.swap 0 2)]
    apply Finset.sum_congr rfl; intro f _
    change (1 + w 0 * ω ^ (4 * (f 2).val)) * (1 + w 1 * ω ^ (4 * (f 1).val)) *
      (u 2 * ω ^ (f 0).val) * (1 + w 3 * ω ^ (4 * (f 3).val)) = _
    ring
  have t3 : (∑ f : Fin 4 ↪ Fin 5,
      (1 + w 0 * ω ^ (4 * (f 0).val)) * (1 + w 1 * ω ^ (4 * (f 1).val)) *
      (1 + w 2 * ω ^ (4 * (f 2).val)) * (u 3 * ω ^ (f 3).val)) =
      (-30 : ℂ) * (u 3 * (w 0 + w 1 + w 2)) := by
    have hrhs : (-30 : ℂ) * (u 3 * (w 0 + w 1 + w 2)) = (-30 : ℂ) * (u 3 * (w 1 + w 2 + w 0)) := by ring
    rw [hrhs, ← pair_term_0 hω (u 3) (w 1) (w 2) (w 0), ← sum_emb_comp (Equiv.swap 0 3)]
    apply Finset.sum_congr rfl; intro f _
    change (1 + w 0 * ω ^ (4 * (f 3).val)) * (1 + w 1 * ω ^ (4 * (f 1).val)) *
      (1 + w 2 * ω ^ (4 * (f 2).val)) * (u 3 * ω ^ (f 0).val) = _
    ring
  rw [t0, t1, t2, t3] at hc1
  linear_combination hc1 / (-30)

lemma cubic_term_01 {ω : ℂ} (hω : IsPrimitiveRoot ω 5) (u0 u1 z2 z3 : ℂ) :
    (∑ f : Fin 4 ↪ Fin 5,
      (u0 * ω ^ (f 0).val) * (u1 * ω ^ (f 1).val) *
      (1 + z2 * ω ^ (3 * (f 2).val)) * (1 + z3 * ω ^ (3 * (f 3).val))) =
    (20 : ℂ) * (u0 * u1 * (z2 + z3)) := by
  have hexp : ∀ f : Fin 4 ↪ Fin 5,
      (u0 * ω ^ (f 0).val) * (u1 * ω ^ (f 1).val) *
      (1 + z2 * ω ^ (3 * (f 2).val)) * (1 + z3 * ω ^ (3 * (f 3).val)) =
      (u0 * u1) * ω ^ (1 * (f 0).val + 1 * (f 1).val + 0 * (f 2).val + 0 * (f 3).val) +
      (u0 * u1 * z2) * ω ^ ((f 0).val + (f 1).val + 3 * (f 2).val) +
      (u0 * u1 * z3) * ω ^ ((f 0).val + (f 1).val + 3 * (f 3).val) +
      (u0 * u1 * z2 * z3) * ω ^ (1 * (f 0).val + 1 * (f 1).val + 3 * (f 2).val + 3 * (f 3).val) := by
    intro f; simp only [one_mul, zero_mul, add_zero, pow_add]; ring
  simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hc013 : (∑ f : Fin 4 ↪ Fin 5, ω ^ ((f 0).val + (f 1).val + 3 * (f 3).val)) = 20 := by
    rw [← sumW_cubic_012 hω, ← sum_emb_comp (Equiv.swap 2 3)]
    apply Finset.sum_congr rfl; intro f _; rfl
  rw [shift_zero_single hω 1 1 0 0 (by decide),
    sumW_cubic_012 hω, hc013,
    shift_zero_single hω 1 1 3 3 (by decide)]
  ring

lemma extract_cubic {ω : ℂ} (hω : IsPrimitiveRoot ω 5) (u z : Fin 4 → ℂ)
    (hconst : ∀ t : ℂ,
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + t * u i * ω ^ (f i).val + z i * ω ^ (3 * (f i).val))) = 120) :
    u 0 * u 1 * (z 2 + z 3) + u 0 * u 2 * (z 1 + z 3) + u 0 * u 3 * (z 1 + z 2) +
    u 1 * u 2 * (z 0 + z 3) + u 1 * u 3 * (z 0 + z 2) + u 2 * u 3 * (z 0 + z 1) = 0 := by
  have hc2 := (sum_two_mode_poly ω 3 u z hconst).2.1
  simp only [Finset.sum_add_distrib] at hc2
  have t01 := cubic_term_01 hω (u 0) (u 1) (z 2) (z 3)
  have t02 : (∑ f : Fin 4 ↪ Fin 5,
      (u 0 * ω ^ (f 0).val) * (1 + z 1 * ω ^ (3 * (f 1).val)) *
      (u 2 * ω ^ (f 2).val) * (1 + z 3 * ω ^ (3 * (f 3).val))) =
      (20 : ℂ) * (u 0 * u 2 * (z 1 + z 3)) := by
    rw [← cubic_term_01 hω (u 0) (u 2) (z 1) (z 3), ← sum_emb_comp (Equiv.swap 1 2)]
    apply Finset.sum_congr rfl; intro f _
    change (u 0 * ω ^ (f 0).val) * (1 + z 1 * ω ^ (3 * (f 2).val)) *
      (u 2 * ω ^ (f 1).val) * (1 + z 3 * ω ^ (3 * (f 3).val)) = _
    ring
  have t03 : (∑ f : Fin 4 ↪ Fin 5,
      (u 0 * ω ^ (f 0).val) * (1 + z 1 * ω ^ (3 * (f 1).val)) *
      (1 + z 2 * ω ^ (3 * (f 2).val)) * (u 3 * ω ^ (f 3).val)) =
      (20 : ℂ) * (u 0 * u 3 * (z 1 + z 2)) := by
    have hrhs : (20 : ℂ) * (u 0 * u 3 * (z 1 + z 2)) = (20 : ℂ) * (u 0 * u 3 * (z 2 + z 1)) := by ring
    rw [hrhs, ← cubic_term_01 hω (u 0) (u 3) (z 2) (z 1), ← sum_emb_comp (Equiv.swap 1 3)]
    apply Finset.sum_congr rfl; intro f _
    change (u 0 * ω ^ (f 0).val) * (1 + z 1 * ω ^ (3 * (f 3).val)) *
      (1 + z 2 * ω ^ (3 * (f 2).val)) * (u 3 * ω ^ (f 1).val) = _
    ring
  have t12 : (∑ f : Fin 4 ↪ Fin 5,
      (1 + z 0 * ω ^ (3 * (f 0).val)) * (u 1 * ω ^ (f 1).val) *
      (u 2 * ω ^ (f 2).val) * (1 + z 3 * ω ^ (3 * (f 3).val))) =
      (20 : ℂ) * (u 1 * u 2 * (z 0 + z 3)) := by
    have hrhs : (20 : ℂ) * (u 1 * u 2 * (z 0 + z 3)) = (20 : ℂ) * (u 2 * u 1 * (z 0 + z 3)) := by ring
    rw [hrhs, ← cubic_term_01 hω (u 2) (u 1) (z 0) (z 3), ← sum_emb_comp (Equiv.swap 0 2)]
    apply Finset.sum_congr rfl; intro f _
    change (1 + z 0 * ω ^ (3 * (f 2).val)) * (u 1 * ω ^ (f 1).val) *
      (u 2 * ω ^ (f 0).val) * (1 + z 3 * ω ^ (3 * (f 3).val)) = _
    ring
  have t13 : (∑ f : Fin 4 ↪ Fin 5,
      (1 + z 0 * ω ^ (3 * (f 0).val)) * (u 1 * ω ^ (f 1).val) *
      (1 + z 2 * ω ^ (3 * (f 2).val)) * (u 3 * ω ^ (f 3).val)) =
      (20 : ℂ) * (u 1 * u 3 * (z 0 + z 2)) := by
    have hrhs : (20 : ℂ) * (u 1 * u 3 * (z 0 + z 2)) = (20 : ℂ) * (u 3 * u 1 * (z 2 + z 0)) := by ring
    rw [hrhs, ← cubic_term_01 hω (u 3) (u 1) (z 2) (z 0), ← sum_emb_comp (Equiv.swap 0 3)]
    apply Finset.sum_congr rfl; intro f _
    change (1 + z 0 * ω ^ (3 * (f 3).val)) * (u 1 * ω ^ (f 1).val) *
      (1 + z 2 * ω ^ (3 * (f 2).val)) * (u 3 * ω ^ (f 0).val) = _
    ring
  have t23 : (∑ f : Fin 4 ↪ Fin 5,
      (1 + z 0 * ω ^ (3 * (f 0).val)) * (1 + z 1 * ω ^ (3 * (f 1).val)) *
      (u 2 * ω ^ (f 2).val) * (u 3 * ω ^ (f 3).val)) =
      (20 : ℂ) * (u 2 * u 3 * (z 0 + z 1)) := by
    rw [← cubic_term_01 hω (u 2) (u 3) (z 0) (z 1),
      ← sum_emb_comp (Equiv.swap 0 2 * Equiv.swap 1 3)]
    apply Finset.sum_congr rfl; intro f _
    change (1 + z 0 * ω ^ (3 * (f 2).val)) * (1 + z 1 * ω ^ (3 * (f 3).val)) *
      (u 2 * ω ^ (f 0).val) * (u 3 * ω ^ (f 1).val) = _
    ring
  rw [t01, t02, t03, t12, t13, t23] at hc2
  linear_combination hc2 / 20

lemma quartic_term_0 {ω : ℂ} (hω : IsPrimitiveRoot ω 5) (y0 u1 u2 u3 : ℂ) :
    (∑ f : Fin 4 ↪ Fin 5,
      (1 + y0 * ω ^ (2 * (f 0).val)) * (u1 * ω ^ (f 1).val) *
      (u2 * ω ^ (f 2).val) * (u3 * ω ^ (f 3).val)) =
    (-30 : ℂ) * (y0 * u1 * u2 * u3) := by
  have hexp : ∀ f : Fin 4 ↪ Fin 5,
      (1 + y0 * ω ^ (2 * (f 0).val)) * (u1 * ω ^ (f 1).val) *
      (u2 * ω ^ (f 2).val) * (u3 * ω ^ (f 3).val) =
      (u1 * u2 * u3) * ω ^ (0 * (f 0).val + 1 * (f 1).val + 1 * (f 2).val + 1 * (f 3).val) +
      (y0 * u1 * u2 * u3) * ω ^ (2 * (f 0).val + (f 1).val + (f 2).val + (f 3).val) := by
    intro f; simp only [one_mul, zero_mul, zero_add, pow_add]; ring
  simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [shift_zero_single hω 0 1 1 1 (by decide), sumW_quartic_0 hω]
  ring

lemma extract_quartic {ω : ℂ} (hω : IsPrimitiveRoot ω 5) (u y : Fin 4 → ℂ)
    (hconst : ∀ t : ℂ,
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + t * u i * ω ^ (f i).val + y i * ω ^ (2 * (f i).val))) = 120) :
    y 0 * u 1 * u 2 * u 3 + y 1 * u 0 * u 2 * u 3 +
    y 2 * u 0 * u 1 * u 3 + y 3 * u 0 * u 1 * u 2 = 0 := by
  have hc3 := (sum_two_mode_poly ω 2 u y hconst).2.2
  simp only [Finset.sum_add_distrib] at hc3
  have t0 := quartic_term_0 hω (y 0) (u 1) (u 2) (u 3)
  have t1 : (∑ f : Fin 4 ↪ Fin 5,
      (u 0 * ω ^ (f 0).val) * (1 + y 1 * ω ^ (2 * (f 1).val)) *
      (u 2 * ω ^ (f 2).val) * (u 3 * ω ^ (f 3).val)) =
      (-30 : ℂ) * (y 1 * u 0 * u 2 * u 3) := by
    rw [← quartic_term_0 hω (y 1) (u 0) (u 2) (u 3), ← sum_emb_comp (Equiv.swap 0 1)]
    apply Finset.sum_congr rfl; intro f _
    change (u 0 * ω ^ (f 1).val) * (1 + y 1 * ω ^ (2 * (f 0).val)) *
      (u 2 * ω ^ (f 2).val) * (u 3 * ω ^ (f 3).val) = _
    ring
  have t2 : (∑ f : Fin 4 ↪ Fin 5,
      (u 0 * ω ^ (f 0).val) * (u 1 * ω ^ (f 1).val) *
      (1 + y 2 * ω ^ (2 * (f 2).val)) * (u 3 * ω ^ (f 3).val)) =
      (-30 : ℂ) * (y 2 * u 0 * u 1 * u 3) := by
    have hrhs : (-30 : ℂ) * (y 2 * u 0 * u 1 * u 3) = (-30 : ℂ) * (y 2 * u 1 * u 0 * u 3) := by ring
    rw [hrhs, ← quartic_term_0 hω (y 2) (u 1) (u 0) (u 3), ← sum_emb_comp (Equiv.swap 0 2)]
    apply Finset.sum_congr rfl; intro f _
    change (u 0 * ω ^ (f 2).val) * (u 1 * ω ^ (f 1).val) *
      (1 + y 2 * ω ^ (2 * (f 0).val)) * (u 3 * ω ^ (f 3).val) = _
    ring
  have t3 : (∑ f : Fin 4 ↪ Fin 5,
      (u 0 * ω ^ (f 0).val) * (u 1 * ω ^ (f 1).val) *
      (u 2 * ω ^ (f 2).val) * (1 + y 3 * ω ^ (2 * (f 3).val))) =
      (-30 : ℂ) * (y 3 * u 0 * u 1 * u 2) := by
    have hrhs : (-30 : ℂ) * (y 3 * u 0 * u 1 * u 2) = (-30 : ℂ) * (y 3 * u 1 * u 2 * u 0) := by ring
    rw [hrhs, ← quartic_term_0 hω (y 3) (u 1) (u 2) (u 0), ← sum_emb_comp (Equiv.swap 0 3)]
    apply Finset.sum_congr rfl; intro f _
    change (u 0 * ω ^ (f 3).val) * (u 1 * ω ^ (f 1).val) *
      (u 2 * ω ^ (f 2).val) * (1 + y 3 * ω ^ (2 * (f 0).val)) = _
    ring
  rw [t0, t1, t2, t3] at hc3
  linear_combination hc3 / (-30)

def H1 (v : Fin 4 → ℂ) : ℂ := v 0 + v 1 - v 2 - v 3
def H2 (v : Fin 4 → ℂ) : ℂ := v 0 - v 1 + v 2 - v 3
def H3 (v : Fin 4 → ℂ) : ℂ := v 0 - v 1 - v 2 + v 3

lemma H_eq_zero_iff (v : Fin 4 → ℂ) (hs : (∑ i : Fin 4, v i) = 0) :
    (H1 v = 0 ∧ H2 v = 0 ∧ H3 v = 0) ↔ v = 0 := by
  rw [Fin.sum_univ_four] at hs
  constructor
  · rintro ⟨h1, h2, h3⟩
    unfold H1 at h1
    unfold H2 at h2
    unfold H3 at h3
    ext i; fin_cases i
    · change v 0 = 0; linear_combination (hs + h1 + h2 + h3) / 4
    · change v 1 = 0; linear_combination (hs + h1 - h2 - h3) / 4
    · change v 2 = 0; linear_combination (hs - h1 + h2 - h3) / 4
    · change v 3 = 0; linear_combination (hs - h1 - h2 + h3) / 4
  · intro hv; subst hv; simp [H1, H2, H3]

lemma H_pair_eq (u w : Fin 4 → ℂ) (hu : (∑ i : Fin 4, u i) = 0) :
    4 * (u 0 * (w 1 + w 2 + w 3) + u 1 * (w 0 + w 2 + w 3) +
         u 2 * (w 0 + w 1 + w 3) + u 3 * (w 0 + w 1 + w 2)) =
      -(H1 u * H1 w + H2 u * H2 w + H3 u * H3 w) := by
  rw [Fin.sum_univ_four] at hu
  unfold H1 H2 H3
  linear_combination 3 * (w 0 + w 1 + w 2 + w 3) * hu

lemma H_cubic_eq (u z : Fin 4 → ℂ) (hu : (∑ i : Fin 4, u i) = 0) (hz : (∑ i : Fin 4, z i) = 0) :
    8 * (u 0 * u 1 * (z 2 + z 3) + u 0 * u 2 * (z 1 + z 3) + u 0 * u 3 * (z 1 + z 2) +
         u 1 * u 2 * (z 0 + z 3) + u 1 * u 3 * (z 0 + z 2) + u 2 * u 3 * (z 0 + z 1)) =
      H1 z * H2 u * H3 u + H2 z * H1 u * H3 u + H3 z * H1 u * H2 u := by
  rw [Fin.sum_univ_four] at hu hz
  have hu0 : 4 * u 0 = H1 u + H2 u + H3 u := by unfold H1 H2 H3; linear_combination hu
  have hu1 : 4 * u 1 = H1 u - H2 u - H3 u := by unfold H1 H2 H3; linear_combination hu
  have hu2 : 4 * u 2 = -H1 u + H2 u - H3 u := by unfold H1 H2 H3; linear_combination hu
  have hu3 : 4 * u 3 = -H1 u - H2 u + H3 u := by unfold H1 H2 H3; linear_combination hu
  have hz0 : 4 * z 0 = H1 z + H2 z + H3 z := by unfold H1 H2 H3; linear_combination hz
  have hz1 : 4 * z 1 = H1 z - H2 z - H3 z := by unfold H1 H2 H3; linear_combination hz
  have hz2 : 4 * z 2 = -H1 z + H2 z - H3 z := by unfold H1 H2 H3; linear_combination hz
  have hz3 : 4 * z 3 = -H1 z - H2 z + H3 z := by unfold H1 H2 H3; linear_combination hz
  have hmul : 64 * (8 * (u 0 * u 1 * (z 2 + z 3) + u 0 * u 2 * (z 1 + z 3) +
      u 0 * u 3 * (z 1 + z 2) + u 1 * u 2 * (z 0 + z 3) +
      u 1 * u 3 * (z 0 + z 2) + u 2 * u 3 * (z 0 + z 1))) =
      64 * (H1 z * H2 u * H3 u + H2 z * H1 u * H3 u + H3 z * H1 u * H2 u) := by
    have hrew : 64 * (8 * (u 0 * u 1 * (z 2 + z 3) + u 0 * u 2 * (z 1 + z 3) +
        u 0 * u 3 * (z 1 + z 2) + u 1 * u 2 * (z 0 + z 3) +
        u 1 * u 3 * (z 0 + z 2) + u 2 * u 3 * (z 0 + z 1))) =
        8 * ((4 * u 0) * (4 * u 1) * ((4 * z 2) + (4 * z 3)) +
             (4 * u 0) * (4 * u 2) * ((4 * z 1) + (4 * z 3)) +
             (4 * u 0) * (4 * u 3) * ((4 * z 1) + (4 * z 2)) +
             (4 * u 1) * (4 * u 2) * ((4 * z 0) + (4 * z 3)) +
             (4 * u 1) * (4 * u 3) * ((4 * z 0) + (4 * z 2)) +
             (4 * u 2) * (4 * u 3) * ((4 * z 0) + (4 * z 1))) := by ring
    rw [hrew, hu0, hu1, hu2, hu3, hz0, hz1, hz2, hz3]
    ring
  linear_combination hmul / 64

lemma H_quartic_eq (u y : Fin 4 → ℂ) (hu : (∑ i : Fin 4, u i) = 0) (hy : (∑ i : Fin 4, y i) = 0) :
    64 * (y 0 * u 1 * u 2 * u 3 + y 1 * u 0 * u 2 * u 3 +
          y 2 * u 0 * u 1 * u 3 + y 3 * u 0 * u 1 * u 2) =
      H1 y * H1 u * (2 * H1 u ^ 2 - (H1 u ^ 2 + H2 u ^ 2 + H3 u ^ 2)) +
      H2 y * H2 u * (2 * H2 u ^ 2 - (H1 u ^ 2 + H2 u ^ 2 + H3 u ^ 2)) +
      H3 y * H3 u * (2 * H3 u ^ 2 - (H1 u ^ 2 + H2 u ^ 2 + H3 u ^ 2)) := by
  rw [Fin.sum_univ_four] at hu hy
  have hu0 : 4 * u 0 = H1 u + H2 u + H3 u := by unfold H1 H2 H3; linear_combination hu
  have hu1 : 4 * u 1 = H1 u - H2 u - H3 u := by unfold H1 H2 H3; linear_combination hu
  have hu2 : 4 * u 2 = -H1 u + H2 u - H3 u := by unfold H1 H2 H3; linear_combination hu
  have hu3 : 4 * u 3 = -H1 u - H2 u + H3 u := by unfold H1 H2 H3; linear_combination hu
  have hy0 : 4 * y 0 = H1 y + H2 y + H3 y := by unfold H1 H2 H3; linear_combination hy
  have hy1 : 4 * y 1 = H1 y - H2 y - H3 y := by unfold H1 H2 H3; linear_combination hy
  have hy2 : 4 * y 2 = -H1 y + H2 y - H3 y := by unfold H1 H2 H3; linear_combination hy
  have hy3 : 4 * y 3 = -H1 y - H2 y + H3 y := by unfold H1 H2 H3; linear_combination hy
  have hmul : 4 * (64 * (y 0 * u 1 * u 2 * u 3 + y 1 * u 0 * u 2 * u 3 +
      y 2 * u 0 * u 1 * u 3 + y 3 * u 0 * u 1 * u 2)) =
      4 * (H1 y * H1 u * (2 * H1 u ^ 2 - (H1 u ^ 2 + H2 u ^ 2 + H3 u ^ 2)) +
           H2 y * H2 u * (2 * H2 u ^ 2 - (H1 u ^ 2 + H2 u ^ 2 + H3 u ^ 2)) +
           H3 y * H3 u * (2 * H3 u ^ 2 - (H1 u ^ 2 + H2 u ^ 2 + H3 u ^ 2))) := by
    have hrew : 4 * (64 * (y 0 * u 1 * u 2 * u 3 + y 1 * u 0 * u 2 * u 3 +
        y 2 * u 0 * u 1 * u 3 + y 3 * u 0 * u 1 * u 2)) =
        (4 * y 0) * (4 * u 1) * (4 * u 2) * (4 * u 3) +
        (4 * y 1) * (4 * u 0) * (4 * u 2) * (4 * u 3) +
        (4 * y 2) * (4 * u 0) * (4 * u 1) * (4 * u 3) +
        (4 * y 3) * (4 * u 0) * (4 * u 1) * (4 * u 2) := by ring
    rw [hrew, hu0, hu1, hu2, hu3, hy0, hy1, hy2, hy3]
    ring
  linear_combination hmul / 4

lemma plane_contradiction_core (s t y1 y2 y3 z1 z2 z3 : ℂ)
    (hy_ne : ¬(y1 = 0 ∧ y2 = 0 ∧ y3 = 0))
    (hz_ne : ¬(z1 = 0 ∧ z2 = 0 ∧ z3 = 0))
    (hyz : y1 * z1 + y2 * z2 + y3 * z3 = 0)
    (hcubic : ∀ a b : ℂ,
      z1 * b * (s * a + t * b) + z2 * a * (s * a + t * b) + z3 * a * b = 0)
    (hquart1 : ∀ a b : ℂ,
      y1 * a * (2 * a ^ 2 - (a ^ 2 + b ^ 2 + (s * a + t * b) ^ 2)) +
      y2 * b * (2 * b ^ 2 - (a ^ 2 + b ^ 2 + (s * a + t * b) ^ 2)) +
      y3 * (s * a + t * b) * (2 * (s * a + t * b) ^ 2 - (a ^ 2 + b ^ 2 + (s * a + t * b) ^ 2)) = 0)
    (hquart2 :
      (-s) * y1 * (2 * y1 ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)) +
      (-t) * y2 * (2 * y2 ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)) +
      1 * y3 * (2 * y3 ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)) = 0) : False := by
  have hc_a2 : s * z2 = 0 := by
    have h := hcubic 1 0; linear_combination h
  have hc_b2 : t * z1 = 0 := by
    have h := hcubic 0 1; linear_combination h
  have hc_ab : s * z1 + t * z2 + z3 = 0 := by
    have h11 := hcubic 1 1
    have h10 := hcubic 1 0
    have h01 := hcubic 0 1
    linear_combination h11 - h10 - h01
  by_cases hst : s ≠ 0 ∧ t ≠ 0
  · have hz2 : z2 = 0 := (mul_eq_zero.mp hc_a2).resolve_left hst.1
    have hz1 : z1 = 0 := (mul_eq_zero.mp hc_b2).resolve_left hst.2
    have hz3 : z3 = 0 := by rw [hz1, hz2] at hc_ab; linear_combination hc_ab
    exact hz_ne ⟨hz1, hz2, hz3⟩
  · have hstep : ∀ (t' y1' y2' y3' z1' z2' z3' : ℂ),
        ¬(y1' = 0 ∧ y2' = 0 ∧ y3' = 0) →
        ¬(z1' = 0 ∧ z2' = 0 ∧ z3' = 0) →
        y1' * z1' + y2' * z2' + y3' * z3' = 0 →
        t' * z1' = 0 →
        t' * z2' + z3' = 0 →
        (∀ a b : ℂ,
          y1' * a * (2 * a ^ 2 - (a ^ 2 + b ^ 2 + (t' * b) ^ 2)) +
          y2' * b * (2 * b ^ 2 - (a ^ 2 + b ^ 2 + (t' * b) ^ 2)) +
          y3' * (t' * b) * (2 * (t' * b) ^ 2 - (a ^ 2 + b ^ 2 + (t' * b) ^ 2)) = 0) →
        ((-t') * y2' * (2 * y2' ^ 2 - (y1' ^ 2 + y2' ^ 2 + y3' ^ 2)) +
         1 * y3' * (2 * y3' ^ 2 - (y1' ^ 2 + y2' ^ 2 + y3' ^ 2)) = 0) →
        False := by
      intro t' y1' y2' y3' z1' z2' z3' hy' hz' hyz' htz1 htz23 hq1' hq2'
      have hy1 : y1' = 0 := by
        have h := hq1' 1 0; linear_combination h
      have hy23 : y2' + t' * y3' = 0 := by
        have h11 := hq1' 1 1
        have hm11 := hq1' (-1) 1
        have h01 := hq1' 0 1
        rw [hy1] at h11 hm11 h01
        linear_combination -(h11 + hm11 - 2 * h01) / 2
      by_cases ht0 : t' = 0
      · subst ht0
        have hy2 : y2' = 0 := by linear_combination hy23
        rw [hy1, hy2] at hq2'
        have hy3_3 : y3' ^ 3 = 0 := by linear_combination hq2'
        have hy3 : y3' = 0 := by
          rcases mul_eq_zero.mp (show y3' * (y3' * y3') = 0 by linear_combination hy3_3) with h | h
          · exact h
          · exact (mul_eq_zero.mp h).elim id id
        exact hy' ⟨hy1, hy2, hy3⟩
      · have hz1 : z1' = 0 := (mul_eq_zero.mp htz1).resolve_left ht0
        have hprod : (-2 * t') * (y3' * z2') = 0 := by
          linear_combination hyz' - hy1 * z1' - hy23 * z2' - y3' * htz23
        have h2t : (-2 * t') ≠ 0 := mul_ne_zero (by norm_num) ht0
        have hyz0 : y3' * z2' = 0 := (mul_eq_zero.mp hprod).resolve_left h2t
        rcases mul_eq_zero.mp hyz0 with hy3 | hz2
        · have hy2 : y2' = 0 := by rw [hy3] at hy23; linear_combination hy23
          exact hy' ⟨hy1, hy2, hy3⟩
        · have hz3 : z3' = 0 := by rw [hz2] at htz23; linear_combination htz23
          exact hz' ⟨hz1, hz2, hz3⟩
    by_cases hs0 : s = 0
    · subst hs0
      refine hstep t y1 y2 y3 z1 z2 z3 hy_ne hz_ne hyz hc_b2 (by linear_combination hc_ab) ?_ ?_
      · intro a b; have h := hquart1 a b; linear_combination h
      · linear_combination hquart2
    · have ht0 : t = 0 := by
        by_contra htne
        exact hst ⟨hs0, htne⟩
      subst ht0
      refine hstep s y2 y1 y3 z2 z1 z3
        (fun ⟨h2, h1, h3⟩ => hy_ne ⟨h1, h2, h3⟩)
        (fun ⟨h2, h1, h3⟩ => hz_ne ⟨h1, h2, h3⟩)
        (by linear_combination hyz)
        hc_a2
        (by linear_combination hc_ab)
        ?_ ?_
      · intro a b; have h := hquart1 b a; linear_combination h
      · linear_combination hquart2

lemma plane_contradiction (p1 p2 p3 q1 q2 q3 y1 y2 y3 z1 z2 z3 w1 w2 w3 : ℂ)
    (hp_ne : ¬(p1 = 0 ∧ p2 = 0 ∧ p3 = 0))
    (hq_indep : ∀ c : ℂ, ¬(q1 = c * p1 ∧ q2 = c * p2 ∧ q3 = c * p3))
    (hy_ne : ¬(y1 = 0 ∧ y2 = 0 ∧ y3 = 0))
    (hz_ne : ¬(z1 = 0 ∧ z2 = 0 ∧ z3 = 0))
    (hw_ne : ¬(w1 = 0 ∧ w2 = 0 ∧ w3 = 0))
    (hpw : p1 * w1 + p2 * w2 + p3 * w3 = 0)
    (hqw : q1 * w1 + q2 * w2 + q3 * w3 = 0)
    (hyz : y1 * z1 + y2 * z2 + y3 * z3 = 0)
    (hcubic : ∀ α β : ℂ,
      let u1 := α * p1 + β * q1
      let u2 := α * p2 + β * q2
      let u3 := α * p3 + β * q3
      z1 * u2 * u3 + z2 * u1 * u3 + z3 * u1 * u2 = 0)
    (hquart1 : ∀ α β : ℂ,
      let u1 := α * p1 + β * q1
      let u2 := α * p2 + β * q2
      let u3 := α * p3 + β * q3
      y1 * u1 * (2 * u1 ^ 2 - (u1 ^ 2 + u2 ^ 2 + u3 ^ 2)) +
      y2 * u2 * (2 * u2 ^ 2 - (u1 ^ 2 + u2 ^ 2 + u3 ^ 2)) +
      y3 * u3 * (2 * u3 ^ 2 - (u1 ^ 2 + u2 ^ 2 + u3 ^ 2)) = 0)
    (hquart2 :
      w1 * y1 * (2 * y1 ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)) +
      w2 * y2 * (2 * y2 ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)) +
      w3 * y3 * (2 * y3 ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)) = 0) : False := by
  have hsolve : ∀ (p1 p2 p3 q1 q2 q3 y1 y2 y3 z1 z2 z3 w1 w2 w3 : ℂ),
      ¬(p1 = 0 ∧ p2 = 0 ∧ p3 = 0) →
      (∀ c : ℂ, ¬(q1 = c * p1 ∧ q2 = c * p2 ∧ q3 = c * p3)) →
      ¬(y1 = 0 ∧ y2 = 0 ∧ y3 = 0) →
      ¬(z1 = 0 ∧ z2 = 0 ∧ z3 = 0) →
      w3 ≠ 0 →
      p1 * w1 + p2 * w2 + p3 * w3 = 0 →
      q1 * w1 + q2 * w2 + q3 * w3 = 0 →
      y1 * z1 + y2 * z2 + y3 * z3 = 0 →
      (∀ α β : ℂ,
        let u1 := α * p1 + β * q1
        let u2 := α * p2 + β * q2
        let u3 := α * p3 + β * q3
        z1 * u2 * u3 + z2 * u1 * u3 + z3 * u1 * u2 = 0) →
      (∀ α β : ℂ,
        let u1 := α * p1 + β * q1
        let u2 := α * p2 + β * q2
        let u3 := α * p3 + β * q3
        y1 * u1 * (2 * u1 ^ 2 - (u1 ^ 2 + u2 ^ 2 + u3 ^ 2)) +
        y2 * u2 * (2 * u2 ^ 2 - (u1 ^ 2 + u2 ^ 2 + u3 ^ 2)) +
        y3 * u3 * (2 * u3 ^ 2 - (u1 ^ 2 + u2 ^ 2 + u3 ^ 2)) = 0) →
      (w1 * y1 * (2 * y1 ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)) +
       w2 * y2 * (2 * y2 ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)) +
       w3 * y3 * (2 * y3 ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)) = 0) →
      False := by
    intro p1 p2 p3 q1 q2 q3 y1 y2 y3 z1 z2 z3 w1 w2 w3
      hp_ne hq_indep hy_ne hz_ne hw3 hpw hqw hyz hcubic hquart1 hquart2
    let s : ℂ := -w1 / w3
    let t : ℂ := -w2 / w3
    have hp3 : p3 = s * p1 + t * p2 := by
      dsimp [s, t]; field_simp [hw3]; linear_combination hpw
    have hq3 : q3 = s * q1 + t * q2 := by
      dsimp [s, t]; field_simp [hw3]; linear_combination hqw
    let Δ : ℂ := p1 * q2 - p2 * q1
    have hΔ : Δ ≠ 0 := by
      intro hΔ0
      dsimp only [Δ] at hΔ0
      by_cases hp1 : p1 = 0
      · by_cases hp2 : p2 = 0
        · rw [hp1, hp2] at hp3
          exact hp_ne ⟨hp1, hp2, by linear_combination hp3⟩
        · have hq1 : q1 = 0 := by
            have : p2 * q1 = 0 := by rw [hp1] at hΔ0; linear_combination -hΔ0
            exact (mul_eq_zero.mp this).resolve_left hp2
          let c : ℂ := q2 / p2
          refine hq_indep c ⟨?_, ?_, ?_⟩
          · rw [hp1, hq1, mul_zero]
          · dsimp [c]; field_simp [hp2]
          · rw [hp3, hq3, hp1, hq1]
            have hc2 : q2 = c * p2 := by dsimp [c]; field_simp [hp2]
            rw [hc2]; ring
      · let c : ℂ := q1 / p1
        have hc1 : q1 = c * p1 := by dsimp [c]; field_simp [hp1]
        have hc2 : q2 = c * p2 := by
          have : p1 * (q2 - c * p2) = 0 := by
            calc p1 * (q2 - c * p2) = p1 * q2 - p2 * (c * p1) := by ring
              _ = p1 * q2 - p2 * q1 := by rw [← hc1]
              _ = 0 := hΔ0
          exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hp1)
        refine hq_indep c ⟨hc1, hc2, ?_⟩
        rw [hp3, hq3, hc1, hc2]; ring
    have hreach : ∀ a b : ℂ, ∃ α β : ℂ,
        α * p1 + β * q1 = a ∧ α * p2 + β * q2 = b ∧ α * p3 + β * q3 = s * a + t * b := by
      intro a b
      refine ⟨(a * q2 - b * q1) / Δ, (b * p1 - a * p2) / Δ, ?_, ?_, ?_⟩
      · field_simp [hΔ]; dsimp [Δ]; ring
      · field_simp [hΔ]; dsimp [Δ]; ring
      · rw [hp3, hq3]; field_simp [hΔ]; dsimp [Δ]; ring
    refine plane_contradiction_core s t y1 y2 y3 z1 z2 z3 hy_ne hz_ne hyz ?_ ?_ ?_
    · intro a b
      rcases hreach a b with ⟨α, β, h1, h2, h3⟩
      have h := hcubic α β
      dsimp only at h
      rw [h1, h2, h3] at h
      exact h
    · intro a b
      rcases hreach a b with ⟨α, β, h1, h2, h3⟩
      have h := hquart1 α β
      dsimp only at h
      rw [h1, h2, h3] at h
      exact h
    · dsimp [s, t]
      field_simp [hw3]
      linear_combination hquart2
  by_cases hw3 : w3 ≠ 0
  · exact hsolve p1 p2 p3 q1 q2 q3 y1 y2 y3 z1 z2 z3 w1 w2 w3
      hp_ne hq_indep hy_ne hz_ne hw3 hpw hqw hyz hcubic hquart1 hquart2
  · push Not at hw3
    by_cases hw2 : w2 ≠ 0
    · refine hsolve p1 p3 p2 q1 q3 q2 y1 y3 y2 z1 z3 z2 w1 w3 w2
        (fun ⟨h1, h3, h2⟩ => hp_ne ⟨h1, h2, h3⟩)
        (fun c ⟨h1, h3, h2⟩ => hq_indep c ⟨h1, h2, h3⟩)
        (fun ⟨h1, h3, h2⟩ => hy_ne ⟨h1, h2, h3⟩)
        (fun ⟨h1, h3, h2⟩ => hz_ne ⟨h1, h2, h3⟩)
        hw2
        (by linear_combination hpw)
        (by linear_combination hqw)
        (by linear_combination hyz)
        ?_ ?_ (by linear_combination hquart2)
      · intro α β; have h := hcubic α β; dsimp only at h ⊢; linear_combination h
      · intro α β; have h := hquart1 α β; dsimp only at h ⊢; linear_combination h
    · push Not at hw2
      have hw1 : w1 ≠ 0 := fun h1 => hw_ne ⟨h1, hw2, hw3⟩
      refine hsolve p3 p2 p1 q3 q2 q1 y3 y2 y1 z3 z2 z1 w3 w2 w1
        (fun ⟨h3, h2, h1⟩ => hp_ne ⟨h1, h2, h3⟩)
        (fun c ⟨h3, h2, h1⟩ => hq_indep c ⟨h1, h2, h3⟩)
        (fun ⟨h3, h2, h1⟩ => hy_ne ⟨h1, h2, h3⟩)
        (fun ⟨h3, h2, h1⟩ => hz_ne ⟨h1, h2, h3⟩)
        hw1
        (by linear_combination hpw)
        (by linear_combination hqw)
        (by linear_combination hyz)
        ?_ ?_ (by linear_combination hquart2)
      · intro α β; have h := hcubic α β; dsimp only at h ⊢; linear_combination h
      · intro α β; have h := hquart1 α β; dsimp only at h ⊢; linear_combination h

lemma finrank_zero_mode_eq_one (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5)
    (U : Fin 4 → Submodule ℂ (Fin 4 → ℂ))
    (hne : ∀ r, U r ≠ ⊥)
    (hsum : ∀ r, ∀ v ∈ U r, (∑ i, v i) = 0)
    (hperm : ∀ x : Fin 4 → Fin 4 → ℂ, (∀ r, x r ∈ U r) →
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + ∑ r : Fin 4, x r i * ζ ^ ((r.val + 1) * (f i).val))) = 120) :
    Module.finrank ℂ (U 0) = 1 := by
  have hne0 : Module.finrank ℂ (U 0) ≠ 0 := by
    intro h0
    exact hne 0 (Submodule.finrank_eq_zero.mp h0)
  by_contra hne1
  have hge2 : 2 ≤ Module.finrank ℂ (U 0) := by omega
  rcases Submodule.exists_mem_ne_zero_of_ne_bot (hne 0) with ⟨p, hpU, hp0⟩
  rcases Submodule.exists_mem_ne_zero_of_ne_bot (hne 1) with ⟨Y, hYU, hY0⟩
  rcases Submodule.exists_mem_ne_zero_of_ne_bot (hne 2) with ⟨Z, hZU, hZ0⟩
  rcases Submodule.exists_mem_ne_zero_of_ne_bot (hne 3) with ⟨W, hWU, hW0⟩
  have hex_q : ∃ q ∈ U 0, ∀ c : ℂ, q ≠ c • p := by
    by_contra hall
    push Not at hall
    have hle : U 0 ≤ Submodule.span ℂ ({p} : Set (Fin 4 → ℂ)) := by
      intro q hq
      rcases hall q hq with ⟨c, rfl⟩
      exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton p))
    have hfin : Module.finrank ℂ (U 0) ≤ 1 := by
      calc Module.finrank ℂ (U 0)
          ≤ Module.finrank ℂ (Submodule.span ℂ ({p} : Set (Fin 4 → ℂ))) :=
            Submodule.finrank_mono hle
        _ = 1 := finrank_span_singleton hp0
    omega
  rcases hex_q with ⟨q, hqU, hq_ind⟩
  have htwo_mode : ∀ (r₁ r₂ : Fin 4), r₁ ≠ r₂ → ∀ (u v : Fin 4 → ℂ),
      u ∈ U r₁ → v ∈ U r₂ → ∀ t : ℂ,
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + t * u i * ζ ^ ((r₁.val + 1) * (f i).val) +
             v i * ζ ^ ((r₂.val + 1) * (f i).val))) = 120 := by
    intro r₁ r₂ hr u v hu hv t
    let x : Fin 4 → Fin 4 → ℂ := fun r =>
      if r = r₁ then t • u else if r = r₂ then v else 0
    have hx : ∀ r, x r ∈ U r := by
      intro r
      dsimp [x]
      split_ifs with h1 h2
      · subst h1; exact (U r).smul_mem t hu
      · subst h2; exact hv
      · exact (U r).zero_mem
    have hpx := hperm x hx
    have hfac : ∀ (f : Fin 4 ↪ Fin 5) (i : Fin 4),
        (1 + ∑ r : Fin 4, x r i * ζ ^ ((r.val + 1) * (f i).val)) =
          1 + t * u i * ζ ^ ((r₁.val + 1) * (f i).val) +
            v i * ζ ^ ((r₂.val + 1) * (f i).val) := by
      intro f i
      fin_cases r₁ <;> fin_cases r₂ <;> simp_all [x, Fin.sum_univ_four] <;> ring
    simp_rw [hfac] at hpx
    exact hpx
  have hpw_raw : ∀ u ∈ U 0,
      u 0 * (W 1 + W 2 + W 3) + u 1 * (W 0 + W 2 + W 3) +
      u 2 * (W 0 + W 1 + W 3) + u 3 * (W 0 + W 1 + W 2) = 0 := by
    intro u hu
    refine extract_pair hζ u W (fun t => ?_)
    have h := htwo_mode 0 3 (by decide) u W hu hWU t
    have h0v : (0 : Fin 4).val + 1 = 1 := rfl
    have h3v : (3 : Fin 4).val + 1 = 4 := rfl
    simp only [h0v, h3v, one_mul] at h
    exact h
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) 5 := isPrimitiveRoot_pow_fin4 hζ 1
  have hyz_raw :
      Y 0 * (Z 1 + Z 2 + Z 3) + Y 1 * (Z 0 + Z 2 + Z 3) +
      Y 2 * (Z 0 + Z 1 + Z 3) + Y 3 * (Z 0 + Z 1 + Z 2) = 0 := by
    refine extract_pair hζ2 Y Z (fun t => ?_)
    have h := htwo_mode 1 2 (by decide) Y Z hYU hZU t
    have h1v : (1 : Fin 4).val + 1 = 2 := rfl
    have h2v : (2 : Fin 4).val + 1 = 3 := rfl
    simp only [h1v, h2v] at h
    have heq : ∀ (f : Fin 4 ↪ Fin 5) (i : Fin 4),
        (1 + t * Y i * (ζ ^ 2) ^ (f i).val + Z i * (ζ ^ 2) ^ (4 * (f i).val)) =
          1 + t * Y i * ζ ^ (2 * (f i).val) + Z i * ζ ^ (3 * (f i).val) := by
      intro f i
      have h1 : (ζ ^ 2) ^ (f i).val = ζ ^ (2 * (f i).val) := by rw [← pow_mul]
      have h2 : (ζ ^ 2) ^ (4 * (f i).val) = ζ ^ (3 * (f i).val) := by
        rw [← pow_mul, zeta_pow_mod hζ, zeta_pow_mod hζ (n := 3 * (f i).val)]
        congr 1; omega
      rw [h1, h2]
    simp_rw [heq]
    exact h
  have hcubic_raw : ∀ u ∈ U 0,
      u 0 * u 1 * (Z 2 + Z 3) + u 0 * u 2 * (Z 1 + Z 3) + u 0 * u 3 * (Z 1 + Z 2) +
      u 1 * u 2 * (Z 0 + Z 3) + u 1 * u 3 * (Z 0 + Z 2) + u 2 * u 3 * (Z 0 + Z 1) = 0 := by
    intro u hu
    refine extract_cubic hζ u Z (fun t => ?_)
    have h := htwo_mode 0 2 (by decide) u Z hu hZU t
    have h0v : (0 : Fin 4).val + 1 = 1 := rfl
    have h2v : (2 : Fin 4).val + 1 = 3 := rfl
    simp only [h0v, h2v, one_mul] at h
    exact h
  have hquart1_raw : ∀ u ∈ U 0,
      Y 0 * u 1 * u 2 * u 3 + Y 1 * u 0 * u 2 * u 3 +
      Y 2 * u 0 * u 1 * u 3 + Y 3 * u 0 * u 1 * u 2 = 0 := by
    intro u hu
    refine extract_quartic hζ u Y (fun t => ?_)
    have h := htwo_mode 0 1 (by decide) u Y hu hYU t
    have h0v : (0 : Fin 4).val + 1 = 1 := rfl
    have h1v : (1 : Fin 4).val + 1 = 2 := rfl
    simp only [h0v, h1v, one_mul] at h
    exact h
  have hquart2_raw :
      W 0 * Y 1 * Y 2 * Y 3 + W 1 * Y 0 * Y 2 * Y 3 +
      W 2 * Y 0 * Y 1 * Y 3 + W 3 * Y 0 * Y 1 * Y 2 = 0 := by
    refine extract_quartic hζ2 Y W (fun t => ?_)
    have h := htwo_mode 1 3 (by decide) Y W hYU hWU t
    have h1v : (1 : Fin 4).val + 1 = 2 := rfl
    have h3v : (3 : Fin 4).val + 1 = 4 := rfl
    simp only [h1v, h3v] at h
    have heq : ∀ (f : Fin 4 ↪ Fin 5) (i : Fin 4),
        (1 + t * Y i * (ζ ^ 2) ^ (f i).val + W i * (ζ ^ 2) ^ (2 * (f i).val)) =
          1 + t * Y i * ζ ^ (2 * (f i).val) + W i * ζ ^ (4 * (f i).val) := by
      intro f i
      rw [← pow_mul, ← pow_mul]
      have : 2 * (2 * (f i).val) = 4 * (f i).val := by ring
      rw [this]
    simp_rw [heq]
    exact h
  have hp_Hne : ¬(H1 p = 0 ∧ H2 p = 0 ∧ H3 p = 0) :=
    fun h => hp0 ((H_eq_zero_iff p (hsum 0 p hpU)).mp h)
  have hY_Hne : ¬(H1 Y = 0 ∧ H2 Y = 0 ∧ H3 Y = 0) :=
    fun h => hY0 ((H_eq_zero_iff Y (hsum 1 Y hYU)).mp h)
  have hZ_Hne : ¬(H1 Z = 0 ∧ H2 Z = 0 ∧ H3 Z = 0) :=
    fun h => hZ0 ((H_eq_zero_iff Z (hsum 2 Z hZU)).mp h)
  have hW_Hne : ¬(H1 W = 0 ∧ H2 W = 0 ∧ H3 W = 0) :=
    fun h => hW0 ((H_eq_zero_iff W (hsum 3 W hWU)).mp h)
  have hq_Hind : ∀ c : ℂ, ¬(H1 q = c * H1 p ∧ H2 q = c * H2 p ∧ H3 q = c * H3 p) := by
    rintro c ⟨h1, h2, h3⟩
    have hdiff : q - c • p ∈ U 0 := (U 0).sub_mem hqU ((U 0).smul_mem c hpU)
    have hH0 : H1 (q - c • p) = 0 ∧ H2 (q - c • p) = 0 ∧ H3 (q - c • p) = 0 := by
      refine ⟨?_, ?_, ?_⟩
      · unfold H1 at h1 ⊢; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; linear_combination h1
      · unfold H2 at h2 ⊢; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; linear_combination h2
      · unfold H3 at h3 ⊢; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; linear_combination h3
    have h0 := (H_eq_zero_iff (q - c • p) (hsum 0 _ hdiff)).mp hH0
    exact hq_ind c (sub_eq_zero.mp h0)
  have hpw_H : H1 p * H1 W + H2 p * H2 W + H3 p * H3 W = 0 := by
    have h := H_pair_eq p W (hsum 0 p hpU)
    rw [hpw_raw p hpU, mul_zero] at h
    linear_combination h
  have hqw_H : H1 q * H1 W + H2 q * H2 W + H3 q * H3 W = 0 := by
    have h := H_pair_eq q W (hsum 0 q hqU)
    rw [hpw_raw q hqU, mul_zero] at h
    linear_combination h
  have hyz_H : H1 Y * H1 Z + H2 Y * H2 Z + H3 Y * H3 Z = 0 := by
    have h := H_pair_eq Y Z (hsum 1 Y hYU)
    rw [hyz_raw, mul_zero] at h
    linear_combination h
  have hcubic_H : ∀ α β : ℂ,
      let u1 := α * H1 p + β * H1 q
      let u2 := α * H2 p + β * H2 q
      let u3 := α * H3 p + β * H3 q
      H1 Z * u2 * u3 + H2 Z * u1 * u3 + H3 Z * u1 * u2 = 0 := by
    intro α β
    let u : Fin 4 → ℂ := α • p + β • q
    have huU : u ∈ U 0 := (U 0).add_mem ((U 0).smul_mem α hpU) ((U 0).smul_mem β hqU)
    have h1 : H1 u = α * H1 p + β * H1 q := by
      simp only [H1, u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have h2 : H2 u = α * H2 p + β * H2 q := by
      simp only [H2, u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have h3 : H3 u = α * H3 p + β * H3 q := by
      simp only [H3, u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hc := H_cubic_eq u Z (hsum 0 u huU) (hsum 2 Z hZU)
    rw [hcubic_raw u huU, mul_zero, h1, h2, h3] at hc
    exact hc.symm
  have hquart1_H : ∀ α β : ℂ,
      let u1 := α * H1 p + β * H1 q
      let u2 := α * H2 p + β * H2 q
      let u3 := α * H3 p + β * H3 q
      H1 Y * u1 * (2 * u1 ^ 2 - (u1 ^ 2 + u2 ^ 2 + u3 ^ 2)) +
      H2 Y * u2 * (2 * u2 ^ 2 - (u1 ^ 2 + u2 ^ 2 + u3 ^ 2)) +
      H3 Y * u3 * (2 * u3 ^ 2 - (u1 ^ 2 + u2 ^ 2 + u3 ^ 2)) = 0 := by
    intro α β
    let u : Fin 4 → ℂ := α • p + β • q
    have huU : u ∈ U 0 := (U 0).add_mem ((U 0).smul_mem α hpU) ((U 0).smul_mem β hqU)
    have h1 : H1 u = α * H1 p + β * H1 q := by
      simp only [H1, u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have h2 : H2 u = α * H2 p + β * H2 q := by
      simp only [H2, u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have h3 : H3 u = α * H3 p + β * H3 q := by
      simp only [H3, u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hq_ := H_quartic_eq u Y (hsum 0 u huU) (hsum 1 Y hYU)
    rw [hquart1_raw u huU, mul_zero, h1, h2, h3] at hq_
    exact hq_.symm
  have hquart2_H :
      H1 W * H1 Y * (2 * H1 Y ^ 2 - (H1 Y ^ 2 + H2 Y ^ 2 + H3 Y ^ 2)) +
      H2 W * H2 Y * (2 * H2 Y ^ 2 - (H1 Y ^ 2 + H2 Y ^ 2 + H3 Y ^ 2)) +
      H3 W * H3 Y * (2 * H3 Y ^ 2 - (H1 Y ^ 2 + H2 Y ^ 2 + H3 Y ^ 2)) = 0 := by
    have hq_ := H_quartic_eq Y W (hsum 1 Y hYU) (hsum 3 W hWU)
    rw [hquart2_raw, mul_zero] at hq_
    exact hq_.symm
  exact plane_contradiction (H1 p) (H2 p) (H3 p) (H1 q) (H2 q) (H3 q)
    (H1 Y) (H2 Y) (H3 Y) (H1 Z) (H2 Z) (H3 Z) (H1 W) (H2 W) (H3 W)
    hp_Hne hq_Hind hY_Hne hZ_Hne hW_Hne hpw_H hqw_H hyz_H hcubic_H hquart1_H hquart2_H

def modePerm (r0 : Fin 4) : Equiv.Perm (Fin 4) :=
  let k : ℕ := r0.val + 1
  let inv : ℕ := if k = 1 then 1 else if k = 2 then 3 else if k = 3 then 2 else 4
  { toFun := fun r => ⟨((k * (r.val + 1)) % 5) - 1, by
      fin_cases r0 <;> fin_cases r <;> decide⟩
    invFun := fun r => ⟨((inv * (r.val + 1)) % 5) - 1, by
      fin_cases r0 <;> fin_cases r <;> decide⟩
    left_inv := fun r => by fin_cases r0 <;> fin_cases r <;> decide
    right_inv := fun r => by fin_cases r0 <;> fin_cases r <;> decide }

lemma modePerm_zero (r0 : Fin 4) : modePerm r0 0 = r0 := by
  fin_cases r0 <;> decide

lemma modePerm_mod (r0 r : Fin 4) :
    ((modePerm r0 r).val + 1) % 5 = ((r0.val + 1) * (r.val + 1)) % 5 := by
  fin_cases r0 <;> fin_cases r <;> decide

end

end PEqualNP.Outside.L_gct_282_aux

theorem PEqualNP.Outside.L_gct_282 :
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ 5 →
      ∀ U : Fin 4 → Submodule ℂ (Fin 4 → ℂ),
        (∀ r, U r ≠ ⊥) →
        (∀ r, ∀ v ∈ U r, (∑ i, v i) = 0) →
        (∀ x : Fin 4 → Fin 4 → ℂ, (∀ r, x r ∈ U r) →
          (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
            (1 + ∑ r : Fin 4, x r i * ζ ^ ((r.val+1)*(f i).val))) = 120) →
        ∀ r, Module.finrank ℂ (U r) = 1 := by
  intro ζ hζ U hne hsum hperm r0
  let π := PEqualNP.Outside.L_gct_282_aux.modePerm r0
  let ζ' := ζ ^ (r0.val + 1)
  have hζ' : IsPrimitiveRoot ζ' 5 :=
    PEqualNP.Outside.L_gct_282_aux.isPrimitiveRoot_pow_fin4 hζ r0
  let U' : Fin 4 → Submodule ℂ (Fin 4 → ℂ) := fun r => U (π r)
  have hU0 : U' 0 = U r0 := by
    dsimp [U', π]
    rw [PEqualNP.Outside.L_gct_282_aux.modePerm_zero]
  rw [← hU0]
  refine PEqualNP.Outside.L_gct_282_aux.finrank_zero_mode_eq_one ζ' hζ' U'
    (fun r => hne (π r)) (fun r v hv => hsum (π r) v hv) ?_
  intro x' hx'
  let x : Fin 4 → Fin 4 → ℂ := fun r => x' (π.symm r)
  have hx : ∀ r, x r ∈ U r := by
    intro r
    have := hx' (π.symm r)
    simpa [U', x] using this
  have hpx := hperm x hx
  have hsum_eq : ∀ (f : Fin 4 ↪ Fin 5) (i : Fin 4),
      (∑ r : Fin 4, x' r i * ζ' ^ ((r.val + 1) * (f i).val)) =
        ∑ r : Fin 4, x r i * ζ ^ ((r.val + 1) * (f i).val) := by
    intro f i
    refine Fintype.sum_equiv π _ _ (fun r => ?_)
    have hxr : x (π r) = x' r := by dsimp [x]; simp
    rw [hxr]
    congr 1
    dsimp [ζ']
    rw [← pow_mul, PEqualNP.Outside.L_gct_282_aux.zeta_pow_mod hζ,
      PEqualNP.Outside.L_gct_282_aux.zeta_pow_mod hζ (n := ((π r).val + 1) * (f i).val)]
    congr 1
    have hmod := PEqualNP.Outside.L_gct_282_aux.modePerm_mod r0 r
    rw [← mul_assoc, Nat.mul_mod, Nat.mul_mod ((π r).val + 1), hmod]
  simp_rw [hsum_eq]
  exact hpx

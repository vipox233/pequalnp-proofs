import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_889

def chi (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

lemma chi_add : ∀ a b : ZMod 2, chi (a + b) = chi a * chi b := by decide

lemma chi_sub : ∀ a b : ZMod 2, chi (a - b) = chi a * chi b := by decide

lemma chi_le : ∀ a : ZMod 2, chi a ≤ 1 := by decide

lemma chi_one : chi 1 = -1 := by decide

lemma chi_zero : chi 0 = 1 := by decide

lemma chi_eq_one : ∀ a : ZMod 2, chi a = 1 → a = 0 := by decide

lemma eq_one_of_ne : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

lemma eq_of_add : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide

lemma self_add : ∀ a : ZMod 2, a + a = 0 := by decide

lemma key5 : ∀ a b c d e : ZMod 2,
    chi (d + e) * chi (a + b + c + d) = chi (a + b + c + e) := by decide

lemma sum_chi_zero {G : Type*} [AddGroup G] [Fintype G] (f : G → ZMod 2)
    (hf : ∀ x y, f (x + y) = f x + f y) (w : G) (hw : f w ≠ 0) :
    ∑ x, chi (f x) = 0 := by
  have h1 : f w = 1 := eq_one_of_ne _ hw
  have h2 : ∑ x, chi (f (x + w)) = ∑ x, chi (f x) :=
    Equiv.sum_comp (Equiv.addRight w) (fun x => chi (f x))
  have h3 : ∑ x, chi (f (x + w)) = - ∑ x, chi (f x) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hf, h1, chi_add, chi_one]
    ring
  linarith

lemma vanish_right {U V : Type*} [AddGroup V] [Fintype U] [Fintype V]
    (β : U → V → ZMod 2) (hr : ∀ x y y', β x (y + y') = β x y + β x y')
    (a₁ : U → ZMod 2) (a₂ : V → ZMod 2) (h2 : ∀ y y', a₂ (y + y') = a₂ y + a₂ y')
    (c : ZMod 2) (hno : ¬ ∃ p, ∀ y, a₂ y = β p y) :
    ∑ x, ∑ y, chi (β x y + a₁ x + a₂ y + c) = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  have hx : ∃ w, β x w + a₂ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hno ⟨x, fun y => eq_of_add _ _ (h y)⟩
  obtain ⟨w, hw⟩ := hx
  have h0 := sum_chi_zero (fun y => β x y + a₂ y)
    (by intro y y'; simp only [hr, h2]; ring) w hw
  have e : ∀ y, chi (β x y + a₁ x + a₂ y + c) = chi (a₁ x + c) * chi (β x y + a₂ y) := by
    intro y
    rw [← chi_add]
    congr 1
    ring
  simp only [e, ← Finset.mul_sum, h0, mul_zero]

lemma vanish_left {U V : Type*} [AddGroup U] [Fintype U] [Fintype V]
    (β : U → V → ZMod 2) (hl : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (a₁ : U → ZMod 2) (a₂ : V → ZMod 2) (h1 : ∀ x x', a₁ (x + x') = a₁ x + a₁ x')
    (c : ZMod 2) (hno : ¬ ∃ q, ∀ x, a₁ x = β x q) :
    ∑ x, ∑ y, chi (β x y + a₁ x + a₂ y + c) = 0 := by
  rw [Finset.sum_comm]
  have h := vanish_right (fun y x => β x y) (fun y x x' => hl x x' y) a₂ a₁ h1 c hno
  rw [← h]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  congr 1
  ring

lemma translate {U V : Type*} [AddGroup U] [AddGroup V] [Fintype U] [Fintype V]
    (β : U → V → ZMod 2) (hl : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (hr : ∀ x y y', β x (y + y') = β x y + β x y') (p : U) (q : V) (c : ZMod 2) :
    ∑ x, ∑ y, chi (β x y + β x q + β p y + c)
      = chi (β p q + c) * ∑ x, ∑ y, chi (β x y) := by
  have h1 : ∑ x, ∑ y, chi (β x y) = ∑ x, ∑ y, chi (β (x + p) (y + q)) := by
    rw [← Equiv.sum_comp (Equiv.addRight p)]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact (Equiv.sum_comp (Equiv.addRight q) (fun y => chi (β (x + p) y))).symm
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h3 : β x y + β p y + (β x q + β p q) = β x y + β x q + β p y + β p q := by ring
  rw [hr, hl, hl, h3, key5]

lemma per {U V : Type*} [AddGroup U] [AddGroup V] [Fintype U] [Fintype V]
    (β : U → V → ZMod 2) (hl : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (hr : ∀ x y y', β x (y + y') = β x y + β x y')
    (a₁ : U → ZMod 2) (a₂ : V → ZMod 2) (h1 : ∀ x x', a₁ (x + x') = a₁ x + a₁ x')
    (h2 : ∀ y y', a₂ (y + y') = a₂ y + a₂ y') (c : ZMod 2)
    (hpos : 0 < ∑ x, ∑ y, chi (β x y)) :
    ∑ x, ∑ y, chi (β x y + a₁ x + a₂ y + c) ≤ ∑ x, ∑ y, chi (β x y) ∧
    (∑ x, ∑ y, chi (β x y + a₁ x + a₂ y + c) = ∑ x, ∑ y, chi (β x y) ↔
      ∃ p q, (∀ u, a₁ u = β u q) ∧ (∀ v, a₂ v = β p v) ∧ c = β p q) := by
  by_cases hq : ∃ q, ∀ x, a₁ x = β x q
  · by_cases hp : ∃ p, ∀ y, a₂ y = β p y
    · obtain ⟨q, hq⟩ := hq
      obtain ⟨p, hp⟩ := hp
      have hT : ∑ x, ∑ y, chi (β x y + a₁ x + a₂ y + c)
          = chi (β p q + c) * ∑ x, ∑ y, chi (β x y) := by
        rw [← translate β hl hr p q c]
        simp only [hq, hp]
      rw [hT]
      have hc := chi_le (β p q + c)
      refine ⟨by nlinarith, ?_, ?_⟩
      · intro h
        have h3 : chi (β p q + c) = 1 := by nlinarith
        exact ⟨p, q, hq, hp, eq_of_add _ _ (chi_eq_one _ h3)⟩
      · rintro ⟨p', q', hq', hp', hc'⟩
        have hT' : ∑ x, ∑ y, chi (β x y + a₁ x + a₂ y + c)
            = chi (β p' q' + c) * ∑ x, ∑ y, chi (β x y) := by
          rw [← translate β hl hr p' q' c]
          simp only [hq', hp']
        rw [← hT, hT', hc', self_add, chi_zero, one_mul]
    · have h0 := vanish_right β hr a₁ a₂ h2 c hp
      rw [h0]
      refine ⟨hpos.le, fun h => absurd h hpos.ne, ?_⟩
      rintro ⟨p, q, -, hp', -⟩
      exact absurd ⟨p, hp'⟩ hp
  · have h0 := vanish_left β hl a₁ a₂ h1 c hq
    rw [h0]
    refine ⟨hpos.le, fun h => absurd h hpos.ne, ?_⟩
    rintro ⟨p, q, hq', -, -⟩
    exact absurd ⟨q, hq'⟩ hq

lemma card_V (k : ℕ) : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
  simp

lemma sum_mask (s : ℕ) (z : Fin s → ZMod 2) :
    ∑ α : Fin s → ZMod 2, chi (dotProduct α z) = if z = 0 then (2 : ℤ) ^ s else 0 := by
  split_ifs with h
  · subst h
    simp [chi_zero]
  · have hi : ∃ i, z i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    obtain ⟨i, hi⟩ := hi
    refine sum_chi_zero (fun α : Fin s → ZMod 2 => dotProduct α z)
      (fun x y => add_dotProduct x y z) (Pi.single i 1) ?_
    simpa using hi

lemma base_sum (l r : ℕ) (g : (Fin l → ZMod 2) →ₗ[ZMod 2] ((Fin r → ZMod 2) → ZMod 2))
    (hr : ∀ x y y', g x (y + y') = g x y + g x y') :
    ∑ x, ∑ y, chi (g x y)
      = (2 : ℤ) ^ (l + r - Module.finrank (ZMod 2) (LinearMap.range g)) := by
  classical
  have hin : ∀ x, ∑ y, chi (g x y) = if g x = 0 then (2 : ℤ) ^ r else 0 := by
    intro x
    split_ifs with h
    · simp [h, chi_zero]
    · have hw : ∃ w, g x w ≠ 0 := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      obtain ⟨w, hw⟩ := hw
      exact sum_chi_zero (fun y => g x y) (hr x) w hw
  have hk : Nat.card (LinearMap.ker g) = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker g) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    simp
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [Module.finrank_fin_fun] at hrn
  have hc : ((Finset.univ.filter (fun x => g x = 0)).card : ℤ)
      = (2 : ℤ) ^ Module.finrank (ZMod 2) (LinearMap.ker g) := by
    have : (Finset.univ.filter (fun x => g x = 0)).card = Nat.card (LinearMap.ker g) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp only [LinearMap.mem_ker]
    rw [this, hk]
    push_cast
    rfl
  simp only [hin]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hc, ← pow_add]
  congr 1
  omega

lemma chi4 : ∀ u v w z : ZMod 2, chi (u - (v + w + z)) = chi (u + v + w + z) := by decide

def gm (l r s : ℕ)
    (B : (Fin l → ZMod 2) →ₗ[ZMod 2] ((Fin r → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)))
    (α : Fin s → ZMod 2) : (Fin l → ZMod 2) →ₗ[ZMod 2] ((Fin r → ZMod 2) → ZMod 2) where
  toFun := fun x y => dotProduct α (B x y)
  map_add' := by
    intro x x'
    funext y
    simp [dotProduct_add]
  map_smul' := by
    intro m x
    funext y
    simp [dotProduct_smul]

lemma hits_cast (l r s : ℕ)
    (B : (Fin l → ZMod 2) →ₗ[ZMod 2] ((Fin r → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)))
    (A : ((Fin l → ZMod 2) × (Fin r → ZMod 2)) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (b : Fin s → ZMod 2) :
    (2 : ℤ) ^ s * (((Finset.univ : Finset ((Fin l → ZMod 2) × (Fin r → ZMod 2))).filter
        (fun p => B p.1 p.2 = A p + b)).card : ℤ)
      = ∑ α : Fin s → ZMod 2, ∑ x, ∑ y,
          chi (dotProduct α (B x y) + dotProduct α (A (x, 0)) + dotProduct α (A (0, y))
            + dotProduct α b) := by
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum, Fintype.sum_prod_type]
  have hsw : ∑ α : Fin s → ZMod 2, ∑ x : Fin l → ZMod 2, ∑ y : Fin r → ZMod 2,
          chi (dotProduct α (B x y) + dotProduct α (A (x, 0)) + dotProduct α (A (0, y))
            + dotProduct α b)
      = ∑ x : Fin l → ZMod 2, ∑ y : Fin r → ZMod 2, ∑ α : Fin s → ZMod 2,
          chi (dotProduct α (B x y) + dotProduct α (A (x, 0)) + dotProduct α (A (0, y))
            + dotProduct α b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
  rw [hsw]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hA : A (x, y) = A (x, 0) + A (0, y) := by
    rw [← map_add]
    simp
  have hm := sum_mask s (B x y - (A (x, y) + b))
  simp only [sub_eq_zero] at hm
  rw [mul_ite, mul_one, mul_zero, ← hm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hA, dotProduct_sub, dotProduct_add, dotProduct_add, chi4]

end PEqualNP.Outside.L_lib_889

theorem PEqualNP.Outside.L_lib_889 : (∀ (l r s : Nat),
  let F := ZMod 2
  let U := Fin l → F
  let V := Fin r → F
  let Z := Fin s → F
  ∀ B : U →ₗ[F] (V →ₗ[F] Z),
    let scalar := fun (a : Z) (x : U) (y : V) => dotProduct a (B x y)
    let rank := fun frequency : Z =>
      Module.finrank F (Submodule.span F (Set.range (fun u : U => scalar frequency u)))
    let hits := fun (L : (U × V) →ₗ[F] Z) (c : Z) =>
      ((Finset.univ : Finset (U × V)).filter (fun p => B p.1 p.2 = L p + c)).card
    2^s * hits 0 0 = (∑ mask : Z, 2^(l+r-rank mask)) ∧
    ∀ (A : (U × V) →ₗ[F] Z) (b : Z),
      hits A b ≤ hits 0 0 ∧
      (hits A b = hits 0 0 ↔ ∀ α : Z, ∃ (p : U) (q : V),
        (∀ u : U, dotProduct α (A (u,0)) = scalar α u q) ∧
        (∀ v : V, dotProduct α (A (0,v)) = scalar α p v) ∧
        dotProduct α b = scalar α p q)) := by
  intro l r s
  dsimp only
  intro B
  have hN : ∀ α : Fin s → ZMod 2,
      ∑ x : Fin l → ZMod 2, ∑ y : Fin r → ZMod 2, L_lib_889.chi (dotProduct α (B x y))
        = (2 : ℤ) ^ (l + r - Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
            (Set.range (fun u : Fin l → ZMod 2 => fun y : Fin r → ZMod 2 =>
              dotProduct α (B u y))))) := by
    intro α
    have h := L_lib_889.base_sum l r (L_lib_889.gm l r s B α) (by
      intro x y y'
      show dotProduct α (B x (y + y')) = dotProduct α (B x y) + dotProduct α (B x y')
      rw [map_add, dotProduct_add])
    have e : Submodule.span (ZMod 2)
        (Set.range (fun u : Fin l → ZMod 2 => fun y : Fin r → ZMod 2 =>
          dotProduct α (B u y))) = LinearMap.range (L_lib_889.gm l r s B α) := by
      have e2 : Set.range (fun u : Fin l → ZMod 2 => fun y : Fin r → ZMod 2 =>
          dotProduct α (B u y)) = (LinearMap.range (L_lib_889.gm l r s B α) : Set _) := by
        rw [LinearMap.coe_range]
        rfl
      rw [e2, Submodule.span_eq]
    rw [e]
    exact h
  have h0 := L_lib_889.hits_cast l r s B 0 0
  simp only [LinearMap.zero_apply, dotProduct_zero, add_zero, hN] at h0
  refine ⟨?_, ?_⟩
  · simp only [LinearMap.zero_apply, add_zero] at h0 ⊢
    exact_mod_cast h0
  · intro A b
    have hA := L_lib_889.hits_cast l r s B A b
    have hper : ∀ α : Fin s → ZMod 2, _ := fun α =>
      L_lib_889.per (fun (x : Fin l → ZMod 2) (y : Fin r → ZMod 2) => dotProduct α (B x y))
        (by intro x x' y; simp [dotProduct_add])
        (by intro x y y'; simp [dotProduct_add])
        (fun x => dotProduct α (A (x, 0))) (fun y => dotProduct α (A (0, y)))
        (by
          intro x x'
          have e : ((x + x', 0) : (Fin l → ZMod 2) × (Fin r → ZMod 2)) = (x, 0) + (x', 0) := by
            simp
          simp only [e, map_add, dotProduct_add])
        (by
          intro y y'
          have e : ((0, y + y') : (Fin l → ZMod 2) × (Fin r → ZMod 2)) = (0, y) + (0, y') := by
            simp
          simp only [e, map_add, dotProduct_add])
        (dotProduct α b)
        (by rw [hN α]; positivity)
    simp only [hN] at hper
    have hle := Finset.sum_le_sum (fun α (_ : α ∈ Finset.univ) => (hper α).1)
    have hiff := Finset.sum_eq_sum_iff_of_le (fun α (_ : α ∈ Finset.univ) => (hper α).1)
    rw [← hA, ← h0] at hle hiff
    have h2 : (0 : ℤ) < 2 ^ s := by positivity
    simp only [LinearMap.zero_apply, add_zero]
    refine ⟨?_, ?_⟩
    · exact_mod_cast le_of_mul_le_mul_left hle h2
    · constructor
      · intro h α
        have h3 := hiff.1 (by rw [h]) α (Finset.mem_univ α)
        exact (hper α).2.1 h3
      · intro h
        have h3 := hiff.2 (fun α _ => (hper α).2.2 (h α))
        exact_mod_cast mul_left_cancel₀ h2.ne' h3

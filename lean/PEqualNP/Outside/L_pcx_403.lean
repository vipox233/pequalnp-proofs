import PEqualNP.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_403

namespace Local403

open scoped Classical

abbrev F := ZMod 2
abbrev B := Fin 3 → F

def mask (z : B) : F := z 2 + z 0 * z 1

def vertical : B := ![0, 0, 1]

def weight (s : B) : ℕ :=
  (Finset.univ.filter fun z : B => mask z = mask (z+s)).card

theorem weight_card (s : B) : weight s = Nat.card {z : B // mask z = mask (z+s)} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem weight_value (s : B) : weight s = if s = 0 then 8 else if s = vertical then 0 else 4 :=
  (show ∀ s : B, weight s = if s = 0 then 8 else if s = vertical then 0 else 4 from
    by decide +kernel) s

def cap (d : ℕ) : ℕ := if d = 0 then 8 else if d = 1 then 12 else if d = 2 then 20 else 32

noncomputable local instance {V : Type} [Finite V] [AddCommMonoid V] [Module F V]
    (U : Submodule F V) : Fintype U := Fintype.ofFinite U

noncomputable def blockSum (U : Submodule F B) (s : B) : ℕ := ∑ z : U, weight (s+z.val)

private theorem add_self_zero (s : B) : s+s = 0 := by
  funext v
  exact (show ∀ a : F, a+a = 0 from by decide +kernel) (s v)

private theorem vertical_ne_zero : vertical ≠ 0 := by decide +kernel

private theorem translated_eq (s z w : B) : s+z = w ↔ z = w+s := by
  constructor
  · intro h
    rw [← h]
    calc
      z = 0+z := (zero_add _).symm
      _ = (s+s)+z := by rw [add_self_zero]
      _ = (s+z)+s := by abel
  · intro h
    rw [h]
    calc
      s + (w+s) = w + (s+s) := by abel
      _ = w := by rw [add_self_zero, add_zero]

private theorem weight_cast (s : B) : (weight s : ℤ) =
    4 + (if s = 0 then 4 else 0) - (if s = vertical then 4 else 0) := by
  rw [weight_value]
  by_cases h0 : s = 0
  · subst s
    simp [vertical_ne_zero.symm]
  · by_cases hv : s = vertical <;> simp [h0, hv, vertical_ne_zero]

private theorem point_sum (U : Submodule F B) (b : B) (c : ℤ) :
    (∑ z : U, if z.val = b then c else 0) = if b ∈ U then c else 0 := by
  classical
  by_cases h : b ∈ U
  · rw [ite_eq_left h, Finset.sum_eq_single ⟨b,h⟩]
    · simp
    · intro z _ hz
      exact ite_eq_right (fun e => hz (Subtype.ext e))
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro z _
    apply ite_eq_right
    intro e
    apply h
    rw [← e]
    exact z.property

private theorem sum_formula (U : Submodule F B) (s : B) : (blockSum U s : ℤ) =
    4 * Nat.card U + (if s ∈ U then 4 else 0) - (if vertical+s ∈ U then 4 else 0) := by
  classical
  rw [blockSum, Nat.cast_sum]
  simp_rw [weight_cast, translated_eq, zero_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    point_sum]
  simp [Nat.card_eq_fintype_card, mul_comm]

theorem coset_le (U : Submodule F B) (s : B) : blockSum U s ≤ blockSum U 0 := by
  classical
  suffices hh : (blockSum U s : ℤ) ≤ (blockSum U 0 : ℤ) by exact_mod_cast hh
  rw [sum_formula, sum_formula]
  simp only [add_zero, U.zero_mem, ite_true]
  by_cases hv : vertical ∈ U
  · have he : vertical+s ∈ U ↔ s ∈ U := by
      constructor
      · intro h
        have hh := U.add_mem hv h
        rwa [← add_assoc, add_self_zero, zero_add] at hh
      · exact U.add_mem hv
    simp [hv, he]
  · by_cases h : s ∈ U <;> by_cases h' : vertical+s ∈ U <;> simp [hv, h, h']
    omega

theorem blockDim (U : Submodule F B) : Module.finrank F U ≤ 3 := by
  exact U.finrank_le.trans_eq (by simp [B])

private theorem card_of_dim (U : Submodule F B) : Nat.card U = 2 ^ Module.finrank F U := by
  rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_zmod]

theorem le_cap (U : Submodule F B) : blockSum U 0 ≤ cap (Module.finrank F U) := by
  classical
  have hd := blockDim U
  have he := sum_formula U 0
  simp only [add_zero, U.zero_mem, ite_true, card_of_dim, Nat.cast_pow, Nat.cast_ofNat] at he
  have hg : Module.finrank F B = 3 := by simp [B]
  interval_cases h : Module.finrank F U
  · by_cases hv : vertical ∈ U <;> norm_num [cap, hv] at he ⊢ <;> omega
  · by_cases hv : vertical ∈ U <;> norm_num [cap, hv] at he ⊢ <;> omega
  · by_cases hv : vertical ∈ U <;> norm_num [cap, hv] at he ⊢ <;> omega
  · have ht : U = ⊤ := Submodule.eq_top_of_finrank_eq (h.trans hg.symm)
    have hv : vertical ∈ U := ht.symm ▸ Submodule.mem_top
    norm_num [cap, hv] at he ⊢
    omega

private def pad (d : ℕ) : (Fin d → F) →ₗ[F] B where
  toFun x i := if hi : i.val < d then x ⟨i.val, hi⟩ else 0
  map_add' x y := by
    funext i
    by_cases hi : i.val < d <;> simp [hi]
  map_smul' c x := by
    funext i
    by_cases hi : i.val < d <;> simp [hi]

theorem attain (d : ℕ) (hd : d ≤ 3) : ∃ U : Submodule F B,
    Module.finrank F U = d ∧ blockSum U 0 = cap d := by
  classical
  let U := (pad d).range
  have hinj : Function.Injective (pad d) := by
    intro x y h
    funext i
    have e := congrFun h (Fin.castLE hd i)
    simpa [pad, i.isLt] using e
  have hdim : Module.finrank F U = d :=
    (LinearMap.finrank_range_of_inj hinj).trans (by simp)
  refine ⟨U, hdim, ?_⟩
  have eq := sum_formula U 0
  simp only [add_zero, U.zero_mem, ite_true, card_of_dim, hdim, Nat.cast_pow, Nat.cast_ofNat] at eq
  have noVert (hle : d < 3) : vertical ∉ U := by
    rintro ⟨x,hx⟩
    have e := congrFun hx (2 : Fin 3)
    have hn : ¬2 < d := by omega
    simp [pad, hn, vertical] at e
  interval_cases d
  · norm_num [cap, noVert (by omega)] at eq ⊢
    omega
  · norm_num [cap, noVert (by omega)] at eq ⊢
    omega
  · norm_num [cap, noVert (by omega)] at eq ⊢
    omega
  · have ht : U = ⊤ := Submodule.eq_top_of_finrank_eq (hdim.trans (by simp [B]))
    have hv : vertical ∈ U := ht.symm ▸ Submodule.mem_top
    norm_num [cap, hv] at eq ⊢
    omega

end Local403

namespace Project403

open scoped BigOperators

abbrev F := ZMod 2
abbrev B := Fin 3 → F

noncomputable local instance {V : Type} [AddCommGroup V] [Module F V] [Finite V]
    (S : Submodule F V) : Fintype S := Fintype.ofFinite S

noncomputable def blockDim (U : Submodule F B) : Fin 4 :=
  ⟨Module.finrank F U, by
    have hu := LinearMap.finrank_le_finrank_of_injective (f := U.subtype) Subtype.val_injective
    have hb : Module.finrank F B = 3 := by simp
    omega⟩

noncomputable def cosetSum (w : B → ℕ) (U : Submodule F B) (z : B) : ℕ :=
  ∑ u : U, w (z + u.val)

noncomputable def weightSum {r : ℕ} (w : B → ℕ) (S : Submodule F (Fin r → B)) : ℕ :=
  ∑ s : S, ∏ i, w (s.val i)

private theorem step {r : ℕ} (w : B → ℕ)
    (hcoset : ∀ (U : Submodule F B) z, cosetSum w U z ≤ cosetSum w U 0)
    (S : Submodule F (Fin (r+1) → B)) :
    ∃ (R : Submodule F (Fin r → B)) (U : Submodule F B),
      Module.finrank F R + Module.finrank F U = Module.finrank F S ∧
      weightSum w S ≤ cosetSum w U 0 * weightSum w R := by
  classical
  let T : S →ₗ[F] (Fin r → B) :=
    { toFun := fun s i => s.val i.succ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let H : T.ker →ₗ[F] B :=
    { toFun := fun s => s.val.val 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hH : Function.Injective H := by
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hh
    · have hx : T x.val = 0 := x.property
      have hy : T y.val = 0 := y.property
      exact congrFun (hx.trans hy.symm) j
  let R := LinearMap.range T
  let U := LinearMap.range H
  let e : T.ker ≃ₗ[F] U := LinearEquiv.ofInjective H hH
  refine ⟨R,U,?_,?_⟩
  · rw [← e.finrank_eq]
    exact T.finrank_range_add_finrank_ker
  · have preimage (y : R) : ∃ x : S, T x = y.val := y.property
    choose rep hrep using preimage
    let ry (x : S) : R := ⟨T x, LinearMap.mem_range_self T x⟩
    let E : R × T.ker ≃ S :=
      { toFun := fun p => rep p.1 + p.2.val
        invFun := fun x => (ry x, ⟨x - rep (ry x), by
          change T (x - rep (ry x)) = 0
          rw [map_sub, hrep]
          exact sub_self _⟩)
        left_inv := by
          rintro ⟨y,z⟩
          have hy : ry (rep y + z.val) = y := by
            apply Subtype.ext
            change T (rep y + z.val) = y.val
            rw [map_add, hrep, show T z.val = 0 from z.property, add_zero]
          apply Prod.ext
          · exact hy
          · apply Subtype.ext
            change rep y + z.val - rep (ry (rep y + z.val)) = z.val
            rw [hy, add_sub_cancel_left]
        right_inv := by
          intro x
          change rep (ry x) + (x - rep (ry x)) = x
          abel }
    have each (y : R) (z : T.ker) :
        (∏ i, w ((E (y,z)).val i)) =
          w ((rep y).val 0 + (e z).val) * ∏ i, w (y.val i) := by
      have head : (E (y,z)).val 0 = (rep y).val 0 + (e z).val := rfl
      have tail : (fun i : Fin r => (E (y,z)).val i.succ) = y.val := by
        change T (rep y + z.val) = y.val
        rw [map_add, hrep, show T z.val = 0 from z.property, add_zero]
      rw [Fin.prod_univ_succ, head]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [congrFun tail i]
    unfold weightSum
    calc
      _ = ∑ yz : R × T.ker, w ((rep yz.1).val 0 + (e yz.2).val) * ∏ i, w (yz.1.val i) :=
        (Fintype.sum_equiv E _ _ (fun yz => (each yz.1 yz.2).symm)).symm
      _ = ∑ y : R, cosetSum w U ((rep y).val 0) * ∏ i, w (y.val i) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro y _
        change (∑ z : T.ker, w ((rep y).val 0 + (e z).val) * ∏ i, w (y.val i)) =
          cosetSum w U ((rep y).val 0) * ∏ i, w (y.val i)
        rw [← Finset.sum_mul]
        congr 1
        exact Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)
      _ ≤ ∑ y : R, cosetSum w U 0 * ∏ i, w (y.val i) :=
        Finset.sum_le_sum (fun y _ => Nat.mul_le_mul_right _ (hcoset U _))
      _ = _ := by rw [Finset.mul_sum]

theorem bound {r : ℕ} (w : B → ℕ) (cap : Fin 4 → ℕ)
    (hcoset : ∀ (U : Submodule F B) z, cosetSum w U z ≤ cosetSum w U 0)
    (hcap : ∀ U, cosetSum w U 0 ≤ cap (blockDim U))
    (S : Submodule F (Fin r → B)) :
    ∃ d : Fin r → Fin 4, (∑ i, (d i).val) = Module.finrank F S ∧
      weightSum w S ≤ ∏ i, cap (d i) := by
  classical
  induction r with
  | zero =>
    have hr : Module.finrank F S = 0 := by
      have h := LinearMap.finrank_le_finrank_of_injective (f := S.subtype) Subtype.val_injective
      have hz : Module.finrank F (Fin 0 → B) = 0 := by
        rw [Module.finrank_pi_fintype]; simp
      omega
    refine ⟨Fin.elim0, by simp [hr], ?_⟩
    have : Unique S :=
      { default := 0
        uniq := fun x => Subtype.ext (by funext i; exact Fin.elim0 i) }
    simp [weightSum]
  | succ r ih =>
    obtain ⟨R,U,hrank,hsum⟩ := step w hcoset S
    obtain ⟨d,hd,hupper⟩ := ih R
    refine ⟨Fin.cons (blockDim U) d, ?_, ?_⟩
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      change Module.finrank F U + (∑ i, (d i).val) = Module.finrank F S
      omega
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact hsum.trans (Nat.mul_le_mul (hcap U) hupper)

end Project403

namespace Opt403

open scoped BigOperators

def cap : Fin 4 → ℕ := ![8, 12, 20, 32]

def best (r h : ℕ) : ℕ :=
  let a := (2*h)%3
  let b := (h-2*a)/3
  if h = 1 then 12*8^(r-1) else 20^a * 32^b * 8^(r-a-b)

private def value (n₀ n₁ n₂ n₃ : ℕ) : ℕ :=
  8^n₀ * 12^n₁ * 20^n₂ * 32^n₃

private theorem exchange11 (n₀ n₁ n₂ n₃ : ℕ) :
    value n₀ (n₁+2) n₂ n₃ ≤ value (n₀+1) n₁ (n₂+1) n₃ := by
  calc
    _ = value n₀ n₁ n₂ n₃ * 144 := by simp [value, pow_add]; ac_rfl
    _ ≤ value n₀ n₁ n₂ n₃ * 160 := Nat.mul_le_mul_left _ (by decide)
    _ = _ := by simp [value, pow_add]; ring

private theorem exchange12 (n₀ n₁ n₂ n₃ : ℕ) :
    value n₀ (n₁+1) (n₂+1) n₃ ≤ value (n₀+1) n₁ n₂ (n₃+1) := by
  calc
    _ = value n₀ n₁ n₂ n₃ * 240 := by simp [value, pow_add]; ring
    _ ≤ value n₀ n₁ n₂ n₃ * 256 := Nat.mul_le_mul_left _ (by decide)
    _ = _ := by simp [value, pow_add]; ring

private theorem exchange13 (n₀ n₁ n₂ n₃ : ℕ) :
    value n₀ (n₁+1) n₂ (n₃+1) ≤ value n₀ n₁ (n₂+2) n₃ := by
  calc
    _ = value n₀ n₁ n₂ n₃ * 384 := by simp [value, pow_add]; ring
    _ ≤ value n₀ n₁ n₂ n₃ * 400 := Nat.mul_le_mul_left _ (by decide)
    _ = _ := by simp [value, pow_add]; ring

private theorem exchange222 (n₀ n₁ n₂ n₃ : ℕ) :
    value n₀ n₁ (n₂+3) n₃ ≤ value (n₀+1) n₁ n₂ (n₃+2) := by
  calc
    _ = value n₀ n₁ n₂ n₃ * 8000 := by simp [value, pow_add]; ring
    _ ≤ value n₀ n₁ n₂ n₃ * 8192 := Nat.mul_le_mul_left _ (by decide)
    _ = _ := by simp [value, pow_add]; ring

private theorem count_bound (r h n₀ n₁ n₂ n₃ : ℕ)
    (hr : n₀+n₁+n₂+n₃=r) (hh : n₁+2*n₂+3*n₃=h) :
    value n₀ n₁ n₂ n₃ ≤ best r h := by
  by_cases h₁ : 2 ≤ n₁
  · obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le h₁
    rw [add_comm] at hq
    subst n₁
    exact (exchange11 n₀ q n₂ n₃).trans
      (count_bound r h (n₀+1) q (n₂+1) n₃ (by omega) (by omega))
  by_cases h₁' : n₁ = 1
  · subst n₁
    by_cases h₂ : n₂ = 0
    · subst n₂
      by_cases h₃ : n₃ = 0
      · subst n₃
        have eh : h=1 := by omega
        have er : r-1=n₀ := by omega
        rw [best, eh, ite_eq_left rfl, er]
        simp [value, mul_comm]
      · obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (show 1 ≤ n₃ by omega)
        rw [add_comm] at hq
        subst n₃
        exact (exchange13 n₀ 0 0 q).trans
          (count_bound r h n₀ 0 2 q (by omega) (by omega))
    · obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (show 1 ≤ n₂ by omega)
      rw [add_comm] at hq
      subst n₂
      exact (exchange12 n₀ 0 q n₃).trans
        (count_bound r h (n₀+1) 0 q (n₃+1) (by omega) (by omega))
  have h₀ : n₁=0 := by omega
  subst n₁
  by_cases h₂ : 3 ≤ n₂
  · obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le h₂
    rw [add_comm] at hq
    subst n₂
    exact (exchange222 n₀ 0 q n₃).trans
      (count_bound r h (n₀+1) 0 q (n₃+2) (by omega) (by omega))
  · have ha : (2*h)%3=n₂ := by omega
    have hb : (h-2*n₂)/3=n₃ := by omega
    have hz : r-n₂-n₃=n₀ := by omega
    have hn : h≠1 := by omega
    simp only [best, ite_eq_right hn, ha, hb, hz, value, pow_zero, mul_one]
    apply le_of_eq
    ac_rfl
termination_by 3*n₁+n₂
decreasing_by all_goals omega

private def count {r : ℕ} (d : Fin r → Fin 4) (x : Fin 4) : ℕ :=
  (Finset.univ.filter (fun i => d i = x)).card

private theorem sum_count {r : ℕ} (d : Fin r → Fin 4) (f : Fin 4 → ℕ) :
    (∑ i, f (d i)) = ∑ x, count d x * f x := by
  calc
    _ = ∑ i : Fin r, ∑ x : Fin 4, if d i = x then f x else 0 := by
      simp [Finset.sum_ite_eq]
    _ = ∑ x : Fin 4, ∑ i : Fin r, if d i = x then f x else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_filter]
      simp [count, Finset.sum_const]

private theorem product_count {r : ℕ} (d : Fin r → Fin 4) (f : Fin 4 → ℕ) :
    (∏ i, f (d i)) = ∏ x, f x ^ count d x := by
  calc
    _ = ∏ i : Fin r, ∏ x : Fin 4, if d i = x then f x else 1 := by
      simp [Finset.prod_ite_eq]
    _ = ∏ x : Fin 4, ∏ i : Fin r, if d i = x then f x else 1 := Finset.prod_comm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro x _
      rw [← Finset.prod_filter]
      simp [count, Finset.prod_const]

theorem bound {r h : ℕ} (d : Fin r → Fin 4) (hd : ∑ i, (d i).val = h) :
    (∏ i, cap (d i)) ≤ best r h := by
  have hr := sum_count d (fun _ => 1)
  have hh := sum_count d Fin.val
  rw [hd] at hh
  norm_num [Fin.sum_univ_succ, Finset.sum_const, nsmul_eq_mul] at hr hh
  have hb := count_bound r h (count d 0) (count d 1) (count d 2) (count d 3)
    (by omega) (by omega)
  rw [product_count]
  simpa [value, cap, Fin.prod_univ_succ, mul_assoc] using hb

private def blocks (n₀ n₁ n₂ n₃ : ℕ) : Fin (n₀+n₁+n₂+n₃) → Fin 4 :=
  Fin.addCases (Fin.addCases (Fin.addCases (fun _ => 0) (fun _ => 1)) (fun _ => 2)) (fun _ => 3)

private theorem blocks_sum (n₀ n₁ n₂ n₃ : ℕ) :
    (∑ i, (blocks n₀ n₁ n₂ n₃ i).val) = n₁ + 2*n₂ + 3*n₃ := by
  norm_num [blocks, Fin.sum_univ_add, Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]

private theorem blocks_prod (n₀ n₁ n₂ n₃ : ℕ) :
    (∏ i, cap (blocks n₀ n₁ n₂ n₃ i)) = value n₀ n₁ n₂ n₃ := by
  norm_num [blocks, Fin.prod_univ_add, cap, value, Finset.prod_const]

private theorem vector_of_counts {r h n₀ n₁ n₂ n₃ : ℕ}
    (hr : n₀+n₁+n₂+n₃=r) (hh : n₁+2*n₂+3*n₃=h) :
    ∃ d : Fin r → Fin 4, (∑ i, (d i).val) = h ∧ (∏ i, cap (d i)) = value n₀ n₁ n₂ n₃ := by
  subst r
  exact ⟨blocks n₀ n₁ n₂ n₃, (blocks_sum _ _ _ _).trans hh, blocks_prod _ _ _ _⟩

theorem attain (r h : ℕ) (hr : h ≤ 3*r) :
    ∃ d : Fin r → Fin 4, (∑ i, (d i).val) = h ∧ (∏ i, cap (d i)) = best r h := by
  by_cases h₁ : h=1
  · obtain ⟨d, hd, hv⟩ := vector_of_counts (n₀ := r-1) (n₁ := 1) (n₂ := 0) (n₃ := 0)
      (r := r) (h := h) (by omega) (by omega)
    exact ⟨d, hd, by rw [hv]; simp [best, h₁, value, mul_comm]⟩
  · let a := (2*h)%3
    let b := (h-2*a)/3
    have ha : a < 3 := Nat.mod_lt _ (by decide)
    have hb : 2*a+3*b=h := by dsimp [a,b]; omega
    have hab : a+b≤r := by omega
    obtain ⟨d, hd, hv⟩ := vector_of_counts (n₀ := r-a-b) (n₁ := 0) (n₂ := a) (n₃ := b)
      (r := r) (h := h) (by omega) (by omega)
    refine ⟨d, hd, hv.trans ?_⟩
    simp only [best, ite_eq_right h₁, value, pow_zero, mul_one]
    change _ = 20^a * 32^b * 8^(r-a-b)
    ac_rfl

end Opt403

namespace Counting403

abbrev F := ZMod 2
abbrev B := Fin 3 → F

noncomputable def measure {r : ℕ} (weight : B → ℕ) (S : Submodule F (Fin r → B)) : ℕ := by
  letI : Fintype (↥S) := Fintype.ofFinite _
  exact ∑ s : S, ∏ i : Fin r, weight (s.val i)

noncomputable def blockMeasure (weight : B → ℕ) (U : Submodule F B) : ℕ := by
  letI : Fintype (↥U) := Fintype.ofFinite _
  exact ∑ z : U, weight z.val

theorem coll_factor {r : ℕ} (mask : B → F) (weight : B → ℕ)
    (hw : ∀ s, weight s = Nat.card {x : B // mask x = mask (x+s)})
    (S : Submodule F (Fin r → B)) :
    Nat.card {p : (Fin r → B) × (Fin r → B) //
      p.2 ∈ S ∧ (fun i => mask (p.1 i)) = fun i => mask ((p.1+p.2) i)} =
        measure weight S := by
  classical
  letI : Fintype (↥S) := Fintype.ofFinite _
  let e : {p : (Fin r → B) × (Fin r → B) //
      p.2 ∈ S ∧ (fun i => mask (p.1 i)) = fun i => mask ((p.1+p.2) i)} ≃
      (Σ s : S, ∀ i : Fin r, {x : B // mask x = mask (x+s.val i)}) :=
    { toFun := fun p => ⟨⟨p.val.2,p.property.1⟩, fun i => ⟨p.val.1 i, congrFun p.property.2 i⟩⟩
      invFun := fun p => ⟨(fun i => (p.2 i).val,p.1.val),p.1.property,funext fun i => (p.2 i).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma, measure]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [hw, Nat.card_eq_fintype_card]

theorem product_space {r : ℕ} (weight : B → ℕ) (U : Fin r → Submodule F B) :
    ∃ S : Submodule F (Fin r → B),
      Module.finrank F S = ∑ i, Module.finrank F (U i) ∧
      measure weight S = ∏ i : Fin r, blockMeasure weight (U i) := by
  classical
  let S := Submodule.pi (Set.univ : Set (Fin r)) U
  letI : Fintype (↥S) := Fintype.ofFinite _
  letI (i : Fin r) : Fintype (↥(U i)) := Fintype.ofFinite _
  let e : S ≃ₗ[F] (∀ i : Fin r, U i) :=
    { toFun := fun x i => ⟨x.val i, x.property i (Set.mem_univ i)⟩
      invFun := fun x => ⟨fun i => (x i).val, fun i _ => (x i).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨S, e.finrank_eq.trans (Module.finrank_pi_fintype F), ?_⟩
  unfold measure blockMeasure
  calc
    _ = ∑ z : (∀ i : Fin r, U i), ∏ i : Fin r, weight (z i).val :=
      Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)
    _ = _ := (Fintype.prod_sum (fun (i : Fin r) (z : U i) => weight z.val)).symm

end Counting403

end PEqualNP.Outside.L_pcx_403

open PEqualNP.Outside.L_pcx_403

theorem PEqualNP.Outside.L_pcx_403 :
    ∀ (r h : ℕ) (_ : h ≤ 3*r),
      let F := ZMod 2
      let X := Fin r → Fin 3 → F
      let Y := Fin r → F
      let target := fun (z : X) (i : Fin r) => z i 2 + z i 0 * z i 1
      let a := (2*h)%3
      let b := (h-2*a)/3
      let best := if h = 1 then 12*8^(r-1) else 20^a * 32^b * 8^(r-a-b)
      ∀ K : ℕ,
        (∃ S : Submodule F X, Module.finrank F S = h ∧
          K ≤ Nat.card {p : X × X // p.2 ∈ S ∧ target p.1 = target (p.1+p.2)}) ↔ K ≤ best := by
  classical
  intro r h hr
  dsimp only
  intro K
  let count (S : Submodule (ZMod 2) (Fin r → Local403.B)) :=
    Nat.card {p : (Fin r → Local403.B) × (Fin r → Local403.B) //
      p.2 ∈ S ∧ (fun i => Local403.mask (p.1 i)) =
        fun i => Local403.mask ((p.1 + p.2) i)}
  change (∃ S : Submodule (ZMod 2) (Fin r → Local403.B),
    Module.finrank (ZMod 2) S = h ∧ K ≤ count S) ↔ K ≤ Opt403.best r h
  have hcount (S : Submodule (ZMod 2) (Fin r → Local403.B)) :
      count S = Counting403.measure Local403.weight S :=
    Counting403.coll_factor Local403.mask Local403.weight Local403.weight_card S
  have matching (i : Fin 4) : Local403.cap i.val = Opt403.cap i := by
    fin_cases i <;> decide
  constructor
  · rintro ⟨S, hS, hK⟩
    obtain ⟨d, hd, hp⟩ := Project403.bound Local403.weight (fun i => Local403.cap i.val)
      Local403.coset_le Local403.le_cap S
    rw [hS] at hd
    rw [hcount] at hK
    have hh : Counting403.measure Local403.weight S ≤ ∏ i, Opt403.cap (d i) := by
      change Project403.weightSum Local403.weight S ≤ _
      simpa only [matching] using hp
    exact hK.trans (hh.trans (Opt403.bound d hd))
  · intro hK
    obtain ⟨d, hd, hopt⟩ := Opt403.attain r h hr
    have each (i : Fin r) : ∃ U : Submodule (ZMod 2) Local403.B,
        Module.finrank (ZMod 2) U = (d i).val ∧
        Local403.blockSum U 0 = Local403.cap (d i).val :=
      Local403.attain (d i).val (by have hi := (d i).isLt; omega)
    choose U hU hs using each
    obtain ⟨S, hS, hm⟩ := Counting403.product_space Local403.weight U
    refine ⟨S, hS.trans (by simpa only [hU] using hd), ?_⟩
    have hblock (i : Fin r) : Counting403.blockMeasure Local403.weight (U i) = Opt403.cap (d i) := by
      rw [← matching]
      simpa only [Counting403.blockMeasure, Local403.blockSum, zero_add] using hs i
    rw [hcount, hm]
    simpa only [hblock, hopt] using hK

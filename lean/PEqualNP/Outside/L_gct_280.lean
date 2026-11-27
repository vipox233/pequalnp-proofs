import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_280_aux

noncomputable section

abbrev V3 := Fin 3 → ℂ
abbrev Triple := V3 × V3 × V3

def had (u : V3) : Fin 4 → ℂ :=
  ![u 0 + u 1 + u 2, u 0 - u 1 - u 2, -u 0 + u 1 - u 2, -u 0 - u 1 + u 2]

def invHad (v : Fin 4 → ℂ) : V3 :=
  ![(v 0 + v 1) / 2, (v 0 + v 2) / 2, (v 0 + v 3) / 2]

theorem had_invHad (v : Fin 4 → ℂ) (hv : (∑ i : Fin 4, v i) = 0) :
    had (invHad v) = v := by
  rw [Fin.sum_univ_four] at hv
  funext i
  fin_cases i
  · change (v 0 + v 1) / 2 + (v 0 + v 2) / 2 + (v 0 + v 3) / 2 = v 0
    linear_combination hv / 2
  · change (v 0 + v 1) / 2 - (v 0 + v 2) / 2 - (v 0 + v 3) / 2 = v 1
    linear_combination -hv / 2
  · change -((v 0 + v 1) / 2) + (v 0 + v 2) / 2 - (v 0 + v 3) / 2 = v 2
    linear_combination -hv / 2
  · change -((v 0 + v 1) / 2) - (v 0 + v 2) / 2 + (v 0 + v 3) / 2 = v 3
    linear_combination -hv / 2

def toTriple : (Fin 3 → Fin 4 → ℂ) →ₗ[ℂ] Triple where
  toFun X := (invHad (X 0), invHad (X 1), invHad (X 2))
  map_add' X Y := by
    ext i <;> fin_cases i <;> simp [invHad] <;> ring
  map_smul' c X := by
    ext i <;> fin_cases i <;> simp [invHad] <;> ring

theorem toTriple_inj_on_zeroSum {X Y : Fin 3 → Fin 4 → ℂ}
    (hX : ∀ r : Fin 3, (∑ i : Fin 4, X r i) = 0)
    (hY : ∀ r : Fin 3, (∑ i : Fin 4, Y r i) = 0)
    (heq : toTriple X = toTriple Y) : X = Y := by
  funext r
  have h1 : invHad (X r) = invHad (Y r) := by
    fin_cases r
    · exact congrArg Prod.fst heq
    · exact congrArg (fun p => p.2.1) heq
    · exact congrArg (fun p => p.2.2) heq
  rw [← had_invHad (X r) (hX r), ← had_invHad (Y r) (hY r), h1]

def c1 (a : ℕ) : ℤ := if a % 5 = 0 then 5 else 0
def c2 (a b : ℕ) : ℤ := c1 a * c1 b - c1 (a + b)
def c3 (a b c : ℕ) : ℤ := c2 a b * c1 c - c2 (a + c) b - c2 a (b + c)
def c4 (a b c d : ℕ) : ℤ := c3 a b c * c1 d - c3 (a + d) b c - c3 a (b + d) c - c3 a b (c + d)

def S1 (ζ : ℂ) (a : ℕ) : ℂ := ∑ x0 : Fin 5, ζ ^ (a * x0.val)

def S2 (ζ : ℂ) (a b : ℕ) : ℂ :=
  ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ζ ^ (a * x0.val + b * x1.val)

def S3 (ζ : ℂ) (a b c : ℕ) : ℂ :=
  ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
    ζ ^ (a * x0.val + b * x1.val + c * x2.val)

def S4 (ζ : ℂ) (a b c d : ℕ) : ℂ :=
  ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
    ∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
      ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val)

theorem S1_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) : S1 ζ a = (c1 a : ℂ) := by
  unfold S1 c1
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  by_cases hmod : a % 5 = 0
  · simp only [hmod, ↓reduceIte, Int.cast_ofNat]
    have hdvd : 5 ∣ a := Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨q, rfl⟩ := hdvd
    have hterm : ∀ x : Fin 5, ζ ^ (5 * q * x.val) = 1 := by
      intro x
      rw [show 5 * q * x.val = 5 * (q * x.val) by ring, pow_mul, h5, one_pow]
    simp [hterm]
  · simp only [hmod, ↓reduceIte, Int.cast_zero]
    have hne : ζ ^ a ≠ 1 := by
      intro h1
      have hdvd : 5 ∣ a := hζ.pow_eq_one_iff_dvd a |>.mp h1
      exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
    have hmul : (ζ ^ a - 1) * (∑ x0 : Fin 5, ζ ^ (a * x0.val)) = 0 := by
      rw [Fin.sum_univ_five]
      have hpow : ∀ k : ℕ, ζ ^ (a * k) = (ζ ^ a) ^ k := fun k => pow_mul ζ a k
      have hv3 : (3 : Fin 5).val = 3 := rfl
      have hv4 : (4 : Fin 5).val = 4 := rfl
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, hv3, hv4, hpow]
      have h5a : (ζ ^ a) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h5, one_pow]
      linear_combination h5a
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)

theorem S2_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a b : ℕ) : S2 ζ a b = (c2 a b : ℂ) := by
  unfold S2 c2
  have hinner : ∀ x0 : Fin 5,
      (∑ x1 ∈ Finset.univ.erase x0, ζ ^ (a * x0.val + b * x1.val)) =
      ζ ^ (a * x0.val) * S1 ζ b - ζ ^ ((a + b) * x0.val) := by
    intro x0
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ x0)]
    have hsplit : (∑ x1 : Fin 5, ζ ^ (a * x0.val + b * x1.val)) = ζ ^ (a * x0.val) * S1 ζ b := by
      rw [S1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x1 _ => ?_
      rw [pow_add]
    rw [hsplit, add_mul]
  simp_rw [hinner, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change S1 ζ a * S1 ζ b - S1 ζ (a + b) = _
  rw [S1_eq hζ, S1_eq hζ, S1_eq hζ]
  push_cast
  rfl

theorem S3_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a b c : ℕ) : S3 ζ a b c = (c3 a b c : ℂ) := by
  have hinner : ∀ x0 : Fin 5, ∀ x1 ∈ Finset.univ.erase x0,
      (∑ x2 ∈ (Finset.univ.erase x0).erase x1, ζ ^ (a * x0.val + b * x1.val + c * x2.val)) =
      ζ ^ (a * x0.val + b * x1.val) * S1 ζ c -
      ζ ^ ((a + c) * x0.val + b * x1.val) -
      ζ ^ (a * x0.val + (b + c) * x1.val) := by
    intro x0 x1 hx1
    rw [Finset.sum_erase_eq_sub hx1, Finset.sum_erase_eq_sub (Finset.mem_univ x0)]
    have hsplit : (∑ x2 : Fin 5, ζ ^ (a * x0.val + b * x1.val + c * x2.val)) =
        ζ ^ (a * x0.val + b * x1.val) * S1 ζ c := by
      rw [S1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x2 _ => ?_
      rw [pow_add]
    rw [hsplit]
    have h1 : a * x0.val + b * x1.val + c * x0.val = (a + c) * x0.val + b * x1.val := by ring
    have h2 : a * x0.val + b * x1.val + c * x1.val = a * x0.val + (b + c) * x1.val := by ring
    rw [h1, h2]
  have hsum : S3 ζ a b c = S2 ζ a b * S1 ζ c - S2 ζ (a + c) b - S2 ζ a (b + c) := by
    unfold S3 S2
    calc (∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0,
            ∑ x2 ∈ (Finset.univ.erase x0).erase x1, ζ ^ (a * x0.val + b * x1.val + c * x2.val))
        = ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0,
            (ζ ^ (a * x0.val + b * x1.val) * S1 ζ c -
             ζ ^ ((a + c) * x0.val + b * x1.val) -
             ζ ^ (a * x0.val + (b + c) * x1.val)) := by
          refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 hx1 => hinner x0 x1 hx1
      _ = _ := by
          simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsum, S2_eq hζ, S2_eq hζ, S2_eq hζ, S1_eq hζ]
  unfold c3
  push_cast
  rfl

theorem S4_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a b c d : ℕ) : S4 ζ a b c d = (c4 a b c d : ℂ) := by
  have hinner : ∀ x0 : Fin 5, ∀ x1 ∈ Finset.univ.erase x0, ∀ x2 ∈ (Finset.univ.erase x0).erase x1,
      (∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
        ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val)) =
      ζ ^ (a * x0.val + b * x1.val + c * x2.val) * S1 ζ d -
      ζ ^ ((a + d) * x0.val + b * x1.val + c * x2.val) -
      ζ ^ (a * x0.val + (b + d) * x1.val + c * x2.val) -
      ζ ^ (a * x0.val + b * x1.val + (c + d) * x2.val) := by
    intro x0 x1 hx1 x2 hx2
    rw [Finset.sum_erase_eq_sub hx2, Finset.sum_erase_eq_sub hx1, Finset.sum_erase_eq_sub (Finset.mem_univ x0)]
    have hsplit : (∑ x3 : Fin 5, ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val)) =
        ζ ^ (a * x0.val + b * x1.val + c * x2.val) * S1 ζ d := by
      rw [S1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x3 _ => ?_
      rw [pow_add]
    rw [hsplit]
    have h1 : a * x0.val + b * x1.val + c * x2.val + d * x0.val = (a + d) * x0.val + b * x1.val + c * x2.val := by ring
    have h2 : a * x0.val + b * x1.val + c * x2.val + d * x1.val = a * x0.val + (b + d) * x1.val + c * x2.val := by ring
    have h3 : a * x0.val + b * x1.val + c * x2.val + d * x2.val = a * x0.val + b * x1.val + (c + d) * x2.val := by ring
    rw [h1, h2, h3]
  have hsum : S4 ζ a b c d = S3 ζ a b c * S1 ζ d - S3 ζ (a + d) b c - S3 ζ a (b + d) c - S3 ζ a b (c + d) := by
    unfold S4 S3
    calc (∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
            ∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
              ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val))
        = ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
            (ζ ^ (a * x0.val + b * x1.val + c * x2.val) * S1 ζ d -
             ζ ^ ((a + d) * x0.val + b * x1.val + c * x2.val) -
             ζ ^ (a * x0.val + (b + d) * x1.val + c * x2.val) -
             ζ ^ (a * x0.val + b * x1.val + (c + d) * x2.val)) := by
          refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 hx1 =>
            Finset.sum_congr rfl fun x2 hx2 => hinner x0 x1 hx1 x2 hx2
      _ = _ := by
          simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsum, S3_eq hζ, S3_eq hζ, S3_eq hζ, S3_eq hζ, S1_eq hζ]
  unfold c4
  push_cast
  rfl

theorem sum_emb_eq_S4 (ζ : ℂ) (a b c d : ℕ) :
    (∑ f : Fin 4 ↪ Fin 5, ζ ^ (a * (f 0).val + b * (f 1).val + c * (f 2).val + d * (f 3).val)) =
    S4 ζ a b c d := by
  unfold S4
  let Q : Finset (Σ x0 : Fin 5, Σ x1 : Fin 5, Σ x2 : Fin 5, Fin 5) :=
    Finset.univ.sigma fun x0 => (Finset.univ.erase x0).sigma fun x1 =>
      ((Finset.univ.erase x0).erase x1).sigma fun x2 => (((Finset.univ.erase x0).erase x1).erase x2)
  have hQ : (∑ p ∈ Q, ζ ^ (a * p.1.val + b * p.2.1.val + c * p.2.2.1.val + d * p.2.2.2.val)) =
      ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
        ∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
          ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val) := by
    simp only [Q, Finset.sum_sigma]
  rw [← hQ]
  refine Finset.sum_bij (fun f _ => ⟨f 0, f 1, f 2, f 3⟩) ?_ ?_ ?_ ?_
  · intro f _
    simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase, and_true, true_and]
    refine ⟨f.injective.ne (by decide : (1 : Fin 4) ≠ 0),
      ⟨f.injective.ne (by decide : (2 : Fin 4) ≠ 1), f.injective.ne (by decide : (2 : Fin 4) ≠ 0)⟩,
      f.injective.ne (by decide : (3 : Fin 4) ≠ 2),
      f.injective.ne (by decide : (3 : Fin 4) ≠ 1),
      f.injective.ne (by decide : (3 : Fin 4) ≠ 0)⟩
  · intro f _ g _ heq
    apply Function.Embedding.ext
    intro i
    have h0 : f 0 = g 0 := congrArg Sigma.fst heq
    have h1 : f 1 = g 1 :=
      congrArg (fun p : Σ _ : Fin 5, Σ _ : Fin 5, Σ _ : Fin 5, Fin 5 => p.2.1) heq
    have h2 : f 2 = g 2 :=
      congrArg (fun p : Σ _ : Fin 5, Σ _ : Fin 5, Σ _ : Fin 5, Fin 5 => p.2.2.1) heq
    have h3 : f 3 = g 3 :=
      congrArg (fun p : Σ _ : Fin 5, Σ _ : Fin 5, Σ _ : Fin 5, Fin 5 => p.2.2.2) heq
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro p hp
    simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase, and_true, true_and] at hp
    rcases p with ⟨x0, x1, x2, x3⟩
    rcases hp with ⟨h10, ⟨h21, h20⟩, h32, h31, h30⟩
    have hinj : Function.Injective ![x0, x1, x2, x3] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
        | rfl
        | exact absurd hij h10 | exact absurd hij.symm h10
        | exact absurd hij h20 | exact absurd hij.symm h20
        | exact absurd hij h21 | exact absurd hij.symm h21
        | exact absurd hij h30 | exact absurd hij.symm h30
        | exact absurd hij h31 | exact absurd hij.symm h31
        | exact absurd hij h32 | exact absurd hij.symm h32
    refine ⟨⟨![x0, x1, x2, x3], hinj⟩, Finset.mem_univ _, rfl⟩
  · intro f _
    rfl

def dot3 (u v : V3) : ℂ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def C3 (u : V3) : V3 := ![u 1 * u 2, u 2 * u 0, u 0 * u 1]

def D3 (u : V3) : V3 :=
  ![u 0 * (u 0 ^ 2 - u 1 ^ 2 - u 2 ^ 2),
    u 1 * (u 1 ^ 2 - u 0 ^ 2 - u 2 ^ 2),
    u 2 * (u 2 ^ 2 - u 0 ^ 2 - u 1 ^ 2)]

def Q2 (y z : V3) : ℂ := dot3 y z

def Q3 (x y z : V3) : ℂ := dot3 z (C3 x) + dot3 x (C3 y)

def R4 (y z : V3) : ℂ :=
  120 * (y 0 ^ 2 * z 0 ^ 2 + y 1 ^ 2 * z 1 ^ 2 + y 2 ^ 2 * z 2 ^ 2) -
  40 * (y 0 ^ 2 * z 1 ^ 2 + y 0 ^ 2 * z 2 ^ 2 + y 1 ^ 2 * z 0 ^ 2 +
        y 1 ^ 2 * z 2 ^ 2 + y 2 ^ 2 * z 0 ^ 2 + y 2 ^ 2 * z 1 ^ 2) -
  160 * (y 0 * y 1 * z 0 * z 1 + y 1 * y 2 * z 1 * z 2 + y 2 * y 0 * z 2 * z 0)

def P4 (x y z : V3) : ℂ :=
  -120 * dot3 y (D3 x) - 120 * dot3 x (D3 z) + R4 y z

theorem sum_c4_a0 (R : Fin 4 → Fin 4 → ℂ) :
    (∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
      R 0 0 * R b 1 * R c 2 * R d 3 * (c4 0 b.val c.val d.val : ℂ)) =
    (120 : ℂ) * (R 0 0 * R 0 1 * R 0 2 * R 0 3) +
    (-30 : ℂ) * (R 0 0 * R 0 1 * R 2 2 * R 3 3) +
    (-30 : ℂ) * (R 0 0 * R 0 1 * R 3 2 * R 2 3) +
    (20 : ℂ) * (R 0 0 * R 1 1 * R 1 2 * R 3 3) +
    (20 : ℂ) * (R 0 0 * R 1 1 * R 2 2 * R 2 3) +
    (20 : ℂ) * (R 0 0 * R 1 1 * R 3 2 * R 1 3) +
    (-30 : ℂ) * (R 0 0 * R 2 1 * R 0 2 * R 3 3) +
    (20 : ℂ) * (R 0 0 * R 2 1 * R 1 2 * R 2 3) +
    (20 : ℂ) * (R 0 0 * R 2 1 * R 2 2 * R 1 3) +
    (-30 : ℂ) * (R 0 0 * R 2 1 * R 3 2 * R 0 3) +
    (-30 : ℂ) * (R 0 0 * R 3 1 * R 0 2 * R 2 3) +
    (20 : ℂ) * (R 0 0 * R 3 1 * R 1 2 * R 1 3) +
    (-30 : ℂ) * (R 0 0 * R 3 1 * R 2 2 * R 0 3) := by
  simp only [Fin.sum_univ_four]
  norm_num [c4, c3, c2, c1]
  ring

theorem sum_c4_a1 (R : Fin 4 → Fin 4 → ℂ) :
    (∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
      R 1 0 * R b 1 * R c 2 * R d 3 * (c4 1 b.val c.val d.val : ℂ)) =
    (20 : ℂ) * (R 1 0 * R 0 1 * R 1 2 * R 3 3) +
    (20 : ℂ) * (R 1 0 * R 0 1 * R 2 2 * R 2 3) +
    (20 : ℂ) * (R 1 0 * R 0 1 * R 3 2 * R 1 3) +
    (20 : ℂ) * (R 1 0 * R 1 1 * R 0 2 * R 3 3) +
    (-30 : ℂ) * (R 1 0 * R 1 1 * R 1 2 * R 2 3) +
    (-30 : ℂ) * (R 1 0 * R 1 1 * R 2 2 * R 1 3) +
    (20 : ℂ) * (R 1 0 * R 1 1 * R 3 2 * R 0 3) +
    (20 : ℂ) * (R 1 0 * R 2 1 * R 0 2 * R 2 3) +
    (-30 : ℂ) * (R 1 0 * R 2 1 * R 1 2 * R 1 3) +
    (20 : ℂ) * (R 1 0 * R 2 1 * R 2 2 * R 0 3) +
    (20 : ℂ) * (R 1 0 * R 3 1 * R 0 2 * R 1 3) +
    (20 : ℂ) * (R 1 0 * R 3 1 * R 1 2 * R 0 3) +
    (-30 : ℂ) * (R 1 0 * R 3 1 * R 3 2 * R 3 3) := by
  simp only [Fin.sum_univ_four]
  norm_num [c4, c3, c2, c1]
  ring

theorem sum_c4_a2 (R : Fin 4 → Fin 4 → ℂ) :
    (∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
      R 2 0 * R b 1 * R c 2 * R d 3 * (c4 2 b.val c.val d.val : ℂ)) =
    (-30 : ℂ) * (R 2 0 * R 0 1 * R 0 2 * R 3 3) +
    (20 : ℂ) * (R 2 0 * R 0 1 * R 1 2 * R 2 3) +
    (20 : ℂ) * (R 2 0 * R 0 1 * R 2 2 * R 1 3) +
    (-30 : ℂ) * (R 2 0 * R 0 1 * R 3 2 * R 0 3) +
    (20 : ℂ) * (R 2 0 * R 1 1 * R 0 2 * R 2 3) +
    (-30 : ℂ) * (R 2 0 * R 1 1 * R 1 2 * R 1 3) +
    (20 : ℂ) * (R 2 0 * R 1 1 * R 2 2 * R 0 3) +
    (20 : ℂ) * (R 2 0 * R 2 1 * R 0 2 * R 1 3) +
    (20 : ℂ) * (R 2 0 * R 2 1 * R 1 2 * R 0 3) +
    (20 : ℂ) * (R 2 0 * R 2 1 * R 3 2 * R 3 3) +
    (-30 : ℂ) * (R 2 0 * R 3 1 * R 0 2 * R 0 3) +
    (20 : ℂ) * (R 2 0 * R 3 1 * R 2 2 * R 3 3) +
    (20 : ℂ) * (R 2 0 * R 3 1 * R 3 2 * R 2 3) := by
  simp only [Fin.sum_univ_four]
  norm_num [c4, c3, c2, c1]
  ring

theorem sum_c4_a3 (R : Fin 4 → Fin 4 → ℂ) :
    (∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
      R 3 0 * R b 1 * R c 2 * R d 3 * (c4 3 b.val c.val d.val : ℂ)) =
    (-30 : ℂ) * (R 3 0 * R 0 1 * R 0 2 * R 2 3) +
    (20 : ℂ) * (R 3 0 * R 0 1 * R 1 2 * R 1 3) +
    (-30 : ℂ) * (R 3 0 * R 0 1 * R 2 2 * R 0 3) +
    (20 : ℂ) * (R 3 0 * R 1 1 * R 0 2 * R 1 3) +
    (20 : ℂ) * (R 3 0 * R 1 1 * R 1 2 * R 0 3) +
    (-30 : ℂ) * (R 3 0 * R 1 1 * R 3 2 * R 3 3) +
    (-30 : ℂ) * (R 3 0 * R 2 1 * R 0 2 * R 0 3) +
    (20 : ℂ) * (R 3 0 * R 2 1 * R 2 2 * R 3 3) +
    (20 : ℂ) * (R 3 0 * R 2 1 * R 3 2 * R 2 3) +
    (-30 : ℂ) * (R 3 0 * R 3 1 * R 1 2 * R 3 3) +
    (20 : ℂ) * (R 3 0 * R 3 1 * R 2 2 * R 2 3) +
    (-30 : ℂ) * (R 3 0 * R 3 1 * R 3 2 * R 1 3) := by
  simp only [Fin.sum_univ_four]
  norm_num [c4, c3, c2, c1]
  ring

theorem permSum_had {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (x y z : V3) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
      (1 + had x i * ζ ^ (f i).val + had y i * ζ ^ (2 * (f i).val) +
        had z i * ζ ^ (3 * (f i).val))) =
    120 + 120 * Q2 y z + 160 * Q3 x y z + P4 x y z := by
  let R : Fin 4 → Fin 4 → ℂ := ![fun _ => 1, had x, had y, had z]
  have hfactor : ∀ f : Fin 4 ↪ Fin 5,
      (∏ i : Fin 4, (1 + had x i * ζ ^ (f i).val + had y i * ζ ^ (2 * (f i).val) +
        had z i * ζ ^ (3 * (f i).val))) =
      ∑ g : Fin 4 → Fin 4,
        (∏ i : Fin 4, R (g i) i) *
        ζ ^ ((g 0).val * (f 0).val + (g 1).val * (f 1).val +
             (g 2).val * (f 2).val + (g 3).val * (f 3).val) := by
    intro f
    have hrow : ∀ i : Fin 4,
        1 + had x i * ζ ^ (f i).val + had y i * ζ ^ (2 * (f i).val) +
          had z i * ζ ^ (3 * (f i).val) =
        ∑ k : Fin 4, R k i * ζ ^ (k.val * (f i).val) := by
      intro i
      rw [Fin.sum_univ_four]
      simp [R]
    simp_rw [hrow]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.prod_mul_distrib, Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [pow_add, mul_assoc]
  simp_rw [hfactor]
  rw [Finset.sum_comm]
  have hstep : ∀ g : Fin 4 → Fin 4,
      (∑ f : Fin 4 ↪ Fin 5, (∏ i : Fin 4, R (g i) i) *
        ζ ^ ((g 0).val * (f 0).val + (g 1).val * (f 1).val +
             (g 2).val * (f 2).val + (g 3).val * (f 3).val)) =
      R (g 0) 0 * R (g 1) 1 * R (g 2) 2 * R (g 3) 3 *
        (c4 (g 0).val (g 1).val (g 2).val (g 3).val : ℂ) := by
    intro g
    rw [← Finset.mul_sum, sum_emb_eq_S4, S4_eq hζ, Fin.prod_univ_four]
  simp_rw [hstep]
  have hfun : (∑ g : Fin 4 → Fin 4,
      R (g 0) 0 * R (g 1) 1 * R (g 2) 2 * R (g 3) 3 *
        (c4 (g 0).val (g 1).val (g 2).val (g 3).val : ℂ)) =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        R a 0 * R b 1 * R c 2 * R d 3 * (c4 a.val b.val c.val d.val : ℂ) := by
    let e : (Fin 4 → Fin 4) ≃ Fin 4 × Fin 4 × Fin 4 × Fin 4 :=
      { toFun := fun g => (g 0, g 1, g 2, g 3)
        invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
        left_inv := fun g => by funext i; fin_cases i <;> rfl
        right_inv := fun ⟨a, b, c, d⟩ => rfl }
    have he := Fintype.sum_equiv e
      (fun g => R (g 0) 0 * R (g 1) 1 * R (g 2) 2 * R (g 3) 3 *
        (c4 (g 0).val (g 1).val (g 2).val (g 3).val : ℂ))
      (fun p => R p.1 0 * R p.2.1 1 * R p.2.2.1 2 * R p.2.2.2 3 *
        (c4 p.1.val p.2.1.val p.2.2.1.val p.2.2.2.val : ℂ))
      (fun _ => rfl)
    simpa only [Fintype.sum_prod_type] using he
  rw [hfun, Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two]
  have hval3 : (3 : Fin 4).val = 3 := rfl
  rw [hval3, sum_c4_a0, sum_c4_a1, sum_c4_a2, sum_c4_a3]
  have hdeg2 :
      (-30 : ℂ) * (R 0 0 * R 0 1 * R 2 2 * R 3 3) +
      (-30 : ℂ) * (R 0 0 * R 0 1 * R 3 2 * R 2 3) +
      (-30 : ℂ) * (R 0 0 * R 2 1 * R 0 2 * R 3 3) +
      (-30 : ℂ) * (R 0 0 * R 2 1 * R 3 2 * R 0 3) +
      (-30 : ℂ) * (R 0 0 * R 3 1 * R 0 2 * R 2 3) +
      (-30 : ℂ) * (R 0 0 * R 3 1 * R 2 2 * R 0 3) +
      (-30 : ℂ) * (R 2 0 * R 0 1 * R 0 2 * R 3 3) +
      (-30 : ℂ) * (R 2 0 * R 0 1 * R 3 2 * R 0 3) +
      (-30 : ℂ) * (R 2 0 * R 3 1 * R 0 2 * R 0 3) +
      (-30 : ℂ) * (R 3 0 * R 0 1 * R 0 2 * R 2 3) +
      (-30 : ℂ) * (R 3 0 * R 0 1 * R 2 2 * R 0 3) +
      (-30 : ℂ) * (R 3 0 * R 2 1 * R 0 2 * R 0 3) =
      120 * Q2 y z := by
    simp only [R, had, Q2, dot3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hdeg3 :
      (20 : ℂ) * (R 0 0 * R 1 1 * R 1 2 * R 3 3) +
      (20 : ℂ) * (R 0 0 * R 1 1 * R 2 2 * R 2 3) +
      (20 : ℂ) * (R 0 0 * R 1 1 * R 3 2 * R 1 3) +
      (20 : ℂ) * (R 0 0 * R 2 1 * R 1 2 * R 2 3) +
      (20 : ℂ) * (R 0 0 * R 2 1 * R 2 2 * R 1 3) +
      (20 : ℂ) * (R 0 0 * R 3 1 * R 1 2 * R 1 3) +
      (20 : ℂ) * (R 1 0 * R 0 1 * R 1 2 * R 3 3) +
      (20 : ℂ) * (R 1 0 * R 0 1 * R 2 2 * R 2 3) +
      (20 : ℂ) * (R 1 0 * R 0 1 * R 3 2 * R 1 3) +
      (20 : ℂ) * (R 1 0 * R 1 1 * R 0 2 * R 3 3) +
      (20 : ℂ) * (R 1 0 * R 1 1 * R 3 2 * R 0 3) +
      (20 : ℂ) * (R 1 0 * R 2 1 * R 0 2 * R 2 3) +
      (20 : ℂ) * (R 1 0 * R 2 1 * R 2 2 * R 0 3) +
      (20 : ℂ) * (R 1 0 * R 3 1 * R 0 2 * R 1 3) +
      (20 : ℂ) * (R 1 0 * R 3 1 * R 1 2 * R 0 3) +
      (20 : ℂ) * (R 2 0 * R 0 1 * R 1 2 * R 2 3) +
      (20 : ℂ) * (R 2 0 * R 0 1 * R 2 2 * R 1 3) +
      (20 : ℂ) * (R 2 0 * R 1 1 * R 0 2 * R 2 3) +
      (20 : ℂ) * (R 2 0 * R 1 1 * R 2 2 * R 0 3) +
      (20 : ℂ) * (R 2 0 * R 2 1 * R 0 2 * R 1 3) +
      (20 : ℂ) * (R 2 0 * R 2 1 * R 1 2 * R 0 3) +
      (20 : ℂ) * (R 3 0 * R 0 1 * R 1 2 * R 1 3) +
      (20 : ℂ) * (R 3 0 * R 1 1 * R 0 2 * R 1 3) +
      (20 : ℂ) * (R 3 0 * R 1 1 * R 1 2 * R 0 3) =
      160 * Q3 x y z := by
    simp only [R, had, Q3, C3, dot3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hdeg4 :
      (-30 : ℂ) * (R 1 0 * R 1 1 * R 1 2 * R 2 3) +
      (-30 : ℂ) * (R 1 0 * R 1 1 * R 2 2 * R 1 3) +
      (-30 : ℂ) * (R 1 0 * R 2 1 * R 1 2 * R 1 3) +
      (-30 : ℂ) * (R 1 0 * R 3 1 * R 3 2 * R 3 3) +
      (-30 : ℂ) * (R 2 0 * R 1 1 * R 1 2 * R 1 3) +
      (20 : ℂ) * (R 2 0 * R 2 1 * R 3 2 * R 3 3) +
      (20 : ℂ) * (R 2 0 * R 3 1 * R 2 2 * R 3 3) +
      (20 : ℂ) * (R 2 0 * R 3 1 * R 3 2 * R 2 3) +
      (-30 : ℂ) * (R 3 0 * R 1 1 * R 3 2 * R 3 3) +
      (20 : ℂ) * (R 3 0 * R 2 1 * R 2 2 * R 3 3) +
      (20 : ℂ) * (R 3 0 * R 2 1 * R 3 2 * R 2 3) +
      (-30 : ℂ) * (R 3 0 * R 3 1 * R 1 2 * R 3 3) +
      (20 : ℂ) * (R 3 0 * R 3 1 * R 2 2 * R 2 3) +
      (-30 : ℂ) * (R 3 0 * R 3 1 * R 3 2 * R 1 3) =
      P4 x y z := by
    simp only [R, had, P4, R4, D3, dot3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hdeg0 : (120 : ℂ) * (R 0 0 * R 0 1 * R 0 2 * R 0 3) = 120 := by
    simp [R]
  linear_combination hdeg0 + hdeg2 + hdeg3 + hdeg4

theorem extract_homog {x y z : V3}
    (h : ∀ t : ℂ, 120 * Q2 (t • y) (t • z) + 160 * Q3 (t • x) (t • y) (t • z) +
      P4 (t • x) (t • y) (t • z) = 0) :
    Q2 y z = 0 ∧ Q3 x y z = 0 ∧ P4 x y z = 0 := by
  have hscale : ∀ t : ℂ,
      t ^ 2 * (120 * Q2 y z) + t ^ 3 * (160 * Q3 x y z) + t ^ 4 * P4 x y z = 0 := by
    intro t
    have ht := h t
    have h2 : Q2 (t • y) (t • z) = t ^ 2 * Q2 y z := by
      simp only [Q2, dot3, Pi.smul_apply, smul_eq_mul]; ring
    have h3 : Q3 (t • x) (t • y) (t • z) = t ^ 3 * Q3 x y z := by
      simp only [Q3, C3, dot3, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val]; ring
    have h4 : P4 (t • x) (t • y) (t • z) = t ^ 4 * P4 x y z := by
      simp only [P4, R4, D3, dot3, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val]; ring
    rw [h2, h3, h4] at ht
    linear_combination ht
  have h1 := hscale 1
  have hm1 := hscale (-1)
  have h2 := hscale 2
  have hQ3 : Q3 x y z = 0 := by linear_combination (h1 - hm1) / 320
  have hQ2 : Q2 y z = 0 := by linear_combination (16 * h1 - h2 - 1280 * hQ3) / 1440
  have hP4 : P4 x y z = 0 := by linear_combination h1 - 120 * hQ2 - 160 * hQ3
  exact ⟨hQ2, hQ3, hP4⟩

theorem extract_zC {x y z u : V3}
    (h : ∀ h : ℂ, Q3 (x + h • u) y z = 0) : dot3 z (C3 u) = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  simp only [Q3, C3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 hm1 ⊢
  linear_combination (h1 + hm1 - 2 * h0) / 2

theorem extract_yD {x y z u : V3}
    (h : ∀ h : ℂ, P4 (x + h • u) y z = 0) : dot3 y (D3 u) = 0 := by
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  simp only [P4, R4, D3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 hm1 h2 hm2 ⊢
  linear_combination -(h2 - hm2 - 2 * h1 + 2 * hm1) / 1440

def swapBilin : (V3 × V3) ≃ₗ[ℂ] Module.Dual ℂ (V3 × V3) where
  toFun p :=
    { toFun := fun q => dot3 p.1 q.2 + dot3 q.1 p.2
      map_add' := fun q1 q2 => by simp only [dot3, Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
      map_smul' := fun c q => by simp only [dot3, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' p1 p2 := by
    apply LinearMap.ext
    intro q
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, dot3, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' c p := by
    apply LinearMap.ext
    intro q
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, dot3, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  invFun f :=
    (fun i => f (0, Pi.single i 1), fun i => f (Pi.single i 1, 0))
  left_inv p := by
    ext i <;> fin_cases i <;> simp [dot3]
  right_inv f := by
    apply LinearMap.ext
    rintro ⟨y, z⟩
    have hdecomp : (y, z) =
        y 0 • (Pi.single 0 1, 0) + y 1 • (Pi.single 1 1, 0) + y 2 • (Pi.single 2 1, 0) +
        z 0 • (0, Pi.single 0 1) + z 1 • (0, Pi.single 1 1) + z 2 • (0, Pi.single 2 1) := by
      ext i <;> fin_cases i <;> simp
    conv_rhs => rw [hdecomp]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, dot3, map_add, map_smul, smul_eq_mul]
    ring

theorem isotropic_finrank_le_three (W : Submodule ℂ (V3 × V3))
    (hiso : ∀ p ∈ W, dot3 p.1 p.2 = 0) : Module.finrank ℂ W ≤ 3 := by
  have hle : W.map swapBilin.toLinearMap ≤ W.dualAnnihilator := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro q hq
    have hpq : p + q ∈ W := W.add_mem hp hq
    have h1 := hiso p hp
    have h2 := hiso q hq
    have h3 := hiso (p + q) hpq
    simp only [swapBilin, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [dot3, Prod.fst_add, Prod.snd_add, Pi.add_apply] at h1 h2 h3 ⊢
    linear_combination h3 - h1 - h2
  have h1 : Module.finrank ℂ (W.map swapBilin.toLinearMap) = Module.finrank ℂ W :=
    LinearEquiv.finrank_map_eq swapBilin W
  have h2 : Module.finrank ℂ (W.map swapBilin.toLinearMap) ≤ Module.finrank ℂ W.dualAnnihilator :=
    Submodule.finrank_mono hle
  have h3 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hdim : Module.finrank ℂ (V3 × V3) = 6 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun]
  omega

def permV3 (σ : Equiv.Perm (Fin 3)) : V3 ≃ₗ[ℂ] V3 where
  toFun u := u ∘ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun u := u ∘ σ.symm
  left_inv u := by funext i; simp
  right_inv u := by funext i; simp

def permTriple (σ : Equiv.Perm (Fin 3)) : Triple ≃ₗ[ℂ] Triple :=
  (permV3 σ).prodCongr ((permV3 σ).prodCongr (permV3 σ))

theorem perm_Q2 (i j : Fin 3) (y z : V3) :
    Q2 (permV3 (Equiv.swap i j) y) (permV3 (Equiv.swap i j) z) = Q2 y z := by
  fin_cases i <;> fin_cases j <;>
    simp [Q2, dot3, permV3, Equiv.swap_apply_def, Fin.ext_iff] <;> ring

theorem perm_Q3 (i j : Fin 3) (x y z : V3) :
    Q3 (permV3 (Equiv.swap i j) x) (permV3 (Equiv.swap i j) y) (permV3 (Equiv.swap i j) z) = Q3 x y z := by
  fin_cases i <;> fin_cases j <;>
    simp [Q3, C3, dot3, permV3, Equiv.swap_apply_def, Fin.ext_iff] <;> ring

theorem perm_P4 (i j : Fin 3) (x y z : V3) :
    P4 (permV3 (Equiv.swap i j) x) (permV3 (Equiv.swap i j) y) (permV3 (Equiv.swap i j) z) = P4 x y z := by
  fin_cases i <;> fin_cases j <;>
    simp [P4, R4, D3, dot3, permV3, Equiv.swap_apply_def, Fin.ext_iff] <;> ring

def projYZ : Triple →ₗ[ℂ] V3 × V3 := LinearMap.snd ℂ V3 (V3 × V3)
def projX : Triple →ₗ[ℂ] V3 := LinearMap.fst ℂ V3 (V3 × V3)

def ValidSubspace (M : Submodule ℂ Triple) : Prop :=
  ∀ p ∈ M, Q2 p.2.1 p.2.2 = 0 ∧ Q3 p.1 p.2.1 p.2.2 = 0 ∧ P4 p.1 p.2.1 p.2.2 = 0

theorem valid_swap {M : Submodule ℂ Triple} (hM : ValidSubspace M) (i j : Fin 3) :
    ValidSubspace (M.map (permTriple (Equiv.swap i j)).toLinearMap) := by
  rintro _ ⟨⟨x, y, z⟩, hp, rfl⟩
  obtain ⟨h2, h3, h4⟩ := hM ⟨x, y, z⟩ hp
  refine ⟨?_, ?_, ?_⟩
  · exact (perm_Q2 i j y z).trans h2
  · exact (perm_Q3 i j x y z).trans h3
  · exact (perm_P4 i j x y z).trans h4

theorem pureX_mem_M {M : Submodule ℂ Triple} {u : V3}
    (hu : u ∈ (LinearMap.ker (projYZ.domRestrict M)).map (projX.comp M.subtype)) :
    (u, 0, 0) ∈ M := by
  rcases hu with ⟨⟨⟨x, y, z⟩, hmem⟩, hker, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hker
  have hy : y = 0 := congrArg Prod.fst hker
  have hz : z = 0 := congrArg Prod.snd hker
  subst hy; subst hz
  exact hmem

theorem kernel_laws {M : Submodule ℂ Triple} (hM : ValidSubspace M)
    {x y z u : V3} (hp : (x, y, z) ∈ M) (hu : (u, 0, 0) ∈ M) :
    dot3 z (C3 u) = 0 ∧ dot3 y (D3 u) = 0 := by
  have htr : ∀ h : ℂ, (x + h • u, y, z) ∈ M := by
    intro h
    have h1 := M.add_mem hp (M.smul_mem h hu)
    simpa [Prod.smul_mk, Prod.mk_add_mk] using h1
  exact ⟨extract_zC (fun h => (hM _ (htr h)).2.1), extract_yD (fun h => (hM _ (htr h)).2.2)⟩

theorem case_all_nonzero {M : Submodule ℂ Triple} (hM : ValidSubspace M)
    (hW : Module.finrank ℂ (LinearMap.range (projYZ.domRestrict M)) = 3)
    (α : V3) (hα0 : α 0 ≠ 0) (hα1 : α 1 ≠ 0) (hα2 : α 2 ≠ 0)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0) ∈ M) : False := by
  have hz_zero : ∀ p ∈ M, p.2.2 = 0 := by
    intro ⟨x, y, z⟩ hp
    let p0 : ℂ := -α 0 / α 2
    let q0 : ℂ := -α 1 / α 2
    have hp0 : p0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα0) hα2
    have hq0 : q0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα1) hα2
    have hu1 : (![1, 0, p0], 0, 0) ∈ M := hU ![1, 0, p0] (by
      simp only [dot3, p0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hα2]; ring)
    have hu2 : (![0, 1, q0], 0, 0) ∈ M := hU ![0, 1, q0] (by
      simp only [dot3, q0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hα2]; ring)
    have hu3 : (![1, 1, p0 + q0], 0, 0) ∈ M := hU ![1, 1, p0 + q0] (by
      simp only [dot3, p0, q0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hα2]; ring)
    have h1 := (kernel_laws hM hp hu1).1
    have h2 := (kernel_laws hM hp hu2).1
    have h3 := (kernel_laws hM hp hu3).1
    simp only [dot3, C3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 h2 h3
    have hz1 : z 1 = 0 := by
      have : p0 * z 1 = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_left hp0
    have hz0 : z 0 = 0 := by
      have : q0 * z 0 = 0 := by linear_combination h2
      exact (mul_eq_zero.mp this).resolve_left hq0
    have hz2 : z 2 = 0 := by linear_combination h3 - (p0 + q0) * hz0 - (p0 + q0) * hz1
    funext i
    fin_cases i <;> assumption
  let S : Submodule ℂ (V3 × V3) := LinearMap.range (LinearMap.inl ℂ V3 V3)
  have hle : LinearMap.range (projYZ.domRestrict M) ≤ S := by
    rintro _ ⟨⟨⟨x, y, z⟩, hp⟩, rfl⟩
    have hz : z = 0 := hz_zero ⟨x, y, z⟩ hp
    refine ⟨y, ?_⟩
    simp [projYZ, hz]
  have hfinS : Module.finrank ℂ S = 3 := by
    rw [LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_fin_fun]
  have heqS : LinearMap.range (projYZ.domRestrict M) = S :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hD_zero : ∀ u : V3, dot3 α u = 0 → D3 u = 0 := by
    intro u hu
    have huM : (u, 0, 0) ∈ M := hU u hu
    have hall_y : ∀ y : V3, dot3 y (D3 u) = 0 := by
      intro y
      have hyS : (y, (0 : V3)) ∈ S := ⟨y, rfl⟩
      rw [← heqS] at hyS
      rcases hyS with ⟨⟨⟨x, y', z'⟩, hp⟩, hpyz⟩
      have hy_eq : y' = y := congrArg Prod.fst hpyz
      subst hy_eq
      exact (kernel_laws hM hp huM).2
    funext i
    have hi := hall_y (Pi.single i 1)
    fin_cases i <;> simp [dot3, Fin.ext_iff] at hi ⊢ <;> exact hi
  let p0 : ℂ := -α 0 / α 2
  let q0 : ℂ := -α 1 / α 2
  have hp0 : p0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα0) hα2
  have hq0 : q0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα1) hα2
  have hex_u : ∃ u : V3, dot3 α u = 0 ∧ u 0 ≠ 0 ∧ u 1 ≠ 0 ∧ u 2 ≠ 0 := by
    by_cases hpq : p0 + q0 ≠ 0
    · refine ⟨![1, 1, p0 + q0], ?_, by norm_num, by norm_num, hpq⟩
      simp only [dot3, p0, q0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hα2]; ring
    · push Not at hpq
      have hp2q : p0 + 2 * q0 ≠ 0 := by
        intro h0
        apply hq0
        linear_combination h0 - hpq
      refine ⟨![1, 2, p0 + 2 * q0], ?_, by norm_num, by norm_num, hp2q⟩
      simp only [dot3, p0, q0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hα2]; ring
  obtain ⟨u, hu, hu0, hu1, hu2⟩ := hex_u
  have hDu := hD_zero u hu
  have hD0 : u 0 * (u 0 ^ 2 - u 1 ^ 2 - u 2 ^ 2) = 0 := congrFun hDu 0
  have hD1 : u 1 * (u 1 ^ 2 - u 0 ^ 2 - u 2 ^ 2) = 0 := congrFun hDu 1
  have hf0 : u 0 ^ 2 - u 1 ^ 2 - u 2 ^ 2 = 0 := (mul_eq_zero.mp hD0).resolve_left hu0
  have hf1 : u 1 ^ 2 - u 0 ^ 2 - u 2 ^ 2 = 0 := (mul_eq_zero.mp hD1).resolve_left hu1
  have hu2_sq : u 2 ^ 2 = 0 := by linear_combination -(hf0 + hf1) / 2
  exact hu2 (sq_eq_zero_iff.mp hu2_sq)

theorem case_two_nonzero {M : Submodule ℂ Triple} (hM : ValidSubspace M)
    (hW : Module.finrank ℂ (LinearMap.range (projYZ.domRestrict M)) = 3)
    (α : V3) (hα0 : α 0 = 0) (hα1 : α 1 ≠ 0) (hα2 : α 2 ≠ 0)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0) ∈ M) : False := by
  let s : ℂ := -α 1 / α 2
  have hs : s ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα1) hα2
  have hmem : ∀ a b : ℂ, (![a, b, s * b], 0, 0) ∈ M := fun a b => hU ![a, b, s * b] (by
    simp only [dot3, hα0, s, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp [hα2]; ring)
  let Ψ : (Fin 2 → ℂ) →ₗ[ℂ] V3 × V3 :=
    { toFun := fun t => (![0, -s * t 0, t 0], ![0, t 1, -s * t 1])
      map_add' := fun t1 t2 => by ext i <;> fin_cases i <;> simp <;> ring
      map_smul' := fun c t => by ext i <;> fin_cases i <;> simp <;> ring }
  have hle : LinearMap.range (projYZ.domRestrict M) ≤ LinearMap.range Ψ := by
    rintro _ ⟨⟨⟨x, y, z⟩, hp⟩, rfl⟩
    have hc1 := (kernel_laws hM hp (hmem 0 1)).1
    have hc2 := (kernel_laws hM hp (hmem 1 1)).1
    have hd0 := (kernel_laws hM hp (hmem 1 0)).2
    have hd1 := (kernel_laws hM hp (hmem 0 1)).2
    have hd2 := (kernel_laws hM hp (hmem 1 1)).2
    simp only [dot3, C3, D3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hc1 hc2 hd0 hd1 hd2
    have hz0 : z 0 = 0 := (mul_eq_zero.mp (by linear_combination hc1 : s * z 0 = 0)).resolve_left hs
    have hz2 : z 2 = -s * z 1 := by linear_combination hc2 - s * hz0
    have hy0 : y 0 = 0 := by linear_combination hd0
    have hy1 : y 1 = -s * y 2 := by linear_combination -(hd2 - hd1) - s ^ 2 * hy0
    refine ⟨![y 2, z 1], ?_⟩
    ext i <;> fin_cases i <;> simp [Ψ, projYZ, hy0, hy1, hz0, hz2]
  have hle_rank : Module.finrank ℂ (LinearMap.range (projYZ.domRestrict M)) ≤ Module.finrank ℂ (LinearMap.range Ψ) :=
    Submodule.finrank_mono hle
  have hrank_Psi : Module.finrank ℂ (LinearMap.range Ψ) ≤ 2 := by
    have h1 := LinearMap.finrank_range_le Ψ
    rw [Module.finrank_fin_fun] at h1
    exact h1
  omega

theorem case_one_nonzero {M : Submodule ℂ Triple} (hM : ValidSubspace M)
    (hW : Module.finrank ℂ (LinearMap.range (projYZ.domRestrict M)) = 3)
    (α : V3) (hα0 : α 0 = 0) (hα1 : α 1 = 0) (hα2 : α 2 ≠ 0)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0) ∈ M) : False := by
  have hmem : ∀ a b : ℂ, (![a, b, 0], 0, 0) ∈ M := fun a b => hU ![a, b, 0] (by
    simp [dot3, hα0, hα1])
  let Ψ : (Fin 3 → ℂ) →ₗ[ℂ] V3 × V3 :=
    { toFun := fun t => (![0, 0, t 2], ![t 0, t 1, 0])
      map_add' := fun t1 t2 => by ext i <;> fin_cases i <;> simp
      map_smul' := fun c t => by ext i <;> fin_cases i <;> simp }
  have hle : LinearMap.range (projYZ.domRestrict M) ≤ LinearMap.range Ψ := by
    rintro _ ⟨⟨⟨x, y, z⟩, hp⟩, rfl⟩
    have hc := (kernel_laws hM hp (hmem 1 1)).1
    have hd0 := (kernel_laws hM hp (hmem 1 0)).2
    have hd1 := (kernel_laws hM hp (hmem 0 1)).2
    simp only [dot3, C3, D3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hc hd0 hd1
    have hz2 : z 2 = 0 := by linear_combination hc
    have hy0 : y 0 = 0 := by linear_combination hd0
    have hy1 : y 1 = 0 := by linear_combination hd1
    refine ⟨![z 0, z 1, y 2], ?_⟩
    ext i <;> fin_cases i <;> simp [Ψ, projYZ, hy0, hy1, hz2]
  have hrank_Psi : Module.finrank ℂ (LinearMap.range Ψ) = 3 := by
    have h1 := LinearMap.finrank_range_le Ψ
    rw [Module.finrank_fin_fun] at h1
    have h2 := Submodule.finrank_mono hle
    omega
  have heq : LinearMap.range (projYZ.domRestrict M) = LinearMap.range Ψ :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have he0 : ((0 : V3), (![1, 0, 0] : V3)) ∈ LinearMap.range (projYZ.domRestrict M) := by
    rw [heq]
    refine ⟨![1, 0, 0], ?_⟩
    ext i <;> fin_cases i <;> simp [Ψ]
  rcases he0 with ⟨⟨⟨x, y, z⟩, hp⟩, hpyz⟩
  have hy : y = 0 := congrArg Prod.fst hpyz
  have hz : z = ![1, 0, 0] := congrArg Prod.snd hpyz
  subst hy; subst hz
  have hw : ((![0, 0, x 2] : V3), (0 : V3), (![1, 0, 0] : V3)) ∈ M := by
    have hsub := M.sub_mem hp (hmem (x 0) (x 1))
    convert hsub using 1
    ext i
    · fin_cases i
      · change (0 : ℂ) = x 0 - x 0; ring
      · change (0 : ℂ) = x 1 - x 1; ring
      · change x 2 = x 2 - 0; ring
    · simp
    · simp
  have hw' : ((![0, 1, x 2] : V3), (0 : V3), (![1, 0, 0] : V3)) ∈ M := by
    have hadd := M.add_mem hw (hmem 0 1)
    convert hadd using 1
    ext i <;> fin_cases i <;> simp
  have hx2 : x 2 = 0 := by
    have hq3 := (hM _ hw').2.1
    simp only [Q3, C3, dot3, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hq3
    linear_combination hq3
  have hv : ((![1, 0, 0] : V3), (0 : V3), (![1, 0, 0] : V3)) ∈ M := by
    have hadd := M.add_mem hw (hmem 1 0)
    convert hadd using 1
    ext i <;> fin_cases i <;> simp [hx2]
  have hp4 := (hM _ hv).2.2
  simp only [P4, R4, D3, dot3, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hp4
  norm_num at hp4

theorem valid_finrank_le_four (M : Submodule ℂ Triple) (hM : ValidSubspace M) :
    Module.finrank ℂ M ≤ 4 := by
  by_contra hgt
  have h5 : 5 ≤ Module.finrank ℂ M := by omega
  let π : M →ₗ[ℂ] V3 × V3 := projYZ.domRestrict M
  have hW_le : Module.finrank ℂ (LinearMap.range π) ≤ 3 := by
    apply isotropic_finrank_le_three
    rintro _ ⟨⟨⟨x, y, z⟩, hp⟩, rfl⟩
    exact (hM ⟨x, y, z⟩ hp).1
  have hrn : Module.finrank ℂ (LinearMap.range π) + Module.finrank ℂ (LinearMap.ker π) =
      Module.finrank ℂ M := LinearMap.finrank_range_add_finrank_ker π
  let U : Submodule ℂ V3 := (LinearMap.ker π).map (projX.comp M.subtype)
  have hker_inj : Set.InjOn (projX.comp M.subtype) (LinearMap.ker π) := by
    rintro ⟨⟨x1, y1, z1⟩, h1⟩ hk1 ⟨⟨x2, y2, z2⟩, h2⟩ hk2 heq
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hk1 hk2
    have hy1 : y1 = 0 := congrArg Prod.fst hk1
    have hz1 : z1 = 0 := congrArg Prod.snd hk1
    have hy2 : y2 = 0 := congrArg Prod.fst hk2
    have hz2 : z2 = 0 := congrArg Prod.snd hk2
    have hx : x1 = x2 := heq
    subst hx hy1 hz1 hy2 hz2
    rfl
  have hU_finrank : Module.finrank ℂ U = Module.finrank ℂ (LinearMap.ker π) := by
    have hinj : Function.Injective ((projX.comp M.subtype).domRestrict (LinearMap.ker π)) := by
      rintro ⟨v1, hv1⟩ ⟨v2, hv2⟩ heq
      exact Subtype.ext (hker_inj hv1 hv2 heq)
    have h1 := LinearMap.finrank_range_of_inj hinj
    have hrange : LinearMap.range ((projX.comp M.subtype).domRestrict (LinearMap.ker π)) = U := by
      ext u
      simp [U]
    rw [hrange] at h1
    exact h1
  have hU_le3 : Module.finrank ℂ U ≤ 3 := by
    have := Submodule.finrank_le U
    rwa [Module.finrank_fin_fun] at this
  have hU_ge2 : 2 ≤ Module.finrank ℂ U := by omega
  by_cases hU3 : Module.finrank ℂ U = 3
  · have hUtop : U = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact hU3)
    have hallU : ∀ u : V3, (u, 0, 0) ∈ M := fun u => pureX_mem_M (by change u ∈ U; rw [hUtop]; trivial)
    have hWbot : LinearMap.range π = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨⟨⟨x, y, z⟩, hp⟩, rfl⟩
      have hz0 : z 0 = 0 := by
        have h := (kernel_laws hM hp (hallU ![0, 1, 1])).1
        simp [dot3, C3] at h; exact h
      have hz1 : z 1 = 0 := by
        have h := (kernel_laws hM hp (hallU ![1, 0, 1])).1
        simp [dot3, C3] at h; exact h
      have hz2 : z 2 = 0 := by
        have h := (kernel_laws hM hp (hallU ![1, 1, 0])).1
        simp [dot3, C3] at h; exact h
      have hy0 : y 0 = 0 := by
        have h := (kernel_laws hM hp (hallU ![1, 0, 0])).2
        simp [dot3, D3] at h; exact h
      have hy1 : y 1 = 0 := by
        have h := (kernel_laws hM hp (hallU ![0, 1, 0])).2
        simp [dot3, D3] at h; exact h
      have hy2 : y 2 = 0 := by
        have h := (kernel_laws hM hp (hallU ![0, 0, 1])).2
        simp [dot3, D3] at h; exact h
      ext i <;> fin_cases i <;> simp [π, projYZ, hy0, hy1, hy2, hz0, hz1, hz2]
    have hW0 : Module.finrank ℂ (LinearMap.range π) = 0 := by rw [hWbot, finrank_bot]
    omega
  · have hU2 : Module.finrank ℂ U = 2 := by omega
    have hW3 : Module.finrank ℂ (LinearMap.range π) = 3 := by omega
    have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq U
    rw [Module.finrank_fin_fun] at hann
    have hann1 : Module.finrank ℂ U.dualAnnihilator = 1 := by omega
    have hne_bot : U.dualAnnihilator ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hann1
      omega
    obtain ⟨f, hf_mem, hf_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
    let α : V3 := fun i => f (Pi.single i 1)
    have hf_eq : ∀ u : V3, f u = dot3 α u := by
      intro u
      have hu : u = u 0 • Pi.single 0 1 + u 1 • Pi.single 1 1 + u 2 • Pi.single 2 1 := by
        ext i; fin_cases i <;> simp
      conv_lhs => rw [hu]
      simp only [map_add, map_smul, smul_eq_mul, dot3, α]
      ring
    have hα_ne : α ≠ 0 := by
      intro h0
      apply hf_ne
      apply LinearMap.ext
      intro u
      rw [hf_eq, h0]
      simp [dot3]
    have hU_eq_ker : U = LinearMap.ker f := by
      have hle : U ≤ LinearMap.ker f := by
        intro u hu
        rw [Submodule.mem_dualAnnihilator] at hf_mem
        exact hf_mem u hu
      have hfr := LinearMap.finrank_range_add_finrank_ker f
      rw [Module.finrank_fin_fun] at hfr
      have hex_ne : ∃ u0 : V3, f u0 ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hf_ne (LinearMap.ext hall)
      obtain ⟨u0, hu0⟩ := hex_ne
      have hrange_top : LinearMap.range f = ⊤ := by
        rw [eq_top_iff]
        intro c _
        refine ⟨(c / f u0) • u0, ?_⟩
        rw [map_smul, smul_eq_mul]
        exact div_mul_cancel₀ c hu0
      have hrange1 : Module.finrank ℂ (LinearMap.range f) = 1 := by
        rw [hrange_top, finrank_top, Module.finrank_self]
      exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
    have hU_char : ∀ u : V3, dot3 α u = 0 → (u, 0, 0) ∈ M := by
      intro u hu
      apply pureX_mem_M
      change u ∈ U
      rw [hU_eq_ker, LinearMap.mem_ker, hf_eq]
      exact hu
    have hswap_red : ∀ i j : Fin 3,
        let M' := M.map (permTriple (Equiv.swap i j)).toLinearMap
        ValidSubspace M' ∧
        Module.finrank ℂ (LinearMap.range (projYZ.domRestrict M')) = 3 ∧
        ∀ u : V3, dot3 (permV3 (Equiv.swap i j) α) u = 0 → (u, 0, 0) ∈ M' := by
      intro i j
      let σ := Equiv.swap i j
      let M' := M.map (permTriple σ).toLinearMap
      refine ⟨valid_swap hM i j, ?_, ?_⟩
      · have hrange : LinearMap.range (projYZ.domRestrict M') =
            (LinearMap.range π).map ((permV3 σ).prodCongr (permV3 σ)).toLinearMap := by
          ext ⟨y', z'⟩
          constructor
          · rintro ⟨⟨⟨x', y1, z1⟩, ⟨⟨x, y, z⟩, hp, hmap⟩⟩, hproj⟩
            have hy1 : y1 = y' := congrArg Prod.fst hproj
            have hz1 : z1 = z' := congrArg Prod.snd hproj
            have hy2 : permV3 σ y = y1 := congrArg (fun p : Triple => p.2.1) hmap
            have hz2 : permV3 σ z = z1 := congrArg (fun p : Triple => p.2.2) hmap
            refine ⟨(y, z), ⟨⟨⟨x, y, z⟩, hp⟩, rfl⟩, ?_⟩
            exact Prod.ext (hy2.trans hy1) (hz2.trans hz1)
          · rintro ⟨⟨y, z⟩, ⟨⟨⟨x, y1, z1⟩, hp⟩, hproj⟩, hmap⟩
            have hy1 : y1 = y := congrArg Prod.fst hproj
            have hz1 : z1 = z := congrArg Prod.snd hproj
            refine ⟨⟨permTriple σ (x, y1, z1), ⟨(x, y1, z1), hp, rfl⟩⟩, ?_⟩
            change (permV3 σ y1, permV3 σ z1) = (y', z')
            rw [hy1, hz1]
            exact hmap
        rw [hrange, LinearEquiv.finrank_map_eq]
        exact hW3
      · intro u hu
        have hu' : dot3 α (permV3 σ u) = 0 := by
          have h1 := perm_Q2 i j (permV3 σ α) u
          simp only [Q2, permV3, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] at h1 hu ⊢
          have h2 : (α ∘ σ) ∘ σ = α := by funext k; simp [σ]
          rw [h2] at h1
          exact h1.trans hu
        refine ⟨(permV3 σ u, 0, 0), hU_char (permV3 σ u) hu', ?_⟩
        ext k <;> simp [permTriple, permV3, σ]
    by_cases h0 : α 0 = 0
    · by_cases h1 : α 1 = 0
      · have h2 : α 2 ≠ 0 := by
          intro h2; apply hα_ne; funext k; fin_cases k <;> assumption
        exact case_one_nonzero hM hW3 α h0 h1 h2 hU_char
      · by_cases h2 : α 2 = 0
        · obtain ⟨hM', hW', hU'⟩ := hswap_red 1 2
          exact case_one_nonzero hM' hW' (permV3 (Equiv.swap 1 2) α)
            (by simp [permV3, Equiv.swap_apply_def, Fin.ext_iff, h0])
            (by simp [permV3, h2])
            (by simp [permV3, h1]) hU'
        · exact case_two_nonzero hM hW3 α h0 h1 h2 hU_char
    · by_cases h1 : α 1 = 0
      · by_cases h2 : α 2 = 0
        · obtain ⟨hM', hW', hU'⟩ := hswap_red 0 2
          exact case_one_nonzero hM' hW' (permV3 (Equiv.swap 0 2) α)
            (by simp [permV3, h2])
            (by simp [permV3, Equiv.swap_apply_def, Fin.ext_iff, h1])
            (by simp [permV3, h0]) hU'
        · obtain ⟨hM', hW', hU'⟩ := hswap_red 0 1
          exact case_two_nonzero hM' hW' (permV3 (Equiv.swap 0 1) α)
            (by simp [permV3, h1])
            (by simp [permV3, h0])
            (by simp [permV3, Equiv.swap_apply_def, Fin.ext_iff, h2]) hU'
      · by_cases h2 : α 2 = 0
        · obtain ⟨hM', hW', hU'⟩ := hswap_red 0 2
          exact case_two_nonzero hM' hW' (permV3 (Equiv.swap 0 2) α)
            (by simp [permV3, h2])
            (by simp [permV3, Equiv.swap_apply_def, Fin.ext_iff, h1])
            (by simp [permV3, h0]) hU'
        · exact case_all_nonzero hM hW3 α h0 h1 h2 hU_char

end

end PEqualNP.Outside.L_gct_280_aux

theorem PEqualNP.Outside.L_gct_280 : (∀ (ζ : ℂ), IsPrimitiveRoot ζ 5 →
  ∀ L : Submodule ℂ (Fin 3 → Fin 4 → ℂ),
    (∀ x ∈ L, (∀ r : Fin 3, (∑ i, x r i) = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + x 0 i * ζ ^ (f i).val + x 1 i * ζ ^ (2 * (f i).val) +
          x 2 i * ζ ^ (3 * (f i).val))) = 120) →
      Module.finrank ℂ L ≤ 4) := by
  intro ζ hζ L hL
  let M : Submodule ℂ PEqualNP.Outside.L_gct_280_aux.Triple :=
    L.map PEqualNP.Outside.L_gct_280_aux.toTriple
  have hfin : Module.finrank ℂ M = Module.finrank ℂ L := by
    have hker : LinearMap.ker (PEqualNP.Outside.L_gct_280_aux.toTriple.domRestrict L) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro ⟨X, hX⟩ h0
      rw [LinearMap.mem_ker] at h0
      have hzero : PEqualNP.Outside.L_gct_280_aux.toTriple X =
          PEqualNP.Outside.L_gct_280_aux.toTriple 0 := by
        simpa using h0
      have hX0 := PEqualNP.Outside.L_gct_280_aux.toTriple_inj_on_zeroSum
        (hL X hX).1 (fun _ => by simp) hzero
      exact Subtype.ext hX0
    have h1 := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hker)
    have hrange : LinearMap.range (PEqualNP.Outside.L_gct_280_aux.toTriple.domRestrict L) = M := by
      ext p
      simp [M]
    rw [hrange] at h1
    exact h1
  have hvalid : PEqualNP.Outside.L_gct_280_aux.ValidSubspace M := by
    rintro _ ⟨X, hX, rfl⟩
    apply PEqualNP.Outside.L_gct_280_aux.extract_homog
    intro t
    have htX : t • X ∈ L := L.smul_mem t hX
    obtain ⟨hsum, hperm⟩ := hL (t • X) htX
    have hhad : ∀ r : Fin 3,
        PEqualNP.Outside.L_gct_280_aux.had (t • PEqualNP.Outside.L_gct_280_aux.invHad (X r)) = (t • X) r := by
      intro r
      have hlin : t • PEqualNP.Outside.L_gct_280_aux.invHad (X r) =
          PEqualNP.Outside.L_gct_280_aux.invHad ((t • X) r) := by
        ext i; fin_cases i <;> simp [PEqualNP.Outside.L_gct_280_aux.invHad] <;> ring
      rw [hlin, PEqualNP.Outside.L_gct_280_aux.had_invHad _ (hsum r)]
    have heval := PEqualNP.Outside.L_gct_280_aux.permSum_had hζ
      (t • PEqualNP.Outside.L_gct_280_aux.invHad (X 0))
      (t • PEqualNP.Outside.L_gct_280_aux.invHad (X 1))
      (t • PEqualNP.Outside.L_gct_280_aux.invHad (X 2))
    rw [hhad 0, hhad 1, hhad 2, hperm] at heval
    dsimp only [PEqualNP.Outside.L_gct_280_aux.toTriple]
    linear_combination -heval
  rw [← hfin]
  exact PEqualNP.Outside.L_gct_280_aux.valid_finrank_le_four M hvalid

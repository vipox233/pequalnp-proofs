import Mathlib

namespace PEqualNP.Outside.L_gct_284_aux

noncomputable section Proof

-- Fourier sum recurrence and Hadamard coordinates adapted from
-- lean/PEqualNP/Outside/L_gct_280.lean at 34b69d9439994e91b48ad3218ab49ac79dfe9fff.

private abbrev V3 := Fin 3 → ℂ

private def had (u : V3) : Fin 4 → ℂ :=
  ![u 0 + u 1 + u 2, u 0 - u 1 - u 2, -u 0 + u 1 - u 2, -u 0 - u 1 + u 2]

private def invHad (v : Fin 4 → ℂ) : V3 :=
  ![(v 0 + v 1) / 2, (v 0 + v 2) / 2, (v 0 + v 3) / 2]

private theorem had_invHad (v : Fin 4 → ℂ) (hv : (∑ i : Fin 4, v i) = 0) :
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

private def dot3 (u v : V3) : ℂ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

private def C3 (u : V3) : V3 := ![u 1 * u 2, u 2 * u 0, u 0 * u 1]

private def D3 (u : V3) : V3 :=
  ![u 0 * (u 0 ^ 2 - u 1 ^ 2 - u 2 ^ 2),
    u 1 * (u 1 ^ 2 - u 0 ^ 2 - u 2 ^ 2),
    u 2 * (u 2 ^ 2 - u 0 ^ 2 - u 1 ^ 2)]

private def R4 (y z : V3) : ℂ :=
  120 * (y 0 ^ 2 * z 0 ^ 2 + y 1 ^ 2 * z 1 ^ 2 + y 2 ^ 2 * z 2 ^ 2) -
  40 * (y 0 ^ 2 * z 1 ^ 2 + y 0 ^ 2 * z 2 ^ 2 + y 1 ^ 2 * z 0 ^ 2 +
        y 1 ^ 2 * z 2 ^ 2 + y 2 ^ 2 * z 0 ^ 2 + y 2 ^ 2 * z 1 ^ 2) -
  160 * (y 0 * y 1 * z 0 * z 1 + y 1 * y 2 * z 1 * z 2 + y 2 * y 0 * z 2 * z 0)

private def c1 (a : ℕ) : ℤ := if a % 5 = 0 then 5 else 0
private def c2 (a b : ℕ) : ℤ := c1 a * c1 b - c1 (a + b)
private def c3 (a b c : ℕ) : ℤ := c2 a b * c1 c - c2 (a + c) b - c2 a (b + c)
private def c4 (a b c d : ℕ) : ℤ := c3 a b c * c1 d - c3 (a + d) b c - c3 a (b + d) c - c3 a b (c + d)

private def S1 (ζ : ℂ) (a : ℕ) : ℂ := ∑ x0 : Fin 5, ζ ^ (a * x0.val)

private def S2 (ζ : ℂ) (a b : ℕ) : ℂ :=
  ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ζ ^ (a * x0.val + b * x1.val)

private def S3 (ζ : ℂ) (a b c : ℕ) : ℂ :=
  ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
    ζ ^ (a * x0.val + b * x1.val + c * x2.val)

private def S4 (ζ : ℂ) (a b c d : ℕ) : ℂ :=
  ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
    ∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
      ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val)

private theorem S1_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) : S1 ζ a = (c1 a : ℂ) := by
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

private theorem S2_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a b : ℕ) : S2 ζ a b = (c2 a b : ℂ) := by
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

private theorem S3_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a b c : ℕ) : S3 ζ a b c = (c3 a b c : ℂ) := by
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

private theorem S4_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a b c d : ℕ) : S4 ζ a b c d = (c4 a b c d : ℂ) := by
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

private theorem sum_emb_eq_S4 (ζ : ℂ) (a b c d : ℕ) :
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

abbrev Quad := V3 × V3 × V3 × V3

private def invHadLinear : (Fin 4 → ℂ) →ₗ[ℂ] V3 where
  toFun := invHad
  map_add' x y := by
    ext i; fin_cases i <;> simp [invHad] <;> ring
  map_smul' t x := by
    ext i; fin_cases i <;> simp [invHad] <;> ring

private def toQuad : (Fin 4 → Fin 4 → ℂ) →ₗ[ℂ] Quad where
  toFun X := (invHad (X 0), invHad (X 1), invHad (X 2), invHad (X 3))
  map_add' X Y := by
    ext i <;> fin_cases i <;> simp [invHad] <;> ring
  map_smul' c X := by
    ext i <;> fin_cases i <;> simp [invHad] <;> ring

private lemma toQuad_inj_on_zeroSum {X Y : Fin 4 → Fin 4 → ℂ}
    (hX : ∀ r : Fin 4, (∑ i : Fin 4, X r i) = 0)
    (hY : ∀ r : Fin 4, (∑ i : Fin 4, Y r i) = 0)
    (heq : toQuad X = toQuad Y) : X = Y := by
  funext r
  have h : invHad (X r) = invHad (Y r) := by
    fin_cases r
    · exact congrArg Prod.fst heq
    · exact congrArg (fun p => p.2.1) heq
    · exact congrArg (fun p => p.2.2.1) heq
    · exact congrArg (fun p => p.2.2.2) heq
  rw [← had_invHad (X r) (hX r), ← had_invHad (Y r) (hY r), h]

private def pure : V3 →ₗ[ℂ] Quad := LinearMap.inl ℂ V3 (V3 × V3 × V3)

private lemma pure_mem_of_row {L : Submodule ℂ (Fin 4 → Fin 4 → ℂ)}
    {v : Fin 4 → ℂ} (hv : (fun r : Fin 4 => if r = 0 then v else 0) ∈ L) :
    pure (invHadLinear v) ∈ L.map toQuad := by
  refine ⟨_, hv, ?_⟩
  simp [toQuad, invHadLinear, pure, invHad]


private def Q2 (x y z w : V3) : ℂ := dot3 x w + dot3 y z

private def Q3 (x y z w : V3) : ℂ :=
  dot3 z (C3 x) + dot3 x (C3 y) + dot3 w (C3 z) + dot3 y (C3 w)

/-- The contribution from using each nonzero Fourier mode once. -/
private def X4 (x y z w : V3) : ℂ :=
  40 * (dot3 x y * dot3 z w + dot3 x z * dot3 y w + dot3 x w * dot3 y z) -
  240 * (x 0 * y 0 * z 0 * w 0 + x 1 * y 1 * z 1 * w 1 + x 2 * y 2 * z 2 * w 2)

private theorem X4_comp (e : Equiv.Perm (Fin 3)) (x y z w : V3) :
    X4 (x ∘ e) (y ∘ e) (z ∘ e) (w ∘ e) = X4 x y z w := by
  have hdot (a b : V3) : dot3 (a ∘ e) (b ∘ e) = dot3 a b := by
    have h := Fintype.sum_equiv e (fun i => a (e i) * b (e i))
      (fun i => a i * b i) (fun _ => rfl)
    simpa only [dot3, Fin.sum_univ_three, Function.comp_apply] using h
  have hdiag := Fintype.sum_equiv e (fun i => x (e i) * y (e i) * z (e i) * w (e i))
    (fun i => x i * y i * z i * w i) (fun _ => rfl)
  simp only [Fin.sum_univ_three] at hdiag
  simp only [X4, hdot, Function.comp_apply, hdiag]

private def P4 (x y z w : V3) : ℂ :=
  -120 * (dot3 y (D3 x) + dot3 x (D3 z) + dot3 w (D3 y) + dot3 z (D3 w)) +
  R4 x w + R4 y z + X4 x y z w

private def mixedHad (x y z w : V3) : ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
    if a.val ≠ b.val ∧ a.val ≠ c.val ∧ a.val ≠ d.val ∧
      b.val ≠ c.val ∧ b.val ≠ d.val ∧ c.val ≠ d.val then
      had x a * had y b * had z c * had w d
    else 0

set_option maxHeartbeats 1000000 in
private theorem mixedHad_eq (x y z w : V3) :
    (c4 1 2 3 4 : ℂ) * mixedHad x y z w = X4 x y z w := by
  norm_num [c4, c3, c2, c1, mixedHad, Fin.sum_univ_four]
  simp only [X4, dot3, had, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def modeRows (x y z w : V3) : Fin 5 → Fin 4 → ℂ :=
  ![fun _ => 1, had x, had y, had z, had w]

set_option maxHeartbeats 2000000 in
private theorem sum_c4_modes (x y z w : V3) :
    let R := modeRows x y z w
    (∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5, ∑ d : Fin 5,
      R a 0 * R b 1 * R c 2 * R d 3 * (c4 a.val b.val c.val d.val : ℂ)) =
    120 + 120 * Q2 x y z w + 160 * Q3 x y z w + P4 x y z w := by
  dsimp only
  rw [P4, ← mixedHad_eq]
  -- Evaluate the character sums before expanding the Hadamard coordinates.
  simp only [Fin.sum_univ_five]
  norm_num [c4, c3, c2, c1, mixedHad, Fin.sum_univ_four]
  simp only [modeRows, had, Q2, Q3, dot3, C3, D3, R4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_mul, mul_one]
  ring

private theorem permSum_had {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (x y z w : V3) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
      (1 + ∑ r : Fin 4, (![had x, had y, had z, had w] : Fin 4 → Fin 4 → ℂ) r i *
        ζ ^ ((r.val + 1) * (f i).val))) =
    120 + 120 * Q2 x y z w + 160 * Q3 x y z w + P4 x y z w := by
  let R := modeRows x y z w
  have hrow (f : Fin 4 ↪ Fin 5) (i : Fin 4) :
      (1 + ∑ r : Fin 4, (![had x, had y, had z, had w] : Fin 4 → Fin 4 → ℂ) r i *
        ζ ^ ((r.val + 1) * (f i).val)) =
      ∑ a : Fin 5, R a i * ζ ^ (a.val * (f i).val) := by
    have hsucc (r : Fin 4) :
        R r.succ = (![had x, had y, had z, had w] : Fin 4 → Fin 4 → ℂ) r := by
      fin_cases r <;> rfl
    have hzero : R 0 i = 1 := rfl
    symm
    rw [Fin.sum_univ_succ]
    simp only [hzero, hsucc, Fin.val_zero, Fin.val_succ, zero_mul, pow_zero, one_mul]
  have hfactor (f : Fin 4 ↪ Fin 5) :
      (∏ i : Fin 4, ∑ a : Fin 5, R a i * ζ ^ (a.val * (f i).val)) =
      ∑ g : Fin 4 → Fin 5, (∏ i : Fin 4, R (g i) i) *
        ζ ^ ((g 0).val * (f 0).val + (g 1).val * (f 1).val +
             (g 2).val * (f 2).val + (g 3).val * (f 3).val) := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.prod_mul_distrib, Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [pow_add, mul_assoc]
  simp_rw [hrow, hfactor]
  rw [Finset.sum_comm]
  have hstep (g : Fin 4 → Fin 5) :
      (∑ f : Fin 4 ↪ Fin 5, (∏ i : Fin 4, R (g i) i) *
        ζ ^ ((g 0).val * (f 0).val + (g 1).val * (f 1).val +
             (g 2).val * (f 2).val + (g 3).val * (f 3).val)) =
      R (g 0) 0 * R (g 1) 1 * R (g 2) 2 * R (g 3) 3 *
        (c4 (g 0).val (g 1).val (g 2).val (g 3).val : ℂ) := by
    rw [← Finset.mul_sum, sum_emb_eq_S4, S4_eq hζ, Fin.prod_univ_four]
  simp_rw [hstep]
  let e : (Fin 4 → Fin 5) ≃ Fin 5 × Fin 5 × Fin 5 × Fin 5 :=
    { toFun := fun g => (g 0, g 1, g 2, g 3)
      invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      left_inv := fun g => by funext i; fin_cases i <;> rfl
      right_inv := fun ⟨a, b, c, d⟩ => rfl }
  calc
    _ = ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5,
        R p.1 0 * R p.2.1 1 * R p.2.2.1 2 * R p.2.2.2 3 *
        (c4 p.1.val p.2.1.val p.2.2.1.val p.2.2.2.val : ℂ) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by simpa only [Fintype.sum_prod_type] using sum_c4_modes x y z w

private abbrev PlaneV2 := Fin 2 → ℂ

private def planeDot (u v : PlaneV2) : ℂ := u 0 * v 0 + u 1 * v 1

private def planeSwapBilin : (PlaneV2 × PlaneV2) ≃ₗ[ℂ] Module.Dual ℂ (PlaneV2 × PlaneV2) where
  toFun p :=
    { toFun := fun q => planeDot p.1 q.2 + planeDot q.1 p.2
      map_add' := fun q1 q2 => by simp only [planeDot, Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
      map_smul' := fun c q => by simp only [planeDot, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' p1 p2 := by
    apply LinearMap.ext
    intro q
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, planeDot, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' c p := by
    apply LinearMap.ext
    intro q
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, planeDot, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  invFun f := (fun i => f (0, Pi.single i 1), fun i => f (Pi.single i 1, 0))
  left_inv p := by
    ext i <;> fin_cases i <;> simp [planeDot]
  right_inv f := by
    apply LinearMap.ext
    rintro ⟨y, z⟩
    have hdecomp : (y, z) =
        y 0 • (Pi.single 0 1, 0) + y 1 • (Pi.single 1 1, 0) +
        z 0 • (0, Pi.single 0 1) + z 1 • (0, Pi.single 1 1) := by
      ext i <;> fin_cases i <;> simp
    conv_rhs => rw [hdecomp]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, planeDot, map_add, map_smul, smul_eq_mul]
    ring

private theorem plane_isotropic_finrank (W : Submodule ℂ (PlaneV2 × PlaneV2))
    (hiso : ∀ p ∈ W, planeDot p.1 p.2 = 0) : Module.finrank ℂ W ≤ 2 := by
  have hle : W.map planeSwapBilin.toLinearMap ≤ W.dualAnnihilator := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro q hq
    have h1 := hiso p hp
    have h2 := hiso q hq
    have h3 := hiso (p + q) (W.add_mem hp hq)
    simp only [planeSwapBilin, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [planeDot, Prod.fst_add, Prod.snd_add, Pi.add_apply] at h1 h2 h3 ⊢
    linear_combination h3 - h1 - h2
  have h1 := LinearEquiv.finrank_map_eq planeSwapBilin W
  have h2 := Submodule.finrank_mono hle
  have h3 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hdim : Module.finrank ℂ (PlaneV2 × PlaneV2) = 4 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun]
  omega

private theorem plane_nonzero (M : Submodule ℂ Quad) (s : ℂ) (hs : s ≠ 0)
    (hquad : ∀ x y z w : V3, (x, y, z, w) ∈ M → Q2 x y z w = 0)
    (hshape : ∀ x y z w : V3, (x, y, z, w) ∈ M →
      y 0 = 0 ∧ y 1 = -s * y 2 ∧ z 0 = 0 ∧ z 2 = -s * z 1 ∧
        w 0 = 0 ∧ w 1 = -s * w 2) : Module.finrank ℂ M ≤ 4 := by
  let f : M →ₗ[ℂ] (PlaneV2 × PlaneV2) :=
    { toFun := fun u =>
        (![u.val.1 2 - s * u.val.1 1, u.val.2.1 2], ![u.val.2.2.2 2, -2 * s * u.val.2.2.1 1])
      map_add' := by
        intro a b
        ext i <;> fin_cases i <;> simp <;> ring
      map_smul' := by
        intro c a
        ext i <;> fin_cases i <;> simp <;> ring }
  have hr : Module.finrank ℂ (LinearMap.range f) ≤ 2 := by
    apply plane_isotropic_finrank
    rintro _ ⟨⟨⟨x, y, z, w⟩, hm⟩, rfl⟩
    obtain ⟨hy0, hy1, hz0, hz2, hw0, hw1⟩ := hshape x y z w hm
    have h := hquad x y z w hm
    simp [Q2, dot3, hy0, hy1, hz0, hz2, hw0, hw1] at h
    change (x 2 - s * x 1) * w 2 + y 2 * (-2 * s * z 1) = 0
    linear_combination h
  let g : LinearMap.ker f →ₗ[ℂ] (ℂ × ℂ) :=
    { toFun := fun u => (u.val.val.1 0, u.val.val.1 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hg : Function.Injective g := by
    suffices hzero : ∀ u, g u = 0 → u = 0 by
      intro u v huv
      apply sub_eq_zero.mp
      exact hzero (u - v) ((map_sub g u v).trans (sub_eq_zero.mpr huv))
    rintro ⟨⟨⟨x, y, z, w⟩, hm⟩, hk⟩ h0
    have hx0 : x 0 = 0 := congrArg Prod.fst h0
    have hx1 : x 1 = 0 := congrArg Prod.snd h0
    have hf : f ⟨(x, y, z, w), hm⟩ = 0 := LinearMap.mem_ker.mp hk
    have hx2 : x 2 - s * x 1 = 0 := congrArg (fun p : PlaneV2 × PlaneV2 => p.1 0) hf
    have hy2 : y 2 = 0 := congrArg (fun p : PlaneV2 × PlaneV2 => p.1 1) hf
    have hw2 : w 2 = 0 := congrArg (fun p : PlaneV2 × PlaneV2 => p.2 0) hf
    have hz : -2 * s * z 1 = 0 := congrArg (fun p : PlaneV2 × PlaneV2 => p.2 1) hf
    have hz1 : z 1 = 0 := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hs)
    obtain ⟨hy0, hy1, hz0, hz2, hw0, hw1⟩ := hshape x y z w hm
    apply Subtype.ext
    apply Subtype.ext
    change (x, y, z, w) = 0
    ext i <;> fin_cases i <;> simp_all
  have hk := LinearMap.finrank_le_finrank_of_injective hg
  have hd : Module.finrank ℂ (ℂ × ℂ) = 2 := by simp [Module.finrank_prod]
  have hn := LinearMap.finrank_range_add_finrank_ker f
  omega

private def Valid (M : Submodule ℂ Quad) : Prop :=
  ∀ x y z w : V3, (x, y, z, w) ∈ M → Q2 x y z w = 0 ∧ Q3 x y z w = 0 ∧ P4 x y z w = 0

set_option maxHeartbeats 1000000 in
private lemma extract_homog {x y z w : V3}
    (h : ∀ t : ℂ, 120 * Q2 (t • x) (t • y) (t • z) (t • w) +
      160 * Q3 (t • x) (t • y) (t • z) (t • w) + P4 (t • x) (t • y) (t • z) (t • w) = 0) :
    Q2 x y z w = 0 ∧ Q3 x y z w = 0 ∧ P4 x y z w = 0 := by
  have hscale (t : ℂ) : t ^ 2 * (120 * Q2 x y z w) + t ^ 3 * (160 * Q3 x y z w) +
      t ^ 4 * P4 x y z w = 0 := by
    have h2 : Q2 (t • x) (t • y) (t • z) (t • w) = t ^ 2 * Q2 x y z w := by
      simp only [Q2, dot3, Pi.smul_apply, smul_eq_mul]; ring
    have h3 : Q3 (t • x) (t • y) (t • z) (t • w) = t ^ 3 * Q3 x y z w := by
      simp only [Q3, C3, dot3, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    have h4 : P4 (t • x) (t • y) (t • z) (t • w) = t ^ 4 * P4 x y z w := by
      simp only [P4, X4, R4, D3, dot3, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    have ht := h t
    rw [h2, h3, h4] at ht
    linear_combination ht
  have h1 := hscale 1
  have hm1 := hscale (-1)
  have h2 := hscale 2
  have hc : Q3 x y z w = 0 := by linear_combination (h1 - hm1) / 320
  have hb : Q2 x y z w = 0 := by linear_combination (16 * h1 - h2 - 1280 * hc) / 1440
  exact ⟨hb, hc, by linear_combination h1 - 120 * hb - 160 * hc⟩

private lemma translate_mem {M : Submodule ℂ Quad} {x y z w u : V3}
    (hp : (x, y, z, w) ∈ M) (hu : (u, 0, 0, 0) ∈ M) (t : ℂ) :
    (x + t • u, y, z, w) ∈ M := by
  simpa [Prod.smul_mk, Prod.mk_add_mk] using M.add_mem hp (M.smul_mem t hu)

set_option maxHeartbeats 1000000 in
private lemma kernel_laws {M : Submodule ℂ Quad} (hM : Valid M)
    {x y z w u : V3} (hp : (x, y, z, w) ∈ M) (hu : (u, 0, 0, 0) ∈ M) :
    dot3 u w = 0 ∧ dot3 z (C3 u) = 0 ∧ dot3 y (D3 u) = 0 := by
  have ht (t : ℂ) := hM _ _ _ _ (translate_mem hp hu t)
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (ht 1).1
    have h0 := (hM _ _ _ _ hp).1
    simp only [Q2, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h0 ⊢
    linear_combination h1 - h0
  · have h1 := (ht 1).2.1
    have hm1 := (ht (-1)).2.1
    have h0 := (hM _ _ _ _ hp).2.1
    simp only [Q3, C3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 hm1 h0 ⊢
    linear_combination (h1 + hm1 - 2 * h0) / 2
  · have h1 := (ht 1).2.2
    have hm1 := (ht (-1)).2.2
    have h2 := (ht 2).2.2
    have hm2 := (ht (-2)).2.2
    simp only [P4, X4, R4, D3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 hm1 h2 hm2 ⊢
    linear_combination -(h2 - hm2 - 2 * h1 + 2 * hm1) / 1440

private lemma axis_free {M : Submodule ℂ Quad} (hM : Valid M)
    (α : V3) (hα0 : α 0 ≠ 0) (hα1 : α 1 ≠ 0) (hα2 : α 2 ≠ 0)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0, 0) ∈ M) :
    ∀ p ∈ M, p.2.2.1 = 0 := by
  rintro ⟨x, y, z, w⟩ hp
  let a : ℂ := -α 0 / α 2
  let b : ℂ := -α 1 / α 2
  have ha : a ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα0) hα2
  have hb : b ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα1) hα2
  have hu (p q : ℂ) : (![p, q, p * a + q * b], 0, 0, 0) ∈ M := by
    apply hU
    simp only [dot3, a, b, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp [hα2]; ring
  have h1 := (kernel_laws hM hp (hu 1 0)).2.1
  have h2 := (kernel_laws hM hp (hu 0 1)).2.1
  have h3 := (kernel_laws hM hp (hu 1 1)).2.1
  simp only [dot3, C3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 h2 h3
  have hz1 : z 1 = 0 := (mul_eq_zero.mp (by linear_combination h1 : a * z 1 = 0)).resolve_left ha
  have hz0 : z 0 = 0 := (mul_eq_zero.mp (by linear_combination h2 : b * z 0 = 0)).resolve_left hb
  have hz2 : z 2 = 0 := by linear_combination h3 - (a + b) * hz0 - (a + b) * hz1
  funext i
  fin_cases i <;> assumption

private lemma axis_shapes {M : Submodule ℂ Quad} (hM : Valid M) (s : ℂ)
    (hU : ∀ a b : ℂ, (![a, b, s * b], 0, 0, 0) ∈ M)
    {x y z w : V3} (hp : (x, y, z, w) ∈ M) :
    y 0 = 0 ∧ y 1 = -s * y 2 ∧ z 2 = -s * z 1 ∧
      s * z 0 = 0 ∧ w 0 = 0 ∧ w 1 = -s * w 2 := by
  obtain ⟨hw0, _, hy0⟩ := kernel_laws hM hp (hU 1 0)
  obtain ⟨hw1, hz0, hy1⟩ := kernel_laws hM hp (hU 0 1)
  obtain ⟨_, hz2, hy2⟩ := kernel_laws hM hp (hU 1 1)
  simp only [dot3, C3, D3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    at hw0 hw1 hy0 hy1 hy2 hz0 hz2
  have hy : y 0 = 0 := by linear_combination hy0
  exact ⟨hy, by linear_combination hy1 - hy2 - s ^ 2 * hy,
    by linear_combination hz2 - hz0, by linear_combination hz0,
    by linear_combination hw0, by linear_combination hw1⟩

set_option maxHeartbeats 1000000 in
private lemma axis_coordinate {M : Submodule ℂ Quad} (hM : Valid M)
    (hU : ∀ a b : ℂ, (![a, b, 0], 0, 0, 0) ∈ M) : ∀ p ∈ M, p.2.2.2 = 0 := by
  rintro ⟨x, y, z, w⟩ hp
  obtain ⟨hy0, hy1, hz2, _, hw0, hw1⟩ := axis_shapes hM 0 (by simpa using hU) hp
  simp only [neg_zero, zero_mul] at hy1 hz2 hw1
  by_cases hw2 : w 2 = 0
  · funext i
    fin_cases i <;> assumption
  · exfalso
    have hquad := (hM _ _ _ _ hp).1
    simp [Q2, dot3, hy0, hy1, hz2, hw0, hw1] at hquad
    have hx2 : x 2 = 0 := hquad.resolve_right hw2
    have ht (t : ℂ) := (hM _ _ _ _ (translate_mem hp (hU 1 0) t)).2.2
    have h1 := ht 1
    have hm1 := ht (-1)
    have h0 := (hM _ _ _ _ hp).2.2
    simp only [P4, X4, R4, D3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hy0, hy1, hz2, hw0, hw1, hx2]
      at h1 hm1 h0
    have hsq : w 2 ^ 2 = 0 := by linear_combination -(h1 + hm1 - 2 * h0) / 80
    exact hw2 (sq_eq_zero_iff.mp hsq)

private lemma axis_normal {M : Submodule ℂ Quad} (hM : Valid M) (hfin : 5 ≤ Module.finrank ℂ M)
    (α : V3) (hα0 : α 0 = 0) (hα2 : α 2 ≠ 0)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0, 0) ∈ M) :
    ∀ p ∈ M, p.2.2.2 = 0 := by
  let s : ℂ := -α 1 / α 2
  have hmem (a b : ℂ) : (![a, b, s * b], 0, 0, 0) ∈ M := by
    apply hU
    simp only [dot3, hα0, s, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp [hα2]; ring
  by_cases hs : s = 0
  · exact axis_coordinate hM (by simpa [hs] using hmem)
  · have hdim := plane_nonzero M s hs (fun x y z w hp => (hM x y z w hp).1) (by
      intro x y z w hp
      obtain ⟨hy0, hy1, hz2, hz0, hw0, hw1⟩ := axis_shapes hM s hmem hp
      exact ⟨hy0, hy1, (mul_eq_zero.mp hz0).resolve_left hs, hz2, hw0, hw1⟩)
    omega

private def permV3 (σ : Equiv.Perm (Fin 3)) : V3 ≃ₗ[ℂ] V3 where
  toFun u := u ∘ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun u := u ∘ σ.symm
  left_inv u := by funext i; simp
  right_inv u := by funext i; simp

private def permQuad (σ : Equiv.Perm (Fin 3)) : Quad ≃ₗ[ℂ] Quad :=
  (permV3 σ).prodCongr ((permV3 σ).prodCongr ((permV3 σ).prodCongr (permV3 σ)))

private lemma perm_dot (i j : Fin 3) (u v : V3) :
    dot3 (permV3 (Equiv.swap i j) u) (permV3 (Equiv.swap i j) v) = dot3 u v := by
  fin_cases i <;> fin_cases j <;> simp [dot3, permV3, Equiv.swap_apply_def, Fin.ext_iff] <;> ring

set_option maxHeartbeats 1500000 in
private lemma perm_Q3 (i j : Fin 3) (x y z w : V3) :
    let p := permV3 (Equiv.swap i j)
    Q3 (p x) (p y) (p z) (p w) = Q3 x y z w := by
  fin_cases i <;> fin_cases j <;>
    simp [Q3, C3, dot3, permV3, Equiv.swap_apply_def, Fin.ext_iff] <;> ring

set_option maxHeartbeats 2500000 in
private lemma perm_P4 (i j : Fin 3) (x y z w : V3) :
    let p := permV3 (Equiv.swap i j)
    P4 (p x) (p y) (p z) (p w) = P4 x y z w := by
  dsimp only
  have hx := X4_comp (Equiv.swap i j) x y z w
  change X4 (permV3 (Equiv.swap i j) x) (permV3 (Equiv.swap i j) y)
    (permV3 (Equiv.swap i j) z) (permV3 (Equiv.swap i j) w) = X4 x y z w at hx
  simp only [P4, hx]
  fin_cases i <;> fin_cases j <;>
    simp [R4, D3, dot3, permV3, Equiv.swap_apply_def, Fin.ext_iff] <;> ring

private def Conclusion (M : Submodule ℂ Quad) : Prop :=
  (∀ p ∈ M, p.2.2.1 = 0) ∨ (∀ p ∈ M, p.2.2.2 = 0)

private lemma swap_reduction {M : Submodule ℂ Quad} {α : V3} (hM : Valid M)
    (hfin : 5 ≤ Module.finrank ℂ M)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0, 0) ∈ M) (i j : Fin 3) :
    let σ := Equiv.swap i j
    let M' := M.map (permQuad σ).toLinearMap
    Valid M' ∧ 5 ≤ Module.finrank ℂ M' ∧
      (∀ u : V3, dot3 (permV3 σ α) u = 0 → (u, 0, 0, 0) ∈ M') ∧
      (Conclusion M' → Conclusion M) := by
  let σ := Equiv.swap i j
  let e := permV3 σ
  let E := permQuad σ
  let M' := M.map E.toLinearMap
  change Valid M' ∧ 5 ≤ Module.finrank ℂ M' ∧
    (∀ u : V3, dot3 (e α) u = 0 → (u, 0, 0, 0) ∈ M') ∧ (Conclusion M' → Conclusion M)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x y z w ⟨⟨a, b, c, d⟩, hp, heq⟩
    change (e a, e b, e c, e d) = (x, y, z, w) at heq
    have hx := congrArg (fun p : Quad => p.1) heq
    have hy := congrArg (fun p : Quad => p.2.1) heq
    have hz := congrArg (fun p : Quad => p.2.2.1) heq
    have hw := congrArg (fun p : Quad => p.2.2.2) heq
    dsimp only at hx hy hz hw
    subst x y z w
    obtain ⟨h2, h3, h4⟩ := hM _ _ _ _ hp
    exact ⟨by simpa only [Q2, e, σ, perm_dot] using h2,
      (perm_Q3 i j _ _ _ _).trans h3, (perm_P4 i j _ _ _ _).trans h4⟩
  · rw [LinearEquiv.finrank_map_eq]; exact hfin
  · intro u hu
    have hαu : dot3 α (e.symm u) = 0 := by
      have h0 := perm_dot i j α (e.symm u)
      change dot3 (e α) (e (e.symm u)) = dot3 α (e.symm u) at h0
      rw [e.apply_symm_apply] at h0
      exact h0.symm.trans hu
    refine ⟨(e.symm u, 0, 0, 0), hU _ hαu, ?_⟩
    change (e (e.symm u), e 0, e 0, e 0) = (u, 0, 0, 0)
    simp
  · rintro (hz | hw)
    · left
      rintro ⟨x, y, z, w⟩ hp
      have h := hz (E (x, y, z, w)) ⟨_, hp, rfl⟩
      change e z = 0 at h
      exact e.injective (h.trans (map_zero e).symm)
    · right
      rintro ⟨x, y, z, w⟩ hp
      have h := hw (E (x, y, z, w)) ⟨_, hp, rfl⟩
      change e w = 0 at h
      exact e.injective (h.trans (map_zero e).symm)

private lemma classify {M : Submodule ℂ Quad} {α : V3} (hM : Valid M)
    (hfin : 5 ≤ Module.finrank ℂ M) (hα : α ≠ 0)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0, 0) ∈ M) : Conclusion M := by
  by_cases h0 : α 0 = 0
  · by_cases h2 : α 2 = 0
    · have h1 : α 1 ≠ 0 := by
        intro h1; apply hα; funext i; fin_cases i <;> assumption
      obtain ⟨hM', hfin', hU', hback⟩ := swap_reduction hM hfin hU 1 2
      apply hback; right
      exact axis_normal hM' hfin' _ (by simpa [permV3, Equiv.swap_apply_def, Fin.ext_iff] using h0)
        (by simpa [permV3] using h1) hU'
    · exact Or.inr (axis_normal hM hfin α h0 h2 hU)
  · by_cases h1 : α 1 = 0
    · by_cases h2 : α 2 = 0
      · obtain ⟨hM', hfin', hU', hback⟩ := swap_reduction hM hfin hU 0 2
        apply hback; right
        exact axis_normal hM' hfin' _ (by simpa [permV3] using h2)
          (by simpa [permV3] using h0) hU'
      · obtain ⟨hM', hfin', hU', hback⟩ := swap_reduction hM hfin hU 0 1
        apply hback; right
        exact axis_normal hM' hfin' _ (by simpa [permV3] using h1)
          (by simpa [permV3, Equiv.swap_apply_def, Fin.ext_iff] using h2) hU'
    · by_cases h2 : α 2 = 0
      · obtain ⟨hM', hfin', hU', hback⟩ := swap_reduction hM hfin hU 0 2
        apply hback; right
        exact axis_normal hM' hfin' _ (by simpa [permV3] using h2)
          (by simpa [permV3] using h0) hU'
      · exact Or.inl (axis_free hM α h0 h1 h2 hU)

private lemma choose_plane (U : Submodule ℂ V3) (hU : 2 ≤ Module.finrank ℂ U) :
    ∃ α : V3, α ≠ 0 ∧ ∀ u : V3, dot3 α u = 0 → u ∈ U := by
  by_cases htop : U = ⊤
  · exact ⟨![0, 0, 1], by intro h; have := congrFun h 2; norm_num at this,
      fun u _ => by simp [htop]⟩
  have hn : Module.finrank ℂ U = 2 := by
    have hk := Submodule.finrank_le U
    rw [Module.finrank_fin_fun] at hk
    by_contra! hne
    have h3 : Module.finrank ℂ U = 3 := by omega
    exact htop (Submodule.eq_top_of_finrank_eq (by rwa [Module.finrank_fin_fun]))
  have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  rw [Module.finrank_fin_fun, hn] at hann
  have hne_bot : U.dualAnnihilator ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hann
    omega
  obtain ⟨f, hf_mem, hf_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  let α : V3 := fun i => f (Pi.single i 1)
  have hf_eq (u : V3) : f u = dot3 α u := by
    have hu : u = u 0 • Pi.single 0 1 + u 1 • Pi.single 1 1 + u 2 • Pi.single 2 1 := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hu]
    simp only [map_add, map_smul, smul_eq_mul, dot3, α]
    ring
  have hα : α ≠ 0 := by
    intro h0
    apply hf_ne
    apply LinearMap.ext
    intro u
    rw [hf_eq, h0]
    simp [dot3]
  have hU_eq : U = LinearMap.ker f := by
    have hle : U ≤ LinearMap.ker f := by
      intro u hu
      rw [Submodule.mem_dualAnnihilator] at hf_mem
      exact hf_mem u hu
    have hfr := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fin_fun] at hfr
    have hex_ne : ∃ u : V3, f u ≠ 0 := by
      by_contra! hall
      exact hf_ne (LinearMap.ext hall)
    obtain ⟨u, hu⟩ := hex_ne
    have hrange_top : LinearMap.range f = ⊤ := by
      rw [eq_top_iff]
      intro c _
      refine ⟨(c / f u) • u, ?_⟩
      rw [map_smul, smul_eq_mul]
      exact div_mul_cancel₀ c hu
    rw [hrange_top, finrank_top, Module.finrank_self] at hfr
    exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
  exact ⟨α, hα, fun u hu => by rw [hU_eq, LinearMap.mem_ker, hf_eq]; exact hu⟩

private lemma solve (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5)
    (L : Submodule ℂ (Fin 4 → Fin 4 → ℂ)) (U : Submodule ℂ (Fin 4 → ℂ))
    (hL : ∀ x ∈ L, (∀ r : Fin 4, (∑ i, x r i) = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + ∑ r : Fin 4, x r i * ζ ^ ((r.val+1)*(f i).val))) = 120)
    (hUL : ∀ u ∈ U, (fun r : Fin 4 => if r = 0 then u else 0) ∈ L)
    (hU : 2 ≤ Module.finrank ℂ U) (hfin : 5 ≤ Module.finrank ℂ L) :
    (∀ x ∈ L, x 2 = 0) ∨ (∀ x ∈ L, x 3 = 0) := by
  classical
  let M := L.map toQuad
  have hdim : Module.finrank ℂ M = Module.finrank ℂ L := by
    have hinj : Function.Injective (toQuad.domRestrict L) := by
      intro a b h
      exact Subtype.ext (toQuad_inj_on_zeroSum (hL a a.property).1 (hL b b.property).1 h)
    have hrange : LinearMap.range (toQuad.domRestrict L) = M := by ext p; simp [M]
    exact hrange ▸ LinearMap.finrank_range_of_inj hinj
  have hValid : Valid M := by
    rintro x y z w ⟨X, hX, heq⟩
    change (invHad (X 0), invHad (X 1), invHad (X 2), invHad (X 3)) = (x, y, z, w) at heq
    have hx := congrArg (fun p : Quad => p.1) heq
    have hy := congrArg (fun p : Quad => p.2.1) heq
    have hz := congrArg (fun p : Quad => p.2.2.1) heq
    have hw := congrArg (fun p : Quad => p.2.2.2) heq
    dsimp only at hx hy hz hw
    subst x y z w
    apply extract_homog
    intro t
    obtain ⟨hsum, hperm⟩ := hL (t • X) (L.smul_mem t hX)
    have hhad (r : Fin 4) : had (t • invHad (X r)) = (t • X) r := by
      have hlin : t • invHad (X r) = invHad ((t • X) r) := by
        ext i; fin_cases i <;> simp [invHad] <;> ring
      rw [hlin, had_invHad _ (hsum r)]
    have hrows : (![had (t • invHad (X 0)), had (t • invHad (X 1)),
        had (t • invHad (X 2)), had (t • invHad (X 3))] : Fin 4 → Fin 4 → ℂ) = t • X := by
      funext r
      fin_cases r
      · exact hhad 0
      · exact hhad 1
      · exact hhad 2
      · exact hhad 3
    have heval := permSum_had hζ (t • invHad (X 0)) (t • invHad (X 1))
      (t • invHad (X 2)) (t • invHad (X 3))
    rw [hrows, hperm] at heval
    linear_combination -heval
  let P := M.comap pure
  have hUzero (u : Fin 4 → ℂ) (hu : u ∈ U) : ∑ i, u i = 0 := by
    simpa using (hL _ (hUL u hu)).1 0
  have hP : 2 ≤ Module.finrank ℂ P := by
    have hinj : Function.Injective (invHadLinear.domRestrict U) := by
      intro a b h
      apply Subtype.ext
      change invHad (a : Fin 4 → ℂ) = invHad (b : Fin 4 → ℂ) at h
      rw [← had_invHad _ (hUzero a a.property), ← had_invHad _ (hUzero b b.property), h]
    have hle : LinearMap.range (invHadLinear.domRestrict U) ≤ P := by
      rintro _ ⟨u, rfl⟩
      exact pure_mem_of_row (hUL u u.property)
    have hr := Submodule.finrank_mono hle
    rw [LinearMap.finrank_range_of_inj hinj] at hr
    exact hU.trans hr
  obtain ⟨α, hα, hnormal⟩ := choose_plane P hP
  rcases classify hValid (hdim.symm ▸ hfin) hα (fun u hu => hnormal u hu) with hz | hw
  · left
    intro X hX
    have h : invHad (X 2) = 0 := hz (toQuad X) ⟨X, hX, rfl⟩
    rw [← had_invHad _ ((hL X hX).1 2), h]
    simp [had]
  · right
    intro X hX
    have h : invHad (X 3) = 0 := hw (toQuad X) ⟨X, hX, rfl⟩
    rw [← had_invHad _ ((hL X hX).1 3), h]
    simp [had]

end Proof

end PEqualNP.Outside.L_gct_284_aux

theorem PEqualNP.Outside.L_gct_284 :
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ 5 →
      ∀ (L : Submodule ℂ (Fin 4 → Fin 4 → ℂ)) (U : Submodule ℂ (Fin 4 → ℂ)),
        (∀ x ∈ L, (∀ r : Fin 4, (∑ i, x r i) = 0) ∧
          (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
            (1 + ∑ r : Fin 4, x r i * ζ ^ ((r.val+1)*(f i).val))) = 120) →
        (∀ u ∈ U, (fun r : Fin 4 => if r = 0 then u else 0) ∈ L) →
        2 ≤ Module.finrank ℂ U → 5 ≤ Module.finrank ℂ L →
          (∀ x ∈ L, x 2 = 0) ∨ (∀ x ∈ L, x 3 = 0) :=
  PEqualNP.Outside.L_gct_284_aux.solve

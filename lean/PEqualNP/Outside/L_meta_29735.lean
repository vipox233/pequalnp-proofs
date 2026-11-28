import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25647

-- Uses the depth-one circuit rank theorem PEqualNP.Outside.L_meta_25647.
-- The pairing rank helpers are adapted from PEqualNP/Outside/L_meta_25830.lean (Apache-2.0).

namespace PEqualNP.Outside.L_meta_29735_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.Outside.L_meta_25647_aux (anchor b2z depthsOf nlGate main)
open Module

def Cheap {n m : ℕ} (G : Fin n → Fin m → Bool) (t : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin 1 → ℕ), ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nlGate ≤ t ∧
    ∀ j : Fin 1, (depthsOf (n+m) C.gates).getD (tap j) 0 ≤ 1 ∧
      Represents G ⟨C.gates, tap j⟩

theorem cheap_iff {n m : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ) :
    Cheap G t ↔ (anchor u v (fun i j => b2z (G i j))).rank ≤ 2*t := by
  rw [main n m G u v t]
  constructor
  · rintro ⟨C, tap, rb, arity, budget, hout⟩
    exact ⟨⟨C.gates, tap 0⟩, ⟨arity, rb, (hout 0).2⟩, (hout 0).1, budget⟩
  · rintro ⟨C, ⟨arity, rb, rep⟩, depth, budget⟩
    exact ⟨C, fun _ => C.output, rb, arity, budget, fun _ => ⟨depth, rep⟩⟩

theorem zmod_of_bool_pred (a : ZMod 2) : b2z (decide (a ≠ 0)) = a := by
  fin_cases a
  · change b2z (decide ((0 : ZMod 2) ≠ 0)) = 0
    decide
  · change b2z (decide ((1 : ZMod 2) ≠ 0)) = 1
    decide

theorem xor_decide (α β : ZMod 2) :
    xor (decide (α ≠ 0)) (decide (β ≠ 0)) = decide (α + β ≠ 0) := by
  fin_cases α <;> fin_cases β <;> decide

section Pairing

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {k : ℕ}

noncomputable def pairCoordinates (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) :
    K →ₗ[F] (Fin k → F) :=
  LinearMap.pi fun i => bit.comp (LinearMap.mulLeft F (b i))

theorem pairCoordinates_apply (b : Basis (Fin k) F K)
    (bit : K →ₗ[F] F) (x : K) (i : Fin k) :
    pairCoordinates b bit x i = bit (b i * x) := rfl

noncomputable def pairEquiv (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hbit : bit ≠ 0) :
    K ≃ₗ[F] (Fin k → F) := by
  letI : FiniteDimensional F K := b.finiteDimensional_of_finite
  have dim : finrank F K = finrank F (Fin k → F) := by
    simp [Module.finrank_eq_card_basis b]
  have hinj : Function.Injective (pairCoordinates b bit) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hn
    have hz : bit.comp (LinearMap.mulLeft F x) = 0 := by
      apply b.ext
      intro i
      have hi := congrFun (LinearMap.mem_ker.mp hx) i
      simpa [pairCoordinates_apply, mul_comm x (b i)] using hi
    apply hbit
    ext y
    have hy := DFunLike.congr_fun hz (x⁻¹ * y)
    simpa [← mul_assoc, mul_inv_cancel₀ hn] using hy
  exact LinearEquiv.ofBijective (pairCoordinates b bit)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mp hinj⟩

noncomputable def pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C : K →ₗ[F] K) : Matrix (Fin k) (Fin k) F :=
  fun i j => bit (b i * C (b j))

theorem pair_toLin_entry (b : Basis (Fin k) F K) (A : Matrix (Fin k) (Fin k) F)
    (i j : Fin k) : Matrix.toLin b (Pi.basisFun F _) A (b j) i = A i j := by
  rw [Matrix.toLin_self]
  simp [Pi.single_apply, mul_ite]

theorem rank_pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (C : K →ₗ[F] K) :
    (pairMatrix b bit C).rank = finrank F (LinearMap.range C) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun F _) b]
  have h : Matrix.toLin b (Pi.basisFun F _) (pairMatrix b bit C) =
      (pairEquiv b bit hbit).toLinearMap.comp C := by
    apply b.ext
    intro j
    funext i
    rw [pair_toLin_entry]
    rfl
  rw [h, LinearMap.range_comp, LinearEquiv.finrank_map_eq]

noncomputable def pairAnchor (A : Matrix (Fin k) (Fin k) F) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
  fun i j => Fin.cases 0 (fun i => Fin.cases 0 (A i) j) i

@[local simp] theorem pairAnchor_zero_left (A : Matrix (Fin k) (Fin k) F) (j : Fin (k + 1)) :
    pairAnchor A 0 j = 0 := rfl

@[local simp] theorem pairAnchor_zero_right (A : Matrix (Fin k) (Fin k) F) (i : Fin (k + 1)) :
    pairAnchor A i 0 = 0 := by
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

@[local simp] theorem pairAnchor_succ_succ (A : Matrix (Fin k) (Fin k) F) (i j : Fin k) :
    pairAnchor A i.succ j.succ = A i j := rfl

theorem rank_pairAnchor (A : Matrix (Fin k) (Fin k) F) : (pairAnchor A).rank = A.rank := by
  classical
  let e : (Fin k → F) →ₗ[F] (Fin (k + 1) → F) :=
    { toFun := Fin.cases 0
      map_add' := by
        intro x y
        funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        simp
      map_smul' := by
        intro a x
        funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        simp }
  let p : (Fin (k + 1) → F) →ₗ[F] (Fin k → F) :=
    { toFun := fun x i => x i.succ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : Function.Injective e := fun _ _ h => funext fun i => congrFun h i.succ
  have hp : LinearMap.range p = ⊤ :=
    LinearMap.range_eq_top.mpr (fun x => ⟨e x, rfl⟩)
  have heq : (pairAnchor A).mulVecLin = e.comp (A.mulVecLin.comp p) := by
    ext x i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [e, Matrix.mulVec, dotProduct]
    · simp [e, p, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [Matrix.rank, Matrix.rank, heq, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ hp]
  exact (Submodule.equivMapOfInjective e he _).finrank_eq.symm

theorem pairAnchor_pairMatrix_apply (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C : K →ₗ[F] K) (i j : Fin (k + 1)) :
    pairAnchor (pairMatrix b bit C) i j =
      bit (Fin.cases 0 b i * C (Fin.cases 0 b j)) := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) j) i
  · simp
  · simp
  · rfl

end Pairing

theorem cheap_table_iff {K : Type*} [Field K] [Algebra (ZMod 2) K] {k : ℕ}
    (b : Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0)
    (D : K →ₗ[ZMod 2] K) (t : ℕ) :
    Cheap (fun (x y : Fin (k+1)) => decide (bit (D (Fin.cases 0 b x) * Fin.cases 0 b y) ≠ 0)) t ↔
      finrank (ZMod 2) (LinearMap.range D) ≤ 2*t := by
  rw [cheap_iff _ 0 0]
  have he : anchor 0 0 (fun (x y : Fin (k+1)) =>
      b2z (decide (bit (D (Fin.cases 0 b x) * Fin.cases 0 b y) ≠ 0))) =
      (pairAnchor (pairMatrix b bit D)).transpose := by
    ext x y
    rw [Matrix.transpose_apply, pairAnchor_pairMatrix_apply]
    simp only [anchor, zmod_of_bool_pred, Fin.cases_zero, map_zero, zero_mul, mul_zero, add_zero]
    rw [mul_comm]
  rw [he, Matrix.rank_transpose, rank_pairAnchor, rank_pairMatrix b bit hbit D]

theorem finrank_restrict (h : ℕ) (hh : 0 < h) {K : Type*} [Field K] [Algebra (ZMod 2) K]
    [Algebra (GaloisField 2 h) K] [FiniteDimensional (GaloisField 2 h) K] [Finite K]
    (D : K →ₗ[GaloisField 2 h] K) (D' : K →ₗ[ZMod 2] K) (hD : ∀ x, D' x = D x) :
    finrank (ZMod 2) (LinearMap.range D') = h * finrank (GaloisField 2 h) (LinearMap.range D) := by
  have h1 := FiniteField.pow_finrank_eq_natCard 2 (LinearMap.range D')
  have h2 := Module.natCard_eq_pow_finrank (K := GaloisField 2 h) (V := LinearMap.range D)
  have h3 : Nat.card (LinearMap.range D') = Nat.card (LinearMap.range D) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp only [LinearMap.mem_range, hD]))
  rw [GaloisField.card 2 h hh.ne'] at h2
  rw [h3, h2, ← pow_mul] at h1
  exact Nat.pow_right_injective (le_refl 2) h1

theorem rank_lt_iff {E K : Type*} [Field E] [AddCommGroup K] [Module E K] [FiniteDimensional E K]
    {m : ℕ} (hK : finrank E K = m) (D : K →ₗ[E] K) :
    finrank E (LinearMap.range D) < m ↔ ∃ x, x ≠ 0 ∧ D x = 0 := by
  have hr := D.finrank_range_add_finrank_ker
  constructor
  · intro hlt
    have hpos : 0 < finrank E (LinearMap.ker D) := by omega
    obtain ⟨⟨x, hx⟩, hx0⟩ := (Module.finrank_pos_iff_exists_ne_zero).mp hpos
    exact ⟨x, fun h => hx0 (Subtype.ext h), hx⟩
  · rintro ⟨x, hx0, hx⟩
    have hpos : 0 < finrank E (LinearMap.ker D) :=
      (Module.finrank_pos_iff_exists_ne_zero).mpr ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩
    omega

theorem hr_iff (h m t r : ℕ) (hk1 : h*m - h ≤ 2*t) (hk2 : 2*t < h*m) :
    h * r ≤ 2 * t ↔ r < m := by
  constructor
  · intro h1
    by_contra hc
    have : h * m ≤ h * r := Nat.mul_le_mul_left h (by omega)
    omega
  · intro h1
    have h2 : h * r ≤ h * (m - 1) := Nat.mul_le_mul_left h (by omega)
    have h3 : h * (m - 1) = h * m - h := Nat.mul_sub_one h m
    omega

theorem served_table {K E : Type*} [Field K] [Algebra (ZMod 2) K] [Field E] [Algebra E K]
    [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) E K] {k : ℕ}
    (b : Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2) (z : K) (C : K →ₗ[E] K) :
    (fun (x y : Fin (k+1)) => xor (decide (bit (z * Fin.cases 0 b x * Fin.cases 0 b y) ≠ 0))
      (decide (bit (C (Fin.cases 0 b x) * Fin.cases 0 b y) ≠ 0))) =
    (fun (x y : Fin (k+1)) => decide (bit (((LinearMap.mulLeft E z + C).restrictScalars (ZMod 2))
      (Fin.cases 0 b x) * Fin.cases 0 b y) ≠ 0)) := by
  funext x y
  rw [xor_decide]
  simp only [LinearMap.restrictScalars_apply, LinearMap.add_apply, add_mul,
    LinearMap.mulLeft_apply, map_add]

theorem served_iff (h m t : ℕ) (hh : 0 < h) (hk1 : h*m - h ≤ 2*t) (hk2 : 2*t < h*m)
    {K : Type*} [Field K] [Algebra (ZMod 2) K] [Algebra (GaloisField 2 h) K]
    [IsScalarTower (ZMod 2) (GaloisField 2 h) K] [FiniteDimensional (GaloisField 2 h) K] [Finite K]
    (hK : finrank (GaloisField 2 h) K = m)
    (b : Basis (Fin (h*m)) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0)
    (z : K) (C : K →ₗ[GaloisField 2 h] K) :
    Cheap (fun (x y : Fin (h*m+1)) => xor (decide (bit (z * Fin.cases 0 b x * Fin.cases 0 b y) ≠ 0))
      (decide (bit (C (Fin.cases 0 b x) * Fin.cases 0 b y) ≠ 0))) t ↔
      ∃ x, x ≠ 0 ∧ z * x + C x = 0 := by
  rw [served_table b bit z C, cheap_table_iff b bit hbit _ t,
    finrank_restrict h hh (LinearMap.mulLeft (GaloisField 2 h) z + C)
      ((LinearMap.mulLeft (GaloisField 2 h) z + C).restrictScalars (ZMod 2)) (fun x => rfl),
    hr_iff h m t _ hk1 hk2, rank_lt_iff hK]
  simp only [LinearMap.add_apply, LinearMap.mulLeft_apply]

theorem table_cheap (h m : ℕ) (hh : 0 < h) {K : Type*} [Field K] [Algebra (ZMod 2) K]
    [Algebra (GaloisField 2 h) K] [IsScalarTower (ZMod 2) (GaloisField 2 h) K]
    [FiniteDimensional (GaloisField 2 h) K] [Finite K]
    (b : Basis (Fin (h*m)) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0)
    (C : K →ₗ[GaloisField 2 h] K) (s : ℕ) :
    Cheap (fun (x y : Fin (h*m+1)) => decide (bit (C (Fin.cases 0 b x) * Fin.cases 0 b y) ≠ 0)) s ↔
      h * finrank (GaloisField 2 h) (LinearMap.range C) ≤ 2 * s := by
  rw [← finrank_restrict h hh C (C.restrictScalars (ZMod 2)) (fun x => rfl)]
  exact cheap_table_iff b bit hbit (C.restrictScalars (ZMod 2)) s

-- The grid bound.

def Lq (q n d : ℕ) : ℕ :=
  q ^ (n - min d (n * (q - 1)) / (q - 1)) -
    min d (n * (q - 1)) % (q - 1) * q ^ (n - min d (n * (q - 1)) / (q - 1) - 1)

theorem Lq_big (q n d : ℕ) (hq : 2 ≤ q) (h : n * (q - 1) ≤ d) : Lq q n d = 1 := by
  have hN : 0 < q - 1 := by omega
  unfold Lq
  rw [min_eq_right h, Nat.mul_div_cancel _ hN]
  simp

theorem Lq_dec (q n d a b : ℕ) (hq : 2 ≤ q) (hd : d = b + (q - 1) * a) (hb : b < q - 1)
    (ha : a < n) : Lq q n d = (q - b) * q ^ (n - 1 - a) := by
  have hN : 0 < q - 1 := by omega
  have hlt : d < n * (q - 1) := by
    have h1 : (q - 1) * (a + 1) ≤ (q - 1) * n := Nat.mul_le_mul_left _ ha
    have h2 : (q - 1) * (a + 1) = (q - 1) * a + (q - 1) := by ring
    have h3 : n * (q - 1) = (q - 1) * n := Nat.mul_comm _ _
    omega
  have hdiv : d / (q - 1) = a := by
    rw [hd, Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hb, zero_add]
  have hmod : d % (q - 1) = b := by
    rw [hd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  unfold Lq
  rw [min_eq_left hlt.le, hdiv, hmod]
  have e1 : n - a = (n - 1 - a) + 1 := by omega
  rw [e1, Nat.add_sub_cancel, pow_succ, Nat.sub_mul, Nat.mul_comm (q ^ (n - 1 - a)) q]

theorem Lq_step (q n d e : ℕ) (hq : 2 ≤ q) (he : e ≤ q - 1) (hed : e ≤ d) :
    Lq q (n+1) d ≤ (q - e) * Lq q n (d - e) := by
  have hN : 0 < q - 1 := by omega
  by_cases h1 : n * (q - 1) ≤ d - e
  · rw [Lq_big q n (d - e) hq h1, mul_one]
    by_cases h2 : (n + 1) * (q - 1) ≤ d
    · rw [Lq_big q (n + 1) d hq h2]
      omega
    · have h3 : (n + 1) * (q - 1) = (q - 1) * n + (q - 1) := by ring
      have h4 : n * (q - 1) = (q - 1) * n := Nat.mul_comm _ _
      rw [Lq_dec q (n + 1) d n (d - (q - 1) * n) hq (by omega) (by omega) (by omega)]
      rw [show n + 1 - 1 - n = 0 by omega, pow_zero, mul_one]
      omega
  · push_neg at h1
    have hdm := Nat.mod_add_div (d - e) (q - 1)
    have hb' : (d - e) % (q - 1) < q - 1 := Nat.mod_lt _ hN
    have ha' : (d - e) / (q - 1) < n := (Nat.div_lt_iff_lt_mul hN).mpr h1
    rw [Lq_dec q n (d - e) ((d - e) / (q - 1)) ((d - e) % (q - 1)) hq hdm.symm hb' ha']
    generalize (d - e) / (q - 1) = a' at hdm hb' ha' ⊢
    generalize (d - e) % (q - 1) = b' at hdm hb' ha' ⊢
    by_cases h3 : b' + e < q - 1
    · rw [Lq_dec q (n + 1) d a' (b' + e) hq (by omega) h3 (by omega)]
      rw [show n + 1 - 1 - a' = (n - 1 - a') + 1 by omega, pow_succ]
      have key : (q - (b' + e)) * q ≤ (q - e) * (q - b') := by
        obtain ⟨r, hr⟩ : ∃ r, q = b' + e + r + 2 := ⟨q - b' - e - 2, by omega⟩
        have e1 : q - (b' + e) = r + 2 := by omega
        have e2 : q - e = b' + r + 2 := by omega
        have e3 : q - b' = e + r + 2 := by omega
        rw [e1, e2, e3, hr]
        nlinarith [Nat.zero_le (b' * e)]
      calc (q - (b' + e)) * (q ^ (n - 1 - a') * q)
          = ((q - (b' + e)) * q) * q ^ (n - 1 - a') := by ring
        _ ≤ ((q - e) * (q - b')) * q ^ (n - 1 - a') := Nat.mul_le_mul_right _ key
        _ = (q - e) * ((q - b') * q ^ (n - 1 - a')) := by ring
    · push_neg at h3
      have h5 : (q - 1) * (a' + 1) = (q - 1) * a' + (q - 1) := by ring
      rw [Lq_dec q (n + 1) d (a' + 1) (b' + e - (q - 1)) hq (by omega) (by omega) (by omega)]
      rw [show n + 1 - 1 - (a' + 1) = n - 1 - a' by omega]
      have key : q - (b' + e - (q - 1)) ≤ (q - e) * (q - b') := by
        have hs1 : 1 ≤ q - e := by omega
        have hu2 : 2 ≤ q - b' := by omega
        have e3 : q - (b' + e - (q - 1)) = (q - e) + (q - b') - 1 := by omega
        rw [e3]
        generalize q - e = s at hs1 ⊢
        generalize q - b' = u at hu2 ⊢
        have : s + u ≤ s * u + 1 := by nlinarith
        omega
      calc (q - (b' + e - (q - 1))) * q ^ (n - 1 - a')
          ≤ ((q - e) * (q - b')) * q ^ (n - 1 - a') := Nat.mul_le_mul_right _ key
        _ = (q - e) * ((q - b') * q ^ (n - 1 - a')) := by ring

def redExp (q e : ℕ) : ℕ := if e = 0 then 0 else (e - 1) % (q - 1) + 1

theorem redExp_le (q e : ℕ) : redExp q e ≤ e := by
  unfold redExp
  split_ifs with h
  · omega
  · have := Nat.mod_le (e - 1) (q - 1)
    omega

theorem redExp_le_q (q e : ℕ) (hq : 2 ≤ q) : redExp q e ≤ q - 1 := by
  unfold redExp
  split_ifs with h
  · omega
  · have := Nat.mod_lt (e - 1) (show 0 < q - 1 by omega)
    omega

theorem pow_redExp {E : Type*} [Field E] [Fintype E] (x : E) (e : ℕ) :
    x ^ redExp (Fintype.card E) e = x ^ e := by
  unfold redExp
  split_ifs with he
  · rw [he]
  · by_cases hx : x = 0
    · rw [hx, zero_pow (Nat.succ_ne_zero _), zero_pow he]
    · have h1 : x ^ (Fintype.card E - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx
      have hdec : e = (e - 1) % (Fintype.card E - 1) + 1 +
          (Fintype.card E - 1) * ((e - 1) / (Fintype.card E - 1)) := by
        have := Nat.mod_add_div (e - 1) (Fintype.card E - 1)
        omega
      conv_rhs => rw [hdec, pow_add, pow_mul, h1, one_pow, mul_one]

theorem reduce {E : Type*} [Field E] [Fintype E] {σ : Type*} (p : MvPolynomial σ E) :
    ∃ p' : MvPolynomial σ E, (∀ v, MvPolynomial.eval v p' = MvPolynomial.eval v p) ∧
      p'.totalDegree ≤ p.totalDegree ∧ ∀ i, p'.degreeOf i ≤ Fintype.card E - 1 := by
  classical
  have hq : 2 ≤ Fintype.card E := Fintype.one_lt_card
  let red : (σ →₀ ℕ) → (σ →₀ ℕ) := fun s =>
    Finsupp.mapRange (redExp (Fintype.card E)) (by simp [redExp]) s
  refine ⟨∑ s ∈ p.support, MvPolynomial.monomial (red s) (p.coeff s), ?_, ?_, ?_⟩
  · intro v
    rw [map_sum, MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [red]
    rw [MvPolynomial.eval_monomial, Finsupp.prod_mapRange_index (fun i => pow_zero _)]
    congr 1
    simp only [Finsupp.prod, pow_redExp]
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
    simp only [red]
    rw [Finsupp.sum_mapRange_index (fun _ => rfl)]
    simp only [Finsupp.sum, id]
    exact Finset.sum_le_sum fun i _ => redExp_le _ _
  · intro i
    rw [MvPolynomial.degreeOf_le_iff]
    intro t ht
    obtain ⟨s, _, hts⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum ht)
    have := MvPolynomial.support_monomial_subset hts
    rw [Finset.mem_singleton] at this
    rw [this]
    simp only [red, Finsupp.mapRange_apply]
    exact redExp_le_q _ _ hq

theorem af {E : Type*} [Field E] [Fintype E] [DecidableEq E] :
    ∀ (n d : ℕ) (p : MvPolynomial (Fin n) E), p ≠ 0 →
      (∀ i, p.degreeOf i ≤ Fintype.card E - 1) → p.totalDegree ≤ d →
      Lq (Fintype.card E) n d ≤
        (Finset.univ.filter (fun x : Fin n → E => MvPolynomial.eval x p ≠ 0)).card
  | 0, d, p, hp, _, _ => by
    have hq : 2 ≤ Fintype.card E := Fintype.one_lt_card
    rw [Lq_big (Fintype.card E) 0 d hq (by simp), Finset.one_le_card]
    refine ⟨fun i => i.elim0, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [p.eq_C_of_isEmpty, MvPolynomial.eval_C]
    intro h0
    apply hp
    rw [p.eq_C_of_isEmpty, h0, map_zero]
  | n+1, d, p, hp, hred, hdeg => by
    have hq : 2 ≤ Fintype.card E := Fintype.one_lt_card
    have hp'0 : MvPolynomial.finSuccEquiv E n p ≠ 0 := EmbeddingLike.map_ne_zero_iff.2 hp
    have hpk0 : (MvPolynomial.finSuccEquiv E n p).leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hp'0
    have hkdeg : (MvPolynomial.finSuccEquiv E n p).natDegree = p.degreeOf 0 :=
      MvPolynomial.natDegree_finSuccEquiv p
    have hkq : (MvPolynomial.finSuccEquiv E n p).natDegree ≤ Fintype.card E - 1 := by
      rw [hkdeg]; exact hred 0
    have hpkdeg : (MvPolynomial.finSuccEquiv E n p).leadingCoeff.totalDegree +
        (MvPolynomial.finSuccEquiv E n p).natDegree ≤ p.totalDegree :=
      MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le p _ hpk0
    have hpkred : ∀ j, (MvPolynomial.finSuccEquiv E n p).leadingCoeff.degreeOf j ≤
        Fintype.card E - 1 := fun j =>
      (MvPolynomial.degreeOf_coeff_finSuccEquiv p j _).trans (hred j.succ)
    have ih := af n (d - (MvPolynomial.finSuccEquiv E n p).natDegree)
      (MvPolynomial.finSuccEquiv E n p).leadingCoeff hpk0 hpkred (by omega)
    have hslice : ∀ xt : Fin n → E,
        MvPolynomial.eval xt (MvPolynomial.finSuccEquiv E n p).leadingCoeff ≠ 0 →
        Fintype.card E - (MvPolynomial.finSuccEquiv E n p).natDegree ≤
          (Finset.univ.filter (fun x0 : E =>
            MvPolynomial.eval (Fin.cons x0 xt : Fin (n+1) → E) p ≠ 0)).card := by
      intro xt hxt
      have hpxdeg : (Polynomial.map (MvPolynomial.eval xt)
          (MvPolynomial.finSuccEquiv E n p)).natDegree =
          (MvPolynomial.finSuccEquiv E n p).natDegree :=
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hxt
      have hpx0 : Polynomial.map (MvPolynomial.eval xt) (MvPolynomial.finSuccEquiv E n p) ≠ 0 := by
        intro h
        apply hxt
        have hc : (Polynomial.map (MvPolynomial.eval xt) (MvPolynomial.finSuccEquiv E n p)).coeff
            (MvPolynomial.finSuccEquiv E n p).natDegree =
            MvPolynomial.eval xt (MvPolynomial.finSuccEquiv E n p).leadingCoeff :=
          Polynomial.coeff_map _ _
        rw [← hc, h, Polynomial.coeff_zero]
      have hzeros : (Finset.univ.filter (fun x0 : E =>
          MvPolynomial.eval (Fin.cons x0 xt : Fin (n+1) → E) p = 0)).card ≤
          (MvPolynomial.finSuccEquiv E n p).natDegree := by
        rw [← hpxdeg]
        apply Polynomial.card_le_degree_of_subset_roots
        intro x0 hx0
        rw [Finset.mem_val, Finset.mem_filter] at hx0
        rw [Polynomial.mem_roots hpx0, Polynomial.IsRoot.def, ← MvPolynomial.eval_eq_eval_mv_eval']
        exact hx0.2
      have hunion : Finset.univ.filter (fun x0 : E =>
            MvPolynomial.eval (Fin.cons x0 xt : Fin (n+1) → E) p = 0) ∪
          Finset.univ.filter (fun x0 : E =>
            MvPolynomial.eval (Fin.cons x0 xt : Fin (n+1) → E) p ≠ 0) = Finset.univ := by
        ext x0
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact em _
      have hle := Finset.card_union_le (Finset.univ.filter (fun x0 : E =>
            MvPolynomial.eval (Fin.cons x0 xt : Fin (n+1) → E) p = 0))
          (Finset.univ.filter (fun x0 : E =>
            MvPolynomial.eval (Fin.cons x0 xt : Fin (n+1) → E) p ≠ 0))
      rw [hunion, Finset.card_univ] at hle
      omega
    have hcount : (Finset.univ.filter (fun x : Fin (n+1) → E => MvPolynomial.eval x p ≠ 0)).card =
        ∑ xt : Fin n → E, (Finset.univ.filter (fun x0 : E =>
          MvPolynomial.eval (Fin.cons x0 xt : Fin (n+1) → E) p ≠ 0)).card := by
      rw [Finset.card_filter]
      rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => E))
        (fun y => if MvPolynomial.eval (Fin.cons y.1 y.2 : Fin (n+1) → E) p ≠ 0 then 1 else 0)
        (fun x => if MvPolynomial.eval x p ≠ 0 then 1 else 0) (fun y => rfl)]
      rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun xt _ => ?_
      simp only [Finset.card_filter]
    calc Lq (Fintype.card E) (n+1) d
        ≤ (Fintype.card E - (MvPolynomial.finSuccEquiv E n p).natDegree) *
            Lq (Fintype.card E) n (d - (MvPolynomial.finSuccEquiv E n p).natDegree) :=
          Lq_step _ n d _ hq hkq (by omega)
      _ ≤ (Fintype.card E - (MvPolynomial.finSuccEquiv E n p).natDegree) *
            (Finset.univ.filter (fun xt : Fin n → E =>
              MvPolynomial.eval xt (MvPolynomial.finSuccEquiv E n p).leadingCoeff ≠ 0)).card :=
          Nat.mul_le_mul_left _ ih
      _ = ∑ xt ∈ Finset.univ.filter (fun xt : Fin n → E =>
              MvPolynomial.eval xt (MvPolynomial.finSuccEquiv E n p).leadingCoeff ≠ 0),
            (Fintype.card E - (MvPolynomial.finSuccEquiv E n p).natDegree) := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ xt ∈ Finset.univ.filter (fun xt : Fin n → E =>
              MvPolynomial.eval xt (MvPolynomial.finSuccEquiv E n p).leadingCoeff ≠ 0),
            (Finset.univ.filter (fun x0 : E =>
              MvPolynomial.eval (Fin.cons x0 xt : Fin (n+1) → E) p ≠ 0)).card :=
          Finset.sum_le_sum fun xt hxt => hslice xt (Finset.mem_filter.mp hxt).2
      _ ≤ ∑ xt : Fin n → E, (Finset.univ.filter (fun x0 : E =>
              MvPolynomial.eval (Fin.cons x0 xt : Fin (n+1) → E) p ≠ 0)).card :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = _ := hcount.symm

theorem detPolyMat {E : Type*} [Field E] {m r : ℕ} (B : Fin m → Matrix (Fin r) (Fin r) E) :
    ∃ Q : MvPolynomial (Fin m) E, Q.totalDegree ≤ r ∧
      ∀ v : Fin m → E, MvPolynomial.eval v Q = (1 + ∑ j, v j • B j).det := by
  let A : Matrix (Fin r) (Fin r) (MvPolynomial (Fin m) E) :=
    1 + ∑ j, (MvPolynomial.X j : MvPolynomial (Fin m) E) • (B j).map MvPolynomial.C
  have hA : ∀ a b, A a b =
      (if a = b then 1 else 0) + ∑ j, MvPolynomial.X j * MvPolynomial.C (B j a b) := by
    intro a b
    simp only [A, Matrix.add_apply, Matrix.one_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul]
  have hent : ∀ a b, (A a b).totalDegree ≤ 1 := by
    intro a b
    rw [hA]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · split_ifs <;> simp
    · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      simp [MvPolynomial.totalDegree_X]
  refine ⟨A.det, ?_, ?_⟩
  · rw [Matrix.det_apply']
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ => ?_)
    have hprod : (∏ a, A (σ a) a).totalDegree ≤ r := by
      refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
      calc ∑ a, (A (σ a) a).totalDegree ≤ ∑ _a : Fin r, 1 :=
            Finset.sum_le_sum fun a _ => hent _ _
        _ = r := by simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, Units.val_one, Int.cast_one, one_mul]
      exact hprod
    · rw [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul,
        MvPolynomial.totalDegree_neg]
      exact hprod
  · intro v
    rw [RingHom.map_det]
    congr 1
    simp only [A, map_add, map_one, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ext a b
    simp [Matrix.smul_apply]

theorem detPoly {E K : Type*} [Field E] [Field K] [Algebra E K] [FiniteDimensional E K] {m : ℕ}
    (eB : Basis (Fin m) E K) (C : K →ₗ[E] K) :
    ∃ Q : MvPolynomial (Fin m) E, Q.totalDegree ≤ finrank E (LinearMap.range C) ∧
      MvPolynomial.eval 0 Q = 1 ∧
      ∀ w : K, (∃ x, x ≠ 0 ∧ x + w * C x = 0) → MvPolynomial.eval (⇑(eB.repr w)) Q = 0 := by
  classical
  let bR : Basis (Fin (finrank E (LinearMap.range C))) E (LinearMap.range C) :=
    Module.finBasisOfFinrankEq E _ rfl
  let L : Fin m → (LinearMap.range C →ₗ[E] LinearMap.range C) := fun j =>
    C.rangeRestrict ∘ₗ LinearMap.mulLeft E (eB j) ∘ₗ (LinearMap.range C).subtype
  obtain ⟨Q, hdeg, heval⟩ := detPolyMat (fun j => LinearMap.toMatrix bR bR (L j))
  refine ⟨Q, hdeg, ?_, ?_⟩
  · rw [heval]
    simp
  · rintro w ⟨x, hx0, hx⟩
    rw [heval, ← Matrix.exists_mulVec_eq_zero_iff]
    have hCx : C x ≠ 0 := by
      intro h0
      rw [h0, mul_zero, add_zero] at hx
      exact hx0 hx
    refine ⟨⇑(bR.repr (C.rangeRestrict x)), ?_, ?_⟩
    · intro h0
      apply hCx
      have h1 : bR.repr (C.rangeRestrict x) = 0 := by
        ext i
        simpa using congrFun h0 i
      have h2 : C.rangeRestrict x = 0 := by simpa using h1
      have h3 := congrArg Subtype.val h2
      simpa using h3
    · have hmat : (1 + ∑ j, (eB.repr w) j • LinearMap.toMatrix bR bR (L j)) =
          LinearMap.toMatrix bR bR (LinearMap.id + ∑ j, (eB.repr w) j • L j) := by
        rw [map_add, LinearMap.toMatrix_id, map_sum]
        simp_rw [map_smul]
      have key : ∑ j, (eB.repr w) j • (eB j * C x) = w * C x := by
        simp_rw [← smul_mul_assoc]
        rw [← Finset.sum_mul, eB.sum_repr]
      have hzero : ((LinearMap.id + ∑ j, (eB.repr w) j • L j :
          LinearMap.range C →ₗ[E] LinearMap.range C) (C.rangeRestrict x)) = 0 := by
        apply Subtype.ext
        simp only [L, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_add,
          Submodule.coe_sum, Submodule.coe_smul, LinearMap.codRestrict_apply,
          LinearMap.rangeRestrict, Submodule.subtype_apply, LinearMap.mulLeft_apply,
          Submodule.coe_zero]
        rw [show ∑ j, (eB.repr w) j • C (eB j * C x) = C (w * C x) by
          rw [← key, map_sum]
          simp_rw [map_smul]]
        rw [← map_add, hx, map_zero]
      rw [hmat, LinearMap.toMatrix_mulVec_repr, hzero]
      simp

theorem upper {E K : Type*} [Field E] [Fintype E] [DecidableEq E] [Field K] [Algebra E K]
    [FiniteDimensional E K] [DecidableEq K] (q : ℕ) (hq : Fintype.card E = q) (m budget : ℕ)
    (hK : finrank E K = m) (l : ℕ) (C : Fin l → (K →ₗ[E] K)) (S : Finset K) (h0 : (0:K) ∉ S)
    (hbud : ∑ i, finrank E (LinearMap.range (C i)) ≤ budget)
    (hS : ∀ z ∈ S, ∃ i, ∃ x, x ≠ 0 ∧ z * x + C i x = 0) :
    S.card + Lq q m budget ≤ q ^ m := by
  classical
  subst hq
  let eB : Basis (Fin m) E K := Module.finBasisOfFinrankEq E K hK
  choose Q hQdeg hQ0 hQw using fun i => detPoly eB (C i)
  have hPdeg : (∏ i, Q i).totalDegree ≤ budget :=
    ((MvPolynomial.totalDegree_finsetProd _ _).trans
      (Finset.sum_le_sum fun i _ => hQdeg i)).trans hbud
  have hP0 : MvPolynomial.eval 0 (∏ i, Q i) = 1 := by
    rw [map_prod]
    simp only [hQ0, Finset.prod_const_one]
  obtain ⟨P', hP'eval, hP'deg, hP'red⟩ := reduce (∏ i, Q i)
  have hP'ne : P' ≠ 0 := by
    intro h
    have := hP'eval 0
    rw [h, map_zero, hP0] at this
    exact zero_ne_one this
  have hAF := af m budget P' hP'ne hP'red (hP'deg.trans hPdeg)
  have hgood : (Finset.univ.filter (fun v : Fin m → E => MvPolynomial.eval v P' ≠ 0)) =
      (Finset.univ.filter (fun v : Fin m → E => MvPolynomial.eval v (∏ i, Q i) ≠ 0)) := by
    ext v
    simp [hP'eval]
  rw [hgood] at hAF
  have hinj : S.card ≤
      (Finset.univ.filter (fun v : Fin m → E => MvPolynomial.eval v (∏ i, Q i) = 0)).card := by
    apply Finset.card_le_card_of_injOn (fun z => ⇑(eB.repr z⁻¹))
    · intro z hz
      rw [Finset.mem_coe] at hz
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨i, x, hx0, hx⟩ := hS z hz
      have hz0 : z ≠ 0 := fun h => h0 (h ▸ hz)
      have hw : ∃ y, y ≠ 0 ∧ y + z⁻¹ * C i y = 0 := by
        refine ⟨x, hx0, ?_⟩
        have h1 := congrArg (fun u => z⁻¹ * u) hx
        simp only [mul_add, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul, mul_zero] at h1
        exact h1
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hQw i z⁻¹ hw)
    · intro z1 _ z2 _ heq
      have h1 : eB.repr z1⁻¹ = eB.repr z2⁻¹ := DFunLike.coe_injective heq
      exact inv_injective (eB.repr.injective h1)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m → E)))
    (fun v => MvPolynomial.eval v (∏ i, Q i) = 0)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hsplit
  have hne : (Finset.univ.filter (fun v : Fin m → E => ¬ MvPolynomial.eval v (∏ i, Q i) = 0)).card =
      (Finset.univ.filter (fun v : Fin m → E => MvPolynomial.eval v (∏ i, Q i) ≠ 0)).card := rfl
  omega

theorem prod_box (q N c a b : ℕ) (hqN : q = N + 1) (hc : c = b + N * a) (hb : b < N) :
    ∀ M, ∏ j ∈ Finset.range M, (q - min N (c - N * j)) =
      if M ≤ a then 1 else (q - b) * q ^ (M - a - 1)
  | 0 => by simp
  | M+1 => by
    rw [Finset.prod_range_succ, prod_box q N c a b hqN hc hb M]
    by_cases h1 : M + 1 ≤ a
    · have h2 : M ≤ a := by omega
      have h3 : min N (c - N * M) = N := by
        apply min_eq_left
        have h6 : N * (M + 1) ≤ N * a := Nat.mul_le_mul_left _ h1
        have h7 : N * (M + 1) = N * M + N := by ring
        omega
      rw [if_pos h2, if_pos h1, h3]
      omega
    · by_cases h4 : M = a
      · have h3 : min N (c - N * M) = b := by
          rw [h4, hc, Nat.add_sub_cancel]
          exact min_eq_right hb.le
        rw [if_pos (le_of_eq h4), if_neg h1, h3, show M + 1 - a - 1 = 0 by omega, pow_zero,
          mul_one, one_mul]
      · have h5 : a < M := by omega
        have h3 : min N (c - N * M) = 0 := by
          have h6 : N * (a + 1) ≤ N * M := Nat.mul_le_mul_left _ h5
          have h7 : N * (a + 1) = N * a + N := by ring
          have h8 : c - N * M = 0 := by omega
          rw [h8]
          exact min_eq_right (Nat.zero_le _)
        rw [if_neg (show ¬ (M ≤ a) by omega), if_neg h1, h3, Nat.sub_zero,
          show M + 1 - a - 1 = (M - a - 1) + 1 by omega, pow_succ, mul_assoc]

theorem attain {E K : Type*} [Field E] [Fintype E] [DecidableEq E] [Field K] [Algebra E K]
    [FiniteDimensional E K] [DecidableEq K] (q : ℕ) (hq : Fintype.card E = q) (m budget : ℕ)
    (hK : finrank E K = m) :
    ∃ (C : Fin (min budget (m * (q - 1))) → (K →ₗ[E] K)) (S : Finset K), (0:K) ∉ S ∧
      (∀ i, finrank E (LinearMap.range (C i)) = 1) ∧
      (∀ z ∈ S, ∃ i, ∃ x, x ≠ 0 ∧ z * x + C i x = 0) ∧ S.card + Lq q m budget = q ^ m := by
  classical
  subst hq
  have hq2 : 2 ≤ Fintype.card E := Fintype.one_lt_card
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card E - 1 = N := ⟨_, rfl⟩
  have hNpos : 0 < N := by omega
  have hqN : Fintype.card E = N + 1 := by omega
  obtain ⟨c, hc⟩ : ∃ c, min budget (m * N) = c := ⟨_, rfl⟩
  rw [hN, hc]
  have hcm : c ≤ m * N := by
    rw [← hc]
    exact min_le_right _ _
  let eB : Basis (Fin m) E K := Module.finBasisOfFinrankEq E K hK
  have hcardU : Fintype.card Eˣ = N := by rw [Fintype.card_units, hN]
  let enum : Fin N ≃ Eˣ := (Fintype.equivFinOfCardEq hcardU).symm
  let jj : Fin c → Fin m := fun i =>
    ⟨i.val / N, (Nat.div_lt_iff_lt_mul hNpos).mpr (lt_of_lt_of_le i.isLt hcm)⟩
  let rr : Fin c → Fin N := fun i => ⟨i.val % N, Nat.mod_lt _ hNpos⟩
  let lam : Fin c → E := fun i => ((enum (rr i) : Eˣ) : E)
  have hlam : ∀ i, lam i ≠ 0 := fun i => Units.ne_zero _
  let Cm : Fin c → (K →ₗ[E] K) := fun i =>
    ((-(lam i)⁻¹) • eB.coord (jj i)).smulRight (1 : K)
  let W : Finset (Fin m → E) := Finset.univ.filter (fun v => ∃ i, v (jj i) = lam i)
  refine ⟨Cm, W.image (fun v => (eB.equivFun.symm v)⁻¹), ?_, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨v, hv, hv0⟩ := Finset.mem_image.mp h
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hv).2
    rw [inv_eq_zero] at hv0
    have hv' : v = 0 := eB.equivFun.symm.injective (hv0.trans (map_zero _).symm)
    rw [hv'] at hi
    exact hlam i hi.symm
  · intro i
    have hle : LinearMap.range (Cm i) ≤ Submodule.span E {(1 : K)} := by
      rintro _ ⟨y, rfl⟩
      simp only [Cm, LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self 1)
    have hne : LinearMap.range (Cm i) ≠ ⊥ := by
      intro hb
      have hmem : Cm i (eB (jj i)) ∈ LinearMap.range (Cm i) := LinearMap.mem_range_self _ _
      rw [hb, Submodule.mem_bot] at hmem
      simp only [Cm, LinearMap.smulRight_apply, LinearMap.smul_apply, Basis.coord_apply,
        Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hmem
      rw [smul_eq_zero] at hmem
      rcases hmem with h1 | h1
      · exact hlam i (inv_eq_zero.mp (neg_eq_zero.mp h1))
      · exact one_ne_zero h1
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton one_ne_zero] at h1
    have h2 : finrank E (LinearMap.range (Cm i)) ≠ 0 := fun h =>
      hne (Submodule.finrank_eq_zero.mp h)
    omega
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hv).2
    have hrep : eB.repr (eB.equivFun.symm v) (jj i) = v (jj i) := by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hw0 : eB.equivFun.symm v ≠ 0 := by
      intro h
      have hv0 : v = 0 := eB.equivFun.symm.injective (h.trans (map_zero _).symm)
      rw [hv0] at hi
      exact hlam i hi.symm
    refine ⟨i, eB.equivFun.symm v, hw0, ?_⟩
    rw [inv_mul_cancel₀ hw0]
    simp only [Cm, LinearMap.smulRight_apply, LinearMap.smul_apply, Basis.coord_apply,
      smul_eq_mul, hrep, hi]
    rw [neg_mul, inv_mul_cancel₀ (hlam i), neg_smul, one_smul, add_neg_cancel]
  · rw [Finset.card_image_of_injective _
      (fun v1 v2 h => eB.equivFun.symm.injective (inv_injective h))]
    let A : Fin m → Finset E := fun j => Finset.univ.filter (fun x => ∀ i, jj i = j → x ≠ lam i)
    have hU : Finset.univ.filter (fun v : Fin m → E => ¬ ∃ i, v (jj i) = lam i) =
        Fintype.piFinset A := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, A,
        not_exists]
      constructor
      · intro h j i hij hv
        apply h i
        rw [hij]
        exact hv
      · intro h i hv
        exact h (jj i) i rfl hv
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin m → E))) (fun v => ∃ i, v (jj i) = lam i)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hU, Fintype.card_piFinset] at hsplit
    have hAcard : ∀ j : Fin m, (A j).card = Fintype.card E - min N (c - N * j.val) := by
      intro j
      have hAeq : A j = Finset.univ \ (Finset.univ.filter (fun r : Fin N =>
          N * j.val + r.val < c)).image (fun r => ((enum r : Eˣ) : E)) := by
        ext x
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
          Finset.mem_image, not_exists, not_and]
        constructor
        · intro h r hr hx
          have hjj : jj ⟨N * j.val + r.val, hr⟩ = j := by
            apply Fin.ext
            show (N * j.val + r.val) / N = j.val
            rw [Nat.mul_add_div hNpos, Nat.div_eq_of_lt r.isLt, add_zero]
          have hrr : rr ⟨N * j.val + r.val, hr⟩ = r := by
            apply Fin.ext
            show (N * j.val + r.val) % N = r.val
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
          apply h ⟨N * j.val + r.val, hr⟩ hjj
          rw [← hx]
          show ((enum r : Eˣ) : E) = ((enum (rr ⟨N * j.val + r.val, hr⟩) : Eˣ) : E)
          rw [hrr]
        · intro h i hij hx
          apply h (rr i) ?_ hx.symm
          have hj : j.val = i.val / N := (congrArg Fin.val hij).symm
          show N * j.val + i.val % N < c
          rw [hj, Nat.div_add_mod]
          exact i.isLt
      have hfilt : (Finset.univ.filter (fun r : Fin N => N * j.val + r.val < c)) =
          Finset.univ.filter (fun r : Fin N => (r : ℕ) < c - N * j.val) :=
        Finset.filter_congr (fun r _ => by omega)
      rw [hAeq, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Finset.card_image_of_injective _ (fun r1 r2 hr => enum.injective (Units.ext hr)),
        hfilt, Fin.card_filter_val_lt]
    have hprod : ∏ j, (A j).card = Lq (Fintype.card E) m budget := by
      rw [Finset.prod_congr rfl (fun j _ => hAcard j)]
      rw [Fin.prod_univ_eq_prod_range (fun j => Fintype.card E - min N (c - N * j)) m]
      have hcd : c = c % N + N * (c / N) := (Nat.mod_add_div c N).symm
      have hb : c % N < N := Nat.mod_lt _ hNpos
      rw [prod_box (Fintype.card E) N c (c / N) (c % N) hqN hcd hb m]
      split_ifs with hma
      · symm
        apply Lq_big _ _ _ hq2
        rw [hN]
        by_contra hlt
        push_neg at hlt
        have hcb : c = budget := by rw [← hc]; exact min_eq_left hlt.le
        have h6 : N * m ≤ N * (c / N) := Nat.mul_le_mul_left _ hma
        have h7 : m * N = N * m := Nat.mul_comm _ _
        omega
      · push_neg at hma
        have h6 : N * (c / N + 1) ≤ N * m := Nat.mul_le_mul_left _ hma
        have h7 : N * (c / N + 1) = N * (c / N) + N := by ring
        have h8 : m * N = N * m := Nat.mul_comm _ _
        have hcb : c = budget := by
          rw [← hc]
          apply min_eq_left
          by_contra hgt
          push_neg at hgt
          have : min budget (m * N) = m * N := min_eq_right hgt.le
          omega
        rw [Lq_dec (Fintype.card E) m budget (c / N) (c % N) hq2 (by rw [hN]; omega)
          (by rw [hN]; exact hb) hma]
        rw [show m - 1 - c / N = m - c / N - 1 by omega]
    rw [← hprod]
    exact hsplit

theorem core (h m t budget : ℕ) (hh : 0 < h) (hm : 0 < m)
    (hk1 : h*m - h ≤ 2*t) (hk2 : 2*t < h*m)
    (K : Type) [Field K] [Algebra (ZMod 2) K] [Algebra (GaloisField 2 h) K]
    [IsScalarTower (ZMod 2) (GaloisField 2 h) K] [FiniteDimensional (GaloisField 2 h) K]
    (hK : finrank (GaloisField 2 h) K = m)
    (basis : Basis (Fin (h*m)) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) :
    let point : Fin (h*m+1) → K := Fin.cases 0 basis
    let mult := fun (z : K) (x y : Fin (h*m+1)) => decide (bit (z * point x * point y) ≠ 0)
    let table := fun (C : K →ₗ[GaloisField 2 h] K) (x y : Fin (h*m+1)) =>
      decide (bit (C (point x) * point y) ≠ 0)
    let serves := fun (l : ℕ) (C : Fin l → (K →ₗ[GaloisField 2 h] K)) (S : Finset K) =>
      ∀ z ∈ S, ∃ i : Fin l, Cheap (fun x y => xor (mult z x y) (table (C i) x y)) t
    let rk := fun (D : K →ₗ[GaloisField 2 h] K) => finrank (GaloisField 2 h) (LinearMap.range D)
    let c := min budget (m*(2^h-1))
    let a := c/(2^h-1)
    let b := c % (2^h-1)
    let left := (2^h)^(m-a) - b*(2^h)^(m-a-1)
    (∀ (l : ℕ) (C : Fin l → (K →ₗ[GaloisField 2 h] K)) (S : Finset K),
        (0 : K) ∉ S → (∑ i : Fin l, rk (C i)) ≤ budget → serves l C S →
        S.card + left ≤ (2^h)^m) ∧
      (∃ (C : Fin c → (K →ₗ[GaloisField 2 h] K)) (S : Finset K),
        (0 : K) ∉ S ∧
        (∀ i : Fin c, rk (C i) = 1 ∧ Cheap (table (C i)) ((h+1)/2)) ∧
        serves c C S ∧ S.card + left = (2^h)^m) := by
  intro point mult table serves rk c a b left
  classical
  haveI : Module.Finite (ZMod 2) K := Module.Finite.of_basis basis
  haveI : Finite K := Module.finite_of_finite (ZMod 2)
  letI : Fintype (GaloisField 2 h) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 h) = 2^h := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 h hh.ne']
  refine ⟨?_, ?_⟩
  · intro l C S h0 hbud hserv
    have hS : ∀ z ∈ S, ∃ i, ∃ x, x ≠ 0 ∧ z * x + C i x = 0 := by
      intro z hz
      obtain ⟨i, hi⟩ := hserv z hz
      exact ⟨i, (served_iff h m t hh hk1 hk2 hK basis bit hbit z (C i)).mp hi⟩
    exact upper (2^h) hq m budget hK l C S h0 hbud hS
  · obtain ⟨C, S, h0, hrk, hserv, hcard⟩ := attain (K := K) (2^h) hq m budget hK
    refine ⟨C, S, h0, fun i => ⟨hrk i, ?_⟩, fun z hz => ?_, hcard⟩
    · refine (table_cheap h m hh basis bit hbit (C i) ((h+1)/2)).mpr ?_
      rw [hrk i]
      omega
    · obtain ⟨i, hi⟩ := hserv z hz
      exact ⟨i, (served_iff h m t hh hk1 hk2 hK basis bit hbit z (C i)).mpr hi⟩

end PEqualNP.Outside.L_meta_29735_aux

theorem PEqualNP.Outside.L_meta_29735 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩
∀ (h m t budget : ℕ), 0 < h → 0 < m →
  let F := ZMod 2
  let E := GaloisField 2 h
  let q := 2^h
  let k := h*m
  let n := k+1
  k-h ≤ 2*t → 2*t < k →
  ∀ (K : Type) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
    [FiniteDimensional E K], Module.finrank E K = m →
    ∀ (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
      let point : Fin n → K := Fin.cases 0 basis
      let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
      let table := fun (C : K →ₗ[E] K) (x y : Fin n) => decide (bit (C (point x) * point y) ≠ 0)
      let serves := fun (l : ℕ) (C : Fin l → (K →ₗ[E] K)) (S : Finset K) =>
        ∀ z ∈ S, ∃ i : Fin l,
          fits n n 1 (fun _ x y => xor (mult z x y) (table (C i) x y)) t
      let rk := fun (D : K →ₗ[E] K) => Module.finrank E (LinearMap.range D)
      let c := min budget (m*(q-1))
      let a := c/(q-1)
      let b := c % (q-1)
      let left := q^(m-a) - b*q^(m-a-1)
      (∀ (l : ℕ) (C : Fin l → (K →ₗ[E] K)) (S : Finset K),
        (0 : K) ∉ S → (∑ i : Fin l, rk (C i)) ≤ budget → serves l C S →
        S.card + left ≤ q^m) ∧
      (∃ (C : Fin c → (K →ₗ[E] K)) (S : Finset K),
        (0 : K) ∉ S ∧
        (∀ i : Fin c, rk (C i) = 1 ∧ fits n n 1 (fun _ => table (C i)) ((h+1)/2)) ∧
        serves c C S ∧ S.card + left = q^m)
) := by
  intro nonlinear depths fits h m t budget hh hm F E q k n hk1 hk2 K iF iAF iAE iST iFD hK basis bit hbit
  exact @PEqualNP.Outside.L_meta_29735_aux.core h m t budget hh hm hk1 hk2 K iF iAF iAE iST iFD hK
    basis bit hbit

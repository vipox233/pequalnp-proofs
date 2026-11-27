import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25695_aux

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

def chi (t : ZMod 2) : ℤ := if t = 0 then 1 else -1

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> decide

lemma chi_zero : chi 0 = 1 := rfl

lemma chi_one : chi 1 = -1 := by decide

lemma sum_chi_linear {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (φ : V →ₗ[ZMod 2] ZMod 2) :
    (∑ x : V, chi (φ x)) = if φ = 0 then (Fintype.card V : ℤ) else 0 := by
  classical
  split_ifs with hφ
  · subst hφ
    simp [chi_zero]
  · have hne : ∃ x0 : V, φ x0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (LinearMap.ext h)
    rcases hne with ⟨x0, hx0⟩
    have hx0_one : φ x0 = 1 := zmod2_eq_one_of_ne_zero hx0
    have hx00 : x0 + x0 = 0 := by
      have h1 : (2 : ZMod 2) • x0 = 0 := by
        have h2 : (2 : ZMod 2) = 0 := by decide
        rw [h2, zero_smul]
      have h3 : (1 + 1 : ZMod 2) • x0 = x0 + x0 := by rw [add_smul, one_smul]
      rw [← h3]
      exact h1
    have hbij : Function.Bijective (fun x : V => x + x0) :=
      ⟨fun x y h => by
        have := congrArg (fun z => z + x0) h
        simpa [add_assoc, hx00] using this,
       fun y => ⟨y + x0, by simp [add_assoc, hx00]⟩⟩
    have hshift : (∑ x : V, chi (φ x)) = ∑ x : V, chi (φ (x + x0)) :=
      (Fintype.sum_bijective (fun x => x + x0) hbij _ _ fun _ => rfl).symm
    have hneg : (∑ x : V, chi (φ (x + x0))) = -(∑ x : V, chi (φ x)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_add, hx0_one, chi_add, chi_one]
      ring
    linarith

lemma card_submodule_zmod2 {I : Type*} [Fintype I] [DecidableEq I]
    (K : Submodule (ZMod 2) (I → ZMod 2)) [Fintype K] :
    Fintype.card K = 2 ^ Module.finrank (ZMod 2) K := by
  let b := Module.finBasis (ZMod 2) K
  have hcard : Fintype.card K = Fintype.card (Fin (Module.finrank (ZMod 2) K) → ZMod 2) :=
    Fintype.card_congr b.equivFun.toEquiv
  rw [hcard]
  simp

lemma walsh_nonzero_card_eq_two_pow_rank {I : Type*} [Fintype I] [DecidableEq I]
    (Q : (I → ZMod 2) → ZMod 2)
    (P : Matrix I I (ZMod 2))
    (hpolar : ∀ u v w : I → ZMod 2,
      Q (u + v + w) + Q (u + v) + Q (u + w) + Q u = dotProduct v (P.mulVec w)) :
    ((Finset.univ : Finset (I → ZMod 2)).filter (fun a =>
      (∑ x : I → ZMod 2, chi (dotProduct a x + Q x)) ≠ 0)).card = 2 ^ P.rank := by
  classical
  let k := Fintype.card I
  let K : Submodule (ZMod 2) (I → ZMod 2) := LinearMap.ker P.mulVecLin
  let W : (I → ZMod 2) → ℤ := fun a => ∑ x : I → ZMod 2, chi (dotProduct a x + Q x)
  have hQ_shift : ∀ x h : I → ZMod 2,
      Q (x + h) + Q x = dotProduct x (P.mulVec h) + Q h + Q 0 := by
    intro x h
    have h1 := hpolar 0 x h
    simp only [zero_add] at h1
    have h2 := congrArg (fun t => t + Q h + Q 0) h1
    have hlhs : Q (x + h) + Q x + Q h + Q 0 + Q h + Q 0 = Q (x + h) + Q x := by
      calc
        Q (x + h) + Q x + Q h + Q 0 + Q h + Q 0
            = Q (x + h) + Q x + (Q h + Q h) + (Q 0 + Q 0) := by ring
        _ = Q (x + h) + Q x := by rw [zmod2_add_self, zmod2_add_self]; ring
    rw [hlhs] at h2
    exact h2
  have hW_sq : ∀ a : I → ZMod 2,
      W a ^ 2 = (2 : ℤ) ^ k * ∑ h : K, chi (dotProduct a h.1 + Q h.1 + Q 0) := by
    intro a
    have hsq : W a ^ 2 =
        ∑ h : I → ZMod 2,
          chi (dotProduct a h + Q h + Q 0) * ∑ x : I → ZMod 2, chi (dotProduct x (P.mulVec h)) := by
      have h1 : W a ^ 2 =
          ∑ x : I → ZMod 2, ∑ y : I → ZMod 2, chi (dotProduct a (x + y) + Q x + Q y) := by
        simp only [W, sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← chi_add, dotProduct_add]
        congr 1; ring
      rw [h1]
      have hshift : ∀ x : I → ZMod 2,
          (∑ y : I → ZMod 2, chi (dotProduct a (x + y) + Q x + Q y)) =
            ∑ h : I → ZMod 2, chi (dotProduct a h + Q (x + h) + Q x) := by
        intro x
        have hxx : x + x = 0 := funext fun i => zmod2_add_self (x i)
        have hbij : Function.Bijective (fun h : I → ZMod 2 => x + h) :=
          ⟨fun h1 h2 heq => by
            have := congrArg (fun z => x + z) heq
            simpa [← add_assoc, hxx] using this,
           fun y => ⟨x + y, by simp [← add_assoc, hxx]⟩⟩
        refine (Fintype.sum_bijective (fun h => x + h) hbij _ _ ?_).symm
        intro h
        have hxa : x + (x + h) = h := by rw [← add_assoc, hxx, zero_add]
        rw [hxa]
        congr 1; ring
      simp_rw [hshift]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← chi_add]
      congr 1
      have hqs := hQ_shift x h
      calc
        dotProduct a h + Q (x + h) + Q x
            = dotProduct a h + (Q (x + h) + Q x) := by ring
        _ = dotProduct a h + (dotProduct x (P.mulVec h) + Q h + Q 0) := by rw [hqs]
        _ = dotProduct a h + Q h + Q 0 + dotProduct x (P.mulVec h) := by ring
    rw [hsq]
    have hinner : ∀ h : I → ZMod 2,
        (∑ x : I → ZMod 2, chi (dotProduct x (P.mulVec h))) =
          if h ∈ K then (2 : ℤ) ^ k else 0 := by
      intro h
      let φ : (I → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun x => dotProduct x (P.mulVec h)
          map_add' := fun x1 x2 => by simp [add_dotProduct]
          map_smul' := fun c x => by simp [smul_dotProduct] }
      have hφ0 : φ = 0 ↔ h ∈ K := by
        constructor
        · intro h0
          show P.mulVec h = 0
          ext i
          have hi := congrArg (fun f => f (Pi.single (M := fun _ => ZMod 2) i 1)) h0
          simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, dotProduct] at hi
          have hterm : ∀ j : I,
              Pi.single (M := fun _ => ZMod 2) i 1 j * P.mulVec h j =
                if j = i then P.mulVec h i else 0 := by
            intro j
            by_cases hji : j = i
            · subst hji; simp
            · simp [hji]
          simp_rw [hterm] at hi
          simpa using hi
        · intro hK
          have hP0 : P.mulVec h = 0 := hK
          ext x
          simp [φ, hP0]
      have hsum : (∑ x : I → ZMod 2, chi (dotProduct x (P.mulVec h))) =
          if φ = 0 then (Fintype.card (I → ZMod 2) : ℤ) else 0 := sum_chi_linear φ
      have hcardV : (Fintype.card (I → ZMod 2) : ℤ) = (2 : ℤ) ^ k := by
        simp [k]
      rw [hsum, hcardV]
      by_cases hmem : h ∈ K
      · have h0 : φ = 0 := hφ0.mpr hmem
        simp only [h0, hmem, ↓reduceIte]
      · have h0 : φ ≠ 0 := mt hφ0.mp hmem
        simp only [h0, hmem, ↓reduceIte]
    simp_rw [hinner]
    have hfilt :
        (∑ h : I → ZMod 2, chi (dotProduct a h + Q h + Q 0) * if h ∈ K then (2 : ℤ) ^ k else 0) =
          (2 : ℤ) ^ k * ∑ h ∈ Finset.univ.filter (fun h : I → ZMod 2 => h ∈ K),
            chi (dotProduct a h + Q h + Q 0) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun h _ => ?_
      split_ifs <;> ring
    rw [hfilt]
    congr 1
    exact Finset.sum_subtype (Finset.univ.filter (fun h : I → ZMod 2 => h ∈ K))
      (p := fun h => h ∈ K) (fun h => by simp)
      (fun h => chi (dotProduct a h + Q h + Q 0))
  have hW_val : ∀ a : I → ZMod 2,
      W a ^ 2 = if W a ≠ 0 then (2 : ℤ) ^ (k + Module.finrank (ZMod 2) K) else 0 := by
    intro a
    let ψ : K →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun h => dotProduct a h.1 + Q h.1 + Q 0
        map_add' := fun h1 h2 => by
          have hP2 : P.mulVec h2.1 = 0 := h2.2
          have hqs := hQ_shift h1.1 h2.1
          rw [hP2, dotProduct_zero, zero_add] at hqs
          have hsumQ : Q (h1.1 + h2.1) + Q 0 = (Q h1.1 + Q 0) + (Q h2.1 + Q 0) := by
            have := congrArg (fun t => t + Q h1.1 + Q 0) hqs
            calc
              Q (h1.1 + h2.1) + Q 0
                  = Q (h1.1 + h2.1) + Q h1.1 + Q h1.1 + Q 0 := by
                have hz := zmod2_add_self (Q h1.1)
                calc
                  Q (h1.1 + h2.1) + Q 0 = Q (h1.1 + h2.1) + (Q h1.1 + Q h1.1) + Q 0 := by
                    rw [hz, add_zero]
                  _ = Q (h1.1 + h2.1) + Q h1.1 + Q h1.1 + Q 0 := by ring
              _ = Q h2.1 + Q 0 + Q h1.1 + Q 0 := this
              _ = (Q h1.1 + Q 0) + (Q h2.1 + Q 0) := by ring
          simp only [Submodule.coe_add, dotProduct_add]
          calc
            dotProduct a h1.1 + dotProduct a h2.1 + Q (h1.1 + h2.1) + Q 0
                = dotProduct a h1.1 + dotProduct a h2.1 + (Q (h1.1 + h2.1) + Q 0) := by ring
            _ = dotProduct a h1.1 + dotProduct a h2.1 + ((Q h1.1 + Q 0) + (Q h2.1 + Q 0)) := by
              rw [hsumQ]
            _ = dotProduct a h1.1 + Q h1.1 + Q 0 + (dotProduct a h2.1 + Q h2.1 + Q 0) := by ring
        map_smul' := fun c h => by
          by_cases hc : c = 0
          · subst hc; simp [zmod2_add_self]
          · have hc1 : c = 1 := zmod2_eq_one_of_ne_zero hc
            subst hc1; simp }
    have hsumK : (∑ h : K, chi (dotProduct a h.1 + Q h.1 + Q 0)) =
        if ψ = 0 then (Fintype.card K : ℤ) else 0 := sum_chi_linear ψ
    have hcardK : (Fintype.card K : ℤ) = (2 : ℤ) ^ Module.finrank (ZMod 2) K := by
      exact_mod_cast card_submodule_zmod2 K
    rw [hW_sq a, hsumK, hcardK]
    by_cases hψ : ψ = 0
    · simp only [hψ, ↓reduceIte, ← pow_add]
      have hne : W a ≠ 0 := by
        intro h0
        have hsq0 : W a ^ 2 = 0 := by rw [h0]; simp
        rw [hW_sq a, hsumK, hcardK] at hsq0
        simp only [hψ, ↓reduceIte, ← pow_add] at hsq0
        have hpos : (0 : ℤ) < (2 : ℤ) ^ (k + Module.finrank (ZMod 2) K) := by positivity
        linarith
      simp [hne]
    · simp only [hψ, ↓reduceIte, mul_zero]
      have h0 : W a = 0 := by
        have hsq0 : W a ^ 2 = 0 := by
          rw [hW_sq a, hsumK]
          simp only [hψ, ↓reduceIte, mul_zero]
        exact sq_eq_zero_iff.mp hsq0
      simp [h0]
  have hparseval : (∑ a : I → ZMod 2, W a ^ 2) = (2 : ℤ) ^ (2 * k) := by
    have h1 : (∑ a : I → ZMod 2, W a ^ 2) =
        ∑ x : I → ZMod 2, ∑ y : I → ZMod 2,
          chi (Q x + Q y) * ∑ a : I → ZMod 2, chi (dotProduct a (x + y)) := by
      have hsq : ∀ a, W a ^ 2 =
          ∑ x : I → ZMod 2, ∑ y : I → ZMod 2, chi (Q x + Q y) * chi (dotProduct a (x + y)) := by
        intro a
        simp only [W, sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← chi_add, ← chi_add, dotProduct_add]
        congr 1; ring
      simp_rw [hsq]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
    rw [h1]
    have hinner : ∀ x y : I → ZMod 2,
        (∑ a : I → ZMod 2, chi (dotProduct a (x + y))) = if x = y then (2 : ℤ) ^ k else 0 := by
      intro x y
      let φ : (I → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun a => dotProduct a (x + y)
          map_add' := fun a1 a2 => by simp only [add_dotProduct, dotProduct_add]; ring
          map_smul' := fun c a => by simp only [smul_dotProduct, dotProduct_add, smul_eq_mul, RingHom.id_apply]; ring }
      have hφ0 : φ = 0 ↔ x = y := by
        constructor
        · intro h0
          have hxy : x + y = 0 := by
            ext i
            have hi := congrArg (fun f => f (Pi.single (M := fun _ => ZMod 2) i 1)) h0
            simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, dotProduct] at hi
            have hterm : ∀ j : I,
                Pi.single (M := fun _ => ZMod 2) i 1 j * (x + y) j =
                  if j = i then (x + y) i else 0 := by
              intro j
              by_cases hji : j = i
              · subst hji; simp
              · simp [hji]
            simp_rw [hterm] at hi
            simpa using hi
          ext i
          have h1 := congrFun hxy i
          simp only [Pi.add_apply, Pi.zero_apply] at h1
          have h2 := congrArg (fun t => t + y i) h1
          simp only [zero_add, add_assoc, zmod2_add_self, add_zero] at h2
          exact h2
        · rintro rfl
          ext a
          have hxx : x + x = 0 := funext fun i => zmod2_add_self (x i)
          simp [φ, hxx]
      have hsum : (∑ a : I → ZMod 2, chi (dotProduct a (x + y))) =
          if φ = 0 then (Fintype.card (I → ZMod 2) : ℤ) else 0 := sum_chi_linear φ
      have hcardV : (Fintype.card (I → ZMod 2) : ℤ) = (2 : ℤ) ^ k := by simp [k]
      rw [hsum, hcardV]
      by_cases hxy : x = y
      · have h0 : φ = 0 := hφ0.mpr hxy
        simp only [h0, hxy, ↓reduceIte]
      · have h0 : φ ≠ 0 := mt hφ0.mp hxy
        simp only [h0, hxy, ↓reduceIte]
    simp_rw [hinner]
    have hdiag : ∀ x : I → ZMod 2,
        (∑ y : I → ZMod 2, chi (Q x + Q y) * if x = y then (2 : ℤ) ^ k else 0) = (2 : ℤ) ^ k := by
      intro x
      rw [Finset.sum_eq_single x]
      · simp [zmod2_add_self, chi_zero]
      · intro y _ hyx
        simp [Ne.symm hyx]
      · intro h; exact absurd (Finset.mem_univ x) h
    simp_rw [hdiag]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcardV : (Fintype.card (I → ZMod 2) : ℤ) = (2 : ℤ) ^ k := by simp [k]
    rw [hcardV, ← pow_add, show k + k = 2 * k by omega]
  have hsum_count : (∑ a : I → ZMod 2, W a ^ 2) =
      ((Finset.univ.filter (fun a : I → ZMod 2 => W a ≠ 0)).card : ℤ) *
        (2 : ℤ) ^ (k + Module.finrank (ZMod 2) K) := by
    simp_rw [hW_val]
    rw [← Finset.sum_filter]
    simp
  have hrP := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  have hdimV : Module.finrank (ZMod 2) (I → ZMod 2) = k := by simp [k]
  rw [hdimV] at hrP
  have h2k : 2 * k = P.rank + (k + Module.finrank (ZMod 2) K) := by
    change 2 * k = Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) +
      (k + Module.finrank (ZMod 2) (LinearMap.ker P.mulVecLin))
    omega
  rw [hsum_count, h2k] at hparseval
  conv at hparseval => rhs; rw [pow_add]
  have hpos : (0 : ℤ) < (2 : ℤ) ^ (k + Module.finrank (ZMod 2) K) := by positivity
  have hcard_int :
      ((Finset.univ.filter (fun a : I → ZMod 2 => W a ≠ 0)).card : ℤ) = (2 : ℤ) ^ P.rank :=
    mul_right_cancel₀ (ne_of_gt hpos) hparseval
  exact_mod_cast hcard_int

def M0 : Matrix (Fin 2) (Fin 2) ℤ := fun _ j => if j = 0 then 1 else 0
def M1 : Matrix (Fin 2) (Fin 2) ℤ := fun i j => if i = 0 then (if j = 1 then 4 else 0) else (if j = 0 then 1 else 0)
def Amat : Matrix (Fin 2) (Fin 2) ℤ := fun src dst =>
  if src = 0 then (if dst = 0 then 1 else 4) else (if dst = 0 then 2 else 0)

def Mbit (b : ZMod 2) : Matrix (Fin 2) (Fin 2) ℤ := if b = 0 then M0 else M1

lemma M0_add_M1 : M0 + M1 = Amat := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

lemma Amat_pow_eq_sum (k : ℕ) :
    Amat ^ k = ∑ w : Fin k → ZMod 2, (List.ofFn (fun i : Fin k => Mbit (w i))).prod := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    have hsplit : (∑ w : Fin (k + 1) → ZMod 2,
        (List.ofFn (fun i : Fin (k + 1) => Mbit (w i))).prod) =
        ∑ w : Fin k → ZMod 2, ∑ last : ZMod 2,
          (List.ofFn (fun i : Fin k => Mbit (w i))).prod * Mbit last := by
      let e : (Fin k → ZMod 2) × ZMod 2 ≃ (Fin (k + 1) → ZMod 2) :=
        { toFun := fun p i => if h : i.val < k then p.1 ⟨i.val, h⟩ else p.2
          invFun := fun w => (fun i => w ⟨i.val, by omega⟩, w ⟨k, by omega⟩)
          left_inv := fun ⟨w, last⟩ => by
            ext i
            · simp [i.2]
            · simp
          right_inv := fun w => by
            ext i
            by_cases h : i.val < k
            · simp [h]
            · have hik : i = ⟨k, by omega⟩ := Fin.ext (by dsimp only; have := i.2; omega)
              rw [hik]; simp }
      rw [← Fintype.sum_prod_type']
      refine (Fintype.sum_bijective e e.bijective _ _ ?_).symm
      rintro ⟨w, last⟩
      have hrec : List.ofFn (fun i : Fin (k + 1) => Mbit (e (w, last) i)) =
          List.ofFn (fun i : Fin k => Mbit (w i)) ++ [Mbit last] := by
        rw [List.ofFn_succ', List.concat_eq_append]
        have h1 : (fun i : Fin k => Mbit (e (w, last) i.castSucc)) = fun i => Mbit (w i) := by
          ext i; simp [e, i.2]
        have h2 : Mbit (e (w, last) (Fin.last k)) = Mbit last := by simp [e]
        rw [h1, h2]
      rw [hrec, List.prod_append, List.prod_singleton]
    rw [hsplit]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    have hsum2 : (∑ last : ZMod 2, Mbit last) = M0 + M1 := by
      ext i j; fin_cases i <;> fin_cases j <;> decide
    rw [hsum2, M0_add_M1]

lemma trace_M1_pow (k : ℕ) :
    Matrix.trace (M1 ^ k) = if k % 2 = 1 then 0 else 2 * (2 : ℤ) ^ k := by
  have hsq : M1 ^ 2 = (4 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have heven : ∀ r : ℕ, M1 ^ (2 * r) = ((4 : ℤ) ^ r) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [show 2 * (r + 1) = 2 * r + 2 by omega, pow_add, ih, hsq, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, one_mul, pow_succ]
  by_cases hodd : k % 2 = 1
  · simp only [hodd, ↓reduceIte]
    have hk : k = 2 * (k / 2) + 1 := by omega
    rw [hk, pow_succ, heven (k / 2), Matrix.smul_mul, one_mul, Matrix.trace_smul]
    have htr1 : Matrix.trace M1 = 0 := by decide
    rw [htr1, smul_zero]
  · simp only [hodd, ↓reduceIte]
    have hk : k = 2 * (k / 2) := by omega
    conv_lhs => rw [hk, heven (k / 2)]
    rw [Matrix.trace_smul]
    have htrI : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℤ) = 2 := by decide
    rw [htrI, smul_eq_mul]
    have h4 : (4 : ℤ) ^ (k / 2) = (2 : ℤ) ^ k := by
      have : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
      rw [this, ← pow_mul, ← hk]
    rw [h4]; ring

def pathMat {m : ℕ} (w : Fin m → ZMod 2) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2) :=
  Matrix.of fun i j =>
    (if h : i.val < m ∧ j.val = i.val + 1 then w ⟨i.val, h.1⟩ else 0) +
    (if h : j.val < m ∧ i.val = j.val + 1 then w ⟨j.val, h.1⟩ else 0)

lemma pathMat_symm {m : ℕ} (w : Fin m → ZMod 2) (i j : Fin (m + 1)) :
    pathMat w i j = pathMat w j i := by
  simp only [pathMat, Matrix.of_apply]
  ring

lemma pathMat_diag {m : ℕ} (w : Fin m → ZMod 2) (i : Fin (m + 1)) :
    pathMat w i i = 0 := by
  simp only [pathMat, Matrix.of_apply]
  have h1 : ¬ (i.val < m ∧ i.val = i.val + 1) := by omega
  simp only [h1, ↓reduceDIte, add_zero]

lemma pathMat_alt {m : ℕ} (w : Fin m → ZMod 2) (x : Fin (m + 1) → ZMod 2) :
    dotProduct x ((pathMat w).mulVec x) = 0 := by
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  have h1 : ∀ i j : Fin (m + 1),
      x i * (pathMat w i j * x j) =
        (if i.val < j.val then x i * pathMat w i j * x j else 0) +
        (if j.val < i.val then x i * pathMat w i j * x j else 0) := by
    intro i j
    by_cases hlt : i.val < j.val
    · have hgt : ¬ j.val < i.val := by omega
      simp only [hlt, hgt, ↓reduceIte, add_zero]; ring
    · by_cases hgt : j.val < i.val
      · simp only [hlt, hgt, ↓reduceIte, zero_add]; ring
      · have heq : i = j := Fin.ext (by omega)
        subst heq
        simp only [lt_self_iff_false, ↓reduceIte, add_zero, pathMat_diag, zero_mul, mul_zero]
  simp_rw [h1, Finset.sum_add_distrib]
  have hswap : (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
      if j.val < i.val then x i * pathMat w i j * x j else 0) =
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        if i.val < j.val then x i * pathMat w i j * x j else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [pathMat_symm]; ring
    · rfl
  rw [hswap, zmod2_add_self]

lemma pathMat_dot_symm {m : ℕ} (w : Fin m → ZMod 2) (x y : Fin (m + 1) → ZMod 2) :
    dotProduct x ((pathMat w).mulVec y) = dotProduct y ((pathMat w).mulVec x) := by
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [pathMat_symm]; ring

lemma pathMat_succ_mulVec {m : ℕ} (w : Fin (m + 1) → ZMod 2) (y : Fin (m + 2) → ZMod 2) :
    let w' : Fin m → ZMod 2 := fun i => w ⟨i.val, by omega⟩
    let y' : Fin (m + 1) → ZMod 2 := fun i => y ⟨i.val, by omega⟩
    (∀ i : Fin m, (pathMat w).mulVec y ⟨i.val, by omega⟩ = (pathMat w').mulVec y' ⟨i.val, by omega⟩) ∧
    (pathMat w).mulVec y ⟨m, by omega⟩ = (pathMat w').mulVec y' ⟨m, by omega⟩ + w ⟨m, by omega⟩ * y ⟨m + 1, by omega⟩ ∧
    (pathMat w).mulVec y ⟨m + 1, by omega⟩ = w ⟨m, by omega⟩ * y ⟨m, by omega⟩ := by
  intro w' y'
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_castSucc]
    have hlast : pathMat w ⟨i.val, by omega⟩ (Fin.last (m + 1)) * y (Fin.last (m + 1)) = 0 := by
      simp only [pathMat, Matrix.of_apply, Fin.val_last]
      have h1 : ¬ (i.val < m + 1 ∧ m + 1 = i.val + 1) := by omega
      have h2 : ¬ (m + 1 < m + 1 ∧ i.val = m + 1 + 1) := by omega
      simp only [h1, h2, ↓reduceDIte, add_zero, zero_mul]
    rw [hlast, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp only [pathMat, Matrix.of_apply, Fin.val_castSucc, w']
    have h1 : (i.val < m + 1 ∧ j.val = i.val + 1) ↔ (i.val < m ∧ j.val = i.val + 1) := by
      have := i.2; omega
    have h2 : (j.val < m + 1 ∧ i.val = j.val + 1) ↔ (j.val < m ∧ i.val = j.val + 1) := by
      have := i.2; omega
    congr 1
    · by_cases ha : i.val < m ∧ j.val = i.val + 1
      · have hb := h1.mpr ha; simp only [ha, hb]
      · have hb : ¬ (i.val < m + 1 ∧ j.val = i.val + 1) := mt h1.mp ha; simp only [ha, hb, ↓reduceDIte]
    · by_cases ha : j.val < m ∧ i.val = j.val + 1
      · have hb := h2.mpr ha; simp only [ha, hb]
      · have hb : ¬ (j.val < m + 1 ∧ i.val = j.val + 1) := mt h2.mp ha; simp only [ha, hb, ↓reduceDIte]
  · simp only [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      simp only [pathMat, Matrix.of_apply, Fin.val_castSucc, w']
      have h1 : ¬ (m < m + 1 ∧ j.val = m + 1) := by have := j.2; omega
      have h2 : ¬ (m < m ∧ j.val = m + 1) := by omega
      have h3 : (j.val < m + 1 ∧ m = j.val + 1) ↔ (j.val < m ∧ m = j.val + 1) := by omega
      simp only [h1, h2, ↓reduceDIte, zero_add]
      split_ifs with hb ha ha
      · rfl
      · exfalso; exact ha (h3.mp hb)
      · exfalso; exact hb (h3.mpr ha)
      · rfl
    · simp only [pathMat, Matrix.of_apply, Fin.val_last]
      have h1 : m < m + 1 ∧ m + 1 = m + 1 := ⟨by omega, rfl⟩
      have h2 : ¬ (m + 1 < m + 1 ∧ m = m + 1 + 1) := by omega
      simp only [h1, h2, ↓reduceDIte, add_zero]
      rfl
  · simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (⟨m, by omega⟩ : Fin (m + 2))]
    · simp only [pathMat, Matrix.of_apply]
      have h1 : ¬ (m + 1 < m + 1 ∧ m = m + 1 + 1) := by omega
      have h2 : m < m + 1 ∧ m + 1 = m + 1 := ⟨by omega, rfl⟩
      simp only [h1, ↓reduceDIte, zero_add]
      split_ifs with h
      · rfl
      · exfalso; exact h ⟨h2.1, trivial⟩
    · intro j _ hne
      have hval : j.val ≠ m := fun h => hne (Fin.ext h)
      simp only [pathMat, Matrix.of_apply]
      have h1 : ¬ (m + 1 < m + 1 ∧ j.val = m + 1 + 1) := by omega
      have h2 : ¬ (j.val < m + 1 ∧ m + 1 = j.val + 1) := by omega
      simp only [h1, h2, ↓reduceDIte, add_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma pathMat_transfer_invariant (m : ℕ) (w : Fin m → ZMod 2) :
    let P := (List.ofFn (fun i : Fin m => Mbit (w i))).prod
    (∃ x : Fin (m + 1) → ZMod 2, (pathMat w).mulVec x = 0 ∧ x ⟨m, by omega⟩ = 1) ∧
      P 0 0 = (2 : ℤ) ^ (pathMat w).rank ∧ P 0 1 = 0 ∨
    (∀ x : Fin (m + 1) → ZMod 2, (pathMat w).mulVec x = 0 → x ⟨m, by omega⟩ = 0) ∧
      P 0 0 = 0 ∧ P 0 1 = (2 : ℤ) ^ (pathMat w).rank := by
  induction m with
  | zero =>
    left
    refine ⟨⟨fun _ => 1, ?_, rfl⟩, ?_, ?_⟩
    · ext i
      fin_cases i
      simp [pathMat, Matrix.mulVec, dotProduct]
    · have h0 : pathMat w = 0 := by ext i j; fin_cases i; fin_cases j; simp [pathMat]
      have hr0 : (pathMat w).rank = 0 := by
        rw [h0]
        have hbot : LinearMap.range (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)).mulVecLin = ⊥ := by
          ext y; simp
        change Module.finrank (ZMod 2) _ = 0
        rw [hbot]; simp
      rw [hr0]
      simp
    · simp
  | succ m ih =>
    let w' : Fin m → ZMod 2 := fun i => w ⟨i.val, by omega⟩
    let P' := (List.ofFn (fun i : Fin m => Mbit (w' i))).prod
    have hP_eq : (List.ofFn (fun i : Fin (m + 1) => Mbit (w i))).prod = P' * Mbit (w ⟨m, by omega⟩) := by
      have hrec : List.ofFn (fun i : Fin (m + 1) => Mbit (w i)) =
          List.ofFn (fun i : Fin m => Mbit (w' i)) ++ [Mbit (w ⟨m, by omega⟩)] := by
        rw [List.ofFn_succ', List.concat_eq_append]
        rfl
      rw [hrec, List.prod_append, List.prod_singleton]
    have hstep_ker : ∀ (y : Fin (m + 2) → ZMod 2),
        (pathMat w).mulVec y = 0 ↔
          (∀ i : Fin m, (pathMat w').mulVec (fun j => y ⟨j.val, by omega⟩) ⟨i.val, by omega⟩ = 0) ∧
          (pathMat w').mulVec (fun j => y ⟨j.val, by omega⟩) ⟨m, by omega⟩ +
            w ⟨m, by omega⟩ * y ⟨m + 1, by omega⟩ = 0 ∧
          w ⟨m, by omega⟩ * y ⟨m, by omega⟩ = 0 := by
      intro y
      have hsp := pathMat_succ_mulVec w y
      dsimp only at hsp
      constructor
      · intro h0
        refine ⟨fun i => ?_, ?_, ?_⟩
        · rw [← hsp.1 i]; exact congrFun h0 ⟨i.val, by omega⟩
        · rw [← hsp.2.1]; exact congrFun h0 ⟨m, by omega⟩
        · rw [← hsp.2.2]; exact congrFun h0 ⟨m + 1, by omega⟩
      · rintro ⟨ha, hb, hc⟩
        ext i
        by_cases h1 : i.val < m
        · have hi : i = ⟨i.val, by omega⟩ := rfl
          rw [hi, hsp.1 ⟨i.val, h1⟩]; exact ha ⟨i.val, h1⟩
        · by_cases h2 : i.val = m
          · have hi : i = ⟨m, by omega⟩ := Fin.ext h2
            rw [hi, hsp.2.1]; exact hb
          · have hi : i = ⟨m + 1, by omega⟩ := Fin.ext (by dsimp only; have := i.2; omega)
            rw [hi, hsp.2.2]; exact hc
    have hrank_add_ker : ∀ (k : ℕ) (M : Matrix (Fin k) (Fin k) (ZMod 2)),
        M.rank + Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) = k := by
      intro k M
      have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
      have hd : Module.finrank (ZMod 2) (Fin k → ZMod 2) = k := by simp
      rw [hd] at h
      exact h
    by_cases hwm : w ⟨m, by omega⟩ = 0
    · left
      let hker_equiv : LinearMap.ker (pathMat w).mulVecLin ≃ₗ[ZMod 2]
          LinearMap.ker (pathMat w').mulVecLin × ZMod 2 :=
        { toFun := fun y =>
            (⟨fun j => y.1 ⟨j.val, by omega⟩, by
              have h0 := (hstep_ker y.1).mp y.2
              ext j
              by_cases hj : j.val < m
              · exact h0.1 ⟨j.val, hj⟩
              · have hjm : j = ⟨m, by omega⟩ := Fin.ext (by dsimp only; have := j.2; omega)
                rw [hjm]
                simpa [hwm] using h0.2.1⟩,
             y.1 ⟨m + 1, by omega⟩)
          invFun := fun p =>
            ⟨fun i => if h : i.val < m + 1 then p.1.1 ⟨i.val, h⟩ else p.2, by
              change (pathMat w).mulVec _ = 0
              rw [hstep_ker]
              have hp0 : (pathMat w').mulVec p.1.1 = 0 := p.1.2
              have hrestr : (fun j : Fin (m + 1) =>
                  if h : j.val < m + 1 then p.1.1 ⟨j.val, h⟩ else p.2) = p.1.1 := by
                ext j; simp only [j.2, ↓reduceDIte]
              rw [hrestr, hp0, hwm]
              simp⟩
          left_inv := fun y => by
            apply Subtype.ext; ext i
            by_cases h : i.val < m + 1
            · simp [h]
            · have hi : i = ⟨m + 1, by omega⟩ := Fin.ext (by dsimp only; have := i.2; omega)
              rw [hi]; simp
          right_inv := fun ⟨⟨x, hx⟩, c⟩ => by
            ext i
            · simp [i.2]
            · simp
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hrank_eq : (pathMat w).rank = (pathMat w').rank := by
        have h1 := hrank_add_ker (m + 1 + 1) (pathMat w)
        have h2 := hrank_add_ker (m + 1) (pathMat w')
        have h3 : Module.finrank (ZMod 2) (LinearMap.ker (pathMat w).mulVecLin) =
            Module.finrank (ZMod 2) (LinearMap.ker (pathMat w').mulVecLin) + 1 := by
          rw [hker_equiv.finrank_eq, Module.finrank_prod, Module.finrank_self]
        omega
      have hex_last : ∃ x : Fin (m + 2) → ZMod 2,
          (pathMat w).mulVec x = 0 ∧ x ⟨m + 1, by omega⟩ = 1 := by
        refine ⟨(hker_equiv.symm (0, 1)).1, (hker_equiv.symm (0, 1)).2, ?_⟩
        simp [hker_equiv]
      rw [hP_eq, show Mbit (w ⟨m, by omega⟩) = M0 by simp [Mbit, hwm], hrank_eq]
      refine ⟨hex_last, ?_, ?_⟩
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, M0]
        rcases ih w' with ⟨_, h00, h01⟩ | ⟨_, h00, h01⟩
        · simp [P', h00, h01]
        · simp [P', h00, h01]
      · simp [Matrix.mul_apply, M0]
    · have hwm1 : w ⟨m, by omega⟩ = 1 := zmod2_eq_one_of_ne_zero hwm
      rcases ih w' with ⟨⟨x0, hx0_ker, hx0_last⟩, h00, h01⟩ | ⟨hall0, h00, h01⟩
      · right
        have hauto : ∀ u : Fin (m + 1) → ZMod 2,
            (∀ i : Fin m, (pathMat w').mulVec u ⟨i.val, by omega⟩ = 0) →
            (pathMat w').mulVec u ⟨m, by omega⟩ = 0 := by
          intro u hu
          have hdot0 : dotProduct x0 ((pathMat w').mulVec u) = 0 := by
            rw [pathMat_dot_symm, hx0_ker, dotProduct_zero]
          simp only [dotProduct] at hdot0
          rw [Fin.sum_univ_castSucc] at hdot0
          have hinit0 : (∑ i : Fin m, x0 i.castSucc * (pathMat w').mulVec u i.castSucc) = 0 :=
            Finset.sum_eq_zero fun i _ => by
              change x0 i.castSucc * (pathMat w').mulVec u ⟨i.val, by omega⟩ = 0
              rw [hu i, mul_zero]
          rw [hinit0, zero_add] at hdot0
          have hlast : x0 (Fin.last m) = 1 := hx0_last
          rw [hlast, one_mul] at hdot0
          exact hdot0
        have hker_sub : ∀ y : Fin (m + 2) → ZMod 2,
            (pathMat w).mulVec y = 0 ↔
              (pathMat w').mulVec (fun j => y ⟨j.val, by omega⟩) = 0 ∧
              y ⟨m, by omega⟩ = 0 ∧ y ⟨m + 1, by omega⟩ = 0 := by
          intro y
          rw [hstep_ker, hwm1]
          simp only [one_mul]
          constructor
          · rintro ⟨ha, hb, hc⟩
            have hauto_y := hauto (fun j => y ⟨j.val, by omega⟩) ha
            rw [hauto_y, zero_add] at hb
            refine ⟨?_, hc, hb⟩
            ext j
            by_cases hj : j.val < m
            · exact ha ⟨j.val, hj⟩
            · have hjm : j = ⟨m, by omega⟩ := Fin.ext (by dsimp only; have := j.2; omega)
              rw [hjm]; exact hauto_y
          · rintro ⟨hker, hm0, hm1⟩
            refine ⟨fun i => congrFun hker ⟨i.val, by omega⟩, ?_, hm0⟩
            rw [congrFun hker ⟨m, by omega⟩, hm1]; simp
        have hrank_eq : (pathMat w).rank = (pathMat w').rank + 2 := by
          let ev : LinearMap.ker (pathMat w').mulVecLin →ₗ[ZMod 2] ZMod 2 :=
            { toFun := fun x => x.1 ⟨m, by omega⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          have hev_surj : Function.Surjective ev := by
            intro c
            fin_cases c
            · exact ⟨0, rfl⟩
            · exact ⟨⟨x0, hx0_ker⟩, hx0_last⟩
          have hr_ev := LinearMap.finrank_range_add_finrank_ker ev
          rw [LinearMap.range_eq_top.mpr hev_surj, finrank_top, Module.finrank_self] at hr_ev
          let eK : LinearMap.ker (pathMat w).mulVecLin ≃ₗ[ZMod 2] LinearMap.ker ev :=
            { toFun := fun y =>
                ⟨⟨fun j => y.1 ⟨j.val, by omega⟩, ((hker_sub y.1).mp y.2).1⟩,
                 ((hker_sub y.1).mp y.2).2.1⟩
              invFun := fun x =>
                ⟨fun i => if h : i.val < m + 1 then x.1.1 ⟨i.val, h⟩ else 0, by
                  change (pathMat w).mulVec _ = 0
                  rw [hker_sub]
                  have hrestr : (fun j : Fin (m + 1) =>
                      if h : j.val < m + 1 then x.1.1 ⟨j.val, h⟩ else 0) = x.1.1 := by
                    ext j; simp only [j.2, ↓reduceDIte]
                  rw [hrestr]
                  exact ⟨x.1.2, by
                    have hlt : (⟨m, by omega⟩ : Fin (m + 2)).val < m + 1 := by dsimp only; omega
                    simp only [hlt, ↓reduceDIte]
                    exact x.2, by simp⟩⟩
              left_inv := fun y => by
                apply Subtype.ext; ext i
                by_cases h : i.val < m + 1
                · simp [h]
                · have hi : i = ⟨m + 1, by omega⟩ := Fin.ext (by dsimp only; have := i.2; omega)
                  rw [hi]
                  simp only [lt_self_iff_false, ↓reduceDIte]
                  exact ((hker_sub y.1).mp y.2).2.2.symm
              right_inv := fun x => by
                apply Subtype.ext; apply Subtype.ext; ext j; simp [j.2]
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          have hker_dim : Module.finrank (ZMod 2) (LinearMap.ker (pathMat w).mulVecLin) + 1 =
              Module.finrank (ZMod 2) (LinearMap.ker (pathMat w').mulVecLin) := by
            rw [eK.finrank_eq]; omega
          have h1 := hrank_add_ker (m + 1 + 1) (pathMat w)
          have h2 := hrank_add_ker (m + 1) (pathMat w')
          omega
        rw [hP_eq, show Mbit (w ⟨m, by omega⟩) = M1 by simp [Mbit, hwm1], hrank_eq]
        refine ⟨fun y hy => ((hker_sub y).mp hy).2.2, ?_, ?_⟩
        · simp [Matrix.mul_apply, Fin.sum_univ_two, M1, P', h01]
        · simp [Matrix.mul_apply, M1, P', h00]
          ring
      · left
        have hex_z : ∃ z : Fin (m + 1) → ZMod 2,
            (pathMat w').mulVec z = Pi.single (M := fun _ => ZMod 2) ⟨m, by omega⟩ 1 := by
          let R := LinearMap.range (pathMat w').mulVecLin
          let eM : Fin (m + 1) → ZMod 2 := Pi.single (M := fun _ => ZMod 2) ⟨m, by omega⟩ 1
          by_contra hnot
          have hnot_mem : eM ∉ R := hnot
          let K0 := LinearMap.ker (pathMat w').mulVecLin
          let orth : Submodule (ZMod 2) (Fin (m + 1) → ZMod 2) :=
            { carrier := {v | ∀ x ∈ K0, dotProduct x v = 0},
              zero_mem' := fun x _ => by simp, add_mem' := fun {a b} ha hb x hx => by simp [dotProduct_add, ha x hx, hb x hx],
              smul_mem' := fun c {a} ha x hx => by simp [dotProduct_smul, ha x hx] }
          have hR_le : R ≤ orth := by
            rintro _ ⟨u, rfl⟩ x hx
            change dotProduct x ((pathMat w').mulVec u) = 0
            rw [pathMat_dot_symm]
            have hx0 : (pathMat w').mulVec x = 0 := hx
            rw [hx0, dotProduct_zero]
          have heM_orth : eM ∈ orth := by
            intro x hx
            simp only [eM, dotProduct]
            have hterm : ∀ j : Fin (m + 1),
                x j * Pi.single (M := fun _ => ZMod 2) ⟨m, by omega⟩ 1 j =
                  if j = ⟨m, by omega⟩ then x ⟨m, by omega⟩ else 0 := by
              intro j
              by_cases hj : j = ⟨m, by omega⟩
              · subst hj; simp
              · simp [hj]
            simp_rw [hterm]
            simp [hall0 x hx]
          have horth_dim : Module.finrank (ZMod 2) orth + Module.finrank (ZMod 2) K0 ≤ m + 1 := by
            let b := Module.finBasis (ZMod 2) K0
            let evalK : (Fin (m + 1) → ZMod 2) →ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) K0) → ZMod 2) :=
              { toFun := fun v i => dotProduct (b i).1 v
                map_add' := fun u v => by ext i; simp [dotProduct_add]
                map_smul' := fun c v => by ext i; simp [dotProduct_smul] }
            have hker_eq : LinearMap.ker evalK = orth := by
              ext v
              constructor
              · intro hv x hx
                have hx_eq : (⟨x, hx⟩ : K0) = ∑ i, b.repr ⟨x, hx⟩ i • b i :=
                  (b.sum_repr ⟨x, hx⟩).symm
                have hval : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i).1 := by
                  have h1 := congrArg Subtype.val hx_eq
                  simp only [Submodule.coe_sum, SetLike.val_smul] at h1
                  exact h1
                rw [hval, sum_dotProduct]
                refine Finset.sum_eq_zero fun i _ => ?_
                rw [smul_dotProduct, smul_eq_mul]
                have hi0 : dotProduct (b i).1 v = 0 := congrFun hv i
                rw [hi0, mul_zero]
              · intro hv
                ext i
                exact hv (b i).1 (b i).2
            have hsurj_eval : Module.finrank (ZMod 2) (LinearMap.range evalK) =
                Module.finrank (ZMod 2) K0 := by
              let M : Matrix (Fin (m + 1)) (Fin (Module.finrank (ZMod 2) K0)) (ZMod 2) :=
                Matrix.of fun j i => (b i).1 j
              have hM_inj : Function.Injective M.mulVecLin := by
                rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
                intro c hc
                have hc' : (∑ i, c i • (b i).1) = 0 := by
                  ext j
                  have hj := congrFun hc j
                  simp only [M, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
                    Matrix.of_apply, Pi.zero_apply] at hj
                  simpa [Finset.sum_apply, mul_comm] using hj
                have hcK : (∑ i, c i • b i) = 0 := by
                  apply Subtype.ext; simpa using hc'
                exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent c hcK)
              have hM_rank : M.rank = Module.finrank (ZMod 2) K0 := by
                have hr := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
                rw [LinearMap.ker_eq_bot.mpr hM_inj] at hr
                simp at hr
                exact hr
              have hMt : M.transpose.mulVecLin = evalK := by
                apply LinearMap.ext; intro v; ext i
                simp [M, evalK, Matrix.mulVec, dotProduct]
              rw [← hMt]
              change M.transpose.rank = Module.finrank (ZMod 2) K0
              rw [Matrix.rank_transpose, hM_rank]
            have hr := LinearMap.finrank_range_add_finrank_ker evalK
            rw [hsurj_eval, hker_eq] at hr
            have hd : Module.finrank (ZMod 2) (Fin (m + 1) → ZMod 2) = m + 1 := by simp
            rw [hd] at hr
            omega
          have hR_dim := hrank_add_ker (m + 1) (pathMat w')
          have hR_eq_orth : R = orth := by
            apply Submodule.eq_of_le_of_finrank_eq hR_le
            have hle : Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) orth :=
              Submodule.finrank_mono hR_le
            dsimp only [R, K0] at hle horth_dim
            change Module.finrank (ZMod 2) (LinearMap.range (pathMat w').mulVecLin) + _ = _ at hR_dim
            change Module.finrank (ZMod 2) (LinearMap.range (pathMat w').mulVecLin) = _
            omega
          exact hnot_mem (hR_eq_orth ▸ heM_orth)
        rcases hex_z with ⟨z, hz⟩
        have hzm : z ⟨m, by omega⟩ = 0 := by
          have halt := pathMat_alt w' z
          rw [hz] at halt
          simp only [dotProduct] at halt
          have hterm : ∀ j : Fin (m + 1),
              z j * Pi.single (M := fun _ => ZMod 2) ⟨m, by omega⟩ 1 j =
                if j = ⟨m, by omega⟩ then z ⟨m, by omega⟩ else 0 := by
            intro j
            by_cases hj : j = ⟨m, by omega⟩
            · subst hj; simp
            · simp [hj]
          simp_rw [hterm] at halt
          simpa using halt
        let zhat : Fin (m + 2) → ZMod 2 := fun i =>
          if h : i.val < m + 1 then z ⟨i.val, h⟩ else 1
        have hzhat_ker : (pathMat w).mulVec zhat = 0 := by
          rw [hstep_ker, hwm1]
          have hrestr : (fun j : Fin (m + 1) => zhat ⟨j.val, by omega⟩) = z := by
            ext j; simp only [zhat, j.2, ↓reduceDIte]
          rw [hrestr, hz]
          refine ⟨fun i => ?_, ?_, ?_⟩
          · have hne : (⟨i.val, by omega⟩ : Fin (m + 1)) ≠ ⟨m, by omega⟩ :=
              fun h => by have hi := i.2; have hv := congrArg Fin.val h; dsimp only at hv; omega
            simp [hne]
          · simp [zhat, zmod2_add_self]
          · simp [zhat, hzm]
        have hker_equiv : LinearMap.ker (pathMat w).mulVecLin ≃ₗ[ZMod 2]
            LinearMap.ker (pathMat w').mulVecLin × ZMod 2 :=
          { toFun := fun y =>
              (⟨fun j => y.1 ⟨j.val, by omega⟩ + y.1 ⟨m + 1, by omega⟩ • z j, by
                have hy := (hstep_ker y.1).mp y.2
                rw [hwm1] at hy
                ext j
                have hlin : (pathMat w').mulVec (fun j => y.1 ⟨j.val, by omega⟩ + y.1 ⟨m + 1, by omega⟩ • z j) =
                    (pathMat w').mulVec (fun j => y.1 ⟨j.val, by omega⟩) +
                      y.1 ⟨m + 1, by omega⟩ • (pathMat w').mulVec z := by
                  rw [← Matrix.mulVecLin_apply, ← Matrix.mulVecLin_apply, ← Matrix.mulVecLin_apply,
                    ← map_smul, ← map_add]
                  rfl
                rw [Matrix.mulVecLin_apply, hlin, hz]
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
                by_cases hj : j.val < m
                · have hne : j ≠ ⟨m, by omega⟩ := fun h => by have hv := congrArg Fin.val h; dsimp only at hv; omega
                  simp [hy.1 ⟨j.val, hj⟩, hne]
                · have hjm : j = ⟨m, by omega⟩ := Fin.ext (by dsimp only; have := j.2; omega)
                  rw [hjm]
                  simpa using hy.2.1⟩,
               y.1 ⟨m + 1, by omega⟩)
            invFun := fun p =>
              ⟨fun i => (if h : i.val < m + 1 then p.1.1 ⟨i.val, h⟩ else 0) + p.2 • zhat i, by
                change (pathMat w).mulVec _ = 0
                have hadd : (fun i : Fin (m + 2) =>
                    (if h : i.val < m + 1 then p.1.1 ⟨i.val, h⟩ else 0) + p.2 • zhat i) =
                    (fun i => if h : i.val < m + 1 then p.1.1 ⟨i.val, h⟩ else 0) + p.2 • zhat := rfl
                rw [hadd, Matrix.mulVec_add, Matrix.mulVec_smul, hzhat_ker, smul_zero, add_zero]
                rw [hstep_ker, hwm1]
                have hrestr : (fun j : Fin (m + 1) =>
                    if h : j.val < m + 1 then p.1.1 ⟨j.val, h⟩ else 0) = p.1.1 := by
                  ext j; simp only [j.2, ↓reduceDIte]
                have hp0 : (pathMat w').mulVec p.1.1 = 0 := p.1.2
                rw [hrestr, hp0]
                simp [hall0 p.1.1 p.1.2]⟩
            left_inv := fun y => by
              apply Subtype.ext; ext i
              by_cases h : i.val < m + 1
              · simp only [h, ↓reduceDIte, zhat, smul_eq_mul]
                have hi_eq : (⟨i.val, by omega⟩ : Fin (m + 2)) = i := rfl
                rw [hi_eq]
                have := zmod2_add_self (y.1 ⟨m + 1, by omega⟩ * z ⟨i.val, h⟩)
                calc
                  y.1 i + y.1 ⟨m + 1, by omega⟩ * z ⟨i.val, h⟩ +
                      y.1 ⟨m + 1, by omega⟩ * z ⟨i.val, h⟩
                      = y.1 i + (y.1 ⟨m + 1, by omega⟩ * z ⟨i.val, h⟩ +
                        y.1 ⟨m + 1, by omega⟩ * z ⟨i.val, h⟩) := by ring
                  _ = y.1 i := by rw [this, add_zero]
              · have hi : i = ⟨m + 1, by omega⟩ := Fin.ext (by dsimp only; have := i.2; omega)
                rw [hi]; simp [zhat]
            right_inv := fun ⟨⟨x, hx⟩, c⟩ => by
              ext i
              · simp only [i.2, ↓reduceDIte, zhat, smul_eq_mul, lt_self_iff_false, zero_add, mul_one]
                have := zmod2_add_self (c * z i)
                calc
                  x i + c * z i + c * z i = x i + (c * z i + c * z i) := by ring
                  _ = x i := by rw [this, add_zero]
              · simp [zhat]
            map_add' := fun y1 y2 => by
              ext i
              · simp only [Submodule.coe_add, Pi.add_apply, Prod.fst_add, smul_eq_mul]; ring
              · simp
            map_smul' := fun c y => by
              ext i
              · simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, Prod.smul_fst,
                  RingHom.id_apply]
                ring
              · simp }
        have hrank_eq : (pathMat w).rank = (pathMat w').rank := by
          have h1 := hrank_add_ker (m + 1 + 1) (pathMat w)
          have h2 := hrank_add_ker (m + 1) (pathMat w')
          have h3 : Module.finrank (ZMod 2) (LinearMap.ker (pathMat w).mulVecLin) =
              Module.finrank (ZMod 2) (LinearMap.ker (pathMat w').mulVecLin) + 1 := by
            rw [hker_equiv.finrank_eq, Module.finrank_prod, Module.finrank_self]
          omega
        rw [hP_eq, show Mbit (w ⟨m, by omega⟩) = M1 by simp [Mbit, hwm1], hrank_eq]
        refine ⟨⟨zhat, hzhat_ker, by simp [zhat]⟩, ?_, ?_⟩
        · simp [Matrix.mul_apply, Fin.sum_univ_two, M1, P', h01]
        · simp [Matrix.mul_apply, M1, P', h00]

lemma trace_Amat_bound (k : ℕ) :
    (2 : ℤ) ^ k * Matrix.trace (Amat ^ k) ≤ 2 * (7 : ℤ) ^ k := by
  have hA2 : Amat ^ 2 = Amat + (8 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  have hrec : ∀ n : ℕ, Matrix.trace (Amat ^ (n + 2)) =
      Matrix.trace (Amat ^ (n + 1)) + 8 * Matrix.trace (Amat ^ n) := by
    intro n
    rw [show n + 2 = n + 2 by rfl, pow_add, hA2, Matrix.mul_add, Matrix.mul_smul, mul_one,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, ← pow_succ]
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    match k with
    | 0 =>
      have h0 : Matrix.trace (Amat ^ 0) = 2 := by decide
      rw [h0]; norm_num
    | 1 =>
      have h1 : Matrix.trace (Amat ^ 1) = 1 := by decide
      rw [h1]; norm_num
    | n + 2 =>
      rw [hrec n]
      have ih1 := ih (n + 1) (by omega)
      have ih0 := ih n (by omega)
      have h7nn : (0 : ℤ) ≤ (7 : ℤ) ^ n := by positivity
      have hterm1 : (2 : ℤ) ^ (n + 2) * Matrix.trace (Amat ^ (n + 1)) ≤ 28 * (7 : ℤ) ^ n := by
        calc
          (2 : ℤ) ^ (n + 2) * Matrix.trace (Amat ^ (n + 1))
              = 2 * ((2 : ℤ) ^ (n + 1) * Matrix.trace (Amat ^ (n + 1))) := by ring
          _ ≤ 2 * (2 * (7 : ℤ) ^ (n + 1)) := by linarith
          _ = 28 * (7 : ℤ) ^ n := by ring
      have hterm2 : (2 : ℤ) ^ (n + 2) * (8 * Matrix.trace (Amat ^ n)) ≤ 64 * (7 : ℤ) ^ n := by
        calc
          (2 : ℤ) ^ (n + 2) * (8 * Matrix.trace (Amat ^ n))
              = 32 * ((2 : ℤ) ^ n * Matrix.trace (Amat ^ n)) := by ring
          _ ≤ 32 * (2 * (7 : ℤ) ^ n) := by linarith
          _ = 64 * (7 : ℤ) ^ n := by ring
      calc
        (2 : ℤ) ^ (n + 2) * (Matrix.trace (Amat ^ (n + 1)) + 8 * Matrix.trace (Amat ^ n))
            = (2 : ℤ) ^ (n + 2) * Matrix.trace (Amat ^ (n + 1)) +
              (2 : ℤ) ^ (n + 2) * (8 * Matrix.trace (Amat ^ n)) := by ring
        _ ≤ 28 * (7 : ℤ) ^ n + 64 * (7 : ℤ) ^ n := add_le_add hterm1 hterm2
        _ ≤ 2 * (7 : ℤ) ^ (n + 2) := by
          have : (2 : ℤ) * (7 : ℤ) ^ (n + 2) = 98 * (7 : ℤ) ^ n := by ring
          linarith

def mixZMod {k : ℕ} [NeZero k] (d : ℕ) :
    (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2) :=
  { toFun := fun x i => x (i - (d : ZMod k)) + x i + x (i + (d : ZMod k))
    map_add' := fun x y => by ext i; simp only [Pi.add_apply]; ring
    map_smul' := fun c x => by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

lemma mixZMod_symm {k : ℕ} [NeZero k] (d : ℕ) (u v : ZMod k → ZMod 2) :
    dotProduct u (mixZMod d v) = dotProduct (mixZMod d u) v := by
  simp only [dotProduct, mixZMod, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  have h1 : (∑ i : ZMod k, u i * v (i - (d : ZMod k))) =
      ∑ i : ZMod k, u (i + (d : ZMod k)) * v i := by
    have hbij : Function.Bijective (fun i : ZMod k => i - (d : ZMod k)) :=
      Function.bijective_iff_has_inverse.mpr ⟨fun i => i + (d : ZMod k),
        fun i => by ring, fun i => by ring⟩
    refine Fintype.sum_bijective (fun i => i - (d : ZMod k)) hbij _ _ fun i => ?_
    simp [sub_add_cancel]
  have h2 : (∑ i : ZMod k, u i * v (i + (d : ZMod k))) =
      ∑ i : ZMod k, u (i - (d : ZMod k)) * v i := by
    have hbij : Function.Bijective (fun i : ZMod k => i + (d : ZMod k)) :=
      Function.bijective_iff_has_inverse.mpr ⟨fun i => i - (d : ZMod k),
        fun i => by ring, fun i => by ring⟩
    refine Fintype.sum_bijective (fun i => i + (d : ZMod k)) hbij _ _ fun i => ?_
    simp [add_sub_cancel_right]
  rw [h1, h2]
  ring

lemma finrank_ker_mixZMod {k : ℕ} [NeZero k] (d : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.ker (mixZMod (k := k) d)) =
      if 3 ∣ k / Nat.gcd k d then 2 * Nat.gcd k d else 0 := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  by_cases hd0 : d = 0
  · subst hd0
    have hg : Nat.gcd k 0 = k := Nat.gcd_zero_right k
    have hdiv : k / k = 1 := Nat.div_self hk
    have hns : ¬ (3 ∣ k / Nat.gcd k 0) := by rw [hg, hdiv]; decide
    simp only [hns, ↓reduceIte]
    have hker : LinearMap.ker (mixZMod (k := k) 0) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      ext i
      have hi := congrFun hx i
      simp only [mixZMod, LinearMap.coe_mk, AddHom.coe_mk, Nat.cast_zero, sub_zero, add_zero,
        Pi.zero_apply] at hi
      rw [zmod2_add_self, zero_add] at hi
      exact hi
    rw [hker]; simp
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    let g := Nat.gcd k d
    let L := k / g
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d hk
    have hg_dvd_k : g ∣ k := Nat.gcd_dvd_left k d
    have hg_dvd_d : g ∣ d := Nat.gcd_dvd_right k d
    have hk_eq : g * L = k := Nat.mul_div_cancel' hg_dvd_k
    have hd_eq : g * (d / g) = d := Nat.mul_div_cancel' hg_dvd_d
    have hL_pos : 0 < L := Nat.div_pos (Nat.le_of_dvd hk hg_dvd_k) hg_pos
    have hcop : Nat.Coprime L (d / g) := Nat.coprime_div_gcd_div_gcd hg_pos
    let orb : Fin g → ℕ → ZMod k := fun r t => ((r.val + t * d : ℕ) : ZMod k)
    have horb_period : ∀ r t, orb r (t + L) = orb r t := by
      intro r t
      simp only [orb]
      rw [ZMod.natCast_eq_natCast_iff']
      have hmul : L * d = k * (d / g) := by
        apply Nat.eq_of_mul_eq_mul_left hg_pos
        calc
          g * (L * d) = (g * L) * d := by ring
          _ = k * d := by rw [hk_eq]
          _ = k * (g * (d / g)) := by rw [hd_eq]
          _ = g * (k * (d / g)) := by ring
      have h1 : r.val + (t + L) * d = (r.val + t * d) + k * (d / g) := by
        rw [Nat.add_mul, hmul]; ring
      rw [h1, Nat.add_mul_mod_self_left]
    have horb_bij : Function.Bijective (fun p : Fin g × Fin L => orb p.1 p.2.val) := by
      have hcard : Fintype.card (Fin g × Fin L) = Fintype.card (ZMod k) := by
        simp [ZMod.card, hk_eq]
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨?_, hcard⟩
      intro ⟨r1, t1⟩ ⟨r2, t2⟩ heq
      simp only [orb] at heq
      rw [ZMod.natCast_eq_natCast_iff'] at heq
      have hr_eq : r1 = r2 := by
        have hmod_g : ∀ a, (a % k) % g = a % g := fun a => Nat.mod_mod_of_dvd a hg_dvd_k
        have h1 := congrArg (fun x => x % g) heq
        rw [hmod_g, hmod_g] at h1
        have hmul_g : ∀ t, (t * d) % g = 0 := fun t =>
          Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hg_dvd_d t)
        rw [Nat.add_mod, hmul_g, Nat.add_zero, Nat.mod_mod,
          Nat.add_mod, hmul_g, Nat.add_zero, Nat.mod_mod,
          Nat.mod_eq_of_lt r1.2, Nat.mod_eq_of_lt r2.2] at h1
        exact Fin.ext h1
      subst hr_eq
      have ht_eq : t1 = t2 := by
        have haux : ∀ a b : Fin L, a.val ≤ b.val →
            (r1.val + a.val * d) % k = (r1.val + b.val * d) % k → a = b := by
          intro a b hab hmod
          have hdvd : k ∣ (r1.val + b.val * d) - (r1.val + a.val * d) :=
            (Nat.modEq_iff_dvd' (by nlinarith)).mp hmod
          have hsub : (r1.val + b.val * d) - (r1.val + a.val * d) = (b.val - a.val) * d := by
            rw [Nat.add_sub_add_left, ← Nat.sub_mul]
          have hdvd' : (g * L) ∣ (b.val - a.val) * (g * (d / g)) := by
            rwa [hk_eq, hd_eq, ← hsub]
          have hdvd2 : L ∣ (b.val - a.val) * (d / g) := by
            have hrew : (b.val - a.val) * (g * (d / g)) = g * ((b.val - a.val) * (d / g)) := by ring
            rw [hrew] at hdvd'
            exact (mul_dvd_mul_iff_left (ne_of_gt hg_pos)).mp hdvd'
          have hdvd3 : L ∣ (b.val - a.val) := hcop.dvd_of_dvd_mul_right hdvd2
          have h0 : b.val - a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd3 (by omega)
          ext; omega
        by_cases hle : t1.val ≤ t2.val
        · exact haux t1 t2 hle heq
        · exact (haux t2 t1 (by omega) heq.symm).symm
      subst ht_eq; rfl
    have horb_step : ∀ z : ZMod k → ZMod 2, mixZMod d z = 0 →
        ∀ r t, z (orb r t) =
          if t % 3 = 0 then z (orb r 0)
          else if t % 3 = 1 then z (orb r 1)
          else z (orb r 0) + z (orb r 1) := by
      intro z hz r t
      have hrec : ∀ n, z (orb r (n + 2)) = z (orb r (n + 1)) + z (orb r n) := by
        intro n
        have h0 := congrFun hz (orb r (n + 1))
        simp only [mixZMod, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
        have hsub : orb r (n + 1) - (d : ZMod k) = orb r n := by
          simp only [orb]; push_cast; ring
        have hadd : orb r (n + 1) + (d : ZMod k) = orb r (n + 2) := by
          simp only [orb]; push_cast; ring
        rw [hsub, hadd] at h0
        have h1 := congrArg (fun u => u + z (orb r (n + 2))) h0
        simp only [zero_add] at h1
        have hlhs : z (orb r n) + z (orb r (n + 1)) + z (orb r (n + 2)) + z (orb r (n + 2)) =
            z (orb r (n + 1)) + z (orb r n) := by
          rw [add_assoc, zmod2_add_self, add_zero, add_comm]
        rw [hlhs] at h1
        exact h1.symm
      induction t using Nat.strong_induction_on with
      | ind t ih =>
        match t with
        | 0 => simp
        | 1 => simp
        | n + 2 =>
          rw [hrec n, ih (n + 1) (by omega), ih n (by omega)]
          have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
          rcases hmod with h0 | h1 | h2
          · have h1' : (n + 1) % 3 = 1 := by omega
            have h2' : (n + 2) % 3 = 2 := by omega
            simp only [h0, h1', h2', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
              OfNat.ofNat_ne_one]; ring
          · have h1' : (n + 1) % 3 = 2 := by omega
            have h2' : (n + 2) % 3 = 0 := by omega
            simp only [h1, h1', h2', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
              OfNat.ofNat_ne_one]
            rw [add_assoc, zmod2_add_self, add_zero]
          · have h1' : (n + 1) % 3 = 0 := by omega
            have h2' : (n + 2) % 3 = 1 := by omega
            simp only [h2, h1', h2', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
              OfNat.ofNat_ne_one]
            rw [← add_assoc, zmod2_add_self, zero_add]
    let e : (Fin g × Fin L) ≃ ZMod k := Equiv.ofBijective _ horb_bij
    split_ifs with hsing
    · have hL3 : 3 ≤ L := Nat.le_of_dvd hL_pos hsing
      let mkVec : (Fin g × Fin 2 → ZMod 2) → (ZMod k → ZMod 2) := fun a v =>
        let p := e.symm v
        if p.2.val % 3 = 0 then a (p.1, 0)
        else if p.2.val % 3 = 1 then a (p.1, 1)
        else a (p.1, 0) + a (p.1, 1)
      have hmk_orb : ∀ a r t,
          mkVec a (orb r t) =
            if t % 3 = 0 then a (r, 0)
            else if t % 3 = 1 then a (r, 1)
            else a (r, 0) + a (r, 1) := by
        intro a r t
        have hdiv : t = (t / L) * L + t % L := (Nat.div_add_mod' t L).symm
        have hm : orb r t = orb r (t % L) := by
          have hstep : ∀ q : ℕ, orb r (q * L + t % L) = orb r (t % L) := by
            intro q
            induction q with
            | zero => simp
            | succ q ih =>
              rw [show (q + 1) * L + t % L = (q * L + t % L) + L by ring, horb_period, ih]
          conv_lhs => rw [hdiv]
          exact hstep (t / L)
        have he_symm : e.symm (orb r (t % L)) = (r, ⟨t % L, Nat.mod_lt _ hL_pos⟩) := by
          apply e.injective; rw [Equiv.apply_symm_apply]; rfl
        have hmod3 : (t % L) % 3 = t % 3 := Nat.mod_mod_of_dvd t hsing
        simp only [mkVec, hm, he_symm, hmod3]
      have hmk_ker : ∀ a, mixZMod d (mkVec a) = 0 := by
        intro a
        ext v
        have hv : v = orb (e.symm v).1 (e.symm v).2.val := (e.apply_symm_apply v).symm
        let r := (e.symm v).1
        let t := (e.symm v).2.val
        have hv_eq : v = orb r (t + L) := by rw [horb_period]; exact hv
        simp only [mixZMod, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
        have hsub : orb r (t + L) - (d : ZMod k) = orb r (t + L - 1) := by
          have h1 : t + L = (t + L - 1) + 1 := by omega
          rw [h1]; simp only [orb]; push_cast; ring
        have hadd : orb r (t + L) + (d : ZMod k) = orb r (t + L + 1) := by
          simp only [orb]; push_cast; ring
        rw [hv_eq, hsub, hadd, hmk_orb, hmk_orb, hmk_orb]
        have hmod : (t + L - 1) % 3 = 0 ∨ (t + L - 1) % 3 = 1 ∨ (t + L - 1) % 3 = 2 := by omega
        rcases hmod with h0 | h1 | h2
        · have h1' : (t + L) % 3 = 1 := by omega
          have h2' : (t + L + 1) % 3 = 2 := by omega
          simp only [h0, h1', h2', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
            OfNat.ofNat_ne_one]
          have : a (r, 0) + a (r, 1) + (a (r, 0) + a (r, 1)) = 0 := zmod2_add_self _
          exact this
        · have h1' : (t + L) % 3 = 2 := by omega
          have h2' : (t + L + 1) % 3 = 0 := by omega
          simp only [h1, h1', h2', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
            OfNat.ofNat_ne_one]
          have : a (r, 0) + a (r, 1) + (a (r, 0) + a (r, 1)) = 0 := zmod2_add_self _
          calc
            a (r, 1) + (a (r, 0) + a (r, 1)) + a (r, 0)
                = a (r, 0) + a (r, 1) + (a (r, 0) + a (r, 1)) := by ring
            _ = 0 := this
        · have h1' : (t + L) % 3 = 0 := by omega
          have h2' : (t + L + 1) % 3 = 1 := by omega
          simp only [h2, h1', h2', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
            OfNat.ofNat_ne_one]
          have : a (r, 0) + a (r, 1) + (a (r, 0) + a (r, 1)) = 0 := zmod2_add_self _
          calc
            a (r, 0) + a (r, 1) + a (r, 0) + a (r, 1)
                = a (r, 0) + a (r, 1) + (a (r, 0) + a (r, 1)) := by ring
            _ = 0 := this
      let Ψ : (Fin g × Fin 2 → ZMod 2) →ₗ[ZMod 2] LinearMap.ker (mixZMod (k := k) d) :=
        { toFun := fun a => ⟨mkVec a, hmk_ker a⟩
          map_add' := fun a1 a2 => by
            apply Subtype.ext; ext v; simp only [mkVec, Submodule.coe_add, Pi.add_apply]
            split_ifs <;> ring
          map_smul' := fun c a => by
            apply Subtype.ext; ext v
            simp only [mkVec, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            split_ifs <;> ring }
      have hΨ_bij : Function.Bijective Ψ := by
        constructor
        · intro a1 a2 heq
          have hval : mkVec a1 = mkVec a2 := congrArg Subtype.val heq
          ext ⟨r, c⟩
          fin_cases c
          · simpa [hmk_orb] using congrFun hval (orb r 0)
          · simpa [hmk_orb] using congrFun hval (orb r 1)
        · rintro ⟨z, hz⟩
          let a : Fin g × Fin 2 → ZMod 2 := fun rc =>
            if rc.2.val = 0 then z (orb rc.1 0) else z (orb rc.1 1)
          refine ⟨a, ?_⟩
          apply Subtype.ext; ext v
          have hv : v = orb (e.symm v).1 (e.symm v).2.val := (e.apply_symm_apply v).symm
          conv_lhs => rw [hv]
          conv_rhs => rw [hv]
          change mkVec a (orb (e.symm v).1 (e.symm v).2.val) = z (orb (e.symm v).1 (e.symm v).2.val)
          rw [hmk_orb, horb_step z hz]
          simp [a]
      rw [← (LinearEquiv.ofBijective Ψ hΨ_bij).finrank_eq]
      simp [g, Nat.mul_comm]
    · have hker_bot : LinearMap.ker (mixZMod (k := k) d) = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro z hz
        ext v
        have hv : v = orb (e.symm v).1 (e.symm v).2.val := (e.apply_symm_apply v).symm
        rw [hv]
        let r := (e.symm v).1
        have h0 : z (orb r L) = z (orb r 0) := by simpa using congrArg z (horb_period r 0)
        have h1 : z (orb r (L + 1)) = z (orb r 1) := by
          have hp := horb_period r 1
          rw [show 1 + L = L + 1 by omega] at hp
          exact congrArg z hp
        rw [horb_step z hz r L] at h0
        rw [horb_step z hz r (L + 1)] at h1
        have hmod : L % 3 = 1 ∨ L % 3 = 2 := by
          have hne : L % 3 ≠ 0 := fun h => hsing (Nat.dvd_of_mod_eq_zero h)
          omega
        have hzero01 : z (orb r 0) = 0 ∧ z (orb r 1) = 0 := by
          rcases hmod with hm1 | hm2
          · have hm1' : (L + 1) % 3 = 2 := by omega
            simp only [hm1, hm1', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
              OfNat.ofNat_ne_one] at h0 h1
            have hz0 : z (orb r 0) = 0 := by
              simpa [add_assoc, zmod2_add_self] using congrArg (fun x => x + z (orb r 1)) h1
            exact ⟨hz0, by rw [h0, hz0]⟩
          · have hm2' : (L + 1) % 3 = 0 := by omega
            simp only [hm2, hm2', ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] at h0 h1
            have hz1 : z (orb r 1) = 0 := by
              have := congrArg (fun x => x + z (orb r 0)) h0
              have hlhs : z (orb r 0) + z (orb r 1) + z (orb r 0) = z (orb r 1) := by
                calc
                  z (orb r 0) + z (orb r 1) + z (orb r 0)
                      = (z (orb r 0) + z (orb r 0)) + z (orb r 1) := by ring
                  _ = z (orb r 1) := by rw [zmod2_add_self, zero_add]
              rw [hlhs, zmod2_add_self] at this
              exact this
            exact ⟨by rw [h1, hz1], hz1⟩
        rw [horb_step z hz r (e.symm v).2.val, hzero01.1, hzero01.2]
        simp
      rw [hker_bot]; simp

lemma rank_sandwich_bounds {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (T P : V →ₗ[ZMod 2] V) :
    Module.finrank (ZMod 2) (LinearMap.range (T.comp (P.comp T))) ≤
      Module.finrank (ZMod 2) (LinearMap.range P) ∧
    Module.finrank (ZMod 2) (LinearMap.range P) ≤
      Module.finrank (ZMod 2) (LinearMap.range (T.comp (P.comp T))) +
        2 * Module.finrank (ZMod 2) (LinearMap.ker T) := by
  have h1 : Module.finrank (ZMod 2) (LinearMap.range (P.comp T)) ≤
      Module.finrank (ZMod 2) (LinearMap.range P) := by
    refine Submodule.finrank_mono ?_
    rintro y ⟨x, rfl⟩
    exact ⟨T x, rfl⟩
  have h2 : Module.finrank (ZMod 2) (LinearMap.range (T.comp (P.comp T))) ≤
      Module.finrank (ZMod 2) (LinearMap.range (P.comp T)) := by
    let R := LinearMap.range (P.comp T)
    let Tres := T.domRestrict R
    have hreq : LinearMap.range Tres = LinearMap.range (T.comp (P.comp T)) := by
      ext y
      constructor
      · rintro ⟨⟨z, ⟨x, rfl⟩⟩, rfl⟩; exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩; exact ⟨⟨P (T x), ⟨x, rfl⟩⟩, rfl⟩
    have hr := LinearMap.finrank_range_add_finrank_ker Tres
    rw [hreq] at hr
    have hR : Module.finrank (ZMod 2) R = Module.finrank (ZMod 2) (LinearMap.range (P.comp T)) := rfl
    rw [hR] at hr
    omega
  have hpost : ∀ (A B : V →ₗ[ZMod 2] V),
      Module.finrank (ZMod 2) (LinearMap.range B) ≤
        Module.finrank (ZMod 2) (LinearMap.range (A.comp B)) +
          Module.finrank (ZMod 2) (LinearMap.ker A) := by
    intro A B
    let R := LinearMap.range B
    let Ares := A.domRestrict R
    have hreq : LinearMap.range Ares = LinearMap.range (A.comp B) := by
      ext y
      constructor
      · rintro ⟨⟨z, ⟨x, rfl⟩⟩, rfl⟩; exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩; exact ⟨⟨B x, ⟨x, rfl⟩⟩, rfl⟩
    let ι : LinearMap.ker Ares →ₗ[ZMod 2] LinearMap.ker A :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hι_inj : Function.Injective ι := by
      intro x y h
      have hv : x.1.1 = y.1.1 := by simpa [ι] using congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext hv)
    have hkle := LinearMap.finrank_le_finrank_of_injective hι_inj
    have hr := LinearMap.finrank_range_add_finrank_ker Ares
    rw [hreq] at hr
    have hR : Module.finrank (ZMod 2) R = Module.finrank (ZMod 2) (LinearMap.range B) := rfl
    rw [hR] at hr
    omega
  have hpre : Module.finrank (ZMod 2) (LinearMap.range P) ≤
      Module.finrank (ZMod 2) (LinearMap.range (P.comp T)) +
        Module.finrank (ZMod 2) (LinearMap.ker T) := by
    let R := LinearMap.range T
    let Pres := P.domRestrict R
    have hreq : LinearMap.range Pres = LinearMap.range (P.comp T) := by
      ext y
      constructor
      · rintro ⟨⟨z, ⟨x, rfl⟩⟩, rfl⟩; exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩; exact ⟨⟨T x, ⟨x, rfl⟩⟩, rfl⟩
    have hrPres := LinearMap.finrank_range_add_finrank_ker Pres
    have hrP := LinearMap.finrank_range_add_finrank_ker P
    have hrT := LinearMap.finrank_range_add_finrank_ker T
    let ι : LinearMap.ker Pres →ₗ[ZMod 2] LinearMap.ker P :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hι_inj : Function.Injective ι := by
      intro x y h
      have hv : x.1.1 = y.1.1 := by simpa [ι] using congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext hv)
    have hkle := LinearMap.finrank_le_finrank_of_injective hι_inj
    rw [hreq] at hrPres
    have hR : Module.finrank (ZMod 2) R = Module.finrank (ZMod 2) (LinearMap.range T) := rfl
    rw [hR] at hrPres
    omega
  have hstep2 := hpost T (P.comp T)
  exact ⟨le_trans h2 h1, by omega⟩

def PbMat {k : ℕ} [NeZero k] (b : ZMod k → ZMod 2) : Matrix (ZMod k) (ZMod k) (ZMod 2) :=
  Matrix.of fun i j =>
    (if j = i + 1 then b (i - 1) else 0) + (if j = i - 1 then b (i - 2) else 0)

lemma PbMat_mulVec {k : ℕ} [NeZero k] (b x : ZMod k → ZMod 2) (i : ZMod k) :
    (PbMat b).mulVec x i = b (i - 1) * x (i + 1) + b (i - 2) * x (i - 1) := by
  simp only [PbMat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  simp_rw [add_mul, Finset.sum_add_distrib]
  have h1 : (∑ j : ZMod k, (if j = i + 1 then b (i - 1) else 0) * x j) = b (i - 1) * x (i + 1) := by
    rw [Finset.sum_eq_single (i + 1)]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : (∑ j : ZMod k, (if j = i - 1 then b (i - 2) else 0) * x j) = b (i - 2) * x (i - 1) := by
    rw [Finset.sum_eq_single (i - 1)]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, h2]

def nlRow {k : ℕ} [NeZero k] (y : ZMod k → ZMod 2) (j : ZMod k) : ZMod 2 :=
  y j + (1 + y (j + 1)) * y (j + 2)

lemma PbMat_polar {k : ℕ} [NeZero k] (b u v w : ZMod k → ZMod 2) :
    dotProduct b (nlRow (u + v + w)) + dotProduct b (nlRow (u + v)) +
      dotProduct b (nlRow (u + w)) + dotProduct b (nlRow u) =
    dotProduct v ((PbMat b).mulVec w) := by
  have hsite : ∀ j : ZMod k,
      nlRow (u + v + w) j + nlRow (u + v) j + nlRow (u + w) j + nlRow u j =
        v (j + 1) * w (j + 2) + w (j + 1) * v (j + 2) := by
    intro j
    simp only [nlRow, Pi.add_apply]
    have hring :
        u j + v j + w j + (1 + (u (j + 1) + v (j + 1) + w (j + 1))) *
            (u (j + 2) + v (j + 2) + w (j + 2)) +
          (u j + v j + (1 + (u (j + 1) + v (j + 1))) * (u (j + 2) + v (j + 2))) +
          (u j + w j + (1 + (u (j + 1) + w (j + 1))) * (u (j + 2) + w (j + 2))) +
          (u j + (1 + u (j + 1)) * u (j + 2)) =
        (v (j + 1) * w (j + 2) + w (j + 1) * v (j + 2)) +
          ((u j + u j) + (u j + u j)) + (v j + v j) + (w j + w j) +
          ((u (j + 2) + u (j + 2)) + (u (j + 2) + u (j + 2))) +
          (v (j + 2) + v (j + 2)) + (w (j + 2) + w (j + 2)) +
          ((u (j + 1) * u (j + 2) + u (j + 1) * u (j + 2)) +
            (u (j + 1) * u (j + 2) + u (j + 1) * u (j + 2))) +
          (u (j + 1) * v (j + 2) + u (j + 1) * v (j + 2)) +
          (u (j + 1) * w (j + 2) + u (j + 1) * w (j + 2)) +
          (v (j + 1) * u (j + 2) + v (j + 1) * u (j + 2)) +
          (w (j + 1) * u (j + 2) + w (j + 1) * u (j + 2)) +
          (v (j + 1) * v (j + 2) + v (j + 1) * v (j + 2)) +
          (w (j + 1) * w (j + 2) + w (j + 1) * w (j + 2)) := by ring
    rw [hring]
    simp only [zmod2_add_self, add_zero]
  have hsplit :
      dotProduct b (nlRow (u + v + w)) + dotProduct b (nlRow (u + v)) +
        dotProduct b (nlRow (u + w)) + dotProduct b (nlRow u) =
      ∑ j : ZMod k, b j * (nlRow (u + v + w) j + nlRow (u + v) j + nlRow (u + w) j + nlRow u j) := by
    simp only [dotProduct]
    simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  simp_rw [hsite, mul_add, Finset.sum_add_distrib]
  have h1 : (∑ j : ZMod k, b j * (v (j + 1) * w (j + 2))) =
      ∑ i : ZMod k, v i * (b (i - 1) * w (i + 1)) := by
    have hbij : Function.Bijective (fun j : ZMod k => j + 1) :=
      Function.bijective_iff_has_inverse.mpr ⟨fun j => j - 1, fun j => by ring, fun j => by ring⟩
    refine Fintype.sum_bijective (fun j => j + 1) hbij _ _ fun j => ?_
    have h1' : j + 1 - 1 = j := by ring
    have h2' : j + 1 + 1 = j + 2 := by ring
    rw [h1', h2']; ring
  have h2 : (∑ j : ZMod k, b j * (w (j + 1) * v (j + 2))) =
      ∑ i : ZMod k, v i * (b (i - 2) * w (i - 1)) := by
    have hbij : Function.Bijective (fun j : ZMod k => j + 2) :=
      Function.bijective_iff_has_inverse.mpr ⟨fun j => j - 2, fun j => by ring, fun j => by ring⟩
    refine Fintype.sum_bijective (fun j => j + 2) hbij _ _ fun j => ?_
    have h1' : j + 2 - 2 = j := by ring
    have h2' : j + 2 - 1 = j + 1 := by ring
    rw [h1', h2']; ring
  rw [h1, h2, ← Finset.sum_add_distrib]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PbMat_mulVec b w i]
  ring

lemma PbMat_allones_rank (k : ℕ) [NeZero k] :
    (PbMat (k := k) (fun _ => 1)).rank = if k % 2 = 1 then k - 1 else k - 2 := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hker_eq : ∀ x : ZMod k → ZMod 2,
      (PbMat (fun _ => 1)).mulVec x = 0 ↔ ∀ i : ZMod k, x (i + 2) = x i := by
    intro x
    constructor
    · intro h0 i
      have hi := congrFun h0 (i + 1)
      rw [PbMat_mulVec] at hi
      simp only [one_mul, add_sub_cancel_right, Pi.zero_apply] at hi
      have h1 : i + 1 + 1 = i + 2 := by ring
      rw [h1] at hi
      have h2 := congrArg (fun t => t + x i) hi
      simp only [zero_add, add_assoc, zmod2_add_self, add_zero] at h2
      exact h2
    · intro hall
      ext i
      rw [PbMat_mulVec]
      simp only [one_mul, Pi.zero_apply]
      have h1 := hall (i - 1)
      have h2 : i - 1 + 2 = i + 1 := by ring
      rw [h2] at h1
      rw [h1, zmod2_add_self]
  have hhr := LinearMap.finrank_range_add_finrank_ker (PbMat (k := k) (fun _ => 1)).mulVecLin
  have hdimV : Module.finrank (ZMod 2) (ZMod k → ZMod 2) = k := by simp [ZMod.card]
  rw [hdimV] at hhr
  by_cases hodd : k % 2 = 1
  · simp only [hodd, ↓reduceIte]
    have hker1 : Module.finrank (ZMod 2) (LinearMap.ker (PbMat (k := k) (fun _ => 1)).mulVecLin) = 1 := by
      let φ : ZMod 2 →ₗ[ZMod 2] LinearMap.ker (PbMat (k := k) (fun _ => 1)).mulVecLin :=
        { toFun := fun c => ⟨fun _ => c, by change (PbMat _).mulVec _ = 0; rw [hker_eq]; intro _; rfl⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hbij : Function.Bijective φ := by
        constructor
        · intro c1 c2 h
          exact congrFun (congrArg Subtype.val h) 0
        · rintro ⟨x, hx⟩
          refine ⟨x 0, ?_⟩
          apply Subtype.ext
          ext i
          have hall := (hker_eq x).mp hx
          have hstep : ∀ n : ℕ, x (2 * n : ZMod k) = x 0 := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              have heq : (2 * ((n + 1 : ℕ) : ZMod k)) = (2 * (n : ZMod k)) + 2 := by push_cast; ring
              rw [heq, hall, ih]
          have hinv : ∃ n : ℕ, (2 * n : ZMod k) = i := by
            have hcop : Nat.Coprime 2 k := by
              exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (fun hdvd => by
                obtain ⟨q, rfl⟩ := hdvd; omega)
            have hu : IsUnit (2 : ZMod k) := (ZMod.isUnit_iff_coprime 2 k).mpr hcop
            rcases hu with ⟨u, hu⟩
            let m := (((u⁻¹ : (ZMod k)ˣ) : ZMod k) * i).val
            refine ⟨m, ?_⟩
            have hm : (m : ZMod k) = ((u⁻¹ : (ZMod k)ˣ) : ZMod k) * i := ZMod.natCast_zmod_val _
            rw [hm, ← hu, ← mul_assoc]
            simp
          rcases hinv with ⟨n, hn⟩
          rw [← hn]
          exact (hstep n).symm
      rw [← (LinearEquiv.ofBijective φ hbij).finrank_eq, Module.finrank_self]
    change Module.finrank (ZMod 2) (LinearMap.range (PbMat (k := k) (fun _ => 1)).mulVecLin) = k - 1
    omega
  · simp only [hodd, ↓reduceIte]
    have hk2 : 2 ≤ k := by omega
    have hker2 : Module.finrank (ZMod 2) (LinearMap.ker (PbMat (k := k) (fun _ => 1)).mulVecLin) = 2 := by
      let φ : (Fin 2 → ZMod 2) →ₗ[ZMod 2] LinearMap.ker (PbMat (k := k) (fun _ => 1)).mulVecLin :=
        { toFun := fun c => ⟨fun i => if i.val % 2 = 0 then c 0 else c 1, by
            change (PbMat _).mulVec _ = 0
            rw [hker_eq]
            intro i
            have h2dvd : 2 ∣ k := Nat.dvd_of_mod_eq_zero (by omega)
            have hmod : (i + 2).val % 2 = i.val % 2 := by
              have hval : (i + 2).val = (i.val + 2) % k := by
                rw [ZMod.val_add]
                have h2v : (2 : ZMod k).val = 2 % k := by
                  rw [← Nat.cast_ofNat, ZMod.val_natCast]
                rw [h2v, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              rw [hval, Nat.mod_mod_of_dvd _ h2dvd]
              omega
            simp [hmod]⟩
          map_add' := fun c1 c2 => by
            apply Subtype.ext; ext i; simp only [Submodule.coe_add, Pi.add_apply]; split_ifs <;> rfl
          map_smul' := fun a c => by
            apply Subtype.ext; ext i
            simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            split_ifs <;> rfl }
      have hbij : Function.Bijective φ := by
        constructor
        · intro c1 c2 h
          have hv := congrArg Subtype.val h
          ext j
          fin_cases j
          · have h0 := congrFun hv 0
            simpa [φ] using h0
          · have h1 := congrFun hv 1
            have hv1 : (1 : ZMod k).val = 1 := ZMod.val_one'' (by omega)
            simpa [φ, hv1] using h1
        · rintro ⟨x, hx⟩
          refine ⟨fun j => if j = 0 then x 0 else x 1, ?_⟩
          apply Subtype.ext
          ext i
          have hall := (hker_eq x).mp hx
          have hstep : ∀ n : ℕ, x (2 * n : ZMod k) = x 0 ∧ x ((2 * n + 1 : ℕ) : ZMod k) = x 1 := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              have he1 : (2 * ((n + 1 : ℕ) : ZMod k)) = (2 * (n : ZMod k)) + 2 := by push_cast; ring
              have he2 : ((2 * (n + 1) + 1 : ℕ) : ZMod k) = ((2 * n + 1 : ℕ) : ZMod k) + 2 := by
                push_cast; ring
              exact ⟨by rw [he1, hall, ih.1], by rw [he2, hall, ih.2]⟩
          have hval : (i.val : ZMod k) = i := ZMod.natCast_zmod_val i
          by_cases hev : i.val % 2 = 0
          · simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, hev, ↓reduceIte]
            have hdiv : i.val = 2 * (i.val / 2) := by omega
            rw [← hval, hdiv, Nat.cast_mul, Nat.cast_ofNat]
            exact (hstep (i.val / 2)).1.symm
          · simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, hev, ↓reduceIte, Fin.one_eq_zero_iff,
              OfNat.ofNat_ne_one]
            have hdiv : i.val = 2 * (i.val / 2) + 1 := by omega
            rw [← hval, hdiv]
            exact (hstep (i.val / 2)).2.symm
      rw [← (LinearEquiv.ofBijective φ hbij).finrank_eq]
      simp
    change Module.finrank (ZMod 2) (LinearMap.range (PbMat (k := k) (fun _ => 1)).mulVecLin) = k - 2
    omega

lemma PbMat_proper_trace {k : ℕ} [NeZero k] (b : ZMod k → ZMod 2) (hne : b ≠ fun _ => 1) :
    (2 : ℤ) ^ (PbMat b).rank =
      Matrix.trace (List.ofFn (fun i : Fin k => Mbit (b (i.val : ZMod k)))).prod := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hex0 : ∃ j0 : ZMod k, b j0 = 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext fun j => zmod2_eq_one_of_ne_zero (hall j))
  rcases hex0 with ⟨j0, hj0⟩
  let shift : Fin k → ZMod k := fun i => j0 + 2 + (i.val : ZMod k)
  have hshift_bij : Function.Bijective shift := by
    have hcard : Fintype.card (Fin k) = Fintype.card (ZMod k) := by simp [ZMod.card]
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun i1 i2 heq => ?_, hcard⟩
    have h1 : (i1.val : ZMod k) = (i2.val : ZMod k) := add_left_cancel heq
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    rw [Nat.mod_eq_of_lt i1.2, Nat.mod_eq_of_lt i2.2] at h1
    exact Fin.ext h1
  let eS : Fin k ≃ ZMod k := Equiv.ofBijective shift hshift_bij
  let w : Fin (k - 1) → ZMod 2 := fun i => b (j0 + 1 + (i.val : ZMod k))
  have hPb_reindex : (PbMat b).rank = (pathMat w).rank := by
    let eK : Fin ((k - 1) + 1) ≃ ZMod k := (finCongr (by omega)).trans eS
    let M' : Matrix (Fin ((k - 1) + 1)) (Fin ((k - 1) + 1)) (ZMod 2) := (PbMat b).submatrix eK eK
    have hM'_eq : M' = pathMat w := by
      ext i j
      simp only [M', Matrix.submatrix_apply, PbMat, Matrix.of_apply, pathMat, eK, Equiv.trans_apply,
        finCongr_apply, Fin.val_cast, eS, Equiv.ofBijective_apply, shift, w]
      have h1 : ((j0 + 2 + (j.val : ZMod k) = j0 + 2 + (i.val : ZMod k) + 1) ↔
          (i.val < k - 1 ∧ j.val = i.val + 1) ∨ (i.val = k - 1 ∧ j.val = 0)) := by
        have hi : i.val < k := by omega
        have hj : j.val < k := by omega
        have hadd : (j0 + 2 + (j.val : ZMod k) = j0 + 2 + (i.val : ZMod k) + 1) ↔
            ((j.val : ZMod k) = ((i.val + 1 : ℕ) : ZMod k)) := by
          constructor
          · intro h
            push_cast
            have h' : j0 + 2 + (j.val : ZMod k) = j0 + 2 + ((i.val : ZMod k) + 1) := by rw [h]; ring
            exact add_left_cancel h'
          · intro h
            push_cast at h
            rw [h]; ring
        rw [hadd, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj]
        by_cases him : i.val < k - 1
        · rw [Nat.mod_eq_of_lt (by omega)]
          constructor
          · intro h; exact Or.inl ⟨him, h⟩
          · rintro (⟨_, h⟩ | ⟨h', _⟩)
            · exact h
            · omega
        · have hik : i.val + 1 = k := by omega
          rw [hik, Nat.mod_self]
          constructor
          · intro h; exact Or.inr ⟨by omega, h⟩
          · rintro (⟨h', _⟩ | ⟨_, h⟩)
            · omega
            · exact h
      have h2 : ((j0 + 2 + (j.val : ZMod k) = j0 + 2 + (i.val : ZMod k) - 1) ↔
          (j.val < k - 1 ∧ i.val = j.val + 1) ∨ (j.val = k - 1 ∧ i.val = 0)) := by
        have hsym : (j0 + 2 + (j.val : ZMod k) = j0 + 2 + (i.val : ZMod k) - 1) ↔
            (j0 + 2 + (i.val : ZMod k) = j0 + 2 + (j.val : ZMod k) + 1) := by
          constructor
          · intro h; exact (sub_eq_iff_eq_add.mp h.symm)
          · intro h; exact (sub_eq_iff_eq_add.mpr h).symm
        rw [hsym]
        have hi : i.val < k := by omega
        have hj : j.val < k := by omega
        have hadd : (j0 + 2 + (i.val : ZMod k) = j0 + 2 + (j.val : ZMod k) + 1) ↔
            ((i.val : ZMod k) = ((j.val + 1 : ℕ) : ZMod k)) := by
          constructor
          · intro h
            push_cast
            have h' : j0 + 2 + (i.val : ZMod k) = j0 + 2 + ((j.val : ZMod k) + 1) := by rw [h]; ring
            exact add_left_cancel h'
          · intro h
            push_cast at h
            rw [h]; ring
        rw [hadd, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hi]
        by_cases hjm : j.val < k - 1
        · rw [Nat.mod_eq_of_lt (by omega)]
          constructor
          · intro h; exact Or.inl ⟨hjm, h⟩
          · rintro (⟨_, h⟩ | ⟨h', _⟩)
            · exact h
            · omega
        · have hjk : j.val + 1 = k := by omega
          rw [hjk, Nat.mod_self]
          constructor
          · intro h; exact Or.inr ⟨by omega, h⟩
          · rintro (⟨h', _⟩ | ⟨_, h⟩)
            · omega
            · exact h
      have hb_end1 : i.val = k - 1 → b (j0 + 2 + (i.val : ZMod k) - 1) = 0 := by
        intro hi
        have heq : j0 + 2 + (i.val : ZMod k) - 1 = j0 := by
          have hk0 : ((k : ℕ) : ZMod k) = 0 := ZMod.natCast_self k
          have hsum : (i.val : ZMod k) + 1 = 0 := by
            have hc : ((i.val + 1 : ℕ) : ZMod k) = ((k : ℕ) : ZMod k) := congrArg Nat.cast (by omega)
            push_cast at hc
            rw [hk0] at hc
            exact hc
          calc
            j0 + 2 + (i.val : ZMod k) - 1 = j0 + ((i.val : ZMod k) + 1) := by ring
            _ = j0 + 0 := by rw [hsum]
            _ = j0 := add_zero j0
        rw [heq, hj0]
      have hb_end2 : i.val = 0 → b (j0 + 2 + (i.val : ZMod k) - 2) = 0 := by
        intro hi
        rw [hi, Nat.cast_zero]
        have : j0 + 2 + 0 - 2 = j0 := by ring
        rw [this, hj0]
      congr 1
      · by_cases hA : i.val < k - 1 ∧ j.val = i.val + 1
        · have hL := h1.mpr (Or.inl hA)
          simp only [hL, ↓reduceIte]
          simp only [hA]
          congr 1; ring
        · by_cases hB : i.val = k - 1 ∧ j.val = 0
          · have hL := h1.mpr (Or.inr hB)
            simp only [hL, ↓reduceIte]
            simp only [hA, ↓reduceDIte]
            exact hb_end1 hB.1
          · have hL : ¬ (j0 + 2 + (j.val : ZMod k) = j0 + 2 + (i.val : ZMod k) + 1) := by
              rw [h1]; tauto
            simp only [hL, ↓reduceIte]
            simp only [hA, ↓reduceDIte]
      · by_cases hA : j.val < k - 1 ∧ i.val = j.val + 1
        · have hL := h2.mpr (Or.inl hA)
          simp only [hL, ↓reduceIte]
          simp only [hA]
          congr 1; push_cast; ring
        · by_cases hB : j.val = k - 1 ∧ i.val = 0
          · have hL := h2.mpr (Or.inr hB)
            simp only [hL, ↓reduceIte]
            simp only [hA, ↓reduceDIte]
            exact hb_end2 hB.2
          · have hL : ¬ (j0 + 2 + (j.val : ZMod k) = j0 + 2 + (i.val : ZMod k) - 1) := by
              rw [h2]; tauto
            simp only [hL, ↓reduceIte]
            simp only [hA, ↓reduceDIte]
    rw [← hM'_eq]
    let eV : (Fin ((k - 1) + 1) → ZMod 2) ≃ₗ[ZMod 2] (ZMod k → ZMod 2) :=
      { toFun := fun x i => x (eK.symm i)
        invFun := fun y j => y (eK j)
        left_inv := fun x => by ext j; simp
        right_inv := fun y => by ext i; simp
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hM'_conj : ∀ x, M'.mulVec x = eV.symm ((PbMat b).mulVec (eV x)) := by
      intro x; ext i
      simp only [M', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, eV,
        LinearEquiv.coe_symm_mk]
      exact Fintype.sum_bijective eK eK.bijective _ _ fun j => by simp
    let eR : LinearMap.range M'.mulVecLin ≃ₗ[ZMod 2] LinearMap.range (PbMat b).mulVecLin :=
      { toFun := fun y => ⟨eV y.1, by
          rcases y.2 with ⟨x, hx⟩
          refine ⟨eV x, ?_⟩
          simp only [Matrix.mulVecLin_apply]
          rw [← hx, Matrix.mulVecLin_apply, hM'_conj, eV.apply_symm_apply]⟩
        invFun := fun y => ⟨eV.symm y.1, by
          rcases y.2 with ⟨x, hx⟩
          refine ⟨eV.symm x, ?_⟩
          rw [Matrix.mulVecLin_apply, hM'_conj, eV.apply_symm_apply, ← hx]
          rfl⟩
        left_inv := fun y => by apply Subtype.ext; exact eV.symm_apply_apply y.1
        right_inv := fun y => by apply Subtype.ext; exact eV.apply_symm_apply y.1
        map_add' := fun _ _ => by apply Subtype.ext; simp
        map_smul' := fun _ _ => by apply Subtype.ext; simp }
    exact eR.finrank_eq.symm
  have htr_rot :
      Matrix.trace (List.ofFn (fun i : Fin k => Mbit (b (i.val : ZMod k)))).prod =
      Matrix.trace ((List.ofFn (fun i : Fin (k - 1) => Mbit (w i))).prod * M0) := by
    let r0 : ℕ := (j0 + 1).val
    have hr0_lt : r0 < k := ZMod.val_lt _
    let Lorig := List.ofFn (fun i : Fin k => Mbit (b (i.val : ZMod k)))
    have hrot_eq :
        (List.ofFn (fun i : Fin (k - 1) => Mbit (w i))) ++ [M0] =
          Lorig.drop r0 ++ Lorig.take r0 := by
      apply List.ext_getElem
      · simp [Lorig]; omega
      · intro n hn1 hn2
        have hn_lt : n < k := by simp at hn1; omega
        have hlen_drop : (Lorig.drop r0).length = k - r0 := by simp [Lorig]
        have hrhs : (Lorig.drop r0 ++ Lorig.take r0)[n] =
            Mbit (b (j0 + 1 + (n : ZMod k))) := by
          by_cases hlt : n < k - r0
          · rw [List.getElem_append_left (by omega), List.getElem_drop]
            simp only [Lorig, List.getElem_ofFn]
            congr 2
            have hcast : ((r0 + n : ℕ) : ZMod k) = j0 + 1 + (n : ZMod k) := by
              rw [Nat.cast_add]
              have hr0c : (r0 : ZMod k) = j0 + 1 := ZMod.natCast_zmod_val (j0 + 1)
              rw [hr0c]
            exact hcast
          · rw [List.getElem_append_right (by omega), List.getElem_take]
            simp only [Lorig, List.getElem_ofFn]
            congr 2
            have hlen_drop' : (List.drop r0 (List.ofFn fun i : Fin k => Mbit (b (i.val : ZMod k)))).length = k - r0 :=
              hlen_drop
            rw [hlen_drop']
            have hcast : ((n - (k - r0) : ℕ) : ZMod k) = j0 + 1 + (n : ZMod k) := by
              have heq : (n - (k - r0)) + k = r0 + n := by omega
              have hmod : ((n - (k - r0) : ℕ) : ZMod k) = ((r0 + n : ℕ) : ZMod k) := by
                rw [← heq, Nat.cast_add, ZMod.natCast_self, add_zero]
              rw [hmod, Nat.cast_add]
              have hr0c : (r0 : ZMod k) = j0 + 1 := ZMod.natCast_zmod_val (j0 + 1)
              rw [hr0c]
            exact hcast
        rw [hrhs]
        by_cases hnm : n < k - 1
        · rw [List.getElem_append_left (by simp; omega)]
          simp [w]
        · have hnk : n = k - 1 := by omega
          have hlen : (List.ofFn fun i : Fin (k - 1) => Mbit (w i)).length = k - 1 := by simp
          rw [List.getElem_append_right (by rw [hlen]; omega)]
          simp only [hlen, hnk, Nat.sub_self, List.getElem_singleton]
          have hlast : j0 + 1 + ((k - 1 : ℕ) : ZMod k) = j0 := by
            have hsum : (1 : ZMod k) + ((k - 1 : ℕ) : ZMod k) = 0 := by
              have hc : ((1 + (k - 1) : ℕ) : ZMod k) = ((k : ℕ) : ZMod k) := congrArg Nat.cast (by omega)
              push_cast at hc
              rw [ZMod.natCast_self] at hc
              exact hc
            calc
              j0 + 1 + ((k - 1 : ℕ) : ZMod k) = j0 + (1 + ((k - 1 : ℕ) : ZMod k)) := by ring
              _ = j0 + 0 := by rw [hsum]
              _ = j0 := add_zero j0
          rw [hlast, hj0]
          simp [Mbit]
    have hsplit : Lorig = Lorig.take r0 ++ Lorig.drop r0 := (List.take_append_drop r0 Lorig).symm
    have hprod_tr : Matrix.trace Lorig.prod = Matrix.trace (Lorig.drop r0 ++ Lorig.take r0).prod := by
      conv_lhs => rw [hsplit]
      rw [List.prod_append, List.prod_append, Matrix.trace_mul_comm]
    rw [hprod_tr, ← hrot_eq, List.prod_append, List.prod_singleton]
  rw [hPb_reindex, htr_rot]
  let P := (List.ofFn (fun i : Fin (k - 1) => Mbit (w i))).prod
  have htr_M0 : Matrix.trace (P * M0) = P 0 0 + P 0 1 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, M0, ↓reduceIte,
      one_ne_zero, mul_one, mul_zero, add_zero]
  rw [htr_M0]
  rcases pathMat_transfer_invariant (k - 1) w with ⟨_, h00, h01⟩ | ⟨_, h00, h01⟩
  · simp only [P, h00, h01, add_zero]
  · simp only [P, h00, h01, zero_add]

end PEqualNP.Outside.L_meta_25695_aux

open PEqualNP.Outside.L_meta_25695_aux in
theorem PEqualNP.Outside.L_meta_25695 :
    ∀ (k : ℕ) [NeZero k] (d : ℕ),
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let sign := fun (t : B) => if t = 0 then (1 : ℤ) else -1
  let mix := fun (s : ℕ) (x : V) (i : I) => x (i-(s : I)) + x i + x (i+(s : I))
  let nl := fun (y : V) (j : I) => y j + (1+y (j+1))*y (j+2)
  let pairs := fun (s : ℕ) => ∑ b : V,
    (Finset.univ.filter (fun a : V =>
      (∑ x : V, sign (dotProduct a x + dotProduct b (nl (mix s x)))) ≠ 0)).card
  let A : Matrix (Fin 2) (Fin 2) ℤ := fun src dst =>
    if src = 0 then (if dst = 0 then 1 else 4) else (if dst = 0 then 2 else 0)
  let total := Matrix.trace (A^k) +
    (if k % 2 = 1 then (2:ℤ)^(k-1) else -7*(2:ℤ)^(k-2))
  let g := Nat.gcd k d
  let h := if 3 ∣ k/g then 2*g else 0
  (pairs 0 : ℤ) = total ∧ (pairs d : ℤ) ≤ total ∧
    total ≤ (2:ℤ)^(2*h) * (pairs d : ℤ) ∧ (2:ℤ)^k * total ≤ 3*(7:ℤ)^k := by
  intro k _ d I B V sign mix nl pairs A total g h
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hpairs_eq : ∀ s : ℕ,
      let Ts : Matrix (ZMod k) (ZMod k) (ZMod 2) := LinearMap.toMatrix' (mixZMod (k := k) s)
      pairs s = ∑ b : ZMod k → ZMod 2, 2 ^ (Ts * PbMat b * Ts).rank := by
    intro s Ts
    simp only [pairs]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hTs_mv : ∀ x : ZMod k → ZMod 2, Ts.mulVec x = mix s x := by
      intro x
      have h1 : Ts.mulVec x = mixZMod s x := by
        rw [← Matrix.mulVecLin_apply]
        simp [Ts]
      rw [h1]
      rfl
    have hpolar_s : ∀ u v w : ZMod k → ZMod 2,
        dotProduct b (nl (mix s (u + v + w))) + dotProduct b (nl (mix s (u + v))) +
          dotProduct b (nl (mix s (u + w))) + dotProduct b (nl (mix s u)) =
        dotProduct v ((Ts * PbMat b * Ts).mulVec w) := by
      intro u v w
      have hm_add : ∀ x y : ZMod k → ZMod 2, mix s (x + y) = mix s x + mix s y :=
        fun x y => (mixZMod (k := k) s).map_add x y
      rw [hm_add, hm_add, hm_add]
      change dotProduct b (nlRow (mix s u + mix s v + mix s w)) +
        dotProduct b (nlRow (mix s u + mix s v)) +
        dotProduct b (nlRow (mix s u + mix s w)) +
        dotProduct b (nlRow (mix s u)) = _
      rw [PbMat_polar b (mix s u) (mix s v) (mix s w)]
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTs_mv w, hTs_mv]
      exact (mixZMod_symm s v ((PbMat b).mulVec (mix s w))).symm
    exact walsh_nonzero_card_eq_two_pow_rank (fun x => dotProduct b (nl (mix s x)))
      (Ts * PbMat b * Ts) hpolar_s
  have hpairs0_eq : pairs 0 = ∑ b : ZMod k → ZMod 2, 2 ^ (PbMat b).rank := by
    rw [hpairs_eq 0]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hT0 : LinearMap.toMatrix' (mixZMod (k := k) 0) = 1 := by
      have hm0 : mixZMod (k := k) 0 = LinearMap.id := by
        apply LinearMap.ext; intro x; ext i
        simp [mixZMod, zmod2_add_self]
      rw [hm0]
      simp
    rw [hT0, one_mul, mul_one]
  have hpairs0_total : (pairs 0 : ℤ) = total := by
    rw [hpairs0_eq]
    have hA_eq : A = Amat := rfl
    have htr_sum : Matrix.trace (A ^ k) =
        ∑ b : ZMod k → ZMod 2, Matrix.trace (List.ofFn (fun i : Fin k => Mbit (b (i.val : ZMod k)))).prod := by
      rw [hA_eq, Amat_pow_eq_sum, Matrix.trace_sum]
      let eV : (Fin k → ZMod 2) ≃ (ZMod k → ZMod 2) :=
        { toFun := fun w i => w ⟨i.val, ZMod.val_lt i⟩
          invFun := fun b i => b (i.val : ZMod k)
          left_inv := fun w => by
            ext i
            dsimp only
            have hv : ((i.val : ZMod k)).val = i.val := by
              rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.2]
            exact congrArg w (Fin.ext hv)
          right_inv := fun b => by
            ext i
            dsimp only
            rw [ZMod.natCast_zmod_val] }
      refine Fintype.sum_bijective eV eV.bijective _ _ fun w => ?_
      have hlist : (fun i : Fin k => Mbit (w i)) = (fun i : Fin k => Mbit (eV w (i.val : ZMod k))) := by
        ext i
        have hv : ((i.val : ZMod k)).val = i.val := by
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.2]
        have hfin : (⟨((i.val : ZMod k)).val, ZMod.val_lt _⟩ : Fin k) = i := Fin.ext hv
        simp only [eV, Equiv.coe_fn_mk, hfin]
      rw [hlist]
    have hones_tr : Matrix.trace (List.ofFn (fun _ : Fin k => Mbit (1 : ZMod 2))).prod =
        if k % 2 = 1 then 0 else 2 * (2 : ℤ) ^ k := by
      have h1 : Mbit (1 : ZMod 2) = M1 := by simp [Mbit]
      simp only [h1, List.ofFn_const, List.prod_replicate]
      exact trace_M1_pow k
    have hsplit_lhs : ((∑ b : ZMod k → ZMod 2, 2 ^ (PbMat b).rank : ℕ) : ℤ) =
        (∑ b ∈ Finset.univ.erase (fun _ : ZMod k => (1 : ZMod 2)), (2 : ℤ) ^ (PbMat b).rank) +
          (2 : ℤ) ^ (PbMat (fun _ : ZMod k => (1 : ZMod 2))).rank := by
      push_cast
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (fun _ : ZMod k => (1 : ZMod 2)))]
      ring
    have hsplit_rhs : Matrix.trace (A ^ k) =
        (∑ b ∈ Finset.univ.erase (fun _ : ZMod k => (1 : ZMod 2)),
          Matrix.trace (List.ofFn (fun i : Fin k => Mbit (b (i.val : ZMod k)))).prod) +
          Matrix.trace (List.ofFn (fun _ : Fin k => Mbit (1 : ZMod 2))).prod := by
      rw [htr_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (fun _ : ZMod k => (1 : ZMod 2)))]
      ring
    have hproper_sum :
        (∑ b ∈ Finset.univ.erase (fun _ : ZMod k => (1 : ZMod 2)), (2 : ℤ) ^ (PbMat b).rank) =
        ∑ b ∈ Finset.univ.erase (fun _ : ZMod k => (1 : ZMod 2)),
          Matrix.trace (List.ofFn (fun i : Fin k => Mbit (b (i.val : ZMod k)))).prod := by
      refine Finset.sum_congr rfl fun b hb => ?_
      exact PbMat_proper_trace b (Finset.mem_erase.mp hb).1
    dsimp only [total]
    rw [hsplit_lhs, hsplit_rhs, hproper_sum, hones_tr, PbMat_allones_rank]
    by_cases hodd : k % 2 = 1
    · simp only [hodd, ↓reduceIte, add_zero]
    · simp only [hodd, ↓reduceIte]
      have hk2 : 2 ≤ k := by omega
      have hpow : (2 : ℤ) ^ k = 4 * (2 : ℤ) ^ (k - 2) := by
        have : k = (k - 2) + 2 := by omega
        conv_lhs => rw [this, pow_add]
        ring
      rw [hpow]; ring
  have hker_dim : Module.finrank (ZMod 2) (LinearMap.ker (mixZMod (k := k) d)) = h :=
    finrank_ker_mixZMod d
  have hpairs_d_le : (pairs d : ℤ) ≤ total := by
    rw [← hpairs0_total, hpairs_eq d, hpairs0_eq]
    exact_mod_cast Finset.sum_le_sum fun b _ => by
      have hle : ((LinearMap.toMatrix' (mixZMod (k := k) d)) * PbMat b *
          (LinearMap.toMatrix' (mixZMod (k := k) d))).rank ≤ (PbMat b).rank := by
        let T := mixZMod (k := k) d
        have hcomp : ((LinearMap.toMatrix' T) * PbMat b * (LinearMap.toMatrix' T)).mulVecLin =
            T.comp ((PbMat b).mulVecLin.comp T) := by
          apply LinearMap.ext; intro x
          simp only [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, LinearMap.comp_apply]
          have hT : ∀ y, (LinearMap.toMatrix' T).mulVec y = T y := fun y => by
            rw [← Matrix.mulVecLin_apply]; simp
          rw [hT, hT]
        change Module.finrank (ZMod 2) (LinearMap.range _) ≤ Module.finrank (ZMod 2) (LinearMap.range _)
        rw [hcomp]
        exact (rank_sandwich_bounds T (PbMat b).mulVecLin).1
      exact Nat.pow_le_pow_right (by omega) hle
  have htotal_le_d : total ≤ (2 : ℤ) ^ (2 * h) * (pairs d : ℤ) := by
    rw [← hpairs0_total, hpairs_eq d, hpairs0_eq]
    have hnat : (∑ b : ZMod k → ZMod 2, 2 ^ (PbMat b).rank) ≤ 2 ^ (2 * h) * ∑ b : ZMod k → ZMod 2,
        2 ^ ((LinearMap.toMatrix' (mixZMod (k := k) d)) * PbMat b *
          (LinearMap.toMatrix' (mixZMod (k := k) d))).rank := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      rw [← pow_add]
      have hge : (PbMat b).rank ≤
          ((LinearMap.toMatrix' (mixZMod (k := k) d)) * PbMat b *
            (LinearMap.toMatrix' (mixZMod (k := k) d))).rank + 2 * h := by
        let T := mixZMod (k := k) d
        have hcomp : ((LinearMap.toMatrix' T) * PbMat b * (LinearMap.toMatrix' T)).mulVecLin =
            T.comp ((PbMat b).mulVecLin.comp T) := by
          apply LinearMap.ext; intro x
          simp only [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, LinearMap.comp_apply]
          have hT : ∀ y, (LinearMap.toMatrix' T).mulVec y = T y := fun y => by
            rw [← Matrix.mulVecLin_apply]; simp
          rw [hT, hT]
        change Module.finrank (ZMod 2) (LinearMap.range _) ≤ Module.finrank (ZMod 2) (LinearMap.range _) + 2 * h
        rw [hcomp, ← hker_dim]
        exact (rank_sandwich_bounds T (PbMat b).mulVecLin).2
      exact Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast hnat
  have hasymp : (2 : ℤ) ^ k * total ≤ 3 * (7 : ℤ) ^ k := by
    have htr := trace_Amat_bound k
    have hA_eq : A = Amat := rfl
    dsimp only [total]
    rw [hA_eq, mul_add]
    by_cases hodd : k % 2 = 1
    · simp only [hodd, ↓reduceIte]
      have h2k : (2 : ℤ) ^ k * (2 : ℤ) ^ (k - 1) ≤ (7 : ℤ) ^ k := by
        rw [← pow_add]
        have hle1 : (2 : ℤ) ^ (k + (k - 1)) ≤ (2 : ℤ) ^ (2 * k) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hle2 : (2 : ℤ) ^ (2 * k) = (4 : ℤ) ^ k := by
          rw [pow_mul]; norm_num
        have hle3 : (4 : ℤ) ^ k ≤ (7 : ℤ) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
        linarith
      linarith
    · simp only [hodd, ↓reduceIte]
      have hneg : (2 : ℤ) ^ k * (-7 * (2 : ℤ) ^ (k - 2)) ≤ 0 := by
        have h1 : (0 : ℤ) ≤ (2 : ℤ) ^ k := by positivity
        have h2 : (0 : ℤ) ≤ (2 : ℤ) ^ (k - 2) := by positivity
        nlinarith
      have h7nn : (0 : ℤ) ≤ (7 : ℤ) ^ k := by positivity
      linarith
  exact ⟨hpairs0_total, hpairs_d_le, htotal_le_d, hasymp⟩

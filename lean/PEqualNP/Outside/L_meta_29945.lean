import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29945_aux

open Finset

abbrev F := ZMod 2

lemma zmod2_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma zmod2_add_self (a : F) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma zmod2_neg_eq (a : F) : -a = a := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma zmod2_sub_eq_add (a b : F) : a - b = a + b := by
  rw [sub_eq_add_neg, zmod2_neg_eq]

lemma zmod2_eq_iff_add_eq_zero (a b : F) : a = b ↔ a + b = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma zmod2_Pprod (u1 u2 u3 u4 u5 : F) :
    (u1 * u2 + u2 * u3 + u3 * u4) * (u2 * u3 + u3 * u4 + u4 * u5) =
    u2 * u4 * (u1 + u3) * (u3 + u5) +
    (u2 * u3 * u1 + u3 * u4 * u5 + u2 * u3 + u3 * u4 + u2 * u4 * u3) := by
  revert u1 u2 u3 u4 u5
  decide

def diffF {W : Type*} [Add W] (f : W → F) (u x : W) : F :=
  f (x + u) - f x

def fourthF {W : Type*} [Add W] (f : W → F) (v : Fin 4 → W) : W → F :=
  (List.ofFn v).foldl diffF f

def cubicF {W : Type*} [Add W] (f : W → F) : Prop :=
  ∀ v x, fourthF f v x = 0

lemma fourthF_eq {W : Type*} [Add W] (f : W → F) (v : Fin 4 → W) (x : W) :
    fourthF f v x = diffF (diffF (diffF (diffF f (v 0)) (v 1)) (v 2)) (v 3) x := by
  simp only [fourthF, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil]
  rfl

lemma fourthF_add {W : Type*} [Add W] (f g : W → F) (v : Fin 4 → W) (x : W) :
    fourthF (fun y => f y + g y) v x = fourthF f v x + fourthF g v x := by
  simp only [fourthF_eq, diffF]; ring

lemma fourthF_zero {W : Type*} [Add W] (v : Fin 4 → W) (x : W) :
    fourthF (fun _ : W => (0 : F)) v x = 0 := by
  simp only [fourthF_eq, diffF]; ring

lemma cubicF_zero {W : Type*} [Add W] : cubicF (fun _ : W => (0 : F)) :=
  fun v x => fourthF_zero v x

lemma fourthF_affine_prod3 {W : Type*} [AddCommGroup W]
    (a b c : W → F) (La Lb Lc : W → F)
    (ha : ∀ x u, a (x + u) = a x + La u)
    (hb : ∀ x u, b (x + u) = b x + Lb u)
    (hc : ∀ x u, c (x + u) = c x + Lc u)
    (v : Fin 4 → W) (x : W) :
    fourthF (fun y => a y * b y * c y) v x = 0 := by
  simp only [fourthF_eq, diffF, ha, hb, hc]; ring

lemma fourthF_affine_prod2 {W : Type*} [AddCommGroup W]
    (a b : W → F) (La Lb : W → F)
    (ha : ∀ x u, a (x + u) = a x + La u)
    (hb : ∀ x u, b (x + u) = b x + Lb u)
    (v : Fin 4 → W) (x : W) :
    fourthF (fun y => a y * b y) v x = 0 := by
  have h := fourthF_affine_prod3 a b (fun _ => 1) La Lb (fun _ => 0) ha hb
    (fun _ _ => by ring) v x
  simpa only [mul_one] using h

lemma fourthF_affine {W : Type*} [AddCommGroup W]
    (a : W → F) (La : W → F)
    (ha : ∀ x u, a (x + u) = a x + La u)
    (v : Fin 4 → W) (x : W) :
    fourthF a v x = 0 := by
  have h := fourthF_affine_prod2 a (fun _ => 1) La (fun _ => 0) ha
    (fun _ _ => by ring) v x
  simpa only [mul_one] using h

def perm4 (a b c d : Fin 4 → F) : F :=
  a 0 * (b 1 * (c 2 * d 3 + c 3 * d 2) + b 2 * (c 1 * d 3 + c 3 * d 1) + b 3 * (c 1 * d 2 + c 2 * d 1)) +
  a 1 * (b 0 * (c 2 * d 3 + c 3 * d 2) + b 2 * (c 0 * d 3 + c 3 * d 0) + b 3 * (c 0 * d 2 + c 2 * d 0)) +
  a 2 * (b 0 * (c 1 * d 3 + c 3 * d 1) + b 1 * (c 0 * d 3 + c 3 * d 0) + b 3 * (c 0 * d 1 + c 1 * d 0)) +
  a 3 * (b 0 * (c 1 * d 2 + c 2 * d 1) + b 1 * (c 0 * d 2 + c 2 * d 0) + b 2 * (c 0 * d 1 + c 1 * d 0))

lemma fourthF_affine_prod4 {W : Type*} [AddCommGroup W]
    (a b c d : W → F) (La Lb Lc Ld : W → F)
    (ha : ∀ x u, a (x + u) = a x + La u)
    (hb : ∀ x u, b (x + u) = b x + Lb u)
    (hc : ∀ x u, c (x + u) = c x + Lc u)
    (hd : ∀ x u, d (x + u) = d x + Ld u)
    (v : Fin 4 → W) (x : W) :
    fourthF (fun y => a y * b y * c y * d y) v x =
    perm4 (fun m => La (v m)) (fun m => Lb (v m)) (fun m => Lc (v m)) (fun m => Ld (v m)) := by
  simp only [fourthF_eq, diffF, ha, hb, hc, hd, perm4]; ring

lemma det_fin4_eq_perm4 (M : Matrix (Fin 4) (Fin 4) F) :
    M.det = perm4 (fun m => M m 0) (fun m => M m 1) (fun m => M m 2) (fun m => M m 3) := by
  rw [Matrix.det_succ_column_zero]
  simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two,
    show (3 : Fin 4).val = 3 from rfl, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show Fin.succ (2 : Fin 3) = 3 from rfl,
    Fin.succAbove_zero,
    show (1 : Fin 4).succAbove 0 = 0 from rfl,
    show (1 : Fin 4).succAbove 1 = 2 from rfl,
    show (1 : Fin 4).succAbove 2 = 3 from rfl,
    show (2 : Fin 4).succAbove 0 = 0 from rfl,
    show (2 : Fin 4).succAbove 1 = 1 from rfl,
    show (2 : Fin 4).succAbove 2 = 3 from rfl,
    show (3 : Fin 4).succAbove 0 = 0 from rfl,
    show (3 : Fin 4).succAbove 1 = 1 from rfl,
    show (3 : Fin 4).succAbove 2 = 2 from rfl,
    zmod2_sub_eq_add, one_mul, pow_zero, pow_one, zmod2_neg_eq, perm4]
  ring

lemma det_eq_zero_of_mulVec_eq_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (v : Fin n → F) (hv : v ≠ 0) (hMv : M.mulVec v = 0) : M.det = 0 := by
  by_contra hdet
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have h1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hu
  have h2 : v = 0 := by
    calc v = (1 : Matrix (Fin n) (Fin n) F).mulVec v := (Matrix.one_mulVec v).symm
      _ = (M⁻¹ * M).mulVec v := by rw [h1]
      _ = M⁻¹.mulVec (M.mulVec v) := by rw [Matrix.mulVec_mulVec]
      _ = M⁻¹.mulVec 0 := by rw [hMv]
      _ = 0 := Matrix.mulVec_zero _
  exact hv h2

lemma fourthF_comp_affine {W : Type*} [AddCommGroup W] [Module F W] (f : W → F)
    (π : W →ₗ[F] W) (x0 : W) (v : Fin 4 → W) (x : W) :
    fourthF (fun y => f (x0 + π (y - x0))) v x =
    fourthF f (fun m => π (v m)) (x0 + π (x - x0)) := by
  have hstep : ∀ (y u : W), x0 + π (y + u - x0) = (x0 + π (y - x0)) + π u := by
    intro y u
    have hsub : y + u - x0 = (y - x0) + u := by abel
    rw [hsub, map_add, add_assoc]
  simp only [fourthF_eq, diffF, hstep]

section IndexArith

variable (k : ℕ) (hk : 0 < k)

def ix (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

lemma ix_val (n : ℕ) : (ix k hk n).val = n % k := rfl

lemma ix_self (i : Fin k) : ix k hk i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

lemma ix_add_left (n m : ℕ) : ix k hk ((ix k hk n).val + m) = ix k hk (n + m) := by
  apply Fin.ext
  simp only [ix_val, Nat.mod_add_mod]

lemma ix_add_k (n : ℕ) : ix k hk (n + k) = ix k hk n := by
  apply Fin.ext
  simp only [ix_val, Nat.add_mod_right]

lemma ix_add_k_sub (n s : ℕ) (hs : s ≤ k) :
    ix k hk ((ix k hk n).val + k - s) = ix k hk (n + k - s) := by
  apply Fin.ext
  simp only [ix_val]
  have h1 : n % k + k - s = n % k + (k - s) := by omega
  have h2 : n + k - s = n + (k - s) := by omega
  rw [h1, h2, Nat.mod_add_mod]

lemma ix_add_sub_cancel (n a : ℕ) (ha : a ≤ k) :
    ix k hk ((ix k hk (n + a)).val + k - a) = ix k hk n := by
  rw [ix_add_k_sub k hk (n + a) a ha]
  have h1 : n + a + k - a = n + k := by omega
  rw [h1, ix_add_k]

lemma ix_sub_add_cancel (n a : ℕ) (ha : a ≤ k) :
    ix k hk ((ix k hk (n + k - a)).val + a) = ix k hk n := by
  rw [ix_add_left]
  have h1 : n + k - a + a = n + k := by omega
  rw [h1, ix_add_k]

def shiftEquiv (s : ℕ) : Fin k ≃ Fin k where
  toFun i := ix k hk (i.val + s)
  invFun i := ix k hk (i.val + k - s % k)
  left_inv i := by
    dsimp only
    have hs : s % k ≤ k := le_of_lt (Nat.mod_lt s hk)
    rw [ix_add_k_sub k hk (i.val + s) (s % k) hs]
    apply Fin.ext
    simp only [ix_val]
    have h1 : i.val + s + k - s % k = i.val + (s - s % k) + k := by
      have := Nat.mod_le s k; omega
    rw [h1, Nat.add_mod_right]
    have h2 : s - s % k = k * (s / k) := by
      have := Nat.div_add_mod s k; omega
    rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
  right_inv i := by
    dsimp only
    rw [ix_add_left]
    apply Fin.ext
    simp only [ix_val]
    have h1 : i.val + k - s % k + s = i.val + k + (s - s % k) := by
      have := Nat.mod_le s k
      have := Nat.mod_lt s hk
      omega
    rw [h1]
    have h2 : s - s % k = k * (s / k) := by
      have := Nat.div_add_mod s k; omega
    rw [h2, Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

end IndexArith

section MainProof

variable (k : ℕ) (hk : 0 < k)

abbrev W (k : ℕ) := Fin k → F

def dot (a x : W k) : F := ∑ i : Fin k, a i * x i

def dotLM (a : W k) : W k →ₗ[F] F where
  toFun := dot k a
  map_add' x y := by
    simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

lemma dot_single (a : W k) (t : Fin k) : dot k a (Pi.single t 1) = a t := by
  simp only [dot]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ t) h

lemma eq_zero_of_dot_eq_zero (a : W k) (h : ∀ x, dot k a x = 0) : a = 0 := by
  funext t
  have := h (Pi.single t 1)
  rwa [dot_single] at this

def rotF (s : ℕ) (x : W k) (i : Fin k) : F :=
  x (ix k hk (i.val + k - s % k))

def mixF (g : ℕ) (x : W k) (i : Fin k) : F :=
  x i + x (ix k hk (i.val + g)) + x (ix k hk (i.val + k - g % k))

def stepF (x : W k) (i : Fin k) : F :=
  x i + (1 + x (ix k hk (i.val + 1))) * x (ix k hk (i.val + 2))

def outFalse (name c₁ c₂ : Bool → W k) (x : W k) : W k :=
  let z := mixF k hk 1 (rotF k hk 1 x + name false)
  let y := stepF k hk z + rotF k hk 0 x + c₁ false
  stepF k hk (mixF k hk 1 y) + rotF k hk 2 x + c₂ false

def Lmap (x : W k) : W k := mixF k hk 1 (rotF k hk 1 x)

lemma Lmap_apply (hk9 : 9 ≤ k) (x : W k) (i : Fin k) :
    Lmap k hk x i =
      x (ix k hk (i.val + k - 1)) + x i + x (ix k hk (i.val + k - 2)) := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  simp only [Lmap, mixF, rotF, h1]
  have ha : ix k hk ((ix k hk (i.val + 1)).val + k - 1) = i := by
    rw [ix_add_sub_cancel k hk i.val 1 (by omega), ix_self]
  have hb : ix k hk ((ix k hk (i.val + k - 1)).val + k - 1) = ix k hk (i.val + k - 2) := by
    rw [ix_add_k_sub k hk (i.val + k - 1) 1 (by omega)]
    apply Fin.ext
    simp only [ix_val]
    have h2 : i.val + k - 1 + k - 1 = i.val + k - 2 + k := by omega
    rw [h2, Nat.add_mod_right]
  rw [ha, hb]

def Llm (hk9 : 9 ≤ k) : W k →ₗ[F] W k where
  toFun := Lmap k hk
  map_add' x y := by
    funext i
    simp only [Lmap_apply k hk hk9, Pi.add_apply]; ring
  map_smul' c x := by
    funext i
    simp only [Lmap_apply k hk hk9, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def Lstar (r : W k) (j : Fin k) : F :=
  r j + r (ix k hk (j.val + 1)) + r (ix k hk (j.val + 2))

def LstarLM : W k →ₗ[F] W k where
  toFun := Lstar k hk
  map_add' r s := by
    funext j
    simp only [Lstar, Pi.add_apply]; ring
  map_smul' c r := by
    funext j
    simp only [Lstar, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma dot_Lmap (hk9 : 9 ≤ k) (r x : W k) : dot k r (Lmap k hk x) = dot k (Lstar k hk r) x := by
  simp only [dot, Lmap_apply k hk hk9, Lstar, mul_add, add_mul, Finset.sum_add_distrib]
  have h1 : ∑ i : Fin k, r i * x (ix k hk (i.val + k - 1)) =
      ∑ j : Fin k, r (ix k hk (j.val + 1)) * x j := by
    refine Fintype.sum_equiv (shiftEquiv k hk 1).symm _ _ (fun i => ?_)
    have hmod : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have hinv : (shiftEquiv k hk 1).symm i = ix k hk (i.val + k - 1) := by
      simp only [shiftEquiv, Equiv.coe_fn_symm_mk, hmod]
    rw [hinv, ix_sub_add_cancel k hk i.val 1 (by omega), ix_self]
  have h2 : ∑ i : Fin k, r i * x (ix k hk (i.val + k - 2)) =
      ∑ j : Fin k, r (ix k hk (j.val + 2)) * x j := by
    refine Fintype.sum_equiv (shiftEquiv k hk 2).symm _ _ (fun i => ?_)
    have hmod : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
    have hinv : (shiftEquiv k hk 2).symm i = ix k hk (i.val + k - 2) := by
      simp only [shiftEquiv, Equiv.coe_fn_symm_mk, hmod]
    rw [hinv, ix_sub_add_cancel k hk i.val 2 (by omega), ix_self]
  rw [h1, h2]
  ring

def phiAt (i : Fin k) : W k →ₗ[F] (Fin 4 → F) where
  toFun z := ![z (ix k hk (i.val + 2)), z (ix k hk (i.val + 4)),
    z (ix k hk (i.val + 1)) + z (ix k hk (i.val + 3)),
    z (ix k hk (i.val + 3)) + z (ix k hk (i.val + 5))]
  map_add' x y := by
    funext j; fin_cases j <;> simp [Pi.add_apply] <;> ring
  map_smul' c x := by
    funext j; fin_cases j <;> simp [Pi.smul_apply, smul_eq_mul] <;> ring

def psiAt (hk9 : 9 ≤ k) (i : Fin k) : W k →ₗ[F] (Fin 4 → F) :=
  (phiAt k hk i).comp (Llm k hk hk9)

lemma fourth_outFalse (hk9 : 9 ≤ k) (name c₁ c₂ : Bool → W k) (i : Fin k) (v : Fin 4 → W k) (x : W k) :
    fourthF (fun y => outFalse k hk name c₁ c₂ y i) v x =
    Matrix.det (fun m : Fin 4 => psiAt k hk hk9 i (v m)) := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  let c0 : W k := mixF k hk 1 (name false)
  let Z : W k → W k := fun y => Lmap k hk y + c0
  have hZ_eq : ∀ y, mixF k hk 1 (rotF k hk 1 y + name false) = Z y := by
    intro y; funext j
    simp only [Z, Lmap, mixF, Pi.add_apply, c0]; ring
  have hZ_aff : ∀ j (y u : W k), Z (y + u) j = Z y j + Lmap k hk u j := by
    intro j y u
    have hL : Lmap k hk (y + u) j = Lmap k hk y j + Lmap k hk u j :=
      congrFun ((Llm k hk hk9).map_add y u) j
    simp only [Z, Pi.add_apply, hL]; ring
  let q : W k → W k := fun y j => Z y (ix k hk (j.val + 1)) * Z y (ix k hk (j.val + 2))
  let A : W k → W k := fun y j => Z y j + Z y (ix k hk (j.val + 2)) + rotF k hk 0 y j + c₁ false j
  let LA : W k → W k := fun u j => Lmap k hk u j + Lmap k hk u (ix k hk (j.val + 2)) + rotF k hk 0 u j
  have hA_aff : ∀ j (y u : W k), A (y + u) j = A y j + LA u j := by
    intro j y u
    simp only [A, LA, hZ_aff, rotF, Pi.add_apply]; ring
  have hy_eq : ∀ y j, (stepF k hk (Z y) + rotF k hk 0 y + c₁ false) j = q y j + A y j := by
    intro y j
    simp only [stepF, q, A, Pi.add_apply]; ring
  let P : W k → W k := fun y j => mixF k hk 1 (q y) j
  let B : W k → W k := fun y j => mixF k hk 1 (A y) j
  let LB : W k → W k := fun u j => mixF k hk 1 (LA u) j
  have hB_aff : ∀ j (y u : W k), B (y + u) j = B y j + LB u j := by
    intro j y u
    simp only [B, LB, mixF, hA_aff]; ring
  have hW_eq : ∀ y j, mixF k hk 1 (stepF k hk (Z y) + rotF k hk 0 y + c₁ false) j = P y j + B y j := by
    intro y j
    simp only [mixF, hy_eq, P, B]; ring
  have hP1 : ∀ y, P y (ix k hk (i.val + 1)) =
      Z y (ix k hk (i.val + 1)) * Z y (ix k hk (i.val + 2)) +
      Z y (ix k hk (i.val + 2)) * Z y (ix k hk (i.val + 3)) +
      Z y (ix k hk (i.val + 3)) * Z y (ix k hk (i.val + 4)) := by
    intro y
    simp only [P, mixF, h1]
    rw [ix_add_left, ix_add_sub_cancel k hk i.val 1 (by omega), ix_self]
    simp only [q, ix_add_left]
    have h11 : i.val + 1 + 1 = i.val + 2 := by omega
    have h12 : i.val + 1 + 2 = i.val + 3 := by omega
    have h21 : i.val + 2 + 1 = i.val + 3 := by omega
    have h22 : i.val + 2 + 2 = i.val + 4 := by omega
    rw [h11, h12, h21, h22]; ring
  have hP2 : ∀ y, P y (ix k hk (i.val + 2)) =
      Z y (ix k hk (i.val + 2)) * Z y (ix k hk (i.val + 3)) +
      Z y (ix k hk (i.val + 3)) * Z y (ix k hk (i.val + 4)) +
      Z y (ix k hk (i.val + 4)) * Z y (ix k hk (i.val + 5)) := by
    intro y
    simp only [P, mixF, h1]
    have hs : ix k hk ((ix k hk (i.val + 2)).val + k - 1) = ix k hk (i.val + 1) := by
      rw [ix_add_k_sub k hk (i.val + 2) 1 (by omega)]
      have : i.val + 2 + k - 1 = i.val + 1 + k := by omega
      rw [this, ix_add_k]
    rw [ix_add_left, hs]
    simp only [q, ix_add_left]
    have h21 : i.val + 2 + 1 = i.val + 3 := by omega
    have h22 : i.val + 2 + 2 = i.val + 4 := by omega
    have h31 : i.val + 3 + 1 = i.val + 4 := by omega
    have h32 : i.val + 3 + 2 = i.val + 5 := by omega
    have h11 : i.val + 1 + 1 = i.val + 2 := by omega
    have h12 : i.val + 1 + 2 = i.val + 3 := by omega
    rw [h21, h22, h31, h32, h11, h12]; ring
  let z1 : W k → F := fun y => Z y (ix k hk (i.val + 1))
  let z2 : W k → F := fun y => Z y (ix k hk (i.val + 2))
  let z3 : W k → F := fun y => Z y (ix k hk (i.val + 3))
  let z4 : W k → F := fun y => Z y (ix k hk (i.val + 4))
  let z5 : W k → F := fun y => Z y (ix k hk (i.val + 5))
  let L1 : W k → F := fun u => Lmap k hk u (ix k hk (i.val + 1))
  let L2 : W k → F := fun u => Lmap k hk u (ix k hk (i.val + 2))
  let L3 : W k → F := fun u => Lmap k hk u (ix k hk (i.val + 3))
  let L4 : W k → F := fun u => Lmap k hk u (ix k hk (i.val + 4))
  let L5 : W k → F := fun u => Lmap k hk u (ix k hk (i.val + 5))
  have hPprod : ∀ y, P y (ix k hk (i.val + 1)) * P y (ix k hk (i.val + 2)) =
      z2 y * z4 y * (z1 y + z3 y) * (z3 y + z5 y) +
      (z2 y * z3 y * z1 y + z3 y * z4 y * z5 y +
       z2 y * z3 y + z3 y * z4 y + z2 y * z4 y * z3 y) := by
    intro y
    rw [hP1 y, hP2 y]
    exact zmod2_Pprod (z1 y) (z2 y) (z3 y) (z4 y) (z5 y)
  have hPi_zero : fourthF (fun y => P y i) v x = 0 := by
    have hPdef : (fun y => P y i) =
        fun y => q y i + q y (ix k hk (i.val + 1)) + q y (ix k hk (i.val + k - 1)) := by
      funext y; simp only [P, mixF, h1]
    rw [hPdef, fourthF_add, fourthF_add]
    have hq0 : ∀ j, fourthF (fun y => q y j) v x = 0 := fun j =>
      fourthF_affine_prod2 _ _ _ _ (hZ_aff _) (hZ_aff _) v x
    rw [hq0, hq0, hq0]; ring
  let main4 : W k → F := fun y => z2 y * z4 y * (z1 y + z3 y) * (z3 y + z5 y)
  let rem1 : W k → F := fun y =>
    z2 y * z3 y * z1 y + z3 y * z4 y * z5 y +
    z2 y * z3 y + z3 y * z4 y + z2 y * z4 y * z3 y + P y i
  let rem2 : W k → F := fun y =>
    (1 + B y (ix k hk (i.val + 1))) * z2 y * z3 y +
    (1 + B y (ix k hk (i.val + 1))) * z3 y * z4 y +
    (1 + B y (ix k hk (i.val + 1))) * z4 y * z5 y
  let rem3 : W k → F := fun y =>
    B y (ix k hk (i.val + 2)) * z1 y * z2 y +
    B y (ix k hk (i.val + 2)) * z2 y * z3 y +
    B y (ix k hk (i.val + 2)) * z3 y * z4 y +
    (1 + B y (ix k hk (i.val + 1))) * B y (ix k hk (i.val + 2)) +
    (B y i + rotF k hk 2 y i + c₂ false i)
  have hfun_eq : (fun y => outFalse k hk name c₁ c₂ y i) =
      fun y => main4 y + rem1 y + rem2 y + rem3 y := by
    funext y
    simp only [outFalse, hZ_eq, Pi.add_apply, stepF, hW_eq, main4, rem1, rem2, rem3]
    have hsplit : (1 + (P y (ix k hk (i.val + 1)) + B y (ix k hk (i.val + 1)))) *
        (P y (ix k hk (i.val + 2)) + B y (ix k hk (i.val + 2))) =
        P y (ix k hk (i.val + 1)) * P y (ix k hk (i.val + 2)) +
        (1 + B y (ix k hk (i.val + 1))) * P y (ix k hk (i.val + 2)) +
        B y (ix k hk (i.val + 2)) * P y (ix k hk (i.val + 1)) +
        (1 + B y (ix k hk (i.val + 1))) * B y (ix k hk (i.val + 2)) := by ring
    rw [hsplit, hPprod y, hP1 y, hP2 y]
    change P y i + B y i + _ + rotF k hk 2 y i + c₂ false i = _
    ring
  have hB1 : ∀ y u, (1 + B (y + u) (ix k hk (i.val + 1))) =
      (1 + B y (ix k hk (i.val + 1))) + LB u (ix k hk (i.val + 1)) := by
    intro y u; rw [hB_aff]; ring
  have hrem1 : fourthF rem1 v x = 0 := by
    simp only [rem1, fourthF_add]
    rw [fourthF_affine_prod3 z2 z3 z1 L2 L3 L1 (hZ_aff _) (hZ_aff _) (hZ_aff _),
        fourthF_affine_prod3 z3 z4 z5 L3 L4 L5 (hZ_aff _) (hZ_aff _) (hZ_aff _),
        fourthF_affine_prod2 z2 z3 L2 L3 (hZ_aff _) (hZ_aff _),
        fourthF_affine_prod2 z3 z4 L3 L4 (hZ_aff _) (hZ_aff _),
        fourthF_affine_prod3 z2 z4 z3 L2 L4 L3 (hZ_aff _) (hZ_aff _) (hZ_aff _),
        hPi_zero]
    ring
  have hrem2 : fourthF rem2 v x = 0 := by
    simp only [rem2, fourthF_add]
    rw [fourthF_affine_prod3 _ z2 z3 _ L2 L3 hB1 (hZ_aff _) (hZ_aff _),
        fourthF_affine_prod3 _ z3 z4 _ L3 L4 hB1 (hZ_aff _) (hZ_aff _),
        fourthF_affine_prod3 _ z4 z5 _ L4 L5 hB1 (hZ_aff _) (hZ_aff _)]
    ring
  have hrem3 : fourthF rem3 v x = 0 := by
    simp only [rem3, fourthF_add]
    rw [fourthF_affine_prod3 _ z1 z2 _ L1 L2 (hB_aff _) (hZ_aff _) (hZ_aff _),
        fourthF_affine_prod3 _ z2 z3 _ L2 L3 (hB_aff _) (hZ_aff _) (hZ_aff _),
        fourthF_affine_prod3 _ z3 z4 _ L3 L4 (hB_aff _) (hZ_aff _) (hZ_aff _),
        fourthF_affine_prod2 _ _ _ _ hB1 (hB_aff _),
        fourthF_affine _ _ (hB_aff i),
        fourthF_affine (fun y => rotF k hk 2 y i) (fun u => rotF k hk 2 u i)
          (fun y u => by simp [rotF]),
        fourthF_affine (fun _ => c₂ false i) (fun _ => 0) (fun _ _ => by ring)]
    ring
  have hmain : fourthF main4 v x = Matrix.det (fun m : Fin 4 => psiAt k hk hk9 i (v m)) := by
    have h13 : ∀ y u, (z1 (y + u) + z3 (y + u)) = (z1 y + z3 y) + (L1 u + L3 u) := by
      intro y u; simp only [z1, z3, L1, L3, hZ_aff]; ring
    have h35 : ∀ y u, (z3 (y + u) + z5 (y + u)) = (z3 y + z5 y) + (L3 u + L5 u) := by
      intro y u; simp only [z3, z5, L3, L5, hZ_aff]; ring
    simp only [main4]
    rw [fourthF_affine_prod4 z2 z4 (fun y => z1 y + z3 y) (fun y => z3 y + z5 y)
      L2 L4 (fun u => L1 u + L3 u) (fun u => L3 u + L5 u)
      (hZ_aff _) (hZ_aff _) h13 h35]
    rw [det_fin4_eq_perm4 (fun m : Fin 4 => psiAt k hk hk9 i (v m))]
    simp only [psiAt, phiAt, Llm, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      show ∀ (a b c d : F), ![a, b, c, d] (0 : Fin 4) = a from fun _ _ _ _ => rfl,
      show ∀ (a b c d : F), ![a, b, c, d] (1 : Fin 4) = b from fun _ _ _ _ => rfl,
      show ∀ (a b c d : F), ![a, b, c, d] (2 : Fin 4) = c from fun _ _ _ _ => rfl,
      show ∀ (a b c d : F), ![a, b, c, d] (3 : Fin 4) = d from fun _ _ _ _ => rfl]
    rfl
  rw [hfun_eq, fourthF_add, fourthF_add, fourthF_add, hmain, hrem1, hrem2, hrem3]
  ring

def tapSet (i : Fin k) : Finset (Fin k) :=
  (Finset.range 5).image (fun j => ix k hk (i.val + j + 1))

lemma mem_tapSet_iff (i t : Fin k) :
    t ∈ tapSet k hk i ↔ ∃ j < 5, t = ix k hk (i.val + j + 1) := by
  simp only [tapSet, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

lemma tap_slot_inj (hk9 : 9 ≤ k) (i : Fin k) {a b : ℕ} (ha : a < 5) (hb : b < 5)
    (heq : ix k hk (i.val + a + 1) = ix k hk (i.val + b + 1)) : a = b := by
  have hmod : (i.val + a + 1) % k = (i.val + b + 1) % k := congrArg Fin.val heq
  have hi := i.isLt
  by_cases h1 : i.val + a + 1 < k <;> by_cases h2 : i.val + b + 1 < k
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod; omega
  · have hlt : i.val + b + 1 - k < k := by omega
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt] at hmod
    omega
  · have hlt : i.val + a + 1 - k < k := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt h2] at hmod
    omega
  · have hlta : i.val + a + 1 - k < k := by omega
    have hltb : i.val + b + 1 - k < k := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlta,
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hltb] at hmod
    omega

def isKilling (i : Fin k) (r : W k) : Prop :=
  r ≠ 0 ∧ (∀ t, t ∉ tapSet k hk i → r t = 0) ∧
  r (ix k hk (i.val + 1)) + r (ix k hk (i.val + 3)) + r (ix k hk (i.val + 5)) = 0

lemma dot_eq_sum_tap (hk9 : 9 ≤ k) (i : Fin k) (r z : W k)
    (hsupp : ∀ t, t ∉ tapSet k hk i → r t = 0) :
    dot k r z =
      r (ix k hk (i.val + 1)) * z (ix k hk (i.val + 1)) +
      r (ix k hk (i.val + 2)) * z (ix k hk (i.val + 2)) +
      r (ix k hk (i.val + 3)) * z (ix k hk (i.val + 3)) +
      r (ix k hk (i.val + 4)) * z (ix k hk (i.val + 4)) +
      r (ix k hk (i.val + 5)) * z (ix k hk (i.val + 5)) := by
  simp only [dot]
  rw [← Finset.sum_subset (Finset.subset_univ (tapSet k hk i))]
  · unfold tapSet
    rw [Finset.sum_image]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    · intro a ha b hb heq
      exact tap_slot_inj k hk hk9 i (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) heq
  · intro t _ ht
    rw [hsupp t ht, zero_mul]

lemma killing_forward (hk9 : 9 ≤ k) (i : Fin k) (r : W k) (hr : isKilling k hk i r)
    (v : Fin 4 → W k) (hv : ∀ m, dot k (Lstar k hk r) (v m) = 0) :
    Matrix.det (fun m : Fin 4 => psiAt k hk hk9 i (v m)) = 0 := by
  rcases hr with ⟨hrne, hsupp, hpar⟩
  let β : Fin 4 → F := ![r (ix k hk (i.val + 2)), r (ix k hk (i.val + 4)),
    r (ix k hk (i.val + 1)), r (ix k hk (i.val + 5))]
  have hβne : β ≠ 0 := by
    intro hβ0
    apply hrne
    funext t
    by_cases ht : t ∈ tapSet k hk i
    · rcases (mem_tapSet_iff k hk i t).mp ht with ⟨j, hj, rfl⟩
      have h0 : r (ix k hk (i.val + 2)) = 0 := congrFun hβ0 0
      have h1 : r (ix k hk (i.val + 4)) = 0 := congrFun hβ0 1
      have h2 : r (ix k hk (i.val + 1)) = 0 := congrFun hβ0 2
      have h3 : r (ix k hk (i.val + 5)) = 0 := congrFun hβ0 3
      have h4 : r (ix k hk (i.val + 3)) = 0 := by
        rw [h2, h3, zero_add, add_zero] at hpar; exact hpar
      interval_cases j <;> assumption
    · exact hsupp t ht
  apply det_eq_zero_of_mulVec_eq_zero _ β hβne
  funext m
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.zero_apply]
  have hdot : dot k r (Lmap k hk (v m)) = 0 := by
    rw [dot_Lmap k hk hk9]; exact hv m
  rw [dot_eq_sum_tap k hk hk9 i r (Lmap k hk (v m)) hsupp] at hdot
  have hr3 : r (ix k hk (i.val + 3)) =
      r (ix k hk (i.val + 1)) + r (ix k hk (i.val + 5)) := by
    rw [zmod2_eq_iff_add_eq_zero]
    linear_combination hpar
  simp only [psiAt, phiAt, Llm, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, β,
    show ∀ (a b c d : F), ![a, b, c, d] (0 : Fin 4) = a from fun _ _ _ _ => rfl,
    show ∀ (a b c d : F), ![a, b, c, d] (1 : Fin 4) = b from fun _ _ _ _ => rfl,
    show ∀ (a b c d : F), ![a, b, c, d] (2 : Fin 4) = c from fun _ _ _ _ => rfl,
    show ∀ (a b c d : F), ![a, b, c, d] (3 : Fin 4) = d from fun _ _ _ _ => rfl]
  rw [hr3] at hdot
  linear_combination hdot

lemma exists_nonzero_functional_of_lt_top {n : ℕ} (S : Submodule F (Fin n → F)) (hS : S < ⊤) :
    ∃ β : Fin n → F, β ≠ 0 ∧ ∀ w ∈ S, ∑ j : Fin n, β j * w j = 0 := by
  obtain ⟨T, hST⟩ := Submodule.exists_isCompl S
  have hTne : T ≠ ⊥ := by
    intro hTbot
    rw [hTbot] at hST
    exact ne_of_lt hS (eq_top_of_isCompl_bot hST)
  obtain ⟨t0, ht0T, ht0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTne
  let e : (S × T) ≃ₗ[F] (Fin n → F) := LinearEquiv.ofBijective
    (S.subtype.coprod T.subtype)
    ⟨by
      intro ⟨s1, t1⟩ ⟨s2, t2⟩ h
      simp only [LinearMap.coprod_apply, Submodule.coe_subtype] at h
      have hs : (s1 : Fin n → F) - s2 = (t2 : Fin n → F) - t1 := by
        calc (s1 : Fin n → F) - s2 = (s1 + t1) - (s2 + t2) + (t2 - t1) := by abel
          _ = t2 - t1 := by rw [h, sub_self, zero_add]
      have hmem : (s1 : Fin n → F) - s2 ∈ S ⊓ T := by
        refine ⟨S.sub_mem s1.2 s2.2, ?_⟩
        rw [hs]; exact T.sub_mem t2.2 t1.2
      rw [hST.inf_eq_bot, Submodule.mem_bot] at hmem
      have hseq : s1 = s2 := Subtype.ext (sub_eq_zero.mp hmem)
      have hteq : t1 = t2 := Subtype.ext (sub_eq_zero.mp (by rw [← hs, hmem])).symm
      exact Prod.ext hseq hteq,
     by
      intro w
      have hmem : w ∈ S ⊔ T := by rw [hST.sup_eq_top]; exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hmem with ⟨s, hs, t, ht, rfl⟩
      exact ⟨(⟨s, hs⟩, ⟨t, ht⟩), rfl⟩⟩
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin n, t0 j0 ≠ 0 := by
    by_contra h
    push Not at h
    exact ht0ne (funext h)
  let ev : T →ₗ[F] F := (LinearMap.proj j0).comp T.subtype
  let f : (Fin n → F) →ₗ[F] F := (ev.comp (LinearMap.snd F S T)).comp e.symm.toLinearMap
  let β : Fin n → F := fun j => f (Pi.single j 1)
  have hf_eq : ∀ w : Fin n → F, f w = ∑ j : Fin n, β j * w j := by
    intro w
    have hw : w = ∑ j : Fin n, w j • Pi.single j (1 : F) := by
      funext l; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hw]
    simp only [map_sum, map_smul, smul_eq_mul, β]
    refine Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  refine ⟨β, ?_, ?_⟩
  · intro hβ0
    have hft0 : f t0 = 0 := by rw [hf_eq, hβ0]; simp
    have heinv : e.symm t0 = (0, ⟨t0, ht0T⟩) := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      change t0 = (S.subtype.coprod T.subtype) (0, ⟨t0, ht0T⟩)
      simp
    have hft0' : f t0 = t0 j0 := by
      simp [f, heinv, ev]
    rw [hft0'] at hft0
    exact hj0 hft0
  · intro w hw
    rw [← hf_eq]
    have heinv : e.symm w = (⟨w, hw⟩, 0) := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      change w = (S.subtype.coprod T.subtype) (⟨w, hw⟩, 0)
      simp
    simp [f, heinv]

lemma killing_converse (hk9 : 9 ≤ k) (i : Fin k) (K : Submodule F (W k))
    (hK : ∀ v : Fin 4 → W k, (∀ m, v m ∈ K) →
      Matrix.det (fun m : Fin 4 => psiAt k hk hk9 i (v m)) = 0) :
    ∃ r : W k, isKilling k hk i r ∧ ∀ x ∈ K, dot k (Lstar k hk r) x = 0 := by
  have hlt : Submodule.map (psiAt k hk hk9 i) K < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hex : ∀ m : Fin 4, ∃ x ∈ K, psiAt k hk hk9 i x = Pi.single m (1 : F) := by
      intro m
      have hmem : Pi.single m (1 : F) ∈ Submodule.map (psiAt k hk hk9 i) K := by
        rw [htop]; exact Submodule.mem_top
      exact Submodule.mem_map.mp hmem
    choose v hvK hvψ using hex
    have hdet := hK v hvK
    have hM : (fun m : Fin 4 => psiAt k hk hk9 i (v m)) = (1 : Matrix (Fin 4) (Fin 4) F) := by
      ext m j
      rw [hvψ m, Matrix.one_apply, Pi.single_apply]
      by_cases hmj : m = j
      · subst hmj; simp
      · simp [hmj, Ne.symm hmj]
    rw [hM, Matrix.det_one] at hdet
    exact one_ne_zero hdet
  obtain ⟨β, hβne, hβ0⟩ := exists_nonzero_functional_of_lt_top _ hlt
  let r : W k :=
    β 2 • Pi.single (ix k hk (i.val + 1)) 1 +
    β 0 • Pi.single (ix k hk (i.val + 2)) 1 +
    (β 2 + β 3) • Pi.single (ix k hk (i.val + 3)) 1 +
    β 1 • Pi.single (ix k hk (i.val + 4)) 1 +
    β 3 • Pi.single (ix k hk (i.val + 5)) 1
  have hne : ∀ a b : ℕ, a < 5 → b < 5 → a ≠ b →
      ix k hk (i.val + a + 1) ≠ ix k hk (i.val + b + 1) := by
    intro a b ha hb hab heq
    exact hab (tap_slot_inj k hk hk9 i ha hb heq)
  have hr1 : r (ix k hk (i.val + 1)) = β 2 := by
    have h12 := hne 0 1 (by omega) (by omega) (by omega)
    have h13 := hne 0 2 (by omega) (by omega) (by omega)
    have h14 := hne 0 3 (by omega) (by omega) (by omega)
    have h15 := hne 0 4 (by omega) (by omega) (by omega)
    simp only [r, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, Pi.single_eq_of_ne h12, Pi.single_eq_of_ne h13,
      Pi.single_eq_of_ne h14, Pi.single_eq_of_ne h15]
    ring
  have hr2 : r (ix k hk (i.val + 2)) = β 0 := by
    have h21 := hne 1 0 (by omega) (by omega) (by omega)
    have h23 := hne 1 2 (by omega) (by omega) (by omega)
    have h24 := hne 1 3 (by omega) (by omega) (by omega)
    have h25 := hne 1 4 (by omega) (by omega) (by omega)
    simp only [r, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, Pi.single_eq_of_ne h21, Pi.single_eq_of_ne h23,
      Pi.single_eq_of_ne h24, Pi.single_eq_of_ne h25]
    ring
  have hr3 : r (ix k hk (i.val + 3)) = β 2 + β 3 := by
    have h31 := hne 2 0 (by omega) (by omega) (by omega)
    have h32 := hne 2 1 (by omega) (by omega) (by omega)
    have h34 := hne 2 3 (by omega) (by omega) (by omega)
    have h35 := hne 2 4 (by omega) (by omega) (by omega)
    simp only [r, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, Pi.single_eq_of_ne h31, Pi.single_eq_of_ne h32,
      Pi.single_eq_of_ne h34, Pi.single_eq_of_ne h35]
    ring
  have hr4 : r (ix k hk (i.val + 4)) = β 1 := by
    have h41 := hne 3 0 (by omega) (by omega) (by omega)
    have h42 := hne 3 1 (by omega) (by omega) (by omega)
    have h43 := hne 3 2 (by omega) (by omega) (by omega)
    have h45 := hne 3 4 (by omega) (by omega) (by omega)
    simp only [r, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, Pi.single_eq_of_ne h41, Pi.single_eq_of_ne h42,
      Pi.single_eq_of_ne h43, Pi.single_eq_of_ne h45]
    ring
  have hr5 : r (ix k hk (i.val + 5)) = β 3 := by
    have h51 := hne 4 0 (by omega) (by omega) (by omega)
    have h52 := hne 4 1 (by omega) (by omega) (by omega)
    have h53 := hne 4 2 (by omega) (by omega) (by omega)
    have h54 := hne 4 3 (by omega) (by omega) (by omega)
    simp only [r, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, Pi.single_eq_of_ne h51, Pi.single_eq_of_ne h52,
      Pi.single_eq_of_ne h53, Pi.single_eq_of_ne h54]
    ring
  have hsupp : ∀ t, t ∉ tapSet k hk i → r t = 0 := by
    intro t ht
    have hnt : ∀ j < 5, t ≠ ix k hk (i.val + j + 1) := by
      intro j hj heq; exact ht ((mem_tapSet_iff k hk i t).mpr ⟨j, hj, heq⟩)
    simp only [r, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne (hnt 0 (by omega)),
      Pi.single_eq_of_ne (hnt 1 (by omega)),
      Pi.single_eq_of_ne (hnt 2 (by omega)),
      Pi.single_eq_of_ne (hnt 3 (by omega)),
      Pi.single_eq_of_ne (hnt 4 (by omega))]
    ring
  refine ⟨r, ⟨?_, hsupp, ?_⟩, ?_⟩
  · intro hr0
    apply hβne
    funext j; fin_cases j
    · simpa [hr2] using congrFun hr0 (ix k hk (i.val + 2))
    · simpa [hr4] using congrFun hr0 (ix k hk (i.val + 4))
    · simpa [hr1] using congrFun hr0 (ix k hk (i.val + 1))
    · simpa [hr5] using congrFun hr0 (ix k hk (i.val + 5))
  · rw [hr1, hr3, hr5]
    have h1 := zmod2_add_self (β 2)
    have h2 := zmod2_add_self (β 3)
    linear_combination h1 + h2
  · intro x hx
    rw [← dot_Lmap k hk hk9, dot_eq_sum_tap k hk hk9 i r (Lmap k hk x) hsupp,
      hr1, hr2, hr3, hr4, hr5]
    have h0 := hβ0 (psiAt k hk hk9 i x) (Submodule.mem_map_of_mem hx)
    simp only [Fin.sum_univ_four, psiAt, phiAt, Llm, LinearMap.comp_apply,
      LinearMap.coe_mk, AddHom.coe_mk,
      show ∀ (a b c d : F), ![a, b, c, d] (0 : Fin 4) = a from fun _ _ _ _ => rfl,
      show ∀ (a b c d : F), ![a, b, c, d] (1 : Fin 4) = b from fun _ _ _ _ => rfl,
      show ∀ (a b c d : F), ![a, b, c, d] (2 : Fin 4) = c from fun _ _ _ _ => rfl,
      show ∀ (a b c d : F), ![a, b, c, d] (3 : Fin 4) = d from fun _ _ _ _ => rfl] at h0
    linear_combination h0

lemma fin3_subspace_card_le (S : Finset (Fin 3)) :
    (Finset.univ.filter (fun v : Fin 3 → F => v 0 + v 1 + v 2 = 0 ∧ ∀ j ∈ S, v j = 0)).card ≤
    2 ^ (2 - S.card) := by
  revert S
  decide

lemma ker_Lstar_taps_finrank_le (taps : Finset (Fin k)) :
    let missed := ((Finset.univ : Finset (Fin k)) \ taps).image (fun i => i.val % 3)
    let h := if k % 3 = 0 then 2 - missed.card else 0
    let Staps : Submodule F (W k) := {
      carrier := { r | ∀ t, t ∉ taps → r t = 0 },
      zero_mem' := fun _ _ => rfl,
      smul_mem' := fun c r hr t ht => by simp [hr t ht], add_mem' := fun hr hs t ht => by simp [hr t ht, hs t ht] }
    Module.finrank F (LinearMap.ker (LstarLM k hk) ⊓ Staps : Submodule F (W k)) ≤ h := by
  intro missed h Staps
  set Kdef : Submodule F (W k) := LinearMap.ker (LstarLM k hk) ⊓ Staps
  have hper3 : ∀ r ∈ Kdef, ∀ a : ℕ, r (ix k hk (a + 3)) = r (ix k hk a) := by
    intro r hr a
    have hker : Lstar k hk r = 0 := hr.1
    have h0 : r (ix k hk a) + r (ix k hk (a + 1)) + r (ix k hk (a + 2)) = 0 := by
      have := congrFun hker (ix k hk a)
      simpa only [Lstar, Pi.zero_apply, ix_add_left] using this
    have h1 : r (ix k hk (a + 1)) + r (ix k hk (a + 2)) + r (ix k hk (a + 3)) = 0 := by
      have := congrFun hker (ix k hk (a + 1))
      simpa only [Lstar, Pi.zero_apply, ix_add_left, add_assoc] using this
    rw [zmod2_eq_iff_add_eq_zero]
    have ha1 := zmod2_add_self (r (ix k hk (a + 1)))
    have ha2 := zmod2_add_self (r (ix k hk (a + 2)))
    linear_combination h0 + h1 - ha1 - ha2
  have hper3q : ∀ r ∈ Kdef, ∀ a q : ℕ, r (ix k hk (a + 3 * q)) = r (ix k hk a) := by
    intro r hr a q
    induction q with
    | zero => simp
    | succ q ih =>
      have : a + 3 * (q + 1) = (a + 3 * q) + 3 := by omega
      rw [this, hper3 r hr, ih]
  by_cases hk3 : k % 3 = 0
  · simp only [h, hk3, ↓reduceIte]
    let S3 : Finset (Fin 3) := missed.attach.image (fun m =>
      ⟨m.1, by
        rcases Finset.mem_image.mp m.2 with ⟨i, _, him⟩
        rw [← him]
        exact Nat.mod_lt _ (by omega)⟩)
    have hS3_card : S3.card = missed.card := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_attach
      · intro a b hab
        exact Subtype.ext (congrArg Fin.val hab)
    let V3 : Finset (Fin 3 → F) :=
      Finset.univ.filter (fun v : Fin 3 → F => v 0 + v 1 + v 2 = 0 ∧ ∀ j ∈ S3, v j = 0)
    let ev : Kdef → V3 := fun r =>
      ⟨fun j => r.1 (ix k hk j.val), by
        simp only [V3, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · have hker : Lstar k hk r.1 = 0 := r.2.1
          have := congrFun hker (ix k hk 0)
          simpa only [Lstar, Pi.zero_apply, ix_val, Nat.zero_mod, zero_add,
            Fin.val_zero, Fin.val_one, Fin.val_two] using this
        · intro j hj
          rcases Finset.mem_image.mp hj with ⟨⟨m, hm⟩, _, hjeq⟩
          rcases Finset.mem_image.mp hm with ⟨i, hi, him⟩
          have hit : i ∉ taps := (Finset.mem_sdiff.mp hi).2
          have hri0 : r.1 i = 0 := r.2.2 i hit
          have hi_eq : r.1 i = r.1 (ix k hk (i.val % 3)) := by
            conv_lhs => rw [← ix_self k hk i]
            have hdiv : i.val = i.val % 3 + 3 * (i.val / 3) := by omega
            conv_lhs => rw [hdiv]
            exact hper3q r.1 r.2 (i.val % 3) (i.val / 3)
          have hjval : j.val = i.val % 3 := by
            have := congrArg Fin.val hjeq
            simpa [him] using this.symm
          rw [hjval, ← hi_eq, hri0]⟩
    have hev_inj : Function.Injective ev := by
      intro r1 r2 heq
      apply Subtype.ext
      funext i
      have h1 : r1.1 i = r1.1 (ix k hk (i.val % 3)) := by
        conv_lhs => rw [← ix_self k hk i]
        have hdiv : i.val = i.val % 3 + 3 * (i.val / 3) := by omega
        conv_lhs => rw [hdiv]
        exact hper3q r1.1 r1.2 (i.val % 3) (i.val / 3)
      have h2 : r2.1 i = r2.1 (ix k hk (i.val % 3)) := by
        conv_lhs => rw [← ix_self k hk i]
        have hdiv : i.val = i.val % 3 + 3 * (i.val / 3) := by omega
        conv_lhs => rw [hdiv]
        exact hper3q r2.1 r2.2 (i.val % 3) (i.val / 3)
      rw [h1, h2]
      exact congrFun (congrArg Subtype.val heq) ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩
    let _ : Fintype Kdef := Fintype.ofFinite Kdef
    have hcard_le : Fintype.card Kdef ≤ V3.card := by
      have := Fintype.card_le_of_injective ev hev_inj
      simpa [Fintype.card_coe] using this
    have hpow : Fintype.card Kdef = 2 ^ Module.finrank F Kdef := by
      have h1 := Module.card_eq_pow_finrank (K := F) (V := Kdef)
      have h2 : Fintype.card F = 2 := by decide
      rw [h2] at h1
      exact h1
    have hle2 : 2 ^ Module.finrank F Kdef ≤ 2 ^ (2 - missed.card) := by
      calc 2 ^ Module.finrank F Kdef = Fintype.card Kdef := hpow.symm
        _ ≤ V3.card := hcard_le
        _ ≤ 2 ^ (2 - S3.card) := fin3_subspace_card_le S3
        _ = 2 ^ (2 - missed.card) := by rw [hS3_card]
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hle2
  · simp only [h, hk3, ↓reduceIte]
    have hbot : Kdef = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro r hr
      have hstep : ∀ a : ℕ, r (ix k hk (a + k % 3)) = r (ix k hk a) := by
        intro a
        have hkdiv : a + k = (a + k % 3) + 3 * (k / 3) := by omega
        calc r (ix k hk (a + k % 3))
            = r (ix k hk ((a + k % 3) + 3 * (k / 3))) := (hper3q r hr _ _).symm
          _ = r (ix k hk (a + k)) := by rw [← hkdiv]
          _ = r (ix k hk a) := by rw [ix_add_k]
      have hconst1 : ∀ a : ℕ, r (ix k hk (a + 1)) = r (ix k hk a) := by
        have hrem : k % 3 = 1 ∨ k % 3 = 2 := by omega
        rcases hrem with h1 | h2
        · intro a; simpa [h1] using hstep a
        · intro a
          have h2a := hstep (a + 1)
          rw [h2] at h2a
          have h3a := hper3 r hr a
          rw [show a + 1 + 2 = a + 3 by omega] at h2a
          rw [← h2a, h3a]
      have hconst : ∀ a : ℕ, r (ix k hk a) = r (ix k hk 0) := by
        intro a
        induction a with
        | zero => rfl
        | succ a ih => rw [hconst1 a, ih]
      have hr0 : r (ix k hk 0) = 0 := by
        have hker0 : Lstar k hk r = 0 := hr.1
        have hker := congrFun hker0 (ix k hk 0)
        simp only [Lstar, Pi.zero_apply, ix_val, Nat.zero_mod, zero_add] at hker
        rw [hconst 1, hconst 2] at hker
        have hadd := zmod2_add_self (r (ix k hk 0))
        linear_combination hker - hadd
      funext i
      rw [← ix_self k hk i, hconst i.val, hr0]; rfl
    rw [hbot, finrank_bot]

section SpacingAndOverlap

def stepP (i j : Fin k) : Prop :=
  j = ix k hk (i.val + 3) ∨ j = ix k hk (i.val + 4)

lemma stepP_irrefl (hk9 : 9 ≤ k) (i : Fin k) : ¬ stepP k hk i i := by
  rintro (h | h)
  · have hmod := congrArg Fin.val h
    simp only [ix_val] at hmod
    have := i.isLt
    by_cases hlt : i.val + 3 < k
    · rw [Nat.mod_eq_of_lt hlt] at hmod; omega
    · have hlt2 : i.val + 3 - k < k := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at hmod; omega
  · have hmod := congrArg Fin.val h
    simp only [ix_val] at hmod
    have := i.isLt
    by_cases hlt : i.val + 4 < k
    · rw [Nat.mod_eq_of_lt hlt] at hmod; omega
    · have hlt2 : i.val + 4 - k < k := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at hmod; omega

lemma stepP_asym (hk9 : 9 ≤ k) (i j : Fin k) (hij : stepP k hk i j) : ¬ stepP k hk j i := by
  intro hji
  have hsum : ∃ s : ℕ, 6 ≤ s ∧ s ≤ 8 ∧ i = ix k hk (i.val + s) := by
    rcases hij with rfl | rfl <;> rcases hji with h | h
    · exact ⟨6, by omega, by omega, by simpa [ix_add_left, add_assoc] using h⟩
    · exact ⟨7, by omega, by omega, by simpa [ix_add_left, add_assoc] using h⟩
    · exact ⟨7, by omega, by omega, by simpa [ix_add_left, add_assoc] using h⟩
    · exact ⟨8, by omega, by omega, by simpa [ix_add_left, add_assoc] using h⟩
  rcases hsum with ⟨s, hs1, hs2, heq⟩
  have hmod := congrArg Fin.val heq
  simp only [ix_val] at hmod
  have := i.isLt
  by_cases hlt : i.val + s < k
  · rw [Nat.mod_eq_of_lt hlt] at hmod; omega
  · have hlt2 : i.val + s - k < k := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at hmod; omega

lemma stepP_unique_next (P : Finset (Fin k))
    (hP : ∀ i ∈ P, ix k hk (i.val + 1) ∉ P ∧ ix k hk (i.val + 2) ∉ P)
    (i j₁ j₂ : Fin k) (hj1 : j₁ ∈ P) (hj2 : j₂ ∈ P)
    (h1 : stepP k hk i j₁) (h2 : stepP k hk i j₂) : j₁ = j₂ := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · rfl
  · exfalso
    have hsp := (hP _ hj1).1
    rw [ix_add_left] at hsp
    exact hsp hj2
  · exfalso
    have hsp := (hP _ hj2).1
    rw [ix_add_left] at hsp
    exact hsp hj1
  · rfl

lemma stepP_unique_prev (hk9 : 9 ≤ k) (P : Finset (Fin k))
    (hP : ∀ i ∈ P, ix k hk (i.val + 1) ∉ P ∧ ix k hk (i.val + 2) ∉ P)
    (i₁ i₂ j : Fin k) (hi1 : i₁ ∈ P) (hi2 : i₂ ∈ P)
    (h1 : stepP k hk i₁ j) (h2 : stepP k hk i₂ j) : i₁ = i₂ := by
  rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
  · have h := congrArg (fun x : Fin k => ix k hk (x.val + k - 3)) h2
    simp only [ix_add_sub_cancel k hk _ 3 (by omega), ix_self] at h
    exact h
  · exfalso
    have h := congrArg (fun x : Fin k => ix k hk (x.val + k - 3)) h2
    rw [ix_add_sub_cancel k hk i₁.val 3 (by omega), ix_self] at h
    have h3 : ix k hk ((ix k hk (i₂.val + 4)).val + k - 3) = ix k hk (i₂.val + 1) := by
      rw [ix_add_k_sub k hk (i₂.val + 4) 3 (by omega)]
      have : i₂.val + 4 + k - 3 = i₂.val + 1 + k := by omega
      rw [this, ix_add_k]
    rw [h3] at h
    exact (hP i₂ hi2).1 (h ▸ hi1)
  · exfalso
    have h := congrArg (fun x : Fin k => ix k hk (x.val + k - 3)) h2.symm
    rw [ix_add_sub_cancel k hk i₂.val 3 (by omega), ix_self] at h
    have h3 : ix k hk ((ix k hk (i₁.val + 4)).val + k - 3) = ix k hk (i₁.val + 1) := by
      rw [ix_add_k_sub k hk (i₁.val + 4) 3 (by omega)]
      have : i₁.val + 4 + k - 3 = i₁.val + 1 + k := by omega
      rw [this, ix_add_k]
    rw [h3] at h
    exact (hP i₁ hi1).1 (h ▸ hi2)
  · have h := congrArg (fun x : Fin k => ix k hk (x.val + k - 4)) h2
    simp only [ix_add_sub_cancel k hk _ 4 (by omega), ix_self] at h
    exact h

lemma tap_inter_cases (hk9 : 9 ≤ k) (P : Finset (Fin k))
    (hP : ∀ i ∈ P, ix k hk (i.val + 1) ∉ P ∧ ix k hk (i.val + 2) ∉ P)
    {i j : Fin k} (hi : i ∈ P) (hj : j ∈ P) (hij : i ≠ j)
    {a b : ℕ} (ha : a < 5) (hb : b < 5)
    (heq : ix k hk (i.val + a + 1) = ix k hk (j.val + b + 1)) :
    (j = ix k hk (i.val + 3) ∧ ((a = 3 ∧ b = 0) ∨ (a = 4 ∧ b = 1))) ∨
    (j = ix k hk (i.val + 4) ∧ a = 4 ∧ b = 0) ∨
    (i = ix k hk (j.val + 3) ∧ ((a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 4))) ∨
    (i = ix k hk (j.val + 4) ∧ a = 0 ∧ b = 4) := by
  let δ : ℕ := (j.val + k - i.val) % k
  have hδlt : δ < k := Nat.mod_lt _ hk
  have hj_eq : j = ix k hk (i.val + δ) := by
    apply Fin.ext
    simp only [ix_val, δ]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h1 : i.val + (j.val + k - i.val) = j.val + k := by
      have := i.isLt; omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
  have hi_eq : i = ix k hk (j.val + (k - δ)) := by
    apply Fin.ext
    simp only [ix_val, hj_eq]
    have h1 : ((i.val + δ) % k + (k - δ)) % k = (i.val + k) % k := by
      rw [Nat.mod_add_mod]
      have : i.val + δ + (k - δ) = i.val + k := by omega
      rw [this]
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  have hδ0 : δ ≠ 0 := by
    intro h0; rw [h0, add_zero, ix_self] at hj_eq; exact hij hj_eq.symm
  have hδ1 : δ ≠ 1 := by
    intro h1; rw [h1] at hj_eq; exact (hP i hi).1 (hj_eq ▸ hj)
  have hδ2 : δ ≠ 2 := by
    intro h2; rw [h2] at hj_eq; exact (hP i hi).2 (hj_eq ▸ hj)
  have hδm1 : k - δ ≠ 1 := by
    intro h1; rw [h1] at hi_eq; exact (hP j hj).1 (hi_eq ▸ hi)
  have hδm2 : k - δ ≠ 2 := by
    intro h2; rw [h2] at hi_eq; exact (hP j hj).2 (hi_eq ▸ hi)
  have hmod : (δ + b) % k = a := by
    have hm := congrArg Fin.val heq
    simp only [ix_val, hj_eq] at hm
    have h1 : ((i.val + δ) % k + b + 1) % k = (i.val + (δ + b) + 1) % k := by
      rw [add_assoc, Nat.mod_add_mod]; ring_nf
    rw [h1] at hm
    have hsub : (i.val + a + 1) % k = (i.val + (δ + b) % k + 1) % k := by
      rw [hm]
      have h2 : (i.val + (δ + b) % k + 1) % k = (i.val + (δ + b) + 1) % k := by
        calc (i.val + (δ + b) % k + 1) % k
            = ((i.val + 1) + (δ + b) % k) % k := by ring_nf
          _ = ((i.val + 1) + (δ + b)) % k := Nat.add_mod_mod _ _ _
          _ = (i.val + (δ + b) + 1) % k := by ring_nf
      exact h2.symm
    have hlt1 := i.isLt
    have hlt2 : (δ + b) % k < k := Nat.mod_lt _ hk
    by_cases c1 : i.val + a + 1 < k <;> by_cases c2 : i.val + (δ + b) % k + 1 < k
    · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hsub; omega
    · have c2' : i.val + (δ + b) % k + 1 - k < k := by omega
      rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt c2'] at hsub
      omega
    · have c1' : i.val + a + 1 - k < k := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt c1', Nat.mod_eq_of_lt c2] at hsub
      omega
    · have c1' : i.val + a + 1 - k < k := by omega
      have c2' : i.val + (δ + b) % k + 1 - k < k := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt c1',
          Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt c2'] at hsub
      omega
  by_cases hlt : δ + b < k
  · rw [Nat.mod_eq_of_lt hlt] at hmod
    have hcases : (δ = 3 ∧ ((a = 3 ∧ b = 0) ∨ (a = 4 ∧ b = 1))) ∨ (δ = 4 ∧ a = 4 ∧ b = 0) := by
      omega
    rcases hcases with ⟨hδ3, hab⟩ | ⟨hδ4, ha4, hb0⟩
    · left; rw [hδ3] at hj_eq; exact ⟨hj_eq, hab⟩
    · right; left; rw [hδ4] at hj_eq; exact ⟨hj_eq, ha4, hb0⟩
  · have hlt2 : δ + b - k < k := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at hmod
    have hcases : (k - δ = 3 ∧ ((a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 4))) ∨
        (k - δ = 4 ∧ a = 0 ∧ b = 4) := by omega
    rcases hcases with ⟨h3, hab⟩ | ⟨h4, ha0, hb4⟩
    · right; right; left; exact ⟨h3 ▸ hi_eq, hab⟩
    · right; right; right; exact ⟨h4 ▸ hi_eq, ha0, hb4⟩

lemma slot3_private (hk9 : 9 ≤ k) (P : Finset (Fin k))
    (hP : ∀ i ∈ P, ix k hk (i.val + 1) ∉ P ∧ ix k hk (i.val + 2) ∉ P)
    {i j : Fin k} (hi : i ∈ P) (hj : j ∈ P) (hij : i ≠ j) :
    ix k hk (i.val + 3) ∉ tapSet k hk j := by
  intro hmem
  rcases (mem_tapSet_iff k hk j _).mp hmem with ⟨b, hb, heq⟩
  have h := tap_inter_cases k hk hk9 P hP hi hj hij (a := 2) (b := b) (by omega) hb heq
  omega

lemma tap_at_most_two (hk9 : 9 ≤ k) (P : Finset (Fin k))
    (hP : ∀ i ∈ P, ix k hk (i.val + 1) ∉ P ∧ ix k hk (i.val + 2) ∉ P)
    (t : Fin k) :
    (P.filter (fun i => t ∈ tapSet k hk i)).card ≤ 2 := by
  by_contra hgt
  have h3 : 3 ≤ (P.filter (fun i => t ∈ tapSet k hk i)).card := by omega
  obtain ⟨i, hi, j, hj, l, hl, hij, hil, hjl⟩ :
      ∃ i ∈ P.filter (fun x => t ∈ tapSet k hk x),
      ∃ j ∈ P.filter (fun x => t ∈ tapSet k hk x),
      ∃ l ∈ P.filter (fun x => t ∈ tapSet k hk x),
      i ≠ j ∧ i ≠ l ∧ j ≠ l := by
    obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq h3
    rw [Finset.card_eq_three] at hscard
    rcases hscard with ⟨i, j, l, hij, hil, hjl, rfl⟩
    exact ⟨i, hs (by simp), j, hs (by simp), l, hs (by simp), hij, hil, hjl⟩
  rcases Finset.mem_filter.mp hi with ⟨hiP, hit⟩
  rcases Finset.mem_filter.mp hj with ⟨hjP, hjt⟩
  rcases Finset.mem_filter.mp hl with ⟨hlP, hlt⟩
  rcases (mem_tapSet_iff k hk i t).mp hit with ⟨a, ha, rfl⟩
  rcases (mem_tapSet_iff k hk j _).mp hjt with ⟨b, hb, heq1⟩
  rcases (mem_tapSet_iff k hk l _).mp hlt with ⟨c, hc, heq2⟩
  have h1 := tap_inter_cases k hk hk9 P hP hiP hjP hij ha hb heq1
  have h2 := tap_inter_cases k hk hk9 P hP hiP hlP hil ha hc heq2
  rcases h1 with ⟨hj3, ha3 | ha4⟩ | ⟨hj4, ha4, _⟩ | ⟨hi3, ha0 | ha1⟩ | ⟨hi4, ha0, _⟩
  · rcases h2 with ⟨hl3, _⟩ | ⟨_, _, _⟩ | ⟨_, h0 | h1⟩ | ⟨_, h0, _⟩
    · exact hjl (hj3.trans hl3.symm)
    · omega
    · omega
    · omega
    · omega
  · rcases h2 with ⟨hl3, _⟩ | ⟨hl4, _, _⟩ | ⟨_, h0 | h1⟩ | ⟨_, h0, _⟩
    · exact hjl (hj3.trans hl3.symm)
    · have hsp := (hP j hjP).1
      rw [hj3, ix_add_left] at hsp
      exact hsp (hl4 ▸ hlP)
    · omega
    · omega
    · omega
  · rcases h2 with ⟨hl3, _⟩ | ⟨hl4, _, _⟩ | ⟨_, h0 | h1⟩ | ⟨_, h0, _⟩
    · have hsp := (hP l hlP).1
      rw [hl3, ix_add_left] at hsp
      exact hsp (hj4 ▸ hjP)
    · exact hjl (hj4.trans hl4.symm)
    · omega
    · omega
    · omega
  · rcases h2 with ⟨_, h3 | h4⟩ | ⟨_, h4, _⟩ | ⟨hl3, _⟩ | ⟨hl4, _, _⟩
    · omega
    · omega
    · omega
    · exact hjl (stepP_unique_prev k hk hk9 P hP j l i hjP hlP (Or.inl hi3) (Or.inl hl3))
    · exact hjl (stepP_unique_prev k hk hk9 P hP j l i hjP hlP (Or.inl hi3) (Or.inr hl4))
  · rcases h2 with ⟨_, h3 | h4⟩ | ⟨_, h4, _⟩ | ⟨hl3, _⟩ | ⟨_, h0, _⟩
    · omega
    · omega
    · omega
    · exact hjl (stepP_unique_prev k hk hk9 P hP j l i hjP hlP (Or.inl hi3) (Or.inl hl3))
    · omega
  · rcases h2 with ⟨_, h3 | h4⟩ | ⟨_, h4, _⟩ | ⟨hl3, _⟩ | ⟨hl4, _, _⟩
    · omega
    · omega
    · omega
    · exact hjl (stepP_unique_prev k hk hk9 P hP j l i hjP hlP (Or.inr hi4) (Or.inl hl3))
    · exact hjl (stepP_unique_prev k hk hk9 P hP j l i hjP hlP (Or.inr hi4) (Or.inr hl4))

end SpacingAndOverlap

section Direction1

def runF {d : ℕ} (ask : Fin d → ℕ → (W k →ₗ[F] F)) (x : W k) : ℕ :=
  (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0

lemma foldl_bits_inj {α : Type*} (l : List α) (f g : α → ℕ)
    (hf : ∀ a ∈ l, f a < 2) (hg : ∀ a ∈ l, g a < 2) :
    ∀ h1 h2 : ℕ,
      l.foldl (fun h j => 2 * h + f j) h1 = l.foldl (fun h j => 2 * h + g j) h2 →
      h1 = h2 ∧ ∀ a ∈ l, f a = g a := by
  induction l with
  | nil =>
    intro h1 h2 heq
    exact ⟨heq, fun _ ha => absurd ha (List.not_mem_nil)⟩
  | cons a t ih =>
    intro h1 h2 heq
    simp only [List.foldl_cons] at heq
    have hfa : f a < 2 := hf a (by simp)
    have hga : g a < 2 := hg a (by simp)
    have hres := ih (fun x hx => hf x (by simp [hx])) (fun x hx => hg x (by simp [hx]))
      (2 * h1 + f a) (2 * h2 + g a) heq
    have hh : h1 = h2 := by omega
    have hfg : f a = g a := by omega
    refine ⟨hh, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact hfg
    · exact hres.2 x hxt

lemma runF_nonadapt_eq_imp {d : ℕ} (q : Fin d → (W k →ₗ[F] F)) (x y : W k)
    (heq : runF k (fun j _ => q j) x = runF k (fun j _ => q j) y) :
    ∀ j : Fin d, q j x = q j y := by
  have h := foldl_bits_inj (List.finRange d)
    (fun j => if q j x = 0 then 0 else 1)
    (fun j => if q j y = 0 then 0 else 1)
    (fun j _ => by split_ifs <;> omega)
    (fun j _ => by split_ifs <;> omega)
    0 0 heq
  intro j
  have hj := h.2 j (List.mem_finRange j)
  rcases zmod2_cases (q j x) with hx | hx <;> rcases zmod2_cases (q j y) with hy | hy
  · rw [hx, hy]
  · simp [hx, hy] at hj
  · simp [hx, hy] at hj
  · rw [hx, hy]

lemma chain_killing_family (hk9 : 9 ≤ k) (C : Finset (Fin k))
    (n : ℕ) (v : ℕ → Fin k) (hn3 : 3 ≤ n) (hcard : C.card = n)
    (hCimg : C = (Finset.range n).image v)
    (hstep : ∀ j, j + 1 < n → stepP k hk (v j) (v (j + 1)))
    (hend : stepP k hk (v (n - 1)) (v 0) ∨
      (v 1 = ix k hk ((v 0).val + 3) ∧ v (n - 1) = ix k hk ((v (n - 2)).val + 3))) :
    ∃ r : Fin k → W k,
      (∀ i ∈ C, isKilling k hk i (r i)) ∧
      ∑ i ∈ C, r i = 0 := by
  classical
  have hv_inj : Set.InjOn v (Finset.range n) := by
    have h1 : ((Finset.range n).image v).card = (Finset.range n).card := by
      rw [← hCimg, hcard, Finset.card_range]
    exact Finset.card_image_iff.mp h1
  let isCyc : Prop := stepP k hk (v (n - 1)) (v 0)
  let p : ℕ → F := fun j => if isCyc then 1 else if j = 0 ∨ j = n - 1 then 0 else 1
  let edgeV : Fin k → Fin k → F → F → W k := fun u w pu pw =>
    if w = ix k hk (u.val + 3) then
      pw • Pi.single (ix k hk (u.val + 4)) 1 + pu • Pi.single (ix k hk (u.val + 5)) 1
    else
      pu • Pi.single (ix k hk (u.val + 5)) 1
  let eAt : ℕ → W k := fun j => edgeV (v j) (v (j + 1)) (p j) (p (j + 1))
  let eWrap : W k := if isCyc then edgeV (v (n - 1)) (v 0) (p (n - 1)) (p 0) else 0
  let leftV : ℕ → W k := fun j => if j = 0 then eWrap else eAt (j - 1)
  let rightV : ℕ → W k := fun j => if j + 1 < n then eAt j else eWrap
  let rIdx : ℕ → W k := fun j => leftV j + rightV j
  have hne : ∀ u : Fin k, ∀ a b : ℕ, a < 5 → b < 5 → a ≠ b →
      ix k hk (u.val + a + 1) ≠ ix k hk (u.val + b + 1) := by
    intro u a b ha hb hab heq
    exact hab (tap_slot_inj k hk hk9 u ha hb heq)
  have hedge_right : ∀ u w : Fin k, ∀ pu pw : F,
      (∀ t, t ∉ ({ix k hk (u.val + 4), ix k hk (u.val + 5)} : Finset (Fin k)) →
        edgeV u w pu pw t = 0) ∧
      edgeV u w pu pw (ix k hk (u.val + 5)) = pu ∧
      edgeV u w pu pw (ix k hk (u.val + 4)) =
        if w = ix k hk (u.val + 3) then pw else 0 := by
    intro u w pu pw
    have h45 := hne u 3 4 (by omega) (by omega) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      simp only [edgeV]
      split_ifs <;> simp [Pi.single_eq_of_ne ht.1, Pi.single_eq_of_ne ht.2]
    · simp only [edgeV]
      split_ifs
      · simp [Pi.single_eq_of_ne h45.symm]
      · simp
    · simp only [edgeV]
      split_ifs
      · simp [Pi.single_eq_of_ne h45]
      · simp [Pi.single_eq_of_ne h45]
  have hedge_left : ∀ u w : Fin k, ∀ pu pw : F,
      stepP k hk u w → (w ≠ ix k hk (u.val + 3) → pu = pw) →
      (∀ t, t ∉ ({ix k hk (w.val + 1), ix k hk (w.val + 2)} : Finset (Fin k)) →
        edgeV u w pu pw t = 0) ∧
      edgeV u w pu pw (ix k hk (w.val + 1)) = pw ∧
      edgeV u w pu pw (ix k hk (w.val + 2)) =
        if w = ix k hk (u.val + 3) then pu else 0 := by
    intro u w pu pw hsw hpar4
    have h12 := hne w 0 1 (by omega) (by omega) (by omega)
    rcases hsw with hw3 | hw4
    · have h41 : ix k hk (u.val + 4) = ix k hk (w.val + 1) := by
        rw [hw3, ix_add_left]
      have h52 : ix k hk (u.val + 5) = ix k hk (w.val + 2) := by
        rw [hw3, ix_add_left]
      have hed : edgeV u w pu pw =
          pw • Pi.single (ix k hk (w.val + 1)) 1 + pu • Pi.single (ix k hk (w.val + 2)) 1 := by
        simp only [edgeV, hw3, ↓reduceIte, h41, h52]
      rw [hed, ite_eq_left_iff.mpr (fun h => absurd hw3 h)]
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
        simp [Pi.single_eq_of_ne ht.1, Pi.single_eq_of_ne ht.2]
      · simp [Pi.single_eq_of_ne h12]
      · simp [Pi.single_eq_of_ne h12.symm]
    · have hne3 : w ≠ ix k hk (u.val + 3) := by
        rw [hw4]; exact hne u 3 2 (by omega) (by omega) (by omega)
      have hpuw : pu = pw := hpar4 hne3
      have h51 : ix k hk (u.val + 5) = ix k hk (w.val + 1) := by
        rw [hw4, ix_add_left]
      have hed : edgeV u w pu pw = pw • Pi.single (ix k hk (w.val + 1)) 1 := by
        simp only [edgeV, hne3, ↓reduceIte, h51, hpuw]
      rw [hed, ite_eq_right_iff.mpr (fun h => absurd h hne3)]
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
        simp [Pi.single_eq_of_ne ht.1]
      · simp
      · simp [Pi.single_eq_of_ne h12.symm]
  have hrIdx_killing : ∀ j < n, isKilling k hk (v j) (rIdx j) := by
    intro j hj
    have hL : (∀ t, t ∉ ({ix k hk ((v j).val + 1), ix k hk ((v j).val + 2)} : Finset (Fin k)) →
        leftV j t = 0) ∧
        leftV j (ix k hk ((v j).val + 1)) = p j ∧
        (¬ isCyc → j = n - 1 → leftV j (ix k hk ((v j).val + 2)) = 1) := by
      by_cases hj0 : j = 0
      · subst hj0
        simp only [leftV, ↓reduceIte]
        by_cases hc : isCyc
        · have hew : eWrap = edgeV (v (n - 1)) (v 0) (p (n - 1)) (p 0) := by
            simp only [eWrap, hc, ↓reduceIte]
          rw [hew]
          have h1 := hedge_left (v (n - 1)) (v 0) (p (n - 1)) (p 0) hc (by
            intro _; simp [p, hc])
          exact ⟨h1.1, h1.2.1, fun hnc => absurd hc hnc⟩
        · have hew : eWrap = 0 := by simp only [eWrap, hc, ↓reduceIte]
          have hp0 : p 0 = 0 := by simp [p, hc]
          rw [hew, hp0]
          exact ⟨fun _ _ => rfl, rfl, fun _ h0 => by omega⟩
      · simp only [leftV, hj0, ↓reduceIte, eAt]
        have hj1 : j - 1 + 1 = j := by omega
        have hstepj : stepP k hk (v (j - 1)) (v j) := by
          have := hstep (j - 1) (by omega); rwa [hj1] at this
        have hpar4 : v j ≠ ix k hk ((v (j - 1)).val + 3) → p (j - 1) = p j := by
          intro hne3
          by_cases hc : isCyc
          · simp [p, hc]
          · rcases hend with hc' | ⟨hstart, hfin⟩
            · exact absurd hc' hc
            · have hjn1 : j ≠ n - 1 := by
                intro hjn
                have hjm : j - 1 = n - 2 := by omega
                rw [hjm, hjn] at hne3
                exact hne3 hfin
              have hj10 : j - 1 ≠ 0 := by
                intro h0
                have hj1eq : j = 1 := by omega
                rw [h0, hj1eq] at hne3
                exact hne3 hstart
              have hj1n : j - 1 ≠ n - 1 := by omega
              simp [p, hc, hj0, hjn1, hj10, hj1n]
        have h1 := hedge_left (v (j - 1)) (v j) (p (j - 1)) (p j) hstepj hpar4
        rw [hj1]
        refine ⟨h1.1, h1.2.1, fun hnc hjn => ?_⟩
        rw [h1.2.2]
        rcases hend with hc | ⟨_, hfin⟩
        · exact absurd hc hnc
        · have : j - 1 = n - 2 := by omega
          rw [this, hjn]
          simp only [hfin, ↓reduceIte, p, hnc]
          have hn20 : n - 2 ≠ 0 := by omega
          have hn21 : n - 2 ≠ n - 1 := by omega
          simp [hn20, hn21]
    have hR : (∀ t, t ∉ ({ix k hk ((v j).val + 4), ix k hk ((v j).val + 5)} : Finset (Fin k)) →
        rightV j t = 0) ∧
        rightV j (ix k hk ((v j).val + 5)) = p j ∧
        (¬ isCyc → j = 0 → rightV j (ix k hk ((v j).val + 4)) = 1) := by
      by_cases hjn : j + 1 < n
      · simp only [rightV, hjn, ↓reduceIte, eAt]
        have h1 := hedge_right (v j) (v (j + 1)) (p j) (p (j + 1))
        refine ⟨h1.1, h1.2.1, fun hnc hj0 => ?_⟩
        rw [h1.2.2]
        rcases hend with hc | ⟨hstart, _⟩
        · exact absurd hc hnc
        · subst hj0
          simp only [zero_add, hstart, ↓reduceIte, p, hnc]
          have h1n : (1 : ℕ) ≠ n - 1 := by omega
          simp [h1n]
      · have hjeq : j = n - 1 := by omega
        simp only [rightV, hjn, ↓reduceIte]
        by_cases hc : isCyc
        · have hew : eWrap = edgeV (v (n - 1)) (v 0) (p (n - 1)) (p 0) := by
            simp only [eWrap, hc, ↓reduceIte]
          rw [hew, hjeq]
          have h1 := hedge_right (v (n - 1)) (v 0) (p (n - 1)) (p 0)
          exact ⟨h1.1, h1.2.1, fun hnc => absurd hc hnc⟩
        · have hew : eWrap = 0 := by simp only [eWrap, hc, ↓reduceIte]
          have hpn : p (n - 1) = 0 := by simp [p, hc]
          rw [hew, hjeq, hpn]
          exact ⟨fun _ _ => rfl, rfl, fun _ h0 => by omega⟩
    have hsupp : ∀ t, t ∉ tapSet k hk (v j) → rIdx j t = 0 := by
      intro t ht
      have hnt : ∀ a < 5, t ≠ ix k hk ((v j).val + a + 1) := by
        intro a ha heq; exact ht ((mem_tapSet_iff k hk (v j) t).mpr ⟨a, ha, heq⟩)
      have hL0 : leftV j t = 0 := hL.1 t (by
        simp [hnt 0 (by omega), hnt 1 (by omega)])
      have hR0 : rightV j t = 0 := hR.1 t (by
        simp [hnt 3 (by omega), hnt 4 (by omega)])
      simp [rIdx, hL0, hR0]
    have hslot1 : rIdx j (ix k hk ((v j).val + 1)) = p j := by
      have hR0 : rightV j (ix k hk ((v j).val + 1)) = 0 := hR.1 _ (by
        simp [hne (v j) 0 3 (by omega) (by omega) (by omega),
              hne (v j) 0 4 (by omega) (by omega) (by omega)])
      simp [rIdx, hL.2.1, hR0]
    have hslot3 : rIdx j (ix k hk ((v j).val + 3)) = 0 := by
      have hL0 : leftV j (ix k hk ((v j).val + 3)) = 0 := hL.1 _ (by
        simp [hne (v j) 2 0 (by omega) (by omega) (by omega),
              hne (v j) 2 1 (by omega) (by omega) (by omega)])
      have hR0 : rightV j (ix k hk ((v j).val + 3)) = 0 := hR.1 _ (by
        simp [hne (v j) 2 3 (by omega) (by omega) (by omega),
              hne (v j) 2 4 (by omega) (by omega) (by omega)])
      simp [rIdx, hL0, hR0]
    have hslot5 : rIdx j (ix k hk ((v j).val + 5)) = p j := by
      have hL0 : leftV j (ix k hk ((v j).val + 5)) = 0 := hL.1 _ (by
        simp [hne (v j) 4 0 (by omega) (by omega) (by omega),
              hne (v j) 4 1 (by omega) (by omega) (by omega)])
      simp [rIdx, hL0, hR.2.1]
    refine ⟨?_, hsupp, ?_⟩
    · intro hr0
      by_cases hp1 : p j = 1
      · have := congrFun hr0 (ix k hk ((v j).val + 1))
        rw [hslot1, hp1] at this; exact one_ne_zero this
      · have hnc : ¬ isCyc := by
          intro hc; apply hp1; simp [p, hc]
        have hjend : j = 0 ∨ j = n - 1 := by
          by_contra h
          apply hp1; simp [p, hnc, h]
        rcases hjend with hj0 | hjn1
        · have hR4 := hR.2.2 hnc hj0
          have hL4 : leftV j (ix k hk ((v j).val + 4)) = 0 := hL.1 _ (by
            simp [hne (v j) 3 0 (by omega) (by omega) (by omega),
                  hne (v j) 3 1 (by omega) (by omega) (by omega)])
          have := congrFun hr0 (ix k hk ((v j).val + 4))
          simp [rIdx, hL4, hR4] at this
        · have hL2 := hL.2.2 hnc hjn1
          have hR2 : rightV j (ix k hk ((v j).val + 2)) = 0 := hR.1 _ (by
            simp [hne (v j) 1 3 (by omega) (by omega) (by omega),
                  hne (v j) 1 4 (by omega) (by omega) (by omega)])
          have := congrFun hr0 (ix k hk ((v j).val + 2))
          simp [rIdx, hL2, hR2] at this
    · rw [hslot1, hslot3, hslot5, add_zero, zmod2_add_self]
  have hsum_range : ∑ j ∈ Finset.range n, rIdx j = 0 := by
    simp only [rIdx, Finset.sum_add_distrib]
    have hLsum : ∑ j ∈ Finset.range n, leftV j = eWrap + ∑ j ∈ Finset.range (n - 1), eAt j := by
      have hn1 : n = (n - 1) + 1 := by omega
      conv_lhs => rw [hn1, Finset.sum_range_succ']
      simp only [leftV, ↓reduceIte, Nat.succ_ne_zero, Nat.add_sub_cancel]
      rw [add_comm]
    have hRsum : ∑ j ∈ Finset.range n, rightV j = (∑ j ∈ Finset.range (n - 1), eAt j) + eWrap := by
      have hn1 : n = (n - 1) + 1 := by omega
      conv_lhs => rw [hn1, Finset.sum_range_succ]
      have h1 : rightV (n - 1) = eWrap := by
        simp only [rightV, show ¬ (n - 1 + 1 < n) by omega, ↓reduceIte]
      rw [h1]
      congr 1
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjl : j + 1 < n := by have := Finset.mem_range.mp hj; omega
      simp [rightV, hjl]
    rw [hLsum, hRsum]
    funext t
    simp only [Pi.add_apply, Pi.zero_apply]
    have h1 := zmod2_add_self (eWrap t)
    have h2 := zmod2_add_self ((∑ j ∈ Finset.range (n - 1), eAt j) t)
    linear_combination h1 + h2
  let r : Fin k → W k := fun i =>
    if h : ∃ j ∈ Finset.range n, v j = i then rIdx (Classical.choose h) else 0
  have hr_at : ∀ j ∈ Finset.range n, r (v j) = rIdx j := by
    intro j hj
    have hex : ∃ j' ∈ Finset.range n, v j' = v j := ⟨j, hj, rfl⟩
    simp only [r, hex, ↓reduceDIte]
    have hspec := Classical.choose_spec hex
    rw [hv_inj hspec.1 hj hspec.2]
  refine ⟨r, ?_, ?_⟩
  · intro i hi
    rw [hCimg] at hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    rw [hr_at j hj]
    exact hrIdx_killing j (Finset.mem_range.mp hj)
  · rw [hCimg, Finset.sum_image hv_inj]
    rw [Finset.sum_congr rfl (fun j hj => hr_at j hj)]
    exact hsum_range

lemma covers_imp_fits (hk9 : 9 ≤ k) (P : Finset (Fin k)) (d : ℕ) (name c₁ c₂ : Bool → W k)
    (family : Finset (Finset (Fin k)))
    (hfam : ∀ C ∈ family, C ⊆ P ∧
      ∃ (n : ℕ) (v : ℕ → Fin k), 3 ≤ n ∧ C.card = n ∧ C = (Finset.range n).image v ∧
        (∀ j, j + 1 < n → stepP k hk (v j) (v (j + 1))) ∧
        (stepP k hk (v (n - 1)) (v 0) ∨
          (v 1 = ix k hk ((v 0).val + 3) ∧ v (n - 1) = ix k hk ((v (n - 2)).val + 3))))
    (hdisj : ∀ C ∈ family, ∀ E ∈ family, C ≠ E → Disjoint C E)
    (hbudget : P.card ≤ d + family.card) :
    ∃ (ask : Fin d → ℕ → (W k →ₗ[F] F)) (readout : ℕ → Bool → Fin k → W k → F),
      (∀ h b i, cubicF (readout h b i)) ∧
      ∀ x i, i ∈ P → outFalse k hk name c₁ c₂ x i = readout (runF k ask x) false i x := by
  classical
  have hchain : ∀ C : family, ∃ r : Fin k → W k,
      (∀ i ∈ C.1, isKilling k hk i (r i)) ∧ ∑ i ∈ C.1, r i = 0 := by
    intro C
    rcases (hfam C.1 C.2).2 with ⟨n, v, hn3, hcard, hCimg, hstep, hend⟩
    exact chain_killing_family k hk hk9 C.1 n v hn3 hcard hCimg hstep hend
  choose rFam hrFam_kill hrFam_sum using hchain
  have hCnonempty : ∀ C : family, C.1.Nonempty := by
    intro C
    rcases (hfam C.1 C.2).2 with ⟨n, _, hn3, hcard, _⟩
    exact Finset.card_pos.mp (by omega)
  let rep : family → Fin k := fun C => Classical.choose (hCnonempty C)
  have hrep_mem : ∀ C : family, rep C ∈ C.1 := fun C => Classical.choose_spec (hCnonempty C)
  have hrep_inj : Function.Injective rep := by
    intro C1 C2 heq
    by_contra hne
    have hd := hdisj C1.1 C1.2 C2.1 C2.2 (fun h => hne (Subtype.ext h))
    exact Finset.disjoint_left.mp hd (hrep_mem C1) (heq ▸ hrep_mem C2)
  let rAll : Fin k → W k := fun i =>
    if h : ∃ C : family, i ∈ C.1 then rFam (Classical.choose h) i
    else Pi.single (ix k hk (i.val + 2)) 1
  have hrAll_on : ∀ (C : family) (i : Fin k), i ∈ C.1 → rAll i = rFam C i := by
    intro C i hi
    have hex : ∃ C' : family, i ∈ C'.1 := ⟨C, hi⟩
    simp only [rAll, hex, ↓reduceDIte]
    have hspec := Classical.choose_spec hex
    have hCeq : Classical.choose hex = C := by
      by_contra hne
      have hd := hdisj _ (Classical.choose hex).2 C.1 C.2 (fun h => hne (Subtype.ext h))
      exact Finset.disjoint_left.mp hd hspec hi
    rw [hCeq]
  have hrAll_kill : ∀ i ∈ P, isKilling k hk i (rAll i) := by
    intro i _
    by_cases h : ∃ C : family, i ∈ C.1
    · rcases h with ⟨C, hiC⟩
      rw [hrAll_on C i hiC]
      exact hrFam_kill C i hiC
    · simp only [rAll, h, ↓reduceDIte]
      refine ⟨?_, ?_, ?_⟩
      · intro h0
        have := congrFun h0 (ix k hk (i.val + 2))
        simp at this
      · intro t ht
        apply Pi.single_eq_of_ne
        intro heq
        exact ht ((mem_tapSet_iff k hk i t).mpr ⟨1, by omega, heq⟩)
      · have h12 : ix k hk (i.val + 1) ≠ ix k hk (i.val + 2) := fun heq =>
          by have := tap_slot_inj k hk hk9 i (a := 0) (b := 1) (by omega) (by omega) heq; omega
        have h32 : ix k hk (i.val + 3) ≠ ix k hk (i.val + 2) := fun heq =>
          by have := tap_slot_inj k hk hk9 i (a := 2) (b := 1) (by omega) (by omega) heq; omega
        have h52 : ix k hk (i.val + 5) ≠ ix k hk (i.val + 2) := fun heq =>
          by have := tap_slot_inj k hk hk9 i (a := 4) (b := 1) (by omega) (by omega) heq; omega
        simp [Pi.single_eq_of_ne h12, Pi.single_eq_of_ne h32, Pi.single_eq_of_ne h52]
  let repSet : Finset (Fin k) := Finset.univ.image rep
  have hrepSet_sub : repSet ⊆ P := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨C, _, rfl⟩
    exact (hfam C.1 C.2).1 (hrep_mem C)
  have hrepSet_card : repSet.card = family.card := by
    rw [Finset.card_image_of_injective _ hrep_inj, Finset.card_univ, Fintype.card_coe]
  let P' : Finset (Fin k) := P \ repSet
  have hP'card : P'.card ≤ d := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hrepSet_sub, hrepSet_card]
    omega
  let eP' : Fin P'.card ≃ P' := P'.equivFin.symm
  let q : Fin d → (W k →ₗ[F] F) := fun m =>
    if h : m.val < P'.card then dotLM k (Lstar k hk (rAll (eP' ⟨m.val, h⟩).1)) else 0
  let ask : Fin d → ℕ → (W k →ₗ[F] F) := fun m _ => q m
  let K : Submodule F (W k) := ⨅ m : Fin d, LinearMap.ker (q m)
  have hK_vanish : ∀ i ∈ P, ∀ u ∈ K, dot k (Lstar k hk (rAll i)) u = 0 := by
    have hP'_vanish : ∀ j ∈ P', ∀ u ∈ K, dot k (Lstar k hk (rAll j)) u = 0 := by
      intro j hj u hu
      simp only [K, Submodule.mem_iInf, LinearMap.mem_ker] at hu
      let idx := P'.equivFin ⟨j, hj⟩
      have hidx : idx.val < d := lt_of_lt_of_le idx.isLt hP'card
      have hu' : q ⟨idx.val, hidx⟩ u = 0 := hu ⟨idx.val, hidx⟩
      simp only [q, idx.isLt, ↓reduceDIte] at hu'
      have heq : (eP' ⟨idx.val, idx.isLt⟩).1 = j := by
        simp [eP', idx]
      rw [heq] at hu'
      exact hu'
    intro i hi u hu
    by_cases hi' : i ∈ P'
    · exact hP'_vanish i hi' u hu
    · have hirep : i ∈ repSet := by
        by_contra hnot
        exact hi' (Finset.mem_sdiff.mpr ⟨hi, hnot⟩)
      rcases Finset.mem_image.mp hirep with ⟨C, _, rfl⟩
      have hsum0 : ∑ j ∈ C.1, rAll j = 0 := by
        rw [Finset.sum_congr rfl (fun j hj => hrAll_on C j hj)]
        exact hrFam_sum C
      have hr_eq : rAll (rep C) = ∑ j ∈ C.1.erase (rep C), rAll j := by
        have h1 := Finset.add_sum_erase C.1 rAll (hrep_mem C)
        rw [hsum0] at h1
        funext t
        have h1t := congrFun h1 t
        simp only [Pi.add_apply, Pi.zero_apply] at h1t
        exact (zmod2_eq_iff_add_eq_zero _ _).mpr h1t
      have hsub : C.1.erase (rep C) ⊆ P' := by
        intro j hj
        have hjC : j ∈ C.1 := Finset.mem_of_mem_erase hj
        have hjne : j ≠ rep C := Finset.ne_of_mem_erase hj
        refine Finset.mem_sdiff.mpr ⟨(hfam C.1 C.2).1 hjC, ?_⟩
        intro hjrep
        rcases Finset.mem_image.mp hjrep with ⟨C', _, rfl⟩
        have hCC' : C = C' := by
          by_contra hneC
          have hd := hdisj C.1 C.2 C'.1 C'.2 (fun h => hneC (Subtype.ext h))
          exact Finset.disjoint_left.mp hd hjC (hrep_mem C')
        exact hjne (congrArg rep hCC'.symm)
      rw [hr_eq]
      change dot k (LstarLM k hk (∑ j ∈ C.1.erase (rep C), rAll j)) u = 0
      rw [map_sum]
      change dot k (∑ j ∈ C.1.erase (rep C), Lstar k hk (rAll j)) u = 0
      simp only [dot, Finset.sum_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero (fun j hj => ?_)
      exact hP'_vanish j (hsub hj) u hu
  obtain ⟨K', hKK'⟩ := Submodule.exists_isCompl K
  let eK : (K × K') ≃ₗ[F] W k := LinearEquiv.ofBijective
    (K.subtype.coprod K'.subtype)
    ⟨by
      intro ⟨a1, b1⟩ ⟨a2, b2⟩ h
      simp only [LinearMap.coprod_apply, Submodule.coe_subtype] at h
      have hs : (a1 : W k) - a2 = (b2 : W k) - b1 := by
        calc (a1 : W k) - a2 = (a1 + b1) - (a2 + b2) + (b2 - b1) := by abel
          _ = b2 - b1 := by rw [h, sub_self, zero_add]
      have hmem : (a1 : W k) - a2 ∈ K ⊓ K' :=
        ⟨K.sub_mem a1.2 a2.2, hs ▸ K'.sub_mem b2.2 b1.2⟩
      rw [hKK'.inf_eq_bot, Submodule.mem_bot] at hmem
      exact Prod.ext (Subtype.ext (sub_eq_zero.mp hmem))
        (Subtype.ext (sub_eq_zero.mp (by rw [← hs, hmem])).symm),
     by
      intro w
      have hmem : w ∈ K ⊔ K' := by rw [hKK'.sup_eq_top]; exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hmem with ⟨a, ha, b, hb, rfl⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩⟩
  let π : W k →ₗ[F] W k := (K.subtype.comp (LinearMap.fst F K K')).comp eK.symm.toLinearMap
  have hπ_mem : ∀ w, π w ∈ K := fun w => (LinearMap.fst F K K' (eK.symm w)).2
  have hπ_id : ∀ w ∈ K, π w = w := by
    intro w hw
    have heinv : eK.symm w = (⟨w, hw⟩, 0) := by
      apply eK.injective
      rw [LinearEquiv.apply_symm_apply]
      change w = (K.subtype.coprod K'.subtype) (⟨w, hw⟩, 0)
      simp
    simp [π, heinv]
  let readout : ℕ → Bool → Fin k → W k → F := fun h b i x =>
    if b then 0
    else if i ∈ P then
      if hex : ∃ x0 : W k, runF k ask x0 = h then
        outFalse k hk name c₁ c₂ (Classical.choose hex + π (x - Classical.choose hex)) i
      else 0
    else 0
  refine ⟨ask, readout, ?_, ?_⟩
  · intro h b i
    by_cases hb : b = true
    · subst hb; simp only [readout, ↓reduceIte]; exact cubicF_zero
    · have hbf : b = false := by cases b <;> simp_all
      subst hbf
      simp only [readout, Bool.false_eq_true, ↓reduceIte]
      by_cases hi : i ∈ P
      · simp only [hi, ↓reduceIte]
        by_cases hex : ∃ x0 : W k, runF k ask x0 = h
        · simp only [hex, ↓reduceDIte]
          intro v x
          rw [fourthF_comp_affine (fun y => outFalse k hk name c₁ c₂ y i) π (Classical.choose hex) v x]
          rw [fourth_outFalse k hk hk9 name c₁ c₂ i]
          exact killing_forward k hk hk9 i (rAll i) (hrAll_kill i hi) (fun m => π (v m))
            (fun m => hK_vanish i hi (π (v m)) (hπ_mem (v m)))
        · simp only [hex, ↓reduceDIte]; exact cubicF_zero
      · simp only [hi, ↓reduceIte]; exact cubicF_zero
  · intro x i hi
    have hex : ∃ x0 : W k, runF k ask x0 = runF k ask x := ⟨x, rfl⟩
    simp only [readout, Bool.false_eq_true, ↓reduceIte, hi, hex, ↓reduceDIte]
    have hdiffK : x - Classical.choose hex ∈ K := by
      rw [Submodule.mem_iInf]
      intro m
      rw [LinearMap.mem_ker, map_sub]
      have heq := runF_nonadapt_eq_imp k q (Classical.choose hex) x (Classical.choose_spec hex) m
      rw [heq, sub_self]
    rw [hπ_id _ hdiffK, add_sub_cancel]

end Direction1

section Direction2

lemma runF_eq_zero_of_ker {d : ℕ} (ask : Fin d → ℕ → (W k →ₗ[F] F)) (x : W k)
    (hx : ∀ m : Fin d, ask m 0 x = 0) : runF k ask x = 0 := by
  unfold runF
  suffices ∀ l : List (Fin d),
      l.foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0 = 0 from this _
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons, hx a, ↓reduceIte, mul_zero, add_zero]
    exact ih

lemma fourthF_congr_on_subspace (K : Submodule F (W k)) (f g : W k → F)
    (hfg : ∀ x ∈ K, f x = g x) (v : Fin 4 → W k) (hv : ∀ m, v m ∈ K) :
    fourthF f v 0 = fourthF g v 0 := by
  have h0 : (0 : W k) ∈ K := K.zero_mem
  have ha : ∀ {x y : W k}, x ∈ K → y ∈ K → x + y ∈ K := fun hx hy => K.add_mem hx hy
  simp only [fourthF_eq, diffF]
  have h1 : f (0 + v 3 + v 2 + v 1 + v 0) = g (0 + v 3 + v 2 + v 1 + v 0) :=
    hfg _ (ha (ha (ha (ha h0 (hv 3)) (hv 2)) (hv 1)) (hv 0))
  have h2 : f (0 + v 3 + v 2 + v 1) = g (0 + v 3 + v 2 + v 1) :=
    hfg _ (ha (ha (ha h0 (hv 3)) (hv 2)) (hv 1))
  have h3 : f (0 + v 3 + v 2 + v 0) = g (0 + v 3 + v 2 + v 0) :=
    hfg _ (ha (ha (ha h0 (hv 3)) (hv 2)) (hv 0))
  have h4 : f (0 + v 3 + v 2) = g (0 + v 3 + v 2) :=
    hfg _ (ha (ha h0 (hv 3)) (hv 2))
  have h5 : f (0 + v 3 + v 1 + v 0) = g (0 + v 3 + v 1 + v 0) :=
    hfg _ (ha (ha (ha h0 (hv 3)) (hv 1)) (hv 0))
  have h6 : f (0 + v 3 + v 1) = g (0 + v 3 + v 1) :=
    hfg _ (ha (ha h0 (hv 3)) (hv 1))
  have h7 : f (0 + v 3 + v 0) = g (0 + v 3 + v 0) :=
    hfg _ (ha (ha h0 (hv 3)) (hv 0))
  have h8 : f (0 + v 3) = g (0 + v 3) :=
    hfg _ (ha h0 (hv 3))
  have h9 : f (0 + v 2 + v 1 + v 0) = g (0 + v 2 + v 1 + v 0) :=
    hfg _ (ha (ha (ha h0 (hv 2)) (hv 1)) (hv 0))
  have h10 : f (0 + v 2 + v 1) = g (0 + v 2 + v 1) :=
    hfg _ (ha (ha h0 (hv 2)) (hv 1))
  have h11 : f (0 + v 2 + v 0) = g (0 + v 2 + v 0) :=
    hfg _ (ha (ha h0 (hv 2)) (hv 0))
  have h12 : f (0 + v 2) = g (0 + v 2) :=
    hfg _ (ha h0 (hv 2))
  have h13 : f (0 + v 1 + v 0) = g (0 + v 1 + v 0) :=
    hfg _ (ha (ha h0 (hv 1)) (hv 0))
  have h14 : f (0 + v 1) = g (0 + v 1) :=
    hfg _ (ha h0 (hv 1))
  have h15 : f (0 + v 0) = g (0 + v 0) :=
    hfg _ (ha h0 (hv 0))
  have h16 : f 0 = g 0 := hfg 0 h0
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

lemma finrank_ann_le {d : ℕ} (q : Fin d → (W k →ₗ[F] F)) (V : Submodule F (W k))
    (hV : ∀ w ∈ V, ∀ x ∈ (⨅ m : Fin d, LinearMap.ker (q m)), dot k w x = 0) :
    Module.finrank F V ≤ d := by
  let K : Submodule F (W k) := ⨅ m : Fin d, LinearMap.ker (q m)
  let T : W k →ₗ[F] (Fin d → F) := {
    toFun := fun x m => q m x,
    map_add' := fun x y => by funext m; exact map_add (q m) x y,
    map_smul' := fun c x => by funext m; exact map_smul (q m) c x }
  have hkerT : LinearMap.ker T = K := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_iInf, K, T, LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · intro h m; exact congrFun h m
    · intro h; funext m; exact h m
  obtain ⟨K', hKK'⟩ := Submodule.exists_isCompl K
  have hfrK' : Module.finrank F K' ≤ d := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hKK'
    have h2 := LinearMap.finrank_range_add_finrank_ker T
    rw [hkerT] at h2
    have h3 : Module.finrank F (LinearMap.range T) ≤ d := by
      calc Module.finrank F (LinearMap.range T)
          ≤ Module.finrank F (Fin d → F) := Submodule.finrank_le _
        _ = d := by simp
    omega
  let φ : V →ₗ[F] (K' →ₗ[F] F) := {
    toFun := fun w => {
      toFun := fun y => dot k w.1 y.1,
      map_add' := fun y1 y2 => (dotLM k w.1).map_add y1.1 y2.1,
      map_smul' := fun c y => (dotLM k w.1).map_smul c y.1 },
    map_add' := fun w1 w2 => by
      ext y; simp [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib],
    map_smul' := fun c w => by
      ext y; simp [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum] }
  have hφ_inj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    apply Subtype.ext
    apply eq_zero_of_dot_eq_zero k
    intro x
    have hx : x ∈ K ⊔ K' := by rw [hKK'.sup_eq_top]; exact Submodule.mem_top
    rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
    have ha0 : dot k w.1 a = 0 := hV w.1 w.2 a ha
    have hb0 : dot k w.1 b = 0 := LinearMap.congr_fun hw ⟨b, hb⟩
    have hadd : dot k w.1 (a + b) = dot k w.1 a + dot k w.1 b := (dotLM k w.1).map_add a b
    rw [hadd, ha0, hb0, zero_add]
  calc Module.finrank F V
      ≤ Module.finrank F (K' →ₗ[F] F) := LinearMap.finrank_le_finrank_of_injective hφ_inj
    _ = Module.finrank F K' := by simp
    _ ≤ d := hfrK'

lemma fits_imp_covers (hk9 : 9 ≤ k) (P : Finset (Fin k)) (d : ℕ) (name c₁ c₂ : Bool → W k)
    (hP : ∀ i ∈ P, ix k hk (i.val + 1) ∉ P ∧ ix k hk (i.val + 2) ∉ P)
    (ask : Fin d → ℕ → (W k →ₗ[F] F)) (readout : ℕ → Bool → Fin k → W k → F)
    (hcubic : ∀ h b i, cubicF (readout h b i))
    (hagree : ∀ x i, i ∈ P → outFalse k hk name c₁ c₂ x i = readout (runF k ask x) false i x) :
    let taps := P.biUnion (fun i => tapSet k hk i)
    let missed := ((Finset.univ : Finset (Fin k)) \ taps).image (fun i => i.val % 3)
    let h := if k % 3 = 0 then 2 - missed.card else 0
    ∃ family : Finset (Finset (Fin k)),
      (∀ C ∈ family, C ⊆ P ∧
        ∃ (n : ℕ) (v : ℕ → Fin k), 3 ≤ n ∧ C.card = n ∧ C = (Finset.range n).image v ∧
          (∀ j, j + 1 < n → stepP k hk (v j) (v (j + 1))) ∧
          (stepP k hk (v (n - 1)) (v 0) ∨
            (v 1 = ix k hk ((v 0).val + 3) ∧ v (n - 1) = ix k hk ((v (n - 2)).val + 3)))) ∧
      (∀ C ∈ family, ∀ E ∈ family, C ≠ E → Disjoint C E) ∧
      P.card ≤ d + h + family.card := by
  classical
  intro taps missed h
  let K : Submodule F (W k) := ⨅ m : Fin d, LinearMap.ker (ask m 0)
  have hkill_ex : ∀ i : P, ∃ r : W k, isKilling k hk i.1 r ∧ ∀ x ∈ K, dot k (Lstar k hk r) x = 0 := by
    intro i
    apply killing_converse k hk hk9 i.1 K
    intro v hv
    rw [← fourth_outFalse k hk hk9 name c₁ c₂ i.1 v 0]
    have hfg : ∀ x ∈ K, outFalse k hk name c₁ c₂ x i.1 = readout 0 false i.1 x := by
      intro x hx
      have hx' : ∀ m : Fin d, ask m 0 x = 0 := by
        simp only [K, Submodule.mem_iInf, LinearMap.mem_ker] at hx
        exact hx
      have hrun : runF k ask x = 0 := runF_eq_zero_of_ker k ask x hx'
      have ha := hagree x i.1 i.2
      rwa [hrun] at ha
    rw [fourthF_congr_on_subspace k K _ _ hfg v hv]
    exact hcubic 0 false i.1 v 0
  choose r hr_kill hr_ann using hkill_ex
  let evalP : (P → F) →ₗ[F] W k := {
    toFun := fun c => ∑ i : P, c i • r i,
    map_add' := fun c1 c2 => by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib],
    map_smul' := fun a c => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  let U : Submodule F (W k) := LinearMap.range evalP
  let Mdep : Submodule F (P → F) := LinearMap.ker evalP
  let Staps : Submodule F (W k) := {
    carrier := { w | ∀ t, t ∉ taps → w t = 0 },
    zero_mem' := fun _ _ => rfl,
    smul_mem' := fun c w hw t ht => by simp [hw t ht], add_mem' := fun hw1 hw2 t ht => by simp [hw1 t ht, hw2 t ht] }
  have hU_taps : U ≤ Staps := by
    rintro _ ⟨c, rfl⟩ t ht
    simp only [evalP, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hti : t ∉ tapSet k hk i.1 := by
      intro hmem
      exact ht (Finset.mem_biUnion.mpr ⟨i.1, i.2, hmem⟩)
    rw [(hr_kill i).2.1 t hti, mul_zero]
  let LstarU : U →ₗ[F] W k := (LstarLM k hk).domRestrict U
  have hker_le : Module.finrank F (LinearMap.ker LstarU) ≤ h := by
    let inc : LinearMap.ker LstarU →ₗ[F] (LinearMap.ker (LstarLM k hk) ⊓ Staps : Submodule F (W k)) := {
      toFun := fun u => ⟨u.1.1, u.2, hU_taps u.1.2⟩,
      map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
    have hinc_inj : Function.Injective inc := by
      intro u1 u2 heq
      have h1 : u1.1.1 = u2.1.1 := congrArg (fun x => x.1) heq
      exact Subtype.ext (Subtype.ext h1)
    calc Module.finrank F (LinearMap.ker LstarU)
        ≤ Module.finrank F (LinearMap.ker (LstarLM k hk) ⊓ Staps : Submodule F (W k)) :=
          LinearMap.finrank_le_finrank_of_injective hinc_inj
      _ ≤ h := ker_Lstar_taps_finrank_le k hk taps
  have hrange_le : Module.finrank F (LinearMap.range LstarU) ≤ d := by
    apply finrank_ann_le k (fun m => ask m 0) (LinearMap.range LstarU)
    rintro w ⟨⟨u, ⟨c, rfl⟩⟩, rfl⟩ x hx
    change dot k (LstarLM k hk (∑ i : P, c i • r i)) x = 0
    rw [map_sum]
    change dot k (∑ i : P, LstarLM k hk (c i • r i)) x = 0
    simp only [dot, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have h1 : ∑ j : Fin k, c i * LstarLM k hk (r i) j * x j =
        c i * dot k (Lstar k hk (r i)) x := by
      simp only [dot, LstarLM, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum, mul_assoc]
    rw [h1, hr_ann i x hx, mul_zero]
  have hP_card_bound : P.card ≤ d + h + Module.finrank F Mdep := by
    have h1 := LinearMap.finrank_range_add_finrank_ker evalP
    change Module.finrank F U + Module.finrank F Mdep = Module.finrank F (P → F) at h1
    have h2 := LinearMap.finrank_range_add_finrank_ker LstarU
    have h3 : Module.finrank F (P → F) = P.card := by
      simp [Fintype.card_coe]
    omega
  let H : SimpleGraph P := {
    Adj := fun i j => i ≠ j ∧ ∃ t : Fin k, r i t = 1 ∧ r j t = 1,
    symm := ⟨fun i j ⟨hne, t, hi, hj⟩ => ⟨hne.symm, t, hj, hi⟩⟩,
    loopless := ⟨fun i ⟨hne, _⟩ => hne rfl⟩ }
  let pinned : P → Prop := fun i =>
    ∃ t : Fin k, r i t = 1 ∧ ∀ j : P, j ≠ i → r j t = 0
  have hr_active_sub : ∀ t : Fin k,
      (Finset.univ.filter (fun i : P => r i t = 1)).card ≤ 2 := by
    intro t
    have hsub : (Finset.univ.filter (fun i : P => r i t = 1)).image Subtype.val ⊆
        P.filter (fun i => t ∈ tapSet k hk i) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      have hri1 : r i t = 1 := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨i.2, ?_⟩
      by_contra hnt
      have h0 := (hr_kill i).2.1 t hnt
      rw [hri1] at h0; exact one_ne_zero h0
    calc (Finset.univ.filter (fun i : P => r i t = 1)).card
        = ((Finset.univ.filter (fun i : P => r i t = 1)).image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (P.filter (fun i => t ∈ tapSet k hk i)).card := Finset.card_le_card hsub
      _ ≤ 2 := tap_at_most_two k hk hk9 P hP t
  have hMdep_iff : ∀ c : P → F,
      c ∈ Mdep ↔ (∀ i : P, pinned i → c i = 0) ∧ (∀ i j : P, H.Adj i j → c i = c j) := by
    intro c
    constructor
    · intro hc
      have hsum0 : ∀ t : Fin k, ∑ i : P, c i * r i t = 0 := fun t => by
        have := congrFun hc t
        simpa [evalP, Finset.sum_apply] using this
      refine ⟨?_, ?_⟩
      · intro i ⟨t, hri, hoth⟩
        have ht := hsum0 t
        rw [Finset.sum_eq_single i] at ht
        · simpa [hri] using ht
        · intro j _ hji; rw [hoth j hji, mul_zero]
        · intro h; exact absurd (Finset.mem_univ i) h
      · intro i j ⟨hij, t, hri, hrj⟩
        have ht := hsum0 t
        have hact : Finset.univ.filter (fun x : P => r x t = 1) = {i, j} := by
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            by_contra hnot
            have hcard3 : 3 ≤ (Finset.univ.filter (fun x : P => r x t = 1)).card := by
              have hsub3 : ({i, j, x} : Finset P) ⊆ Finset.univ.filter (fun y : P => r y t = 1) := by
                intro y hy
                simp only [Finset.mem_insert, Finset.mem_singleton] at hy
                rcases hy with rfl | rfl | rfl
                · simp [hri]
                · simp [hrj]
                · exact hx
              have hneix : i ≠ x := fun h => hnot (by simp [h])
              have hnejx : j ≠ x := fun h => hnot (by simp [h])
              have hc3 : ({i, j, x} : Finset P).card = 3 := by
                rw [Finset.card_insert_of_notMem (by simp [hij, hneix]),
                    Finset.card_insert_of_notMem (by simp [hnejx]), Finset.card_singleton]
              rw [← hc3]
              exact Finset.card_le_card hsub3
            have hle2 := hr_active_sub t
            omega
          · rw [Finset.card_pair hij]
            have hsub2 : ({i, j} : Finset P) ⊆ Finset.univ.filter (fun y : P => r y t = 1) := by
              intro y hy
              simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl <;> simp [hri, hrj]
            have h2c : ({i, j} : Finset P).card = 2 := Finset.card_pair hij
            calc (2 : ℕ) = ({i, j} : Finset P).card := h2c.symm
              _ ≤ (Finset.univ.filter (fun y : P => r y t = 1)).card := Finset.card_le_card hsub2
        have hsum_act : ∑ x : P, c x * r x t =
            ∑ x ∈ Finset.univ.filter (fun x : P => r x t = 1), c x * r x t := by
          rw [← Finset.sum_subset (Finset.filter_subset (fun x : P => r x t = 1) Finset.univ)]
          intro x _ hx
          have hx0 : r x t = 0 := by
            rcases zmod2_cases (r x t) with h0 | h1
            · exact h0
            · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h1⟩) hx
          rw [hx0, mul_zero]
        rw [hsum_act, hact, Finset.sum_pair hij, hri, hrj, mul_one, mul_one] at ht
        exact (zmod2_eq_iff_add_eq_zero _ _).mpr ht
    · rintro ⟨hpin, hadj⟩
      change ∑ i : P, c i • r i = 0
      funext t
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      let A := Finset.univ.filter (fun i : P => r i t = 1)
      have hsum_act : ∑ i : P, c i * r i t = ∑ i ∈ A, c i := by
        rw [← Finset.sum_subset (Finset.filter_subset (fun i : P => r i t = 1) Finset.univ)]
        · refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [(Finset.mem_filter.mp hi).2, mul_one]
        · intro i _ hi
          have hi0 : r i t = 0 := by
            rcases zmod2_cases (r i t) with h0 | h1
            · exact h0
            · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩) hi
          rw [hi0, mul_zero]
      rw [hsum_act]
      have hle2 : A.card ≤ 2 := hr_active_sub t
      have hcases : A.card = 0 ∨ A.card = 1 ∨ A.card = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]
      · rcases Finset.card_eq_one.mp h1 with ⟨i, hiA⟩
        rw [hiA, Finset.sum_singleton]
        apply hpin i
        refine ⟨t, ?_, ?_⟩
        · have : i ∈ A := by rw [hiA]; simp
          exact (Finset.mem_filter.mp this).2
        · intro j hji
          rcases zmod2_cases (r j t) with hj0 | hj1
          · exact hj0
          · exfalso
            have hjA : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj1⟩
            rw [hiA, Finset.mem_singleton] at hjA
            exact hji hjA
      · rcases Finset.card_eq_two.mp h2 with ⟨i, j, hij, hijA⟩
        rw [hijA, Finset.sum_pair hij]
        have hiA : i ∈ A := by rw [hijA]; simp
        have hjA : j ∈ A := by rw [hijA]; simp
        have hri : r i t = 1 := (Finset.mem_filter.mp hiA).2
        have hrj : r j t = 1 := (Finset.mem_filter.mp hjA).2
        rw [hadj i j ⟨hij, t, hri, hrj⟩, zmod2_add_self]
  let freeComps : Finset H.ConnectedComponent :=
    Finset.univ.filter (fun q => ∀ i : P, H.connectedComponentMk i = q → ¬ pinned i)
  let compSet : H.ConnectedComponent → Finset (Fin k) := fun q =>
    (Finset.univ.filter (fun i : P => H.connectedComponentMk i = q)).image Subtype.val
  let family : Finset (Finset (Fin k)) := freeComps.image compSet
  have hcomp_inj : Function.Injective compSet := by
    intro q1 q2 heq
    obtain ⟨i, hiq⟩ := q1.exists_rep
    have hi1 : i.1 ∈ compSet q1 := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiq⟩, rfl⟩
    rw [heq] at hi1
    rcases Finset.mem_image.mp hi1 with ⟨j, hj, hji⟩
    have hij : j = i := Subtype.ext hji
    subst hij
    exact hiq.symm.trans (Finset.mem_filter.mp hj).2
  have hfam_card : family.card = freeComps.card :=
    Finset.card_image_of_injective _ hcomp_inj
  have hMdep_finrank : Module.finrank F Mdep = freeComps.card := by
    let toM : (freeComps → F) →ₗ[F] Mdep := {
      toFun := fun a => ⟨fun i =>
        if hq : H.connectedComponentMk i ∈ freeComps then a ⟨H.connectedComponentMk i, hq⟩ else 0,
        (hMdep_iff _).mpr ⟨by
          intro i hpi
          have hnot : H.connectedComponentMk i ∉ freeComps := by
            simp only [freeComps, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not]
            exact ⟨i, rfl, hpi⟩
          simp [hnot],
         by
          intro i j hij
          have heq : H.connectedComponentMk i = H.connectedComponentMk j :=
            SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hij)
          simp [heq]⟩⟩,
      map_add' := fun a b => by
        apply Subtype.ext; funext i
        by_cases hq : H.connectedComponentMk i ∈ freeComps <;> simp [hq],
      map_smul' := fun s a => by
        apply Subtype.ext; funext i
        by_cases hq : H.connectedComponentMk i ∈ freeComps <;> simp [hq] }
    have hreach_eq : ∀ c ∈ Mdep, ∀ i j : P, H.Reachable i j → c i = c j := by
      intro c hc i j ⟨w⟩
      induction w with
      | nil => rfl
      | cons hadj _ ih =>
        exact ((hMdep_iff c).mp hc).2 _ _ hadj |>.trans ih
    have hbij : Function.Bijective toM := by
      refine ⟨?_, ?_⟩
      · intro a1 a2 heq
        funext ⟨q, hq⟩
        obtain ⟨i, hiq⟩ := q.exists_rep
        have hiq' : H.connectedComponentMk i = q := hiq
        have h1 := congrFun (congrArg Subtype.val heq) i
        have hqi : H.connectedComponentMk i ∈ freeComps := hiq'.symm ▸ hq
        simp only [toM, LinearMap.coe_mk, AddHom.coe_mk, hqi, ↓reduceDIte] at h1
        have hsub : (⟨H.connectedComponentMk i, hqi⟩ : freeComps) = ⟨q, hq⟩ := Subtype.ext hiq'
        rwa [hsub] at h1
      · intro ⟨c, hc⟩
        refine ⟨fun q => c (Classical.choose q.1.exists_rep), ?_⟩
        apply Subtype.ext; funext i
        simp only [toM, LinearMap.coe_mk, AddHom.coe_mk]
        by_cases hq : H.connectedComponentMk i ∈ freeComps
        · simp only [hq, ↓reduceDIte]
          have hrep := Classical.choose_spec (H.connectedComponentMk i).exists_rep
          have hreach : H.Reachable (Classical.choose (H.connectedComponentMk i).exists_rep) i :=
            SimpleGraph.ConnectedComponent.exact hrep
          exact hreach_eq c hc _ i hreach
        · simp only [hq, ↓reduceDIte]
          simp only [freeComps, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hq
          rcases hq with ⟨j, hjq, hjp⟩
          have hreach : H.Reachable i j :=
            SimpleGraph.ConnectedComponent.exact hjq.symm
          rw [hreach_eq c hc i j hreach, ((hMdep_iff c).mp hc).1 j hjp]
    have heq := (LinearEquiv.ofBijective toM hbij).finrank_eq
    rw [← heq, Module.finrank_pi, Fintype.card_coe]
  have hAdj_step : ∀ i j : P, H.Adj i j → stepP k hk i.1 j.1 ∨ stepP k hk j.1 i.1 := by
    intro i j ⟨hij, t, hri, hrj⟩
    have hti : t ∈ tapSet k hk i.1 := by
      by_contra hnt; rw [(hr_kill i).2.1 t hnt] at hri; exact zero_ne_one hri
    have htj : t ∈ tapSet k hk j.1 := by
      by_contra hnt; rw [(hr_kill j).2.1 t hnt] at hrj; exact zero_ne_one hrj
    rcases (mem_tapSet_iff k hk i.1 t).mp hti with ⟨a, ha, rfl⟩
    rcases (mem_tapSet_iff k hk j.1 _).mp htj with ⟨b, hb, heq⟩
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have hc := tap_inter_cases k hk hk9 P hP i.2 j.2 hne ha hb heq
    rcases hc with ⟨h3, _⟩ | ⟨h4, _⟩ | ⟨h3, _⟩ | ⟨h4, _⟩
    · left; left; exact h3
    · left; right; exact h4
    · right; left; exact h3
    · right; right; exact h4
  refine ⟨family, ?_, ?_, ?_⟩
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨q, hq, rfl⟩
    have hCsub : compSet q ⊆ P := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact i.2
    have hCmem : ∀ i : P, i.1 ∈ compSet q ↔ H.connectedComponentMk i = q := by
      intro i
      constructor
      · intro hi
        rcases Finset.mem_image.mp hi with ⟨j, hj, hji⟩
        have : j = i := Subtype.ext hji
        subst this
        exact (Finset.mem_filter.mp hj).2
      · intro hi
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
    have hC_unpin : ∀ i : P, i.1 ∈ compSet q → ¬ pinned i := by
      intro i hi
      exact (Finset.mem_filter.mp hq).2 i ((hCmem i).mp hi)
    have hC_conn : ∀ x (hx : x ∈ compSet q), ∀ y (hy : y ∈ compSet q),
        H.Reachable ⟨x, hCsub hx⟩ ⟨y, hCsub hy⟩ := by
      intro x hx y hy
      have hqx := (hCmem ⟨x, hCsub hx⟩).mp hx
      have hqy := (hCmem ⟨y, hCsub hy⟩).mp hy
      exact SimpleGraph.ConnectedComponent.exact (hqx.trans hqy.symm)
    have hC_closed : ∀ (S : Finset (Fin k)) (hSsub : S ⊆ compSet q), S.Nonempty →
        (∀ x (hx : x ∈ S), ∀ y (hy : y ∈ compSet q),
          H.Adj ⟨x, hCsub (hSsub hx)⟩ ⟨y, hCsub hy⟩ → y ∈ S) →
        S = compSet q := by
      intro S hSsub ⟨x0, hx0⟩ hScl
      apply Finset.Subset.antisymm hSsub
      intro y hy
      have hreach := hC_conn x0 (hSsub hx0) y hy
      rcases hreach with ⟨w⟩
      have hwalk : ∀ {a b : P} (w : H.Walk a b), a.1 ∈ S → b.1 ∈ S := by
        intro a b w
        induction w with
        | nil => intro ha; exact ha
        | @cons u u' b hadj w' ih =>
          intro hu
          have hu'C : u'.1 ∈ compSet q := by
            have hqu : H.connectedComponentMk u = q := (hCmem u).mp (hSsub hu)
            have hqu' : H.connectedComponentMk u' = q :=
              (SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hadj)).symm.trans hqu
            exact (hCmem u').mpr hqu'
          exact ih (hScl u.1 hu u'.1 hu'C hadj)
      exact hwalk w hx0
    refine ⟨hCsub, ?_⟩
    by_cases hpred : ∀ x ∈ compSet q, ∃ y ∈ compSet q, stepP k hk y x
    · have hsucc_ex : ∀ x ∈ compSet q, ∃ y ∈ compSet q, stepP k hk x y := by
        let prev : compSet q → compSet q := fun x =>
          ⟨Classical.choose (hpred x.1 x.2), (Classical.choose_spec (hpred x.1 x.2)).1⟩
        have hprev_step : ∀ x : compSet q, stepP k hk (prev x).1 x.1 := fun x =>
          (Classical.choose_spec (hpred x.1 x.2)).2
        have hprev_inj : Function.Injective prev := by
          intro x1 x2 heq
          apply Subtype.ext
          have h1 := hprev_step x1
          have h2 := hprev_step x2
          rw [heq] at h1
          exact stepP_unique_next k hk P hP (prev x2).1 x1.1 x2.1
            (hCsub x1.2) (hCsub x2.2) h1 h2
        have hprev_surj : Function.Surjective prev := Finite.injective_iff_surjective.mp hprev_inj
        intro x hx
        obtain ⟨y, hy⟩ := hprev_surj ⟨x, hx⟩
        refine ⟨y.1, y.2, ?_⟩
        have hst := hprev_step y
        rw [hy] at hst
        exact hst
      let f : compSet q → compSet q := fun x =>
        ⟨Classical.choose (hsucc_ex x.1 x.2), (Classical.choose_spec (hsucc_ex x.1 x.2)).1⟩
      have hf_step : ∀ x : compSet q, stepP k hk x.1 (f x).1 := fun x =>
        (Classical.choose_spec (hsucc_ex x.1 x.2)).2
      have hf_inj : Function.Injective f := by
        intro x1 x2 heq
        apply Subtype.ext
        have h1 := hf_step x1
        have h2 := hf_step x2
        rw [heq] at h1
        exact stepP_unique_prev k hk hk9 P hP x1.1 x2.1 (f x2).1
          (hCsub x1.2) (hCsub x2.2) h1 h2
      obtain ⟨i0, hi0q⟩ := q.exists_rep
      let x0 : compSet q := ⟨i0.1, (hCmem i0).mpr hi0q⟩
      have hper_ex : ∃ m : ℕ, 0 < m ∧ f^[m] x0 = x0 := by
        obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] x0)
        rcases lt_or_gt_of_ne hab with hlt | hgt
        · refine ⟨b - a, by omega, ?_⟩
          have hba : a + (b - a) = b := by omega
          rw [← hba, Function.iterate_add_apply] at heq
          exact (hf_inj.iterate a) heq.symm
        · refine ⟨a - b, by omega, ?_⟩
          have hab' : b + (a - b) = a := by omega
          rw [← hab', Function.iterate_add_apply] at heq
          exact (hf_inj.iterate b) heq
      let m : ℕ := Nat.find hper_ex
      have hm_spec : 0 < m ∧ f^[m] x0 = x0 := Nat.find_spec hper_ex
      have hm_min : ∀ j, 0 < j → j < m → f^[j] x0 ≠ x0 := fun j hj1 hj2 =>
        fun heq => Nat.find_min hper_ex hj2 ⟨hj1, heq⟩
      let v : ℕ → Fin k := fun j => (f^[j] x0).1
      have hv_inj : Set.InjOn v (Finset.range m) := by
        intro a ha b hb hab
        have ha' := Finset.mem_range.mp ha
        have hb' := Finset.mem_range.mp hb
        have hab' : f^[a] x0 = f^[b] x0 := Subtype.ext hab
        rcases lt_trichotomy a b with hlt | rfl | hgt
        · exfalso
          have hba : a + (b - a) = b := by omega
          rw [← hba, Function.iterate_add_apply] at hab'
          exact hm_min (b - a) (by omega) (by omega) ((hf_inj.iterate a) hab'.symm)
        · rfl
        · exfalso
          have hba : b + (a - b) = a := by omega
          rw [← hba, Function.iterate_add_apply] at hab'
          exact hm_min (a - b) (by omega) (by omega) ((hf_inj.iterate b) hab')
      let Orb : Finset (Fin k) := (Finset.range m).image v
      have hOrb_sub : Orb ⊆ compSet q := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
        exact (f^[j] x0).2
      have hOrb_eq : Orb = compSet q := by
        apply hC_closed Orb hOrb_sub ⟨v 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hm_spec.1, rfl⟩⟩
        intro x hx y hy hadj
        rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
        have hjm : j < m := Finset.mem_range.mp hj
        rcases hAdj_step _ _ hadj with hxy | hyx
        · have hyf : y = (f (f^[j] x0)).1 :=
            stepP_unique_next k hk P hP _ y _ (hCsub hy) (hCsub (f (f^[j] x0)).2) hxy (hf_step _)
          by_cases hj1 : j + 1 < m
          · refine Finset.mem_image.mpr ⟨j + 1, Finset.mem_range.mpr hj1, ?_⟩
            simp only [v, Function.iterate_succ_apply', hyf]
          · have hjm1 : j + 1 = m := by omega
            refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hm_spec.1, ?_⟩
            have h0 : f (f^[j] x0) = x0 := by
              have : f (f^[j] x0) = f^[j + 1] x0 := (Function.iterate_succ_apply' f j x0).symm
              rw [this, hjm1, hm_spec.2]
            simp only [v, Function.iterate_zero_apply, hyf, h0]
        · by_cases hj0 : j = 0
          · subst hj0
            have hprev_eq : y = (f^[m - 1] x0).1 := by
              have hstep_last : stepP k hk (f^[m - 1] x0).1 x0.1 := by
                have h1 := hf_step (f^[m - 1] x0)
                have h2 : f (f^[m - 1] x0) = x0 := by
                  have : f (f^[m - 1] x0) = f^[m - 1 + 1] x0 := (Function.iterate_succ_apply' f _ x0).symm
                  rw [this, show m - 1 + 1 = m by omega, hm_spec.2]
                rw [h2] at h1
                exact h1
              exact stepP_unique_prev k hk hk9 P hP y _ x0.1 (hCsub hy) (hCsub (f^[m - 1] x0).2) hyx hstep_last
            exact Finset.mem_image.mpr ⟨m - 1, Finset.mem_range.mpr (by omega), hprev_eq.symm⟩
          · have hprev_eq : y = (f^[j - 1] x0).1 := by
              have hstep_prev : stepP k hk (f^[j - 1] x0).1 (f^[j] x0).1 := by
                have h1 := hf_step (f^[j - 1] x0)
                have h2 : f (f^[j - 1] x0) = f^[j] x0 := by
                  have : f (f^[j - 1] x0) = f^[j - 1 + 1] x0 := (Function.iterate_succ_apply' f _ x0).symm
                  rw [this, show j - 1 + 1 = j by omega]
                rw [h2] at h1
                exact h1
              exact stepP_unique_prev k hk hk9 P hP y _ _ (hCsub hy) (hCsub (f^[j - 1] x0).2) hyx hstep_prev
            exact Finset.mem_image.mpr ⟨j - 1, Finset.mem_range.mpr (by omega), hprev_eq.symm⟩
      have hcard_eq : (compSet q).card = m := by
        rw [← hOrb_eq, Finset.card_image_of_injOn hv_inj, Finset.card_range]
      have hstep_all : ∀ j, j + 1 < m → stepP k hk (v j) (v (j + 1)) := by
        intro j _
        simp only [v, Function.iterate_succ_apply']
        exact hf_step (f^[j] x0)
      have hstep_wrap : stepP k hk (v (m - 1)) (v 0) := by
        have h1 := hf_step (f^[m - 1] x0)
        have h2 : f (f^[m - 1] x0) = x0 := by
          have : f (f^[m - 1] x0) = f^[m - 1 + 1] x0 := (Function.iterate_succ_apply' f _ x0).symm
          rw [this, show m - 1 + 1 = m by omega, hm_spec.2]
        rw [h2] at h1
        exact h1
      have hm3 : 3 ≤ m := by
        by_contra hlt3
        have hcases : m = 1 ∨ m = 2 := by omega
        rcases hcases with hm1 | hm2
        · rw [hm1] at hstep_wrap
          exact stepP_irrefl k hk hk9 (v 0) hstep_wrap
        · rw [hm2] at hstep_wrap
          exact stepP_asym k hk hk9 (v 0) (v 1) (hstep_all 0 (by omega)) hstep_wrap
      exact ⟨m, v, hm3, hcard_eq, hOrb_eq.symm, hstep_all, Or.inl hstep_wrap⟩
    · push Not at hpred
      rcases hpred with ⟨v0, hv0C, hv0_nopred⟩
      let nextOpt : Fin k → Option (Fin k) := fun x =>
        if ix k hk (x.val + 3) ∈ compSet q then some (ix k hk (x.val + 3))
        else if ix k hk (x.val + 4) ∈ compSet q then some (ix k hk (x.val + 4))
        else none
      have hnextOpt_some : ∀ x ∈ compSet q, ∀ y : Fin k,
          nextOpt x = some y ↔ y ∈ compSet q ∧ stepP k hk x y := by
        intro x _ y
        simp only [nextOpt]
        by_cases h3 : ix k hk (x.val + 3) ∈ compSet q
        · simp only [h3, ↓reduceIte, Option.some.injEq]
          constructor
          · rintro rfl; exact ⟨h3, Or.inl rfl⟩
          · rintro ⟨hyC, hst⟩
            exact stepP_unique_next k hk P hP x _ y (hCsub h3) (hCsub hyC) (Or.inl rfl) hst
        · simp only [h3, ↓reduceIte]
          by_cases h4 : ix k hk (x.val + 4) ∈ compSet q
          · simp only [h4, ↓reduceIte, Option.some.injEq]
            constructor
            · rintro rfl; exact ⟨h4, Or.inr rfl⟩
            · rintro ⟨hyC, hst⟩
              exact stepP_unique_next k hk P hP x _ y (hCsub h4) (hCsub hyC) (Or.inr rfl) hst
          · simp only [h4, ↓reduceIte, reduceCtorEq, false_iff, not_and]
            rintro hyC (rfl | rfl)
            · exact h3 hyC
            · exact h4 hyC
      let v : ℕ → Fin k := fun j => Nat.rec v0 (fun _ cur => (nextOpt cur).getD cur) j
      have hv_mem : ∀ j, v j ∈ compSet q := by
        intro j
        induction j with
        | zero => exact hv0C
        | succ j ih =>
          simp only [v]
          cases hopt : nextOpt (v j) with
          | none => exact ih
          | some y => exact ((hnextOpt_some (v j) ih y).mp hopt).1
      have hstop_ex : ∃ j : ℕ, nextOpt (v j) = none := by
        by_contra hno
        push Not at hno
        have hv_step_all : ∀ j, stepP k hk (v j) (v (j + 1)) := by
          intro j
          obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hno j)
          have hvy : v (j + 1) = y := by simp only [v, hy, Option.getD_some]
          rw [hvy]
          exact ((hnextOpt_some (v j) (hv_mem j) y).mp hy).2
        have hrep : ∃ b : ℕ, ∃ a < b, v a = v b := by
          obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite v
          rcases lt_or_gt_of_ne hab with hlt | hgt
          · exact ⟨b, a, hlt, heq⟩
          · exact ⟨a, b, hgt, heq.symm⟩
        let _ : DecidablePred (fun b : ℕ => ∃ a < b, v a = v b) := Classical.decPred _
        let b := Nat.find hrep
        rcases Nat.find_spec hrep with ⟨a, hab, hvab⟩
        by_cases ha0 : a = 0
        · subst ha0
          have hst : stepP k hk (v (b - 1)) v0 := by
            have h1 := hv_step_all (b - 1)
            rw [show b - 1 + 1 = b by omega, ← hvab] at h1
            exact h1
          exact hv0_nopred (v (b - 1)) (hv_mem _) hst
        · have hprev_eq : v (a - 1) = v (b - 1) := by
            have h1 := hv_step_all (a - 1)
            have h2 := hv_step_all (b - 1)
            rw [show a - 1 + 1 = a by omega] at h1
            rw [show b - 1 + 1 = b by omega, ← hvab] at h2
            exact stepP_unique_prev k hk hk9 P hP _ _ (v a)
              (hCsub (hv_mem _)) (hCsub (hv_mem _)) h1 h2
          exact Nat.find_min hrep (by omega : b - 1 < b) ⟨a - 1, by omega, hprev_eq⟩
      let m0 : ℕ := Nat.find hstop_ex
      let n : ℕ := m0 + 1
      have hm0_stop : nextOpt (v m0) = none := Nat.find_spec hstop_ex
      have hv_step_lt : ∀ j, j + 1 < n → stepP k hk (v j) (v (j + 1)) := by
        intro j hj
        have hne : nextOpt (v j) ≠ none := Nat.find_min hstop_ex (by omega)
        obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hne
        have hvy : v (j + 1) = y := by simp only [v, hy, Option.getD_some]
        rw [hvy]
        exact ((hnextOpt_some (v j) (hv_mem j) y).mp hy).2
      have hv_nosucc_end : ∀ y ∈ compSet q, ¬ stepP k hk (v (n - 1)) y := by
        intro y hy hst
        have h1 : nextOpt (v m0) = some y := (hnextOpt_some (v m0) (hv_mem m0) y).mpr ⟨hy, hst⟩
        rw [hm0_stop] at h1
        cases h1
      have hv_inj : Set.InjOn v (Finset.range n) := by
        by_contra hnot
        have hex : ∃ b : ℕ, b < n ∧ ∃ a < b, v a = v b := by
          unfold Set.InjOn at hnot
          push Not at hnot
          rcases hnot with ⟨a, ha, b, hb, hvab, hab⟩
          have ha' := Finset.mem_range.mp ha
          have hb' := Finset.mem_range.mp hb
          rcases lt_or_gt_of_ne hab with hlt | hgt
          · exact ⟨b, hb', a, hlt, hvab⟩
          · exact ⟨a, ha', b, hgt, hvab.symm⟩
        let _ : DecidablePred (fun b : ℕ => b < n ∧ ∃ a < b, v a = v b) := Classical.decPred _
        let b := Nat.find hex
        rcases Nat.find_spec hex with ⟨hbn, a, hab, hvab⟩
        by_cases ha0 : a = 0
        · subst ha0
          have hst : stepP k hk (v (b - 1)) v0 := by
            have h1 := hv_step_lt (b - 1) (by omega)
            rw [show b - 1 + 1 = b by omega, ← hvab] at h1
            exact h1
          exact hv0_nopred (v (b - 1)) (hv_mem _) hst
        · have hprev_eq : v (a - 1) = v (b - 1) := by
            have h1 := hv_step_lt (a - 1) (by omega)
            have h2 := hv_step_lt (b - 1) (by omega)
            rw [show a - 1 + 1 = a by omega] at h1
            rw [show b - 1 + 1 = b by omega, ← hvab] at h2
            exact stepP_unique_prev k hk hk9 P hP _ _ (v a)
              (hCsub (hv_mem _)) (hCsub (hv_mem _)) h1 h2
          exact Nat.find_min hex (by omega : b - 1 < b) ⟨by omega, a - 1, by omega, hprev_eq⟩
      let Path : Finset (Fin k) := (Finset.range n).image v
      have hPath_sub : Path ⊆ compSet q := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
        exact hv_mem j
      have hPath_eq : Path = compSet q := by
        apply hC_closed Path hPath_sub ⟨v 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩
        intro x hx y hy hadj
        rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
        have hjn : j < n := Finset.mem_range.mp hj
        rcases hAdj_step _ _ hadj with hxy | hyx
        · dsimp only at hxy
          have hj1 : j + 1 < n := by
            by_contra hge
            have hjeq : j = n - 1 := by omega
            rw [hjeq] at hxy
            exact hv_nosucc_end y hy hxy
          have hy_eq : y = v (j + 1) :=
            stepP_unique_next k hk P hP (v j) y (v (j + 1)) (hCsub hy) (hCsub (hv_mem (j + 1)))
              hxy (hv_step_lt j hj1)
          exact Finset.mem_image.mpr ⟨j + 1, Finset.mem_range.mpr hj1, hy_eq.symm⟩
        · dsimp only at hyx
          have hj0 : 0 < j := by
            by_contra hle
            have hjeq : j = 0 := by omega
            rw [hjeq] at hyx
            exact hv0_nopred y hy hyx
          have hy_eq : y = v (j - 1) := by
            have h1 := hv_step_lt (j - 1) (by omega)
            rw [show j - 1 + 1 = j by omega] at h1
            exact stepP_unique_prev k hk hk9 P hP y (v (j - 1)) (v j)
              (hCsub hy) (hCsub (hv_mem (j - 1))) hyx h1
          exact Finset.mem_image.mpr ⟨j - 1, Finset.mem_range.mpr (by omega), hy_eq.symm⟩
      have hcard_eq : (compSet q).card = n := by
        rw [← hPath_eq, Finset.card_image_of_injOn hv_inj, Finset.card_range]
      have hslot3_zero : ∀ i : P, i.1 ∈ compSet q → r i (ix k hk (i.1.val + 3)) = 0 := by
        intro i hi
        rcases zmod2_cases (r i (ix k hk (i.1.val + 3))) with h0 | h1
        · exact h0
        · exfalso
          apply hC_unpin i hi
          refine ⟨ix k hk (i.1.val + 3), h1, fun j hji => ?_⟩
          apply (hr_kill j).2.1
          exact slot3_private k hk hk9 P hP i.2 j.2 (fun h => hji (Subtype.ext h.symm))
      have hslot15_eq : ∀ i : P, i.1 ∈ compSet q →
          r i (ix k hk (i.1.val + 1)) = r i (ix k hk (i.1.val + 5)) := by
        intro i hi
        have hpar := (hr_kill i).2.2
        rw [hslot3_zero i hi, add_zero] at hpar
        exact (zmod2_eq_iff_add_eq_zero _ _).mpr hpar
      let p0 : P := ⟨v 0, hCsub (hv_mem 0)⟩
      let pend : P := ⟨v (n - 1), hCsub (hv_mem (n - 1))⟩
      have hp0_1 : r p0 (ix k hk (p0.1.val + 1)) = 0 := by
        rcases zmod2_cases (r p0 (ix k hk (p0.1.val + 1))) with h0 | h1
        · exact h0
        · exfalso
          apply hC_unpin p0 (hv_mem 0)
          refine ⟨ix k hk (p0.1.val + 1), h1, fun j hjp => ?_⟩
          rcases zmod2_cases (r j (ix k hk (p0.1.val + 1))) with hj0 | hj1
          · exact hj0
          · exfalso
            have hadj : H.Adj p0 j := ⟨hjp.symm, ix k hk (p0.1.val + 1), h1, hj1⟩
            have hjC : j.1 ∈ compSet q := (hCmem j).mpr
              ((SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hadj)).symm.trans ((hCmem p0).mp (hv_mem 0)))
            have htj : ix k hk (p0.1.val + 1) ∈ tapSet k hk j.1 := by
              by_contra hnt; rw [(hr_kill j).2.1 _ hnt] at hj1; exact zero_ne_one hj1
            rcases (mem_tapSet_iff k hk j.1 _).mp htj with ⟨b, hb, heq⟩
            have hcases := tap_inter_cases k hk hk9 P hP p0.2 j.2 (fun h => hjp (Subtype.ext h.symm))
              (a := 0) (b := b) (by omega) hb heq
            rcases hcases with ⟨_, h3 | h4⟩ | ⟨_, h4, _⟩ | ⟨h3, _⟩ | ⟨h4, _⟩
            · omega
            · omega
            · omega
            · exact hv0_nopred j.1 hjC (Or.inl h3)
            · exact hv0_nopred j.1 hjC (Or.inr h4)
      have hp0_2 : r p0 (ix k hk (p0.1.val + 2)) = 0 := by
        rcases zmod2_cases (r p0 (ix k hk (p0.1.val + 2))) with h0 | h1
        · exact h0
        · exfalso
          apply hC_unpin p0 (hv_mem 0)
          refine ⟨ix k hk (p0.1.val + 2), h1, fun j hjp => ?_⟩
          rcases zmod2_cases (r j (ix k hk (p0.1.val + 2))) with hj0 | hj1
          · exact hj0
          · exfalso
            have hadj : H.Adj p0 j := ⟨hjp.symm, ix k hk (p0.1.val + 2), h1, hj1⟩
            have hjC : j.1 ∈ compSet q := (hCmem j).mpr
              ((SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hadj)).symm.trans ((hCmem p0).mp (hv_mem 0)))
            have htj : ix k hk (p0.1.val + 2) ∈ tapSet k hk j.1 := by
              by_contra hnt; rw [(hr_kill j).2.1 _ hnt] at hj1; exact zero_ne_one hj1
            rcases (mem_tapSet_iff k hk j.1 _).mp htj with ⟨b, hb, heq⟩
            have hcases := tap_inter_cases k hk hk9 P hP p0.2 j.2 (fun h => hjp (Subtype.ext h.symm))
              (a := 1) (b := b) (by omega) hb heq
            rcases hcases with ⟨_, h3 | h4⟩ | ⟨_, h4, _⟩ | ⟨h3, _⟩ | ⟨_, h0, _⟩
            · omega
            · omega
            · omega
            · exact hv0_nopred j.1 hjC (Or.inl h3)
            · omega
      have hp0_4 : r p0 (ix k hk (p0.1.val + 4)) = 1 := by
        rcases zmod2_cases (r p0 (ix k hk (p0.1.val + 4))) with h0 | h1
        · exfalso
          apply (hr_kill p0).1
          funext t
          by_cases ht : t ∈ tapSet k hk p0.1
          · rcases (mem_tapSet_iff k hk p0.1 t).mp ht with ⟨a, ha, rfl⟩
            have hp0_3 := hslot3_zero p0 (hv_mem 0)
            have hp0_5 : r p0 (ix k hk (p0.1.val + 5)) = 0 := by
              rw [← hslot15_eq p0 (hv_mem 0), hp0_1]
            interval_cases a <;> assumption
          · exact (hr_kill p0).2.1 t ht
        · exact h1
      have hstart_step : 1 < n ∧ v 1 = ix k hk ((v 0).val + 3) ∧
          r ⟨v 1, hCsub (hv_mem 1)⟩ (ix k hk ((v 1).val + 1)) = 1 := by
        have hnotpin := hC_unpin p0 (hv_mem 0)
        have hexj : ∃ j : P, j ≠ p0 ∧ r j (ix k hk (p0.1.val + 4)) = 1 := by
          by_contra hno
          push Not at hno
          apply hnotpin
          refine ⟨ix k hk (p0.1.val + 4), hp0_4, fun j hjp => ?_⟩
          rcases zmod2_cases (r j (ix k hk (p0.1.val + 4))) with h0 | h1
          · exact h0
          · exact absurd h1 (hno j hjp)
        rcases hexj with ⟨j, hjp, hrj4⟩
        have hadj : H.Adj p0 j := ⟨hjp.symm, ix k hk (p0.1.val + 4), hp0_4, hrj4⟩
        have hjC : j.1 ∈ compSet q := (hCmem j).mpr
          ((SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hadj)).symm.trans ((hCmem p0).mp (hv_mem 0)))
        have htj : ix k hk (p0.1.val + 4) ∈ tapSet k hk j.1 := by
          by_contra hnt; rw [(hr_kill j).2.1 _ hnt] at hrj4; exact zero_ne_one hrj4
        rcases (mem_tapSet_iff k hk j.1 _).mp htj with ⟨b, hb, heq⟩
        have hcases := tap_inter_cases k hk hk9 P hP p0.2 j.2 (fun h => hjp (Subtype.ext h.symm))
          (a := 3) (b := b) (by omega) hb heq
        have hj3 : j.1 = ix k hk ((v 0).val + 3) := by
          rcases hcases with ⟨h3, _⟩ | ⟨_, h4, _⟩ | ⟨_, h0 | h1⟩ | ⟨_, h0, _⟩
          · exact h3
          · omega
          · omega
          · omega
          · omega
        have hn2 : 1 < n := by
          by_contra hle
          have hn1 : n = 1 := by omega
          have h0 : n - 1 = 0 := by omega
          exact hv_nosucc_end j.1 hjC (by rw [h0]; exact Or.inl hj3)
        have hv1eq : v 1 = j.1 :=
          stepP_unique_next k hk P hP (v 0) (v 1) j.1 (hCsub (hv_mem 1)) j.2
            (hv_step_lt 0 hn2) (Or.inl hj3)
        have hrj1 : r ⟨v 1, hCsub (hv_mem 1)⟩ (ix k hk ((v 1).val + 1)) = 1 := by
          have hsubeq : (⟨v 1, hCsub (hv_mem 1)⟩ : P) = j := Subtype.ext hv1eq
          rw [hsubeq, hv1eq]
          have hidx : ix k hk (j.1.val + 1) = ix k hk (p0.1.val + 4) := by
            rw [hj3, ix_add_left]
          rw [hidx]; exact hrj4
        exact ⟨hn2, hv1eq.trans hj3, hrj1⟩
      have hpend_5 : r pend (ix k hk (pend.1.val + 5)) = 0 := by
        rcases zmod2_cases (r pend (ix k hk (pend.1.val + 5))) with h0 | h1
        · exact h0
        · exfalso
          apply hC_unpin pend (hv_mem (n - 1))
          refine ⟨ix k hk (pend.1.val + 5), h1, fun j hjp => ?_⟩
          rcases zmod2_cases (r j (ix k hk (pend.1.val + 5))) with hj0 | hj1
          · exact hj0
          · exfalso
            have hadj : H.Adj pend j := ⟨hjp.symm, ix k hk (pend.1.val + 5), h1, hj1⟩
            have hjC : j.1 ∈ compSet q := (hCmem j).mpr
              ((SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hadj)).symm.trans ((hCmem pend).mp (hv_mem (n - 1))))
            have htj : ix k hk (pend.1.val + 5) ∈ tapSet k hk j.1 := by
              by_contra hnt; rw [(hr_kill j).2.1 _ hnt] at hj1; exact zero_ne_one hj1
            rcases (mem_tapSet_iff k hk j.1 _).mp htj with ⟨b, hb, heq⟩
            have hcases := tap_inter_cases k hk hk9 P hP pend.2 j.2 (fun h => hjp (Subtype.ext h.symm))
              (a := 4) (b := b) (by omega) hb heq
            rcases hcases with ⟨h3, _⟩ | ⟨h4, _⟩ | ⟨_, h0 | h1⟩ | ⟨_, h0, _⟩
            · exact hv_nosucc_end j.1 hjC (Or.inl h3)
            · exact hv_nosucc_end j.1 hjC (Or.inr h4)
            · omega
            · omega
            · omega
      have hpend_4 : r pend (ix k hk (pend.1.val + 4)) = 0 := by
        rcases zmod2_cases (r pend (ix k hk (pend.1.val + 4))) with h0 | h1
        · exact h0
        · exfalso
          apply hC_unpin pend (hv_mem (n - 1))
          refine ⟨ix k hk (pend.1.val + 4), h1, fun j hjp => ?_⟩
          rcases zmod2_cases (r j (ix k hk (pend.1.val + 4))) with hj0 | hj1
          · exact hj0
          · exfalso
            have hadj : H.Adj pend j := ⟨hjp.symm, ix k hk (pend.1.val + 4), h1, hj1⟩
            have hjC : j.1 ∈ compSet q := (hCmem j).mpr
              ((SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hadj)).symm.trans ((hCmem pend).mp (hv_mem (n - 1))))
            have htj : ix k hk (pend.1.val + 4) ∈ tapSet k hk j.1 := by
              by_contra hnt; rw [(hr_kill j).2.1 _ hnt] at hj1; exact zero_ne_one hj1
            rcases (mem_tapSet_iff k hk j.1 _).mp htj with ⟨b, hb, heq⟩
            have hcases := tap_inter_cases k hk hk9 P hP pend.2 j.2 (fun h => hjp (Subtype.ext h.symm))
              (a := 3) (b := b) (by omega) hb heq
            rcases hcases with ⟨h3, _⟩ | ⟨_, h4, _⟩ | ⟨_, h0 | h1⟩ | ⟨_, h0, _⟩
            · exact hv_nosucc_end j.1 hjC (Or.inl h3)
            · omega
            · omega
            · omega
            · omega
      have hpend_1 : r pend (ix k hk (pend.1.val + 1)) = 0 := by
        rw [hslot15_eq pend (hv_mem (n - 1)), hpend_5]
      have hn3 : 3 ≤ n := by
        by_contra hlt3
        have hn2 : n = 2 := by omega
        have hpeq : (⟨v 1, hCsub (hv_mem 1)⟩ : P) = pend := by
          apply Subtype.ext; simp [pend, hn2]
        have hvp : v 1 = pend.1 := by simp [pend, hn2]
        have h1 := hstart_step.2.2
        rw [hpeq, hvp, hpend_1] at h1
        exact zero_ne_one h1
      have hpend_2 : r pend (ix k hk (pend.1.val + 2)) = 1 := by
        rcases zmod2_cases (r pend (ix k hk (pend.1.val + 2))) with h0 | h1
        · exfalso
          apply (hr_kill pend).1
          funext t
          by_cases ht : t ∈ tapSet k hk pend.1
          · rcases (mem_tapSet_iff k hk pend.1 t).mp ht with ⟨a, ha, rfl⟩
            have hpend_3 := hslot3_zero pend (hv_mem (n - 1))
            interval_cases a <;> assumption
          · exact (hr_kill pend).2.1 t ht
        · exact h1
      have hend_step : v (n - 1) = ix k hk ((v (n - 2)).val + 3) := by
        have hnotpin := hC_unpin pend (hv_mem (n - 1))
        have hexj : ∃ j : P, j ≠ pend ∧ r j (ix k hk (pend.1.val + 2)) = 1 := by
          by_contra hno
          push Not at hno
          apply hnotpin
          refine ⟨ix k hk (pend.1.val + 2), hpend_2, fun j hjp => ?_⟩
          rcases zmod2_cases (r j (ix k hk (pend.1.val + 2))) with h0 | h1
          · exact h0
          · exact absurd h1 (hno j hjp)
        rcases hexj with ⟨j, hjp, hrj2⟩
        have hadj : H.Adj pend j := ⟨hjp.symm, ix k hk (pend.1.val + 2), hpend_2, hrj2⟩
        have hjC : j.1 ∈ compSet q := (hCmem j).mpr
          ((SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hadj)).symm.trans ((hCmem pend).mp (hv_mem (n - 1))))
        have htj : ix k hk (pend.1.val + 2) ∈ tapSet k hk j.1 := by
          by_contra hnt; rw [(hr_kill j).2.1 _ hnt] at hrj2; exact zero_ne_one hrj2
        rcases (mem_tapSet_iff k hk j.1 _).mp htj with ⟨b, hb, heq⟩
        have hcases := tap_inter_cases k hk hk9 P hP pend.2 j.2 (fun h => hjp (Subtype.ext h.symm))
          (a := 1) (b := b) (by omega) hb heq
        have hj3 : pend.1 = ix k hk (j.1.val + 3) := by
          rcases hcases with ⟨_, h3 | h4⟩ | ⟨_, h4, _⟩ | ⟨h3, _⟩ | ⟨_, h0, _⟩
          · omega
          · omega
          · omega
          · exact h3
          · omega
        have hst_prev : stepP k hk (v (n - 2)) (v (n - 1)) := by
          have h1 := hv_step_lt (n - 2) (by omega)
          rwa [show n - 2 + 1 = n - 1 by omega] at h1
        have hjeq : j.1 = v (n - 2) :=
          stepP_unique_prev k hk hk9 P hP j.1 (v (n - 2)) (v (n - 1)) j.2 (hCsub (hv_mem _))
            (Or.inl hj3) hst_prev
        rw [← hjeq]; exact hj3
      exact ⟨n, v, hn3, hcard_eq, hPath_eq.symm, hv_step_lt, Or.inr ⟨hstart_step.2.1, hend_step⟩⟩
  · intro C hC E hE hCE
    rcases Finset.mem_image.mp hC with ⟨q1, _, rfl⟩
    rcases Finset.mem_image.mp hE with ⟨q2, _, rfl⟩
    have hqne : q1 ≠ q2 := fun h => hCE (congrArg compSet h)
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨i1, hi1, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨i2, hi2, heq⟩
    have hi12 : i2 = i1 := Subtype.ext heq
    subst hi12
    have h1 := (Finset.mem_filter.mp hi1).2
    have h2 := (Finset.mem_filter.mp hi2).2
    exact hqne (h1.symm.trans h2)
  · rw [hfam_card, ← hMdep_finrank]
    exact hP_card_bound

end Direction2

end MainProof

end PEqualNP.Outside.L_meta_29945_aux

theorem PEqualNP.Outside.L_meta_29945 : (
let fits := fun (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → ZMod 2) =>
  let F := ZMod 2
  let W := Fin k → F
  let D := W →ₗ[F] F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + g)) + x (ix (i.val + k - g % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  let gap := fun b : Bool => if b then 2 else (1 : ℕ)
  let spin := fun b : Bool => if b then 3 else (1 : ℕ)
  let diff := fun (f : W → F) (u x : W) => f (x + u) - f x
  let fourth := fun (f : W → F) (v : Fin 4 → W) => (List.ofFn v).foldl diff f
  let cubic := fun (f : W → F) => ∀ v x, fourth f v x = 0
  let out := fun (x : W) (b : Bool) =>
    let z := mix (gap b) (rot (spin b) x + name b)
    let y := step z + rot (if b then 4 else 0) x + c₁ b
    step (mix (gap b) y) + rot (if b then 7 else 2) x + c₂ b
  let run := fun (ask : Fin d → ℕ → D) (x : W) =>
    (List.finRange d).foldl (fun h j =>
      2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
  ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin k → W → F),
    (∀ h b i, cubic (readout h b i)) ∧
    ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
      out x b i = readout (run ask x) b i x
∀ (k : ℕ) (hk : 0 < k), 9 ≤ k →
  ∀ (P : Finset (Fin k)) (d : ℕ) (name c₁ c₂ : Bool → Fin k → ZMod 2),
    let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
    let mark := fun i : Fin k => (decide (i ∈ P), false)
    let step := fun (i j : Fin k) => j = ix (i.val + 3) ∨ j = ix (i.val + 4)
    let chain := fun C : Finset (Fin k) =>
      ∃ (n : ℕ) (v : ℕ → Fin k), 3 ≤ n ∧ C.card = n ∧ C = (Finset.range n).image v ∧
        (∀ j : ℕ, j + 1 < n → step (v j) (v (j + 1))) ∧
        (step (v (n - 1)) (v 0) ∨
          (v 1 = ix ((v 0).val + 3) ∧ v (n - 1) = ix ((v (n - 2)).val + 3)))
    let covers := fun budget : ℕ =>
      ∃ family : Finset (Finset (Fin k)),
        (∀ C ∈ family, C ⊆ P ∧ chain C) ∧
        (∀ C ∈ family, ∀ E ∈ family, C ≠ E → Disjoint C E) ∧
        P.card ≤ budget + family.card
    let taps := P.biUnion (fun i =>
      (Finset.range 5).image (fun j => ix (i.val + j + 1)))
    let missed := ((Finset.univ : Finset (Fin k)) \ taps).image (fun i => i.val % 3)
    let h := if k % 3 = 0 then 2 - missed.card else 0
    (∀ i ∈ P, ix (i.val + 1) ∉ P ∧ ix (i.val + 2) ∉ P) →
      (covers d → fits k hk mark d name c₁ c₂) ∧
      (fits k hk mark d name c₁ c₂ → covers (d + h))) := by
  dsimp only
  intro k hk hk9 P d name c₁ c₂ hP
  constructor
  · rintro ⟨family, hfam, hdisj, hbudget⟩
    obtain ⟨ask, readout, hcubic, hagree⟩ :=
      PEqualNP.Outside.L_meta_29945_aux.covers_imp_fits k hk hk9 P d name c₁ c₂
        family hfam hdisj hbudget
    refine ⟨ask, readout, hcubic, ?_⟩
    intro x b i hm
    cases b
    · exact hagree x i (by simpa using hm)
    · simp at hm
  · rintro ⟨ask, readout, hcubic, hagree⟩
    exact PEqualNP.Outside.L_meta_29945_aux.fits_imp_covers k hk hk9 P d name c₁ c₂
      hP ask readout hcubic (fun x i hi => hagree x false i (by simp [hi]))

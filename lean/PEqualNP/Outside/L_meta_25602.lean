import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25602_aux

abbrev W (k : Nat) := Fin k → ZMod 2

def ix {k : Nat} (hk : 0 < k) (a : Nat) : Fin k :=
  ⟨a % k, Nat.mod_lt _ hk⟩

lemma ix_val {k : Nat} (hk : 0 < k) (a : Nat) : (ix hk a).val = a % k := rfl

lemma ix_val_self {k : Nat} (hk : 0 < k) (i : Fin k) : ix hk i.val = i := by
  ext
  exact Nat.mod_eq_of_lt i.isLt

lemma ix_mod {k : Nat} (hk : 0 < k) (a : Nat) : ix hk (a % k) = ix hk a := by
  ext
  exact Nat.mod_mod a k

lemma ix_add_mod {k : Nat} (hk : 0 < k) (a b : Nat) : ix hk (a % k + b) = ix hk (a + b) := by
  ext
  simp [ix, Nat.add_mod]

lemma ix_add_mul_left {k : Nat} (hk : 0 < k) (a q : Nat) : ix hk (a + q * k) = ix hk a := by
  ext
  simp [ix, Nat.add_mul_mod_self_right]

lemma ix_add_sub_cancel {k : Nat} (hk : 0 < k) (a r : Nat) (hr : r < k) :
    ix hk ((a + r) % k + k - r) = ix hk a := by
  ext
  dsimp only [ix]
  have h1 : (a + r) % k + k - r = (a + r) % k + (k - r) := by omega
  rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h2 : a + r + (k - r) = a + k := by omega
  rw [h2, Nat.add_mod_right]

lemma ix_sub_add_cancel {k : Nat} (hk : 0 < k) (a r : Nat) (hr : r < k) :
    ix hk ((a + k - r) % k + r) = ix hk a := by
  ext
  dsimp only [ix]
  have h1 : a + k - r = a + (k - r) := by omega
  rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h2 : a + (k - r) + r = a + k := by omega
  rw [h2, Nat.add_mod_right]

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

lemma zmod2_sub_eq_add (x y : ZMod 2) : x - y = x + y := by
  fin_cases x <;> fin_cases y <;> rfl

lemma zmod2_add_self_self (x : ZMod 2) : x + x + x = x := by
  fin_cases x <;> rfl

lemma zmod2_mul_sub_self (c : ZMod 2) : c * (1 - c) = 0 := by
  fin_cases c <;> rfl

def rotLin {k : Nat} (hk : 0 < k) (q : Nat) : W k →ₗ[ZMod 2] W k where
  toFun v j := v (ix hk (j.val + k - q % k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rotEquiv {k : Nat} (hk : 0 < k) (q : Nat) : W k ≃ₗ[ZMod 2] W k :=
  LinearEquiv.ofLinearMap
    (rotLin hk q)
    { toFun := fun v j => v (ix hk (j.val + q % k))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (by
      apply LinearMap.ext
      intro v
      ext j
      change v (ix hk ((j.val + k - q % k) % k + q % k)) = v j
      rw [ix_sub_add_cancel hk j.val (q % k) (Nat.mod_lt q hk), ix_val_self])
    (by
      apply LinearMap.ext
      intro v
      ext j
      change v (ix hk ((j.val + q % k) % k + k - q % k)) = v j
      rw [ix_add_sub_cancel hk j.val (q % k) (Nat.mod_lt q hk), ix_val_self])

def mixLin {k : Nat} (hk : 0 < k) (d : Nat) : W k →ₗ[ZMod 2] W k where
  toFun z i := z i + z (ix hk (i.val + d)) + z (ix hk (i.val + k - d % k))
  map_add' u v := by
    ext i
    dsimp only [Pi.add_apply]
    ring
  map_smul' c u := by
    ext i
    dsimp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma mixLin_injective {k : Nat} (hk : 0 < k) (h5 : 5 ≤ k) (h3 : k % 3 ≠ 0)
    {d : Nat} (hd : d = 1 ∨ d = 2) : Function.Injective (mixLin hk d) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hdk : d < k := by omega
  have hdmod : d % k = d := Nat.mod_eq_of_lt hdk
  have htri : ∀ m : Nat, z (ix hk m) + z (ix hk (m + d)) + z (ix hk (m + 2 * d)) = 0 := by
    intro m
    have hi := congr_fun hz (ix hk (m + d))
    dsimp only [mixLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hi
    have h1 : ix hk ((ix hk (m + d)).val + d) = ix hk (m + 2 * d) := by
      rw [ix_val, ix_add_mod]
      congr 1
      omega
    have h2 : ix hk ((ix hk (m + d)).val + k - d % k) = ix hk m := by
      rw [ix_val, hdmod]
      exact ix_add_sub_cancel hk m d hdk
    rw [h1, h2] at hi
    calc
      z (ix hk m) + z (ix hk (m + d)) + z (ix hk (m + 2 * d))
          = z (ix hk (m + d)) + z (ix hk (m + 2 * d)) + z (ix hk m) := by ring
      _ = 0 := hi
  have hper3 : ∀ m : Nat, z (ix hk (m + 3 * d)) = z (ix hk m) := by
    intro m
    have h1 := htri m
    have h2 := htri (m + d)
    have h2' : z (ix hk (m + d)) + z (ix hk (m + 2 * d)) + z (ix hk (m + 3 * d)) = 0 := by
      have ha : m + d + d = m + 2 * d := by omega
      have hb : m + d + 2 * d = m + 3 * d := by omega
      rw [ha, hb] at h2
      exact h2
    have hsum : (z (ix hk m) + z (ix hk (m + d)) + z (ix hk (m + 2 * d))) +
        (z (ix hk (m + d)) + z (ix hk (m + 2 * d)) + z (ix hk (m + 3 * d))) = 0 := by
      rw [h1, h2', add_zero]
    have hsimp : z (ix hk m) + z (ix hk (m + 3 * d)) = 0 := by
      calc
        z (ix hk m) + z (ix hk (m + 3 * d))
            = (z (ix hk m) + z (ix hk (m + d)) + z (ix hk (m + 2 * d))) +
              (z (ix hk (m + d)) + z (ix hk (m + 2 * d)) + z (ix hk (m + 3 * d))) -
              (z (ix hk (m + d)) + z (ix hk (m + d))) -
              (z (ix hk (m + 2 * d)) + z (ix hk (m + 2 * d))) := by ring
        _ = 0 - 0 - 0 := by rw [hsum, zmod2_add_self, zmod2_add_self]
        _ = 0 := by ring
    calc
      z (ix hk (m + 3 * d)) = z (ix hk m) + (z (ix hk m) + z (ix hk (m + 3 * d))) := by
        rw [← add_assoc, zmod2_add_self, zero_add]
      _ = z (ix hk m) := by rw [hsimp, add_zero]
  have hper3q : ∀ (q m : Nat), z (ix hk (m + 3 * q * d)) = z (ix hk m) := by
    intro q
    induction q with
    | zero => intro m; simp
    | succ q ih =>
      intro m
      have harg : m + 3 * (q + 1) * d = (m + 3 * q * d) + 3 * d := by ring
      rw [harg, hper3, ih]
  have hper1 : ∀ m : Nat, z (ix hk (m + d)) = z (ix hk m) := by
    intro m
    have hmod3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod3 with h1 | h2
    · have hk_eq : 3 * (k / 3) + 1 = k := by omega
      have harg : (m + d) + 3 * (k / 3) * d = m + d * k := by
        calc
          (m + d) + 3 * (k / 3) * d = m + (3 * (k / 3) + 1) * d := by ring
          _ = m + k * d := by rw [hk_eq]
          _ = m + d * k := by ring
      rw [← hper3q (k / 3) (m + d), harg, ix_add_mul_left]
    · have hk_eq : 3 * (2 * (k / 3) + 1) + 1 = 2 * k := by omega
      have harg : (m + d) + 3 * (2 * (k / 3) + 1) * d = m + (2 * d) * k := by
        calc
          (m + d) + 3 * (2 * (k / 3) + 1) * d = m + (3 * (2 * (k / 3) + 1) + 1) * d := by ring
          _ = m + (2 * k) * d := by rw [hk_eq]
          _ = m + (2 * d) * k := by ring
      rw [← hper3q (2 * (k / 3) + 1) (m + d), harg, ix_add_mul_left]
  ext i
  have h0 := htri i.val
  have h2d : z (ix hk (i.val + 2 * d)) = z (ix hk i.val) := by
    have harg : i.val + 2 * d = (i.val + d) + d := by omega
    rw [harg, hper1, hper1]
  rw [hper1, h2d, zmod2_add_self_self, ix_val_self] at h0
  exact h0

noncomputable def mixEquiv {k : Nat} (hk : 0 < k) (h5 : 5 ≤ k) (h3 : k % 3 ≠ 0)
    {d : Nat} (hd : d = 1 ∨ d = 2) : W k ≃ₗ[ZMod 2] W k :=
  LinearEquiv.ofBijective (mixLin hk d)
    ((Finite.injective_iff_bijective).mp (mixLin_injective hk h5 h3 hd))

noncomputable def roundEquiv {k : Nat} (hk : 0 < k) (h5 : 5 ≤ k) (h3 : k % 3 ≠ 0)
    {d : Nat} (hd : d = 1 ∨ d = 2) (s : Nat) : W k ≃ₗ[ZMod 2] W k :=
  (rotEquiv hk s).trans (mixEquiv hk h5 h3 hd)

def crossEdge {k : Nat} (hk : 0 < k) (Q : W k →ₗ[ZMod 2] W k) (i : Fin k) :
    W k × W k → ZMod 2 :=
  fun p =>
    Q p.1 i * (p.2 - Q p.2) (ix hk (i.val + 1)) +
    Q p.1 (ix hk (i.val + 1)) * (p.2 - Q p.2) i

def phiMap {k : Nat} (hk : 0 < k) (Q : W k →ₗ[ZMod 2] W k) :
    W k →ₗ[ZMod 2] (W k × W k → ZMod 2) where
  toFun mask p := ∑ j : Fin k, mask j * crossEdge hk Q (ix hk (j.val + 1)) p
  map_add' m1 m2 := by
    ext p
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c m := by
    ext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]

lemma quad_second_diff (a1 b1 g1 a2 b2 g2 : ZMod 2) :
    (1 + (a1 + b1 + g1)) * (a2 + b2 + g2) +
    (1 + (a1 + g1)) * (a2 + g2) +
    (1 + (b1 + g1)) * (b2 + g2) +
    (1 + g1) * g2 = a1 * b2 + a2 * b1 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  have h4 : (4 : ZMod 2) = 0 := rfl
  calc
    (1 + (a1 + b1 + g1)) * (a2 + b2 + g2) +
      (1 + (a1 + g1)) * (a2 + g2) +
      (1 + (b1 + g1)) * (b2 + g2) +
      (1 + g1) * g2
        = a1 * b2 + a2 * b1 +
          2 * (a2 + b2 + a1 * a2 + a1 * g2 + b1 * b2 + b1 * g2 + g1 * a2 + g1 * b2) +
          4 * (g2 + g1 * g2) := by ring
    _ = a1 * b2 + a2 * b1 := by rw [h2, h4]; ring

lemma additive_iff_ker_phi {k : Nat} (hk : 0 < k) (h5 : 5 ≤ k) (h3 : k % 3 ≠ 0)
    {d : Nat} (hd : d = 1 ∨ d = 2) (s t : Nat) (name c : W k)
    (P : W k →ₗ[ZMod 2] W k) (hP : ∀ w, P (P w) = P w) (mask : W k) :
    let run := fun (key : W k) (j : Fin k) =>
      let z := (fun j => key (ix hk (j.val + k - s % k))) + name
      let y := fun i : Fin k =>
        z i + z (ix hk (i.val + d)) + z (ix hk (i.val + k - d % k))
      y j + (1 + y (ix hk (j.val + 1))) * y (ix hk (j.val + 2)) +
        key (ix hk (j.val + k - t % k)) + c j
    let M := roundEquiv hk h5 h3 hd s
    let Q := M.toLinearMap.comp (P.comp M.symm.toLinearMap)
    (∃ left right : W k → ZMod 2, ∀ a b : W k,
      (∑ j : Fin k, mask j * run (P a + (b - P b)) j) = left a + right b) ↔
    mask ∈ LinearMap.ker (phiMap hk Q) := by
  intro run M Q
  let F : W k → ZMod 2 := fun w => ∑ j : Fin k, mask j * run w j
  have hrun_diff : ∀ u v : W k, ∀ j : Fin k,
      run (u + v) j + run u j + run v j + run 0 j =
      M u (ix hk (j.val + 1)) * M v (ix hk (j.val + 2)) +
      M u (ix hk (j.val + 2)) * M v (ix hk (j.val + 1)) := by
    intro u v j
    let y0 : W k := mixLin hk d name
    have hrun_eq : ∀ w : W k, ∀ j : Fin k,
        run w j = M w j + y0 j +
          (1 + (M w (ix hk (j.val + 1)) + y0 (ix hk (j.val + 1)))) *
          (M w (ix hk (j.val + 2)) + y0 (ix hk (j.val + 2))) +
          w (ix hk (j.val + k - t % k)) + c j := by
      intro w r
      have hy : ∀ i : Fin k,
          ((fun q : Fin k => w (ix hk (q.val + k - s % k))) + name) i +
          ((fun q : Fin k => w (ix hk (q.val + k - s % k))) + name) (ix hk (i.val + d)) +
          ((fun q : Fin k => w (ix hk (q.val + k - s % k))) + name) (ix hk (i.val + k - d % k)) =
          M w i + y0 i := by
        intro i
        change (mixLin hk d (rotLin hk s w + name)) i =
          (mixLin hk d (rotLin hk s w)) i + (mixLin hk d name) i
        rw [map_add, Pi.add_apply]
      dsimp only [run]
      rw [hy r, hy (ix hk (r.val + 1)), hy (ix hk (r.val + 2))]
    rw [hrun_eq (u + v) j, hrun_eq u j, hrun_eq v j, hrun_eq 0 j]
    have hMadd : M (u + v) = M u + M v := map_add M u v
    have hM0 : M 0 = 0 := map_zero M
    simp only [hMadd, hM0, Pi.add_apply, Pi.zero_apply, zero_add]
    have hlin : ∀ (x1 x2 x3 x4 x5 x6 : ZMod 2),
        ((x1 + x2 + x3) + (x4 + x5) + x6) +
        ((x1 + x3) + x4 + x6) +
        ((x2 + x3) + x5 + x6) +
        (x3 + 0 + x6) = 0 := by
      intro x1 x2 x3 x4 x5 x6
      have h2 : (2 : ZMod 2) = 0 := rfl
      have h4 : (4 : ZMod 2) = 0 := rfl
      calc
        ((x1 + x2 + x3) + (x4 + x5) + x6) +
          ((x1 + x3) + x4 + x6) +
          ((x2 + x3) + x5 + x6) +
          (x3 + 0 + x6)
            = 2 * (x1 + x2 + x4 + x5) + 4 * (x3 + x6) := by ring
        _ = 0 := by rw [h2, h4]; ring
    have hq := quad_second_diff
      (M u (ix hk (j.val + 1))) (M v (ix hk (j.val + 1))) (y0 (ix hk (j.val + 1)))
      (M u (ix hk (j.val + 2))) (M v (ix hk (j.val + 2))) (y0 (ix hk (j.val + 2)))
    have hl := hlin (M u j) (M v j) (y0 j)
      (u (ix hk (j.val + k - t % k))) (v (ix hk (j.val + k - t % k))) (c j)
    have hsum :
        (M u j + M v j + y0 j + (1 + (M u (ix hk (j.val + 1)) + M v (ix hk (j.val + 1)) + y0 (ix hk (j.val + 1)))) *
            (M u (ix hk (j.val + 2)) + M v (ix hk (j.val + 2)) + y0 (ix hk (j.val + 2))) +
          (u (ix hk (j.val + k - t % k)) + v (ix hk (j.val + k - t % k))) + c j) +
        (M u j + y0 j + (1 + (M u (ix hk (j.val + 1)) + y0 (ix hk (j.val + 1)))) *
            (M u (ix hk (j.val + 2)) + y0 (ix hk (j.val + 2))) +
          u (ix hk (j.val + k - t % k)) + c j) +
        (M v j + y0 j + (1 + (M v (ix hk (j.val + 1)) + y0 (ix hk (j.val + 1)))) *
            (M v (ix hk (j.val + 2)) + y0 (ix hk (j.val + 2))) +
          v (ix hk (j.val + k - t % k)) + c j) +
        (y0 j + (1 + y0 (ix hk (j.val + 1))) * y0 (ix hk (j.val + 2)) + 0 + c j)
        =
        (((M u j + M v j + y0 j) + (u (ix hk (j.val + k - t % k)) + v (ix hk (j.val + k - t % k))) + c j) +
         ((M u j + y0 j) + u (ix hk (j.val + k - t % k)) + c j) +
         ((M v j + y0 j) + v (ix hk (j.val + k - t % k)) + c j) +
         (y0 j + 0 + c j)) +
        ((1 + (M u (ix hk (j.val + 1)) + M v (ix hk (j.val + 1)) + y0 (ix hk (j.val + 1)))) *
            (M u (ix hk (j.val + 2)) + M v (ix hk (j.val + 2)) + y0 (ix hk (j.val + 2))) +
         (1 + (M u (ix hk (j.val + 1)) + y0 (ix hk (j.val + 1)))) *
            (M u (ix hk (j.val + 2)) + y0 (ix hk (j.val + 2))) +
         (1 + (M v (ix hk (j.val + 1)) + y0 (ix hk (j.val + 1)))) *
            (M v (ix hk (j.val + 2)) + y0 (ix hk (j.val + 2))) +
         (1 + y0 (ix hk (j.val + 1))) * y0 (ix hk (j.val + 2))) := by ring
    rw [hsum, hl, hq, zero_add]
  have hF_diff : ∀ a b : W k,
      F (P a + (b - P b)) + F (P a) + F (b - P b) + F 0 = phiMap hk Q mask (M a, M b) := by
    intro a b
    dsimp only [F, phiMap, LinearMap.coe_mk, AddHom.coe_mk, crossEdge]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    have hmul : mask j * run (P a + (b - P b)) j + mask j * run (P a) j +
        mask j * run (b - P b) j + mask j * run 0 j =
        mask j * (run (P a + (b - P b)) j + run (P a) j + run (b - P b) j + run 0 j) := by ring
    rw [hmul, hrun_diff (P a) (b - P b) j]
    have hQa : Q (M a) = M (P a) := by
      dsimp only [Q]
      simp [M.symm_apply_apply]
    have hQb : M b - Q (M b) = M (b - P b) := by
      dsimp only [Q]
      simp [M.symm_apply_apply, map_sub]
    have hj2 : ix hk ((ix hk (j.val + 1)).val + 1) = ix hk (j.val + 2) := by
      rw [ix_val, ix_add_mod]
    rw [hQa, hQb, hj2]
  constructor
  · rintro ⟨left, right, hlr⟩
    rw [LinearMap.mem_ker]
    ext ⟨x, y⟩
    have hx : M (M.symm x) = x := M.apply_symm_apply x
    have hy : M (M.symm y) = y := M.apply_symm_apply y
    rw [← hx, ← hy, ← hF_diff (M.symm x) (M.symm y)]
    set a := M.symm x
    set b := M.symm y
    have h1 := hlr a b
    have h2 := hlr a 0
    have h3 := hlr 0 b
    have h4 := hlr 0 0
    simp only [map_zero, sub_zero, add_zero, zero_add] at h2 h3 h4
    dsimp only [F]
    rw [h1, h2, h3, h4]
    have h2z : (2 : ZMod 2) = 0 := rfl
    calc
      left a + right b + (left a + right 0) + (left 0 + right b) + (left 0 + right 0)
          = 2 * (left a + right b + left 0 + right 0) := by ring
      _ = 0 := by rw [h2z]; ring
  · intro hker
    rw [LinearMap.mem_ker] at hker
    refine ⟨fun a => F (P a), fun b => F (b - P b) + F 0, ?_⟩
    intro a b
    have h0 : phiMap hk Q mask (M a, M b) = 0 := congr_fun hker (M a, M b)
    have hd0 := hF_diff a b
    rw [h0] at hd0
    change F (P a + (b - P b)) = F (P a) + (F (b - P b) + F 0)
    calc
      F (P a + (b - P b))
          = (F (P a + (b - P b)) + F (P a) + F (b - P b) + F 0) +
            (F (P a) + (F (b - P b) + F 0)) := by
              have h2z : (2 : ZMod 2) = 0 := rfl
              calc
                F (P a + (b - P b))
                    = F (P a + (b - P b)) + 2 * (F (P a) + F (b - P b) + F 0) := by rw [h2z]; ring
                _ = (F (P a + (b - P b)) + F (P a) + F (b - P b) + F 0) +
                    (F (P a) + (F (b - P b) + F 0)) := by ring
      _ = F (P a) + (F (b - P b) + F 0) := by rw [hd0, zero_add]

lemma crossEdge_diag {k : Nat} (hk : 0 < k) (Q : W k →ₗ[ZMod 2] W k) (i : Fin k) (w : W k) :
    crossEdge hk Q i (w, w) =
    Q w i * w (ix hk (i.val + 1)) + Q w (ix hk (i.val + 1)) * w i := by
  dsimp only [crossEdge]
  simp only [Pi.sub_apply, zmod2_sub_eq_add]
  have h2z : (2 : ZMod 2) = 0 := rfl
  calc
    Q w i * (w (ix hk (i.val + 1)) + Q w (ix hk (i.val + 1))) +
      Q w (ix hk (i.val + 1)) * (w i + Q w i)
        = Q w i * w (ix hk (i.val + 1)) + Q w (ix hk (i.val + 1)) * w i +
          2 * (Q w i * Q w (ix hk (i.val + 1))) := by ring
    _ = Q w i * w (ix hk (i.val + 1)) + Q w (ix hk (i.val + 1)) * w i := by rw [h2z]; ring

lemma crossEdge_sym {k : Nat} (hk : 0 < k) (Q : W k →ₗ[ZMod 2] W k) (i : Fin k) (a b : W k) :
    crossEdge hk Q i (a, b) + crossEdge hk Q i (b, a) =
    Q a i * b (ix hk (i.val + 1)) + Q a (ix hk (i.val + 1)) * b i +
    Q b i * a (ix hk (i.val + 1)) + Q b (ix hk (i.val + 1)) * a i := by
  dsimp only [crossEdge]
  simp only [Pi.sub_apply, zmod2_sub_eq_add]
  have h2z : (2 : ZMod 2) = 0 := rfl
  calc
    (Q a i * (b (ix hk (i.val + 1)) + Q b (ix hk (i.val + 1))) +
      Q a (ix hk (i.val + 1)) * (b i + Q b i)) +
    (Q b i * (a (ix hk (i.val + 1)) + Q a (ix hk (i.val + 1))) +
      Q b (ix hk (i.val + 1)) * (a i + Q a i))
        = Q a i * b (ix hk (i.val + 1)) + Q a (ix hk (i.val + 1)) * b i +
          Q b i * a (ix hk (i.val + 1)) + Q b (ix hk (i.val + 1)) * a i +
          2 * (Q a i * Q b (ix hk (i.val + 1)) + Q a (ix hk (i.val + 1)) * Q b i) := by ring
    _ = Q a i * b (ix hk (i.val + 1)) + Q a (ix hk (i.val + 1)) * b i +
        Q b i * a (ix hk (i.val + 1)) + Q b (ix hk (i.val + 1)) * a i := by rw [h2z]; ring

lemma ix_succ_ne_self {k : Nat} (hk : 0 < k) (h5 : 5 ≤ k) (i : Fin k) :
    ix hk (i.val + 1) ≠ i := by
  intro h
  have hv := congr_arg Fin.val h
  dsimp only [ix] at hv
  by_cases hi : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt hi] at hv
    omega
  · have hi' : i.val + 1 = k := by omega
    rw [hi', Nat.mod_self] at hv
    omega

lemma exists_diag_or_sym_unit {k : Nat} (hk : 0 < k) (h5 : 5 ≤ k)
    (Q : W k →ₗ[ZMod 2] W k) (i : Fin k) (hne : crossEdge hk Q i ≠ 0) :
    (∃ p : Fin k, crossEdge hk Q i (Pi.single p 1, Pi.single p 1) = 1) ∨
    (∃ p q : Fin k, crossEdge hk Q i (Pi.single p 1, Pi.single q 1) +
      crossEdge hk Q i (Pi.single q 1, Pi.single p 1) = 1) := by
  by_contra h
  push Not at h
  have hdiag : ∀ p : Fin k, crossEdge hk Q i (Pi.single p 1, Pi.single p 1) = 0 := by
    intro p
    rcases zmod2_eq_zero_or_one (crossEdge hk Q i (Pi.single p 1, Pi.single p 1)) with h0 | h1
    · exact h0
    · exact absurd h1 (h.1 p)
  have hsym : ∀ p q : Fin k,
      crossEdge hk Q i (Pi.single p 1, Pi.single q 1) +
      crossEdge hk Q i (Pi.single q 1, Pi.single p 1) = 0 := by
    intro p q
    rcases zmod2_eq_zero_or_one (crossEdge hk Q i (Pi.single p 1, Pi.single q 1) +
        crossEdge hk Q i (Pi.single q 1, Pi.single p 1)) with h0 | h1
    · exact h0
    · exact absurd h1 (h.2 p q)
  let i1 := ix hk (i.val + 1)
  have hi_ne : i1 ≠ i := ix_succ_ne_self hk h5 i
  have hQi_i1 : Q (Pi.single i 1) i1 = 0 := by
    have h0 := hdiag i
    rw [crossEdge_diag] at h0
    change Q (Pi.single i 1) i * (Pi.single i 1 : W k) i1 +
      Q (Pi.single i 1) i1 * (Pi.single i 1 : W k) i = 0 at h0
    simp [Pi.single_apply, hi_ne] at h0
    exact h0
  have hQi1_i : Q (Pi.single i1 1) i = 0 := by
    have h0 := hdiag i1
    rw [crossEdge_diag] at h0
    change Q (Pi.single i1 1) i * (Pi.single i1 1 : W k) i1 +
      Q (Pi.single i1 1) i1 * (Pi.single i1 1 : W k) i = 0 at h0
    simp [Pi.single_apply, hi_ne.symm] at h0
    exact h0
  have hQeq : Q (Pi.single i 1) i = Q (Pi.single i1 1) i1 := by
    have h0 := hsym i i1
    rw [crossEdge_sym] at h0
    change Q (Pi.single i 1) i * (Pi.single i1 1 : W k) i1 +
      Q (Pi.single i 1) i1 * (Pi.single i1 1 : W k) i +
      Q (Pi.single i1 1) i * (Pi.single i 1 : W k) i1 +
      Q (Pi.single i1 1) i1 * (Pi.single i 1 : W k) i = 0 at h0
    simp [Pi.single_apply, hi_ne, hi_ne.symm] at h0
    calc
      Q (Pi.single i 1) i
          = Q (Pi.single i 1) i + Q (Pi.single i1 1) i1 + Q (Pi.single i1 1) i1 := by
              rw [add_assoc, zmod2_add_self, add_zero]
      _ = Q (Pi.single i1 1) i1 := by rw [h0, zero_add]
  let c : ZMod 2 := Q (Pi.single i 1) i
  have hbasis_i : ∀ r : Fin k, Q (Pi.single r 1) i = c * (Pi.single r 1 : W k) i := by
    intro r
    by_cases hri : r = i
    · subst hri; simp [c]
    · by_cases hri1 : r = i1
      · subst hri1; simp [hQi1_i, Pi.single_apply, hi_ne]
      · have h0 := hsym r i1
        rw [crossEdge_sym] at h0
        change Q (Pi.single r 1) i * (Pi.single i1 1 : W k) i1 +
          Q (Pi.single r 1) i1 * (Pi.single i1 1 : W k) i +
          Q (Pi.single i1 1) i * (Pi.single r 1 : W k) i1 +
          Q (Pi.single i1 1) i1 * (Pi.single r 1 : W k) i = 0 at h0
        simp [Pi.single_apply, hi_ne.symm, hri, hri1, Ne.symm hri, Ne.symm hri1] at h0
        simp [Pi.single_apply, Ne.symm hri, h0]
  have hbasis_i1 : ∀ r : Fin k, Q (Pi.single r 1) i1 = c * (Pi.single r 1 : W k) i1 := by
    intro r
    by_cases hri : r = i
    · subst hri; simp [hQi_i1, Pi.single_apply, hi_ne]
    · by_cases hri1 : r = i1
      · subst hri1; simp [c, hQeq]
      · have h0 := hsym r i
        rw [crossEdge_sym] at h0
        change Q (Pi.single r 1) i * (Pi.single i 1 : W k) i1 +
          Q (Pi.single r 1) i1 * (Pi.single i 1 : W k) i +
          Q (Pi.single i 1) i * (Pi.single r 1 : W k) i1 +
          Q (Pi.single i 1) i1 * (Pi.single r 1 : W k) i = 0 at h0
        simp [Pi.single_apply, hi_ne, hri, hri1, Ne.symm hri, Ne.symm hri1] at h0
        simp [Pi.single_apply, Ne.symm hri1, h0]
  have hQa_i : ∀ a : W k, Q a i = c * a i := by
    intro a
    have ha : a = ∑ r : Fin k, a r • (Pi.single r 1 : W k) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [ha]
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, hbasis_i]
    have hsum : ∑ r : Fin k, a r * (c * (Pi.single r 1 : W k) i) =
        c * ∑ r : Fin k, a r * (Pi.single r 1 : W k) i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    rw [hsum]
    simp [Pi.single_apply]
  have hQa_i1 : ∀ a : W k, Q a i1 = c * a i1 := by
    intro a
    have ha : a = ∑ r : Fin k, a r • (Pi.single r 1 : W k) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [ha]
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, hbasis_i1]
    have hsum : ∑ r : Fin k, a r * (c * (Pi.single r 1 : W k) i1) =
        c * ∑ r : Fin k, a r * (Pi.single r 1 : W k) i1 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    rw [hsum]
    simp [Pi.single_apply]
  apply hne
  ext ⟨a, b⟩
  change Q a i * (b i1 - Q b i1) + Q a i1 * (b i - Q b i) = 0
  rw [hQa_i a, hQa_i1 b, hQa_i1 a, hQa_i b]
  calc
    c * a i * (b i1 - c * b i1) + c * a i1 * (b i - c * b i)
        = (c * (1 - c)) * (a i * b i1 + a i1 * b i) := by ring
    _ = 0 := by rw [zmod2_mul_sub_self, zero_mul]

lemma inactive_edge_pure {k : Nat} (hk : 0 < k) (h5 : 5 ≤ k)
    (Q : W k →ₗ[ZMod 2] W k) (hQ : ∀ w, Q (Q w) = Q w) (i : Fin k)
    (hzero : crossEdge hk Q i = 0) :
    ((∀ w : W k, Q w i = 0) ∧ (∀ w : W k, Q w (ix hk (i.val + 1)) = 0)) ∨
    ((∀ w : W k, (w - Q w) i = 0) ∧ (∀ w : W k, (w - Q w) (ix hk (i.val + 1)) = 0)) := by
  let i1 := ix hk (i.val + 1)
  have hi_ne : i1 ≠ i := ix_succ_ne_self hk h5 i
  have hE : ∀ a b : W k, Q a i * (b - Q b) i1 + Q a i1 * (b - Q b) i = 0 := fun a b =>
    congr_fun hzero (a, b)
  have hnot_both_zero : ∀ j : Fin k, ¬ ((∀ w, Q w j = 0) ∧ (∀ w, (w - Q w) j = 0)) := by
    intro j ⟨hL, hR⟩
    have h1 := hL (Pi.single j 1)
    have h2 := hR (Pi.single j 1)
    simp only [Pi.sub_apply, h1, sub_zero, Pi.single_eq_same] at h2
    exact one_ne_zero h2
  have hnot_eq : ¬ ((∀ w, Q w i = Q w i1) ∧ (∀ w, (w - Q w) i = (w - Q w) i1)) := by
    intro ⟨hL, hR⟩
    have h1 := hL (Pi.single i 1)
    have h2 := hR (Pi.single i 1)
    simp only [Pi.sub_apply] at h2
    have hw : (Pi.single i 1 : W k) i = (Pi.single i 1 : W k) i1 := by
      calc
        (Pi.single i 1 : W k) i = ((Pi.single i 1 : W k) i - Q (Pi.single i 1) i) + Q (Pi.single i 1) i := by ring
        _ = ((Pi.single i 1 : W k) i1 - Q (Pi.single i 1) i1) + Q (Pi.single i 1) i1 := by rw [h2, h1]
        _ = (Pi.single i 1 : W k) i1 := by ring
    simp [hi_ne] at hw
  by_cases hLi : ∀ w, Q w i = 0
  · by_cases hLi1 : ∀ w, Q w i1 = 0
    · exact Or.inl ⟨hLi, hLi1⟩
    · exfalso
      push Not at hLi1
      rcases hLi1 with ⟨a, ha⟩
      have ha1 : Q a i1 = 1 := by
        rcases zmod2_eq_zero_or_one (Q a i1) with h0 | h1
        · exact absurd h0 ha
        · exact h1
      have hRi : ∀ b, (b - Q b) i = 0 := by
        intro b
        have hb := hE a b
        rw [hLi a, zero_mul, zero_add, ha1, one_mul] at hb
        exact hb
      exact hnot_both_zero i ⟨hLi, hRi⟩
  · by_cases hRi : ∀ w, (w - Q w) i = 0
    · by_cases hRi1 : ∀ w, (w - Q w) i1 = 0
      · exact Or.inr ⟨hRi, hRi1⟩
      · exfalso
        push Not at hRi1
        rcases hRi1 with ⟨b, hb⟩
        have hb1 : (b - Q b) i1 = 1 := by
          rcases zmod2_eq_zero_or_one ((b - Q b) i1) with h0 | h1
          · exact absurd h0 hb
          · exact h1
        have hLi' : ∀ a, Q a i = 0 := by
          intro a
          have ha := hE a b
          rw [hRi b, mul_zero, add_zero, hb1, mul_one] at ha
          exact ha
        exact hLi hLi'
    · exfalso
      push Not at hLi hRi
      rcases hLi with ⟨a0, ha0⟩
      rcases hRi with ⟨b0, hb0⟩
      have ha01 : Q a0 i = 1 := by
        rcases zmod2_eq_zero_or_one (Q a0 i) with h0 | h1
        · exact absurd h0 ha0
        · exact h1
      have hb01 : (b0 - Q b0) i = 1 := by
        rcases zmod2_eq_zero_or_one ((b0 - Q b0) i) with h0 | h1
        · exact absurd h0 hb0
        · exact h1
      by_cases ha0_i1 : Q a0 i1 = 0
      · have hRi1 : ∀ b, (b - Q b) i1 = 0 := by
          intro b
          have hb := hE a0 b
          rw [ha01, one_mul, ha0_i1, zero_mul, add_zero] at hb
          exact hb
        have hLi1 : ∀ a, Q a i1 = 0 := by
          intro a
          have ha := hE a b0
          rw [hRi1 b0, mul_zero, zero_add, hb01, mul_one] at ha
          exact ha
        exact hnot_both_zero i1 ⟨hLi1, hRi1⟩
      · have ha0_i1_1 : Q a0 i1 = 1 := by
          rcases zmod2_eq_zero_or_one (Q a0 i1) with h0 | h1
          · exact absurd h0 ha0_i1
          · exact h1
        have hReq : ∀ b, (b - Q b) i = (b - Q b) i1 := by
          intro b
          have hb := hE a0 b
          rw [ha01, one_mul, ha0_i1_1, one_mul] at hb
          calc
            (b - Q b) i = (b - Q b) i1 + ((b - Q b) i1 + (b - Q b) i) := by
              rw [← add_assoc, zmod2_add_self, zero_add]
            _ = (b - Q b) i1 := by rw [hb, add_zero]
        have hb0_i1_1 : (b0 - Q b0) i1 = 1 := by rw [← hReq b0, hb01]
        have hLeq : ∀ a, Q a i = Q a i1 := by
          intro a
          have ha := hE a b0
          rw [hb01, hb0_i1_1, mul_one, mul_one] at ha
          calc
            Q a i = Q a i1 + (Q a i + Q a i1) := by
              calc
                Q a i = Q a i + (Q a i1 + Q a i1) := by rw [zmod2_add_self, add_zero]
                _ = Q a i1 + (Q a i + Q a i1) := by ring
            _ = Q a i1 := by rw [ha, add_zero]
        exact hnot_eq ⟨hLeq, hReq⟩

lemma exists_inactive_edge_of_two_values {k : Nat} (hk : 0 < k) (h5 : 5 ≤ k)
    (Q : W k →ₗ[ZMod 2] W k) (β : W k × W k → ZMod 2)
    (hvals : ∀ i : Fin k, crossEdge hk Q i = 0 ∨ crossEdge hk Q i = β) :
    ∃ j : Fin k, crossEdge hk Q j = 0 := by
  by_cases hall0 : ∀ i : Fin k, crossEdge hk Q i = 0
  · exact ⟨⟨0, hk⟩, hall0 ⟨0, hk⟩⟩
  · push Not at hall0
    rcases hall0 with ⟨i0, hi0⟩
    have hβ_eq : crossEdge hk Q i0 = β := by
      rcases hvals i0 with h0 | h1
      · exact absurd h0 hi0
      · exact h1
    have hunit := exists_diag_or_sym_unit hk h5 Q i0 hi0
    have hfind : ∀ p q : Fin k,
        ∃ j : Fin k, j ≠ p ∧ j ≠ q ∧ ix hk (j.val + 1) ≠ p ∧ ix hk (j.val + 1) ≠ q := by
      intro p q
      let bad : Finset (Fin k) := {p, q, ix hk (p.val + k - 1), ix hk (q.val + k - 1)}
      have hcard_le : bad.card ≤ 4 := by
        calc
          bad.card ≤ ({q, ix hk (p.val + k - 1), ix hk (q.val + k - 1)} : Finset (Fin k)).card + 1 :=
            Finset.card_insert_le _ _
          _ ≤ ({ix hk (p.val + k - 1), ix hk (q.val + k - 1)} : Finset (Fin k)).card + 1 + 1 := by
            gcongr; exact Finset.card_insert_le _ _
          _ ≤ ({ix hk (q.val + k - 1)} : Finset (Fin k)).card + 1 + 1 + 1 := by
            gcongr; exact Finset.card_insert_le _ _
          _ = 4 := by simp
      have hlt : bad.card < (Finset.univ : Finset (Fin k)).card := by
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨j, _, hj⟩
      have hjp : j ≠ p := fun h => hj (by simp [bad, h])
      have hjq : j ≠ q := fun h => hj (by simp [bad, h])
      have hj1p : ix hk (j.val + 1) ≠ p := by
        intro h
        apply hj
        have heq : j = ix hk (p.val + k - 1) := by
          rw [← h, ix_val, ix_add_sub_cancel hk j.val 1 (by omega), ix_val_self]
        simp [bad, heq]
      have hj1q : ix hk (j.val + 1) ≠ q := by
        intro h
        apply hj
        have heq : j = ix hk (q.val + k - 1) := by
          rw [← h, ix_val, ix_add_sub_cancel hk j.val 1 (by omega), ix_val_self]
        simp [bad, heq]
      exact ⟨j, hjp, hjq, hj1p, hj1q⟩
    rcases hunit with ⟨p, hp⟩ | ⟨p, q, hpq⟩
    · rcases hfind p p with ⟨j, hjp, _, hj1p, _⟩
      refine ⟨j, ?_⟩
      rcases hvals j with h0 | h1
      · exact h0
      · exfalso
        have hdj : crossEdge hk Q j (Pi.single p 1, Pi.single p 1) = 0 := by
          rw [crossEdge_diag]
          simp [hjp, hj1p]
        rw [h1, ← hβ_eq, hp] at hdj
        exact one_ne_zero hdj
    · rcases hfind p q with ⟨j, hjp, hjq, hj1p, hj1q⟩
      refine ⟨j, ?_⟩
      rcases hvals j with h0 | h1
      · exact h0
      · exfalso
        have hsj : crossEdge hk Q j (Pi.single p 1, Pi.single q 1) +
            crossEdge hk Q j (Pi.single q 1, Pi.single p 1) = 0 := by
          rw [crossEdge_sym]
          simp [hjp, hjq, hj1p, hj1q]
        rw [h1, ← hβ_eq, hpq] at hsj
        exact one_ne_zero hsj

lemma run_boundary_contradiction {k : Nat} (hk : 0 < k) (h5 : 5 ≤ k)
    (Q : W k →ₗ[ZMod 2] W k) (hQ : ∀ w, Q (Q w) = Q w)
    (β : W k × W k → ZMod 2)
    (hvals : ∀ i : Fin k, crossEdge hk Q i = 0 ∨ crossEdge hk Q i = β)
    (j : Fin k) (hj0 : ∀ w, (w - Q w) j = 0) (hj1 : ∀ w, (w - Q w) (ix hk (j.val + 1)) = 0)
    (hnotall : ∃ z : Fin k, ¬ (∀ w, (w - Q w) z = 0)) : False := by
  let T : Fin k → Prop := fun i => ∀ w : W k, (w - Q w) i = 0
  letI : DecidablePred T := fun i => Classical.propDecidable (T i)
  have hnot_both : ∀ i : Fin k, ¬ (T i ∧ ∀ w, Q w i = 0) := by
    intro i ⟨hR, hL⟩
    have h1 := hL (Pi.single i 1)
    have h2 := hR (Pi.single i 1)
    simp only [Pi.sub_apply, h1, sub_zero, Pi.single_eq_same] at h2
    exact one_ne_zero h2
  have hex_fwd : ∃ m : Nat, 1 ≤ m ∧ m ≤ k - 2 ∧ ¬ T (ix hk (j.val + 1 + m)) := by
    rcases hnotall with ⟨z, hz⟩
    have hzj : z ≠ j := fun h => hz (h ▸ hj0)
    have hzj1 : z ≠ ix hk (j.val + 1) := fun h => hz (h ▸ hj1)
    let m := (z.val + k - (j.val + 1) % k) % k
    have hm_ix : ix hk (j.val + 1 + m) = z := by
      have h1 : (j.val + 1 + m) % k = z.val := by
        dsimp only [m]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hlt : (j.val + 1) % k < k := Nat.mod_lt _ hk
        have hd : k * ((j.val + 1) / k) + (j.val + 1) % k = j.val + 1 := Nat.div_add_mod (j.val + 1) k
        have h2 : j.val + 1 + (z.val + k - (j.val + 1) % k) =
            z.val + ((j.val + 1) / k + 1) * k := by
          have hsub : z.val + k - (j.val + 1) % k = z.val + (k - (j.val + 1) % k) := by omega
          rw [hsub]
          have hadd : (j.val + 1) % k + (k - (j.val + 1) % k) = k := by omega
          linarith
        rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt z.isLt]
      ext
      exact h1
    have hm_lt : m < k := Nat.mod_lt _ hk
    have hm_ne0 : m ≠ 0 := by
      intro h0
      rw [h0, add_zero] at hm_ix
      exact hzj1 hm_ix.symm
    have hm_ne_k1 : m ≠ k - 1 := by
      intro h1
      have harg : j.val + 1 + (k - 1) = j.val + k := by omega
      rw [h1, harg] at hm_ix
      have h2 : ix hk (j.val + k) = j := by
        ext
        simp [ix, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
      rw [h2] at hm_ix
      exact hzj hm_ix.symm
    exact ⟨m, by omega, by omega, by rw [hm_ix]; exact hz⟩
  let rFwd := Nat.find hex_fwd
  have hrFwd_spec := Nat.find_spec hex_fwd
  have hrFwd_ge1 : 1 ≤ rFwd := hrFwd_spec.1
  have hrFwd_le : rFwd ≤ k - 2 := hrFwd_spec.2.1
  have hb_notT : ¬ T (ix hk (j.val + 1 + rFwd)) := hrFwd_spec.2.2
  have hu2_T : T (ix hk (j.val + rFwd)) := by
    by_cases h1 : rFwd = 1
    · rw [h1]; exact hj1
    · by_contra hnt
      have hlt : rFwd - 1 < rFwd := by omega
      have hprev : 1 ≤ rFwd - 1 ∧ rFwd - 1 ≤ k - 2 ∧ ¬ T (ix hk (j.val + 1 + (rFwd - 1))) := by
        refine ⟨by omega, by omega, ?_⟩
        have harg : j.val + 1 + (rFwd - 1) = j.val + rFwd := by omega
        rw [harg]
        exact hnt
      exact Nat.find_min hex_fwd hlt hprev
  have hex_bwd : ∃ m : Nat, 1 ≤ m ∧ m ≤ k - 1 - rFwd ∧ ¬ T (ix hk (j.val + k - m)) := by
    refine ⟨k - 1 - rFwd, by omega, le_rfl, ?_⟩
    have harg : j.val + k - (k - 1 - rFwd) = j.val + 1 + rFwd := by omega
    rw [harg]
    exact hb_notT
  let rBwd := Nat.find hex_bwd
  have hrBwd_spec := Nat.find_spec hex_bwd
  have hrBwd_ge1 : 1 ≤ rBwd := hrBwd_spec.1
  have hrBwd_le : rBwd ≤ k - 1 - rFwd := hrBwd_spec.2.1
  have ha_notT : ¬ T (ix hk (j.val + k - rBwd)) := hrBwd_spec.2.2
  have hu1_T : T (ix hk (j.val + k - (rBwd - 1))) := by
    by_cases h1 : rBwd = 1
    · rw [h1, Nat.sub_self, Nat.sub_zero]
      have heq : ix hk (j.val + k) = j := by
        ext
        simp [ix, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
      rw [heq]
      exact hj0
    · by_contra hnt
      have hlt : rBwd - 1 < rBwd := by omega
      have hprev : 1 ≤ rBwd - 1 ∧ rBwd - 1 ≤ k - 1 - rFwd ∧ ¬ T (ix hk (j.val + k - (rBwd - 1))) :=
        ⟨by omega, by omega, hnt⟩
      exact Nat.find_min hex_bwd hlt hprev
  let a := ix hk (j.val + k - rBwd)
  let u1 := ix hk (j.val + k - (rBwd - 1))
  let u2 := ix hk (j.val + rFwd)
  let b := ix hk (j.val + 1 + rFwd)
  have ha_succ : ix hk (a.val + 1) = u1 := by
    ext
    dsimp only [a, u1, ix]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    congr 1
    omega
  have hu2_succ : ix hk (u2.val + 1) = b := by
    ext
    dsimp only [u2, b, ix]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    congr 1
    omega
  have hu1_ne_u2 : u1 ≠ u2 := by
    intro h
    have hv := congr_arg Fin.val h
    dsimp only [u1, u2, ix] at hv
    have hdelta : 1 ≤ rFwd + rBwd - 1 ∧ rFwd + rBwd - 1 < k := by omega
    have heq_mod : (j.val + k - (rBwd - 1) + (rFwd + rBwd - 1)) % k = (j.val + rFwd) % k := by
      have h1 : j.val + k - (rBwd - 1) + (rFwd + rBwd - 1) = (j.val + rFwd) + k := by omega
      rw [h1, Nat.add_mod_right]
    have h2 : (u1.val + (rFwd + rBwd - 1)) % k = u1.val := by
      dsimp only [u1, ix]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, heq_mod, ← hv]
    have h3 : (u1.val + (rFwd + rBwd - 1)) % k ≠ u1.val := by
      by_cases hsum : u1.val + (rFwd + rBwd - 1) < k
      · rw [Nat.mod_eq_of_lt hsum]; omega
      · have hsub : u1.val + (rFwd + rBwd - 1) - k < k := by omega
        have hsplit : u1.val + (rFwd + rBwd - 1) = (u1.val + (rFwd + rBwd - 1) - k) + k := by omega
        rw [hsplit, Nat.add_mod_right, Nat.mod_eq_of_lt hsub]
        omega
    exact h3 h2
  have hEa_formula : ∀ x y : W k, crossEdge hk Q a (x, y) = Q x u1 * (y - Q y) a := by
    intro x y
    dsimp only [crossEdge]
    rw [ha_succ, hu1_T y, mul_zero, zero_add]
  have hEu2_formula : ∀ x y : W k, crossEdge hk Q u2 (x, y) = Q x u2 * (y - Q y) b := by
    intro x y
    dsimp only [crossEdge]
    rw [hu2_succ, hu2_T y, mul_zero, add_zero]
  have hLu1_ne : ∃ x : W k, Q x u1 = 1 := by
    by_contra h0
    have hall0 : ∀ x : W k, Q x u1 = 0 := by
      intro x
      rcases zmod2_eq_zero_or_one (Q x u1) with hval | hval
      · exact hval
      · exact absurd ⟨x, hval⟩ h0
    exact hnot_both u1 ⟨hu1_T, hall0⟩
  have hLu2_ne : ∃ x : W k, Q x u2 = 1 := by
    by_contra h0
    have hall0 : ∀ x : W k, Q x u2 = 0 := by
      intro x
      rcases zmod2_eq_zero_or_one (Q x u2) with hval | hval
      · exact hval
      · exact absurd ⟨x, hval⟩ h0
    exact hnot_both u2 ⟨hu2_T, hall0⟩
  have hRa_ne : ∃ y : W k, (y - Q y) a = 1 := by
    have hnt : ∃ y : W k, (y - Q y) a ≠ 0 := by
      by_contra h0; push Not at h0; exact ha_notT h0
    rcases hnt with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rcases zmod2_eq_zero_or_one ((y - Q y) a) with hval | hval
    · exact absurd hval hy
    · exact hval
  have hRb_ne : ∃ y : W k, (y - Q y) b = 1 := by
    have hnt : ∃ y : W k, (y - Q y) b ≠ 0 := by
      by_contra h0; push Not at h0; exact hb_notT h0
    rcases hnt with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rcases zmod2_eq_zero_or_one ((y - Q y) b) with hval | hval
    · exact absurd hval hy
    · exact hval
  have hEa_ne : crossEdge hk Q a ≠ 0 := by
    intro h0
    rcases hLu1_ne with ⟨x, hx⟩
    rcases hRa_ne with ⟨y, hy⟩
    have hv := congr_fun h0 (x, y)
    rw [hEa_formula, hx, hy, mul_one] at hv
    exact one_ne_zero hv
  have hEu2_ne : crossEdge hk Q u2 ≠ 0 := by
    intro h0
    rcases hLu2_ne with ⟨x, hx⟩
    rcases hRb_ne with ⟨y, hy⟩
    have hv := congr_fun h0 (x, y)
    rw [hEu2_formula, hx, hy, mul_one] at hv
    exact one_ne_zero hv
  have hEa_eq_Eu2 : crossEdge hk Q a = crossEdge hk Q u2 := by
    have h1 : crossEdge hk Q a = β := by
      rcases hvals a with h0 | hβ
      · exact absurd h0 hEa_ne
      · exact hβ
    have h2 : crossEdge hk Q u2 = β := by
      rcases hvals u2 with h0 | hβ
      · exact absurd h0 hEu2_ne
      · exact hβ
    rw [h1, h2]
  rcases hRa_ne with ⟨y0, hy0⟩
  rcases zmod2_eq_zero_or_one ((y0 - Q y0) b) with hyb | hyb
  · rcases hLu1_ne with ⟨x0, hx0⟩
    have hv := congr_fun hEa_eq_Eu2 (x0, y0)
    rw [hEa_formula, hEu2_formula, hx0, hy0, hyb, mul_one, mul_zero] at hv
    exact one_ne_zero hv
  · have hLeq : ∀ x : W k, Q x u1 = Q x u2 := by
      intro x
      have hv := congr_fun hEa_eq_Eu2 (x, y0)
      rw [hEa_formula, hEu2_formula, hy0, hyb, mul_one, mul_one] at hv
      exact hv
    have h1 := hLeq (Pi.single u1 1)
    have hR1 := hu1_T (Pi.single u1 1)
    have hR2 := hu2_T (Pi.single u1 1)
    simp only [Pi.sub_apply] at hR1 hR2
    have hsame : (Pi.single u1 1 : W k) u1 = (Pi.single u1 1 : W k) u2 := by
      calc
        (Pi.single u1 1 : W k) u1
            = ((Pi.single u1 1 : W k) u1 - Q (Pi.single u1 1) u1) + Q (Pi.single u1 1) u1 := by ring
        _ = ((Pi.single u1 1 : W k) u2 - Q (Pi.single u1 1) u2) + Q (Pi.single u1 1) u2 := by rw [hR1, hR2, h1]
        _ = (Pi.single u1 1 : W k) u2 := by ring
    simp [hu1_ne_u2.symm] at hsame

lemma two_le_finrank_range_phi {k : Nat} (hk : 0 < k) (h5 : 5 ≤ k)
    (Q : W k →ₗ[ZMod 2] W k) (hQ : ∀ w, Q (Q w) = Q w)
    (hn0 : 0 < Module.finrank (ZMod 2) (LinearMap.range Q))
    (hnk : Module.finrank (ZMod 2) (LinearMap.range Q) < k) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (phiMap hk Q)) := by
  by_contra hlt
  have hle1 : Module.finrank (ZMod 2) (LinearMap.range (phiMap hk Q)) ≤ 1 := by omega
  have hmem_edge : ∀ i : Fin k, crossEdge hk Q i ∈ LinearMap.range (phiMap hk Q) := by
    intro i
    refine ⟨Pi.single (ix hk (i.val + k - 1)) 1, ?_⟩
    ext p
    dsimp only [phiMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single (ix hk (i.val + k - 1))]
    · simp only [Pi.single_eq_same, one_mul]
      have hix : ix hk ((ix hk (i.val + k - 1)).val + 1) = i := by
        rw [ix_val, ix_sub_add_cancel hk i.val 1 (by omega), ix_val_self]
      rw [hix]
    · intro j _ hne
      simp [hne]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  have hex_beta : ∃ β : W k × W k → ZMod 2,
      ∀ i : Fin k, crossEdge hk Q i = 0 ∨ crossEdge hk Q i = β := by
    by_cases hbot : LinearMap.range (phiMap hk Q) = ⊥
    · refine ⟨0, fun i => Or.inl ?_⟩
      have hm := hmem_edge i
      rw [hbot, Submodule.mem_bot] at hm
      exact hm
    · obtain ⟨β, hβ_mem, hβ_ne⟩ : ∃ β ∈ LinearMap.range (phiMap hk Q), β ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hbot
        ext x
        simp only [Submodule.mem_bot]
        exact ⟨hall x, fun h => h ▸ Submodule.zero_mem _⟩
      have hspan_le : Submodule.span (ZMod 2) ({β} : Set (W k × W k → ZMod 2)) ≤
          LinearMap.range (phiMap hk Q) :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hβ_mem)
      have hfr_span : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({β} : Set (W k × W k → ZMod 2))) = 1 :=
        finrank_span_singleton hβ_ne
      have hfr_eq : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({β} : Set (W k × W k → ZMod 2))) =
          Module.finrank (ZMod 2) (LinearMap.range (phiMap hk Q)) := by
        have hle := Submodule.finrank_mono hspan_le
        omega
      have heq_sub : Submodule.span (ZMod 2) ({β} : Set (W k × W k → ZMod 2)) =
          LinearMap.range (phiMap hk Q) :=
        Submodule.eq_of_le_of_finrank_eq hspan_le hfr_eq
      refine ⟨β, fun i => ?_⟩
      have hm : crossEdge hk Q i ∈ Submodule.span (ZMod 2) ({β} : Set (W k × W k → ZMod 2)) := by
        rw [heq_sub]
        exact hmem_edge i
      rcases Submodule.mem_span_singleton.mp hm with ⟨c, hc⟩
      rcases zmod2_eq_zero_or_one c with rfl | rfl
      · left; rw [zero_smul] at hc; exact hc.symm
      · right; rw [one_smul] at hc; exact hc.symm
  rcases hex_beta with ⟨β, hvals⟩
  rcases exists_inactive_edge_of_two_values hk h5 Q β hvals with ⟨j, hj0⟩
  rcases inactive_edge_pure hk h5 Q hQ j hj0 with ⟨hLj0, hLj1⟩ | ⟨hRj0, hRj1⟩
  · let Q' : W k →ₗ[ZMod 2] W k := LinearMap.id - Q
    have hQ' : ∀ w, Q' (Q' w) = Q' w := by
      intro w
      change (w - Q w) - Q (w - Q w) = w - Q w
      rw [map_sub, hQ w]
      abel
    have hQ'sub : ∀ w, w - Q' w = Q w := by
      intro w
      change w - (w - Q w) = Q w
      abel
    have hcross_eq : ∀ i : Fin k, crossEdge hk Q' i = fun p => crossEdge hk Q i (p.2, p.1) := by
      intro i
      ext ⟨a, b⟩
      change (a - Q a) i * (b - (b - Q b)) (ix hk (i.val + 1)) +
        (a - Q a) (ix hk (i.val + 1)) * (b - (b - Q b)) i =
        Q b i * (a - Q a) (ix hk (i.val + 1)) + Q b (ix hk (i.val + 1)) * (a - Q a) i
      have h1 : b - (b - Q b) = Q b := by abel
      rw [h1]
      ring
    have hvals' : ∀ i : Fin k,
        crossEdge hk Q' i = 0 ∨ crossEdge hk Q' i = fun p => β (p.2, p.1) := by
      intro i
      rw [hcross_eq i]
      rcases hvals i with h0 | h1
      · left; ext p; exact congr_fun h0 (p.2, p.1)
      · right; ext p; exact congr_fun h1 (p.2, p.1)
    have hnotall' : ∃ z : Fin k, ¬ (∀ w, (w - Q' w) z = 0) := by
      by_contra hall
      push Not at hall
      have hQ0 : Q = 0 := by
        apply LinearMap.ext
        intro w
        ext z
        have hz := hall z w
        rw [hQ'sub w] at hz
        exact hz
      have hbot : LinearMap.range Q = ⊥ := by rw [hQ0, LinearMap.range_zero]
      rw [hbot, finrank_bot] at hn0
      exact Nat.lt_irrefl 0 hn0
    exact run_boundary_contradiction hk h5 Q' hQ' (fun p => β (p.2, p.1)) hvals' j
      (fun w => by rw [hQ'sub w]; exact hLj0 w)
      (fun w => by rw [hQ'sub w]; exact hLj1 w)
      hnotall'
  · have hnotall : ∃ z : Fin k, ¬ (∀ w, (w - Q w) z = 0) := by
      by_contra hall
      push Not at hall
      have hQid : Q = LinearMap.id := by
        apply LinearMap.ext
        intro w
        ext z
        have hz := hall z w
        simp only [Pi.sub_apply, sub_eq_zero] at hz
        exact hz.symm
      have htop : LinearMap.range Q = ⊤ := by rw [hQid, LinearMap.range_id]
      rw [htop, finrank_top, Module.finrank_fin_fun] at hnk
      exact Nat.lt_irrefl k hnk
    exact run_boundary_contradiction hk h5 Q hQ β hvals j hRj0 hRj1 hnotall

lemma card_ker_phi_le {k : Nat} (hk : 0 < k) (h5 : 5 ≤ k)
    (Q : W k →ₗ[ZMod 2] W k) (hQ : ∀ w, Q (Q w) = Q w)
    (hn0 : 0 < Module.finrank (ZMod 2) (LinearMap.range Q))
    (hnk : Module.finrank (ZMod 2) (LinearMap.range Q) < k) :
    Nat.card (LinearMap.ker (phiMap hk Q)) ≤ 2 ^ (k - 2) := by
  have h2 := two_le_finrank_range_phi hk h5 Q hQ hn0 hnk
  have hrn := LinearMap.finrank_range_add_finrank_ker (phiMap hk Q)
  rw [Module.finrank_fin_fun] at hrn
  have hker_le : Module.finrank (ZMod 2) (LinearMap.ker (phiMap hk Q)) ≤ k - 2 := by omega
  have hcard : Nat.card (LinearMap.ker (phiMap hk Q)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (phiMap hk Q)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcard]
  exact Nat.pow_le_pow_right (by omega) hker_le

def coordProj {k : Nat} (n : Nat) : W k →ₗ[ZMod 2] W k where
  toFun v i := if i.val < n then v i else 0
  map_add' u v := by
    ext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

lemma coordProj_idem {k : Nat} (n : Nat) (w : W k) :
    coordProj n (coordProj n w) = coordProj n w := by
  ext i
  dsimp only [coordProj, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs <;> rfl

lemma finrank_range_coordProj {k : Nat} {n : Nat} (hnk : n < k) :
    Module.finrank (ZMod 2) (LinearMap.range (coordProj (k := k) n)) = n := by
  let e : LinearMap.range (coordProj (k := k) n) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    { toFun := fun v j => v.1 ⟨j.val, lt_trans j.isLt hnk⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun f =>
        ⟨fun i => if h : i.val < n then f ⟨i.val, h⟩ else 0,
         ⟨fun i => if h : i.val < n then f ⟨i.val, h⟩ else 0, by
           ext i
           dsimp only [coordProj, LinearMap.coe_mk, AddHom.coe_mk]
           split_ifs <;> rfl⟩⟩
      left_inv := fun ⟨v, ⟨u, hu⟩⟩ => by
        ext i
        dsimp only
        rw [← hu]
        dsimp only [coordProj, LinearMap.coe_mk, AddHom.coe_mk]
        split_ifs with h
        · rfl
        · rfl
      right_inv := fun f => by
        ext j
        simp [j.isLt] }
  rw [e.finrank_eq, Module.finrank_fin_fun]

lemma card_ker_phi_coordProj {k : Nat} (hk : 0 < k) (h5 : 5 ≤ k)
    {n : Nat} (hn0 : 0 < n) (hnk : n < k) :
    Nat.card (LinearMap.ker (phiMap hk (coordProj (k := k) n))) = 2 ^ (k - 2) := by
  let j1 : Fin k := ix hk (n + k - 2)
  let j2 : Fin k := ix hk (k - 2)
  have hj1_s1 : ix hk (j1.val + 1) = ⟨n - 1, by omega⟩ := by
    ext
    dsimp only [j1, ix]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h1 : n + k - 2 + 1 = (n - 1) + k := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hj1_s2 : ix hk (j1.val + 2) = ⟨n, hnk⟩ := by
    ext
    dsimp only [j1, ix]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h1 : n + k - 2 + 2 = n + k := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hnk]
  have hj2_s1 : ix hk (j2.val + 1) = ⟨k - 1, by omega⟩ := by
    ext
    dsimp only [j2, ix]
    rw [Nat.mod_eq_of_lt (by omega : k - 2 < k)]
    have h1 : k - 2 + 1 = k - 1 := by omega
    rw [h1, Nat.mod_eq_of_lt (by omega)]
  have hj2_s2 : ix hk (j2.val + 2) = ⟨0, hk⟩ := by
    ext
    dsimp only [j2, ix]
    rw [Nat.mod_eq_of_lt (by omega : k - 2 < k)]
    have h1 : k - 2 + 2 = k := by omega
    rw [h1, Nat.mod_self]
  have hj1_ne_j2 : j1 ≠ j2 := by
    intro h
    have h1 := congr_arg (fun j : Fin k => (ix hk (j.val + 2)).val) h
    rw [hj1_s2, hj2_s2] at h1
    dsimp only at h1
    omega
  have hcross_other : ∀ j : Fin k, j ≠ j1 → j ≠ j2 →
      crossEdge hk (coordProj (k := k) n) (ix hk (j.val + 1)) = 0 := by
    intro j hj1 hj2
    have hr_ne_n1 : (ix hk (j.val + 1)).val ≠ n - 1 := by
      intro h
      apply hj1
      ext
      dsimp only [j1, ix] at h ⊢
      have h1 : (n + k - 2) % k = (j.val + 1 + k - 1) % k := by
        have h2 : n + k - 2 = (n - 1) + (k - 1) := by omega
        rw [h2, ← h, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1
        omega
      rw [h1]
      have h3 : j.val + 1 + k - 1 = j.val + k := by omega
      rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    have hr_ne_k1 : (ix hk (j.val + 1)).val ≠ k - 1 := by
      intro h
      apply hj2
      ext
      dsimp only [j2, ix] at h ⊢
      rw [Nat.mod_eq_of_lt (by omega : k - 2 < k)]
      by_cases hjlt : j.val + 1 < k
      · rw [Nat.mod_eq_of_lt hjlt] at h; omega
      · have hjk : j.val + 1 = k := by omega
        rw [hjk, Nat.mod_self] at h
        omega
    have hr_lt : (ix hk (j.val + 1)).val < k := (ix hk (j.val + 1)).isLt
    have hs_eq : (ix hk ((ix hk (j.val + 1)).val + 1)).val = (ix hk (j.val + 1)).val + 1 := by
      rw [ix_val]
      exact Nat.mod_eq_of_lt (by omega)
    ext ⟨a, b⟩
    dsimp only [crossEdge, coordProj, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.zero_apply]
    by_cases hlt : (ix hk (j.val + 1)).val < n
    · have hlt2 : (ix hk ((ix hk (j.val + 1)).val + 1)).val < n := by omega
      simp [hlt, hlt2]
    · have hge2 : ¬ ((ix hk ((ix hk (j.val + 1)).val + 1)).val < n) := by omega
      simp [hlt, hge2]
  have hker_iff : ∀ mask : W k,
      mask ∈ LinearMap.ker (phiMap hk (coordProj (k := k) n)) ↔ mask j1 = 0 ∧ mask j2 = 0 := by
    intro mask
    have hphi_eq : ∀ a b : W k,
        phiMap hk (coordProj (k := k) n) mask (a, b) =
        mask j1 * a ⟨n - 1, by omega⟩ * b ⟨n, hnk⟩ +
        mask j2 * a ⟨0, hk⟩ * b ⟨k - 1, by omega⟩ := by
      intro a b
      dsimp only [phiMap, LinearMap.coe_mk, AddHom.coe_mk]
      have hsum : ∑ j : Fin k, mask j * crossEdge hk (coordProj (k := k) n) (ix hk (j.val + 1)) (a, b) =
          mask j1 * crossEdge hk (coordProj (k := k) n) (ix hk (j1.val + 1)) (a, b) +
          mask j2 * crossEdge hk (coordProj (k := k) n) (ix hk (j2.val + 1)) (a, b) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j1)]
        have hj2_mem : j2 ∈ Finset.univ.erase j1 := Finset.mem_erase.mpr ⟨hj1_ne_j2.symm, Finset.mem_univ j2⟩
        rw [← Finset.add_sum_erase _ _ hj2_mem]
        have hrest : ∑ j ∈ (Finset.univ.erase j1).erase j2,
            mask j * crossEdge hk (coordProj (k := k) n) (ix hk (j.val + 1)) (a, b) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro j hj
          have hj_ne2 : j ≠ j2 := (Finset.mem_erase.mp hj).1
          have hj_ne1 : j ≠ j1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
          rw [hcross_other j hj_ne1 hj_ne2]
          simp
        rw [hrest, add_zero]
      rw [hsum]
      have hce1 : crossEdge hk (coordProj (k := k) n) (ix hk (j1.val + 1)) (a, b) =
          a ⟨n - 1, by omega⟩ * b ⟨n, hnk⟩ := by
        dsimp only [crossEdge]
        have hs2 : ix hk ((ix hk (j1.val + 1)).val + 1) = ⟨n, hnk⟩ := by
          rw [ix_val, ix_add_mod, ← hj1_s2]
        rw [hs2, hj1_s1]
        dsimp only [coordProj, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
        have hlt1 : (⟨n - 1, by omega⟩ : Fin k).val < n := by dsimp only; omega
        simp [hlt1]
      have hce2 : crossEdge hk (coordProj (k := k) n) (ix hk (j2.val + 1)) (a, b) =
          a ⟨0, hk⟩ * b ⟨k - 1, by omega⟩ := by
        dsimp only [crossEdge]
        have hs2 : ix hk ((ix hk (j2.val + 1)).val + 1) = ⟨0, hk⟩ := by
          rw [ix_val, ix_add_mod, ← hj2_s2]
        rw [hs2, hj2_s1]
        dsimp only [coordProj, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
        have hge1 : ¬ ((⟨k - 1, by omega⟩ : Fin k).val < n) := by dsimp only; omega
        have hlt2 : (⟨0, hk⟩ : Fin k).val < n := by dsimp only; omega
        simp [hge1, hlt2]
      rw [hce1, hce2]
      ring
    constructor
    · intro hker
      rw [LinearMap.mem_ker] at hker
      have hnot_both : (⟨n - 1, by omega⟩ : Fin k) ≠ ⟨0, hk⟩ ∨ (⟨n, hnk⟩ : Fin k) ≠ ⟨k - 1, by omega⟩ := by
        by_cases h1 : n = 1
        · right; intro h; have hv := congr_arg Fin.val h; dsimp only at hv; omega
        · left; intro h; have hv := congr_arg Fin.val h; dsimp only at hv; omega
      have hterm_zero :
          (Pi.single (⟨n - 1, by omega⟩ : Fin k) (1 : ZMod 2) : W k) ⟨0, hk⟩ *
          (Pi.single (⟨n, hnk⟩ : Fin k) (1 : ZMod 2) : W k) ⟨k - 1, by omega⟩ = 0 := by
        rcases hnot_both with h1 | h2
        · simp [h1]
        · simp [h2]
      have hterm_zero2 :
          (Pi.single (⟨0, hk⟩ : Fin k) (1 : ZMod 2) : W k) ⟨n - 1, by omega⟩ *
          (Pi.single (⟨k - 1, by omega⟩ : Fin k) (1 : ZMod 2) : W k) ⟨n, hnk⟩ = 0 := by
        rcases hnot_both with h1 | h2
        · simp [h1.symm]
        · simp [h2.symm]
      have hm1 : mask j1 = 0 := by
        have hv := congr_fun hker
          ((Pi.single (⟨n - 1, by omega⟩ : Fin k) (1 : ZMod 2) : W k),
           (Pi.single (⟨n, hnk⟩ : Fin k) (1 : ZMod 2) : W k))
        rw [hphi_eq] at hv
        simp only [Pi.single_eq_same, mul_one, mul_assoc, hterm_zero, mul_zero, add_zero] at hv
        exact hv
      have hm2 : mask j2 = 0 := by
        have hv := congr_fun hker
          ((Pi.single (⟨0, hk⟩ : Fin k) (1 : ZMod 2) : W k),
           (Pi.single (⟨k - 1, by omega⟩ : Fin k) (1 : ZMod 2) : W k))
        rw [hphi_eq] at hv
        simp only [Pi.single_eq_same, mul_one, mul_assoc, hterm_zero2, mul_zero, zero_add] at hv
        exact hv
      exact ⟨hm1, hm2⟩
    · rintro ⟨hm1, hm2⟩
      rw [LinearMap.mem_ker]
      ext ⟨a, b⟩
      rw [hphi_eq, hm1, hm2]
      simp
  let e : LinearMap.ker (phiMap hk (coordProj (k := k) n)) ≃
      ({ i : Fin k // i ≠ j1 ∧ i ≠ j2 } → ZMod 2) :=
    { toFun := fun m i => m.1 i.1
      invFun := fun f =>
        ⟨fun i => if h : i ≠ j1 ∧ i ≠ j2 then f ⟨i, h⟩ else 0,
         (hker_iff _).mpr ⟨by simp, by simp⟩⟩
      left_inv := fun ⟨m, hm⟩ => by
        ext i
        have ⟨hm1, hm2⟩ := (hker_iff m).mp hm
        dsimp only
        split_ifs with h
        · rfl
        · push Not at h
          by_cases h1 : i = j1
          · rw [h1, hm1]
          · rw [h h1, hm2]
      right_inv := fun f => by
        ext ⟨i, hi⟩
        simp [hi] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod]
  have hsub_card : Nat.card { i : Fin k // i ≠ j1 ∧ i ≠ j2 } = k - 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hfilt : Finset.univ.filter (fun i : Fin k => i ≠ j1 ∧ i ≠ j2) =
        (Finset.univ.erase j1).erase j2 := by
      ext i
      simp [and_comm]
    rw [hfilt, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hj1_ne_j2.symm, Finset.mem_univ j2⟩),
      Finset.card_erase_of_mem (Finset.mem_univ j1), Finset.card_univ, Fintype.card_fin]
    omega
  rw [hsub_card]

end PEqualNP.Outside.L_meta_25602_aux

open PEqualNP.Outside.L_meta_25602_aux

theorem PEqualNP.Outside.L_meta_25602 : (∀ (k : Nat) (hk : 0 < k), 5 ≤ k → k % 3 ≠ 0 →
  let ix := fun (a : Nat) => (⟨a % k, Nat.mod_lt _ hk⟩ : Fin k)
  let W := Fin k → ZMod 2
  let rot := fun (q : Nat) (v : W) (j : Fin k) => v (ix (j.val + k - q % k))
  ∀ (d s t : Nat) (name c : W), (d = 1 ∨ d = 2) →
    let run := fun (key : W) (j : Fin k) =>
      let z := rot s key + name
      let y := fun i : Fin k =>
        z i + z (ix (i.val + d)) + z (ix (i.val + k - d % k))
      y j + (1 + y (ix (j.val + 1))) * y (ix (j.val + 2)) + rot t key j + c j
    let count := fun (P : W →ₗ[ZMod 2] W) =>
      Nat.card { mask : W //
        ∃ left right : W → ZMod 2, ∀ a b : W,
          (∑ j : Fin k, mask j * run (P a + (b - P b)) j) = left a + right b }
    ∀ n : Nat, 0 < n → n < k →
      (∀ P : W →ₗ[ZMod 2] W, (∀ w, P (P w) = P w) →
        Module.finrank (ZMod 2) (LinearMap.range P) = n → count P ≤ 2 ^ (k - 2)) ∧
      ∃ P : W →ₗ[ZMod 2] W, (∀ w, P (P w) = P w) ∧
        Module.finrank (ZMod 2) (LinearMap.range P) = n ∧ count P = 2 ^ (k - 2)) := by
  intro k hk h5 h3 ix0 W0 rot0 d s t name c hd run count n hn0 hnk
  let M := roundEquiv hk h5 h3 hd s
  have hcount_eq : ∀ P : W k →ₗ[ZMod 2] W k, (∀ w, P (P w) = P w) →
      count P = Nat.card (LinearMap.ker (phiMap hk (M.toLinearMap.comp (P.comp M.symm.toLinearMap)))) := by
    intro P hP
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro mask
    exact additive_iff_ker_phi hk h5 h3 hd s t name c P hP mask
  constructor
  · intro P hP hfr
    rw [hcount_eq P hP]
    let Q := M.toLinearMap.comp (P.comp M.symm.toLinearMap)
    have hQ : ∀ w, Q (Q w) = Q w := by
      intro w
      dsimp only [Q]
      simp [hP]
    have hQ_range : LinearMap.range Q = Submodule.map M.toLinearMap (LinearMap.range P) := by
      ext y
      simp only [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨P (M.symm x), ⟨M.symm x, rfl⟩, hx⟩
      · rintro ⟨u, ⟨v, rfl⟩, hy⟩
        exact ⟨M v, by dsimp only [Q]; simpa using hy⟩
    have hQ_fr : Module.finrank (ZMod 2) (LinearMap.range Q) = n := by
      rw [hQ_range, LinearEquiv.finrank_map_eq, hfr]
    exact card_ker_phi_le hk h5 Q hQ (by omega) (by omega)
  · let Q0 : W k →ₗ[ZMod 2] W k := coordProj (k := k) n
    let P : W k →ₗ[ZMod 2] W k := M.symm.toLinearMap.comp (Q0.comp M.toLinearMap)
    have hP : ∀ w, P (P w) = P w := by
      intro w
      dsimp only [P, Q0]
      simp [coordProj_idem]
    have hP_range : LinearMap.range P = Submodule.map M.symm.toLinearMap (LinearMap.range Q0) := by
      ext y
      simp only [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨Q0 (M x), ⟨M x, rfl⟩, hx⟩
      · rintro ⟨u, ⟨v, rfl⟩, hy⟩
        exact ⟨M.symm v, by dsimp only [P]; simpa using hy⟩
    have hP_fr : Module.finrank (ZMod 2) (LinearMap.range P) = n := by
      rw [hP_range, LinearEquiv.finrank_map_eq, finrank_range_coordProj hnk]
    have hconj : M.toLinearMap.comp (P.comp M.symm.toLinearMap) = Q0 := by
      ext w j
      dsimp only [P]
      simp
    refine ⟨P, hP, hP_fr, ?_⟩
    rw [hcount_eq P hP, hconj]
    exact card_ker_phi_coordProj hk h5 hn0 hnk

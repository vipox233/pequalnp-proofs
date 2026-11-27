import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_745

open Polynomial

variable {K : Type*} [Field K] [Algebra (ZMod 2) K] {s : ℕ}

def bb (coord : K ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (z : ℕ) : K :=
  coord.symm (fun z' : Fin s => if z'.val = z then (1 : ZMod 2) else 0)

def dot (y v : Fin s → ZMod 2) : ZMod 2 := ∑ z, y z * v z

theorem coord_bb (coord : K ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (z : ℕ) :
    coord (bb coord z) = fun z' : Fin s => if z'.val = z then (1 : ZMod 2) else 0 := by
  simp [bb]

theorem dot_single_right (y : Fin s → ZMod 2) (z : Fin s) :
    dot y (fun z' : Fin s => if z'.val = z.val then (1 : ZMod 2) else 0) = y z := by
  unfold dot
  rw [Finset.sum_eq_single z]
  · simp
  · intro b _ hb
    have : b.val ≠ z.val := fun h => hb (Fin.ext h)
    simp [this]
  · simp

theorem dot_single_left (v : Fin s → ZMod 2) (z : Fin s) :
    dot (fun z' : Fin s => if z'.val = z.val then (1 : ZMod 2) else 0) v = v z := by
  unfold dot
  rw [Finset.sum_eq_single z]
  · simp
  · intro b _ hb
    have : b.val ≠ z.val := fun h => hb (Fin.ext h)
    simp [this]
  · simp

def dotL (y : Fin s → ZMod 2) : (Fin s → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := dot y v
  map_add' a b := by
    simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem inj_core (k : ℕ) (hk : 2 * s ≤ k) (coord : K ≃ₗ[ZMod 2] (Fin s → ZMod 2))
    (x x' : K) (y y' : Fin s → ZMod 2) (hy : y ≠ 0)
    (h : ∀ j : Fin k, dot y (coord (bb coord (j.val % s) * x ^ (j.val / s))) =
      dot y' (coord (bb coord (j.val % s) * x' ^ (j.val / s)))) :
    y = y' ∧ x = x' := by
  have hyy : y = y' := by
    funext z
    have h1 := h ⟨z.val, by omega⟩
    simp only [Nat.mod_eq_of_lt z.isLt, Nat.div_eq_of_lt z.isLt, pow_zero, mul_one,
      coord_bb] at h1
    rwa [dot_single_right, dot_single_right] at h1
  refine ⟨hyy, ?_⟩
  subst hyy
  by_contra hne
  have hd : x - x' ≠ 0 := sub_ne_zero.mpr hne
  have hz : ∀ z : Fin s, dot y (coord (bb coord z.val * (x - x'))) = 0 := by
    intro z
    have h1 := h ⟨s + z.val, by omega⟩
    have e1 : (s + z.val) % s = z.val := by
      rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt z.isLt
    have e2 : (s + z.val) / s = 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ (by omega), Nat.div_eq_of_lt z.isLt]
    simp only [e1, e2, pow_one] at h1
    have : dot y (coord (bb coord z.val * (x - x'))) =
        dotL y (coord (bb coord z.val * x)) - dotL y (coord (bb coord z.val * x')) := by
      rw [mul_sub, map_sub]; exact map_sub (dotL y) _ _
    rw [this]
    show dot y _ - dot y _ = 0
    rw [h1, sub_self]
  let L : (Fin s → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    ((dotL y).comp coord.toLinearMap).comp
      ((LinearMap.mulRight (ZMod 2) (x - x')).comp coord.symm.toLinearMap)
  have hL : ∀ w, L w = 0 := by
    intro w
    rw [LinearMap.pi_apply_eq_sum_univ L w]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : L (fun j => if i = j then 1 else 0) = 0 := by
      have e : (fun j : Fin s => if i = j then (1 : ZMod 2) else 0) =
          fun j : Fin s => if j.val = i.val then (1 : ZMod 2) else 0 := by
        funext j
        by_cases hij : i = j
        · subst hij; simp
        · have : j.val ≠ i.val := fun hh => hij (Fin.ext hh.symm)
          simp [hij, this]
      rw [e]
      exact hz i
    rw [this, smul_zero]
  apply hy
  funext z
  have h2 := hL (coord (bb coord z.val * (x - x')⁻¹))
  simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.mulRight_apply, mul_assoc, inv_mul_cancel₀ hd, mul_one, coord_bb] at h2
  change dot y _ = 0 at h2
  rw [dot_single_right] at h2
  simpa using h2

def T (coord : K ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (k : ℕ) (x : K) (j : Fin k) : K :=
  bb coord (j.val % s) * x ^ (j.val / s)

def Bx (coord : K ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (k r : ℕ) (a : Fin k → Fin r → ZMod 2) (x : K) :
    (Fin s → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) where
  toFun y := fun l => ∑ j, dot y (coord (T coord k x j)) * a j l
  map_add' y y' := by
    funext l
    simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c y := by
    funext l
    simp only [dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

noncomputable def Qp (coord : K ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (k r : ℕ) (a : Fin k → Fin r → ZMod 2)
    (c : Fin r → ZMod 2) : K[X] :=
  ∑ j : Fin k, C ((∑ l, c l * a j l) • bb coord (j.val % s)) * X ^ (j.val / s)

theorem Qp_deg (coord : K ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (k r : ℕ) (a : Fin k → Fin r → ZMod 2)
    (c : Fin r → ZMod 2) : (Qp coord k r a c).natDegree ≤ (k - 1) / s := by
  unfold Qp
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.div_le_div_right (by omega))

theorem Qp_eval (coord : K ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (k r : ℕ) (a : Fin k → Fin r → ZMod 2)
    (c : Fin r → ZMod 2) (x : K) :
    (Qp coord k r a c).eval x = ∑ j, (∑ l, c l * a j l) • T coord k x j := by
  unfold Qp T
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, smul_mul_assoc]

theorem Qp_ne (hs : 0 < s) (coord : K ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (k r : ℕ)
    (a : Fin k → Fin r → ZMod 2) (c : Fin r → ZMod 2) (j0 : Fin k)
    (hj0 : (∑ l, c l * a j0 l) ≠ 0) : Qp coord k r a c ≠ 0 := by
  intro h0
  have key : coord ((Qp coord k r a c).coeff (j0.val / s)) ⟨j0.val % s, Nat.mod_lt _ hs⟩ =
      ∑ l, c l * a j0 l := by
    unfold Qp
    rw [finsetSum_coeff, map_sum, Finset.sum_apply, Finset.sum_eq_single j0]
    · rw [coeff_C_mul_X_pow, if_pos rfl, map_smul, coord_bb]
      simp
    · intro j _ hj
      rw [coeff_C_mul_X_pow]
      split_ifs with h
      · rw [map_smul, coord_bb, Pi.smul_apply]
        have : j0.val % s ≠ j.val % s := by
          intro hm
          apply hj
          apply Fin.ext
          rw [← Nat.div_add_mod j.val s, ← Nat.div_add_mod j0.val s, hm, h]
        simp [this]
      · simp
    · simp
  rw [h0] at key
  simp at key
  exact hj0 key.symm

theorem root_card (coord : K ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (q : ℕ) (point : Fin q ≃ K)
    (P : K[X]) [DecidablePred fun x : Fin q => P.eval (point x) = 0]
    (hP : P ≠ 0) (D : ℕ) (hD : P.natDegree ≤ D) :
    (Finset.univ.filter fun x : Fin q => P.eval (point x) = 0).card ≤ D := by
  classical
  refine le_trans ?_ ((Multiset.toFinset_card_le _).trans ((card_roots' P).trans hD))
  apply Finset.card_le_card_of_injOn point
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (mem_roots hP).mpr hx
  · intro x _ y _ hxy
    exact point.injective hxy

theorem count_core (k r m d : ℕ) (hs : 0 < s) (q : ℕ) (point : Fin q ≃ K)
    (coord : K ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (inner : Fin m → (Fin s → ZMod 2))
    (hd : ∀ (A : (Fin s → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)), Function.Surjective A →
      ∀ t, d ≤ (Finset.univ.filter fun i => A (inner i) = t).card)
    (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hA : Function.Surjective A)
    (t : Fin r → ZMod 2) :
    (q - (2 ^ r - 1) * ((k - 1) / s)) * d ≤
      (Finset.univ.filter (fun u : Fin q × Fin m =>
        A (fun j : Fin k => dot (inner u.2) (coord (T coord k (point u.1) j))) = t)).card := by
  classical
  let a : Fin k → Fin r → ZMod 2 := fun j => A (fun l => if j = l then 1 else 0)
  have hAm : ∀ (x : K) (y : Fin s → ZMod 2),
      A (fun j : Fin k => dot y (coord (T coord k x j))) = Bx coord k r a x y := by
    intro x y
    rw [LinearMap.pi_apply_eq_sum_univ A]
    funext l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  -- bad points are roots
  have hbad : ∀ x : Fin q, ¬ Function.Surjective (Bx coord k r a (point x)) →
      ∃ c : Fin r → ZMod 2, c ≠ 0 ∧ (Qp coord k r a c).eval (point x) = 0 := by
    intro x hns
    rw [← LinearMap.range_eq_top, ← Ne, ← lt_top_iff_ne_top] at hns
    obtain ⟨φ, φ0, hle⟩ := (LinearMap.range (Bx coord k r a (point x))).exists_le_ker_of_lt_top hns
    let c : Fin r → ZMod 2 := fun l => φ (fun l' => if l = l' then 1 else 0)
    have hφ : ∀ v, φ v = ∑ l, v l * c l := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ φ]
      rfl
    refine ⟨c, ?_, ?_⟩
    · intro hc
      apply φ0
      refine LinearMap.ext fun v => ?_
      rw [hφ, hc]
      simp
    · have hz : ∀ z : Fin s, coord ((Qp coord k r a c).eval (point x)) z = 0 := by
        intro z
        have h1 : φ (Bx coord k r a (point x)
            (fun z' : Fin s => if z'.val = z.val then (1 : ZMod 2) else 0)) = 0 :=
          LinearMap.mem_ker.mp (hle ⟨_, rfl⟩)
        rw [hφ] at h1
        simp only [Bx, LinearMap.coe_mk, AddHom.coe_mk, dot_single_left] at h1
        rw [Qp_eval, map_sum, Finset.sum_apply, ← h1]
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      have : coord ((Qp coord k r a c).eval (point x)) = 0 := funext hz
      simpa using this
  have hne : ∀ c : Fin r → ZMod 2, c ≠ 0 → Qp coord k r a c ≠ 0 := by
    intro c hc
    obtain ⟨l0, hl0⟩ := Function.ne_iff.mp hc
    obtain ⟨v, hv⟩ := hA (fun l => if l = l0 then 1 else 0)
    have e1 : ∑ l, c l * A v l = c l0 := by
      rw [hv]
      simp
    have e2 : ∑ l, c l * A v l = ∑ j, v j * ∑ l, c l * a j l := by
      rw [LinearMap.pi_apply_eq_sum_univ A v]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have : ∃ j0, (∑ l, c l * a j0 l) ≠ 0 := by
      by_contra hno
      push_neg at hno
      rw [e2] at e1
      simp [hno] at e1
      exact hl0 (by simpa using e1.symm)
    obtain ⟨j0, hj0⟩ := this
    exact Qp_ne hs coord k r a c j0 hj0
  -- the count
  let G := Finset.univ.filter fun x : Fin q => Function.Surjective (Bx coord k r a (point x))
  let Bad := Finset.univ.filter fun x : Fin q => ¬ Function.Surjective (Bx coord k r a (point x))
  have hBad : Bad.card ≤ (2 ^ r - 1) * ((k - 1) / s) := by
    have hsub : Bad ⊆ (Finset.univ.erase (0 : Fin r → ZMod 2)).biUnion
        (fun c => Finset.univ.filter fun x : Fin q => (Qp coord k r a c).eval (point x) = 0) := by
      intro x hx
      simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨c, hc, hroot⟩ := hbad x hx
      simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_filter, true_and]
      exact ⟨c, hc, hroot⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
    refine (Finset.sum_le_sum fun c hc =>
      root_card coord q point _ (hne c (Finset.mem_erase.mp hc).1) _ (Qp_deg coord k r a c)).trans ?_
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    simp [ZMod.card]
  have hGB : G.card + Bad.card = q := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin q))) (fun x => Function.Surjective (Bx coord k r a (point x)))
    simpa [G, Bad] using this
  have hG : q - (2 ^ r - 1) * ((k - 1) / s) ≤ G.card := by omega
  rw [Finset.card_filter, Fintype.sum_prod_type]
  calc (q - (2 ^ r - 1) * ((k - 1) / s)) * d ≤ G.card * d := Nat.mul_le_mul_right _ hG
    _ = ∑ x ∈ G, d := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ x ∈ G, ∑ i : Fin m, (if A (fun j : Fin k => dot (inner i)
          (coord (T coord k (point x) j))) = t then 1 else 0) := by
        refine Finset.sum_le_sum fun x hx => ?_
        simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [← Finset.card_filter]
        simp only [hAm]
        exact hd _ hx t
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end PEqualNP.Outside.L_lib_745

open PEqualNP.Outside.L_lib_745 in
theorem PEqualNP.Outside.L_lib_745 :
  ∀ (k s r m d : ℕ), 0 < s → 2*s ≤ k → 0 < r →
    let F := ZMod 2
    let K := GaloisField 2 s
    let q := 2^s
    let V := Fin k → F
    let W := Fin s → F
    let R := Fin r → F
    ∀ (point : Fin q ≃ K) (coord : K ≃ₗ[F] W) (inner : Fin m ↪ W),
      (∀ i, inner i ≠ 0) →
      (∀ (A : W →ₗ[F] R), Function.Surjective A → ∀ t : R,
        d ≤ ((Finset.univ : Finset (Fin m)).filter (fun i => A (inner i) = t)).card) →
      let basisBit := fun j : Fin k => coord.symm
        (fun z : Fin s => if z.val = j.val % s then (1 : F) else 0)
      let mask := fun (u : Fin q × Fin m) (j : Fin k) =>
        ∑ z : Fin s, inner u.2 z * coord (basisBit j * (point u.1)^(j.val/s)) z
      Function.Injective mask ∧
        ∀ (A : V →ₗ[F] R), Function.Surjective A → ∀ t : R,
          (q-(2^r-1)*((k-1)/s))*d ≤
            ((Finset.univ : Finset (Fin q × Fin m)).filter (fun u => A (mask u) = t)).card := by
  intro k s r m d hs hk _ F K q V W R point coord inner hinner hd basisBit mask
  refine ⟨?_, ?_⟩
  · rintro ⟨x, i⟩ ⟨x', i'⟩ h
    have h' : ∀ j : Fin k, dot (inner i) (coord (bb coord (j.val % s) * (point x) ^ (j.val / s))) =
        dot (inner i') (coord (bb coord (j.val % s) * (point x') ^ (j.val / s))) :=
      fun j => congrFun h j
    obtain ⟨h1, h2⟩ := inj_core k hk coord (point x) (point x') (inner i) (inner i') (hinner i) h'
    have := point.injective h2
    have := inner.injective h1
    simp_all
  · intro A hA t
    exact count_core k r m d hs q point coord inner hd A hA t

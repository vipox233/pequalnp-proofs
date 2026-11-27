import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_690_aux

private def sgn2 (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

private lemma sgn2_add (x y : ZMod 2) : sgn2 (x + y) = sgn2 x * sgn2 y := by
  fin_cases x <;> fin_cases y <;> decide

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact (hx rfl).elim
  · rfl

private lemma sum_sgn2_dot {m : ℕ} (u : Fin m → ZMod 2) :
    ∑ v : Fin m → ZMod 2, sgn2 (∑ i : Fin m, v i * u i) =
      if u = 0 then (2 : ℤ) ^ m else 0 := by
  by_cases hu : u = 0
  · subst hu
    simp [sgn2]
  · simp only [hu, ↓reduceIte]
    have hex : ∃ i0 : Fin m, u i0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (funext h)
    rcases hex with ⟨i0, hi0⟩
    have hi0_one : u i0 = 1 := zmod2_eq_one_of_ne_zero hi0
    let flip : (Fin m → ZMod 2) → (Fin m → ZMod 2) := fun v i => if i = i0 then v i + 1 else v i
    have hinv : ∀ v, flip (flip v) = v := by
      intro v; funext i
      by_cases hi : i = i0
      · simp [flip, hi, add_assoc, zmod2_add_self]
      · simp [flip, hi]
    have hbij : ∑ v : Fin m → ZMod 2, sgn2 (∑ i : Fin m, flip v i * u i) =
        ∑ v : Fin m → ZMod 2, sgn2 (∑ i : Fin m, v i * u i) :=
      Equiv.sum_comp ⟨flip, flip, hinv, hinv⟩ (fun v => sgn2 (∑ i : Fin m, v i * u i))
    have hneg : ∀ v : Fin m → ZMod 2,
        sgn2 (∑ i : Fin m, flip v i * u i) = -sgn2 (∑ i : Fin m, v i * u i) := by
      intro v
      have hdiff : ∑ i : Fin m, flip v i * u i = (∑ i : Fin m, v i * u i) + 1 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
            ← Finset.add_sum_erase (s := Finset.univ) (f := fun i => v i * u i) (Finset.mem_univ i0)]
        have her : ∑ x ∈ Finset.univ.erase i0, flip v x * u x =
            ∑ x ∈ Finset.univ.erase i0, v x * u x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hne : x ≠ i0 := (Finset.mem_erase.mp hx).1
          simp [flip, hne]
        rw [her]
        simp only [flip, ↓reduceIte, hi0_one, mul_one]
        ring
      rw [hdiff, sgn2_add]
      have h1 : sgn2 1 = -1 := by decide
      rw [h1]
      ring
    have hsum_neg : ∑ v : Fin m → ZMod 2, sgn2 (∑ i : Fin m, flip v i * u i) =
        -∑ v : Fin m → ZMod 2, sgn2 (∑ i : Fin m, v i * u i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun v _ => hneg v)
    linarith

private lemma card_neg_masks_le {r : ℕ} (hr : 0 < r) (t : Fin r → ZMod 2) :
    (Finset.univ.filter (fun mask : Fin r → ZMod 2 => (∑ i : Fin r, mask i * t i) ≠ 0)).card ≤
      2 ^ (r - 1) := by
  by_cases ht : t = 0
  · subst ht
    simp
  · have hex : ∃ i0 : Fin r, t i0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact ht (funext h)
    rcases hex with ⟨i0, hi0⟩
    have hi0_one : t i0 = 1 := zmod2_eq_one_of_ne_zero hi0
    let S := Finset.univ.filter (fun mask : Fin r → ZMod 2 => (∑ i : Fin r, mask i * t i) ≠ 0)
    let T := Finset.univ.filter (fun mask : Fin r → ZMod 2 => (∑ i : Fin r, mask i * t i) = 0)
    let flip : (Fin r → ZMod 2) → (Fin r → ZMod 2) := fun v i => if i = i0 then v i + 1 else v i
    have hflip_dot : ∀ v : Fin r → ZMod 2,
        (∑ i : Fin r, flip v i * t i) = (∑ i : Fin r, v i * t i) + 1 := by
      intro v
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
          ← Finset.add_sum_erase (s := Finset.univ) (f := fun i => v i * t i) (Finset.mem_univ i0)]
      have her : ∑ x ∈ Finset.univ.erase i0, flip v x * t x =
          ∑ x ∈ Finset.univ.erase i0, v x * t x := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hne : x ≠ i0 := (Finset.mem_erase.mp hx).1
        simp [flip, hne]
      rw [her]
      simp only [flip, ↓reduceIte, hi0_one, mul_one]
      ring
    have hST : S.card = T.card := by
      apply Finset.card_bij (fun v _ => flip v)
      · intro v hv
        simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        rw [hflip_dot v, zmod2_eq_one_of_ne_zero hv, zmod2_add_self]
      · intro v1 _ v2 _ heq
        funext i
        have hi := congrFun heq i
        by_cases h : i = i0
        · subst h
          simp only [flip, ↓reduceIte] at hi
          have := congrArg (fun z => z + 1) hi
          simpa [add_assoc, zmod2_add_self] using this
        · simpa [flip, h] using hi
      · intro w hw
        refine ⟨flip w, ?_, ?_⟩
        · simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          rw [hflip_dot w, hw, zero_add]
          decide
        · funext i
          by_cases h : i = i0
          · simp [flip, h, add_assoc, zmod2_add_self]
          · simp [flip, h]
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_filter]
      intro _ _ h1 h2; exact h1 h2
    have hunion : S ∪ T = Finset.univ := by
      ext v
      simp only [S, T, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact (em _).symm
    have htot : S.card + T.card = 2 ^ r := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
      simp
    have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hr, pow_succ, mul_comm]
    change S.card ≤ 2 ^ (r - 1)
    omega

end PEqualNP.Outside.L_lib_690_aux

open PEqualNP.Outside.L_lib_690_aux in
theorem PEqualNP.Outside.L_lib_690 :
∀ (k s r : ℕ), 0 < k → 0 < s → 0 < r →
  let F := ZMod 2
  let K := GaloisField 2 s
  let q := 2^s
  let V := Fin k → F
  let W := Fin s → F
  let R := Fin r → F
  ∀ (atPoint : Fin q ≃ K) (coord : K ≃ₗ[F] W) (a : Fin r → V) (t : R),
    let sample := fun (x : Fin q) (y : W) (j : Fin k) =>
      ∑ i : Fin s, y i * coord (atPoint x ^ j.val) i
    let hits := ((Finset.univ : Finset (Fin q × W)).filter (fun z =>
      ∀ i : Fin r, (∑ j : Fin k, a i j * sample z.1 z.2 j) = t i)).card
    let roots := fun mask : R => ((Finset.univ : Finset (Fin q)).filter (fun x =>
      coord (∑ j : Fin k, if (∑ i : Fin r, mask i * a i j) = 0 then (0 : K) else atPoint x ^ j.val) = (0 : W))).card
    (2:ℤ)^r * (hits : ℤ) =
      (q : ℤ) * ∑ mask : R,
        (if (∑ i : Fin r, mask i*t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) ∧
    (LinearIndependent F a → q^2 ≤ 2^r*hits + 2^(r-1)*q*(k-1)) := by
  classical
  intro k s r hk hs hr
  dsimp only
  intro atPoint coord a t
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := ZMod 2
  let K := GaloisField 2 s
  let q := 2 ^ s
  let V := Fin k → F
  let W := Fin s → F
  let R := Fin r → F
  let sample : Fin q → W → Fin k → F := fun x y j =>
    ∑ i : Fin s, y i * coord (atPoint x ^ j.val) i
  let hits : ℕ := ((Finset.univ : Finset (Fin q × W)).filter (fun z =>
    ∀ i : Fin r, (∑ j : Fin k, a i j * sample z.1 z.2 j) = t i)).card
  let roots : R → ℕ := fun mask => ((Finset.univ : Finset (Fin q)).filter (fun x =>
    coord (∑ j : Fin k, if (∑ i : Fin r, mask i * a i j) = 0 then (0 : K) else atPoint x ^ j.val) = (0 : W))).card
  have hpart1 : (2 : ℤ) ^ r * (hits : ℤ) =
      (q : ℤ) * ∑ mask : R,
        (if (∑ i : Fin r, mask i * t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) := by
    let expr : Fin q × W → R → ℤ := fun z mask =>
      sgn2 (∑ i : Fin r, mask i * ((∑ j : Fin k, a i j * sample z.1 z.2 j) + t i))
    have hlhs : ∑ z : Fin q × W, ∑ mask : R, expr z mask = (2 : ℤ) ^ r * (hits : ℤ) := by
      have hinner : ∀ z : Fin q × W,
          ∑ mask : R, expr z mask =
            if (∀ i : Fin r, (∑ j : Fin k, a i j * sample z.1 z.2 j) = t i) then (2 : ℤ) ^ r else 0 := by
        intro z
        let u : R := fun i => (∑ j : Fin k, a i j * sample z.1 z.2 j) + t i
        have hu : u = 0 ↔ ∀ i : Fin r, (∑ j : Fin k, a i j * sample z.1 z.2 j) = t i := by
          have h0i : ∀ i : Fin r, (0 : R) i = 0 := fun _ => rfl
          constructor
          · intro h0 i
            have hi : (∑ j : Fin k, a i j * sample z.1 z.2 j) + t i = 0 := by
              have := congrFun h0 i
              rwa [h0i i] at this
            have := congrArg (fun x => x + t i) hi
            simpa [add_assoc, zmod2_add_self] using this
          · intro hall
            funext i
            change (∑ j : Fin k, a i j * sample z.1 z.2 j) + t i = 0
            rw [hall i, zmod2_add_self]
        have hdot := sum_sgn2_dot u
        have heq_sum : ∑ mask : R, expr z mask = ∑ mask : R, sgn2 (∑ i : Fin r, mask i * u i) := rfl
        rw [heq_sum, hdot]
        by_cases h : u = 0
        · have h' := hu.mp h
          simp [h, h']
        · have h' : ¬ ∀ i : Fin r, (∑ j : Fin k, a i j * sample z.1 z.2 j) = t i := fun x => h (hu.mpr x)
          simp [h, h']
      calc
        ∑ z : Fin q × W, ∑ mask : R, expr z mask
            = ∑ z : Fin q × W,
                if (∀ i : Fin r, (∑ j : Fin k, a i j * sample z.1 z.2 j) = t i) then (2 : ℤ) ^ r else 0 :=
              Finset.sum_congr rfl (fun z _ => hinner z)
        _ = (hits : ℤ) * (2 : ℤ) ^ r := by
              rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        _ = (2 : ℤ) ^ r * (hits : ℤ) := mul_comm _ _
    have hrhs : ∑ mask : R, ∑ z : Fin q × W, expr z mask =
        (q : ℤ) * ∑ mask : R,
          (if (∑ i : Fin r, mask i * t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro mask _
      let c : V := fun j => ∑ i : Fin r, mask i * a i j
      let vecAt : Fin q → W := fun x =>
        coord (∑ j : Fin k, if c j = 0 then (0 : K) else atPoint x ^ j.val)
      have hvec_coord : ∀ (x : Fin q) (l : Fin s),
          vecAt x l = ∑ j : Fin k, c j * coord (atPoint x ^ j.val) l := by
        intro x l
        have hsmul : ∀ j : Fin k,
            (if c j = 0 then (0 : K) else atPoint x ^ j.val) = c j • (atPoint x ^ j.val) := by
          intro j
          by_cases hcj : c j = 0
          · simp [hcj]
          · simp [hcj, zmod2_eq_one_of_ne_zero hcj]
        have hsumK : (∑ j : Fin k, if c j = 0 then (0 : K) else atPoint x ^ j.val) =
            ∑ j : Fin k, c j • (atPoint x ^ j.val) :=
          Finset.sum_congr rfl (fun j _ => hsmul j)
        dsimp only [vecAt]
        rw [hsumK, map_sum]
        simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
      have hexpr_eq : ∀ (x : Fin q) (y : W),
          expr (x, y) mask =
            sgn2 (∑ i : Fin r, mask i * t i) * sgn2 (∑ l : Fin s, y l * vecAt x l) := by
        intro x y
        have hdot : (∑ i : Fin r, mask i * ((∑ j : Fin k, a i j * sample x y j) + t i)) =
            (∑ i : Fin r, mask i * t i) + (∑ l : Fin s, y l * vecAt x l) := by
          have h1 : (∑ i : Fin r, mask i * ((∑ j : Fin k, a i j * sample x y j) + t i)) =
              (∑ i : Fin r, mask i * (∑ j : Fin k, a i j * sample x y j)) +
              (∑ i : Fin r, mask i * t i) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => by ring)
          rw [h1, add_comm]
          congr 1
          calc
            ∑ i : Fin r, mask i * (∑ j : Fin k, a i j * sample x y j)
                = ∑ i : Fin r, ∑ j : Fin k, (mask i * a i j) * sample x y j := by
                    refine Finset.sum_congr rfl ?_
                    intro i _
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl (fun j _ => by ring)
            _ = ∑ j : Fin k, ∑ i : Fin r, (mask i * a i j) * sample x y j := Finset.sum_comm
            _ = ∑ j : Fin k, c j * sample x y j := by
                    refine Finset.sum_congr rfl ?_
                    intro j _
                    rw [← Finset.sum_mul]
            _ = ∑ j : Fin k, ∑ l : Fin s, y l * (c j * coord (atPoint x ^ j.val) l) := by
                    refine Finset.sum_congr rfl ?_
                    intro j _
                    dsimp only [sample]
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl (fun l _ => by ring)
            _ = ∑ l : Fin s, ∑ j : Fin k, y l * (c j * coord (atPoint x ^ j.val) l) := Finset.sum_comm
            _ = ∑ l : Fin s, y l * (∑ j : Fin k, c j * coord (atPoint x ^ j.val) l) := by
                    refine Finset.sum_congr rfl (fun l _ => (Finset.mul_sum _ _ _).symm)
            _ = ∑ l : Fin s, y l * vecAt x l := by
                    refine Finset.sum_congr rfl (fun l _ => by rw [hvec_coord x l])
        dsimp only [expr]
        rw [hdot, sgn2_add]
      calc
        ∑ z : Fin q × W, expr z mask
            = ∑ x : Fin q, ∑ y : W, expr (x, y) mask := Fintype.sum_prod_type _
        _ = ∑ x : Fin q, ∑ y : W,
              sgn2 (∑ i : Fin r, mask i * t i) * sgn2 (∑ l : Fin s, y l * vecAt x l) := by
              refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hexpr_eq x y))
        _ = sgn2 (∑ i : Fin r, mask i * t i) *
              ∑ x : Fin q, ∑ y : W, sgn2 (∑ l : Fin s, y l * vecAt x l) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun x _ => (Finset.mul_sum _ _ _).symm)
        _ = sgn2 (∑ i : Fin r, mask i * t i) *
              ∑ x : Fin q, (if vecAt x = 0 then (2 : ℤ) ^ s else 0) := by
              congr 1
              refine Finset.sum_congr rfl (fun x _ => sum_sgn2_dot (vecAt x))
        _ = sgn2 (∑ i : Fin r, mask i * t i) * ((roots mask : ℤ) * (q : ℤ)) := by
              congr 1
              rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
              push_cast [q]
              rfl
        _ = (q : ℤ) * ((if (∑ i : Fin r, mask i * t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ)) := by
              dsimp only [sgn2]; ring
    rw [← hlhs, Finset.sum_comm, hrhs]
  refine ⟨hpart1, ?_⟩
  intro hli
  have h0R : ∀ i : Fin r, (0 : R) i = 0 := fun _ => rfl
  have hroots_zero : roots 0 = q := by
    dsimp only [roots]
    have hall : (Finset.univ : Finset (Fin q)).filter (fun x =>
        coord (∑ j : Fin k, if (∑ i : Fin r, (0 : R) i * a i j) = 0 then (0 : K) else atPoint x ^ j.val) = (0 : W)) =
        Finset.univ := by
      ext x
      simp [h0R]
    rw [hall]
    simp [q]
  have hroots_nz : ∀ mask : R, mask ≠ 0 → roots mask ≤ k - 1 := by
    intro mask hmask
    let c : V := fun j => ∑ i : Fin r, mask i * a i j
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hcomb : ∑ i : Fin r, mask i • a i = 0 := by
        funext j
        have hj : c j = 0 := congrFun hc0 j
        simpa [c, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hj
      have hall0 := Fintype.linearIndependent_iff.mp hli mask hcomb
      exact hmask (funext hall0)
    have hex_j : ∃ j0 : Fin k, c j0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hc_ne (funext h)
    let P : Polynomial K :=
      ∑ j : Fin k, Polynomial.C (if c j = 0 then (0 : K) else 1) * Polynomial.X ^ j.val
    have hP_ne : P ≠ 0 := by
      rcases hex_j with ⟨j0, hj0⟩
      intro hP0
      have hcoeff : P.coeff j0.val = 0 := by rw [hP0]; simp
      have hcoeff1 : P.coeff j0.val = 1 := by
        have hsumc : P.coeff j0.val =
            ∑ j : Fin k, (Polynomial.C (if c j = 0 then (0 : K) else 1) * Polynomial.X ^ j.val).coeff j0.val := by
          simpa [P, Polynomial.lcoeff_apply] using
            map_sum (Polynomial.lcoeff K j0.val)
              (fun j : Fin k => Polynomial.C (if c j = 0 then (0 : K) else 1) * Polynomial.X ^ j.val) Finset.univ
        rw [hsumc, Finset.sum_eq_single j0]
        · simp [hj0]
        · intro j _ hne
          have hvalne : j.val ≠ j0.val := fun h => hne (Fin.ext h)
          by_cases hcj : c j = 0 <;> simp [hcj, Polynomial.coeff_X_pow, hvalne.symm]
        · intro h; exact (h (Finset.mem_univ j0)).elim
      rw [hcoeff1] at hcoeff
      exact one_ne_zero hcoeff
    have hP_deg : P.natDegree ≤ k - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      calc
        (Polynomial.C (if c j = 0 then (0 : K) else 1) * Polynomial.X ^ j.val).natDegree
            ≤ (Polynomial.C (if c j = 0 then (0 : K) else 1)).natDegree +
              (Polynomial.X ^ j.val : Polynomial K).natDegree := Polynomial.natDegree_mul_le
        _ ≤ 0 + j.val := by
              rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
        _ ≤ k - 1 := by omega
    have hP_eval : ∀ x : Fin q,
        Polynomial.eval (atPoint x) P =
          ∑ j : Fin k, if c j = 0 then (0 : K) else atPoint x ^ j.val := by
      intro x
      have h1 : Polynomial.eval (atPoint x) P =
          ∑ j : Fin k, Polynomial.eval (atPoint x) (Polynomial.C (if c j = 0 then (0 : K) else 1) * Polynomial.X ^ j.val) := by
        have hm := map_sum (Polynomial.evalRingHom (atPoint x))
          (fun j : Fin k => Polynomial.C (if c j = 0 then (0 : K) else 1) * Polynomial.X ^ j.val) Finset.univ
        simpa only [P, Polynomial.coe_evalRingHom] using hm
      rw [h1]
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hcj : c j = 0 <;> simp [hcj]
    let S := (Finset.univ : Finset (Fin q)).filter (fun x =>
      coord (∑ j : Fin k, if c j = 0 then (0 : K) else atPoint x ^ j.val) = (0 : W))
    have hcard_le : S.card ≤ P.roots.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun x => atPoint x)
      · intro x hx
        have hzeroW : coord (∑ j : Fin k, if c j = 0 then (0 : K) else atPoint x ^ j.val) = 0 :=
          (Finset.mem_filter.mp hx).2
        have hzeroK : (∑ j : Fin k, if c j = 0 then (0 : K) else atPoint x ^ j.val) = 0 :=
          coord.injective (by simpa [map_zero] using hzeroW)
        have hroot : Polynomial.IsRoot P (atPoint x) := by
          rw [Polynomial.IsRoot, hP_eval x, hzeroK]
        simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP_ne]
        exact hroot
      · intro x1 _ x2 _ heq
        exact atPoint.injective heq
    calc
      roots mask = S.card := rfl
      _ ≤ P.roots.toFinset.card := hcard_le
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ ≤ k - 1 := hP_deg
  suffices hZ : ((q ^ 2 : ℕ) : ℤ) ≤ ((2 ^ r * hits + 2 ^ (r - 1) * q * (k - 1) : ℕ) : ℤ) by
    exact_mod_cast hZ
  let Neg := Finset.univ.filter (fun mask : R => (∑ i : Fin r, mask i * t i) ≠ 0)
  have hsum_ge :
      (q : ℤ) - (2 ^ (r - 1) : ℤ) * ((k - 1 : ℕ) : ℤ) ≤
      ∑ mask : R, (if (∑ i : Fin r, mask i * t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) := by
    have h0t : ∑ i : Fin r, (0 : R) i * t i = 0 := by simp [h0R]
    have hsplit : ∑ mask : R,
        (if (∑ i : Fin r, mask i * t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) =
        (q : ℤ) + ∑ mask ∈ Finset.univ.erase (0 : R),
          (if (∑ i : Fin r, mask i * t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : R)), h0t, hroots_zero]
      simp
    rw [hsplit]
    have hbound_rest :
        -(Neg.card : ℤ) * ((k - 1 : ℕ) : ℤ) ≤
        ∑ mask ∈ Finset.univ.erase (0 : R),
          (if (∑ i : Fin r, mask i * t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) := by
      have hterm : ∀ mask ∈ Finset.univ.erase (0 : R),
          (if (∑ i : Fin r, mask i * t i) = 0 then (0 : ℤ) else -((k - 1 : ℕ) : ℤ)) ≤
          (if (∑ i : Fin r, mask i * t i) = 0 then (1 : ℤ) else -1) * (roots mask : ℤ) := by
        intro mask hmem
        have hnz : mask ≠ 0 := (Finset.mem_erase.mp hmem).1
        by_cases h0 : (∑ i : Fin r, mask i * t i) = 0
        · simp only [h0, ↓reduceIte, one_mul]
          exact Nat.cast_nonneg _
        · simp only [h0, ↓reduceIte, neg_mul, one_mul, neg_le_neg_iff]
          exact_mod_cast hroots_nz mask hnz
      have hle1 := Finset.sum_le_sum hterm
      have hsum_neg_eq : ∑ mask ∈ Finset.univ.erase (0 : R),
          (if (∑ i : Fin r, mask i * t i) = 0 then (0 : ℤ) else -((k - 1 : ℕ) : ℤ)) =
          -(Neg.card : ℤ) * ((k - 1 : ℕ) : ℤ) := by
        have heq_u : ∑ mask ∈ Finset.univ.erase (0 : R),
            (if (∑ i : Fin r, mask i * t i) = 0 then (0 : ℤ) else -((k - 1 : ℕ) : ℤ)) =
            ∑ mask : R, (if (∑ i : Fin r, mask i * t i) = 0 then (0 : ℤ) else -((k - 1 : ℕ) : ℤ)) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : R)), h0t]
          simp
        rw [heq_u, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
        dsimp only [Neg]
        ring
      rw [← hsum_neg_eq]
      exact hle1
    have hNeg_le : (Neg.card : ℤ) ≤ (2 ^ (r - 1) : ℤ) := by
      exact_mod_cast card_neg_masks_le hr t
    have hk_nonneg : (0 : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := Nat.cast_nonneg _
    have hmul_le : (Neg.card : ℤ) * ((k - 1 : ℕ) : ℤ) ≤ (2 ^ (r - 1) : ℤ) * ((k - 1 : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_right hNeg_le hk_nonneg
    linarith
  have hmulq := mul_le_mul_of_nonneg_left hsum_ge (Nat.cast_nonneg q : (0 : ℤ) ≤ (q : ℤ))
  rw [← hpart1] at hmulq
  push_cast
  linarith

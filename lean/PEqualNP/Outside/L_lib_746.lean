import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_746

open Finset MvPolynomial

noncomputable def Bd (q d c : ℕ) : ℕ :=
  q ^ (d - min c (d * (q - 1)) / (q - 1)) -
    (min c (d * (q - 1)) % (q - 1)) * q ^ (d - min c (d * (q - 1)) / (q - 1) - 1)

theorem Bd_eq {q d a b : ℕ} (hq : 2 ≤ q) (hb : b < q - 1) (ha : a < d) :
    Bd q d (a * (q - 1) + b) = (q - b) * q ^ (d - a - 1) := by
  have hQ : 0 < q - 1 := by omega
  have h1 : a * (q - 1) + b ≤ d * (q - 1) := by
    have : (a + 1) * (q - 1) ≤ d * (q - 1) := Nat.mul_le_mul_right _ ha
    nlinarith
  have h2 : (a * (q - 1) + b) / (q - 1) = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hb, zero_add]
  have h3 : (a * (q - 1) + b) % (q - 1) = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  unfold Bd
  rw [min_eq_left h1, h2, h3]
  have : d - a = (d - a - 1) + 1 := by omega
  rw [this, pow_succ, Nat.add_sub_cancel, Nat.sub_mul]
  ring_nf

theorem Bd_top {q d c : ℕ} (hq : 2 ≤ q) (hc : d * (q - 1) ≤ c) : Bd q d c = 1 := by
  have hQ : 0 < q - 1 := by omega
  unfold Bd
  rw [min_eq_right hc, Nat.mul_div_cancel _ hQ, Nat.mul_mod_left]
  simp

theorem arith {q d c k : ℕ} (hq : 2 ≤ q) (hk : k ≤ q - 1) (hkc : k ≤ c) :
    Bd q (d + 1) c ≤ (q - k) * Bd q d (c - k) := by
  have hQ : 0 < q - 1 := by omega
  by_cases h : d * (q - 1) ≤ c - k
  · rw [Bd_top hq h, mul_one]
    by_cases h' : (d + 1) * (q - 1) ≤ c
    · rw [Bd_top hq h']
      omega
    · have hj : c - d * (q - 1) < q - 1 := by
        rw [add_mul, one_mul] at h'
        omega
      have hc : c = d * (q - 1) + (c - d * (q - 1)) := by omega
      rw [hc, Bd_eq hq hj (Nat.lt_succ_self d)]
      rw [show d + 1 - d - 1 = 0 by omega, pow_zero, mul_one]
      omega
  · push_neg at h
    set a := (c - k) / (q - 1) with ha
    set b := (c - k) % (q - 1) with hb
    have hb' : b < q - 1 := Nat.mod_lt _ hQ
    have hab : c - k = a * (q - 1) + b := by
      rw [ha, hb, mul_comm]
      exact (Nat.div_add_mod _ _).symm
    have had : a < d := by
      by_contra hcon
      push_neg at hcon
      have : d * (q - 1) ≤ a * (q - 1) := Nat.mul_le_mul_right _ hcon
      omega
    rw [hab, Bd_eq hq hb' had]
    by_cases hbk : b + k < q - 1
    · have hc : c = a * (q - 1) + (b + k) := by omega
      rw [hc, Bd_eq hq hbk (by omega)]
      have : d + 1 - a - 1 = (d - a - 1) + 1 := by omega
      rw [this, pow_succ]
      have key : (q - (b + k)) * q ≤ (q - k) * (q - b) := by
        obtain ⟨r, hr⟩ : ∃ r, q = b + k + r := ⟨q - (b + k), by omega⟩
        rw [hr]
        have e1 : b + k + r - (b + k) = r := by omega
        have e2 : b + k + r - k = b + r := by omega
        have e3 : b + k + r - b = k + r := by omega
        rw [e1, e2, e3]
        nlinarith
      calc (q - (b + k)) * (q ^ (d - a - 1) * q) = ((q - (b + k)) * q) * q ^ (d - a - 1) := by ring
        _ ≤ ((q - k) * (q - b)) * q ^ (d - a - 1) := Nat.mul_le_mul_right _ key
        _ = (q - k) * ((q - b) * q ^ (d - a - 1)) := by ring
    · push_neg at hbk
      have hj : b + k - (q - 1) < q - 1 := by omega
      have hc : c = (a + 1) * (q - 1) + (b + k - (q - 1)) := by
        rw [add_mul, one_mul]
        omega
      rw [hc, Bd_eq hq hj (by omega)]
      have : d + 1 - (a + 1) - 1 = d - a - 1 := by omega
      rw [this, ← mul_assoc]
      apply Nat.mul_le_mul_right
      obtain ⟨u, hu⟩ : ∃ u, q - k = u + 1 := ⟨q - k - 1, by omega⟩
      obtain ⟨v, hv⟩ : ∃ v, q - b = v + 1 := ⟨q - b - 1, by omega⟩
      have : q - (b + k - (q - 1)) = u + v + 1 := by omega
      rw [this, hu, hv]
      nlinarith

theorem Bd_zero (q c : ℕ) : Bd q 0 c = 1 := by
  simp [Bd]

noncomputable def redN (q n : ℕ) : ℕ := if n = 0 then 0 else (n - 1) % (q - 1) + 1

theorem redN_le (q n : ℕ) : redN q n ≤ n := by
  unfold redN
  split_ifs with h
  · omega
  · have : (n - 1) % (q - 1) ≤ n - 1 := Nat.mod_le _ _
    omega

theorem redN_lt {q : ℕ} (hq : 2 ≤ q) (n : ℕ) : redN q n < q := by
  unfold redN
  split_ifs with h
  · omega
  · have := Nat.mod_lt (n - 1) (show 0 < q - 1 by omega)
    omega

theorem pow_redN {E : Type} [Field E] [Fintype E] (x : E) (n : ℕ) :
    x ^ redN (Fintype.card E) n = x ^ n := by
  unfold redN
  split_ifs with h
  · rw [h]
  · by_cases hx : x = 0
    · rw [hx, zero_pow (by omega), zero_pow h]
    · have h1 := FiniteField.pow_card_sub_one_eq_one x hx
      have h2 : n = (n - 1) % (Fintype.card E - 1) + (Fintype.card E - 1) *
          ((n - 1) / (Fintype.card E - 1)) + 1 := by
        have := Nat.mod_add_div (n - 1) (Fintype.card E - 1)
        omega
      conv_rhs => rw [h2]
      rw [pow_succ, pow_succ, pow_add, pow_mul, h1, one_pow, mul_one]

noncomputable def redM (q : ℕ) {σ : Type} (m : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.mapRange (redN q) (by simp [redN]) m

noncomputable def red {E : Type} [Field E] {σ : Type} (q : ℕ) (p : MvPolynomial σ E) :
    MvPolynomial σ E :=
  ∑ m ∈ p.support, monomial (redM q m) (p.coeff m)

theorem eval_red {E : Type} [Field E] [Fintype E] {σ : Type} (p : MvPolynomial σ E)
    (x : σ → E) : eval x (red (Fintype.card E) p) = eval x p := by
  conv_rhs => rw [p.as_sum]
  unfold red
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [eval_monomial, eval_monomial]
  congr 1
  unfold redM
  rw [Finsupp.prod_mapRange_index (by simp)]
  refine Finsupp.prod_congr (fun j _ => ?_)
  exact pow_redN (x j) (m j)

theorem totalDegree_red {E : Type} [Field E] {σ : Type} (q : ℕ) (p : MvPolynomial σ E) :
    totalDegree (red q p) ≤ totalDegree p := by
  unfold red
  apply totalDegree_finsetSum_le
  intro m hm
  refine (totalDegree_monomial_le _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  unfold redM
  rw [Finsupp.sum_mapRange_index (by simp)]
  exact Finset.sum_le_sum (fun j _ => redN_le q (m j))

theorem degreeOf_red {E : Type} [Field E] {σ : Type} [DecidableEq σ] {q : ℕ} (hq : 2 ≤ q)
    (p : MvPolynomial σ E) (j : σ) : degreeOf j (red q p) < q := by
  rw [degreeOf_lt_iff (by omega)]
  intro m hm
  unfold red at hm
  have := support_sum hm
  rw [Finset.mem_biUnion] at this
  obtain ⟨m', _, hm'⟩ := this
  have := support_monomial_subset hm'
  rw [Finset.mem_singleton] at this
  subst this
  unfold redM
  rw [Finsupp.mapRange_apply]
  exact redN_lt hq _

theorem AF (E : Type) [Field E] [Fintype E] [DecidableEq E] : ∀ (d c : ℕ)
    (p : MvPolynomial (Fin d) E), p ≠ 0 → (∀ j, degreeOf j p < Fintype.card E) →
    totalDegree p ≤ c →
    Bd (Fintype.card E) d c ≤ (univ.filter (fun x => eval x p ≠ 0)).card := by
  intro d
  induction d with
  | zero =>
    intro c p hp _ _
    rw [Bd_zero]
    apply Finset.card_pos.2
    refine ⟨fun i => i.elim0, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [eq_C_of_isEmpty p] at hp ⊢
    rw [eval_C]
    intro h
    exact hp (by rw [h, map_zero])
  | succ d ih =>
    intro c p hp hdeg hc
    have hq : 2 ≤ Fintype.card E := by
      have := Fintype.one_lt_card (α := E)
      omega
    set P := finSuccEquiv E d p with hPdef
    have hP : P ≠ 0 := by
      intro h
      apply hp
      have : (finSuccEquiv E d) p = (finSuccEquiv E d) 0 := by rw [← hPdef, h, map_zero]
      exact (finSuccEquiv E d).injective this
    set k := P.natDegree with hkdef
    have hk : k < Fintype.card E := by
      rw [hkdef, hPdef, natDegree_finSuccEquiv]
      exact hdeg 0
    set L := P.coeff k with hLdef
    have hL : L ≠ 0 := by
      rw [hLdef, hkdef]
      exact Polynomial.leadingCoeff_ne_zero.2 hP
    have hLdeg : totalDegree L + k ≤ totalDegree p := totalDegree_coeff_finSuccEquiv_add_le p k hL
    have hLred : ∀ j, degreeOf j L < Fintype.card E := fun j =>
      lt_of_le_of_lt (degreeOf_coeff_finSuccEquiv p j k) (hdeg j.succ)
    have IH := ih (c - k) L hL hLred (by omega)
    have AR := arith (d := d) hq (show k ≤ Fintype.card E - 1 by omega) (show k ≤ c by omega)
    refine AR.trans ((Nat.mul_le_mul_left _ IH).trans ?_)
    set S := univ.filter (fun x : Fin d → E => eval x L ≠ 0)
    set G := univ.filter (fun x : Fin (d + 1) → E => eval x p ≠ 0)
    have hfib := Finset.card_eq_sum_card_fiberwise (s := G) (t := univ) (f := Fin.tail)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [hfib]
    have hsub : ∑ x' ∈ S, (G.filter (fun x => Fin.tail x = x')).card ≤
        ∑ x' ∈ univ, (G.filter (fun x => Fin.tail x = x')).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    refine le_trans ?_ hsub
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro x' hx'
    rw [Finset.mem_filter] at hx'
    have hx'L := hx'.2
    set Q := Polynomial.map (eval x') P with hQdef
    have hQk : Q.coeff k = eval x' L := by rw [hQdef, Polynomial.coeff_map]
    have hQ0 : Q ≠ 0 := by
      intro h
      apply hx'L
      rw [← hQk, h, Polynomial.coeff_zero]
    have hQdeg : Q.natDegree ≤ k := Polynomial.natDegree_map_le
    have hroots : (univ.filter (fun t : E => Q.eval t = 0)).card ≤ k := by
      have h1 : univ.filter (fun t : E => Q.eval t = 0) ⊆ Q.roots.toFinset := by
        intro t ht
        rw [Finset.mem_filter] at ht
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ0]
        exact ht.2
      exact (Finset.card_le_card h1).trans
        ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' Q).trans hQdeg))
    have hnon : Fintype.card E - k ≤ (univ.filter (fun t : E => Q.eval t ≠ 0)).card := by
      have := Finset.card_filter_add_card_filter_not (s := (univ : Finset E))
        (fun t : E => Q.eval t = 0)
      rw [Finset.card_univ] at this
      have e : (univ.filter (fun t : E => ¬ Q.eval t = 0)) =
          (univ.filter (fun t : E => Q.eval t ≠ 0)) := rfl
      rw [e] at this
      omega
    refine hnon.trans ?_
    have himg : (univ.filter (fun t : E => Q.eval t ≠ 0)).image
        (fun t => (Fin.cons t x' : Fin (d + 1) → E)) ⊆ G.filter (fun x => Fin.tail x = x') := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      rw [Finset.mem_filter] at ht ⊢
      refine ⟨?_, Fin.tail_cons _ _⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [eval_eq_eval_mv_eval']
      exact ht.2
    refine le_trans (le_of_eq ?_) (Finset.card_le_card himg)
    rw [Finset.card_image_of_injective]
    intro t1 t2 h
    simpa using congrFun h 0

theorem factor {E : Type} [Field E] {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    ∃ (r : ℕ) (A : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin r) (Fin n) E),
      r = M.rank ∧ A * B = M := by
  set W := LinearMap.range M.mulVecLin
  set b := Module.finBasis E W
  have hw : ∀ s : Fin n, M.mulVecLin (Pi.single s 1) ∈ W := fun s => LinearMap.mem_range_self _ _
  refine ⟨Module.finrank E W, Matrix.of fun i k => (b k : Fin n → E) i,
    Matrix.of fun k s => b.repr ⟨M.mulVecLin (Pi.single s 1), hw s⟩ k, rfl, ?_⟩
  ext i s
  have h := congrArg (fun v : W => (v : Fin n → E) i) (b.sum_repr ⟨M.mulVecLin (Pi.single s 1), hw s⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  rw [Matrix.col_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

noncomputable def Kp {E : Type} [Field E] {n d r : ℕ} (A : Matrix (Fin n) (Fin r) E)
    (B : Matrix (Fin r) (Fin n) E) (P : (Fin d → E) →ₗ[E] Matrix (Fin n) (Fin n) E) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin d) E) :=
  Matrix.of fun u v => ∑ j : Fin d, X j * C ((B * P (fun j' => if j = j' then 1 else 0) * A) u v)

theorem eval_Kp {E : Type} [Field E] {n d r : ℕ} (A : Matrix (Fin n) (Fin r) E)
    (B : Matrix (Fin r) (Fin n) E) (P : (Fin d → E) →ₗ[E] Matrix (Fin n) (Fin n) E)
    (x : Fin d → E) :
    eval x (Matrix.det (1 + Kp A B P)) = Matrix.det (1 + P x * (A * B)) := by
  rw [RingHom.map_det, ← Matrix.mul_assoc, Matrix.det_one_add_mul_comm]
  congr 1
  ext u v
  rw [P.pi_apply_eq_sum_univ x]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Kp, Matrix.of_apply,
    map_add, map_sum, map_mul, eval_X, eval_C, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> simp [Matrix.mul_assoc]

theorem totalDegree_Kp {E : Type} [Field E] {n d r : ℕ} (A : Matrix (Fin n) (Fin r) E)
    (B : Matrix (Fin r) (Fin n) E) (P : (Fin d → E) →ₗ[E] Matrix (Fin n) (Fin n) E) :
    totalDegree (Matrix.det (1 + Kp A B P)) ≤ r := by
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro σ _
  refine (totalDegree_mul _ _).trans ?_
  have h0 : totalDegree ((((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin d) E))) = 0 := by
    rw [← map_intCast (C : E →+* MvPolynomial (Fin d) E), totalDegree_C]
  rw [h0, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  have hent : ∀ u v, totalDegree ((1 + Kp A B P) u v) ≤ 1 := by
    intro u v
    rw [Matrix.add_apply]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [Matrix.one_apply]
      split_ifs
      · rw [totalDegree_one]; omega
      · rw [totalDegree_zero]; omega
    · simp only [Kp, Matrix.of_apply]
      apply totalDegree_finsetSum_le
      intro j _
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_C]
  calc ∑ i, totalDegree ((1 + Kp A B P) (σ i) i) ≤ ∑ _i : Fin r, 1 :=
        Finset.sum_le_sum (fun i _ => hent _ _)
    _ = r := by simp

end PEqualNP.Outside.L_lib_746

open PEqualNP.Outside.L_lib_746 MvPolynomial in
theorem PEqualNP.Outside.L_lib_746 : ∀ (E : Type) [Field E] [Fintype E] (d n l : ℕ),
  let q := Fintype.card E
  let Mat := Matrix (Fin n) (Fin n) E
  ∀ (M : Fin l → Mat) (P : Fin l → ((Fin d → E) →ₗ[E] Mat)),
    let c := min (∑ i : Fin l, (M i).rank) (d*(q-1))
    let a := c/(q-1)
    let b := c % (q-1)
    let good := @Finset.filter (Fin d → E)
      (fun x => ∀ i : Fin l, ((1 : Mat) + P i x * M i).det ≠ 0)
      (fun _ => Classical.propDecidable _) Finset.univ
    q^(d-a) - b*q^(d-a-1) ≤ good.card := by
  intro E _ _ d n l q Mat M P c a b good
  classical
  have hq : 2 ≤ Fintype.card E := by
    have := Fintype.one_lt_card (α := E)
    omega
  choose r A B hr hAB using fun i => factor (M i)
  set f : MvPolynomial (Fin d) E := ∏ i, Matrix.det (1 + Kp (A i) (B i) (P i)) with hf
  have hev : ∀ x, eval x f = ∏ i, ((1 : Mat) + P i x * M i).det := by
    intro x
    rw [hf, map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [eval_Kp, hAB i]
  have hdeg : totalDegree f ≤ ∑ i, (M i).rank := by
    rw [hf]
    refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [← hr i]
    exact totalDegree_Kp _ _ _
  set g := red (Fintype.card E) f with hg
  have hevg : ∀ x, eval x g = eval x f := fun x => eval_red f x
  have hg0 : g ≠ 0 := by
    intro h
    have := hevg 0
    rw [h, map_zero, hev] at this
    simp only [map_zero, zero_mul, add_zero, Matrix.det_one, Finset.prod_const_one] at this
    exact zero_ne_one this
  have key := AF E d (∑ i, (M i).rank) g hg0 (fun j => degreeOf_red hq f j)
    ((totalDegree_red _ f).trans hdeg)
  refine le_trans (le_of_eq rfl) (key.trans (le_of_eq ?_))
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hevg, hev, good]
  rw [Finset.prod_ne_zero_iff]
  simp

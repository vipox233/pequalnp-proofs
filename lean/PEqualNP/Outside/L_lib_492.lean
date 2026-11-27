import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_492_aux

open MvPolynomial PEqualNP.ProofComplexity

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

def boolAx (n : ℕ) : Set (Poly n) :=
  {q : Poly n | ∃ i : Fin n, q = X i * X i + X i}

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  fin_cases c <;> decide

theorem zmod2_sq_add_self (c : ZMod 2) : c * c + c = 0 := by
  fin_cases c <;> decide

theorem add_self_eq_zero {n : ℕ} (p : Poly n) : p + p = 0 := by
  ext d
  rw [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_zero]
  exact zmod2_add_self (p.coeff d)

theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  fin_cases c
  · exact absurd rfl h
  · rfl

theorem pc_mono {n : ℕ} {F1 F2 : Set (Poly n)} {D1 D2 : ℕ} {p : Poly n}
    (hF : F1 ⊆ F2) (hD : D1 ≤ D2) (hp : PCDerivable F1 D1 p) : PCDerivable F2 D2 p := by
  induction hp with
  | ax hmem hdeg => exact PCDerivable.ax (hF hmem) (hdeg.trans hD)
  | zero => exact PCDerivable.zero
  | add _ _ ih1 ih2 => exact PCDerivable.add ih1 ih2
  | mulX j _ hdeg ih => exact PCDerivable.mulX j ih (hdeg.trans hD)

theorem pc_sum {n : ℕ} {F : Set (Poly n)} {D : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Poly n)
    (hf : ∀ a ∈ s, PCDerivable F D (f a)) : PCDerivable F D (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact PCDerivable.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PCDerivable.add (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

def weight {n : ℕ} (d : Fin n →₀ ℕ) : ℕ := ∑ i : Fin n, d i

theorem weight_eq_sum {n : ℕ} (d : Fin n →₀ ℕ) : d.sum (fun _ k => k) = weight d := by
  unfold weight
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

theorem totalDegree_X_le_one {n : ℕ} (j : Fin n) : (X j : Poly n).totalDegree ≤ 1 := by
  rw [X]
  exact (totalDegree_monomial_le (Finsupp.single j 1) (1 : ZMod 2)).trans (by simp)

theorem pc_mul_monomial {n : ℕ} {F : Set (Poly n)} {D : ℕ} :
    ∀ (k : ℕ) (r : Fin n →₀ ℕ) (q : Poly n), weight r = k →
      PCDerivable F D q → k + q.totalDegree ≤ D → PCDerivable F D (monomial r 1 * q)
  | 0, r, q, hr, hq, _ => by
    have hr0 : r = 0 := by
      ext i
      have hle : r i ≤ ∑ j : Fin n, r j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [← weight] at hle
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [hr0, monomial_zero', map_one, one_mul]
    exact hq
  | k + 1, r, q, hr, hq, hd => by
    have hex : ∃ j : Fin n, 0 < r j := by
      by_contra h
      have h0 : ∀ j : Fin n, r j = 0 := by
        intro j
        have : ¬ 0 < r j := fun hj => h ⟨j, hj⟩
        omega
      have hw : weight r = 0 := by
        unfold weight
        simp [h0]
      omega
    obtain ⟨j, hj⟩ := hex
    let r' : Fin n →₀ ℕ := r - Finsupp.single j 1
    have hreq : r = Finsupp.single j 1 + r' := by
      ext i
      simp only [r', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      by_cases hij : j = i
      · subst hij
        simp only [ite_true]
        omega
      · simp [hij]
    have hwr' : weight r' = k := by
      have h1 : weight r = weight (Finsupp.single j 1) + weight r' := by
        conv_lhs => rw [hreq]
        unfold weight
        simp [Finset.sum_add_distrib]
      have h2 : weight (Finsupp.single j 1) = 1 := by
        unfold weight
        simp [Finsupp.single_apply]
      omega
    have ih := pc_mul_monomial k r' q hwr' hq (by omega)
    have hmul : monomial r 1 * q = X j * (monomial r' 1 * q) := by
      rw [hreq, ← mul_assoc]
      congr 1
      rw [X, monomial_mul_monomial, mul_one]
    rw [hmul]
    refine PCDerivable.mulX j ih ?_
    calc (X j * (monomial r' 1 * q)).totalDegree
        ≤ (X j : Poly n).totalDegree + (monomial r' 1 * q).totalDegree := totalDegree_mul _ _
      _ ≤ 1 + ((monomial r' (1 : ZMod 2)).totalDegree + q.totalDegree) :=
          Nat.add_le_add (totalDegree_X_le_one j) (totalDegree_mul (monomial r' (1 : ZMod 2)) q)
      _ ≤ 1 + (r'.sum (fun _ m => m) + q.totalDegree) :=
          Nat.add_le_add_left (Nat.add_le_add_right (totalDegree_monomial_le r' 1) _) _
      _ = k + 1 + q.totalDegree := by
          rw [weight_eq_sum, hwr']
          omega
      _ ≤ D := hd

noncomputable def ml {n : ℕ} (d : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  d.mapRange (fun k => min k 1) rfl

theorem ml_apply {n : ℕ} (d : Fin n →₀ ℕ) (i : Fin n) : ml d i = min (d i) 1 := by
  simp [ml]

theorem totalDegree_boolAx {n : ℕ} (i : Fin n) :
    (X i * X i + X i : Poly n).totalDegree ≤ 2 := by
  calc (X i * X i + X i : Poly n).totalDegree
      ≤ max (X i * X i : Poly n).totalDegree (X i : Poly n).totalDegree := totalDegree_add _ _
    _ ≤ max ((X i : Poly n).totalDegree + (X i : Poly n).totalDegree) 1 :=
        max_le_max (totalDegree_mul _ _) (totalDegree_X_le_one i)
    _ ≤ max (1 + 1) 1 :=
        max_le_max (Nat.add_le_add (totalDegree_X_le_one i) (totalDegree_X_le_one i)) le_rfl
    _ = 2 := by decide

theorem pc_monomial_ml {n : ℕ} {D : ℕ} :
    ∀ (k : ℕ) (d : Fin n →₀ ℕ), weight d = k → k ≤ D →
      PCDerivable (boolAx n) D (monomial d 1 + monomial (ml d) 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro d hwd hkD
    by_cases hle : ∀ i : Fin n, d i ≤ 1
    · have hml : ml d = d := by
        ext i
        rw [ml_apply]
        exact Nat.min_eq_left (hle i)
      rw [hml, add_self_eq_zero]
      exact PCDerivable.zero
    · obtain ⟨i, hi⟩ := not_forall.mp hle
      have hi2 : 2 ≤ d i := by omega
      let r : Fin n →₀ ℕ := d - Finsupp.single i 2
      let e : Fin n →₀ ℕ := r + Finsupp.single i 1
      have hd_eq : d = r + Finsupp.single i 2 := by
        ext j
        simp only [r, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        by_cases hij : i = j
        · subst hij
          simp only [ite_true]
          omega
        · simp [hij]
      have hwr : weight r + 2 = k := by
        have h1 : weight d = weight r + weight (Finsupp.single i 2) := by
          conv_lhs => rw [hd_eq]
          unfold weight
          simp [Finset.sum_add_distrib]
        have h2 : weight (Finsupp.single i 2) = 2 := by
          unfold weight
          simp [Finsupp.single_apply]
        omega
      have hwe : weight e = weight r + 1 := by
        have h1 : weight e = weight r + weight (Finsupp.single i 1) := by
          unfold weight e
          simp [Finset.sum_add_distrib]
        have h2 : weight (Finsupp.single i 1) = 1 := by
          unfold weight
          simp [Finsupp.single_apply]
        omega
      have hmle : ml e = ml d := by
        ext j
        rw [ml_apply, ml_apply, hd_eq]
        simp only [e, Finsupp.add_apply, Finsupp.single_apply]
        by_cases hij : i = j
        · subst hij
          simp only [ite_true]
          omega
        · simp [hij]
      have hstep1 : PCDerivable (boolAx n) D (monomial d 1 + monomial e 1) := by
        have hax : PCDerivable (boolAx n) D (X i * X i + X i) :=
          PCDerivable.ax ⟨i, rfl⟩ ((totalDegree_boolAx i).trans (by omega))
        have hmul := pc_mul_monomial (weight r) r (X i * X i + X i) rfl hax
          (Nat.add_le_add_left (totalDegree_boolAx i) _ |>.trans (by omega))
        have heq : (monomial r (1 : ZMod 2) * (X i * X i + X i) : Poly n) =
            monomial d 1 + monomial e 1 := by
          rw [mul_add, hd_eq]
          congr 1
          · rw [X, monomial_mul_monomial, mul_one, monomial_mul_monomial, mul_one,
              ← Finsupp.single_add]
          · rw [X, monomial_mul_monomial, mul_one]
        exact heq ▸ hmul
      have hstep2 : PCDerivable (boolAx n) D (monomial e 1 + monomial (ml d) 1) := by
        rw [← hmle]
        exact ih (weight e) (by omega) e rfl (by omega)
      have hsum := PCDerivable.add hstep1 hstep2
      have hcancel : (monomial d (1 : ZMod 2) + monomial e 1) +
          (monomial e 1 + monomial (ml d) 1) = monomial d 1 + monomial (ml d) 1 := by
        calc (monomial d (1 : ZMod 2) + monomial e 1) + (monomial e 1 + monomial (ml d) 1)
            = monomial d 1 + (monomial e 1 + monomial e 1) + monomial (ml d) 1 := by ring
          _ = monomial d 1 + 0 + monomial (ml d) 1 := by rw [add_self_eq_zero]
          _ = monomial d 1 + monomial (ml d) 1 := by ring
      rwa [hcancel] at hsum

noncomputable def nf {n : ℕ} (p : Poly n) : Poly n :=
  ∑ d ∈ p.support, monomial (ml d) (p.coeff d)

theorem nf_degreeOf_le_one {n : ℕ} (p : Poly n) (i : Fin n) : (nf p).degreeOf i ≤ 1 := by
  rw [degreeOf_eq_sup]
  refine Finset.sup_le fun m hm => ?_
  have hmem := support_sum (s := p.support) (f := fun d => monomial (ml d) (p.coeff d)) hm
  rw [Finset.mem_biUnion] at hmem
  obtain ⟨d, _, hmd⟩ := hmem
  have hmeq : m = ml d := Finset.mem_singleton.mp (support_monomial_subset hmd)
  rw [hmeq, ml_apply]
  exact Nat.min_le_right _ _

theorem pc_nf {n : ℕ} (p : Poly n) :
    PCDerivable (boolAx n) p.totalDegree (p + nf p) := by
  have hdecomp : p + nf p = ∑ d ∈ p.support, (monomial d (p.coeff d) + monomial (ml d) (p.coeff d)) := by
    rw [Finset.sum_add_distrib, ← p.as_sum, nf]
  rw [hdecomp]
  refine pc_sum p.support _ fun d hd => ?_
  have hc : p.coeff d = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp hd)
  rw [hc]
  have hwd : weight d ≤ p.totalDegree := by
    rw [← weight_eq_sum]
    exact Finset.le_sup (f := fun s : Fin n →₀ ℕ => s.sum (fun _ k => k)) hd
  exact pc_monomial_ml (weight d) d rfl hwd

theorem eval_eq_zero_of_pc {n : ℕ} {G : Set (Poly n)} {D : ℕ} {q : Poly n}
    (hq : PCDerivable (boolAx n ∪ G) D q) (x : Fin n → ZMod 2)
    (hG : ∀ g ∈ G, eval x g = 0) : eval x q = 0 := by
  induction hq with
  | ax hp _ =>
    rcases hp with ⟨i, rfl⟩ | hg
    · simp only [map_add, map_mul, eval_X]
      exact zmod2_sq_add_self (x i)
    · exact hG _ hg
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]

theorem eval_nf {n : ℕ} (p : Poly n) (x : Fin n → ZMod 2) : eval x (nf p) = eval x p := by
  have hpc : PCDerivable (boolAx n ∪ ∅) p.totalDegree (p + nf p) :=
    pc_mono Set.subset_union_left le_rfl (pc_nf p)
  have h0 := eval_eq_zero_of_pc hpc x (fun _ h => False.elim h)
  rw [map_add] at h0
  calc eval x (nf p) = 0 + eval x (nf p) := (zero_add _).symm
    _ = (eval x p + eval x p) + eval x (nf p) := by rw [zmod2_add_self]
    _ = eval x p + (eval x p + eval x (nf p)) := by ring
    _ = eval x p + 0 := by rw [h0]
    _ = eval x p := add_zero _

theorem eq_zero_of_eval_eq_zero {n : ℕ} (r : Poly n) (hdeg : ∀ i : Fin n, r.degreeOf i ≤ 1)
    (heval : ∀ x : Fin n → ZMod 2, eval x r = 0) : r = 0 := by
  by_contra hr0
  have hne : r.support.Nonempty := support_nonempty.mpr hr0
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image r.support weight hne
  let x : Fin n → ZMod 2 := fun i => if m i = 0 then 0 else 1
  have hle1 : ∀ s ∈ r.support, ∀ i : Fin n, s i ≤ 1 := by
    intro s hs i
    have h1 : s i ≤ r.degreeOf i := by
      rw [degreeOf_eq_sup]
      exact Finset.le_sup (f := fun d : Fin n →₀ ℕ => d i) hs
    exact h1.trans (hdeg i)
  have hterm0 : ∀ s ∈ r.support, s ≠ m → r.coeff s * ∏ i ∈ s.support, x i ^ s i = 0 := by
    intro s hs hsm
    have hex : ∃ i ∈ s.support, m i = 0 := by
      by_contra hno
      have hle : ∀ i : Fin n, s i ≤ m i := by
        intro i
        by_cases hsi : s i = 0
        · omega
        · have his : i ∈ s.support := Finsupp.mem_support_iff.mpr hsi
          have hmi : m i ≠ 0 := fun h0 => hno ⟨i, his, h0⟩
          have hs1 := hle1 s hs i
          omega
      have hne_i : ∃ j : Fin n, s j < m j := by
        by_contra hge
        apply hsm
        ext j
        have h1 := hle j
        have h2 : ¬ s j < m j := fun hj => hge ⟨j, hj⟩
        omega
      obtain ⟨j, hj⟩ := hne_i
      have hlt : weight s < weight m :=
        Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ j, hj⟩
      have hgm := hmin s hs
      omega
    obtain ⟨i, hi, hmi⟩ := hex
    have hsi : s i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hprod0 : ∏ j ∈ s.support, x j ^ s j = 0 := by
      apply Finset.prod_eq_zero hi
      simp only [x, hmi, ite_true]
      exact zero_pow hsi
    rw [hprod0, mul_zero]
  have htermm : ∏ i ∈ m.support, x i ^ m i = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp hi
    simp [x, hmi]
  have hev := heval x
  rw [eval_eq] at hev
  rw [Finset.sum_eq_single m (fun s hs hsm => hterm0 s hs hsm) (fun h => absurd hm h),
    htermm, mul_one] at hev
  exact (mem_support_iff.mp hm) hev

theorem eq_of_multilinear_eval_eq {n : ℕ} (p q : Poly n)
    (hp : ∀ i, p.degreeOf i ≤ 1) (hq : ∀ i, q.degreeOf i ≤ 1)
    (hev : ∀ x : Fin n → ZMod 2, eval x p = eval x q) : p = q := by
  have h0 : p + q = 0 := by
    apply eq_zero_of_eval_eq_zero (p + q)
    · intro i
      exact (degreeOf_add_le i p q).trans (max_le (hp i) (hq i))
    · intro x
      rw [map_add, hev x]
      exact zmod2_add_self _
  calc p = p + 0 := (add_zero p).symm
    _ = p + (q + q) := by rw [add_self_eq_zero]
    _ = (p + q) + q := by ring
    _ = 0 + q := by rw [h0]
    _ = q := zero_add _

noncomputable def fac {n : ℕ} (a : Fin n → ZMod 2) (i : Fin n) : Poly n :=
  if a i = 1 then X i else 1 + X i

noncomputable def indPoly {n : ℕ} (a : Fin n → ZMod 2) : Poly n :=
  ∏ i : Fin n, fac a i

theorem totalDegree_fac_le {n : ℕ} (a : Fin n → ZMod 2) (i : Fin n) :
    (fac a i).totalDegree ≤ 1 := by
  unfold fac
  split_ifs
  · exact totalDegree_X_le_one i
  · exact (totalDegree_add (1 : Poly n) (X i)).trans
      (max_le (by simp) (totalDegree_X_le_one i))

theorem degreeOf_fac_le {n : ℕ} (a : Fin n → ZMod 2) (j i : Fin n) :
    (fac a j).degreeOf i ≤ if i = j then 1 else 0 := by
  unfold fac
  have hX : (X j : Poly n).degreeOf i ≤ if i = j then 1 else 0 := by
    rw [degreeOf_X]
  have h1 : (1 : Poly n).degreeOf i = 0 := by simp
  by_cases h : a j = 1
  · simp only [h, ite_true]
    exact hX
  · simp only [h, ite_false]
    exact (degreeOf_add_le i (1 : Poly n) (X j)).trans (max_le (by omega) hX)

theorem degreeOf_prod_fac_le {n : ℕ} (a : Fin n → ZMod 2) (s : Finset (Fin n)) (i : Fin n) :
    (∏ j ∈ s, fac a j).degreeOf i ≤ if i ∈ s then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj]
    have h1 := degreeOf_mul_le i (fac a j) (∏ k ∈ s, fac a k)
    have h2 := degreeOf_fac_le a j i
    by_cases hij : i = j
    · subst hij
      have hns : i ∉ s := hj
      simp only [ite_true, hns, ite_false, Finset.mem_insert_self] at h2 ih ⊢
      omega
    · simp only [hij, ite_false, Finset.mem_insert, false_or] at h2 ih ⊢
      omega

theorem degreeOf_indPoly_le {n : ℕ} (a : Fin n → ZMod 2) (i : Fin n) :
    (indPoly a).degreeOf i ≤ 1 := by
  unfold indPoly
  simpa using degreeOf_prod_fac_le a Finset.univ i

theorem eval_fac {n : ℕ} (a b : Fin n → ZMod 2) (i : Fin n) :
    eval b (fac a i) = if b i = a i then 1 else 0 := by
  unfold fac
  simp only [apply_ite (eval b), eval_X, map_add, map_one]
  generalize a i = x
  generalize b i = y
  fin_cases x <;> fin_cases y <;> decide

theorem eval_indPoly {n : ℕ} (a b : Fin n → ZMod 2) :
    eval b (indPoly a) = if b = a then 1 else 0 := by
  unfold indPoly
  rw [map_prod]
  by_cases hba : b = a
  · subst hba
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    apply Finset.prod_eq_one
    intro i _
    rw [eval_fac, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hba)]
    have hex : ∃ i : Fin n, b i ≠ a i := by
      by_contra h
      apply hba
      funext i
      by_contra hne
      exact h ⟨i, hne⟩
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [eval_fac, ite_eq_right_of_eq_false _ _ (eq_false hi)]

theorem totalDegree_prod_fac_le {n : ℕ} (a : Fin n → ZMod 2) (s : Finset (Fin n)) :
    (∏ j ∈ s, fac a j).totalDegree ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have h1 := totalDegree_mul (fac a j) (∏ k ∈ s, fac a k)
    have h2 := totalDegree_fac_le a j
    omega

theorem pc_mul_fac {n : ℕ} {F : Set (Poly n)} {D : ℕ} (a : Fin n → ZMod 2) (j : Fin n)
    {p : Poly n} (hp : PCDerivable F D p) (hd : p.totalDegree + 1 ≤ D) :
    PCDerivable F D (fac a j * p) := by
  have hdeg : (X j * p).totalDegree ≤ D := by
    have h1 := totalDegree_mul (X j : Poly n) p
    have h2 := totalDegree_X_le_one j
    omega
  have hX : PCDerivable F D (X j * p) := PCDerivable.mulX j hp hdeg
  unfold fac
  split_ifs
  · exact hX
  · rw [add_mul, one_mul]
    exact PCDerivable.add hp hX

theorem pc_mul_prod_fac {n : ℕ} {F : Set (Poly n)} {D : ℕ} (a : Fin n → ZMod 2)
    (s : Finset (Fin n)) {g : Poly n} (hg : PCDerivable F D g)
    (hd : s.card + g.totalDegree ≤ D) :
    PCDerivable F D ((∏ j ∈ s, fac a j) * g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_mul]
    exact hg
  | @insert j s hj ih =>
    rw [Finset.card_insert_of_notMem hj] at hd
    rw [Finset.prod_insert hj, mul_assoc]
    have ih' := ih (by omega)
    have htd : ((∏ k ∈ s, fac a k) * g).totalDegree ≤ s.card + g.totalDegree := by
      have h1 := totalDegree_mul (∏ k ∈ s, fac a k) g
      have h2 := totalDegree_prod_fac_le a s
      omega
    exact pc_mul_fac a j ih' (by omega)

theorem degreeOf_sum_le {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Poly n) (i : Fin n)
    (hf : ∀ a ∈ s, (f a).degreeOf i ≤ 1) : (∑ a ∈ s, f a).degreeOf i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (degreeOf_add_le i _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s)) (ih fun b hb => hf b (Finset.mem_insert_of_mem hb)))

theorem nf_eq_sum_ind {n : ℕ} (p : Poly n) :
    nf p = ∑ a ∈ Finset.univ.filter (fun a : Fin n → ZMod 2 => eval a p = 1), indPoly a := by
  apply eq_of_multilinear_eval_eq
  · exact nf_degreeOf_le_one p
  · intro i
    exact degreeOf_sum_le _ _ i (fun a _ => degreeOf_indPoly_le a i)
  · intro b
    rw [eval_nf, map_sum]
    by_cases hb : eval b p = 1
    · rw [hb]
      have hmem : b ∈ Finset.univ.filter (fun a : Fin n → ZMod 2 => eval a p = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩
      rw [Finset.sum_eq_single b]
      · rw [eval_indPoly, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      · intro a _ hab
        rw [eval_indPoly, ite_eq_right_of_eq_false _ _ (eq_false hab.symm)]
      · intro h
        exact absurd hmem h
    · have hb0 : eval b p = 0 := by
        by_contra h0
        exact hb (zmod2_eq_one_of_ne_zero h0)
      rw [hb0]
      symm
      apply Finset.sum_eq_zero
      intro a ha
      have hne : b ≠ a := by
        intro hba
        subst hba
        exact hb (Finset.mem_filter.mp ha).2
      rw [eval_indPoly, ite_eq_right_of_eq_false _ _ (eq_false hne)]

theorem main (n w : ℕ) (G : Set (Poly n)) (p : Poly n)
    (hGdeg : ∀ g ∈ G, g.totalDegree ≤ w) :
    (∀ a : Fin n → ZMod 2, (∀ g ∈ G, eval a g = 0) → eval a p = 0) ↔
      PCDerivable (boolAx n ∪ G) (max p.totalDegree (n + w)) p := by
  let D := max p.totalDegree (n + w)
  constructor
  · intro hsem
    have hnf_pc : PCDerivable (boolAx n ∪ G) D (nf p) := by
      rw [nf_eq_sum_ind p]
      refine pc_sum _ _ fun a ha => ?_
      have hap : eval a p = 1 := (Finset.mem_filter.mp ha).2
      have hex : ∃ g ∈ G, eval a g ≠ 0 := by
        by_contra h
        have h0 : ∀ g ∈ G, eval a g = 0 := by
          intro g hg
          by_contra hne
          exact h ⟨g, hg, hne⟩
        have := hsem a h0
        rw [hap] at this
        exact one_ne_zero this
      obtain ⟨g, hgG, hga_ne⟩ := hex
      have hga : eval a g = 1 := zmod2_eq_one_of_ne_zero hga_ne
      have hgw : g.totalDegree ≤ w := hGdeg g hgG
      have hprod_td : (indPoly a * g).totalDegree ≤ n + w := by
        have h1 := totalDegree_mul (indPoly a) g
        have h2 := totalDegree_prod_fac_le a Finset.univ
        simp only [Finset.card_univ, Fintype.card_fin] at h2
        unfold indPoly at h1 ⊢
        omega
      have hprod_pc : PCDerivable (boolAx n ∪ G) D (indPoly a * g) := by
        have hg_pc : PCDerivable (boolAx n ∪ G) D g :=
          PCDerivable.ax (Or.inr hgG) (hgw.trans (by omega))
        have h := pc_mul_prod_fac a Finset.univ hg_pc (by simp; omega)
        exact h
      have hnf_eq : nf (indPoly a * g) = indPoly a := by
        apply eq_of_multilinear_eval_eq (nf (indPoly a * g)) (indPoly a)
          (nf_degreeOf_le_one _) (degreeOf_indPoly_le a)
        intro b
        rw [eval_nf, map_mul, eval_indPoly]
        by_cases hba : b = a
        · subst hba
          simp [hga]
        · simp [hba]
      have hred : PCDerivable (boolAx n ∪ G) D (indPoly a * g + indPoly a) := by
        have h : PCDerivable (boolAx n ∪ G) D (indPoly a * g + nf (indPoly a * g)) :=
          pc_mono Set.subset_union_left (hprod_td.trans (le_max_right p.totalDegree (n + w)))
            (pc_nf (indPoly a * g))
        rwa [hnf_eq] at h
      have hsum := PCDerivable.add hprod_pc hred
      have hcancel : indPoly a * g + (indPoly a * g + indPoly a) = indPoly a := by
        calc indPoly a * g + (indPoly a * g + indPoly a)
            = (indPoly a * g + indPoly a * g) + indPoly a := by ring
          _ = 0 + indPoly a := by rw [add_self_eq_zero]
          _ = indPoly a := zero_add _
      rwa [hcancel] at hsum
    have hpnf : PCDerivable (boolAx n ∪ G) D (p + nf p) :=
      pc_mono Set.subset_union_left (le_max_left _ _) (pc_nf p)
    have hsum := PCDerivable.add hpnf hnf_pc
    have hcancel : (p + nf p) + nf p = p := by
      calc (p + nf p) + nf p = p + (nf p + nf p) := by ring
        _ = p + 0 := by rw [add_self_eq_zero]
        _ = p := add_zero _
    rwa [hcancel] at hsum
  · intro hpc a hG0
    exact eval_eq_zero_of_pc hpc a hG0

end PEqualNP.Outside.L_lib_492_aux

theorem PEqualNP.Outside.L_lib_492 : ∀ (n w : ℕ), let P := MvPolynomial (Fin n) (ZMod 2)
  let B := {q : P | ∃ i : Fin n, q = MvPolynomial.X i * MvPolynomial.X i + MvPolynomial.X i}
  ∀ (G : Set P) (p : P), (∀ g ∈ G, MvPolynomial.totalDegree g ≤ w) →
    ((∀ a : Fin n → ZMod 2, (∀ g ∈ G, MvPolynomial.eval a g = 0) → MvPolynomial.eval a p = 0) ↔
      PEqualNP.ProofComplexity.PCDerivable (B ∪ G) (max p.totalDegree (n + w)) p) := by
  intro n w P B G p hGdeg
  exact PEqualNP.Outside.L_lib_492_aux.main n w G p hGdeg
